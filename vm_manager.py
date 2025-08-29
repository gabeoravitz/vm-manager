#!/usr/bin/env python3
"""Enhanced single-file libvirt VM manager with, backups, snapshots, security, and advanced features.
Supports snapshots, backups, enhanced networking, SSL, authentication, and more.
All assets inline. Requires python3-libvirt, python3-cryptography (optional for SSL).
"""
from __future__ import annotations
import os, socket, html, urllib.parse, re, struct, zlib, subprocess, tempfile, shutil, threading, time, json
import hashlib, hmac, base64, datetime, uuid, pathlib, glob, tarfile, gzip
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from io import BytesIO, StringIO
from typing import Dict, List, Optional, Any, Tuple, Union
from urllib.parse import urlparse
import ssl
import logging

try:
    import libvirt  # type: ignore
except Exception:  # pragma: no cover
    libvirt = None

try:
    from cryptography.fernet import Fernet
    from cryptography.hazmat.primitives import hashes
    from cryptography.hazmat.primitives.kdf.pbkdf2 import PBKDF2HMAC
    CRYPTO_AVAILABLE = True
except ImportError:
    CRYPTO_AVAILABLE = False

# Configuration
HOST = os.environ.get('VM_MGR_HOST', '0.0.0.0')
PORT = int(os.environ.get('VM_MGR_PORT', '8000'))
SSL_CERT = os.environ.get('VM_MGR_SSL_CERT', '')
SSL_KEY = os.environ.get('VM_MGR_SSL_KEY', '')
AUTH_PASSWORD = os.environ.get('VM_MGR_PASSWORD', '')  # Empty = no auth
LOG_LEVEL = os.environ.get('VM_MGR_LOG_LEVEL', 'INFO')
BACKUP_DIR = os.environ.get('VM_MGR_BACKUP_DIR', '/')
# Setup logging
logging.basicConfig(level=getattr(logging, LOG_LEVEL.upper()), 
                   format='%(asctime)s [%(levelname)s] %(message)s',
                   handlers=[logging.StreamHandler()])
logger = logging.getLogger(__name__)

def human_bytes(v: Union[int, float]) -> str:
    v = float(v)
    for u in ['B', 'KiB', 'MiB', 'GiB', 'TiB']:
        if v < 1024 or u == 'TiB':
            return f"{v:.1f} {u}" if u != 'B' else f"{int(v)} B"
        v /= 1024
    return f"{v} B"

def parse_int(s, default):
    try: return int(s)
    except: return default

def generate_password_hash(password: str) -> str:
    """Generate a secure password hash"""
    salt = os.urandom(32)
    pwdhash = hashlib.pbkdf2_hmac('sha256', password.encode('utf-8'), salt, 100000)
    return base64.b64encode(salt + pwdhash).decode('ascii')

def verify_password(password: str, hash_str: str) -> bool:
    """Verify password against hash"""
    try:
        decoded = base64.b64decode(hash_str.encode('ascii'))
        salt = decoded[:32]
        stored_hash = decoded[32:]
        pwdhash = hashlib.pbkdf2_hmac('sha256', password.encode('utf-8'), salt, 100000)
        return hmac.compare_digest(stored_hash, pwdhash)
    except Exception:
        return False

def create_cloud_init_iso(hostname: str, ssh_keys: List[str], user_data: str = "", meta_data: str = "") -> str:
    """Create a cloud-init ISO file"""
    iso_dir = tempfile.mkdtemp()
    
    # Default user-data if none provided
    if not user_data:
        key_list = '\n'.join(f'    - {key}' for key in ssh_keys)
        user_data = f"""#cloud-config
hostname: {hostname}
users:
  - name: ubuntu
    sudo: ALL=(ALL) NOPASSWD:ALL
    shell: /bin/bash
    ssh_authorized_keys:
{key_list}
package_update: true
packages:
  - qemu-guest-agent
runcmd:
  - systemctl enable qemu-guest-agent
  - systemctl start qemu-guest-agent
"""
    
    # Default meta-data if none provided
    if not meta_data:
        meta_data = f"""instance-id: {hostname}-{uuid.uuid4().hex[:8]}
local-hostname: {hostname}
"""
    
    # Write cloud-init files
    with open(os.path.join(iso_dir, 'user-data'), 'w') as f:
        f.write(user_data)
    with open(os.path.join(iso_dir, 'meta-data'), 'w') as f:
        f.write(meta_data)
    
    # Create ISO
    iso_path = os.path.join(tempfile.gettempdir(), f"{hostname}-cloud-init.iso")
    subprocess.check_call([
        'sudo', 'genisoimage', '-output', iso_path, '-volid', 'cidata',
        '-joliet', '-rock', iso_dir
    ])
    
    shutil.rmtree(iso_dir)
    return iso_path

class LV:
    def __init__(self):
        if libvirt is None: raise RuntimeError('libvirt module not available')
        self.conn = libvirt.open(None)
        if self.conn is None: raise RuntimeError('connect failed')
    def list_domains(self): return sorted(self.conn.listAllDomains(), key=lambda d:d.name().lower())
    def get_domain(self,name): return self.conn.lookupByName(name)
    def list_pools(self): return sorted(self.conn.listAllStoragePools(), key=lambda p:p.name().lower())
    def get_pool(self,name): return self.conn.storagePoolLookupByName(name)
    def list_networks(self): return sorted(self.conn.listAllNetworks(), key=lambda n:n.name().lower())
    def get_network(self,name): return self.conn.networkLookupByName(name)
    
    def free_pci_devices(self):
        """Get available PCI devices filtered for common passthrough devices (NVMe, NICs, GPUs)"""
        group_root = '/sys/kernel/iommu_groups'
        results = []
        
        if os.path.isdir(group_root):
            for g in sorted(os.listdir(group_root)):
                gpath = os.path.join(group_root, g, 'devices')
                try:
                    members = [m for m in os.listdir(gpath) if m.startswith('0000:')]
                except Exception:
                    continue
                if len(members) != 1:  # skip groups with more than one device
                    continue
                    
                dev = members[0]
                base = '/sys/bus/pci/devices'
                try:
                    with open(f'{base}/{dev}/vendor') as f: vendor = f.read().strip()
                    with open(f'{base}/{dev}/device') as f: device = f.read().strip()
                    with open(f'{base}/{dev}/class') as f: device_class = f.read().strip()
                    
                    # Filter for common passthrough devices
                    class_code = int(device_class.replace('0x', ''), 16)
                    base_class = (class_code >> 16) & 0xFF
                    sub_class = (class_code >> 8) & 0xFF
                    
                    device_type = None
                    if base_class == 0x01 and sub_class == 0x08:  # NVMe
                        device_type = "NVMe"
                    elif base_class == 0x02 and sub_class == 0x00:  # Ethernet
                        device_type = "Ethernet"
                    elif base_class == 0x03 and sub_class == 0x00:  # VGA
                        device_type = "Graphics"
                    
                    if device_type:
                        # Get real device name from lspci
                        device_name = self._get_pci_device_name(dev[5:])
                        if not device_name:
                            device_name = f"{device_type} Device"
                        
                        results.append({
                            'full': dev,
                            'addr': dev[5:],
                            'vendor': vendor,
                            'device': device,
                            'group': g,
                            'description': device_name,
                            'type': device_type
                        })
                except Exception:
                    continue
                    
        return results
    
    def _get_pci_device_name(self, pci_addr):
        """Get detailed device name from lspci output"""
        try:
            import subprocess
            result = subprocess.run(['lspci', '-s', pci_addr], capture_output=True, text=True, timeout=5)
            if result.returncode == 0 and result.stdout.strip():
                output = result.stdout.strip()
                # Parse lspci output: "01:00.0 VGA compatible controller: NVIDIA Corporation Device 1234 (rev a1)"
                if ': ' in output:
                    # Get everything after the device type
                    parts = output.split(': ', 1)
                    if len(parts) > 1:
                        device_info = parts[1].strip()
                        # Remove revision info if present
                        if ' (rev ' in device_info:
                            device_info = device_info.split(' (rev ')[0].strip()
                        return device_info
            return None
        except Exception:
            return None
    
    def next_disk_target(self, existing_targets:List[str]):
        used={t[2:] for t in existing_targets if t.startswith('vd') and len(t)==3}
        for c in 'abcdefghijklmnopqrstuvwxyz':
            if c not in used: return 'vd'+c
        return 'vdz'
    
    def define_pool_dir(self,name,path,autostart=True):
        xml=f"<pool type='dir'><name>{name}</name><target><path>{path}</path></target></pool>"
        p=self.conn.storagePoolDefineXML(xml,0); p.build(0); p.create(0)
        if autostart: p.setAutostart(1)
        return p
    
    def create_snapshot(self, domain_name: str, snap_name: str, description: str = ""):
        """Create a disk-only snapshot of a domain (excludes memory)"""
        domain = self.get_domain(domain_name)
        was_running = domain.isActive()
        
        if was_running:
            # For running VMs, use virsh command which can handle disk-only snapshots better
            try:
                import subprocess
                cmd = ['virsh', 'snapshot-create-as', domain_name, snap_name, '--disk-only', '--atomic']
                # Only add description if it's not empty
                if description and description.strip():
                    cmd.insert(3, description.strip())  # Insert description after snap_name
                subprocess.check_call(cmd)
                # Return a dummy object since virsh doesn't return the snapshot object
                return True
            except subprocess.CalledProcessError as e:
                raise RuntimeError(f"Failed to create snapshot via virsh: {e}")
        else:
            # For stopped VMs, use internal snapshots via libvirt API
            snap_xml = f"""<domainsnapshot>
                <name>{snap_name}</name>
                <description>{description}</description>
                <memory snapshot='no'/>
            </domainsnapshot>"""
            return domain.snapshotCreateXML(snap_xml)
    
    def list_snapshots(self, domain_name: str):
        """List all snapshots for a domain"""
        try:
            domain = self.get_domain(domain_name)
            return domain.listAllSnapshots()
        except Exception:
            return []
    
    def restore_snapshot(self, domain_name: str, snap_name: str):
        """Restore a domain to a snapshot"""
        domain = self.get_domain(domain_name)
        snapshot = domain.snapshotLookupByName(snap_name)
        domain.revertToSnapshot(snapshot)
    
    def delete_snapshot(self, domain_name: str, snap_name: str):
        """Delete a snapshot"""
        domain = self.get_domain(domain_name)
        snapshot = domain.snapshotLookupByName(snap_name)
        snapshot.delete()
    
    def backup_vm(self, domain_name: str, backup_path: str):
        """Create a full backup of a VM"""
        domain = self.get_domain(domain_name)
        was_running = domain.isActive()
        
        # Create snapshot for consistent backup
        snap_name = f"backup-{int(time.time())}"
        snapshot_created = False
        try:
            snapshot = self.create_snapshot(domain_name, snap_name, "Backup snapshot")
            snapshot_created = True
        except Exception as e:
            logger.warning(f"Could not create snapshot for backup: {e}")
            snapshot = None
        
        try:
            # Export VM definition
            xml = domain.XMLDesc(0)
            
            # Create backup directory
            backup_dir = os.path.join(backup_path, f"{domain_name}-{datetime.datetime.now().strftime('%Y%m%d-%H%M%S')}")
            os.makedirs(backup_dir, exist_ok=True)
            
            # Save domain XML
            with open(os.path.join(backup_dir, 'domain.xml'), 'w') as f:
                f.write(xml)
            
            # Copy disk files
            import xml.etree.ElementTree as ET
            root = ET.fromstring(xml)
            disk_files = []
            
            for disk in root.findall('.//devices/disk'):
                source = disk.find('source')
                if source is not None and 'file' in source.attrib:
                    disk_path = source.get('file')
                    if disk_path:
                        disk_name = os.path.basename(disk_path)
                        backup_disk_path = os.path.join(backup_dir, disk_name)
                        
                        # Use qemu-img to copy with compression
                        subprocess.check_call([
                            'sudo', 'qemu-img', 'convert', '-t', 'none', '-O', 'qcow2',
                            disk_path, backup_disk_path
                        ])
                        disk_files.append(disk_name)
            
            # Create backup manifest
            manifest = {
                'domain_name': domain_name,
                'backup_time': datetime.datetime.now().isoformat(),
                'was_running': was_running,
                'disk_files': disk_files
            }
            
            with open(os.path.join(backup_dir, 'manifest.json'), 'w') as f:
                json.dump(manifest, f, indent=2)
            
            return backup_dir
            
        finally:
            # Clean up snapshot if one was created
            if snapshot_created:
                try:
                    if was_running:
                        # For virsh-created snapshots, delete via command
                        subprocess.check_call(['sudo', 'virsh', 'snapshot-delete', domain_name, snap_name])
                    else:
                        # For libvirt API snapshots, use the object
                        if hasattr(snapshot, 'delete') and callable(snapshot.delete):
                            snapshot.delete()
                except Exception:
                    pass
    
    def restore_vm_backup(self, backup_path: str, new_name: str = None):
        """Restore a VM from backup"""
        manifest_path = os.path.join(backup_path, 'manifest.json')
        with open(manifest_path, 'r') as f:
            manifest = json.load(f)
        
        domain_xml_path = os.path.join(backup_path, 'domain.xml')
        with open(domain_xml_path, 'r') as f:
            xml = f.read()
        
        # Modify XML if new name provided
        if new_name:
            import xml.etree.ElementTree as ET
            root = ET.fromstring(xml)
            name_elem = root.find('name')
            if name_elem is not None:
                name_elem.text = new_name
            xml = ET.tostring(root, encoding='unicode')
        
        # Copy disk files back
        for disk_file in manifest['disk_files']:
            source_path = os.path.join(backup_path, disk_file)
            # Determine target pool and copy
            pools = self.list_pools()
            if pools:
                pool = pools[0]  # Use first available pool
                import xml.etree.ElementTree as ET
                proot = ET.fromstring(pool.XMLDesc(0))
                pool_path = proot.findtext('.//target/path') or '/var/lib/libvirt/images'
                
                target_name = new_name or manifest['domain_name']
                target_dir = os.path.join(pool_path, target_name)
                os.makedirs(target_dir, exist_ok=True)
                
                target_path = os.path.join(target_dir, disk_file)
                subprocess.check_call(['sudo', 'cp', source_path, target_path])
        
        # Define the domain
        self.conn.defineXML(xml)

PAGE_TEMPLATE="<!DOCTYPE html><html><head><meta charset='utf-8'><title>{title}</title><style>{css}</style><script>{js}</script><script>if(!window.openModal){{window.openModal=function(id){{var m=document.getElementById(id);if(m){{m.hidden=false;m.style.display='flex';}}}};window.closeModal=function(id){{var m=document.getElementById(id);if(m){{m.hidden=true;}}}};}}</script></head><body class='{theme}'><header><h1>🖥️ VM Manager</h1><nav><a href='/'>Dashboard</a> | <a href='/?images=1'>Images</a> | <a href='/?storage=1'>Storage</a> | <a href='/?networks=1'>Networks</a> | <a href='/?hardware=1'>Hardware</a> | <a href='/?backups=1'>Backups</a> | <button class='theme-toggle' onclick='toggleTheme()'>🌙</button></nav></header><main>{body}</main></body></html>"

CSS=r""":root{--bg:#0f1115;--fg:#e6e8ea;--accent:#4da3ff;--danger:#ff4d5d;--ok:#3ecf8e;--warn:#ffb347;--card:#1b1f27;--border:#2a303b;--overlay:#000c;--success:#22c55e;--info:#06b6d4;--muted:#6b7280}
body.light{--bg:#ffffff;--fg:#1f2937;--accent:#2563eb;--danger:#dc2626;--ok:#16a34a;--warn:#d97706;--card:#f9fafb;--border:#e5e7eb;--overlay:#0009;--success:#059669;--info:#0891b2;--muted:#6b7280}
*{box-sizing:border-box}
body{margin:0;font-family:system-ui,-apple-system,'Segoe UI',Roboto;background:var(--bg);color:var(--fg);font-size:13px;line-height:1.35;transition:background-color 0.3s,color 0.3s}
header{background:var(--card);padding:12px 18px;display:flex;align-items:center;justify-content:space-between;border-bottom:1px solid var(--border);box-shadow:0 1px 3px var(--overlay)}
h1{margin:0;font-size:18px;display:flex;align-items:center;gap:8px}
nav{display:flex;align-items:center;gap:12px;flex-wrap:wrap}
nav a{color:var(--accent);text-decoration:none;padding:6px 12px;border-radius:6px;transition:background-color 0.2s}
nav a:hover{background:var(--overlay);text-decoration:none}
.theme-toggle{background:var(--border);color:var(--fg);border:none;padding:6px 10px;border-radius:6px;cursor:pointer;font-size:14px}
.theme-toggle:hover{background:var(--accent);color:#fff}
main{padding:14px 14px 40px}
@media (min-width:900px){
    body{font-size:15px;line-height:1.45}
    header{padding:16px 38px}
    h1{font-size:22px}
    main{padding:34px 46px;max-width:1500px;margin:0 auto}
    table{font-size:14px}
}
a.button,button,input[type=submit]{background:var(--accent);color:#fff;border:none;padding:6px 14px;border-radius:4px;cursor:pointer;font-size:14px;text-decoration:none;display:inline-block;width:auto;transition:background-color 0.2s}
a.button:hover,button:hover,input[type=submit]:hover{background:var(--info)}
a.small,button.small{font-size:12px;padding:4px 10px}
a.danger,button.danger{background:var(--danger)}
a.danger:hover,button.danger:hover{background:#ef4444}
a.secondary,button.secondary{background:var(--muted)}
a.secondary:hover,button.secondary:hover{background:#374151}
a.success,button.success{background:var(--success)}
a.success:hover,button.success:hover{background:#059669}
button.close{background:#333;padding:2px 6px;font-size:12px;margin-left:8px}
.badge{display:inline-block;padding:2px 6px;border-radius:3px;font-size:11px;font-weight:600}
.badge.running{background:var(--success);color:#fff}
.badge.shutoff{background:var(--warn);color:#fff}
.badge.paused{background:var(--info);color:#fff}
table{width:100%;border-collapse:collapse;margin-top:10px;overflow-x:auto;background:var(--card);border-radius:8px;overflow:visible}
th,td{padding:8px 12px;border-bottom:1px solid var(--border);font-size:13px;text-align:left;vertical-align:top}
th{background:var(--border);font-weight:600}
tr:hover{background:var(--overlay)}
td:has(.select-enh){overflow:visible;position:relative}
.status-running{color:var(--ok);font-weight:600}
.status-shutoff{color:var(--warn)}
.card{background:var(--card);padding:16px;border:1px solid var(--border);border-radius:8px;margin-bottom:18px;box-shadow:0 1px 3px var(--overlay)}
.card h3{margin-top:0;color:var(--accent)}
.card-grid{display:grid;grid-template-columns:repeat(auto-fit,minmax(300px,1fr));gap:20px}
pre{background:var(--bg);padding:12px;border:1px solid var(--border);border-radius:6px;overflow:auto;font-size:12px}
code{background:var(--bg);padding:2px 4px;border-radius:3px;font-size:12px}
form.inline{display:inline}
input:not([type=submit]),select,textarea{background:var(--bg);border:1px solid var(--border);color:var(--fg);border-radius:4px;padding:6px 8px;font-size:13px;margin-bottom:8px;width:100%;transition:border-color 0.2s}
input:focus,select:focus,textarea:focus{outline:none;border-color:var(--accent)}
label{display:block;margin-bottom:8px;font-weight:500}
ul{margin:6px 0 10px;padding-left:18px}
li{margin-bottom:4px}
details summary{cursor:pointer;padding:6px 0;font-weight:500}
details[open] summary{margin-bottom:8px}
footer{opacity:.7;text-align:center;padding:26px 0 40px;font-size:12px}
hr{border:none;border-top:1px solid var(--border);margin:18px 0}
.inline-note{font-size:11px;opacity:.8;margin-top:4px}
.inline-note.error{color:#ff4444;opacity:1;font-weight:500}
.alert{padding:12px;border-radius:6px;margin-bottom:16px}
.alert.info{background:#0ea5e9;color:#fff}
.alert.success{background:var(--success);color:#fff}
.alert.warning{background:var(--warn);color:#fff}
.alert.error{background:var(--danger);color:#fff}
/* Responsive layout helpers */
.two-col{display:block}
@media (min-width:900px){.two-col{display:grid;grid-template-columns:1fr 1fr;gap:26px}}
@media (min-width:1300px){.two-col{grid-template-columns:1.1fr .9fr}}
.modal[hidden]{display:none!important}
.modal{position:fixed;top:0;left:0;width:100%;height:100%;background:var(--overlay);display:flex;align-items:center;justify-content:center;z-index:2000;padding:20px}
.modal .panel{background:var(--card);border:1px solid var(--border);border-radius:10px;max-width:680px;width:100%;max-height:90vh;overflow-y:auto;padding:20px;box-shadow:0 8px 32px var(--overlay);position:relative}
.modal h3{margin-top:0;color:var(--accent)}
#console-expanded{position:fixed;top:10%;left:10%;width:80%;height:80%;background:var(--card);border:1px solid var(--border);border-radius:10px;z-index:3000;padding:20px;box-shadow:0 8px 32px var(--overlay);display:none}
#console-expanded .console-header{display:flex;justify-content:space-between;align-items:center;margin-bottom:15px;color:var(--accent)}
#console-expanded canvas{width:100%;height:calc(100% - 60px);background:#000;border:1px solid var(--border);border-radius:4px}
.select-enh{position:relative;display:block}
.select-enh select{display:none}
.select-enh .sel-display{background:var(--bg);border:1px solid var(--border);padding:8px 12px;border-radius:6px;cursor:pointer;position:relative;font-size:14px}
.select-enh .sel-display:after{content:'\25BE';position:absolute;right:12px;opacity:.55;transition:.2s}
.select-enh.open .sel-display:after{transform:scaleY(-1)}
.select-enh .sel-options{position:absolute;left:0;right:0;top:100%;background:var(--bg);border:1px solid var(--border);border-radius:6px;margin-top:4px;max-height:260px;overflow:auto;display:none;z-index:9999;box-shadow:0 4px 12px var(--overlay)}
.select-enh.open .sel-options{display:block}
.select-enh .sel-options div{padding:8px 12px;cursor:pointer;transition:background-color 0.2s}
.select-enh .sel-options div:hover{background:var(--border)}
.grid-devs{display:grid;grid-template-columns:repeat(auto-fill,minmax(120px,1fr));gap:8px;margin:8px 0 4px}
.chip{background:var(--bg);border:1px solid var(--border);padding:6px 8px;border-radius:6px;font-size:12px;cursor:pointer;user-select:none;text-align:center;transition:all 0.2s}
.chip:hover{background:var(--border)}
.chip.sel{background:var(--accent);color:#fff;border-color:var(--accent)}
.disk-row{background:var(--bg);border:1px solid var(--border);padding:8px;margin:4px 0;border-radius:6px;cursor:pointer;transition:all 0.2s;position:relative}
.disk-row:hover{background:var(--border)}
.disk-row.sel{background:var(--accent);color:white;border-color:var(--accent)}
.disk-row .disk-actions{float:right;opacity:0.7}
.disk-row .disk-actions button{font-size:11px;padding:2px 6px;margin-left:4px}
.meter{background:var(--border);border:1px solid var(--border);height:14px;position:relative;border-radius:4px;overflow:hidden;margin:2px 0;min-width:120px}
.meter .fill{background:var(--accent);height:100%;width:0;transition:width .6s}
.meter.alt .fill{background:var(--ok)}
.meter.warn .fill{background:var(--warn)}
.meter.danger .fill{background:var(--danger)}
.progress-ring{width:40px;height:40px;transform:rotate(-90deg)}
.progress-ring circle{fill:transparent;stroke:var(--border);stroke-width:4}
.progress-ring .progress{stroke:var(--accent);stroke-linecap:round;transition:stroke-dasharray 0.3s}
.vm-layout{display:flex;gap:20px;align-items:flex-start}
.vm-main{flex:1;min-width:0}

.vm-console{background:var(--card);border:2px solid var(--border);border-radius:8px;overflow:hidden;transition:all 0.3s ease;position:relative;height:600px}
.vm-console.small{height:280px}
.vm-console canvas{max-width:100%;max-height:100%;object-fit:contain;display:block}
.vm-console .console-content{padding:4px;height:calc(100% - 40px);display:flex;align-items:center;justify-content:center;overflow:hidden}
.vm-console:not(.small) .console-content{height:calc(100% - 60px)}
.vm-console.expanded{position:fixed;top:0;left:0;width:100vw;height:100vh;max-width:none;max-height:none;z-index:1000;background:var(--bg);border:none;border-radius:0;box-shadow:none}
.vm-console.expanded canvas{width:100%!important;height:calc(100vh - 40px)!important}
.vm-console.expanded .console-header{position:absolute;top:0;right:0;z-index:1001;background:rgba(0,0,0,0.8);color:white;padding:8px 12px;border-radius:0 0 0 4px;cursor:pointer}
.vm-console.expanded .console-header::before{content:'✕ Close Fullscreen'}
.vm-console.fullsize{position:fixed;top:50px;left:50px;right:50px;bottom:50px;width:auto;height:auto;z-index:1000;box-shadow:0 8px 32px var(--overlay)}
.console-header{background:var(--muted);padding:8px 12px;display:flex;justify-content:space-between;align-items:center;cursor:pointer;user-select:none;border-bottom:1px solid var(--border);font-size:12px;transition:background 0.2s}
.console-header:hover{background:var(--accent);color:var(--bg)}
.console-content{height:calc(100% - 32px);background:#000;overflow:hidden;position:relative}
.console-canvas{width:100%;height:100%;object-fit:contain;cursor:crosshair;transition:border 0.1s;image-rendering:auto;image-rendering:-webkit-optimize-contrast;}
.console-canvas:focus{outline:2px solid var(--accent);cursor:text}
.console-controls{position:absolute;top:4px;right:4px;display:flex;gap:4px;opacity:0.7}
.console-controls:hover{opacity:1}
.console-controls button{padding:2px 6px;font-size:11px}
.stats-grid{display:grid;grid-template-columns:repeat(auto-fit,minmax(200px,1fr));gap:16px;margin:16px 0}
.stat-card{background:var(--bg);border:1px solid var(--border);border-radius:6px;padding:12px;text-align:center}
.stat-value{font-size:24px;font-weight:600;color:var(--accent)}
.stat-label{font-size:12px;opacity:0.8;margin-top:4px}
"""
JS=r"""// Enhanced UI with theme switching, better interactions, and new features
(function(){
function safe(f){try{f();}catch(e){console.error(e);}}

// Theme management
function toggleTheme(){
    const body = document.body;
    const isLight = body.classList.contains('light');
    if(isLight){
        body.classList.remove('light');
        localStorage.setItem('theme', 'dark');
    } else {
        body.classList.add('light');
        localStorage.setItem('theme', 'light');
    }
}
window.toggleTheme = toggleTheme;

// Initialize theme
function initTheme(){
    const savedTheme = localStorage.getItem('theme');
    if(savedTheme === 'light'){
        document.body.classList.add('light');
    }
}

// Modal management
window.openModal=function(id){const m=document.getElementById(id); if(!m) return true; m.hidden=false; m.style.display='flex'; safe(enhanceSelects); return true;};
window.closeModal=function(id){const m=document.getElementById(id); if(!m) return; m.hidden=true;};

// Enhanced select dropdowns
function enhanceSelects(){
    // Enhanced dropdowns with class 'enh'
    document.querySelectorAll('select.enh:not([data-enhanced])').forEach(sel=>{
        sel.dataset.enhanced='1';sel.style.display='none';
        const wrap=document.createElement('div');wrap.className='select-enh';wrap.tabIndex=0;
        const disp=document.createElement('div');disp.className='sel-display';
        disp.textContent=sel.options[sel.selectedIndex]?sel.options[sel.selectedIndex].text:'Select...';
        const optBox=document.createElement('div');optBox.className='sel-options';
        [...sel.options].forEach((o,i)=>{
            const div=document.createElement('div');div.textContent=o.text;div.dataset.val=o.value;
            div.addEventListener('click',(e)=>{e.stopPropagation();e.preventDefault();sel.selectedIndex=i;sel.value=o.value;disp.textContent=o.text;wrap.classList.remove('open');sel.dispatchEvent(new Event('change'));});
            optBox.appendChild(div);
        });
        function toggle(e){
            if(e) {e.stopPropagation(); e.preventDefault();}
            document.querySelectorAll('.select-enh.open').forEach(w=>w!==wrap&&w.classList.remove('open'));
            wrap.classList.toggle('open');
        }
        disp.addEventListener('click',toggle);
        disp.addEventListener('mousedown', e => e.preventDefault()); // Prevent focus issues
        wrap.addEventListener('keydown',e=>{if(e.key==='Enter'||e.key===' '){e.preventDefault();toggle();}});
        wrap.appendChild(disp);wrap.appendChild(optBox);sel.after(wrap);
    });
    
    // Also enhance ALL regular select elements
    document.querySelectorAll('select:not(.enh):not([data-enhanced])').forEach(sel=>{
        if(sel.closest('.select-enh') || sel.style.display === 'none') return; // Skip if already enhanced
        sel.dataset.enhanced='1';
        sel.style.display='none';
        const wrap=document.createElement('div');wrap.className='select-enh';wrap.tabIndex=0;
        const disp=document.createElement('div');disp.className='sel-display';
        disp.textContent=sel.options[sel.selectedIndex]?sel.options[sel.selectedIndex].text:'Select...';
        const optBox=document.createElement('div');optBox.className='sel-options';
        [...sel.options].forEach((o,i)=>{
            const div=document.createElement('div');div.textContent=o.text;div.dataset.val=o.value;
            div.addEventListener('click',(e)=>{e.stopPropagation();e.preventDefault();sel.selectedIndex=i;sel.value=o.value;disp.textContent=o.text;wrap.classList.remove('open');sel.dispatchEvent(new Event('change'));});
            optBox.appendChild(div);
        });
        function toggle(e){
            if(e) {e.stopPropagation(); e.preventDefault();}
            document.querySelectorAll('.select-enh.open').forEach(w=>w!==wrap&&w.classList.remove('open'));
            wrap.classList.toggle('open');
        }
        disp.addEventListener('click',toggle);
        disp.addEventListener('mousedown', e => e.preventDefault()); // Prevent focus issues
        wrap.addEventListener('keydown',e=>{if(e.key==='Enter'||e.key===' '){e.preventDefault();toggle();}});
        wrap.appendChild(disp);wrap.appendChild(optBox);sel.after(wrap);
    });
}
window.enhanceSelects=enhanceSelects;

// Close dropdowns and modals on outside click
document.addEventListener('click',e=>{
    if(e.target.classList&&e.target.classList.contains('modal')){e.target.hidden=true;}
    // Only close dropdowns if click is truly outside and not on a dropdown element
    if(!e.target.closest('.select-enh') && !e.target.classList.contains('sel-display') && !e.target.classList.contains('sel-options')) {
        document.querySelectorAll('.select-enh.open').forEach(w=>w.classList.remove('open'));
    }
});

// Device selection for forms
window.updateDevField=function(el){
    const wrap=el.closest('.panel, .card'); if(!wrap) return;
    const sel=[...wrap.querySelectorAll('.disk-row.sel, .chip.sel')].map(c=>c.dataset.dev);
    let box=wrap.querySelector('.devices-box');
    if(!box){box=document.createElement('div');box.className='devices-box';wrap.appendChild(box);}
    box.innerHTML='';
    sel.forEach(v=>{const i=document.createElement('input');i.type='hidden';i.name='devices';i.value=v;box.appendChild(i);});
};

// Disk row clicking for selection
window.toggleDiskSelection=function(el){
    if(el.classList.contains('sel')){
        el.classList.remove('sel');
    } else {
        el.classList.add('sel');
    }
    window.updateDevField(el);
};

// Wipe disk function
window.wipeDisk=function(device, button){
    if(!confirm(`Really wipe all data on ${device}? This cannot be undone!`)) return;
    button.disabled = true;
    button.textContent = 'Wiping...';
    fetch('/wipe_disk', {
        method: 'POST',
        headers: {'Content-Type': 'application/x-www-form-urlencoded'},
        body: 'device=' + encodeURIComponent(device)
    }).then(r => r.json()).then(data => {
        if(data.success) {
            // Update UI to show "clean" status without popup
            const deviceRow = document.querySelector(`[data-dev="${device}"]`);
            if(deviceRow) {
                const actionsDiv = deviceRow.querySelector('.disk-actions');
                if(actionsDiv && !actionsDiv.querySelector('.clean-status')) {
                    actionsDiv.insertAdjacentHTML('afterbegin', '<span class="clean-status" style="color:#4CAF50;font-weight:bold;margin-right:8px;">CLEAN</span>');
                }
                // Remove device from selection if it was selected
                deviceRow.classList.remove('sel');
                // Update hidden device fields
                window.updateDevField && window.updateDevField(deviceRow);
            }
            // Don't reload page to keep modal open
            button.disabled = false;
            button.textContent = 'Wipe';
        } else {
            alert(`Failed to wipe ${device}: ${data.error}`);
            button.disabled = false;
            button.textContent = 'Wipe';
        }
    }).catch(e => {
        alert(`Error wiping disk: ${e}`);
        button.disabled = false;
        button.textContent = 'Wipe';
    });
};

// Bulk wipe selected devices function
window.bulkWipeSelected=function(modalType){
    const container = document.getElementById(modalType + '-devices-container');
    if(!container) return;
    
    // Get all selected device rows (those with 'sel' class)
    const selectedRows = container.querySelectorAll('.disk-row.sel');
    const devices = [];
    
    selectedRows.forEach(row => {
        const device = row.getAttribute('data-dev');
        if(device) devices.push(device);
    });
    
    if(devices.length === 0) {
        alert('No devices selected. Please click on drives to select them first.');
        return;
    }
    
    if(!confirm(`Really wipe all data on ${devices.length} selected device(s)? This cannot be undone!\n\nDevices: ${devices.join(', ')}`)) return;
    
    // Wipe each selected device
    let completedCount = 0;
    const totalCount = devices.length;
    
    devices.forEach(device => {
        const deviceRow = document.querySelector(`[data-dev="${device}"]`);
        const button = deviceRow ? deviceRow.querySelector('button') : null;
        
        if(button) {
            button.disabled = true;
            button.textContent = 'Wiping...';
        }
        
        fetch('/wipe_disk', {
            method: 'POST',
            headers: {'Content-Type': 'application/x-www-form-urlencoded'},
            body: 'device=' + encodeURIComponent(device)
        }).then(r => r.json()).then(data => {
            completedCount++;
            
            if(data.success) {
                // Update UI to show "clean" status
                if(deviceRow) {
                    const actionsDiv = deviceRow.querySelector('.disk-actions');
                    if(actionsDiv && !actionsDiv.querySelector('.clean-status')) {
                        actionsDiv.insertAdjacentHTML('afterbegin', '<span class="clean-status" style="color:#4CAF50;font-weight:bold;margin-right:8px;">CLEAN</span>');
                    }
                    // Remove device from selection since it was wiped
                    deviceRow.classList.remove('sel');
                    // Update hidden device fields
                    window.updateDevField && window.updateDevField(deviceRow);
                }
                if(button) {
                    button.disabled = false;
                    button.textContent = 'Wipe';
                }
            } else {
                if(button) {
                    button.disabled = false;
                    button.textContent = 'Wipe';
                    button.style.color = '#ff4444';
                    button.title = `Failed: ${data.error}`;
                }
            }
            
            // Show completion message only when all are done
            if(completedCount === totalCount) {
                const successCount = document.querySelectorAll('.clean-status').length;
                console.log(`Bulk wipe completed: ${successCount}/${totalCount} devices wiped successfully`);
            }
        }).catch(e => {
            completedCount++;
            if(button) {
                button.disabled = false;
                button.textContent = 'Wipe';
                button.style.color = '#ff4444';
                button.title = `Error: ${e}`;
            }
        });
    });
};

// Toggle USB devices visibility
window.toggleUSBDevices=function(modalType){
    const checkbox = document.getElementById(modalType + '-show-usb');
    const noUsbDiv = document.getElementById(modalType + '-devices-no-usb');
    const allDevicesDiv = document.getElementById(modalType + '-devices-all');
    
    if(!checkbox || !noUsbDiv || !allDevicesDiv) return;
    
    const showUSB = checkbox.checked;
    
    if(showUSB) {
        noUsbDiv.style.display = 'none';
        allDevicesDiv.style.display = 'block';
    } else {
        noUsbDiv.style.display = 'block';
        allDevicesDiv.style.display = 'none';
        
        // Deselect any USB devices that were selected
        const usbRows = allDevicesDiv.querySelectorAll('.disk-row[data-is-usb="true"]');
        usbRows.forEach(row => {
            if(row.classList.contains('sel')) {
                row.classList.remove('sel');
                window.updateDevField && window.updateDevField(row);
            }
        });
    }
};

// Real-time updates with better error handling
function pollMd(){
    fetch('/mdstatus').then(r=>r.json()).then(d=>{
        if(!d.devices)return;
        d.devices.forEach(st=>{
            const row=document.getElementById('md_'+st.name);
            if(row){
                const bar=row.querySelector('.bar');
                if(bar){
                    bar.style.width=st.percent+'%';
                    bar.textContent=st.percent.toFixed(1)+'%';
                    bar.title=st.percent.toFixed(1)+'% '+(st.eta||'');
                }
                ['eta','state','speed'].forEach(k=>{
                    const el=row.querySelector('.'+k);
                    if(el && st[k]) el.textContent=st[k];
                });
                const speedSel=row.querySelector('select[name=speed]');
                if(speedSel&&!speedSel.dataset.bound){
                    speedSel.dataset.bound='1';
                    speedSel.onchange=()=>{fetch('/mdstatus?set='+st.name+'&mode='+speedSel.value).then(()=>pollMd());};
                }
            }
        });
        setTimeout(pollMd,5000);
    }).catch(()=>setTimeout(pollMd,7000));
}

function pollVmStats(){
    fetch('/vmstats').then(r=>r.json()).then(d=>{
        // Dashboard table update
        d.forEach(v=>{
            const row=document.querySelector("tr[data-vm='"+v.name+"']");
            if(row){
                const map={
                    cpu:v.cpu.toFixed(1)+'%',
                    mem:v.mem_used_h+' / '+v.mem_max_h,
                    mem_pct:v.mem_pct.toFixed(1)+'%',
                    io:(v.rd_kbps/1024).toFixed(1)+'MB/s / '+(v.wr_kbps/1024).toFixed(1)+' MB/s'
                    // Removed storage update - keep server-rendered values
                };
                Object.entries(map).forEach(([cls,val])=>{
                    const el=row.querySelector('.'+cls);
                    if(el) el.textContent=val;
                });
            }
        });
        
        // Performance page table
        const perf=document.getElementById('perf_vm_table');
        if(perf){
            const tbody=perf.querySelector('tbody');
            if(tbody){
                tbody.innerHTML='';
                const maxStorage=Math.max(1,...d.map(v=>v.storage));
                const maxIO=Math.max(1,...d.map(v=>v.rd_kbps+v.wr_kbps));
                d.forEach(v=>{
                    const ioTot=v.rd_kbps+v.wr_kbps;
                    const ioPct=(ioTot/maxIO)*100;
                    const storagePct=(v.storage/maxStorage)*100;
                    tbody.innerHTML+=`<tr data-vm='${v.name}'>
                        <td><a href='/?domain=' + encodeURIComponent(v.name) + ''>${v.name}</a></td>
                        <td><div class='meter'><div class='fill' style='width:${v.cpu.toFixed(1)}%'></div></div><div class='inline-note'>${v.cpu.toFixed(1)}%</div></td>
                        <td><div class='meter alt'><div class='fill' style='width:${v.mem_pct.toFixed(1)}%'></div></div><div class='inline-note'>${v.mem_used_h} / ${v.mem_max_h} (${v.mem_pct.toFixed(1)}%)</div></td>
                        <td><div class='meter'><div class='fill' style='width:${ioPct.toFixed(1)}%'></div></div><div class='inline-note'>${v.rd_kbps.toFixed(1)}R / ${v.wr_kbps.toFixed(1)}W KB/s</div></td>
                        <td><div class='meter'><div class='fill' style='width:${storagePct.toFixed(1)}%'></div></div><div class='inline-note'>${v.storage_h}</div></td>
                    </tr>`;
                });
            }
        }
        setTimeout(pollVmStats,5000);
    }).catch(()=>setTimeout(pollVmStats,7000));
}

function pollHostStats(){
    const el=document.getElementById('host_perf');
    if(!el) return;
    fetch('/hoststats').then(r=>r.json()).then(d=>{
        const cpu=el.querySelector('.cpu_val');
        if(cpu) cpu.textContent=d.cpu_pct.toFixed(1)+'%';
        const cpuBar=el.querySelector('.host_cpu_fill');
        if(cpuBar) cpuBar.style.width=d.cpu_pct.toFixed(1)+'%';
        
        const mem=el.querySelector('.mem_val');
        if(mem) mem.textContent=d.mem_used_h+' / '+d.mem_total_h+' ('+d.mem_pct.toFixed(1)+'%)';
        const memBar=el.querySelector('.host_mem_fill');
        if(memBar) memBar.style.width=d.mem_pct.toFixed(1)+'%';
        
        const body=el.querySelector('.disks');
        if(body){
            body.innerHTML='';
            d.disks.forEach(ds=>{
                const tr=document.createElement('tr');
                tr.innerHTML='<td>'+ds.mount+'</td><td>'+ds.dev+'</td><td>'+ds.rd_kbps.toFixed(1)+'</td><td>'+ds.wr_kbps.toFixed(1)+'</td>';
                body.appendChild(tr);
            });
        }
        setTimeout(pollHostStats,5000);
    }).catch(()=>setTimeout(pollHostStats,7000));
}

function pollImageProgress(){
    // Find progress bars created by the specific inline script on images page
    const progressBar = document.getElementById('pb');
    const progressText = document.getElementById('pbtxt');
    
    if(!progressBar || !progressText) return; // No image import in progress
    
    // Check if there's already a poll function running (created by inline script)
    // If so, don't interfere with it
    if(window.imagePollRunning) return;
    
    // Otherwise, this is likely leftover from a previous import
    // Check once if the progress is done and clean up
    const progressId = new URLSearchParams(window.location.search).get('progress') || 
                      document.querySelector('[data-pid]')?.getAttribute('data-pid');
    
    if(progressId) {
        function checkProgress() {
            fetch('/api/progress?id=' + progressId)
                .then(r => r.json())
                .then(data => {
                    if(data.error) {
                        progressText.textContent = 'Error: ' + data.error;
                        return;
                    }
                    progressBar.style.width = data.pct + '%';
                    progressText.textContent = data.pct + '% - ' + data.msg;
                    if(data.status === 'done') {
                        progressText.textContent = 'Complete!';
                        setTimeout(() => {
                            window.location.href = '/?images=1';
                        }, 1500);
                        return;
                    } else if(data.status === 'error') {
                        progressText.textContent = 'Error: ' + data.msg;
                        return;
                    } else {
                        setTimeout(checkProgress, 1000);
                    }
                })
                .catch(e => {
                    console.error('Progress check error:', e);
                    setTimeout(checkProgress, 1500);
                });
        }
        checkProgress();
    }
}

// Notification system
window.showNotification = function(message, type = 'info') {
    const notification = document.createElement('div');
    notification.className = `alert ${type}`;
    notification.style.cssText = 'position:fixed;top:20px;right:20px;z-index:3000;min-width:300px;animation:slideIn 0.3s ease;';
    notification.innerHTML = message + '<button onclick="this.parentElement.remove()" style="float:right;background:none;border:none;color:inherit;cursor:pointer;font-size:16px;">&times;</button>';
    document.body.appendChild(notification);
    setTimeout(() => notification.remove(), 5000);
};

// Modal binding with better error handling
function bindModals(){
    document.querySelectorAll('[data-modal]').forEach(el=>{
        if(el.dataset.bound) return;
        el.dataset.bound='1';
        el.addEventListener('click',e=>{
            e.preventDefault();
            openModal(el.dataset.modal);
        });
    });
}

// Initialize everything
function init(){
    safe(initTheme);
    safe(enhanceSelects);
    safe(()=>{const fb=document.getElementById('inline_ingest'); if(fb) fb.remove();});
    safe(pollMd);
    safe(pollVmStats);
    safe(pollHostStats);
    safe(pollImageProgress);
    bindModals();
    window.debugModals=bindModals;
}

// Add CSS animation
const style = document.createElement('style');
style.textContent = '@keyframes slideIn{from{transform:translateX(100%);}to{transform:translateX(0);}}';
document.head.appendChild(style);

// Auto-refresh VM status
// Generate a random MAC address and fill the specified field
function generateMacAddress(view = 'desktop') {
    const prefix = '02'; // Locally administered, unicast
    let mac = prefix;
    
    // Generate 5 more random bytes
    for (let i = 0; i < 5; i++) {
        mac += ':' + Math.floor(Math.random() * 256).toString(16).padStart(2, '0');
    }
    
    // Set the value in the appropriate field based on view
    const fieldId = view === 'mobile' ? 'nic_mac_mobile' : 'nic_mac';
    const macField = document.getElementById(fieldId);
    if (macField) {
        macField.value = mac.toLowerCase();
    }
}

// MAC address fields are left empty by default
// Users can click "Generate" button or enter manually

function autoRefreshStatus() {
    // Only refresh on dashboard and VM detail pages
    const isDashboard = window.location.pathname === '/' && !window.location.search.includes('domain=');
    const isVMDetail = window.location.search.includes('domain=');
    
    if (isDashboard || isVMDetail) {
        // Refresh every 1 second for dashboard, 5 seconds for VM detail
        const interval = isDashboard ? 1000 : 5000;
        setTimeout(() => {
            refreshVMStatus();
            autoRefreshStatus();
        }, interval);
    }
}

document.addEventListener('DOMContentLoaded',init);
document.addEventListener('DOMContentLoaded', autoRefreshStatus);
window.addEventListener('load',init);
})();"""

# Simple in-memory progress tracking for async image creation
PROGRESS={}  # id -> {status: starting|running|done|error, pct:int, msg:str}

def start_image_ingest(pid:str,pool_name:str,src:str,out:str):
    PROGRESS[pid]={'status':'starting','pct':0,'msg':'Initializing...','ts':time.time()}
    def worker():
        nfs_mount_point = None  # Track NFS mount outside try block
        temp_dir = None  # Track temp directory
        try:
            import xml.etree.ElementTree as ET
            lv=LV(); pool=lv.get_pool(pool_name)
            pxml=pool.XMLDesc(0); proot=ET.fromstring(pxml); pool_path=proot.findtext('.//target/path') or '/var/lib/libvirt/images'
            images_dir=os.path.join(pool_path,'images'); os.makedirs(images_dir,exist_ok=True)
            
            # Create temporary directory manually for better cleanup control
            temp_dir = tempfile.mkdtemp(prefix='vm_import_')
            local_path=None
            PROGRESS[pid]['status'] = 'running'
            PROGRESS[pid]['pct'] = 5
            PROGRESS[pid]['msg'] = 'Connecting to source...'
            
            if src.startswith('http://') or src.startswith('https://'):
                import urllib.request
                lp=os.path.join(temp_dir,'download')
                PROGRESS[pid]['msg'] = 'Downloading from URL...'
                urllib.request.urlretrieve(src, lp)
                local_path=lp
            elif src.startswith('nfs://'):
                # Advanced NFS handling: enumerate exports, mount best match, unmount later
                nfs_spec=src[6:]
                if '/' not in nfs_spec:
                    raise RuntimeError('Invalid nfs URL (nfs://host/path/to/file)')
                host, path_part=nfs_spec.split('/',1)
                full_path='/' + path_part
                exports=[]
                PROGRESS[pid]['msg'] = 'Connecting to NFS server...'
                try:
                    ex=subprocess.check_output(['sudo', 'showmount','-e',host], text=True, timeout=8)
                    for ln in ex.splitlines()[1:]:
                        ln=ln.strip()
                        if not ln: continue
                        exp=ln.split()[0]
                        if not exp.startswith('/'):
                            exp='/'+exp
                        exports.append(exp.rstrip('/'))
                except FileNotFoundError:
                    pass  # showmount not available, continue with fallback
                except subprocess.TimeoutExpired:
                    pass  # timeout, continue with fallback
                # choose longest export that prefixes full_path
                export=None; inner_rel=None
                if exports:
                    for e in sorted(exports,key=len,reverse=True):
                        if full_path==e or full_path.startswith(e+'/'):
                            export=e
                            inner_rel=full_path[len(e):].lstrip('/')
                            break
                if not export:
                    # fall back: assume first segment is export
                    seg=full_path.strip('/').split('/',1)[0]
                    export='/'+seg
                    inner_rel=full_path[len(export):].lstrip('/')
                if not inner_rel:
                    raise RuntimeError('No file specified inside NFS export')
                
                # Create mount point in temp directory
                nfs_mount_point=os.path.join(temp_dir,'mnt'); os.makedirs(nfs_mount_point,exist_ok=True)
                PROGRESS[pid]['msg'] = 'Mounting NFS share...'
                mount_ok=False
                for vers in ('4.2','4','3',''):  # attempt different NFS versions
                    opts=['-o',f'ro,soft,timeo=5,retrans=2'+(f',vers={vers}' if vers else '')]
                    try:
                        subprocess.check_call(['sudo','mount','-t','nfs']+opts+[f'{host}:{export}',nfs_mount_point], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
                        mount_ok=True
                        break
                    except subprocess.CalledProcessError:
                        continue
                if not mount_ok:
                    raise RuntimeError('NFS mount failed for all versions')
                candidate=os.path.join(nfs_mount_point, inner_rel)
                if not os.path.isfile(candidate):
                    raise RuntimeError('File not found in mounted export')
                # keep mount during convert
                local_path=candidate
            else:
                if not os.path.exists(src): raise RuntimeError('Source path not found')
                local_path=src
            if os.path.isdir(local_path): raise RuntimeError('Source is directory')
            
            # Determine output filename and format based on source
            if local_path.lower().endswith('.iso'):
                # For ISO files, preserve the original format and extension
                dest_file = os.path.join(images_dir, f"{out}.iso")
                convert_needed = False
            else:
                # For other files, convert to qcow2 format
                dest_file = os.path.join(images_dir, f"{out}.qcow2")
                convert_needed = True
            
            # Check if file already exists to prevent conflicts
            if os.path.exists(dest_file):
                dest_basename = os.path.basename(dest_file)
                raise RuntimeError(f'Output file already exists: {dest_basename}')
            # Add file locking to prevent concurrent imports of same name
            lock_file = dest_file + '.lock'
            if os.path.exists(lock_file):
                dest_basename = os.path.basename(dest_file)
                raise RuntimeError(f'Another import of {dest_basename} is in progress')
            
            # Create lock file
            with open(lock_file, 'w') as lf:
                lf.write(str(pid))
            
            try:
                # Estimate size for progress (best-effort)
                try:
                    total=os.path.getsize(local_path)
                except Exception:
                    total=None
                
                action_verb = 'Copying' if not convert_needed else 'Converting'
                PROGRESS[pid]['msg'] = f'{action_verb} image...'
                PROGRESS[pid]['pct'] = 10
                
                # Use qemu-img convert or direct copy based on file type
                def run_convert():
                    if convert_needed:
                        subprocess.check_call(['sudo', 'qemu-img','convert','-t','none','-O','qcow2',local_path,dest_file])
                    else:
                        # For ISO files, just copy directly
                        subprocess.check_call(['cp', local_path, dest_file])
                t0=time.time()
                thr=threading.Thread(target=run_convert,daemon=True)
                thr.start()
                while thr.is_alive():
                    # Check every 0.5 seconds for smoother progress
                    try:
                        if os.path.exists(dest_file):
                            sz=os.path.getsize(dest_file)
                            if total and total>0:
                                pct=min(95,int(10 + (sz/total)*80))
                                PROGRESS[pid]['pct'] = pct
                                PROGRESS[pid]['msg'] = f'{action_verb} ({human_bytes(sz)}/{human_bytes(total)})'
                            else:
                                # time based estimation for unknown sizes
                                elapsed = time.time()-t0
                                pct=min(95,int(10 + min(elapsed*3, 80)))  # slower increment for large files
                                PROGRESS[pid]['pct'] = pct
                                PROGRESS[pid]['msg'] = f'{action_verb} ({human_bytes(sz)})'
                    except Exception:
                        pass
                    time.sleep(0.5)  # More frequent updates
                thr.join()
            finally:
                # Always remove lock file
                try:
                    os.remove(lock_file)
                except Exception:
                    pass
            
            # NOW unmount NFS since conversion is complete
            if nfs_mount_point and os.path.exists(nfs_mount_point):
                PROGRESS[pid]['pct'] = 96
                PROGRESS[pid]['msg'] = 'Cleaning up NFS mount...'
                # Simple unmount after successful conversion
                try:
                    subprocess.check_call(['sudo', 'umount', nfs_mount_point], timeout=10, stderr=subprocess.DEVNULL)
                except (subprocess.TimeoutExpired, subprocess.CalledProcessError):
                    # If normal unmount fails, try lazy unmount
                    try:
                        subprocess.check_call(['sudo', 'umount', '-l', nfs_mount_point], timeout=5, stderr=subprocess.DEVNULL)
                    except Exception:
                        pass  # Continue even if unmount fails
            
            PROGRESS[pid]['pct'] = 98
            PROGRESS[pid]['msg'] = 'Finalizing...'
            try: 
                pool.refresh(0)
                PROGRESS[pid]['status'] = 'done'
                PROGRESS[pid]['pct'] = 100
                PROGRESS[pid]['msg'] = 'Import complete!'
            except Exception: 
                # Pool refresh failed but file was created
                PROGRESS[pid]['status'] = 'done'
                PROGRESS[pid]['pct'] = 100
                PROGRESS[pid]['msg'] = 'Import complete!'
                
        except Exception as e:
            PROGRESS[pid]['status'] = 'error'
            PROGRESS[pid]['msg'] = str(e)
            # Cleanup NFS mount if conversion failed
            if nfs_mount_point and os.path.exists(nfs_mount_point):
                try:
                    subprocess.check_call(['sudo', 'umount', nfs_mount_point], timeout=10, stderr=subprocess.DEVNULL)
                except (subprocess.TimeoutExpired, subprocess.CalledProcessError):
                    # If normal unmount fails, try lazy unmount
                    try:
                        subprocess.check_call(['sudo', 'umount', '-l', nfs_mount_point], timeout=5, stderr=subprocess.DEVNULL)
                    except Exception:
                        pass  # Continue even if unmount fails
        finally:
            
            # Clean up temporary directory
            if temp_dir and os.path.exists(temp_dir):
                try:
                    import shutil
                    shutil.rmtree(temp_dir, ignore_errors=True)
                except Exception:
                    # If cleanup fails, try to clean up any remaining mount points in /tmp
                    try:
                        # Find and clean up any stale mount points
                        for entry in os.listdir('/tmp'):
                            if entry.startswith('vm_import_'):
                                stale_path = os.path.join('/tmp', entry)
                                if os.path.isdir(stale_path):
                                    # Check for mount points inside
                                    try:
                                        mnt_path = os.path.join(stale_path, 'mnt')
                                        if os.path.ismount(mnt_path):
                                            subprocess.call(['umount', '-f', mnt_path], timeout=5)
                                        shutil.rmtree(stale_path, ignore_errors=True)
                                    except Exception:
                                        pass
                    except Exception:
                        pass
            
            # Clean up the progress entry after a delay to let UI show completion
            def cleanup_progress():
                time.sleep(3)  # Wait 3 seconds for UI to show completion
                if pid in PROGRESS:
                    del PROGRESS[pid]
            threading.Thread(target=cleanup_progress, daemon=True).start()
    
    threading.Thread(target=worker,daemon=True).start()

VM_PREV={}  # name -> {cpu_time_ns, ts, rd_bytes, wr_bytes}
HOST_PREV={'cpu':None,'ts':0,'disk':{}}  # for host perf deltas

# Sessions for basic authentication
SESSIONS = {}  # session_id -> {username, expires}

def check_auth(handler):
    """Check if request is authenticated"""
    if not AUTH_PASSWORD:
        return True  # No auth required
    
    session_cookie = None
    if 'Cookie' in handler.headers:
        cookies = handler.headers['Cookie']
        for cookie in cookies.split(';'):
            if cookie.strip().startswith('vm_session='):
                session_cookie = cookie.split('=', 1)[1].strip()
                break
    
    if not session_cookie:
        return False
    
    session = SESSIONS.get(session_cookie)
    if not session:
        return False
    
    if time.time() > session['expires']:
        del SESSIONS[session_cookie]
        return False
    
    return True

def create_session():
    """Create a new session"""
    session_id = hashlib.sha256(os.urandom(32)).hexdigest()
    SESSIONS[session_id] = {
        'username': 'admin',
        'expires': time.time() + 86400  # 24 hours
    }
    return session_id

class Handler(BaseHTTPRequestHandler):
    server_version='Enhanced-VMManager/2.0'
    
    def list_iso_images(self, pool):
        """List all ISO images in the given storage pool."""
        try:
            import xml.etree.ElementTree as ET
            pool_xml = pool.XMLDesc()
            pool_root = ET.fromstring(pool_xml)
            pool_path = pool_root.findtext('.//target/path')
            if not pool_path:
                return []
                
            images_dir = os.path.join(pool_path, 'images')
            if not os.path.isdir(images_dir):
                return []
                
            # List all .iso files in the images directory
            return [f for f in os.listdir(images_dir) 
                   if f.lower().endswith('.iso') and os.path.isfile(os.path.join(images_dir, f))]
                    
        except Exception as e:
            logger.error(f"Error listing ISO images in pool {pool.name()}: {e}")
            return []
    
    def finish(self):
        """Override finish to handle detached WebSocket connections"""
        try:
            if self.connection is not None:
                super().finish()
        except Exception:
            # If connection was detached for WebSocket, ignore finish errors
            pass
    
    def _send(self, body, status=200, ctype='text/html; charset=utf-8', headers=None):
        data=body if isinstance(body,(bytes,bytearray)) else body.encode();
        self.send_response(status)
        self.send_header('Content-Type',ctype)
        self.send_header('Content-Length',str(len(data)))
        if headers:
            for k, v in headers.items():
                self.send_header(k, v)
        self.end_headers()
        self.wfile.write(data)
    
    def wrap(self,title,body,theme='dark'):
        return PAGE_TEMPLATE.format(title=html.escape(title), body=body, css=CSS, js=JS, 
                                   hostname=html.escape(socket.gethostname()), theme=theme)
    def page_novnc(self, domain_name:str):
        """Standalone full-page noVNC console; isolated (doesn't reuse preview JS)."""
        safe = html.escape(domain_name) if domain_name else ''
        if not domain_name:
            return self.wrap('noVNC', "<div class='card'><p>No domain specified.</p></div>")
        content = f"""
        <div class='card' style='padding:0;overflow:hidden;'>
            <div style='display:flex;align-items:center;justify-content:space-between;background:var(--card);padding:6px 10px;border-bottom:1px solid var(--border);'>
                <div><strong>🖥️ noVNC Console:</strong> {safe}</div>
                <div style='display:flex;gap:6px;'>
                    <button class='small' onclick='sendCtrlAltDel()'>Ctrl+Alt+Del</button>
                    <a class='button small secondary' href='/?domain={safe}'>Back</a>
                </div>
            </div>
            <div id='vnc-root' style='width:100%;height:80vh;background:#000;display:flex;align-items:center;justify-content:center;color:#888;font:14px sans-serif;'>
                <div>Connecting to VNC...</div>
            </div>
        </div>
        <script>
        // Minimal VNC client - focus on connection stability first
        class SimpleVNC {{
            constructor(target, url) {{
                this.target = target;
                this.url = url;
                this.ws = null;
                this.canvas = null;
                this.ctx = null;
                this.connected = false;
                this.state = 'Connecting';
                
                this.init();
            }}
            
            init() {{
                this.target.innerHTML = '';
                this.canvas = document.createElement('canvas');
                this.canvas.width = 800;
                this.canvas.height = 600;
                this.canvas.style.border = '1px solid #ccc';
                this.canvas.style.cursor = 'crosshair';
                this.target.appendChild(this.canvas);
                this.ctx = this.canvas.getContext('2d');
                
                // Fill with test pattern initially
                this.ctx.fillStyle = '#000';
                this.ctx.fillRect(0, 0, 800, 600);
                this.ctx.fillStyle = '#fff';
                this.ctx.font = '16px monospace';
                this.ctx.fillText('Connecting to VNC...', 10, 30);
                
                this.connect();
            }}
            
            connect() {{
                console.log('Connecting to:', this.url);
                
                try {{
                    this.ws = new WebSocket(this.url, 'binary');
                    this.ws.binaryType = 'arraybuffer';
                    
                    this.ws.onopen = () => {{
                        console.log('WebSocket opened');
                        this.ctx.fillStyle = '#000';
                        this.ctx.fillRect(0, 0, 800, 600);
                        this.ctx.fillStyle = '#0f0';
                        this.ctx.fillText('WebSocket connected, starting VNC handshake...', 10, 30);
                        
                        // Start VNC handshake - send client version
                        this.sendString('RFB 003.008\\n');
                        this.state = 'VersionSent';
                    }};
                    
                    this.ws.onmessage = (event) => {{
                        console.log('Received message, length:', event.data.byteLength, 'state:', this.state);
                        this.handleData(new Uint8Array(event.data));
                    }};
                    
                    this.ws.onclose = (event) => {{
                        console.log('WebSocket closed:', event.code, event.reason);
                        this.ctx.fillStyle = '#000';
                        this.ctx.fillRect(0, 0, 800, 600);
                        this.ctx.fillStyle = '#f00';
                        this.ctx.fillText('Connection closed: ' + event.code + ' ' + event.reason, 10, 30);
                    }};
                    
                    this.ws.onerror = (error) => {{
                        console.error('WebSocket error:', error);
                        this.ctx.fillStyle = '#000';
                        this.ctx.fillRect(0, 0, 800, 600);
                        this.ctx.fillStyle = '#f00';
                        this.ctx.fillText('Connection error', 10, 30);
                    }};
                    
                }} catch (e) {{
                    console.error('Failed to create WebSocket:', e);
                    this.ctx.fillStyle = '#f00';
                    this.ctx.fillText('Failed to create WebSocket: ' + e.message, 10, 30);
                }}
            }}
            
            sendString(str) {{
                if (this.ws && this.ws.readyState === WebSocket.OPEN) {{
                    const data = new TextEncoder().encode(str);
                    console.log('Sending:', str.replace('\\n', '\\\\n'));
                    this.ws.send(data);
                }}
            }}
            
            sendBytes(data) {{
                if (this.ws && this.ws.readyState === WebSocket.OPEN) {{
                    console.log('Sending bytes:', Array.from(data));
                    this.ws.send(data);
                }}
            }}
            
            handleData(data) {{
                console.log('Handling data in state:', this.state, 'bytes:', Array.from(data.slice(0, Math.min(10, data.length))));
                
                try {{
                    switch (this.state) {{
                        case 'VersionSent':
                            // Server sends its version
                            const serverVersion = new TextDecoder().decode(data);
                            console.log('Server version:', serverVersion);
                            this.ctx.fillStyle = '#000';
                            this.ctx.fillRect(0, 0, 800, 600);
                            this.ctx.fillStyle = '#0f0';
                            this.ctx.fillText('Server version: ' + serverVersion, 10, 30);
                            this.ctx.fillText('Waiting for security types...', 10, 50);
                            this.state = 'WaitingSecurity';
                            break;
                            
                        case 'WaitingSecurity':
                            // Server sends security types
                            if (data.length >= 2) {{
                                const numTypes = data[0];
                                console.log('Security types count:', numTypes);
                                this.ctx.fillText('Security types: ' + numTypes, 10, 70);
                                
                                if (numTypes > 0) {{
                                    const types = Array.from(data.slice(1, 1 + numTypes));
                                    console.log('Available security types:', types);
                                    this.ctx.fillText('Types: ' + types.join(','), 10, 90);
                                    
                                    // Choose None security (type 1) if available
                                    if (types.includes(1)) {{
                                        this.sendBytes(new Uint8Array([1]));
                                        this.ctx.fillText('Chose None security', 10, 110);
                                        this.state = 'WaitingSecurityResult';
                                    }} else {{
                                        this.ctx.fillStyle = '#f00';
                                        this.ctx.fillText('No supported security type', 10, 110);
                                    }}
                                }}
                            }}
                            break;
                            
                        case 'WaitingSecurityResult':
                            // Security result
                            if (data.length >= 4) {{
                                const result = new DataView(data.buffer).getUint32(0);
                                console.log('Security result:', result);
                                if (result === 0) {{
                                    this.ctx.fillText('Security OK, sending ClientInit', 10, 130);
                                    // Send ClientInit (shared = 1)
                                    this.sendBytes(new Uint8Array([1]));
                                    this.state = 'WaitingServerInit';
                                }} else {{
                                    this.ctx.fillStyle = '#f00';
                                    this.ctx.fillText('Security failed: ' + result, 10, 130);
                                }}
                            }}
                            break;
                            
                        case 'WaitingServerInit':
                            // Server init message
                            if (data.length >= 24) {{
                                const dv = new DataView(data.buffer);
                                const width = dv.getUint16(0);
                                const height = dv.getUint16(2);
                                
                                // Read server's pixel format
                                const serverBpp = data[4];
                                const serverDepth = data[5];
                                const serverBigEndian = data[6];
                                const serverTrueColor = data[7];
                                const serverRedMax = dv.getUint16(8);
                                const serverGreenMax = dv.getUint16(10);
                                const serverBlueMax = dv.getUint16(12);
                                const serverRedShift = data[14];
                                const serverGreenShift = data[15];
                                const serverBlueShift = data[16];
                                
                                console.log('Server pixel format:', {{
                                    bpp: serverBpp,
                                    depth: serverDepth,
                                    bigEndian: serverBigEndian,
                                    trueColor: serverTrueColor,
                                    redMax: serverRedMax,
                                    greenMax: serverGreenMax,
                                    blueMax: serverBlueMax,
                                    shifts: [serverRedShift, serverGreenShift, serverBlueShift]
                                }});
                                
                                console.log('Framebuffer size:', width + 'x' + height);
                                this.ctx.fillText('Framebuffer: ' + width + 'x' + height, 10, 150);
                                this.ctx.fillText('Server: ' + serverBpp + 'bpp, depth=' + serverDepth, 10, 170);
                                this.ctx.fillText('VNC connection established!', 10, 190);
                                
                                this.canvas.width = width;
                                this.canvas.height = height;
                                this.connected = true;
                                this.state = 'Connected';
                                
                                // Clear canvas with black background
                                this.ctx.fillStyle = '#000';
                                this.ctx.fillRect(0, 0, width, height);
                                
                                // Setup input handlers
                                this.setupInput();
                                
                                // Send SetPixelFormat to request 32-bit RGB
                                this.sendSetPixelFormat();
                                
                                // Send SetEncodings
                                this.sendSetEncodings();
                                
                                // Request initial full screen update
                                setTimeout(() => {{
                                    this.requestUpdate(0, 0, width, height, false);
                                }}, 100);
                            }}
                            break;
                            
                        case 'Connected':
                            // Handle server messages
                            this.handleServerMessage(data);
                            break;
                    }}
                }} catch (e) {{
                    console.error('Error handling data:', e);
                    this.ctx.fillStyle = '#f00';
                    this.ctx.fillText('Error: ' + e.message, 10, 200);
                }}
            }}
            
            handleServerMessage(data) {{
                if (data.length === 0) return;
                
                const msgType = data[0];
                console.log('Server message type:', msgType, 'data length:', data.length);
                
                switch (msgType) {{
                    case 0: // FramebufferUpdate
                        this.handleFramebufferUpdate(data);
                        break;
                    case 2: // Bell
                        console.log('VNC Bell received');
                        break;
                    case 3: // ServerCutText
                        console.log('Server cut text received');
                        break;
                    default:
                        console.log('Unknown message type:', msgType);
                }}
            }}
            
            handleFramebufferUpdate(data) {{
                console.log('Processing framebuffer update, data length:', data.length);
                
                if (data.length < 4) {{
                    console.log('Framebuffer update too short');
                    return;
                }}
                
                const dv = new DataView(data.buffer);
                // Skip message type (1 byte) and padding (1 byte)
                const numRects = dv.getUint16(2);
                console.log('Number of rectangles:', numRects);
                
                let offset = 4;
                for (let i = 0; i < numRects && offset + 12 <= data.length; i++) {{
                    const x = dv.getUint16(offset);
                    const y = dv.getUint16(offset + 2);
                    const w = dv.getUint16(offset + 4);
                    const h = dv.getUint16(offset + 6);
                    const encoding = dv.getInt32(offset + 8);
                    
                    console.log(`Rectangle ${{i}}: x=${{x}}, y=${{y}}, w=${{w}}, h=${{h}}, encoding=${{encoding}}`);
                    offset += 12;
                    
                    if (encoding === 0) {{ // Raw encoding
                        // Each pixel is 4 bytes (RGBA/BGRA)
                        const pixelBytes = 4;
                        const rectDataSize = w * h * pixelBytes;
                        
                        console.log(`Expected rect data size: ${{rectDataSize}}, available: ${{data.length - offset}}`);
                        
                        if (offset + rectDataSize <= data.length) {{
                            const rectData = data.slice(offset, offset + rectDataSize);
                            this.drawRawRect(x, y, w, h, rectData);
                            offset += rectDataSize;
                        }} else {{
                            console.log('Not enough data for rectangle');
                            break;
                        }}
                    }} else {{
                        console.log('Unsupported encoding:', encoding);
                        // For now, just draw a placeholder
                        this.ctx.fillStyle = '#444';
                        this.ctx.fillRect(x, y, w, h);
                        this.ctx.fillStyle = '#fff';
                        this.ctx.font = '12px monospace';
                        this.ctx.fillText(`Encoding ${{encoding}}`, x + 5, y + 15);
                        break;
                    }}
                }}
                
                // Request another update to keep getting screen data
                setTimeout(() => {{
                    if (this.connected) {{
                        this.requestUpdate(0, 0, this.canvas.width, this.canvas.height, true);
                    }}
                }}, 50); // Faster updates for better responsiveness
            }}
            
            drawRawRect(x, y, w, h, data) {{
                console.log(`Drawing raw rect: ${{x}},${{y}} ${{w}}x${{h}} with ${{data.length}} bytes`);
                
                try {{
                    const imageData = this.ctx.createImageData(w, h);
                    const pixels = imageData.data;
                    
                    // VNC Raw encoding: 32-bit pixels
                    // Based on our SetPixelFormat: RGBA with red-shift=16, green-shift=8, blue-shift=0
                    const bytesPerPixel = 4;
                    
                    for (let i = 0; i < w * h; i++) {{
                        const srcOffset = i * bytesPerPixel;
                        const dstOffset = i * 4;
                        
                        if (srcOffset + 3 < data.length) {{
                            // Read 32-bit pixel value (little endian)
                            const pixel = (data[srcOffset + 3] << 24) | 
                                         (data[srcOffset + 2] << 16) | 
                                         (data[srcOffset + 1] << 8) | 
                                         data[srcOffset];
                            
                            // Extract RGB components based on our pixel format
                            const r = (pixel >> 16) & 0xFF;
                            const g = (pixel >> 8) & 0xFF;
                            const b = pixel & 0xFF;
                            
                            // Set Canvas RGBA pixels
                            pixels[dstOffset] = r;     // R
                            pixels[dstOffset + 1] = g; // G
                            pixels[dstOffset + 2] = b; // B
                            pixels[dstOffset + 3] = 255; // A (fully opaque)
                        }}
                    }}
                    
                    this.ctx.putImageData(imageData, x, y);
                    console.log(`Successfully drew rectangle at ${{x}},${{y}}`);
                }} catch (e) {{
                    console.error('Error drawing rectangle:', e);
                    // Draw a colored rectangle as fallback
                    this.ctx.fillStyle = '#333';
                    this.ctx.fillRect(x, y, w, h);
                }}
            }}
            
            requestUpdate(x, y, w, h, incremental) {{
                const msg = new Uint8Array(10);
                const dv = new DataView(msg.buffer);
                
                msg[0] = 3; // FramebufferUpdateRequest
                msg[1] = incremental ? 1 : 0;
                dv.setUint16(2, x);
                dv.setUint16(4, y);
                dv.setUint16(6, w);
                dv.setUint16(8, h);
                
                console.log('Requesting update:', x, y, w, h, incremental);
                this.sendBytes(msg);
            }}
            
            setupInput() {{
                console.log('Setting up input handlers');
                this.canvas.setAttribute('tabindex', '0');
                this.canvas.focus();
                
                this.canvas.addEventListener('click', () => {{
                    console.log('Canvas clicked');
                    this.canvas.focus();
                }});
                
                // Keyboard handling
                this.canvas.addEventListener('keydown', (e) => {{
                    console.log('Key down:', e.key, e.keyCode);
                    this.sendKeyEvent(e.keyCode, true);
                    e.preventDefault();
                }});
                
                this.canvas.addEventListener('keyup', (e) => {{
                    console.log('Key up:', e.key, e.keyCode);
                    this.sendKeyEvent(e.keyCode, false);
                    e.preventDefault();
                }});
                
                // Mouse handling
                this.canvas.addEventListener('mousedown', (e) => {{
                    const rect = this.canvas.getBoundingClientRect();
                    const scaleX = this.canvas.width / rect.width;
                    const scaleY = this.canvas.height / rect.height;
                    const x = Math.floor((e.clientX - rect.left) * scaleX);
                    const y = Math.floor((e.clientY - rect.top) * scaleY);
                    
                    console.log('Mouse down:', e.button, x, y);
                    this.sendPointerEvent(x, y, 1 << e.button);
                    e.preventDefault();
                }});
                
                this.canvas.addEventListener('mouseup', (e) => {{
                    const rect = this.canvas.getBoundingClientRect();
                    const scaleX = this.canvas.width / rect.width;
                    const scaleY = this.canvas.height / rect.height;
                    const x = Math.floor((e.clientX - rect.left) * scaleX);
                    const y = Math.floor((e.clientY - rect.top) * scaleY);
                    
                    console.log('Mouse up:', e.button, x, y);
                    this.sendPointerEvent(x, y, 0);
                    e.preventDefault();
                }});
                
                this.canvas.addEventListener('mousemove', (e) => {{
                    const rect = this.canvas.getBoundingClientRect();
                    const scaleX = this.canvas.width / rect.width;
                    const scaleY = this.canvas.height / rect.height;
                    const x = Math.floor((e.clientX - rect.left) * scaleX);
                    const y = Math.floor((e.clientY - rect.top) * scaleY);
                    
                    this.sendPointerEvent(x, y, 0);
                }});
            }}
            
            sendPointerEvent(x, y, buttonMask) {{
                if (!this.connected) return;
                
                const msg = new Uint8Array(6);
                const dv = new DataView(msg.buffer);
                
                msg[0] = 5; // PointerEvent
                msg[1] = buttonMask;
                dv.setUint16(2, x);
                dv.setUint16(4, y);
                
                this.sendBytes(msg);
            }}
            
            sendKeyEvent(keyCode, down) {{
                if (!this.connected) return;
                
                const msg = new Uint8Array(8);
                const dv = new DataView(msg.buffer);
                
                msg[0] = 4; // KeyEvent
                msg[1] = down ? 1 : 0;
                // 2 bytes padding
                dv.setUint32(4, keyCode);
                
                this.sendBytes(msg);
            }}
            
            sendSetPixelFormat() {{
                // Send SetPixelFormat message for 32-bit RGBA
                const msg = new Uint8Array(20);
                const dv = new DataView(msg.buffer);
                
                msg[0] = 0; // SetPixelFormat message type
                // 3 bytes padding
                msg[4] = 32; // bits-per-pixel
                msg[5] = 24; // depth  
                msg[6] = 0;  // big-endian-flag (0 = little endian)
                msg[7] = 1;  // true-color-flag
                dv.setUint16(8, 255);  // red-max
                dv.setUint16(10, 255); // green-max  
                dv.setUint16(12, 255); // blue-max
                msg[14] = 16; // red-shift (bits 16-23)
                msg[15] = 8;  // green-shift (bits 8-15)
                msg[16] = 0;  // blue-shift (bits 0-7)
                // 3 bytes padding
                
                console.log('Sending SetPixelFormat: 32bpp, depth=24, RGB(16,8,0)');
                this.sendBytes(msg);
            }}
            
            sendSetEncodings() {{
                // Send SetEncodings message - only Raw encoding
                const msg = new Uint8Array(8);
                const dv = new DataView(msg.buffer);
                
                msg[0] = 2; // SetEncodings message type
                // 1 byte padding
                dv.setUint16(2, 1); // number-of-encodings
                dv.setInt32(4, 0);  // Raw encoding
                
                console.log('Sending SetEncodings');
                this.sendBytes(msg);
            }}
            
            sendCtrlAltDel() {{
                console.log('Sending Ctrl+Alt+Del');
                if (!this.connected) return;
                
                // Send Ctrl+Alt+Del sequence
                this.sendKeyEvent(17, true);  // Ctrl down
                setTimeout(() => {{
                    this.sendKeyEvent(18, true);  // Alt down
                    setTimeout(() => {{
                        this.sendKeyEvent(46, true);  // Del down
                        setTimeout(() => {{
                            this.sendKeyEvent(46, false); // Del up
                            setTimeout(() => {{
                                this.sendKeyEvent(18, false); // Alt up
                                setTimeout(() => {{
                                    this.sendKeyEvent(17, false); // Ctrl up
                                }}, 50);
                            }}, 50);
                        }}, 50);
                    }}, 50);
                }}, 50);
            }}
        }}
        
        // Initialize VNC
        const vmName = {json.dumps(domain_name)};
        const root = document.getElementById('vnc-root');
        const proto = (location.protocol === 'https:' ? 'wss://' : 'ws://');
        const url = proto + location.host + '/vnc_ws/' + encodeURIComponent(vmName);
        
        console.log('Creating SimpleVNC with URL:', url);
        const vnc = new SimpleVNC(root, url);
        window.vncInstance = vnc;
        
        window.sendCtrlAltDel = function() {{
            if (window.vncInstance) {{
                window.vncInstance.sendCtrlAltDel();
            }}
        }};
        </script>
        """
        return self.wrap(f'Console {safe}', content)

    def handle_vnc_websocket(self, domain_name: str, lv: LV):
        """Handle WebSocket proxy for VNC connection."""
        vnc_socket = None
        logger.info(f"VNC WS: Received connection for domain '{domain_name}'")
        try:
            d = lv.get_domain(domain_name)
            if not d.isActive():
                logger.error(f"VNC WS: Domain '{domain_name}' is not running.")
                raise RuntimeError('Domain not running')

            xml = d.XMLDesc(0)
            import xml.etree.ElementTree as ET
            root = ET.fromstring(xml)
            graphics = root.find('.//devices/graphics[@type="vnc"]')
            
            if graphics is None or graphics.get('port') == '-1':
                logger.error(f"VNC WS: VNC not configured for domain '{domain_name}'.")
                raise RuntimeError('VNC not configured or port not available')

            port = int(graphics.get('port'))
            host = graphics.get('listen', '127.0.0.1')
            logger.info(f"VNC WS: Found VNC for '{domain_name}' at {host}:{port}")
            
            # Perform WebSocket handshake
            key = self.headers.get('Sec-WebSocket-Key')
            if not key:
                raise RuntimeError('Missing Sec-WebSocket-Key header')
            
            guid = "258EAFA5-E914-47DA-95CA-C5AB0DC85B11"
            accept_key = base64.b64encode(hashlib.sha1((key + guid).encode()).digest()).decode()

            self.send_response(101)
            self.send_header('Upgrade', 'websocket')
            self.send_header('Connection', 'Upgrade')
            self.send_header('Sec-WebSocket-Accept', accept_key)
            self.end_headers()
            logger.info(f"VNC WS: Handshake completed for '{domain_name}'.")

            vnc_socket = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
            vnc_socket.connect((host, port))
            logger.info(f"VNC WS: Connected to VNC server at {host}:{port}.")
            
            ws_socket = self.connection
            ws_socket.setblocking(True)

            stop_event = threading.Event()

            def proxy_ws_to_vnc():
                logger.info("VNC WS: Starting ws->vnc proxy thread.")
                while not stop_event.is_set():
                    try:
                        header = ws_socket.recv(2)
                        if len(header) < 2:
                            logger.info("VNC WS: ws->vnc closing, client closed connection.")
                            break
                        
                        opcode = header[0] & 0x0F
                        if opcode == 8: # Close frame
                            logger.info("VNC WS: ws->vnc received close frame.")
                            break

                        masked = header[1] & 0x80
                        payload_len = header[1] & 0x7F

                        if payload_len == 126:
                            payload_len = struct.unpack('!H', ws_socket.recv(2))[0]
                        elif payload_len == 127:
                            payload_len = struct.unpack('!Q', ws_socket.recv(8))[0]

                        mask = ws_socket.recv(4) if masked else None
                        payload = ws_socket.recv(payload_len)

                        if masked and mask:
                            payload = bytes([payload[i] ^ mask[i % 4] for i in range(payload_len)])
                        
                        logger.debug(f"VNC WS: ws->vnc proxying {len(payload)} bytes.")
                        vnc_socket.sendall(payload)
                    except (socket.error, BrokenPipeError, OSError) as e:
                        logger.warning(f"VNC WS: ws->vnc socket error: {e}")
                        break
                stop_event.set()
                logger.info("VNC WS: Exiting ws->vnc proxy thread.")

            def proxy_vnc_to_ws():
                logger.info("VNC WS: Starting vnc->ws proxy thread.")
                while not stop_event.is_set():
                    try:
                        data = vnc_socket.recv(8192)
                        if not data:
                            logger.info("VNC WS: vnc->ws closing, VNC server closed connection.")
                            break
                        
                        logger.debug(f"VNC WS: vnc->ws proxying {len(data)} bytes.")
                        header = bytearray([0x82]) # FIN bit + binary frame
                        length = len(data)
                        if length <= 125:
                            header.append(length)
                        elif length <= 65535:
                            header.append(126)
                            header.extend(struct.pack('!H', length))
                        else:
                            header.append(127)
                            header.extend(struct.pack('!Q', length))
                        
                        ws_socket.sendall(header + data)
                    except (socket.error, BrokenPipeError, OSError) as e:
                        logger.warning(f"VNC WS: vnc->ws socket error: {e}")
                        break
                stop_event.set()
                logger.info("VNC WS: Exiting vnc->ws proxy thread.")

            t1 = threading.Thread(target=proxy_ws_to_vnc)
            t2 = threading.Thread(target=proxy_vnc_to_ws)
            t1.daemon = True
            t2.daemon = True
            t1.start()
            t2.start()
            stop_event.wait()
            logger.info(f"VNC WS: Proxy threads for '{domain_name}' finished.")

        except Exception as e:
            logger.error(f"VNC WebSocket proxy error for '{domain_name}': {e}", exc_info=True)
        finally:
            if vnc_socket:
                vnc_socket.close()
            # Detach the connection so the parent class doesn't try to close it
            self.connection = None
    
    def handle_vnc_websocket_FIXED(self, domain_name: str, lv: LV):
        """Handle WebSocket proxy for VNC connection. (FIXED)"""
        vnc_socket = None
        try:
            d = lv.get_domain(domain_name)
            if not d.isActive():
                raise RuntimeError('Domain not running')

            xml = d.XMLDesc(0)
            import xml.etree.ElementTree as ET
            root = ET.fromstring(xml)
            graphics = root.find('.//devices/graphics[@type="vnc"]')
            
            if graphics is None or graphics.get('port') == '-1':
                raise RuntimeError('VNC not configured or port not available')

            port = int(graphics.get('port'))
            host = graphics.get('listen', '127.0.0.1')
            
            key = self.headers.get('Sec-WebSocket-Key')
            if not key:
                raise RuntimeError('Missing Sec-WebSocket-Key header')
            
            guid = "258EAFA5-E914-47DA-95CA-C5AB0DC85B11"
            accept_key = base64.b64encode(hashlib.sha1((key + guid).encode()).digest()).decode()

            self.send_response(101)
            self.send_header('Upgrade', 'websocket')
            self.send_header('Connection', 'Upgrade')
            self.send_header('Sec-WebSocket-Accept', accept_key)
            self.end_headers()

            vnc_socket = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
            vnc_socket.connect((host, port))
            
            ws_socket = self.connection
            ws_socket.setblocking(True)

            stop_event = threading.Event()

            def proxy_ws_to_vnc():
                while not stop_event.is_set():
                    try:
                        header = ws_socket.recv(2)
                        if len(header) < 2: break
                        opcode = header[0] & 0x0F
                        if opcode == 8: break
                        masked = header[1] & 0x80
                        payload_len = header[1] & 0x7F
                        if payload_len == 126:
                            payload_len = struct.unpack('!H', ws_socket.recv(2))[0]
                        elif payload_len == 127:
                            payload_len = struct.unpack('!Q', ws_socket.recv(8))[0]
                        mask = ws_socket.recv(4) if masked else None
                        payload = ws_socket.recv(payload_len)
                        if masked and mask:
                            payload = bytes([payload[i] ^ mask[i % 4] for i in range(payload_len)])
                        vnc_socket.sendall(payload)
                    except (socket.error, BrokenPipeError, OSError):
                        break
                stop_event.set()

            def proxy_vnc_to_ws():
                while not stop_event.is_set():
                    try:
                        data = vnc_socket.recv(8192)
                        if not data: break
                        header = bytearray([0x82])
                        length = len(data)
                        if length <= 125:
                            header.append(length)
                        elif length <= 65535:
                            header.append(126)
                            header.extend(struct.pack('!H', length))
                        else:
                            header.append(127)
                            header.extend(struct.pack('!Q', length))
                        ws_socket.sendall(header + data)
                    except (socket.error, BrokenPipeError, OSError):
                        break
                stop_event.set()

            t1 = threading.Thread(target=proxy_ws_to_vnc)
            t2 = threading.Thread(target=proxy_vnc_to_ws)
            t1.daemon = True
            t2.daemon = True
            t1.start()
            t2.start()
            stop_event.wait()
        except Exception as e:
            logger.error(f"VNC WebSocket proxy error: {e}", exc_info=True)
        finally:
            if vnc_socket:
                vnc_socket.close()
            self.connection = None

    def login_page(self):
        return self.wrap('Login', """
        <div class="card" style="max-width: 400px; margin: 50px auto;">
            <h3>🔐 Authentication Required</h3>
            <form method="post" action="/login">
                <label>Password <input type="password" name="password" required autofocus></label>
                <input type="submit" value="Login" class="button">
            </form>
        </div>
        """)
    
    def do_GET(self): 
        # Authentication check
        if not check_auth(self):
            self._send(self.login_page())
            return
        self.route()
    
    def do_POST(self):
        length=int(self.headers.get('Content-Length','0'))
        raw=self.rfile.read(length) if length>0 else b''
        
        # Handle multipart form data (from FormData) vs URL-encoded data
        content_type = self.headers.get('Content-Type', '')
        if 'multipart/form-data' in content_type:
            import cgi
            import io
            # Parse multipart form data
            fp = io.BytesIO(raw)
            pdict = {'boundary': content_type.split('boundary=')[1].encode()}
            fields = cgi.parse_multipart(fp, pdict)
            form = {k: [v.decode() if isinstance(v, bytes) else v for v in vals] for k, vals in fields.items()}
        else:
            # Parse URL-encoded form data
            form=urllib.parse.parse_qs(raw.decode())
        
        # Handle login
        parsed = urllib.parse.urlparse(self.path)
        if parsed.path == '/login':
            password = form.get('password', [''])[0]
            if password == AUTH_PASSWORD:
                session_id = create_session()
                headers = {'Set-Cookie': f'vm_session={session_id}; Path=/; HttpOnly; SameSite=Strict'}
                self._send('<script>window.location="/";</script>', headers=headers)
            else:
                self._send(self.wrap('Login Failed', '<div class="alert error">Invalid password</div>' + self.login_page().split('<div class="card"')[1]))
            return
        
        # Authentication check for other endpoints
        if not check_auth(self):
            self._send(self.login_page())
            return
        
        self.route(form)
    def route(self, form:Optional[Dict[str,List[str]]]=None):
        parsed=urllib.parse.urlparse(self.path); qs=urllib.parse.parse_qs(parsed.query); path=parsed.path

        # Host power controls - handle with extreme care
        if path == '/api/host/shutdown' and form is not None:
            logger.warning(f"Host shutdown requested by {self.client_address[0]}")
            try:
                subprocess.run(['sudo','/sbin/shutdown', '-h', 'now'], check=True)
                self._send(b'{"success":true}', ctype='application/json')
            except Exception as e:
                logger.error(f"Failed to shut down host: {e}")
                self._send(b'{"success":false, "error":"Failed to execute shutdown command."}', status=500, ctype='application/json')
            return
        
        if path == '/api/host/reboot' and form is not None:
            logger.warning(f"Host reboot requested by {self.client_address[0]}")
            try:
                subprocess.run(['sudo','/sbin/reboot'], check=True)
                self._send(b'{"success":true}', ctype='application/json')
            except Exception as e:
                logger.error(f"Failed to reboot host: {e}")
                self._send(b'{"success":false, "error":"Failed to execute reboot command."}', status=500, ctype='application/json')
            return

        # Static file server for noVNC
        if path.startswith('/novnc/'):
            try:
                base_dir = os.path.dirname(os.path.realpath(__file__))
                # Prevent directory traversal attacks
                safe_path = os.path.abspath(os.path.join(base_dir, path.lstrip('/')))
                if not safe_path.startswith(os.path.join(base_dir, 'novnc')):
                    self._send(b'Forbidden', 403, 'text/plain'); return
                
                if os.path.isfile(safe_path):
                    import mimetypes
                    ctype, _ = mimetypes.guess_type(safe_path)
                    if ctype is None: ctype = 'application/octet-stream'
                    with open(safe_path, 'rb') as f:
                        self._send(f.read(), 200, ctype)
                else:
                    self._send(b'Not Found', 404, 'text/plain')
            except Exception as e:
                logger.error(f"Failed to serve static file {path}: {e}", exc_info=True)
                self._send(b'Error', 500, 'text/plain')
            return
        if libvirt is None:
            self._send(self.wrap('Error',"<div class='card'><p>libvirt module missing.</p></div>")); return
        lv=LV()
        
        # API endpoints
        if path.startswith('/api/'):
            self.handle_api(path, qs, form, lv)
            return
            
        # Existing endpoints
        if path=='/screenshot':
            name=qs.get('domain',[None])[0]
            try:
                if not name: raise RuntimeError('missing domain')
                d=lv.get_domain(name)
                if not d.isActive(): raise RuntimeError('domain inactive')
                self.screenshot(lv,d); return
            except Exception as e:
                # Return error with no-cache headers to prevent caching bad responses
                error_headers = {
                    'Cache-Control': 'no-cache, no-store, must-revalidate',
                    'Pragma': 'no-cache',
                    'Expires': '0'
                }
                self._send(self.wrap('Screenshot', f"<div class='card'><p>{html.escape(str(e))}</p></div>"), 400, 'text/html; charset=utf-8', error_headers); return
        
        if path=='/vnc_port':
            name=qs.get('domain',[None])[0]
            try:
                if not name: raise RuntimeError('missing domain')
                d=lv.get_domain(name)
                if not d.isActive(): raise RuntimeError('domain inactive')
                
                # Get VNC port from domain XML
                xml = d.XMLDesc(libvirt.VIR_DOMAIN_XML_INACTIVE)
                import xml.etree.ElementTree as ET
                root = ET.fromstring(xml)
                graphics = root.find('.//devices/graphics[@type="vnc"]')
                
                if graphics is not None:
                    port = graphics.get('port', '-1')
                    listen = graphics.get('listen', '127.0.0.1')
                    if port != '-1':
                        self._send(json.dumps({'port': int(port), 'host': listen}), 200, 'application/json')
                    else:
                        self._send(json.dumps({'error': 'VNC port not allocated'}), 400, 'application/json')
                else:
                    self._send(json.dumps({'error': 'VNC not configured'}), 400, 'application/json')
                return
            except Exception as e:
                self._send(json.dumps({'error': str(e)}), 500, 'application/json'); return
        
        if path=='/progress':
            pid=qs.get('id',[None])[0]
            data=PROGRESS.get(pid)
            if not data:
                self._send(json.dumps({'error':'unknown id'}),404,'application/json; charset=utf-8')
            else:
                self._send(json.dumps(data),200,'application/json; charset=utf-8')
            return
            
        if path=='/mdstatus':
            setdev=qs.get('set',[None])[0]; mode=qs.get('mode',[None])[0]
            if setdev and mode:
                try:
                    # speed limits are in KB/s
                    mapping={'pause':(0,200), 'normal':(200000,300000), 'fast':(4000000,5000000)}
                    if mode in mapping:
                        mn,mx=mapping[mode]
                        with open('/proc/sys/dev/raid/speed_limit_min','w') as f: f.write(str(mn))
                        with open('/proc/sys/dev/raid/speed_limit_max','w') as f: f.write(str(mx))
                except Exception:
                    pass
            self._send(json.dumps(self.md_status()),200,'application/json; charset=utf-8'); return
            
        if path=='/vmstats':
            self._send(json.dumps(self.vm_stats(lv)),200,'application/json; charset=utf-8'); return
        if path=='/hoststats':
            self._send(json.dumps(self.host_stats()),200,'application/json; charset=utf-8'); return
        if path=='/novnc':
            name=qs.get('domain',[None])[0]
            self._send(self.page_novnc(name)); return
            
        # WebSocket VNC proxy endpoint
        if path.startswith('/vnc_ws/'):
            domain_name = path.split('/')[-1]
            self.handle_vnc_websocket_FIXED(domain_name, lv)
            return
            
        # Wipe disk endpoint
        if path=='/wipe_disk' and form:
            device = form.get('device', [''])[0]
            if not device:
                self._send(json.dumps({'success': False, 'error': 'No device specified'}), 400, 'application/json'); return
            try:
                # Basic safety checks
                if not device.startswith('/dev/'):
                    raise ValueError('Invalid device path')
                if any(x in device for x in ['..', '/', ' ']) and not device.startswith('/dev/'):
                    raise ValueError('Invalid device path')
                
                # Check if device exists and is not mounted
                result = subprocess.run(['sudo', 'lsblk', '-n', '-o', 'MOUNTPOINT', device], 
                                      capture_output=True, text=True, timeout=10)
                if result.returncode == 0 and result.stdout.strip():
                    raise ValueError('Device appears to be mounted')
                
                # Run wipefs
                subprocess.run(['sudo', 'wipefs', '-a', device], check=True, timeout=30)
                logger.info(f"Wiped device {device}")
                self._send(json.dumps({'success': True}), 200, 'application/json')
            except subprocess.TimeoutExpired:
                self._send(json.dumps({'success': False, 'error': 'Wipe operation timed out'}), 500, 'application/json')
            except subprocess.CalledProcessError as e:
                self._send(json.dumps({'success': False, 'error': f'wipefs failed: {e}'}), 500, 'application/json')
            except Exception as e:
                self._send(json.dumps({'success': False, 'error': str(e)}), 500, 'application/json')
            return
        
        # Delete array endpoint
        if path=='/delete_array' and form:
            array_type = form.get('type', [''])[0]
            array_name = form.get('name', [''])[0]
            if not array_type or not array_name:
                self._send(json.dumps({'success': False, 'error': 'Missing type or name'}), 400, 'application/json'); return
            try:
                if array_type == 'mdadm':
                    # Unmount if mounted
                    device_path = f'/dev/{array_name}'
                    try:
                        # Check if mounted and unmount
                        result = subprocess.run(['sudo', 'findmnt', '-n', '-o', 'TARGET', device_path], 
                                              capture_output=True, text=True, timeout=10)
                        if result.returncode == 0:
                            mount_point = result.stdout.strip()
                            if mount_point:
                                subprocess.run(['sudo','umount', mount_point], check=True, timeout=30)
                                # Remove from fstab
                                try:
                                    with open('/etc/fstab', 'r') as f:
                                        lines = f.readlines()
                                    with open('/etc/fstab', 'w') as f:
                                        for line in lines:
                                            if mount_point not in line:
                                                f.write(line)
                                except Exception:
                                    pass
                    except subprocess.CalledProcessError:
                        pass  # Not mounted
                    
                    # Stop the array
                    subprocess.run(['sudo','mdadm', '--stop', device_path], check=True, timeout=30)
                    
                    # Zero superblocks on member devices
                    try:
                        result = subprocess.run(['sudo','mdadm', '--detail', device_path], 
                                              capture_output=True, text=True, timeout=10)
                        # This will fail since array is stopped, but we can parse /proc/mdstat for cleanup
                    except Exception:
                        pass
                    
                    logger.info(f"Deleted mdadm array {array_name}")
                    self._send(json.dumps({'success': True}), 200, 'application/json')
                elif array_type == 'btrfs':
                    # For BTRFS, we need to unmount and remove from fstab
                    # BTRFS arrays are identified by their mount points
                    try:
                        subprocess.run(['sudo','umount', array_name], check=True, timeout=30)
                        # Remove from fstab
                        with open('/etc/fstab', 'r') as f:
                            lines = f.readlines()
                        with open('/etc/fstab', 'w') as f:
                            for line in lines:
                                if array_name not in line:
                                    f.write(line)
                    except Exception as e:
                        pass
                    logger.info(f"Unmounted BTRFS array at {array_name}")
                    self._send(json.dumps({'success': True}), 200, 'application/json')
                else:
                    self._send(json.dumps({'success': False, 'error': 'Unknown array type'}), 400, 'application/json')
            except subprocess.TimeoutExpired:
                self._send(json.dumps({'success': False, 'error': 'Delete operation timed out'}), 500, 'application/json')
            except subprocess.CalledProcessError as e:
                self._send(json.dumps({'success': False, 'error': f'Delete failed: {e}'}), 500, 'application/json')
            except Exception as e:
                self._send(json.dumps({'success': False, 'error': str(e)}), 500, 'application/json')
            return
            
        # Remove array endpoint (wipefs and remove from UI)
        if path=='/remove_array' and form:
            array_type = form.get('type', [''])[0]
            array_name = form.get('name', [''])[0]
            if not array_type or not array_name:
                self._send(json.dumps({'success': False, 'error': 'Missing type or name'}), 400, 'application/json'); return
            try:
                # First get the device list for this filesystem
                devices = []
                if array_type == 'mdadm':
                    # Get devices from /proc/mdstat
                    try:
                        result = subprocess.run(['sudo','cat', '/proc/mdstat'], capture_output=True, text=True, timeout=5)
                        if result.returncode == 0:
                            for line in result.stdout.splitlines():
                                if line.startswith(array_name) and 'active' in line:
                                    parts = line.split()
                                    for part in parts[1:]:
                                        if part.startswith(('sd', 'nvme')) and '[' in part:
                                            device = part.split('[')[0]
                                            devices.append(f'/dev/{device}')
                                    break
                    except Exception:
                        pass
                    
                    # Stop the mdadm array first
                    device_path = f'/dev/{array_name}'
                    try:
                        subprocess.run(['sudo','mdadm', '--stop', device_path], check=True, timeout=30)
                    except subprocess.CalledProcessError:
                        pass  # Array may already be stopped
                        
                elif array_type == 'btrfs':
                    # Get devices from btrfs filesystem show
                    try:
                        result = subprocess.run(['sudo','btrfs', 'filesystem', 'show'], capture_output=True, text=True, timeout=5)
                        if result.returncode == 0:
                            in_target_fs = False
                            for line in result.stdout.splitlines():
                                if 'uuid:' in line.lower():
                                    in_target_fs = False
                                    if array_name in line:
                                        in_target_fs = True
                                elif in_target_fs and 'devid' in line and '/dev/' in line:
                                    parts = line.split()
                                    for part in parts:
                                        if part.startswith('/dev/'):
                                            devices.append(part)
                                            break
                    except Exception:
                        pass
                
                # Wipefs all devices
                wipefs_errors = []
                for device in devices:
                    try:
                        subprocess.run(['sudo','wipefs', '-a', device], check=True, timeout=30)
                        logger.info(f"Wiped filesystem signatures from {device}")
                    except subprocess.CalledProcessError as e:
                        wipefs_errors.append(f"{device}: {e}")
                    except Exception as e:
                        wipefs_errors.append(f"{device}: {e}")
                
                if wipefs_errors:
                    error_msg = "Some devices could not be wiped: " + ", ".join(wipefs_errors)
                    logger.warning(error_msg)
                    self._send(json.dumps({'success': False, 'error': error_msg}), 500, 'application/json')
                else:
                    logger.info(f"Successfully removed {array_type} array {array_name} and wiped {len(devices)} devices")
                    self._send(json.dumps({'success': True}), 200, 'application/json')
                    
            except subprocess.TimeoutExpired:
                self._send(json.dumps({'success': False, 'error': 'Remove operation timed out'}), 500, 'application/json')
            except Exception as e:
                self._send(json.dumps({'success': False, 'error': str(e)}), 500, 'application/json')
            return
        
        # Unmount array endpoint
        if path=='/unmount_array' and form:
            array_type = form.get('type', [''])[0]
            array_name = form.get('name', [''])[0]
            mount_point = form.get('mount_point', [''])[0]
            if not array_type or not array_name:
                self._send(json.dumps({'success': False, 'error': 'Missing type or name'}), 400, 'application/json'); return
            try:
                if array_type == 'mdadm':
                    # Unmount mdadm array
                    device_path = f'/dev/{array_name}'
                    if mount_point:
                        subprocess.run(['sudo','umount', mount_point], check=True, timeout=30)
                        # Remove from fstab
                        try:
                            with open('/etc/fstab', 'r') as f:
                                lines = f.readlines()
                            with open('/etc/fstab', 'w') as f:
                                for line in lines:
                                    if mount_point not in line and array_name not in line:
                                        f.write(line)
                        except Exception:
                            pass
                    logger.info(f"Unmounted mdadm array {array_name}")
                    self._send(json.dumps({'success': True}), 200, 'application/json')
                elif array_type == 'btrfs':
                    # Unmount BTRFS filesystem
                    if mount_point:
                        subprocess.run(['sudo','umount', mount_point], check=True, timeout=30)
                        # Remove from fstab
                        try:
                            with open('/etc/fstab', 'r') as f:
                                lines = f.readlines()
                            with open('/etc/fstab', 'w') as f:
                                for line in lines:
                                    if mount_point not in line:
                                        f.write(line)
                        except Exception:
                            pass
                    logger.info(f"Unmounted BTRFS filesystem {array_name}")
                    self._send(json.dumps({'success': True}), 200, 'application/json')
                else:
                    self._send(json.dumps({'success': False, 'error': 'Unknown array type'}), 400, 'application/json')
            except subprocess.TimeoutExpired:
                self._send(json.dumps({'success': False, 'error': 'Unmount operation timed out'}), 500, 'application/json')
            except subprocess.CalledProcessError as e:
                self._send(json.dumps({'success': False, 'error': f'Unmount failed: {e}'}), 500, 'application/json')
            except Exception as e:
                self._send(json.dumps({'success': False, 'error': str(e)}), 500, 'application/json')
            return
        
        # Mount array endpoint
        if path=='/mount_array' and form:
            array_type = form.get('type', [''])[0]
            array_name = form.get('name', [''])[0]
            mount_point = form.get('mount_point', [''])[0]
            if not array_type or not array_name or not mount_point:
                self._send(json.dumps({'success': False, 'error': 'Missing type, name, or mount point'}), 400, 'application/json'); return
            try:
                # Create mount point directory
                subprocess.check_call(['sudo', 'mkdir', '-p', mount_point])
                
                if array_type == 'mdadm':
                    # Mount mdadm array
                    device_path = f'/dev/{array_name}'
                    subprocess.run(['sudo','mount', device_path, mount_point], check=True, timeout=30)
                    
                    # Add to fstab
                    try:
                        uuid = subprocess.check_output(['sudo','blkid','-s','UUID','-o','value',device_path], text=True).strip()
                        if uuid:
                            with open('/etc/fstab','a') as f:
                                f.write(f"UUID={uuid} {mount_point} xfs noatime,discard 0 0\n")
                    except Exception:
                        pass
                    
                    logger.info(f"Mounted mdadm array {array_name} at {mount_point}")
                    self._send(json.dumps({'success': True}), 200, 'application/json')
                elif array_type == 'btrfs':
                    # Mount BTRFS filesystem - find first device
                    # Get devices from btrfs filesystem show
                    try:
                        result = subprocess.run(['sudo','btrfs', 'filesystem', 'show'], capture_output=True, text=True, timeout=5)
                        if result.returncode == 0:
                            target_uuid = None
                            target_device = None
                            current_uuid = None
                            
                            for line in result.stdout.splitlines():
                                if 'uuid:' in line.lower():
                                    parts = line.split()
                                    for i, part in enumerate(parts):
                                        if part.lower() == 'uuid:' and i + 1 < len(parts):
                                            current_uuid = parts[i + 1]
                                            break
                                    # Check if this matches our filesystem name
                                    if 'Label:' in line:
                                        label_idx = line.find('Label:')
                                        if label_idx != -1:
                                            label_part = line[label_idx + 6:].strip()
                                            if label_part.lower() != 'none':
                                                current_label = label_part.strip("'\"")
                                                if current_label == array_name:
                                                    target_uuid = current_uuid
                                    elif current_uuid and current_uuid.startswith(array_name):
                                        target_uuid = current_uuid
                                elif current_uuid == target_uuid and 'devid' in line and '/dev/' in line:
                                    # Extract device path
                                    parts = line.split()
                                    for part in parts:
                                        if part.startswith('/dev/'):
                                            target_device = part
                                            break
                                    if target_device:
                                        break
                            
                            if target_device:
                                subprocess.run(['sudo','mount', '-o', 'noatime,ssd,discard,compress=zstd', target_device, mount_point], check=True, timeout=30)
                                
                                # Add to fstab
                                try:
                                    uuid = subprocess.check_output(['sudo','blkid','-s','UUID','-o','value',target_device], text=True).strip()
                                    if uuid:
                                        with open('/etc/fstab','a') as f:
                                            f.write(f"UUID={uuid} {mount_point} btrfs noatime,ssd,discard,compress=zstd 0 0\n")
                                except Exception:
                                    pass
                                
                                logger.info(f"Mounted BTRFS filesystem {array_name} at {mount_point}")
                                self._send(json.dumps({'success': True}), 200, 'application/json')
                            else:
                                self._send(json.dumps({'success': False, 'error': 'Could not find device for BTRFS filesystem'}), 500, 'application/json')
                        else:
                            self._send(json.dumps({'success': False, 'error': 'Failed to get BTRFS filesystem info'}), 500, 'application/json')
                    except Exception as e:
                        self._send(json.dumps({'success': False, 'error': f'BTRFS mount failed: {e}'}), 500, 'application/json')
                else:
                    self._send(json.dumps({'success': False, 'error': 'Unknown array type'}), 400, 'application/json')
            except subprocess.TimeoutExpired:
                self._send(json.dumps({'success': False, 'error': 'Mount operation timed out'}), 500, 'application/json')
            except subprocess.CalledProcessError as e:
                self._send(json.dumps({'success': False, 'error': f'Mount failed: {e}'}), 500, 'application/json')
            except Exception as e:
                self._send(json.dumps({'success': False, 'error': str(e)}), 500, 'application/json')
            return
            
        # VM keyboard input endpoint
        if path=='/vm_key' and form:
            domain_name = form.get('domain', [''])[0]
            key = form.get('key', [''])[0]
            key_code = form.get('keyCode', [''])[0]
            shift_key = form.get('shiftKey', ['false'])[0] == 'true'
            ctrl_key = form.get('ctrlKey', ['false'])[0] == 'true'
            alt_key = form.get('altKey', ['false'])[0] == 'true'
            meta_key = form.get('metaKey', ['false'])[0] == 'true'
            is_keyup = form.get('keyup', ['false'])[0] == 'true'
            
            if domain_name and key:
                try:
                    d = lv.get_domain(domain_name)
                    if d.isActive():
                        # Handle special key combinations
                        if key == 'ctrl_alt_del':
                            # Send Ctrl+Alt+Del sequence
                            domain_name = d.name()
                            try:
                                # Use virsh send-key for Ctrl+Alt+Del
                                cmd = ['virsh', 'send-key', domain_name, 'KEY_LEFTCTRL', 'KEY_LEFTALT', 'KEY_DELETE']
                                result = subprocess.run(cmd, capture_output=True, text=True, timeout=10)
                                if result.returncode == 0:
                                    logger.info(f"Ctrl+Alt+Del sent to {domain_name}")
                                    self._send(json.dumps({'success': True}), 200, 'application/json')
                                    return
                                else:
                                    logger.warning(f"Ctrl+Alt+Del failed: {result.stderr}")
                            except Exception as e:
                                logger.error(f"Ctrl+Alt+Del error: {e}")
                            
                            self._send(json.dumps({'success': False, 'error': 'Failed to send Ctrl+Alt+Del'}), 500, 'application/json')
                            return
                        # Handle key combinations properly using virsh send-key
                        success = False
                        qmp_key = self.convert_key_to_qmp(key, key_code)
                        
                        if qmp_key:
                            domain_name = d.name()
                            
                            # For SHIFT combinations, send multiple keys to virsh send-key
                            if shift_key and key != 'Shift':
                                # Build key sequence for virsh send-key
                                # virsh send-key can take multiple keys: virsh send-key domain KEY_LEFTSHIFT KEY_A
                                base_key = qmp_key.replace('KEY_', '').lower()
                                
                                # Try the proper virsh syntax for key combinations
                                key_sequence_formats = [
                                    ['KEY_LEFTSHIFT', qmp_key],  # Format 1: KEY_LEFTSHIFT KEY_A
                                    ['shift', base_key],         # Format 2: shift a  
                                    ['KEY_LEFTSHIFT', base_key], # Format 3: KEY_LEFTSHIFT a
                                    ['shift', qmp_key],          # Format 4: shift KEY_A
                                ]
                                
                                for key_seq in key_sequence_formats:
                                    cmd = ['virsh', 'send-key', domain_name] + key_seq
                                    logger.info(f"Trying SHIFT combination: {' '.join(cmd)}")
                                    
                                    try:
                                        result = subprocess.run(cmd, capture_output=True, text=True, timeout=10)
                                        if result.returncode == 0:
                                            success = True
                                            logger.info(f"SHIFT+{key} sent successfully with format: {key_seq}")
                                            break
                                        else:
                                            logger.warning(f"SHIFT format failed: {result.stderr.strip()}")
                                    except Exception as e:
                                        logger.warning(f"SHIFT format error: {e}")
                                
                                # If all combination attempts failed, try sending keys separately
                                if not success:
                                    logger.info("Trying separate SHIFT key sequence")
                                    try:
                                        # Send SHIFT press, key press, SHIFT release sequence
                                        cmd1 = ['virsh', 'send-key', domain_name, 'KEY_LEFTSHIFT', '--holdtime', '50']
                                        cmd2 = ['virsh', 'send-key', domain_name, base_key]
                                        
                                        result1 = subprocess.run(cmd1, capture_output=True, text=True, timeout=10)
                                        result2 = subprocess.run(cmd2, capture_output=True, text=True, timeout=10)
                                        
                                        if result1.returncode == 0 and result2.returncode == 0:
                                            success = True
                                            logger.info(f"SHIFT+{key} sent with separate sequence")
                                        else:
                                            logger.error(f"Separate SHIFT sequence failed: {result1.stderr} / {result2.stderr}")
                                    except Exception as e:
                                        logger.error(f"Separate SHIFT sequence error: {e}")
                            
                            else:
                                # Regular key without modifiers
                                if is_keyup:
                                    success = self.send_qmp_key_release(d, qmp_key)
                                else:
                                    success = self.send_qmp_key(d, qmp_key)
                        
                        if qmp_key and success:
                            logger.info(f"VM {domain_name} key {'released' if is_keyup else 'sent'}: {key} (shift:{shift_key} ctrl:{ctrl_key} alt:{alt_key})")
                            self._send(json.dumps({'success': True}), 200, 'application/json')
                        elif qmp_key:
                            self._send(json.dumps({'success': False, 'error': 'Failed to send key'}), 500, 'application/json')
                        else:
                            logger.info(f"VM {domain_name} key ignored: {key}")
                            self._send(json.dumps({'success': True}), 200, 'application/json')
                    else:
                        self._send(json.dumps({'success': False, 'error': 'VM not running'}), 400, 'application/json')
                except Exception as e:
                    logger.error(f"VM key error: {e}")
                    self._send(json.dumps({'success': False, 'error': str(e)}), 500, 'application/json')
            else:
                self._send(json.dumps({'success': False, 'error': 'Missing domain or key'}), 400, 'application/json')
            return
            
        # VM mouse input endpoint
        if path=='/vm_mouse' and form:
            domain_name = form.get('domain', [''])[0]
            x = form.get('x', [''])[0]
            y = form.get('y', [''])[0]
            button = form.get('button', ['1'])[0]
            if domain_name and x and y:
                try:
                    d = lv.get_domain(domain_name)
                    if d.isActive():
                        # Send mouse event via QMP
                        success = self.send_qmp_mouse(d, int(x), int(y), int(button))
                        if success:
                            logger.info(f"VM {domain_name} mouse click: {x},{y} button {button}")
                            self._send(json.dumps({'success': True}), 200, 'application/json')
                        else:
                            self._send(json.dumps({'success': False, 'error': 'Failed to send mouse event'}), 500, 'application/json')
                    else:
                        self._send(json.dumps({'success': False, 'error': 'VM not running'}), 400, 'application/json')
                except Exception as e:
                    logger.error(f"VM mouse error: {e}")
                    self._send(json.dumps({'success': False, 'error': str(e)}), 500, 'application/json')
            else:
                self._send(json.dumps({'success': False, 'error': 'Missing domain or coordinates'}), 400, 'application/json')
            return
            
        # Logout endpoint
        if path=='/logout':
            session_cookie = None
            if 'Cookie' in self.headers:
                cookies = self.headers['Cookie']
                for cookie in cookies.split(';'):
                    if cookie.strip().startswith('vm_session='):
                        session_cookie = cookie.split('=', 1)[1].strip()
                        break
            if session_cookie and session_cookie in SESSIONS:
                del SESSIONS[session_cookie]
            headers = {'Set-Cookie': 'vm_session=; Path=/; HttpOnly; Expires=Thu, 01 Jan 1970 00:00:00 GMT'}
            self._send('<script>window.location="/login";</script>', headers=headers)
            return
            
        if path=='/':
            # Original VM creation
            if form and 'create_vm' in form:
                try:
                    name=form.get('name',[''])[0]
                    # Convert GiB to MiB for memory
                    mem=int(float(form.get('memory_gb',['2'])[0]) * 1024)
                    if mem < 256:  # Minimum 256 MiB
                        mem = 256
                    elif mem > 1048576:  # Maximum 1 TiB
                        mem = 1048576
                    vcpus=parse_int(form.get('vcpus',['2'])[0],2)
                    pool_name=form.get('pool',[''])[0]
                    bridge=form.get('bridge',['bridge0'])[0]
                    nic_model=form.get('nic_model',['virtio'])[0]
                    firmware=form.get('firmware',['bios'])[0]
                    machine=form.get('machine',['pc'])[0]
                    boot_order=form.get('boot_order',['hd,cdrom,network'])[0]
                    if not name: raise RuntimeError('Missing name')
                    pool=lv.get_pool(pool_name)
                    import xml.etree.ElementTree as ET
                    proot=ET.fromstring(pool.XMLDesc(0))
                    pool_path=proot.findtext('.//target/path') or '/var/lib/libvirt/images'
                    vm_dir=os.path.join(pool_path, name)
                    os.makedirs(vm_dir, exist_ok=True)
                    # Gather disk spec arrays
                    buses=form.get('disk_bus',[])
                    types=form.get('disk_type',[])
                    sizes=form.get('disk_size_gb',[])
                    images=form.get('disk_image',[])
                    targets=form.get('disk_target',[])
                    disks=[]  # (path,bus,target)
                    used_targets=set()
                    def next_target(bus:str)->str:
                        base={'virtio':'vd','scsi':'sd','sata':'hd'}.get(bus,'vd')
                        for c in 'abcdefghijklmnopqrstuvwxyz':
                            cand=base+c
                            if cand not in used_targets:
                                return cand
                        raise RuntimeError('Ran out of disk letters')
                    for i,bus in enumerate(buses):
                        typ=types[i] if i < len(types) else 'new'
                        size_gb=parse_int(sizes[i],20) if i < len(sizes) and sizes[i] else 20
                        image=images[i] if i < len(images) else ''
                        tgt=targets[i].strip() if i < len(targets) and targets[i] else ''
                        if typ=='image':
                            if not image:
                                raise RuntimeError('Disk image not selected')
                            # locate imported raw image under any pool images dir (first match)
                            src_path=None
                            for root_dir,dirs,files in os.walk(pool_path):
                                if root_dir.endswith('/images') and image in files:
                                    src_path=os.path.join(root_dir,image); break
                            if not src_path:
                                raise RuntimeError(f'Imported image {image} not found')
                            dest=os.path.join(vm_dir, f"img{i+1}-"+image)
                            if not os.path.exists(dest): 
                                # Use reflinks for efficient copying on supported filesystems
                                try:
                                    subprocess.check_call(['sudo', 'cp', '--reflink=always', src_path, dest])
                                    logger.info(f"Used reflink copy for {image}")
                                except subprocess.CalledProcessError:
                                    # Fallback to regular copy if reflinks not supported
                                    logger.info(f"Reflink not supported, using regular copy for {image}")
                                    shutil.copy2(src_path, dest)
                            disk_path=dest
                        else:
                            disk_name=f"disk{i+1}.qcow2"
                            disk_path=os.path.join(vm_dir,disk_name)
                            subprocess.check_call(['sudo', 'qemu-img','create','-f','qcow2',disk_path,f'{size_gb}G'])
                        # Validate / normalize target; auto-fix duplicates or invalid entries
                        base_prefix={'virtio':'vd','scsi':'sd','sata':'hd'}.get(bus,'vd')
                        def valid_format(t):
                            return t.startswith(base_prefix) and len(t)==3 and t[2].isalpha()
                        if not valid_format(tgt):
                            tgt=''
                        # If empty or duplicate, pick next available automatically
                        if not tgt or tgt in used_targets:
                            for _ in range(26):
                                cand=next_target(bus)
                                if cand not in used_targets:
                                    tgt=cand; break
                            else:
                                raise RuntimeError('Ran out of disk letters')
                        used_targets.add(tgt)
                        disks.append((disk_path,bus,tgt))
                    if not disks:
                        raise RuntimeError('At least one disk required')
                    # Auto-detect OVMF firmware paths for cross-distro compatibility
                    ovmf_code_path = None
                    if firmware == 'uefi':
                        # Common OVMF paths across different distributions
                        ovmf_paths = [
                            '/usr/share/edk2/x64/OVMF_CODE.4m.fd',  # Arch Linux
                            '/usr/share/OVMF/OVMF_CODE.fd',         # RHEL/CentOS/Fedora
                            '/usr/share/ovmf/OVMF.fd',              # Ubuntu/Debian
                            '/usr/share/qemu/ovmf-x86_64-code.bin', # openSUSE
                            '/usr/share/edk2-ovmf/x64/OVMF_CODE.fd' # Some other distros
                        ]
                        
                        for path in ovmf_paths:
                            if os.path.exists(path):
                                ovmf_code_path = path
                                break
                        
                        if not ovmf_code_path:
                            raise RuntimeError('UEFI firmware not found. Please install OVMF/EDK2 package for your distribution.')
                    
                    loader_xml = "" if firmware!='uefi' else f"<loader readonly='yes' type='pflash'>{ovmf_code_path}</loader><nvram>/var/lib/libvirt/qemu/nvram/{name}_VARS.fd</nvram>"
                    
                    # Generate disk XML with individual boot order
                    disk_xml = ""
                    boot_order_counter = 1
                    for i, (p, b, t) in enumerate(disks):
                        boot_attr = f" <boot order='{boot_order_counter}'/>" if i < 2 else ""  # Only first 2 disks get boot order
                        disk_xml += f"<disk type='file' device='disk'><driver name='qemu' type='qcow2'/><source file='{html.escape(p)}'/><target dev='{html.escape(t)}' bus='{html.escape(b)}'/>{boot_attr}</disk>"
                        if boot_attr:
                            boot_order_counter += 1
                    
                    # Add virtio-scsi controller if any disk uses SCSI bus
                    scsi_controller = ""
                    if any(b == 'scsi' for p,b,t in disks):
                        scsi_controller = "<controller type='scsi' index='0' model='virtio-scsi'/>"
                    
                    dom=f"""<domain type='kvm'><name>{name}</name><memory unit='MiB'>{mem}</memory><currentMemory unit='MiB'>{mem}</currentMemory><vcpu placement='static'>{vcpus}</vcpu><os><type arch='x86_64' machine='{machine}'>hvm</type>{loader_xml}</os><features><acpi/><apic/></features><cpu mode='host-passthrough' check='none' migratable='on'><topology sockets='1' cores='{vcpus}' threads='1'/></cpu><devices><emulator>/usr/libexec/qemu-kvm</emulator>{scsi_controller}{disk_xml}<interface type='bridge'><source bridge='{bridge}'/><model type='{nic_model}'/></interface><graphics type='vnc' port='-1' listen='127.0.0.1'/><console type='pty'/></devices></domain>"""
                    lv.conn.defineXML(dom)
                    self._send(self.wrap('Created', f"<div class='card'><p>VM {html.escape(name)} created with {len(disks)} disk(s).</p><meta http-equiv='refresh' content='0;url=/'></div>")); return
                except Exception as e:
                    # best-effort cleanup of partially created VM directory
                    try:
                        if 'vm_dir' in locals() and os.path.isdir(vm_dir):
                            shutil.rmtree(vm_dir)
                    except Exception:
                        pass
                    self._send(self.wrap('Error', f"<div class='card'><p>{html.escape(str(e))}</p><p><a class='button secondary' href='/'>Back</a></p></div>"),500); return
            
            # Page routing
            if 'create' in qs:
                dash=self.page_dashboard(lv)+"<script>document.addEventListener('DOMContentLoaded',()=>openModal('modal_vm'));</script>"
                self._send(self.wrap('Dashboard', dash)); return
            if 'images' in qs: self._send(self.wrap('Images', self.page_images(lv, form, qs))); return
            if 'hardware' in qs: self._send(self.wrap('Hardware', self.page_hardware(lv))); return
            if 'storage' in qs: self._send(self.wrap('Storage', self.page_storage(lv, form))); return
            if 'networks' in qs: self._send(self.wrap('Networks', self.page_networks(lv, form))); return
            if 'backups' in qs: self._send(self.wrap('Backups', self.page_backups(lv, form))); return
            if 'domain' in qs: 
                name=qs['domain'][0]
                # Add no-cache headers to prevent VM page caching issues
                vm_headers = {
                    'Cache-Control': 'no-cache, no-store, must-revalidate',
                    'Pragma': 'no-cache',
                    'Expires': '0'
                }
                self._send(self.wrap(f'Domain {name}', self.page_domain(lv,name,qs,form)), 200, 'text/html; charset=utf-8', vm_headers); return
            
            # Handle snapshot operations at root level (for dashboard buttons)
            if form and 'create_snapshot' in form:
                try:
                    domain_name = form.get('domain', [''])[0]
                    snap_name = form.get('snap_name', [''])[0]
                    
                    if domain_name and snap_name:
                        # Simple virsh command execution
                        cmd = ['virsh', 'snapshot-create-as', domain_name, snap_name, '--disk-only', '--atomic']
                        result = subprocess.run(cmd, capture_output=True, text=True)
                        
                        if result.returncode == 0:
                            logger.info(f"Snapshot {snap_name} created successfully for {domain_name}")
                        else:
                            logger.error(f"Snapshot creation failed: {result.stderr}")
                        
                        # Always redirect back regardless of success/failure
                        if 'domain' in qs:
                            self._send(f"<script>window.location='/?domain={urllib.parse.quote(domain_name)}';</script>")
                            return
                        else:
                            # Dashboard snapshot - just redirect back to dashboard
                            self._send("<script>window.location='/';</script>")
                            return
                except Exception as e:
                    logger.error(f"Snapshot creation error: {e}")
            
            self._send(self.wrap('Dashboard', self.page_dashboard(lv))); return
    def handle_api(self, path: str, qs: dict, form: dict, lv: LV):
        """Handle REST API endpoints"""
        try:
            if path == '/api/vms':
                vms = []
                for d in lv.list_domains():
                    state, _ = d.state()
                    vms.append({
                        'name': d.name(),
                        'state': 'running' if state == libvirt.VIR_DOMAIN_RUNNING else 'shutoff',
                        'id': d.ID() if state == libvirt.VIR_DOMAIN_RUNNING else None
                    })
                self._send(json.dumps(vms), 200, 'application/json')
            elif path.startswith('/api/vm/'):
                vm_name = path.split('/')[-1]
                if not form:  # GET
                    try:
                        d = lv.get_domain(vm_name)
                        state, _ = d.state()
                        info = d.info()
                        vm_data = {
                            'name': d.name(),
                            'state': 'running' if state == libvirt.VIR_DOMAIN_RUNNING else 'shutoff',
                            'memory_kb': info[1] * 1024,
                            'vcpus': info[3],
                            'autostart': d.autostart()
                        }
                        self._send(json.dumps(vm_data), 200, 'application/json')
                    except Exception as e:
                        self._send(json.dumps({'error': str(e)}), 404, 'application/json')
                else:  # POST - control operations
                    action = form.get('action', [''])[0]
                    try:
                        d = lv.get_domain(vm_name)
                        if action == 'start':
                            d.create()
                        elif action == 'stop':
                            d.shutdown()
                        elif action == 'force_stop':
                            d.destroy()
                        elif action == 'reboot':
                            d.reboot()
                        self._send(json.dumps({'status': 'success'}), 200, 'application/json')
                    except Exception as e:
                        self._send(json.dumps({'error': str(e)}), 400, 'application/json')
            elif path == '/api/host-stats':
                # Return host performance statistics
                stats = self.host_stats()
                self._send(json.dumps(stats), 200, 'application/json')
            elif path.startswith('/api/migration-status/'):
                # Return migration job status
                job_id = path.split('/')[-1]
                if hasattr(self, 'migration_jobs') and job_id in self.migration_jobs:
                    status = self.migration_jobs[job_id]
                    self._send(json.dumps(status), 200, 'application/json')
                else:
                    self._send(json.dumps({'error': 'Migration job not found'}), 404, 'application/json')
            elif path == '/api/active-migrations':
                # Return list of active migrations
                active_migrations = []
                if hasattr(self, 'migration_jobs'):
                    for job_id, job_info in self.migration_jobs.items():
                        if job_info['status'] in ['starting', 'copying', 'pivoted']:
                            active_migrations.append({
                                'job_id': job_id,
                                'vm_name': job_info['vm_name'],
                                'disk_target': job_info['disk_target'],
                                'status': job_info['status'],
                                'progress': job_info['progress']
                            })
                self._send(json.dumps({'migrations': active_migrations}), 200, 'application/json')
            elif path.startswith('/api/snapshot/'):
                # Handle snapshot operations via API
                action = path.split('/')[-1]  # create, restore, delete
                
                if action == 'create' and form:
                    domain_name = form.get('domain', [''])[0]
                    snap_name = form.get('snap_name', [''])[0]
                    
                    if domain_name and snap_name:
                        cmd = ['virsh', 'snapshot-create-as', domain_name, snap_name, '--disk-only', '--atomic']
                        result = subprocess.run(cmd, capture_output=True, text=True)
                        
                        if result.returncode == 0:
                            self._send('{"status": "success"}', 200, 'application/json')
                        else:
                            self._send(f'{{"status": "error", "message": "{result.stderr}"}}', 400, 'application/json')
                    else:
                        self._send('{"status": "error", "message": "Missing domain or snap_name"}', 400, 'application/json')
                
                elif action == 'restore' and form:
                    domain_name = form.get('domain', [''])[0]
                    snap_name = form.get('snap_name', [''])[0]
                    
                    if domain_name and snap_name:
                        # Stop VM first if running
                        try:
                            d = lv.get_domain(domain_name)
                            if d.isActive():
                                d.destroy()
                        except:
                            pass
                        
                        cmd = ['virsh', 'snapshot-revert', domain_name, snap_name]
                        result = subprocess.run(cmd, capture_output=True, text=True)
                        
                        if result.returncode == 0:
                            self._send('{"status": "success"}', 200, 'application/json')
                        else:
                            self._send(f'{{"status": "error", "message": "{result.stderr}"}}', 400, 'application/json')
                    else:
                        self._send('{"status": "error", "message": "Missing domain or snap_name"}', 400, 'application/json')
                
                elif action == 'delete' and form:
                    domain_name = form.get('domain', [''])[0]
                    snap_name = form.get('snap_name', [''])[0]
                    
                    if domain_name and snap_name:
                        cmd = ['virsh', 'snapshot-delete', domain_name, snap_name]
                        result = subprocess.run(cmd, capture_output=True, text=True)
                        
                        if result.returncode == 0:
                            self._send('{"status": "success"}', 200, 'application/json')
                        else:
                            self._send(f'{{"status": "error", "message": "{result.stderr}"}}', 400, 'application/json')
                    else:
                        self._send('{"status": "error", "message": "Missing domain or snap_name"}', 400, 'application/json')
            
            elif path == '/api/progress':
                # Return progress data for active operations
                pid = qs.get('id', [None])[0]
                if pid:
                    data = PROGRESS.get(pid)
                    if data:
                        self._send(json.dumps(data), 200, 'application/json')
                    else:
                        self._send(json.dumps({'error': 'Progress ID not found'}), 404, 'application/json')
                else:
                    # Return all active progress items
                    self._send(json.dumps(dict(PROGRESS)), 200, 'application/json')
                
            else:
                self._send(json.dumps({'error': 'Not found'}), 404, 'application/json')
        except Exception as e:
            self._send(json.dumps({'error': str(e)}), 500, 'application/json')

    def page_snapshots(self, lv: LV, form: Optional[dict] = None):
        """Snapshots management page"""
        msg = ""
        
        if form:
            try:
                if 'create_snapshot' in form:
                    domain_name = form.get('domain', [''])[0]
                    snap_name = form.get('snap_name', [''])[0]
                    description = form.get('description', [''])[0]
                    
                    if domain_name and snap_name:
                        lv.create_snapshot(domain_name, snap_name, description)
                        msg = f"<div class='alert success'>Snapshot '{snap_name}' created for {domain_name}</div>"
                
                elif 'restore_snapshot' in form:
                    domain_name = form.get('domain', [''])[0]
                    snap_name = form.get('snap_name', [''])[0]
                    
                    if domain_name and snap_name:
                        lv.restore_snapshot(domain_name, snap_name)
                        msg = f"<div class='alert success'>Restored {domain_name} to snapshot '{snap_name}'</div>"
                
                elif 'delete_snapshot' in form:
                    domain_name = form.get('domain', [''])[0]
                    snap_name = form.get('snap_name', [''])[0]
                    
                    if domain_name and snap_name:
                        lv.delete_snapshot(domain_name, snap_name)
                        msg = f"<div class='alert info'>Deleted snapshot '{snap_name}' from {domain_name}</div>"
                        
            except Exception as e:
                msg = f"<div class='alert error'>{html.escape(str(e))}</div>"
        
        # List all VMs and their snapshots
        vm_cards = []
        for domain in lv.list_domains():
            snapshots = lv.list_snapshots(domain.name())
            state, _ = domain.state()
            status = 'running' if state == libvirt.VIR_DOMAIN_RUNNING else 'shutoff'
            
            snap_rows = []
            for snap in snapshots:
                snap_xml = snap.getXMLDesc()
                # Parse creation time from XML if available
                creation_time = "Unknown"
                try:
                    import xml.etree.ElementTree as ET
                    root = ET.fromstring(snap_xml)
                    creation = root.find('creationTime')
                    if creation is not None:
                        creation_time = datetime.datetime.fromtimestamp(int(creation.text)).strftime('%Y-%m-%d %H:%M:%S')
                except:
                    pass
                
                snap_rows.append(f"""
                <tr>
                    <td>{html.escape(snap.getName())}</td>
                    <td>{creation_time}</td>
                    <td>
                        <form method='post' class='inline'>
                            <input type='hidden' name='restore_snapshot' value='1'>
                            <input type='hidden' name='domain' value='{html.escape(domain.name())}'>
                            <input type='hidden' name='snap_name' value='{html.escape(snap.getName())}'>
                            <button class='small secondary' onclick="return confirm('Restore to this snapshot?')">Restore</button>
                        </form>
                        <form method='post' class='inline'>
                            <input type='hidden' name='delete_snapshot' value='1'>
                            <input type='hidden' name='domain' value='{html.escape(domain.name())}'>
                            <input type='hidden' name='snap_name' value='{html.escape(snap.getName())}'>
                            <button class='small danger' onclick="return confirm('Delete this snapshot?')">Delete</button>
                        </form>
                    </td>
                </tr>
                """)
            
            snap_table = f"""
            <table>
                <thead><tr><th>Snapshot</th><th>Created</th><th>Actions</th></tr></thead>
                <tbody>
                    {''.join(snap_rows) if snap_rows else '<tr><td colspan="3"><em>No snapshots</em></td></tr>'}
                </tbody>
            </table>
            """ if snapshots or True else "<p><em>No snapshots</em></p>"
            
            vm_cards.append(f"""
            <div class="card">
                <h4>{html.escape(domain.name())} <span class="badge {status}">{status}</span></h4>
                {snap_table}
                <form method='post' class='inline' style='margin-top:12px'>
                    <input type='hidden' name='create_snapshot' value='1'>
                    <input type='hidden' name='domain' value='{html.escape(domain.name())}'>
                    <div style='display:flex;gap:8px;align-items:end'>
                        <label style='flex:1'>Snapshot Name <input name='snap_name' required placeholder='snapshot-{int(time.time())}'></label>
                        <label style='flex:2'>Description <input name='description' placeholder='Description (optional)'></label>
                        <button class='small success'>Create Snapshot</button>
                    </div>
                    <div class='inline-note' style='margin-top:4px'>ℹ️ Creates disk-only snapshots (excludes memory state). Uses optimized method for running VMs.</div>
                </form>
            </div>
            """)
        
        return f"""
        <div class="card">
            <h3>📸 VM Snapshots</h3>
            {msg}
            <p>Create, restore, and manage VM snapshots for quick rollbacks and testing.</p>
        </div>
        <div class="card-grid">
            {''.join(vm_cards) if vm_cards else '<div class="card"><p><em>No VMs found</em></p></div>'}
        </div>
        """

    def page_backups(self, lv: LV, form: Optional[dict] = None):
        """Backup management page"""
        msg = ""
        
        # Ensure backup directory exists
        os.makedirs(BACKUP_DIR, exist_ok=True)
        
        if form:
            try:
                if 'create_backup' in form:
                    domain_name = form.get('domain', [''])[0]
                    backup_dir = form.get('backup_dir', [BACKUP_DIR])[0] or BACKUP_DIR
                    if domain_name:
                        # Ensure backup directory exists
                        os.makedirs(backup_dir, exist_ok=True)
                        backup_path = lv.backup_vm(domain_name, backup_dir)
                        msg = f"<div class='alert success'>Backup created: {backup_path}</div>"
                
                elif 'restore_backup' in form:
                    backup_path = form.get('backup_path', [''])[0]
                    new_name = form.get('new_name', [''])[0] or None
                    
                    if backup_path and os.path.exists(backup_path):
                        lv.restore_vm_backup(backup_path, new_name)
                        restored_name = new_name or "restored VM"
                        msg = f"<div class='alert success'>Backup restored as: {restored_name}</div>"
                
                elif 'delete_backup' in form:
                    backup_path = form.get('backup_path', [''])[0]
                    if backup_path and os.path.exists(backup_path):
                        shutil.rmtree(backup_path)
                        msg = f"<div class='alert info'>Backup deleted: {os.path.basename(backup_path)}</div>"
                        
            except Exception as e:
                msg = f"<div class='alert error'>{html.escape(str(e))}</div>"
        
        # List VMs for backup creation
        vm_options = ''.join(f"<option value='{html.escape(d.name())}'>{html.escape(d.name())}</option>" for d in lv.list_domains())
        
        # List existing backups
        backup_rows = []
        try:
            for backup_dir in sorted(os.listdir(BACKUP_DIR)):
                backup_path = os.path.join(BACKUP_DIR, backup_dir)
                if os.path.isdir(backup_path):
                    manifest_path = os.path.join(backup_path, 'manifest.json')
                    if os.path.exists(manifest_path):
                        try:
                            with open(manifest_path, 'r') as f:
                                manifest = json.load(f)
                            
                            # Calculate backup size
                            total_size = 0
                            for root, dirs, files in os.walk(backup_path):
                                for file in files:
                                    total_size += os.path.getsize(os.path.join(root, file))
                            
                            backup_rows.append(f"""
                            <tr>
                                <td>{html.escape(manifest['domain_name'])}</td>
                                <td>{manifest['backup_time'][:19].replace('T', ' ')}</td>
                                <td>{human_bytes(total_size)}</td>
                                <td>{'Yes' if manifest.get('was_running') else 'No'}</td>
                                <td>
                                    <button class='small secondary' onclick="openRestoreModal('{html.escape(backup_path)}', '{html.escape(manifest['domain_name'])}')">Restore</button>
                                    <form method='post' class='inline'>
                                        <input type='hidden' name='delete_backup' value='1'>
                                        <input type='hidden' name='backup_path' value='{html.escape(backup_path)}'>
                                        <button class='small danger' onclick="return confirm('Delete this backup?')">Delete</button>
                                    </form>
                                </td>
                            </tr>
                            """)
                        except:
                            pass
        except:
            pass
        
        backup_table = f"""
        <table>
            <thead><tr><th>VM Name</th><th>Backup Time</th><th>Size</th><th>Was Running</th><th>Actions</th></tr></thead>
            <tbody>
                {''.join(backup_rows) if backup_rows else '<tr><td colspan="5"><em>No backups found</em></td></tr>'}
            </tbody>
        </table>
        """
        
        # Restore modal
        restore_modal = """
        <div class='modal' id='modal_restore_backup' hidden>
            <div class='panel'>
                <div style='display:flex;justify-content:space-between;align-items:center'>
                    <h3>🔄 Restore Backup</h3>
                    <button class='close secondary' onclick="closeModal('modal_restore_backup')">×</button>
                </div>
                <form method='post'>
                    <input type='hidden' name='restore_backup' value='1'>
                    <input type='hidden' id='restore_backup_path' name='backup_path' value=''>
                    
                    <p>Restore backup of: <strong id='restore_original_name'></strong></p>
                    
                    <label>New VM Name (leave empty to use original name)
                        <input name='new_name' placeholder='Optional: new-vm-name'>
                    </label>
                    
                    <div style='margin-top:16px'>
                        <input type='submit' class='button success' value='Restore Backup'>
                        <button type='button' class='button secondary' onclick="closeModal('modal_restore_backup')">Cancel</button>
                    </div>
                </form>
            </div>
        </div>
        
        <script>
        function openRestoreModal(backupPath, originalName) {
            document.getElementById('restore_backup_path').value = backupPath;
            document.getElementById('restore_original_name').textContent = originalName;
            openModal('modal_restore_backup');
        }
        </script>
        """
        
        return f"""
        <div class="card">
            <h3>💾 VM Backups</h3>
            {msg}
            <p>Create full VM backups and restore them when needed. Backups are stored in: <code>{BACKUP_DIR}</code></p>
            
            <form method='post' class='inline' style='margin-top:16px'>
                <input type='hidden' name='create_backup' value='1'>
                <div style='display:grid;gap:12px;grid-template-columns:1fr 1fr auto;align-items:end'>
                    <label>VM to Backup <select name='domain' class='enh'>{vm_options}</select></label>
                    <label>Backup Directory <input name='backup_dir' value='{BACKUP_DIR}' placeholder='/path/to/backup/dir'></label>
                    <button class='success'>Create Backup</button>
                </div>
            </form>
        </div>
        
        <div class="card">
            <h4>📦 Existing Backups</h4>
            {backup_table}
        </div>
        
        {restore_modal}
        """

    def page_networks(self, lv: LV, form: Optional[dict] = None):
        """Network management page redirecting to Cockpit"""
        # Get the host IP address
        import socket
        try:
            # Connect to a remote address to determine the local IP
            s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
            s.connect(("8.8.8.8", 80))
            host_ip = s.getsockname()[0]
            s.close()
        except Exception:
            # Fallback to localhost if unable to determine IP
            host_ip = "127.0.0.1"
        
        # Get NetworkManager bridges (read-only)
        bridge_rows = []
        try:
            result = subprocess.run(['sudo', 'nmcli', '-t', '-f', 'NAME,TYPE,DEVICE,STATE', 'connection', 'show'], 
                                  capture_output=True, text=True, timeout=5)
            if result.returncode == 0:
                for line in result.stdout.strip().split('\n'):
                    if line and 'bridge' in line:
                        parts = line.split(':')
                        if len(parts) >= 4:
                            name, conn_type, device, state = parts[:4]
                            if conn_type == 'bridge':
                                # Get IP address
                                ip_result = subprocess.run(['sudo', 'nmcli', '-t', '-f', 'IP4.ADDRESS', 'connection', 'show', name],
                                                         capture_output=True, text=True, timeout=3)
                                ip_addr = ip_result.stdout.strip().replace('IP4.ADDRESS:', '') if ip_result.returncode == 0 else 'N/A'
                                
                                bridge_rows.append(f"""
                                <tr>
                                    <td>{html.escape(name)}</td>
                                    <td><span class="badge {'running' if state == 'activated' else 'shutoff'}">{html.escape(state)}</span></td>
                                    <td>{html.escape(device or 'N/A')}</td>
                                    <td>{html.escape(ip_addr)}</td>
                                </tr>
                                """)
        except Exception as e:
            bridge_rows.append(f"<tr><td colspan='4'><em>Error listing bridges: {html.escape(str(e))}</em></td></tr>")
        
        bridge_table = f"""
        <table>
            <thead><tr><th>Name</th><th>Status</th><th>Device</th><th>IP Address</th></tr></thead>
            <tbody>
                {''.join(bridge_rows) if bridge_rows else '<tr><td colspan="4"><em>No NetworkManager bridges found</em></td></tr>'}
            </tbody>
        </table>
        """
        
        return f"""
        <div class="card">
            <h3>🌐 Network Configuration</h3>
            <p>Network configuration is managed through Cockpit's web interface.</p>
            <p>Click the link below to access the network configuration:</p>
            <p style="margin: 20px 0;">
                <a href="https://{host_ip}:9090/network" target="_blank" class="button" style="font-size: 16px; padding: 12px 24px;">
                    🌐 Open Cockpit Networks Configuration
                </a>
            </p>
            <p class="inline-note">
                <strong>Note:</strong> This will open Cockpit's network configuration in a new tab. 
                You may need to accept the SSL certificate if this is your first time accessing Cockpit.
            </p>
        </div>
        
        <div class="card">
            <h4>🌉 Current NetworkManager Bridges</h4>
            <p class="inline-note">View existing bridges below. Use Cockpit for configuration changes.</p>
            {bridge_table}
        </div>
        """
    # Screenshot -> inline console
    def screenshot(self, lv:LV, d):
        import threading
        import time
        
        def screenshot_worker(result_container):
            """Worker function to capture screenshot with timeout"""
            try:
                stream = lv.conn.newStream(0)
                try:
                    # Try to get higher resolution by specifying screen 0 with flags
                    fmt = d.screenshot(stream, 0, libvirt.VIR_DOMAIN_SCREENSHOT_CONSOLE)
                except:
                    # Fallback to basic screenshot
                    fmt = d.screenshot(stream, 0)
                
                buf = BytesIO()
                start_time = time.time()
                
                while True:
                    try:
                        # Check for timeout within the read loop
                        if time.time() - start_time > 5:  # 5 second timeout
                            raise TimeoutError("Screenshot read timeout")
                        
                        chunk = stream.recv(65536)
                        if not chunk: 
                            break
                        buf.write(chunk)
                    except libvirt.libvirtError: 
                        break
                    except TimeoutError:
                        break
                
                raw = buf.getvalue()
                
                if raw:
                    if fmt == 'ppm':
                        png = self.ppm_to_png(raw)
                        data = png if png else raw
                        ctype = 'image/png' if png else 'image/x-portable-pixmap'
                    else:
                        data = raw
                        ctype = f'image/{fmt}'
                    
                    result_container['data'] = data
                    result_container['ctype'] = ctype
                    result_container['success'] = True
                else:
                    result_container['success'] = False
                    result_container['error'] = 'No screenshot data received'
                
                try:
                    stream.finish()
                except:
                    pass
                    
            except Exception as e:
                result_container['success'] = False
                result_container['error'] = str(e)
        
        # Use threading to implement timeout
        result_container = {'success': False, 'error': 'Unknown error'}
        worker_thread = threading.Thread(target=screenshot_worker, args=(result_container,))
        worker_thread.daemon = True
        worker_thread.start()
        worker_thread.join(timeout=8)  # 8 second overall timeout
        
        if worker_thread.is_alive():
            # Thread is still running, screenshot timed out
            result_container['success'] = False
            result_container['error'] = 'Screenshot operation timed out'
        
        # Add no-cache headers to prevent browser caching issues
        cache_headers = {
            'Cache-Control': 'no-cache, no-store, must-revalidate',
            'Pragma': 'no-cache',
            'Expires': '0'
        }
        
        if result_container['success']:
            self._send(result_container['data'], 200, result_container['ctype'], cache_headers)
        else:
            # Return a simple error image
            error_msg = result_container.get('error', 'Screenshot failed')
            error_data = self.generate_simple_error_image(error_msg)
            self._send(error_data, 200, 'image/png', cache_headers)
    
    def generate_simple_error_image(self, message):
        """Generate a simple black PNG with error text"""
        # Create a minimal 320x240 black PNG
        width, height = 320, 240
        
        # PNG signature
        png_sig = b'\x89PNG\r\n\x1a\n'
        
        # IHDR chunk (width, height, bit_depth=8, color_type=0 (grayscale), compression=0, filter=0, interlace=0)
        ihdr_data = struct.pack('>IIBBBBB', width, height, 8, 0, 0, 0, 0)
        ihdr_crc = zlib.crc32(b'IHDR' + ihdr_data) & 0xffffffff
        ihdr = struct.pack('>I', len(ihdr_data)) + b'IHDR' + ihdr_data + struct.pack('>I', ihdr_crc)
        
        # IDAT chunk (compressed black pixels)
        pixels = b'\x00' * (width + 1) * height  # +1 for filter byte per row
        idat_data = zlib.compress(pixels)
        idat_crc = zlib.crc32(b'IDAT' + idat_data) & 0xffffffff
        idat = struct.pack('>I', len(idat_data)) + b'IDAT' + idat_data + struct.pack('>I', idat_crc)
        
        # IEND chunk
        iend_crc = zlib.crc32(b'IEND') & 0xffffffff
        iend = struct.pack('>I', 0) + b'IEND' + struct.pack('>I', iend_crc)
        
        return png_sig + ihdr + idat + iend
    def ppm_to_png(self, ppm:bytes):  # minimalist converter
        try:
            parts=ppm.split(b'\n');
            if parts[0]!=b'P6': return None
            i=1
            while parts[i].startswith(b'#'): i+=1
            dims=parts[i]; i+=1
            while parts[i].startswith(b'#'): i+=1
            maxv=parts[i]; i+=1
            width,height=map(int,dims.split()); maxval=int(maxv)
            pixel=b'\n'.join(parts[i:])
            def chunk(t,d): return struct.pack('!I',len(d))+t+d+struct.pack('!I', zlib.crc32(t+d)&0xffffffff)
            sig=b'\x89PNG\r\n\x1a\n'; ihdr=struct.pack('!IIBBBBB',width,height,8,2,0,0,0)
            stride=width*3; scan=BytesIO()
            for y in range(height): scan.write(b'\x00'+pixel[y*stride:y*stride+stride])
            idat=zlib.compress(scan.getvalue(),6)
            return sig+chunk(b'IHDR',ihdr)+chunk(b'IDAT',idat)+chunk(b'IEND',b'')
        except: return None
    # Pages
    def page_dashboard(self, lv:LV):
        # Get host performance data
        host_perf = self.host_stats()
        
        # Format with unit conversion (KB/s to B/s, MB/s, or GB/s without decimals)
        def format_rate(kbps):
            bytes_per_sec = kbps * 1024
            if bytes_per_sec >= 1024 * 1024 * 1024:
                return f"{int(bytes_per_sec / (1024 * 1024 * 1024))}GB/s"
            elif bytes_per_sec >= 1024 * 1024:
                return f"{int(bytes_per_sec / (1024 * 1024))}MB/s"
            elif bytes_per_sec >= 1024:
                return f"{int(bytes_per_sec / 1024)}KB/s"
            else:
                return f"{int(bytes_per_sec)}B/s"
        
        # Format the new iotop-style I/O metrics
        fs_read_display = format_rate(host_perf.get('phys_rd_kbps', 0))
        fs_write_display = format_rate(host_perf.get('phys_wr_kbps', 0))
        
        # Performance cards with 3 metrics
        stats_cards = f"""
        <div class="stats-grid">
            <div class="stat-card">
                <div class="stat-value">{host_perf['cpu_pct']:.1f}%</div>
                <div class="stat-label">CPU Usage</div>
            </div>
            <div class="stat-card">
                <div class="stat-value">{host_perf['mem_used_h']} / {host_perf['mem_total_h']}</div>
                <div class="stat-label">Memory ({host_perf['mem_pct']:.1f}%)</div>
            </div>
            <div class="stat-card">
                <div class="stat-value">Read: {fs_read_display}<br>Write: {fs_write_display}</div>
                <div class="stat-label">Filesystem I/O</div>
            </div>
        </div>
        """
        
        rows = []
        for d in lv.list_domains():
            state, _ = d.state()
            # Check if libvirt.VIR_DOMAIN_RUNNING exists, otherwise use numeric value
            running_state = getattr(libvirt, 'VIR_DOMAIN_RUNNING', 1) if hasattr(libvirt, 'VIR_DOMAIN_RUNNING') else 1
            status = 'running' if state == running_state else 'shutoff'
            
            # Calculate storage information
            storage_info = "-"
            try:
                import xml.etree.ElementTree as ET
                xml = d.XMLDesc(libvirt.VIR_DOMAIN_XML_INACTIVE)
                root = ET.fromstring(xml)
                total_used = 0
                total_allocated = 0
                disk_count = 0
                
                for disk in root.findall('.//devices/disk[@type="file"][@device="disk"]'):
                    source = disk.find('source')
                    if source is not None and source.get('file'):
                        disk_path = source.get('file')
                        used_space, allocated_space = self.get_disk_usage(disk_path)
                        total_used += used_space
                        total_allocated += allocated_space
                        disk_count += 1
                
                if disk_count > 0:
                    storage_info = f"{total_used:.1f}G / {total_allocated:.1f}G"
            except Exception:
                storage_info = "-"
            
            # Determine status color outside f-string to avoid nested quotes
            status_color = "#4a9eff" if status == "running" else "#666"
            
            rows.append(
                f"<tr data-vm='{html.escape(d.name())}'><td><div style='display:flex;align-items:center;gap:8px;'><div style='width:8px;height:8px;border-radius:50%;background:{status_color};'></div><a href='/?domain={urllib.parse.quote(d.name())}' style='font-weight:500;text-decoration:none;color:var(--text);'>{html.escape(d.name())}</a></div></td><td><span class='badge {status}'>{status}</span></td><td class='cpu'>-</td><td class='mem'>-</td><td class='mem_pct'>-</td><td class='io'>-</td><td class='storage'>{storage_info}</td><td>{self.row_actions(d,status)}</td></tr>"
            )
        tbl = (
            "<table id='vm_table'><thead><tr><th>Name</th><th>Status</th><th>CPU%</th><th>Memory</th><th>Mem%</th><th>Disk R/W</th><th>Storage</th><th>Actions</th></tr></thead><tbody>"
            + "".join(rows)
            + "</tbody></table>"
        )
        
        # Quick actions
        quick_actions = """
        <div style="margin: 16px 0; display: flex; gap: 12px; flex-wrap: wrap;">
            <button class="button" onclick="openModal('modal_vm')">🆕 Create VM</button>
            <a href="/?backups=1" class="button secondary">💾 Backups</a>
        </div>
        """
        
        return (
            f"<div class='card'><h3>🖥️ Virtual Machines Dashboard</h3>{stats_cards}{quick_actions}{tbl}</div>"
            + self.modal_vm(lv)
            + """
            <script>
            function refreshVMStatus() {
                // Refresh VM status on dashboard
                const isDashboard = window.location.pathname === '/' && !window.location.search.includes('domain=');
                const isVMDetail = window.location.search.includes('domain=');
                
                if (isDashboard) {
                    fetch('/')
                        .then(response => response.text())
                        .then(html => {
                            const parser = new DOMParser();
                            const doc = parser.parseFromString(html, 'text/html');
                            
                            // Update VM table rows
                            const newTable = doc.querySelector('#vm_table tbody');
                            const currentTable = document.querySelector('#vm_table tbody');
                            
                            if (newTable && currentTable) {
                                const newRows = newTable.querySelectorAll('tr[data-vm]');
                                const currentRows = currentTable.querySelectorAll('tr[data-vm]');
                                
                                newRows.forEach((newRow) => {
                                    const vmName = newRow.getAttribute('data-vm');
                                    const currentRow = currentTable.querySelector(`tr[data-vm="${vmName}"]`);
                                    
                                    if (currentRow) {
                                        // Update status badge
                                        const oldBadge = currentRow.querySelector('.badge');
                                        const newBadge = newRow.querySelector('.badge');
                                        if (oldBadge && newBadge && oldBadge.textContent !== newBadge.textContent) {
                                            oldBadge.textContent = newBadge.textContent;
                                            oldBadge.className = newBadge.className;
                                        }
                                        
                                        // Update status indicator dot
                                        const oldDot = currentRow.querySelector('div[style*="border-radius:50%"]');
                                        const newDot = newRow.querySelector('div[style*="border-radius:50%"]');
                                        if (oldDot && newDot && oldDot.style.background !== newDot.style.background) {
                                            oldDot.style.background = newDot.style.background;
                                        }
                                        
                                        // Update action buttons (last td)
                                        const oldActions = currentRow.querySelector('td:last-child');
                                        const newActions = newRow.querySelector('td:last-child');
                                        if (oldActions && newActions) {
                                            oldActions.innerHTML = newActions.innerHTML;
                                        }
                                    }
                                });
                            }
                        })
                        .catch(err => console.warn('Status refresh failed:', err));
                } else if (isVMDetail) {
                    fetch(window.location.href)
                        .then(response => response.text())
                        .then(html => {
                            const parser = new DOMParser();
                            const doc = parser.parseFromString(html, 'text/html');
                            
                            // Update action buttons
                            const newActions = doc.querySelector('.action-buttons');
                            const currentActions = document.querySelector('.action-buttons');
                            if (newActions && currentActions) {
                                currentActions.innerHTML = newActions.innerHTML;
                            }
                        })
                        .catch(err => console.warn('Status refresh failed:', err));
                }
            }
            
            function takeSnapshot(vmName) {
                // Auto-generate snapshot name: vmname-YYYYMMDD-HHMMSS
                const now = new Date();
                const timestamp = now.getFullYear() + 
                    String(now.getMonth() + 1).padStart(2, '0') + 
                    String(now.getDate()).padStart(2, '0') + '-' +
                    String(now.getHours()).padStart(2, '0') + 
                    String(now.getMinutes()).padStart(2, '0') + 
                    String(now.getSeconds()).padStart(2, '0');
                const snapName = vmName + '-' + timestamp;
                
                // Show loading indicator
                const button = event.target;
                const originalText = button.innerHTML;
                button.innerHTML = '⏳ Creating...';
                button.disabled = true;
                
                const params = new URLSearchParams();
                params.append('domain', vmName);
                params.append('snap_name', snapName);
                
                fetch('/api/snapshot/create', {
                    method: 'POST',
                    headers: {'Content-Type': 'application/x-www-form-urlencoded'},
                    body: params.toString()
                }).then(response => response.json()).then(data => {
                    button.innerHTML = originalText;
                    button.disabled = false;
                    if (data.status === 'success') {
                        // Show success message briefly
                        button.innerHTML = '✅ Done';
                        setTimeout(() => {
                            button.innerHTML = originalText;
                        }, 2000);
                    } else {
                        alert('Snapshot creation failed: ' + (data.message || 'Unknown error'));
                    }
                }).catch(error => {
                    button.innerHTML = originalText;
                    button.disabled = false;
                    alert('Network error. Please try again.');
                });
            }
            
            function vmAction(domain, action, needsConfirm = false) {
                // Show loading indicator
                const button = event.target;
                const originalText = button.innerHTML;
                button.innerHTML = '⏳ Working...';
                button.disabled = true;
                
                const params = new URLSearchParams();
                params.append('domain', domain);
                params.append('op', action);
                if (needsConfirm) params.append('confirm', '1');
                
                fetch('/?' + params.toString(), {
                    method: 'POST',
                    headers: {'Content-Type': 'application/x-www-form-urlencoded'},
                    body: ''
                }).then(response => {
                    if (response.ok) {
                        // Success - restore button and trigger immediate status refresh
                        button.innerHTML = originalText;
                        button.disabled = false;
                        
                        // Trigger immediate status update
                        refreshVMStatus();
                        
                        // For shutdown/destroy actions, check more frequently for a few seconds
                        if (action === 'shutdown' || action === 'destroy') {
                            let checks = 0;
                            const quickRefresh = setInterval(() => {
                                refreshVMStatus();
                                checks++;
                                if (checks >= 6) { // Check 6 times (3 seconds at 500ms intervals)
                                    clearInterval(quickRefresh);
                                }
                            }, 500);
                        }
                    } else {
                        // Error - restore button and show message
                        button.innerHTML = originalText;
                        button.disabled = false;
                        alert('Action failed. Please try again.');
                    }
                }).catch(error => {
                    // Network error - restore button
                    button.innerHTML = originalText;
                    button.disabled = false;
                    alert('Network error. Please try again.');
                });
            }
            
            // Auto-refresh performance data every 5 seconds
            setInterval(function() {
                fetch('/api/host-stats')
                    .then(response => response.json())
                    .then(data => {
                        // Update CPU
                        document.querySelector('.stats-grid .stat-card:nth-child(1) .stat-value').textContent = data.cpu_pct.toFixed(1) + '%';
                        // Update Memory
                        document.querySelector('.stats-grid .stat-card:nth-child(2) .stat-value').textContent = data.mem_used_h + ' / ' + data.mem_total_h;
                        document.querySelector('.stats-grid .stat-card:nth-child(2) .stat-label').textContent = 'Memory (' + data.mem_pct.toFixed(1) + '%)';
                        
                        // Update Filesystem I/O
                        if (data.phys_rd_kbps !== undefined && data.phys_wr_kbps !== undefined) {
                            
                            // Format with unit conversion (KB/s to B/s, MB/s, or GB/s without decimals)
                            function formatRate(kbps) {
                                const bytesPerSec = kbps * 1024;
                                if (bytesPerSec >= 1024 * 1024 * 1024) {
                                    return Math.floor(bytesPerSec / (1024 * 1024 * 1024)) + 'GB/s';
                                } else if (bytesPerSec >= 1024 * 1024) {
                                    return Math.floor(bytesPerSec / (1024 * 1024)) + 'MB/s';
                                } else if (bytesPerSec >= 1024) {
                                    return Math.floor(bytesPerSec / 1024) + 'KB/s';
                                } else {
                                    return Math.floor(bytesPerSec) + 'B/s';
                                }
                            }
                            
                            // Update Filesystem I/O (3rd card)
                            const fsReadDisplay = formatRate(data.phys_rd_kbps);
                            const fsWriteDisplay = formatRate(data.phys_wr_kbps);
                            const fsIo = 'Read: ' + fsReadDisplay + '<br>Write: ' + fsWriteDisplay;
                            document.querySelector('.stats-grid .stat-card:nth-child(3) .stat-value').innerHTML = fsIo;
                        }
                        // Only skip update if data is undefined (no data available)
                    })
                    .catch(error => console.log('Stats update failed:', error));
            }, 1000);
            </script>
            """
        )
    
    def convert_key_to_qmp(self, key, key_code):
        """Convert JavaScript key to virsh send-key format"""
        # Map common keys to virsh key names (these are the correct codes for virsh send-key)
        key_map = {
            'Enter': 'KEY_ENTER',
            'Backspace': 'KEY_BACKSPACE', 
            'Tab': 'KEY_TAB',
            'Escape': 'KEY_ESC',
            'Space': 'KEY_SPACE',
            ' ': 'KEY_SPACE',
            'ArrowUp': 'KEY_UP',
            'ArrowDown': 'KEY_DOWN',
            'ArrowLeft': 'KEY_LEFT',
            'ArrowRight': 'KEY_RIGHT',
            'Delete': 'KEY_DELETE',
            'Home': 'KEY_HOME',
            'End': 'KEY_END',
            'PageUp': 'KEY_PAGEUP',
            'PageDown': 'KEY_PAGEDOWN',
            'Insert': 'KEY_INSERT',
            'F1': 'KEY_F1', 'F2': 'KEY_F2', 'F3': 'KEY_F3', 'F4': 'KEY_F4',
            'F5': 'KEY_F5', 'F6': 'KEY_F6', 'F7': 'KEY_F7', 'F8': 'KEY_F8',
            'F9': 'KEY_F9', 'F10': 'KEY_F10', 'F11': 'KEY_F11', 'F12': 'KEY_F12',
            'Shift': 'KEY_LEFTSHIFT', 'Control': 'KEY_LEFTCTRL', 'Alt': 'KEY_LEFTALT',
            'Meta': 'KEY_LEFTMETA', 'CapsLock': 'KEY_CAPSLOCK',
        }
        
        # Check if it's a mapped key
        if key in key_map:
            return key_map[key]
        
        # For single characters, convert to KEY_X format
        if len(key) == 1:
            if key.isalpha():
                # For letters, always use the base key (lowercase)
                return f'KEY_{key.upper()}'
            elif key.isdigit():
                return f'KEY_{key}'
            else:
                # Special characters - map to their base keys
                # The shift handling happens at the endpoint level
                char_map = {
                    # Shifted number row
                    '!': 'KEY_1', '@': 'KEY_2', '#': 'KEY_3', '$': 'KEY_4', '%': 'KEY_5',
                    '^': 'KEY_6', '&': 'KEY_7', '*': 'KEY_8', '(': 'KEY_9', ')': 'KEY_0',
                    # Base punctuation
                    '-': 'KEY_MINUS', '_': 'KEY_MINUS',
                    '=': 'KEY_EQUAL', '+': 'KEY_EQUAL',
                    '[': 'KEY_LEFTBRACE', '{': 'KEY_LEFTBRACE',
                    ']': 'KEY_RIGHTBRACE', '}': 'KEY_RIGHTBRACE',
                    '\\': 'KEY_BACKSLASH', '|': 'KEY_BACKSLASH',
                    ';': 'KEY_SEMICOLON', ':': 'KEY_SEMICOLON',
                    "'": 'KEY_APOSTROPHE', '"': 'KEY_APOSTROPHE',
                    '`': 'KEY_GRAVE', '~': 'KEY_GRAVE',
                    ',': 'KEY_COMMA', '<': 'KEY_COMMA',
                    '.': 'KEY_DOT', '>': 'KEY_DOT',
                    '/': 'KEY_SLASH', '?': 'KEY_SLASH',
                }
                return char_map.get(key, None)
            
        return None
    
    def send_qmp_key(self, domain, qmp_key):
        """Send key event to VM via virsh send-key"""
        try:
            # Use virsh send-key with the correct key format
            domain_name = domain.name()
            
            # Try multiple approaches as different systems may use different formats
            key_formats = [
                qmp_key,  # Try the KEY_ format first
                qmp_key.replace('KEY_', '').lower(),  # Try without KEY_ prefix, lowercase
                qmp_key.replace('KEY_', '')  # Try without KEY_ prefix, same case
            ]
            
            for key_format in key_formats:
                cmd = ['virsh', 'send-key', domain_name, key_format]
                logger.info(f"Trying key command: {' '.join(cmd)}")
                
                result = subprocess.run(cmd, capture_output=True, text=True, timeout=10)
                
                if result.returncode == 0:
                    logger.info(f"Key sent successfully to {domain_name}: {key_format}")
                    return True
                else:
                    logger.warning(f"Key format '{key_format}' failed: {result.stderr.strip()}")
            
            # If all formats failed, log final error
            logger.error(f"All key format attempts failed for {domain_name}, key: {qmp_key}")
            return False
                
        except subprocess.TimeoutExpired:
            logger.error("virsh send-key timeout")
            return False
        except Exception as e:
            logger.error(f"Key send error: {e}")
            return False
    
    def send_qmp_key_release(self, domain, qmp_key):
        """Send key release event to VM via virsh (limited support)"""
        try:
            # virsh send-key doesn't have explicit key release, 
            # it sends a complete key press+release cycle
            # For modifier keys, we just log the release
            domain_name = domain.name()
            logger.info(f"Key release logged for {domain_name}: {qmp_key}")
            return True
        except Exception as e:
            logger.error(f"Key release error: {e}")
            return False
    
    def send_qmp_mouse(self, domain, x, y, button):
        """Send mouse event to VM via QMP monitor"""
        try:
            domain_name = domain.name()
            logger.info(f"Mouse event for {domain_name}: {x},{y} button {button}")
            
            # Try to send mouse event via QMP using absolute positioning
            try:
                # Use QMP JSON command for absolute mouse positioning
                # This works better with VNC than relative positioning
                qmp_cmd = {
                    "execute": "input-send-event",
                    "arguments": {
                        "events": [
                            {
                                "type": "abs",
                                "data": {
                                    "axis": "x",
                                    "value": int(x)
                                }
                            },
                            {
                                "type": "abs", 
                                "data": {
                                    "axis": "y",
                                    "value": int(y)
                                }
                            },
                            {
                                "type": "btn",
                                "data": {
                                    "button": "left" if button == 1 else "right" if button == 3 else "middle",
                                    "down": True
                                }
                            },
                            {
                                "type": "btn",
                                "data": {
                                    "button": "left" if button == 1 else "right" if button == 3 else "middle", 
                                    "down": False
                                }
                            }
                        ]
                    }
                }
                
                import json
                qmp_json = json.dumps(qmp_cmd)
                
                # Send via virsh qemu-monitor-command with QMP
                cmd = ['virsh', 'qemu-monitor-command', domain_name, '--pretty', qmp_json]
                result = subprocess.run(cmd, capture_output=True, text=True, timeout=5)
                
                if result.returncode == 0:
                    logger.info(f"Mouse click sent via QMP JSON: {x},{y} button {button}")
                    return True
                else:
                    logger.warning(f"QMP mouse command failed: {result.stderr}")
                    
                # Fallback to HMP commands
                move_cmd = ['virsh', 'qemu-monitor-command', domain_name, '--hmp', f'mouse_move {x} {y}']
                move_result = subprocess.run(move_cmd, capture_output=True, text=True, timeout=5)
                
                if move_result.returncode == 0:
                    # Send mouse button press and release
                    press_cmd = ['virsh', 'qemu-monitor-command', domain_name, '--hmp', f'mouse_button {button}']
                    press_result = subprocess.run(press_cmd, capture_output=True, text=True, timeout=5)
                    
                    if press_result.returncode == 0:
                        logger.info(f"Mouse click sent via HMP: {x},{y} button {button}")
                        return True
                    else:
                        logger.warning(f"HMP mouse button failed: {press_result.stderr}")
                else:
                    logger.warning(f"HMP mouse move failed: {move_result.stderr}")
                    
            except Exception as e:
                logger.warning(f"QMP mouse command failed: {e}")
            
            # Always return True to provide visual feedback even if command fails
            logger.info(f"Mouse event processed: {x},{y} button {button}")
            return True
                
        except Exception as e:
            logger.error(f"Mouse send error: {e}")
            return False
    
    def get_domain_snapshots(self, domain):
        """Get list of snapshots for a domain with details"""
        snapshots = []
        try:
            # Get snapshot names using the correct method
            snapshot_names = domain.snapshotListNames(0)
            for snap_name in snapshot_names:
                try:
                    snap = domain.snapshotLookupByName(snap_name, 0)
                    snap_xml = snap.getXMLDesc(0)
                    
                    # Parse snapshot XML for details
                    import xml.etree.ElementTree as ET
                    root = ET.fromstring(snap_xml)
                    
                    # Get creation time
                    creation_time = root.findtext('creationTime', '0')
                    try:
                        import datetime
                        dt = datetime.datetime.fromtimestamp(int(creation_time))
                        creation_str = dt.strftime('%Y-%m-%d %H:%M:%S')
                    except:
                        creation_str = 'Unknown'
                    
                    # Get description
                    description = root.findtext('description', 'No description')
                    
                    # Get state (running, shutoff)
                    state = root.findtext('state', 'unknown')
                    
                    snapshots.append({
                        'name': snap_name,
                        'description': description,
                        'creation_time': creation_str,
                        'state': state
                    })
                except Exception as e:
                    logger.error(f"Error getting snapshot details for {snap_name}: {e}")
                    # Add basic info even if details fail
                    snapshots.append({
                        'name': snap_name,
                        'description': 'Error loading details',
                        'creation_time': 'Unknown',
                        'state': 'unknown'
                    })
                    
        except Exception as e:
            logger.error(f"Error listing snapshots: {e}")
            
        return sorted(snapshots, key=lambda x: x['creation_time'], reverse=True)

    def row_actions(self,d,status):
        n=urllib.parse.quote(d.name())
        if status=='running':
            return " ".join([
                f"<a href='/novnc/vnc.html?path=vnc_ws/{n}&autoconnect=true' class='button small secondary' title='Open VNC Console' onclick=\"window.open(this.href, 'vnc_console', 'width=1024,height=768,resizable=yes,scrollbars=yes'); return false;\">🖥️ Console</a>",
                f"<button type='button' class='button secondary small' onclick=\"vmAction('{html.escape(d.name())}', 'shutdown')\">⏹️ Shutdown</button>",
                f"<button type='button' class='button small' onclick=\"vmAction('{html.escape(d.name())}', 'reboot')\">🔄 Reboot</button>",
                f"<button type='button' class='button danger small' onclick=\"if(confirm('Force stop VM?')) vmAction('{html.escape(d.name())}', 'destroy', true)\">⚡ Force</button>",
                f"<button type='button' class='button small tertiary' onclick=\"takeSnapshot('{html.escape(d.name())}')\">📸 Snapshot</button>"])
        return " ".join([
            f"<button type='button' class='button small' onclick=\"vmAction('{html.escape(d.name())}', 'start')\">▶️ Start</button>",
            f"<button type='button' class='button small tertiary' onclick=\"takeSnapshot('{html.escape(d.name())}')\">📸 Snapshot</button>",
            f"<button type='button' class='button danger small' onclick=\"if(confirm('Delete domain (files & NVRAM)?')) vmAction('{html.escape(d.name())}', 'undefine', true)\">🗑️ Delete</button>"])

    def get_disk_usage(self, disk_path):
        """Get actual disk usage using qemu-img info
        Returns (used_space, allocated_space) where:
        - used_space = disk size (actual consumed space)
        - allocated_space = virtual size (file length)
        """
        if not disk_path or not os.path.exists(disk_path):
            return 0, 0
        try:
            result = subprocess.run(['sudo','qemu-img', 'info', '--force-share', disk_path], 
                                  capture_output=True, text=True, timeout=10)
            if result.returncode == 0:
                used_space = 0      # disk size = actual consumed space
                allocated_space = 0 # virtual size = file length (allocated)
                for line in result.stdout.split('\n'):
                    if 'disk size:' in line.lower():
                        # Extract disk size (actual consumed space)
                        # Format: "disk size: 21 GiB"
                        size_str = line.split(':')[1].strip()
                        if 'GiB' in size_str or 'GB' in size_str or 'G' in size_str:
                            # Extract number before GiB/GB/G
                            import re
                            match = re.search(r'(\d+\.?\d*)\s*[GT]i?B?', size_str)
                            if match:
                                used_space = float(match.group(1))
                        elif 'MiB' in size_str or 'MB' in size_str or 'M' in size_str:
                            import re
                            match = re.search(r'(\d+\.?\d*)\s*[MT]i?B?', size_str)
                            if match:
                                used_space = float(match.group(1)) / 1024
                        elif 'KiB' in size_str or 'KB' in size_str or 'K' in size_str:
                            import re
                            match = re.search(r'(\d+\.?\d*)\s*[KT]i?B?', size_str)
                            if match:
                                used_space = float(match.group(1)) / (1024 * 1024)
                    elif 'virtual size:' in line.lower():
                        # Extract virtual size (allocated file length)
                        # Format: "virtual size: 40 GiB (42949672960 bytes)"
                        size_part = line.split(':')[1].strip()
                        if 'GiB' in size_part or 'GB' in size_part or 'G' in size_part:
                            import re
                            match = re.search(r'(\d+\.?\d*)\s*[GT]i?B?', size_part)
                            if match:
                                allocated_space = float(match.group(1))
                        elif 'MiB' in size_part or 'MB' in size_part or 'M' in size_part:
                            import re
                            match = re.search(r'(\d+\.?\d*)\s*[MT]i?B?', size_part)
                            if match:
                                allocated_space = float(match.group(1)) / 1024
                return used_space, allocated_space
        except Exception as e:
            # Fallback to file size
            try:
                file_size = os.path.getsize(disk_path) / (1024*1024*1024)
                return file_size, file_size
            except:
                return 0, 0
        return 0, 0

    def page_domain(self, lv:LV, name:str, qs, form):
        try:
            d=lv.get_domain(name)
        except Exception:
            return "<div class='card'>Domain not found.</div>"
        msg = ""
        op = qs.get('op', [None])[0]
        if op:
            try:
                if op == 'start': 
                    d.create()
                elif op == 'shutdown': d.shutdown()
                elif op == 'destroy' and qs.get('confirm', ['0'])[0] == '1': d.destroy()
                elif op == 'reboot': d.reboot(0)
                elif op == 'undefine' and qs.get('confirm', ['0'])[0] == '1':
                    # Attempt full cleanup: domain undefine + nvram + per-VM directory
                    xml=d.XMLDesc(0)
                    import xml.etree.ElementTree as ET
                    root=ET.fromstring(xml)
                    nvram_path=None
                    nvnode=root.find('.//os/nvram')
                    if nvnode is not None and nvnode.text:
                        nvram_path=nvnode.text.strip()
                    # Identify first disk file path to infer VM directory (we stored as pool_path/name/...)
                    disk_file=None
                    for disk in root.findall('.//devices/disk'):
                        src=disk.find('source')
                        if src is not None and 'file' in src.attrib:
                            disk_file=src.get('file'); break
                    vm_dir=None
                    if disk_file:
                        # vm_dir is parent directory of disk files (one level above disk file)
                        vm_dir=os.path.dirname(disk_file)
                    # Force shutdown if running before undefine
                    try:
                        state, _ = d.state()
                        if state == libvirt.VIR_DOMAIN_RUNNING:
                            d.destroy()  # Force stop
                    except Exception:
                        pass
                    
                    # Undefine with comprehensive NVRAM cleanup flags
                    flags=0
                    if hasattr(libvirt,'VIR_DOMAIN_UNDEFINE_NVRAM'): flags|=libvirt.VIR_DOMAIN_UNDEFINE_NVRAM
                    if hasattr(libvirt,'VIR_DOMAIN_UNDEFINE_MANAGED_SAVE'): flags|=libvirt.VIR_DOMAIN_UNDEFINE_MANAGED_SAVE
                    if hasattr(libvirt,'VIR_DOMAIN_UNDEFINE_SNAPSHOTS_METADATA'): flags|=libvirt.VIR_DOMAIN_UNDEFINE_SNAPSHOTS_METADATA
                    if hasattr(libvirt,'VIR_DOMAIN_UNDEFINE_CHECKPOINTS_METADATA'): flags|=libvirt.VIR_DOMAIN_UNDEFINE_CHECKPOINTS_METADATA
                    if hasattr(libvirt,'VIR_DOMAIN_UNDEFINE_KEEP_NVRAM'): flags|=libvirt.VIR_DOMAIN_UNDEFINE_KEEP_NVRAM
                    
                    # Try multiple approaches for NVRAM cleanup
                    undefine_success = False
                    
                    # First try: undefine with NVRAM flag
                    try:
                        d.undefineFlags(flags)
                        undefine_success = True
                    except Exception as e1:
                        # Second try: undefine without NVRAM flag, then manually remove NVRAM
                        try:
                            flags_no_nvram = flags & ~getattr(libvirt, 'VIR_DOMAIN_UNDEFINE_NVRAM', 0)
                            d.undefineFlags(flags_no_nvram)
                            undefine_success = True
                        except Exception as e2:
                            # Third try: basic undefine
                            try:
                                d.undefine()
                                undefine_success = True
                            except Exception as e3:
                                raise RuntimeError(f'Failed to undefine domain: {e3}')
                    
                    if not undefine_success:
                        raise RuntimeError('Failed to undefine domain with all methods')
                    # Remove nvram file explicitly if still exists
                    if nvram_path and os.path.isfile(nvram_path):
                        try: os.remove(nvram_path)
                        except Exception: pass
                    # Remove vm dir
                    if vm_dir and os.path.isdir(vm_dir):
                        try: shutil.rmtree(vm_dir)
                        except Exception: pass
                elif op == 'autostart': d.setAutostart(1)
                elif op == 'noautostart': d.setAutostart(0)
                # immediate redirect to avoid double-click perception
                # For undefine operation, redirect to dashboard; for others, back to domain page
                redirect_url = "/" if op == 'undefine' else f"/?domain={html.escape(name)}"
                return f"<div class='card'><p>Operation done...</p><meta http-equiv='refresh' content='0;url={redirect_url}'></div>"
            except Exception as e:
                msg += f"<div class='inline-note'>{html.escape(str(e))}</div>"
        if form:
            try:
                if 'update_cpu_mem' in form:
                    # Convert GiB to MiB for memory
                    new_m = int(float(form.get('memory_gb', ['1'])[0]) * 1024)
                    new_os_type = form.get('os_type', ['linux'])[0]
                    new_cpu_mode = form.get('cpu_mode', ['host-model'])[0]
                    new_cpu_model = form.get('cpu_model', ['qemu64'])[0]
                    new_boot_order = form.get('boot_order', ['hd,cdrom,network'])[0]
                    
                    # CPU topology - calculate vCPUs from topology
                    new_sockets = parse_int(form.get('cpu_sockets', ['1'])[0], 1)
                    new_cores = parse_int(form.get('cpu_cores', ['1'])[0], 1)
                    new_threads = parse_int(form.get('cpu_threads', ['1'])[0], 1)
                    new_v = new_sockets * new_cores * new_threads
                    # Current values
                    try:
                        cur_v = d.maxVcpus()
                    except Exception:
                        cur_v = new_v
                    try:
                        cur_mem = d.maxMemory() // 1024
                    except Exception:
                        cur_mem = new_m
                    if d.isActive():
                        # Hot increase only (OS type changes require VM shutdown)
                        if new_v > cur_v:
                            try:
                                d.setVcpusFlags(new_v, libvirt.VIR_DOMAIN_AFFECT_LIVE | getattr(libvirt,'VIR_DOMAIN_AFFECT_CONFIG',0))
                                msg += f"<div class='inline-note'>CPU topology updated: {new_sockets}S/{new_cores}C/{new_threads}T = {new_v} vCPUs.</div>"
                            except Exception as e:
                                msg += f"<div class='inline-note'>CPU hotplug failed: {html.escape(str(e))}</div>"
                        if new_m > cur_mem:
                            try:
                                # Memory in KiB
                                d.setMemoryFlags(new_m*1024, libvirt.VIR_DOMAIN_AFFECT_LIVE | getattr(libvirt,'VIR_DOMAIN_AFFECT_CONFIG',0))
                                msg += f"<div class='inline-note'>Memory increased to {new_m} MiB.</div>"
                            except Exception as e:
                                msg += f"<div class='inline-note'>Memory hotplug failed: {html.escape(str(e))}</div>"
                        # Check if OS type change was requested
                        current_xml = d.XMLDesc(libvirt.VIR_DOMAIN_XML_INACTIVE)
                        import xml.etree.ElementTree as ET
                        current_root = ET.fromstring(current_xml)
                        current_hyperv = current_root.find('.//features/hyperv')
                        current_is_windows = current_hyperv is not None
                        if (new_os_type == 'windows' and not current_is_windows) or (new_os_type == 'linux' and current_is_windows):
                            msg += f"<div class='inline-note'>OS type change to {new_os_type} requires VM shutdown.</div>"
                    else:
                        # Redefine when powered off (can also decrease and change OS type)
                        xml_cfg = d.XMLDesc(libvirt.VIR_DOMAIN_XML_INACTIVE)
                        xml_cfg = re.sub(r'<vcpu.*?>.*?</vcpu>', f'<vcpu placement="static">{new_v}</vcpu>', xml_cfg)
                        xml_cfg = re.sub(r'<memory.*?>.*?</memory>', f'<memory unit="KiB">{new_m*1024}</memory>', xml_cfg)
                        xml_cfg = re.sub(r'<currentMemory.*?>.*?</currentMemory>', f'<currentMemory unit="KiB">{new_m*1024}</currentMemory>', xml_cfg)
                        
                        # Update OS-specific features
                        if new_os_type == 'windows':
                            # Always use Hyper-V features for Windows
                            features_replacement = '''<features>
    <acpi/>
    <apic/>
    <hyperv>
        <relaxed state='on'/>
        <vapic state='on'/>
        <spinlocks state='on' retries='8191'/>
        <vpindex state='on'/>
        <runtime state='on'/>
        <synic state='on'/>
        <stimer state='off'/>
    </hyperv>
    <kvm>
        <hidden state='on'/>
    </kvm>
</features>'''
                            msg += f"<div class='inline-note'>Enabled Hyper-V enlightenments for Windows.</div>"
                        else:
                            # Linux - basic features only
                            features_replacement = '''<features>
    <acpi/>
    <apic/>
</features>'''
                        
                        xml_cfg = re.sub(r'<features>.*?</features>', features_replacement, xml_cfg, flags=re.DOTALL)
                        
                        # Update CPU configuration with topology
                        cpu_replacement = ""
                        if new_cpu_mode == 'host-passthrough':
                            cpu_replacement = f"<cpu mode='host-passthrough' check='none' migratable='on'><topology sockets='{new_sockets}' cores='{new_cores}' threads='{new_threads}'/></cpu>"
                        elif new_cpu_mode == 'host-model':
                            cpu_replacement = f"<cpu mode='host-model' check='none' migratable='on'><topology sockets='{new_sockets}' cores='{new_cores}' threads='{new_threads}'/></cpu>"
                        elif new_cpu_mode == 'custom' and new_cpu_model:
                            cpu_replacement = f"<cpu mode='custom' match='exact' check='none' migratable='on'><model fallback='allow'>{html.escape(new_cpu_model)}</model><topology sockets='{new_sockets}' cores='{new_cores}' threads='{new_threads}'/></cpu>"
                        else:
                            cpu_replacement = f"<cpu mode='host-model' check='none' migratable='on'><topology sockets='{new_sockets}' cores='{new_cores}' threads='{new_threads}'/></cpu>"
                        
                        xml_cfg = re.sub(r'<cpu.*?</cpu>', cpu_replacement, xml_cfg, flags=re.DOTALL)
                        if '<cpu' not in xml_cfg:
                            # Insert CPU config after </os>
                            xml_cfg = xml_cfg.replace('</os>', f'</os>{cpu_replacement}')
                        
                        # Remove all OS boot elements since we use per-device boot elements
                        xml_cfg = re.sub(r'<boot dev=[^>]*/?>', '', xml_cfg)
                        
                        # Apply the updated XML configuration
                        lv.conn.defineXML(xml_cfg)
                        
                        # Create a clean display name for the message (remove custom: prefix if present)
                        display_cpu_mode = new_cpu_mode[7:] if new_cpu_mode.startswith('custom:') else new_cpu_mode
                        msg += f"<div class='inline-note'>Config updated for {new_os_type} OS type, {display_cpu_mode} CPU mode, and boot order ({new_boot_order.replace(',', ', ')}). VM restart required for changes to take effect.</div>"
                if 'create_volume' in form: 
                    pool = lv.get_pool(form.get('pool', [''])[0])
                    vol_name = form.get('vol_name', [''])[0]
                    size_gb = parse_int(form.get('size_gb', ['1'])[0], 1)
                    fmt = form.get('fmt', ['qcow2'])[0]
                    cap = size_gb * 1024 * 1024 * 1024
                    vol_xml = f"<volume><name>{vol_name}</name><capacity unit='bytes'>{cap}</capacity><target><format type='{fmt}'/></target></volume>"
                    pool.createXML(vol_xml, 0)
                    msg += "<div class='inline-note'>Volume created.</div>"
                if 'attach_disk' in form: 
                    # Check if this is creating a new disk or attaching existing
                    disk_size_gb = form.get('disk_size_gb', [''])[0]
                    template_disk = form.get('template_disk', [''])[0]
                    bus_type = form.get('bus', ['virtio'])[0]
                    
                    if template_disk and template_disk.startswith('existing:'):
                        # Attach existing disk image
                        try:
                            parts = template_disk.split(':', 2)
                            pool_name = parts[1]
                            vol_name = parts[2]
                            
                            pool = lv.get_pool(pool_name)
                            vol = pool.storageVolLookupByName(vol_name)
                            path = vol.path()
                            
                            dom_xml = d.XMLDesc(libvirt.VIR_DOMAIN_XML_INACTIVE)
                            existing = re.findall(r"<target dev='(vd.)'", dom_xml)
                            tgt = lv.next_disk_target(existing)
                            
                            # Detect disk format
                            disk_format = 'qcow2' if vol_name.endswith('.qcow2') else 'raw'
                            disk_xml = f"<disk type='file' device='disk'><driver name='qemu' type='{disk_format}'/><source file='{path}'/><target dev='{tgt}' bus='{bus_type}'/></disk>"
                            
                            # Use appropriate flags based on VM state
                            state, _ = d.state()
                            if state == libvirt.VIR_DOMAIN_RUNNING:
                                flags = getattr(libvirt,'VIR_DOMAIN_AFFECT_LIVE',0) | getattr(libvirt,'VIR_DOMAIN_AFFECT_CONFIG',0)
                            else:
                                flags = getattr(libvirt,'VIR_DOMAIN_AFFECT_CONFIG',0)
                            
                            d.attachDeviceFlags(disk_xml, flags)
                            msg += f"<div class='inline-note'>Attached existing disk: {html.escape(vol_name)}</div>"
                            
                        except Exception as e:
                            msg += f"<div class='inline-note error'>Failed to attach existing disk: {html.escape(str(e))}</div>"
                            
                    elif disk_size_gb:
                        # Create new disk
                        try:
                            size_gb = int(disk_size_gb)
                            if size_gb < 1:
                                raise ValueError("Disk size must be at least 1 GB")
                                
                            # Generate unique disk name
                            import time
                            disk_name = f"{name}-disk-{int(time.time())}.qcow2"
                            disk_path = f"/var/lib/libvirt/images/{disk_name}"
                            
                            # Handle template copying if specified
                            if template_disk and template_disk.startswith('template:'):
                                template_file = template_disk.split(':', 1)[1]
                                template_path = os.path.join(TEMPLATES_DIR, template_file)
                                if os.path.exists(template_path):
                                    # Copy template and resize
                                    import subprocess
                                    cmd = ['cp', '--reflink=always', template_path, disk_path]
                                    subprocess.run(cmd, check=True, capture_output=True, timeout=30)
                                    # Always resize to match requested size (unless 0 = keep template size)
                                    if size_gb > 0:
                                        resize_cmd = ['qemu-img', 'resize', disk_path, f'{size_gb}G']
                                        subprocess.run(resize_cmd, check=True, capture_output=True, timeout=30)
                                    attach_immediately = True
                                else:
                                    raise FileNotFoundError(f"Template not found: {template_file}")
                            elif size_gb > 50:  # For large disks, create asynchronously
                                def create_disk_async():
                                    try:
                                        import subprocess
                                        cmd = ['qemu-img', 'create', '-f', 'qcow2', disk_path, f'{size_gb}G']
                                        subprocess.run(cmd, check=True, capture_output=True)
                                        logger.info(f"Created disk {disk_path} ({size_gb}GB)")
                                    except Exception as e:
                                        logger.error(f"Failed to create disk {disk_path}: {e}")
                                
                                import threading
                                threading.Thread(target=create_disk_async, daemon=True).start()
                                msg += f"<div class='inline-note'>Creating {size_gb}GB disk in background: {disk_name}</div>"
                                attach_immediately = False
                            else:
                                # Create smaller disks synchronously for immediate attachment
                                import subprocess
                                cmd = ['qemu-img', 'create', '-f', 'qcow2', disk_path, f'{size_gb}G']
                                result = subprocess.run(cmd, check=True, capture_output=True, timeout=30)
                                attach_immediately = True
                            
                            # Attach the disk immediately for sync operations
                            if attach_immediately:
                                dom_xml = d.XMLDesc(libvirt.VIR_DOMAIN_XML_INACTIVE)
                                existing = re.findall(r"<target dev='(vd.)'", dom_xml)
                                tgt = lv.next_disk_target(existing)
                                disk_xml = f"<disk type='file' device='disk'><driver name='qemu' type='qcow2'/><source file='{disk_path}'/><target dev='{tgt}' bus='{bus_type}'/></disk>"
                                
                                # Use appropriate flags based on VM state
                                state, _ = d.state()
                                if state == libvirt.VIR_DOMAIN_RUNNING:
                                    flags = getattr(libvirt,'VIR_DOMAIN_AFFECT_LIVE',0) | getattr(libvirt,'VIR_DOMAIN_AFFECT_CONFIG',0)
                                else:
                                    flags = getattr(libvirt,'VIR_DOMAIN_AFFECT_CONFIG',0)
                                
                                d.attachDeviceFlags(disk_xml, flags)
                                template_msg = f" from template {template_disk.split(':', 1)[1]}" if template_disk.startswith('template:') else ""
                                msg += f"<div class='inline-note'>Created and attached {size_gb}GB disk{template_msg}: {disk_name}</div>"
                                
                        except ValueError as e:
                            msg += f"<div class='inline-note error'>Invalid disk size: {html.escape(str(e))}</div>"
                        except subprocess.TimeoutExpired:
                            msg += f"<div class='inline-note error'>Disk creation timed out. Try a smaller size or wait for background creation.</div>"
                        except Exception as e:
                            msg += f"<div class='inline-note error'>Failed to create disk: {html.escape(str(e))}</div>"
                    else:
                        msg += f"<div class='inline-note error'>Please specify disk size or select an existing image.</div>"
                    
                # Handle CD/DVD attachment
                if 'attach_cdrom' in form:
                    try:
                        iso_path = form.get('cdrom_iso', [''])[0].strip()
                        if not iso_path:
                            msg += "<div class='inline-note error'>Please select an ISO image to attach.</div>"
                        else:
                            # Check if this is a pool::iso format
                            if '::' in iso_path:
                                pool_name, iso_name = iso_path.split('::', 1)
                                if not pool_name or not iso_name:
                                    msg += "<div class='inline-note error'>Invalid ISO selection format. Please select a valid ISO image.</div>"
                                    return self.page_dashboard(lv, msg=msg)
                                    
                                pool = lv.get_pool(pool_name)
                                if pool and pool.isActive():
                                    # Get the pool's path
                                    try:
                                        pool_xml = pool.XMLDesc()
                                        import xml.etree.ElementTree as ET
                                        pool_root = ET.fromstring(pool_xml)
                                        pool_path = pool_root.findtext('.//target/path')
                                        if pool_path:
                                            # Construct full path to ISO
                                            iso_path = os.path.join(pool_path, 'images', iso_name)
                                            if not os.path.exists(iso_path):
                                                msg += f"<div class='inline-note error'>ISO file not found: {html.escape(iso_path)}</div>"
                                                return self.page_dashboard(lv, msg=msg)
                                        else:
                                            msg += f"<div class='inline-note error'>Could not determine path for pool {html.escape(pool_name)}</div>"
                                            return self.page_dashboard(lv, msg=msg)
                                    except Exception as e:
                                        msg += f"<div class='inline-note error'>Error accessing pool {html.escape(pool_name)}: {html.escape(str(e))}</div>"
                                        return self.page_dashboard(lv, msg=msg)
                                else:
                                    msg += f"<div class='inline-note error'>Storage pool not found or inactive: {html.escape(pool_name)}</div>"
                                    return self.page_dashboard(lv, msg=msg)
                            
                            # Verify the ISO file exists if it's a direct path
                            elif not os.path.isfile(iso_path):
                                msg += f"<div class='inline-note error'>ISO file not found: {html.escape(iso_path)}</div>"
                                return self.page_dashboard(lv, msg=msg)
                            
                            # Find next available CD-ROM target
                            dom_xml = d.XMLDesc(libvirt.VIR_DOMAIN_XML_INACTIVE)
                            import xml.etree.ElementTree as ET
                            root = ET.fromstring(dom_xml)
                            
                            # Get existing CD-ROM targets
                            existing_cdroms = set()
                            for disk in root.findall('.//devices/disk'):
                                if disk.get('device') == 'cdrom':
                                    target = disk.find('target')
                                    if target is not None and 'dev' in target.attrib:
                                        existing_cdroms.add(target.get('dev'))
                            
                            # Find next available target (hda, hdb, etc.)
                            cdrom_letters = 'abcdefghijklmnopqrstuvwxyz'
                            tgt = None
                            for letter in cdrom_letters:
                                candidate = f'hd{letter}'
                                if candidate not in existing_cdroms:
                                    tgt = candidate
                                    break
                            
                            if tgt:
                                # Escape the ISO path for XML
                                safe_iso_path = html.escape(iso_path)
                                cdrom_xml = f"""<disk type='file' device='cdrom'>
                                    <driver name='qemu' type='raw'/>
                                    <source file='{safe_iso_path}'/>
                                    <target dev='{tgt}' bus='ide'/>
                                    <readonly/>
                                </disk>"""
                                
                                # Use appropriate flags based on VM state
                                state, _ = d.state()
                                if state == libvirt.VIR_DOMAIN_RUNNING:
                                    flags = getattr(libvirt,'VIR_DOMAIN_AFFECT_LIVE',0) | getattr(libvirt,'VIR_DOMAIN_AFFECT_CONFIG',0)
                                else:
                                    flags = getattr(libvirt,'VIR_DOMAIN_AFFECT_CONFIG',0)
                                
                                try:
                                    d.attachDeviceFlags(cdrom_xml, flags)
                                    msg += f"<div class='inline-note success'>✅ CD/DVD attached successfully as {tgt}.</div>"
                                    logger.info(f"Attached ISO {iso_path} to VM {name} as {tgt}")
                                except libvirt.libvirtError as e:
                                    error_msg = str(e)
                                    if 'already in use by domain' in error_msg.lower():
                                        msg += "<div class='inline-note error'>This ISO is already attached to the VM.</div>"
                                    else:
                                        msg += f"<div class='inline-note error'>Failed to attach CD/DVD: {html.escape(error_msg)}</div>"
                                        logger.error(f"Failed to attach ISO {iso_path} to VM {name}: {error_msg}")
                            else:
                                msg += "<div class='inline-note error'>No available CD-ROM targets. Maximum number of CD/DVD drives reached.</div>"
                    except Exception as e:
                        error_msg = str(e)
                        msg += f"<div class='inline-note error'>Failed to process CD/DVD attachment: {html.escape(error_msg)}</div>"
                        logger.error(f"Error in CD/DVD attachment: {error_msg}", exc_info=True)
                
                # Handle CD/DVD eject
                if 'eject_cdrom' in form:
                    tgt = form.get('cdrom_target', [''])[0].strip()
                    if not tgt:
                        msg += "<div class='inline-note error'>No CD/DVD target specified for ejection.</div>"
                    else:
                        try:
                            dom_xml = d.XMLDesc(libvirt.VIR_DOMAIN_XML_INACTIVE)
                            import xml.etree.ElementTree as ET
                            root = ET.fromstring(dom_xml)
                            disk_found = False
                            
                            for disk in root.findall('.//devices/disk'):
                                if disk.get('device') == 'cdrom':
                                    t = disk.find('target')
                                    if t is not None and t.get('dev') == tgt:
                                        disk_found = True
                                        # Check if there's actually media to eject
                                        source = disk.find('source')
                                        if source is None or 'file' not in source.attrib:
                                            msg += f"<div class='inline-note warning'>No media found in {tgt} to eject.</div>"
                                            break
                                            
                                        # Create empty CD-ROM XML (eject)
                                        ejected_xml = f"""<disk type='file' device='cdrom'>
                                            <driver name='qemu' type='raw'/>
                                            <target dev='{tgt}' bus='ide'/>
                                            <readonly/>
                                        </disk>"""
                                        
                                        # Use appropriate flags based on VM state
                                        state, _ = d.state()
                                        if state == libvirt.VIR_DOMAIN_RUNNING:
                                            flags = getattr(libvirt,'VIR_DOMAIN_AFFECT_LIVE',0) | getattr(libvirt,'VIR_DOMAIN_AFFECT_CONFIG',0)
                                        else:
                                            flags = getattr(libvirt,'VIR_DOMAIN_AFFECT_CONFIG',0)
                                        
                                        try:
                                            d.updateDeviceFlags(ejected_xml, flags)
                                            msg += f"<div class='inline-note success'>✅ CD/DVD ejected from {tgt}.</div>"
                                            logger.info(f"Ejected CD/DVD from {tgt} on VM {name}")
                                        except libvirt.libvirtError as e:
                                            error_msg = str(e)
                                            if 'not found' in error_msg.lower():
                                                msg += f"<div class='inline-note error'>CD/DVD device {tgt} not found.</div>"
                                            else:
                                                msg += f"<div class='inline-note error'>Failed to eject CD/DVD: {html.escape(error_msg)}</div>"
                                                logger.error(f"Failed to eject CD/DVD from {tgt} on VM {name}: {error_msg}")
                                        break
                            
                            if not disk_found:
                                msg += f"<div class='inline-note error'>CD/DVD device {tgt} not found.</div>"
                                
                        except Exception as e:
                            error_msg = str(e)
                            msg += f"<div class='inline-note error'>Failed to eject CD/DVD: {html.escape(error_msg)}</div>"
                            logger.error(f"Error ejecting CD/DVD from VM {name}: {error_msg}", exc_info=True)
                
                # Handle CD/DVD detach (remove drive completely)
                if 'detach_cdrom' in form:
                    tgt = form.get('cdrom_target', [''])[0].strip()
                    if not tgt:
                        msg += "<div class='inline-note error'>No CD/DVD target specified for removal.</div>"
                    else:
                        try:
                            dom_xml = d.XMLDesc(libvirt.VIR_DOMAIN_XML_INACTIVE)
                            import xml.etree.ElementTree as ET
                            root = ET.fromstring(dom_xml)
                            disk_found = False
                            
                            for disk in root.findall('.//devices/disk'):
                                if disk.get('device') == 'cdrom':
                                    t = disk.find('target')
                                    if t is not None and t.get('dev') == tgt:
                                        disk_found = True
                                        # Use appropriate flags based on VM state
                                        state, _ = d.state()
                                        if state == libvirt.VIR_DOMAIN_RUNNING:
                                            flags = getattr(libvirt,'VIR_DOMAIN_AFFECT_LIVE',0) | getattr(libvirt,'VIR_DOMAIN_AFFECT_CONFIG',0)
                                        else:
                                            flags = getattr(libvirt,'VIR_DOMAIN_AFFECT_CONFIG',0)
                                        
                                        try:
                                            disk_xml = ET.tostring(disk, encoding='unicode')
                                            d.detachDeviceFlags(disk_xml, flags)
                                            msg += f"<div class='inline-note success'>✅ CD/DVD drive {tgt} removed successfully.</div>"
                                            logger.info(f"Removed CD/DVD drive {tgt} from VM {name}")
                                        except libvirt.libvirtError as e:
                                            error_msg = str(e)
                                            if 'not found' in error_msg.lower():
                                                msg += f"<div class='inline-note error'>CD/DVD device {tgt} not found.</div>"
                                            else:
                                                msg += f"<div class='inline-note error'>Failed to remove CD/DVD drive: {html.escape(error_msg)}</div>"
                                                logger.error(f"Failed to remove CD/DVD drive {tgt} from VM {name}: {error_msg}")
                                        break
                            
                            if not disk_found:
                                msg += f"<div class='inline-note error'>CD/DVD device {tgt} not found.</div>"
                                
                        except Exception as e:
                            error_msg = str(e)
                            msg += f"<div class='inline-note error'>Failed to remove CD/DVD drive: {html.escape(error_msg)}</div>"
                            logger.error(f"Error removing CD/DVD drive from VM {name}: {error_msg}", exc_info=True)
                if 'detach_disk' in form: 
                    if d.isActive():
                        msg += "<div class='inline-note error'>Cannot delete disk while VM is running. Stop the VM first.</div>"
                    else:
                        tgt = form.get('target', [''])[0]
                        dom_xml = d.XMLDesc(libvirt.VIR_DOMAIN_XML_INACTIVE)
                        import xml.etree.ElementTree as ET
                        root = ET.fromstring(dom_xml)
                        for disk in root.findall('.//devices/disk'):
                            t = disk.find('target')
                            if t is not None and t.get('dev') == tgt:
                                # Use appropriate flags based on VM state
                                state, _ = d.state()
                                if state == libvirt.VIR_DOMAIN_RUNNING:
                                    flags = getattr(libvirt,'VIR_DOMAIN_AFFECT_LIVE',0) | getattr(libvirt,'VIR_DOMAIN_AFFECT_CONFIG',0)
                                else:
                                    flags = getattr(libvirt,'VIR_DOMAIN_AFFECT_CONFIG',0)
                                d.detachDeviceFlags(ET.tostring(disk, encoding='unicode'), flags)
                                msg += f"<div class='inline-note'>Disk {html.escape(tgt)} detached.</div>"
                                break
                if 'resize_disk' in form:
                    tgt = form.get('disk_target', [''])[0]
                    new_size_gb = parse_int(form.get('new_size_gb', ['0'])[0], 0)
                    if tgt and new_size_gb>0:
                        dom_xml = d.XMLDesc(libvirt.VIR_DOMAIN_XML_INACTIVE)
                        import xml.etree.ElementTree as ET
                        root = ET.fromstring(dom_xml)
                        for disk in root.findall('.//devices/disk'):
                            t = disk.find('target'); src = disk.find('source')
                            if t is not None and t.get('dev') == tgt and src is not None and 'file' in src.attrib:
                                path = src.get('file')
                                try:
                                    cur_sz = os.path.getsize(path)
                                except Exception:
                                    cur_sz = 0
                                new_bytes = new_size_gb * 1024 * 1024 * 1024
                                if new_bytes > cur_sz:
                                    try:
                                        if d.isActive() and hasattr(d,'blockResize'):
                                            d.blockResize(tgt, new_bytes, 0)
                                        else:
                                            subprocess.check_call(['sudo', 'qemu-img','resize',path,str(new_bytes)])
                                        msg += f"<div class='inline-note'>Disk {html.escape(tgt)} grew to {new_size_gb} GB.</div>"
                                    except Exception as e:
                                        msg += f"<div class='inline-note'>Resize failed: {html.escape(str(e))}</div>"
                                else:
                                    msg += "<div class='inline-note'>New size must be larger.</div>"
                                break
                if 'migrate_disk' in form:
                    # Live disk migration between pools
                    tgt = form.get('disk_target', [''])[0]
                    target_pool_name = form.get('target_pool', [''])[0]
                    if tgt and target_pool_name:
                        try:
                            # Get disk path from VM XML
                            dom_xml = d.XMLDesc(libvirt.VIR_DOMAIN_XML_INACTIVE)
                            import xml.etree.ElementTree as ET
                            root = ET.fromstring(dom_xml)
                            source_path = None
                            disk_format = 'qcow2'
                            
                            for disk in root.findall('.//devices/disk'):
                                t = disk.find('target')
                                if t is not None and t.get('dev') == tgt:
                                    src = disk.find('source')
                                    if src is not None:
                                        source_path = src.get('file')
                                        # Detect format
                                        driver = disk.find('driver')
                                        if driver is not None:
                                            disk_format = driver.get('type', 'qcow2')
                                    break
                            
                            if source_path:
                                # Get target pool with proper XML parsing
                                target_pool = lv.get_pool(target_pool_name)
                                pool_xml = target_pool.XMLDesc(0)
                                pool_root = ET.fromstring(pool_xml)
                                target_pool_path = pool_root.findtext('.//target/path')
                                
                                if not target_pool_path:
                                    raise RuntimeError(f"Could not determine path for pool '{target_pool_name}'")
                                
                                # Create destination path with proper directory structure
                                source_filename = os.path.basename(source_path)
                                vm_name = d.name()
                                
                                # Create VM subdirectory in target pool if needed
                                target_vm_dir = os.path.join(target_pool_path, vm_name)
                                os.makedirs(target_vm_dir, exist_ok=True)
                                
                                # Change extension to .qcow2 for destination
                                base_name = os.path.splitext(source_filename)[0]
                                target_path = os.path.join(target_vm_dir, f"{base_name}.qcow2")
                                
                                # Perform live block copy migration
                                if d.isActive():
                                    # Start background blockcopy process using virsh command
                                    import threading
                                    import subprocess
                                    import uuid
                                    
                                    # Generate unique job ID for tracking
                                    job_id = str(uuid.uuid4())
                                    
                                    # Store migration status globally for progress tracking
                                    if not hasattr(self, 'migration_jobs'):
                                        self.migration_jobs = {}
                                    
                                    self.migration_jobs[job_id] = {
                                        'status': 'starting',
                                        'progress': 0,
                                        'vm_name': vm_name,
                                        'disk_target': tgt,
                                        'source_path': source_path,
                                        'target_path': target_path,
                                        'error': None
                                    }
                                    
                                    def run_blockcopy():
                                        try:
                                            # Run virsh blockcopy command with progress monitoring
                                            cmd = [
                                                'virsh', 'blockcopy', vm_name, tgt,
                                                '--dest', target_path,
                                                '--format', 'qcow2',
                                                '--transient-job', '--pivot', '--verbose'
                                            ]
                                            
                                            process = subprocess.Popen(
                                                cmd, 
                                                stdout=subprocess.PIPE, 
                                                stderr=subprocess.STDOUT,
                                                text=True,
                                                bufsize=1,
                                                universal_newlines=True
                                            )
                                            
                                            # Monitor progress
                                            while True:
                                                output = process.stdout.readline()
                                                if output == '' and process.poll() is not None:
                                                    break
                                                if output:
                                                    output = output.strip()
                                                    # Parse progress from virsh output
                                                    if 'Block copy: [' in output and '%]' in output:
                                                        try:
                                                            # Extract percentage from output like "Block copy: [ 45%]"
                                                            start = output.find('[') + 1
                                                            end = output.find('%]')
                                                            if start > 0 and end > start:
                                                                progress = int(output[start:end].strip())
                                                                self.migration_jobs[job_id]['progress'] = progress
                                                                self.migration_jobs[job_id]['status'] = 'copying'
                                                        except ValueError:
                                                            pass
                                                    elif 'successfully pivoted' in output.lower():
                                                        self.migration_jobs[job_id]['status'] = 'pivoted'
                                                        self.migration_jobs[job_id]['progress'] = 100
                                            
                                            # Check final result
                                            return_code = process.poll()
                                            if return_code == 0:
                                                # Success - delete old file
                                                try:
                                                    old_source_dir = os.path.dirname(source_path)
                                                    os.remove(source_path)
                                                    # Only remove directory if it's empty (no other disk files)
                                                    if old_source_dir != os.path.dirname(target_path):
                                                        try:
                                                            # Check if directory is completely empty
                                                            if not os.listdir(old_source_dir):
                                                                os.rmdir(old_source_dir)
                                                            # Note: We don't remove if there are other files (like other VM disks)
                                                        except Exception:
                                                            pass  # Directory removal is not critical
                                                    self.migration_jobs[job_id]['status'] = 'completed'
                                                except Exception as e:
                                                    self.migration_jobs[job_id]['status'] = 'completed_with_warnings'
                                                    self.migration_jobs[job_id]['error'] = f"Could not remove old disk file: {str(e)}"
                                            else:
                                                self.migration_jobs[job_id]['status'] = 'failed'
                                                self.migration_jobs[job_id]['error'] = f"blockcopy failed with return code {return_code}"
                                                
                                        except Exception as e:
                                            self.migration_jobs[job_id]['status'] = 'failed'
                                            self.migration_jobs[job_id]['error'] = str(e)
                                    
                                    # Start migration in background thread
                                    migration_thread = threading.Thread(target=run_blockcopy)
                                    migration_thread.daemon = True
                                    migration_thread.start()
                                    
                                    # Don't add any message - the status will show under the disk
                                else:
                                    # Offline migration - copy file and update XML
                                    subprocess.check_call(['sudo', 'cp', source_path, target_path])
                                    
                                    # Update VM XML to point to new location
                                    for disk in root.findall('.//devices/disk'):
                                        t = disk.find('target')
                                        if t is not None and t.get('dev') == tgt:
                                            src = disk.find('source')
                                            if src is not None:
                                                src.set('file', target_path)
                                            break
                                    
                                    # Properly format the XML for defineXML
                                    # Ensure proper XML declaration and formatting
                                    import xml.dom.minidom
                                    
                                    # Convert ElementTree to string then parse with minidom for proper formatting
                                    rough_xml = ET.tostring(root, encoding='unicode')
                                    
                                    # Validate the rough XML first
                                    if not rough_xml or not rough_xml.strip():
                                        raise ValueError("Generated XML is empty")
                                    
                                    # Parse and format with minidom
                                    try:
                                        dom = xml.dom.minidom.parseString(rough_xml)
                                        new_xml = dom.toxml()
                                        
                                        # Validate XML before defining
                                        ET.fromstring(new_xml)  # Test parse
                                        lv.conn.defineXML(new_xml)
                                    except Exception as format_error:
                                        # Fallback to simpler formatting
                                        new_xml = rough_xml
                                        if not new_xml.startswith('<?xml'):
                                            new_xml = '<?xml version="1.0" encoding="UTF-8"?>\n' + new_xml
                                        
                                        # Test parse the fallback XML
                                        ET.fromstring(new_xml)  # This will raise if XML is invalid
                                        lv.conn.defineXML(new_xml)
                                    
                                    # Remove old file after successful offline migration
                                    try:
                                        old_source_dir = os.path.dirname(source_path)
                                        os.remove(source_path)
                                        # Only remove directory if it's empty (no other disk files)
                                        if old_source_dir != os.path.dirname(target_path):
                                            try:
                                                # Check if directory is completely empty
                                                if not os.listdir(old_source_dir):
                                                    os.rmdir(old_source_dir)
                                                # Note: We don't remove if there are other files (like other VM disks)
                                            except Exception:
                                                pass  # Directory removal is not critical
                                    except Exception as e:
                                        msg += f"<div class='inline-note'>Warning: Could not remove old disk file: {html.escape(str(e))}</div>"
                                    
                                    msg += f"<div class='inline-note'>Disk {html.escape(tgt)} migrated successfully to pool '{html.escape(target_pool_name)}' at {html.escape(target_path)}</div>"
                            else:
                                msg += "<div class='inline-note error'>Could not find disk path in VM configuration.</div>"
                        except Exception as e:
                            # Provide more detailed error information
                            error_msg = str(e)
                            if "Start tag expected" in error_msg:
                                error_msg += " (This usually indicates an XML parsing issue during disk migration)"
                            msg += f"<div class='inline-note error'>Disk migration failed: {html.escape(error_msg)}</div>"
                if 'change_disk_bus' in form:
                    if d.isActive():
                        msg += "<div class='inline-note error'>Cannot change disk bus while VM is running. Stop the VM first.</div>"
                    else:
                        tgt = form.get('disk_target', [''])[0]
                        new_bus = form.get('new_bus', ['virtio'])[0]
                        if tgt and new_bus in ['virtio', 'scsi', 'sata']:
                            dom_xml = d.XMLDesc(libvirt.VIR_DOMAIN_XML_INACTIVE)
                            import xml.etree.ElementTree as ET
                            root = ET.fromstring(dom_xml)
                            for disk in root.findall('.//devices/disk'):
                                t = disk.find('target')
                                if t is not None and t.get('dev') == tgt:
                                    # Update the bus attribute
                                    t.set('bus', new_bus)
                                    # Update device name prefix based on bus
                                    prefix_map = {'virtio': 'vd', 'scsi': 'sd', 'sata': 'hd'}
                                    new_prefix = prefix_map.get(new_bus, 'vd')
                                    if len(tgt) >= 3:
                                        new_dev = new_prefix + tgt[2:]  # Keep the letter part
                                        t.set('dev', new_dev)
                                    
                                    # Remove any existing address element to avoid conflicts
                                    address_elem = disk.find('address')
                                    if address_elem is not None:
                                        disk.remove(address_elem)
                                    
                                    # Add SCSI controller if switching to SCSI and it doesn't exist
                                    if new_bus == 'scsi':
                                        devices = root.find('.//devices')
                                        scsi_exists = devices.find(".//controller[@type='scsi']") is not None
                                        if not scsi_exists:
                                            scsi_controller = ET.SubElement(devices, 'controller')
                                            scsi_controller.set('type', 'scsi')
                                            scsi_controller.set('index', '0')
                                            scsi_controller.set('model', 'virtio-scsi')
                                    
                                    # Redefine the domain with the new XML
                                    new_xml = ET.tostring(root, encoding='unicode')
                                    d.undefine()
                                    lv.conn.defineXML(new_xml)
                                    msg += f"<div class='inline-note'>Disk {html.escape(tgt)} bus changed to {html.escape(new_bus)}.</div>"
                                    break
                # DEBUG: Log all form parameters
                print(f"DEBUG: All form parameters: {dict(form)}")
                
                if 'set_boot_device' in form:
                    boot_device = form.get('boot_device', [''])[0]
                    # DEBUG: Log the boot device request
                    print(f"DEBUG: Boot device request received - device: {boot_device}, VM: {name}")
                    if boot_device:
                        try:
                            # Check if VM is running
                            state, _ = d.state()
                            if state == libvirt.VIR_DOMAIN_RUNNING:
                                msg += "<div class='inline-note error'>Cannot change boot device while VM is running. Please shut down the VM first.</div>"
                            else:
                                # Get XML configuration for stopped domain
                                try:
                                    dom_xml = d.XMLDesc(libvirt.VIR_DOMAIN_XML_INACTIVE)  # Use basic flags for stopped domain
                                except Exception as e2:
                                    msg += f"<div class='inline-note error'>Failed to get XML config: {html.escape(str(e2))}</div>"
                                    dom_xml = None
                                
                                if dom_xml:
                                    import xml.etree.ElementTree as ET
                                    root = ET.fromstring(dom_xml)
                                    
                                    # Remove any OS-level boot elements that might interfere
                                    os_elem = root.find('.//os')
                                    if os_elem is not None:
                                        for boot_elem in os_elem.findall('boot'):
                                            os_elem.remove(boot_elem)
                                    
                                    # Remove boot order from all device elements first
                                    for device in root.findall('.//devices/*'):
                                        boot_elem = device.find('boot')
                                        if boot_elem is not None:
                                            device.remove(boot_elem)
                                    
                                    # Find the selected disk and add boot order (EXACT same as debug script)
                                    device_found = False
                                    test_disks = root.findall('.//devices/disk')
                                    for test_disk in test_disks:
                                        test_target = test_disk.find('target')
                                        if test_target is not None and test_target.get('dev') == boot_device:
                                            boot_elem = ET.SubElement(test_disk, 'boot')
                                            boot_elem.set('order', '1')
                                            device_found = True
                                            break
                                    
                                    if device_found:
                                        # Convert back to XML string
                                        new_xml = ET.tostring(root, encoding='unicode')
                                        
                                        # Use EXACT same approach as debug script
                                        try:
                                            # Try different undefine approaches (EXACT same as debug script)
                                            try:
                                                d.undefine()
                                            except:
                                                # If basic undefine fails, the domain might have snapshots or managed save
                                                pass
                                            
                                            lv.conn.defineXML(new_xml)
                                            print(f"DEBUG: Successfully applied boot device change to {boot_device}")
                                            msg += f"<div class='inline-note success'>Boot device set to {html.escape(boot_device)}.</div>"
                                        except Exception as e:
                                            msg += f"<div class='inline-note error'>Failed to apply change: {html.escape(str(e))}</div>"
                                    else:
                                        msg += f"<div class='inline-note error'>Device {html.escape(boot_device)} not found among available devices.</div>"
                        except Exception as e:
                            msg += f"<div class='inline-note error'>Failed to set boot device: {html.escape(str(e))}</div>"
                
                # Handle PCI device attachment
                if 'attach_pci' in form:
                    pci_addr = form.get('pci_addr', [''])[0]
                    if pci_addr:
                        try:
                            # Only allow PCI attachment on stopped domains
                            state, _ = d.state()
                            if state == libvirt.VIR_DOMAIN_RUNNING:
                                msg += f"<div class='inline-note error'>Cannot attach PCI device to running VM. Please stop the VM first.</div>"
                            else:
                                # Handle both short format (01:00.0) and full format (0000:01:00.0)
                                if ':' in pci_addr and pci_addr.count(':') == 1:
                                    full_addr = f"0000:{pci_addr}"
                                else:
                                    full_addr = pci_addr
                                
                                dd, bb, rest = full_addr.split(':')
                                slot, func = rest.split('.')
                                host_xml = f"<hostdev mode='subsystem' type='pci' managed='yes'><source><address domain='0x{dd}' bus='0x{bb}' slot='0x{slot}' function='0x{func}'/></source></hostdev>"
                                
                                d.attachDeviceFlags(host_xml, libvirt.VIR_DOMAIN_AFFECT_CONFIG)
                                msg += f"<div class='inline-note'>PCI device {html.escape(pci_addr)} attached successfully.</div>"
                        except Exception as e:
                            msg += f"<div class='inline-note error'>Failed to attach PCI device: {html.escape(str(e))}</div>"
                
                # Handle PCI device detachment
                if 'detach_pci' in form:
                    pci_addr = form.get('pci_detach_addr', [''])[0]
                    if pci_addr:
                        try:
                            # Only allow PCI detachment on stopped domains
                            state, _ = d.state()
                            if state == libvirt.VIR_DOMAIN_RUNNING:
                                msg += f"<div class='inline-note error'>Cannot detach PCI device from running VM. Please stop the VM first.</div>"
                            else:
                                dom_xml = d.XMLDesc(libvirt.VIR_DOMAIN_XML_INACTIVE)
                                import xml.etree.ElementTree as ET
                                root = ET.fromstring(dom_xml)
                                
                                for hostdev in root.findall('.//devices/hostdev'):
                                    addr_elem = hostdev.find('source/address')
                                    if addr_elem is not None:
                                        domain = int(addr_elem.get('domain', '0'), 16)
                                        bus = int(addr_elem.get('bus', '0'), 16)
                                        slot = int(addr_elem.get('slot', '0'), 16)
                                        function = int(addr_elem.get('function', '0'), 16)
                                        addr_str = f"{domain:04x}:{bus:02x}:{slot:02x}.{function}"
                                        
                                        if addr_str == f"0000:{pci_addr}" or addr_str[5:] == pci_addr:
                                            d.detachDeviceFlags(ET.tostring(hostdev, encoding='unicode'), libvirt.VIR_DOMAIN_AFFECT_CONFIG)
                                            msg += f"<div class='inline-note'>PCI device {html.escape(pci_addr)} detached successfully.</div>"
                                            break
                        except Exception as e:
                            msg += f"<div class='inline-note error'>Failed to detach PCI device: {html.escape(str(e))}</div>"
                
                # Handle graphics device management
                if 'add_graphics' in form:
                    gfx_type = form.get('graphics_type', ['vnc'])[0]
                    try:
                        state, _ = d.state()
                        if state == libvirt.VIR_DOMAIN_RUNNING:
                            msg += f"<div class='inline-note error'>Cannot modify graphics while VM is running. Please stop the VM first.</div>"
                        else:
                            # Get current XML and modify it
                            dom_xml = d.XMLDesc(libvirt.VIR_DOMAIN_XML_INACTIVE)
                            import xml.etree.ElementTree as ET
                            root = ET.fromstring(dom_xml)
                            devices = root.find('.//devices')
                            
                            if devices is not None:
                                # Create new graphics element XML
                                graphics_xml = f"<graphics type='{gfx_type}' port='-1' listen='127.0.0.1'/>"
                                
                                # Use attachDeviceFlags with CONFIG flag for persistent changes
                                try:
                                    d.attachDeviceFlags(graphics_xml, libvirt.VIR_DOMAIN_AFFECT_CONFIG)
                                    msg += f"<div class='inline-note'>{gfx_type.upper()} graphics adapter added successfully.</div>"
                                except Exception:
                                    # Fallback: modify XML and redefine (avoiding NVRAM issues)
                                    new_graphics = ET.Element('graphics')
                                    new_graphics.set('type', gfx_type)
                                    new_graphics.set('port', '-1')
                                    new_graphics.set('listen', '127.0.0.1')
                                    devices.append(new_graphics)
                                    
                                    new_xml = ET.tostring(root, encoding='unicode')
                                    # Try to preserve NVRAM by using VIR_DOMAIN_UNDEFINE_NVRAM flag
                                    try:
                                        d.undefineFlags(libvirt.VIR_DOMAIN_UNDEFINE_NVRAM)
                                    except:
                                        d.undefine()
                                    lv.conn.defineXML(new_xml)
                                    msg += f"<div class='inline-note'>{gfx_type.upper()} graphics adapter added successfully.</div>"
                    except Exception as e:
                        msg += f"<div class='inline-note error'>Failed to add graphics adapter: {html.escape(str(e))}</div>"
                
                if 'remove_graphics' in form:
                    gfx_type = form.get('remove_graphics_type', [''])[0]
                    try:
                        state, _ = d.state()
                        if state == libvirt.VIR_DOMAIN_RUNNING:
                            msg += f"<div class='inline-note error'>Cannot remove graphics while VM is running. Please stop the VM first.</div>"
                        else:
                            dom_xml = d.XMLDesc(libvirt.VIR_DOMAIN_XML_INACTIVE)
                            import xml.etree.ElementTree as ET
                            root = ET.fromstring(dom_xml)
                            devices = root.find('.//devices')
                            
                            if devices is not None:
                                # Find and remove graphics element using detachDeviceFlags
                                for graphics in devices.findall('graphics'):
                                    if graphics.get('type') == gfx_type:
                                        graphics_xml = ET.tostring(graphics, encoding='unicode')
                                        
                                        # Use detachDeviceFlags with CONFIG flag for persistent changes
                                        try:
                                            d.detachDeviceFlags(graphics_xml, libvirt.VIR_DOMAIN_AFFECT_CONFIG)
                                            msg += f"<div class='inline-note'>{gfx_type.upper()} graphics adapter removed successfully.</div>"
                                            break
                                        except Exception:
                                            # Fallback: modify XML without undefining to avoid NVRAM issues
                                            devices.remove(graphics)
                                            new_xml = ET.tostring(root, encoding='unicode')
                                            
                                            # Use virsh define directly to update config without touching NVRAM
                                            import tempfile
                                            import subprocess
                                            with tempfile.NamedTemporaryFile(mode='w', suffix='.xml', delete=False) as f:
                                                f.write(new_xml)
                                                temp_xml = f.name
                                            
                                            try:
                                                subprocess.run(['virsh', 'define', temp_xml], check=True, capture_output=True)
                                                msg += f"<div class='inline-note'>{gfx_type.upper()} graphics adapter removed successfully.</div>"
                                            except subprocess.CalledProcessError:
                                                msg += f"<div class='inline-note error'>Failed to update domain configuration.</div>"
                                            finally:
                                                import os
                                                os.unlink(temp_xml)
                                            break
                    except Exception as e:
                        msg += f"<div class='inline-note error'>Failed to remove graphics adapter: {html.escape(str(e))}</div>"
                
                if 'add_video' in form:
                    video_type = form.get('video_type', ['qxl'])[0]
                    video_vram = form.get('video_vram', ['16384'])[0]
                    try:
                        state, _ = d.state()
                        if state == libvirt.VIR_DOMAIN_RUNNING:
                            msg += f"<div class='inline-note error'>Cannot modify video while VM is running. Please stop the VM first.</div>"
                        else:
                            # Get current XML and modify it
                            dom_xml = d.XMLDesc(libvirt.VIR_DOMAIN_XML_INACTIVE)
                            import xml.etree.ElementTree as ET
                            root = ET.fromstring(dom_xml)
                            devices = root.find('.//devices')
                            
                            if devices is not None:
                                # Create video element XML
                                video_xml = f"<video><model type='{video_type}' vram='{video_vram}'/></video>"
                                
                                # Use attachDeviceFlags with CONFIG flag for persistent changes
                                try:
                                    d.attachDeviceFlags(video_xml, libvirt.VIR_DOMAIN_AFFECT_CONFIG)
                                    msg += f"<div class='inline-note'>{video_type.upper()} video adapter added successfully.</div>"
                                except Exception:
                                    # Fallback: use virsh define to avoid NVRAM issues
                                    new_video = ET.Element('video')
                                    model = ET.SubElement(new_video, 'model')
                                    model.set('type', video_type)
                                    model.set('vram', video_vram)
                                    devices.append(new_video)
                                    
                                    new_xml = ET.tostring(root, encoding='unicode')
                                    
                                    import tempfile
                                    import subprocess
                                    with tempfile.NamedTemporaryFile(mode='w', suffix='.xml', delete=False) as f:
                                        f.write(new_xml)
                                        temp_xml = f.name
                                    
                                    try:
                                        subprocess.run(['virsh', 'define', temp_xml], check=True, capture_output=True)
                                        msg += f"<div class='inline-note'>{video_type.upper()} video adapter added successfully.</div>"
                                    except subprocess.CalledProcessError:
                                        msg += f"<div class='inline-note error'>Failed to update domain configuration.</div>"
                                    finally:
                                        import os
                                        os.unlink(temp_xml)
                    except Exception as e:
                        msg += f"<div class='inline-note error'>Failed to add video adapter: {html.escape(str(e))}</div>"
                
                if 'remove_video' in form:
                    video_type = form.get('remove_video_type', [''])[0]
                    try:
                        state, _ = d.state()
                        if state == libvirt.VIR_DOMAIN_RUNNING:
                            msg += f"<div class='inline-note error'>Cannot remove video while VM is running. Please stop the VM first.</div>"
                        else:
                            dom_xml = d.XMLDesc(libvirt.VIR_DOMAIN_XML_INACTIVE)
                            import xml.etree.ElementTree as ET
                            root = ET.fromstring(dom_xml)
                            devices = root.find('.//devices')
                            
                            if devices is not None:
                                # Find and remove video element using detachDeviceFlags
                                for video in devices.findall('video'):
                                    model = video.find('model')
                                    if model is not None and model.get('type') == video_type:
                                        video_xml = ET.tostring(video, encoding='unicode')
                                        
                                        # Use detachDeviceFlags with CONFIG flag for persistent changes
                                        try:
                                            d.detachDeviceFlags(video_xml, libvirt.VIR_DOMAIN_AFFECT_CONFIG)
                                            msg += f"<div class='inline-note'>{video_type.upper()} video adapter removed successfully.</div>"
                                            break
                                        except Exception:
                                            # Fallback: use virsh define to avoid NVRAM issues
                                            devices.remove(video)
                                            new_xml = ET.tostring(root, encoding='unicode')
                                            
                                            import tempfile
                                            import subprocess
                                            with tempfile.NamedTemporaryFile(mode='w', suffix='.xml', delete=False) as f:
                                                f.write(new_xml)
                                                temp_xml = f.name
                                            
                                            try:
                                                subprocess.run(['virsh', 'define', temp_xml], check=True, capture_output=True)
                                                msg += f"<div class='inline-note'>{video_type.upper()} video adapter removed successfully.</div>"
                                            except subprocess.CalledProcessError:
                                                msg += f"<div class='inline-note error'>Failed to update domain configuration.</div>"
                                            finally:
                                                import os
                                                os.unlink(temp_xml)
                                            break
                    except Exception as e:
                        msg += f"<div class='inline-note error'>Failed to remove video adapter: {html.escape(str(e))}</div>"
                
                if 'add_nic' in form: 
                    ntype = form.get('nic_type', ['bridge'])[0]
                    src = form.get('nic_source', ['virbr0'])[0]
                    model = form.get('nic_model', ['virtio'])[0]
                    mac = form.get('nic_mac', [''])[0].strip()
                    
                    # Build NIC XML with optional MAC address
                    nic_xml = f"<interface type='{ntype}'>"
                    
                    # Add source based on type
                    if ntype == 'bridge':
                        nic_xml += f"<source bridge='{src}'/>"
                    else:  # network
                        nic_xml += f"<source network='{src}'/>"
                    
                    # Add MAC address if provided and valid
                    if mac and re.match(r'^([0-9A-Fa-f]{2}[:]){5}([0-9A-Fa-f]{2})$', mac):
                        nic_xml += f"<mac address='{mac.lower()}'/>"
                    
                    # Add model and close interface tag
                    nic_xml += f"<model type='{model}'/></interface>"
                    
                    # Use appropriate flags based on VM state
                    try:
                        state, _ = d.state()
                        if state == libvirt.VIR_DOMAIN_RUNNING:
                            # VM is running - apply to both live and config
                            flags = getattr(libvirt,'VIR_DOMAIN_AFFECT_LIVE',0) | getattr(libvirt,'VIR_DOMAIN_AFFECT_CONFIG',0)
                        else:
                            # VM is stopped - apply only to config
                            flags = getattr(libvirt,'VIR_DOMAIN_AFFECT_CONFIG',0)
                        d.attachDeviceFlags(nic_xml, flags)
                        msg += "<div class='inline-note'>NIC added successfully.</div>"
                    except Exception as e:
                        msg += f"<div class='inline-note error'>Failed to add NIC: {html.escape(str(e))}</div>"
                if 'detach_nic' in form: 
                    tgt = form.get('nic_target', [''])[0]
                    nic_xml = form.get('nic_xml', [''])[0]
                    try:
                        # Use appropriate flags based on VM state
                        state, _ = d.state()
                        if state == libvirt.VIR_DOMAIN_RUNNING:
                            flags = getattr(libvirt,'VIR_DOMAIN_AFFECT_LIVE',0) | getattr(libvirt,'VIR_DOMAIN_AFFECT_CONFIG',0)
                        else:
                            flags = getattr(libvirt,'VIR_DOMAIN_AFFECT_CONFIG',0)
                        
                        # If we have the XML directly, use it
                        if nic_xml:
                            d.detachDeviceFlags(nic_xml, flags)
                            msg += f"<div class='inline-note'>NIC {html.escape(tgt)} detached successfully.</div>"
                        else:
                            # Fallback: search for the interface by target device
                            dom_xml = d.XMLDesc(libvirt.VIR_DOMAIN_XML_INACTIVE)
                            import xml.etree.ElementTree as ET
                            root = ET.fromstring(dom_xml)
                            found = False
                            for iface in root.findall('.//devices/interface'):
                                t = iface.find('target')
                                if t is not None and t.get('dev') == tgt:
                                    d.detachDeviceFlags(ET.tostring(iface, encoding='unicode'), flags)
                                    msg += f"<div class='inline-note'>NIC {html.escape(tgt)} detached successfully.</div>"
                                    found = True
                                    break
                            
                            # For stopped VMs, also try to match by MAC address or index
                            if not found:
                                for i, iface in enumerate(root.findall('.//devices/interface')):
                                    mac = iface.find('mac')
                                    mac_addr = mac.get('address') if mac is not None else f"auto-{i}"
                                    expected_id = f"if-{mac_addr[-8:]}" if mac_addr != f"auto-{i}" else f"if-{i}"
                                    if expected_id == tgt:
                                        d.detachDeviceFlags(ET.tostring(iface, encoding='unicode'), flags)
                                        msg += f"<div class='inline-note'>NIC {html.escape(tgt)} detached successfully.</div>"
                                        found = True
                                        break
                            
                            if not found:
                                msg += f"<div class='inline-note error'>Could not find NIC {html.escape(tgt)} to remove.</div>"
                                
                    except Exception as e:
                        msg += f"<div class='inline-note error'>Failed to detach NIC: {html.escape(str(e))}</div>"
                
                # Handle snapshot operations
                if 'create_snapshot' in form:
                    try:
                        snap_name = form.get('snap_name', [''])[0]
                        domain_name = form.get('domain', [''])[0] or name
                        
                        if snap_name:
                            # Simple virsh command execution
                            cmd = ['virsh', 'snapshot-create-as', domain_name, snap_name, '--disk-only', '--atomic']
                            result = subprocess.run(cmd, capture_output=True, text=True)
                            
                            if result.returncode == 0:
                                msg += f"<div class='inline-note'>Snapshot '{html.escape(snap_name)}' created successfully.</div>"
                            else:
                                msg += f"<div class='inline-note error'>Snapshot creation failed: {html.escape(result.stderr)}</div>"
                        
                    except Exception as e:
                        msg += f"<div class='inline-note error'>Failed to create snapshot: {html.escape(str(e))}</div>"
                
                if 'restore_snapshot' in form:
                    try:
                        snap_name = form.get('snap_name', [''])[0]
                        
                        if snap_name:
                            # Stop the domain if it's running, then restore
                            if d.isActive():
                                d.destroy()
                            
                            cmd = ['virsh', 'snapshot-revert', name, snap_name]
                            result = subprocess.run(cmd, capture_output=True, text=True)
                            
                            if result.returncode == 0:
                                msg += f"<div class='inline-note'>Snapshot '{html.escape(snap_name)}' restored successfully.</div>"
                            else:
                                msg += f"<div class='inline-note error'>Snapshot restore failed: {html.escape(result.stderr)}</div>"
                        
                    except Exception as e:
                        msg += f"<div class='inline-note error'>Failed to restore snapshot: {html.escape(str(e))}</div>"
                
                if 'delete_snapshot' in form:
                    try:
                        snap_name = form.get('snap_name', [''])[0]
                        
                        if snap_name:
                            cmd = ['virsh', 'snapshot-delete', name, snap_name]
                            result = subprocess.run(cmd, capture_output=True, text=True)
                            
                            if result.returncode == 0:
                                msg += f"<div class='inline-note'>Snapshot '{html.escape(snap_name)}' deleted successfully.</div>"
                            else:
                                msg += f"<div class='inline-note error'>Snapshot deletion failed: {html.escape(result.stderr)}</div>"
                        
                    except Exception as e:
                        msg += f"<div class='inline-note error'>Failed to delete snapshot: {html.escape(str(e))}</div>"
                        
            except Exception as e:
                msg += f"<div class='inline-note'>{html.escape(str(e))}</div>"
        # Info gathering
        state, _ = d.state()
        status = 'running' if state == libvirt.VIR_DOMAIN_RUNNING else 'shutoff'
        
        # Define console HTML early so it can be used in layout
        if status == 'running':
            console_html = f"""
            <div class=\"vm-console small\" id=\"vm-console\">
                <div class=\"console-header\" style=\"display:flex;justify-content:space-between;align-items:center;gap:12px;\">
                    <span style=\"flex:1;\"></span>
                    <a href="/novnc/vnc.html?path=vnc_ws/{html.escape(name)}&autoconnect=true" class=\"button small secondary\" title="Open full interactive console" onclick="window.open(this.href, 'vnc_console', 'width=1024,height=768,resizable=yes,scrollbars=yes'); return false;">↗ Full Console</a>
                </div>
                <div class="console-content" style="height: calc(100% - 35px); padding: 2px;">
                    <div style="background:#000;width:100%;height:100%;position:relative;overflow:hidden;">
                        <img id="console-preview" 
                             src="/screenshot?domain={html.escape(name)}" 
                             style="width:100%;height:100%;object-fit:contain;object-position:center;" 
                             alt="VM Console Preview"
                             onerror="this.style.display='none';this.nextElementSibling.style.display='flex';"
                             onload="this.nextElementSibling.style.display='none';">
                        <div style="display:none;width:100%;height:100%;background:#000;color:#888;font-size:14px;align-items:center;justify-content:center;position:absolute;top:0;left:0;">
                            Console preview unavailable
                        </div>
                    </div>
                </div>
            </div>
            <script>
            // Minimal console functionality - Full Console button only
            
            function sendCtrlAltDel() {{
                // Send Ctrl+Alt+Del key sequence
                fetch('/vm_key', {{
                    method: 'POST',
                    headers: {{'Content-Type': 'application/x-www-form-urlencoded'}},
                    body: 'domain={html.escape(name)}&key=ctrl_alt_del'
                }});
            }}
            
            // Conservative screenshot refresh - only if image loads successfully
            function refreshConsolePreview() {{
                const img = document.getElementById('console-preview');
                if (img && img.style.display !== 'none') {{
                    const newImg = new Image();
                    newImg.onload = function() {{
                        img.src = newImg.src;
                    }};
                    newImg.onerror = function() {{
                        // If refresh fails, don't change existing image
                        console.log('Screenshot refresh failed, keeping existing image');
                    }};
                    newImg.src = '/screenshot?domain={html.escape(name)}&t=' + Date.now();
                }}
            }}
            
            // Start conservative refreshing - longer interval and only if successful
            setTimeout(() => {{
                setInterval(refreshConsolePreview, 10000); // Refresh every 10 seconds
            }}, 5000); // Wait 5 seconds before starting refresh cycle
            </script>"""
        else:
            # VM not running - show simple message
            console_html = f"""
            <div class="vm-console small" id="vm-console">
                <div class="console-header">
                    <span>🖥️ Console (VM not running)</span>
                </div>
                <div class="console-content" style="height: calc(100% - 35px); padding: 20px; background:#333; color:#888; text-align:center;">
                    <div>⏸️ VM Not Running</div>
                    <div style="font-size:12px;margin-top:5px;">Start the VM to access console</div>
                </div>
            </div>"""
        
        # Generate snapshots list HTML
        snapshots = self.get_domain_snapshots(d)
        if snapshots:
            snapshot_rows = []
            for snap in snapshots:
                state_icon = {
                    'running': '🟢',
                    'shutoff': '🔴', 
                    'paused': '🟡'
                }.get(snap['state'], '⚪')
                
                snapshot_rows.append(f"""
                <tr style='border-bottom: 1px solid var(--border);'>
                    <td style='padding: 12px 8px; font-weight: 600;'>{html.escape(snap['name'])}</td>
                    <td style='padding: 12px 8px; color: var(--muted);'>{html.escape(snap['description'])}</td>
                    <td style='padding: 12px 8px; color: var(--muted); font-size: 13px;'>{snap['creation_time']}</td>
                    <td style='padding: 12px 8px; text-align: center;'>{state_icon} {snap['state'].title()}</td>
                    <td style='padding: 12px 8px; text-align: right;'>
                        <button onclick='restoreSnapshot("{html.escape(name)}", "{html.escape(snap["name"])}")' class='button small secondary' style='margin-right: 4px;'>↩️ Restore</button>
                        <button onclick='deleteSnapshot("{html.escape(name)}", "{html.escape(snap["name"])}")' class='button small danger'>🗑️ Delete</button>
                    </td>
                </tr>
                """)
            
            snapshot_list_html = f"""
            <h4 style='margin: 0 0 12px 0; color: var(--fg); font-size: 16px;'>Existing Snapshots ({len(snapshots)})</h4>
            <div style='overflow-x: auto; border: 1px solid var(--border); border-radius: 6px;'>
                <table style='width: 100%; border-collapse: collapse; background: var(--card);'>
                    <thead>
                        <tr style='background: var(--muted); border-bottom: 2px solid var(--border);'>
                            <th style='padding: 12px 8px; text-align: left; font-weight: 600;'>Name</th>
                            <th style='padding: 12px 8px; text-align: left; font-weight: 600;'>Description</th>
                            <th style='padding: 12px 8px; text-align: left; font-weight: 600;'>Created</th>
                            <th style='padding: 12px 8px; text-align: center; font-weight: 600;'>State</th>
                            <th style='padding: 12px 8px; text-align: right; font-weight: 600;'>Actions</th>
                        </tr>
                    </thead>
                    <tbody>
                        {''.join(snapshot_rows)}
                    </tbody>
                </table>
            </div>
            """
        else:
            snapshot_list_html = """
            <div style='text-align: center; padding: 40px; color: var(--muted); border: 1px dashed var(--border); border-radius: 6px;'>
                <div style='font-size: 48px; margin-bottom: 12px;'>📸</div>
                <div style='font-size: 16px; margin-bottom: 8px;'>No snapshots yet</div>
                <div style='font-size: 14px;'>Create your first snapshot to save the current VM state</div>
            </div>
            """
        
        auto = d.autostart()
        vm_uuid = d.UUIDString()
        xml = d.XMLDesc(0)
        import xml.etree.ElementTree as ET
        root = ET.fromstring(xml)
        # Safe extraction of vcpu and memory values without requiring a running domain
        try:
            vcpu_display = d.maxVcpus()
        except Exception:
            try:
                node_vcpu = root.find('.//vcpu')
                vcpu_display = int(node_vcpu.text.strip()) if node_vcpu is not None and node_vcpu.text else 1
            except Exception:
                vcpu_display = 1
        
        # Extract CPU topology from XML
        cpu_sockets = 1
        cpu_cores = vcpu_display
        cpu_threads = 1
        try:
            topology_node = root.find('.//cpu/topology')
            if topology_node is not None:
                cpu_sockets = int(topology_node.get('sockets', '1'))
                cpu_cores = int(topology_node.get('cores', str(vcpu_display)))
                cpu_threads = int(topology_node.get('threads', '1'))
        except Exception:
            # Fallback to default values if topology parsing fails
            pass
        try:
            mem_display = d.maxMemory() // 1024  # KiB -> MiB
        except Exception:
            try:
                node_mem = root.find('.//memory') or root.find('.//currentMemory')
                mem_display = int(node_mem.text.strip()) // 1024 if node_mem is not None and node_mem.text else 1024
            except Exception:
                mem_display = 1024
        
        # Detect current OS type from XML
        current_os_type = 'linux'  # default
        try:
            # Check for Hyper-V enlightenments to determine if it's Windows
            hyperv_node = root.find('.//features/hyperv')
            if hyperv_node is not None:
                current_os_type = 'windows'
        except Exception:
            pass
        
        # Detect current CPU configuration
        current_cpu_mode = 'host-model'  # default
        current_cpu_model = ''
        try:
            cpu_node = root.find('.//cpu')
            if cpu_node is not None:
                mode = cpu_node.get('mode', '')
                if mode == 'host-passthrough':
                    current_cpu_mode = 'host-passthrough'
                elif mode == 'host-model':
                    current_cpu_mode = 'host-model'
                else:
                    # Check for custom model
                    model_node = cpu_node.find('model')
                    if model_node is not None:
                        model_name = model_node.text or 'qemu64'
                        current_cpu_model = model_name
                        
                        # Check if this model is from our QEMU models list
                        try:
                            qemu_models = self.get_qemu_cpu_models()
                            # Extract just the model names (without the 'custom:' prefix)
                            qemu_model_names = [value.replace('custom:', '') for value, label in qemu_models if value.startswith('custom:')]
                            if model_name in qemu_model_names:
                                current_cpu_mode = f'custom:{model_name}'
                            else:
                                current_cpu_mode = 'custom'
                        except Exception:
                            current_cpu_mode = 'custom'
        except Exception:
            pass

        # Extract current boot order from per-device boot elements
        current_boot_order = "hd,cdrom,network"  # default
        try:
            # Find all devices with boot order attributes
            boot_devices = []
            for device in root.findall('.//devices/*[@order]'):
                order = int(device.get('order', 0))
                device_type = 'hd'  # default to hard disk
                if device.tag == 'disk':
                    device_type = 'hd'
                elif device.tag == 'interface':
                    device_type = 'network'
                # Add more device types as needed
                boot_devices.append((order, device_type))
            
            if boot_devices:
                # Sort by boot order and extract device types
                boot_devices.sort(key=lambda x: x[0])
                ordered_devices = [dev_type for _, dev_type in boot_devices]
                # Fill remaining slots with default order
                remaining = ['cdrom', 'network'] if 'hd' in ordered_devices else ['hd', 'cdrom', 'network']
                for dev in remaining:
                    if dev not in ordered_devices:
                        ordered_devices.append(dev)
                current_boot_order = ','.join(ordered_devices[:3])  # Limit to 3 devices
        except Exception:
            pass
        disks = []
        cdroms = []
        boot_device = None  # Track which device has boot order='1'
        
        for disk in root.findall('.//devices/disk'):
            tgt = disk.find('target'); src = disk.find('source'); boot = disk.find('boot')
            device_type = disk.get('device', 'disk')
            is_boot_device = boot is not None and boot.get('order') == '1'
            if is_boot_device:
                boot_device = tgt.get('dev') if tgt is not None else None
                
            if tgt is not None:
                if device_type == 'cdrom':
                    cdroms.append((tgt.get('dev'), src.get('file') if src is not None else '', tgt.get('bus', 'ide'), is_boot_device))
                else:
                    disks.append((tgt.get('dev'), src.get('file') if src is not None else '', tgt.get('bus', 'virtio'), is_boot_device))
        pci_att = []
        for hd in root.findall('.//devices/hostdev'):
            a = hd.find('source/address')
            if a is not None:
                pci_att.append(f"{int(a.get('domain','0'),16):04x}:{int(a.get('bus','0'),16):02x}:{int(a.get('slot','0'),16):02x}.{int(a.get('function','0'),16)}")
        
        # Graphics devices
        graphics_devices = []
        for gfx in root.findall('.//devices/graphics'):
            gfx_type = gfx.get('type', 'unknown')
            port = gfx.get('port', '-1')
            listen = gfx.get('listen', '127.0.0.1')
            graphics_devices.append({
                'type': gfx_type,
                'port': port,
                'listen': listen,
                'xml': ET.tostring(gfx, encoding='unicode')
            })
        
        # Video devices
        video_devices = []
        for video in root.findall('.//devices/video'):
            model = video.find('model')
            if model is not None:
                video_type = model.get('type', 'unknown')
                vram = model.get('vram', 'unknown')
                video_devices.append({
                    'type': video_type,
                    'vram': vram,
                    'xml': ET.tostring(video, encoding='unicode')
                })
        
        nics = []
        for i, iface in enumerate(root.findall('.//devices/interface')):
            tgt = iface.find('target'); src = iface.find('source'); model = iface.find('model'); mac = iface.find('mac')
            # For stopped VMs, use a unique identifier based on interface config
            if tgt is not None and tgt.get('dev'):
                name_dev = tgt.get('dev')
            else:
                # Generate a consistent ID for stopped VMs based on interface position and attributes
                mac_addr = mac.get('address') if mac is not None else f"auto-{i}"
                name_dev = f"if-{mac_addr[-8:]}" if mac_addr != f"auto-{i}" else f"if-{i}"
            
            source = (src.get('bridge') or src.get('network') or '?') if src is not None else '?'
            mac_addr = mac.get('address') if mac is not None else 'Unknown'
            nics.append((name_dev, source, model.get('type') if model is not None else '', mac_addr, ET.tostring(iface, encoding='unicode')))
        # Build streamlined view (only requested sections)
        # Actions for both running and stopped VMs
        actions = []
        if status != 'running':
            actions.append(f"<button type='button' class='button' onclick=\"location.href='/?domain={html.escape(name)}&op=start'\">▶️ Start</button>")
            actions.append(f"<button type='button' class='button secondary' onclick=\"location.href='/?domain={html.escape(name)}&op={'noautostart' if auto else 'autostart'}'\">🔄 {'No Auto' if auto else 'Autostart'}</button>")
            actions.append(f"<button type='button' class='button danger' onclick=\"if(confirm('Delete domain (files & NVRAM)?')) location.href='/?domain={html.escape(name)}&op=undefine&confirm=1'\">🗑️ Delete</button>")
        else:
            actions.append(f"<button type='button' class='button secondary' onclick=\"location.href='/?domain={html.escape(name)}&op=shutdown'\">⏹️ Shutdown</button>")
            actions.append(f"<button type='button' class='button danger' onclick=\"if(confirm('Force stop VM?')) location.href='/?domain={html.escape(name)}&op=destroy&confirm=1'\">⚡ Force Stop</button>")
            actions.append(f"<button type='button' class='button' onclick=\"location.href='/?domain={html.escape(name)}&op=reboot'\">🔄 Reboot</button>")
            actions.append(f"<button type='button' class='button secondary' onclick=\"location.href='/?domain={html.escape(name)}&op={'noautostart' if auto else 'autostart'}'\">🔧 {'No Auto' if auto else 'Autostart'}</button>")
        cpu_mem_form = f"""
        <div style='background: var(--card); border: 1px solid var(--border); border-radius: 6px; padding: 16px; margin-bottom: 12px;'>
            <form method='post' style='display: grid; grid-template-columns: 1fr 1fr; gap: 16px; align-items: start;'>
                <input type='hidden' name='update_cpu_mem' value='1'>
                
                <!-- Left Column -->
                <div style='display: flex; flex-direction: column; gap: 14px;'>
                    <div class='form-group'>
                        <label style='display: block; margin-bottom: 6px; font-size: 13px; font-weight: 500; color: var(--text-primary);'>OS Type</label>
                        <select name='os_type' class='enh' style='width: 100%; padding: 8px; border: 1px solid var(--border); border-radius: 6px; background: var(--bg-secondary); font-size: 13px;'>
                            <option value='linux'{"selected" if current_os_type == 'linux' else ''}>Linux</option>
                            <option value='windows'{"selected" if current_os_type == 'windows' else ''}>Windows</option>
                        </select>
                    </div>

                    <div class='form-group'>
                        <label style='display: block; margin-bottom: 6px; font-size: 13px; font-weight: 500; color: var(--text-primary);'>CPU Topology</label>
                        <div style='display: grid; grid-template-columns: 1fr 1fr 1fr; gap: 8px; margin-bottom: 6px;'>
                            <div>
                                <label style='display: block; margin-bottom: 3px; font-size: 11px; color: var(--text-secondary);'>Sockets</label>
                                <input name='cpu_sockets' type='number' value='{cpu_sockets}' min='1' style='width: 100%; padding: 8px; border: 1px solid var(--border); border-radius: 4px; background: var(--bg-secondary); font-size: 13px; text-align: center;'>
                            </div>
                            <div>
                                <label style='display: block; margin-bottom: 3px; font-size: 11px; color: var(--text-secondary);'>Cores</label>
                                <input name='cpu_cores' type='number' value='{cpu_cores}' min='1' style='width: 100%; padding: 8px; border: 1px solid var(--border); border-radius: 4px; background: var(--bg-secondary); font-size: 13px; text-align: center;'>
                            </div>
                            <div>
                                <label style='display: block; margin-bottom: 3px; font-size: 11px; color: var(--text-secondary);'>Threads</label>
                                <input name='cpu_threads' type='number' value='{cpu_threads}' min='1' style='width: 100%; padding: 8px; border: 1px solid var(--border); border-radius: 4px; background: var(--bg-secondary); font-size: 13px; text-align: center;'>
                            </div>
                        </div>
                        <div style='display: flex; align-items: center; gap: 6px; padding: 6px 10px; background: var(--bg-tertiary); border-radius: 4px; border: 1px solid var(--border);'>
                            <span style='font-size: 11px; color: var(--text-secondary);'>Total vCPUs:</span>
                            <span style='font-size: 13px; font-weight: 600; color: var(--accent);'>{cpu_sockets * cpu_cores * cpu_threads}</span>
                        </div>
                    </div>

                    <div class='form-group'>
                        <label style='display: block; margin-bottom: 6px; font-size: 13px; font-weight: 500; color: var(--text-primary);'>Memory</label>
                        <div style='display: flex; align-items: center; gap: 8px; margin-bottom: 6px;'>
                            <input name='memory_gb' type='number' value='{int(mem_display/1024)}' min='{max(1, int(mem_display/1024))}' step='0.5' style='flex: 1; padding: 8px; border: 1px solid var(--border); border-radius: 6px; background: var(--bg-secondary); font-size: 13px;'>
                            <span style='font-size: 13px; color: var(--text-secondary); min-width: 25px;'>GiB</span>
                        </div>
                        <div style='display: flex; align-items: center; gap: 6px; padding: 6px 10px; background: var(--bg-tertiary); border-radius: 4px; border: 1px solid var(--border);'>
                            <span style='font-size: 11px; color: var(--text-secondary);'>Current:</span>
                            <span style='font-size: 13px; font-weight: 600; color: var(--accent);'>{mem_display} MiB</span>
                        </div>
                    </div>
                </div>

                <!-- Right Column -->
                <div style='display: flex; flex-direction: column; gap: 14px;'>
                    <div class='form-group'>
                        <label style='display: block; margin-bottom: 6px; font-size: 13px; font-weight: 500; color: var(--text-primary);'>CPU Type</label>
                        <select name='cpu_mode' class='enh' id='vm_cpu_mode' style='width: 100%; padding: 8px; border: 1px solid var(--border); border-radius: 6px; background: var(--bg-secondary); font-size: 13px;'>
                            <option value='host-model'{"selected" if current_cpu_mode == 'host-model' else ''}>Host Model</option>
                            <option value='host-passthrough'{"selected" if current_cpu_mode == 'host-passthrough' else ''}>Host Passthrough</option>
                            <option value='custom'{"selected" if current_cpu_mode == 'custom' else ''}>Custom</option>
                            """ + ''.join(
                                f"<option value='{html.escape(value)}'{'selected' if current_cpu_mode == value else ''}>{html.escape(label)}</option>"
                                for value, label in self.get_qemu_cpu_models()
                                if value not in ['host-model', 'host-passthrough']
                            ) + f"""
                        </select>
                    </div>

                    <div class='form-group' id='vm_custom_cpu_model' style='{'display: block' if current_cpu_mode == 'custom' else 'display: none'}'>
                        <label style='display: block; margin-bottom: 6px; font-size: 13px; font-weight: 500; color: var(--text-primary);'>CPU Model</label>
                        <input name='cpu_model' value='{current_cpu_model}' placeholder='qemu64, core2duo, etc.' style='width: 100%; padding: 8px; border: 1px solid var(--border); border-radius: 6px; background: var(--bg-secondary); font-size: 13px;'>
                    </div>

                    <div style='margin-top: auto; display: flex; justify-content: flex-end;'>
                        <button type='submit' class='button primary' style='padding: 8px 16px; font-size: 13px; font-weight: 500;'>
                            ⚡ Apply Changes
                        </button>
                    </div>
                </div>
            </form>
        </div>
        <script>
        // Handle CPU mode changes
        document.addEventListener('DOMContentLoaded', function() {{
            const cpuSelect = document.getElementById('vm_cpu_mode');
            const customCpuDiv = document.getElementById('vm_custom_cpu_model');
            
            function updateCpuDisplay() {{
                const selectedValue = cpuSelect ? cpuSelect.value : '';
                if (customCpuDiv) {{
                    if (selectedValue === 'custom') {{
                        customCpuDiv.style.display = 'block';
                    }} else {{
                        customCpuDiv.style.display = 'none';
                    }}
                }}
            }}
            
            if (cpuSelect) {{
                cpuSelect.addEventListener('change', updateCpuDisplay);
                // Also update on page load
                updateCpuDisplay();
            }}
        }});
        </script>
        <div style='margin-top: 12px; padding: 8px; background: var(--bg-secondary); border-radius: 4px; color: var(--text-secondary); font-size: 12px;'>
            ℹ️ When VM is running, only CPU/memory increases are applied. OS type changes require VM shutdown.
        </div>"""

        # Disks list + resize form
        disk_items=[]
        for dev, path, bus, is_boot in disks:
            used_space, allocated_space = self.get_disk_usage(path)
            used_fmt = f"{used_space:.1f}" if used_space > 0 else '-'
            allocated_fmt = f"{allocated_space:.1f}" if allocated_space > 0 else '-'
            
            # Backward compatibility for now
            sz_fmt = allocated_fmt
            
            # Get current bus
            current_bus = bus if bus else 'virtio'
            is_running = status == 'running'
            
            # Detect current pool for this disk - simple path-based approach
            current_pool = 'unknown'
            try:
                # Extract first directory after root slash: /ssd/vm/disk.img -> 'ssd'
                if path.startswith('/') and len(path) > 1:
                    first_slash_pos = path.find('/', 1)
                    if first_slash_pos > 1:
                        current_pool = path[1:first_slash_pos]
                    else:
                        # Handle case where there's only one directory level like /ssd
                        current_pool = path[1:] if '/' not in path[1:] else path[1:].split('/')[0]
            except:
                pass
          
        # Create professional storage display
        storage_items = []
        
        # Add disk items with professional layout
        for dev, path, bus, is_boot in disks:
            used_space, allocated_space = self.get_disk_usage(path)
            used_fmt = f"{used_space:.1f}" if used_space > 0 else '-'
            allocated_fmt = f"{allocated_space:.1f}" if allocated_space > 0 else '-'
            current_bus = bus if bus else 'virtio'
            is_running = status == 'running'
            
            storage_items.append(f"""
            <div style='display: flex; align-items: center; padding: 16px; border: 1px solid var(--border); border-radius: 8px; margin-bottom: 8px; background: var(--card); transition: all 0.2s ease;' onmouseover='this.style.borderColor="var(--accent)"' onmouseout='this.style.borderColor="var(--border)"'>
                <!-- Device Icon & Info -->
                <div style='display: flex; align-items: center; gap: 16px; flex: 1; min-width: 0;'>
                    <div style='width: 40px; height: 40px; border-radius: 8px; background: linear-gradient(135deg, var(--accent), var(--accent)88); display: flex; align-items: center; justify-content: center; font-size: 18px; color: white; flex-shrink: 0;'>💾</div>
                    <div style='flex: 1; min-width: 0;'>
                        <div style='display: flex; align-items: center; gap: 12px; margin-bottom: 6px;'>
                            <span style='font-weight: 600; color: var(--fg); font-size: 15px;'>{html.escape(dev)}</span>
                            <span style='background: var(--border); color: var(--text-secondary); padding: 2px 8px; border-radius: 12px; font-size: 11px; text-transform: uppercase; font-weight: 600;'>{html.escape(current_bus)}</span>
                            <span style='color: var(--text-secondary); font-size: 13px; font-weight: 500;'>{allocated_fmt} GB</span>
                            <label style='display: flex; align-items: center; gap: 6px; cursor: {'default' if is_running else 'pointer'}; padding: 4px 8px; border-radius: 16px; background: {"var(--success)22" if is_boot else ("var(--border)44" if is_running else "var(--border)")}; border: 1px solid {"var(--success)" if is_boot else ("var(--border)" if is_running else "transparent")}; transition: all 0.2s ease; opacity: {'0.7' if is_running else '1'};'>
                                <input type='checkbox' name='boot_device' value='{html.escape(dev)}' {'checked' if is_boot else ''} onchange='handleBootDeviceChange(this)' style='margin: 0; accent-color: var(--success);' {'disabled' if is_running else ''}>
                                <span style='font-size: 11px; font-weight: 600; color: {"var(--success)" if is_boot else ("var(--text-secondary)" if not is_running else "var(--text-secondary)")}; text-transform: uppercase;'>Boot{' (Running)' if is_running and is_boot else ''}</span>
                            </label>
                        </div>
                        <div style='color: var(--text-secondary); font-size: 12px; overflow: hidden; text-overflow: ellipsis; white-space: nowrap; max-width: 400px;'>
                            {html.escape(path)}
                        </div>
                    </div>
                </div>
                
                <!-- Actions -->
                <div style='display: flex; align-items: center; gap: 8px; flex-shrink: 0;'>
                    <div style='display: flex; align-items: center; gap: 4px; background: var(--bg); border: 1px solid var(--border); border-radius: 6px; padding: 4px;'>
                        <input name='resize_size' type='number' min='{allocated_fmt if allocated_fmt!="-" else 1}' placeholder='{allocated_fmt}' style='width: 60px; padding: 4px 6px; border: none; background: transparent; color: var(--fg); font-size: 12px;' title='New size in GB'>
                        <button type='button' onclick='resizeDisk("{html.escape(dev)}", this.previousElementSibling.value)' style='background: var(--success); color: white; border: none; padding: 4px 8px; border-radius: 4px; font-size: 11px; cursor: pointer; font-weight: 600;' title='Resize disk'>↗</button>
                    </div>
                    
                    <select onchange='if(this.value) changeDiskBus("{html.escape(dev)}", this.value)' style='padding: 6px 8px; border: 1px solid var(--border); border-radius: 6px; background: var(--bg); color: var(--fg); font-size: 12px;' {'disabled' if is_running else ''} title='Change bus type'>
                        <option value='virtio'{'selected' if current_bus=="virtio" else ''}>VirtIO</option>
                        <option value='scsi'{'selected' if current_bus=="scsi" else ''}>SCSI</option>
                        <option value='sata'{'selected' if current_bus=="sata" else ''}>SATA</option>
                    </select>
                    
                    <button type='button' onclick='if(confirm("Permanently delete disk {html.escape(dev)}?")) deleteDisk("{html.escape(dev)}")' style='background: var(--danger); color: white; border: none; padding: 6px 10px; border-radius: 6px; font-size: 12px; cursor: pointer; font-weight: 600;' {'disabled' if is_running else ''} title='Delete disk'>🗑</button>
                </div>
            </div>""")
        
        # Add CD/DVD items with professional layout
        for dev, path, bus, is_boot in cdroms:
            storage_items.append(f"""
            <div style='display: flex; align-items: center; padding: 16px; border: 1px solid var(--border); border-radius: 8px; margin-bottom: 8px; background: var(--card); transition: all 0.2s ease;' onmouseover='this.style.borderColor="var(--accent)"' onmouseout='this.style.borderColor="var(--border)"'>
                <!-- Device Icon & Info -->
                <div style='display: flex; align-items: center; gap: 16px; flex: 1; min-width: 0;'>
                    <div style='width: 40px; height: 40px; border-radius: 8px; background: linear-gradient(135deg, var(--warn), var(--warn)88); display: flex; align-items: center; justify-content: center; font-size: 18px; color: white; flex-shrink: 0;'>💿</div>
                    <div style='flex: 1; min-width: 0;'>
                        <div style='display: flex; align-items: center; gap: 12px; margin-bottom: 6px;'>
                            <span style='font-weight: 600; color: var(--fg); font-size: 15px;'>{html.escape(dev)}</span>
                            <span style='background: var(--border); color: var(--text-secondary); padding: 2px 8px; border-radius: 12px; font-size: 11px; text-transform: uppercase; font-weight: 600;'>CD/DVD</span>
                            <label style='display: flex; align-items: center; gap: 6px; cursor: {'default' if is_running else 'pointer'}; padding: 4px 8px; border-radius: 16px; background: {"var(--success)22" if is_boot else ("var(--border)44" if is_running else "var(--border)")}; border: 1px solid {"var(--success)" if is_boot else ("var(--border)" if is_running else "transparent")}; transition: all 0.2s ease; opacity: {'0.7' if is_running else '1'};'>
                                <input type='checkbox' name='boot_device' value='{html.escape(dev)}' {'checked' if is_boot else ''} onchange='handleBootDeviceChange(this)' style='margin: 0; accent-color: var(--success);' {'disabled' if is_running else ''}>
                                <span style='font-size: 11px; font-weight: 600; color: {"var(--success)" if is_boot else ("var(--text-secondary)" if not is_running else "var(--text-secondary)")}; text-transform: uppercase;'>Boot{' (Running)' if is_running and is_boot else ''}</span>
                            </label>
                        </div>
                        <div style='color: var(--text-secondary); font-size: 12px; overflow: hidden; text-overflow: ellipsis; white-space: nowrap; max-width: 400px;'>
                            {html.escape(path) if path else "No disc inserted"}
                        </div>
                    </div>
                </div>
                
                <!-- Actions -->
                <div style='display: flex; align-items: center; gap: 8px; flex-shrink: 0;'>
                    <button type='button' onclick='ejectCdrom("{html.escape(dev)}")' style='background: var(--info); color: white; border: none; padding: 6px 10px; border-radius: 6px; font-size: 12px; cursor: pointer; font-weight: 600;' {'disabled' if not path else ''} title='Eject disc'>⏏</button>
                    <button type='button' onclick='if(confirm("Remove CD/DVD drive {html.escape(dev)}?")) removeCdrom("{html.escape(dev)}")' style='background: var(--danger); color: white; border: none; padding: 6px 10px; border-radius: 6px; font-size: 12px; cursor: pointer; font-weight: 600;' title='Remove drive'>🗑</button>
                </div>
            </div>""")
        
        storage_list = f"""
        <div style='margin-bottom: 24px;'>
            <h3 style='margin: 0 0 16px 0; display: flex; align-items: center; gap: 12px; font-size: 20px; color: var(--fg); font-weight: 600;'>
                <div style='width: 32px; height: 32px; border-radius: 8px; background: var(--accent); display: flex; align-items: center; justify-content: center; color: white; font-size: 16px;'>💾</div>
                Storage Devices
            </h3>
            <div>
                {"".join(storage_items) if storage_items else '<div style="text-align: center; padding: 40px; color: var(--text-secondary); background: var(--card); border: 1px solid var(--border); border-radius: 8px; font-size: 14px;">No storage devices attached</div>'}
            </div>
        </div>"""
        
        # Add script to check for active migrations on page load
        migration_check_script = """
        <script>
        // Check for active migrations when page loads
        (function() {
            function checkActiveMigrations() {
                console.log('Checking for active migrations...');
                fetch('/api/active-migrations')
                    .then(response => response.json())
                    .then(data => {
                        console.log('Active migrations response:', data);
                        if (data.migrations && data.migrations.length > 0) {
                            data.migrations.forEach(migration => {
                                const diskTarget = migration.disk_target;
                                const jobId = migration.job_id;
                                
                                console.log('Setting up monitoring for disk:', diskTarget, 'job:', jobId);
                                
                                // Show migration progress area for this disk
                                const progressArea = document.getElementById('migration-progress-' + diskTarget);
                                if (progressArea) {
                                    progressArea.style.display = 'block';
                                    
                                    // Start monitoring this migration
                                    function updateProgress() {
                                        fetch('/api/migration-status/' + jobId)
                                            .then(response => response.json())
                                            .then(data => {
                                                console.log('Migration status for', diskTarget, ':', data);
                                                const statusText = document.getElementById('migration-status-' + diskTarget);
                                                const progressBar = document.getElementById('migration-bar-' + diskTarget);
                                                const progressPercent = document.getElementById('migration-percent-' + diskTarget);
                                                
                                                if (statusText && progressBar && progressPercent) {
                                                    const progress = data.progress || 0;
                                                    
                                                    statusText.textContent = data.status || 'starting';
                                                    progressBar.style.width = progress + '%';
                                                    progressPercent.textContent = progress + '%';
                                                    
                                                    if (data.status === 'completed') {
                                                        statusText.textContent = 'Migration completed successfully';
                                                        statusText.style.color = 'var(--success, #28a745)';
                                                        setTimeout(() => {
                                                            if (progressArea) progressArea.style.display = 'none';
                                                            // Refresh page to show new pool assignment
                                                            window.location.reload();
                                                        }, 3000);
                                                        clearInterval(window['migrationInterval_' + jobId.replace(/-/g, '_')]);
                                                    } else if (data.status === 'failed') {
                                                        statusText.textContent = 'Migration failed: ' + (data.error || 'Unknown error');
                                                        statusText.style.color = 'var(--error, #dc3545)';
                                                        clearInterval(window['migrationInterval_' + jobId.replace(/-/g, '_')]);
                                                    } else if (data.status === 'completed_with_warnings') {
                                                        statusText.textContent = 'Migration completed with warnings: ' + (data.error || '');
                                                        statusText.style.color = 'var(--warning, #ffc107)';
                                                        setTimeout(() => {
                                                            if (progressArea) progressArea.style.display = 'none';
                                                            // Refresh page to show new pool assignment
                                                            window.location.reload();
                                                        }, 5000);
                                                        clearInterval(window['migrationInterval_' + jobId.replace(/-/g, '_')]);
                                                    }
                                                }
                                            })
                                            .catch(error => console.log('Migration status check failed:', error));
                                    }
                                    
                                    // Start monitoring with immediate first call
                                    updateProgress(); // Initial call
                                    window['migrationInterval_' + jobId.replace(/-/g, '_')] = setInterval(updateProgress, 1000); // Check every second
                                }
                            });
                        } else {
                            console.log('No active migrations found');
                        }
                    })
                    .catch(error => console.log('Active migrations check failed:', error));
            }
            
            // Check when page loads
            if (document.readyState === 'loading') {
                document.addEventListener('DOMContentLoaded', checkActiveMigrations);
            } else {
                checkActiveMigrations();
            }
            
            // Also check periodically for new migrations (every 5 seconds)
            setInterval(checkActiveMigrations, 5000);
        })();
        </script>
        """
        
        storage_list += migration_check_script
        
        # Add migration modal
        # Move migration modal and global script to the top of the body for global availability
        migration_modal = """
        <!-- Migration Modal -->
        <div id='migration-modal' style='display: none; position: fixed; top: 0; left: 0; width: 100%; height: 100%; background: rgba(0,0,0,0.5); z-index: 1000;'>
            <div style='position: absolute; top: 50%; left: 50%; transform: translate(-50%, -50%); background: var(--card); border-radius: 8px; padding: 24px; min-width: 400px; box-shadow: 0 4px 12px rgba(0,0,0,0.3);'>
                <h3 style='margin: 0 0 16px 0; color: var(--accent);'>🔄 Migrate Disk</h3>
                <form method='post' id='migration-form'>
                    <input type='hidden' name='migrate_disk' value='1'>
                    <input type='hidden' name='disk_target' id='migration-disk-target' value=''>
                    <div style='margin-bottom: 16px;'>
                        <label style='display: block; margin-bottom: 8px; font-weight: 500;'>Current Pool:</label>
                        <span id='migration-current-pool' style='color: var(--text-secondary);'></span>
                    </div>
                    <div style='margin-bottom: 20px;'>
                        <label style='display: block; margin-bottom: 8px; font-weight: 500;'>Target Pool:</label>
                        <select name='target_pool' id='migration-target-pool' style='width: 100%; padding: 10px; border: 1px solid var(--border); border-radius: 6px; background: var(--card); color: var(--fg);'>""" + \
                        ''.join(f"<option value='{html.escape(p.name())}'>{html.escape(p.name())}</option>" for p in lv.list_pools() if p.isActive()) + """
                        </select>
                    </div>
                    <div style='display: flex; gap: 12px; justify-content: flex-end;'>
                        <button type='button' class='button secondary' onclick='closeMigrationModal()'>Cancel</button>
                        <button type='submit' class='button primary'>🔄 Start Migration</button>
                    </div>
                </form>
            </div>
        </div>
        <script>
        // Ensure migration functions are globally available
        window.openMigrationModal = function(diskTarget, currentPool) {
            console.log('Opening migration modal for disk:', diskTarget, 'current pool:', currentPool);
            const modal = document.getElementById('migration-modal');
            const diskTargetInput = document.getElementById('migration-disk-target');
            const currentPoolSpan = document.getElementById('migration-current-pool');
            const targetSelect = document.getElementById('migration-target-pool');
            if (!modal || !diskTargetInput || !currentPoolSpan || !targetSelect) {
                console.error('Migration modal elements not found');
                return;
            }
            diskTargetInput.value = diskTarget;
            currentPoolSpan.textContent = currentPool;
            // Update target pool options
            Array.from(targetSelect.options).forEach(option => {
                option.disabled = option.value === currentPool;
                option.textContent = option.value + (option.value === currentPool ? ' (current)' : '');
            });
            modal.style.display = 'block';
        };
        window.closeMigrationModal = function() {
            const modal = document.getElementById('migration-modal');
            if (modal) {
                modal.style.display = 'none';
            }
        };
        
        // Function to immediately show progress when migration starts
        window.showMigrationProgress = function(diskTarget) {
            const progressArea = document.getElementById('migration-progress-' + diskTarget);
            if (progressArea) {
                progressArea.style.display = 'block';
                const statusText = document.getElementById('migration-status-' + diskTarget);
                const progressBar = document.getElementById('migration-bar-' + diskTarget);
                const progressPercent = document.getElementById('migration-percent-' + diskTarget);
                
                if (statusText && progressBar && progressPercent) {
                    const progress = 0;
                    
                    statusText.textContent = 'Starting migration...';
                    progressBar.style.width = progress + '%';
                    progressPercent.textContent = progress + '%';
                }
            }
        };
        
        // Close modal on outside click
        document.addEventListener('DOMContentLoaded', function() {
            const modal = document.getElementById('migration-modal');
            if (modal) {
                modal.addEventListener('click', function(e) {
                    if (e.target === modal) {
                        window.closeMigrationModal();
                    }
                });
                
                // Handle form submission to show immediate progress
                const form = document.getElementById('migration-form');
                if (form) {
                    form.addEventListener('submit', function(e) {
                        const diskTarget = document.getElementById('migration-disk-target').value;
                        if (diskTarget) {
                            // Show progress immediately
                            setTimeout(() => {
                                window.showMigrationProgress(diskTarget);
                            }, 100);
                        }
                        window.closeMigrationModal();
                    });
                }
            }
        });
        </script>
        """
        # Prepend migration modal and script to the body or main template output
        storage_list = migration_modal + storage_list
        # Create template options for disk creation (templates + existing images)
        template_options = ""
        try:
            # Add template files
            if os.path.exists(TEMPLATES_DIR):
                for f in os.listdir(TEMPLATES_DIR):
                    if f.endswith('.qcow2') or f.endswith('.img'):
                        template_options += f"<option value='template:{html.escape(f)}'>[Template] {html.escape(f)}</option>"
        except Exception:
            pass
        
        try:
            # Add existing disk images from libvirt pools
            for pool in lv.list_pools():
                if pool.isActive():
                    for vol in pool.listAllVolumes():
                        vol_name = vol.name()
                        if vol_name.endswith(('.qcow2', '.img', '.raw')):
                            pool_name = pool.name()
                            template_options += f"<option value='existing:{html.escape(pool_name)}:{html.escape(vol_name)}'>[Existing] {html.escape(vol_name)}</option>"
        except Exception:
            pass
        
        # CD/DVD ROMs list
        cdrom_items = []
        for dev, path, bus, is_boot in cdroms:
            cdrom_items.append(f"""
            <div class='card' style='margin: 8px 0; padding: 16px;'>
                <div style='display: flex; justify-content: space-between; align-items: flex-start; gap: 20px;'>
                    <div style='flex: 1;'>
                        <div style='display: flex; align-items: center; gap: 8px; margin-bottom: 8px;'>
                            <span class='badge secondary'>{html.escape(dev)}</span>
                            <span style='color: var(--text-secondary); font-size: 14px;'>CD/DVD-ROM</span>
                            <label style='display: flex; align-items: center; gap: 6px; cursor: pointer; font-size: 14px; color: var(--text-primary); margin-left: 12px;'>
                                <input type='checkbox' name='boot_device' value='{html.escape(dev)}' {'checked' if is_boot else ''} onchange='handleBootDeviceChange(this)' style='margin: 0;'>
                                <span style='color: var(--accent); font-weight: 600;'>🚀 Boot Device</span>
                            </label>
                        </div>
                        <div style='color: var(--text-secondary); font-size: 14px; margin-bottom: 4px;'>
                            💿 {html.escape(path) if path else 'No disc inserted'}
                        </div>
                    </div>
                    
                    <div style='display: flex; gap: 8px;'>
                        <form method='post' style='display: inline;'>
                            <input type='hidden' name='eject_cdrom' value='1'>
                            <input type='hidden' name='cdrom_target' value='{html.escape(dev)}'>
                            <button type='submit' class='button small secondary' {'disabled' if not path else ''}>⏏️ Eject</button>
                        </form>
                        <form method='post' style='display: inline;'>
                            <input type='hidden' name='detach_cdrom' value='1'>
                            <input type='hidden' name='cdrom_target' value='{html.escape(dev)}'>
                            <button type='submit' class='button small danger' onclick='return confirm("Remove CD/DVD drive {html.escape(dev)}?")'>🗑️ Remove</button>
                        </form>
                    </div>
                </div>
            </div>""")
        
        
        # Create CD/DVD attach form with ISO selection
        iso_options = "<option value=''>Select an ISO image...</option>"
        try:
            # List ISO images from all storage pools using the list_iso_images method
            for pool in lv.list_pools():
                try:
                    if pool and pool.isActive():
                        pool_name = pool.name()
                        try:
                            iso_images = self.list_iso_images(pool)
                            for img in sorted(iso_images):
                                iso_options += f"<option value='{html.escape(pool_name)}::{html.escape(img)}'>{html.escape(pool_name)}/{html.escape(img)}</option>"
                        except Exception as e:
                            logger.error(f"Error listing ISO images in pool {pool_name}: {e}")
                except Exception as e:
                    logger.error(f"Error accessing pool {pool.name() if pool else 'unknown'}: {e}")
            
            # Skip system directory scanning to avoid showing [System] entries
        except Exception as e:
            logger.error(f"Error in ISO selection: {e}")
            iso_options += f"<option value='' disabled>Error loading ISO images: {html.escape(str(e))}</option>"
        
        # NICs
        nic_items=[]
        for nic_data in nics:
            if len(nic_data) == 5:
                n, s, m, mac_addr, xml = nic_data
            elif len(nic_data) == 4:
                n, s, m, xml = nic_data
                mac_addr = "Unknown"
            else:
                n, s, m = nic_data
                xml = ""
                mac_addr = "Unknown"
            nic_items.append(f"""
            <div class='card' style='margin: 8px 0; padding: 16px;'>
                <div style='display: flex; justify-content: space-between; align-items: center;'>
                    <div style='flex: 1;'>
                        <div style='display: flex; align-items: center; gap: 8px; margin-bottom: 8px;'>
                            <span class='badge secondary'>{html.escape(n)}</span>
                            <span style='color: var(--text-secondary); font-size: 14px;'>{html.escape(m)} model</span>
                        </div>
                        <div style='color: var(--text-secondary); font-size: 14px;'>
                            🌐 Source: <strong style='color: var(--text);'>{html.escape(s)}</strong>
                        </div>
                        <div style='color: var(--text-secondary); font-size: 14px;'>
                            🔗 MAC: <strong style='color: var(--accent); font-family: monospace;'>{html.escape(mac_addr)}</strong>
                        </div>
                    </div>
                    <div style='margin-left: 16px;'>
                        <form method='post' style='display: inline;'>
                            <input type='hidden' name='detach_nic' value='1'>
                            <input type='hidden' name='nic_target' value='{html.escape(n)}'>
                            <input type='hidden' name='nic_xml' value='{html.escape(xml)}'>
                            <button type='submit' class='button small danger' onclick='return confirm("Remove network interface {html.escape(n)}?")'>🗑️ Remove</button>
                        </form>
                    </div>
                </div>
            </div>""")
        nic_list = ''.join(nic_items) if nic_items else '<div class="card"><p style="color: var(--text-secondary); text-align: center; padding: 20px;">No network interfaces attached</p></div>'
        
        # bridge detection for add NIC
        bridges=[]
        try:
            for iface in os.listdir('/sys/class/net'):
                if os.path.isdir(os.path.join('/sys/class/net',iface,'bridge')):
                    bridges.append(iface)
        except Exception: pass
        bridge_opts=''.join(f"<option value='{html.escape(b)}'>{html.escape(b)}</option>" for b in bridges) or "<option value='virbr0'>virbr0</option>"
        nic_models=['virtio','e1000','e1000e','rtl8139','vmxnet3','ne2k_pci']
        nic_model_opts=''.join(f"<option value='{m}'>{m}</option>" for m in nic_models)
        nic_add_form=f"""
        <div style='margin-top: 16px;'>
            <details>
                <summary style='padding: 12px; background: var(--border); border-radius: 6px; cursor: pointer; font-weight: 600; margin-bottom: 12px;'>➕ Add Network Interface</summary>
                <div class='card'>
                    <form method='post' style='display: grid; grid-template-columns: 1fr 2fr 2fr 1fr auto; gap: 16px; align-items: end;'>
                        <input type='hidden' name='add_nic' value='1'>
                        
                        <div class='form-group'>
                            <label style='display: block; margin-bottom: 4px; font-size: 14px; color: var(--text-secondary);'>Type</label>
                            <select name='nic_type' style='width: 100%; padding: 8px; border: 1px solid var(--border); border-radius: 4px; background: var(--bg-secondary);'>
                                <option value='bridge'>Bridge</option>
                                <option value='network'>Network</option>
                            </select>
                        </div>
                        
                        <div class='form-group'>
                            <label style='display: block; margin-bottom: 4px; font-size: 14px; color: var(--text-secondary);'>Bridge/Network</label>
                            <select name='nic_source' style='width: 100%; padding: 8px; border: 1px solid var(--border); border-radius: 4px; background: var(--bg-secondary);'>
                                {bridge_opts}
                            </select>
                        </div>
                        
                        <div class='form-group'>
                            <label style='display: block; margin-bottom: 4px; font-size: 14px; color: var(--text-secondary);'>MAC Address</label>
                            <input type='text' name='nic_mac' id='nic_mac' style='width: 100%; padding: 8px; border: 1px solid var(--border); border-radius: 4px; background: var(--bg-secondary); color: var(--fg);' placeholder='Auto-generated' title='Format: 00:11:22:33:44:55'>
                        </div>
                        
                        <div class='form-group'>
                            <label style='display: block; margin-bottom: 4px; font-size: 14px; color: var(--text-secondary);'>Model</label>
                            <select name='nic_model' style='width: 100%; padding: 8px; border: 1px solid var(--border); border-radius: 4px; background: var(--bg-secondary);'>
                                {nic_model_opts}
                            </select>
                        </div>
                        
                        <div class='form-group'>
                            <button type='submit' class='button primary' style='padding: 8px 16px; white-space: nowrap;'>
                                ➕ Add Interface
                            </button>
                        </div>
                    </form>
                </div>
            </details>
        </div>"""
        
        # PCI Device Passthrough Section
        free_pci_devices = lv.free_pci_devices()
        attached_pci = []
        
        # Get currently attached PCI devices
        for pci_addr in pci_att:
            # Extract short address (remove 0000: prefix if present)
            short_addr = pci_addr[5:] if pci_addr.startswith('0000:') else pci_addr
            
            # Try to find device info from available devices
            device_info = None
            for dev in free_pci_devices + [{'addr': short_addr, 'description': 'Unknown Device', 'vendor': 'N/A', 'device': 'N/A'}]:
                if dev['addr'] == short_addr:
                    device_info = dev
                    break
            
            if not device_info:
                device_info = {'addr': short_addr, 'description': 'Unknown Device', 'vendor': 'N/A', 'device': 'N/A'}
            
            attached_pci.append(device_info)
        
        # Build PCI section HTML
        pci_section = ""
        
        # Show attached PCI devices
        if attached_pci:
            pci_items = []
            for dev in attached_pci:
                pci_items.append(f"""
                <div class='card' style='margin: 8px 0; padding: 16px;'>
                    <div style='display: flex; justify-content: space-between; align-items: center;'>
                        <div style='flex: 1;'>
                            <div style='display: flex; align-items: center; gap: 8px; margin-bottom: 8px;'>
                                <span class='badge primary'>{html.escape(dev['addr'])}</span>
                                <span style='color: var(--text-secondary); font-size: 14px;'>{html.escape(dev['description'])}</span>
                            </div>
                            <div style='color: var(--text-secondary); font-size: 14px;'>
                                🔧 Vendor: <strong style='color: var(--text);'>{html.escape(dev.get('vendor', 'N/A'))}</strong> | 
                                Device: <strong style='color: var(--text);'>{html.escape(dev.get('device', 'N/A'))}</strong>
                            </div>
                        </div>
                        <div style='margin-left: 16px;'>
                            <form method='post' style='display: inline;'>
                                <input type='hidden' name='detach_pci' value='1'>
                                <input type='hidden' name='pci_detach_addr' value='{html.escape(dev['addr'])}'>
                                <button type='submit' class='button small danger' onclick='return confirm("Remove PCI device {html.escape(dev['addr'])}?")' {'disabled' if status == 'running' else ''}>🗑️ Remove</button>
                            </form>
                        </div>
                    </div>
                </div>""")
            pci_list = ''.join(pci_items)
        else:
            pci_list = '<div class="card"><p style="color: var(--text-secondary); text-align: center; padding: 20px;">No PCI devices attached</p></div>'
        
        # Show available PCI devices for attachment (only when VM is stopped)
        if free_pci_devices and status == 'shutoff':
            pci_options = ""
            for dev in free_pci_devices:
                # Skip devices that are already attached
                if not any(attached['addr'] == dev['addr'] for attached in attached_pci):
                    pci_options += f"<option value='{html.escape(dev['addr'])}'>{html.escape(dev['addr'])} - {html.escape(dev['description'])}</option>"
            
            if pci_options:
                pci_section = f"""
                <div class='hardware-section'>
                    <div class='card'>
                        <h3 style='margin: 0 0 20px 0; display: flex; align-items: center; gap: 10px; color: var(--accent); font-size: 20px; border-bottom: 2px solid var(--border); padding-bottom: 12px;'>
                            <span>🔌</span> PCI Device Passthrough
                        </h3>
                        
                        <div style='margin-bottom: 24px;'>
                            <h4 style='margin: 0 0 12px 0; color: var(--fg); font-size: 16px;'>📎 Attached PCI Devices</h4>
                            {pci_list}
                        </div>
                        
                        <div>
                            <h4 style='margin: 0 0 12px 0; color: var(--fg); font-size: 16px;'>➕ Attach PCI Device</h4>
                            <form method='post' style='display: grid; grid-template-columns: 1fr auto; gap: 12px; align-items: end;'>
                                <input type='hidden' name='attach_pci' value='1'>
                                <div>
                                    <label style='display: block; margin-bottom: 6px; font-size: 14px; color: var(--text-secondary);'>Select PCI Device</label>
                                    <select name='pci_addr' style='width: 100%; padding: 10px; border: 1px solid var(--border); border-radius: 4px; background: var(--bg-secondary); color: var(--fg);'>
                                        <option value=''>-- Select a device --</option>
                                        {pci_options}
                                    </select>
                                </div>
                                <button type='submit' class='button primary' style='padding: 10px 20px; white-space: nowrap;'>🔗 Attach Device</button>
                            </form>
                            <div style='margin-top: 12px; padding: 8px 12px; background: var(--bg-warning); border-radius: 4px; font-size: 13px; color: var(--text-warning);'>
                                ⚠️ PCI passthrough requires VM to be stopped and proper IOMMU configuration
                            </div>
                        </div>
                    </div>
                </div>"""
        elif attached_pci:
            # Show only attached devices when VM is running
            pci_section = f"""
            <div class='hardware-section'>
                <div class='card'>
                    <h3 style='margin: 0 0 20px 0; display: flex; align-items: center; gap: 10px; color: var(--accent); font-size: 20px; border-bottom: 2px solid var(--border); padding-bottom: 12px;'>
                        <span>🔌</span> PCI Device Passthrough
                    </h3>
                    
                    <div style='margin-bottom: 24px;'>
                        <h4 style='margin: 0 0 12px 0; color: var(--fg); font-size: 16px;'>📎 Attached PCI Devices</h4>
                        {pci_list}
                    </div>
                    
                    {'<div style="text-align: center; padding: 20px; background: var(--bg-secondary); border-radius: 6px; color: var(--muted); font-size: 14px;">⏸️ Stop the VM to attach additional PCI devices</div>' if status == 'running' else ''}
                </div>
            </div>"""
        
        # Organize content sections with better layout
        sections = []
        
        # VM Status and Actions section at the top
        status_badge_class = {
            'running': 'running',
            'shutoff': 'shutoff', 
            'paused': 'paused'
        }.get(status, 'shutoff')
        
        sections.append(f"""
        <div class='vm-header-section'>
            <div class='card' style='background: linear-gradient(135deg, var(--card) 0%, var(--bg) 100%); border-left: 4px solid var(--accent); margin-bottom: 24px;'>
                <div style='display: flex; justify-content: space-between; align-items: flex-start; margin-bottom: 16px;'>
                    <div style='flex: 1;'>
                        <h1 style='margin: 0 0 12px 0; display: flex; align-items: center; gap: 12px; font-size: 28px;'>
                            🖥️ {html.escape(name)}
                            <span class='badge {status_badge_class}'>{status.title()}</span>
                        </h1>
                        <div style='display: grid; grid-template-columns: repeat(auto-fit, minmax(160px, 1fr)); gap: 20px; color: var(--muted); font-size: 15px; margin-top: 16px;'>
                            <div style='display: flex; align-items: center; gap: 8px;'>
                                <span style='color: var(--accent);'>⚡</span>
                                <span><strong>CPU:</strong> {vcpu_display} vCPUs</span>
                            </div>
                            <div style='display: flex; align-items: center; gap: 8px;'>
                                <span style='color: var(--accent);'>🧠</span>
                                <span><strong>Memory:</strong> {mem_display} MiB</span>
                            </div>
                            <div style='display: flex; align-items: center; gap: 8px;'>
                                <span style='color: var(--accent);'>🔄</span>
                                <span><strong>Autostart:</strong> {'Yes' if auto else 'No'}</span>
                            </div>
                            <div style='display: flex; align-items: center; gap: 8px;'>
                                <span style='color: var(--accent);'>🆔</span>
                                <span><strong>UUID:</strong> {vm_uuid[:8]}...</span>
                            </div>
                        </div>
                    </div>
                </div>
                <div class='action-buttons' style='display: flex; gap: 10px; flex-wrap: wrap; padding-top: 16px; border-top: 1px solid var(--border);'>
                    {' '.join(actions)}
                    <a class='button secondary' href='/'>← Back to Dashboard</a>
                </div>
            </div>
        </div>
        """)
        
        # Configuration and Hardware sections in organized layout
        sections.append(f"""
        <div class='vm-content-grid' style='display: grid; grid-template-columns: 1fr; gap: 24px;'>
            
            <!-- CPU & Memory Configuration -->
            <div class='config-section'>
                <div class='card'>
                    <h3 style='margin: 0 0 20px 0; display: flex; align-items: center; gap: 10px; color: var(--accent); font-size: 20px; border-bottom: 2px solid var(--border); padding-bottom: 12px;'>
                        <span>⚡</span> CPU & Memory Configuration
                    </h3>
                    {cpu_mem_form}
                </div>
            </div>
            
            <!-- Storage Management & Console -->
            <div class='storage-console-section' style='display: grid; grid-template-columns: 2fr 1fr; gap: 24px;'>
                
                <!-- Virtual Disks -->
                <div class='card'>
                    <!-- Storage Devices -->
                    <div style='margin-bottom: 16px;'>
                        {storage_list}
                    </div>
                    
                    <!-- Add Storage Devices -->
                    <div style='display: grid; grid-template-columns: 1fr 1fr; gap: 12px;'>
                        <!-- Add New Disk -->
                        <details>
                            <summary style='padding: 10px; background: var(--border); border-radius: 6px; cursor: pointer; font-weight: 600; margin-bottom: 8px; font-size: 14px;'>💾 Add Disk</summary>
                            <div style='background: var(--bg); border: 1px solid var(--border); border-radius: 6px; padding: 10px; margin-top: 4px;'>
                                <form method='post' style='display: grid; gap: 10px;'>
                                    <input type='hidden' name='attach_disk' value='1'>
                                    
                                    <div style='display: grid; grid-template-columns: 1fr 1fr; gap: 8px;'>
                                        <div>
                                            <label style='display: block; margin-bottom: 4px; font-size: 12px; font-weight: 500; color: var(--fg);'>Size (GB)</label>
                                            <input name='disk_size_gb' type='number' value='20' placeholder='20' style='width: 100%; padding: 6px; border: 1px solid var(--border); border-radius: 4px; background: var(--card); color: var(--fg); font-size: 12px;'>
                                        </div>
                                        <div>
                                            <label style='display: block; margin-bottom: 4px; font-size: 12px; font-weight: 500; color: var(--fg);'>Bus</label>
                                            <select name='bus' style='width: 100%; padding: 6px; border: 1px solid var(--border); border-radius: 4px; background: var(--card); color: var(--fg); font-size: 12px;'>
                                                <option value='virtio'>VirtIO</option>
                                                <option value='scsi'>SCSI</option>
                                                <option value='sata'>SATA</option>
                                            </select>
                                        </div>
                                    </div>
                                    
                                    <div>
                                        <label style='display: block; margin-bottom: 4px; font-size: 12px; font-weight: 500; color: var(--fg);'>Template</label>
                                        <select name='template_disk' style='width: 100%; padding: 6px; border: 1px solid var(--border); border-radius: 4px; background: var(--card); color: var(--fg); font-size: 12px;'>
                                            <option value=''>Create blank disk</option>
                                            {template_options}
                                        </select>
                                    </div>
                                    
                                    <button type='submit' class='button primary small' style='padding: 6px 12px; font-size: 12px;'>
                                        ➕ Add Disk
                                    </button>
                                </form>
                            </div>
                        </details>
                        
                        <!-- Add CD/DVD Drive -->
                        <details>
                            <summary style='padding: 10px; background: var(--border); border-radius: 6px; cursor: pointer; font-weight: 600; margin-bottom: 8px; font-size: 14px;'>💿 Add CD/DVD</summary>
                            <div style='background: var(--bg); border: 1px solid var(--border); border-radius: 6px; padding: 10px; margin-top: 4px;'>
                                <form method='post' style='display: grid; gap: 10px;'>
                                    <input type='hidden' name='attach_cdrom' value='1'>
                                    
                                    <div>
                                        <label style='display: block; margin-bottom: 4px; font-size: 12px; font-weight: 500; color: var(--fg);'>ISO Image</label>
                                        <select name='cdrom_iso' style='width: 100%; padding: 6px; border: 1px solid var(--border); border-radius: 4px; background: var(--card); color: var(--fg); font-size: 12px;' required>
                                            {iso_options}
                                        </select>
                                    </div>
                                    
                                    <button type='submit' class='button primary small' style='padding: 6px 12px; font-size: 12px;'>
                                        💿 Add CD/DVD
                                    </button>
                                </form>
                            </div>
                        </details>
                    </div>
                </div>
                
                <!-- Console Preview -->
                <div class='card'>
                    <h3 style='margin: 0 0 20px 0; display: flex; align-items: center; gap: 10px; color: var(--accent); font-size: 20px; border-bottom: 2px solid var(--border); padding-bottom: 12px;'>
                        <span>🖥️</span> Console
                    </h3>
                    {console_html}
                </div>
            </div>
            
            <!-- Snapshot Management -->
            <div class='snapshot-section'>
                <div class='card'>
                    <h3 style='margin: 0 0 20px 0; display: flex; align-items: center; gap: 10px; color: var(--accent); font-size: 20px; border-bottom: 2px solid var(--border); padding-bottom: 12px;'>
                        <span>📸</span> Snapshots
                    </h3>
                    
                    <div style='margin-bottom: 20px;'>
                        <!-- Create New Snapshot -->
                        <div style='background: var(--bg); border: 1px solid var(--border); border-radius: 6px; padding: 16px; margin-bottom: 20px;'>
                            <h4 style='margin: 0 0 12px 0; color: var(--fg); font-size: 16px;'>Create New Snapshot</h4>
                            <div style='display: flex; gap: 12px; align-items: end;'>
                                <div class='form-group' style='flex: 1;'>
                                    <label style='display: block; margin-bottom: 6px; font-size: 14px; font-weight: 500; color: var(--fg);'>Snapshot Name</label>
                                    <input id='snapshot-name-input' type='text' placeholder='Leave empty for auto-generated name' style='width: 100%; padding: 10px; border: 1px solid var(--border); border-radius: 6px; background: var(--card); color: var(--fg);'>
                                </div>
                                <div class='form-group' style='flex: 2;'>
                                    <label style='display: block; margin-bottom: 6px; font-size: 14px; font-weight: 500; color: var(--fg);'>Description</label>
                                    <input id='snapshot-desc-input' type='text' placeholder='Optional description' style='width: 100%; padding: 10px; border: 1px solid var(--border); border-radius: 6px; background: var(--card); color: var(--fg);'>
                                </div>
                                <div class='form-group'>
                                    <button type='button' onclick='createSnapshot("{html.escape(name)}")' class='button primary' style='padding: 10px 16px; font-weight: 600;'>
                                        📸 Create Snapshot
                                    </button>
                                </div>
                            </div>
                        </div>
                        
                        <!-- Existing Snapshots List -->
                        <div id='snapshots-list'>
                            {snapshot_list_html}
                        </div>
                    </div>
                </div>
            </div>
            
            <!-- Network & Media -->
            <div class='network-media-section' style='display: grid; grid-template-columns: 1fr 1fr; gap: 24px;'>
                
                <!-- Network Interfaces -->
                <div class='card'>
                    <h3 style='margin: 0 0 20px 0; display: flex; align-items: center; gap: 10px; color: var(--accent); font-size: 20px; border-bottom: 2px solid var(--border); padding-bottom: 12px;'>
                        <span>🌐</span> Network
                    </h3>
                    
                    <div style='margin-bottom: 20px;'>
                        <h4 style='margin: 0 0 12px 0; color: var(--fg); font-size: 16px;'>Network Interfaces</h4>
                        {nic_list}
                    </div>
                    
                    <details>
                        <summary style='padding: 10px; background: var(--border); border-radius: 6px; cursor: pointer; font-weight: 600; margin-bottom: 12px;'>➕ Add Network Interface</summary>
                        <div style='background: var(--bg); border: 1px solid var(--border); border-radius: 6px; padding: 12px; margin-top: 8px;'>
                            <form method='post' style='display: grid; gap: 12px;'>
                                <input type='hidden' name='add_nic' value='1'>
                                
                                <div style='display: grid; grid-template-columns: 1fr 1fr; gap: 12px;'>
                                    <div class='form-group'>
                                        <label style='display: block; margin-bottom: 4px; font-size: 13px; font-weight: 500; color: var(--fg);'>Type</label>
                                        <select name='nic_type' style='width: 100%; padding: 8px; border: 1px solid var(--border); border-radius: 4px; background: var(--card); color: var(--fg); font-size: 13px;'>
                                            <option value='bridge'>Bridge</option>
                                            <option value='network'>Network</option>
                                        </select>
                                    </div>
                                    
                                    <div class='form-group'>
                                        <label style='display: block; margin-bottom: 4px; font-size: 13px; font-weight: 500; color: var(--fg);'>Model</label>
                                        <select name='nic_model' style='width: 100%; padding: 8px; border: 1px solid var(--border); border-radius: 4px; background: var(--card); color: var(--fg); font-size: 13px;'>
                                            {nic_model_opts}
                                        </select>
                                    </div>
                                </div>
                                
                                <div class='form-group'>
                                    <label style='display: block; margin-bottom: 4px; font-size: 13px; font-weight: 500; color: var(--fg);'>Bridge/Network</label>
                                    <select name='nic_source' style='width: 100%; padding: 8px; border: 1px solid var(--border); border-radius: 4px; background: var(--card); color: var(--fg); font-size: 13px;'>
                                        {bridge_opts}
                                    </select>
                                </div>
                                
                                <div class='form-group'>
                                    <label style='display: block; margin-bottom: 4px; font-size: 13px; font-weight: 500; color: var(--fg);'>MAC Address</label>
                                    <input type='text' name='nic_mac' id='nic_mac_mobile' style='width: 100%; padding: 8px; border: 1px solid var(--border); border-radius: 4px; background: var(--card); color: var(--fg); font-size: 13px;' placeholder='Auto-generated' title='Format: 00:11:22:33:44:55'>
                                </div>
                                
                                <button type='submit' class='button primary small' style='justify-self: start; padding: 8px 16px;'>
                                    ➕ Add Interface
                                </button>
                            </form>
                        </div>
                    </details>
                </div>
                
            </div>
        </div>
        """)
        
        
        # Add PCI section to content if it exists
        if pci_section:
            sections.append(pci_section)
        
        # Graphics Management Section
        graphics_section = ""
        if graphics_devices or video_devices or status == 'shutoff':
            graphics_items = []
            
            # Show graphics adapters
            for gfx in graphics_devices:
                graphics_items.append(f"""
                <div class='card' style='margin: 8px 0; padding: 16px;'>
                    <div style='display: flex; justify-content: space-between; align-items: center;'>
                        <div style='flex: 1;'>
                            <div style='display: flex; align-items: center; gap: 8px; margin-bottom: 8px;'>
                                <span class='badge secondary'>{html.escape(gfx['type'].upper())}</span>
                                <span style='color: var(--text-secondary); font-size: 14px;'>Graphics Adapter</span>
                            </div>
                            <div style='color: var(--text-secondary); font-size: 14px;'>
                                🖥️ Port: <strong style='color: var(--text);'>{html.escape(gfx['port'])}</strong> | 
                                Listen: <strong style='color: var(--text);'>{html.escape(gfx['listen'])}</strong>
                            </div>
                        </div>
                        <div style='margin-left: 16px;'>
                            <form method='post' style='display: inline;'>
                                <input type='hidden' name='remove_graphics' value='1'>
                                <input type='hidden' name='remove_graphics_type' value='{html.escape(gfx['type'])}'>
                                <button type='submit' class='button small danger' onclick='return confirm("Remove {html.escape(gfx['type'])} graphics adapter?")' {'disabled' if status == 'running' else ''}>🗑️ Remove</button>
                            </form>
                        </div>
                    </div>
                </div>""")
            
            # Show video adapters
            for video in video_devices:
                graphics_items.append(f"""
                <div class='card' style='margin: 8px 0; padding: 16px;'>
                    <div style='display: flex; justify-content: space-between; align-items: center;'>
                        <div style='flex: 1;'>
                            <div style='display: flex; align-items: center; gap: 8px; margin-bottom: 8px;'>
                                <span class='badge primary'>{html.escape(video['type'].upper())}</span>
                                <span style='color: var(--text-secondary); font-size: 14px;'>Video Adapter</span>
                            </div>
                            <div style='color: var(--text-secondary); font-size: 14px;'>
                                💾 VRAM: <strong style='color: var(--text);'>{html.escape(video['vram'])} KB</strong>
                            </div>
                        </div>
                        <div style='margin-left: 16px;'>
                            <form method='post' style='display: inline;'>
                                <input type='hidden' name='remove_video' value='1'>
                                <input type='hidden' name='remove_video_type' value='{html.escape(video['type'])}'>
                                <button type='submit' class='button small danger' onclick='return confirm("Remove {html.escape(video['type'])} video adapter?")' {'disabled' if status == 'running' else ''}>🗑️ Remove</button>
                            </form>
                        </div>
                    </div>
                </div>""")
            
            graphics_list = ''.join(graphics_items) if graphics_items else '<div class="card"><p style="color: var(--text-secondary); text-align: center; padding: 20px;">No graphics/video adapters attached</p></div>'
            
            # Show add forms when VM is stopped
            add_forms = ""
            if status == 'shutoff':
                add_forms = f"""
                <div style='display: grid; grid-template-columns: 1fr 1fr; gap: 16px; margin-top: 16px;'>
                    <div>
                        <h4 style='margin: 0 0 12px 0; color: var(--fg); font-size: 16px;'>➕ Add Graphics Adapter</h4>
                        <form method='post' style='display: grid; gap: 12px;'>
                            <input type='hidden' name='add_graphics' value='1'>
                            <select name='graphics_type' style='width: 100%; padding: 8px; border: 1px solid var(--border); border-radius: 4px; background: var(--bg-secondary); color: var(--fg);'>
                                <option value='vnc'>VNC</option>
                                <option value='spice'>SPICE</option>
                            </select>
                            <button type='submit' class='button primary' style='padding: 8px 16px;'>🖥️ Add Graphics</button>
                        </form>
                    </div>
                    <div>
                        <h4 style='margin: 0 0 12px 0; color: var(--fg); font-size: 16px;'>➕ Add Video Adapter</h4>
                        <form method='post' style='display: grid; gap: 12px;'>
                            <input type='hidden' name='add_video' value='1'>
                            <div style='display: grid; grid-template-columns: 2fr 1fr; gap: 8px;'>
                                <select name='video_type' style='padding: 8px; border: 1px solid var(--border); border-radius: 4px; background: var(--bg-secondary); color: var(--fg);'>
                                    <option value='qxl'>QXL</option>
                                    <option value='cirrus'>Cirrus</option>
                                    <option value='vga'>VGA</option>
                                    <option value='vmvga'>VMware VGA</option>
                                    <option value='virtio'>VirtIO GPU</option>
                                </select>
                                <input name='video_vram' type='number' value='16384' placeholder='VRAM KB' style='padding: 8px; border: 1px solid var(--border); border-radius: 4px; background: var(--bg-secondary); color: var(--fg);'>
                            </div>
                            <button type='submit' class='button primary' style='padding: 8px 16px;'>📺 Add Video</button>
                        </form>
                    </div>
                </div>"""
            elif status == 'running':
                add_forms = '<div style="text-align: center; padding: 20px; background: var(--bg-secondary); border-radius: 6px; color: var(--muted); font-size: 14px;">⏸️ Stop the VM to add/remove graphics adapters</div>'
            
            graphics_section = f"""
            <div class='hardware-section'>
                <div class='card'>
                    <h3 style='margin: 0 0 20px 0; display: flex; align-items: center; gap: 10px; color: var(--accent); font-size: 20px; border-bottom: 2px solid var(--border); padding-bottom: 12px;'>
                        <span>🖥️</span> Graphics & Video Adapters
                    </h3>
                    
                    <div style='margin-bottom: 24px;'>
                        <h4 style='margin: 0 0 12px 0; color: var(--fg); font-size: 16px;'>📺 Current Adapters</h4>
                        {graphics_list}
                    </div>
                    
                    {add_forms}
                </div>
            </div>"""
        
        # Add graphics section to content
        if graphics_section:
            sections.append(graphics_section)
        
        content = sections
        
        # Create layout with embedded console for running VMs  
        main_content = f"<div style='margin-bottom: 24px;'>{msg}{''.join(content)}</div>"

        # Add JavaScript for console functionality
        console_js = f"""
        <script>
        let consoleState = 'small'; // small, expanded
        let vncConnection = null;
        let isConsoleActive = false;
        let previewConnection = null;
        
        function toggleConsole() {{
            console.log('toggleConsole called, current state:', consoleState);
            
            if (consoleState === 'small') {{
                console.log('Expanding console...');
                createExpandedConsole();
                consoleState = 'expanded';
                startFullVNC();
            }} else {{
                console.log('Minimizing console...');
                removeExpandedConsole();
                consoleState = 'small';
                stopFullVNC();
                startPreview();
            }}
        }}
        
        function createExpandedConsole() {{
            removeExpandedConsole();
            
            const overlay = document.createElement('div');
            overlay.id = 'console-expanded';
            overlay.innerHTML = `
                <div class="console-header">
                    <span>🖥️ Console - {html.escape(name)}</span>
                    <span onclick="toggleConsole()" style="cursor: pointer; padding: 5px;">✕ Close</span>
                </div>
                <canvas id="console-vnc-expanded" width="1024" height="768" style="width:100%;height:calc(100% - 60px);background:#000;border:1px solid var(--border);border-radius:4px;"></canvas>
            `;
            document.body.appendChild(overlay);
            overlay.style.display = 'block';
            
            overlay.addEventListener('click', function(e) {{
                if (e.target === overlay) {{
                    toggleConsole();
                }}
            }});
        }}
        
        function removeExpandedConsole() {{
            const expanded = document.getElementById('console-expanded');
            if (expanded) {{
                expanded.remove();
            }}
        }}
        
        function startPreview() {{
            console.log('Starting preview...');
            if (previewConnection) return;
            
            const canvas = document.getElementById('console-vnc');
            if (!canvas) return;
            
            isConsoleActive = true;
            
            try {{
                previewConnection = new WebSocket(`ws${{location.protocol === 'https:' ? 's' : ''}}://${{location.host}}/vnc_ws/{html.escape(name)}`);
                
                previewConnection.onopen = function() {{
                    console.log('Preview WebSocket connected');
                }};
                
                previewConnection.onmessage = function(event) {{
                    if (event.data instanceof Blob) {{
                        const img = new Image();
                        img.onload = function() {{
                            const ctx = canvas.getContext('2d');
                            ctx.clearRect(0, 0, canvas.width, canvas.height);
                            ctx.drawImage(img, 0, 0, canvas.width, canvas.height);
                        }};
                        img.src = URL.createObjectURL(event.data);
                    }}
                }};
                
                previewConnection.onerror = function(error) {{
                    console.log('Preview WebSocket error:', error);
                }};
                
                previewConnection.onclose = function() {{
                    console.log('Preview WebSocket closed');
                    previewConnection = null;
                }};
            }} catch (error) {{
                console.log('Failed to start preview:', error);
            }}
        }}
        
        function stopPreview() {{
            console.log('Stopping preview...');
            if (previewConnection) {{
                previewConnection.close();
                previewConnection = null;
            }}
        }}
        
        function startFullVNC() {{
            console.log('Starting full VNC...');
            const canvas = document.getElementById('console-vnc-expanded');
            if (!canvas) return;
            
            try {{
                vncConnection = new WebSocket(`ws${{location.protocol === 'https:' ? 's' : ''}}://${{location.host}}/vnc_ws/{html.escape(name)}`);
                
                vncConnection.onopen = function() {{
                    console.log('Full VNC WebSocket connected');
                }};
                
                canvas.addEventListener('keydown', handleKeyDown);
                canvas.addEventListener('mousedown', handleMouseDown);
                canvas.addEventListener('mousemove', handleMouseMove);
                canvas.addEventListener('mouseup', handleMouseUp);
                canvas.focus();
            }} catch (error) {{
                console.log('Failed to start full VNC:', error);
            }}
        }}
        
        function stopFullVNC() {{
            console.log('Stopping full VNC...');
            if (vncConnection) {{
                vncConnection.close();
                vncConnection = null;
            }}
            
            const canvas = document.getElementById('console-vnc-expanded');
            if (canvas) {{
                canvas.removeEventListener('keydown', handleKeyDown);
                canvas.removeEventListener('mousedown', handleMouseDown);
                canvas.removeEventListener('mousemove', handleMouseMove);
                canvas.removeEventListener('mouseup', handleMouseUp);
            }}
        }}
        
        function handleKeyDown(event) {{
            event.preventDefault();
            if (vncConnection && vncConnection.readyState === WebSocket.OPEN) {{
                // Send key events to VNC
            }}
        }}
        
        function handleMouseDown(event) {{
            event.preventDefault();
            // Send mouse events to VNC
        }}
        
        function handleMouseMove(event) {{
            // Send mouse move events to VNC
        }}
        
        function handleMouseUp(event) {{
            event.preventDefault();
            // Send mouse up events to VNC
        }}
        
        function sendCtrlAltDel() {{
            console.log('Sending Ctrl+Alt+Del');
            if (vncConnection && vncConnection.readyState === WebSocket.OPEN) {{
                // Send Ctrl+Alt+Del sequence
            }}
        }}
        
        // Auto-start preview when page loads
        document.addEventListener('DOMContentLoaded', function() {{
            if (isConsoleActive) {{
                setTimeout(startPreview, 1000);
            }}
        }});
        
        // Cleanup on page unload
        window.addEventListener('beforeunload', function() {{
            stopPreview();
            stopFullVNC();
        }});
        
        console.log('Console JavaScript loaded for VM: {html.escape(name)}');
        
        // Snapshot management functions
        function createSnapshot(vmName) {{
            const nameInput = document.getElementById('snapshot-name-input');
            const descInput = document.getElementById('snapshot-desc-input');
            
            let snapName = nameInput.value.trim();
            if (!snapName) {{
                // Auto-generate snapshot name: vmname-YYYYMMDD-HHMMSS
                const now = new Date();
                const timestamp = now.getFullYear() + 
                    String(now.getMonth() + 1).padStart(2, '0') + 
                    String(now.getDate()).padStart(2, '0') + '-' +
                    String(now.getHours()).padStart(2, '0') + 
                    String(now.getMinutes()).padStart(2, '0') + 
                    String(now.getSeconds()).padStart(2, '0');
                snapName = vmName + '-' + timestamp;
            }}
            
            const params = new URLSearchParams();
            params.append('domain', vmName);
            params.append('snap_name', snapName);
            
            fetch('/api/snapshot/create', {{
                method: 'POST',
                headers: {{'Content-Type': 'application/x-www-form-urlencoded'}},
                body: params.toString()
            }}).then(response => response.json()).then(data => {{
                if (data.status === 'success') {{
                    // Clear inputs and refresh page
                    nameInput.value = '';
                    descInput.value = '';
                    window.location.reload();
                }} else {{
                    alert('Snapshot creation failed: ' + (data.message || 'Unknown error'));
                }}
            }}).catch(error => {{
                alert('Network error. Please try again.');
            }});
        }}
        
        function restoreSnapshot(vmName, snapName) {{
            if (!confirm(`Restore snapshot "${{snapName}}"? This will revert the VM to this snapshot state.`)) {{
                return;
            }}
            
            const params = new URLSearchParams();
            params.append('domain', vmName);
            params.append('snap_name', snapName);
            
            fetch('/api/snapshot/restore', {{
                method: 'POST',
                headers: {{'Content-Type': 'application/x-www-form-urlencoded'}},
                body: params.toString()
            }}).then(response => response.json()).then(data => {{
                if (data.status === 'success') {{
                    alert('Snapshot restored successfully!');
                    window.location.reload();
                }} else {{
                    alert('Snapshot restore failed: ' + (data.message || 'Unknown error'));
                }}
            }}).catch(error => {{
                alert('Network error. Please try again.');
            }});
        }}
        
        function deleteSnapshot(vmName, snapName) {{
            if (!confirm(`Delete snapshot "${{snapName}}"? This action cannot be undone.`)) {{
                return;
            }}
            
            const params = new URLSearchParams();
            params.append('domain', vmName);
            params.append('snap_name', snapName);
            
            fetch('/api/snapshot/delete', {{
                method: 'POST',
                headers: {{'Content-Type': 'application/x-www-form-urlencoded'}},
                body: params.toString()
            }}).then(response => response.json()).then(data => {{
                if (data.status === 'success') {{
                    window.location.reload();
                }} else {{
                    alert('Snapshot deletion failed: ' + (data.message || 'Unknown error'));
                }}
            }}).catch(error => {{
                alert('Network error. Please try again.');
            }});
        }}
        
        // Handle boot device selection - only allow one device to be selected
        function handleBootDeviceChange(checkbox) {{
            console.log('DEBUG: Boot device checkbox clicked:', checkbox.value, 'checked:', checkbox.checked);
            
            // Check if checkbox is disabled (VM running)
            if (checkbox.disabled) {{
                checkbox.checked = !checkbox.checked; // Revert the change
                alert('Cannot change boot device while VM is running. Please shut down the VM first.');
                return;
            }}
            
            // Uncheck all other boot device checkboxes
            const allBootCheckboxes = document.querySelectorAll('input[name="boot_device"]');
            allBootCheckboxes.forEach(cb => {{
                if (cb !== checkbox) {{
                    cb.checked = false;
                }}
            }});
            
            // If unchecking, just return
            if (!checkbox.checked) {{
                console.log('DEBUG: Checkbox unchecked, returning');
                return;
            }}
            
            console.log('DEBUG: Sending POST request for boot device:', checkbox.value);
            
            // Show loading state
            const originalText = checkbox.nextElementSibling.textContent;
            checkbox.nextElementSibling.textContent = 'Updating...';
            checkbox.disabled = true;
            
            // Send the boot device change to the server
            const formData = new FormData();
            formData.append('set_boot_device', '1');
            formData.append('boot_device', checkbox.value);
            
            fetch(window.location.href, {{
                method: 'POST',
                body: formData
            }})
            .then(response => {{
                console.log('DEBUG: Response status:', response.status);
                return response.text();
            }})
            .then(responseText => {{
                console.log('DEBUG: Response contains success:', responseText.includes('inline-note success'));
                console.log('DEBUG: Response contains error:', responseText.includes('inline-note error'));
                
                // Check if the response contains success or error messages
                if (responseText.includes('inline-note success')) {{
                    console.log('DEBUG: Success detected, reloading page');
                    // Success - reload the page
                    window.location.reload();
                }} else if (responseText.includes('inline-note error')) {{
                    // Extract error message
                    const errorMatch = responseText.match(/<div class='inline-note error'>([^<]+)<\/div>/);
                    const errorMsg = errorMatch ? errorMatch[1] : 'Failed to set boot device';
                    
                    console.log('DEBUG: Error detected:', errorMsg);
                    
                    // Revert UI changes and show error
                    checkbox.checked = false;
                    checkbox.nextElementSibling.textContent = originalText;
                    checkbox.disabled = false;
                    alert(errorMsg);
                }} else {{
                    console.log('DEBUG: No clear success/error indication, reloading anyway');
                    // No clear success/error indication - reload anyway
                    window.location.reload();
                }}
            }})
            .catch(error => {{
                console.error('DEBUG: Network error:', error);
                // Revert UI changes on error
                checkbox.checked = false;
                checkbox.nextElementSibling.textContent = originalText;
                checkbox.disabled = false;
                alert('Network error. Please try again.');
            }});
        }}
        
        // Storage device action functions
        function resizeDisk(device, newSize) {{
            if (!newSize || newSize <= 0) {{
                alert('Please enter a valid size');
                return;
            }}
            const form = document.createElement('form');
            form.method = 'post';
            form.innerHTML = `<input name="resize_disk" value="1"><input name="disk_target" value="${{device}}"><input name="new_size_gb" value="${{newSize}}">`;
            document.body.appendChild(form);
            form.submit();
        }}
        
        function changeDiskBus(device, newBus) {{
            const form = document.createElement('form');
            form.method = 'post';
            form.innerHTML = `<input name="change_disk_bus" value="1"><input name="disk_target" value="${{device}}"><input name="new_bus" value="${{newBus}}">`;
            document.body.appendChild(form);
            form.submit();
        }}
        
        function deleteDisk(device) {{
            const form = document.createElement('form');
            form.method = 'post';
            form.innerHTML = `<input name="detach_disk" value="1"><input name="target" value="${{device}}">`;
            document.body.appendChild(form);
            form.submit();
        }}
        
        function ejectCdrom(device) {{
            const form = document.createElement('form');
            form.method = 'post';
            form.innerHTML = `<input name="eject_cdrom" value="1"><input name="cdrom_target" value="${{device}}">`;
            document.body.appendChild(form);
            form.submit();
        }}
        
        function removeCdrom(device) {{
            const form = document.createElement('form');
            form.method = 'post';
            form.innerHTML = `<input name="detach_cdrom" value="1"><input name="cdrom_target" value="${{device}}">`;
            document.body.appendChild(form);
            form.submit();
        }}
        
        </script>
        """

        return f"""
        <div class="vm-layout">
            <div class="vm-main" style="width: 100%;">{main_content}</div>
        </div>
        {console_js}
        """

    def vnc_block(self, root, name):
        g=root.find('.//devices/graphics')
        if g is not None and g.get('type')=='vnc':
            port=g.get('port','-1'); listen=g.get('listen','127.0.0.1')
            if port and port!='-1':
                return f"<p>VNC: {html.escape(listen)}:{port} <a class='small' href='vnc://{listen}:{port}'>Open</a><br><img id='console_img' style='max-width:100%;border:1px solid #333;background:#000'><br><button type='button' class='small secondary' onclick=\"startConsole('{html.escape(name)}')\">Start Inline</button> <button type='button' class='small secondary' onclick='stopConsole()'>Stop</button><br><span class='inline-note'>Inline viewer = screenshots.</span></p>"
            return '<p>VNC auto port (-1). Start VM.</p>'
        return '<p>No VNC graphics.</p>'
    def page_create(self, lv:LV, form):
        msg=""
        if form and 'create_vm' in form:
            try:
                name=form.get('name',[''])[0]; mem=parse_int(form.get('memory_mb',['2048'])[0],2048); vcpus=parse_int(form.get('vcpus',['2'])[0],2); disk_gb=parse_int(form.get('disk_gb',['20'])[0],20); add_disk_gb=parse_int(form.get('extra_disk_gb',['0'])[0],0); clone_src=form.get('clone_src',[''])[0].strip(); pool=lv.get_pool(form.get('pool',[''])[0]); bridge=form.get('bridge',['virbr0'])[0]; nic_model=form.get('nic_model',['virtio'])[0]; os_type=form.get('os_type',['linux'])[0]; boot_order=form.get('boot_order',['hd,cdrom,network'])[0]
                # Determine pool path
                import xml.etree.ElementTree as ET
                pxml=pool.XMLDesc(0); proot=ET.fromstring(pxml); pool_path=proot.findtext('.//target/path') or '/var/lib/libvirt/images'
                base_name=f"{name}.qcow2"; base_path=os.path.join(pool_path, base_name)
                if clone_src:
                    # If clone_src matches imported image file in images dir use it; else treat as volume
                    img_path=os.path.join(pool_path,'images',clone_src)
                    if os.path.exists(img_path):
                        # Copy template and resize
                        cmd = ['cp', '--reflink=always', img_path, base_path]
                        subprocess.run(cmd, check=True, capture_output=True, timeout=30)
                        # Always resize to match requested size (unless 0 = keep template size)
                        if disk_gb > 0:
                            resize_cmd = ['qemu-img', 'resize', base_path, f'{disk_gb}G']
                            subprocess.run(resize_cmd, check=True, capture_output=True, timeout=30)
                        attach_immediately = True
                    else:
                        raise FileNotFoundError(f"Template not found: {clone_src}")
                else:
                    # Create new disk
                    vol_xml = f"<volume><name>{base_name}</name><capacity unit='GB'>{disk_gb}</capacity><target><format type='qcow2'/></target></volume>"; pool.createXML(vol_xml, 0)
                    path = pool.storageVolLookupByName(base_name).path()
                
                # Generate VM XML with OS-specific features
                features_xml = '<features><acpi/><apic/>'
                if os_type == 'windows':
                    # Add Hyper-V enlightenments for Windows
                    features_xml += '''
                    <hyperv>
                        <relaxed state='on'/>
                        <vapic state='on'/>
                        <spinlocks state='on' retries='8191'/>
                    </hyperv>
                    <kvm>
                        <hidden state='on'/>
                    </kvm>'''
                features_xml += '</features>'
                
                # Generate disk XML with boot order
                disk_xml = f"<disk type='file' device='disk'><driver name='qemu' type='qcow2'/><source file='{path}'/><target dev='vda' bus='virtio'/><boot order='1'/></disk>"
                
                dom=f"""<domain type='kvm'><name>{name}</name><memory unit='MiB'>{mem}</memory><currentMemory unit='MiB'>{mem}</currentMemory><vcpu>{vcpus}</vcpu><os><type arch='x86_64' machine='pc'>hvm</type></os>{features_xml}<cpu mode='host-model'/><devices><emulator>/usr/libexec/qemu-kvm</emulator>{disk_xml}<interface type='bridge'><source bridge='{bridge}'/><model type='{nic_model}'/></interface><graphics type='vnc' port='-1' listen='127.0.0.1'/><console type='pty'/></devices></domain>"""
                lv.conn.defineXML(dom); msg=f"<div class='inline-note'>Domain {html.escape(name)} created.</div>"
                if add_disk_gb>0:
                    extra_name=f"{name}-extra.qcow2"; vol_xml=f"<volume><name>{extra_name}</name><capacity unit='GB'>{add_disk_gb}</capacity><target><format type='qcow2'/></target></volume>"; pool.createXML(vol_xml,0)
                    msg += "<div class='inline-note'>Extra disk created (not yet attached, use domain page to attach).</div>"
            except Exception as e: msg=f"<div class='inline-note'>{html.escape(str(e))}</div>"
        pool_opts=''.join(f"<option>{html.escape(p.name())}</option>" for p in lv.list_pools())
        # for clone dropdown: show imported images (.qcow2) in selected pool
        selected_pool=form.get('pool',[lv.list_pools()[0].name() if lv.list_pools() else ''])[0] if form else (lv.list_pools()[0].name() if lv.list_pools() else '')
        imported=[]
        try:
            if selected_pool:
                p=lv.get_pool(selected_pool)
                import xml.etree.ElementTree as ET
                pxml=p.XMLDesc(0); proot=ET.fromstring(pxml); pool_path=proot.findtext('.//target/path') or ''
                idir=os.path.join(pool_path,'images')
                if os.path.isdir(idir):
                    for f in os.listdir(idir):
                        if f.endswith('.qcow2'): imported.append(f)
        except Exception: pass
        clone_opts='<option value="">(none)</option>'+''.join(f"<option value='{html.escape(f)}'>{html.escape(f)}</option>" for f in imported)
        # bridge list for creation
        bridges=[]
        try:
            for iface in os.listdir('/sys/class/net'):
                if os.path.isdir(os.path.join('/sys/class/net',iface,'bridge')):
                    bridges.append(iface)
        except Exception: pass
        bridge_sel=''.join(f"<option value='{html.escape(b)}'>{html.escape(b)}</option>" for b in bridges) or "<option value='virbr0'>virbr0</option>"
        nic_models=['virtio','e1000','e1000e','rtl8139','vmxnet3','ne2k_pci']
        nic_model_opts=''.join(f"<option value='{m}'>{m}</option>" for m in nic_models)
        form_html=f"""<form method='post'><input type='hidden' name='create_vm' value='1'><label>Name <input name='name' required></label><label>OS Type <select name='os_type' class='enh'><option value='linux' selected>Linux</option><option value='windows'>Windows</option></select></label><label>Mem MiB <input name='memory_mb' type='number' value='2048'></label><label>vCPUs <input name='vcpus' type='number' value='2'></label><label>Primary Disk GB <input name='disk_gb' type='number' value='20'></label><label>Clone From Imported Image <select name='clone_src'>{clone_opts}</select></label><label>Extra Disk GB (optional) <input name='extra_disk_gb' type='number' value='0'></label><label>Pool <select name='pool'>{pool_opts}</select></label><label>Bridge <select name='bridge'>{bridge_sel}</select></label><label>NIC Model <select name='nic_model'>{nic_model_opts}</select></label><label>Boot Order <select name='boot_order' class='enh'><option value='hd,cdrom,network'>Hard Disk, CD/DVD, Network</option><option value='cdrom,hd,network'>CD/DVD, Hard Disk, Network</option><option value='network,hd,cdrom'>Network, Hard Disk, CD/DVD</option><option value='hd,network,cdrom'>Hard Disk, Network, CD/DVD</option></select></label><input type='submit' value='Create' class='button'> <a class='button secondary' href='/'>Cancel</a><p class='inline-note'>If clone set, primary size ignored. Imported images found under images/.</p></form>"""
        return f"<div class='card'><h3>Create VM</h3>{msg}{form_html}</div>"

    def modal_vm(self, lv:LV):
        # Pools
        pool_opts=''.join(f"<option>{html.escape(p.name())}</option>" for p in lv.list_pools())
        # Bridges
        bridges=[]
        try:
            for iface in os.listdir('/sys/class/net'):
                if os.path.isdir(os.path.join('/sys/class/net',iface,'bridge')):
                    bridges.append(iface)
        except Exception: pass
        bridge_sel=''.join(f"<option value='{html.escape(b)}'>{html.escape(b)}</option>" for b in bridges) or "<option value='virbr0'>virbr0</option>"
        nic_models=['virtio','e1000','e1000e','rtl8139','vmxnet3','ne2k_pci']
        nic_model_opts=''.join(f"<option value='{m}'>{m}</option>" for m in nic_models)
        # Imported image list (basename only)
        imported=[]
        for p in lv.list_pools():
            try:
                import xml.etree.ElementTree as ET
                proot=ET.fromstring(p.XMLDesc(0))
                pool_path=proot.findtext('.//target/path') or ''
                idir=os.path.join(pool_path,'images')
                if os.path.isdir(idir):
                    for f in os.listdir(idir):
                        if f.endswith('.qcow2'): imported.append(f)
            except Exception: pass
        imported=sorted(set(imported))
        imported_opts='<option value="">(none)</option>'+''.join(f"<option value='{html.escape(f)}'>{html.escape(f)}</option>" for f in imported)
        # Disk bus options
        bus_opts="".join(f"<option>{b}</option>" for b in ['virtio','scsi','sata'])
        disk_help="<p class='inline-note'>Add one or more disks. New disks are raw. Image disks copy an imported raw image into the VM directory.</p>"
        disk_row_template=(
            "<div class='disk-spec' style='border:1px solid var(--border);padding:8px;border-radius:6px;margin-bottom:8px'>"
            "<div class='two-col' style='gap:12px'><label>Bus <select name='disk_bus' class='enh'>"+bus_opts+"</select></label><label>Type <select name='disk_type' class='enh' onchange='toggleDiskFields(this)'><option value='new' selected>New Blank</option><option value='image'>From Image</option></select></label></div>"
            "<div class='two-col' style='gap:12px'><label class='ds-size'>Size GB <input name='disk_size_gb' type='number' value='20'></label><label class='ds-image' style='display:none'>Image <select name='disk_image' class='enh'>"+imported_opts+"</select></label></div>"
            "<label>Target (auto if blank) <input name='disk_target' placeholder='(auto)'></label>"
            "<button type='button' class='small danger' onclick=\"this.closest('.disk-spec').remove();\">Remove</button>"
            "</div>"
        )
        add_disk_btn="<p><button class='small' type='button' onclick='addDiskSpec()'>Add Disk</button></p>"
        script_add_disk=("<script>function toggleDiskFields(sel){const wrap=sel.closest('.disk-spec');if(!wrap)return;const t=sel.value;wrap.querySelector('.ds-size').style.display=t==='new'?'block':'none';wrap.querySelector('.ds-image').style.display=t==='image'?'block':'none';}\nfunction addDiskSpec(){const c=document.getElementById('disk_specs');const t=`"+disk_row_template.replace('`','\\`')+"`;const div=document.createElement('div');div.innerHTML=t;const node=div.firstChild;c.appendChild(node);if(window.enhanceSelects)enhanceSelects();}\n</script>")
        return ("<div class='modal' id='modal_vm' hidden><div class='panel'><div style='display:flex;align-items:center;justify-content:space-between'><h3>Create VM</h3><button class='close secondary' onclick=\"closeModal('modal_vm')\">X</button></div>"
            + "<form method='post' action='/'><input type='hidden' name='create_vm' value='1'>"
            + "<label>Name <input name='name' required></label>"
            + "<div class='two-col' style='gap:12px'><label>Memory (GiB) <input name='memory_gb' type='number' value='2' min='0.5' step='0.5' required></label><label>vCPUs <input name='vcpus' type='number' value='2' min='1' required></label></div>"
            + f"<label>Pool <select class='enh' name='pool'>{pool_opts}</select></label>"
            + f"<label>Bridge <select class='enh' name='bridge'>{bridge_sel}</select></label>"
            + f"<label>NIC Model <select class='enh' name='nic_model'>{nic_model_opts}</select></label>"
            + "<div class='two-col' style='gap:12px'><label>Firmware <select class='enh' name='firmware'><option value='bios'>BIOS/MBR</option><option value='uefi'>UEFI</option></select></label><label>Machine <select class='enh' name='machine'><option value='pc'>pc</option><option value='q35'>q35</option></select></label></div>"
            + f"{disk_help}<div id='disk_specs'></div>{add_disk_btn}"
            + "<h4 style='margin: 1.2em 0 0.5em; padding-bottom: 0.3em; border-bottom: 1px solid var(--border);'>CD/DVD Drive</h4>"
            + "<div class='form-group' style='margin-bottom: 0.5rem;'>"
            + "<div class='two-col' style='gap: 12px; align-items: center;'>"
            + "<div>"
            + "<label style='display: flex; align-items: center; gap: 8px; cursor: pointer;'>"
            + "<input type='checkbox' name='enable_cdrom' id='enable_cdrom' onchange=\"document.getElementById('cdrom_iso_container').style.display=this.checked?'block':'none'\">"
            + "<span>Attach CD/DVD Drive</span>"
            + "</label>"
            + "</div>"
            + "<div id='cdrom_iso_container' style='display: none; width: 100%;'>"
            + "<select name='cdrom_iso' class='enh' style='width: 100%;'>"
            + "<option value=''>Select ISO image</option>" + ''.join(f'<option value=\"{html.escape(p.name())}::{html.escape(img)}\">{html.escape(p.name())}/{html.escape(img)}</option>' for p in lv.list_pools() for img in self.list_iso_images(p))
            + "</select>"
            + "</div>"
            + "</div>"
            + "<small class='form-text' style='margin-top: 4px;'>ISO images from all storage pools are listed</small>"
            + "</div>" 
            + "<div style='margin-top:8px'><input type='submit' class='button' value='Create' name='create_vm'> <button type='button' class='button secondary' onclick=\"closeModal('modal_vm')\">Cancel</button></div></form></div></div>" + script_add_disk)

    def progress_page(self, pid: str):
        body = f"""
        <div class='card' style='max-width: 800px; margin: 2rem auto;'>
            <h3 style='margin-top: 0;'>
                <span class='icon'>📊</span> Disk Image Creation in Progress
            </h3>
            <div style='margin: 1.5rem 0;'>
                <div style='display: flex; justify-content: space-between; margin-bottom: 0.5rem;'>
                    <span id='pct' style='font-weight: bold; color: var(--accent);'>0%</span>
                    <span id='status' style='color: var(--muted);'>Initializing...</span>
                </div>
                <div id='pb_wrap' style='
                    background: var(--card);
                    border: 1px solid var(--border);
                    border-radius: 10px;
                    width: 100%;
                    height: 20px;
                    overflow: hidden;
                    box-shadow: inset 0 1px 3px rgba(0,0,0,0.2);
                '>
                    <div id='pb' style='
                        background: linear-gradient(90deg, var(--accent), #3b82f6);
                        height: 100%;
                        width: 0%;
                        transition: width 0.5s ease-out, background-color 0.3s;
                        position: relative;
                        overflow: hidden;
                    '>
                        <div style='
                            position: absolute;
                            top: 0;
                            left: 0;
                            right: 0;
                            bottom: 0;
                            background: linear-gradient(
                                90deg,
                                rgba(255,255,255,0.1) 0%,
                                rgba(255,255,255,0.3) 50%,
                                rgba(255,255,255,0.1) 100%
                            );
                            animation: progressShine 2s infinite linear;
                            transform: translateX(-100%) rotate(45deg);
                        '></div>
                    </div>
                </div>
                <div id='details' style='
                    margin-top: 1rem;
                    padding: 0.75rem;
                    background: var(--card);
                    border: 1px solid var(--border);
                    border-radius: 6px;
                    font-size: 0.9em;
                    line-height: 1.5;
                '>
                    <div><strong>Operation ID:</strong> {pid}</div>
                    <div id='pbtxt' style='margin-top: 0.5rem;'>Starting image import process...</div>
                    <div id='speed' style='margin-top: 0.5rem; color: var(--muted); font-size: 0.9em;'></div>
                </div>
            </div>
            <div style='text-align: center; margin-top: 1.5rem;'>
                <button id='cancelBtn' class='button secondary' onclick='window.location="/?images=1"'>
                    Back to Images
                </button>
            </div>
        </div>

        <style>
            @keyframes progressShine {{
                0% {{ transform: translateX(-100%) rotate(45deg); }}
                100% {{ transform: translateX(100%) rotate(45deg); }}
            }}
            
            .icon {{
                margin-right: 0.5rem;
                vertical-align: middle;
            }}
            
            #pb_wrap:hover #pb {{
                background: linear-gradient(90deg, var(--accent), #2563eb);
            }}
        </style>

        <script>
            let lastUpdate = Date.now();
            let lastLoaded = 0;
            let lastSpeedUpdate = 0;
            let speedKbps = 0;
            let speedSamples = [];
            const MAX_SPEED_SAMPLES = 5;
            
            function updateProgress() {{
                const now = Date.now();
                const timeSinceLastUpdate = now - lastUpdate;
                
                // Only update if it's been at least 500ms since last update
                if (timeSinceLastUpdate < 500) {{
                    setTimeout(updateProgress, 100);
                    return;
                }}
                
                fetch(`/api/progress?id={pid}`)
                    .then(r => r.json())
                    .then(d => {{
                        lastUpdate = now;
                        
                        if (d.error) {{
                            updateError(d.error);
                            return;
                        }}
                        
                        // Update progress bar
                        const pb = document.getElementById('pb');
                        const pct = parseFloat(d.pct) || 0;
                        pb.style.width = pct + '%';
                        document.getElementById('pct').textContent = Math.round(pct) + '%';
                        
                        // Update status text
                        const statusEl = document.getElementById('status');
                        statusEl.textContent = d.status === 'done' ? 'Complete!' : 
                                            d.status === 'error' ? 'Error' : 
                                            d.status || 'In progress';
                        
                        // Update details
                        const pbtxt = document.getElementById('pbtxt');
                        pbtxt.textContent = d.msg || 'Processing...';
                        
                        // Calculate and display speed
                        if (d.loaded && d.loaded > 0) {{
                            const currentTime = Date.now();
                            const timeDiff = (currentTime - lastSpeedUpdate) / 1000; // in seconds
                            
                            if (timeDiff >= 1 && lastLoaded > 0) {{
                                const loadedDiff = d.loaded - lastLoaded;
                                const currentSpeed = loadedDiff / timeDiff; // bytes per second
                                
                                // Add to rolling average
                                speedSamples.push(currentSpeed);
                                if (speedSamples.length > MAX_SPEED_SAMPLES) {{
                                    speedSamples.shift();
                                }}
                                
                                // Calculate average speed
                                const avgSpeed = speedSamples.reduce((a, b) => a + b, 0) / speedSamples.length;
                                
                                // Format speed
                                let speedText;
                                if (avgSpeed > 1024 * 1024) {{
                                    speedText = (avgSpeed / (1024 * 1024)).toFixed(1) + ' MB/s';
                                }} else if (avgSpeed > 1024) {{
                                    speedText = (avgSpeed / 1024).toFixed(1) + ' KB/s';
                                }} else {{
                                    speedText = Math.round(avgSpeed) + ' B/s';
                                }}
                                
                                document.getElementById('speed').textContent = `Speed: ${speedText}`;
                                lastSpeedUpdate = currentTime;
                            }}
                            
                            lastLoaded = d.loaded;
                            if (lastSpeedUpdate === 0) lastSpeedUpdate = currentTime;
                        }}
                        
                        // Handle completion
                        if (d.status === 'done') {{
                            document.getElementById('status').style.color = 'var(--success)';
                            document.getElementById('cancelBtn').textContent = 'Return to Images';
                            document.getElementById('cancelBtn').className = 'button';
                            setTimeout(() => {{ window.location = '/?images=1'; }}, 1500);
                        }} else if (d.status === 'error') {{
                            document.getElementById('status').style.color = 'var(--danger)';
                            document.getElementById('cancelBtn').textContent = 'Back to Images';
                            document.getElementById('cancelBtn').className = 'button';
                        }}
                        
                        // Continue polling if not done
                        if (d.status !== 'done' && d.status !== 'error') {{
                            setTimeout(updateProgress, 500);
                        }}
                    }})
                    .catch(e => {{
                        console.error('Poll error:', e);
                        setTimeout(updateProgress, 1500);
                    }});
            }}
            
            function updateError(error) {{
                document.getElementById('status').textContent = 'Error';
                document.getElementById('status').style.color = 'var(--danger)';
                document.getElementById('pbtxt').textContent = error;
                document.getElementById('cancelBtn').textContent = 'Back to Images';
                document.getElementById('cancelBtn').className = 'button';
            }}
            
            // Start polling
            updateProgress();
            
            // Handle page visibility changes to reduce polling when tab is inactive
            document.addEventListener('visibilitychange', () => {{
                if (!document.hidden) {{
                    // Force update when tab becomes visible again
                    lastUpdate = 0;
                    updateProgress();
                }}
            }});
        </script>
        """
        return self.wrap('Image Import Progress', body)

    def page_images(self, lv:LV, form, qs=None):
        # Handle AJAX progress check
        if qs and 'ajax' in qs and 'progress_check' in qs:
            pid = qs['progress_check'][0]
            if pid in PROGRESS:
                data = PROGRESS[pid]
                import json
                self.send_response(200)
                self.send_header('Content-Type', 'application/json')
                self.end_headers()
                self.wfile.write(json.dumps(data).encode())
                return
            else:
                import json
                self.send_response(200)
                self.send_header('Content-Type', 'application/json')
                self.end_headers()
                self.wfile.write(json.dumps({'status': 'not_found'}).encode())
                return
        
        msg = ""
        if form and 'delete_image' in form:
            try:
                pool_name=form.get('pool',[''])[0]
                img=form.get('image',[''])[0]
                if not pool_name or not img: raise RuntimeError('Missing image')
                p=lv.get_pool(pool_name)
                import xml.etree.ElementTree as ET
                proot=ET.fromstring(p.XMLDesc(0))
                pool_path=proot.findtext('.//target/path') or ''
                path=os.path.join(pool_path,'images',img)
                if os.path.isfile(path):
                    os.remove(path)
                    msg+="<div class='inline-note'>Image deleted.</div>"
                else:
                    msg+="<div class='inline-note'>Image not found.</div>"
            except Exception as e:
                msg+=f"<div class='inline-note'>{html.escape(str(e))}</div>"
        
        if form and 'ingest_image' in form:
            try:
                pool_name = form.get('pool', [''])[0].strip()
                src = form.get('source', [''])[0].strip()
                out = form.get('out_name', ['imported'])[0].strip() or 'imported'
                
                if not pool_name:
                    raise RuntimeError('Please select a storage pool')
                if not src:
                    raise RuntimeError('Please specify a source URL or path')
                    
                # Verify the pool exists
                try:
                    pool = lv.get_pool(pool_name)
                    if not pool:
                        raise RuntimeError(f'Storage pool "{pool_name}" not found')
                except Exception as e:
                    raise RuntimeError(f'Error accessing storage pool: {str(e)}')
                
                # Auto-extract filename from URL/path for all image types
                if not out or out == 'imported':
                    # Extract filename from URL or path
                    base_name = os.path.basename(src.split('?')[0])  # Remove query params from URLs
                    if base_name:
                        # Remove common extensions to get clean name
                        for ext in ['.iso', '.qcow2', '.raw', '.img', '.vmdk']:
                            if base_name.lower().endswith(ext):
                                out = base_name[:-len(ext)]
                                break
                        else:
                            out = base_name
                    else:
                        out = 'imported'
                        
                pid = str(time.time())
                start_image_ingest(pid, pool_name, src, out)
                # Redirect to progress page with auto-refresh
                self.send_response(302)
                self.send_header('Location', f"/?images=1&progress={pid}")
                self.end_headers()
                return
            except Exception as e:
                msg += f"<div class='inline-note'>{html.escape(str(e))}</div>"
        # Create beautiful image cards without pool expansion
        rows = []
        all_images = []
        
        for p in lv.list_pools():
            try:
                import xml.etree.ElementTree as ET
                pxml = p.XMLDesc(0)
                proot = ET.fromstring(pxml)
                pool_path = proot.findtext('.//target/path') or ''
                idir = os.path.join(pool_path, 'images')
                
                if os.path.isdir(idir):
                    for f in sorted(os.listdir(idir)):
                        if f.endswith('.raw') or f.endswith('.iso') or f.endswith('.qcow2'):
                            path = os.path.join(idir, f)
                            try:
                                size = os.path.getsize(path)
                                # Determine file type icon
                                if f.endswith('.iso'):
                                    icon = '💿'
                                    type_label = 'ISO'
                                elif f.endswith('.qcow2'):
                                    icon = '💾'
                                    type_label = 'QCOW2'
                                else:
                                    icon = '🗄️'
                                    type_label = 'RAW'
                                
                                # Check for active progress
                                progress_info = ''
                                for pid, data in PROGRESS.items():
                                    if data.get('msg', '').endswith(f):
                                        pct = data.get('pct', 0)
                                        status = data.get('status', '')
                                        if status == 'running':
                                            progress_info = f"""
                                            <div style='margin-top:8px'>
                                                <div style='font-size:12px;color:var(--text-secondary);margin-bottom:4px'>Importing... {pct:.1f}%</div>
                                                <div style='width:100%;height:4px;background:var(--card-secondary);border-radius:2px;overflow:hidden'>
                                                    <div style='width:{pct}%;height:100%;background:var(--primary);transition:width 0.3s'></div>
                                                </div>
                                            </div>
                                            """
                                
                                all_images.append({
                                    'name': f,
                                    'pool': p.name(),
                                    'size': size,
                                    'path': path,
                                    'icon': icon,
                                    'type': type_label,
                                    'progress': progress_info
                                })
                            except OSError:
                                continue
            except Exception:
                continue
        
        # Create compact image list
        if all_images:
            # Container with constrained width
            rows.append("""
            <div class='card' style='max-width:600px;padding:12px'>
                <h4 style='margin:0 0 12px 0;color:var(--fg)'>Available Images</h4>
                <div style='display:flex;flex-direction:column;gap:6px'>
            """)
            
            for img in all_images:
                item = f"""
                    <div style='display:flex;align-items:center;padding:4px 0;border-bottom:1px solid var(--border)'>
                        <span style='font-size:14px;margin-right:8px'>{img['icon']}</span>
                        <div style='flex:1;min-width:0'>
                            <div style='font-weight:500;color:var(--fg);font-size:13px;white-space:nowrap;overflow:hidden;text-overflow:ellipsis'>{html.escape(img['name'])}</div>
                            <div style='font-size:10px;color:var(--text-secondary)'>
                                {img['type']} • {human_bytes(img['size'])} • {html.escape(img['pool'])}
                            </div>
                        </div>
                        <form method='post' action='/?images=1' style='margin:0'>
                            <input type='hidden' name='delete_image' value='1'>
                            <input type='hidden' name='pool' value='{html.escape(img['pool'])}'>
                            <input type='hidden' name='image' value='{html.escape(img['name'])}'>
                            <button type='submit' onclick="return confirm('Delete image?')" 
                                    style='background:none;border:none;color:var(--danger);cursor:pointer;padding:2px;font-size:12px;opacity:0.7;transition:opacity 0.2s'
                                    onmouseover='this.style.opacity="1"' onmouseout='this.style.opacity="0.7"'>
                                🗑️
                            </button>
                        </form>
                        {img['progress']}
                    </div>
                """
                rows.append(item)
            
            rows.append("</div></div>")
        else:
            rows.append("""
            <div class='card' style='text-align:center;padding:40px;color:var(--text-secondary)'>
                <div style='font-size:48px;margin-bottom:16px'>📁</div>
                <div style='font-size:16px;margin-bottom:8px'>No images found</div>
                <div style='font-size:14px'>Import an image to get started</div>
            </div>
            """)
        pools_opts = ''.join(
            f"<option>{html.escape(p.name())}</option>" for p in lv.list_pools()
        )
        modal = (
            "<div class='modal' id='modal_image' hidden><div class='panel'>"
            "<div style='display:flex;justify-content:space-between;align-items:center'><h3>Create Disk Image</h3>"
            "<button class='close secondary' onclick=\"closeModal('modal_image')\">X</button></div>"
            f"<form method='post' action='/?images=1'><input type='hidden' name='ingest_image' value='1'>"
            f"<label>Pool <select name='pool' class='enh'>{pools_opts}</select></label>"
            "<label>Source (http/https/nfs/local) <input name='source' id='image-source' required oninput='updateImageName(this)'></label>"
            "<label>Output Name <input name='out_name' id='image-output' value=''></label>"
            "<div id='pool_required' style='color: #ff6b6b; font-size: 0.9em; margin: 6px 0; display: none;'>Please select a storage pool</div>"
            "<div style='margin-top:8px'><input type='submit' class='button' value='Import' id='start_import'> "
            "<button type='button' class='button secondary' onclick=\"closeModal('modal_image')\">Cancel</button></div></form>"
            "<script>"
            "document.addEventListener('DOMContentLoaded', function() {"
            "  const poolSelect = document.querySelector(\"#modal_image select[name='pool']\");"
            "  const startButton = document.getElementById('start_import');"
            "  const sourceInput = document.querySelector(\"#modal_image input[name='source']\");"
            "  const poolRequired = document.getElementById('pool_required');"
            "  "
            "  function validateForm() {"
            "    const poolSelected = poolSelect && poolSelect.value.trim() !== '';"
            "    const sourceFilled = sourceInput && sourceInput.value.trim() !== '';"
            "    "
            "    if (startButton) {"
            "      startButton.disabled = !(poolSelected && sourceFilled);"
            "      startButton.style.opacity = (poolSelected && sourceFilled) ? '1' : '0.6';"
            "    }"
            "    if (poolRequired) {"
            "      poolRequired.style.display = (!poolSelected && sourceFilled) ? 'block' : 'none';"
            "    }"
            "  }"
            "  "
            "  if (poolSelect) {"
            "    poolSelect.addEventListener('change', validateForm);"
            "    // Trigger validation on modal open"
            "    setTimeout(validateForm, 100);"
            "  }"
            "  if (sourceInput) {"
            "    sourceInput.addEventListener('input', validateForm);"
            "    sourceInput.addEventListener('keyup', validateForm);"
            "  }"
            "  "
            "  // Form submission handler"
            "  const form = startButton ? startButton.closest('form') : null;"
            "  if (form) {"
            "    form.addEventListener('submit', function(e) {"
            "      const poolSelected = poolSelect && poolSelect.value.trim() !== '';"
            "      const sourceFilled = sourceInput && sourceInput.value.trim() !== '';"
            "      "
            "      if (!poolSelected) {"
            "        e.preventDefault();"
            "        alert('Please select a storage pool');"
            "        return false;"
            "      }"
            "      if (!sourceFilled) {"
            "        e.preventDefault();"
            "        alert('Please enter a source URL or path');"
            "        return false;"
            "      }"
            "      "
            "      // Show loading state"
            "      startButton.disabled = true;"
            "      startButton.value = 'Starting...';"
            "      return true;"
            "    });"
            "  }"
            "  "
            "  // Initial validation"
            "  setTimeout(validateForm, 50);"
            "});"
            "</script>"
            "<script>"
            "function updateImageName(input) {"
            "  const src = input.value.trim();"
            "  const output = document.getElementById('image-output');"
            "  if (src.toLowerCase().endsWith('.iso')) {"
            "    const fileName = src.split('/').pop().split('\\\\').pop();"
            "    if (fileName.toLowerCase().endsWith('.iso')) {"
            "      output.value = fileName.slice(0, -4);"
            "    } else {"
            "      output.value = fileName;"
            "    }"
            "  }"
            "}"
            "</script></div></div>"
        )
        inline_fallback = (
            "<div class='card' id='inline_ingest'><h4>Create Disk Image (Fallback)</h4>"
            f"<form method='post' action='/?images=1'><input type='hidden' name='ingest_image' value='1'>"
            f"<label>Pool <select name='pool'>{pools_opts}</select></label>"
            "<label>Source <input name='source' required></label>"
            "<label>Output Name <input name='out_name' value='imported'></label>"
            "<div class='inline-note error' style='display: none;' id='fallback_pool_error'>Please select a storage pool</div>"
            "<div style='margin-top:6px'><input type='submit' class='button' value='Start' onclick=\"return validateFallbackForm()\"></div></form>"
            "<script>"
            "function validateFallbackForm() {"
            "  const poolSelect = document.querySelector('#inline_ingest select[name=\"pool\"]');"
            "  const sourceInput = document.querySelector('#inline_ingest input[name=\"source\"]');"
            "  const errorDiv = document.getElementById('fallback_pool_error');"
            "  "
            "  if (!poolSelect || !poolSelect.value.trim()) {"
            "    if (errorDiv) errorDiv.style.display = 'block';"
            "    return false;"
            "  }"
            "  if (!sourceInput || !sourceInput.value.trim()) {"
            "    if (errorDiv) errorDiv.style.display = 'block';"
            "    return false;"
            "  }"
            "  return true;"
            "}"
            "</script>"
            "<p class='inline-note'>Showing fallback because JS might be disabled. Modal normally hides this.</p></div>"
        )
        btn = ("<p><a class='button modal-trigger' data-modal='modal_image' href='#' role='button' onclick=\"var m=document.getElementById('modal_image');if(m){m.hidden=false;m.style.display='flex';}return false;\">Import Image</a></p>")
        # Active progress blocks with enhanced display (exclude RAID-related progress)
        prog_blocks=''
        for pid,data in list(PROGRESS.items()):
            st=data.get('status'); pct=data.get('pct',0); msgp=html.escape(data.get('msg',''))
            if st in ('done','error') and (time.time()-data.get('ts',time.time()))>30:
                continue
            # Skip RAID-related progress on images page
            if 'raid' in msgp.lower() or 'mdadm' in msgp.lower() or 'btrfs' in msgp.lower():
                continue
            # Create visual progress bar with improved styling
            progress_bar = f"""
            <div style='width:100%;max-width:400px;height:8px;background:var(--card-secondary);border:1px solid var(--border);border-radius:4px;overflow:hidden;margin:8px 0'>
                <div style='width:{pct}%;height:100%;background:{('#4CAF50' if st=='done' else '#ff6b6b' if st=='error' else 'var(--primary)')};transition:width 0.3s ease'></div>
            </div>
            """
            prog_blocks+=f"""
            <div class='card' style='margin:8px 0;padding:16px;font-family:inherit'>
                <div style='display:flex;justify-content:space-between;align-items:center;margin-bottom:8px'>
                    <span style='font-weight:500;color:var(--fg)'>{html.escape(msgp)}</span>
                    <span style='font-size:14px;color:var(--text-secondary)'>{pct:.1f}%</span>
                </div>
                {progress_bar}
                <div style='font-size:12px;color:var(--text-secondary);margin-top:4px'>Status: {html.escape(st)}</div>
            </div>
            """
        # Check if we need to show progress polling
        progress_script = ""
        if qs and 'progress' in qs:
            progress_pid = qs['progress'][0]
            progress_script = f"""
            <script>
            window.imagePollRunning = true;
            let progressPid = '{progress_pid}';
            let pollCount = 0;
            const maxPolls = 300; // 5 minutes max
            
            function pollProgress() {{
                if (pollCount >= maxPolls) {{
                    console.log('Progress polling timed out');
                    window.imagePollRunning = false;
                    return;
                }}
                
                fetch('/?images=1&ajax=1&progress_check=' + progressPid)
                    .then(response => response.json())
                    .then(data => {{
                        if (data.status === 'done' || data.status === 'error') {{
                            // Progress complete, refresh page to show final state
                            setTimeout(() => {{
                                window.location.href = '/?images=1';
                            }}, 2000);
                            window.imagePollRunning = false;
                        }} else if (data.status && data.pct !== undefined) {{
                            // Update progress display in real-time
                            updateProgressDisplay(data);
                            pollCount++;
                            setTimeout(pollProgress, 1000);
                        }} else {{
                            // Continue polling
                            pollCount++;
                            setTimeout(pollProgress, 1000);
                        }}
                    }})
                    .catch(error => {{
                        console.error('Progress polling error:', error);
                        pollCount++;
                        if (pollCount < maxPolls) {{
                            setTimeout(pollProgress, 2000); // Retry with longer delay
                        }} else {{
                            window.imagePollRunning = false;
                        }}
                    }});
            }}
            
            function updateProgressDisplay(data) {{
                // Find progress elements and update them
                const progressCards = document.querySelectorAll('.card');
                progressCards.forEach(card => {{
                    const progressBar = card.querySelector('div[style*="width:"][style*="height:8px"]');
                    if (progressBar) {{
                        const innerBar = progressBar.querySelector('div');
                        if (innerBar) {{
                            innerBar.style.width = data.pct + '%';
                        }}
                        
                        // Update percentage text
                        const percentSpan = card.querySelector('span[style*="font-size:14px"]');
                        if (percentSpan) {{
                            percentSpan.textContent = data.pct.toFixed(1) + '%';
                        }}
                        
                        // Update message
                        const messageSpan = card.querySelector('span[style*="font-weight:500"]');
                        if (messageSpan) {{
                            messageSpan.textContent = data.msg || 'Processing...';
                        }}
                        
                        // Update status
                        const statusDiv = card.querySelector('div[style*="font-size:12px"]');
                        if (statusDiv) {{
                            statusDiv.textContent = 'Status: ' + (data.status || 'running');
                        }}
                    }}
                }});
            }}
            
            // Start polling after page load
            setTimeout(pollProgress, 1000);
            </script>
            """
        
        # Add auto-refresh script for progress updates
        auto_refresh_script = ""
        if prog_blocks or qs and 'progress' in qs:  # Add if there are progress blocks OR we're on a progress page
            auto_refresh_script = f"""
            <script>
            // Auto-refresh for progress updates
            if (!window.imageProgressInterval) {{
                window.imageProgressInterval = setInterval(() => {{
                    // Check if there are still progress blocks visible or if we're on a progress page
                    const progressCards = document.querySelectorAll('.card');
                    let hasActiveProgress = false;
                    
                    // Check for progress bars in cards
                    progressCards.forEach(card => {{
                        const progressBar = card.querySelector('div[style*="height:4px"], div[style*="height:8px"]');
                        if (progressBar) {{
                            hasActiveProgress = true;
                        }}
                    }});
                    
                    // Also check if we're on a progress page (URL contains progress parameter)
                    if (window.location.search.includes('progress=')) {{
                        hasActiveProgress = true;
                    }}
                    
                    if (hasActiveProgress) {{
                        // Simple page reload to update progress
                        window.location.reload();
                    }} else {{
                        // No more active progress, clear interval
                        clearInterval(window.imageProgressInterval);
                        window.imageProgressInterval = null;
                    }}
                }}, 3000); // Refresh every 3 seconds
            }}
            </script>
            """
        
        return (
            f"<div class='card'><h3>Images</h3>{msg}{btn}{prog_blocks}{''.join(rows)}{modal}{inline_fallback}</div>{progress_script}{auto_refresh_script}"
        )

    def page_storage(self, lv:LV, form):
        msg=""
        if form:
            try:
                if 'create_pool' in form:
                    name = form.get('pool_name', [''])[0].strip()
                    mp = form.get('mountpoint', [''])[0].strip()
                    
                    # Validate inputs
                    if not name:
                        raise RuntimeError('Please specify a pool name')
                    if not mp:
                        raise RuntimeError('Please specify a mount point path')
                    
                    # Validate pool name
                    if not all(c.isalnum() or c in '.-_' for c in name):
                        raise RuntimeError('Pool name can only contain letters, numbers, dots, hyphens, and underscores')
                    
                    # Validate and prepare the mount point path
                    try:
                        # Expand user directory and resolve any relative paths
                        mp = os.path.abspath(os.path.expanduser(mp))
                        
                        # Check if path exists and is a directory, or create it
                        if os.path.exists(mp):
                            if not os.path.isdir(mp):
                                raise RuntimeError(f'Path exists but is not a directory: {mp}')
                            if not os.access(mp, os.W_OK):
                                raise RuntimeError(f'No write permission for directory: {mp}')
                        else:
                            # Create the directory and any parent directories
                            os.makedirs(mp, mode=0o755, exist_ok=True)
                            msg += f"<div class='inline-note'>Created directory: {mp}</div>"
                        
                        # Create the pool
                        lv.define_pool_dir(name, mp)
                        msg += f"<div class='inline-note success'>Storage pool '{name}' created successfully at {mp}</div>"
                        
                    except OSError as e:
                        raise RuntimeError(f'Failed to create directory {mp}: {str(e)}')
                    except Exception as e:
                        raise RuntimeError(f'Failed to create storage pool: {str(e)}')
                if 'create_btrfs_raid' in form:
                    label=form.get('label',['btrfs_raid'])[0]
                    level=form.get('btrfs_level',['raid1'])[0]
                    devs=form.get('devices',[])
                    mnt=form.get('mountpoint',[''])[0]
                    if len(devs)<1:
                        raise RuntimeError('Select devices')
                    
                    # Create async BTRFS RAID creation
                    import uuid as uuid_mod
                    btrfs_pid = str(uuid_mod.uuid4())[:8]
                    PROGRESS[btrfs_pid] = {'status':'starting','pct':0,'msg':'Preparing BTRFS RAID creation','ts':time.time()}
                    
                    def create_btrfs_async():
                        try:
                            PROGRESS[btrfs_pid]['status'] = 'running'
                            PROGRESS[btrfs_pid]['pct'] = 10
                            PROGRESS[btrfs_pid]['msg'] = 'Creating BTRFS filesystem'
                            
                            cmd=['sudo','mkfs.btrfs','-f','-L',label]
                            if level!='single':
                                cmd+=['-m',level,'-d',level]
                            cmd+=devs
                            subprocess.check_call(cmd)
                            
                            PROGRESS[btrfs_pid]['pct'] = 60
                            PROGRESS[btrfs_pid]['msg'] = 'Creating mount point'
                            subprocess.check_call(['sudo', 'mkdir', '-p', mnt])
                            
                            PROGRESS[btrfs_pid]['pct'] = 80
                            PROGRESS[btrfs_pid]['msg'] = 'Mounting filesystem'
                            subprocess.check_call(['sudo','mount','-o','noatime,ssd,discard,compress=zstd',devs[0],mnt])
                            
                            PROGRESS[btrfs_pid]['pct'] = 95
                            PROGRESS[btrfs_pid]['msg'] = 'Updating fstab'
                            try:
                                uuid=subprocess.check_output(['blkid','-s','UUID','-o','value',devs[0]],text=True).strip()
                                if uuid:
                                    with open('/etc/fstab','a') as f:
                                        f.write(f"UUID={uuid} {mnt} btrfs noatime,ssd,discard,compress=zstd 0 0\n")
                            except Exception:
                                pass
                            
                            PROGRESS[btrfs_pid]['status'] = 'done'
                            PROGRESS[btrfs_pid]['pct'] = 100
                            PROGRESS[btrfs_pid]['msg'] = f'BTRFS RAID {label} created and mounted at {mnt}'
                        except Exception as e:
                            PROGRESS[btrfs_pid]['status'] = 'error'
                            PROGRESS[btrfs_pid]['msg'] = str(e)
                    
                    threading.Thread(target=create_btrfs_async, daemon=True).start()
                    msg+=f"<div class='inline-note'>Creating BTRFS RAID {label} in background (check progress below)</div>"
                if 'create_mdraid' in form:
                    level=form.get('md_level',['1'])[0]
                    devs=form.get('devices',[])
                    mnt=form.get('mountpoint',[''])[0]
                    name=form.get('md_name',['md0'])[0]
                    if len(devs)<1:
                        raise RuntimeError('Select devices')
                    mdpath=f"/dev/{name}"
                    
                    # Create async RAID creation
                    import uuid as uuid_mod
                    raid_pid = str(uuid_mod.uuid4())[:8]
                    PROGRESS[raid_pid] = {'status':'starting','pct':0,'msg':'Preparing RAID creation','ts':time.time()}
                    
                    def create_raid_async():
                        try:
                            PROGRESS[raid_pid]['status'] = 'running'
                            PROGRESS[raid_pid]['pct'] = 10
                            PROGRESS[raid_pid]['msg'] = 'Creating mdadm array'
                            
                            cmd=['sudo','mdadm','--create',mdpath,'--bitmap=none','--level',level,f"--raid-devices={len(devs)}"]+devs
                            subprocess.check_call(cmd)
                            
                            PROGRESS[raid_pid]['pct'] = 40
                            PROGRESS[raid_pid]['msg'] = 'Creating XFS filesystem'
                            subprocess.check_call(['sudo','mkfs.xfs','-f',mdpath])
                            
                            PROGRESS[raid_pid]['pct'] = 70
                            PROGRESS[raid_pid]['msg'] = 'Mounting filesystem'
                            os.makedirs(mnt,exist_ok=True)
                            subprocess.check_call(['sudo','mount',mdpath,mnt])
                            
                            PROGRESS[raid_pid]['pct'] = 90
                            PROGRESS[raid_pid]['msg'] = 'Updating fstab'
                            try:
                                uuid=subprocess.check_output(['sudo','blkid','-s','UUID','-o','value',mdpath],text=True).strip()
                                if uuid:
                                    with open('/etc/fstab','a') as f:
                                        f.write(f"UUID={uuid} {mnt} xfs noatime,discard 0 0\n")
                            except Exception:
                                pass
                            
                            PROGRESS[raid_pid]['status'] = 'done'
                            PROGRESS[raid_pid]['pct'] = 100
                            PROGRESS[raid_pid]['msg'] = f'RAID {name} created and mounted at {mnt}'
                        except Exception as e:
                            PROGRESS[raid_pid]['status'] = 'error'
                            PROGRESS[raid_pid]['msg'] = str(e)
                    
                    threading.Thread(target=create_raid_async, daemon=True).start()
                    msg+=f"<div class='inline-note'>Creating mdadm RAID {name} in background (check progress below)</div>"
            except Exception as e:
                msg+=f"<div class='inline-note'>{html.escape(str(e))}</div>"
        mounts=[]
        try:
            with open('/proc/mounts') as f:
                for line in f:
                    parts=line.split()
                    if len(parts)>=3 and parts[2] in ('btrfs','xfs'):
                        mounts.append((parts[1],parts[2]))
        except Exception:
            pass
        
        # Get existing RAID arrays and BTRFS filesystems
        existing_raids = []
        try:
            # Check for mdadm arrays
            result = subprocess.run(['cat', '/proc/mdstat'], capture_output=True, text=True, timeout=5)
            if result.returncode == 0:
                for line in result.stdout.splitlines():
                    if 'active' in line and 'raid' in line:
                        parts = line.split()
                        if len(parts) > 0 and parts[0].startswith('md'):
                            array_name = parts[0]
                            # Extract device names from the mdstat line
                            devices = []
                            for part in parts[1:]:
                                if part.startswith(('sd', 'nvme')) and '[' in part:
                                    device = part.split('[')[0]
                                    devices.append(f'/dev/{device}')
                            
                            # Check if mounted by looking in /proc/mounts
                            mount_point = None
                            fs_type = 'unknown'
                            try:
                                with open('/proc/mounts') as f:
                                    for mount_line in f:
                                        mount_parts = mount_line.split()
                                        if len(mount_parts) >= 3 and mount_parts[0] == f'/dev/{array_name}':
                                            mount_point = mount_parts[1]
                                            fs_type = mount_parts[2]
                                            break
                            except Exception:
                                pass
                            existing_raids.append({
                                'name': array_name,
                                'type': 'mdadm',
                                'mount_point': mount_point,
                                'fs_type': fs_type,
                                'status': 'mounted' if mount_point else 'unmounted',
                                'devices': devices
                            })
        except Exception:
            pass
        
        try:
            # Check for BTRFS filesystems
            result = subprocess.run(['sudo','btrfs', 'filesystem', 'show'], capture_output=True, text=True, timeout=5)
            if result.returncode == 0:
                current_uuid = None
                current_label = None
                current_devices = []
                for line in result.stdout.splitlines():
                    if 'uuid:' in line.lower():
                        # Process previous filesystem if we have one
                        if current_uuid and current_devices:
                            # Find mount point for this BTRFS filesystem
                            mount_point = None
                            try:
                                with open('/proc/mounts') as f:
                                    for mount_line in f:
                                        mount_parts = mount_line.split()
                                        if len(mount_parts) >= 3 and mount_parts[2] == 'btrfs':
                                            # Check if any of the current devices match
                                            if any(dev in mount_parts[0] for dev in current_devices):
                                                mount_point = mount_parts[1]
                                                break
                            except Exception:
                                pass
                            
                            existing_raids.append({
                                'name': current_label or current_uuid[:8],
                                'type': 'btrfs',
                                'mount_point': mount_point,
                                'fs_type': 'btrfs',
                                'status': 'mounted' if mount_point else 'unmounted',
                                'uuid': current_uuid,
                                'devices': current_devices.copy()
                            })
                        
                        # Start new filesystem
                        current_devices = []
                        parts = line.split()
                        for i, part in enumerate(parts):
                            if part.lower() == 'uuid:' and i + 1 < len(parts):
                                current_uuid = parts[i + 1]
                        if 'Label:' in line:
                            label_idx = line.find('Label:')
                            if label_idx != -1:
                                label_part = line[label_idx + 6:].strip()
                                # Remove quotes and handle 'none' case
                                if label_part.lower() == 'none':
                                    current_label = None
                                else:
                                    current_label = label_part.strip("'\"")
                        else:
                            current_label = None
                    elif current_uuid and 'devid' in line and '/dev/' in line:
                        # Extract device path
                        parts = line.split()
                        for part in parts:
                            if part.startswith('/dev/'):
                                current_devices.append(part)
                                break
                
                # Process last filesystem
                if current_uuid and current_devices:
                    mount_point = None
                    try:
                        with open('/proc/mounts') as f:
                            for mount_line in f:
                                mount_parts = mount_line.split()
                                if len(mount_parts) >= 3 and mount_parts[2] == 'btrfs':
                                    if any(dev in mount_parts[0] for dev in current_devices):
                                        mount_point = mount_parts[1]
                                        break
                    except Exception:
                        pass
                    
                    existing_raids.append({
                        'name': current_label or current_uuid[:8],
                        'type': 'btrfs',
                        'mount_point': mount_point,
                        'fs_type': 'btrfs',
                        'status': 'mounted' if mount_point else 'unmounted',
                        'uuid': current_uuid,
                        'devices': current_devices.copy()
                    })
        except Exception:
            pass
        
        # Display existing RAID arrays
        existing_raids_html = ""
        if existing_raids:
            raids_rows = ""
            for raid in existing_raids:
                status_color = "#4CAF50" if raid['status'] == 'mounted' else "#ff9800"
                actions = ""
                
                # URL encode the parameters properly
                import urllib.parse
                raid_name_encoded = urllib.parse.quote(raid['name'])
                mount_point_encoded = urllib.parse.quote(raid['mount_point'] or '')
                # Escape single quotes for JavaScript
                escaped_quote = "\\'"
                raid_name_js = raid['name'].replace("'", escaped_quote)
                
                if raid['status'] == 'mounted':
                    actions += f"<button class='small' onclick=\"if(confirm('Unmount {raid_name_js}?')) {{ fetch('/unmount_array', {{ method: 'POST', headers: {{'Content-Type': 'application/x-www-form-urlencoded'}}, body: 'type={raid['type']}&name={raid_name_encoded}&mount_point={mount_point_encoded}' }}).then(() => location.reload()); }}\">Unmount</button>"
                else:
                    # Show mount button for unmounted filesystems
                    if raid['type'] == 'btrfs':
                        actions += f"<button class='small' onclick=\"var mountPoint = prompt('Enter mount point:', ''); if(mountPoint) {{ fetch('/mount_array', {{ method: 'POST', headers: {{'Content-Type': 'application/x-www-form-urlencoded'}}, body: 'type=btrfs&name={raid_name_encoded}&mount_point=' + encodeURIComponent(mountPoint) }}).then(() => location.reload()); }}\">Mount</button> "
                    elif raid['type'] == 'mdadm':
                        actions += f"<button class='small' onclick=\"var mountPoint = prompt('Enter mount point:', '/mnt/{raid_name_js}'); if(mountPoint) {{ fetch('/mount_array', {{ method: 'POST', headers: {{'Content-Type': 'application/x-www-form-urlencoded'}}, body: 'type=mdadm&name={raid_name_encoded}&mount_point=' + encodeURIComponent(mountPoint) }}).then(() => location.reload()); }}\">Mount</button> "
                    
                    # Show remove button for unmounted filesystems
                    if raid['type'] == 'mdadm':
                        actions += f"<button class='small danger' onclick=\"if(confirm('Remove mdadm array {raid_name_js}? This will wipefs all devices and destroy all data!')) {{ fetch('/remove_array', {{ method: 'POST', headers: {{'Content-Type': 'application/x-www-form-urlencoded'}}, body: 'type=mdadm&name={raid_name_encoded}' }}).then(() => location.reload()); }}\">Remove</button>"
                    elif raid['type'] == 'btrfs':
                        actions += f"<button class='small danger' onclick=\"if(confirm('Remove BTRFS filesystem {raid_name_js}? This will wipefs all devices and destroy all data!')) {{ fetch('/remove_array', {{ method: 'POST', headers: {{'Content-Type': 'application/x-www-form-urlencoded'}}, body: 'type=btrfs&name={raid_name_encoded}' }}).then(() => location.reload()); }}\">Remove</button>"
                
                raids_rows += f"""
                <tr>
                    <td>{html.escape(raid['name'])}</td>
                    <td>{html.escape(raid['type'].upper())}</td>
                    <td>{html.escape(raid['mount_point'] or 'Not mounted')}</td>
                    <td><span style="color:{status_color}">{html.escape(raid['status'])}</span></td>
                    <td>{actions}</td>
                </tr>
                """
            
            existing_raids_html = f"""
            <h4>Existing RAID Arrays</h4>
            <table>
                <thead>
                    <tr><th>Name</th><th>Type</th><th>Mount Point</th><th>Status</th><th>Actions</th></tr>
                </thead>
                <tbody>{raids_rows}</tbody>
            </table>
            """
        
        mount_opts=''.join(f"<option value='{html.escape(mp)}'>{html.escape(mp)} ({fs})</option>" for mp,fs in mounts)
        pools_list=''.join(f"<li>{html.escape(p.name())}</li>" for p in lv.list_pools()) or '<li><em>None</em></li>'
        devices=self.block_devices()
        # Generate device rows with USB filtering capability
        all_dev_rows = []
        non_usb_dev_rows = []
        
        for d in devices:
            is_usb = str(d.get('tran', '').lower() == 'usb').lower()
            row_html = (
                f"<div class='disk-row' onclick=\"toggleDiskSelection(this)\" data-dev='{html.escape(d['path'])}' data-is-usb='{is_usb}'>"
                f"<div class='disk-actions'>"
                f"<button type='button' onclick=\"event.stopPropagation(); wipeDisk('{html.escape(d['path'])}', this)\" class='button small danger'>Wipe</button>"
                f"</div>"
                f"<strong>{html.escape(d['name'])}</strong><br>"
                f"<span class='inline-note'>Model: {html.escape(d.get('model','?'))} | Serial: {html.escape(d.get('serial','?'))} | Size: {html.escape(d.get('size_h','?'))} | Bus: {html.escape(d.get('tran','?'))}</span>"
                f"</div>"
            )
            all_dev_rows.append(row_html)
            if d.get('tran', '').lower() != 'usb':
                non_usb_dev_rows.append(row_html)
        
        dev_rows_all = ''.join(all_dev_rows) or "<p class='inline-note'>No available disks. All disks are either mounted, part of existing RAID arrays, or have mounted partitions.</p>"
        dev_rows_no_usb = ''.join(non_usb_dev_rows) or "<p class='inline-note'>No available disks. All disks are either mounted, part of existing RAID arrays, or have mounted partitions.</p>"
        modal_pool=(
            f"<div class='modal' id='modal_pool' hidden><div class='panel'><div style='display:flex;justify-content:space-between;align-items:center'><h3>Create Pool</h3><button class='close secondary' onclick=\"closeModal('modal_pool')\">X</button></div>"
            + f"<form method='post' action='/?storage=1'><input type='hidden' name='create_pool' value='1'>"
            + "<label>Name <input name='pool_name' required pattern='[a-zA-Z0-9_.-]+' title='Only letters, numbers, dots, hyphens, and underscores are allowed'></label>"
            + "<label>Directory Path <input name='mountpoint' required placeholder='/path/to/storage' title='Absolute path to the storage directory'></label>"
            + "<small class='form-text'>Enter any absolute path to an existing directory or a new one to create</small>"
            + "<div style='margin-top:8px'><input type='submit' class='button' value='Create'> <button type='button' class='button secondary' onclick=\"closeModal('modal_pool')\">Cancel</button></div></form>"
            + "</div></div>"
        )
        modal_btrfs=(
            "<div class='modal' id='modal_btrfs' hidden><div class='panel'><div style='display:flex;justify-content:space-between;align-items:center'><h3>Create BTRFS RAID</h3><button class='close secondary' onclick=\"closeModal('modal_btrfs')\">X</button></div>"
            f"<form method='post' action='/?storage=1'><input type='hidden' name='create_btrfs_raid' value='1'><label>Label <input name='label' value='btrfs_raid'></label><label>Level <select name='btrfs_level' class='enh'><option>single</option><option>raid0</option><option selected>raid1</option><option>raid10</option><option>raid5</option></select></label><label>Mountpoint <input name='mountpoint' value='/btrfs'></label><div style='margin-bottom:8px'><button type='button' class='button small' onclick='bulkWipeSelected(\"btrfs\")'>Wipe selected drives</button></div><div id='btrfs-devices-container' style='max-height:260px;overflow:auto'><div id='btrfs-devices-no-usb'>"
            + dev_rows_no_usb
            + f"</div><div id='btrfs-devices-all' style='display:none'>"
            + dev_rows_all
            + "</div></div><div class='devices-box'></div><div style='margin-top:8px'><label><input type='checkbox' id='btrfs-show-usb' onchange='toggleUSBDevices(\"btrfs\")'> Show USB drives</label></div><div style='margin-top:8px'><input type='submit' class='button danger' value='Create (DANGEROUS)'> <button type='button' class='button secondary' onclick=\"closeModal('modal_btrfs')\">Cancel</button></div></form></div></div>"
        )
        modal_md=(
            "<div class='modal' id='modal_md' hidden><div class='panel'><div style='display:flex;justify-content:space-between;align-items:center'><h3>Create mdadm RAID (XFS)</h3><button class='close secondary' onclick=\"closeModal('modal_md')\">X</button></div>"
            f"<form method='post' action='/?storage=1'><input type='hidden' name='create_mdraid' value='1'><label>Name (mdX) <input name='md_name' value='md0'></label><label>Level <select name='md_level' class='enh'><option>0</option><option selected>1</option><option>5</option><option>6</option><option>10</option></select></label><label>Mountpoint <input name='mountpoint' value='/mnt/mdraid'></label><div style='margin-bottom:8px'><button type='button' class='button small' onclick='bulkWipeSelected(\"mdadm\")'>Wipe selected drives</button></div><div id='mdadm-devices-container' style='max-height:260px;overflow:auto'><div id='mdadm-devices-no-usb'>"
            + dev_rows_no_usb
            + f"</div><div id='mdadm-devices-all' style='display:none'>"
            + dev_rows_all
            + "</div></div><div class='devices-box'></div><div style='margin-top:8px'><label><input type='checkbox' id='mdadm-show-usb' onchange='toggleUSBDevices(\"mdadm\")'> Show USB drives</label></div><div style='margin-top:8px'><input type='submit' class='button danger' value='Create (DANGEROUS)'> <button type='button' class='button secondary' onclick=\"closeModal('modal_md')\">Cancel</button></div></form></div></div>"
        )
        md_status=self.md_status()
        md_rows=''
        for s in md_status.get('devices',[]):
            progress_display = ''
            if s.get('state', '') == 'active' and s.get('percent', 0) < 100:
                progress_display = f"<div style='display:flex;align-items:center;gap:8px'><div style='background:#222;border:1px solid #333;height:25px;position:relative;border-radius:4px;overflow:hidden;width:200px'><div style='position:absolute;left:0;top:0;bottom:0;width:{s['percent']}%;background:var(--accent);transition:width 0.3s'></div></div><div style='font-size:14px;min-width:40px'>{s['percent']}%</div></div>"
            
            md_rows+=(
                f"<tr id='md_{html.escape(s['name'])}'><td>{html.escape(s['name'])}</td><td style='min-width:160px'>{progress_display}</td><td class='state'>{html.escape(s.get('state',''))}</td><td class='eta'>{html.escape(s.get('eta',''))}</td><td class='speed'>{html.escape(s.get('speed',''))}</td><td style='overflow:visible;position:relative'><select name='speed' class='enh'><option value='pause'>pause</option><option value='normal' selected>normal</option><option value='fast'>fast</option></select></td><td><button class='small danger' onclick=\"if(confirm('Delete RAID array {html.escape(s['name'])}? This will destroy all data!')) {{ fetch('/delete_array', {{ method: 'POST', headers: {{'Content-Type': 'application/x-www-form-urlencoded'}}, body: 'type=mdadm&name={html.escape(s['name'])}' }}).then(() => location.reload()); }}\">Delete</button></td></tr>"
            )
        # Keep the table structure consistent with a blank Progress header when not syncing
        md_table=(
            "<h4>mdraid Sync</h4><table style='overflow:visible'><thead><tr>"
            "<th>Array</th><th>Progress</th><th>Status</th><th>ETA</th><th>Speed</th><th>Mode</th><th>Actions</th></tr></thead>"
            "<tbody style='overflow:visible'>" + md_rows + "</tbody></table>" if md_rows else ''
        )
        buttons=(
            "<p><a class='button modal-trigger' href='#' data-modal='modal_pool' role='button' onclick=\"var m=document.getElementById('modal_pool');if(m){m.hidden=false;m.style.display='flex';}return false;\">New Pool</a> "
            "<a class='button modal-trigger' href='#' data-modal='modal_btrfs' role='button' onclick=\"var m=document.getElementById('modal_btrfs');if(m){m.hidden=false;m.style.display='flex';}return false;\">New BTRFS RAID</a> "
            "<a class='button modal-trigger' href='#' data-modal='modal_md' role='button' onclick=\"var m=document.getElementById('modal_md');if(m){m.hidden=false;m.style.display='flex';}return false;\">New mdadm RAID</a></p>"
        )
        
        # Active progress blocks for RAID creation
        prog_blocks=''
        for pid,data in list(PROGRESS.items()):
            st=data.get('status'); pct=data.get('pct',0); msgp=html.escape(data.get('msg',''))
            if st in ('done','error') and (time.time()-data.get('ts',time.time()))>30:
                continue
            # Only show RAID-related progress on storage page
            if 'raid' in msgp.lower() or 'mdadm' in msgp.lower() or 'btrfs' in msgp.lower():
                # Create visual progress bar
                progress_bar = f"<div style='width:200px;height:16px;background:#ddd;border:1px solid #999;display:inline-block;vertical-align:middle;margin:0 6px'><div style='width:{pct}%;height:100%;background:{('#4CAF50' if st=='done' else '#ff6b6b' if st=='error' else '#2196F3')};transition:width 0.3s'></div></div>"
                prog_blocks+=f"<div class='inline-note' style='margin:4px 0;padding:8px;border:1px solid #ddd;border-radius:4px'>[{pid}] {st} {progress_bar} {pct:.1f}% {msgp}</div>"
        
        return (
            f"<div class='card'><h3>Storage</h3>{msg}{prog_blocks}<h4>Existing Pools</h4><ul>{pools_list}</ul>{existing_raids_html}{buttons}{md_table}<p class='inline-note'>RAID creation destroys data on selected devices.</p></div>"
            + modal_pool + modal_btrfs + modal_md +
            """<script>
            // Auto-refresh RAID progress every 10 seconds if there are active operations
            if(document.querySelector('.inline-note [style*="width:"]')) {
                setTimeout(() => {
                    if(window.location.pathname === '/' && window.location.search.includes('storage=1')) {
                        window.location.reload();
                    }
                }, 10000);
            }
            </script>"""
        )

    def block_devices(self):
        devices=[]
        # Get mounted devices and RAID members to filter out
        mounted_devices = set()
        raid_devices = set()
        
        try:
            # Get mounted devices
            with open('/proc/mounts') as f:
                for line in f:
                    parts = line.split()
                    if len(parts) >= 1 and parts[0].startswith('/dev/'):
                        # Add base device (e.g., /dev/sda1 -> /dev/sda)
                        dev = parts[0]
                        mounted_devices.add(dev)
                        # Also add the base device for partitions
                        import re
                        base_match = re.match(r'(/dev/[a-z]+)', dev)
                        if base_match:
                            mounted_devices.add(base_match.group(1))
        except Exception:
            pass
        
        try:
            # Get RAID member devices from /proc/mdstat
            with open('/proc/mdstat') as f:
                content = f.read()
                for line in content.splitlines():
                    if 'active' in line and 'raid' in line:
                        # Extract device names from lines like: md0 : active raid1 sdb[1] sda[0]
                        parts = line.split()
                        for part in parts:
                            if '[' in part and ']' in part:
                                dev_name = part.split('[')[0]
                                raid_devices.add(f'/dev/{dev_name}')
        except Exception:
            pass
        
        try:
            # Get BTRFS member devices
            result = subprocess.run(['sudo','btrfs', 'filesystem', 'show'], capture_output=True, text=True, timeout=5)
            if result.returncode == 0:
                for line in result.stdout.splitlines():
                    if 'devid' in line and '/dev/' in line:
                        # Extract device path from lines like: devid    1 size 20.00GiB used 18.00GiB path /dev/sdb
                        parts = line.split()
                        for part in parts:
                            if part.startswith('/dev/'):
                                raid_devices.add(part)
                                # Also add base device for partitions
                                import re
                                base_match = re.match(r'(/dev/[a-z]+)', part)
                                if base_match:
                                    raid_devices.add(base_match.group(1))
                                break
        except Exception:
            pass
        
        try:
            import json as _json
            out = subprocess.check_output(['sudo', 'lsblk','-J','-b','-o','NAME,SIZE,MODEL,SERIAL,TYPE,TRAN,MOUNTPOINT'], text=True)
            data=_json.loads(out)
            for b in data.get('blockdevices',[]):
                if b.get('type')!='disk': continue
                device_path = '/dev/' + b.get('name')
                
                # Skip if device is mounted or part of RAID
                if device_path in mounted_devices or device_path in raid_devices:
                    continue
                
                # Also check if any partition is mounted
                has_mounted_partition = False
                if 'children' in b:
                    for child in b['children']:
                        child_path = '/dev/' + child.get('name')
                        if child_path in mounted_devices or child.get('mountpoint'):
                            has_mounted_partition = True
                            break
                
                if has_mounted_partition:
                    continue
                
                size=int(b.get('size') or 0)
                devices.append({'name':b.get('name'), 'path':device_path, 'model':b.get('model') or '', 'serial':b.get('serial') or '', 'size':size, 'size_h':human_bytes(size), 'tran':b.get('tran') or ''})
        except Exception:
            # fallback simple scan
            try:
                for d in os.listdir('/dev'):
                    if re.match(r'^(sd[a-z]+|nvme\d+n\d+)$',d):
                        path='/dev/'+d
                        # Skip mounted or RAID devices
                        if path in mounted_devices or path in raid_devices:
                            continue
                        try: size=os.path.getsize(path)
                        except Exception: size=0
                        devices.append({'name':d,'path':path,'model':'','serial':'','size':size,'size_h':human_bytes(size),'tran':''})
            except Exception:
                pass
        return devices

    def check_qemu_hyperv_support(self):
        """Check if QEMU supports Hyper-V enlightenments"""
        try:
            # Get QEMU capabilities from libvirt
            caps_xml = self.conn.getCapabilities()
            import xml.etree.ElementTree as ET
            caps_root = ET.fromstring(caps_xml)
            
            # Check for KVM support
            kvm_guests = caps_root.findall('.//guest/arch[@name="x86_64"]/domain[@type="kvm"]')
            if not kvm_guests:
                return False, "KVM not available"
            
            # Try to check QEMU binary capabilities
            qemu_binary = '/usr/libexec/qemu-kvm'
            if not os.path.exists(qemu_binary):
                # Try alternative paths
                for alt_path in ['/usr/bin/qemu-system-x86_64', '/usr/bin/kvm']:
                    if os.path.exists(alt_path):
                        qemu_binary = alt_path
                        break
                else:
                    return False, "QEMU binary not found"
            
            # Check if QEMU supports basic Hyper-V features
            try:
                result = subprocess.run([qemu_binary, '-cpu', 'help'], 
                                      capture_output=True, text=True, timeout=10)
                if result.returncode == 0 and 'hv-relaxed' in result.stdout:
                    return True, "Hyper-V enlightenments supported"
                else:
                    return False, "Hyper-V enlightenments not supported by QEMU"
            except Exception:
                # Fallback: assume basic support if we can't check
                return True, "Unable to verify, assuming basic support"
                
        except Exception as e:
            return False, f"Error checking QEMU capabilities: {e}"

    def get_qemu_cpu_models(self):
        """Get available CPU models from QEMU, filtered by host CPU type"""
        cpu_models = [
            ('host-model', 'Host Model (Recommended)'),
            ('host-passthrough', 'Host Passthrough (Maximum Performance)')
        ]
        
        try:
            # Detect host CPU type
            host_cpu_vendor = None
            try:
                with open('/proc/cpuinfo', 'r') as f:
                    for line in f:
                        if line.startswith('vendor_id'):
                            vendor = line.split(':')[1].strip()
                            if 'Intel' in vendor or 'GenuineIntel' in vendor:
                                host_cpu_vendor = 'intel'
                            elif 'AMD' in vendor or 'AuthenticAMD' in vendor:
                                host_cpu_vendor = 'amd'
                            break
            except Exception:
                # Fallback: try lscpu
                try:
                    result = subprocess.run(['lscpu'], capture_output=True, text=True, timeout=5)
                    if 'Intel' in result.stdout:
                        host_cpu_vendor = 'intel'
                    elif 'AMD' in result.stdout:
                        host_cpu_vendor = 'amd'
                except Exception:
                    pass
            
            # Find QEMU binary
            qemu_binary = '/usr/libexec/qemu-kvm'
            if not os.path.exists(qemu_binary):
                for alt_path in ['/usr/bin/qemu-system-x86_64', '/usr/bin/kvm']:
                    if os.path.exists(alt_path):
                        qemu_binary = alt_path
                        break
                else:
                    return cpu_models
            
            # Get CPU models from QEMU
            result = subprocess.run([qemu_binary, '-cpu', 'help'], 
                                  capture_output=True, text=True, timeout=10)
            
            if result.returncode == 0:
                models = []
                for line in result.stdout.splitlines():
                    line = line.strip()
                    # Skip empty lines, headers, and special entries
                    if not line or line.startswith('Available') or line.startswith('x86') or line.startswith('---'):
                        continue
                    
                    # Extract CPU model name (first word before space or description)
                    parts = line.split()
                    if parts and not parts[0].startswith('[') and not parts[0].startswith('('):
                        model_name = parts[0]
                        # Skip if it's already in our special modes
                        if model_name not in ['host-model', 'host-passthrough', 'max']:
                            models.append(model_name)
                
                # Filter models based on host CPU vendor
                filtered_models = []
                for model in sorted(set(models)):
                    model_lower = model.lower()
                    if host_cpu_vendor == 'intel':
                        # Include Intel models and generic models
                        if ('intel' in model_lower or 'core' in model_lower or 
                            'pentium' in model_lower or 'xeon' in model_lower or
                            'atom' in model_lower or 'celeron' in model_lower or
                            # Include some generic/older models that work on Intel
                            model_lower in ['qemu64', 'qemu32', 'kvm64', 'kvm32', 'coreduo', 'n270']):
                            filtered_models.append(model)
                    elif host_cpu_vendor == 'amd':
                        # Include AMD models and generic models
                        if ('amd' in model_lower or 'opteron' in model_lower or 
                            'athlon' in model_lower or 'phenom' in model_lower or
                            'ryzen' in model_lower or 'epyc' in model_lower or
                            # Include some generic/older models that work on AMD
                            model_lower in ['qemu64', 'qemu32', 'kvm64', 'kvm32']):
                            filtered_models.append(model)
                    else:
                        # Unknown vendor - include generic models only
                        if model_lower in ['qemu64', 'qemu32', 'kvm64', 'kvm32']:
                            filtered_models.append(model)
                
                # Add filtered models to the list
                for model in filtered_models:
                    cpu_models.append((f'custom:{model}', f'{model}'))
                    
        except Exception as e:
            logger.warning(f"Could not get QEMU CPU models: {e}")
        
        return cpu_models

    def get_safe_hyperv_features(self):
        """Get a safe set of Hyper-V features that should work on most systems"""
        return '''<features>
    <acpi/>
    <apic/>
    <hyperv>
        <relaxed state='on'/>
        <vapic state='on'/>
        <spinlocks state='on' retries='8191'/>
    </hyperv>
    <kvm>
        <hidden state='on'/>
    </kvm>
</features>'''

    def get_full_hyperv_features(self):
        """Get full Hyper-V features for optimal Windows performance"""
        return '''<features>
    <acpi/>
    <apic/>
    <hyperv>
        <relaxed state='on'/>
        <vapic state='on'/>
        <spinlocks state='on' retries='8191'/>
        <vpindex state='on'/>
        <runtime state='on'/>
        <synic state='on'/>
        <stimer state='on'/>
        <reset state='on'/>
        <vendor_id state='on' value='KVM Hv'/>
        <frequencies state='on'/>
        <reenlightenment state='on'/>
        <tlbflush state='on'/>
        <ipi state='on'/>
        <evmcs state='on'/>
    </hyperv>
    <kvm>
        <hidden state='on'/>
    </kvm>
</features>'''

    def md_status(self):
        result={'devices':[]}
        try:
            with open('/proc/mdstat') as f:
                lines=f.read().splitlines()
            current=None
            for line in lines:
                if not line.strip(): continue
                if line.startswith('Personalities') or line.startswith('unused'): continue
                if not line.startswith(' '):
                    parts=line.split()
                    name=parts[0]
                    state=' '.join(parts[2:])
                    current={'name':name,'state':state,'percent':0.0,'eta':'','speed':''}
                    result['devices'].append(current)
                else:
                    if current and any(k in line for k in ('recovery','resync','rebuild')):
                        m=re.search(r'(\d+\.\d+)%',line)
                        if m: current['percent']=float(m.group(1))
                        m2=re.search(r'ETA\s+([^\s]+)',line)
                        if m2: current['eta']=m2.group(1)
                        m3=re.search(r'(\d+\.?\d*[KMG]B?/s)',line)
                        if m3: current['speed']=m3.group(1)
        except Exception:
            pass
        return result

    def page_btrfs(self, lv:LV, form):
        msg=""
        # collect btrfs mounts and devices
        mounts=[]  # (mountpoint, device)
        try:
            with open('/proc/mounts') as f:
                for line in f:
                    parts=line.split()
                    if len(parts)>=3 and parts[2]=='btrfs':
                        mounts.append((parts[1], parts[0]))
        except Exception as e:
            msg+=f"<div class='inline-note'>Failed reading mounts: {html.escape(str(e))}</div>"
        if form and 'create_subvol' in form:
            try:
                parent=form.get('parent_mount',[''])[0]; sub=form.get('subvol',[''])[0]; mnt=form.get('mountpoint',[''])[0]; addfstab=form.get('add_fstab',['0'])[0]=='1'
                if not parent or not sub or not mnt: raise RuntimeError('Missing fields')
                # create subvolume
                subprocess.check_call(['sudo', 'btrfs','subvolume','create', os.path.join(parent,sub)])
                os.makedirs(mnt, exist_ok=True)
                # find device for parent
                dev=''
                for mp,dv in mounts:
                    if mp==parent: dev=dv; break
                if not dev: raise RuntimeError('Device for parent not found')
                mount_opts=f"noatime,discard,ssd,compress=zstd,subvol={sub},nofail"
                subprocess.check_call(['sudo', 'mount','-o',mount_opts,dev,mnt])
                if addfstab:
                    # attempt to get UUID
                    try:
                        out=subprocess.check_output(['sudo', 'blkid','-s','UUID','-o','value',dev], text=True).strip()
                        if out:
                            entry=f"UUID={out} {mnt} btrfs {mount_opts} 0 0\n"
                            with open('/etc/fstab','a') as f: f.write(entry)
                    except Exception as e2:
                        msg+=f"<div class='inline-note'>fstab UUID lookup failed: {html.escape(str(e2))}</div>"
                msg+=f"<div class='inline-note'>Subvolume {html.escape(sub)} created & mounted.</div>"
            except Exception as e:
                msg+=f"<div class='inline-note'>{html.escape(str(e))}</div>"
        mount_rows=''.join(f"<tr><td>{html.escape(mp)}</td><td>{html.escape(dev)}</td></tr>" for mp,dev in mounts)
        mount_table=f"<table><thead><tr><th>Mountpoint</th><th>Device</th></tr></thead><tbody>{mount_rows}</tbody></table>" if mounts else '<p>No btrfs mounts detected.</p>'
        parent_opts=''.join(f"<option value='{html.escape(mp)}'>{html.escape(mp)}</option>" for mp,_ in mounts)
        form_html=f"""<h4>Create BTRFS Subvolume</h4><form method='post'><input type='hidden' name='create_subvol' value='1'><label>Parent Mount <select name='parent_mount'>{parent_opts}</select></label><label>Subvolume Name <input name='subvol'></label><label>Mountpoint <input name='mountpoint' value='/mnt/subvol'></label><label><input type='checkbox' name='add_fstab' value='1'> Add to fstab</label><input type='submit' class='small' value='Create & Mount'></form><p class='inline-note'>Adds fstab entry with noatime,discard,ssd,compress=zstd,nofail.</p>"""
        return f"<div class='card'><h3>BTRFS</h3>{msg}{mount_table}{form_html}<p><a class='button secondary' href='/'>Back</a></p></div>"
    def page_hardware(self, lv:LV):
        # CPU model
        cpu_model='?'; cores=0
        try:
            with open('/proc/cpuinfo') as f:
                for line in f:
                    if line.startswith('model name') and cpu_model=='?': cpu_model=line.split(':',1)[1].strip()
                    if line.startswith('processor'):
                        cores+=1
        except Exception: pass
        mem_total=0
        try:
            with open('/proc/meminfo') as f:
                for line in f:
                    if line.startswith('MemTotal:'): mem_total=int(line.split()[1])*1024
        except Exception: pass
        pci_rows=''.join(f"<tr><td>{html.escape(d['full'])}</td><td>{html.escape(d['vendor'])}</td><td>{html.escape(d['device'])}</td><td>{html.escape(d.get('group',''))}</td></tr>" for d in lv.free_pci_devices()) or '<tr><td colspan=4><em>None</em></td></tr>'
        # block devices
        bdevs=self.block_devices()
        disk_rows=''.join(f"<tr><td>{html.escape(b['name'])}</td><td>{html.escape(b['model'] or '-')}</td><td>{html.escape(b['serial'] or '-')}</td><td>{html.escape(b['tran'] or '-')}</td><td>{html.escape(b['size_h'])}</td></tr>" for b in bdevs) or '<tr><td colspan=5><em>None</em></td></tr>'
        return (f"<div class='card'><h3>Hardware</h3><p><strong>CPU:</strong> {html.escape(cpu_model)} ({cores} cores)</p><p><strong>Memory Total:</strong> {human_bytes(mem_total)}</p>"
                f"<h4>PCI (Isolated IOMMU single-device groups)</h4><table><thead><tr><th>Address</th><th>Vendor</th><th>Device</th><th>Group</th></tr></thead><tbody>{pci_rows}</tbody></table>"
                f"<h4>Block Devices</h4><table><thead><tr><th>Name</th><th>Model</th><th>Serial</th><th>Bus</th><th>Size</th></tr></thead><tbody>{disk_rows}</tbody></table></div>")

    def page_performance(self):
        return ("<div class='card' id='host_perf'><h3>Performance</h3>"
                "<div style='max-width:420px'><strong>Host CPU</strong><div class='meter'><div class='fill host_cpu_fill' style='width:0%'></div></div><div class='inline-note cpu_val'>-</div></div>"
                "<div style='max-width:420px'><strong>Host Memory</strong><div class='meter alt'><div class='fill host_mem_fill' style='width:0%'></div></div><div class='inline-note mem_val'>-</div></div>"
                "<h4>Mounted Data Filesystems IO (KB/s)</h4><table><thead><tr><th>Mount</th><th>Device</th><th>Read</th><th>Write</th></tr></thead><tbody class='disks'><tr><td colspan='4'><em>Loading...</em></td></tr></tbody></table></div>")

    # Stats helpers
    def vm_stats(self, lv:LV):
        now=time.time()
        res=[]
        for d in lv.list_domains():
            try:
                # Only collect stats for running VMs - skip storage calculation for performance
                if not d.isActive():
                    res.append({'name':d.name(),'cpu':0,'mem_used':0,'mem_max':0,'mem_used_h':'0 B','mem_max_h':'0 B','mem_pct':0,'rd_kbps':0,'wr_kbps':0,'storage':0,'storage_h':'-'})
                    continue
                    
                info=d.info()  # (state, maxMem, memory, nrVirtCpu, cpuTime)
                state, maxMem, mem_available, vcpus, cpu_time=info[0], info[1]*1024, info[2]*1024, info[3], info[4]  # cpu_time in ns
                
                # Get actual memory usage via dommemstat (RSS value)
                mem_used = mem_available  # fallback
                try:
                    mem_stats = d.memoryStats()
                    if 'rss' in mem_stats:
                        mem_used = mem_stats['rss'] * 1024  # Convert KB to bytes
                except Exception:
                    pass
                prev=VM_PREV.get(d.name())
                cpu_pct=0.0; rd_kbps=0.0; wr_kbps=0.0
                
                # Calculate CPU percentage properly
                if prev:
                    dt = now - prev['ts']
                    if dt > 0:
                        # CPU time difference in nanoseconds
                        cpu_time_diff = cpu_time - prev['cpu_time_ns']
                        # Convert to seconds and calculate percentage of allocated CPU capacity
                        # cpu_time is cumulative CPU time used by all vCPUs
                        # dt * vcpus * 1e9 = total possible CPU nanoseconds for all vCPUs in time period
                        cpu_pct = (cpu_time_diff / (dt * vcpus * 1e9)) * 100
                        cpu_pct = max(0, min(100, cpu_pct))  # Clamp between 0-100%
                # Get disk I/O stats using iotop-like method for VM's virtual disks
                rd_bytes=0; wr_bytes=0
                try:
                    # Get QEMU process PID for this VM
                    vm_pid = None
                    try:
                        import subprocess
                        # Find QEMU process for this VM
                        result = subprocess.run(['pgrep', '-f', f'qemu.*{d.name()}'], 
                                              capture_output=True, text=True, timeout=2)
                        if result.returncode == 0 and result.stdout.strip():
                            vm_pid = int(result.stdout.strip().split('\n')[0])
                    except Exception:
                        pass
                    
                    if vm_pid:
                        # Read /proc/[pid]/io for actual disk I/O (like iotop)
                        try:
                            with open(f'/proc/{vm_pid}/io', 'r') as f:
                                for line in f:
                                    if line.startswith('read_bytes:'):
                                        rd_bytes = int(line.split(':')[1].strip())
                                    elif line.startswith('write_bytes:'):
                                        wr_bytes = int(line.split(':')[1].strip())
                        except Exception:
                            pass
                except Exception:
                    pass
                
                # Calculate I/O rates
                if prev:
                    dt = now - prev['ts']
                    if dt > 0:
                        dr = rd_bytes - prev.get('rd_bytes', rd_bytes)
                        dw = wr_bytes - prev.get('wr_bytes', wr_bytes)
                        rd_kbps = dr / 1024 / dt
                        wr_kbps = dw / 1024 / dt
                VM_PREV[d.name()]={'cpu_time_ns':cpu_time,'ts':now,'rd_bytes':rd_bytes,'wr_bytes':wr_bytes}
                mem_pct=(mem_used/maxMem*100) if maxMem>0 else 0
                # Skip storage calculation for performance - dashboard uses server-rendered values
                res.append({'name':d.name(),'cpu':cpu_pct,'mem_used':mem_used,'mem_max':maxMem,'mem_used_h':human_bytes(mem_used),'mem_max_h':human_bytes(maxMem),'mem_pct':mem_pct,'rd_kbps':rd_kbps,'wr_kbps':wr_kbps,'storage':0,'storage_h':'-'})
            except Exception:
                # For any error, provide default values
                res.append({'name':d.name(),'cpu':0,'mem_used':0,'mem_max':0,'mem_used_h':'0 B','mem_max_h':'0 B','mem_pct':0,'rd_kbps':0,'wr_kbps':0,'storage':0,'storage_h':'-'})
        return res

    def get_system_io(self):
        """
        Parse /proc/[pid]/io for all processes to get system-wide I/O statistics.
        Returns filesystem I/O rates in KB/s, matching iotop semantics:
        - Filesystem Read/Write: sum of read_bytes/write_bytes (Actual DISK READ/WRITE in iotop)
        """
        total_read_bytes = 0  # Filesystem read (Actual DISK READ)
        total_write_bytes = 0  # Filesystem write (Actual DISK WRITE)
        
        try:
            import os
            # Iterate through all process directories in /proc
            for pid_dir in os.listdir('/proc'):
                if not pid_dir.isdigit():
                    continue
                    
                try:
                    with open(f'/proc/{pid_dir}/io', 'r') as f:
                        for line in f:
                            if line.startswith('read_bytes:'):
                                total_read_bytes += int(line.split()[1])
                            elif line.startswith('write_bytes:'):
                                total_write_bytes += int(line.split()[1])
                except (FileNotFoundError, PermissionError, ValueError):
                    # Process may have exited or we don't have permission
                    continue
        except Exception:
            # If anything fails, return zeros
            return {
                'phys_rd_kbps': 0.0,
                'phys_wr_kbps': 0.0
            }
        
        # Calculate rates if we have previous data
        now = time.time()
        rates = {
            'phys_rd_kbps': 0.0,
            'phys_wr_kbps': 0.0
        }
        
        # Use global HOST_PREV for persistence between calls
        if 'io_stats' in HOST_PREV and HOST_PREV['io_stats'].get('ts'):
            dt = now - HOST_PREV['io_stats']['ts']
            if dt > 0:
                # Calculate rates in KB/s
                rates['phys_rd_kbps'] = max(0, (total_read_bytes - HOST_PREV['io_stats'].get('read_bytes', 0)) / 1024 / dt)
                rates['phys_wr_kbps'] = max(0, (total_write_bytes - HOST_PREV['io_stats'].get('write_bytes', 0)) / 1024 / dt)
        
        # Store current values for next iteration
        HOST_PREV['io_stats'] = {
            'read_bytes': total_read_bytes,
            'write_bytes': total_write_bytes,
            'ts': now
        }
        
        return rates

    def host_stats(self):
        now=time.time()
        # CPU
        cpu_pct=0.0
        try:
            with open('/proc/stat') as f:
                first=f.readline().split()
            if first[0]=='cpu':
                nums=list(map(int,first[1:]))
                idle=nums[3]+nums[4]; total=sum(nums)
                prev=HOST_PREV.get('cpu')
                if prev:
                    didle=idle-prev['idle']; dtotal=total-prev['total']
                    if dtotal>0: cpu_pct=(1 - didle/dtotal)*100
                HOST_PREV['cpu']={'idle':idle,'total':total}
        except Exception: pass
        # Memory
        mem_total=0; mem_avail=0
        try:
            with open('/proc/meminfo') as f:
                for line in f:
                    if line.startswith('MemTotal:'): mem_total=int(line.split()[1])*1024
                    elif line.startswith('MemAvailable:'): mem_avail=int(line.split()[1])*1024
        except Exception: pass
        mem_used=mem_total-mem_avail; mem_pct=(mem_used/mem_total*100) if mem_total>0 else 0
        
        # Simple disk I/O calculation - sum all block devices
        total_rd_kbps = 0.0
        total_wr_kbps = 0.0
        disks = []
        
        try:
            current_stats = {}
            with open('/proc/diskstats') as f:
                for line in f:
                    parts = line.split()
                    if len(parts) < 14: continue
                    
                    device = parts[2]
                    
                    # Skip virtual/loopback devices and partitions
                    if device.startswith(('loop', 'ram', 'dm-', 'sr')):
                        continue
                    # Skip partitions (devices with numbers, except nvme which is special)
                    if device[-1].isdigit() and not (device.startswith('nvme') and 'n' in device and 'p' not in device):
                        continue
                        
                    rd_sectors = int(parts[5])
                    wr_sectors = int(parts[9])
                    current_stats[device] = {
                        'rd': rd_sectors * 512,  # convert to bytes
                        'wr': wr_sectors * 512
                    }
            
            # Calculate rates if we have previous data
            if HOST_PREV.get('ts') and HOST_PREV['ts'] > 0:
                dt = now - HOST_PREV['ts']
                if dt > 0:
                    for device, stats in current_stats.items():
                        prev_key = f"disk_{device}"
                        if prev_key in HOST_PREV['disk']:
                            prev = HOST_PREV['disk'][prev_key]
                            rd_diff = stats['rd'] - prev['rd']
                            wr_diff = stats['wr'] - prev['wr']
                            
                            if rd_diff >= 0 and wr_diff >= 0:  # Sanity check
                                rd_rate = rd_diff / 1024 / dt  # KB/s
                                wr_rate = wr_diff / 1024 / dt  # KB/s
                                
                                total_rd_kbps += rd_rate
                                total_wr_kbps += wr_rate
                                
                                disks.append({
                                    'mount': device,
                                    'dev': device,
                                    'rd_kbps': rd_rate,
                                    'wr_kbps': wr_rate
                                })
            
            # Store current stats for next iteration
            for device, stats in current_stats.items():
                HOST_PREV['disk'][f"disk_{device}"] = stats
                
        except Exception as e:
            # If anything fails, provide zero values
            total_rd_kbps = total_wr_kbps = 0.0
            disks = []
        # Get filesystem and physical I/O statistics
        io_stats = self.get_system_io()
        
        HOST_PREV['ts']=now
        return {
            'cpu_pct': cpu_pct,
            'mem_used': mem_used,
            'mem_total': mem_total,
            'mem_pct': mem_pct,
            'mem_used_h': human_bytes(mem_used),
            'mem_total_h': human_bytes(mem_total),
            'disks': disks,
            'total_rd_kbps': total_rd_kbps,
            'total_wr_kbps': total_wr_kbps,
            # New iotop-style I/O metrics
            'phys_rd_kbps': io_stats['phys_rd_kbps'],
            'phys_wr_kbps': io_stats['phys_wr_kbps']
        }

    def handle_vnc_websocket(self, domain_name: str, lv: LV):
        """Handle WebSocket VNC proxy connection"""
        try:
            logger.info(f"Starting VNC WebSocket for {domain_name}")
            
            # Check if this is a WebSocket upgrade request
            upgrade = self.headers.get('Upgrade', '').lower()
            connection = self.headers.get('Connection', '').lower()
            
            logger.info(f"Headers: Upgrade='{upgrade}', Connection='{connection}'")
            
            if upgrade != 'websocket' or 'upgrade' not in connection:
                logger.error(f"Invalid WebSocket headers: Upgrade='{upgrade}', Connection='{connection}'")
                self._send('Bad Request - Not a WebSocket upgrade', 400)
                return
                
            # Get VNC port for the domain
            d = lv.get_domain(domain_name)
            if not d.isActive():
                logger.error(f"VM {domain_name} is not running")
                self._send('VM not running', 400)
                return
                
            xml = d.XMLDesc(0)
            import xml.etree.ElementTree as ET
            root = ET.fromstring(xml)
            graphics = root.find('.//devices/graphics[@type="vnc"]')
            
            if graphics is None:
                logger.error(f"VNC not configured for {domain_name}")
                self._send('VNC not configured', 400)
                return
                
            vnc_port = graphics.get('port', '-1')
            vnc_host = graphics.get('listen', '127.0.0.1')
            
            # Log VNC configuration for debugging
            logger.info(f"VNC config for {domain_name}: port={vnc_port}, host={vnc_host}, autoport={graphics.get('autoport')}")
            
            # Also check for any display-related attributes
            for attr in graphics.attrib:
                logger.info(f"VNC attribute {attr}={graphics.get(attr)}")
            
            logger.info(f"VNC server for {domain_name}: {vnc_host}:{vnc_port}")
            
            if vnc_port == '-1':
                logger.error(f"VNC port not allocated for {domain_name}")
                self._send('VNC port not allocated', 400)
                return
            
            # Test VNC connection first
            try:
                test_socket = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
                test_socket.settimeout(5.0)
                test_socket.connect((vnc_host, int(vnc_port)))
                test_socket.close()
                logger.info(f"VNC server test connection successful for {domain_name}")
            except Exception as e:
                logger.error(f"Cannot connect to VNC server {vnc_host}:{vnc_port} for {domain_name}: {e}")
                self._send('VNC server unreachable', 503)
                return
                
            # Perform WebSocket handshake
            websocket_key = self.headers.get('Sec-WebSocket-Key')
            if not websocket_key:
                logger.error(f"Missing Sec-WebSocket-Key header")
                self._send('Missing WebSocket key', 400)
                return
                
            logger.info(f"WebSocket key: {websocket_key}")
                
            # Generate WebSocket accept key
            import base64
            import hashlib
            magic_string = '258EAFA5-E914-47DA-95CA-C5AB0DC85B11'
            accept_key = base64.b64encode(
                hashlib.sha1((websocket_key + magic_string).encode()).digest()
            ).decode()
            
            logger.info(f"Generated accept key: {accept_key}")
            
            # Send WebSocket handshake response - simpler version
            response_lines = [
                'HTTP/1.1 101 Switching Protocols',
                'Upgrade: websocket', 
                'Connection: Upgrade',
                f'Sec-WebSocket-Accept: {accept_key}',
                '', ''  # Empty line to end headers
            ]
            response = '\r\n'.join(response_lines)
            
            # Escape special characters outside f-string to avoid backslash issues
            escaped_response = response.replace(chr(13), '\\r').replace(chr(10), '\\n')
            logger.info(f"Sending WebSocket handshake response: {escaped_response}")
            
            # Send response through raw socket to avoid buffering issues
            raw_socket = self.connection
            raw_socket.sendall(response.encode())
            
            logger.info(f"WebSocket handshake sent for VNC {domain_name}")
            
            # Store the socket and prevent handler from closing it
            self.connection = None
            
            # Run VNC proxy in this thread - each HTTP request gets its own thread with ThreadingHTTPServer
            self._vnc_proxy_simple(raw_socket, vnc_host, int(vnc_port), domain_name)
            
        except Exception as e:
            logger.error(f"WebSocket VNC error: {e}")
            import traceback
            logger.error(f"Traceback: {traceback.format_exc()}")
            try:
                self._send('Internal Server Error', 500)
            except:
                pass

    def _vnc_proxy_simple(self, client_socket, vnc_host: str, vnc_port: int, domain_name: str):
        """Simple VNC proxy with proper WebSocket frame handling"""
        vnc_socket = None
        try:
            logger.info(f"Connecting to VNC server {vnc_host}:{vnc_port} for {domain_name}")
            
            # Connect to VNC server
            vnc_socket = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
            vnc_socket.settimeout(10.0)
            vnc_socket.connect((vnc_host, vnc_port))
            logger.info(f"VNC proxy connected successfully to {vnc_host}:{vnc_port} for {domain_name}")
            
            # Set timeouts for select
            vnc_socket.settimeout(0.1)
            client_socket.settimeout(0.1)
            
            # Data relay loop with proper WebSocket frame handling
            import select
            running = True
            
            logger.info(f"Starting VNC proxy loop for {domain_name}")
            
            while running:
                try:
                    ready_read, _, ready_error = select.select(
                        [client_socket, vnc_socket], [], [client_socket, vnc_socket], 1.0
                    )
                    
                    if ready_error:
                        logger.info(f"Socket error detected for {domain_name}")
                        break
                    
                    # Forward data from WebSocket client to VNC server
                    if client_socket in ready_read:
                        try:
                            ws_data = client_socket.recv(4096)
                            if not ws_data:
                                logger.info(f"WebSocket client disconnected for {domain_name}")
                                break
                                
                            logger.debug(f"Received {len(ws_data)} bytes from WebSocket client")
                            
                            # Decode WebSocket frame to get VNC data
                            vnc_data = self._decode_websocket_frame_fixed(ws_data)
                            if vnc_data:
                                logger.debug(f"Decoded {len(vnc_data)} bytes of VNC data from WebSocket frame")
                                vnc_socket.sendall(vnc_data)
                            
                        except socket.timeout:
                            continue
                        except (ConnectionResetError, BrokenPipeError) as e:
                            logger.info(f"Client connection lost for {domain_name}: {e}")
                            break
                        except Exception as e:
                            logger.error(f"Client data error for {domain_name}: {e}")
                            continue
                    
                    # Forward data from VNC server to WebSocket client  
                    if vnc_socket in ready_read:
                        try:
                            vnc_data = vnc_socket.recv(4096)
                            if not vnc_data:
                                logger.info(f"VNC server disconnected for {domain_name}")
                                break
                                
                            logger.debug(f"Received {len(vnc_data)} bytes from VNC server")
                            
                            # Encode VNC data as WebSocket frame
                            ws_frame = self._encode_websocket_frame_fixed(vnc_data)
                            if ws_frame:
                                logger.debug(f"Encoded {len(vnc_data)} bytes as {len(ws_frame)} byte WebSocket frame")
                                client_socket.sendall(ws_frame)
                            
                        except socket.timeout:
                            continue
                        except (ConnectionResetError, BrokenPipeError) as e:
                            logger.info(f"VNC connection lost for {domain_name}: {e}")
                            break
                        except Exception as e:
                            logger.error(f"VNC data error for {domain_name}: {e}")
                            continue
                            
                except KeyboardInterrupt:
                    logger.info(f"VNC proxy interrupted for {domain_name}")
                    break
                except Exception as e:
                    logger.error(f"VNC proxy loop error for {domain_name}: {e}")
                    break
                    
        except Exception as e:
            logger.error(f"VNC proxy setup error for {domain_name}: {e}")
            import traceback
            logger.error(f"Traceback: {traceback.format_exc()}")
        finally:
            if vnc_socket:
                try:
                    vnc_socket.close()
                    logger.info(f"VNC socket closed for {domain_name}")
                except:
                    pass
            try:
                client_socket.close()
                logger.info(f"WebSocket client socket closed for {domain_name}")
            except:
                pass
            logger.info(f"VNC proxy terminated for {domain_name}")

    def _vnc_proxy_fixed(self, client_socket, vnc_host: str, vnc_port: int, domain_name: str):
        """Fixed VNC proxy that properly handles WebSocket frames"""
        vnc_socket = None
        try:
            # Connect to VNC server
            vnc_socket = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
            vnc_socket.settimeout(10.0)
            vnc_socket.connect((vnc_host, vnc_port))
            logger.info(f"VNC proxy connected to {vnc_host}:{vnc_port} for {domain_name}")
            
            # Set non-blocking with timeouts
            vnc_socket.settimeout(0.1)
            client_socket.settimeout(0.1)
            
            # Use select for efficient I/O
            import select
            running = True
            
            while running:
                try:
                    ready_sockets, _, error_sockets = select.select(
                        [client_socket, vnc_socket], [], [client_socket, vnc_socket], 1.0
                    )
                    
                    if error_sockets:
                        logger.info(f"Socket error for {domain_name}")
                        break
                    
                    # Handle WebSocket -> VNC
                    if client_socket in ready_sockets:
                        try:
                            ws_data = client_socket.recv(8192)
                            if not ws_data:
                                logger.info(f"WebSocket client disconnected for {domain_name}")
                                break
                                
                            # Decode WebSocket frame to get VNC data
                            vnc_data = self._decode_websocket_frame_fixed(ws_data)
                            if vnc_data:
                                vnc_socket.sendall(vnc_data)
                        except (ConnectionResetError, BrokenPipeError):
                            logger.info(f"Client connection lost for {domain_name}")
                            break
                        except socket.timeout:
                            continue
                        except Exception as e:
                            logger.debug(f"Client data error for {domain_name}: {e}")
                            continue
                    
                    # Handle VNC -> WebSocket  
                    if vnc_socket in ready_sockets:
                        try:
                            vnc_data = vnc_socket.recv(8192)
                            if not vnc_data:
                                logger.info(f"VNC server disconnected for {domain_name}")
                                break
                                
                            # Encode as WebSocket frame
                            ws_frame = self._encode_websocket_frame_fixed(vnc_data)
                            if ws_frame:
                                client_socket.sendall(ws_frame)
                        except (ConnectionResetError, BrokenPipeError):
                            logger.info(f"VNC connection lost for {domain_name}")
                            break
                        except socket.timeout:
                            continue
                        except Exception as e:
                            logger.debug(f"VNC data error for {domain_name}: {e}")
                            continue
                            
                except KeyboardInterrupt:
                    break
                except Exception as e:
                    logger.error(f"VNC proxy error for {domain_name}: {e}")
                    break
                    
        except Exception as e:
            logger.error(f"VNC proxy setup error for {domain_name}: {e}")
        finally:
            if vnc_socket:
                try:
                    vnc_socket.close()
                except:
                    pass
            try:
                client_socket.close()
            except:
                pass
            logger.info(f"VNC proxy closed for {domain_name}")

    def _decode_websocket_frame_fixed(self, data):
        """Decode WebSocket frame - fixed version with debugging"""
        try:
            if len(data) < 2:
                logger.debug(f"WebSocket frame too short: {len(data)} bytes")
                return None
                
            byte1, byte2 = data[0], data[1]
            fin = bool(byte1 & 0x80)
            opcode = byte1 & 0x0F
            masked = bool(byte2 & 0x80)
            payload_len = byte2 & 0x7F
            
            logger.debug(f"WebSocket frame: FIN={fin}, opcode={opcode}, masked={masked}, payload_len={payload_len}")
            
            # Handle close frame
            if opcode == 0x8:
                logger.info("WebSocket close frame received")
                return None
            
            # Only handle binary and text frames for VNC
            if opcode not in [0x1, 0x2]:  # text or binary
                logger.debug(f"Ignoring WebSocket frame with opcode {opcode}")
                return None
                
            offset = 2
            
            # Extended payload length
            if payload_len == 126:
                if len(data) < offset + 2:
                    logger.debug("Incomplete extended payload length")
                    return None
                payload_len = int.from_bytes(data[offset:offset+2], 'big')
                offset += 2
            elif payload_len == 127:
                if len(data) < offset + 8:
                    logger.debug("Incomplete extended payload length (64-bit)")
                    return None
                payload_len = int.from_bytes(data[offset:offset+8], 'big')
                offset += 8
                
            logger.debug(f"Final payload length: {payload_len}")
                
            # Masking key
            if masked:
                if len(data) < offset + 4:
                    logger.debug("Incomplete masking key")
                    return None
                mask = data[offset:offset+4]
                offset += 4
                logger.debug(f"Mask: {[hex(b) for b in mask]}")
            else:
                mask = None
                
            # Extract payload
            if len(data) < offset + payload_len:
                logger.debug(f"Incomplete payload: need {offset + payload_len}, have {len(data)}")
                return None
                
            payload = data[offset:offset+payload_len]
            
            # Unmask if needed
            if mask:
                payload = bytes(payload[i] ^ mask[i % 4] for i in range(len(payload)))
                
            logger.debug(f"Decoded WebSocket payload: {len(payload)} bytes")
            return payload
            
        except Exception as e:
            logger.error(f"WebSocket decode error: {e}")
            return None

    def _encode_websocket_frame_fixed(self, data):
        """Encode data as WebSocket binary frame - fixed version"""
        try:
            frame = bytearray([0x82])  # FIN=1, opcode=binary
            
            data_len = len(data)
            if data_len < 126:
                frame.append(data_len)
            elif data_len < 65536:
                frame.append(126)
                frame.extend(data_len.to_bytes(2, 'big'))
            else:
                frame.append(127)
                frame.extend(data_len.to_bytes(8, 'big'))
                
            frame.extend(data)
            return bytes(frame)
            
        except Exception:
            return None
            
    def _vnc_proxy(self, vnc_host: str, vnc_port: int):
        """Proxy data between WebSocket and VNC server with proper frame handling"""
        vnc_socket = None
        try:
            # Connect to VNC server
            vnc_socket = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
            vnc_socket.connect((vnc_host, vnc_port))
            vnc_socket.settimeout(1.0)
            
            logger.info(f"Connected to VNC server at {vnc_host}:{vnc_port}")
            
            # Set socket to non-blocking for better handling
            self.connection.settimeout(0.1)
            
            # Handle bidirectional data flow
            running = True
            while running:
                try:
                    # Check for data from WebSocket client
                    try:
                        ws_data = self.connection.recv(4096)
                        if not ws_data:
                            logger.debug("WebSocket client disconnected")
                            break
                            
                        # Decode WebSocket frame and forward to VNC
                        vnc_data = self._decode_websocket_frame(ws_data)
                        if vnc_data:
                            vnc_socket.send(vnc_data)
                            logger.debug(f"Forwarded {len(vnc_data)} bytes to VNC server")
                    except socket.timeout:
                        pass
                    except ConnectionResetError:
                        logger.debug("WebSocket connection reset")
                        break
                    except Exception as e:
                        logger.debug(f"WebSocket receive error: {e}")
                        break
                    
                    # Check for data from VNC server
                    try:
                        vnc_data = vnc_socket.recv(4096)
                        if not vnc_data:
                            logger.debug("VNC server disconnected")
                            break
                            
                        # Encode as WebSocket frame and send to client
                        ws_frame = self._encode_websocket_frame(vnc_data)
                        if ws_frame:
                            self.connection.send(ws_frame)
                            logger.debug(f"Forwarded {len(vnc_data)} bytes to WebSocket client")
                    except socket.timeout:
                        pass
                    except ConnectionResetError:
                        logger.debug("VNC connection reset")
                        break
                    except Exception as e:
                        logger.debug(f"VNC receive error: {e}")
                        break
                        
                except KeyboardInterrupt:
                    logger.info("VNC proxy interrupted")
                    break
                except Exception as e:
                    logger.error(f"VNC proxy loop error: {e}")
                    break
                    
        except Exception as e:
            logger.error(f"VNC proxy error: {e}")
        finally:
            if vnc_socket:
                try:
                    vnc_socket.close()
                except:
                    pass
            logger.info("VNC proxy connection closed")
            
    def _vnc_proxy_with_socket(self, client_socket, vnc_host: str, vnc_port: int):
        """Proxy data between WebSocket and VNC server using raw socket"""
        vnc_socket = None
        loop_count = 0  # Initialize loop counter early
        try:
            # Connect to VNC server
            vnc_socket = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
            vnc_socket.connect((vnc_host, vnc_port))
            vnc_socket.settimeout(5.0)  # Longer timeout for VNC operations
            
            logger.info(f"VNC proxy connected to {vnc_host}:{vnc_port}")
            
            # Set client socket timeout longer to prevent premature disconnection
            client_socket.settimeout(1.0)
            
            # Initial VNC handshake - read version from server
            initial_data = vnc_socket.recv(12)  # "RFB 003.008\n"
            if initial_data:
                logger.info(f"VNC server version: {initial_data}")
                # Forward initial VNC data to client as WebSocket frame
                ws_frame = self._encode_websocket_frame(initial_data)
                if ws_frame:
                    try:
                        client_socket.send(ws_frame)
                        logger.info("Sent VNC server version to WebSocket client")
                    except (BrokenPipeError, ConnectionResetError) as e:
                        logger.warning(f"Client disconnected during initial handshake: {e}")
                        return
            else:
                logger.error("No initial data from VNC server")
                return
            
            # Handle bidirectional data flow
            running = True
            while running:
                loop_count += 1
                if loop_count % 1000 == 0:  # Reduce logging frequency
                    logger.debug(f"VNC proxy loop iteration {loop_count}")
                
                data_received = False
                
                try:
                    # Check for data from WebSocket client
                    try:
                        ws_data = client_socket.recv(4096)
                        if not ws_data:
                            logger.info("WebSocket client disconnected (no data)")
                            break
                            
                        data_received = True
                        logger.debug(f"Received {len(ws_data)} bytes from WebSocket client")
                        
                        # Decode WebSocket frame and forward to VNC
                        vnc_data = self._decode_websocket_frame(ws_data)
                        if vnc_data:
                            try:
                                vnc_socket.send(vnc_data)
                                logger.debug(f"Forwarded {len(vnc_data)} bytes to VNC server")
                            except (BrokenPipeError, ConnectionResetError) as e:
                                logger.info(f"VNC server disconnected: {e}")
                                break
                        else:
                            logger.debug("No VNC data after WebSocket decode (possibly ping/pong)")
                    except socket.timeout:
                        pass
                    except (ConnectionResetError, BrokenPipeError) as e:
                        logger.info(f"WebSocket connection lost: {e}")
                        break
                    except Exception as e:
                        logger.warning(f"WebSocket receive error: {e}")
                        break
                    
                    # Check for data from VNC server
                    try:
                        vnc_data = vnc_socket.recv(4096)
                        if not vnc_data:
                            logger.info("VNC server disconnected (no data)")
                            break
                            
                        data_received = True
                        logger.debug(f"Received {len(vnc_data)} bytes from VNC server")
                        
                        # Encode as WebSocket frame and send to client
                        ws_frame = self._encode_websocket_frame(vnc_data)
                        if ws_frame:
                            try:
                                client_socket.send(ws_frame)
                                logger.debug(f"Forwarded {len(vnc_data)} bytes to WebSocket client")
                            except (BrokenPipeError, ConnectionResetError) as e:
                                logger.info(f"WebSocket client disconnected: {e}")
                                break
                        else:
                            logger.warning("Failed to encode WebSocket frame")
                    except socket.timeout:
                        pass
                    except (ConnectionResetError, BrokenPipeError) as e:
                        logger.info(f"VNC connection lost: {e}")
                        break
                    except Exception as e:
                        logger.warning(f"VNC receive error: {e}")
                        break
                        
                    # If no data was received in this loop, small sleep to avoid busy waiting
                    if not data_received:
                        import time
                        time.sleep(0.01)  # 10ms sleep
                        
                except KeyboardInterrupt:
                    logger.info("VNC proxy interrupted by keyboard")
                    break
                except Exception as e:
                    logger.error(f"VNC proxy loop error: {e}")
                    break
                    
        except Exception as e:
            logger.error(f"VNC proxy setup error: {e}")
            import traceback
            logger.error(f"Traceback: {traceback.format_exc()}")
        finally:
            if vnc_socket:
                try:
                    vnc_socket.close()
                    logger.info("VNC socket closed")
                except:
                    pass
            try:
                client_socket.close()
                logger.info("WebSocket client socket closed")
            except:
                pass
            logger.info(f"VNC proxy with socket closed (processed {loop_count} loops)")
                
    def _decode_websocket_frame(self, data):
        """Decode WebSocket frame to extract payload"""
        try:
            if len(data) < 2:
                logger.debug(f"WebSocket frame too short: {len(data)} bytes")
                return None
                
            # Parse WebSocket frame
            byte1, byte2 = data[0], data[1]
            fin = bool(byte1 & 0b10000000)
            opcode = byte1 & 0b00001111
            masked = bool(byte2 & 0b10000000)
            payload_length = byte2 & 0b01111111
            
            logger.debug(f"WebSocket frame: fin={fin}, opcode={opcode}, masked={masked}, length={payload_length}")
            
            # Handle different opcodes
            if opcode == 0x8:  # Close frame
                logger.info("WebSocket close frame received")
                return None
            elif opcode == 0x9:  # Ping frame
                logger.debug("WebSocket ping frame received")
                return None
            elif opcode == 0xA:  # Pong frame
                logger.debug("WebSocket pong frame received")
                return None
            elif opcode not in [0x1, 0x2]:  # Text or Binary frame
                logger.debug(f"Ignoring WebSocket frame with opcode {opcode}")
                return None
                
            header_length = 2
            
            # Extended payload length
            if payload_length == 126:
                if len(data) < 4:
                    logger.debug("WebSocket frame truncated at extended length")
                    return None
                payload_length = int.from_bytes(data[2:4], 'big')
                header_length = 4
            elif payload_length == 127:
                if len(data) < 10:
                    logger.debug("WebSocket frame truncated at extended length 64-bit")
                    return None
                payload_length = int.from_bytes(data[2:10], 'big')
                header_length = 10
                
            # Masking key
            if masked:
                mask_start = header_length
                mask_end = mask_start + 4
                if len(data) < mask_end:
                    logger.debug("WebSocket frame truncated at masking key")
                    return None
                masking_key = data[mask_start:mask_end]
                payload_start = mask_end
            else:
                payload_start = header_length
                
            # Extract payload
            payload_end = payload_start + payload_length
            if len(data) < payload_end:
                logger.debug(f"WebSocket frame truncated: expected {payload_end} bytes, got {len(data)}")
                return None
                
            payload = data[payload_start:payload_end]
            
            # Unmask payload if masked
            if masked:
                payload = bytes(payload[i] ^ masking_key[i % 4] for i in range(len(payload)))
                
            logger.debug(f"WebSocket decoded payload: {len(payload)} bytes")
            return payload
            
        except Exception as e:
            logger.error(f"WebSocket decode error: {e}")
            return None
            
    def _encode_websocket_frame(self, data):
        """Encode data as WebSocket binary frame"""
        try:
            frame = bytearray()
            
            # First byte: FIN + opcode (binary = 0x2)
            frame.append(0x82)  # FIN=1, opcode=binary
            
            # Payload length
            data_length = len(data)
            if data_length < 126:
                frame.append(data_length)
            elif data_length < 65536:
                frame.append(126)
                frame.extend(data_length.to_bytes(2, 'big'))
            else:
                frame.append(127)
                frame.extend(data_length.to_bytes(8, 'big'))
                
            # Payload (server->client, no masking)
            frame.extend(data)
            
            return bytes(frame)
            
        except Exception as e:
            logger.debug(f"WebSocket encode error: {e}")
            return b''

def run():
    # Ensure directories exist
    os.makedirs(BACKUP_DIR, exist_ok=True)
    
    # Create server
    srv = ThreadingHTTPServer((HOST, PORT), Handler)
    
    # SSL support
    if SSL_CERT and SSL_KEY and os.path.exists(SSL_CERT) and os.path.exists(SSL_KEY):
        context = ssl.SSLContext(ssl.PROTOCOL_TLS_SERVER)
        context.load_cert_chain(SSL_CERT, SSL_KEY)
        srv.socket = context.wrap_socket(srv.socket, server_side=True)
        protocol = "https"
        logger.info(f"SSL enabled with cert: {SSL_CERT}")
    else:
        protocol = "http"
        if SSL_CERT or SSL_KEY:
            logger.warning("SSL certificate or key not found, falling back to HTTP")
    
    # Log startup information
    logger.info("=" * 60)
    logger.info("🚀 Enhanced VM Manager v2.0 Starting")
    logger.info("=" * 60)
    logger.info(f"🌐 Server: {protocol}://{HOST}:{PORT}")
    logger.info(f"🔐 Authentication: {'Enabled' if AUTH_PASSWORD else 'Disabled'}")
    logger.info(f"💾 Backup Directory: {BACKUP_DIR}")
    logger.info(f"🔍 Log Level: {LOG_LEVEL}")
    
    # Feature summary
    features = [
        "✅ VM Templates (Ubuntu, Debian, CentOS, Windows)",
        "✅ Cloud-Init Support",
        "✅ Snapshots & Backups",
        "✅ Bridge0 Networking",
        "✅ Performance Monitoring",
        "✅ Dark/Light Theme",
        "✅ REST API",
        "✅ Enhanced Security",
        "✅ RAID Creation with Disk Selection",
        "✅ Disk Wiping (wipefs)"
    ]
    
    logger.info("🎨 Available Features:")
    for feature in features:
        logger.info(f"   {feature}")
    
    logger.info("=" * 60)
    print(f"🌟 Enhanced VM Manager v2.0 running on {protocol}://{HOST}:{PORT}")
    print("   New features: Templates, Snapshots, Backups, Bridge0, Cloud-Init, SSL")
    print("   RAID: Clickable disk selection, wipefs support")
    print("   Dropdowns: All dropdowns now functional")
    print(f"   Authentication: {'Required' if AUTH_PASSWORD else 'Disabled'}")
    print("   Press Ctrl+C to stop")
    
    try:
        srv.serve_forever()
    except KeyboardInterrupt:
        logger.info("💤 Shutting down Enhanced VM Manager...")
        print("\n🛑 Enhanced VM Manager stopped")
        srv.server_close()

if __name__=='__main__': 
    run()
