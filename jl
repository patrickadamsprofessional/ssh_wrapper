#!/usr/bin/env python3
"""
jl: Modern SSH automation and login tool with extensibility, jump host, and logging support.
Inspired by jlogin, but designed for Python and modern network automation workflows.
"""

# jl: Modern SSH automation and login tool
# Resource files (config, inventory, jumps, etc.) are expected by default in the './resources/' directory.
# You can override with --config and --inventory flags.

VERSION = "1.0.0"

# =========================
# Imports
# =========================
import argparse
import os
import sys
import yaml
import pexpect
import getpass
import datetime
import stat
import hashlib
import time
import paramiko
import termios
import tty
import select
import fnmatch
from collections import OrderedDict
import socket
import tempfile
import random
import string

# =========================
# Argument Parsing Section
# =========================
def parse_args():
    """
    Parse command-line arguments for jl.
    Returns an argparse.Namespace with all options.
    """
    parser = argparse.ArgumentParser(description="Modern Python jlogin replacement with Nornir-style inventory.")
    # Target host (from inventory) - only one allowed
    parser.add_argument('host', help='Target host as defined in inventory (only one host per invocation)')
    # Command to run on remote host
    parser.add_argument('-c', '--command', help='Run a command on the remote host')
    # Command file to run
    parser.add_argument('-x', '--command-file', help='Run commands from a file')
    # Environment variable(s) for scripts
    parser.add_argument('-E', '--env', action='append', help='Set environment variable for scripts (VAR=VAL), can be used multiple times')
    # Environment file for scripts
    parser.add_argument('-e', '--env-file', help='Environment file for scripts')
    # Python script to run with session object
    parser.add_argument('-s', '--script', help='Python script to run with session object')
    # Global config file (logging, scrollback, etc.)
    parser.add_argument('-f', '--config', default='./resources/jl_config.yaml', help='Global config file (logging, scrollback, etc.). Default: ./resources/jl_config.yaml')
    # Inventory file (hosts, groups, defaults)
    parser.add_argument('-i', '--inventory', default='./resources/inventory.yaml', help='Inventory file (hosts, groups, defaults). Default: ./resources/inventory.yaml')
    # User password
    parser.add_argument('-p', '--password', help='User password')
    # Username
    parser.add_argument('-u', '--username', help='Username')
    # SSH key passphrase
    parser.add_argument('-r', '--passphrase', help='SSH key passphrase')
    # SSH cipher type
    parser.add_argument('-y', '--cipher', help='SSH cipher type (modern only)')
    # Show version
    parser.add_argument('-V', '--version', action='store_true', help='Show version and exit')
    # Debug output
    parser.add_argument('-d', '--debug', action='store_true', help='Enable debug output')
    # SSH private key file
    parser.add_argument('--keyfile', help='SSH private key file (overrides inventory)')
    # Print timestamp after each command
    parser.add_argument('-T', '--timestamp', action='store_true', help='Print timestamp after each command')
    # Log all input/output to this file (overrides config)
    parser.add_argument('--logfile', help='Log all input/output to this file (overrides config)')
    # ProxyJump (ssh -J) string
    parser.add_argument('-J', '--proxyjump', help='ProxyJump (ssh -J) string, e.g. user@jump1[,user2@jump2,...]')
    # Manual jump host options
    parser.add_argument('--jump-host', help='Jump server hostname (manual pexpect chain)')
    parser.add_argument('--jump-username', help='Jump server username')
    parser.add_argument('--jump-keyfile', help='Jump server keyfile')
    parser.add_argument('--jump-password', help='Jump server password')
    parser.add_argument('--jump-keyfile-location', help='Where the jump keyfile is located ("local" or hostname)')
    # YAML file with jump chain configuration
    parser.add_argument('--jump-config', help='YAML file with jump chain configuration')
    # Witness/learning mode
    parser.add_argument('--witness-jump', action='store_true', help='Witness/learning mode: record jump sequence and offer to save as config')
    # Force refresh of remote config file
    parser.add_argument('--refresh-config', action='store_true', help='Force refresh of remote config file')
    # Remote config cache expiry in seconds (0 = always flush)
    parser.add_argument('--config-cache-expiry', type=int, default=600, help='Remote config cache expiry in seconds (0 = always flush)')
    return parser.parse_args()

# =========================
# Utility Functions
# =========================
def print_timestamp():
    """Print a timestamp line in the format [Time HH:MM:SS Day, Month DD]"""
    now = datetime.datetime.now()
    print(f"[Time {now.strftime('%H:%M:%S %A, %B %d')}]", flush=True)

# =========================
# Remote Config Support
# =========================
def is_remote_config(path):
    """Return True if the config path is a remote (sftp/scp) URL."""
    return path.startswith('sftp://') or path.startswith('scp://')

def parse_remote_url(url):
    """Parse a remote config URL into protocol, user, host, and path."""
    import re
    m = re.match(r'(sftp|scp)://([^@]+)@([^:]+):(.*)', url)
    if not m:
        raise ValueError(f"Invalid remote config URL: {url}")
    proto, user, host, path = m.groups()
    return proto, user, host, path

def get_cache_path(user, host, path):
    """Return a unique local cache path for a remote config file."""
    h = hashlib.sha256(f"{user}@{host}:{path}".encode()).hexdigest()[:16]
    cache_dir = os.path.expanduser('~/.jl_cache')
    os.makedirs(cache_dir, exist_ok=True)
    return os.path.join(cache_dir, f"{h}.yaml")

def fetch_remote_config(url, refresh=False, cache_expiry=600):
    """
    Fetch a remote config file using paramiko SFTP.
    If refresh is False and cache is fresh, use the cache.
    If cache_expiry is 0, always re-download.
    """
    proto, user, host, rpath = parse_remote_url(url)
    cache_path = get_cache_path(user, host, rpath)
    # Use cache if not refreshing and cache is fresh
    if not refresh and os.path.exists(cache_path):
        if cache_expiry == 0:
            pass  # Always flush
        else:
            mtime = os.path.getmtime(cache_path)
            if time.time() - mtime < cache_expiry:
                return cache_path
    # Fetch using paramiko
    try:
        client = paramiko.SSHClient()
        client.load_system_host_keys()
        client.set_missing_host_key_policy(paramiko.AutoAddPolicy())
        client.connect(host, username=user)
        sftp = client.open_sftp()
        sftp.get(rpath, cache_path)
        sftp.close()
        client.close()
        return cache_path
    except Exception as e:
        print(f"[WARNING] Failed to fetch remote config: {e}")
        if os.path.exists(cache_path):
            print(f"[INFO] Using cached config: {cache_path}")
            return cache_path
        else:
            raise RuntimeError(f"Could not fetch or find cached config for {url}")

# =========================
# Inventory Loader
# =========================
def load_inventory(config_file, refresh_config=False, cache_expiry=600):
    """
    Load the inventory YAML file, supporting local or remote (SFTP/SCP) sources.
    """
    if is_remote_config(config_file):
        local_path = fetch_remote_config(config_file, refresh=refresh_config, cache_expiry=cache_expiry)
        with open(local_path, 'r') as f:
            return yaml.safe_load(f)
    else:
        with open(config_file, 'r') as f:
            return yaml.safe_load(f)

def load_inventory_ordered(path, refresh_config=False, cache_expiry=None):
    # Load YAML preserving order
    import yaml
    with open(path, 'r') as f:
        return yaml.load(f, Loader=yaml.SafeLoader)

# =========================
# Logging Config
# =========================
def get_logging_config(args, inventory, device_name=None):
    """
    Determine if logging is enabled and what the log file path should be.
    Supports dynamic log file naming and date-based directories.
    """
    logfile = None
    logging_enabled = False
    log_filename_format = None
    log_dir_by_date = False
    # CLI flag takes precedence
    if hasattr(args, 'logfile') and args.logfile:
        logfile = args.logfile
        logging_enabled = True
    elif 'logging' in inventory:
        logconf = inventory['logging']
        if logconf.get('enabled', False):
            logging_enabled = True
            logfile = logconf.get('file')
            log_filename_format = logconf.get('log_filename_format')
            log_dir_by_date = logconf.get('log_dir_by_date', False)
    # Dynamic log filename logic
    if logging_enabled:
        now = datetime.datetime.now()
        date_str = now.strftime('%Y-%m-%d')
        time_str = now.strftime('%H%M%S')
        device = device_name or 'session'
        if log_filename_format:
            filename = log_filename_format.format(device=device, date=date_str, time=time_str)
        elif logfile:
            filename = os.path.basename(logfile)
        else:
            filename = f"{device}_{date_str}_{time_str}.log"
        logdir = os.path.dirname(logfile) if logfile else '.'
        if log_dir_by_date:
            logdir = os.path.join(logdir, date_str)
        os.makedirs(logdir, exist_ok=True)
        logfile_path = os.path.join(logdir, filename)
        return logging_enabled, logfile_path
    return logging_enabled, logfile

# =========================
# Scrollback Buffer
# =========================
class ScrollbackBuffer:
    """
    A buffer to store the last N lines of session output for scrollback.
    If max_lines is 0, buffer is unlimited (subject to system memory).
    """
    def __init__(self, max_lines):
        self.max_lines = max_lines
        self.lines = []
    def append(self, line):
        self.lines.append(line)
        if self.max_lines > 0 and len(self.lines) > self.max_lines:
            self.lines = self.lines[-self.max_lines:]
    def get(self):
        return self.lines

# =========================
# Key Type Detection
# =========================
def detect_key_type(keyfile):
    """Detect the type of an SSH private key file (RSA, ECDSA, ED25519, etc)."""
    try:
        with open(keyfile, 'r') as f:
            first_line = f.readline()
            if 'BEGIN OPENSSH PRIVATE KEY' in first_line:
                return 'OPENSSH'
            elif 'BEGIN RSA PRIVATE KEY' in first_line:
                return 'RSA'
            elif 'BEGIN DSA PRIVATE KEY' in first_line:
                return 'DSA'
            elif 'BEGIN EC PRIVATE KEY' in first_line:
                return 'ECDSA'
            elif 'BEGIN ED25519 PRIVATE KEY' in first_line:
                return 'ED25519'
            else:
                return 'UNKNOWN'
    except Exception as e:
        return f'ERROR: {e}'

# =========================
# Jump Host Logic
# =========================
def load_jump_config_file(jump_config_path):
    """Load a jump chain config from a YAML file."""
    with open(jump_config_path, 'r') as f:
        return yaml.safe_load(f)

def get_jump_config(args, hostdata, inventory):
    """
    Determine jump host configuration from CLI, hostdata, inventory, or external file.
    Returns (proxyjump, jump_chain).
    """
    proxyjump = args.proxyjump or hostdata.get('proxyjump') or inventory.get('defaults', {}).get('proxyjump')
    jump_chain = []
    jump_config_path = args.jump_config or hostdata.get('jump_config') or inventory.get('defaults', {}).get('jump_config')
    if jump_config_path:
        jump_config = load_jump_config_file(jump_config_path)
        if isinstance(jump_config, list):
            jump_chain = jump_config
        elif 'jump' in jump_config:
            if isinstance(jump_config['jump'], list):
                jump_chain = jump_config['jump']
            else:
                jump_chain = [jump_config['jump']]
    elif args.jump_host:
        jump_chain.append({
            'host': args.jump_host,
            'username': args.jump_username,
            'keyfile': args.jump_keyfile,
            'password': args.jump_password,
            'keyfile_location': args.jump_keyfile_location or 'local',
        })
    elif 'jump' in hostdata:
        if isinstance(hostdata['jump'], list):
            jump_chain = hostdata['jump']
        else:
            jump_chain = [hostdata['jump']]
    elif 'jump' in inventory.get('defaults', {}):
        if isinstance(inventory['defaults']['jump'], list):
            jump_chain = inventory['defaults']['jump']
        else:
            jump_chain = [inventory['defaults']['jump']]
    return proxyjump, jump_chain

def match_host_in_inventory(host, inventory_hosts):
    # inventory_hosts: OrderedDict or list of (name, data)
    for entry, data in inventory_hosts.items():
        if entry == host:
            return data, entry
        if '*' in entry or '?' in entry:
            if fnmatch.fnmatch(host, entry):
                return data, entry
    return None, None

# =========================
# Witness/Learning Mode
# =========================
def witness_jump_sequence():
    """
    Interactive mode to record a jump sequence, confirming only successful logins.
    Offers to save the sequence as a YAML config file.
    """
    print("[WITNESS MODE] Please manually perform your jump sequence. Each time you SSH to a new host, enter the details below.")
    jump_chain = []
    while True:
        host = input("Jump host (or blank to finish): ").strip()
        if not host:
            break
        username = input(f"Username for {host} (blank for default): ").strip() or None
        keyfile = input(f"Keyfile for {host} (blank if none): ").strip() or None
        password = input(f"Password for {host} (blank if none): ").strip() or None
        keyfile_location = input(f"Keyfile location for {host} (local/remote, default local): ").strip() or 'local'
        # Confirm successful login before recording
        while True:
            confirm = input(f"Did you successfully log in to {host}? (y/n/r=retry/skip): ").strip().lower()
            if confirm == 'y':
                jump_chain.append({
                    'host': host,
                    'username': username,
                    'keyfile': keyfile,
                    'password': password,
                    'keyfile_location': keyfile_location,
                })
                break
            elif confirm == 'n':
                print("Not recording this jump. You can re-enter details.")
                break
            elif confirm == 'r':
                # Re-enter details for this host
                host = input("Jump host (or blank to finish): ").strip()
                if not host:
                    break
                username = input(f"Username for {host} (blank for default): ").strip() or None
                keyfile = input(f"Keyfile for {host} (blank if none): ").strip() or None
                password = input(f"Password for {host} (blank if none): ").strip() or None
                keyfile_location = input(f"Keyfile location for {host} (local/remote, default local): ").strip() or 'local'
            else:
                print("Please enter 'y' for yes, 'n' for no, or 'r' to retry.")
        # If user breaks out of retry, stop
        if not host:
            break
    if jump_chain:
        import yaml
        save = input("Save this jump chain to a YAML file? (y/n): ").strip().lower()
        if save == 'y':
            path = input("Path to save jump config YAML: ").strip()
            with open(path, 'w') as f:
                yaml.dump({'jump': jump_chain}, f)
            print(f"Jump config saved to {path}")
        else:
            print("Jump config not saved.")
    else:
        print("No jump sequence recorded.")
    return jump_chain

# =========================
# SSH Connection Logic
# =========================
def propagate_keyfile_to_jump(child, local_keyfile_path, remote_keyfile_path, debug=False):
    """
    Securely copy a keyfile to a remote jump host via the open shell session (pexpect child).
    1. touch the file
    2. chmod 600
    3. cat the contents (not echoed)
    """
    with open(local_keyfile_path, 'r') as f:
        key_contents = f.read()
    # Step 1: touch the file
    child.sendline(f'touch {remote_keyfile_path}')
    child.expect(r'[$#] ')
    # Step 2: chmod 600
    child.sendline(f'chmod 600 {remote_keyfile_path}')
    child.expect(r'[$#] ')
    # Step 3: cat the contents (not echoed)
    child.sendline(f'cat > {remote_keyfile_path}')
    child.send(key_contents)
    child.send("\x04")  # Send EOF (Ctrl-D)
    child.expect(r'[$#] ')
    if debug:
        print(f"[DEBUG] Keyfile propagated to jump host: {remote_keyfile_path}")


def delete_keyfile_from_jump(child, remote_keyfile_path, debug=False):
    """Delete the temporary keyfile from the remote jump host."""
    child.sendline(f'rm -f {remote_keyfile_path}')
    child.expect(r'[$#] ')
    if debug:
        print(f"[DEBUG] Keyfile deleted from jump host: {remote_keyfile_path}")

def ssh_connect(host, user, password, keyfile, passphrase, cipher, command, debug, user_script=None, hostdata=None, env_vars=None, timestamp=False, logging_enabled=False, logfile=None, scrollback_lines=1000, proxyjump=None, jump_chain=None, target_device_name=None, previous_jump_host=None):
    """
    Establish an SSH connection using pexpect.
    Handles ProxyJump and manual jump chain logic.
    keyfile_location can be 'local' (originating client) or a hostname (use keyfile from that jump host).
    """
    import shlex
    # Always use the final target device name for logging
    if target_device_name is None:
        target_device_name = host
    # ProxyJump mode
    if proxyjump:
        ssh_cmd = f"ssh -J {proxyjump} "
        if keyfile:
            ssh_cmd += f"-i {shlex.quote(keyfile)} "
            if debug:
                key_type = detect_key_type(keyfile)
                print(f"[DEBUG] Using keyfile: {keyfile} (type: {key_type})")
        if cipher:
            ssh_cmd += f"-c {shlex.quote(cipher)} "
        ssh_cmd += f"{shlex.quote(user)}@{shlex.quote(host)}"
        if command:
            ssh_cmd += f" '{command}'"
        if debug:
            print(f"[DEBUG] SSH ProxyJump command: {ssh_cmd}")
        child = pexpect.spawn(ssh_cmd, encoding='utf-8', timeout=30)
        return ssh_pexpect_session(child, host, user, password, keyfile, passphrase, cipher, command, debug, user_script, hostdata, env_vars, timestamp, logging_enabled, logfile, scrollback_lines, target_device_name=target_device_name)
    # Manual jump chain mode
    elif jump_chain:
        jump = jump_chain[0]
        jump_user = jump.get('username') or user
        jump_host = jump['host']
        jump_keyfile = jump.get('keyfile')
        jump_password = jump.get('password')
        # Determine keyfile_location logic
        keyfile_location = jump.get('keyfile_location')
        if not keyfile_location:
            # Default: 'local' for first hop, previous jump host for others
            keyfile_location = 'local' if previous_jump_host is None else previous_jump_host
        # For the current jump, use keyfile from the correct location
        ssh_cmd = f"ssh "
        remote_keyfile_path = None
        if keyfile_location == 'local' and jump_keyfile:
            # If the keyfile is needed on a remote jump host, propagate it
            if previous_jump_host is not None:
                # Generate a unique filename for the keyfile on the jump host
                rand_str = ''.join(random.choices(string.ascii_letters + string.digits, k=8))
                remote_keyfile_path = f"/tmp/jl_keyfile_{rand_str}.pem"
                propagate_keyfile_to_jump(child, jump_keyfile, remote_keyfile_path, debug=debug)
                ssh_cmd += f"-i {shlex.quote(remote_keyfile_path)} "
            else:
                ssh_cmd += f"-i {shlex.quote(jump_keyfile)} "
                if debug:
                    key_type = detect_key_type(jump_keyfile)
                    print(f"[DEBUG] Using jump keyfile (local): {jump_keyfile} (type: {key_type})")
        elif keyfile_location == jump_host:
            pass  # Assume keyfile is present on this jump host
        else:
            pass  # Not supported for this hop
        ssh_cmd += f"{shlex.quote(jump_user)}@{shlex.quote(jump_host)}"
        if debug:
            print(f"[DEBUG] SSH jump command: {ssh_cmd}")
        jump_child = pexpect.spawn(ssh_cmd, encoding='utf-8', timeout=30)
        try:
            while True:
                i = jump_child.expect([
                    r"Are you sure you want to continue connecting \(yes/no.*\)\?",
                    r"[Pp]assword:",
                    r"Enter passphrase for key.*:",
                    r"[$#] ",
                    pexpect.EOF,
                    pexpect.TIMEOUT
                ])
                if i == 0:
                    jump_child.sendline("yes")
                elif i == 1:
                    if jump_password is not None:
                        jump_child.sendline(jump_password)
                    else:
                        jump_password = getpass.getpass(f"Password for {jump_user}@{jump_host}: ")
                        jump_child.sendline(jump_password)
                elif i == 2:
                    passphrase = getpass.getpass(f"SSH key passphrase for {jump_user}@{jump_host}: ")
                    jump_child.sendline(passphrase)
                elif i == 3:
                    # At jump shell, now SSH to next hop or target
                    if len(jump_chain) > 1:
                        # Pass the current jump host as previous_jump_host for the next hop
                        return ssh_connect(
                            host, user, password, keyfile, passphrase, cipher, command, debug,
                            user_script=user_script, hostdata=hostdata, env_vars=env_vars, timestamp=timestamp,
                            logging_enabled=logging_enabled, logfile=logfile, scrollback_lines=scrollback_lines,
                            proxyjump=None, jump_chain=jump_chain[1:], target_device_name=target_device_name, previous_jump_host=jump_host
                        )
                    else:
                        # Final hop: SSH to target from jump
                        inner_ssh_cmd = f"ssh "
                        if keyfile:
                            final_keyfile_location = keyfile_location if keyfile_location != 'local' else previous_jump_host
                            if final_keyfile_location == jump_host or keyfile_location == 'local':
                                inner_ssh_cmd += f"-i {shlex.quote(keyfile)} "
                                if debug:
                                    key_type = detect_key_type(keyfile)
                                    print(f"[DEBUG] Using remote keyfile for final hop: {keyfile} (type: {key_type}) from {keyfile_location}")
                        if cipher:
                            inner_ssh_cmd += f"-c {shlex.quote(cipher)} "
                        inner_ssh_cmd += f"{shlex.quote(user)}@{shlex.quote(host)}"
                        if command:
                            inner_ssh_cmd += f" '{command}'"
                        if debug:
                            print(f"[DEBUG] SSH from jump to target: {inner_ssh_cmd}")
                        jump_child.sendline(inner_ssh_cmd)
                        # After use, delete the propagated keyfile if it was created
                        if remote_keyfile_path:
                            delete_keyfile_from_jump(jump_child, remote_keyfile_path, debug=debug)
                        return ssh_pexpect_session(jump_child, host, user, password, keyfile, passphrase, cipher, command, debug, user_script, hostdata, env_vars, timestamp, logging_enabled, logfile, scrollback_lines, target_device_name=target_device_name)
                elif i == 4:
                    print("[ERROR] Jump server connection closed unexpectedly.")
                    jump_child.close()
                    sys.exit(1)
                elif i == 5:
                    print("[ERROR] Jump server connection timed out.")
                    jump_child.close()
                    sys.exit(1)
        except KeyboardInterrupt:
            jump_child.close()
            sys.exit(0)
    else:
        return ssh_pexpect_session(pexpect.spawn(f"ssh {user}@{host}", encoding='utf-8', timeout=30), host, user, password, keyfile, passphrase, cipher, command, debug, user_script, hostdata, env_vars, timestamp, logging_enabled, logfile, scrollback_lines, target_device_name=target_device_name)

# Helper to handle the rest of the session (logging, scrollback, etc.)
def ssh_pexpect_session(child, host, user, password, keyfile, passphrase, cipher, command, debug, user_script=None, hostdata=None, env_vars=None, timestamp=False, logging_enabled=False, logfile=None, scrollback_lines=1000, target_device_name=None):
    """
    Manage the pexpect session for an SSH connection, including logging, scrollback, and user interaction.
    """
    logf = None
    if logging_enabled and logfile:
        logf = open(logfile, 'a')
    scrollback = ScrollbackBuffer(scrollback_lines)
    def log(line):
        if logf:
            logf.write(line)
            logf.flush()
        scrollback.append(line)
    try:
        while True:
            i = child.expect([
                r"Are you sure you want to continue connecting \(yes/no.*\)\?",
                r"[Pp]assword:",
                r"Enter passphrase for key.*:",
                r"Permission denied",
                r"no matching cipher found|no matching key exchange method found|no matching host key type found|no hostkey alg",
                r"[$#] ",  # shell prompt (very basic)
                pexpect.EOF,
                pexpect.TIMEOUT
            ])
            if i == 0:
                child.sendline("yes")
            elif i == 1:
                if password is None:
                    password = getpass.getpass(f"Password for {user}@{host}: ")
                child.sendline(password)
            elif i == 2:
                if passphrase is None:
                    passphrase = getpass.getpass(f"SSH key passphrase for {user}@{host}: ")
                child.sendline(passphrase)
            elif i == 3:
                print("Permission denied, wrong password or key?")
                if logf:
                    logf.close()
                child.close()
                sys.exit(1)
            elif i == 4:
                print("[ERROR] SSH connection failed due to cipher or key exchange mismatch.")
                print("Try specifying a cipher with the -y/--cipher option.")
                if logf:
                    logf.close()
                child.close()
                sys.exit(1)
            elif i == 5:
                # At shell prompt or command output
                if user_script:
                    script_globals = {
                        'session': child,
                        'host': host,
                        'user': user,
                        'hostdata': hostdata,
                        'env_vars': env_vars or {},
                        'log': log,
                        'scrollback': scrollback,
                    }
                    with open(user_script, 'r') as f:
                        code = f.read()
                    try:
                        exec(code, script_globals)
                    except Exception as e:
                        print(f"[ERROR] Exception in user script: {e}")
                    if logf:
                        logf.close()
                    child.close()
                    break
                elif command:
                    if timestamp:
                        print_timestamp()
                        log(f"[Time {datetime.datetime.now().strftime('%H:%M:%S %A, %B %d')}]\n")
                    child.interact()
                    break
                else:
                    # Interactive mode: wrap input to inject timestamp after each command
                    # In a jump chain, pass the current child to interact_with_features
                    # to manage the escape menu and jump stack.
                    jump_stack = []
                    if target_device_name is not None: # Only if it's a jump host
                        jump_stack.append(child)
                    interact_with_features(child, timestamp, log, jump_stack)
                    if logf:
                        logf.close()
                    break
            elif i == 6:
                if logf:
                    logf.close()
                break
            elif i == 7:
                print("Connection timed out.")
                if logf:
                    logf.close()
                child.close()
                sys.exit(1)
    except KeyboardInterrupt:
        if logf:
            logf.close()
        child.close()
        sys.exit(0)

def interact_with_features(child, timestamp, log, jump_stack=None):
    """
    Interact with the pexpect session in a non-blocking way,
    allowing user input to be sent to the child process and logged.
    All keystrokes, including Ctrl-C, are sent to the remote host.
    Only Ctrl-] (ASCII 29) is intercepted locally to present an escape menu.
    If in a jump chain, jump_stack is a list of pexpect children (from outermost to innermost).
    """
    old_settings = termios.tcgetattr(sys.stdin)
    ESCAPE_CHAR = b'\x1d'  # Ctrl-]
    try:
        tty.setraw(sys.stdin.fileno())
        input_buffer = b''
        while True:
            rlist, _, _ = select.select([sys.stdin, child.child_fd], [], [])
            if sys.stdin in rlist:
                user_input = os.read(sys.stdin.fileno(), 65536)
                # Check for escape sequence (Ctrl-])
                if ESCAPE_CHAR in user_input:
                    # Split input at escape char, send everything before to remote
                    before, _, after = user_input.partition(ESCAPE_CHAR)
                    if before:
                        child.write(before)
                        log(before.decode(errors='replace'))
                    # Enter escape menu
                    while True:
                        print("\n[Escape Menu] Select an option:")
                        print("  1) Abort entire session")
                        print("  2) Abort most remote session (pop one jump)")
                        print("  3) Resume session")
                        choice = input("Enter choice [1-3]: ").strip()
                        if choice == '1':
                            print("Aborting all sessions...")
                            # Close all jump sessions if jump_stack is provided
                            if jump_stack:
                                for s in reversed(jump_stack):
                                    s.close()
                            child.close()
                            sys.exit(0)
                        elif choice == '2':
                            print("Aborting most remote session...")
                            # Close only the innermost session
                            if jump_stack and len(jump_stack) > 1:
                                jump_stack[-1].close()
                                print("Returned to previous jump host.")
                                return  # Resume at previous jump
                            else:
                                print("No jump stack or only one session; aborting entire session.")
                                child.close()
                                sys.exit(0)
                        elif choice == '3':
                            print("Resuming session...")
                            break
                        else:
                            print("Invalid choice. Please enter 1, 2, or 3.")
                    # After menu, continue loop
                    if after:
                        child.write(after)
                        log(after.decode(errors='replace'))
                    continue
                # Normal input: send to remote
                child.write(user_input)
                log(user_input.decode(errors='replace'))
                if b'\n' in user_input and timestamp:
                    print_timestamp()
                    log(f"[Time {datetime.datetime.now().strftime('%H:%M:%S %A, %B %d')}]\n")
            if child.child_fd in rlist:
                try:
                    data = os.read(child.child_fd, 65536)
                    if not data:
                        break
                    os.write(sys.stdout.fileno(), data)
                    log(data.decode(errors='replace'))
                except OSError:
                    break
    finally:
        termios.tcsetattr(sys.stdin, termios.TCSADRAIN, old_settings)

# --- Main Logic ---
def main():
    """
    Main execution flow for jl.
    Parses arguments, loads inventory, sets up environment, and handles jumps.
    """
    args = parse_args()
    if args.version:
        print(f"jl version {VERSION}")
        sys.exit(0)

    # Witness/learning mode
    if args.witness_jump:
        witness_jump_sequence()
        sys.exit(0)

    # Check for config and inventory file existence
    if not is_remote_config(args.config) and not os.path.isfile(args.config):
        print(f"[ERROR] Config file not found: {args.config}")
        sys.exit(1)
    if not is_remote_config(args.inventory) and not os.path.isfile(args.inventory):
        print(f"[ERROR] Inventory file not found: {args.inventory}")
        sys.exit(1)

    # Load global config (logging, scrollback, etc.)
    config = load_inventory(args.config, refresh_config=args.refresh_config, cache_expiry=args.config_cache_expiry) or {}
    # Load inventory (hosts, groups, defaults) with order preserved
    inventory = load_inventory_ordered(args.inventory, refresh_config=args.refresh_config, cache_expiry=args.config_cache_expiry) or {}
    host = args.host

    # Merge defaults: inventory defaults override config defaults
    merged_defaults = dict(config.get('defaults', {}))
    merged_defaults.update(inventory.get('defaults', {}))
    inventory['defaults'] = merged_defaults

    # Prepare environment variables
    env_vars = {}
    if args.env:
        for ev in args.env:
            if '=' in ev:
                k, v = ev.split('=', 1)
                env_vars[k] = v
    if args.env_file:
        env_vars.update(load_env_file(args.env_file))
    merge_env_vars(env_vars)

    # Host lookup with ordered wildcard logic
    hostdata, matched_entry = match_host_in_inventory(host, inventory['hosts'])
    if hostdata is not None:
        if '*' in matched_entry or '?' in matched_entry:
            # Wildcard match: check /etc/hosts for IP, else use literal host
            hostdata = dict(hostdata)
            etc_hosts_ip = None
            try:
                with open('/etc/hosts', 'r') as f:
                    for line in f:
                        if line.strip() and not line.startswith('#'):
                            parts = line.split()
                            if len(parts) >= 2 and host in parts[1:]:
                                etc_hosts_ip = parts[0]
                                break
            except Exception:
                pass
            if etc_hosts_ip:
                hostdata['hostname'] = etc_hosts_ip
                print(f"[INFO] Using /etc/hosts IP for {host}: {etc_hosts_ip}")
            else:
                hostdata['hostname'] = host
                print(f"[INFO] Using wildcard inventory entry '{matched_entry}' for host: {host}")
        # else: exact match, use inventory hostname as usual
    else:
        # Try /etc/hosts as a last resort
        etc_hosts_ip = None
        try:
            with open('/etc/hosts', 'r') as f:
                for line in f:
                    if line.strip() and not line.startswith('#'):
                        parts = line.split()
                        if len(parts) >= 2 and host in parts[1:]:
                            etc_hosts_ip = parts[0]
                            hostdata = {'hostname': etc_hosts_ip}
                            print(f"[INFO] Using /etc/hosts IP for {host}: {etc_hosts_ip}")
                            break
        except Exception as e:
            pass
        # If still not found, try DNS resolution
        if not hostdata:
            try:
                resolved_ip = socket.gethostbyname(host)
                hostdata = {'hostname': resolved_ip}
                print(f"[INFO] Using DNS-resolved IP for {host}: {resolved_ip}")
            except Exception:
                pass
    if not hostdata:
        print(f"Host {host} not found in inventory, wildcards, /etc/hosts, or DNS.")
        sys.exit(1)

    # Use merged defaults for all lookups
    user = args.username or hostdata.get('username') or inventory['defaults'].get('username') or os.environ.get('USER')
    password = args.password or hostdata.get('password') or inventory['defaults'].get('password')
    keyfile = args.keyfile or hostdata.get('keyfile') or inventory['defaults'].get('keyfile')
    passphrase = args.passphrase or hostdata.get('passphrase') or inventory['defaults'].get('passphrase')
    cipher = args.cipher or hostdata.get('cipher') or inventory['defaults'].get('cipher')
    command = args.command
    if args.command_file:
        with open(args.command_file, 'r') as f:
            command = f.read().replace('\n', '; ')
    if args.debug:
        print(f"[DEBUG] Connecting to {host} as {user}")
    proxyjump, jump_chain = get_jump_config(args, hostdata, inventory)
    # Enhanced logging config: pass device/host name, use config for global logging if not set in inventory
    logging_enabled, logfile = get_logging_config(args, {**config, **hostdata.get('logging', {})}, device_name=host)
    scrollback_lines = hostdata.get('scrollback', config.get('scrollback', 1000))
    ssh_connect(
        host, user, password, keyfile, passphrase, cipher, command, args.debug,
        user_script=args.script, hostdata=hostdata, env_vars=env_vars, timestamp=args.timestamp,
        logging_enabled=logging_enabled, logfile=logfile, scrollback_lines=scrollback_lines,
        proxyjump=proxyjump, jump_chain=jump_chain, target_device_name=host
    )

if __name__ == "__main__":
    main()
