#!/usr/bin/env python3
"""Recreate the x86-64 libseccomp policy used for the native evidence run.

Usage: python3 checks/make-native-network-filter.py /path/to/network-denied.bpf
"""
import ctypes
import errno
from pathlib import Path
import sys


library = ctypes.CDLL("libseccomp.so.2")
library.seccomp_init.argtypes = [ctypes.c_uint32]
library.seccomp_init.restype = ctypes.c_void_p
library.seccomp_syscall_resolve_name.argtypes = [ctypes.c_char_p]
library.seccomp_syscall_resolve_name.restype = ctypes.c_int
library.seccomp_rule_add.argtypes = [ctypes.c_void_p, ctypes.c_uint32, ctypes.c_int, ctypes.c_uint]
library.seccomp_rule_add.restype = ctypes.c_int
library.seccomp_export_bpf.argtypes = [ctypes.c_void_p, ctypes.c_int]
library.seccomp_export_bpf.restype = ctypes.c_int
library.seccomp_release.argtypes = [ctypes.c_void_p]

# SCMP_ACT_ALLOW is the default. The listed calls return EPERM.
ctx = library.seccomp_init(0x7FFF0000)
if not ctx:
    raise RuntimeError("libseccomp could not allocate a policy")
try:
    for name in (
        "socket", "socketpair", "connect", "bind", "listen", "accept", "accept4",
        "sendto", "sendmsg", "sendmmsg", "recvfrom", "recvmsg", "recvmmsg",
        "io_uring_setup", "io_uring_enter", "io_uring_register",
    ):
        number = library.seccomp_syscall_resolve_name(name.encode())
        action = 0x00050000 | errno.EPERM
        if number < 0 or library.seccomp_rule_add(ctx, action, number, 0) != 0:
            raise RuntimeError(f"Could not deny {name}")
    with Path(sys.argv[1]).open("xb") as destination:
        if library.seccomp_export_bpf(ctx, destination.fileno()) != 0:
            raise RuntimeError("libseccomp could not write the filter")
finally:
    library.seccomp_release(ctx)
