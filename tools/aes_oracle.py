#!/usr/bin/env python3
"""Independent check of the AES benchmark: the same chained AES-256 encryptions done by OpenSSL.

usage: aes_oracle.py N SEED   -> prints the number bench/aes/AesBench.lean's `aesBench N SEED` prints.
Slow (one openssl process per block), so keep N small."""
import subprocess, sys

def pat(seed, i):
    return (seed * 31 + i * 7 + i * i) % 256

n, seed = int(sys.argv[1]), int(sys.argv[2])
key = bytes(pat(seed, i) for i in range(32))
blk = bytes(pat(seed, 100 + i) for i in range(16))
for _ in range(n):
    blk = subprocess.run(["openssl", "enc", "-aes-256-ecb", "-nopad", "-K", key.hex()],
                         input=blk, capture_output=True, check=True).stdout
lane = [sum(blk[4 * j + k] << (8 * k) for k in range(4)) for j in range(4)]
print((lane[0] * 4294967296 + lane[1]) % 2305843009213693951 + lane[2] + lane[3])
