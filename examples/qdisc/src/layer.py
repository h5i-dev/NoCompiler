# SPDX-License-Identifier: Apache-2.0
# Read a gzip tar layer of a container image from standard input; extract the
# members whose path starts with one of PREFIX... into OUT (no absolute paths,
# no `..`), and print the SHA-256 of the bytes read (the layer's digest).
#   python3 -I layer.py OUT PREFIX... < layer.tar.gz
import hashlib, sys, tarfile

class Hashed:
    def __init__(self, f):
        self.f, self.h = f, hashlib.sha256()
    def read(self, n=-1):
        b = self.f.read(n)
        self.h.update(b)
        return b

out, prefixes = sys.argv[1], tuple(sys.argv[2:])
src = Hashed(sys.stdin.buffer)
with tarfile.open(fileobj=src, mode='r|gz') as t:
    for m in t:
        n = m.name.lstrip('./')
        if n.startswith(prefixes) and '..' not in n.split('/') and not n.startswith('/'):
            m.name = n
            t.extract(m, out, set_attrs=False, filter='tar')
while src.read(1 << 20):
    pass
print(src.h.hexdigest())
