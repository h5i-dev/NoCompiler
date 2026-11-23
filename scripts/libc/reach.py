#!/usr/bin/env python3
"""Which functions a binary can reach from ROOTS (jal/branch targets and auipc+jalr pairs), and whether each is
byte-identical to the same-named function of OTHER ELFs (SAME), differs (diff), or is absent there (-).

    reach.py ELF ROOT[,ROOT...] [OTHER.elf...]

Functions passed by address (main to __libc_start_main, atexit handlers) are not followed: give them as roots.
"""
import subprocess,re,sys,hashlib
def syms(p):
    out={}
    for l in subprocess.run(['nm','-S','--defined-only',p],capture_output=True,text=True).stdout.splitlines():
        f=l.split()
        # Assembler-local labels (.Lpcrel_hi*, ...) and mapping symbols ($x) are not functions: they
        # would cut a function at an auipc's label (crt1's _start, sized to the next symbol).
        if f and (f[-1].startswith('.L') or f[-1].startswith('$')): continue
        if len(f)==4 and f[2] in 'Tt': out[f[3]]=(int(f[0],16),int(f[1],16))
        elif len(f)==3 and f[1] in 'Tt': out[f[2]]=(int(f[0],16),None)
    addrs=sorted(set(v[0] for v in out.values()))
    import bisect
    for n,(a,z) in list(out.items()):
        if z is None:
            i=bisect.bisect_right(addrs,a); out[n]=(a,(addrs[i]-a) if i<len(addrs) else 4)
    return out
def dis(p):
    S=syms(p); fs=sorted((v[0],v[0]+v[1],n) for n,v in S.items())
    def fn(a):
        for lo,hi,n in fs:
            if lo<=a<hi: return n
    t=subprocess.run(['llvm-objdump','-d','--no-show-raw-insn','-M','no-aliases',p],capture_output=True,text=True).stdout
    calls={}; au={}
    for l in t.splitlines():
        m=re.match(r'^\s*([0-9a-f]+):\s+(\S+)\s*(.*)',l)
        if not m: continue
        a=int(m.group(1),16); op=m.group(2); args=m.group(3); f=fn(a)
        if f is None: continue
        calls.setdefault(f,set())
        tgt=None
        if op in('jal','c.jal','c.j'):
            mm=re.search(r'0x([0-9a-f]+)',args)
            if mm: tgt=int(mm.group(1),16)
        elif op=='auipc':
            r,imm=[x.strip() for x in args.split(',')[:2]]; au[r]=(a,int(imm,0))
        elif op=='jalr':
            mm=re.match(r'(\w+),\s*(-?\d+)\((\w+)\)',args)
            if mm and mm.group(3) in au:
                b,imm=au[mm.group(3)]; tgt=b+((imm<<12)-(1<<32 if imm>=1<<19 else 0)*4096//4096)+int(mm.group(2))
        if tgt is not None:
            g=fn(tgt)
            if g and g!=f: calls[f].add(g)
        if op.startswith('b') or op.startswith('c.b'):
            mm=re.search(r'0x([0-9a-f]+)',args)
            if mm:
                g=fn(int(mm.group(1),16))
                if g and g!=f: calls[f].add(g)
    return calls
def fbytes(p,s):
    data=open(p,'rb').read()
    ph=subprocess.run(['readelf','-lW',p],capture_output=True,text=True).stdout
    loads=[(int(x.split()[2],16),int(x.split()[1],16),int(x.split()[4],16)) for x in ph.splitlines() if x.split()[:1]==['LOAD']]
    va,sz=s
    for lva,off,fsz in loads:
        if lva<=va<lva+fsz: return data[off+va-lva:off+va-lva+sz]
Q=sys.argv[1]; roots=sys.argv[2].split(',')
S=syms(Q); C=dis(Q)
seen=set(); st=list(roots)
while st:
    f=st.pop()
    if f in seen: continue
    seen.add(f); st+= [g for g in C.get(f,()) if g!=f]
others={}
for o in sys.argv[3:]:
    so=syms(o)
    for n,s in so.items(): others.setdefault(n,set()).add(hashlib.sha256(fbytes(o,s)).hexdigest())
for f in sorted(seen):
    if f not in S: continue
    h=hashlib.sha256(fbytes(Q,S[f])).hexdigest()
    tag='SAME' if h in others.get(f,()) else ('diff' if f in others else '-')
    print(f'{f} {S[f][1]} {tag}')
