#!/usr/bin/env python3
"""Compile only the immutable registered SVK source dependency closure, serially."""
import os, pathlib, re, subprocess, sys
root=pathlib.Path(__file__).resolve().parent.parent
src=root
seen=set(); order=[]
def visit(name):
    if name in seen: return
    seen.add(name)
    p=src.joinpath(*name.split('.')).with_suffix('.lean')
    if not p.exists(): return
    for line in p.read_text().splitlines():
        m=re.match(r'^(?:public\s+)?import\s+(.+)',line)
        if m:
            for module in m.group(1).split(): visit(module)
    order.append((name,p))
visit('ClassicalSVK.Pushout')
lean=os.environ['CELL_LEAN_BIN']
for i,(name,path) in enumerate(order,1):
    out=root/'.lake/build/lib/lean'/path.relative_to(src).with_suffix('.olean')
    out.parent.mkdir(parents=True,exist_ok=True)
    print(f'[{i}/{len(order)}] {name}',flush=True)
    r=subprocess.run([lean,'--root',str(src),'-o',str(out),'-i',str(out.with_suffix('.ilean')),str(path)],cwd=src)
    if r.returncode: sys.exit(r.returncode)
