#!/usr/bin/env python3
"""Serial, source-based build of all first-party and vendored modules using readonly imports."""
from pathlib import Path
import re,subprocess,sys
root=Path(__file__).resolve().parent.parent
seen=set();order=[]
def visit(name):
    if name in seen:return
    seen.add(name)
    p=root.joinpath(*name.split('.')).with_suffix('.lean')
    if not p.exists():return
    for line in p.read_text().splitlines():
        m=re.match(r'^(?:public\s+)?import\s+(.+)',line)
        if m:
            for dep in m.group(1).split():visit(dep)
    order.append((name,p))
for p in sorted([*root.glob('CellAttachment/*.lean'),*root.glob('Lean4/**/*.lean'),*root.glob('ClassicalSVK/**/*.lean')]):
    visit('.'.join(p.relative_to(root).with_suffix('').parts))
for module in ['Lean4','ClassicalSVK','CellAttachment','Challenge','Solution']:visit(module)
for i,(name,p) in enumerate(order,1):
    print(f'[{i}/{len(order)}] {name}',flush=True)
    r=subprocess.run([str(root/'scripts/lean-file.sh'),str(p.relative_to(root))],cwd=root)
    if r.returncode:sys.exit(r.returncode)
print('PASS: all submitted Lean module sources compiled',flush=True)
