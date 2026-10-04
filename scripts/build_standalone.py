#!/usr/bin/env python3
"""Reproducibly flatten exact local dependency closure; never import the Solution in Challenge."""
from pathlib import Path
import re
root=Path(__file__).resolve().parent.parent
vendor=root/'vendor/classical-svk'

def local_source(name):
    p=root.joinpath(*name.split('.')).with_suffix('.lean')
    if p.is_file(): return p
    p=vendor.joinpath(*name.split('.')).with_suffix('.lean')
    return p if p.is_file() else None

# Remove comments only for a lexical scope count, retaining every source byte in output.
def uncomment(s):
    out=[]; i=0; depth=0
    while i<len(s):
        if s.startswith('/-',i): depth+=1; i+=2; continue
        if depth and s.startswith('-/',i): depth-=1; i+=2; continue
        if depth:
            if s[i]=='\n': out.append('\n')
            i+=1; continue
        if s.startswith('--',i):
            while i<len(s) and s[i]!='\n': i+=1
            continue
        out.append(s[i]); i+=1
    return ''.join(out)

def body(s):
    return '\n'.join(l for l in s.splitlines() if not re.match(r'^(?:public\s+)?import\s+',l)
        and l!='module' and l!='@[expose] public section')+'\n'

def wrap(name,s):
    s=body(s)
    balance=0
    for l in uncomment(s).splitlines():
        if re.match(r'^\s*(?:noncomputable\s+)?section(?:\s|$)',l) or re.match(r'^\s*namespace\s+',l): balance+=1
        elif re.match(r'^\s*end(?:\s|$)',l): balance-=1
        if balance<0: raise ValueError(f'unbalanced source scope in {name}')
    label=name.replace('.','_')
    return f'\n/-! Source module: {name} -/\nsection {label}\n{s}' + 'end\n'*balance + f'end {label}\n'

seen=set(); order=[]; external=[]
def visit(name):
    if name in seen:return
    seen.add(name)
    p=local_source(name)
    if p is None:
        external.append(name);return
    text=p.read_text()
    for l in text.splitlines():
        m=re.match(r'^(?:public\s+)?import\s+(.+)',l)
        if m:
            for n in m.group(1).split():visit(n)
    order.append((name,p))
visit('CellAttachment.Main')
header='''/-
Attaching arbitrary families of two-cells, Hatcher Proposition 1.26.
Authors: Arthur Freitas Ramos, David Barros Hulak,
Ruy Jose Guerra Barretto de Queiroz.
First-party sources released under Apache-2.0.
Vendored sources preserve their original license and copyright notices below.
-/
'''
mit_notice='/-\nVendored directed-topology helpers retain the following MIT notice.\n'+(root/'Lean4/LICENSE.md').read_text()+'\n-/\n'
solution=header+mit_notice+'module\n\n'+'\n'.join('public import '+n for n in external)+'\n\n@[expose] public section\n'
solution+=''.join(wrap(name,p.read_text()) for name,p in order)
solution='\n'.join(l for l in solution.splitlines() if l.strip())+'\n'
(root/'Solution.lean').write_text(solution)
# The independent Challenge has only actual construction and target definitions.
imports=['Mathlib.Analysis.Complex.Circle','Mathlib.Analysis.SpecialFunctions.Complex.Circle','Mathlib.Topology.Constructions',
 'Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup',
 'Mathlib.GroupTheory.QuotientGroup.Basic']
challenge=header+'module\n\n'+'\n'.join('public import '+n for n in imports)+'\n\n@[expose] public section\n'
challenge+=wrap('CellAttachment.Adjunction',(root/'CellAttachment/Adjunction.lean').read_text())
s=(root/'CellAttachment/CircleGenerator.lean').read_text()
start=s.index('namespace CellAttachment\n')
end=s.index('/-- The complex unit circle fundamental group',start)
challenge+=wrap('CellAttachment.CircleDefinitions','noncomputable section\nopen unitInterval\n'+s[start:end]+'\nend CellAttachment\n')
challenge+=wrap('CellAttachment.Statement',(root/'CellAttachment/Statement.lean').read_text())
challenge+='''\nnamespace CellAttachment
universe u v
/-- The independent full arbitrary-family cell-attachment challenge. -/
theorem two_cell_attachment : completeStatement.{u,v} := by
  sorry
end CellAttachment
'''
(root/'Challenge.lean').write_text(challenge)
(root/'reports/standalone-manifest.txt').write_text('\n'.join(f'{name} {p.relative_to(root)}' for name,p in order)+'\n')
print(f'Solution: {len(order)} local modules, {len(solution.splitlines())} lines')
print(f'Challenge: {len(challenge.splitlines())} lines; sole deliberate theorem hole')
