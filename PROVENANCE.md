# Source and proof provenance

## Mathematical source

The target is Hatcher, Algebraic Topology, Proposition 1.26(a), printed pages50–51:
https://pi.math.cornell.edu/~hatcher/AT/AT..pdf#page=59

It is a classical theorem. This development asserts no mathematical novelty,
worldwide first formalization, human review, or registry acceptance.

## Exact dependency pins

- Lean4.35.0-rc2, compiler11acb17ec6b07a8f9e9173e6845197929540936b
- Mathlib065356127b1dc0016f66b7283ce0ce2c4055aa55
- Ordinary groupoid SVK source:
  https://github.com/Arthur742Ramos/classical-svk-lean/tree/874680e16db88b4a41daadf56eafbac79fd2f748
- Inherited constructive subdivision source:
  https://github.com/Dominique-Lawson/Directed-Topology-Lean-4/tree/009529606c66d37ef93b4b81b8587f71ce4d2c56

Only the 34-module imported ordinary SVK helper closure is copied into Lean4/
and ClassicalSVK/. Neither upstream Challenge nor an admitted result is copied.
The new first-party quotient/geometry/vertex-group proofs are in CellAttachment/.

Basold, Bruin and Lawson's path-subdivision and homotopy-grid infrastructure is
used through the explicitly credited ordinary-groupoid bridge. No claim of
independent authorship of that infrastructure is made. The inherited provenance,
original source manifest, licensing and compatibility-port account remain under
vendor/svk-provenance/. Lean4/LICENSE.md preserves the upstream MIT license and
copyright; first-party project sources are Apache-2.0. The flattened Solution
also includes the MIT notice, so distributing it separately preserves attribution.

## Circle backport

CellAttachment/CircleGenerator.lean minimally backports the actual circle
winding-number theorem and required supporting calculations from Mathlib
389347a7c1cfa76f6bd5be2ca35d4cb621610ad3. It retains the Ruize Chen, Junyan Xu,
Chris Hughes and Snir Broshi notices and exact file links. No newer toolchain or
unacknowledged theorem axiom is introduced. Project-specific concrete complex-circle
generator and integer-power spanning proofs follow the credited section.

## Module visibility port and standalone generation

For the current official policy, the copied and authored canonical modules use
module headers, public imports and exposed public sections. This is a mechanical
visibility port; mathematical definitions and proof bodies are retained. The
copied-source comparison and SHA-256 manifest record exact upstream/local files.

scripts/build_standalone.py orders the actual local dependency graph, removes
only import/module-wrapper commands while preserving source content, confines
module-local scopes in sections, and emits the complete Solution. Only blank
physical lines are omitted in this generated artifact to meet the10,000-line
cap. The readable canonical modules retain their layout and documentation.

The independently generated Challenge contains only the actual adjunction,
concrete once-around circle loop and complete theorem definitions, plus a single
deliberate target theorem hole. It never imports the proof package. Comparator
has no configured definition holes, so its ordinary transitive statement closure
must match these constructions exactly.

## Authorship and assistance

Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy Jose Guerra Barretto de Queiroz
Responsible maintainers: Arthur Freitas Ramos, David Barros Hulak, Ruy Jose Guerra Barretto de Queiroz

Lean construction and separate statement, implementation and adversarial reviews
were AI-assisted. Mathematical/proof scope, actual source hashes and kernel
results are documented without substituting review opinion for kernel checking.
