# Fundamental groups of arbitrary two-cell attachments

A complete Lean formalization of Hatcher's Proposition1.26(a), with the actual
adjunction quotient and the actual inclusion-induced fundamental-group map.

For an arbitrary path-connected topological space X, basepoint x₀, and any
indexed family of continuous attaching maps S¹→X, construct Y by attaching a
coproduct of closed two-disks along their prescribed boundaries. The theorem
proves:

- π₁(X,x₀)→π₁(Y,j(x₀)) induced by the genuine inclusion j is surjective
- Its kernel is exactly the normal closure of the once-around attaching loops,
  conjugated along the specified paths from x₀ to the attaching basepoints
- The quotient group isomorphism commutes with that actual induced map

Space and index universes are independent. There are no finiteness, countability,
CW, separation, local-path-connectivity or semilocal-simple-connectivity hypotheses.
Empty, repeated, constant and noninjective attaching families are included.

## Proof

The carrier is literally the boundary-generated quotient of X⊕Σ i,D², with
Mathlib's quotient topology. Its interiors form the actual disk coproduct.
Removing all disk centers yields an open neighborhood with a proved jointly
continuous radial deformation onto X. The overlap is the actual coproduct of
punctured open disks, each homotopy equivalent to its radius-half circle.

The ordinary all-object groupoid van Kampen theorem is applied to this genuine
open cover. A local categorical argument constructs componentwise coordinates,
descends quotient-valued functors and glues natural transformations to prove
surjectivity and the exact kernel. The radial paths identify these geometric
relators with the requested attaching loops; the first isomorphism theorem
supplies the compatible quotient equivalence.

No geometric retraction, exactness claim or quotient identity is assumed.

## Files

- Challenge.lean: independent construction and exact target; one deliberate theorem hole
- Solution.lean: complete standalone proof importing Mathlib only, no admissions
- CellAttachment/: readable canonical geometric/algebraic proof modules and28 adversarial checks
- Lean4/ and ClassicalSVK/: precisely credited ordinary SVK source closure
- scripts/build_standalone.py: reproducible standalone generation
- reports/: exact-scope independent reviews and local verification logs

The generated Solution omits only blank lines, retaining mathematical source and
license notices, to meet the current10,000-physical-line cap. Canonical modules
retain readable layout. Comparator has no definition holes: its transitive
statement closure must match the construction and theorem definitions exactly.

## Reproduction

Lean leanprover/lean4:v4.35.0-rc2; Mathlib065356127b1dc0016f66b7283ce0ce2c4055aa55.
With an official Lean/elan installation, in a fresh checkout:

    lake exe cache get
    python3 scripts/build_standalone.py
    lake build

Exact dependency pins and development-only readonly cache reuse are described in
SETUP.md. Generated caches and checker exports are excluded from the source.

## Verification status

The main theorem, the post-module-port whole-source aggregate and the standalone
proof compile. Independent statement, modular implementation and adversarial
reviews passed. On the frozen standalone proof, fresh Lean default/paranoid
checkers, NanoDa with only the three standard axioms, and con-ron --verified all
passed. Axiom audits report only propext, Classical.choice and Quot.sound.

The local Comparator from-export run completed its statement/dependency and
axiom phase, then its sandboxed checker was blocked by a network-namespace
permission. Its overall verdict is not passed. Official hosted mechanical
verification and trusted rendering remain separate required gates; local replay
is not an official runner-profile verdict. No sandbox bypass, registry submission
or registry acceptance is asserted.

## Attribution

- Allen Hatcher, Algebraic Topology, printed pp50–51, Proposition1.26:
  https://pi.math.cornell.edu/~hatcher/AT/AT..pdf#page=59
- The pinned ordinary groupoid SVK formalization:
  https://github.com/Arthur742Ramos/classical-svk-lean/tree/874680e16db88b4a41daadf56eafbac79fd2f748
- Basold, Bruin and Lawson's credited constructive path-descent infrastructure
- Mathlib's circle/covering contributors, including the fully credited minimal
  Ruize Chen winding-number backport retained on the required rc2 toolchain

PROVENANCE.md and preserved Apache-2.0/MIT notices give exact source details.
The theorem is classical; no mathematical novelty or worldwide first claim is made.

Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy Jose Guerra Barretto de Queiroz
Sole responsible maintainer: Arthur Freitas Ramos

Construction and separate mathematical/proof reviews were AI-assisted. Formal
kernel checking is the proof-validation mechanism; no human-review claim is made.
