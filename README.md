# Attaching arbitrary families of two-cells

Lean development of the full two-cell attachment theorem (Hatcher Proposition 1.26).
This is an in-progress formalization, not yet a verified proof of the main theorem.

For an arbitrary path-connected topological space X and any indexed family of continuous
maps from the unit circle into X, the project constructs the actual adjunction quotient
of X with an indexed coproduct of closed complex disks. The target says that the actual
inclusion induces a surjective fundamental-group map with kernel the normal closure of
the attaching loops, conjugated along chosen basepoint paths. The quotient isomorphism
must commute with this map. There are no finiteness, CW, separation, local-connectivity,
or semilocal-simple-connectivity hypotheses.

## Current compiled infrastructure

- Adjunction: boundary-generated quotient topology and genuine continuous maps
- NormalForm: algebraic classification of quotient points, without a topology substitution
- OpenCover: genuine disk interiors and complement of all centers form an open cover
- Embeddings: original X is closed embedded; coproduct of all interiors is open embedded
- Radial: explicit jointly continuous radial deformation of the punctured closed disk
- CircleGenerator: actual exp(2πt) generator and its fundamental-group spanning theorem
- GroupQuotient: normal-closure algebra and compatible quotient equivalences
- Statement: exact arbitrary-family target proposition; it asserts no unproved theorem

Geometric retraction descent, disk/annulus homotopy types, van Kampen assembly,
surjectivity and reverse kernel inclusion remain proof obligations.

## Pins and development

Lean: leanprover/lean4:v4.35.0-rc2
Mathlib: 065356127b1dc0016f66b7283ce0ce2c4055aa55

The local env.sh points only to a previously verified readonly compiler and mathlib
cache. scripts/lean-file.sh writes this project's own compiled outputs. It does not
modify the reused project or dependency cache.

## Attribution

Source: Allen Hatcher, Algebraic Topology, pp. 50–51, Proposition 1.26
https://pi.math.cornell.edu/~hatcher/AT/AT..pdf#page=59

The ordinary fundamental-groupoid van Kampen theorem is reused from
Arthur742Ramos/classical-svk-lean at 874680e16db88b4a41daadf56eafbac79fd2f748.
Its exact provenance, Apache-2.0 and vendored MIT licenses remain preserved under vendor/.
The inherited path-subdivision helpers originate with Basold, Bruin and Lawson.
The circle module preserves the upstream Ruize Chen and supporting mathlib copyright,
license notices and exact revision links for its minimal rc2 backport.

Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy Jose Guerra Barretto de Queiroz
Sole responsible maintainer: Arthur Freitas Ramos

No mathematical novelty or worldwide first-formalization claim is made.
No registry submission or acceptance is asserted.
