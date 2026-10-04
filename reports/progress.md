# Historical development checkpoint, 2026-10-04 00:32 UTC

This early infrastructure snapshot predates the completed main theorem. It is
superseded by README.md, the final local kernel logs and later independent reviews.

The exact source pins are fixed. Statement, Adjunction, NormalForm, OpenCover,
Embeddings, Radial, GroupQuotient, CircleGenerator compile independently against
Lean 4.35.0-rc2 and mathlib065356127b1dc0016f66b7283ce0ce2c4055aa55.

Circle infrastructure was minimally backported with proper attribution; no toolchain
migration has occurred. No completed main theorem is asserted. No authored sorry or
custom axiom was introduced in these proof modules. Partial axiom checks report only
propext, Classical.choice, Quot.sound; whole theorem closure and independent kernels
will be checked only after proof assembly.

The arbitrary index universe is independent of X's universe. The raw space is the
actual topological sum X ⊕ Σ i, Disk, avoiding an unintended topology on the index.
The quotient relation is generated only by boundary identifications.

Current active proof obligations: radial descent onto the punctured neighborhood;
homotopy equivalences and overlap generator computation; Cat-pushout-to-vertex-group
surjectivity and exactness; assembly of the exact statement; adversarial examples;
fresh Lean, axiom, NanoDa, con-ron and separately official hosted profile gates.
