# Verified disk, annulus, and actual cover models

## Status

Both `CellAttachment/Annulus.lean` and `CellAttachment/CoverModels.lean` compile on the pinned Lean 4.35.0-rc2/mathlib environment using the project's read-only dependency cache. Neither file introduces a `sorry` or a custom axiom.

## Annulus geometry

- `Annulus` is the genuine punctured open complex unit disk
- `annulusPolar` is continuous polar normalization into `Circle`
- `halfCircle` embeds the radius-half circle into the annulus
- `annulusRadialCoefficient t z = (1-t) + t*(1/2)/‖z‖`
- `annulusRadialDeformation` is continuous, stays nonzero and strictly inside the open disk, starts at the identity, ends at the half-radius polar projection, and fixes the half-radius circle
- `annulusHomotopyEquivCircle` is the proved homotopy equivalence
- The actual convex metric-ball geometry proves `openDisk_contractibleSpace` and `openDisk_simplyConnectedSpace`
- `annulusGenerator t = (1/2) exp(2πt)` and `annulusGenerator_generates` proves every actual based class is an integer power
- `annulusFundamentalGroupEquivInt` is an actual induced isomorphism to `Multiplicative ℤ`, sending the concrete generator to `1`

Reusable helpers: `homotopyEquivFundamentalGroup`, `homotopyEquivFundamentalGroupOfEq`, and `homotopyEquivPathConnectedSpace`. The fundamental-group equivalences have forward maps definitionally equal to the actual induced map / mapOfEq.

## Actual quotient-cover geometry

`CoverModels.lean` imports the existing `CoverPushout.lean` definition of `overlap`, avoiding duplicate constants.

- `overlapHomeomorph` identifies the actual overlap with `Σ i, Annulus`; `interiorsHomeomorph` is the existing interior-coproduct identification
- `cellInteriorHomeomorph` gives each actual cell interior its genuine disk coordinates, and contractible/simply-connected instances
- `cellOverlapHomeomorph` gives each actual overlap component its genuine annulus coordinates and circle homotopy type
- `overlapToInteriors`, `overlapToNeighborhood`, `cellInteriorToInteriors`, and `cellOverlapToOverlap` are actual continuous inclusions with commuting coordinate formulas
- `interiorIndex` and `overlapIndex` are locally constant and constant at every point of any continuous path, and on endpoints of every actual path-homotopy quotient arrow
- `interiorIndex_overlapToInteriors` proves compatibility of the component indices
- `coproductFundamentalGroupEquiv` is genuinely induced by component inclusion, using constant-index loop reconstruction

Global APIs for the groupoid-pushout bridge:

- `overlapAnchor f i : overlap f`
- `overlapAnchorPaths f w : Path (overlapAnchor f (overlapIndex f w)) w`
- `interiorAnchorPaths f v : Path (overlapRight f (overlapAnchor f (interiorIndex f v))) v`
- `interiorVertexGroup_subsingleton f v`
- `overlapAnchorGeneratorClass f i`
- `overlapAnchorGenerator_generates f i γ : ∃ n : ℤ, γ = overlapAnchorGeneratorClass f i ^ n`

The global anchor and generator agree definitionally with the mapped per-cell anchor and generator.

## Attaching-loop identification

- `neighborhoodRetraction_overlap_coordinates` proves the retraction on overlap coordinates is exactly `f i (annulusPolar z)`
- `neighborhoodRetraction_overlapAnchor` identifies the retracted anchor with `f i 1`
- `neighborhoodRetraction_overlapAnchorGenerator` identifies the actual mapped/cast generator path with `circleGenerator.map (f i).continuous`
- `neighborhoodRetraction_overlapAnchorGeneratorClass` proves the actual induced based map sends the global overlap generator to `FundamentalGroup.map (f i) 1 circleGeneratorClass`

## Verification

Commands:

- `./scripts/lean-file.sh CellAttachment/Annulus.lean`
- `./scripts/lean-file.sh CellAttachment/CoverModels.lean`

Kernel axiom audit of the main geometry, generator, overlap-homeomorphism, thin vertex-group, and attaching-class lemmas reports only the usual Lean foundations `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx` or additional axioms.
