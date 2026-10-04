# Independent statement review

Reviewed 2026-10-04 UTC, before the main attachment theorem was implemented.

## Verdict

**Statement fidelity passes.** `CellAttachment.completeStatement` preserves the requested arbitrary-family theorem for ordinary continuous-path fundamental groups. This review verifies definitions and the target proposition; it does not certify a proof of that proposition.

Hatcher's Proposition 1.26 starts with a path-connected space and a collection of continuous attaching maps. Its statement has no CW, finiteness, Hausdorff, or local path-connectedness hypothesis: [printed pp. 50–51](https://pi.math.cornell.edu/~hatcher/AT/AT..pdf#page=59).

## Definition audit

- **Independent universes:** the elaborated declaration is `completeStatement.{u,v}` with `X : Type u` and `ι : Type v`. Both instantiations `{0,1}` and `{1,0}` typecheck. `Space f : Type (max u v)`; the source fundamental group and its normal closure remain in universe `u`.
- **Only path-connectedness on X:** the target quantifies `[TopologicalSpace X] [PathConnectedSpace X]`, arbitrary `f`, arbitrary `x₀`, and an explicit family `γ : ∀ i, Path x₀ (f i 1)`. It contains no separation, local connectivity, countability, finite-index, CW, injectivity, or nonempty-index assumption. Nonemptiness of X in `PathConnectedSpace` causes no extra restriction because a basepoint is already supplied.
- **Actual two-disks:** `Disk` is the closed complex unit disk `{z : ℂ // ‖z‖ ≤ 1}`; `Circle` is the complex unit circle. `boundaryInclusion` is their usual continuous boundary embedding.
- **Actual disjoint union:** `Raw X ι = X ⊕ (Σ _ : ι, Disk)`. Mathlib's sigma topology is the topological coproduct topology, with no topology on the index type and no requirement of joint continuity in the index.
- **Actual adjunction quotient:** `Space f = Quot (AttachingRel f)`. The relation has exactly one constructor, identifying each disk-boundary point with its prescribed image in X. `Quot` implements the generated equivalence relation. Its topology is Mathlib's `coinduced (Quot.mk _)` topology, and `quotientMap_isQuotientMap` proves the genuine quotient-map property. No group quotient, normal closure, or desired fundamental-group conclusion occurs in this construction.
- **Actual induced map:** `inclusionPi1` is `FundamentalGroup.map (inclusion f) x₀`, with target based at the actual image of `x₀`.
- **Correct chosen-path relators:** `attachingLoop` traverses `γ i`, the mapped circle generator, then `(γ i).symm`. The relator subgroup is exactly `Subgroup.normalClosure (Set.range attachingLoopClass)`.
- **Genuine generator:** `circleGenerator` is based at 1 and is the complex loop `t ↦ exp(2π i t)`. Its compiled integer-valued equivalence sends its class to 1, and `circleGenerator_generates` proves every circle class is an integer power. Fixing the source basepoint to 1 is a standard circle-coordinate convention and does not restrict the attaching maps.
- **All requested conclusions:** the proposition separately demands surjectivity, equality of the actual kernel with the specified normal closure, and a multiplicative quotient equivalence whose homomorphism composed with `QuotientGroup.mk'` equals `inclusionPi1`.

### Exact Mathlib convention

`FundamentalGroup.mul_def` is **`p * q = q.trans p`**. Group multiplication reverses chronological path concatenation. The statement correctly defines relators using `Path.trans`, so it does not mechanically misread Hatcher's word order. `fundamentalGroupMulEquivOfPath γ` transports from the initial basepoint to the terminal one; its inverse transports a loop back along the chosen whisker. See the [pinned primary source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/AlgebraicTopology/FundamentalGroupoid/FundamentalGroup.lean).

## Remaining proof obligations and routes

**Global SVK route.** Hatcher enlarges the attachment by strips along the chosen paths. Removing one point in each disk gives a neighborhood retracting onto X; removing X gives a contractible set. Their overlap has circle generators corresponding to the whiskered attaching loops. A further open-cover calculation identifies the image subgroup, and van Kampen gives the quotient. Prove every claimed openness, retraction, overlap generator, and basepoint identification in the actual quotient topology. Handle the empty family separately when this construction selects an overlap basepoint.

**Finite-reduction alternative.** For one cell, use the cover by the complement of the disk center and the open disk interior; their overlap is a punctured open disk. Combine radial retraction, basepoint transport, and SVK. Induct over finite families. For an arbitrary family, prove that every compact subset meets only finitely many disk interiors: selecting one point per met interior gives a closed discrete subset, since its quotient preimage is empty in X and a closed singleton or empty set in each disk. Such a subset of a compact space must be finite, without any separation assumption on X. Finite subattachments are closed embedded subspaces by componentwise closed-set tests. Compact images of loops and nullhomotopies then factor continuously through finite subattachments.

**Joint homotopy continuity.** A homotopy must be continuous on `Space f × I`, not merely continuous at each fixed time. Product with the compact Hausdorff interval preserves quotient maps: [Hatcher, Appendix Proposition A.17, printed p. 532](https://pi.math.cornell.edu/~hatcher/AT/AT..pdf#page=541). Do not assume the full attaching quotient map is open or closed.

## Degenerate cases and verification

The target accepts empty families, constant attaching maps, repeated maps, and noninjective maps. Empty families have no relators and recover X; constant maps contribute trivial relators. The boundary relation never identifies distinct original points, as the proved `inclusion_injective` confirms. Different chosen whiskers give conjugate classes and hence the same normal closure.

`GroupQuotient.lean` supplies conditional algebraic first-isomorphism tools; its surjectivity and kernel premises are not silently installed as geometric assumptions. No `sorry`, `admit`, or custom `axiom` occurs in the four inspected definition dependencies. Independent compiled axiom checks for the circle-generator theorem, quotient-map theorem, original-space injection, and quotient-equivalence compatibility report only `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.

All four source files independently elaborated successfully with the project's Lean 4.35.0-rc2 environment. Reviewed SHA-256 snapshots:

- `Adjunction.lean`: `d85ffe317f2b65937de9174837ef186abda3421c6e6dabe68b8253ea27cef0d8`
- `CircleGenerator.lean`: `e4f17854294d73c7907da72039199a83727c983ccc9536bea57500711cde84f9`
- `GroupQuotient.lean`: `cc112c0e6fc6698abf14eb40c188ebbe5578bb8abb38fc176e8ca27aa00e7c6f`
- `Statement.lean`: `455aa1e90de9ecb5543d22a0220352fdceffbb1b2917631f09f584f27206fb19`

No implementation source was edited by this reviewer.
