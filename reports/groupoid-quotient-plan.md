# Groupoid-pushout quotient bridge

## Verified deliverable

`CellAttachment/GroupoidQuotient.lean` compiles with the pinned Lean 4.35.0-rc2 / mathlib revision. It contains no authored `sorry`, `admit`, or custom `axiom`.

The main theorem is:

`CellAttachment.pushout_vertex_quotient_of_component_data`

For a genuine strict categorical pushout of small groupoids

```
A --i--> B
|        |
k        j
|        |
v        v
C --l--> D
```

it proves, for the **actual** functor `j` and base vertex `x : B`:

1. `Function.Surjective (j.mapEnd x)`
2. `(j.mapEnd x).ker = Subgroup.normalClosure (Set.range R)`
3. An equivalence `End x / normalClosure(range R) ≃* End (j.obj x)` satisfying `E(quotient(g)) = j.mapEnd x g`

Here `R a` is exactly the transported overlap generator

`p a ≫ i.map (r a) ≫ inv (p a)`.

Neither surjectivity nor kernel equality is assumed by this theorem.

## Precise geometric/groupoid inputs still required

The theorem's hypotheses are:

- A verified `IsPushout` in `Cat` for `i`, `k`, `j`, and `l`
- Injectivity of `i.obj`
- A base vertex `x` outside the overlap object image: `∀ w, i.obj w ≠ x`
- Connectedness of the left groupoid, expressed as `∀ y, Nonempty (x ⟶ y)`
- An arbitrary component index type `I`
- Component labels `indexA : A → I` and `indexC : C → I`
- Overlap anchors `anchor : I → A`
- Paths `q w : anchor (indexA w) ⟶ w`
- Left anchor paths `p a : x ⟶ i.obj (anchor a)`
- Right component paths `s y : k.obj (anchor (indexC y)) ⟶ y`
- Trivial right vertex groups: `∀ y : C, Subsingleton (End y)`
- Constancy of `indexC` on every right morphism
- Agreement of component labels on overlap objects: `indexC (k.obj w) = indexA w`
- An overlap generator `r a : End (anchor a)` for each component
- Cyclicity at each anchor: every element is `(r a) ^ n` for some `n : ℤ`

These are genuine local geometry hypotheses. They must be proved for the selected open cover of the actual attachment space. This file alone does not assert that the cover exists or that the disk and annulus fundamental groupoids have the required properties.

No finiteness or cardinality assumption is placed on `I`. The empty-index case is allowed when the corresponding hypotheses hold.

## Proof architecture

### Construct the coordinates

`normalizedPaths` chooses left paths normalized at `x`.

`overlapCoordinates` extends the prescribed paths `p (indexA w) ≫ i.map (q w)` from overlap objects to all left objects. Injectivity of `i.obj` makes the prescription well-defined. The basepoint-outside-overlap hypothesis preserves normalization. `exists_overlapCoordinates` packages both properties.

`rightCoordinates` follows the mapped left anchor path and then the chosen right component path. `hom_subsingleton_of_end_subsingleton` derives thinness of each fixed hom-set from trivial right vertex groups. `rightCoordinates_natural` establishes naturality, including transports when component labels are propositionally equal.

`rightCoordinates_match_overlap` proves that left and right coordinates agree on the overlap, with endpoint equality handled by `eqToHom` and heterogeneous equality.

### Derive the kernel

`map_overlapLoop_eq_one` shows a commutative square kills a transported overlap loop whenever its image in the right groupoid is trivial. `normalClosure_overlapLoops_le_ker` packages the normal-closure lower bound.

`overlap_coordinate_eq_one_of_cyclic` and `overlapCoordinates_eq_one_of_cyclic` reduce arbitrary overlap arrows to powers of transported anchor generators.

`basedFunctor` turns the quotient map on `End x` into a one-object quotient-groupoid functor on the whole left groupoid. Its map on `f : y ⟶ z` is the quotient of `p y ≫ f ≫ inv (p z)`. Its overlap restriction is constant because the cyclic generators vanish in the quotient.

The pushout universal property descends this functor against the constant right functor. `pushout_kernel_le_kernel` and `pushout_kernel_le_normalClosure` prove the reverse kernel inclusion from that descent.

### Derive surjectivity

An ordinary `Cat` pushout also glues natural transformations. This is proved by encoding each transformation as a functor into an arrow category:

- `natTransArrow`
- `pushout_natTrans_exists`

This argument uses the given strict categorical pushout directly; it does not assume a separate bicategorical van Kampen theorem.

The descended quotient functor is followed by the reconstruction functor into the target vertex groupoid. `reconstructionLeft` and `reconstructionRight` construct its local path contractions. Their agreement permits gluing a transformation to the identity functor. At the basepoint its component is the identity, so naturality forces every target loop to lie in the inclusion image. `pushout_mapEnd_surjective_of_contraction` proves this step.

Finally `pushout_exact_of_path_coordinates` and `pushout_vertex_quotient_of_component_data` derive exactness and apply the verified quotient-group first-isomorphism theorem.

## API findings

Relevant existing mathlib APIs:

- `CategoryTheory.End` has a group instance for a groupoid
- `Functor.mapEnd` is the actual induced vertex-group homomorphism
- `FundamentalGroup X x` is definitionally `End (FundamentalGroupoid.mk x)`
- `FundamentalGroup.map f x` is definitionally the induced `mapEnd` of the fundamental-groupoid functor
- `SingleObj G`, `SingleObj.mapHom`, `SingleObj.functor`, and `SingleObj.toEnd`
- `ULift` with the local `uliftCategory` instance keeps the object universe compatible with `Cat`
- `IsPushout.desc`, `IsPushout.inl_desc`, `IsPushout.inr_desc`, `IsPushout.hom_ext`
- `Arrow.mk`, `Arrow.homMk`, `Arrow.leftFunc`, `Arrow.rightFunc`, and `Arrow.leftToRight`
- `Functor.congr_obj`, `Functor.congr_hom`, `eqToHom_map`
- `QuotientGroup.mk'`, `QuotientGroup.mk'_surjective`, `QuotientGroup.ker_mk'`, and `QuotientGroup.eq_one_iff`

`End` multiplication is reverse categorical composition. All transport, cyclic-power, and homomorphism proofs respect that convention.

## Verification

Run:

```
scripts/lean-file.sh CellAttachment/GroupoidQuotient.lean
```

The main theorem, quotient path-coordinate theorem, and natural-transformation gluing theorem depend only on the standard Lean foundations `propext`, `Classical.choice`, and `Quot.sound`; there is no `sorryAx` dependency.

## Instantiation on the actual attachment cover

`CellAttachment/GeometricPushout.lean` is also compiled. Its main theorem is

`CellAttachment.neighborhood_inclusion_vertex_quotient`.

For arbitrary independent universes `X : Type u`, `ι : Type v`, a path-connected `X`, an attaching family `f : ι → C(Circle, X)`, a basepoint `x₀`, and an arbitrary specified path family

`p i : Path (neighborhoodInclusion f x₀) (overlapLeft f (coverOverlapAnchor f i))`,

it proves:

- Surjectivity of the actual `FundamentalGroup.map (neighborhoodToSpace f) (neighborhoodInclusion f x₀)`
- Kernel exactly the normal closure of `neighborhoodTransportedRelator f x₀ p`
- A quotient equivalence commuting with the actual inclusion map

All abstract bridge hypotheses are discharged from `coverPushout`, the actual cover inclusions, `neighborhood_pathConnectedSpace`, `inclusion_not_mem_interiors`, and the proved `CoverModels` component path/thinness/cyclic-generator APIs.

The exposed anchor and generator definitions are exactly:

- `coverOverlapAnchor f i = cellOverlapToOverlap f i (cellOverlapBasepoint f i)`
- `coverOverlapGeneratorClass f i` is `cellOverlapGeneratorClass f i` mapped by that genuine component inclusion

`neighborhoodTransportedRelator_path` identifies the transported class with the actual path formed by `p i`, the mapped half-circle generator, and `(p i).symm`.

`ULift.{u} ι` is used only to instantiate the generic theorem at the common groupoid universe. The lifted index is removed from the relator range before returning the geometric result; no cardinality restriction or equality of user universes is required.

A separate short corollary `inclusionPi1_surjective` derives surjectivity of the original inclusion through the constructed neighborhood equivalence. Identification of transported neighborhood relators with the original attaching-loop classes is handled by the separate `RelatorTransport` module, rather than assumed here.

Both `neighborhood_inclusion_vertex_quotient` and `neighborhoodTransportedRelator_path` have axiom footprint exactly `[propext, Classical.choice, Quot.sound]`.

Verification command:

```
scripts/lean-file.sh CellAttachment/GeometricPushout.lean
```
