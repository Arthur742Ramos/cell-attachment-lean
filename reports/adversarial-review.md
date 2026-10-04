# Adversarial and degenerate examples

## Scope

`CellAttachment/Examples.lean` imports only the completed theorem module
`CellAttachment.Main`, never `Challenge` or the generated standalone `Solution`.
Its declarations use `module`, `public import`, and an `@[expose] public section`.
All examples concern the actual `Space f`, `inclusion f`, and `inclusionPi1 f x₀`.

The generic declarations require only `TopologicalSpace X` and, where exactness
is invoked, `PathConnectedSpace X`. They do not require `Finite ι`, `Fintype ι`,
Hausdorffness, a CW structure, or any local-connectivity instance. The subgroup
calculations and nullity of constant-map relators do not even require
path-connectedness.

## Proved expected outcomes

1. **Empty family.** For an arbitrary empty index type, the relator normal closure
   is bottom. The actual inclusion homomorphism has bottom kernel and is
   bijective. `empty_inclusionPi1Equiv` is constructed from that homomorphism,
   and its application lemma proves equality with the actual inclusion on every
   group element. `empty_index_bijective` specializes this to `Empty`.
2. **Constant maps and arbitrary whiskers.** For any index type and arbitrary
   values `y : ι → X`, `constant_attachingLoopClass` proves every whiskered
   relator equals `1`, even if the chosen whisker is not constant. It proves the
   image of the generator is the constant path and cancels the whisker with its
   reverse in the path-homotopy quotient. Thus the normal closure and the actual
   inclusion kernel are bottom, and the actual inclusion is a group equivalence.
   Its application lemma again identifies the equivalence with the actual map.
3. **Singleton constant attachment.** `singleton_constant` specializes the
   preceding statements to a single `Unit`-indexed two-cell and an arbitrary
   path from `x₀` to the attaching value.
4. **Genuinely infinite family on arbitrary X.**
   `countably_infinite_constant` uses `ℕ` as its index and permits different
   attaching values and arbitrary chosen whiskers at every index. It proves
   bottom relator normal closure and bijectivity of the actual inclusion, rather
   than merely restating general exactness.
5. **Repeated and noninjective maps.** `repeated_normalClosure` proves that
   duplicating every map through `ι × Bool → ι` leaves the source normal closure
   unchanged. `repeated_inclusionPi1_kernel` proves equality of the kernels of
   the actual maps into the two different attachment spaces. The duplicated
   family is proved noninjective for every nonempty `ι`. Every constant circle
   map is separately proved noninjective by the distinct points `-1` and `1`.
6. **Both independent universe orderings.**
   `index_higher_pi1_bijective` uses `X = Unit : Type 0` and the infinite
   `ι = ULift.{1} ℕ : Type 1`; `space_higher_pi1_bijective` reverses the ordering
   with `X = ULift.{1} Unit : Type 1` and `ι = ℕ : Type 0`. The corresponding
   `*_quotient_compatible` declarations directly invoke the full theorem at
   universe levels `.{0,1}` and `.{1,0}`, including its equality with the actual
   inclusion homomorphism.
7. **Non-Hausdorff space with nonconstant attaching maps.** `IndiscreteTwo` is
   a finite two-point type with the indiscrete topology. Path-connectedness is
   obtained from that topology, and it is proved not even T₀, hence not T₂.
   `indiscreteTwo_arbitrary_family` proves triviality of the attached space's
   actual fundamental group for every family of continuous maps into this
   space. `nonconstantIndiscreteMap` sends `1` and `-1` to distinct points and
   is proved nonconstant. `indiscreteTwo_infinite_nonconstant` attaches an
   infinite repeated family of these nonconstant maps and proves the target
   fundamental group is a subsingleton.

## Verification

The canonical module compiled warning-free with exit code 0 on 2026-10-04:

```sh
./scripts/lean-file.sh CellAttachment/Examples.lean
```

A separate `module`-based probe publicly imports `CellAttachment.Examples` and
checks its exported declarations and their axiom dependencies. Both checks use
the freshly rebuilt canonical `Main` dependency chain, not a legacy import or
the generated standalone solution.

`#print axioms` has been checked for `cell_attachment_exact`,
`two_cell_attachment`, and all 28 named definitions/theorems in the examples.
The only dependencies reported are the ordinary Lean foundational axioms
`propext`, `Classical.choice`, and `Quot.sound` (the finite test carrier itself
has no axiom dependency). No `sorryAx` or additional proof axiom is reported.

The example source contains none of `sorry`, `admit`, `axiom`, `unsafe`,
`implemented_by`, `extern`, or `native_decide`.

No heavyweight dependency build was run. The checks use the project's `env.sh`
and pinned Lean `4.35.0-rc2` / mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55` environment.

Example source SHA-256:
`55ad5fd47a8a47661f2973b60f0024b1abdf7a2a0e01adfe0fdd137c7fc11ac8`.
