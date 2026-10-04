# Provenance

## Selected result

The selected declaration is
`ClassicalSVK.seifert_van_kampen_groupoid` in `Solution.lean`. It states that
the inclusion square of Mathlib's ordinary continuous-path fundamental
groupoids for `U ∩ V`, `U`, `V`, and `X` is a categorical pushout whenever
`U` and `V` are open and cover `X`.

## Formalization dependencies

- Mathlib is pinned to commit
  `065356127b1dc0016f66b7283ce0ce2c4055aa55`. The `Challenge` module imports
  Mathlib only.
- Directed-Topology-Lean-4 is pinned as a source dependency to commit
  `009529606c66d37ef93b4b81b8587f71ce4d2c56`. Its `Lean4/` module tree and
  upstream root `Lean4.lean` are vendored and compatibility-ported here so the
  package builds on Lean 4.35.0-rc2 and the selected Mathlib pin. The selected proof
  reuses constructive interval-subdivision and homotopy-grid lemmas under
  `DirectedVanKampen.PushoutFunctor` in the extracted
  `Lean4/path_descent_helpers.lean`, sourced from upstream
  `Lean4/directed_van_kampen.lean`. It does not invoke
  `DirectedVanKampen.directed_van_kampen`. Instead, it directly assembles the
  pushout universal property using the descent functor and its factorization
  and uniqueness lemmas. Supporting copied source paths and their upstream
  and vendored SHA-256 hashes are recorded in `Lean4/vendor-manifest.json`.
  The upstream MIT license and source README are preserved in
  `Lean4/LICENSE.md` and `Lean4/README.md`. Ported source files and API changes
  are listed in `Lean4/PORTING.md`.
- The new bridge is in `ClassicalSVK/Bridge/`. It gives every space the
  indiscrete preorder, constructs inverse equivalences between the directed
  path category and Mathlib's path groupoid, and proves naturality. Since the
  preorder is indiscrete, these objects are actual continuous paths and
  endpoint-preserving homotopies. The open-cover result uses path subdivision
  and homotopy-grid lemmas to construct its own descent functor.

## Related formalizations

- The immutable source snapshot
  <https://github.com/Dominique-Lawson/Directed-Topology-Lean-4/tree/009529606c66d37ef93b4b81b8587f71ce4d2c56>
  supplies the constructive path subdivision, reparametrization, and
  homotopy-grid infrastructure used in the proof. Its upstream module path is
  `Lean4/directed_van_kampen.lean`; the copied helper source is extracted as
  `Lean4/path_descent_helpers.lean`. The selected declaration directly
  assembles the pushout universal property and does not call the source's final
  `directed_van_kampen` theorem.
- The immutable Mathlib snapshot
  <https://github.com/leanprover-community/mathlib4/tree/065356127b1dc0016f66b7283ce0ce2c4055aa55>
  supplies the ordinary fundamental groupoid, topological subspaces, and
  category-theoretic pushout API.
- The snapshot
  <https://github.com/Arthur742Ramos/ComputationalPathsLean/tree/257c659b7973aeda900d86a5da73b208712c7523>
  contains the author's earlier computational-path SVK developments. No
  source code or proof from that repository is reused. The selected result
  here is an all-object pushout for actual topological subspaces and continuous
  paths, with no basepoint or connectedness hypotheses.
- The Archive of Formal Proofs entry
  <https://isa-afp.org/entries/Seifert-Van-Kampen.html> formalizes a related
  based fundamental-group theorem. It is background only; no Isabelle source
  or proof is reused.

## Licensing and attribution

The first-party project files are licensed under Apache-2.0. The vendored
directed-topology source retains its upstream MIT license and copyright notice
in `Lean4/LICENSE.md`; its authors and exact source revision are identified in
`Lean4/PORTING.md`, `Lean4/vendor-manifest.json`, and `formalization.yaml`.
Mathlib is fetched as a pinned Lake dependency and retains its own license.
