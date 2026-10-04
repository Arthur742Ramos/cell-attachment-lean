# Vendored directed-topology source

This module tree is derived from
<https://github.com/Dominique-Lawson/Directed-Topology-Lean-4> at commit
`009529606c66d37ef93b4b81b8587f71ce4d2c56`, under the upstream `Lean4/`
directory (with the upstream root module `Lean4.lean`). The upstream MIT
license is preserved in [LICENSE.md](LICENSE.md), and the source README is
preserved in [README.md](README.md). `vendor-manifest.json` records the SHA-256
of each copied Lean source file both at that commit and in this port.

The port updates old Lean 4.6 / Mathlib APIs for Lean 4.35.0-rc2 and Mathlib commit
`065356127b1dc0016f66b7283ce0ce2c4055aa55`. The compatibility edits are in:

- `Lean4/cover_lemma.lean`
- `Lean4/dihomotopy_cover.lean`
- `Lean4/dihomotopy_flip.lean`
- `Lean4/dihomotopy_to_path_dihomotopy.lean`
- `Lean4/dipath_subtype.lean`
- `Lean4/dipath.lean`
- `Lean4/directed_homotopy.lean`
- `Lean4/directed_map.lean`
- `Lean4/directed_path_homotopy.lean`
- `Lean4/directed_space.lean`
- `Lean4/directed_unit_interval.lean`
- `Lean4/directed_van_kampen.lean`
- `Lean4/dTop.lean`
- `Lean4/fraction_equalities.lean`
- `Lean4/fraction.lean`
- `Lean4/fundamental_category.lean`
- `Lean4/interpolate.lean`
- `Lean4/monotone_path.lean`
- `Lean4/path_cover.lean`
- `Lean4/pushout_alternative.lean`
- `Lean4/trans_refl.lean`
- `Lean4/unit_interval_aux.lean`
- `Lean4/SplitPath/split_dipath.lean`
- `Lean4/SplitPath/split_path.lean`
- `Lean4/SplitPath/split_properties.lean`
- `Lean4/stretch_path.lean`

The path subdivision and homotopy-grid construction formerly grouped with the
final directed theorem in `Lean4/directed_van_kampen.lean` is extracted into
`Lean4/path_descent_helpers.lean`. The helper file is attributed to that exact
upstream source and commit in `vendor-manifest.json`; it does not contain or
invoke the packaged directed Van Kampen theorem.

These changes adapt the source to current Lean and Mathlib declarations. The
selected result reuses the path-cover subdivision and homotopy-grid
construction in the `DirectedVanKampen.PushoutFunctor` namespace of
`Lean4/path_descent_helpers.lean`. It does not invoke the packaged
`directed_van_kampen` theorem: `ClassicalSVK.Pushout` directly assembles the
universal property from the descent functor and its factorization and
uniqueness lemmas. The indiscrete-preorder equivalence identifies the source's
auxiliary paths and homotopies with Mathlib's ordinary continuous-path
groupoid. The reused construction is fully attributed in `PROVENANCE.md` and
`formalization.yaml`.
