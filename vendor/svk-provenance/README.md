# Classical Seifert–van Kampen theorem in Mathlib

This Lean project proves that for every topological space \(X\) and open cover
\(X = U \cup V\), the square of inclusion-induced functors

\[
\Pi_1(U \cap V) \longrightarrow \Pi_1(U),\quad
\Pi_1(U \cap V) \longrightarrow \Pi_1(V),\quad
\Pi_1(U),\Pi_1(V) \longrightarrow \Pi_1(X)
\]

is a pushout in `Cat`. The fundamental groupoids are Mathlib's ordinary
continuous-path groupoids. The statement has no chosen basepoint, path
connectedness assumptions, or separation assumptions; it retains every point
as an object and therefore also handles a disconnected intersection.

The proof uses Mathlib's continuous paths and endpoint-preserving homotopies.
It gives each space the indiscrete preorder, so the auxiliary path and
homotopy types coincide with the ordinary topological ones; the project proves
inverse equivalences and their naturality for inclusions. For the pushout, it
constructs the descent functor from compatible functors on `U` and `V`: paths
are subdivided into pieces lying in the cover, and homotopies are subdivided
into small rectangles. The proof assembles the universal property from these
constructions; it does not invoke the packaged directed van Kampen theorem as
a black box.

The interval-subdivision and homotopy-grid infrastructure is adapted from the
directed-topology formalization by Basold, Bruin, and Lawson. The selected
proof uses those constructive path and homotopy lemmas to build its own
descent functor and universal property; it makes no claim to a new topological
theorem or to independent authorship of the helper infrastructure. The exact
relationship and comparison with the earlier computational-path
formalization are recorded in [PROVENANCE.md](PROVENANCE.md) and
[RESEARCH_INTEREST.md](RESEARCH_INTEREST.md).

## Build and audit

With the pinned Lean toolchain installed, run:

```sh
lake build Challenge Solution
lake env lean scripts/check-closed-statement.lean
python scripts/check-axioms.py
python scripts/check-package.py
python scripts/check-provenance.py
```

`Challenge.lean` imports only Mathlib and contains the selected statement.
`Solution.lean` independently repeats the statement and proves it using the
Mathlib fundamental groupoid. The Comparator configuration selects
`ClassicalSVK.completeStatement` and
`ClassicalSVK.seifert_van_kampen_groupoid`.

The workflows run the pinned Palomar renderer (including its core-notation
audit under Linux Landrun) and the pinned Palomar mechanical verifier. They
prepare verification reports only; they do not create an intake or register a
Palomar entry.

## Status

The candidate now uses Lean `leanprover/lean4:v4.35.0-rc2`, meeting Palomar's
minimum, and Mathlib commit
`065356127b1dc0016f66b7283ce0ce2c4055aa55`. The exact commit and challenge
digest checked by the pinned Palomar renderer and mechanical replay are
recorded in their [workflow runs](https://github.com/Arthur742Ramos/classical-svk-lean/actions).
The prior Lean 4.28 candidate and its receipts are historical; see
[VERIFICATION.md](VERIFICATION.md). These workflows prepare verification
reports only. No Palomar intake, editorial acceptance, or registration is
claimed.
