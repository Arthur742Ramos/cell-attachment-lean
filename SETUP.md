# Reproduction and verification

The package pins Lean leanprover/lean4:v4.35.0-rc2 and Mathlib commit
065356127b1dc0016f66b7283ce0ce2c4055aa55 in lean-toolchain, lakefile.toml and
the complete committed lake-manifest.json.

## Normal fresh checkout

Use an installed official elan/Lean setup, then from the repository:

    lake exe cache get
    python3 scripts/build_standalone.py
    lake build

The root libraries include the complete proof, canonical Challenge and Solution,
and precisely copied ordinary SVK dependency modules. Challenge intentionally
has one target theorem hole; no proof library/Solution admission is permitted.

## This cloud development workspace

The project-local env.sh reuses the exact prior compiler and Mathlib cached
imports read-only. No earlier project source, build cache or global user shell
configuration is modified. Each source compile writes only this project's
.lake/build/lib/lean. From the project:

    source env.sh
    python3 scripts/build_all.py

This serial source-based aggregate checks all submitted Lean module sources,
including the standalone artifacts. It is not represented as a fresh network
Lake dependency installation or as the official hosted execution profile.

## Gates and scope

The modular proof and first complete standalone replay passed before the
mechanical module-system port. The fresh whole-package post-port replay passed
on2026-10-04; its command/output is in reports/post-port-build-all.log. Canonical
adversarial examples also passed. Separate reviewers' reports record their exact
reviewed source hashes; the later standalone/post-port addendum binds final bytes.

Local additional exports and kernels are checked sequentially with the bundled
pinned tools. Their exact targets, source and binary hashes, logs and exit codes
are recorded in reports. Comparator's supported from-export mode, if passed,
compares those exact generated exports; it does not establish the official
pipeline's isolated build/export provenance or resource-profile verdict.

No --inadvisably-no-sandbox flag or bubblewrap/security workaround is used.
A full official hosted mechanical gate and trusted Challenge rendering are
separate workflows. Their conditional exact-bubblewrap AppArmor setup on a
throwaway hosted runner needs project-specific action-time approval before
dispatch. Publishing this source does not authorize registry submission.

Current policy was reverified at PalomarPolicy96b034cc31a72a63d4f4041911dce337a85c9a04;
current workflow/pipeline at PalomarSubmission65f0154ed776cd26c224254aa57b379137f28b0d.

## Reproduce the separate direct gates

After a normal fresh build, run from the repository root:

    mkdir -p .toolchain/audits
    lake env leanchecker Solution
    lake env leanchecker-paranoid Solution
    lake env leanexport Solution -- $(python3 -c 'import json; print(" ".join(json.load(open("reports/export-targets.json"))))') > .toolchain/audits/solution.ndjson
    lake env nanoda_bin reports/nanoda-config.json
    lake env con-ron --verified --jobs=4 .toolchain/audits/solution.ndjson

The export target list contains the exact pinned toolchain primitive targets,
quotient primitives, main theorem and permitted axioms. reports/nanoda-config.json
uses a relative export path and forbids every additional axiom. These are the
separate direct gates; they must not be relabeled a passing Comparator or official
hosted pipeline verdict.
