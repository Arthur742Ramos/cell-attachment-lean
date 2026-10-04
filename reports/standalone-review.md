# Independent standalone and module-port addendum

Reviewed 2026-10-04 UTC at source checkpoint `6197134ff779870141a99b5cd3c6c593ff7464fe`. This addendum covers the final standalone artifacts and mechanical module port. The earlier statement and modular implementation reports remain historical reviews of their respective snapshots.

## Scoped verdict

**PASS for the final standalone proof, independent construction/statement alignment, reproducible generation, and examined package/workflow preparation.** No mathematical or proof-integrity blocker remains. A stale Challenge hash in the advisory rendering workflow was identified during this review, corrected by the author, and independently rechecked.

**The complete comparator gate and official hosted execution profile are not verified.** The supported local from-export comparator exits 1 when its default-kernel bubblewrap sandbox cannot create a NETLINK_ROUTE socket. Its preceding statement/dependency/axiom comparison phase succeeds. Direct local kernel checks are separate evidence and do not turn that blocked overall result into a comparator pass. No workflow was dispatched or registry submission performed during this review.

## Exact artifacts and reproduction

- `Challenge.lean`: SHA-256 `5cfeb633dc3ebdcc0ed64497421c9e8894cb8541ea4159a45b9d528f88fe112b`; 211 physical lines
- `Solution.lean`: SHA-256 `38d906697acca34d93729f27fa92d5823e12c7dec4812a75b5f57aec69cad22a`; 9,231 physical lines
- Generator `scripts/build_standalone.py`: SHA-256 `9cca478b80ff8d36c8ce7570d5c3b90bde039c9d366ee3c7abede069e77d5baa`

The reviewer copied the canonical source directories, license, and generator into a separate scratch root and ran the generator there. It reproduced both artifacts and `reports/standalone-manifest.txt` **byte-for-byte**. The Solution contains exactly the 55 local modules in the actual final proof dependency graph, followed in dependency order, and imports only external Mathlib modules. Generation removes import/module-visibility wrapper commands, adds named sections and required closing scope commands, and omits blank physical lines. No mathematical declaration or proof body is substituted. Reproducibility here is verified for this exact source corpus, not asserted as a universal property of the lexical scope-counting script.

The Challenge never imports Solution or the proof package. It includes the actual adjunction construction, concrete circle generator definitions, specified whiskered relators, and complete target statement. Its sole deliberate admission is `CellAttachment.two_cell_attachment`; no construction definition is a hole. The complete Solution and its copied source closure contain no authored `sorry`, `admit`, custom `axiom`, or unsafe declaration.

## Module visibility and inherited source

All 34 entries in `reports/vendor-module-port.json` were independently checked against the clean immutable SVK snapshot `874680e16db88b4a41daadf56eafbac79fd2f748`: both recorded SHA-256 hashes match, and normalized source bodies are identical after removing only module/public-section commands, changing `public import` back to `import`, and discarding blank lines. The mathematical SVK/helper content has not changed in the module port.

Canonical modules use module headers, public imports, and exposed public sections. The flattened artifact's per-module sections contain local variables, opens, options, and local instances rather than allowing them to accumulate unintentionally. The final sources compile with those wrappers. Separate smoke modules importing only Challenge or only Solution successfully access the public construction and target declarations and instantiate the final theorem in both universe orders `{1,0}` and `{0,1}`. No explicit private declarations hide the target construction.

The root Apache-2.0 license and `Lean4/LICENSE.md` MIT notice were checked byte-identical to their immutable dependency counterparts. The full directed-topology MIT notice is also present in the standalone Solution. The credited Mathlib circle backport retains its Ruize Chen, Junyan Xu, Chris Hughes, and Snir Broshi attribution and exact upstream file/revision links. Inherited README, provenance, port account, source manifest, and license copies remain under `vendor/svk-provenance/`. This verifies preservation of the supplied licensing and attribution material; it is not a separate legal opinion.

## Independent build, export, and comparison evidence

The reviewer independently compiled the reproduced final Challenge and Solution into a fresh scratch olean tree, both exit 0. Standard `leanchecker Solution` and `leanchecker-paranoid Solution` then independently exited 0 against that tree. The final theorem's fresh axiom audit is exactly `[propext, Classical.choice, Quot.sound]`, with no `sorryAx`, and its two independent universe parameters remain present.

The reviewer exported the configured target closure from those independently compiled artifacts. Both exports exactly match the package's audited export hashes:

- Challenge export: `07a6e56b5b1b538f7ae91a316c73a2564a394effd21072dd843b1e57fe40612a`
- Solution export: `9514a23abb6af38299d467e31561ba087531c2dd7a3e213d7a1fbb037c9be9b7`

The supported from-export comparator command was independently replayed without a sandbox-disabling option. It reaches `Running Lean default kernel on solution` and then encounters the stated NETLINK_ROUTE failure. Inspection of the pinned compiler's `Lake/CLI/Check.lean`, `verifyMatch` (lines 514–527), confirms that `compareAt` and `checkAxioms` must return successfully before `runKernels` prints that message. The committed comparator config has **no definition holes** (`definition_names: []`), so the ordinary transitive statement dependencies and their construction bodies are compared, not merely their types. The local comparator config differs only by disabling its NanoDa invocation; the separately recorded strict NanoDa gate is separate.

The package's final direct NanoDa and con-ron records were examined and bind these same exports: both exit 0. NanoDa uses strict permitted-axiom enforcement and reports no typechecker errors, with one axiom pretty-printer diagnostic. Con-ron uses `--verified` and reports acceptance. These are local targeted-export checks, not official sandbox/resource-profile certification. The post-port whole-source aggregate build is additionally recorded as passing in `reports/post-port-build-all.log`.

## Metadata, pins, and prepared workflows

The toolchain remains Lean 4.35.0-rc2; lakefile and complete manifest pin Mathlib to `065356127b1dc0016f66b7283ce0ce2c4055aa55`. Metadata identifies the classical source, exact proof/backport dependencies, AI-assisted construction/review, deliberate Challenge hole, and absence of novelty, human-review, or registry-acceptance claims. The development environment's cache-reuse script is explicitly separate from portable fresh-checkout Lake instructions.

Both examined workflows are **manual workflow_dispatch only**, use read-only repository permissions, and pin the official reusable workflow/renderer and third-party actions to exact commits. The full verification workflow requires the explicit AppArmor approval input before invoking the pinned conditional installer. The advisory renderer independently binds the dispatched repository/commit, verifies the exact Challenge digest, and guards a conditional exact-bubblewrap AppArmor change. Preparation does not itself authorize dispatch or security-setting changes.

The corrected render wrapper hash is `1181c0cbef6002d5ffc88775d6e346c0241906af6f69a7a3ba96710d8ed504b8`; its hardcoded reviewed statement digest now matches the final Challenge above. The full-verification wrapper hash is `f034f38574cd0ccf04ab89158b087d3c391ad4bfaa833087d26270ef7ec31825`. Both YAML files parse. No security setting was changed, no sandbox bypass was attempted, and no registry or rendering workflow was dispatched by this reviewer.

Complete reviewed final source and package hashes are recorded in `standalone-review-sha256.txt`. No implementation or dependency source was edited by the reviewer.

## Scoped workflow-label correction, 2026-10-04 UTC

After the first hosted full attempt [37168202144](https://github.com/Arthur742Ramos/cell-attachment-lean/actions/runs/37168202144), the second authorization choice in `.github/workflows/palomar.yml` was corrected from `I am submitting on behalf of a responsible author or maintainer` to the pinned backend's exact accepted label, `I have approval from a responsible author or maintainer`.

**This minimal correction passes independent validation.** Git diff against `7a61606c6b511a20178beb26705be5c61a7890b9` contains only that one choice replacement. The reviewer verified `scripts/submission_contract.py` and `scripts/verify_submission.py` against their exact Git blob identities in the cached tree for pipeline commit `65f0154ed776cd26c224254aa57b379137f28b0d`. Both workflow choices are in `AUTHORIZATION_RELATIONSHIPS`; the corrected value maps to `approved`, while the old value is unrecognized. A local `submission_request` smoke using the corrected options and its approved-role lookup succeeds.

The corrected full-verification wrapper SHA-256 is **`dc1df86ef4b874e72e7df1efb3950ec4b5b531052ea15df2cc97fa8f3743e7cf`**. This supersedes only the prior wrapper digest in this review; the earlier source manifest remains a historical snapshot. The proof and standalone artifact hashes, renderer hash, pipeline pin, security-approval guard, and execution profile are unchanged. No proof recompilation was needed for this non-mathematical edit.

The first hosted report's visible diagnostic is `palomar.reporting_failed`. Its logs show the old, unrecognized relationship and `prepare.ready: false`; Lean installation, bubblewrap, and proof execution were skipped. The pinned preparation code rejects that relationship before constructing the source-binding report, which supports the wrapper diagnosis rather than a theorem failure. This correction does not certify a successful retry or a completed official verification gate. The reviewer performed no dispatch, intake, security change, or external outreach.
