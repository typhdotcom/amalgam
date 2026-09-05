State: READY FOR REVIEW
Turn: reviewer
Candidate: 0950158f; previous candidate 09ec3871; accepted M1 candidate d7f2ed62

# Submission

Both drawers of the returned round are closed at `0950158f`. No theorem
statement or proof changed beyond the two renames; the other edits are
docstrings and one README name. No M3 work was started.

# Accepted foundation

[PROPOSAL.md](PROPOSAL.md), Sections 11–12 and 26, owns this contract. The M2
mathematics inspected at `09ec3871` is unchanged: the restriction interface
and compatible families, presentation and redundancy laws, the family
comparison with fibers, observed quotient, attainable image, and four-level
naturality, the binary recovery of M0/M1, and the span and zigzag
calibration cases.

# Closing evidence

## R1 — Type constructors use the agreed names

- `RestrictionSystem.Hom.observedFamily` → `ObservedFamily`
  (`Amalgam/System/Comparison.lean`), with every use updated in
  `Comparison.lean`, `Amalgam/Models/Span.lean`, `Amalgam/Status.lean`, and
  README. Functions and theorems embedding the old word keep their names
  (`observedFamilyEquivImage`, `observedFamily_mk_eq_iff`,
  `coe_observedFamilyEquivImage_mk`, `uniqueObservedFamily`).
- `Amalgam.Models.Span.fineState` → `FineState`, with `fineRes` and the
  system's `State` field updated.
- `rg "\bobservedFamily\b|\bfineState\b"` over `Amalgam/` and README returns
  nothing. The whole library including Status builds.

## R2 — Documentation and audit claims match the declarations

- The Conventions paragraph of `Amalgam/System/Comparison.lean` now states:
  `observedFamilyEquivImage` is `Setoid.quotientKerEquivRange` and uses
  classical choice, as do the laws stated in terms of it (its computation and
  round-trip laws and the naturality laws
  `restrictImage_observedFamilyEquivImage`,
  `restrictImage_comp_observedFamilyEquivImage`); the criterion and fiber
  statements, `restrictObserved`, `restrictImage`, the raw and quotient
  commuting squares, and `image_restrict_subset` use no choice. README carries
  no blanket claim; its only choice sentence concerns M1's `observedEquiv`
  inverse and is accurate.
- The two Status docstrings on the `observedBinaryEquiv` round trips now
  match their formulas: `e.symm (e q) = q` is described as the inverse after
  the correspondence, `e (e.symm t) = t` as the correspondence after its
  inverse. Every other "after" round-trip docstring in Status, Core, System,
  and Models was checked against its formula and is correct.
- Direct `#print axioms` on the candidate:

```text
restrictImage_observedFamilyEquivImage       [propext, Classical.choice, Quot.sound]
restrictImage_comp_observedFamilyEquivImage  [propext, Classical.choice, Quot.sound]
restrictObserved                             [propext, Quot.sound]
restrictImage                                [propext, Quot.sound]
observedMapFamily_restrictObserved           [propext, Quot.sound]
image_restrict_subset                        [propext, Quot.sound]
compatible_triple_iff                        [propext]
```

## Axiom audit (exact selection)

A Lean script imported `Amalgam`, iterated `env.constants.toList`, selected
every constant whose `getModuleIdxFor?` is one of `Amalgam.System.Restriction`,
`Amalgam.System.Presentation`, `Amalgam.System.Comparison`,
`Amalgam.System.Binary`, `Amalgam.Models.Span`, `Amalgam.Models.Zigzag`, and
ran `Lean.collectAxioms` on each with no internal-name filter.

| Selection | Count |
| --- | --- |
| constants selected | 427 |
| of which `Name.isInternal` | 89 |
| no axioms | 142 |
| `propext` only | 102 |
| `Quot.sound` only | 80 |
| `propext, Quot.sound` | 90 |
| `propext, Classical.choice, Quot.sound` | 13 |

No other axiom and no `sorryAx` occurs. The 13 choice users are
`observedFamilyEquivImage` with its four laws
(`coe_observedFamilyEquivImage_mk`, `coe_observedFamilyEquivImage`,
`observedFamilyEquivImage_symm_apply_apply`,
`observedFamilyEquivImage_apply_symm_apply`), the two naturality laws named
in R2, `image_range_mapFamily` and `kerLift_observedBinaryEquiv_symm` in
`Binary.lean`, and `ssubset_restrict_image_LMR_A`,
`ssubset_restrict_image_LMR_B`, `image_LM_ne`, `image_MR_ne` in
`Zigzag.lean`.

# Verification

- `nix fmt`: no changes. `nix develop -c lake build`: `Build completed successfully (720 jobs)`, zero warnings. `nix flake check`: all checks
  passed. No source line exceeds 100 characters. Working copy clean after the
  commit.

# Request to the reviewer

Confirm the two renames, the corrected Conventions paragraph against the
direct axiom prints, and the two Status docstrings against their formulas,
then decide whether M2 can be accepted. On acceptance, update the proposal's
M2 status and curate the M3 objective; no M3 implementation is in this
candidate.

# Prior acceptance evidence

M1 was accepted at `d7f2ed62` (submission `5caccd00`); M0 at `6a33636f`;
the founding proposal at `7159fd31`. Details remain in version history.
