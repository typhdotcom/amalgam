State: READY FOR REVIEW
Turn: reviewer
Candidate: a1957c29; accepted M3 candidate 08c41b29 (submission b88d4986)

# Submission

M4 — realizability closure on the fixed zigzag — is submitted at `a1957c29`.
M4.1 supplies six explicit abstract targets, one per condition of
`realizable_target_iff`, each violating exactly its condition and proved
nonrealizable through the accepted criterion, plus the theorem that the
adjacent datum itself carries no realizability condition. M4.2 records the
obligation-to-theorem map for Section 31, and the public-surface audit
yielded direct imports, process-free docstrings, and two small theorems. No
theorem debt remains in the declared scope. The shape, datum, candidate
class, and target are unchanged from M3.

# Accepted foundation

[PROPOSAL.md](PROPOSAL.md), Sections 11–14, 26, and 31, owns this contract.
M0 `6a33636f`, M1 `d7f2ed62`, M2 `0950158f`, M3 `08c41b29` are reused
unchanged in statement and proof; this candidate adds declarations, direct
imports, and docstring corrections only.

# Closing evidence

## M4.1 — Strict incompatible targets

`Amalgam/Models/Incompatible.lean` (namespace `Amalgam.Models.Incompatible`),
over the all-singleton `Amalgam.Models.MiddleSplit.coarse`, where every
target entry is `∅` or `Set.univ`. Six abstract `Target coarse` values:

| Target | Violated condition | Other five | Nonrealizable |
| --- | --- | --- | --- |
| `noEmpty` (`empty := ∅`) | `noEmpty_empty_ne_univ` | `noEmpty_satisfies_others` | `noEmpty_not_realizable` |
| `noL` (`l := ∅`) | `noL_l_ne_univ` | `noL_satisfies_others` | `noL_not_realizable` |
| `noM` (`m := ∅`) | `noM_m_ne_univ` | `noM_satisfies_others` | `noM_not_realizable` |
| `noR` (`r := ∅`) | `noR_r_ne_univ` | `noR_satisfies_others` | `noR_not_realizable` |
| `noLR` (`lr := ∅`) | `noLR_lr_ne_univ` | `noLR_satisfies_others` | `noLR_not_realizable` |
| `noJoin` (`lm := ∅`, rest `univ`) | `noJoin_lmr_not_subset_join` | `noJoin_satisfies_others` | `noJoin_not_realizable` |

Each `*_satisfies_others` is the five-way conjunction in the exact shape of
the criterion minus the violated conjunct; each `*_not_realizable` is
`¬ ∃ c : Candidate.{0, 0} coarse, c.target = …`, obtained by projecting the
violated conjunct out of `realizable_target_iff` (`coarse` is
`RestrictionSystem.{0, 0} Context`, so `Candidate.{0, 0}` is the class the
criterion quantifies over). `noJoin_lmr_not_subset_join` exhibits `y₀` in
the `LMR` entry whose `toLM`-restriction would have to lie in `∅`. Shared
certificates: `univ_subset_join_univ_univ`; positive control
`ofDatum_univ_univ_empty_realizable`. The adjacent datum has no extra
condition: `exists_candidate_datum (A A') : ∃ c : Candidate.{w, w} S', c.datum = (A, A')` for any coarse `S'`, from `exists_candidate_iff` at
`T = ∅`. The module docstring separates separate adjacent lifts, coarse
overlap compatibility (the join), simultaneous fine lifting (the full image),
and the residual freedom of the full image inside the join; no common fine
middle representative is inferred and no global assignment is imposed. No
minimality claim. All mirrored in README ("Strict incompatible targets") and
Status (27 typed examples).

## M4.2 — Closure of the declared question

### Obligation-to-theorem map (Section 31)

1. **Datum, comparisons, class, target equivalence fixed and recorded.**
   `System/Zigzag.lean`: `Zigzag.Context` with its order lemmas; families
   `empty`, `single`, `LM`, `LR`, `MR`, `LMR`; the thirteen declared
   `FamilyMap`s. `System/ZigzagTarget.lean`: `Candidate` (fine system,
   morphism, objectwise surjectivity), `Candidate.datum`, `Target` (eight
   subsets), `Candidate.target`, `Family`, `Target.image`. The target
   equivalence is literal equality of eight subsets: `Target.ext`,
   `Target.ext_iff`, `Target.ext_iff_image`.
2. **Datum-induced equivalence classified exactly.** `Candidate.target_eq_iff`
   (independent fine universes), `datum_determines_target_iff`,
   `target_eq_of_join_eq_empty`, `exists_candidate_iff`,
   `exists_candidate_target_iff`, `exists_candidate_target_iff'`: same datum
   is the target equivalence exactly when the join is empty, and otherwise
   splits into classes indexed by the subsets of the join.
3. **Gap to the whole target collection with its maps.** Fixed entries
   `image_empty`, `image_single`, `image_LR`, `Candidate.target_empty/_l/_m/_r/_lr`;
   datum entries `target_lm`, `target_mr`; `Candidate.target_eq_ofDatum` and
   the packaged `Candidate.exists_subset_join_target_eq_ofDatum` (any fine
   universe); induced maps `coe_restrictImage_eq`, `restrictImage_setCongr`,
   `Candidate.restrictImage_setCongr_of_target_eq`, inclusion
   `Hom.image_restrict_subset`. The full-image-only clause is discharged
   because datum plus full image determine the seven other entries, whose maps
   are restrictions of the fixed coarse maps.
4. **Realizability necessary and sufficient, residual freedom characterized.**
   `exists_realization_iff`, `exists_candidate_iff`, `realizable_target_iff`
   with any-universe forward half `Candidate.target_realizable`; necessity at
   any universe `image_LMR_subset_join`, `subset_join_of_images`,
   `Candidate.image_LMR_subset_join`, `subset_join_of_candidate`; construction
   `realize`, `realizeHom`, `surjective_realizeHom`, `image_LM/MR/LMR_realize`,
   `realizeCandidate`; freedom exactly the subsets of the join,
   `unique_full_image_iff`, `image_LMR_determined_iff`; necessity of each
   condition by M4.1.
5. **Strict witnesses and round trips.** No refinement of the datum was
   introduced, so none is owed. Strict pairs `Models/MiddleSplit`
   (`datum_eq`, `target_ne`) and `Models/Zigzag` (`image_LMR_eq`,
   `image_LM_ne`, `image_MR_ne`); collapse `nonempty_LMR_iff_of_subsingleton_middle`.
   Round trips: `observedEquivRange`, `observedEquiv` (with uniqueness),
   `observedFamilyEquivImage`, `binaryEquiv`, `observedBinaryEquiv`, `relabel`,
   `redundancyEquiv`, `restrictEquiv`, `restrictFiberEquiv`, `Span.fiberEquiv`.
   No inverse from targets to fine presentations is claimed; the map from
   candidates to targets is noninjective: `exists_target_eq_not_nonempty_equiv`
   (two candidates of `coarse` with equal targets whose middle carriers are
   not equivalent as types, via `target_realizeCandidate_eq_target_glue`,
   `full_ne_solo_M`, `not_subsingleton_realize_state_M`).
6. **Closure audit.** Below.

### Native-theorem check

Nothing missing for the declared classification. The `Candidate.{w, w}`
restriction on the existential iffs is necessary, not an omission: below the
coarse universe a large coarse carrier admits no objectwise surjection, so the
class can be empty while the join is nonempty; every direction not needing
existence is stated at arbitrary fine universes. One class-level remark, no
change made: surjectivity at `B` and `D` is consumed by no theorem
(`target_l/_m/_r/_lr` use `L`, `M`, `R`; `realize` is surjective
everywhere), so the classification is verbatim exact for the class
"surjective at `L`, `M`, `R`"; the declared class is kept.

### Public surface

- Root `Amalgam.lean` lists all seventeen modules.
- Direct imports added so no module relies on transitive imports:
  `Core/Reduction` (+ `Core.Fiber`), `System/Comparison` (+ `Core.Fiber`),
  `System/Binary` (+ `Core.Comparison`, `Core.Fiber`), `System/ZigzagTarget`,
  `System/ZigzagRealization` (+ `System.Restriction`),
  `System/ZigzagClassification` (+ `System.Comparison`, `System.Restriction`,
  `System.Zigzag`), `Models/Lifting` (+ `Core.Comparison`), `Models/Span`
  (+ `Core.Reduction`, `System.Restriction`), `Models/Zigzag`,
  `Models/MiddleSplit` (+ `System.Restriction`; MiddleSplit also
  `System.ZigzagClassification`); `Models/Overlap` import order sorted.
- Every hypothesis in `System/Zigzag*.lean` and `System/Binary.lean` is
  consumed; universe docstrings match the code.
- Process language removed from 24 docstring sites (milestone labels,
  reviewer references) in `Binary`, `Span`, `ZigzagTarget`,
  `ZigzagClassification`, `Models/Zigzag`, `MiddleSplit`; a stale location
  of `toLM`/`toMR` in `Presentation.lean` corrected; README no longer names
  milestones. Every backticked identifier in module docstrings resolves.
- README-to-Status: the names `stateLMR`, `stateLM`, `stateMR`,
  `Target.ext_iff`, `Candidate.exists_subset_join_target_eq_ofDatum`, and
  `exists_target_eq_not_nonempty_equiv` now have typed examples; every
  declaration name in README appears in Status.

### Research horizon, not debt

The strongest theorem a critic could ask for is recovery of the fine
presentation from the target; the proposal excludes it (Section 31:
observable content need not recover a unique presentation; Section 12 keeps
presentation equivalence a separate target), no presentation equivalence is
defined, and `exists_target_eq_not_nonempty_equiv` shows it is false even at
the level of carrier equivalence. Horizon: a presentation target with a
declared equivalence of fine systems; larger shapes (more interior views, or a
genuine common coarser context of `L` and `R`); observables beyond attainable
images (fiber multiplicities, quotient fibers as data); the Descent bridge;
finite profiles and counts. None changes the fixed datum, target, or class.

# Verification

- `nix fmt`: no changes. `nix develop -c lake build`: `Build completed successfully (726 jobs)`, zero warnings. `nix flake check`: all checks
  passed. `rg "sorry|^axiom" Amalgam`: none. No source line exceeds 100
  characters. Working copy clean after the commit.

- Axiom audit, unfiltered: selection by `getModuleIdxFor?` over all
  seventeen library modules (`Core.Fiber`, `Core.Comparison`,
  `Core.Reduction`, `System.Restriction`, `System.Presentation`,
  `System.Comparison`, `System.Binary`, `System.Zigzag`,
  `System.ZigzagTarget`, `System.ZigzagRealization`,
  `System.ZigzagClassification`, `Models.Overlap`, `Models.Lifting`,
  `Models.Span`, `Models.Zigzag`, `Models.MiddleSplit`,
  `Models.Incompatible`), `Lean.collectAxioms` on every constant:

  | Selection | Count |
  | --- | --- |
  | constants selected (including generated and internal) | 1132 |
  | of which `Name.isInternal` | 232 |
  | no axioms | 371 |
  | `propext` only | 356 |
  | `Quot.sound` only | 130 |
  | `propext, Quot.sound` | 229 |
  | `propext, Classical.choice, Quot.sound` | 46 |

  No other axiom and no `sorryAx`. Change from the accepted M3 selection:
  the six M3-audited modules now hold 428 constants (+1
  `Candidate.exists_subset_join_target_eq_ofDatum`, +6 for the MiddleSplit
  noninjectivity witness: four public theorems and two generated
  auxiliaries), with the same six choice users; the sixteen previously
  existing modules total 1104 constants with 36 choice users; the new
  `Models.Incompatible` adds 28 constants of which 10 use choice, all through
  `Set.empty_ne_univ`: the five `*_ne_univ` theorems and the five
  `*_not_realizable` theorems built on them (`noJoin`'s two use none).
  Choice users in the new work outside `Incompatible`: none. The 36 prior
  users are the M1/M2 quotient-to-image equivalences and their laws, the two
  `Binary` transport lemmas, the eight `decide`-based `Overlap` witnesses,
  and the six model set-inequality witnesses.

# Request to the reviewer

Check the six strict targets against the criterion's conditions, the
obligation map against Section 31, and the public-surface changes. If the
declared obligations are discharged, close the scope explicitly per Section
31; do not open another milestone merely because more theorems are possible.

# Prior acceptance evidence

M3 was accepted at `08c41b29` (submission `b88d4986`); M2 at `0950158f`;
M1 at `d7f2ed62`; M0 at `6a33636f`; the founding proposal at `7159fd31`.
