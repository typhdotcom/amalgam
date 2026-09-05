State: READY FOR REVIEW
Turn: reviewer
Candidate: ed91c378; accepted M2 candidate 0950158f; accepted M1 candidate d7f2ed62

# Submission

M3 — the information boundary of adjacent binary images on the zigzag — is
settled at `ed91c378`. The conjecture of M3.3 is true and proved as an
exact if-and-only-if over arbitrary coarse systems: a triple of subsets
`(A_LM, A_MR, T)` is the image datum of a candidate realization exactly when
`T ⊆ J(A_LM, A_MR)`. Combined with M3.2 this classifies every target
collection at fixed supplied datum and gives the exact uniqueness condition
`J(A_LM, A_MR) = ∅`. The strict finite pair of M3.1 is certified through the
family API and agrees with the bounded sweep. No `sorry`, no project axiom;
the M3 modules use no classical choice beyond what is named below. M0–M2
declarations are unchanged except that the zigzag preorder now lives in a
shared shape module consumed by the accepted witness.

# Accepted foundation

[PROPOSAL.md](PROPOSAL.md), Sections 11–14 and 26, owns this contract.

- M0 `6a33636f`, M1 `d7f2ed62`, M2 `0950158f` are reused: `Hom.image`,
  `image_restrict_subset`/`mapsTo_restrict_image` (naturality),
  `restrictImage`, `compatible_pair_iff`, `compatible_triple_iff`,
  `compatible_fin_two_iff`, `uniqueOfIsEmpty`, `observedMapFamily`.
- Carriers may be empty and vary between candidates; fine carriers live in an
  independent universe; no finiteness enters the general laws.
- The target is attainable content: equality of eight subsets of the fixed
  coarse family types; not fiber counts, not presentation equivalence.
- No refinement of the datum, counting hierarchy, scalar invariant, larger
  shape, or Descent bridge was introduced.

# Fixed datum, realizations, and target (as built)

`Amalgam/System/Zigzag.lean` (namespace `Zigzag`): the preorder `Context`
(`L B M D R`; `B ≤ L`, `B ≤ M`, `D ≤ M`, `D ≤ R`, reflexivity, nothing else)
moved here from the accepted model, with its order facts; the eight admissible
families `empty`, `single L/M/R`, `LM`, `LR`, `MR`, `LMR` on `Fin n` in the
order `L, M, R`; the declared forgetful operations `toLM`, `toMR`, `toLR`,
`LMR.toL/toM/toR`, `LM.toL/toM`, `LR.toL/toR`, `MR.toM/toR`, `toEmpty F`,
all with reflexive inequalities. `Amalgam/Models/Zigzag.lean` consumes the
shared shape; its accepted theorems are unchanged.

`Amalgam/System/ZigzagTarget.lean`: `Candidate.{v, w} S'` = fine system
`S : RestrictionSystem.{0, v} Context`, `φ : S.Hom S'`, and
`surjective : ∀ c, Surjective (φ.toFun c)`; nothing else. `Candidate.datum c = (c.φ.image LM, c.φ.image MR)`. `Target S'` has eight `Set` fields with
`@[ext]`; `Candidate.target` collects all eight images; `Family` labels the
eight families and `Target.image` indexes by them.

# Closing evidence

## M3.1 — Finite reconnaissance and a strict information-loss witness

`scripts/zigzag_sweep.py` (`uv run scripts/zigzag_sweep.py`): singleton coarse
objects, fine carriers of size 1–2 at each of the five contexts, all
restriction functions enumerated: 872 systems. Realized `(I_LM, I_MR, I_LMR)`
triples: `(1,1,1)`, `(1,1,0)`, `(1,0,0)`, `(0,1,0)`, `(0,0,0)`. The necessary
condition `I_LMR ≤ min(I_LM, I_MR)` holds on all 872; all 5 allowed triples are
realized; the smallest `(1,1,0)` system has 8 states and needs two middle
states (one middle state forces a full lift). At bound 3 (1,554,228 systems)
nothing changes. Limits: singleton coarse objects only, bounded sizes; a sweep
cannot prove the universal law.

`Amalgam/Models/MiddleSplit.lean` (namespace `Amalgam.Models.MiddleSplit`):
`coarse` all-`Unit`; `split` with `State M = Bool`, `L→B ↦ false`,
`M→B = M→D = id`, `R→D ↦ true`; `glue` all-`Unit`; `φsplit`, `φglue` with
`surjective_φsplit`, `surjective_φglue`. Through the family API:
`compatible_LM_split_iff`, `compatible_MR_split_iff`,
`compatible_LMR_split_iff`, `not_compatible_LMR_split`; `nonempty_LM_split`,
`nonempty_MR_split`, `isEmpty_LMR_split`, `nonempty_LMR_glue`; images
`image_LM_split = univ`, `image_MR_split = univ`, `image_LMR_split = ∅`,
`image_LM_glue = image_MR_glue = image_LMR_glue = univ`; the strict pair
`image_LM_eq`, `image_MR_eq`, `image_LMR_ne`; the named coarse family `y₀`
with `y₀_mem_image_glue`, `y₀_notMem_image_split`; both binary comparisons
surjective on both sides (`surjective_observedMapFamily_LM_split`,
`_MR_split`, `_LM_glue`, `_MR_glue`). No minimality claim.

## M3.2 — Proper-family content fixed by every candidate

`ZigzagTarget.lean`: `compatible_single`, `compatible_LR` (no common coarser
context of `L`, `R`); `image_empty φ = univ` (no hypothesis),
`image_single φ c (h : Surjective (φ.toFun c)) = univ`,
`image_LR φ hL hR = univ`; for candidates `target_empty`, `target_l/m/r`,
`target_lr` (all `univ`), `target_lm = datum.1`, `target_mr = datum.2`,
`target_lmr = image LMR`. Closing equivalence
`Candidate.target_eq_iff (c₁ : Candidate.{v₁,w}) (c₂ : Candidate.{v₂,w}) : c₁.target = c₂.target ↔ c₁.datum = c₂.datum ∧ c₁.φ.image LMR = c₂.φ.image LMR`,
with `image_eq_of_target_eq`. Induced image restriction maps agree:
`coe_restrictImage_eq` (pointwise, any `FamilyMap`, by `rfl` through
`coe_restrictImage`), `restrictImage_setCongr` and
`Candidate.restrictImage_setCongr_of_target_eq` (commuting square with
`Equiv.setCongr`, over every `FamilyMap` between declared families). None of
these assume that the full image projects onto proper images.

## M3.3 — Exact classification of the full image

`ZigzagRealization.lean`: `join A A' := {y | S'.restrict toLM y ∈ A ∧ S'.restrict toMR y ∈ A'}`, `mem_join_iff`. Necessity from M2 naturality with
no surjectivity and any fine universe: `image_LMR_subset_join φ : φ.image LMR ⊆ join (φ.image LM) (φ.image MR)`, `subset_join_of_images`.

Sufficiency by the tagged-copies realization: `TaggedState A A' T c` with
constructors `full (y : T)`, `lm (a : A) (h : c ≤ L ∨ c ≤ M)`,
`mr (a' : A') (h : c ≤ M ∨ c ≤ R)`, `solo (p : Σ d, S'.State d) (h : c ≤ p.1)`;
restriction `TaggedState.res` preserves tags; observation `TaggedState.obs`
reads the dictated coarse state (`stateLMR`, `stateLM`, `stateMR`, with
naturality `res_stateLMR`, `res_stateLM`, `res_stateMR` from coarse
compatibility of the tagged family). `realize A A' T : RestrictionSystem Context` (laws by `cases`), `realizeHom`, `surjective_realizeHom` (solo
copies). Tag classification `res_eq_res_LM_iff`, `res_eq_res_MR_iff`,
`eq_full_of_res_eq`; the five constant-tag fine families `fullFamily`,
`fullFamilyLM`, `fullFamilyMR`, `lmFamily`, `mrFamily` with their `mapFamily`
values. Images: `image_LMR_realize = T` (unconditional),
`image_LM_realize (hT : T ⊆ join A A') = A`, `image_MR_realize hT = A'`.

Exact classification `exists_realization_iff A A' T : (∃ S φ, (∀ c, Surjective (φ.toFun c)) ∧ φ.image LM = A ∧ φ.image MR = A' ∧ φ.image LMR = T) ↔ T ⊆ join A A'`. Uniqueness `unique_full_image_iff A A' : (∀ T₁ T₂ ⊆ join A A', T₁ = T₂) ↔ join A A' = ∅` and, on realizations,
`image_LMR_determined_iff`.

`ZigzagClassification.lean` combines with M3.2: `Candidate.image_LMR_subset_join`,
`subset_join_of_candidate` (any universe); `realizeCandidate A A' T : Candidate.{w,w} S'` with `realizeCandidate_datum hT`,
`realizeCandidate_image_LMR`; `exists_candidate_iff`; `Target.ofDatum A A' T`
with `Target.eq_ofDatum_iff`, `Candidate.target_eq_ofDatum`; classification of
every target at fixed datum `exists_candidate_target_iff A A' t : (∃ c, c.datum = (A, A') ∧ c.target = t) ↔ ∃ T ⊆ join A A', t = Target.ofDatum A A' T` and the eight-field form `exists_candidate_target_iff'`; the exact
uniqueness condition `datum_determines_target_iff A A' : (∀ c₁ c₂, c₁.datum = (A, A') → c₂.datum = (A, A') → c₁.target = c₂.target) ↔ join A A' = ∅`; the
realizability statement `Candidate.target_realizable` (any universe) and
`realizable_target_iff t : (∃ c, c.target = t) ↔ t.empty = univ ∧ t.l = univ ∧ t.m = univ ∧ t.r = univ ∧ t.lr = univ ∧ t.lmr ⊆ join t.lm t.mr`.
The any-universe forward half of uniqueness is `target_eq_of_join_eq_empty {c₁ : Candidate.{v₁,w}} {c₂ : Candidate.{v₂,w}} (h : join A A' = ∅) … : c₁.target = c₂.target`. The strict pair is also packaged as candidates:
`splitCandidate`, `glueCandidate : Candidate coarse` with `datum_eq : splitCandidate.datum = glueCandidate.datum` and `target_ne : splitCandidate.target ≠ glueCandidate.target`.

The missing information is explicit: the datum records the two binary images
but not whether the fine middle states used by an `LM`-lift and an `MR`-lift
coincide; when the join is nonempty, `Target.ofDatum A A' ∅` and
`Target.ofDatum A A' (join A A')` are two distinct realizable targets. No
refinement of the datum is introduced. Universe convention: forward directions
hold for candidates at any fine universe; existential directions produce the
tagged realization in the coarse universe.

**M4 consequence recorded.** `realizable_target_iff` characterizes, with no
further hypothesis, which abstract target collections arise from a candidate
on this shape and datum. The next review decides what closure obligations
remain; this candidate does not claim M4.

## Root exports, README, Status

`Amalgam.lean` imports all seventeen modules. README gained the section "The
zigzag information boundary" (shape and datum; candidates and target; join,
necessity, realization; strict witness and sweep; classification at fixed
datum); `Amalgam/Status.lean` mirrors every sentence under the same headings
at explicit universes. Dependency direction: `System/Zigzag*` import Core,
System, and mathlib only; `Models/MiddleSplit` and `Models/Zigzag` import
System; only the root imports Status.

# Verification

- `nix fmt`: no changes. `nix develop -c lake build`: success, zero warnings.
  `nix flake check`: all checks passed. `rg sorry Amalgam`: none. No source
  line exceeds 100 characters. `uv run scripts/zigzag_sweep.py` reproduces the
  numbers above.
- Axioms (unfiltered selection by `getModuleIdxFor?` over the six modules
  `Amalgam.System.Zigzag`, `ZigzagTarget`, `ZigzagRealization`,
  `ZigzagClassification`, `Amalgam.Models.MiddleSplit`, `Amalgam.Models.Zigzag`,
  with `Lean.collectAxioms`): 413 constants selected, 58 of them
  `Name.isInternal`; 74 use no axioms, 265 only `propext`, 68 `propext, Quot.sound`, 6 `propext, Classical.choice, Quot.sound`; no other axiom and
  no `sorryAx`. The six choice users are the set-inequality witnesses
  `Models.Zigzag.image_LM_ne`, `image_MR_ne`, `ssubset_restrict_image_LMR_A`,
  `ssubset_restrict_image_LMR_B`, `MiddleSplit.image_LMR_ne`, and
  `MiddleSplit.target_ne` (all through `Set.empty_ne_univ`). No declaration in
  the four `System/Zigzag*` modules uses choice.

An independent audit of `2f7ece70` against this contract passed all twelve
items. It re-derived the sweep's count of 872 systems by hand, probed the
realization on a coarse system with a two-element state at `L` (`A` a single
pair, `A'` everything, `T = ∅`) and confirmed the three images and
non-uniqueness there, checked every one of the 25 restriction cases of
`realizeHom`'s naturality, and found no verbatim mathlib duplicate. Its
additions are in `ed91c378`: `target_eq_of_join_eq_empty`, the packaged
`splitCandidate`/`glueCandidate` with `datum_eq` and `target_ne`, a stated
universe convention in the two module docstrings, and neutral wording of the
M4 note. Naming remarks recorded but not acted on: `Target.ofDatum` also takes
the full image `T`; `join` could read `coarseJoin`; `Family.fam` is an
abbreviation; `Context.not_L_le_MR` reads oddly. The orchestrator mirrored the
additions in Status and README. The working copy is clean after the commit.

# Request to the reviewer

Inspect the datum and target definitions against the contract, the necessary
inclusion's use of naturality, the tagged realization as an actual coherent
restriction system with surjective observations, the three image equalities,
the classification and uniqueness theorems, and the strict pair on the
production path. Decide whether M3 is complete and which M4 obligations the
recorded realizability statement discharges. On acceptance, update the
proposal's M3 status and curate the next objective.

# Prior acceptance evidence

M2 was accepted at `0950158f` (submission `c15aff3c`); M1 at `d7f2ed62`;
M0 at `6a33636f`; the founding proposal at `7159fd31`. Details remain in
version history.
