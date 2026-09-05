State: RETURNED
Turn: worker
Candidate: ed91c378 (submission fdce1c7d)

# Verdict and objective

M3 is returned for one theorem/manifest gap and a consolidated documentation
correction. Independent review found the central classification, tagged
realization, target comparison, uniqueness condition, and strict finite pair
mathematically sound. Build, flake checks, both sweeps, and the axiom audit pass.

Close R1–R2 without changing the selected reconstruction problem or replacing
the proved classification. M3 is not accepted yet. The assessment of M4 below
records which obligations the existing theorems already address; it does not
open another implementation track in this revision.

# Accepted foundation and fixed question

[PROPOSAL.md](PROPOSAL.md), Sections 11–14, 22–23, 26, and 31, owns the contract.
M0 `6a33636f`, M1 `d7f2ed62`, and M2 `0950158f` remain accepted.

The selected shape is the five-context zigzag `L → B ← M → D ← R`, with the
four generating inequalities and reflexivity. The coarse system is fixed and
arbitrary. Candidates have arbitrary fine carriers and commuting observations
surjective at every context. The supplied datum is `(I_LM, I_MR)`. The target
is equality of all eight admissible images (empty, the three singletons, the
three pairs, and LMR) and their induced restrictions over that fixed coarse
system. No change to presentation equivalence, cardinal profiles, a larger
shape, or an extension hypothesis is in scope.

Preserve the implementation reviewed here:

- `Zigzag.Candidate` and `Target` encode exactly this class and target.
  `Candidate.target_eq_iff` and `restrictImage_setCongr_of_target_eq` account
  for all proper images and the induced maps, including independent fine
  universes.
- `image_LMR_subset_join` uses M2 naturality. `TaggedState.res` retains each
  tag; the `solo` tag includes its originating context and coarse state.
  `res_eq_res_LM_iff`, `res_eq_res_MR_iff`, and `eq_full_of_res_eq` rule out
  unintended binary and full lifts. The observation is objectwise surjective.
- `exists_realization_iff` and `exists_candidate_target_iff` classify the full
  remaining freedom by all subsets of the coarse join. The uniqueness
  condition is exactly empty join. The necessary results cover arbitrary fine
  universes; existential witnesses live in the coarse universe.
- `MiddleSplit.datum_eq` and `target_ne`, with the named coarse witness `y₀`,
  certify equal supplied data and different targets through the family API.
  The accepted M2 witness is distinct and does not substitute for this pair.

Toolchain, license, and build/cache tasks remain settled. No naming refactor
of `join`, `Target.ofDatum`, or the family labels is requested.

# Current drawers

## R1 — Prove the singleton-middle claim made in the README

`README.md:613–615` asserts a general mathematical lower bound, not merely a
bounded search observation: with one fine middle state, the two adjacent
binary lifts combine, so `(I_LM, I_MR, I_LMR) = (1,1,0)` is impossible.
There is no corresponding general theorem or typed Status example. The
concrete Bool witness and enumeration do not establish that universal claim.

Add the consumed collapse lemma on the fixed zigzag, at least at this
strength for arbitrary fine restriction systems:

```text
If S.State M is a subsingleton, then
  Nonempty (S.CompatibleFamily LMR)
iff
  Nonempty (S.CompatibleFamily LM) and Nonempty (S.CompatibleFamily MR).
```

The reverse implication combines the actual two supplied families using
agreement of their middle states; the forward implication uses restrictions.
No finiteness, decidability, global nonemptiness, or observation-surjectivity
assumption is needed for this statement. This closes the README's claim in
its singleton-coarse setting without introducing a counting package or
claiming overall minimality of the strict pair.

Give the lemma a mathematical name, mirror the exact statement in Status,
and connect the README's explanation to it. Retain the bounded scope of the
numerical minima reported by the sweep. Removing the useful collapse fact
instead of certifying it would leave its stated mathematical explanation
without the required evidence.

## R2 — Correct hypotheses, implication directions, and tag descriptions

Correct these related public descriptions in one pass:

1. `README.md:12–14` says no coverage hypothesis appears in any criterion.
   M3's candidate class explicitly requires objectwise surjectivity, which is
   used to fix the singleton and LR images. Scope the introductory generality
   statement accurately and name that requirement for the zigzag
   classification. No finiteness or decidability restriction needs to be added.
2. `README.md:677–681` attributes the listed arbitrary-universe results to
   naturality alone. That explains the necessary join inclusion, but
   `Candidate.target_eq_ofDatum` and `Candidate.target_realizable` also use
   the fixed-image lemmas and candidate surjectivity. Preserve the correct
   universe claim and describe the actual hypotheses consumed.
3. `README.md:660` and the docstring of `target_eq_of_join_eq_empty` at
   `System/ZigzagClassification.lean:181–183` call it the forward half of
   `datum_determines_target_iff`. The iff is written “determination iff empty
   join”; this lemma proves the reverse/sufficiency direction, from empty
   join to determination. Its theorem and Status example already have the
   correct direction. Correct the prose, including the next submission.
4. `System/ZigzagRealization.lean:263` describes `realize A A' T`
   unconditionally as realizing all three prescribed images. It only realizes
   the requested binary images under `T ⊆ join A A'`. The full-image equality
   and objectwise surjectivity are unconditional. Carry this distinction into
   the corresponding constructor descriptions, `realizeCandidate`, and the
   Status docstrings at 1647 and 1902. Keep the constructors usable without
   the inclusion; no API or proof restriction is requested.
5. `System/ZigzagRealization.lean:174–175` calls `solo` an “untagged copy”.
   It is tagged by `p : Σ d, S'.State d`, and retaining that origin under
   restriction is essential to prevent unwanted compatible pairs. Describe
   the origin tag explicitly.

The constructor qualification has a checked negative control. Over
`MiddleSplit.coarse`, take `A = ∅`, `A' = ∅`, and `T = Set.univ`. Then
`(realizeCandidate A A' T).datum ≠ (A, A')`: a full coarse family in `T`
forces its two binary restrictions into the actual images. A disposable Lean
probe established this using `subset_join_of_candidate` and
`realizeCandidate_image_LMR`. The implementation behaves correctly; the
unconditional description is the mismatch.

Closure evidence: the descriptions match the elaborated hypotheses and
formulas, including this out-of-domain constructor case. Preserve the exact
classification statements and the correct universe convention. No additional
classical assumptions or generalization of the reconstruction target is needed.

# Assessment of M4's obligations

The submitted mathematics already establishes the substantive realizability
boundary, rather than merely a constructor for positive examples:

- `exists_realization_iff` characterizes simultaneous realization of the two
  binary images and the full image by actual coherent candidates.
- `exists_candidate_target_iff` and `realizable_target_iff` characterize all
  eight entries and all remaining target collections; the induced maps are
  accounted for by `Candidate.restrictImage_setCongr_of_target_eq`.
- `datum_determines_target_iff` identifies exactly when the residual target
  freedom collapses. The strict finite pair proves the loss of full content.
- The construction's image laws and `Candidate.target_eq_ofDatum` provide
  extraction of its target; no inverse recovering a unique fine presentation
  is claimed or required.

After M3 acceptance, M4 should finish the declared closure obligations, reusing
these theorems. In particular, Section 26 requires a strict incompatible datum
for each proper realizability condition. The current `Target` criterion has
five full-entry conditions and the join-inclusion condition. The two existing
strict candidates are both realizable and do not supply those negative
controls. A small finite collection of explicit impossible targets, or one
parameterized certificate covering the conditions, should connect each
failure to `realizable_target_iff`. Then perform Section 31's final
obligation-to-theorem and public-surface audit and update durable status.
There is no need for another classification, a larger shape, or new invariants.

# Independent verification of ed91c378

- Read all four new System modules, `Models/MiddleSplit`, the shared-shape
  extraction from the accepted model, the new Status section, README, sweep,
  and governing M3/M4 and closure contracts.
- `nix develop -c lake build`: success, 725 jobs, no warnings.
- `nu tasks.nu check`: flake checks pass, including formatting. Source search
  finds no unfinished proof, project axiom, native proof bypass, or unsafe
  declaration.
- Ran the submitted sweep at bounds 2 and 3: 872 and 1,554,228 systems,
  respectively. Both produce exactly the five permitted boolean triples,
  with no violation. Inspected the enumeration of all four restriction
  functions and its singleton-coarse limitation.
- Unfiltered axiom audit: imported `Amalgam`, selected constants by defining
  module for `System.Zigzag`, `ZigzagTarget`, `ZigzagRealization`,
  `ZigzagClassification`, `Models.MiddleSplit`, and `Models.Zigzag`, and ran
  `Lean.collectAxioms`. There are 413 constants, 58 internal: 74 use no axioms,
  265 only `propext`, 68 `propext` and `Quot.sound`, and six also use
  `Classical.choice`. No other axiom occurs. The six choice users are the
  reported model inequalities; the four System modules use no choice.
- Direct axiom prints for `exists_realization_iff`, `realizable_target_iff`,
  and `datum_determines_target_iff` show only `propext` and `Quot.sound`.
- Disposable Lean probes checked the invalid prescribed-image example in R2
  and instantiated the existence theorem with every coarse carrier empty,
  using the documented equal-universe existential convention. Both compile.

# Resubmission

Work from this file and close R1–R2 in one round. Run formatting, the full
build, flake checks, and the revised axiom audit. Commit the candidate and
rewrite this file as `READY FOR REVIEW`, `Turn: reviewer`, with the exact
candidate and evidence for every drawer. A chat reply alone is not a submission.
Do not begin a separate M4 implementation in this revision; its remaining
closure scope is recorded above for the next acceptance decision.
