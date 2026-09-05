State: READY FOR REVIEW
Turn: reviewer
Candidate: a566fc2c; previous candidate ed91c378; accepted M2 candidate 0950158f

# Submission

Both drawers of the returned round are closed at `a566fc2c`. No existing
theorem statement or proof changed; R1 adds four lemmas and their Status
mirrors, R2 is prose in README, two module docstrings, and two Status
docstrings. No M4 work was started.

# Accepted foundation

[PROPOSAL.md](PROPOSAL.md), Sections 11–14 and 26, owns this contract. The
M3 mathematics inspected at `ed91c378` is unchanged: the shared shape and
eight admissible families, `Candidate`/`Target`, the five fixed images and
`Candidate.target_eq_iff`, the join with `image_LMR_subset_join`, the tagged
realization with its three image laws, `exists_realization_iff`,
`exists_candidate_target_iff`, `datum_determines_target_iff`,
`realizable_target_iff`, and the `split`/`glue` pair.

# Closing evidence

## R1 — The singleton-middle collapse is a theorem

`Amalgam/System/ZigzagTarget.lean`, section "Collapse of the full family at a
single fine middle state", for an arbitrary fine system
`S : RestrictionSystem.{0, v} Context` with no finiteness, decidability,
nonemptiness, or surjectivity hypothesis:

- `nonempty_LM_and_MR_of_nonempty_LMR (S) : Nonempty (S.CompatibleFamily LMR) → Nonempty (S.CompatibleFamily LM) ∧ Nonempty (S.CompatibleFamily MR)`, by
  restriction along `toLM` and `toMR` (no subsingleton hypothesis).
- `exists_LMR_of_subsingleton_middle (S) [Subsingleton (S.State M)] (a : S.CompatibleFamily LM) (a' : S.CompatibleFamily MR) : ∃ x : S.CompatibleFamily LMR, S.restrict toLM x = a ∧ S.restrict toMR x = a'`:
  the two supplied families are combined on their (agreeing) middle states;
  compatibility by `compatible_triple_iff` from the two `compatible_pair_iff`
  equations, the second transported along `Subsingleton.elim`.
- `nonempty_LMR_of_subsingleton_middle`, and the requested statement
  `nonempty_LMR_iff_of_subsingleton_middle (S) [Subsingleton (S.State M)] : Nonempty (S.CompatibleFamily LMR) ↔ Nonempty (S.CompatibleFamily LM) ∧ Nonempty (S.CompatibleFamily MR)`.

Axioms: `nonempty_LM_and_MR_of_nonempty_LMR` uses `propext`; the other three
use `propext, Quot.sound`. All four are mirrored verbatim in
`Amalgam/Status.lean` (strict-witness subsection, universe `uV`). README's
sweep paragraph now attributes the "one middle state forces a full lift"
explanation to `nonempty_LMR_iff_of_subsingleton_middle` and keeps the
numeric minima as bounded-search observations; no minimality claim.

## R2 — Descriptions match the elaborated hypotheses and formulas

1. README intro: the criteria of M0–M2 carry no finiteness, decidability, or
   coverage hypothesis; the zigzag classification's candidate class requires
   objectwise surjective observations, which fixes the empty, singleton, and
   `LR` images.
2. README universe paragraph and the "Universe convention" header of
   `ZigzagClassification.lean`: `Candidate.image_LMR_subset_join` and
   `subset_join_of_candidate` consume naturality only;
   `Candidate.target_eq_ofDatum`, `Candidate.target_realizable`, and
   `target_eq_of_join_eq_empty` also consume the fixed-image lemmas and
   candidate surjectivity; all hold at an independent fine universe.
3. `target_eq_of_join_eq_empty` is described, in README and in its docstring,
   as the sufficiency direction of `datum_determines_target_iff` (from empty
   join to determination).
4. `realize`, `realizeHom`, `realizeCandidate` (module headers, docstrings,
   the two Status docstrings, and README): full image `T` and objectwise
   surjectivity hold for every `A`, `A'`, `T`; the binary images equal `A`,
   `A'` only under `T ⊆ join A A'`; the constructors stay usable without the
   inclusion. The `realize` docstring records the negative control. The
   reviewer's probe was reproduced on the candidate: over
   `Amalgam.Models.MiddleSplit.coarse` with `A = A' = ∅`, `T = Set.univ`,
   `(realizeCandidate A A' T).datum ≠ (∅, ∅)` via `subset_join_of_candidate`,
   `realizeCandidate_image_LMR`, and `mem_join_iff` at the default coarse
   family (axioms `propext, Quot.sound`).
5. `TaggedState` docstring, module header, and README: `solo` is tagged by its
   origin `p : Σ d, S'.State d`; restriction retains the origin, so two solo
   copies agree on an overlap only when they copy the same coarse state at
   the same context, which prevents unwanted compatible pairs.

`rg "untagged|forward half|naturality alone|no coverage|realizes all three"`
over README and `Amalgam/` leaves one hit, the sentence "Necessity is
naturality alone" about `image_LMR_subset_join`, which is correct.

# Verification

- `nix fmt`: no changes. `nix develop -c lake build`: `Build completed successfully (725 jobs)`, zero warnings. `nix flake check`: all checks
  passed. No source line exceeds 100 characters. Working copy clean after the
  commit.
- The 413-constant unfiltered audit of `ed91c378` carries forward; the only
  new constants are the four R1 lemmas with the axioms named above.

# Request to the reviewer

Check the four collapse lemmas against the required strength, the corrected
descriptions against the elaborated hypotheses (including the negative
control), and decide whether M3 can be accepted. On acceptance, update the
proposal's M3 status and curate M4's remaining obligations: strict
incompatible targets for each condition of `realizable_target_iff`, and the
final obligation-to-theorem and public-surface audit.

# Prior acceptance evidence

M2 was accepted at `0950158f` (submission `c15aff3c`); M1 at `d7f2ed62`;
M0 at `6a33636f`; the founding proposal at `7159fd31`. Details remain in
version history.
