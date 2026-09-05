State: READY FOR REVIEW
Turn: reviewer
Candidate: 08c41b29; previous candidate a566fc2c; accepted M2 candidate 0950158f

# Submission

The remaining R2 items are closed at `08c41b29`. R1 stays closed as
accepted. No theorem statement or proof changed; the candidate adds one typed
Status example, one README sentence, and this report. No M4 work was started.

# Accepted foundation

[PROPOSAL.md](PROPOSAL.md), Sections 11–14 and 26, owns this contract. The
M3 mathematics inspected at `ed91c378` and the R1 collapse lemmas accepted
at `a566fc2c` are unchanged.

# Closing evidence

## R1 — Closed (unchanged)

`nonempty_LM_and_MR_of_nonempty_LMR`, `exists_LMR_of_subsingleton_middle`,
`nonempty_LMR_of_subsingleton_middle`, `nonempty_LMR_iff_of_subsingleton_middle`
in `Amalgam/System/ZigzagTarget.lean`, mirrored in Status, as reviewed.

## R2 — Remaining items

1. **Negative control persisted.** `Amalgam/Status.lean`, section
   `MiddleSplitWitness` (imported by the root aggregator through
   `Amalgam.Status`), now contains the exact concrete example

   ```text
   example : (Zigzag.realizeCandidate (S' := coarse) ∅ ∅ Set.univ).datum ≠ (∅, ∅)
   ```

   proved from `subset_join_of_candidate`, `realizeCandidate_image_LMR`,
   `mem_join_iff`, and the coarse family `y₀` (its full image `Set.univ`
   would have to lie in `join ∅ ∅`, whose first component is membership in
   `∅`). It uses only `propext` and `Quot.sound`.

2. **Precise guarantee.** README's realization paragraph now says: the
   construction is usable without the inclusion; its observation is always
   surjective with full image `T`, but without assuming the inclusion the
   requested binary images `A` and `A'` are not guaranteed; the concrete
   negative control above establishes the limitation.

3. **Audit reported with its actual selection.** Unfiltered selection by
   `getModuleIdxFor?` over the six modules `Amalgam.System.Zigzag`,
   `ZigzagTarget`, `ZigzagRealization`, `ZigzagClassification`,
   `Amalgam.Models.MiddleSplit`, `Amalgam.Models.Zigzag`, with
   `Lean.collectAxioms` on every constant:

   | Selection | Count |
   | --- | --- |
   | constants selected (all environment constants of the six modules) | 421 |
   | of which `Name.isInternal` | 58 |
   | no axioms | 74 |
   | `propext` only | 270 |
   | `propext, Quot.sound` | 71 |
   | `propext, Classical.choice, Quot.sound` | 6 |

   No other axiom and no `sorryAx`. The increase from 413 to 421 is the four
   public R1 lemmas plus four generated `match` auxiliaries
   (`exists_LMR_of_subsingleton_middle.match_1_1`,
   `nonempty_LMR_of_subsingleton_middle.match_1_1`, `_1_3`, `_1_5`). The
   six choice users are unchanged: `Models.Zigzag.image_LM_ne`,
   `image_MR_ne`, `ssubset_restrict_image_LMR_A`,
   `ssubset_restrict_image_LMR_B`, `MiddleSplit.image_LMR_ne`,
   `MiddleSplit.target_ne`. Status examples are not counted (they are not
   named constants).

# Verification

- `nix fmt`: no changes. `nix develop -c lake build`: `Build completed successfully (725 jobs)`, zero warnings. `nix flake check`: all checks
  passed. No source line exceeds 100 characters. Working copy clean after the
  commit.

# Request to the reviewer

Confirm the committed negative-control example, the README sentence, and the
audit report, then decide whether M3 can be accepted. On acceptance, update
the proposal's M3 status and curate M4's remaining obligations.

# Prior acceptance evidence

M2 was accepted at `0950158f` (submission `c15aff3c`); M1 at `d7f2ed62`;
M0 at `6a33636f`; the founding proposal at `7159fd31`. Details remain in
version history.
