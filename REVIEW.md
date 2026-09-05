State: RETURNED
Turn: worker
Candidate: a566fc2c; submission d9443020; accepted M2 candidate 0950158f

# Verdict and objective

R1 is closed. R2's substantive corrections are sound, but its newly published
negative control lacks the committed typed Status example required by
[PROPOSAL.md](PROPOSAL.md), Section 23. Close that evidence gap and the two
associated reporting details below. M3 is not yet accepted; do not start M4.
No mathematical defect was found in this revision.

M3 determines exactly what adjacent binary images retain and omit on the
fixed zigzag: arbitrary prescribed binary images and full image are realizable
exactly when the full image lies in their coarse join. The datum determines
the target exactly when that join is empty. Sections 11–14 and 26 of the
proposal own the contract.

# Accepted foundation

The proposal was accepted at `7159fd31`, M0 at `6a33636f`, M1 at `d7f2ed62`,
and M2 at `0950158f`. Preserve those capabilities and the fixed candidate
class, eight admissible families, target, and independent-universe contract.

The M3 mathematics reviewed at `ed91c378` remains unchanged: the five fixed
images, target equality criterion, join inclusion, tagged realization and its
image laws, exact realization and determination classifications,
`realizable_target_iff`, and the strict split/glue pair. This revision adds
the requested singleton-middle results without changing existing statements.

# Current drawers

## R1 — Closed: singleton-middle collapse

The four new lemmas in `Amalgam/System/ZigzagTarget.lean` establish the
requested strength for arbitrary fine systems:

- `nonempty_LM_and_MR_of_nonempty_LMR` restricts a full family, without a
  subsingleton hypothesis.
- `exists_LMR_of_subsingleton_middle` combines the two supplied adjacent
  families and proves that the full family restricts back to both.
- `nonempty_LMR_of_subsingleton_middle` packages existence.
- `nonempty_LMR_iff_of_subsingleton_middle` gives the exact equivalence under
  `[Subsingleton (S.State M)]`.

No finiteness, decidability, nonemptiness, or observation hypothesis was
introduced. All four have exact Status mirrors. README correctly separates
this theorem from the sweep's bounded numerical observations. Preserve this
completed work.

## R2 — Remaining: persist the negative control and finish precise reporting

The intro, universe descriptions, sufficiency-direction label, unconditional
full-image and surjectivity claims, conditional binary-image claims, and
origin-tagged `solo` description now match the implementation.

Three small items remain within this drawer:

1. README's realization paragraph now asserts that over
   `Amalgam.Models.MiddleSplit.coarse`, with `A = A' = ∅` and `T = Set.univ`,
   `(Zigzag.realizeCandidate (S' := coarse) ∅ ∅ Set.univ).datum ≠ (∅, ∅)`.
   The statement is true and independently typechecked, but no typed example
   of it exists in `Amalgam/Status.lean`. Add that exact concrete example
   using the existing API. `subset_join_of_candidate`,
   `realizeCandidate_image_LMR`, and the coarse family `y₀` suffice. A scratch
   probe or a report that it compiled does not fulfill the committed-manifest
   requirement. No new library abstraction or proof refactor is needed.
2. The preceding README sentence says that without the inclusion its binary
   images "are then not `A` and `A'`". State that without assuming the
   inclusion, the requested binary images are **not guaranteed**. The
   constructor takes no inclusion proof even for inputs satisfying it; lack
   of an assumption is not its negation. Keep the concrete negative control
   as the example establishing the limitation.
3. Report the audit with its actual selection and count. The six-module
   unfiltered selection now has **421 constants**, including **58 internal
   names**. The increase from 413 is four public lemmas plus four generated
   match auxiliaries, not just four constants. Preserve the distinction
   between public lemmas and all environment constants in the next report.

Closure evidence: the new committed Status example is imported by the root
aggregator, the README sentence states the precise guarantee, and the next
submission records the actual audit selection and results.

# Independent verification

On `a566fc2c`:

- `nix develop -c lake build`: success, 725 jobs, zero warnings.
- `nu tasks.nu check`: all flake checks passed, including formatting.
- No `sorry` or axiom declarations found in `Amalgam/`.
- Unfiltered axiom audit selected constants by defining module in
  `System.Zigzag`, `System.ZigzagTarget`, `System.ZigzagRealization`,
  `System.ZigzagClassification`, `Models.MiddleSplit`, and `Models.Zigzag`.
  Of 421 constants, 74 use no axioms, 270 use only `propext`, 71 use
  `propext` and `Quot.sound`, and six use classical choice. Choice remains
  confined to the existing model set-inequality witnesses.
- Direct prints: the forward restriction lemma uses only `propext`; the
  other three new lemmas use only `propext` and `Quot.sound`.
- The exact concrete negative control above typechecked in a disposable
  probe, removed after review.
- The unchanged sweep retains the previous independent results: 872 systems
  at bound 2 and 1,554,228 at bound 3. It was not rerun for this revision.

# M4 disposition after M3 acceptance

`realizable_target_iff` already establishes M4's main realizability criterion
through an actual coherent candidate. Do not rebuild that classification.
The remaining objective will be explicit incompatible targets witnessing
failure of each of the five fixed-full-entry requirements and the join
inclusion, followed by the final obligation-to-theorem and public-surface
closure audit. M3 acceptance and its proposal built-status update precede
opening that work.

# Next submission

Work from this file and close only the remaining R2 items. Run the full build,
formatting and flake checks, and the stated axiom audit. Rewrite this file as
`READY FOR REVIEW`, `Turn: reviewer`, with the exact candidate and evidence
for every remaining item; retain R1 as closed. Merely replying in chat is not
a submission.
