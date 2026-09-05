State: READY FOR WORK
Turn: worker
Candidate: —; accepted M3 candidate 08c41b29, submission b88d4986

# Acceptance and next objective

M3 is accepted. Both returned drawers are closed. The exact realization
negative control is now a committed typed Status example, the README states
the conditional guarantee precisely, and the audit report matches the
independent 421-constant selection. The proposal records M3's built status.

M4 closes realizability on the same fixed zigzag. Its classification theorem
is already proved by M3. Supply the strict incompatible targets demonstrating
its proper conditions, then audit the declared reconstruction question for
closure. Do not enlarge the shape, datum, candidate class, or target.

# Accepted foundation

[PROPOSAL.md](PROPOSAL.md), Sections 11–14, 26, and 31, owns the mathematical
contract. M0 was accepted at `6a33636f`, M1 at `d7f2ed62`, M2 at `0950158f`,
and M3 at `08c41b29`; the founding proposal was accepted at `7159fd31`.

Fix an arbitrary coarse restriction system on `L → B ← M → D ← R`.
Candidates have commuting, objectwise surjective observations; fine carriers
may vary and need not be finite or nonempty. The datum consists of the two
adjacent images. The target consists of the images on all eight subfamilies
of `L, M, R`, with maps induced by the fixed coarse restrictions. Target
equality does not assert equivalence of fine presentations.

M3 supplies the following completed obligations:

- `Candidate.target_eq_iff` and
  `Candidate.restrictImage_setCongr_of_target_eq`: the datum and full image
  determine the entire target and its induced maps; five entries are full.
- `exists_realization_iff` and `exists_candidate_iff`: a prescribed triple
  `(A, A', T)` is realized exactly when `T ⊆ join A A'`. The converse is an
  actual coherent fine system, not a collection of unrelated function ranges.
- `exists_candidate_target_iff` and its field form: all remaining targets at
  fixed datum, with no further condition on the adjacent subsets themselves.
- `datum_determines_target_iff`: target determination exactly when the join is
  empty. `target_eq_of_join_eq_empty` supplies sufficiency across independent
  fine universes. The existential constructions use the coarse universe.
- `realizable_target_iff`: an abstract target is realizable exactly when its
  empty, `L`, `M`, `R`, and `LR` entries are full and its `LMR` entry is
  contained in the join of its `LM` and `MR` entries.
- `Models.MiddleSplit`: equal adjacent images with different full images;
  the singleton-middle collapse explains why adjacent lifts combine when
  the fine middle carrier is a subsingleton.

# Current drawers

## M4.1 — Strict incompatible targets

Give six explicit finite abstract targets through the existing `Target` API:
for each of the five fixed-full-entry conditions and for the join inclusion,
one target violating that condition while satisfying the other five. Prove
the failed condition and nonrealizability through the accepted criterion.
These are abstract targets, not candidate systems that violate their own laws.
The all-singleton coarse system already available in `Models.MiddleSplit`
suffices; reuse it rather than introduce another realization framework.

Keep the controls small and named. They must expose the actual target fields
and certify the other conditions, rather than establish only an opaque
negation of an existential. Put their public README claims in exact typed
Status examples. No minimality claim is required.

This establishes the necessity of each stated condition. The adjacent datum
itself has no extra realizability condition: an empty full image is permitted
for every pair of adjacent subsets by the accepted construction. Reuse that
result when explaining the distinction between separate adjacent lifts,
coarse overlap compatibility, simultaneous fine lifting, and freedom in the
full image. Do not infer a common fine middle representative from two separate
lifts or impose a global assignment on the candidate class.

## M4.2 — Closure of the declared question

Audit the proposal's Section 31 obligations against the actual API. Record a
compact obligation-to-theorem map in the submission, including the fixed
realization class and target equivalence, all admissible images and their
maps, exact realizability, residual freedom, and strict witnesses. Any durable
mathematical consequence belongs in the existing proposal or README with its
Status evidence; REVIEW.md remains the single active coordination artifact.

Inspect root imports and direct module dependencies, statement assumptions
and universe qualifications, public naming and docstrings, README-to-Status
coverage, and axiom dependencies. Check the reconstruction and transport laws
actually claimed, without inventing an inverse to the noninjective map from
fine presentations to their observable targets.

Identify any unresolved native theorem required for this classification and
resolve it before submission. Distinguish stronger presentation targets,
larger shapes, and new observables as a research horizon, not as debt in this
scope. If the declared obligations are discharged, submit M4 for final closure;
do not open another milestone merely because more theorems are possible.

# Verification

For M4, run the root Lean build, formatting and all flake checks, and check
for `sorry` or project axioms. Report the axiom audit's exact module selection,
counts including generated and internal constants, and every classical-choice
user in the new work. Explain any change from the accepted audit rather than
carrying counts forward across source changes.

M3 acceptance evidence:

- The current root build passed: 725 jobs, zero warnings, including the new
  negative-control Status example.
- The candidate changes since the previous review are limited to that example,
  the README sentence, and the submission report. The six audited modules
  are unchanged, so the previous direct audit remains applicable.
- Unfiltered defining-module selection: `System.Zigzag`, `ZigzagTarget`,
  `ZigzagRealization`, `ZigzagClassification`, `Models.MiddleSplit`, and
  `Models.Zigzag`, all under `Amalgam`. It contains 421 constants, 58 of them
  internal: 74 axiom-free, 270 using only `propext`, 71 using `propext` and
  `Quot.sound`, and six using classical choice as well. The six choice users
  remain the model set-inequality witnesses. Four public collapse lemmas plus
  four generated match auxiliaries explain the increase from 413.
- The unchanged sweep retains the independently reproduced 872 systems at
  bound 2 and 1,554,228 at bound 3; these remain bounded observations.
- Formatting and all seven flake checks passed on the acceptance handoff.

# Next submission

Work from this file and perform M4.1 and M4.2. Rewrite it as
`READY FOR REVIEW`, `Turn: reviewer`, with the exact implementation candidate
and evidence for each drawer. Keep the accepted M3 result explicit. Merely
replying in chat is not a submission.
