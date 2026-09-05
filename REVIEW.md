State: READY FOR WORK
Turn: worker
Candidate: —; accepted M2 candidate 0950158f (submission c15aff3c)

# Objective and meaning

M3 — Classify what adjacent binary attainable images determine on the
five-context zigzag `L → B ← M → D ← R`.

Separate local liftability from the existence of one compatible fine family.
The reconstruction target is every declared family's attainable image, with
its restriction maps. First test the conjecture below on finite systems, then
prove the exact information boundary on this fixed shape and datum. An
isolated counterexample or a restatement of the generic fiber criterion does
not close this round.

# Accepted foundation

[PROPOSAL.md](PROPOSAL.md), Sections 11–12 and 26, owns the mathematical
contract and selected reconstruction question.

- M0 `6a33636f`, M1 `d7f2ed62`, and M2 `0950158f` are accepted. Reuse generic
  fibers, `Function.Pullback`, M1's exact lifting criterion, and M2's
  `RestrictionSystem`, `FamilyMap`, `CompatibleFamily`, `Hom.mapFamily`,
  `ObservedFamily`, `observedMapFamily`, and `image` constructions.
- Raw fibers count fine lifts; quotient fibers retain existence and discard
  multiplicity. The reconstruction target here is attainable content, not
  fine presentations, fiber counts, or coherent diagram isomorphism.
- Naturality gives `restrict(I_F) ⊆ I_E`. It supplies no extension assumption.
  Use the existing declared restrictions and induced image maps.
- Carriers may be empty and may vary between candidate fine systems. The
  finite context shape imposes no finiteness assumption on the general laws.
- The Section 12/M2 zigzag pair has different adjacent binary images. It
  cannot witness failure of the supplied datum chosen for M3.
- Toolchain, license, and the build/cache tasks remain settled. No external
  application, scalar invariant, counting hierarchy, or larger shape enters.

# Fixed datum, realizations, and target

Use the five-point preorder already exhibited in `Models/Zigzag.lean`:
`B ≤ L`, `B ≤ M`, `D ≤ M`, `D ≤ R`, and reflexivity, with no other relations.
A generic theory consuming this shape belongs outside Models; share the
context definition if needed, preserving the accepted models and results.

Fix an arbitrary coarse restriction system `S'` on that preorder. A candidate
realization is a fine restriction system `S` and a morphism `φ : S.Hom S'`
whose observation at every context is surjective. Do not impose finite fine
carriers, nonempty global families, or surjective family restrictions.

Declare all eight subfamilies of the local views `L, M, R` admissible:

```text
empty, L, M, R, LM, LR, MR, LMR
```

Their declared operations are all forgetful restrictions along inclusions.
Choose a clear finite indexing presentation and use M2's presentation laws
for equivalent labels; duplicates are not additional reconstruction targets.
The overlap contexts belong to the system and compatibility conditions, but
are not additional local views in this declared family collection.

The supplied datum is precisely the ordered pair of subsets `(I_LM, I_MR)`
of the fixed coarse binary compatible-family types. Equality of supplied data
means equality of both subsets. It supplies no fine carriers, fine middle
states, lift multiplicities, or identification of independently chosen lifts.

The target equivalence is equality of `I_F` for all eight families as subsets
of the same coarse family types. The image restriction maps must agree under
these equalities because they restrict the fixed coarse maps. Do not replace
this equivalence by arbitrary bijections or by presentation equivalence.

# Current drawers

## M3.1 — Finite reconnaissance and a strict information-loss witness

Test whether identical adjacent binary images can conceal different full
images. Search small finite fine systems on the fixed shape with singleton
coarse objects and surjective observations; allow more than one fine middle
state so the two binary lifts can use different middle states.

Certify a strict finite pair through the production family API: equal supplied
`I_LM` and `I_MR`, but different `I_LMR`, naming a coarse family attained on one
side and not the other. Prefer a pair with both binary comparisons surjective.
State the full systems and observations, certify the realization hypotheses,
and mirror the claims in Status. No minimality claim is required.

Record bounded search evidence and its limits tersely. A finite sweep can
refute the conjecture or guide a proof; it cannot prove the universal law.

## M3.2 — Prove which proper-family content is already fixed

Prove that every candidate has the full coarse image on the empty family and
on each singleton, and on `LR` (the two outer views have no common coarser
context). The other two proper images are exactly the supplied datum.

Deduce an explicit equivalence: two candidates have the same entire target
exactly when they have the same supplied binary images and the same full
image. Include the agreement of all induced image restriction maps. This is
what licenses treating `I_LMR` as the remaining joint question; it is not an
assumption that the full image projects onto each proper image.

## M3.3 — Classify the possible full images exactly

For arbitrary subsets `A_LM` and `A_MR` of the fixed coarse binary family types,
define the coarse join

```text
J(A_LM, A_MR) =
  {y in P'_LMR | restrict_toLM(y) in A_LM and restrict_toMR(y) in A_MR}.
```

The central conjecture to test and settle is:

```text
There exists a candidate realization with
  I_LM = A_LM, I_MR = A_MR, I_LMR = T
if and only if
  T is a subset of J(A_LM, A_MR).
```

Quantify over arbitrary coarse systems and all three subsets, retaining the
candidate hypotheses above. The forward direction must consume M2 naturality.
The converse requires an actual coherent fine restriction system and
objectwise surjective observations, with proofs of exactly the claimed images
through `Hom.mapFamily`. Constructing an abstract function with range `T` is
not sufficient evidence of realizability by the fixed restriction shape.

This is a conjecture, not an assumed theorem. If finite reconnaissance refutes
it, retain the counterexample and replace it by the sharper exact criterion
on the same datum and candidate class; do not quietly add hypotheses or
change the target. Explain any necessary change in the next submission.

Combine the classification with M3.2 to characterize all remaining target
collections at fixed supplied datum, and give the exact condition for that
datum to determine a unique target. Explain the missing agreement of fine
middle states. If a refinement is introduced, give its reconstruction theorem
and a strict witness for the information loss it claims to repair; a renamed
copy of the full target is not an explanatory refinement.

An unconditional converse may also settle M4's realizability obligations.
Record that consequence if proved. Reuse one theorem rather than inventing a
second classification to preserve milestone numbering; the next review will
assess which closure obligations remain. Do not move to a larger shape.

# Verification and submission

- Reuse the accepted M0–M2 API. Keep README about compiled results and mirror
  every new factual claim in typed Status examples. Record the datum, target
  equivalence, exact theorem, hypotheses, and witnesses in durable source/docs.
- Run formatting, the full Lake build, and all flake checks. Audit all new
  declarations for axioms with the selection stated explicitly. No unfinished
  proof or new project axiom is allowed; name classical dependencies accurately.
- Verify the strict pair, the empty and proper-family cases, the necessary
  inclusion, and the sufficient construction against the actual family images.
  The theorem must cover all target families and their induced maps.
- Work from this file and perform M3.1–M3.3. Commit the implementation candidate,
  then rewrite this file as `READY FOR REVIEW`, `Turn: reviewer`, with the exact
  candidate and evidence for every drawer. A chat reply alone is not a
  submission.

# M2 acceptance evidence

M2 candidate `0950158f` is accepted without remaining drawers. The complete
mathematical review of `09ec3871` carries forward: this revision changes only
`ObservedFamily`/`FineState` names and the requested descriptions. Both R1 and
R2 are closed; no old type-name references remain in source or README.

Independent verification: full build succeeds (720 jobs, no warnings), flake
checks pass including formatting, and the unfiltered six-module axiom audit
covers 427 constants, including 89 internal names. Counts by dependency are
142 with none, 102 with only `propext`, 80 with only `Quot.sound`, 90 with both,
and 13 also using `Classical.choice`; no other axiom occurs. Direct prints
confirm the two image-equivalence naturality laws use choice and the basic
restriction maps and image inclusion do not. The corrected Status round-trip
descriptions match their formulas. Earlier review details remain in history.
