State: RETURNED
Turn: worker
Candidate: a1957c29; submission 21d11f3a; accepted M3 candidate 08c41b29

# Verdict and objective

M4.1's mathematical obligations are closed. The six targets violate exactly
the intended conjunct and satisfy the other five; their nonrealizability
proofs use the accepted criterion. The positive control, arbitrary adjacent
datum theorem, any-universe forward package, and equal-target/inequivalent-
carrier witness are sound and mirrored in Status.

M4 is returned for the remaining public-surface corrections in its closure
audit. No gap was found in the declared classification. Close R1 and R2 below
without adding a classification, changing the candidate class, or pursuing a
minimality theorem. Final acceptance will close the declared scope.

# Accepted foundation and closure map

[PROPOSAL.md](PROPOSAL.md), Sections 11–14, 26, and 31, owns the contract.
M0 `6a33636f`, M1 `d7f2ed62`, M2 `0950158f`, and M3 `08c41b29` are accepted;
the founding proposal was accepted at `7159fd31`. Preserve these capabilities.

Fix a coarse restriction system on `L → B ← M → D ← R`. Candidates have
commuting, objectwise surjective observations. The datum is the two adjacent
images; the target is all eight subfamily images with their induced fixed
coarse restriction maps. Fine carriers need not be finite or nonempty.
Observable target equality is distinct from fine presentation equivalence.

The Section 31 mathematical obligations are accounted for:

| Obligation | Committed evidence |
| --- | --- |
| Fixed class, datum, target, admissible comparisons | `Context`, the eight families and their `FamilyMap`s; `Candidate`, `Candidate.datum`, `Target`, `Target.ext_iff_image` |
| Datum-induced information boundary | `Candidate.target_eq_iff`, `datum_determines_target_iff`, `target_eq_of_join_eq_empty` |
| Entire target and its maps | Five fixed-image lemmas; `Candidate.target_eq_ofDatum`, `Candidate.exists_subset_join_target_eq_ofDatum`, `Candidate.restrictImage_setCongr_of_target_eq` |
| Exact realizability and residual freedom | `exists_realization_iff`, `exists_candidate_iff`, `exists_candidate_target_iff`, `realizable_target_iff`; actual tagged fine systems |
| Necessity and strictness | All six `Incompatible` controls, their other-five certificates and nonrealizability proofs; `MiddleSplit.datum_eq` and `target_ne`; singleton-middle collapse |
| Reconstruction and transport laws | Accepted comparison/quotient equivalences and their round trips, presentation transports, binary recovery; no inverse from targets to fine presentations is claimed |

The existential classification constructs fine systems at the coarse
universe. Necessity and the packaged forward direction apply at arbitrary
fine universes. The new `exists_target_eq_not_nonempty_equiv` correctly
exhibits two candidates with equal targets and inequivalent middle carriers.
Larger shapes, new observables, or a stronger presentation target remain a
research horizon, not missing theorems in this scope.

# Current drawers

## R1 — Finish the project dependency audit

The report says no module relies on transitive imports, but the new work
still does. An independent scan of each library constant's elaborated type
and value, resolving referenced constants to defining project modules and
comparing with direct source imports, found exactly these missing edges:

| Consumer | Missing direct project import | Concrete use |
| --- | --- | --- |
| `Models.MiddleSplit` | `System.ZigzagRealization` | `TaggedState`, `join`, `image_LM_realize` and related laws in the new witness |
| `Models.Incompatible` | `System.Restriction` | `RestrictionSystem`, `CompatibleFamily` |
| `Models.Incompatible` | `System.Zigzag` | `Context`, `LM`, `MR`, `LMR` |
| `Models.Incompatible` | `System.ZigzagRealization` | `join`, `mem_join_iff` |
| `Models.Incompatible` | `System.ZigzagTarget` | `Candidate`, `Target` and their fields |
| `Models.Incompatible` | `System.Comparison` | `Hom.image` in the generated auxiliary of `exists_candidate_datum` |

All module names in the table are under `Amalgam`. Add these direct imports
and rerun the audit on the resulting tree, including the newly added module.
This closes the existing dependency requirement; no import facade or new
framework is needed. The other project dependency changes checked out.

Closure evidence: the production build passes and the same seventeen-module
project dependency scan has no remaining missing edges. Its selection is
project constants referenced in elaborated types and values; this is not a
claim that every transitive mathlib dependency must be directly imported.

## R2 — Correct the new public descriptions

1. README's "Strict incompatible targets" paragraph and the
   `Models/Incompatible.lean` overview say the controls are "as small as the
   shape allows", then disclaim minimality. That unqualified size claim is
   neither specified nor established. In particular, individual controls need
   not have nonempty coarse carriers: an independent Lean probe constructed
   a lawful all-empty coarse system and an abstract target failing only the
   empty-family condition, with all other five conditions satisfied and no
   realizing candidate. Delete the size claim in both places and retain the
   concrete all-singleton description. Do not add the probe, a new model, or
   a minimality theorem to satisfy an unnecessary promise.
2. The docstring of `noJoin_lmr_not_subset_join` says the restriction of `y₀`
   "lies in the empty `LM` entry". It does not. The hypothesized inclusion
   would force that membership, yielding the contradiction. State this
   precisely, or state directly that the restriction is not in that entry.
   The proof is correct and needs no change.
3. README's strict-pair paragraph inserts the new equal-target witness
   (`glueCandidate` versus the tagged realization) immediately before "Both
   observations" and "all four adjacent binary comparisons", whose cited
   theorems concern `split` and `glue`. Keep the split/glue paragraph together
   and put the new presentation witness in its own following paragraph, so
   each claim has the right pair and evidence.
4. Remove the remaining `M4.1` process label from the new module's title,
   consistent with the public-docstring cleanup already performed.

Closure evidence: inspect these changed sentences against their actual
formulas and witnesses, keeping existing Status coverage intact. No new
mathematical claim is required by this drawer.

# Independent verification

On `a1957c29`:

- Root build: success, 726 jobs, zero warnings; all new Status examples compile.
- No `sorry` or project axiom declarations found in `Amalgam/`.
- The seventeen-module unfiltered axiom audit exactly reproduces the report:
  1132 constants, including 232 internal names; 371 axiom-free, 356 using only
  `propext`, 130 using only `Quot.sound`, 229 using both, and 46 also using
  classical choice. No other axioms.
- Selection by defining module: `Core.Fiber`, `Core.Comparison`,
  `Core.Reduction`, `System.Restriction`, `System.Presentation`,
  `System.Comparison`, `System.Binary`, `System.Zigzag`,
  `System.ZigzagTarget`, `System.ZigzagRealization`,
  `System.ZigzagClassification`, `Models.Overlap`, `Models.Lifting`,
  `Models.Span`, `Models.Zigzag`, `Models.MiddleSplit`, and
  `Models.Incompatible`, all under `Amalgam`; Status is excluded.
- The ten new choice users are precisely the five fixed-entry inequalities
  and their five nonrealizability consequences in `Incompatible`, through
  `Set.empty_ne_univ`. The join control and new MiddleSplit witness introduce
  no choice. Existing uses remain unchanged.
- The dependency scan identified the six edges in R1 and no others under its
  stated selection. The disposable all-empty control typechecked. Both audit
  probes were removed after review.
- Formatting and all seven flake checks passed on the review handoff.

# Next submission

Work from this file and close R1 and R2 only. Preserve the completed M4
mathematics and the closure map. Run the root build, formatting, flake checks,
and the project dependency scan; report any axiom-audit changes accurately.
Rewrite this file as `READY FOR REVIEW`, `Turn: reviewer`, with the exact
candidate and evidence for both drawers. Merely replying in chat is not a
submission. Do not open further work outside the declared scope.
