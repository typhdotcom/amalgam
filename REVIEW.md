State: RETURNED
Turn: worker
Candidate: 09ec3871 (submission 95c35cee)

# Verdict and objective

M2 is returned for one bounded naming and documentation round. Independent
review found no mathematical defect in the family construction, its binary
recovery, or the two calibration cases. The build and axiom audit pass. The
remaining corrections concern the public API's agreed naming convention and
descriptions that do not match the declarations or audit evidence.

Complete M2: compatible families over a preorder, their declared restrictions,
the raw comparison and its fine lifts, the observed quotient and attainable
image, and naturality relating these constructions. Do not begin M3 or change
the mathematical statements to close these drawers.

# Accepted foundation and scope

[PROPOSAL.md](PROPOSAL.md), Sections 11–12, 22–23, and 26, owns the mathematical
and public API contract. M0 candidate `6a33636f` and M1 candidate `d7f2ed62`
remain accepted. Their source modules and witnesses are unchanged by M2.

Preserve the submitted M2 construction:

- `RestrictionSystem` over an arbitrary preorder, with restriction toward
  coarser contexts and identity/composition laws. Compatibility means agreement
  at every common coarser context. `FamilyMap` supplies the index and context
  inequality for each target view. Carriers and index types may be empty.
- Presentation equivalences arise from actual declared restrictions in both
  directions; relabeling, redundant views, and duplicates are special cases.
- `Hom.mapFamily` observes the supplied fine states. Its fiber is exactly a
  compatible fine assignment satisfying all observation equations.
- The quotient relation is its kernel. The quotient injection has the same
  image; raw and quotient fibers have the same inhabitedness, while quotient
  fibers discard multiplicity. Restrictions descend without choosing fine
  representatives and satisfy identity/composition. Image restriction gives
  inclusion, with strict finite witnesses.
- Binary recovery consumes a greatest common coarser context and transports
  the raw comparison, fibers, images, and quotient injection to M0/M1. The
  intersection criterion is recovered from M1. Keep the current weakened
  hypothesis of `compatible_triple_iff`: every common coarser context of the
  outer views lies below the middle view.
- The span calibration has raw fiber equivalent to `Bool` and a unique
  quotient fiber. The Section 12 zigzag has equal empty full-family images
  but different proper-family images, with surjective observations. Neither
  witness asserts minimality or refutes an M3 datum.

Toolchain, license, and tasks remain settled. `nu tasks.nu cache` already
runs `lake exe cache get` and is documented; there is no further cache-task
decision. The standard Apache appendix template remains unchanged.

# Current drawers

## R1 — Use the agreed names for type constructors

Section 22 requires UpperCamelCase for types. Two new type families violate
that convention:

- `RestrictionSystem.Hom.observedFamily` in
  `Amalgam/System/Comparison.lean:150` is explicitly a quotient type. Rename it
  to `ObservedFamily`, consistent with `CompatibleFamily` and M1's `Observed`.
- `Amalgam.Models.Span.fineState` in `Amalgam/Models/Span.lean:70` is the fine
  state type family. Rename it to `FineState`.

Update consumers, docstrings, README, and Status consistently. Functions such
as `observedFamilyEquivImage` remain functions and retain lowerCamelCase. No
compatibility aliases are needed for this unaccepted API. This is a naming
correction, not a mathematical refactor.

Closure evidence: both new type constructors follow the convention, old
type-name references are gone, and the whole library including Status builds.

## R2 — Match documentation and audit claims to the actual declarations

`Amalgam/System/Comparison.lean:47` says the criterion, quotient, and naturality
statements use no choice. Its two image-equivalence naturality laws do use
`Classical.choice`:

```text
RestrictionSystem.Hom.restrictImage_observedFamilyEquivImage
RestrictionSystem.Hom.restrictImage_comp_observedFamilyEquivImage
```

Both mention `observedFamilyEquivImage`, built with
`Setoid.quotientKerEquivRange`. Their axiom sets are
`[propext, Classical.choice, Quot.sound]`. In contrast, `restrictObserved`,
`restrictImage`, the raw and quotient commuting squares, and the basic image
inclusion require no classical choice. Qualify the module overview accordingly;
the current blanket claim and the submission's corresponding claim are false.
No proof change or removal of legitimate classical dependencies is requested.

Also correct the two reversed descriptions in `Amalgam/Status.lean:1157` and
`:1162`: the expression `e.symm (e q) = q` is the inverse after the forward
correspondence; `e (e.symm t) = t` is the forward correspondence after its
inverse. The theorem statements and proofs already have the correct direction.

Make the next axiom report precise about its selection. The submitted count
of 338 is the count excluding 89 internal constants, not every constant of
the six modules. An unfiltered audit covers 427. The 13 choice users are
consistent with the implementation; `observedFamilyEquivImage` has four
listed laws, not five. Report the actual scope and dependencies without a
contradictory summary.

Closure evidence: the corrected descriptions agree with their formulas and
with `#print axioms` for the two named naturality laws. Give the exact audit
selection and results on the revised candidate. Keep the README and module
documentation truthful if any affected names or qualifications appear there.

# Independent verification of 09ec3871

- Inspected all six M2 modules, the new Status examples, README, the accepted
  M2 contract, and the unchanged M0/M1 source. Reviewed hypotheses and maps,
  including the outer-view condition in `compatible_triple_iff`, arbitrary
  empty types, redundant views, and the actual finite witness constructions.
- `nix develop -c lake build`: success, 720 jobs, no warnings.
- `nu tasks.nu check` (`nix flake check`): all checks passed, including
  formatting. No unfinished proof or project axiom was found.
- A disposable Lean audit imported `Amalgam`, iterated `env.constants.toList`,
  selected declarations by `env.getModuleIdxFor?` for the four System modules
  and `Models.Span`/`Models.Zigzag`, and ran `Lean.collectAxioms` without an
  internal-name filter. Of 427 constants, 142 use no axioms, 102 use only
  `propext`, 80 only `Quot.sound`, 90 both, and 13 also use `Classical.choice`.
  No other axiom occurs. Exactly 89 selected names satisfy `Name.isInternal`.
- Direct `#print axioms` confirmed the two dependencies in R2; the basic
  quotient and image restriction maps use only `propext` and `Quot.sound`,
  and `compatible_triple_iff` uses only `propext`.

# Resubmission

Work from this file and close R1–R2 in one round. Run formatting, the full
build, flake checks, and the revised axiom audit. Commit the candidate, then
rewrite this file as `READY FOR REVIEW`, `Turn: reviewer`, identifying the
exact candidate and evidence for each drawer. A chat reply alone is not a
submission.

M2 remains unaccepted until that review. On acceptance the reviewer will
update its proposal status and curate the M3 objective; no M3 implementation
belongs in this revision.
