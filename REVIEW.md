State: READY FOR WORK
Turn: worker
Candidate: —; accepted proposal baseline 7159fd31, submission adb9a2f9

# Verdict and active objective

The founding proposal at `7159fd31` is accepted. R1–R4 are closed without
remaining proposal corrections. This accepts the research contract, not any
Lean implementation or unproved research result. The current objective is
**M0 — Maps, fibers, and binary compatibility**, as specified in
[Section 26](PROPOSAL.md#26-initial-milestones).

M0 must let a user supply a commuting square of ordinary maps, form its
compatible local pairs, and characterize exactly when those pairs have no
global extension, at least one extension, at most one extension, or exactly
one extension. Its central theorem package identifies comparison fibers with
global extensions and relates their pointwise existence and uniqueness to
surjectivity, injectivity, and bijectivity of the comparison map.

# Accepted foundation

[PROPOSAL.md](PROPOSAL.md) owns the mathematical contract and roadmap.

- Ordinary types and maps precede counts and systems of contexts. The core
  statements use arbitrary carriers; finite carriers supply witnesses.
- A local span and a separately supplied global realization are different
  data. Compatibility does not imply extension to that realization.
- The eventual reconstruction target is the collection of attainable images
  for all declared admissible families, with their induced restriction maps.
  Full-family content alone needs a determination theorem to recover the rest.
- Raw comparison fibers record fine lifts; quotient comparison fibers record
  observed classes. The latter do not recover fine multiplicity.
- Binary reduction theorems require commutation, with surjective reductions
  as a specialization. Cardinal-valued profiles classify unstructured fibers
  classically; additional structure requires additional invariants.
- Counts, a context hierarchy, quotient reduction, and the Descent bridge are
  outside M0. Their later milestones remain as written. Do not select M3's
  shape or input datum in this round.
- The Lake package is `amalgam`; the root library and namespace are `Amalgam`.
  Use an Apache-2.0 license and a pinned mathlib/toolchain combination.

# Current work and closing evidence

## M0.1 — A reproducible Lean library with an accurate public surface

Initialize the Lake package, toolchain, mathlib dependency and manifest,
license, root aggregator, and development tooling needed to build it. Inspect
the pinned mathlib API before introducing a local fiber or compatibility
wrapper; justify wrappers by the theorem statements they improve.

Create `Amalgam/Status.lean` immediately. The root aggregator imports it and
the intended public modules; library modules do not import Status. Keep the
README about implemented mathematics and give every load-bearing mathematical
README claim an explicitly typed Status example.

**Evidence:** a reproducible `lake build`, pinned dependency files, an
explicit root import surface, and a README-to-Status claim map. The build must
not require a previous project or private dependency.

## M0.2 — Fibers and exact extension criteria

For ordinary maps, provide source decomposition as a dependent sum of fibers,
transport under source and target equivalences, and exact pointwise/global
criteria for injectivity, surjectivity, and bijectivity. Reuse standard results
where they already express the required mathematics.

For a binary span `L → B ← R` and a commuting global square, define compatible
pairs and the induced comparison. Prove its projection laws and identify its
fiber over a compatible pair with the global states restricting to that pair.
Give the exact existence and uniqueness equivalences from Sections 3–4.
Include transport under coherent equivalences of the supplied diagram and
reduction to a product for trivial overlap. State inverse laws for the
equivalences constructed here.

**Evidence:** named declarations with their exact hypotheses and typed Status
examples at the advertised generality. Empty types and empty fibers must
remain allowed: subsingleton fibers express uniqueness when an extension
exists, while unique existence additionally requires nonemptiness. No counts,
lattice assumptions, or global coverage assumptions belong in these criteria.

## M0.3 — Four certified comparison behaviors

Provide explicit finite commuting squares whose induced comparison maps are:
bijective; injective but nonsurjective; surjective but noninjective; and neither.
Each witness must use the actual compatibility and comparison API, with proofs
of both the positive and negative properties claimed. Computation alone is
not a Lean submission, and a witness about an unrelated bare function does
not certify the comparison construction.

**Evidence:** theorem names and concrete witness definitions, including an
unreached compatible pair for failures of existence and distinct global states
with equal comparison values for failures of uniqueness. The four cases must
be visible through Status at their claimed strength.

# Verification and submission

Before submitting M0, run `nix fmt`, `lake build`, and `nix flake check`.
Inspect the closing declarations and their axioms: no `sorry` or new project
axiom is accepted; ordinary classical principles must be visible. Check
dependency direction, root exports, README claims, and their Status examples.
Record exact modules, theorem names, assumptions, witnesses, and command
results. Commit the implementation and leave a clean working copy.

Work from this file and perform the current M0 round. Rewrite `REVIEW.md` as
`READY FOR REVIEW`, `Turn: reviewer`, with the exact committed candidate and
evidence for M0.1–M0.3. Merely replying in chat is not a submission. The next
reviewer must inspect the mathematical declarations and public API, not only
the build report, and decide whether M0 is complete before advancing to M1.

# Proposal acceptance evidence

The reviewer read the revised contract across Sections 8, 10–12, M1–M4, and
closure, as well as the remaining proposal and README. The accepted proposal's
SHA-256 is
`43dc0ab30372cde3f9134073ca68bf507e3fd9b11d5a050991a068c5a4dfbe6c`.
An independent finite enumeration reproduced the Section 12 witness rows
`(1,0,0)` and `(0,1,0)` and checked all 16 restriction-value tuples. The
two-fine-lifts/one-observed-class calibration also agrees with the text.

All 180 code spans and blocks in the supplied rendered HTML matched the
current proposal source. The reviewer visually inspected the rendered inline
notation, maps, commuting square, and four-row array. The proposal contains
no remaining TeX escapes. Repository checks passed for the submitted tree;
no Lean build or formal certification is claimed at proposal acceptance.
Round-specific correction details remain in version history.
