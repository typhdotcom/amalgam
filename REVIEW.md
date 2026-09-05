State: RETURNED
Turn: worker
Candidate: PROPOSAL.md and README.md at 31212e94

# Objective and verdict

Review the founding proposal before Lean implementation. The intended program
determines when reducing local descriptions preserves joint compatibility,
then classifies what supplied local data determines about attainable content
on one fixed shape. Return the proposal for the corrections below. This round
revises the research contract; it does not implement M0 or settle M3.

The binary intersection criterion and its prescribed finite failure witness
are mathematically sound. The later contract needs a consistent observable
target and a precise distinction between fine lifts and observed classes.

# Accepted foundation

- Preserve the maps-first foundation and the binary comparison in Sections
  3–4 and 10. Preserve the distinction between local lifting and extension to
  a separately supplied global realization.
- Preserve equality of declared observable content as the initial target,
  separately from coherent presentation equivalence (Sections 5, 7, 12).
- Preserve the bounded M0–M4 program and its allowance for negative closure.
  Shape selection and the precise supplied datum remain research work at M3;
  this review does not select them or require a stronger presentation target.
- Counts and the Descent bridge remain conditional supporting work. No Lean
  implementation exists, and the current README accurately says so.

# Current drawers

## R1 — Align full-family reconstruction with all admissible observations

**Mismatch.** Section 12 defines observable-content equivalence by all declared
observations and their joint constraints, but M3's closing test names only the
image of the full-family comparison. That image does not in general determine
images for admissible subfamilies. Naturality supplies restriction maps, not
surjectivity of those maps. M4 explicitly forbids silently assuming that local
assignments extend globally.

**Counterexample.** Use the fixed shape `L → B ← M → D ← R`. Each local type
`L`, `M`, `R` is a singleton; each overlap `B`, `D` is `{0,1}`. All coarse
objects are singletons and all reductions are the unique surjections, so all
reduction squares commute. List the four fine restriction values in the order
`L→B`, `M→B`, `M→D`, `R→D`:

| System | Restriction values | Attainable LM | Attainable MR | Attainable LMR |
| --- | --- | --- | --- | --- |
| A | `(0,0,0,1)` | singleton | empty | empty |
| B | `(0,1,0,0)` | empty | singleton | empty |

These systems agree on full-family content but disagree on admissible binary
content. This refutes the general implication from equality of full images to
equality of all admissible images; it does not purport to refute completeness
of the still-unspecified M3 input datum.

**Required end state.** Make the target the collection of attainable images
`I_F` for every declared admissible family `F`, with its restriction maps; keep
the full-family image as the distinguished joint question. State explicitly
which proper-family images the supplied M3 datum already fixes and which must
be reconstructed. A full-image-only closing theorem suffices for that target
only with a theorem that it, together with the supplied datum, determines the
remaining admissible images. Align Sections 12, 26, and the closure criteria.
Do not add a blanket extension assumption to eliminate the counterexample.

**Closing evidence.** The revised contract distinguishes restriction inclusion
`restrict(I_F) ⊆ I_E` from equality, records the example above as a prospective
finite witness, and gives one consistent target in M3 and M4. Future Lean
certification belongs to the relevant implementation milestone.

## R2 — Carry both family comparison maps into M2

**Mismatch.** M1 separately characterizes fibers of the raw comparison `k`
and the injection from its quotient `Q`. M2 instead asks for the image and
fibers of the comparison *from observed classes*. Those quotient fibers are
automatically subsingletons. They cannot record how many fine compatible
families lift an observation, a distinction Section 10 explicitly preserves.

For a constant map from two fine lifts to one coarse family, the raw fiber has
two elements and the quotient fiber has one. Identifying the latter does not
characterize the former.

**Required end state.** Name both `k_F : P_F → P'_F` and the induced injection
`Q_F → P'_F` in M2. Assign the fine-lift fiber characterization to `k_F`, the
attainable-content identification to the injection, and naturality to both.
The image-only reconstruction target does not require recovering multiplicity,
but its supporting statements must not conflate these two fibers.

**Closing evidence.** M2's statement says which map each theorem concerns and
retains the two-lifts/one-class distinction as a calibration case.

## R3 — Correct the role of finiteness

**Mismatch.** Section 10 and M1 impose finite carriers on a theorem that uses
only maps, equality, images, and a quotient. This conflicts with the weakest
hypotheses policy and the proposed placement of reduction in `Core`, which
must not import finiteness. Commutation alone gives the comparison, its image
criterion, its fiber description, and the quotient injection. Objectwise
surjectivity defines the intended reduction scenario; it is not needed to
prove those constructions and equivalences.

Section 8 also says reconstruction by fiber cardinality is special to finite
sets and groups infinite fibers with structured fibers as a source of further
loss. For ordinary types in classical set theory, the cardinal-valued profile
still classifies maps over a fixed base: equal cardinalities give equivalences
of corresponding fibers, and choice assembles them over the base. Mathlib's
[`Cardinal.eq`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/SetTheory/Cardinal/Defs.html#Cardinal.eq)
states the underlying equivalence for arbitrary types. This does not produce
a computable inverse or preserve additional structure.

**Required end state.** State the binary core results for arbitrary types and
commuting maps, then specialize to surjective reductions and finite witnesses.
Keep finite enumeration and natural-number counting where consumed. Correct
Section 8 to distinguish natural-number profiles, general cardinal profiles
with classical choice, and invariants that forget additional fiber structure.
This correction does not add an infinite-cardinal formalization milestone.

**Closing evidence.** The proposal's theorem hypotheses and dependency rules
agree. Its warning about profile loss identifies the actual forgotten
structure or restricted statistic instead of infinitude alone.

## R4 — Make the mathematical contract readable and internally consistent

**Mismatch.** Display blocks use `\[` delimiters with doubled TeX commands
such as `\\operatorname`, and inline expressions appear as ordinary
parentheses. The configured Markdown formatter has only the front-matter
plugin, so it does not protect mathematical syntax. For example, the formula
at Section 3 is not written as a conventional Markdown math block with normal
TeX commands. Formatting checks currently do not establish that formulas
render correctly. Separately, Section 22 calls the package `Amalgam`, while M0
correctly distinguishes the Lake package `amalgam` from the root library
`Amalgam`.

**Required end state.** Use a documented Markdown math convention supported
by the intended renderer and protect it through formatting, or use readable
plain-text formulas consistently. Preserve real TeX row separators while
repairing command escaping. Align Section 22 with M0's package/library names.

**Closing evidence.** Inspect representative rendered inline expressions,
displayed maps, the commuting square, and the array in Section 1. Run the
formatter twice and verify that the corrected formulas remain intact. Inspect
the full document for the same escaping pattern, not only those examples.

# Verification and next submission

This review inspected the full proposal, README, and Nix configuration. A
disposable exhaustive enumeration of the singleton local assignments produced
the R1 table. The cardinality boundary was checked against mathlib's cardinal
definition and `Cardinal.eq`. No Lean theorem or build is claimed: no Lean
project exists here yet. Repository check results are recorded with this
review's commit and user-facing report.

The worker must revise the proposal for all four drawers, keep the README
accurate, inspect the mathematical rendering, and run `nix fmt` and
`nix flake check`. Rewrite this file as `READY FOR REVIEW`, `Turn: reviewer`,
identifying the exact committed candidate and evidence addressing every
drawer. Merely replying in chat is not a submission. The next reviewer should
read the revised contract as a whole and check that all-family content,
full-family content, fine lifts, and observed classes remain distinct.
