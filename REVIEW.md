State: READY FOR REVIEW
Turn: reviewer
Candidate: PROPOSAL.md and README.md at 7159fd31

# Objective and submission

Review the revised founding proposal before Lean implementation. Candidate
`7159fd31` revises the mathematical contract in response to R1–R4 from review
`60f38e6d`. The README is unchanged and still accurately describes a proposal
with Nix tooling and no Lean implementation. This submission requests review;
it does not declare the proposal accepted or any milestone implemented.

The maps-first foundation, binary lifting criterion, separation of local
lifting from extension to a supplied global realization, and bounded M0–M4
program remain. M3 still selects the precise shape and supplied local datum.
Counts and the Descent bridge remain conditional supporting work.

# R1 — Target covers every admissible family

**Candidate:** [Section 12](PROPOSAL.md#12-coherent-reconstruction),
[M2–M4](PROPOSAL.md#26-initial-milestones), and
[completion criteria](PROPOSAL.md#31-stopping-and-completion).

The target is the collection `I_F = image(k_F) = image(k_bar_F)` for every
declared admissible family, with restrictions inherited from the fixed coarse
datum. Naturality gives `restrict_(F,E)(I_F) ⊆ I_E`; equality needs a further
theorem. Over the fixed coarse datum, equality of the images also fixes these
restricted maps.

M3 must list the proper-family images fixed by its input and those requiring
reconstruction. The full-family image remains the distinguished joint question.
A theorem reconstructing only that image closes the target only with a theorem
that it and the supplied datum determine all remaining admissible images and
their restriction maps. M4 and the closure criteria retain this same target.
No blanket extension assumption was added.

**Evidence:** Section 12 records the prospective witness on
`L → B ← M → D ← R`, with singleton local types, two-point overlaps, and
singleton coarse objects. A disposable enumeration checked all 16 possible
four-tuples of fine restriction values. For a tuple `(a, b, c, d)`, the image
sizes are `(|I_LM|, |I_MR|, |I_LMR|) = (1[a=b], 1[c=d], 1[a=b and c=d])`.
The prescribed rows give:

```text
A: (0, 0, 0, 1) → (1, 0, 0)
B: (0, 1, 0, 0) → (0, 1, 0)
```

The example separates full-family content from all admissible content. It
makes no completeness claim about M3's still-unspecified input. Future Lean
certification is assigned to M2.

# R2 — Fine lifts and observed classes have separate maps

**Candidate:** [Section 12](PROPOSAL.md#12-coherent-reconstruction) and
[M2](PROPOSAL.md#m2--the-comparison-for-finite-families).

M2 names both `k_F : P_F → P'_F` and `k_bar_F : Q_F → P'_F`. The raw map's
fibers are fine compatible lifts. The quotient map is injective, identifies
`Q_F` with `I_F`, and has subsingleton fibers. Naturality is required for both
maps under the declared family restrictions. The image target does not require
recovering fine multiplicity.

**Evidence:** M2 retains the two-lifts/one-class calibration case. A disposable
check of the constant map `{0, 1} → {0}` found two elements in its raw fiber and
one quotient class over the same outcome. This is a sanity check; the
calibration theorem remains part of the future Lean milestone.

# R3 — Hypotheses and cardinality boundary corrected

**Candidate:** [Section 8](PROPOSAL.md#8-finite-profiles-are-derived-observables),
[Section 10](PROPOSAL.md#10-compatibility-is-more-than-a-product), and
[M1–M2](PROPOSAL.md#26-initial-milestones).

The binary constructions, fiber descriptions, and image criterion now assume
arbitrary types and commuting maps. Objectwise surjective reductions are a
specialization; finite carriers are used for the prescribed witnesses. M2
also distinguishes finite indexing families from arbitrary state carriers.
This agrees with placing reduction in `Core` without finiteness imports.

Section 8 distinguishes natural-number profiles and finite sums from general
cardinal-valued profiles. It explains the classical existence classification
over a fixed base, the need for a common universe or cardinal lifts, and the
absence of a computable inverse supplied merely by cardinal equality. The
warning about lost information now concerns additional fiber structure or a
coarser statistic, rather than infinitude alone. No infinite-cardinal milestone
was added.

**Evidence:** Checked the published mathlib statement of
[`Cardinal.eq`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/SetTheory/Cardinal/Defs.html#Cardinal.eq):
cardinal equality of arbitrary types is equivalent to existence of a type
equivalence. Choosing such equivalences fiberwise and assembling them over the
fixed base gives the stated classical classification. The proposal cites that
source and distinguishes this mathematical boundary from implemented results.

# R4 — Plain-text mathematical notation and consistent names

**Candidate:** the notation convention near the proposal's start, all formulas
throughout the document, and [Section 22](PROPOSAL.md#22-mathlib-quality-naming-and-documentation).

The proposal uses the permitted plain-text alternative: Unicode mathematical
symbols and readable names in CommonMark inline code and fenced `text` blocks.
All 32 former display-math blocks were converted, including the original row
structure of the Section 1 array and Section 3 commuting square. Parenthesized
inline math was converted too. The full proposal contains no backslashes or
remaining TeX command escapes. No formatter or renderer plugin is needed.
Section 22 now matches M0: Lake package `amalgam`, root library and namespace
`Amalgam`.

**Evidence:** Rendered the entire candidate with markdown-it-py's CommonMark
renderer. An HTML-parser check verified that all 180 code spans and blocks
retained their source text, including all 36 `text` fences. Rendered excerpts
from Sections 1 and 3 in headless Chromium and visually inspected inline
expressions, displayed maps, the commuting square, and the four-row array.
All were legible with their intended rows and symbols.

The disposable inspection artifacts are `/tmp/amalgam-review/proposal.html`,
`/tmp/amalgam-review/notation.html`, and `/tmp/amalgam-review/notation.png`.
They are verification artifacts, not project dependencies or formal proofs.

Two consecutive `nix fmt` runs left the proposal byte-for-byte unchanged.
Its SHA-256 after each run was:

```text
43dc0ab30372cde3f9134073ca68bf507e3fd9b11d5a050991a068c5a4dfbe6c
```

# Verification and reviewer handoff

For candidate `7159fd31`, `nix flake check` passed all seven checks:
formatting, statix, deadnix, gitleaks, shellcheck, actionlint, and markers.
The finite enumerations and rendering inspection above are evidence for this
proposal revision, not Lean theorem certification. No `lake build` is claimed:
there is no Lean project yet.

The reviewer should read the revised contract as a whole and decide whether
R1–R4 are closed. In particular, check that all-family content, full-family
content, fine lifts, and observed classes remain distinct from Sections 10–12
through M2–M4 and closure. The next decision is acceptance of this research
contract or a precise remaining gap; this submission does not implement M0 or
select M3's research datum.
