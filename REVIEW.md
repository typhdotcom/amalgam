State: READY FOR WORK
Turn: worker
Candidate: —; accepted M1 candidate d7f2ed62, submission 5caccd00

# Verdict and active objective

M1 is accepted without remaining corrections. R1–R2 are closed. The proposal's
[M1 section](PROPOSAL.md#26-initial-milestones) records the built API, closing
theorems, and strict finite failure.

The active objective is **M2 — The comparison for finite families**.
Construct the attainable observed content of each declared compatible family,
together with its restrictions to other declared families. The central
theorem must identify the fine-lift fibers and observed quotient and prove
that comparison commutes with those restrictions. M2 prepares the objects for
the coherent inverse problem; it does not settle M3's classification.

# Accepted foundation

[PROPOSAL.md](PROPOSAL.md), Sections 11–12 and 26, owns the M2 contract.

- M0 is accepted at `6a33636f`; M1 at `d7f2ed62`. Reuse their generic fiber,
  comparison, quotient/image, and lifting results where they apply.
- Carriers remain arbitrary types, possibly empty. Finite families concern
  indexing, not finiteness or decidability of state types.
- Raw fibers record fine compatible lifts. Quotient fibers record observed
  classes. They share inhabitedness; quotient injectivity does not imply
  uniqueness of fine lifts.
- The target is the collection of attainable images for every declared
  admissible family, with its induced restriction maps on the fixed coarse
  datum. A full-family image need not determine proper-family images.
- Restriction naturality gives image inclusion. Surjectivity or equality of
  restricted images requires an additional theorem.
- A supplied global realization is separate from compatible descriptions.
  Do not assume every local family extends globally.
- Do not select M3's research shape or datum, classify local sufficiency,
  introduce a counting hierarchy, or start the Descent bridge in this round.
- Keep the pinned build setup, Status discipline, resolved Apache appendix,
  and existing build/cache tasks.

# Datum and construction

Use a preorder of contexts with a state type at each context and restriction
maps toward coarser contexts satisfying identity and composition. This
supports the binary span and the shared-overlap shape required below without
category-theoretic infrastructure. Name the order direction in the API.

For a finite indexed family of contexts, a compatible assignment consists of
one state per local context, agreeing after restriction to every common
coarser context. Expose which families and restriction operations are declared
admissible; a map between underlying products alone does not make an operation
admissible. The interface must support forgetting local views and restricting
a view along a supplied context restriction.

A fine and coarse restriction system on the same context shape, with
component observation maps commuting with restriction, induce
`k_F : P_F → P'_F` for each admissible family. Define `Q_F` by agreement of
all observed components, its injection `k_bar_F : Q_F → P'_F`, and the
attainable image `I_F`. These are schematic names; choose standard Lean names
and reuse existing constructions. State the setup explicitly before claiming
a theorem about it. No componentwise surjectivity is implicit.

# Current work and closing evidence

## M2.1 — Compatible families and their restrictions

Implement the restriction interface and compatible-family type at the weakest
hypotheses the statements consume. Define family restriction maps and prove
their identity/composition laws. Their action must be actual restriction of
the supplied state assignments, not an arbitrary function assumed to preserve
an opaque compatibility predicate.

Prove invariance under relabeling the same finite presentation. Prove the
redundancy law: adding a view already obtained by restricting an included
context adds no information, and forgetting it is an equivalence. Use the
restriction laws to discharge the added compatibility conditions. Include
duplicate occurrences as a presentation case. Expose the equivalences and
both round trips.

**Evidence:** concrete definitions and theorem statements, with a dependency
graph showing which restriction laws are consumed. The interface represents
both a binary overlap and `L → B ← M → D ← R`. Empty families and empty
state types are accounted for by the definitions, without coverage assumptions.

## M2.2 — Comparison, fibers, quotients, and naturality

Construct the raw comparison by observing each component. Identify its fiber
over a coarse compatible family as fine assignments satisfying compatibility
and every component observation equation. Derive the image criterion as
existence of such a simultaneous fine lift.

Use the observed-equality quotient to construct the injection and identify
its image with `I_F`, with factorization and round-trip laws for the
quotient-to-image equivalence. Establish shared inhabitedness of raw and
quotient fibers, separately from the latter's automatic subsingleton property.

For every declared family restriction `F → E`, construct the corresponding
maps on fine families, coarse families, quotient classes, and attainable
images. Prove the commuting diagrams for the raw and quotient comparisons.
Quotient restriction must be well-defined on observed classes, not chosen
fine representatives. Preserve identity/composition through these maps.

**Evidence:** the actual naturality equalities, image restriction maps, and

```text
restrict_(F,E)(I_F) ⊆ I_E.
```

Do not claim equality or surjectivity from naturality. Describe fibers of the
family restrictions as extension choices from the smaller assignment and
relate them to the full-family lift constraints. The relationship must track
the same shared local states, not independently chosen lifts.

## M2.3 — Binary recovery and two finite calibration cases

Identify the binary compatible-family types with the accepted pullbacks and
prove that the family raw comparison agrees with M1's `Function.Pullback.map`
under those equivalences. Transport the observed quotient, attained image,
and fine-lift interpretation coherently. Recover M1's intersection criterion
through this identification rather than leaving the binary and family APIs
as independent theories.

Certify the two required finite cases through the family construction:

1. Two distinct fine compatible families map to one coarse family and yield
   one observed class. Show that the raw fiber has exactly those two elements
   and the quotient fiber is a singleton, without adding a general counting
   package.
2. The Section 12 witness on `L → B ← M → D ← R`: singleton local state
   types, two-point overlaps, singleton coarse objects, and fine restriction
   values `(0,0,0,1)` versus `(0,1,0,0)` in the declared arrow order.
   Both full-family images are empty, while the `LM` and `MR` images
   differ as stated in the proposal. All observations commute and are
   surjective. Include the local families and their restriction maps in the
   admissible datum.

**Evidence:** named equivalences/naturality theorems for binary recovery and
named finite data and theorems for both cases. The second case must visibly
give strict image restriction inclusion and distinguish full-family from
all-family content. It does not yet refute any M3 datum, which remains
unselected; no smallest-shape claim is requested.

# Verification and submission

Place the system interface and family results downstream of the generic core;
finite witnesses belong in Models. Reuse generic quotient and fiber results
when statements coincide. Keep explicit root exports and concise module
documentation. Update the README to compiled claims and mirror new claims
with explicitly typed Status examples at their stated generality.

Run `nix fmt`, `lake build`, and `nix flake check`. Audit closing
declarations and witnesses for axioms; no `sorry` or new project axiom is
accepted. Inspect the naturality and binary transport statements, not only
their names. The cumulative M0–M1 evidence must continue to build.

Work from this file and complete M2. Commit the candidate and rewrite
`REVIEW.md` as `READY FOR REVIEW`, `Turn: reviewer`, with the exact
committed candidate and evidence for M2.1–M2.3. Merely replying in chat is
not a submission. The next reviewer must judge the whole family construction
and both calibration cases before opening M3.

# M1 acceptance evidence

The corrected prose names `observedEquiv` as the equivalence whose forward
function is `observedMap` and `.symm` as the inverse. Coarse compatibility
is `p' u = q' v`; equality after `b` is explained only after supplying fine
representatives. The public description now records the shared existence
and potentially different multiplicity of raw and quotient fibers.

The new typed Status example proves their pointwise shared inhabitedness at
six independent carrier universes with no added hypotheses. An independent
audit of that exact proof used only `propext` and `Quot.sound`. No M1
library declaration statement or proof changed from the prior inspected
candidate. The reviewer reran the full build (713 jobs, no warnings) and
repository checks successfully. Prior criterion, inverse, witness, and
100-declaration axiom audit evidence remains in version history.
