State: RETURNED
Turn: worker
Candidate: d33ec042; submission a40daa94; accepted proposal baseline 7159fd31

# Objective and verdict

Complete **M0 — Maps, fibers, and binary compatibility**. The submitted
mathematics establishes the closing fiber identification, pointwise/global
existence and uniqueness criteria, coherent transport, trivial-overlap
reduction, and the four finite comparison behaviors. No false closing theorem
or missing comparison behavior was found.

Return the candidate for the bounded consolidation and tooling work below.
M0 is not accepted yet; do not start M1 or add an accepted M0 built-status
paragraph. The proposal's opening status has been truth-corrected to acknowledge
the implementation now present.

# Accepted foundation and resolved decisions

[PROPOSAL.md](PROPOSAL.md) remains the research contract.

- Preserve arbitrary carriers, independent universes, empty fibers, and the
  absence of finiteness or coverage hypotheses in the core criteria.
- Preserve mathlib's `Function.Pullback` and the fiber subtype
  `{x // f x = y}`; no replacement wrapper or bundled square is requested.
- Preserve the public comparison criteria, their projection and computation
  laws, and the concrete witnesses over the common nontrivial overlap.
- The later target remains all admissible attainable images with their
  restriction maps, distinct from fine multiplicity and presentation
  equivalence. M1–M4 retain their accepted scope.
- **License resolved:** leave the standard Apache LICENSE appendix and its
  example placeholders unchanged. They are the template for a notice copied
  into a work, not an unfinished project-specific copyright declaration.
  This is not a returned issue and requires no user decision.
- **Cache task resolved:** add `nu tasks.nu cache` invoking
  `lake exe cache get`, with a help entry, following the existing descent
  convention. This routine addition is authorized; do not ask again.

# Current drawers

## R1 — Make the comparison API consume the generic fiber API

**Mismatch.** `Core/Comparison.lean` imports no `Core/Fiber.lean` and
independently reproves results already supplied there:

- `injective_lift_iff_forall_subsingleton` repeats
  `Function.injective_iff_subsingleton_fiber` at `lift f g h`.
- `surjective_lift_iff_forall_nonempty` repeats
  `Function.surjective_iff_nonempty_fiber` at that map.
- `bijective_lift_iff_forall_nonempty_unique` repeats
  `Function.bijective_iff_nonempty_unique_fiber`.
- `fiberLiftCongr` rebuilds the transport already supplied by
  `Equiv.fiberCongr`, with `eG`, the pullback equivalence, and the proved
  naturality of `lift`.

These statements are correct. The issue is that the elementary fiber package
is bypassed by its first intended consumer, leaving two implementations of
the same mechanism before reduction and finite-family consumers arrive.

Within `Core/Fiber.lean`, `Equiv.fiberCompEquiv` also manually reconstructs
mathlib's `Equiv.subtypeEquivOfSubtype`. The existing docstring acknowledges
that equivalence. A fiber-specific name and generated simp lemmas justify a
specialization, not another implementation of its inverse and round trips.

**Required end state.** Import the generic fiber module from the comparison
module and derive the named comparison specializations from its results.
Use `Equiv.fiberCongr` for comparison-fiber transport after establishing
the diagram's naturality. Define the fiber-specific precomposition
equivalence by specializing mathlib's existing subtype equivalence.
Keep the useful public names, statement strength, and computation behavior.
Retain proofs specific to compatible pairs where the generic API does not
already establish the result. This drawer does not request new abstraction,
a broad rewrite, or consolidation of every one-line lemma.

**Closing evidence.** The source dependency and declaration bodies show this
reuse. Existing typed Status examples and all four witnesses still compile.
The transport apply/symm simp laws still act by the supplied global
equivalence and its inverse. Audit the changed definitions/theorems for
unexpected axioms and run the full build.

## R2 — Add the cache task and document the build workflow

**Mismatch.** `tasks.nu` exposes build, check, and fmt but omits the requested
mathlib-cache command. The pinned mathlib checkout already provides the cache
executable; no new dependency or copying from a sibling repository is needed.

**Required end state.** Add a Nushell `main cache` command running
`lake exe cache get`, advertise it in the task listing, and briefly document
its use after a toolchain or mathlib revision change in the README's build
instructions. The command must fetch artifacts for this project's pinned
dependencies. Do not modify dependency pins or add an automatic update.

**Closing evidence.** The help listing includes cache, and invoking
`nu tasks.nu cache` in the development shell succeeds; an already populated
cache is a valid outcome. Re-run the normal formatting and repository checks.
No extra test harness is required for this wrapper.

# Verification performed by the reviewer

- Read all four Lean modules, the root aggregator, README, package and pinned
  manifest, development shell, task runner, and submitted evidence.
- `nix develop -c lake build` succeeded with 697 jobs and no warnings.
- `nix flake check` succeeded for the submitted tree.
- A disposable Lean file ran `#print axioms` on all 130 explicitly declared
  library definitions, abbreviations, and theorems. Only `propext`,
  `Classical.choice`, and `Quot.sound` appeared; no project axiom or
  `sorryAx` appeared. Generated simp declarations were not counted separately.
- Inspected the closing theorem hypotheses, equivalence inverse laws, and
  README-to-Status statements at their advertised generality. The four finite
  examples use the actual comparison construction and carry the claimed
  unreached pairs and distinct-state witnesses.
- Checked the relevant existing mathlib subtype equivalence and pullback
  definitions in the pinned source. The cache task matches descent's
  `lake exe cache get` convention.
- No Lean implementation was changed by this review. Temporary axiom-audit
  artifacts are disposable verification only.

# Next submission

Work from this file and address R1–R2. Preserve M0's mathematical scope, keep
README and proposal status truthful, then run `nix fmt`, `lake build`, and
`nix flake check`. Commit the candidate and leave a clean working copy.

Rewrite `REVIEW.md` as `READY FOR REVIEW`, `Turn: reviewer`, with the exact
committed candidate and evidence for both drawers, including the cache
invocation and the changed declarations' axiom audit. Merely replying in chat
is not a submission. The next reviewer should check the consolidation without
weakening the API or its Status coverage, then decide whether M0 can be
accepted and advance to M1.
