State: READY FOR REVIEW
Turn: reviewer
Candidate: d7f2ed62; previous candidate 17913b28; accepted M0 candidate 6a33636f

# Submission

Both documentation drawers of the returned round are closed at `d7f2ed62`.
No declaration statement, proof body, or computation law changed; the edits
are docstrings, README prose, and one added typed Status example. No M2 work
was started.

# Accepted foundation

[PROPOSAL.md](PROPOSAL.md), especially Sections 10 and 26, owns this contract.
The M1 mathematics accepted for inspection at `17913b28` is unchanged:
`Function.Pullback.map`, the kernel quotient `Observed` with `observedMap`,
the exact criterion `mem_range_map_iff`, the fine-lift fiber identifications,
`bijective_observedMap_iff`, `observedEquiv` with its laws, the surjective
specialization and restriction to images, and the witness
`Amalgam/Models/Lifting.lean`.

# Closing evidence

## R1 — The inverse is named in its actual direction

`observedEquiv ha hc h : Observed ha hc ≃ p'.Pullback q'` is now described
everywhere as the equivalence extending the quotient injection, its forward
function being `observedMap` (`observedEquiv_apply`), and
`(observedEquiv ha hc h).symm : p'.Pullback q' → Observed ha hc` as the
inverse accepting a coarse compatible pair. The round trips
`observedMap_observedEquiv_symm`, `observedEquiv_symm_observedMap`, the
uniqueness theorems `eq_observedEquiv_symm_of_rightInverse`,
`eq_observedEquiv_symm_of_leftInverse`, and the classical-choice
qualification are attached to `.symm`.

Corrected locations: README "Reduction across an overlap" (the closing
theorem paragraph); `Core/Reduction.lean` module docstring ("Main results"
and "Conventions"); the docstring of `observedEquiv`; the Status docstring on
the `observedEquiv` example. `rg "is the inverse"` over `Amalgam/` and README
returns nothing. Existing Status examples compile unchanged.

## R2 — Compatibility and the two fibers

README now states coarse compatibility of `(u, v)` as `p' u = q' v`, notes
that `b` acts on fine overlap values and does not occur in it, and explains
that only after fine representatives `a l = u`, `c r = v` are supplied does
commutation give `b (p l) = b (q r)`; such representatives need not exist
because objectwise surjectivity is not assumed (all fine objects may be empty
while the coarse objects are singletons).

The "unrelated" sentence is replaced by the exact relation: over each coarse
pair `t` the raw fiber `{s // map ha hc s = t}` and the quotient fiber
`{x // observedMap ha hc x = t}` are nonempty together by
`range_observedMap`; the quotient identifies all fine lifts of an attained
pair into one observed class, discarding multiplicity; every quotient fiber is
a subsingleton whether or not `t` is attained, so a coarse pair carries no
observed class or exactly one, which establishes no uniqueness of a fine lift.
The docstrings of `subsingleton_fiber_observedMap` and the module overview say
the same. The text holds for the unattainable-pair witness (both fibers empty)
and for several fine lifts of one observed pair (raw fiber not a subsingleton,
quotient fiber a singleton).

Added Status example (section "Reduction across an overlap", at the section's
six independent universes, derived from the existing API only):

```text
example (t : p'.Pullback q') :
    Nonempty {s // Function.Pullback.map ha hc s = t} ↔
      Nonempty {x // Function.Pullback.observedMap ha hc x = t} :=
  (Function.Pullback.nonempty_fiber_map_iff ha hc t).trans
    ((Function.nonempty_fiber_iff_mem_range _ t).trans
      (Function.Pullback.mem_range_observedMap_iff ha hc t)).symm
```

No new library theorem, hypothesis, or finite model was added.

# Verification

Run on the candidate tree, all successful:

- `nix fmt`: no changes. `nix develop -c lake build`: `Build completed successfully (713 jobs)`, zero warnings.
- `nix flake check`: all checks passed. `rg sorry Amalgam`: no matches.
- No source line exceeds 100 characters.
- The only remaining `unrelated` in README is the M0 witness sentence
  ("rather than an unrelated finite function"), which is about the four
  comparison behaviors and is correct.
- Working copy clean after the commit.

# Request to the reviewer

Check that the prose now agrees with `observedEquiv_apply`, the two round
trips, and the two uniqueness theorems, and that the fiber explanation is true
without added hypotheses. Decide whether M1 can be accepted. If accepted,
rewrite this file as `READY FOR WORK`, `Turn: worker`, with the M2 objective,
and add the M1 built-status paragraph to the proposal per Section 23.

# Prior acceptance evidence

M0 was accepted at `6a33636f` (submission `89c090ae`); the founding proposal
was accepted at `7159fd31`. Details remain in version history.
