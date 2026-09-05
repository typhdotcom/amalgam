State: RETURNED
Turn: worker
Candidate: 17913b28; submission 1e572e80; accepted M0 candidate 6a33636f

# Objective and verdict

Complete **M1 — When local reduction preserves compatibility**. The compiled
quotient relation, exact image criterion, raw fiber identifications, inverse
laws, image restriction, and prescribed finite failure satisfy the mathematical
obligations inspected in this round. Return the submission for the public
explanation and corresponding Status coverage below. M1 is not yet accepted;
do not begin M2 or add an accepted M1 built-status paragraph.

The issue is a mismatch between correct typed declarations and the sentences
that explain what they mean. This round does not request a new research
theorem, an API redesign, or a replacement proof of the criterion.

# Accepted foundation

[PROPOSAL.md](PROPOSAL.md), Sections 10 and 26, owns the M1 contract.

- Keep arbitrary carriers and independent universes, including empty types.
  Commutation is the only hypothesis of the exact lifting criterion;
  objectwise surjectivity specializes to reductions.
- Keep the raw comparison as the existing pullback map, the observed quotient
  as `Quotient (Setoid.ker map)`, and the quotient injection from mathlib's
  `Setoid.kerLift`. Preserve the factorization and equality of images.
- Keep all current image criteria, inverse laws, and fine-lift fiber
  identifications at their present strength. Preserve the four M0 behaviors
  and the M1 witness through the actual comparison API.
- M0 is accepted at `6a33636f`. M2's families, M3's shape selection, counting,
  and the Descent bridge remain outside this correction round.
- The Apache appendix and the implemented cache task remain resolved.

# Current drawers

## R1 — Name the inverse in its actual direction

**Mismatch.** README's reduction section says
`Function.Pullback.observedEquiv` “is the inverse on all coarse compatible
pairs.” The module overview in `Core/Reduction.lean` makes the same claim.
But the declaration has type `Observed ha hc ≃ p'.Pullback q'`, and
`observedEquiv_apply` proves that its forward function is `observedMap`.
The inverse accepting a coarse compatible pair is
`(observedEquiv ha hc h).symm`.

The round-trip and uniqueness theorems already use `.symm` correctly.
The typed Status examples also have the correct orientation. The public
explanation currently tells a reader to use the forward map where an inverse
is required.

**Required end state.** Describe `observedEquiv` as the equivalence extending
the quotient injection and its `.symm` as the inverse. Attach the inverse's
type, round trips, uniqueness, and classical-choice qualification to that
direction. Correct both README and the module overview; inspect the rest of
the public prose for the same reversal. Preserve the existing declarations
and their computation laws.

**Closing evidence.** The prose agrees with `observedEquiv_apply`,
`observedMap_observedEquiv_symm`,
`observedEquiv_symm_observedMap`, and the two uniqueness theorems.
Existing typed Status examples continue to compile.

## R2 — Explain compatibility and the two fibers without erasing their relation

**Mismatch.** Two sentences in README's reduction section overstate the
separation between fine and observed data.

First, it says coarse views “agree after `b`.” Here
`b : B → B'` acts on fine overlap values, not coarse local views.
The definition of coarse compatibility is `p' u = q' v`. Only after
supplying fine representatives `a l = u` and `c r = v` can commutation
turn that equality into `b (p l) = b (q r)`. Such representatives need not
exist in the general theorem: objectwise surjectivity is not assumed.
For example, all fine objects can be empty and all coarse objects singleton,
with vacuously commuting observations and an unattainable coarse pair.

Second, it calls the fibers of `observedMap` “unrelated” to the raw fibers.
They have exactly the same inhabitedness over each coarse pair.
`range_observedMap` and the generic fiber/range criterion already imply:

```text
Nonempty {s // map ha hc s = t}
  ↔ Nonempty {x // observedMap ha hc x = t}.
```

The quotient identifies all fine lifts over an attained pair into a single
observed class. It preserves existence and discards distinctions between
those fine lifts. Its fibers are subsingletons whether attained or not;
they do not establish uniqueness of a fine lift.

**Required end state.** State coarse compatibility as `p' u = q' v` and
explain equality after `b` conditionally on supplied fine representatives.
Replace “unrelated” with the exact distinction above: shared existence,
potentially different multiplicity. Preserve the distinction between no
observed class and exactly one observed class.

**Closing evidence.** Add an explicitly typed Status example for the displayed
pointwise nonemptiness equivalence, deriving it from the existing image/fiber
API; a new named library theorem is not required. The revised README should
be true for both the existing unattainable-pair witness and cases with several
fine lifts of one observed pair. Do not add surjectivity or nonemptiness
hypotheses to make the explanation true, and do not create a new finite-model
package for these prose corrections.

# Verification performed by the reviewer

- Read `Core/Reduction.lean`, `Models/Lifting.lean`, the complete new
  README section, its typed Status examples, the root exports, and the
  unchanged M0 surface and pinned build setup.
- `nix develop -c lake build` succeeded (713 jobs, no warnings).
  `nix flake check` passed for the submitted tree.
- Independently ran `#print axioms` on all 100 explicit new declarations
  across Reduction and Lifting, including the named instance. The only
  axioms were `propext`, `Quot.sound`, and `Classical.choice`.
  Choice appeared only in the quotient-to-image equivalence, the inverse
  equivalence, existence-of-inverse packaging, and declarations depending
  on those constructions. No `sorryAx`, project axiom, or warning appeared.
- Inspected the relation as equality of both observed components, the actual
  common-overlap-value criterion with no coverage assumptions, the inverse's
  round trips and uniqueness, and restriction to images. The finite failure
  uses the exact criterion and actual quotient comparison.
- M0's core modules and four-witness module are unchanged from their accepted
  candidate. The cumulative build checks their Status examples too.
- No product implementation was changed. The disposable axiom-audit file was
  removed after verification.

# Next submission

Work from this file and address R1–R2. Keep the mathematical API and scope,
make the public prose agree with the compiled statements, and add the one
typed Status example requested above. Run `nix fmt`, `lake build`, and
`nix flake check`; audit the added example for unexpected axioms.

Commit the candidate and rewrite `REVIEW.md` as `READY FOR REVIEW`,
`Turn: reviewer`, with the exact committed candidate and evidence for both
drawers. Merely replying in chat is not a submission. The next reviewer
should check the corrected public interpretation against the existing
declarations, then decide whether M1 can be accepted and M2 opened.
