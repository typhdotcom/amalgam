State: READY FOR REVIEW
Turn: reviewer
Candidate: 6a33636f; previous candidate d33ec042; accepted proposal baseline 7159fd31

# Submission

Both drawers of the returned round are closed at `6a33636f`. The M0
mathematics, public names, statement strength, Status coverage, and the four
witnesses are unchanged; only proof bodies, one definition body, imports, the
task runner, and the README build section changed. No M1 work and no accepted
built-status paragraph were added.

# Accepted foundation and resolved decisions

[PROPOSAL.md](PROPOSAL.md) remains the research contract.

- Arbitrary carriers, independent universes, empty fibers, and the absence of
  finiteness or coverage hypotheses in the core criteria are preserved.
- Mathlib's `Function.Pullback` and the fiber subtype `{x // f x = y}` remain
  the only representations; no wrapper or bundled square exists.
- The later target remains all admissible attainable images with their
  restriction maps, distinct from fine multiplicity and presentation
  equivalence. M1–M4 retain their accepted scope.
- License: the Apache appendix placeholders are left unchanged, as resolved.
- Cache task: added as resolved; no dependency pin changed.

# Closing evidence

## R1 — The comparison API consumes the generic fiber API

`Amalgam/Core/Comparison.lean` now begins with `import Amalgam.Core.Fiber`
(the `Mathlib.Logic.Equiv.Basic` and `Mathlib.Logic.Unique` imports moved
into `Fiber.lean`, which already needed them). Changed bodies, statements
unchanged:

- `injective_lift_iff_forall_subsingleton` :=
  `injective_iff_subsingleton_fiber (lift f g h)`.
- `surjective_lift_iff_forall_nonempty` :=
  `surjective_iff_nonempty_fiber (lift f g h)`.
- `bijective_lift_iff_forall_nonempty_unique` :=
  `bijective_iff_nonempty_unique_fiber (lift f g h)`.
- `fiberLiftCongr … c` :=
  `Equiv.fiberCongr eG (congr eL eR eB hp hq) (fun x => (congr_lift … x).symm) c`,
  so comparison-fiber transport is the generic fiber transport along `eG`
  and the pullback equivalence, with naturality `congr_lift` supplying the
  intertwining law. `fiberLiftCongr_apply_coe` and
  `fiberLiftCongr_symm_apply_coe` keep their statements (`= eG x`,
  `= eG.symm x`) and both close by `rfl`; a scratch check confirmed `simp`
  proves them from the simp set.

`Amalgam/Core/Fiber.lean`: `Equiv.fiberCompEquiv f e y` is now
`subtypeEquivOfSubtype (p := fun x => f x = y) e`, mathlib's subtype
equivalence specialized to the fiber predicate; its docstring says so. The
two simp lemmas `fiberCompEquiv_apply_coe : ↑(… x') = e ↑x'` and
`fiberCompEquiv_symm_apply_coe : ↑(….symm x) = e.symm ↑x` are stated by hand
and close by `rfl`, with the same statements the generated lemmas had.

Comparison-specific proofs that the generic API does not supply are retained:
the pointwise `_fiber_lift_iff` family (which rewrite through `lift_eq_iff`),
`injective_lift_iff`, `surjective_lift_iff`, `bijective_lift_iff`,
`bijective_lift_iff_existsUnique`, projection fibers, `swap`, `congr`, and
the trivial-overlap reduction.

Axiom audit of every changed declaration (`#print axioms` in a scratch file
importing `Amalgam`):

| Declaration | Axioms |
| --- | --- |
| `injective_lift_iff_forall_subsingleton` | none |
| `surjective_lift_iff_forall_nonempty` | none |
| `bijective_lift_iff_forall_nonempty_unique` | none |
| `fiberLiftCongr`, `_apply_coe`, `_symm_apply_coe` | propext, Quot.sound |
| `injective/surjective/bijective_lift_iff_of_congr` | propext, Quot.sound |
| `Equiv.fiberCompEquiv`, `_apply_coe`, `_symm_apply_coe` | propext, Quot.sound |

`Classical.choice` does not appear in any of them. `Status.lean` and
`Models/Overlap.lean` compile unchanged, so every typed Status example and all
four witnesses still hold at their previous strength.

## R2 — Cache task and build workflow

`tasks.nu` gains `main cache` running `lake exe cache get`, listed in the
help output between `build` and `check`. README's Building section says to run
`nu tasks.nu cache` after changing `lean-toolchain` or the mathlib revision,
before `lake build`. No pin changed and no automatic update was added.

Invocation in the development shell (`nix develop -c nu tasks.nu cache`):

```text
Using cache from origin: (some leanprover-community/mathlib4)
No files to download
Already decompressed 8690 file(s)
```

`nix develop -c nu tasks.nu` lists build, cache, check, fmt.

# Verification

Run on the candidate tree, all successful:

- `nix develop -c lake build`: `Build completed successfully (697 jobs)`,
  zero warnings.
- `nix fmt`: no changes. `nix flake check`: all checks passed.
- `rg sorry Amalgam`: no matches.
- Working copy clean after the commit.

# Request to the reviewer

Check that the consolidation neither weakened the API nor reduced Status
coverage, then decide whether M0 can be accepted. If accepted, rewrite this
file as `READY FOR WORK`, `Turn: worker`, with the M1 objective from
[Section 26](PROPOSAL.md#26-initial-milestones), and add the M0 built-status
paragraph to the proposal per Section 23.

# Proposal acceptance evidence

The founding proposal at `7159fd31` was accepted (SHA-256
`43dc0ab30372cde3f9134073ca68bf507e3fd9b11d5a050991a068c5a4dfbe6c`); R1–R4
of that round closed without remaining corrections. Details remain in
version history.
