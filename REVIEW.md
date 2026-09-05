State: READY FOR REVIEW
Turn: reviewer
Candidate: d33ec042; accepted proposal baseline 7159fd31

# Submission

M0 — Maps, fibers, and binary compatibility — is implemented at
`d33ec042`. The Lean library builds from a clean checkout on the pinned
toolchain and mathlib, contains no `sorry` and no project axiom, and every
load-bearing README claim has a typed example in `Amalgam/Status.lean`. The
reviewer should inspect the declarations named below and decide whether M0 is
complete before advancing to M1.

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

# Evidence

## M0.1 — Reproducible library and public surface

- `lakefile.toml`: package `amalgam`, library `Amalgam`, `license = "Apache-2.0"`,
  `licenseFiles = ["LICENSE"]`, `autoImplicit = false`, mathlib `v4.33.1`.
- `lean-toolchain`: `leanprover/lean4:v4.33.1`. `lake-manifest.json` pins
  mathlib at `0df444a360eaa60ab8c11dca51a86af692955474` with its transitive
  dependencies. `LICENSE` is Apache-2.0. No private dependency.
- `nix/devshell.nix` supplies `elan`; `nu tasks.nu build` runs `lake build`.
- Root `Amalgam.lean` imports exactly `Amalgam.Core.Comparison`,
  `Amalgam.Core.Fiber`, `Amalgam.Models.Overlap`, `Amalgam.Status`.
- Dependency direction: `Core` imports mathlib only; `Models/Overlap` imports
  `Core.Comparison` and `Mathlib.Data.Fintype.Prod`; `Status` imports the
  three library modules; no library module imports `Status`.
- README-to-Status claim map: README sections *Fibers*, *Compatible pairs and
  the comparison map*, *Four comparison behaviors* correspond to the Status
  sections of the same names; each README sentence has an explicitly typed
  `example` there.

## M0.2 — Fibers and exact extension criteria

Conventions: the fiber of `f` over `y` is `{x // f x = y}` (the
`Equiv.sigmaFiberEquiv` convention); compatible pairs are mathlib's
`Function.Pullback p q`; no wrapper types. All Core statements are for
arbitrary types in arbitrary universes with no `Fintype`, `DecidableEq`,
cardinality, or coverage hypothesis. Empty carriers and empty fibers are
allowed.

`Amalgam/Core/Fiber.lean` (namespaces `Function`, `Equiv`):

- source decomposition: mathlib `Equiv.sigmaFiberEquiv`, computation lemma
  `Equiv.sigmaFiberEquiv_mk`;
- reached/missed: `Function.nonempty_fiber_iff_mem_range`,
  `Function.isEmpty_fiber_iff_notMem_range`;
- pointwise and global criteria: `Function.subsingleton_fiber_iff`,
  `Function.injective_iff_subsingleton_fiber`,
  `Function.surjective_iff_nonempty_fiber`,
  `Function.bijective_iff_nonempty_unique_fiber`,
  `Function.bijective_iff_nonempty_and_subsingleton_fiber`;
- transport: `Equiv.fiberCongr` (source and target equivalences intertwining
  `f` and `f'`), `Equiv.fiberCompEquiv`, `Equiv.fiberEquivComp`;
- composition: `Equiv.fiberComp`; set form: `Equiv.fiberEquivPreimage`.
  All are `@[simps]`, so inverse laws are the generated `_apply_coe` and
  `_symm_apply_coe` lemmas.

`Amalgam/Core/Comparison.lean` (namespace `Function.Pullback`), for a span
`p : L → B`, `q : R → B` and a square `f : G → L`, `g : G → R`,
`h : ∀ x, p (f x) = q (g x)`:

- compatible pairs: `mk`, `fst_mk`, `snd_mk`, `comm`, `ext`, `ext_iff`,
  `mk_eq_mk`;
- comparison `lift f g h : G → p.Pullback q` with projection laws `fst_lift`,
  `snd_lift`, `fst_comp_lift`, `snd_comp_lift`, universal property
  `lift_unique`, `hom_ext`, `lift_fst_snd`, `lift_comp`;
- closing identification `fiberLiftEquiv c : {x // lift f g h x = c} ≃ {x // f x = c.fst ∧ g x = c.snd}` with
  `fiberLiftEquiv_apply_coe`, `fiberLiftEquiv_symm_apply_coe`;
- pointwise criteria (Section 4): `isEmpty_fiber_lift_iff`,
  `nonempty_fiber_lift_iff`, `subsingleton_fiber_lift_iff`,
  `nonempty_unique_fiber_lift_iff`, `existsUnique_lift_eq_iff`;
- global criteria and pointwise↔global equivalences: `injective_lift_iff`,
  `injective_lift_iff_forall_subsingleton`, `surjective_lift_iff`,
  `surjective_lift_iff_forall_nonempty`, `bijective_lift_iff`,
  `bijective_lift_iff_existsUnique`,
  `bijective_lift_iff_forall_nonempty_unique`;
- projection fibers (base change): `fiberFstEquiv`, `fiberSndEquiv` with
  apply/symm simp lemmas;
- symmetry: `swap`, `fst_swap`, `snd_swap`, `swap_mk`, `swap_symm`,
  `swap_swap`, `swap_lift`, `swap_comp_lift`;
- transport under coherent equivalences `eL eR eB` with `hp hq` and
  `eG` with `hf hg`: `congr` (with `fst_congr`, `snd_congr`, `congr_mk`,
  `fst_congr_symm`, `snd_congr_symm`), naturality `congr_lift`,
  `congr_comp_lift`, `fiberLiftCongr` (with apply/symm simp lemmas),
  `injective_lift_iff_of_congr`, `surjective_lift_iff_of_congr`,
  `bijective_lift_iff_of_congr`;
- trivial overlap under `[Subsingleton B]`: `equivProdOfSubsingleton`
  (with apply and symm projection lemmas), `equivProdOfSubsingleton_lift`,
  `equivProdOfSubsingleton_comp_lift`, `injective_lift_iff_of_subsingleton`,
  `surjective_lift_iff_of_subsingleton`, `bijective_lift_iff_of_subsingleton`.

Squares and coherent equivalences are unbundled; the module docstring records
that a structure would only shorten argument lists.

## M0.3 — Four certified comparison behaviors

`Amalgam/Models/Overlap.lean` (namespace `Amalgam.Models.Overlap`). One span
for all four cases: `B = Bool`, `L = R = Bool × Bool`, `p = q = Prod.fst`, so
compatibility discards half of `L × R` (Status: `¬Subsingleton B`). Each
`compareᵢ` is definitionally `Function.Pullback.lift fᵢ gᵢ commᵢ` (Status
checks this by `rfl`).

| Square | `G` | `f`, `g` | Positive | Negative | Witness |
| --- | --- | --- | --- | --- | --- |
| 1 | `Bool × Bool × Bool` | `(b,x,y) ↦ (b,x)`, `(b,y)` | `bijective_compare₁` | — | — |
| 2 | `Bool × Bool` | identity, identity | `injective_compare₂` | `not_surjective_compare₂` | `unreached₂ = mk (true,true) (true,false)`, `isEmpty_fiber_unreached₂` |
| 3 | `Bool × Bool × Bool × Bool` | `(b,x,y,z) ↦ (b,x)`, `(b,y)` | `surjective_compare₃` | `not_injective_compare₃` | `state₃ ≠ state₃'`, `compare₃_state₃_eq` |
| 4 | `Bool × Bool` | `(b,x) ↦ (b,false)` both | — | `not_injective_compare₄`, `not_surjective_compare₄` | `unreached₄`, `isEmpty_fiber_unreached₄`; `state₄ ≠ state₄'`, `compare₄_state₄_eq` |

`not_bijective_compare₂/₃/₄` are also provided. Positive properties are proved
through `bijective_lift_iff`, `injective_lift_iff`, `surjective_lift_iff`;
failures of existence through `isEmpty_fiber_lift_iff` and
`surjective_lift_iff_forall_nonempty`.

# Verification

Commands run on the candidate tree, all successful:

- `nix fmt`: no changes.
- `nix develop -c lake build`: `Build completed successfully`, zero warnings.
- `nix flake check`: all checks passed (formatting, statix, deadnix,
  gitleaks, shellcheck, actionlint, markers).
- `rg "sorry|axiom "` over `Amalgam/`: no matches.
- `#print axioms` on every closing theorem and witness: only `propext`,
  `Classical.choice`, `Quot.sound` (the `decide` witnesses use all three;
  `injective_lift_iff_forall_subsingleton` and `fiberComp` use none).

An independent audit of `cd721bf7` against this contract checked all 130
library declarations for axioms, searched mathlib for verbatim duplicates of
each Core declaration (none found; `Equiv.fiberCompEquiv` is the fiber form of
`Equiv.subtypeEquivOfSubtype`, restated for its `simps` lemmas), and added the
Status examples for the injective and surjective trivial-overlap criteria and
for the empty fiber over `unreached₂` being a subsingleton, which the README
now names as uniqueness without existence. The candidate `d33ec042` includes
those additions. The working copy is clean after the commit.

# Request to the reviewer

Inspect the declarations above and their hypotheses in the Lean sources, the
README-to-Status map, and the dependency direction. Decide whether M0 is
complete. If accepted, rewrite this file as `READY FOR WORK`, `Turn: worker`,
with the M1 objective from [Section 26](PROPOSAL.md#26-initial-milestones),
and add the built-status paragraph to the proposal's M0 section per
Section 23.

# Proposal acceptance evidence

The founding proposal at `7159fd31` was accepted (SHA-256
`43dc0ab30372cde3f9134073ca68bf507e3fd9b11d5a050991a068c5a4dfbe6c`); R1–R4
closed without remaining corrections. Round-specific details remain in
version history.
