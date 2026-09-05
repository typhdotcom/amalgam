State: READY FOR REVIEW
Turn: reviewer
Candidate: 09ec3871; accepted M1 candidate d7f2ed62; accepted M0 candidate 6a33636f

# Submission

M2 — The comparison for finite families — is implemented at `09ec3871`.
The restriction interface, compatible families, declared family restrictions
with their laws, presentation invariance and redundancy, the family raw
comparison with its fibers, observed quotient, attainable image and
naturality at all four levels, the binary recovery of M0/M1, and both finite
calibration cases are compiled. No `sorry`, no project axiom; classical
choice appears only where named below. M0 and M1 modules are unchanged. No
M3 shape or datum was selected and no counting hierarchy was introduced.

# Accepted foundation

[PROPOSAL.md](PROPOSAL.md), Sections 11–12 and 26, owns this contract.

- M0 (`6a33636f`) and M1 (`d7f2ed62`) are reused: fibers as
  `{x // f x = y}`, `Function.Pullback`, `Function.Pullback.map`, `Observed`,
  `mem_range_map_iff`; quotients through `Setoid.ker`, `Setoid.kerLift`,
  `Setoid.quotientKerEquivRange`.
- Carriers and index types are arbitrary, possibly empty; nothing in
  `Amalgam/System/` assumes finiteness, decidability, or surjectivity.
- Raw fibers are fine lifts; quotient fibers are observed classes; they share
  inhabitedness and the quotient discards multiplicity.
- Naturality gives image inclusion only; equality and surjectivity are never
  claimed and are refuted by the second calibration case.
- Toolchain, license, tasks, and Status discipline unchanged.

# Datum and construction (as built)

`Amalgam/System/Restriction.lean`. `RestrictionSystem C` over `[Preorder C]`:
`State : C → Type`, `res : c ≤ d → State d → State c` (the order reads `c ≤ d`
as “`c` is coarser than `d`”), laws `res_refl`, `res_trans`.
`Compatible F x := ∀ ⦃c i j⦄ (hi : c ≤ F i) (hj : c ≤ F j), res hi (x i) = res hj (x j)`; `CompatibleFamily F` its subtype. A declared operation is
`FamilyMap F E` (`index : κ → ι`, `le : ∀ k, E k ≤ F (index k)`), with `id`,
`comp`; `restrict m x := fun k => res (m.le k) (x (m.index k))` acts by
actual restriction; `restrict_id` (by `res_refl`), `restrict_comp` (by
`res_trans`). `Hom S S'` is an observation per context with `naturality`;
`Hom.mapFamily` is `k_F`; `restrict_mapFamily` its naturality.

# Closing evidence

## M2.1 — Compatible families and their restrictions

`Amalgam/System/Presentation.lean` (namespace `RestrictionSystem`):

- Relabeling: `relabel (e : κ ≃ ι) : CompatibleFamily F ≃ CompatibleFamily (F ∘ e)` with `relabel_apply`, `relabel_symm_apply(_coe)`, round trips
  `relabel_symm_relabel`, `relabel_relabel_symm`, and `restrict_relabel`,
  `relabel_restrict`, `relabel_relabel`, `relabel_refl_apply`. Consumes
  `res_refl`.
- Redundancy (general form): for `σ : κ → ι`, `h : ∀ k, G k ≤ F (σ k)`,
  `redundancyEquiv σ h : CompatibleFamily (Sum.elim F G) ≃ CompatibleFamily F`
  forgets forwards (`FamilyMap.inl`) and extends backwards by
  `res (h k) (x (σ k))` (`FamilyMap.extend`, `Compatible.extend`), with
  `redundancyEquiv_apply`, `redundancyEquiv_symm_apply`, round trips
  `forget_extend`, `extend_forget`, and `bijective_restrict_inl`. Consumes
  `res_refl`, `res_trans`, and `Compatible` at the added context. Cases:
  `addViewEquiv` (one added view) and `duplicateEquiv` with
  `bijective_restrict_inl_duplicate` (duplicate occurrence).
- General reverse-operation form: `restrict_endo`, `restrict_restrict`,
  `restrictEquiv`, `bijective_restrict`.
- Fibers of family restrictions: `restrictFiberEquiv m z : {x // restrict m x = z} ≃ {x // ∀ k, res (m.le k) (x.1 (m.index k)) = z.1 k}` (extension
  choices), `subsingleton_fiber_restrict`, `subsingleton_fiber_restrict_inl`.
- Shapes: `compatible_fin_two_iff` (binary family); `uniqueOfIsEmpty` (empty
  family); the shared-overlap shape is `![L, M, R]` (see `compatible_triple_iff`
  below).

## M2.2 — Comparison, fibers, quotients, and naturality

`Amalgam/System/Comparison.lean` (namespace `RestrictionSystem.Hom`, for
`φ : S.Hom S'`):

- Raw fibers: `fiberMapFamilyEquiv y : {x // mapFamily F x = y} ≃ {x : ∀ i, State (F i) // Compatible F x ∧ ∀ i, φ.toFun (F i) (x i) = y.1 i}`;
  `mem_range_mapFamily_iff` (simultaneous fine lift); existence and
  uniqueness separately: `nonempty_fiber_mapFamily_iff`,
  `isEmpty_fiber_mapFamily_iff`, `subsingleton_fiber_mapFamily_iff`,
  `nonempty_unique_fiber_mapFamily_iff`; `mapFamily_eq_iff`,
  `mapFamily_eq_mapFamily_iff`.
- Quotient: `observedFamily F := Quotient (Setoid.ker (mapFamily F))`,
  `observed_rel_family_iff` (agreement of all observed components),
  `observed_rel_family_iff_mapFamily_eq`, `observedFamily_mk_eq_iff`;
  `observedMapFamily := Setoid.kerLift _` with `observedMapFamily_mk`,
  `observedMapFamily_comp_mk`, `observedMapFamily_injective`,
  `range_observedMapFamily`; `image F := Set.range (mapFamily F)` (`I_F`),
  `mem_image_iff`, `image_eq_range_observedMapFamily`;
  `observedFamilyEquivImage : observedFamily F ≃ image F` with computation on
  `Quotient.mk` and round trips `observedFamilyEquivImage_symm_apply_apply`,
  `observedFamilyEquivImage_apply_symm_apply`.
- `subsingleton_fiber_observedMapFamily` and, separately,
  `nonempty_fiber_mapFamily_iff_nonempty_fiber_observedMapFamily`.
- Naturality along `m : FamilyMap F E`: raw square `restrict_mapFamily`,
  `restrict_comp_mapFamily`; quotient level `restrictObserved m : observedFamily F → observedFamily E` defined on classes
  (`ker_mapFamily_restrict` is the well-definedness), `restrictObserved_mk`,
  square `observedMapFamily_restrictObserved`,
  `observedMapFamily_comp_restrictObserved`; image level
  `mapsTo_restrict_image`, `image_restrict_subset` (this is
  `restrict_(F,E)(I_F) ⊆ I_E`; no equality or surjectivity claimed),
  `restrictImage m : image F → image E` with squares
  `restrictImage_observedFamilyEquivImage`,
  `restrictImage_comp_observedFamilyEquivImage`; identity and composition at
  every level: `restrictObserved_id`, `restrictObserved_comp`,
  `restrictImage_id`, `restrictImage_comp`.
- Fiber tracking: `fiberRestrict m y : {x // mapFamily F x = y} → {x' // mapFamily E x' = restrict m y}` acting by `restrict m` on the same
  states (`coe_fiberRestrict`, `fiberRestrict_id_coe`, `fiberRestrict_comp_coe`).

## M2.3 — Binary recovery and two finite calibration cases

`Amalgam/System/Binary.lean`, for `hl : b ≤ l`, `hr : b ≤ r`, and
`hb : ∀ ⦃c⦄, c ≤ l → c ≤ r → c ≤ b` (b is a greatest common coarser context;
no lattice assumed):

- `compatible_pair_iff`, `binaryEquiv : CompatibleFamily ![l, r] ≃ Function.Pullback (res hl) (res hr)` with round trips
  `binaryEquiv_symm_apply_apply`, `binaryEquiv_apply_symm_apply`;
  `isGreatest_lowerBounds_pair_iff`, `res_eq_res_of_res_eq_res`.
- `binaryEquiv_mapFamily`, `binaryEquiv_comp_mapFamily`: the family raw
  comparison is `Function.Pullback.map (φ.naturality hl) (φ.naturality hr)`
  under `binaryEquiv`.
- Transport: `fiberMapFamilyBinaryEquiv` (fine-lift fibers),
  `mem_range_mapFamily_iff_mem_range_map`, `image_range_mapFamily` (attained
  image), `observedBinaryEquiv : observedFamily ![l, r] ≃ Observed …` with
  `observedMap_observedBinaryEquiv`, `observedMap_comp_observedBinaryEquiv`,
  `kerLift_observedBinaryEquiv_symm`, and round trips
  `observedBinaryEquiv_symm_apply_apply`, `observedBinaryEquiv_apply_symm_apply`; M1's criterion recovered:
  `mem_range_mapFamily_iff_inter_nonempty`, `surjective_kerLift_mapFamily_iff`,
  `bijective_kerLift_mapFamily_iff`, `bijective_kerLift_mapFamily_iff_forall`.
- `compatible_triple_iff` for `![L, M, R]` under `B` greatest common coarser
  of `L, M`, `D` of `M, R`, and every common coarser context of `L, R` lying
  below `M` (weaker than “no common coarser context”, which the zigzag model
  satisfies and from which `le_M_of_le_L_of_le_R` derives the hypothesis).

`Amalgam/Models/Span.lean` (case 1): preorder `Context` with `B_le_L`,
`B_le_R`, `le_B_of_le_L_of_le_R`; `fine` (states `Bool` at `L`, `Unit`
elsewhere), `coarse` (all `Unit`), `φ : fine.Hom coarse`; `LR := ![L, R]`;
`uniqueCoarseFamily`, `y₀`; `x₀ ≠ x₁` (`x₀_ne_x₁`), `eq_x₀_or_eq_x₁`,
`mapFamily_x₀`, `mapFamily_x₁`, `mapFamily_eq_y₀`; raw fiber
`fiberEquiv : {x // φ.mapFamily LR x = y₀} ≃ Bool` with
`fiberEquiv_symm_apply_apply`, `fiberEquiv_apply_symm_apply`; quotient fiber
`nonempty_observedFiber`, `subsingleton_observedFiber`, `uniqueObservedFiber`;
`observed_x₀_eq_observed_x₁`, `uniqueObservedFamily` (exactly one observed
class); pullback agreement `map_binaryEquiv_x₀_eq`,
`y₀_mem_image_of_inter_nonempty`. No counting package.

`Amalgam/Models/Zigzag.lean` (case 2, Section 12): preorder `Context` with
`B_le_L`, `B_le_M`, `D_le_M`, `D_le_R`, `le_B_of_le_L_of_le_M`,
`le_D_of_le_M_of_le_R`, `not_le_L_of_le_R`, `le_M_of_le_L_of_le_R`; `sys lb mb md rd` with states
`Unit` at `L, M, R` and `Bool` at `B, D`, restriction values in the arrow order
`L→B, M→B, M→D, R→D`; `sysA = sys false false false true`,
`sysB = sys false true false false`; `coarse` (all `Unit`,
`uniqueCoarseFamily`); `φA`, `φB` with `surjective_φA`, `surjective_φB`;
declared families `LM`, `MR`, `LMR` and operations `toLM`, `toMR`;
`compatible_LM_iff`, `compatible_MR_iff`, `compatible_LMR_iff`;
`nonempty_LM_A`, `isEmpty_MR_A`, `isEmpty_LMR_A`, `isEmpty_LM_B`,
`nonempty_MR_B`, `isEmpty_LMR_B`; images `image_LM_A = univ`,
`image_MR_A = ∅`, `image_LMR_A = ∅`, `image_LM_B = ∅`, `image_MR_B = univ`,
`image_LMR_B = ∅`; strict inclusion `ssubset_restrict_image_LMR_A`,
`ssubset_restrict_image_LMR_B`, `not_surjective_restrictImage_A`,
`not_surjective_restrictImage_B`; `image_LMR_eq` while `image_LM_ne`,
`image_MR_ne`. No smallest-shape claim; no M3 datum refuted.

## Root exports, README, Status

`Amalgam.lean` imports the twelve modules. README gained "Restriction systems
and compatible families" with the subsection "Two calibration cases";
`Amalgam/Status.lean` mirrors every sentence under the same headings at
independent universes for generic claims and on the two models for the
cases. Dependency direction: `System` imports `Core` and mathlib; `Models`
import `System`; only the root imports `Status`.

# Verification

- `nix fmt`: no changes. `nix develop -c lake build`: success, zero
  warnings. `nix flake check`: all checks passed. `rg sorry Amalgam`: none.
- Axioms: a Lean script collected the axioms of every constant
  of the six M2 modules (338 constants including generated projections):
  119 use none, 64 `propext`, 65 `Quot.sound`, 77 `propext, Quot.sound`,
  13 `propext, Classical.choice, Quot.sound`. Nothing else appears; no
  `sorryAx`. The choice users are `observedFamilyEquivImage` and its five
  laws (`Setoid.quotientKerEquivRange`), `restrictImage_observedFamilyEquivImage`
  and its function-level form, `kerLift_observedBinaryEquiv_symm`,
  `image_range_mapFamily`, and the four set-level Zigzag statements
  `ssubset_restrict_image_LMR_A/B`, `image_LM_ne`, `image_MR_ne`. Every
  criterion, naturality, and fiber iff is choice-free.

An independent audit of `a20bb87b` against this contract passed every
drawer. Its additions are in `09ec3871`: `uniqueObservedFamily` in the span
model, the two round-trip laws of `observedBinaryEquiv`, and docstring
corrections in `Binary.lean` and `Presentation.lean`; the orchestrator added
the matching Status examples. The audit also proved that the third hypothesis
of `compatible_triple_iff` can be weakened to “every common coarser context of
`L`, `R` lies below `M`” and exhibited a counterexample showing some such
hypothesis is necessary; the weaker statement is now the library theorem, with
the zigzag model discharging it through `le_M_of_le_L_of_le_R`. Two name collisions between the concurrently
written modules (`Hom.fiberRestrict`, `Hom.mem_range_mapFamily_iff`) were
resolved before the witnesses were built: one definition kept in
`Comparison.lean`, the binary transport lemma renamed to
`mem_range_mapFamily_iff_mem_range_map`. The working copy is clean after the
commit.

# Request to the reviewer

Judge the whole family construction: the quotient relation, the four-level
naturality and the inclusion `image_restrict_subset`, the binary transport
statements, and both calibration cases on the production path, together
with the cumulative M0–M1 evidence. Decide whether M2 is complete. If
accepted, rewrite this file as `READY FOR WORK`, `Turn: worker`, with the M3
objective, and add the M2 built-status paragraph to the proposal per
Section 23.

# Prior acceptance evidence

M1 was accepted at `d7f2ed62` (submission `5caccd00`); M0 at `6a33636f`;
the founding proposal at `7159fd31`. Details remain in version history.
