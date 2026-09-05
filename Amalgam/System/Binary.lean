import Amalgam.Core.Reduction
import Amalgam.System.Restriction
import Mathlib.Data.Fin.VecNotation
import Mathlib.Order.Bounds.Basic

/-!
# Binary recovery: compatible pairs of a restriction system are pullbacks

Fix contexts `l`, `r` of a restriction system `S` and a common coarser context `b` that is
greatest among common coarser contexts: `hl : b ≤ l`, `hr : b ≤ r`, and
`hb : ∀ ⦃c⦄, c ≤ l → c ≤ r → c ≤ b`. Together these say `IsGreatest (lowerBounds {l, r}) b`
(`isGreatest_lowerBounds_pair_iff`); no lattice structure and no uniqueness of `b` is assumed.
Under `hb`, agreement at every common coarser context reduces to agreement at `b`
(`compatible_pair_iff`), so the compatible families over `![l, r]` are the compatible pairs
`Function.Pullback (S.res hl) (S.res hr)` of M0 (`binaryEquiv`).

Under this identification the raw family comparison `Hom.mapFamily` of a morphism `φ` is M1's
observed comparison `Function.Pullback.map (φ.naturality hl) (φ.naturality hr)` for the
observations `φ.toFun l`, `φ.toFun b`, `φ.toFun r` (`Hom.binaryEquiv_mapFamily`). The fine-lift
fibers, the attained image, and the observed quotient transport accordingly
(`Hom.fiberMapFamilyBinaryEquiv`, `Hom.mem_range_mapFamily_iff_mem_range_map`,
`Hom.image_range_mapFamily`, `Hom.observedBinaryEquiv`), and
M1's intersection criterion is recovered for families
(`Hom.mem_range_mapFamily_iff_inter_nonempty`, `Hom.bijective_kerLift_mapFamily_iff_forall`).

The observed quotient of a family comparison is written `Quotient (Setoid.ker (φ.mapFamily F))`
with injection `Setoid.kerLift (φ.mapFamily F)`, the M1 construction applied to `φ.mapFamily F`.

## Indexing

Binary families are indexed by `Fin 2` through `![l, r]`, so the two states of a family `x` are
`x 0` and `x 1`, the dependent tuple of a pair is `Fin.cons`, and `Fin.forall_fin_two` and
`match` on `Fin` literals discharge index case analysis. The shared-overlap shape
`L → B ← M → D ← R` is indexed by `Fin 3` through `![L, M, R]` (`compatible_triple_iff`): two
views with no common coarser context impose no condition on each other.
-/

universe u v w

namespace RestrictionSystem

variable {C : Type u} [Preorder C] (S : RestrictionSystem.{u, v} C)

/-! ### Compatible pairs -/

section Pair

/-- The overlap hypotheses `hl`, `hr`, `hb` below say exactly that `b` is the greatest common
coarser context of `l` and `r`. -/
theorem isGreatest_lowerBounds_pair_iff {l r b : C} :
    IsGreatest (lowerBounds {l, r}) b ↔ (b ≤ l ∧ b ≤ r) ∧ ∀ ⦃c⦄, c ≤ l → c ≤ r → c ≤ b := by
  simp only [IsGreatest, upperBounds, mem_lowerBounds, Set.mem_insert_iff, Set.mem_singleton_iff,
    forall_eq_or_imp, forall_eq, Set.mem_ofPred_eq, and_imp]

variable {l r b : C} (hl : b ≤ l) (hr : b ≤ r) (hb : ∀ ⦃c⦄, c ≤ l → c ≤ r → c ≤ b)

include hb in
/-- Agreement at a greatest common coarser context gives agreement at every common coarser
context, by `res_trans`. -/
theorem res_eq_res_of_res_eq_res {u : S.State l} {v : S.State r} (h : S.res hl u = S.res hr v)
    {c : C} (hi : c ≤ l) (hj : c ≤ r) : S.res hi u = S.res hj v :=
  calc S.res hi u = S.res (hb hi hj) (S.res hl u) := (S.res_trans _ _ _).symm
    _ = S.res (hb hi hj) (S.res hr v) := congrArg _ h
    _ = S.res hj v := S.res_trans _ _ _

include hb in
/-- A family over `![l, r]` is compatible exactly when its two states agree at `b`. -/
theorem compatible_pair_iff (x : ∀ i, S.State (![l, r] i)) :
    S.Compatible ![l, r] x ↔ S.res hl (x 0) = S.res hr (x 1) where
  mp h := h (i := 0) (j := 1) hl hr
  mpr h := by
    intro c i j hi hj
    match i, j, hi, hj with
    | 0, 0, _, _ => rfl
    | 0, 1, hi, hj => exact S.res_eq_res_of_res_eq_res hl hr hb h hi hj
    | 1, 0, hi, hj => exact (S.res_eq_res_of_res_eq_res hl hr hb h hj hi).symm
    | 1, 1, _, _ => rfl

/-- Compatible families over `![l, r]` are the compatible pairs of the span
`S.State l → S.State b ← S.State r`. -/
def binaryEquiv : S.CompatibleFamily ![l, r] ≃ Function.Pullback (S.res hl) (S.res hr) where
  toFun x := Function.Pullback.mk (x.1 0) (x.1 1) (x.2 (i := 0) (j := 1) hl hr)
  invFun s :=
    ⟨Fin.cons s.fst (Fin.cons s.snd finZeroElim), (S.compatible_pair_iff hl hr hb _).2 s.comm⟩
  left_inv _ := Subtype.ext (funext (Fin.forall_fin_two.2 ⟨rfl, rfl⟩))
  right_inv _ := rfl

/-- The left view of the pair of a compatible family. -/
@[simp] theorem binaryEquiv_apply_fst (x : S.CompatibleFamily ![l, r]) :
    (S.binaryEquiv hl hr hb x).fst = x.1 0 :=
  rfl

/-- The right view of the pair of a compatible family. -/
@[simp] theorem binaryEquiv_apply_snd (x : S.CompatibleFamily ![l, r]) :
    (S.binaryEquiv hl hr hb x).snd = x.1 1 :=
  rfl

/-- The state at index `0` of the family of a compatible pair. -/
@[simp] theorem binaryEquiv_symm_apply_coe_zero (s : Function.Pullback (S.res hl) (S.res hr)) :
    ((S.binaryEquiv hl hr hb).symm s).1 0 = s.fst :=
  rfl

/-- The state at index `1` of the family of a compatible pair. -/
@[simp] theorem binaryEquiv_symm_apply_coe_one (s : Function.Pullback (S.res hl) (S.res hr)) :
    ((S.binaryEquiv hl hr hb).symm s).1 1 = s.snd :=
  rfl

/-- Round trip: the family of the pair of a compatible family. -/
theorem binaryEquiv_symm_apply_apply (x : S.CompatibleFamily ![l, r]) :
    (S.binaryEquiv hl hr hb).symm (S.binaryEquiv hl hr hb x) = x :=
  (S.binaryEquiv hl hr hb).symm_apply_apply x

/-- Round trip: the pair of the family of a compatible pair. -/
theorem binaryEquiv_apply_symm_apply (s : Function.Pullback (S.res hl) (S.res hr)) :
    S.binaryEquiv hl hr hb ((S.binaryEquiv hl hr hb).symm s) = s :=
  (S.binaryEquiv hl hr hb).apply_symm_apply s

/-! ### The binary comparison is `Function.Pullback.map` -/

namespace Hom

variable {S} {S' : RestrictionSystem.{u, w} C} (φ : S.Hom S')

/-- The raw comparison of binary families is M1's observed comparison
`Function.Pullback.map (φ.naturality hl) (φ.naturality hr)` of the observations `φ.toFun l`,
`φ.toFun b`, `φ.toFun r`, under `binaryEquiv`. -/
theorem binaryEquiv_mapFamily (x : S.CompatibleFamily ![l, r]) :
    S'.binaryEquiv hl hr hb (φ.mapFamily ![l, r] x) =
      Function.Pullback.map (φ.naturality hl) (φ.naturality hr) (S.binaryEquiv hl hr hb x) :=
  rfl

/-- Function-level form of `binaryEquiv_mapFamily`. -/
theorem binaryEquiv_comp_mapFamily :
    S'.binaryEquiv hl hr hb ∘ φ.mapFamily ![l, r] =
      Function.Pullback.map (φ.naturality hl) (φ.naturality hr) ∘ S.binaryEquiv hl hr hb :=
  rfl

/-- Fine-lift fibers of the family comparison over `y` are the fine-lift fibers of M1's
comparison over the pair of `y`. -/
def fiberMapFamilyBinaryEquiv (y : S'.CompatibleFamily ![l, r]) :
    {x // φ.mapFamily ![l, r] x = y} ≃
      {s // Function.Pullback.map (φ.naturality hl) (φ.naturality hr) s =
        S'.binaryEquiv hl hr hb y} :=
  Equiv.fiberCongr (S.binaryEquiv hl hr hb) (S'.binaryEquiv hl hr hb)
    (fun x => (φ.binaryEquiv_mapFamily hl hr hb x).symm) y

/-- `fiberMapFamilyBinaryEquiv` is `binaryEquiv` on underlying fine families. -/
@[simp] theorem fiberMapFamilyBinaryEquiv_apply_coe (y : S'.CompatibleFamily ![l, r])
    (x : {x // φ.mapFamily ![l, r] x = y}) :
    (φ.fiberMapFamilyBinaryEquiv hl hr hb y x : Function.Pullback (S.res hl) (S.res hr)) =
      S.binaryEquiv hl hr hb x :=
  rfl

/-- `fiberMapFamilyBinaryEquiv.symm` is `binaryEquiv.symm` on underlying fine pairs. -/
@[simp] theorem fiberMapFamilyBinaryEquiv_symm_apply_coe (y : S'.CompatibleFamily ![l, r])
    (s : {s // Function.Pullback.map (φ.naturality hl) (φ.naturality hr) s =
      S'.binaryEquiv hl hr hb y}) :
    ((φ.fiberMapFamilyBinaryEquiv hl hr hb y).symm s : S.CompatibleFamily ![l, r]) =
      (S.binaryEquiv hl hr hb).symm s :=
  rfl

/-- A coarse binary family is attained exactly when its pair is attained by M1's comparison. -/
theorem mem_range_mapFamily_iff_mem_range_map (y : S'.CompatibleFamily ![l, r]) :
    y ∈ Set.range (φ.mapFamily ![l, r]) ↔
      S'.binaryEquiv hl hr hb y ∈
        Set.range (Function.Pullback.map (φ.naturality hl) (φ.naturality hr)) := by
  rw [← Function.nonempty_fiber_iff_mem_range, ← Function.nonempty_fiber_iff_mem_range]
  exact (φ.fiberMapFamilyBinaryEquiv hl hr hb y).nonempty_congr

/-- The attained image of the binary family comparison is the attained image of M1's comparison,
as sets under `binaryEquiv`. -/
theorem image_range_mapFamily :
    S'.binaryEquiv hl hr hb '' Set.range (φ.mapFamily ![l, r]) =
      Set.range (Function.Pullback.map (φ.naturality hl) (φ.naturality hr)) := by
  rw [← Set.range_comp, binaryEquiv_comp_mapFamily, Set.range_comp,
    (S.binaryEquiv hl hr hb).range_eq_univ, Set.image_univ]

include hb in
/-- M1's intersection criterion for binary families: a coarse family `y` is attained exactly when
the fine overlap values at `b` reached from fine states at `l` observed as `y.1 0` and from fine
states at `r` observed as `y.1 1` have a common element. -/
theorem mem_range_mapFamily_iff_inter_nonempty (y : S'.CompatibleFamily ![l, r]) :
    y ∈ Set.range (φ.mapFamily ![l, r]) ↔
      (S.res hl '' (φ.toFun l ⁻¹' {y.1 0}) ∩ S.res hr '' (φ.toFun r ⁻¹' {y.1 1})).Nonempty :=
  (φ.mem_range_mapFamily_iff_mem_range_map hl hr hb y).trans
    (Function.Pullback.mem_range_map_iff (φ.naturality hl) (φ.naturality hr) _)

/-! ### The observed quotient -/

/-- The observed quotient of the binary family comparison is M1's observed quotient, by
transporting the kernel relation along `binaryEquiv`. -/
def observedBinaryEquiv :
    Quotient (Setoid.ker (φ.mapFamily ![l, r])) ≃
      Function.Pullback.Observed (φ.naturality hl) (φ.naturality hr) :=
  Quotient.congr (S.binaryEquiv hl hr hb) fun x x' =>
    Setoid.ker_def.trans <|
      ((S'.binaryEquiv hl hr hb).injective.eq_iff (a := φ.mapFamily ![l, r] x)
        (b := φ.mapFamily ![l, r] x')).symm.trans <| by
          rw [binaryEquiv_mapFamily, binaryEquiv_mapFamily]
          exact Setoid.ker_def.symm

/-- `observedBinaryEquiv` on a class is `binaryEquiv` on a representative. -/
@[simp] theorem observedBinaryEquiv_mk (x : S.CompatibleFamily ![l, r]) :
    φ.observedBinaryEquiv hl hr hb (Quotient.mk _ x) =
      Quotient.mk _ (S.binaryEquiv hl hr hb x) :=
  rfl

/-- `observedBinaryEquiv.symm` on a class is `binaryEquiv.symm` on a representative. -/
@[simp] theorem observedBinaryEquiv_symm_mk (s : Function.Pullback (S.res hl) (S.res hr)) :
    (φ.observedBinaryEquiv hl hr hb).symm (Quotient.mk _ s) =
      Quotient.mk _ ((S.binaryEquiv hl hr hb).symm s) :=
  rfl

/-- Round trip: `observedBinaryEquiv.symm` after `observedBinaryEquiv`. -/
theorem observedBinaryEquiv_symm_apply_apply (q : Quotient (Setoid.ker (φ.mapFamily ![l, r]))) :
    (φ.observedBinaryEquiv hl hr hb).symm (φ.observedBinaryEquiv hl hr hb q) = q :=
  (φ.observedBinaryEquiv hl hr hb).symm_apply_apply q

/-- Round trip: `observedBinaryEquiv` after `observedBinaryEquiv.symm`. -/
theorem observedBinaryEquiv_apply_symm_apply
    (t : Function.Pullback.Observed (φ.naturality hl) (φ.naturality hr)) :
    φ.observedBinaryEquiv hl hr hb ((φ.observedBinaryEquiv hl hr hb).symm t) = t :=
  (φ.observedBinaryEquiv hl hr hb).apply_symm_apply t

/-- The commuting square of the quotient injections: M1's `observedMap` after
`observedBinaryEquiv` is `binaryEquiv` after the family injection `Setoid.kerLift`. -/
theorem observedMap_observedBinaryEquiv (q : Quotient (Setoid.ker (φ.mapFamily ![l, r]))) :
    Function.Pullback.observedMap (φ.naturality hl) (φ.naturality hr)
        (φ.observedBinaryEquiv hl hr hb q) =
      S'.binaryEquiv hl hr hb (Setoid.kerLift (φ.mapFamily ![l, r]) q) :=
  Quotient.inductionOn q fun _ => rfl

/-- Function-level form of `observedMap_observedBinaryEquiv`. -/
theorem observedMap_comp_observedBinaryEquiv :
    Function.Pullback.observedMap (φ.naturality hl) (φ.naturality hr) ∘
        φ.observedBinaryEquiv hl hr hb =
      S'.binaryEquiv hl hr hb ∘ Setoid.kerLift (φ.mapFamily ![l, r]) :=
  funext (φ.observedMap_observedBinaryEquiv hl hr hb)

/-- The inverse square: the family injection after `observedBinaryEquiv.symm` is
`binaryEquiv.symm` after M1's `observedMap`. -/
theorem kerLift_observedBinaryEquiv_symm
    (t : Function.Pullback.Observed (φ.naturality hl) (φ.naturality hr)) :
    Setoid.kerLift (φ.mapFamily ![l, r]) ((φ.observedBinaryEquiv hl hr hb).symm t) =
      (S'.binaryEquiv hl hr hb).symm
        (Function.Pullback.observedMap (φ.naturality hl) (φ.naturality hr) t) :=
  (S'.binaryEquiv hl hr hb).eq_symm_apply.2 <| by
    rw [← observedMap_observedBinaryEquiv, Equiv.apply_symm_apply]

include hb in
/-- The family injection is surjective exactly when M1's `observedMap` is. -/
theorem surjective_kerLift_mapFamily_iff :
    Function.Surjective (Setoid.kerLift (φ.mapFamily ![l, r])) ↔
      Function.Surjective (Function.Pullback.observedMap (φ.naturality hl) (φ.naturality hr)) := by
  rw [← (S'.binaryEquiv hl hr hb).comp_surjective, ← observedMap_comp_observedBinaryEquiv,
    (φ.observedBinaryEquiv hl hr hb).surjective_comp]

include hb in
/-- The family injection is bijective exactly when M1's `observedMap` is. -/
theorem bijective_kerLift_mapFamily_iff :
    Function.Bijective (Setoid.kerLift (φ.mapFamily ![l, r])) ↔
      Function.Bijective (Function.Pullback.observedMap (φ.naturality hl) (φ.naturality hr)) := by
  rw [← (S'.binaryEquiv hl hr hb).comp_bijective, ← observedMap_comp_observedBinaryEquiv,
    (φ.observedBinaryEquiv hl hr hb).bijective_comp]

include hb in
/-- Exact lifting criterion for binary families: the family injection is bijective exactly when
the intersection criterion holds at every coarse compatible family. -/
theorem bijective_kerLift_mapFamily_iff_forall :
    Function.Bijective (Setoid.kerLift (φ.mapFamily ![l, r])) ↔
      ∀ y : S'.CompatibleFamily ![l, r],
        (S.res hl '' (φ.toFun l ⁻¹' {y.1 0}) ∩ S.res hr '' (φ.toFun r ⁻¹' {y.1 1})).Nonempty := by
  rw [φ.bijective_kerLift_mapFamily_iff hl hr hb, Function.Pullback.bijective_observedMap_iff]
  exact (S'.binaryEquiv hl hr hb).forall_congr_right.symm

end Hom

end Pair

/-! ### The shared-overlap shape -/

section Triple

variable {L M R B D : C} (hBL : B ≤ L) (hBM : B ≤ M) (hDM : D ≤ M) (hDR : D ≤ R)
  (hB : ∀ ⦃c⦄, c ≤ L → c ≤ M → c ≤ B) (hD : ∀ ⦃c⦄, c ≤ M → c ≤ R → c ≤ D)
  (hLR : ∀ ⦃c⦄, c ≤ L → c ≤ R → False)

include hB hD hLR in
/-- On the shape `L → B ← M → D ← R`, with `B` greatest among common coarser contexts of `L`, `M`,
`D` greatest among those of `M`, `R`, and no common coarser context of `L`, `R`, a family over
`![L, M, R]` is compatible exactly when it satisfies the two overlap equations. -/
theorem compatible_triple_iff (x : ∀ i, S.State (![L, M, R] i)) :
    S.Compatible ![L, M, R] x ↔
      S.res hBL (x 0) = S.res hBM (x 1) ∧ S.res hDM (x 1) = S.res hDR (x 2) where
  mp h := ⟨h (i := 0) (j := 1) hBL hBM, h (i := 1) (j := 2) hDM hDR⟩
  mpr h := by
    intro c i j hi hj
    match i, j, hi, hj with
    | 0, 0, _, _ => rfl
    | 0, 1, hi, hj => exact S.res_eq_res_of_res_eq_res hBL hBM hB h.1 hi hj
    | 0, 2, hi, hj => exact (hLR hi hj).elim
    | 1, 0, hi, hj => exact (S.res_eq_res_of_res_eq_res hBL hBM hB h.1 hj hi).symm
    | 1, 1, _, _ => rfl
    | 1, 2, hi, hj => exact S.res_eq_res_of_res_eq_res hDM hDR hD h.2 hi hj
    | 2, 0, hi, hj => exact (hLR hj hi).elim
    | 2, 1, hi, hj => exact (S.res_eq_res_of_res_eq_res hDM hDR hD h.2 hj hi).symm
    | 2, 2, _, _ => rfl

end Triple

end RestrictionSystem
