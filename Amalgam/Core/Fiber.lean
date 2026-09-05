import Mathlib.Data.Set.Operations
import Mathlib.Logic.Equiv.Sum
import Mathlib.Logic.Function.Basic
import Mathlib.Logic.IsEmpty.Basic
import Mathlib.Logic.Unique

/-!
# Fibers of a map

The fiber of `f : X → Y` over `y : Y` is the subtype `{x // f x = y}`, the convention of
`Equiv.sigmaFiberEquiv`. No wrapper type is introduced; extensionality of fiber elements is
`Subtype.ext`.

This file provides, for a single map between arbitrary types:

* the decomposition `Equiv.sigmaFiberEquiv` of the source as the dependent sum of the fibers,
  with the computation lemma `Equiv.sigmaFiberEquiv_mk`;
* the fiber over `y` is nonempty iff `y` is reached, empty iff `y` is missed;
* pointwise criteria: `Function.subsingleton_fiber_iff`, and the global fiber
  characterizations `Function.injective_iff_subsingleton_fiber`,
  `Function.surjective_iff_nonempty_fiber`, `Function.bijective_iff_nonempty_unique_fiber`,
  `Function.bijective_iff_nonempty_and_subsingleton_fiber`;
* transport under equivalences of source and target, `Equiv.fiberCongr`;
* fibers of composites, `Equiv.fiberComp`, `Equiv.fiberCompEquiv`, `Equiv.fiberEquivComp`;
* the identification `Equiv.fiberEquivPreimage` with the set preimage `f ⁻¹' {y}`.

Empty types and empty fibers are allowed throughout. Uniqueness is `Subsingleton`, existence is
`Nonempty`, and unique existence is `Nonempty (Unique _)`, equivalently `∃! x, f x = y`.

## Mathlib reuse

The following statements already exist in mathlib in exactly the form needed and are not
restated: `nonempty_subtype` (`Nonempty {x // f x = y} ↔ ∃ x, f x = y`), `isEmpty_subtype`
(`IsEmpty {x // f x = y} ↔ ∀ x, ¬f x = y`), `unique_subtype_iff_existsUnique`
(`Nonempty (Unique {x // f x = y}) ↔ ∃! x, f x = y`), `Function.bijective_iff_existsUnique`,
and `Equiv.sigmaFiberEquiv` with its `simps` lemmas `Equiv.sigmaFiberEquiv_apply`,
`Equiv.sigmaFiberEquiv_symm_apply_fst`, and `Equiv.sigmaFiberEquiv_symm_apply_snd_coe`. Base
change along a pullback is not treated here.
-/

universe u v w u' v'

variable {X : Type u} {Y : Type v} {Z : Type w} {X' : Type u'} {Y' : Type v'}

namespace Equiv

/-! ### Source decomposition -/

/-- `Equiv.sigmaFiberEquiv` sends the point `x` of the fiber over `y` to `x`. -/
theorem sigmaFiberEquiv_mk (f : X → Y) (y : Y) (x : {x // f x = y}) :
    sigmaFiberEquiv f ⟨y, x⟩ = x :=
  rfl

end Equiv

namespace Function

/-! ### Reached and missed values -/

/-- The fiber over `y` is nonempty iff `y` is in the range. -/
theorem nonempty_fiber_iff_mem_range (f : X → Y) (y : Y) :
    Nonempty {x // f x = y} ↔ y ∈ Set.range f :=
  nonempty_subtype

/-- The fiber over `y` is empty iff `y` is not in the range. -/
theorem isEmpty_fiber_iff_notMem_range (f : X → Y) (y : Y) :
    IsEmpty {x // f x = y} ↔ y ∉ Set.range f := by
  rw [← not_nonempty_iff, nonempty_fiber_iff_mem_range]

/-! ### Pointwise and global criteria -/

/-- The fiber over `y` is a subsingleton iff any two preimages of `y` coincide. -/
theorem subsingleton_fiber_iff (f : X → Y) (y : Y) :
    Subsingleton {x // f x = y} ↔ ∀ x x', f x = y → f x' = y → x = x' :=
  ⟨fun h x x' hx hx' => congrArg Subtype.val (h.elim ⟨x, hx⟩ ⟨x', hx'⟩),
    fun h => ⟨fun a b => Subtype.ext (h a b a.2 b.2)⟩⟩

/-- `f` is injective iff every fiber is a subsingleton. -/
theorem injective_iff_subsingleton_fiber (f : X → Y) :
    Injective f ↔ ∀ y, Subsingleton {x // f x = y} :=
  ⟨fun hf _ => ⟨fun a b => Subtype.ext (hf (a.2.trans b.2.symm))⟩,
    fun h a b hab => congrArg Subtype.val ((h (f b)).elim ⟨a, hab⟩ ⟨b, rfl⟩)⟩

/-- `f` is surjective iff every fiber is nonempty. -/
theorem surjective_iff_nonempty_fiber (f : X → Y) :
    Surjective f ↔ ∀ y, Nonempty {x // f x = y} :=
  forall_congr' fun _ => nonempty_subtype.symm

/-- `f` is bijective iff every fiber has a unique element. -/
theorem bijective_iff_nonempty_unique_fiber (f : X → Y) :
    Bijective f ↔ ∀ y, Nonempty (Unique {x // f x = y}) :=
  (bijective_iff_existsUnique f).trans <|
    forall_congr' fun y => (unique_subtype_iff_existsUnique fun x => f x = y).symm

/-- `f` is bijective iff every fiber is nonempty and a subsingleton. -/
theorem bijective_iff_nonempty_and_subsingleton_fiber (f : X → Y) :
    Bijective f ↔ ∀ y, Nonempty {x // f x = y} ∧ Subsingleton {x // f x = y} :=
  ⟨fun hf y => ((surjective_iff_nonempty_fiber f).1 hf.2 y).elim fun x =>
      ⟨⟨x⟩, (injective_iff_subsingleton_fiber f).1 hf.1 y⟩,
    fun h => ⟨(injective_iff_subsingleton_fiber f).2 fun y => (h y).2,
      (surjective_iff_nonempty_fiber f).2 fun y => (h y).1⟩⟩

end Function

namespace Equiv

/-! ### Transport under equivalences -/

/-- Fibers of maps intertwined by equivalences of source and target are equivalent: the fiber
of `f` over `y` matches the fiber of `f'` over `e₂ y`. -/
@[simps]
def fiberCongr {f : X → Y} {f' : X' → Y'} (e₁ : X ≃ X') (e₂ : Y ≃ Y')
    (h : ∀ x, f' (e₁ x) = e₂ (f x)) (y : Y) : {x // f x = y} ≃ {x' // f' x' = e₂ y} where
  toFun x := ⟨e₁ x, by rw [h, x.2]⟩
  invFun x' := ⟨e₁.symm x', e₂.injective <| by rw [← h, apply_symm_apply, x'.2]⟩
  left_inv x := Subtype.ext (e₁.symm_apply_apply x)
  right_inv x' := Subtype.ext (e₁.apply_symm_apply x')

/-! ### Composition -/

/-- The fiber of `g ∘ f` over `z` is the sum over the fiber of `g` over `z` of the fibers of
`f`. -/
@[simps]
def fiberComp (g : Y → Z) (f : X → Y) (z : Z) :
    {x // (g ∘ f) x = z} ≃ Σ y : {y // g y = z}, {x // f x = y.1} where
  toFun x := ⟨⟨f x.1, x.2⟩, ⟨x.1, rfl⟩⟩
  invFun p := ⟨p.2.1, (congrArg g p.2.2).trans p.1.2⟩
  left_inv _ := rfl
  right_inv := by rintro ⟨⟨_, _⟩, ⟨_, hx⟩⟩; cases hx; rfl

/-- Precomposition with an equivalence of the source preserves fibers. Compare
`Equiv.subtypeEquivOfSubtype`. -/
@[simps]
def fiberCompEquiv (f : X → Y) (e : X' ≃ X) (y : Y) : {x' // f (e x') = y} ≃ {x // f x = y} where
  toFun x' := ⟨e x', x'.2⟩
  invFun x := ⟨e.symm x, by rw [apply_symm_apply, x.2]⟩
  left_inv x' := Subtype.ext (e.symm_apply_apply x')
  right_inv x := Subtype.ext (e.apply_symm_apply x)

/-- Postcomposition with an equivalence of the target transports fibers along its inverse. -/
@[simps]
def fiberEquivComp (e : Y ≃ Y') (f : X → Y) (y' : Y') :
    {x // e (f x) = y'} ≃ {x // f x = e.symm y'} where
  toFun x := ⟨x, (e.symm_apply_apply _).symm.trans (congrArg e.symm x.2)⟩
  invFun x := ⟨x, (congrArg e x.2).trans (e.apply_symm_apply y')⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-! ### Set preimage -/

/-- The fiber over `y` is the preimage of `{y}`; the underlying elements agree definitionally. -/
@[simps]
def fiberEquivPreimage (f : X → Y) (y : Y) : {x // f x = y} ≃ f ⁻¹' {y} where
  toFun x := ⟨x, x.2⟩
  invFun x := ⟨x, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

end Equiv
