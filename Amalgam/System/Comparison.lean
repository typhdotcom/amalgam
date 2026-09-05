import Amalgam.Core.Reduction
import Amalgam.System.Restriction
import Mathlib.Data.Setoid.Basic
import Mathlib.Logic.Equiv.Set

/-!
# The family comparison, its fibers, quotient, image, and naturality

Fix a morphism `φ : S.Hom S'` of restriction systems over the same preorder of contexts. For
every family `F : ι → C` the raw comparison `φ.mapFamily F : S.CompatibleFamily F →
S'.CompatibleFamily F` (`k_F`) observes each component. This file studies its fibers, the
observed quotient, the attainable image, and their behavior under declared family restrictions.

## Main results

* `fiberMapFamilyEquiv`, `mem_range_mapFamily_iff`: the fiber of `k_F` over a coarse family `y`
  is the type of fine assignments that are compatible and observed componentwise as `y`, so `y`
  is attained exactly when such a simultaneous fine lift exists. `nonempty_fiber_mapFamily_iff`,
  `isEmpty_fiber_mapFamily_iff`, `subsingleton_fiber_mapFamily_iff`,
  `nonempty_unique_fiber_mapFamily_iff` separate existence from uniqueness of fine lifts.
* `observedFamily`, `observedMapFamily`: the quotient `Q_F` of fine families by observed
  equality, `Setoid.ker k_F`, and the induced injection `k_bar_F`. `observed_rel_family_iff`
  states the relation as agreement of all observed components, `observedMapFamily_mk` is the
  factorization law, `observedMapFamily_injective` and `range_observedMapFamily` give
  injectivity and equality of images.
* `image`, `mem_image_iff`, `observedFamilyEquivImage`: the attainable image `I_F` with its
  membership criterion and its identification with `Q_F`, with computation law on classes and
  both round trips.
* `subsingleton_fiber_observedMapFamily`,
  `nonempty_fiber_mapFamily_iff_nonempty_fiber_observedMapFamily`: quotient fibers are
  subsingletons; raw and quotient fibers share inhabitedness, so the quotient preserves
  existence of a fine lift while discarding its multiplicity.
* Naturality along a declared restriction `m : FamilyMap F E`: `restrict_comp_mapFamily` on
  raw families, `restrictObserved` with `observedMapFamily_restrictObserved` on observed
  classes, `restrictImage` with `restrictImage_observedFamilyEquivImage` on attainable images,
  and the identity and composition laws `restrictObserved_id`, `restrictObserved_comp`,
  `restrictImage_id`, `restrictImage_comp`. `restrictObserved` is well defined on observed
  classes by `ker_mapFamily_restrict`, not by choosing fine representatives.
* `image_restrict_subset`: `restrict_(F,E)(I_F) ⊆ I_E`. Naturality gives inclusion only;
  equality or surjectivity of restricted images is not claimed.
* `fiberRestrict`: restriction sends the raw fiber over `y` into the raw fiber over
  `S'.restrict m y`, acting on the same supplied local states.

## Conventions

No finiteness, decidability, or surjectivity hypothesis enters; index types and state types may
be empty. The criterion, quotient, and naturality statements use no choice;
`observedFamilyEquivImage` is `Setoid.quotientKerEquivRange` and uses classical choice.
-/

universe u v w

namespace RestrictionSystem.Hom

variable {C : Type u} [Preorder C] {S : RestrictionSystem.{u, v} C}
  {S' : RestrictionSystem.{u, w} C} (φ : S.Hom S') {ι : Type*} {κ : Type*} {μ : Type*}
  {F : ι → C} {E : κ → C} {D : μ → C}

/-! ### Fibers of the raw comparison -/

/-- A fine family lies over `y` exactly when every component is observed as the corresponding
component of `y`. -/
theorem mapFamily_eq_iff (x : S.CompatibleFamily F) (y : S'.CompatibleFamily F) :
    φ.mapFamily F x = y ↔ ∀ i, φ.toFun (F i) (x.1 i) = y.1 i :=
  Subtype.ext_iff.trans funext_iff

/-- Two fine families have the same observed family exactly when all observed components
agree. -/
theorem mapFamily_eq_mapFamily_iff (x x' : S.CompatibleFamily F) :
    φ.mapFamily F x = φ.mapFamily F x' ↔ ∀ i, φ.toFun (F i) (x.1 i) = φ.toFun (F i) (x'.1 i) :=
  φ.mapFamily_eq_iff x _

section Fiber

variable (y : S'.CompatibleFamily F)

/-- The fiber of the raw comparison over `y` is the type of fine assignments satisfying
compatibility and every component observation equation. -/
def fiberMapFamilyEquiv :
    {x // φ.mapFamily F x = y} ≃
      {x : ∀ i, S.State (F i) // S.Compatible F x ∧ ∀ i, φ.toFun (F i) (x i) = y.1 i} where
  toFun x := ⟨x.1.1, x.1.2, (φ.mapFamily_eq_iff x.1 y).1 x.2⟩
  invFun x := ⟨⟨x.1, x.2.1⟩, (φ.mapFamily_eq_iff _ y).2 x.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- `fiberMapFamilyEquiv` is the identity on underlying assignments. -/
@[simp] theorem fiberMapFamilyEquiv_apply_coe (x : {x // φ.mapFamily F x = y}) :
    (φ.fiberMapFamilyEquiv y x : ∀ i, S.State (F i)) = x.1.1 :=
  rfl

/-- `fiberMapFamilyEquiv.symm` is the identity on underlying assignments. -/
@[simp] theorem fiberMapFamilyEquiv_symm_apply_coe
    (x : {x : ∀ i, S.State (F i) // S.Compatible F x ∧ ∀ i, φ.toFun (F i) (x i) = y.1 i}) :
    (((φ.fiberMapFamilyEquiv y).symm x : S.CompatibleFamily F) : ∀ i, S.State (F i)) = x.1 :=
  rfl

/-- The image criterion: a coarse compatible family is attained exactly when some compatible
fine assignment is observed componentwise as it, a simultaneous fine lift. -/
theorem mem_range_mapFamily_iff :
    y ∈ Set.range (φ.mapFamily F) ↔
      ∃ x : ∀ i, S.State (F i), S.Compatible F x ∧ ∀ i, φ.toFun (F i) (x i) = y.1 i :=
  ⟨fun ⟨x, hx⟩ => ⟨x.1, x.2, (φ.mapFamily_eq_iff x y).1 hx⟩,
    fun ⟨x, hx, h⟩ => ⟨⟨x, hx⟩, (φ.mapFamily_eq_iff _ y).2 h⟩⟩

/-- Existence of a fine lift of `y` is the image criterion at `y`. -/
theorem nonempty_fiber_mapFamily_iff :
    Nonempty {x // φ.mapFamily F x = y} ↔
      ∃ x : ∀ i, S.State (F i), S.Compatible F x ∧ ∀ i, φ.toFun (F i) (x i) = y.1 i :=
  (Function.nonempty_fiber_iff_mem_range _ y).trans (φ.mem_range_mapFamily_iff y)

/-- `y` has no fine lift exactly when the image criterion fails at `y`. -/
theorem isEmpty_fiber_mapFamily_iff :
    IsEmpty {x // φ.mapFamily F x = y} ↔
      ¬ ∃ x : ∀ i, S.State (F i), S.Compatible F x ∧ ∀ i, φ.toFun (F i) (x i) = y.1 i :=
  (Function.isEmpty_fiber_iff_notMem_range _ y).trans (not_congr (φ.mem_range_mapFamily_iff y))

/-- Uniqueness of fine lifts of `y`: any two fine compatible families observed as `y` coincide.
This is independent of existence and of the automatic uniqueness of the observed class. -/
theorem subsingleton_fiber_mapFamily_iff :
    Subsingleton {x // φ.mapFamily F x = y} ↔
      ∀ x x' : S.CompatibleFamily F, (∀ i, φ.toFun (F i) (x.1 i) = y.1 i) →
        (∀ i, φ.toFun (F i) (x'.1 i) = y.1 i) → x = x' :=
  (Function.subsingleton_fiber_iff _ y).trans <| forall_congr' fun x => forall_congr' fun x' =>
    imp_congr (φ.mapFamily_eq_iff x y) (imp_congr (φ.mapFamily_eq_iff x' y) Iff.rfl)

/-- Unique existence of a fine lift of `y`. -/
theorem nonempty_unique_fiber_mapFamily_iff :
    Nonempty (Unique {x // φ.mapFamily F x = y}) ↔
      ∃! x : S.CompatibleFamily F, ∀ i, φ.toFun (F i) (x.1 i) = y.1 i :=
  (unique_subtype_iff_existsUnique _).trans (existsUnique_congr fun x => φ.mapFamily_eq_iff x y)

end Fiber

/-! ### The observed quotient and its injection -/

/-- Observed equality of fine families is the kernel of the raw comparison: all observed
components agree. -/
theorem observed_rel_family_iff (x x' : S.CompatibleFamily F) :
    Setoid.ker (φ.mapFamily F) x x' ↔
      ∀ i, φ.toFun (F i) (x.1 i) = φ.toFun (F i) (x'.1 i) :=
  Setoid.ker_def.trans (φ.mapFamily_eq_mapFamily_iff x x')

/-- Observed equality is equality under the raw comparison. -/
theorem observed_rel_family_iff_mapFamily_eq (x x' : S.CompatibleFamily F) :
    Setoid.ker (φ.mapFamily F) x x' ↔ φ.mapFamily F x = φ.mapFamily F x' :=
  Setoid.ker_def

/-- The quotient `Q_F` of fine compatible families over `F` by observed equality. -/
abbrev observedFamily (F : ι → C) : Type _ :=
  Quotient (Setoid.ker (φ.mapFamily F))

/-- Two fine families have the same observed class exactly when all observed components
agree. -/
theorem observedFamily_mk_eq_iff (x x' : S.CompatibleFamily F) :
    (Quotient.mk _ x : φ.observedFamily F) = Quotient.mk _ x' ↔
      ∀ i, φ.toFun (F i) (x.1 i) = φ.toFun (F i) (x'.1 i) :=
  Quotient.eq.trans (φ.observed_rel_family_iff x x')

/-- The comparison induced on the observed quotient, `k_bar_F`. -/
def observedMapFamily (F : ι → C) : φ.observedFamily F → S'.CompatibleFamily F :=
  Setoid.kerLift (φ.mapFamily F)

/-- Factorization law: `observedMapFamily` on a class is `mapFamily` on a representative. -/
@[simp] theorem observedMapFamily_mk (x : S.CompatibleFamily F) :
    φ.observedMapFamily F (Quotient.mk _ x) = φ.mapFamily F x :=
  rfl

/-- Function-level form of `observedMapFamily_mk`. -/
theorem observedMapFamily_comp_mk : φ.observedMapFamily F ∘ Quotient.mk _ = φ.mapFamily F :=
  rfl

/-- The induced comparison is injective. -/
theorem observedMapFamily_injective : Function.Injective (φ.observedMapFamily F) :=
  Setoid.kerLift_injective _

/-- The induced comparison and the raw comparison have the same image. -/
theorem range_observedMapFamily :
    Set.range (φ.observedMapFamily F) = Set.range (φ.mapFamily F) :=
  Setoid.range_kerLift_eq_range _

/-- Every fiber of the induced comparison is a subsingleton: an observed class over `y` is
unique. This identifies all fine lifts of `y` and asserts no uniqueness of those lifts. -/
theorem subsingleton_fiber_observedMapFamily (y : S'.CompatibleFamily F) :
    Subsingleton {q // φ.observedMapFamily F q = y} :=
  (Function.injective_iff_subsingleton_fiber _).1 (φ.observedMapFamily_injective) y

/-- Shared inhabitedness: the raw fiber over `y` is nonempty exactly when the quotient fiber
is, by equality of images. The quotient preserves existence of a fine lift and discards its
multiplicity. -/
theorem nonempty_fiber_mapFamily_iff_nonempty_fiber_observedMapFamily
    (y : S'.CompatibleFamily F) :
    Nonempty {x // φ.mapFamily F x = y} ↔ Nonempty {q // φ.observedMapFamily F q = y} := by
  rw [Function.nonempty_fiber_iff_mem_range, Function.nonempty_fiber_iff_mem_range,
    range_observedMapFamily]

/-! ### The attainable image -/

/-- The attainable image `I_F`: the coarse compatible families over `F` reached by the raw
comparison. -/
abbrev image (F : ι → C) : Set (S'.CompatibleFamily F) :=
  Set.range (φ.mapFamily F)

/-- Membership in the attainable image is the image criterion. -/
theorem mem_image_iff (y : S'.CompatibleFamily F) :
    y ∈ φ.image F ↔
      ∃ x : ∀ i, S.State (F i), S.Compatible F x ∧ ∀ i, φ.toFun (F i) (x i) = y.1 i :=
  φ.mem_range_mapFamily_iff y

/-- The attainable image is the image of the induced comparison. -/
theorem image_eq_range_observedMapFamily : φ.image F = Set.range (φ.observedMapFamily F) :=
  (φ.range_observedMapFamily).symm

/-- The observed quotient is the attainable image, by the first isomorphism theorem for
sets. -/
noncomputable def observedFamilyEquivImage (F : ι → C) : φ.observedFamily F ≃ φ.image F :=
  Setoid.quotientKerEquivRange _

/-- `observedFamilyEquivImage` on a class is `mapFamily` on a representative. -/
@[simp] theorem coe_observedFamilyEquivImage_mk (x : S.CompatibleFamily F) :
    (φ.observedFamilyEquivImage F (Quotient.mk _ x) : S'.CompatibleFamily F) =
      φ.mapFamily F x :=
  rfl

/-- `observedFamilyEquivImage` is `observedMapFamily` on underlying families. -/
@[simp] theorem coe_observedFamilyEquivImage (q : φ.observedFamily F) :
    (φ.observedFamilyEquivImage F q : S'.CompatibleFamily F) = φ.observedMapFamily F q :=
  rfl

/-- Round trip: `observedFamilyEquivImage.symm` after `observedFamilyEquivImage`. -/
theorem observedFamilyEquivImage_symm_apply_apply (q : φ.observedFamily F) :
    (φ.observedFamilyEquivImage F).symm (φ.observedFamilyEquivImage F q) = q :=
  (φ.observedFamilyEquivImage F).symm_apply_apply q

/-- Round trip: `observedFamilyEquivImage` after `observedFamilyEquivImage.symm`. -/
theorem observedFamilyEquivImage_apply_symm_apply (y : φ.image F) :
    φ.observedFamilyEquivImage F ((φ.observedFamilyEquivImage F).symm y) = y :=
  (φ.observedFamilyEquivImage F).apply_symm_apply y

/-! ### Naturality along a declared family restriction -/

section Naturality

variable (m : FamilyMap F E)

/-- Function-level form of `restrict_mapFamily`: the raw commuting square. -/
theorem restrict_comp_mapFamily :
    S'.restrict m ∘ φ.mapFamily F = φ.mapFamily E ∘ S.restrict m :=
  funext (φ.restrict_mapFamily m)

/-- Observed equality is preserved by restriction: equal observations restrict to equal
observations, by `restrict_mapFamily`. This makes `restrictObserved` well defined. -/
theorem ker_mapFamily_restrict {x x' : S.CompatibleFamily F}
    (h : Setoid.ker (φ.mapFamily F) x x') :
    Setoid.ker (φ.mapFamily E) (S.restrict m x) (S.restrict m x') := by
  rw [Setoid.ker_def, ← restrict_mapFamily, ← restrict_mapFamily, Setoid.ker_def.1 h]

/-- Restriction of observed classes along `m`, induced by `S.restrict m` on representatives.
It is well defined on classes by `ker_mapFamily_restrict`. -/
def restrictObserved : φ.observedFamily F → φ.observedFamily E :=
  Quotient.map' (S.restrict m) fun _ _ => φ.ker_mapFamily_restrict m

/-- `restrictObserved` on a class is `S.restrict m` on a representative. -/
@[simp] theorem restrictObserved_mk (x : S.CompatibleFamily F) :
    φ.restrictObserved m (Quotient.mk _ x) = Quotient.mk _ (S.restrict m x) :=
  rfl

/-- The quotient commuting square: the induced comparison intertwines restriction of observed
classes with restriction of coarse families. -/
theorem observedMapFamily_restrictObserved (q : φ.observedFamily F) :
    φ.observedMapFamily E (φ.restrictObserved m q) = S'.restrict m (φ.observedMapFamily F q) :=
  Quotient.inductionOn q fun x => (φ.restrict_mapFamily m x).symm

/-- Function-level form of `observedMapFamily_restrictObserved`. -/
theorem observedMapFamily_comp_restrictObserved :
    φ.observedMapFamily E ∘ φ.restrictObserved m = S'.restrict m ∘ φ.observedMapFamily F :=
  funext (φ.observedMapFamily_restrictObserved m)

/-- Restriction of coarse families sends the attainable image over `F` into the attainable
image over `E`, by naturality of the raw comparison. -/
theorem mapsTo_restrict_image : Set.MapsTo (S'.restrict m) (φ.image F) (φ.image E) :=
  Set.mapsTo_range_range (φ.restrict_mapFamily m)

/-- `restrict_(F,E)(I_F) ⊆ I_E`. Naturality gives inclusion only. -/
theorem image_restrict_subset : S'.restrict m '' φ.image F ⊆ φ.image E :=
  (φ.mapsTo_restrict_image m).image_subset

/-- The map induced by restriction on attainable images. -/
def restrictImage : φ.image F → φ.image E :=
  (φ.mapsTo_restrict_image m).restrict _ _ _

/-- `restrictImage` is `S'.restrict m` on underlying coarse families. -/
@[simp] theorem coe_restrictImage (y : φ.image F) :
    (φ.restrictImage m y : S'.CompatibleFamily E) = S'.restrict m y :=
  rfl

/-- The image commuting square: `observedFamilyEquivImage` intertwines `restrictObserved` and
`restrictImage`. -/
theorem restrictImage_observedFamilyEquivImage (q : φ.observedFamily F) :
    φ.restrictImage m (φ.observedFamilyEquivImage F q) =
      φ.observedFamilyEquivImage E (φ.restrictObserved m q) :=
  Subtype.ext (φ.observedMapFamily_restrictObserved m q).symm

/-- Function-level form of `restrictImage_observedFamilyEquivImage`. -/
theorem restrictImage_comp_observedFamilyEquivImage :
    φ.restrictImage m ∘ φ.observedFamilyEquivImage F =
      φ.observedFamilyEquivImage E ∘ φ.restrictObserved m :=
  funext (φ.restrictImage_observedFamilyEquivImage m)

/-- Restriction sends the raw fiber over `y` into the raw fiber over `S'.restrict m y`, acting
on the supplied local states by `S.restrict m`. -/
def fiberRestrict (y : S'.CompatibleFamily F) :
    {x // φ.mapFamily F x = y} → {x' // φ.mapFamily E x' = S'.restrict m y} :=
  fun x => ⟨S.restrict m x.1, by rw [← restrict_mapFamily, x.2]⟩

/-- `fiberRestrict` is `S.restrict m` on underlying fine families. -/
@[simp] theorem coe_fiberRestrict (y : S'.CompatibleFamily F) (x : {x // φ.mapFamily F x = y}) :
    (φ.fiberRestrict m y x : S.CompatibleFamily E) = S.restrict m x.1 :=
  rfl

end Naturality

/-! ### Identity and composition -/

/-- Restriction of observed classes along the identity operation is the identity. -/
theorem restrictObserved_id (q : φ.observedFamily F) :
    φ.restrictObserved (FamilyMap.id F) q = q :=
  Quotient.inductionOn q fun x => congrArg (Quotient.mk _) (S.restrict_id x)

/-- Restriction of observed classes along a composite is the composite of restrictions. -/
theorem restrictObserved_comp (n : FamilyMap E D) (m : FamilyMap F E) (q : φ.observedFamily F) :
    φ.restrictObserved (n.comp m) q = φ.restrictObserved n (φ.restrictObserved m q) :=
  Quotient.inductionOn q fun x => congrArg (Quotient.mk _) (S.restrict_comp n m x)

/-- Restriction of attainable images along the identity operation is the identity. -/
theorem restrictImage_id (y : φ.image F) : φ.restrictImage (FamilyMap.id F) y = y :=
  Subtype.ext (S'.restrict_id y.1)

/-- Restriction of attainable images along a composite is the composite of restrictions. -/
theorem restrictImage_comp (n : FamilyMap E D) (m : FamilyMap F E) (y : φ.image F) :
    φ.restrictImage (n.comp m) y = φ.restrictImage n (φ.restrictImage m y) :=
  Subtype.ext (S'.restrict_comp n m y.1)

/-- Restricting a fine lift along the identity keeps its local states, by `restrict_id`. -/
theorem fiberRestrict_id_coe (y : S'.CompatibleFamily F) (x : {x // φ.mapFamily F x = y}) :
    (φ.fiberRestrict (FamilyMap.id F) y x).1 = x.1 :=
  S.restrict_id x.1

/-- Restricting a fine lift along a composite is restricting twice, by `restrict_comp`. -/
theorem fiberRestrict_comp_coe (n : FamilyMap E D) (m : FamilyMap F E)
    (y : S'.CompatibleFamily F) (x : {x // φ.mapFamily F x = y}) :
    (φ.fiberRestrict (n.comp m) y x).1 = (φ.fiberRestrict n _ (φ.fiberRestrict m y x)).1 :=
  S.restrict_comp n m x.1

end RestrictionSystem.Hom
