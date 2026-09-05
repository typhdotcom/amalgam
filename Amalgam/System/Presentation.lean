import Amalgam.Core.Fiber
import Amalgam.System.Restriction

/-!
# Presentations of compatible families

Two presentations of the same finite shape have equivalent compatible-family types. The single
principle behind every result here is `RestrictionSystem.restrict_endo`: a declared restriction
operation from a family to itself acts as the identity on compatible families, because
compatibility already forces each restricted state to agree with the state it is compared to.
Consequently any pair of declared operations `F → E → F` composes to the identity
(`restrict_restrict`), and two families with declared operations in both directions have
equivalent compatible-family types (`restrictEquiv`).

Specializations:

* **Relabeling.** For `e : κ ≃ ι`, `relabel e : CompatibleFamily F ≃ CompatibleFamily (F ∘ e)`,
  reindexing along `e` forwards and along `e.symm` backwards.
* **Redundancy.** For `σ : κ → ι` and `h : ∀ k, G k ≤ F (σ k)`, every view of `G` is obtained by
  restricting an included view, and `redundancyEquiv σ h :
  CompatibleFamily (Sum.elim F G) ≃ CompatibleFamily F` forgets the added views forwards and
  extends by `res (h k)` backwards. Adding a single view (`addViewEquiv`) and duplicating a view
  (`duplicateEquiv`) are the cases `κ = Unit`.
* **Fibers of family restrictions.** The fiber of `restrict m` over `z` is the type of families
  over the finer presentation whose declared restrictions equal the components of `z`
  (`restrictFiberEquiv`); under a reverse operation it is a subsingleton. The raw comparison of a
  morphism restricts fibers along `m` by restricting the same local states
  (`Hom.fiberRestrict` in `Amalgam/System/Comparison.lean`).

## Shapes at the interface level

A binary overlap is the family `![l, r]` over a preorder with a context `b ≤ l`, `b ≤ r`;
`compatible_fin_two_iff` reduces compatibility over `Fin 2` to the single cross condition. The
shared-overlap shape `L → B ← M → D ← R` is the family `![L, M, R]` over a preorder with
`B ≤ L`, `B ≤ M`, `D ≤ M`, `D ≤ R`; its subfamilies `![L, M]` and `![M, R]` are reached by the
forgetful operations `FamilyMap.inl`-style reindexings. Concrete preorders are not built here.

Index types are arbitrary and may be empty: over an empty index type the compatible-family type
is a singleton (`RestrictionSystem.uniqueOfIsEmpty`). State types may be empty.
-/

universe u v w

variable {C : Type u} [Preorder C]

namespace FamilyMap

variable {ι : Type*} {κ : Type*}

/-- Reindexing a family along `e`: the operation `F → F ∘ e` with reflexive inequalities. -/
def reindex (F : ι → C) (e : κ → ι) : FamilyMap F (F ∘ e) := ⟨e, fun _ => le_rfl⟩

/-- Reindexing back along the inverse of an equivalence, with the inequality
`F i ≤ F (e (e.symm i))` obtained by rewriting `e.apply_symm_apply`. -/
def reindexSymm (F : ι → C) (e : κ ≃ ι) : FamilyMap (F ∘ e) F :=
  ⟨e.symm, fun i => le_of_eq (congrArg F (e.apply_symm_apply i)).symm⟩

/-- Forgetting the views of `G` from `Sum.elim F G`. -/
def inl (F : ι → C) (G : κ → C) : FamilyMap (Sum.elim F G) F := ⟨Sum.inl, fun _ => le_rfl⟩

/-- Extending `F` by the views of `G`, each obtained by restricting the included context
`F (σ k)`. -/
def extend {F : ι → C} {G : κ → C} (σ : κ → ι) (h : ∀ k, G k ≤ F (σ k)) :
    FamilyMap F (Sum.elim F G) :=
  ⟨Sum.elim (fun i => i) σ, fun k => by cases k with | inl i => exact le_rfl | inr k => exact h k⟩

@[simp] theorem reindex_index (F : ι → C) (e : κ → ι) (k : κ) : (reindex F e).index k = e k := rfl

@[simp] theorem reindexSymm_index (F : ι → C) (e : κ ≃ ι) (i : ι) :
    (reindexSymm F e).index i = e.symm i := rfl

@[simp] theorem inl_index (F : ι → C) (G : κ → C) (i : ι) : (inl F G).index i = Sum.inl i := rfl

@[simp] theorem extend_index_inl {F : ι → C} {G : κ → C} (σ : κ → ι) (h : ∀ k, G k ≤ F (σ k))
    (i : ι) : (extend σ h).index (Sum.inl i) = i := rfl

@[simp] theorem extend_index_inr {F : ι → C} {G : κ → C} (σ : κ → ι) (h : ∀ k, G k ≤ F (σ k))
    (k : κ) : (extend σ h).index (Sum.inr k) = σ k := rfl

end FamilyMap

namespace RestrictionSystem

variable (S : RestrictionSystem.{u, v} C) {ι : Type*} {κ : Type*} {μ : Type*}
variable {F : ι → C} {E : κ → C} {D : μ → C}

/-! ### Empty families -/

/-- Over an empty index type there is exactly one compatible family. -/
instance uniqueOfIsEmpty [IsEmpty ι] : Unique (S.CompatibleFamily F) where
  default := ⟨isEmptyElim, fun _ i => isEmptyElim i⟩
  uniq _ := Subtype.ext (funext isEmptyElim)

/-! ### Round trips of declared restrictions -/

/-- A declared restriction operation from a family to itself is the identity on compatible
families: compatibility at the context `F i` against `F i ≤ F (m.index i)` and `F i ≤ F i`,
followed by `res_refl`. Consumes `Compatible` and `res_refl`. -/
theorem restrict_endo (m : FamilyMap F F) (x : S.CompatibleFamily F) : S.restrict m x = x :=
  Subtype.ext (funext fun i => (x.2 (m.le i) (le_refl (F i))).trans (S.res_refl _ _))

/-- Declared operations in opposite directions compose to the identity on compatible families.
Consumes `restrict_comp` (hence `res_trans`) and `restrict_endo`. -/
theorem restrict_restrict (m : FamilyMap F E) (n : FamilyMap E F) (x : S.CompatibleFamily F) :
    S.restrict n (S.restrict m x) = x :=
  (S.restrict_comp n m x).symm.trans (S.restrict_endo _ x)

/-- Two families with declared restriction operations in both directions have equivalent
compatible-family types, the operations being mutually inverse. Both inverse laws are
`restrict_restrict`. -/
def restrictEquiv (m : FamilyMap F E) (n : FamilyMap E F) :
    S.CompatibleFamily F ≃ S.CompatibleFamily E where
  toFun := S.restrict m
  invFun := S.restrict n
  left_inv := S.restrict_restrict m n
  right_inv := S.restrict_restrict n m

@[simp] theorem restrictEquiv_apply (m : FamilyMap F E) (n : FamilyMap E F)
    (x : S.CompatibleFamily F) : S.restrictEquiv m n x = S.restrict m x :=
  rfl

@[simp] theorem restrictEquiv_symm_apply (m : FamilyMap F E) (n : FamilyMap E F)
    (y : S.CompatibleFamily E) : (S.restrictEquiv m n).symm y = S.restrict n y :=
  rfl

/-- A declared operation with a declared operation back is bijective. -/
theorem bijective_restrict (m : FamilyMap F E) (n : FamilyMap E F) :
    Function.Bijective (S.restrict m) :=
  (S.restrictEquiv m n).bijective

/-! ### Relabeling -/

/-- Relabeling invariance: reindexing the presentation along an equivalence `e : κ ≃ ι` gives
equivalent compatible-family types. The forward map is restriction along `FamilyMap.reindex F e`
and the inverse is restriction along `FamilyMap.reindexSymm F e`; both inverse laws are
`restrict_restrict`, consuming `Compatible`, `res_refl` and `res_trans`. -/
def relabel (e : κ ≃ ι) : S.CompatibleFamily F ≃ S.CompatibleFamily (F ∘ e) :=
  S.restrictEquiv (FamilyMap.reindex F e) (FamilyMap.reindexSymm F e)

theorem relabel_apply (e : κ ≃ ι) (x : S.CompatibleFamily F) :
    S.relabel e x = S.restrict (FamilyMap.reindex F e) x :=
  rfl

theorem relabel_symm_apply (e : κ ≃ ι) (y : S.CompatibleFamily (F ∘ e)) :
    (S.relabel e).symm y = S.restrict (FamilyMap.reindexSymm F e) y :=
  rfl

/-- The relabeled family reads the original at `e k`, by `res_refl`. -/
@[simp] theorem relabel_apply_coe (e : κ ≃ ι) (x : S.CompatibleFamily F) (k : κ) :
    (S.relabel e x).1 k = x.1 (e k) :=
  S.res_refl _ _

/-- The inverse relabeling reads the relabeled family at `e.symm i`, restricted along the
rewritten inequality `F i ≤ F (e (e.symm i))`. -/
theorem relabel_symm_apply_coe (e : κ ≃ ι) (y : S.CompatibleFamily (F ∘ e)) (i : ι) :
    ((S.relabel e).symm y).1 i =
      S.res (le_of_eq (congrArg F (e.apply_symm_apply i)).symm) (y.1 (e.symm i)) :=
  rfl

/-- At an index of the form `e k` the inverse relabeling is the original component, by
compatibility of `y` and `res_refl`. -/
@[simp] theorem relabel_symm_apply_coe_apply (e : κ ≃ ι) (y : S.CompatibleFamily (F ∘ e))
    (k : κ) : ((S.relabel e).symm y).1 (e k) = y.1 k :=
  (y.2 ((FamilyMap.reindexSymm F e).le (e k)) (le_refl ((F ∘ e) k))).trans (S.res_refl _ _)

/-- Round trip: relabeling then unrelabeling. -/
theorem relabel_symm_relabel (e : κ ≃ ι) (x : S.CompatibleFamily F) :
    (S.relabel e).symm (S.relabel e x) = x :=
  (S.relabel e).symm_apply_apply x

/-- Round trip: unrelabeling then relabeling. -/
theorem relabel_relabel_symm (e : κ ≃ ι) (y : S.CompatibleFamily (F ∘ e)) :
    S.relabel e ((S.relabel e).symm y) = y :=
  (S.relabel e).apply_symm_apply y

/-- Relabeling along the identity is the identity. -/
theorem relabel_refl_apply (x : S.CompatibleFamily F) : S.relabel (Equiv.refl ι) x = x :=
  S.restrict_id x

/-- Relabeling twice is relabeling along the composite. -/
theorem relabel_relabel (e : κ ≃ ι) (e' : μ ≃ κ) (x : S.CompatibleFamily F) :
    S.relabel e' (S.relabel e x) = S.relabel (e'.trans e) x :=
  (S.restrict_comp _ _ x).symm

/-- A declared operation out of a relabeled family is a declared operation out of the original,
by `restrict_comp`. -/
theorem restrict_relabel (e : κ ≃ ι) (n : FamilyMap (F ∘ e) D) (x : S.CompatibleFamily F) :
    S.restrict n (S.relabel e x) = S.restrict ⟨fun d => e (n.index d), n.le⟩ x :=
  (S.restrict_comp _ _ x).symm

/-- Relabeling the target of a declared operation is a declared operation, by `restrict_comp`. -/
theorem relabel_restrict (m : FamilyMap F E) (e : μ ≃ κ) (x : S.CompatibleFamily F) :
    S.relabel e (S.restrict m x) = S.restrict ⟨fun d => m.index (e d), fun d => m.le (e d)⟩ x :=
  (S.restrict_comp _ _ x).symm

/-! ### Redundancy -/

variable {G : κ → C}

/-- The extension of a compatible family by redundant views is compatible; this is
`Compatible.restrict`, consuming `res_trans` and `Compatible`. -/
theorem Compatible.extend {x : ∀ i, S.State (F i)} (hx : S.Compatible F x) (σ : κ → ι)
    (h : ∀ k, G k ≤ F (σ k)) :
    S.Compatible (Sum.elim F G) fun k =>
      S.res ((FamilyMap.extend σ h).le k) (x ((FamilyMap.extend σ h).index k)) :=
  hx.restrict _

/-- The redundancy law: adding views each obtained by restricting an included context changes
nothing. The forward map forgets the added views (restriction along `FamilyMap.inl`), the
inverse extends by `S.res (h k) (x.1 (σ k))` (restriction along `FamilyMap.extend σ h`). The
extension is compatible by `res_trans` and `Compatible`; the extend-then-forget round trip is
`res_refl`; the forget-then-extend round trip uses compatibility of the original family at the
context `G k` against `G k ≤ G k` and `G k ≤ F (σ k)`, plus `res_refl`. -/
def redundancyEquiv (σ : κ → ι) (h : ∀ k, G k ≤ F (σ k)) :
    S.CompatibleFamily (Sum.elim F G) ≃ S.CompatibleFamily F :=
  S.restrictEquiv (FamilyMap.inl F G) (FamilyMap.extend σ h)

theorem redundancyEquiv_apply (σ : κ → ι) (h : ∀ k, G k ≤ F (σ k))
    (x : S.CompatibleFamily (Sum.elim F G)) :
    S.redundancyEquiv σ h x = S.restrict (FamilyMap.inl F G) x :=
  rfl

theorem redundancyEquiv_symm_apply (σ : κ → ι) (h : ∀ k, G k ≤ F (σ k))
    (y : S.CompatibleFamily F) :
    (S.redundancyEquiv σ h).symm y = S.restrict (FamilyMap.extend σ h) y :=
  rfl

/-- Forgetting keeps the included components, by `res_refl`. -/
@[simp] theorem redundancyEquiv_apply_coe (σ : κ → ι) (h : ∀ k, G k ≤ F (σ k))
    (x : S.CompatibleFamily (Sum.elim F G)) (i : ι) :
    (S.redundancyEquiv σ h x).1 i = x.1 (Sum.inl i) :=
  S.res_refl _ _

/-- Extending keeps the included components, by `res_refl`. -/
@[simp] theorem redundancyEquiv_symm_apply_coe_inl (σ : κ → ι) (h : ∀ k, G k ≤ F (σ k))
    (y : S.CompatibleFamily F) (i : ι) :
    ((S.redundancyEquiv σ h).symm y).1 (Sum.inl i) = y.1 i :=
  S.res_refl _ _

/-- Extending fills the added components by restriction. -/
@[simp] theorem redundancyEquiv_symm_apply_coe_inr (σ : κ → ι) (h : ∀ k, G k ≤ F (σ k))
    (y : S.CompatibleFamily F) (k : κ) :
    ((S.redundancyEquiv σ h).symm y).1 (Sum.inr k) = S.res (h k) (y.1 (σ k)) :=
  rfl

/-- Round trip: extending then forgetting. -/
theorem forget_extend (σ : κ → ι) (h : ∀ k, G k ≤ F (σ k)) (y : S.CompatibleFamily F) :
    S.restrict (FamilyMap.inl F G) (S.restrict (FamilyMap.extend σ h) y) = y :=
  S.restrict_restrict _ _ y

/-- Round trip: forgetting then extending. -/
theorem extend_forget (σ : κ → ι) (h : ∀ k, G k ≤ F (σ k))
    (x : S.CompatibleFamily (Sum.elim F G)) :
    S.restrict (FamilyMap.extend σ h) (S.restrict (FamilyMap.inl F G) x) = x :=
  S.restrict_restrict _ _ x

/-- Forgetting redundant views is bijective. -/
theorem bijective_restrict_inl (σ : κ → ι) (h : ∀ k, G k ≤ F (σ k)) :
    Function.Bijective (S.restrict (FamilyMap.inl F G)) :=
  S.bijective_restrict _ (FamilyMap.extend σ h)

/-- Adding a single view `c ≤ F i₀` changes nothing. -/
def addViewEquiv (c : C) (i₀ : ι) (hc : c ≤ F i₀) :
    S.CompatibleFamily (Sum.elim F fun _ : Unit => c) ≃ S.CompatibleFamily F :=
  S.redundancyEquiv (fun _ => i₀) fun _ => hc

@[simp] theorem addViewEquiv_apply_coe (c : C) (i₀ : ι) (hc : c ≤ F i₀)
    (x : S.CompatibleFamily (Sum.elim F fun _ : Unit => c)) (i : ι) :
    (S.addViewEquiv c i₀ hc x).1 i = x.1 (Sum.inl i) :=
  S.res_refl _ _

@[simp] theorem addViewEquiv_symm_apply_coe_inl (c : C) (i₀ : ι) (hc : c ≤ F i₀)
    (y : S.CompatibleFamily F) (i : ι) :
    ((S.addViewEquiv c i₀ hc).symm y).1 (Sum.inl i) = y.1 i :=
  S.res_refl _ _

@[simp] theorem addViewEquiv_symm_apply_coe_inr (c : C) (i₀ : ι) (hc : c ≤ F i₀)
    (y : S.CompatibleFamily F) (u : Unit) :
    ((S.addViewEquiv c i₀ hc).symm y).1 (Sum.inr u) = S.res hc (y.1 i₀) :=
  rfl

/-- Duplicate occurrences: repeating the view `F i₀` changes nothing, and forgetting the
duplicate is an equivalence. -/
def duplicateEquiv (i₀ : ι) :
    S.CompatibleFamily (Sum.elim F fun _ : Unit => F i₀) ≃ S.CompatibleFamily F :=
  S.addViewEquiv (F i₀) i₀ le_rfl

@[simp] theorem duplicateEquiv_apply_coe (i₀ : ι)
    (x : S.CompatibleFamily (Sum.elim F fun _ : Unit => F i₀)) (i : ι) :
    (S.duplicateEquiv i₀ x).1 i = x.1 (Sum.inl i) :=
  S.res_refl _ _

@[simp] theorem duplicateEquiv_symm_apply_coe_inl (i₀ : ι) (y : S.CompatibleFamily F) (i : ι) :
    ((S.duplicateEquiv i₀).symm y).1 (Sum.inl i) = y.1 i :=
  S.res_refl _ _

/-- The duplicate component is the original component, by `res_refl`. -/
@[simp] theorem duplicateEquiv_symm_apply_coe_inr (i₀ : ι) (y : S.CompatibleFamily F)
    (u : Unit) : ((S.duplicateEquiv i₀).symm y).1 (Sum.inr u) = y.1 i₀ :=
  S.res_refl _ _

/-- Forgetting a duplicated view is bijective. -/
theorem bijective_restrict_inl_duplicate (i₀ : ι) :
    Function.Bijective (S.restrict (FamilyMap.inl F fun _ : Unit => F i₀)) :=
  S.bijective_restrict_inl (fun _ => i₀) fun _ => le_rfl

/-! ### Fibers of family restrictions -/

/-- The fiber of `restrict m` over `z` is the type of compatible families over `F` whose declared
restrictions are the components of `z`: the extension choices of `z` along `m`. -/
def restrictFiberEquiv (m : FamilyMap F E) (z : S.CompatibleFamily E) :
    {x // S.restrict m x = z} ≃
      {x : S.CompatibleFamily F // ∀ k, S.res (m.le k) (x.1 (m.index k)) = z.1 k} where
  toFun x := ⟨x.1, fun k => congrArg (fun w => w.1 k) x.2⟩
  invFun x := ⟨x.1, Subtype.ext (funext x.2)⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem restrictFiberEquiv_apply_coe (m : FamilyMap F E) (z : S.CompatibleFamily E)
    (x : {x // S.restrict m x = z}) : (S.restrictFiberEquiv m z x).1 = x.1 :=
  rfl

@[simp] theorem restrictFiberEquiv_symm_apply_coe (m : FamilyMap F E) (z : S.CompatibleFamily E)
    (x : {x : S.CompatibleFamily F // ∀ k, S.res (m.le k) (x.1 (m.index k)) = z.1 k}) :
    ((S.restrictFiberEquiv m z).symm x).1 = x.1 :=
  rfl

/-- With a declared operation back, every fiber of `restrict m` is a subsingleton. -/
theorem subsingleton_fiber_restrict (m : FamilyMap F E) (n : FamilyMap E F)
    (z : S.CompatibleFamily E) : Subsingleton {x // S.restrict m x = z} :=
  (Function.injective_iff_subsingleton_fiber _).1 (S.bijective_restrict m n).1 z

/-- Under the redundancy hypothesis, the extension choices of a forgetful restriction form a
subsingleton. -/
theorem subsingleton_fiber_restrict_inl (σ : κ → ι) (h : ∀ k, G k ≤ F (σ k))
    (z : S.CompatibleFamily F) : Subsingleton {x // S.restrict (FamilyMap.inl F G) x = z} :=
  S.subsingleton_fiber_restrict _ (FamilyMap.extend σ h) z

/-! ### Binary shape -/

/-- Over `Fin 2`, compatibility is the single cross condition between the two views: the
diagonal cases hold by proof irrelevance and the symmetric case by `Eq.symm`. -/
theorem compatible_fin_two_iff (F : Fin 2 → C) (x : ∀ i, S.State (F i)) :
    S.Compatible F x ↔
      ∀ ⦃c : C⦄ (hl : c ≤ F 0) (hr : c ≤ F 1), S.res hl (x 0) = S.res hr (x 1) := by
  refine ⟨fun hx _ hl hr => hx hl hr, fun H c i j hi hj => ?_⟩
  match i, j, hi, hj with
  | 0, 0, _, _ => rfl
  | 0, 1, hi, hj => exact H hi hj
  | 1, 0, hi, hj => exact (H hj hi).symm
  | 1, 1, _, _ => rfl

end RestrictionSystem
