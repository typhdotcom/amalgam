import Mathlib.Order.Basic

/-!
# Restriction systems and compatible families

A restriction system assigns a state type to every context of a preorder `C`, with restriction
maps toward coarser contexts. The order reads `c ≤ d` as “`c` is coarser than `d`”: a state at
`d` restricts along `h : c ≤ d` to a state at `c`. Restriction satisfies the identity and
composition laws `res_refl` and `res_trans`.

For an indexed family of contexts `F : ι → C`, a compatible family is one state per context
agreeing after restriction to every common coarser context. A declared restriction operation
between families is a `FamilyMap`: a reindexing together with a context inequality at every
target index. It covers forgetting local views (`index` non-surjective, `le` reflexive) and
restricting a view along a context inequality. `RestrictionSystem.restrict` acts on compatible
families by actual restriction of the supplied states and satisfies identity and composition
laws through `res_refl` and `res_trans`.

A morphism of restriction systems over the same contexts is an observation at every context
commuting with restriction; it sends compatible families to compatible families
(`RestrictionSystem.Hom.mapFamily`) naturally in the family (`restrict_mapFamily`).

Finiteness of the index type is never assumed; empty index types and empty state types are
allowed throughout.
-/

universe u v w

variable {C : Type u} [Preorder C]

/-- State types over a preorder of contexts with restriction toward coarser contexts.
`res h : State d → State c` for `h : c ≤ d`. -/
structure RestrictionSystem (C : Type u) [Preorder C] where
  /-- The state type at a context. -/
  State : C → Type v
  /-- Restriction of a state at `d` to a coarser context `c`. -/
  res : ∀ {c d : C}, c ≤ d → State d → State c
  /-- Restriction along a reflexivity proof is the identity. -/
  res_refl : ∀ {c : C} (h : c ≤ c) (x : State c), res h x = x
  /-- Restriction composes along transitivity. -/
  res_trans : ∀ {c d e : C} (h₁ : c ≤ d) (h₂ : d ≤ e) (x : State e),
    res h₁ (res h₂ x) = res (h₁.trans h₂) x

/-- A declared restriction operation from the family `F` to the family `E`: every index of `E`
names an index of `F` whose context is at least as fine. -/
structure FamilyMap {ι : Type*} {κ : Type*} (F : ι → C) (E : κ → C) where
  /-- The index of `F` supplying each index of `E`. -/
  index : κ → ι
  /-- The context of `E k` is coarser than the context supplying it. -/
  le : ∀ k, E k ≤ F (index k)

namespace FamilyMap

variable {ι : Type*} {κ : Type*} {μ : Type*} {F : ι → C} {E : κ → C} {D : μ → C}

/-- The identity restriction operation. -/
def id (F : ι → C) : FamilyMap F F := ⟨fun i => i, fun _ => le_rfl⟩

/-- Composition of restriction operations, `n` after `m`. -/
def comp (n : FamilyMap E D) (m : FamilyMap F E) : FamilyMap F D :=
  ⟨fun d => m.index (n.index d), fun d => (n.le d).trans (m.le (n.index d))⟩

@[simp] theorem id_index (F : ι → C) (i : ι) : (id F).index i = i := rfl

@[simp] theorem comp_index (n : FamilyMap E D) (m : FamilyMap F E) (d : μ) :
    (n.comp m).index d = m.index (n.index d) := rfl

end FamilyMap

namespace RestrictionSystem

variable (S : RestrictionSystem.{u, v} C) {ι : Type*} {κ : Type*} {μ : Type*}

/-- A family of states over `F` is compatible when any two of its states agree after
restriction to every common coarser context. -/
def Compatible (F : ι → C) (x : ∀ i, S.State (F i)) : Prop :=
  ∀ ⦃c : C⦄ ⦃i j : ι⦄ (hi : c ≤ F i) (hj : c ≤ F j), S.res hi (x i) = S.res hj (x j)

/-- The type of compatible families of states over `F`. -/
abbrev CompatibleFamily (F : ι → C) : Type _ :=
  {x : ∀ i, S.State (F i) // S.Compatible F x}

variable {S} {F : ι → C} {E : κ → C} {D : μ → C}

/-- Restricting a compatible family along a `FamilyMap` gives a compatible family, by
`res_trans`. -/
theorem Compatible.restrict {x : ∀ i, S.State (F i)} (hx : S.Compatible F x) (m : FamilyMap F E) :
    S.Compatible E fun k => S.res (m.le k) (x (m.index k)) := by
  intro c k k' hk hk'
  rw [S.res_trans, S.res_trans]
  exact hx _ _

variable (S)

/-- The action of a declared restriction operation on compatible families: restrict each
supplied state along the declared context inequality. -/
def restrict (m : FamilyMap F E) (x : S.CompatibleFamily F) : S.CompatibleFamily E :=
  ⟨fun k => S.res (m.le k) (x.1 (m.index k)), x.2.restrict m⟩

@[simp] theorem restrict_apply (m : FamilyMap F E) (x : S.CompatibleFamily F) (k : κ) :
    (S.restrict m x).1 k = S.res (m.le k) (x.1 (m.index k)) :=
  rfl

/-- Restriction along the identity operation is the identity, by `res_refl`. -/
theorem restrict_id (x : S.CompatibleFamily F) : S.restrict (FamilyMap.id F) x = x :=
  Subtype.ext (funext fun _ => S.res_refl _ _)

/-- Restriction along a composite is the composite of restrictions, by `res_trans`. -/
theorem restrict_comp (n : FamilyMap E D) (m : FamilyMap F E) (x : S.CompatibleFamily F) :
    S.restrict (n.comp m) x = S.restrict n (S.restrict m x) :=
  Subtype.ext (funext fun _ => (S.res_trans _ _ _).symm)

/-- A morphism of restriction systems over the same contexts: an observation at every context
commuting with restriction. -/
structure Hom (S : RestrictionSystem.{u, v} C) (S' : RestrictionSystem.{u, w} C) where
  /-- The observation at a context. -/
  toFun : ∀ c, S.State c → S'.State c
  /-- Observation commutes with restriction. -/
  naturality : ∀ {c d : C} (h : c ≤ d) (x : S.State d), S'.res h (toFun d x) = toFun c (S.res h x)

variable {S} {S' : RestrictionSystem.{u, w} C}

/-- Observing every state of a compatible family gives a compatible family, by naturality. -/
theorem Compatible.map (φ : S.Hom S') {x : ∀ i, S.State (F i)} (hx : S.Compatible F x) :
    S'.Compatible F fun i => φ.toFun (F i) (x i) := by
  intro c i j hi hj
  rw [φ.naturality, φ.naturality, hx hi hj]

namespace Hom

variable (φ : S.Hom S')

/-- The raw comparison of a family: observe every component. -/
def mapFamily (F : ι → C) (x : S.CompatibleFamily F) : S'.CompatibleFamily F :=
  ⟨fun i => φ.toFun (F i) (x.1 i), x.2.map φ⟩

@[simp] theorem mapFamily_apply (F : ι → C) (x : S.CompatibleFamily F) (i : ι) :
    (φ.mapFamily F x).1 i = φ.toFun (F i) (x.1 i) :=
  rfl

/-- Naturality of the raw comparison in the family: observing then restricting is restricting
then observing. -/
theorem restrict_mapFamily (m : FamilyMap F E) (x : S.CompatibleFamily F) :
    S'.restrict m (φ.mapFamily F x) = φ.mapFamily E (S.restrict m x) :=
  Subtype.ext (funext fun _ => φ.naturality _ _)

end Hom

end RestrictionSystem
