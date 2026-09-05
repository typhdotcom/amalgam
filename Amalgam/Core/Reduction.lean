import Amalgam.Core.Comparison
import Amalgam.Core.Fiber
import Mathlib.Data.Setoid.Basic
import Mathlib.Logic.Equiv.Set

/-!
# Reduction of compatible pairs across an observed overlap

Fix spans `L ─p→ B ←q─ R` and `L' ─p'→ B' ←q'─ R'` of arbitrary types and observation maps
`a : L → L'`, `b : B → B'`, `c : R → R'` commuting pointwise: `p' (a l) = b (p l)` and
`q' (c r) = b (q r)`. Commutation alone induces the comparison
`Function.Pullback.map : p.Pullback q → p'.Pullback q'`, `(l, r) ↦ (a l, c r)`, the lift of
`a ∘ fst` and `c ∘ snd`; it agrees with mathlib's `Function.mapPullback`.

## Main results

* `Function.Pullback.map`, `fst_map`, `snd_map`, `map_eq_iff`, `map_eq_map_iff`: the observed
  comparison and its projection laws. Its raw fibers are the fine lifts of a coarse pair.
* `Function.Pullback.Observed`, `observedMap`: the quotient of fine pairs by observed equality,
  `Setoid.ker map`, and the induced injection `k_bar`. `observed_rel_iff` states the relation as
  agreement of observed components, `observedMap_injective` and `range_observedMap` give
  injectivity and equality of images, and `observedEquivRange` identifies the quotient with the
  common image. Fibers of `observedMap` are subsingletons, `subsingleton_fiber_observedMap`;
  by equality of images they are nonempty exactly when the raw fibers of `map` are, so the
  quotient preserves existence of a fine lift while discarding its multiplicity.
* `mem_range_map_iff`: a coarse compatible pair `t` is attained exactly when
  `p '' (a ⁻¹' {t.fst}) ∩ q '' (c ⁻¹' {t.snd})` is nonempty, i.e. some fine overlap value is
  reached from both sides above `t`. `fiberMapEquiv`, `fiberMapEquivProd`,
  `fiberMapEquivPullback`, `nonempty_fiber_map_iff`, `subsingleton_fiber_map_iff` describe the
  fine lifts of `t` and separate their existence from their uniqueness.
* `bijective_observedMap_iff`: `observedMap` is bijective exactly when the criterion holds at
  every coarse compatible pair. Under the criterion `observedEquiv` is the equivalence
  `Observed ha hc ≃ p'.Pullback q'` extending the quotient injection, its forward function being
  `observedMap` (`observedEquiv_apply`); the inverse accepting a coarse compatible pair is
  `observedEquiv.symm : p'.Pullback q' → Observed ha hc`, with both round trips
  `observedMap_observedEquiv_symm`, `observedEquiv_symm_observedMap` and uniqueness
  `eq_observedEquiv_symm_of_rightInverse`, `eq_observedEquiv_symm_of_leftInverse`;
  `exists_inverse_observedMap_iff` packages the converse.
* `mem_range_map_iff_of_injective`, `bijective_observedMap_of_injective`: with an injective
  overlap observation `b` the criterion is componentwise, and surjective `a`, `c` then suffice.
  This is a sufficient special case only.
* `Set.mapsTo_range_range`, `rangeFactorization_comm`, `mapRangeFactorization`: arbitrary
  observations restrict to surjections onto their images, with the coarse span restricted to
  those images; the restricted comparison has the same attained pairs.

## Conventions

Empty types are allowed and no finiteness, decidability, or surjectivity hypothesis enters the
core statements. The criterion theorems use no choice; `observedEquiv` uses `Equiv.ofBijective`
and hence classical choice. Its inverse `observedEquiv.symm` selects an observed class over a
coarse pair, never a fine representative, and asserts nothing about uniqueness of fine lifts.
Carriers are `Type*` because the criterion is a set of fine overlap values and the restriction
uses `Set.range b`.
-/

namespace Set

variable {X : Type*} {Y : Type*} {X' : Type*} {Y' : Type*}

/-- A map commuting with observations sends the image of the source observation into the image
of the target observation. -/
theorem mapsTo_range_range {f : X → Y} {f' : X' → Y'} {a : X → X'} {b : Y → Y'}
    (h : ∀ x, f' (a x) = b (f x)) : MapsTo f' (range a) (range b) :=
  mapsTo_range_iff.2 fun x => ⟨f x, (h x).symm⟩

/-- The preimage of a point of the image under the range factorization is the preimage of its
underlying value. -/
theorem rangeFactorization_preimage_singleton (f : X → Y) (y : range f) :
    rangeFactorization f ⁻¹' {y} = f ⁻¹' {y.1} :=
  Set.ext fun _ => Subtype.ext_iff

end Set

namespace Function.Pullback

variable {L : Type*} {R : Type*} {B : Type*} {p : L → B} {q : R → B}
  {L' : Type*} {R' : Type*} {B' : Type*} {p' : L' → B'} {q' : R' → B'}
  {a : L → L'} {b : B → B'} {c : R → R'}
  (ha : ∀ l, p' (a l) = b (p l)) (hc : ∀ r, q' (c r) = b (q r))

/-! ### The observed comparison -/

/-- The observed comparison `(l, r) ↦ (a l, c r)` of a commuting pair of span maps, as the lift
of `a ∘ fst` and `c ∘ snd`. -/
def map : p.Pullback q → p'.Pullback q' :=
  lift (a ∘ fst) (c ∘ snd) fun s => (ha s.fst).trans ((congrArg b s.comm).trans (hc s.snd).symm)

/-- `map` is mathlib's `Function.mapPullback` for the composite commutation laws. -/
theorem map_eq_mapPullback : map ha hc = mapPullback a b c (funext ha) (funext hc) :=
  rfl

/-- The left observed component of a mapped pair. -/
@[simp] theorem fst_map (s : p.Pullback q) : (map ha hc s).fst = a s.fst := rfl

/-- The right observed component of a mapped pair. -/
@[simp] theorem snd_map (s : p.Pullback q) : (map ha hc s).snd = c s.snd := rfl

/-- `map` on a constructed pair. -/
@[simp] theorem map_mk (l : L) (r : R) (h : p l = q r) :
    map ha hc (mk l r h) = mk (a l) (c r) ((ha l).trans ((congrArg b h).trans (hc r).symm)) :=
  rfl

/-- A fine pair lies over `t` exactly when both observed components are those of `t`. -/
theorem map_eq_iff {s : p.Pullback q} {t : p'.Pullback q'} :
    map ha hc s = t ↔ a s.fst = t.fst ∧ c s.snd = t.snd :=
  lift_eq_iff

/-- Two fine pairs have the same observed pair exactly when both observed components agree. -/
theorem map_eq_map_iff {s s' : p.Pullback q} :
    map ha hc s = map ha hc s' ↔ a s.fst = a s'.fst ∧ c s.snd = c s'.snd :=
  lift_eq_lift_iff

variable {G : Type*} {f : G → L} {g : G → R} {h : ∀ x, p (f x) = q (g x)}

/-- The observed image of a global realization is the lift of the observed local views. -/
theorem map_lift (x : G) :
    map ha hc (lift f g h x) =
      lift (a ∘ f) (c ∘ g) (fun x => (ha _).trans ((congrArg b (h x)).trans (hc _).symm)) x :=
  rfl

/-- The identity observation induces the identity comparison. -/
theorem map_id :
    map (p := p) (q := q) (a := id) (b := id) (c := id) (fun _ => rfl) (fun _ => rfl) = id :=
  rfl

variable {L'' : Type*} {R'' : Type*} {B'' : Type*} {p'' : L'' → B''} {q'' : R'' → B''}
  {a' : L' → L''} {b' : B' → B''} {c' : R' → R''}
  (ha' : ∀ l, p'' (a' l) = b' (p' l)) (hc' : ∀ r, q'' (c' r) = b' (q' r))

/-- Observing twice is observing along the composite. -/
theorem map_map (s : p.Pullback q) :
    map ha' hc' (map ha hc s) =
      map (b := b' ∘ b) (fun l => (ha' (a l)).trans (congrArg b' (ha l)))
        (fun r => (hc' (c r)).trans (congrArg b' (hc r))) s :=
  rfl

/-! ### The observed quotient -/

/-- Observed equality of fine pairs is the kernel of `map`: both observed components agree. -/
theorem observed_rel_iff (s s' : p.Pullback q) :
    Setoid.ker (map ha hc) s s' ↔ a s.fst = a s'.fst ∧ c s.snd = c s'.snd :=
  map_eq_map_iff ha hc

/-- Observed equality is equality under `map`. -/
theorem observed_rel_iff_map_eq (s s' : p.Pullback q) :
    Setoid.ker (map ha hc) s s' ↔ map ha hc s = map ha hc s' :=
  Setoid.ker_def

/-- The quotient of fine compatible pairs by observed equality. -/
abbrev Observed : Type _ :=
  Quotient (Setoid.ker (map ha hc))

/-- Two fine pairs have the same observed class exactly when both observed components agree. -/
theorem observed_mk_eq_iff (s s' : p.Pullback q) :
    (Quotient.mk _ s : Observed ha hc) = Quotient.mk _ s' ↔
      a s.fst = a s'.fst ∧ c s.snd = c s'.snd :=
  Quotient.eq.trans (observed_rel_iff ha hc s s')

/-- The comparison induced on the observed quotient, `k_bar`. -/
def observedMap : Observed ha hc → p'.Pullback q' :=
  Setoid.kerLift (map ha hc)

/-- Factorization law: `observedMap` on a class is `map` on a representative. -/
@[simp] theorem observedMap_mk (s : p.Pullback q) :
    observedMap ha hc (Quotient.mk _ s) = map ha hc s :=
  rfl

/-- Function-level form of `observedMap_mk`. -/
theorem observedMap_comp_mk : observedMap ha hc ∘ Quotient.mk _ = map ha hc :=
  rfl

/-- The left observed component of a class. -/
@[simp] theorem fst_observedMap_mk (s : p.Pullback q) :
    (observedMap ha hc (Quotient.mk _ s)).fst = a s.fst :=
  rfl

/-- The right observed component of a class. -/
@[simp] theorem snd_observedMap_mk (s : p.Pullback q) :
    (observedMap ha hc (Quotient.mk _ s)).snd = c s.snd :=
  rfl

/-- The induced comparison is injective. -/
theorem observedMap_injective : Injective (observedMap ha hc) :=
  Setoid.kerLift_injective _

/-- The induced comparison and the raw comparison have the same image. -/
theorem range_observedMap : Set.range (observedMap ha hc) = Set.range (map ha hc) :=
  Setoid.range_kerLift_eq_range _

/-- The observed quotient is the common image of `map` and `observedMap`, by the first
isomorphism theorem for sets. -/
noncomputable def observedEquivRange : Observed ha hc ≃ Set.range (map ha hc) :=
  Setoid.quotientKerEquivRange _

/-- `observedEquivRange` on a class is `map` on a representative. -/
@[simp] theorem coe_observedEquivRange_mk (s : p.Pullback q) :
    (observedEquivRange ha hc (Quotient.mk _ s) : p'.Pullback q') = map ha hc s :=
  rfl

/-- `observedEquivRange` is `observedMap` on underlying pairs. -/
@[simp] theorem coe_observedEquivRange (x : Observed ha hc) :
    (observedEquivRange ha hc x : p'.Pullback q') = observedMap ha hc x :=
  rfl

/-- Round trip: `observedEquivRange.symm` after `observedEquivRange`. -/
theorem observedEquivRange_symm_apply_apply (x : Observed ha hc) :
    (observedEquivRange ha hc).symm (observedEquivRange ha hc x) = x :=
  (observedEquivRange ha hc).symm_apply_apply x

/-- Round trip: `observedEquivRange` after `observedEquivRange.symm`. -/
theorem observedEquivRange_apply_symm_apply (t : Set.range (map ha hc)) :
    observedEquivRange ha hc ((observedEquivRange ha hc).symm t) = t :=
  (observedEquivRange ha hc).apply_symm_apply t

/-- Every fiber of the induced comparison is a subsingleton: an observed class is unique. By
`range_observedMap` it is nonempty exactly when the raw fiber of `map` over `t` is, but it
identifies all fine lifts of `t`, so it asserts no uniqueness of those fine lifts. -/
theorem subsingleton_fiber_observedMap (t : p'.Pullback q') :
    Subsingleton {x // observedMap ha hc x = t} :=
  (injective_iff_subsingleton_fiber _).1 (observedMap_injective ha hc) t

/-! ### The image criterion -/

section Criterion

variable (t : p'.Pullback q')

/-- A coarse compatible pair is attained exactly when some fine compatible pair is observed as
it. -/
theorem mem_range_map_iff_exists :
    t ∈ Set.range (map ha hc) ↔ ∃ l r, a l = t.fst ∧ c r = t.snd ∧ p l = q r := by
  simp only [Set.mem_range, map_eq_iff, Subtype.exists, Prod.exists, fst_mk, snd_mk]
  exact ⟨fun ⟨l, r, hlr, hl, hr⟩ => ⟨l, r, hl, hr, hlr⟩,
    fun ⟨l, r, hl, hr, hlr⟩ => ⟨l, r, hlr, hl, hr⟩⟩

/-- A coarse compatible pair is attained exactly when some fine overlap value is restricted to
by a fine left view observed as `t.fst` and a fine right view observed as `t.snd`. -/
theorem mem_range_map_iff_exists_overlap :
    t ∈ Set.range (map ha hc) ↔
      ∃ β, (∃ l, a l = t.fst ∧ p l = β) ∧ ∃ r, c r = t.snd ∧ q r = β := by
  rw [mem_range_map_iff_exists]
  exact ⟨fun ⟨l, r, hl, hr, hlr⟩ => ⟨p l, ⟨l, hl, rfl⟩, ⟨r, hr, hlr.symm⟩⟩,
    fun ⟨_, ⟨l, hl, rfl⟩, ⟨r, hr, hr'⟩⟩ => ⟨l, r, hl, hr, hr'.symm⟩⟩

/-- The exact lifting criterion: a coarse compatible pair `t` is attained exactly when the fine
overlap values reached from left views observed as `t.fst` and from right views observed as
`t.snd` have a common element. -/
theorem mem_range_map_iff :
    t ∈ Set.range (map ha hc) ↔ (p '' (a ⁻¹' {t.fst}) ∩ q '' (c ⁻¹' {t.snd})).Nonempty := by
  rw [mem_range_map_iff_exists_overlap]
  simp only [Set.inter_nonempty, Set.mem_image, Set.mem_preimage, Set.mem_singleton_iff]

/-- The lifting criterion for the induced comparison. -/
theorem mem_range_observedMap_iff :
    t ∈ Set.range (observedMap ha hc) ↔
      (p '' (a ⁻¹' {t.fst}) ∩ q '' (c ⁻¹' {t.snd})).Nonempty := by
  rw [range_observedMap, mem_range_map_iff]

/-! ### Fine lifts of a coarse pair -/

/-- The fiber of `map` over `t` is the type of fine compatible pairs observed as `t`. -/
def fiberMapEquiv :
    {s // map ha hc s = t} ≃ {s : p.Pullback q // a s.fst = t.fst ∧ c s.snd = t.snd} :=
  fiberLiftEquiv t

/-- `fiberMapEquiv` is the identity on underlying fine pairs. -/
@[simp] theorem fiberMapEquiv_apply_coe (s : {s // map ha hc s = t}) :
    (fiberMapEquiv ha hc t s : p.Pullback q) = s :=
  rfl

/-- `fiberMapEquiv.symm` is the identity on underlying fine pairs. -/
@[simp] theorem fiberMapEquiv_symm_apply_coe
    (s : {s : p.Pullback q // a s.fst = t.fst ∧ c s.snd = t.snd}) :
    ((fiberMapEquiv ha hc t).symm s : p.Pullback q) = s :=
  rfl

/-- The fiber of `map` over `t` is the type of pairs of fine views satisfying the three
conditions: fine compatibility, left view observed as `t.fst`, right view observed as `t.snd`. -/
def fiberMapEquivProd :
    {s // map ha hc s = t} ≃ {x : L × R // p x.1 = q x.2 ∧ a x.1 = t.fst ∧ c x.2 = t.snd} where
  toFun s := ⟨(s.1.fst, s.1.snd), s.1.comm, ((map_eq_iff ha hc).1 s.2).1,
    ((map_eq_iff ha hc).1 s.2).2⟩
  invFun x := ⟨mk x.1.1 x.1.2 x.2.1, (map_eq_iff ha hc).2 ⟨x.2.2.1, x.2.2.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- `fiberMapEquivProd` forgets the compatibility proof. -/
@[simp] theorem fiberMapEquivProd_apply_coe (s : {s // map ha hc s = t}) :
    (fiberMapEquivProd ha hc t s : L × R) = (s.1.fst, s.1.snd) :=
  rfl

/-- `fiberMapEquivProd.symm` reassembles the compatible pair. -/
@[simp] theorem fiberMapEquivProd_symm_apply_coe
    (x : {x : L × R // p x.1 = q x.2 ∧ a x.1 = t.fst ∧ c x.2 = t.snd}) :
    ((fiberMapEquivProd ha hc t).symm x : p.Pullback q) = mk x.1.1 x.1.2 x.2.1 :=
  rfl

/-- The fiber of `map` over `t` is the pullback of `p` and `q` restricted to the fine views
observed as `t.fst` and `t.snd`: compatible pairs of fine lifts of the two components. -/
def fiberMapEquivPullback :
    {s // map ha hc s = t} ≃
      Function.Pullback (fun l : {l // a l = t.fst} => p l.1)
        fun r : {r // c r = t.snd} => q r.1 where
  toFun s := mk ⟨s.1.fst, ((map_eq_iff ha hc).1 s.2).1⟩ ⟨s.1.snd, ((map_eq_iff ha hc).1 s.2).2⟩
    s.1.comm
  invFun x := ⟨mk x.fst.1 x.snd.1 x.comm, (map_eq_iff ha hc).2 ⟨x.fst.2, x.snd.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The left fine lift of `fiberMapEquivPullback`. -/
@[simp] theorem fiberMapEquivPullback_apply_fst_coe (s : {s // map ha hc s = t}) :
    ((fiberMapEquivPullback ha hc t s).fst : L) = s.1.fst :=
  rfl

/-- The right fine lift of `fiberMapEquivPullback`. -/
@[simp] theorem fiberMapEquivPullback_apply_snd_coe (s : {s // map ha hc s = t}) :
    ((fiberMapEquivPullback ha hc t s).snd : R) = s.1.snd :=
  rfl

/-- `fiberMapEquivPullback.symm` pairs the two fine lifts. -/
@[simp] theorem fiberMapEquivPullback_symm_apply_coe
    (x : Function.Pullback (fun l : {l // a l = t.fst} => p l.1)
      fun r : {r // c r = t.snd} => q r.1) :
    ((fiberMapEquivPullback ha hc t).symm x : p.Pullback q) = mk x.fst.1 x.snd.1 x.comm :=
  rfl

/-- Existence of a fine lift of `t` is the lifting criterion at `t`. -/
theorem nonempty_fiber_map_iff :
    Nonempty {s // map ha hc s = t} ↔
      (p '' (a ⁻¹' {t.fst}) ∩ q '' (c ⁻¹' {t.snd})).Nonempty :=
  (nonempty_fiber_iff_mem_range _ t).trans (mem_range_map_iff ha hc t)

/-- `t` has no fine lift exactly when the lifting criterion fails at `t`. -/
theorem isEmpty_fiber_map_iff :
    IsEmpty {s // map ha hc s = t} ↔
      ¬ (p '' (a ⁻¹' {t.fst}) ∩ q '' (c ⁻¹' {t.snd})).Nonempty :=
  (isEmpty_fiber_iff_notMem_range _ t).trans (not_congr (mem_range_map_iff ha hc t))

/-- Uniqueness of fine lifts of `t`: any two fine compatible pairs observed as `t` coincide. This
is independent of existence and of the automatic uniqueness of the observed class. -/
theorem subsingleton_fiber_map_iff :
    Subsingleton {s // map ha hc s = t} ↔
      ∀ s s' : p.Pullback q, a s.fst = t.fst ∧ c s.snd = t.snd →
        a s'.fst = t.fst ∧ c s'.snd = t.snd → s = s' :=
  subsingleton_fiber_lift_iff _ t

/-- Unique existence of a fine lift of `t`. -/
theorem nonempty_unique_fiber_map_iff :
    Nonempty (Unique {s // map ha hc s = t}) ↔
      ∃! s : p.Pullback q, a s.fst = t.fst ∧ c s.snd = t.snd :=
  nonempty_unique_fiber_lift_iff _ t

end Criterion

/-! ### The lifting criterion and the inverse -/

/-- The raw comparison is surjective exactly when the lifting criterion holds at every coarse
compatible pair. -/
theorem surjective_map_iff :
    Surjective (map ha hc) ↔
      ∀ t : p'.Pullback q', (p '' (a ⁻¹' {t.fst}) ∩ q '' (c ⁻¹' {t.snd})).Nonempty :=
  forall_congr' fun t => Set.mem_range.symm.trans (mem_range_map_iff ha hc t)

/-- The induced comparison is surjective exactly when the raw comparison is. -/
theorem surjective_observedMap_iff_surjective_map :
    Surjective (observedMap ha hc) ↔ Surjective (map ha hc) := by
  rw [← Set.range_eq_univ, ← Set.range_eq_univ, range_observedMap]

/-- The induced comparison is surjective exactly when the lifting criterion holds at every
coarse compatible pair. -/
theorem surjective_observedMap_iff :
    Surjective (observedMap ha hc) ↔
      ∀ t : p'.Pullback q', (p '' (a ⁻¹' {t.fst}) ∩ q '' (c ⁻¹' {t.snd})).Nonempty :=
  (surjective_observedMap_iff_surjective_map ha hc).trans (surjective_map_iff ha hc)

/-- The induced comparison, being injective, is bijective exactly when it is surjective. -/
theorem bijective_observedMap_iff_surjective :
    Bijective (observedMap ha hc) ↔ Surjective (observedMap ha hc) :=
  ⟨And.right, fun hs => ⟨observedMap_injective ha hc, hs⟩⟩

/-- The induced comparison is bijective exactly when the raw comparison is surjective. -/
theorem bijective_observedMap_iff_surjective_map :
    Bijective (observedMap ha hc) ↔ Surjective (map ha hc) :=
  (bijective_observedMap_iff_surjective ha hc).trans
    (surjective_observedMap_iff_surjective_map ha hc)

/-- Exact lifting criterion: reduction and assembly agree, i.e. the observed quotient is all of
the coarse compatible pairs, exactly when every coarse compatible pair has a common fine overlap
value above it. -/
theorem bijective_observedMap_iff :
    Bijective (observedMap ha hc) ↔
      ∀ t : p'.Pullback q', (p '' (a ⁻¹' {t.fst}) ∩ q '' (c ⁻¹' {t.snd})).Nonempty :=
  (bijective_observedMap_iff_surjective ha hc).trans (surjective_observedMap_iff ha hc)

/-- A two-sided inverse of the induced comparison exists exactly under the lifting criterion. -/
theorem exists_inverse_observedMap_iff :
    (∃ i, LeftInverse i (observedMap ha hc) ∧ RightInverse i (observedMap ha hc)) ↔
      ∀ t : p'.Pullback q', (p '' (a ⁻¹' {t.fst}) ∩ q '' (c ⁻¹' {t.snd})).Nonempty :=
  bijective_iff_has_inverse.symm.trans (bijective_observedMap_iff ha hc)

/-- A right inverse of the induced comparison forces the lifting criterion everywhere. -/
theorem inter_nonempty_of_rightInverse (i : p'.Pullback q' → Observed ha hc)
    (hi : ∀ t, observedMap ha hc (i t) = t) (t : p'.Pullback q') :
    (p '' (a ⁻¹' {t.fst}) ∩ q '' (c ⁻¹' {t.snd})).Nonempty :=
  (surjective_observedMap_iff ha hc).1 (fun t => ⟨i t, hi t⟩) t

section Inverse

variable (h : ∀ t : p'.Pullback q', (p '' (a ⁻¹' {t.fst}) ∩ q '' (c ⁻¹' {t.snd})).Nonempty)

/-- Under the lifting criterion the observed quotient is equivalent to all coarse compatible
pairs. Its forward function is `observedMap` (`observedEquiv_apply`), so it extends the quotient
injection to all coarse compatible pairs; the inverse accepting a coarse pair is
`observedEquiv.symm`, obtained by classical choice from bijectivity. That inverse selects the
observed class over a coarse pair, not a fine representative, and asserts nothing about
uniqueness of fine lifts. -/
noncomputable def observedEquiv : Observed ha hc ≃ p'.Pullback q' :=
  Equiv.ofBijective _ ((bijective_observedMap_iff ha hc).2 h)

/-- The forward direction of `observedEquiv` is `observedMap`. -/
@[simp] theorem observedEquiv_apply (x : Observed ha hc) :
    observedEquiv ha hc h x = observedMap ha hc x :=
  rfl

/-- `observedEquiv` on a class is `map` on a representative. -/
theorem observedEquiv_mk (s : p.Pullback q) :
    observedEquiv ha hc h (Quotient.mk _ s) = map ha hc s :=
  rfl

/-- Round trip: `observedMap` after the inverse is the identity on coarse pairs. -/
@[simp] theorem observedMap_observedEquiv_symm (t : p'.Pullback q') :
    observedMap ha hc ((observedEquiv ha hc h).symm t) = t :=
  (observedEquiv ha hc h).apply_symm_apply t

/-- Round trip: the inverse after `observedMap` is the identity on observed classes. -/
@[simp] theorem observedEquiv_symm_observedMap (x : Observed ha hc) :
    (observedEquiv ha hc h).symm (observedMap ha hc x) = x :=
  (observedEquiv ha hc h).symm_apply_apply x

/-- The inverse is unique among right inverses of `observedMap`. -/
theorem eq_observedEquiv_symm_of_rightInverse (i : p'.Pullback q' → Observed ha hc)
    (hi : ∀ t, observedMap ha hc (i t) = t) : i = (observedEquiv ha hc h).symm :=
  funext fun t =>
    observedMap_injective ha hc ((hi t).trans (observedMap_observedEquiv_symm ha hc h t).symm)

/-- The inverse is unique among left inverses of `observedMap`, since `observedMap` is
surjective under the criterion. -/
theorem eq_observedEquiv_symm_of_leftInverse (i : p'.Pullback q' → Observed ha hc)
    (hi : ∀ x, i (observedMap ha hc x) = x) : i = (observedEquiv ha hc h).symm :=
  LeftInverse.eq_rightInverse hi (observedMap_observedEquiv_symm ha hc h)

end Inverse

/-! ### Injective overlap observation -/

section InjectiveOverlap

variable (hb : Injective b)
include hb

/-- With an injective overlap observation the lifting criterion is componentwise: a coarse
compatible pair is attained exactly when each component is observed. -/
theorem mem_range_map_iff_of_injective (t : p'.Pullback q') :
    t ∈ Set.range (map ha hc) ↔ t.fst ∈ Set.range a ∧ t.snd ∈ Set.range c := by
  rw [mem_range_map_iff_exists]
  constructor
  · rintro ⟨l, r, hl, hr, -⟩
    exact ⟨⟨l, hl⟩, ⟨r, hr⟩⟩
  · rintro ⟨⟨l, hl⟩, ⟨r, hr⟩⟩
    exact ⟨l, r, hl, hr, hb ((ha l).symm.trans ((congrArg p' hl).trans
      (t.comm.trans ((congrArg q' hr).symm.trans (hc r)))))⟩

/-- Sufficient special case: an injective overlap observation and surjective local observations
make the induced comparison bijective. The exact criterion is `bijective_observedMap_iff`. -/
theorem bijective_observedMap_of_injective (hsa : Surjective a) (hsc : Surjective c) :
    Bijective (observedMap ha hc) :=
  (bijective_observedMap_iff_surjective_map ha hc).2 fun t =>
    (mem_range_map_iff_of_injective ha hc hb t).2 ⟨hsa t.fst, hsc t.snd⟩

end InjectiveOverlap

/-! ### Restriction of observations to their images -/

section Restrict

/-- The coarse leg restricted to the images of the observations: `p'` maps `Set.range a` into
`Set.range b`. -/
def rangeRestrict {X : Type*} {Y : Type*} {X' : Type*} {Y' : Type*} {f : X → Y} {f' : X' → Y'}
    {a : X → X'} {b : Y → Y'} (h : ∀ x, f' (a x) = b (f x)) : Set.range a → Set.range b :=
  (Set.mapsTo_range_range h).restrict f' _ _

/-- `rangeRestrict` is the original map on underlying values. -/
@[simp] theorem coe_rangeRestrict {X : Type*} {Y : Type*} {X' : Type*} {Y' : Type*}
    {f : X → Y} {f' : X' → Y'} {a : X → X'} {b : Y → Y'} (h : ∀ x, f' (a x) = b (f x))
    (x : Set.range a) : (rangeRestrict h x : Y') = f' x :=
  rfl

/-- The range factorizations commute with the restricted coarse leg: the restricted square
commutes pointwise. -/
theorem rangeFactorization_comm {X : Type*} {Y : Type*} {X' : Type*} {Y' : Type*}
    {f : X → Y} {f' : X' → Y'} {a : X → X'} {b : Y → Y'} (h : ∀ x, f' (a x) = b (f x)) (x : X) :
    rangeRestrict h (Set.rangeFactorization a x) = Set.rangeFactorization b (f x) :=
  Subtype.ext (h x)

/-- The observed comparison of the restricted system, whose observation maps
`Set.rangeFactorization a`, `Set.rangeFactorization b`, `Set.rangeFactorization c` are
surjective by `Set.rangeFactorization_surjective`. -/
abbrev mapRangeFactorization :
    p.Pullback q → (rangeRestrict ha).Pullback (rangeRestrict hc) :=
  map (rangeFactorization_comm ha) (rangeFactorization_comm hc)

/-- The inclusion of the restricted coarse compatible pairs into all coarse compatible pairs. -/
abbrev rangeInclusion : (rangeRestrict ha).Pullback (rangeRestrict hc) → p'.Pullback q' :=
  map (a := Subtype.val) (b := Subtype.val) (c := Subtype.val) (fun _ => rfl) fun _ => rfl

/-- The original comparison factors through the restricted system. -/
theorem rangeInclusion_mapRangeFactorization (s : p.Pullback q) :
    rangeInclusion ha hc (mapRangeFactorization ha hc s) = map ha hc s :=
  rfl

/-- The lifting criterion of the restricted system at a restricted coarse pair is the lifting
criterion of the original system at its underlying coarse pair. -/
theorem inter_nonempty_rangeFactorization_iff
    (t : (rangeRestrict ha).Pullback (rangeRestrict hc)) :
    (p '' (Set.rangeFactorization a ⁻¹' {t.fst}) ∩
        q '' (Set.rangeFactorization c ⁻¹' {t.snd})).Nonempty ↔
      (p '' (a ⁻¹' {(rangeInclusion ha hc t).fst}) ∩
        q '' (c ⁻¹' {(rangeInclusion ha hc t).snd})).Nonempty := by
  rw [Set.rangeFactorization_preimage_singleton, Set.rangeFactorization_preimage_singleton]
  rfl

/-- A restricted coarse pair is attained in the restricted system exactly when its underlying
coarse pair is attained in the original system. -/
theorem mem_range_mapRangeFactorization_iff
    (t : (rangeRestrict ha).Pullback (rangeRestrict hc)) :
    t ∈ Set.range (mapRangeFactorization ha hc) ↔
      rangeInclusion ha hc t ∈ Set.range (map ha hc) := by
  rw [mem_range_map_iff, mem_range_map_iff, inter_nonempty_rangeFactorization_iff]

end Restrict

end Function.Pullback
