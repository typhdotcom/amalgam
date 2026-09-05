import Amalgam.Core.Fiber
import Mathlib.Data.Set.Prod

/-!
# Compatible pairs and the comparison map of a commuting square

For a span `L ─p→ B ←q─ R` of arbitrary types, the compatible local pairs are
mathlib's fiber product `Function.Pullback p q`, the subtype of `L × R` on
which `p` and `q` agree, with projections `Function.Pullback.fst` and
`Function.Pullback.snd`. A commuting square `f : G → L`, `g : G → R`,
`p ∘ f = q ∘ g` induces the comparison map `Function.Pullback.lift f g h`,
and the fiber of a map `k` over `c` is the subtype `{x // k x = c}`.

## Main results

* `Function.Pullback.mk`, `ext` (with the generated `ext_iff`), `comm`: the
  constructor, extensionality, and overlap law of compatible pairs.
* `Function.Pullback.lift`, `fst_lift`, `snd_lift`, `lift_unique`: the
  universal map into the pullback and its universal property.
* `Function.Pullback.fiberLiftEquiv`: the fiber of the comparison over a
  compatible pair `c` is the type of global states restricting to `c`.
* `isEmpty_fiber_lift_iff`, `nonempty_fiber_lift_iff`,
  `subsingleton_fiber_lift_iff`, `nonempty_unique_fiber_lift_iff`: pointwise
  existence and uniqueness of global extensions.
* `injective_lift_iff`, `surjective_lift_iff`, `bijective_lift_iff` and the
  `_forall_` variants: global uniqueness, existence, and unique existence,
  and their equivalence with the pointwise fiber conditions.
* `fiberFstEquiv`, `fiberSndEquiv`: fibers of the projections are fibers of
  the opposite leg.
* `swap`, `congr`, `equivProdOfSubsingleton`: symmetry, transport along
  coherent equivalences of the span, and the trivial-overlap product.

## Conventions

Empty types and empty fibers are allowed throughout. No finiteness,
decidability, or surjectivity hypotheses appear. A pointwise commutation
proof `h : ∀ x, p (f x) = q (g x)` is the primitive form; the composite form
`p ∘ f = q ∘ g` reduces to it by `congr_fun`. Squares and coherent
equivalences of squares stay unbundled, matching `Function.mapPullback`: a
structure would only shorten the argument lists of the transport corollaries.
-/

namespace Function.Pullback

variable {L : Type*} {R : Type*} {B : Sort*} {p : L → B} {q : R → B}

/-! ### Compatible pairs -/

/-- The compatible pair `(l, r)` witnessed by `h : p l = q r`. -/
abbrev mk (l : L) (r : R) (h : p l = q r) : p.Pullback q := ⟨(l, r), h⟩

/-- The first projection of a constructed pair. -/
@[simp] theorem fst_mk (l : L) (r : R) (h : p l = q r) : (mk l r h).fst = l := rfl

/-- The second projection of a constructed pair. -/
@[simp] theorem snd_mk (l : L) (r : R) (h : p l = q r) : (mk l r h).snd = r := rfl

/-- The two local views of a compatible pair agree on the overlap. -/
theorem comm (c : p.Pullback q) : p c.fst = q c.snd := c.2

/-- A compatible pair is the pair of its projections. -/
@[simp] theorem mk_fst_snd (c : p.Pullback q) : mk c.fst c.snd c.comm = c := rfl

/-- Compatible pairs are determined by their two projections. -/
@[ext] theorem ext {c d : p.Pullback q} (h₁ : c.fst = d.fst) (h₂ : c.snd = d.snd) : c = d :=
  Subtype.ext (Prod.ext h₁ h₂)

/-- Constructed pairs are equal exactly when their components are. -/
@[simp] theorem mk_eq_mk {l l' : L} {r r' : R} {h : p l = q r} {h' : p l' = q r'} :
    mk l r h = mk l' r' h' ↔ l = l' ∧ r = r' :=
  Pullback.ext_iff

/-! ### The comparison map -/

variable {G : Type*}

/-- The comparison map of a commuting square: the universal map `G → p.Pullback q` induced by
`f : G → L`, `g : G → R`, and `h : ∀ x, p (f x) = q (g x)`. -/
def lift (f : G → L) (g : G → R) (h : ∀ x, p (f x) = q (g x)) (x : G) : p.Pullback q :=
  mk (f x) (g x) (h x)

variable {f : G → L} {g : G → R} {h : ∀ x, p (f x) = q (g x)}

/-- Projection law: the first component of the comparison is `f`. -/
@[simp] theorem fst_lift (x : G) : (lift f g h x).fst = f x := rfl

/-- Projection law: the second component of the comparison is `g`. -/
@[simp] theorem snd_lift (x : G) : (lift f g h x).snd = g x := rfl

/-- Function-level form of `fst_lift`. -/
theorem fst_comp_lift : fst ∘ lift f g h = f := rfl

/-- Function-level form of `snd_lift`. -/
theorem snd_comp_lift : snd ∘ lift f g h = g := rfl

/-- A global state lies over `c` exactly when both local views restrict to `c`. -/
theorem lift_eq_iff {x : G} {c : p.Pullback q} : lift f g h x = c ↔ f x = c.fst ∧ g x = c.snd :=
  Pullback.ext_iff

/-- Two global states have the same comparison value exactly when both local views agree. -/
theorem lift_eq_lift_iff {x y : G} : lift f g h x = lift f g h y ↔ f x = f y ∧ g x = g y :=
  Pullback.ext_iff

/-- Two maps into the pullback agree when their projections do. -/
theorem hom_ext {u v : G → p.Pullback q} (h₁ : ∀ x, (u x).fst = (v x).fst)
    (h₂ : ∀ x, (u x).snd = (v x).snd) : u = v :=
  funext fun x => ext (h₁ x) (h₂ x)

/-- Uniqueness half of the universal property: `lift f g h` is the only map with projections
`f` and `g`. -/
theorem lift_unique (u : G → p.Pullback q) (hf : ∀ x, (u x).fst = f x)
    (hg : ∀ x, (u x).snd = g x) : u = lift f g h :=
  hom_ext hf hg

/-- Every map into the pullback is the lift of its projections. -/
theorem lift_fst_snd (u : G → p.Pullback q) : lift (fst ∘ u) (snd ∘ u) (fun x => (u x).comm) = u :=
  rfl

/-- Precomposition commutes with `lift`. -/
theorem lift_comp {G' : Type*} (k : G' → G) :
    lift f g h ∘ k = lift (f ∘ k) (g ∘ k) fun x => h (k x) :=
  rfl

/-! ### Fibers of the comparison map are global extensions -/

/-- The fiber of the comparison over `c` is the type of global states restricting to `c`. -/
def fiberLiftEquiv (c : p.Pullback q) :
    {x // lift f g h x = c} ≃ {x // f x = c.fst ∧ g x = c.snd} :=
  Equiv.subtypeEquivRight fun _ => lift_eq_iff

/-- `fiberLiftEquiv` is the identity on underlying global states. -/
@[simp] theorem fiberLiftEquiv_apply_coe (c : p.Pullback q) (x : {x // lift f g h x = c}) :
    (fiberLiftEquiv c x : G) = x :=
  rfl

/-- `fiberLiftEquiv.symm` is the identity on underlying global states. -/
@[simp] theorem fiberLiftEquiv_symm_apply_coe (c : p.Pullback q)
    (x : {x // f x = c.fst ∧ g x = c.snd}) : ((fiberLiftEquiv (h := h) c).symm x : G) = x :=
  rfl

section Pointwise

variable (h) (c : p.Pullback q)

/-- Globalization fails at `c` exactly when no global state restricts to `c`. -/
theorem isEmpty_fiber_lift_iff :
    IsEmpty {x // lift f g h x = c} ↔ ¬ ∃ x, f x = c.fst ∧ g x = c.snd := by
  simp [isEmpty_subtype, lift_eq_iff]

/-- A global extension of `c` exists exactly when some global state restricts to `c`. -/
theorem nonempty_fiber_lift_iff :
    Nonempty {x // lift f g h x = c} ↔ ∃ x, f x = c.fst ∧ g x = c.snd := by
  simp [nonempty_subtype, lift_eq_iff]

/-- Global extensions of `c` are unique when they exist exactly when any two global states
restricting to `c` coincide. -/
theorem subsingleton_fiber_lift_iff :
    Subsingleton {x // lift f g h x = c} ↔
      ∀ x y, f x = c.fst ∧ g x = c.snd → f y = c.fst ∧ g y = c.snd → x = y := by
  simp only [subsingleton_iff, Subtype.forall, Subtype.mk.injEq, lift_eq_iff]
  exact ⟨fun H x y hx hy => H x hx y hy, fun H x hx y hy => H x y hx hy⟩

/-- `c` has exactly one global extension exactly when exactly one global state restricts to it. -/
theorem nonempty_unique_fiber_lift_iff :
    Nonempty (Unique {x // lift f g h x = c}) ↔ ∃! x, f x = c.fst ∧ g x = c.snd := by
  simp only [unique_subtype_iff_existsUnique, lift_eq_iff]

/-- Unique existence over `c`, in `∃!` form. -/
theorem existsUnique_lift_eq_iff : (∃! x, lift f g h x = c) ↔ ∃! x, f x = c.fst ∧ g x = c.snd := by
  simp only [lift_eq_iff]

end Pointwise

/-! ### Global criteria -/

section Global

variable (h)

/-- Injectivity of the comparison is joint separation by the local views. -/
theorem injective_lift_iff : Injective (lift f g h) ↔ ∀ x y, f x = f y → g x = g y → x = y := by
  simp only [Injective, lift_eq_lift_iff, and_imp]

/-- Injectivity of the comparison is uniqueness of global extensions over every compatible pair. -/
theorem injective_lift_iff_forall_subsingleton :
    Injective (lift f g h) ↔ ∀ c, Subsingleton {x // lift f g h x = c} :=
  injective_iff_subsingleton_fiber (lift f g h)

/-- Surjectivity of the comparison is existence of a global state over every compatible pair. -/
theorem surjective_lift_iff :
    Surjective (lift f g h) ↔ ∀ l r, p l = q r → ∃ x, f x = l ∧ g x = r := by
  simp only [Surjective, lift_eq_iff]
  exact ⟨fun hs l r hlr => hs (mk l r hlr), fun hs c => hs c.fst c.snd c.comm⟩

/-- Surjectivity of the comparison is existence of global extensions over every compatible pair. -/
theorem surjective_lift_iff_forall_nonempty :
    Surjective (lift f g h) ↔ ∀ c, Nonempty {x // lift f g h x = c} :=
  surjective_iff_nonempty_fiber (lift f g h)

/-- Bijectivity of the comparison is joint separation together with joint attainment. -/
theorem bijective_lift_iff :
    Bijective (lift f g h) ↔
      (∀ x y, f x = f y → g x = g y → x = y) ∧ ∀ l r, p l = q r → ∃ x, f x = l ∧ g x = r :=
  and_congr (injective_lift_iff h) (surjective_lift_iff h)

/-- Bijectivity of the comparison is unique existence of a global state over every compatible
pair. -/
theorem bijective_lift_iff_existsUnique :
    Bijective (lift f g h) ↔ ∀ l r, p l = q r → ∃! x, f x = l ∧ g x = r := by
  rw [bijective_iff_existsUnique]
  simp only [lift_eq_iff]
  exact ⟨fun hs l r hlr => hs (mk l r hlr), fun hs c => hs c.fst c.snd c.comm⟩

/-- Bijectivity of the comparison is unique existence of global extensions over every compatible
pair. -/
theorem bijective_lift_iff_forall_nonempty_unique :
    Bijective (lift f g h) ↔ ∀ c, Nonempty (Unique {x // lift f g h x = c}) :=
  bijective_iff_nonempty_unique_fiber (lift f g h)

end Global

/-! ### Fibers of the projections -/

/-- The fiber of `fst` over `l` is the fiber of `q` over `p l`. -/
def fiberFstEquiv (l : L) : {c : p.Pullback q // c.fst = l} ≃ {r // q r = p l} where
  toFun c := ⟨c.1.snd, c.1.comm.symm.trans (congrArg p c.2)⟩
  invFun r := ⟨mk l r r.2.symm, rfl⟩
  left_inv c := Subtype.ext (ext c.2.symm rfl)
  right_inv _ := rfl

/-- `fiberFstEquiv` sends a pair over `l` to its second component. -/
@[simp] theorem fiberFstEquiv_apply_coe (l : L) (c : {c : p.Pullback q // c.fst = l}) :
    (fiberFstEquiv l c : R) = c.1.snd :=
  rfl

/-- `fiberFstEquiv.symm` pairs `l` with a point of the opposite fiber. -/
@[simp] theorem fiberFstEquiv_symm_apply_coe (l : L) (r : {r // q r = p l}) :
    ((fiberFstEquiv (p := p) (q := q) l).symm r).1 = mk l r.1 r.2.symm :=
  rfl

/-- The fiber of `snd` over `r` is the fiber of `p` over `q r`. -/
def fiberSndEquiv (r : R) : {c : p.Pullback q // c.snd = r} ≃ {l // p l = q r} where
  toFun c := ⟨c.1.fst, c.1.comm.trans (congrArg q c.2)⟩
  invFun l := ⟨mk l r l.2, rfl⟩
  left_inv c := Subtype.ext (ext rfl c.2.symm)
  right_inv _ := rfl

/-- `fiberSndEquiv` sends a pair over `r` to its first component. -/
@[simp] theorem fiberSndEquiv_apply_coe (r : R) (c : {c : p.Pullback q // c.snd = r}) :
    (fiberSndEquiv r c : L) = c.1.fst :=
  rfl

/-- `fiberSndEquiv.symm` pairs a point of the opposite fiber with `r`. -/
@[simp] theorem fiberSndEquiv_symm_apply_coe (r : R) (l : {l // p l = q r}) :
    ((fiberSndEquiv (p := p) (q := q) r).symm l).1 = mk l.1 r l.2 :=
  rfl

/-! ### Symmetry -/

/-- Exchanging the two local views. -/
def swap : p.Pullback q ≃ q.Pullback p where
  toFun c := mk c.snd c.fst c.comm.symm
  invFun c := mk c.snd c.fst c.comm.symm
  left_inv _ := rfl
  right_inv _ := rfl

/-- The first projection after `swap` is the old second projection. -/
@[simp] theorem fst_swap (c : p.Pullback q) : (swap c).fst = c.snd := rfl

/-- The second projection after `swap` is the old first projection. -/
@[simp] theorem snd_swap (c : p.Pullback q) : (swap c).snd = c.fst := rfl

/-- `swap` on a constructed pair. -/
@[simp] theorem swap_mk (l : L) (r : R) (h : p l = q r) : swap (mk l r h) = mk r l h.symm := rfl

/-- `swap` is its own inverse. -/
@[simp] theorem swap_symm : (swap (p := p) (q := q)).symm = swap := rfl

/-- `swap` is an involution. -/
@[simp] theorem swap_swap (c : p.Pullback q) : swap (swap c) = c := rfl

/-- `swap` exchanges the two legs of the comparison map. -/
theorem swap_lift (x : G) : swap (lift f g h x) = lift g f (fun x => (h x).symm) x := rfl

/-- Function-level form of `swap_lift`. -/
theorem swap_comp_lift : swap ∘ lift f g h = lift g f fun x => (h x).symm := rfl

/-! ### Transport along coherent equivalences -/

section Congr

variable {L' : Type*} {R' : Type*} {B' : Sort*} {p' : L' → B'} {q' : R' → B'}
  (eL : L ≃ L') (eR : R ≃ R') (eB : B ≃ B')
  (hp : ∀ l, p' (eL l) = eB (p l)) (hq : ∀ r, q' (eR r) = eB (q r))

/-- Transport of compatible pairs along equivalences of the span commuting with `p` and `q`. -/
def congr : p.Pullback q ≃ p'.Pullback q' :=
  Equiv.subtypeEquiv (eL.prodCongr eR) fun c => by
    simp only [Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd, hp, hq, eB.injective.eq_iff]

/-- `congr` transports the first projection along `eL`. -/
@[simp] theorem fst_congr (c : p.Pullback q) : (congr eL eR eB hp hq c).fst = eL c.fst := rfl

/-- `congr` transports the second projection along `eR`. -/
@[simp] theorem snd_congr (c : p.Pullback q) : (congr eL eR eB hp hq c).snd = eR c.snd := rfl

/-- `congr` on a constructed pair. -/
@[simp] theorem congr_mk (l : L) (r : R) (h : p l = q r) :
    congr eL eR eB hp hq (mk l r h) = mk (eL l) (eR r) (by rw [hp, hq, h]) :=
  rfl

/-- `congr.symm` transports the first projection along `eL.symm`. -/
@[simp] theorem fst_congr_symm (c : p'.Pullback q') :
    ((congr eL eR eB hp hq).symm c).fst = eL.symm c.fst :=
  rfl

/-- `congr.symm` transports the second projection along `eR.symm`. -/
@[simp] theorem snd_congr_symm (c : p'.Pullback q') :
    ((congr eL eR eB hp hq).symm c).snd = eR.symm c.snd :=
  rfl

variable {G' : Type*} {f' : G' → L'} {g' : G' → R'} {h' : ∀ x, p' (f' x) = q' (g' x)}
  (eG : G ≃ G') (hf : ∀ x, f' (eG x) = eL (f x)) (hg : ∀ x, g' (eG x) = eR (g x))

include hf hg in
/-- Naturality of the comparison map under a coherent equivalence of squares. -/
theorem congr_lift (x : G) :
    congr eL eR eB hp hq (lift f g h x) = lift f' g' h' (eG x) :=
  ext (hf x).symm (hg x).symm

include hf hg in
/-- Function-level form of `congr_lift`. -/
theorem congr_comp_lift : congr eL eR eB hp hq ∘ lift f g h = lift f' g' h' ∘ eG :=
  funext (congr_lift eL eR eB hp hq eG hf hg)

include hf hg in
/-- Fibers of the comparison map correspond under a coherent equivalence of squares. -/
def fiberLiftCongr (c : p.Pullback q) :
    {x // lift f g h x = c} ≃ {x' // lift f' g' h' x' = congr eL eR eB hp hq c} :=
  Equiv.fiberCongr eG (congr eL eR eB hp hq)
    (fun x => (congr_lift eL eR eB hp hq eG hf hg x).symm) c

/-- `fiberLiftCongr` acts as `eG` on underlying global states. -/
@[simp] theorem fiberLiftCongr_apply_coe (c : p.Pullback q) (x : {x // lift f g h x = c}) :
    (fiberLiftCongr (h' := h') eL eR eB hp hq eG hf hg c x : G') = eG x :=
  rfl

/-- `fiberLiftCongr.symm` acts as `eG.symm` on underlying global states. -/
@[simp] theorem fiberLiftCongr_symm_apply_coe (c : p.Pullback q)
    (x : {x' // lift f' g' h' x' = congr eL eR eB hp hq c}) :
    ((fiberLiftCongr (h := h) (h' := h') eL eR eB hp hq eG hf hg c).symm x : G) = eG.symm x :=
  rfl

include eB hp hq hf hg in
/-- Injectivity of the comparison is invariant under coherent equivalence of squares. -/
theorem injective_lift_iff_of_congr : Injective (lift f' g' h') ↔ Injective (lift f g h) := by
  rw [← (congr eL eR eB hp hq).comp_injective, congr_comp_lift eL eR eB hp hq eG hf hg,
    eG.injective_comp]

include eB hp hq hf hg in
/-- Surjectivity of the comparison is invariant under coherent equivalence of squares. -/
theorem surjective_lift_iff_of_congr : Surjective (lift f' g' h') ↔ Surjective (lift f g h) := by
  rw [← (congr eL eR eB hp hq).comp_surjective, congr_comp_lift eL eR eB hp hq eG hf hg,
    eG.surjective_comp]

include eB hp hq hf hg in
/-- Bijectivity of the comparison is invariant under coherent equivalence of squares. -/
theorem bijective_lift_iff_of_congr : Bijective (lift f' g' h') ↔ Bijective (lift f g h) := by
  rw [← (congr eL eR eB hp hq).comp_bijective, congr_comp_lift eL eR eB hp hq eG hf hg,
    eG.bijective_comp]

end Congr

/-! ### Trivial overlap -/

section Subsingleton

variable [Subsingleton B]

/-- Over a subsingleton overlap every pair is compatible. -/
def equivProdOfSubsingleton : p.Pullback q ≃ L × R where
  toFun c := (c.fst, c.snd)
  invFun x := mk x.1 x.2 (Subsingleton.elim _ _)
  left_inv _ := rfl
  right_inv _ := rfl

/-- `equivProdOfSubsingleton` forgets the compatibility proof. -/
@[simp] theorem equivProdOfSubsingleton_apply (c : p.Pullback q) :
    equivProdOfSubsingleton c = (c.fst, c.snd) :=
  rfl

/-- The first projection of a pair reconstructed over a trivial overlap. -/
@[simp] theorem fst_equivProdOfSubsingleton_symm (x : L × R) :
    ((equivProdOfSubsingleton (p := p) (q := q)).symm x).fst = x.1 :=
  rfl

/-- The second projection of a pair reconstructed over a trivial overlap. -/
@[simp] theorem snd_equivProdOfSubsingleton_symm (x : L × R) :
    ((equivProdOfSubsingleton (p := p) (q := q)).symm x).snd = x.2 :=
  rfl

/-- Over a trivial overlap the comparison is the joint map `x ↦ (f x, g x)`. -/
theorem equivProdOfSubsingleton_lift (x : G) :
    equivProdOfSubsingleton (lift f g h x) = (f x, g x) :=
  rfl

/-- Function-level form of `equivProdOfSubsingleton_lift`. -/
theorem equivProdOfSubsingleton_comp_lift :
    equivProdOfSubsingleton ∘ lift f g h = fun x => (f x, g x) :=
  rfl

variable (h)

/-- Over a trivial overlap the comparison is injective exactly when the joint map is. -/
theorem injective_lift_iff_of_subsingleton :
    Injective (lift f g h) ↔ Injective fun x => (f x, g x) := by
  rw [← equivProdOfSubsingleton.comp_injective, equivProdOfSubsingleton_comp_lift]

/-- Over a trivial overlap the comparison is surjective exactly when the joint map is. -/
theorem surjective_lift_iff_of_subsingleton :
    Surjective (lift f g h) ↔ Surjective fun x => (f x, g x) := by
  rw [← equivProdOfSubsingleton.comp_surjective, equivProdOfSubsingleton_comp_lift]

/-- Over a trivial overlap the comparison is bijective exactly when the joint map is. -/
theorem bijective_lift_iff_of_subsingleton :
    Bijective (lift f g h) ↔ Bijective fun x => (f x, g x) := by
  rw [← equivProdOfSubsingleton.comp_bijective, equivProdOfSubsingleton_comp_lift]

end Subsingleton

end Function.Pullback
