import Amalgam.Core.Comparison
import Amalgam.Core.Fiber
import Amalgam.Core.Reduction
import Amalgam.Models.Lifting
import Amalgam.Models.Overlap
import Amalgam.Models.Span
import Amalgam.Models.Zigzag
import Amalgam.System.Binary
import Amalgam.System.Comparison
import Amalgam.System.Presentation
import Amalgam.System.Restriction

/-!
# Status manifest

Every load-bearing mathematical claim `README.md` makes is restated here as an `example` with an
explicit type. Renaming, weakening, or deleting a result breaks this file, which is what makes
stale prose detectable. Generic claims are mirrored at the generality the README advertises:
arbitrary types in arbitrary universes, no finiteness and no decidability. Concrete claims are
mirrored on the concrete squares that carry them.

No library module imports this file; only the root `Amalgam` aggregator does, so the manifest
compiles with every build.

The section headings match the README headings.
-/

universe uX uY uZ uX' uY' uL' uR' uG' uB' uLf uRf uBf uLc uRc uBc uC uS uS' uI uK uM

namespace Amalgam.Status

/-! ## Fibers -/

section Fiber

variable {X : Type uX} {Y : Type uY} {Z : Type uZ} {X' : Type uX'} {Y' : Type uY'}

/-- The source is the dependent sum of the fibers. -/
example (f : X → Y) : (Σ y : Y, {x // f x = y}) ≃ X :=
  Equiv.sigmaFiberEquiv f

/-- The decomposition is the identity on underlying points. -/
example (f : X → Y) (y : Y) (x : {x // f x = y}) : Equiv.sigmaFiberEquiv f ⟨y, x⟩ = x :=
  Equiv.sigmaFiberEquiv_mk f y x

/-- A fiber is nonempty exactly over a reached value. -/
example (f : X → Y) (y : Y) : Nonempty {x // f x = y} ↔ y ∈ Set.range f :=
  Function.nonempty_fiber_iff_mem_range f y

/-- A fiber is empty exactly over a missed value. -/
example (f : X → Y) (y : Y) : IsEmpty {x // f x = y} ↔ y ∉ Set.range f :=
  Function.isEmpty_fiber_iff_notMem_range f y

/-- A fiber is a subsingleton exactly when the value has at most one preimage. -/
example (f : X → Y) (y : Y) :
    Subsingleton {x // f x = y} ↔ ∀ x x', f x = y → f x' = y → x = x' :=
  Function.subsingleton_fiber_iff f y

/-- Injectivity is subsingleton fibers. -/
example (f : X → Y) : Function.Injective f ↔ ∀ y, Subsingleton {x // f x = y} :=
  Function.injective_iff_subsingleton_fiber f

/-- Surjectivity is nonempty fibers. -/
example (f : X → Y) : Function.Surjective f ↔ ∀ y, Nonempty {x // f x = y} :=
  Function.surjective_iff_nonempty_fiber f

/-- Bijectivity is fibers with a unique element. -/
example (f : X → Y) : Function.Bijective f ↔ ∀ y, Nonempty (Unique {x // f x = y}) :=
  Function.bijective_iff_nonempty_unique_fiber f

/-- Bijectivity is fibers that are nonempty and subsingletons. -/
example (f : X → Y) :
    Function.Bijective f ↔ ∀ y, Nonempty {x // f x = y} ∧ Subsingleton {x // f x = y} :=
  Function.bijective_iff_nonempty_and_subsingleton_fiber f

/-- Fibers transport along equivalences of source and target intertwining the two maps. -/
example (f : X → Y) (f' : X' → Y') (e₁ : X ≃ X') (e₂ : Y ≃ Y') (h : ∀ x, f' (e₁ x) = e₂ (f x))
    (y : Y) : {x // f x = y} ≃ {x' // f' x' = e₂ y} :=
  Equiv.fiberCongr e₁ e₂ h y

/-- A fiber of a composite is the sum of the fibers of the first map over the fiber of the
second. -/
example (g : Y → Z) (f : X → Y) (z : Z) :
    {x // (g ∘ f) x = z} ≃ Σ y : {y // g y = z}, {x // f x = y.1} :=
  Equiv.fiberComp g f z

/-- Precomposition with an equivalence preserves fibers. -/
example (f : X → Y) (e : X' ≃ X) (y : Y) : {x' // f (e x') = y} ≃ {x // f x = y} :=
  Equiv.fiberCompEquiv f e y

/-- Postcomposition with an equivalence transports fibers along its inverse. -/
example (e : Y ≃ Y') (f : X → Y) (y' : Y') : {x // e (f x) = y'} ≃ {x // f x = e.symm y'} :=
  Equiv.fiberEquivComp e f y'

/-- A fiber is the preimage of a singleton. -/
example (f : X → Y) (y : Y) : {x // f x = y} ≃ f ⁻¹' {y} :=
  Equiv.fiberEquivPreimage f y

end Fiber

/-! ## Compatible pairs and the comparison map -/

section Comparison

variable {L : Type uX} {R : Type uY} {G : Type uZ} {B : Sort uX'} {p : L → B} {q : R → B}

/-- Compatible pairs of local views are mathlib's `Function.Pullback`. -/
example (l : L) (r : R) (h : p l = q r) : p.Pullback q :=
  Function.Pullback.mk l r h

/-- The two local views of a compatible pair agree on the overlap. -/
example (c : p.Pullback q) : p c.fst = q c.snd :=
  Function.Pullback.comm c

/-- Compatible pairs are determined by their two projections. -/
example (c d : p.Pullback q) (h₁ : c.fst = d.fst) (h₂ : c.snd = d.snd) : c = d :=
  Function.Pullback.ext h₁ h₂

/-- A commuting square induces the comparison map. -/
example (f : G → L) (g : G → R) (h : ∀ x, p (f x) = q (g x)) : G → p.Pullback q :=
  Function.Pullback.lift f g h

/-- The first projection of the comparison is the left restriction. -/
example (f : G → L) (g : G → R) (h : ∀ x, p (f x) = q (g x)) (x : G) :
    (Function.Pullback.lift f g h x).fst = f x :=
  Function.Pullback.fst_lift x

/-- The second projection of the comparison is the right restriction. -/
example (f : G → L) (g : G → R) (h : ∀ x, p (f x) = q (g x)) (x : G) :
    (Function.Pullback.lift f g h x).snd = g x :=
  Function.Pullback.snd_lift x

/-- The comparison is the only map with those two projections. -/
example (f : G → L) (g : G → R) (h : ∀ x, p (f x) = q (g x)) (u : G → p.Pullback q)
    (hf : ∀ x, (u x).fst = f x) (hg : ∀ x, (u x).snd = g x) : u = Function.Pullback.lift f g h :=
  Function.Pullback.lift_unique u hf hg

/-- The fiber of the comparison over a compatible pair is the type of global states restricting
to that pair. -/
example (f : G → L) (g : G → R) (h : ∀ x, p (f x) = q (g x)) (c : p.Pullback q) :
    {x // Function.Pullback.lift f g h x = c} ≃ {x // f x = c.fst ∧ g x = c.snd} :=
  Function.Pullback.fiberLiftEquiv (h := h) c

/-! ### Pointwise criteria -/

/-- Globalization fails at a compatible pair exactly when its fiber is empty. -/
example (f : G → L) (g : G → R) (h : ∀ x, p (f x) = q (g x)) (c : p.Pullback q) :
    IsEmpty {x // Function.Pullback.lift f g h x = c} ↔ ¬∃ x, f x = c.fst ∧ g x = c.snd :=
  Function.Pullback.isEmpty_fiber_lift_iff h c

/-- A global extension exists exactly when the fiber is nonempty. -/
example (f : G → L) (g : G → R) (h : ∀ x, p (f x) = q (g x)) (c : p.Pullback q) :
    Nonempty {x // Function.Pullback.lift f g h x = c} ↔ ∃ x, f x = c.fst ∧ g x = c.snd :=
  Function.Pullback.nonempty_fiber_lift_iff h c

/-- Global extensions are unique when they exist exactly when the fiber is a subsingleton. -/
example (f : G → L) (g : G → R) (h : ∀ x, p (f x) = q (g x)) (c : p.Pullback q) :
    Subsingleton {x // Function.Pullback.lift f g h x = c} ↔
      ∀ x y, f x = c.fst ∧ g x = c.snd → f y = c.fst ∧ g y = c.snd → x = y :=
  Function.Pullback.subsingleton_fiber_lift_iff h c

/-- A compatible pair has exactly one global extension exactly when its fiber has a unique
element. -/
example (f : G → L) (g : G → R) (h : ∀ x, p (f x) = q (g x)) (c : p.Pullback q) :
    Nonempty (Unique {x // Function.Pullback.lift f g h x = c}) ↔
      ∃! x, f x = c.fst ∧ g x = c.snd :=
  Function.Pullback.nonempty_unique_fiber_lift_iff h c

/-- Unique existence over a compatible pair, in `∃!` form. -/
example (f : G → L) (g : G → R) (h : ∀ x, p (f x) = q (g x)) (c : p.Pullback q) :
    (∃! x, Function.Pullback.lift f g h x = c) ↔ ∃! x, f x = c.fst ∧ g x = c.snd :=
  Function.Pullback.existsUnique_lift_eq_iff h c

/-! ### Global criteria -/

/-- Injectivity of the comparison is joint separation by the two local views. -/
example (f : G → L) (g : G → R) (h : ∀ x, p (f x) = q (g x)) :
    Function.Injective (Function.Pullback.lift f g h) ↔ ∀ x y, f x = f y → g x = g y → x = y :=
  Function.Pullback.injective_lift_iff h

/-- Injectivity of the comparison is uniqueness of extensions over every compatible pair. -/
example (f : G → L) (g : G → R) (h : ∀ x, p (f x) = q (g x)) :
    Function.Injective (Function.Pullback.lift f g h) ↔
      ∀ c, Subsingleton {x // Function.Pullback.lift f g h x = c} :=
  Function.Pullback.injective_lift_iff_forall_subsingleton h

/-- Surjectivity of the comparison is amalgamation of every compatible pair. -/
example (f : G → L) (g : G → R) (h : ∀ x, p (f x) = q (g x)) :
    Function.Surjective (Function.Pullback.lift f g h) ↔
      ∀ l r, p l = q r → ∃ x, f x = l ∧ g x = r :=
  Function.Pullback.surjective_lift_iff h

/-- Surjectivity of the comparison is existence of extensions over every compatible pair. -/
example (f : G → L) (g : G → R) (h : ∀ x, p (f x) = q (g x)) :
    Function.Surjective (Function.Pullback.lift f g h) ↔
      ∀ c, Nonempty {x // Function.Pullback.lift f g h x = c} :=
  Function.Pullback.surjective_lift_iff_forall_nonempty h

/-- Bijectivity of the comparison is joint separation together with joint attainment. -/
example (f : G → L) (g : G → R) (h : ∀ x, p (f x) = q (g x)) :
    Function.Bijective (Function.Pullback.lift f g h) ↔
      (∀ x y, f x = f y → g x = g y → x = y) ∧ ∀ l r, p l = q r → ∃ x, f x = l ∧ g x = r :=
  Function.Pullback.bijective_lift_iff h

/-- Bijectivity of the comparison is unique amalgamation of every compatible pair. -/
example (f : G → L) (g : G → R) (h : ∀ x, p (f x) = q (g x)) :
    Function.Bijective (Function.Pullback.lift f g h) ↔
      ∀ l r, p l = q r → ∃! x, f x = l ∧ g x = r :=
  Function.Pullback.bijective_lift_iff_existsUnique h

/-- Bijectivity of the comparison is unique existence of extensions over every compatible pair. -/
example (f : G → L) (g : G → R) (h : ∀ x, p (f x) = q (g x)) :
    Function.Bijective (Function.Pullback.lift f g h) ↔
      ∀ c, Nonempty (Unique {x // Function.Pullback.lift f g h x = c}) :=
  Function.Pullback.bijective_lift_iff_forall_nonempty_unique h

/-! ### Projections and symmetry -/

/-- The fiber of the first projection over a left view is the fiber of the right restriction. -/
example (l : L) : {c : p.Pullback q // c.fst = l} ≃ {r // q r = p l} :=
  Function.Pullback.fiberFstEquiv l

/-- The fiber of the second projection over a right view is the fiber of the left restriction. -/
example (r : R) : {c : p.Pullback q // c.snd = r} ≃ {l // p l = q r} :=
  Function.Pullback.fiberSndEquiv r

/-- Exchanging the two local views is an equivalence of compatible pairs. -/
example : p.Pullback q ≃ q.Pullback p :=
  Function.Pullback.swap

/-- Exchanging the two local views is an involution. -/
example (c : p.Pullback q) : Function.Pullback.swap (Function.Pullback.swap c) = c :=
  Function.Pullback.swap_swap c

/-- Exchanging the two local views exchanges the two legs of the comparison. -/
example (f : G → L) (g : G → R) (h : ∀ x, p (f x) = q (g x)) (x : G) :
    Function.Pullback.swap (Function.Pullback.lift f g h x) =
      Function.Pullback.lift g f (fun x => (h x).symm) x :=
  Function.Pullback.swap_lift x

end Comparison

/-! ### Transport along coherent equivalences -/

section Congr

variable {L : Type uX} {R : Type uY} {G : Type uZ} {B : Sort uX'} {p : L → B} {q : R → B}
  {L' : Type uL'} {R' : Type uR'} {G' : Type uG'} {B' : Sort uB'} {p' : L' → B'} {q' : R' → B'}

/-- Compatible pairs transport along equivalences of the span commuting with the two
restrictions. -/
example (eL : L ≃ L') (eR : R ≃ R') (eB : B ≃ B') (hp : ∀ l, p' (eL l) = eB (p l))
    (hq : ∀ r, q' (eR r) = eB (q r)) : p.Pullback q ≃ p'.Pullback q' :=
  Function.Pullback.congr eL eR eB hp hq

/-- Fibers of the comparison correspond under a coherent equivalence of squares. -/
example (f : G → L) (g : G → R) (h : ∀ x, p (f x) = q (g x)) (f' : G' → L') (g' : G' → R')
    (h' : ∀ x, p' (f' x) = q' (g' x)) (eL : L ≃ L') (eR : R ≃ R') (eB : B ≃ B')
    (hp : ∀ l, p' (eL l) = eB (p l)) (hq : ∀ r, q' (eR r) = eB (q r)) (eG : G ≃ G')
    (hf : ∀ x, f' (eG x) = eL (f x)) (hg : ∀ x, g' (eG x) = eR (g x)) (c : p.Pullback q) :
    {x // Function.Pullback.lift f g h x = c} ≃
      {x' // Function.Pullback.lift f' g' h' x' = Function.Pullback.congr eL eR eB hp hq c} :=
  Function.Pullback.fiberLiftCongr (h := h) (h' := h') eL eR eB hp hq eG hf hg c

/-- Injectivity of the comparison is invariant under a coherent equivalence of squares. -/
example (f : G → L) (g : G → R) (h : ∀ x, p (f x) = q (g x)) (f' : G' → L') (g' : G' → R')
    (h' : ∀ x, p' (f' x) = q' (g' x)) (eL : L ≃ L') (eR : R ≃ R') (eB : B ≃ B')
    (hp : ∀ l, p' (eL l) = eB (p l)) (hq : ∀ r, q' (eR r) = eB (q r)) (eG : G ≃ G')
    (hf : ∀ x, f' (eG x) = eL (f x)) (hg : ∀ x, g' (eG x) = eR (g x)) :
    Function.Injective (Function.Pullback.lift f' g' h') ↔
      Function.Injective (Function.Pullback.lift f g h) :=
  Function.Pullback.injective_lift_iff_of_congr eL eR eB hp hq eG hf hg

/-- Surjectivity of the comparison is invariant under a coherent equivalence of squares. -/
example (f : G → L) (g : G → R) (h : ∀ x, p (f x) = q (g x)) (f' : G' → L') (g' : G' → R')
    (h' : ∀ x, p' (f' x) = q' (g' x)) (eL : L ≃ L') (eR : R ≃ R') (eB : B ≃ B')
    (hp : ∀ l, p' (eL l) = eB (p l)) (hq : ∀ r, q' (eR r) = eB (q r)) (eG : G ≃ G')
    (hf : ∀ x, f' (eG x) = eL (f x)) (hg : ∀ x, g' (eG x) = eR (g x)) :
    Function.Surjective (Function.Pullback.lift f' g' h') ↔
      Function.Surjective (Function.Pullback.lift f g h) :=
  Function.Pullback.surjective_lift_iff_of_congr eL eR eB hp hq eG hf hg

/-- Bijectivity of the comparison is invariant under a coherent equivalence of squares. -/
example (f : G → L) (g : G → R) (h : ∀ x, p (f x) = q (g x)) (f' : G' → L') (g' : G' → R')
    (h' : ∀ x, p' (f' x) = q' (g' x)) (eL : L ≃ L') (eR : R ≃ R') (eB : B ≃ B')
    (hp : ∀ l, p' (eL l) = eB (p l)) (hq : ∀ r, q' (eR r) = eB (q r)) (eG : G ≃ G')
    (hf : ∀ x, f' (eG x) = eL (f x)) (hg : ∀ x, g' (eG x) = eR (g x)) :
    Function.Bijective (Function.Pullback.lift f' g' h') ↔
      Function.Bijective (Function.Pullback.lift f g h) :=
  Function.Pullback.bijective_lift_iff_of_congr eL eR eB hp hq eG hf hg

end Congr

/-! ### Trivial overlap -/

section TrivialOverlap

variable {L : Type uX} {R : Type uY} {G : Type uZ} {B : Sort uX'} {p : L → B} {q : R → B}
  [Subsingleton B]

/-- Over a trivial overlap every pair of local views is compatible. -/
example : p.Pullback q ≃ L × R :=
  Function.Pullback.equivProdOfSubsingleton

/-- Over a trivial overlap the comparison is injective exactly when the joint map is. -/
example (f : G → L) (g : G → R) (h : ∀ x, p (f x) = q (g x)) :
    Function.Injective (Function.Pullback.lift f g h) ↔ Function.Injective fun x => (f x, g x) :=
  Function.Pullback.injective_lift_iff_of_subsingleton h

/-- Over a trivial overlap the comparison is surjective exactly when the joint map is. -/
example (f : G → L) (g : G → R) (h : ∀ x, p (f x) = q (g x)) :
    Function.Surjective (Function.Pullback.lift f g h) ↔ Function.Surjective fun x => (f x, g x) :=
  Function.Pullback.surjective_lift_iff_of_subsingleton h

/-- Over a trivial overlap the comparison is bijective exactly when the joint map is. -/
example (f : G → L) (g : G → R) (h : ∀ x, p (f x) = q (g x)) :
    Function.Bijective (Function.Pullback.lift f g h) ↔ Function.Bijective fun x => (f x, g x) :=
  Function.Pullback.bijective_lift_iff_of_subsingleton h

end TrivialOverlap

/-! ## Reduction across an overlap -/

section Reduction

variable {L : Type uLf} {R : Type uRf} {B : Type uBf} {p : L → B} {q : R → B}
  {L' : Type uLc} {R' : Type uRc} {B' : Type uBc} {p' : L' → B'} {q' : R' → B'}
  {a : L → L'} {b : B → B'} {c : R → R'}
  (ha : ∀ l, p' (a l) = b (p l)) (hc : ∀ r, q' (c r) = b (q r))

/-! ### The observed comparison -/

/-- Commutation alone induces the comparison of compatible pairs. -/
example : p.Pullback q → p'.Pullback q' :=
  Function.Pullback.map ha hc

/-- The comparison is the lift of the observed projections, by definition. -/
example :
    Function.Pullback.map ha hc =
      Function.Pullback.lift (a ∘ Function.Pullback.fst) (c ∘ Function.Pullback.snd)
        fun s => (ha s.fst).trans ((congrArg b s.comm).trans (hc s.snd).symm) :=
  rfl

/-- The left observed component of a mapped pair. -/
example (s : p.Pullback q) : (Function.Pullback.map ha hc s).fst = a s.fst :=
  Function.Pullback.fst_map ha hc s

/-- The right observed component of a mapped pair. -/
example (s : p.Pullback q) : (Function.Pullback.map ha hc s).snd = c s.snd :=
  Function.Pullback.snd_map ha hc s

/-- A fine pair lies over a coarse pair exactly when both observed components match. -/
example (s : p.Pullback q) (t : p'.Pullback q') :
    Function.Pullback.map ha hc s = t ↔ a s.fst = t.fst ∧ c s.snd = t.snd :=
  Function.Pullback.map_eq_iff ha hc

/-- Two fine pairs are observed alike exactly when both observed components agree. -/
example (s s' : p.Pullback q) :
    Function.Pullback.map ha hc s = Function.Pullback.map ha hc s' ↔
      a s.fst = a s'.fst ∧ c s.snd = c s'.snd :=
  Function.Pullback.map_eq_map_iff ha hc

/-- The comparison is mathlib's `Function.mapPullback`. -/
example :
    Function.Pullback.map ha hc = Function.mapPullback a b c (funext ha) (funext hc) :=
  Function.Pullback.map_eq_mapPullback ha hc

/-! ### The observed quotient -/

/-- Observed equality of fine pairs is agreement of both observed components. -/
example (s s' : p.Pullback q) :
    Setoid.ker (Function.Pullback.map ha hc) s s' ↔
      a s.fst = a s'.fst ∧ c s.snd = c s'.snd :=
  Function.Pullback.observed_rel_iff ha hc s s'

/-- Observed equality is equality under the comparison. -/
example (s s' : p.Pullback q) :
    Setoid.ker (Function.Pullback.map ha hc) s s' ↔
      Function.Pullback.map ha hc s = Function.Pullback.map ha hc s' :=
  Function.Pullback.observed_rel_iff_map_eq ha hc s s'

/-- Fine compatible pairs pass to the observed quotient. -/
example : p.Pullback q → Function.Pullback.Observed ha hc :=
  Quotient.mk (Setoid.ker (Function.Pullback.map ha hc))

/-- Two fine pairs have the same observed class exactly when both observed components agree. -/
example (s s' : p.Pullback q) :
    (Quotient.mk (Setoid.ker (Function.Pullback.map ha hc)) s :
        Function.Pullback.Observed ha hc) =
      Quotient.mk (Setoid.ker (Function.Pullback.map ha hc)) s' ↔
      a s.fst = a s'.fst ∧ c s.snd = c s'.snd :=
  Function.Pullback.observed_mk_eq_iff ha hc s s'

/-- The comparison induced on the observed quotient. -/
example : Function.Pullback.Observed ha hc → p'.Pullback q' :=
  Function.Pullback.observedMap ha hc

/-- The induced comparison on a class is the comparison on a representative. -/
example (s : p.Pullback q) :
    Function.Pullback.observedMap ha hc
        (Quotient.mk (Setoid.ker (Function.Pullback.map ha hc)) s) =
      Function.Pullback.map ha hc s :=
  Function.Pullback.observedMap_mk ha hc s

/-- The induced comparison is injective. -/
example : Function.Injective (Function.Pullback.observedMap ha hc) :=
  Function.Pullback.observedMap_injective ha hc

/-- The induced comparison and the raw comparison have the same image. -/
example :
    Set.range (Function.Pullback.observedMap ha hc) = Set.range (Function.Pullback.map ha hc) :=
  Function.Pullback.range_observedMap ha hc

/-- The observed quotient is the common image of the two comparisons. -/
noncomputable example :
    Function.Pullback.Observed ha hc ≃ Set.range (Function.Pullback.map ha hc) :=
  Function.Pullback.observedEquivRange ha hc

/-- The identification on a class is the comparison on a representative. -/
example (s : p.Pullback q) :
    (Function.Pullback.observedEquivRange ha hc
        (Quotient.mk (Setoid.ker (Function.Pullback.map ha hc)) s) : p'.Pullback q') =
      Function.Pullback.map ha hc s :=
  Function.Pullback.coe_observedEquivRange_mk ha hc s

/-- Round trip: the inverse identification after the identification. -/
example (x : Function.Pullback.Observed ha hc) :
    (Function.Pullback.observedEquivRange ha hc).symm
        (Function.Pullback.observedEquivRange ha hc x) = x :=
  Function.Pullback.observedEquivRange_symm_apply_apply ha hc x

/-- Round trip: the identification after the inverse identification. -/
example (t : Set.range (Function.Pullback.map ha hc)) :
    Function.Pullback.observedEquivRange ha hc
        ((Function.Pullback.observedEquivRange ha hc).symm t) = t :=
  Function.Pullback.observedEquivRange_apply_symm_apply ha hc t

/-- Every fiber of the induced comparison is a subsingleton: an observed class is unique. This is
no uniqueness of a fine lift. -/
example (t : p'.Pullback q') :
    Subsingleton {x // Function.Pullback.observedMap ha hc x = t} :=
  Function.Pullback.subsingleton_fiber_observedMap ha hc t

/-! ### The exact lifting criterion -/

/-- A coarse compatible pair is attained exactly when the fine overlap values reached from the
two sides above it have a common element. -/
example (t : p'.Pullback q') :
    t ∈ Set.range (Function.Pullback.map ha hc) ↔
      (p '' (a ⁻¹' {t.fst}) ∩ q '' (c ⁻¹' {t.snd})).Nonempty :=
  Function.Pullback.mem_range_map_iff ha hc t

/-- The same criterion for the induced comparison. -/
example (t : p'.Pullback q') :
    t ∈ Set.range (Function.Pullback.observedMap ha hc) ↔
      (p '' (a ⁻¹' {t.fst}) ∩ q '' (c ⁻¹' {t.snd})).Nonempty :=
  Function.Pullback.mem_range_observedMap_iff ha hc t

/-- The criterion as an actual common fine overlap value. -/
example (t : p'.Pullback q') :
    t ∈ Set.range (Function.Pullback.map ha hc) ↔
      ∃ β : B, (∃ l : L, a l = t.fst ∧ p l = β) ∧ ∃ r : R, c r = t.snd ∧ q r = β :=
  Function.Pullback.mem_range_map_iff_exists_overlap ha hc t

/-! ### Fine lifts of a coarse pair -/

/-- The fiber of the raw comparison over a coarse pair is the fine compatible pairs observed as
it. -/
example (t : p'.Pullback q') :
    {s // Function.Pullback.map ha hc s = t} ≃
      {s : p.Pullback q // a s.fst = t.fst ∧ c s.snd = t.snd} :=
  Function.Pullback.fiberMapEquiv ha hc t

/-- That fiber is the pairs of fine views that are compatible and observed as the two coarse
components. -/
example (t : p'.Pullback q') :
    {s // Function.Pullback.map ha hc s = t} ≃
      {x : L × R // p x.1 = q x.2 ∧ a x.1 = t.fst ∧ c x.2 = t.snd} :=
  Function.Pullback.fiberMapEquivProd ha hc t

/-- That fiber is the compatible pairs of fine lifts of the two coarse components. -/
example (t : p'.Pullback q') :
    {s // Function.Pullback.map ha hc s = t} ≃
      Function.Pullback (fun l : {l // a l = t.fst} => p l.1)
        fun r : {r // c r = t.snd} => q r.1 :=
  Function.Pullback.fiberMapEquivPullback ha hc t

/-- Existence of a fine lift is the lifting criterion at that coarse pair. -/
example (t : p'.Pullback q') :
    Nonempty {s // Function.Pullback.map ha hc s = t} ↔
      (p '' (a ⁻¹' {t.fst}) ∩ q '' (c ⁻¹' {t.snd})).Nonempty :=
  Function.Pullback.nonempty_fiber_map_iff ha hc t

/-- A coarse pair has a fine lift exactly when it has an observed class: over each coarse pair
the raw fiber and the quotient fiber are nonempty together. -/
example (t : p'.Pullback q') :
    Nonempty {s // Function.Pullback.map ha hc s = t} ↔
      Nonempty {x // Function.Pullback.observedMap ha hc x = t} :=
  (Function.Pullback.nonempty_fiber_map_iff ha hc t).trans
    ((Function.nonempty_fiber_iff_mem_range _ t).trans
      (Function.Pullback.mem_range_observedMap_iff ha hc t)).symm

/-- Absence of a fine lift is failure of the lifting criterion at that coarse pair. -/
example (t : p'.Pullback q') :
    IsEmpty {s // Function.Pullback.map ha hc s = t} ↔
      ¬(p '' (a ⁻¹' {t.fst}) ∩ q '' (c ⁻¹' {t.snd})).Nonempty :=
  Function.Pullback.isEmpty_fiber_map_iff ha hc t

/-- Uniqueness of fine lifts, independently of their existence. -/
example (t : p'.Pullback q') :
    Subsingleton {s // Function.Pullback.map ha hc s = t} ↔
      ∀ s s' : p.Pullback q, a s.fst = t.fst ∧ c s.snd = t.snd →
        a s'.fst = t.fst ∧ c s'.snd = t.snd → s = s' :=
  Function.Pullback.subsingleton_fiber_map_iff ha hc t

/-- Unique existence of a fine lift. -/
example (t : p'.Pullback q') :
    Nonempty (Unique {s // Function.Pullback.map ha hc s = t}) ↔
      ∃! s : p.Pullback q, a s.fst = t.fst ∧ c s.snd = t.snd :=
  Function.Pullback.nonempty_unique_fiber_map_iff ha hc t

/-! ### The closing criterion and the inverse -/

/-- The raw comparison is surjective exactly under the criterion everywhere. -/
example :
    Function.Surjective (Function.Pullback.map ha hc) ↔
      ∀ t : p'.Pullback q', (p '' (a ⁻¹' {t.fst}) ∩ q '' (c ⁻¹' {t.snd})).Nonempty :=
  Function.Pullback.surjective_map_iff ha hc

/-- The two comparisons are surjective together. -/
example :
    Function.Surjective (Function.Pullback.observedMap ha hc) ↔
      Function.Surjective (Function.Pullback.map ha hc) :=
  Function.Pullback.surjective_observedMap_iff_surjective_map ha hc

/-- The induced comparison is bijective exactly when the raw comparison is surjective. -/
example :
    Function.Bijective (Function.Pullback.observedMap ha hc) ↔
      Function.Surjective (Function.Pullback.map ha hc) :=
  Function.Pullback.bijective_observedMap_iff_surjective_map ha hc

/-- The observed quotient is all coarse compatible pairs exactly under the criterion
everywhere. -/
example :
    Function.Bijective (Function.Pullback.observedMap ha hc) ↔
      ∀ t : p'.Pullback q', (p '' (a ⁻¹' {t.fst}) ∩ q '' (c ⁻¹' {t.snd})).Nonempty :=
  Function.Pullback.bijective_observedMap_iff ha hc

/-- A two-sided inverse of the induced comparison exists exactly under the criterion. -/
example :
    (∃ i : p'.Pullback q' → Function.Pullback.Observed ha hc,
        Function.LeftInverse i (Function.Pullback.observedMap ha hc) ∧
          Function.RightInverse i (Function.Pullback.observedMap ha hc)) ↔
      ∀ t : p'.Pullback q', (p '' (a ⁻¹' {t.fst}) ∩ q '' (c ⁻¹' {t.snd})).Nonempty :=
  Function.Pullback.exists_inverse_observedMap_iff ha hc

/-- A right inverse forces the criterion everywhere. -/
example (i : p'.Pullback q' → Function.Pullback.Observed ha hc)
    (hi : ∀ t, Function.Pullback.observedMap ha hc (i t) = t) (t : p'.Pullback q') :
    (p '' (a ⁻¹' {t.fst}) ∩ q '' (c ⁻¹' {t.snd})).Nonempty :=
  Function.Pullback.inter_nonempty_of_rightInverse ha hc i hi t

section Inverse

variable (h : ∀ t : p'.Pullback q', (p '' (a ⁻¹' {t.fst}) ∩ q '' (c ⁻¹' {t.snd})).Nonempty)

/-- Under the criterion the observed quotient is equivalent to all coarse compatible pairs. The
forward function is the induced comparison; the inverse accepting a coarse pair is its `symm`,
obtained by classical choice. -/
noncomputable example : Function.Pullback.Observed ha hc ≃ p'.Pullback q' :=
  Function.Pullback.observedEquiv ha hc h

/-- The forward direction of that equivalence is the induced comparison. -/
example (x : Function.Pullback.Observed ha hc) :
    Function.Pullback.observedEquiv ha hc h x = Function.Pullback.observedMap ha hc x :=
  Function.Pullback.observedEquiv_apply ha hc h x

/-- Round trip: the induced comparison after the inverse. -/
example (t : p'.Pullback q') :
    Function.Pullback.observedMap ha hc ((Function.Pullback.observedEquiv ha hc h).symm t) = t :=
  Function.Pullback.observedMap_observedEquiv_symm ha hc h t

/-- Round trip: the inverse after the induced comparison. -/
example (x : Function.Pullback.Observed ha hc) :
    (Function.Pullback.observedEquiv ha hc h).symm
        (Function.Pullback.observedMap ha hc x) = x :=
  Function.Pullback.observedEquiv_symm_observedMap ha hc h x

/-- The inverse is the only right inverse. -/
example (i : p'.Pullback q' → Function.Pullback.Observed ha hc)
    (hi : ∀ t, Function.Pullback.observedMap ha hc (i t) = t) :
    i = (Function.Pullback.observedEquiv ha hc h).symm :=
  Function.Pullback.eq_observedEquiv_symm_of_rightInverse ha hc h i hi

/-- The inverse is the only left inverse. -/
example (i : p'.Pullback q' → Function.Pullback.Observed ha hc)
    (hi : ∀ x, i (Function.Pullback.observedMap ha hc x) = x) :
    i = (Function.Pullback.observedEquiv ha hc h).symm :=
  Function.Pullback.eq_observedEquiv_symm_of_leftInverse ha hc h i hi

end Inverse

/-! ### Injective overlap observation -/

/-- With an injective overlap observation the criterion is componentwise. -/
example (hb : Function.Injective b) (t : p'.Pullback q') :
    t ∈ Set.range (Function.Pullback.map ha hc) ↔
      t.fst ∈ Set.range a ∧ t.snd ∈ Set.range c :=
  Function.Pullback.mem_range_map_iff_of_injective ha hc hb t

/-- Sufficient special case: injective overlap observation and surjective local observations. -/
example (hb : Function.Injective b) (hsa : Function.Surjective a)
    (hsc : Function.Surjective c) :
    Function.Bijective (Function.Pullback.observedMap ha hc) :=
  Function.Pullback.bijective_observedMap_of_injective ha hc hb hsa hsc

/-! ### Restriction of observations to their images -/

/-- The coarse left leg restricts to the images of the observations. -/
example : Set.range a → Set.range b :=
  Function.Pullback.rangeRestrict ha

/-- The restricted square commutes pointwise. -/
example (l : L) :
    Function.Pullback.rangeRestrict ha (Set.rangeFactorization a l) =
      Set.rangeFactorization b (p l) :=
  Function.Pullback.rangeFactorization_comm ha l

/-- The restricted observations are surjective. -/
example : Function.Surjective (Set.rangeFactorization a) :=
  Set.rangeFactorization_surjective

/-- The restricted system attains a restricted coarse pair exactly when the original system
attains its underlying coarse pair. -/
example (t : (Function.Pullback.rangeRestrict ha).Pullback
    (Function.Pullback.rangeRestrict hc)) :
    t ∈ Set.range (Function.Pullback.mapRangeFactorization ha hc) ↔
      Function.Pullback.rangeInclusion ha hc t ∈ Set.range (Function.Pullback.map ha hc) :=
  Function.Pullback.mem_range_mapRangeFactorization_iff ha hc t

end Reduction

/-! ### A surjective reduction that loses compatibility -/

section Lifting

open Amalgam.Models.Lifting

/-- The two fine local views restrict to distinct overlap values. -/
example : p () = false ∧ q () = true := ⟨rfl, rfl⟩

/-- The two squares commute. -/
example : ∀ l, p' (a l) = b (p l) := ha

example : ∀ r, q' (c r) = b (q r) := hc

/-- All three observation maps are surjective, so this is a reduction onto the coarse span. -/
example : Function.Surjective a := surjective_a

example : Function.Surjective b := surjective_b

example : Function.Surjective c := surjective_c

/-- No fine pair is compatible. -/
example : IsEmpty (p.Pullback q) := isEmpty_pullback

/-- The coarse compatible pairs are a singleton. -/
example : Unique (p'.Pullback q') := uniqueCoarsePullback

/-- Its unique pair. -/
example : p'.Pullback q' := t₀

/-- The unique coarse pair is compatible. -/
example : p' t₀.fst = q' t₀.snd := Function.Pullback.comm t₀

/-- The lifting criterion fails there: the fine overlap values reached from the two sides are
disjoint. -/
example : ¬(p '' (a ⁻¹' {t₀.fst}) ∩ q '' (c ⁻¹' {t₀.snd})).Nonempty :=
  not_nonempty_inter_t₀

/-- The unique coarse pair is attained by neither comparison. -/
example : t₀ ∉ Set.range (Function.Pullback.map ha hc) := t₀_notMem_range_map

example : t₀ ∉ Set.range (Function.Pullback.observedMap ha hc) := t₀_notMem_range_observedMap

/-- It has no fine lift. -/
example : IsEmpty {s // Function.Pullback.map ha hc s = t₀} := isEmpty_fiber_t₀

/-- The observed quotient is empty. -/
example : IsEmpty (Function.Pullback.Observed ha hc) := isEmpty_observed

/-- Existence fails, so surjective observations do not suffice. -/
example : ¬Function.Surjective (Function.Pullback.map ha hc) := not_surjective_map

example : ¬Function.Bijective (Function.Pullback.observedMap ha hc) := not_bijective_observedMap

end Lifting

/-! ## Restriction systems and compatible families -/

section RestrictionDatum

variable {C : Type uC} [Preorder C] {S : RestrictionSystem.{uC, uS} C}
  {S' : RestrictionSystem.{uC, uS'} C} {ι : Type uI} {κ : Type uK} {μ : Type uM}
  {F : ι → C} {E : κ → C} {D : μ → C} {G : κ → C}

/-- A state at `d` restricts along `h : c ≤ d` to a state at the coarser context `c`. -/
example {c d : C} (h : c ≤ d) : S.State d → S.State c :=
  S.res h

/-- Restriction along a reflexivity proof is the identity. -/
example {c : C} (h : c ≤ c) (x : S.State c) : S.res h x = x :=
  S.res_refl h x

/-- Restriction composes along transitivity. -/
example {c d e : C} (h₁ : c ≤ d) (h₂ : d ≤ e) (x : S.State e) :
    S.res h₁ (S.res h₂ x) = S.res (h₁.trans h₂) x :=
  S.res_trans h₁ h₂ x

/-- Compatibility is agreement after restriction to every common coarser context. -/
example (x : ∀ i, S.State (F i)) :
    S.Compatible F x ↔
      ∀ ⦃c : C⦄ ⦃i j : ι⦄ (hi : c ≤ F i) (hj : c ≤ F j), S.res hi (x i) = S.res hj (x j) :=
  Iff.rfl

/-- A compatible family is one state per index satisfying compatibility. -/
example : S.CompatibleFamily F = {x : ∀ i, S.State (F i) // S.Compatible F x} :=
  rfl

/-- Over an empty index type there is exactly one compatible family. -/
example [IsEmpty ι] : Unique (S.CompatibleFamily F) :=
  S.uniqueOfIsEmpty

/-- A declared restriction operation names an index of the finer family and supplies a context
inequality at every target index. -/
example (m : FamilyMap F E) (k : κ) : E k ≤ F (m.index k) :=
  m.le k

/-- A declared operation acts on compatible families. -/
example (m : FamilyMap F E) : S.CompatibleFamily F → S.CompatibleFamily E :=
  S.restrict m

/-- Its action is actual restriction of the supplied states. -/
example (m : FamilyMap F E) (x : S.CompatibleFamily F) (k : κ) :
    (S.restrict m x).1 k = S.res (m.le k) (x.1 (m.index k)) :=
  S.restrict_apply m x k

/-- Restriction along the identity operation is the identity, by `res_refl`. -/
example (x : S.CompatibleFamily F) : S.restrict (FamilyMap.id F) x = x :=
  S.restrict_id x

/-- Restriction along a composite is the composite of restrictions, by `res_trans`. -/
example (n : FamilyMap E D) (m : FamilyMap F E) (x : S.CompatibleFamily F) :
    S.restrict (n.comp m) x = S.restrict n (S.restrict m x) :=
  S.restrict_comp n m x

/-- A morphism of restriction systems observes at every context, commuting with restriction. -/
example (φ : S.Hom S') {c d : C} (h : c ≤ d) (x : S.State d) :
    S'.res h (φ.toFun d x) = φ.toFun c (S.res h x) :=
  φ.naturality h x

/-- The raw comparison of a family. -/
example (φ : S.Hom S') : S.CompatibleFamily F → S'.CompatibleFamily F :=
  φ.mapFamily F

/-- It observes each component. -/
example (φ : S.Hom S') (x : S.CompatibleFamily F) (i : ι) :
    (φ.mapFamily F x).1 i = φ.toFun (F i) (x.1 i) :=
  φ.mapFamily_apply F x i

/-- Naturality of the raw comparison in the family: observing then restricting is restricting
then observing. -/
example (φ : S.Hom S') (m : FamilyMap F E) (x : S.CompatibleFamily F) :
    S'.restrict m (φ.mapFamily F x) = φ.mapFamily E (S.restrict m x) :=
  φ.restrict_mapFamily m x

/-! ### Presentation invariance -/

/-- A declared operation from a family to itself is the identity on compatible families. -/
example (m : FamilyMap F F) (x : S.CompatibleFamily F) : S.restrict m x = x :=
  S.restrict_endo m x

/-- Declared operations in opposite directions compose to the identity. -/
example (m : FamilyMap F E) (n : FamilyMap E F) (x : S.CompatibleFamily F) :
    S.restrict n (S.restrict m x) = x :=
  S.restrict_restrict m n x

/-- Two families with declared operations both ways have equivalent compatible-family types. -/
example (m : FamilyMap F E) (n : FamilyMap E F) : S.CompatibleFamily F ≃ S.CompatibleFamily E :=
  S.restrictEquiv m n

/-- Relabeling along an equivalence of index types. -/
example (e : κ ≃ ι) : S.CompatibleFamily F ≃ S.CompatibleFamily (F ∘ e) :=
  S.relabel e

/-- The relabeled family reads the original at `e k`. -/
example (e : κ ≃ ι) (x : S.CompatibleFamily F) (k : κ) : (S.relabel e x).1 k = x.1 (e k) :=
  S.relabel_apply_coe e x k

/-- Round trip: relabeling then unrelabeling. -/
example (e : κ ≃ ι) (x : S.CompatibleFamily F) : (S.relabel e).symm (S.relabel e x) = x :=
  S.relabel_symm_relabel e x

/-- Round trip: unrelabeling then relabeling. -/
example (e : κ ≃ ι) (y : S.CompatibleFamily (F ∘ e)) : S.relabel e ((S.relabel e).symm y) = y :=
  S.relabel_relabel_symm e y

/-- The redundancy law: adding views each obtained by restricting an included context changes
nothing. -/
example (σ : κ → ι) (h : ∀ k, G k ≤ F (σ k)) :
    S.CompatibleFamily (Sum.elim F G) ≃ S.CompatibleFamily F :=
  S.redundancyEquiv σ h

/-- Forgetting the added views keeps the included components, by `res_refl`. -/
example (σ : κ → ι) (h : ∀ k, G k ≤ F (σ k)) (x : S.CompatibleFamily (Sum.elim F G)) (i : ι) :
    (S.redundancyEquiv σ h x).1 i = x.1 (Sum.inl i) :=
  S.redundancyEquiv_apply_coe σ h x i

/-- Extending keeps the included components, by `res_refl`. -/
example (σ : κ → ι) (h : ∀ k, G k ≤ F (σ k)) (y : S.CompatibleFamily F) (i : ι) :
    ((S.redundancyEquiv σ h).symm y).1 (Sum.inl i) = y.1 i :=
  S.redundancyEquiv_symm_apply_coe_inl σ h y i

/-- Extending fills the added components by restriction. -/
example (σ : κ → ι) (h : ∀ k, G k ≤ F (σ k)) (y : S.CompatibleFamily F) (k : κ) :
    ((S.redundancyEquiv σ h).symm y).1 (Sum.inr k) = S.res (h k) (y.1 (σ k)) :=
  S.redundancyEquiv_symm_apply_coe_inr σ h y k

/-- Round trip: extending then forgetting. -/
example (σ : κ → ι) (h : ∀ k, G k ≤ F (σ k)) (y : S.CompatibleFamily F) :
    S.restrict (FamilyMap.inl F G) (S.restrict (FamilyMap.extend σ h) y) = y :=
  S.forget_extend σ h y

/-- Round trip: forgetting then extending. -/
example (σ : κ → ι) (h : ∀ k, G k ≤ F (σ k)) (x : S.CompatibleFamily (Sum.elim F G)) :
    S.restrict (FamilyMap.extend σ h) (S.restrict (FamilyMap.inl F G) x) = x :=
  S.extend_forget σ h x

/-- Forgetting redundant views is bijective. -/
example (σ : κ → ι) (h : ∀ k, G k ≤ F (σ k)) :
    Function.Bijective (S.restrict (FamilyMap.inl F G)) :=
  S.bijective_restrict_inl σ h

/-- Adding a single view obtained by restricting an included context changes nothing. -/
example (c : C) (i₀ : ι) (hc : c ≤ F i₀) :
    S.CompatibleFamily (Sum.elim F fun _ : Unit => c) ≃ S.CompatibleFamily F :=
  S.addViewEquiv c i₀ hc

/-- Repeating an included view changes nothing. -/
example (i₀ : ι) :
    S.CompatibleFamily (Sum.elim F fun _ : Unit => F i₀) ≃ S.CompatibleFamily F :=
  S.duplicateEquiv i₀

/-- The fiber of a family restriction is the extension choices along it. -/
example (m : FamilyMap F E) (z : S.CompatibleFamily E) :
    {x // S.restrict m x = z} ≃
      {x : S.CompatibleFamily F // ∀ k, S.res (m.le k) (x.1 (m.index k)) = z.1 k} :=
  S.restrictFiberEquiv m z

/-- Under the redundancy hypothesis those extension choices form a subsingleton. -/
example (σ : κ → ι) (h : ∀ k, G k ≤ F (σ k)) (z : S.CompatibleFamily F) :
    Subsingleton {x // S.restrict (FamilyMap.inl F G) x = z} :=
  S.subsingleton_fiber_restrict_inl σ h z

/-- A subfamily is reached by a forgetful reindexing. -/
example (e : κ → ι) : FamilyMap F (F ∘ e) :=
  FamilyMap.reindex F e

/-- Over `Fin 2` compatibility is the single cross condition between the two views. -/
example (F₂ : Fin 2 → C) (x : ∀ i, S.State (F₂ i)) :
    S.Compatible F₂ x ↔
      ∀ ⦃c : C⦄ (hl : c ≤ F₂ 0) (hr : c ≤ F₂ 1), S.res hl (x 0) = S.res hr (x 1) :=
  S.compatible_fin_two_iff F₂ x

/-! ### Family comparison -/

section FamilyComparison

variable (φ : S.Hom S')

/-- The fiber of the raw comparison over a coarse family is the fine assignments satisfying
compatibility and every component observation equation. -/
example (y : S'.CompatibleFamily F) :
    {x // φ.mapFamily F x = y} ≃
      {x : ∀ i, S.State (F i) // S.Compatible F x ∧ ∀ i, φ.toFun (F i) (x i) = y.1 i} :=
  φ.fiberMapFamilyEquiv y

/-- The image criterion: a coarse family is attained exactly when a simultaneous fine lift
exists. -/
example (y : S'.CompatibleFamily F) :
    y ∈ Set.range (φ.mapFamily F) ↔
      ∃ x : ∀ i, S.State (F i), S.Compatible F x ∧ ∀ i, φ.toFun (F i) (x i) = y.1 i :=
  φ.mem_range_mapFamily_iff y

/-- A fine lift exists exactly under the criterion. -/
example (y : S'.CompatibleFamily F) :
    Nonempty {x // φ.mapFamily F x = y} ↔
      ∃ x : ∀ i, S.State (F i), S.Compatible F x ∧ ∀ i, φ.toFun (F i) (x i) = y.1 i :=
  φ.nonempty_fiber_mapFamily_iff y

/-- There is no fine lift exactly when the criterion fails. -/
example (y : S'.CompatibleFamily F) :
    IsEmpty {x // φ.mapFamily F x = y} ↔
      ¬∃ x : ∀ i, S.State (F i), S.Compatible F x ∧ ∀ i, φ.toFun (F i) (x i) = y.1 i :=
  φ.isEmpty_fiber_mapFamily_iff y

/-- Uniqueness of fine lifts, independently of their existence. -/
example (y : S'.CompatibleFamily F) :
    Subsingleton {x // φ.mapFamily F x = y} ↔
      ∀ x x' : S.CompatibleFamily F, (∀ i, φ.toFun (F i) (x.1 i) = y.1 i) →
        (∀ i, φ.toFun (F i) (x'.1 i) = y.1 i) → x = x' :=
  φ.subsingleton_fiber_mapFamily_iff y

/-- Unique existence of a fine lift. -/
example (y : S'.CompatibleFamily F) :
    Nonempty (Unique {x // φ.mapFamily F x = y}) ↔
      ∃! x : S.CompatibleFamily F, ∀ i, φ.toFun (F i) (x.1 i) = y.1 i :=
  φ.nonempty_unique_fiber_mapFamily_iff y

/-- Observed equality of fine families is agreement of all observed components. -/
example (x x' : S.CompatibleFamily F) :
    Setoid.ker (φ.mapFamily F) x x' ↔ ∀ i, φ.toFun (F i) (x.1 i) = φ.toFun (F i) (x'.1 i) :=
  φ.observed_rel_family_iff x x'

/-- Observed equality is equality under the raw comparison. -/
example (x x' : S.CompatibleFamily F) :
    Setoid.ker (φ.mapFamily F) x x' ↔ φ.mapFamily F x = φ.mapFamily F x' :=
  φ.observed_rel_family_iff_mapFamily_eq x x'

/-- Fine compatible families pass to the observed quotient. -/
example : S.CompatibleFamily F → φ.observedFamily F :=
  Quotient.mk (Setoid.ker (φ.mapFamily F))

/-- Two fine families have the same observed class exactly when all observed components
agree. -/
example (x x' : S.CompatibleFamily F) :
    (Quotient.mk (Setoid.ker (φ.mapFamily F)) x : φ.observedFamily F) =
        Quotient.mk (Setoid.ker (φ.mapFamily F)) x' ↔
      ∀ i, φ.toFun (F i) (x.1 i) = φ.toFun (F i) (x'.1 i) :=
  φ.observedFamily_mk_eq_iff x x'

/-- The comparison induced on the observed quotient. -/
example : φ.observedFamily F → S'.CompatibleFamily F :=
  φ.observedMapFamily F

/-- Factorization: the induced comparison on a class is the raw comparison on a
representative. -/
example (x : S.CompatibleFamily F) :
    φ.observedMapFamily F (Quotient.mk (Setoid.ker (φ.mapFamily F)) x) = φ.mapFamily F x :=
  φ.observedMapFamily_mk x

/-- The induced comparison is injective. -/
example : Function.Injective (φ.observedMapFamily F) :=
  φ.observedMapFamily_injective

/-- The induced comparison and the raw comparison have the same image. -/
example : Set.range (φ.observedMapFamily F) = Set.range (φ.mapFamily F) :=
  φ.range_observedMapFamily

/-- The attainable image. -/
example : Set (S'.CompatibleFamily F) :=
  φ.image F

/-- Membership in the attainable image is the image criterion. -/
example (y : S'.CompatibleFamily F) :
    y ∈ φ.image F ↔
      ∃ x : ∀ i, S.State (F i), S.Compatible F x ∧ ∀ i, φ.toFun (F i) (x i) = y.1 i :=
  φ.mem_image_iff y

/-- The observed quotient is the attainable image. -/
noncomputable example : φ.observedFamily F ≃ φ.image F :=
  φ.observedFamilyEquivImage F

/-- The identification on a class is the raw comparison on a representative. -/
example (x : S.CompatibleFamily F) :
    (φ.observedFamilyEquivImage F (Quotient.mk (Setoid.ker (φ.mapFamily F)) x) :
        S'.CompatibleFamily F) = φ.mapFamily F x :=
  φ.coe_observedFamilyEquivImage_mk x

/-- The identification is the induced comparison on underlying coarse families. -/
example (q : φ.observedFamily F) :
    (φ.observedFamilyEquivImage F q : S'.CompatibleFamily F) = φ.observedMapFamily F q :=
  φ.coe_observedFamilyEquivImage q

/-- Round trip: the inverse identification after the identification. -/
example (q : φ.observedFamily F) :
    (φ.observedFamilyEquivImage F).symm (φ.observedFamilyEquivImage F q) = q :=
  φ.observedFamilyEquivImage_symm_apply_apply q

/-- Round trip: the identification after the inverse identification. -/
example (y : φ.image F) :
    φ.observedFamilyEquivImage F ((φ.observedFamilyEquivImage F).symm y) = y :=
  φ.observedFamilyEquivImage_apply_symm_apply y

/-- Every fiber of the induced comparison is a subsingleton, attained or not. -/
example (y : S'.CompatibleFamily F) : Subsingleton {q // φ.observedMapFamily F q = y} :=
  φ.subsingleton_fiber_observedMapFamily y

/-- Raw and quotient fibers are nonempty together; the quotient discards multiplicity only. -/
example (y : S'.CompatibleFamily F) :
    Nonempty {x // φ.mapFamily F x = y} ↔ Nonempty {q // φ.observedMapFamily F q = y} :=
  φ.nonempty_fiber_mapFamily_iff_nonempty_fiber_observedMapFamily y

/-- The raw commuting square along a declared family restriction. -/
example (m : FamilyMap F E) : S'.restrict m ∘ φ.mapFamily F = φ.mapFamily E ∘ S.restrict m :=
  φ.restrict_comp_mapFamily m

/-- Restriction of observed classes. -/
example (m : FamilyMap F E) : φ.observedFamily F → φ.observedFamily E :=
  φ.restrictObserved m

/-- Equal observations restrict to equal observations, which is what makes restriction of
observed classes well defined. -/
example (m : FamilyMap F E) (x x' : S.CompatibleFamily F) (h : Setoid.ker (φ.mapFamily F) x x') :
    Setoid.ker (φ.mapFamily E) (S.restrict m x) (S.restrict m x') :=
  φ.ker_mapFamily_restrict m h

/-- It is well defined on observed classes, computing as `S.restrict m` on a representative. -/
example (m : FamilyMap F E) (x : S.CompatibleFamily F) :
    φ.restrictObserved m (Quotient.mk (Setoid.ker (φ.mapFamily F)) x) =
      Quotient.mk (Setoid.ker (φ.mapFamily E)) (S.restrict m x) :=
  φ.restrictObserved_mk m x

/-- The quotient commuting square. -/
example (m : FamilyMap F E) (q : φ.observedFamily F) :
    φ.observedMapFamily E (φ.restrictObserved m q) = S'.restrict m (φ.observedMapFamily F q) :=
  φ.observedMapFamily_restrictObserved m q

/-- Restriction sends the attainable image over `F` into the attainable image over `E`. -/
example (m : FamilyMap F E) : Set.MapsTo (S'.restrict m) (φ.image F) (φ.image E) :=
  φ.mapsTo_restrict_image m

/-- `restrict_(F,E)(I_F) ⊆ I_E`; naturality gives inclusion only. -/
example (m : FamilyMap F E) : S'.restrict m '' φ.image F ⊆ φ.image E :=
  φ.image_restrict_subset m

/-- The map induced by restriction on attainable images. -/
example (m : FamilyMap F E) : φ.image F → φ.image E :=
  φ.restrictImage m

/-- It is restriction on underlying coarse families. -/
example (m : FamilyMap F E) (y : φ.image F) :
    (φ.restrictImage m y : S'.CompatibleFamily E) = S'.restrict m y.1 :=
  φ.coe_restrictImage m y

/-- The image commuting square. -/
example (m : FamilyMap F E) (q : φ.observedFamily F) :
    φ.restrictImage m (φ.observedFamilyEquivImage F q) =
      φ.observedFamilyEquivImage E (φ.restrictObserved m q) :=
  φ.restrictImage_observedFamilyEquivImage m q

/-- Restriction of observed classes along the identity operation is the identity. -/
example (q : φ.observedFamily F) : φ.restrictObserved (FamilyMap.id F) q = q :=
  φ.restrictObserved_id q

/-- Restriction of observed classes along a composite is the composite of restrictions. -/
example (n : FamilyMap E D) (m : FamilyMap F E) (q : φ.observedFamily F) :
    φ.restrictObserved (n.comp m) q = φ.restrictObserved n (φ.restrictObserved m q) :=
  φ.restrictObserved_comp n m q

/-- Restriction of attainable images along the identity operation is the identity. -/
example (y : φ.image F) : φ.restrictImage (FamilyMap.id F) y = y :=
  φ.restrictImage_id y

/-- Restriction of attainable images along a composite is the composite of restrictions. -/
example (n : FamilyMap E D) (m : FamilyMap F E) (y : φ.image F) :
    φ.restrictImage (n.comp m) y = φ.restrictImage n (φ.restrictImage m y) :=
  φ.restrictImage_comp n m y

/-- Restriction sends the raw fiber over `y` into the raw fiber over the restriction of `y`. -/
example (m : FamilyMap F E) (y : S'.CompatibleFamily F) :
    {x // φ.mapFamily F x = y} → {x' // φ.mapFamily E x' = S'.restrict m y} :=
  φ.fiberRestrict m y

/-- It restricts the same supplied local states, choosing no independent lift. -/
example (m : FamilyMap F E) (y : S'.CompatibleFamily F) (x : {x // φ.mapFamily F x = y}) :
    (φ.fiberRestrict m y x : S.CompatibleFamily E) = S.restrict m x.1 :=
  φ.coe_fiberRestrict m y x

end FamilyComparison

end RestrictionDatum

/-! ### Binary recovery -/

section BinaryRecovery

variable {C : Type uC} [Preorder C] {S : RestrictionSystem.{uC, uS} C}
  {S' : RestrictionSystem.{uC, uS'} C} {l r b : C} (hl : b ≤ l) (hr : b ≤ r)
  (hb : ∀ ⦃c : C⦄, c ≤ l → c ≤ r → c ≤ b)

/-- The three overlap hypotheses say exactly that `b` is greatest among the common coarser
contexts of `l` and `r`. -/
example :
    IsGreatest (lowerBounds {l, r}) b ↔
      (b ≤ l ∧ b ≤ r) ∧ ∀ ⦃c : C⦄, c ≤ l → c ≤ r → c ≤ b :=
  RestrictionSystem.isGreatest_lowerBounds_pair_iff

/-- A binary family is compatible exactly when its two states agree at `b`. -/
example (x : ∀ i, S.State (![l, r] i)) :
    S.Compatible ![l, r] x ↔ S.res hl (x 0) = S.res hr (x 1) :=
  S.compatible_pair_iff hl hr hb x

/-- Binary compatible families are the compatible pairs of the span at `b`. -/
example : S.CompatibleFamily ![l, r] ≃ Function.Pullback (S.res hl) (S.res hr) :=
  S.binaryEquiv hl hr hb

/-- Round trip: the family of the pair of a compatible family. -/
example (x : S.CompatibleFamily ![l, r]) :
    (S.binaryEquiv hl hr hb).symm (S.binaryEquiv hl hr hb x) = x :=
  S.binaryEquiv_symm_apply_apply hl hr hb x

/-- Round trip: the pair of the family of a compatible pair. -/
example (s : Function.Pullback (S.res hl) (S.res hr)) :
    S.binaryEquiv hl hr hb ((S.binaryEquiv hl hr hb).symm s) = s :=
  S.binaryEquiv_apply_symm_apply hl hr hb s

/-- The family raw comparison is the reduction comparison of the observations at `l`, `b`
and `r`. -/
example (φ : S.Hom S') (x : S.CompatibleFamily ![l, r]) :
    S'.binaryEquiv hl hr hb (φ.mapFamily ![l, r] x) =
      Function.Pullback.map (φ.naturality hl) (φ.naturality hr) (S.binaryEquiv hl hr hb x) :=
  φ.binaryEquiv_mapFamily hl hr hb x

/-- Fine-lift fibers correspond. -/
example (φ : S.Hom S') (y : S'.CompatibleFamily ![l, r]) :
    {x // φ.mapFamily ![l, r] x = y} ≃
      {s // Function.Pullback.map (φ.naturality hl) (φ.naturality hr) s =
        S'.binaryEquiv hl hr hb y} :=
  φ.fiberMapFamilyBinaryEquiv hl hr hb y

/-- A coarse binary family is attained exactly when its pair is. -/
example (φ : S.Hom S') (y : S'.CompatibleFamily ![l, r]) :
    y ∈ Set.range (φ.mapFamily ![l, r]) ↔
      S'.binaryEquiv hl hr hb y ∈
        Set.range (Function.Pullback.map (φ.naturality hl) (φ.naturality hr)) :=
  φ.mem_range_mapFamily_iff_mem_range_map hl hr hb y

/-- The two attained images agree as sets under `binaryEquiv`. -/
example (φ : S.Hom S') :
    S'.binaryEquiv hl hr hb '' Set.range (φ.mapFamily ![l, r]) =
      Set.range (Function.Pullback.map (φ.naturality hl) (φ.naturality hr)) :=
  φ.image_range_mapFamily hl hr hb

/-- The intersection criterion, recovered for binary families. -/
example (φ : S.Hom S') (y : S'.CompatibleFamily ![l, r]) :
    y ∈ Set.range (φ.mapFamily ![l, r]) ↔
      (S.res hl '' (φ.toFun l ⁻¹' {y.1 0}) ∩ S.res hr '' (φ.toFun r ⁻¹' {y.1 1})).Nonempty :=
  φ.mem_range_mapFamily_iff_inter_nonempty hl hr hb y

/-- The observed quotients correspond. -/
example (φ : S.Hom S') :
    Quotient (Setoid.ker (φ.mapFamily ![l, r])) ≃
      Function.Pullback.Observed (φ.naturality hl) (φ.naturality hr) :=
  φ.observedBinaryEquiv hl hr hb

/-- Round trip: the correspondence of quotients after its inverse. -/
example (φ : S.Hom S') (q : Quotient (Setoid.ker (φ.mapFamily ![l, r]))) :
    (φ.observedBinaryEquiv hl hr hb).symm (φ.observedBinaryEquiv hl hr hb q) = q :=
  φ.observedBinaryEquiv_symm_apply_apply hl hr hb q

/-- Round trip: the inverse of the correspondence of quotients after the correspondence. -/
example (φ : S.Hom S') (t : Function.Pullback.Observed (φ.naturality hl) (φ.naturality hr)) :
    φ.observedBinaryEquiv hl hr hb ((φ.observedBinaryEquiv hl hr hb).symm t) = t :=
  φ.observedBinaryEquiv_apply_symm_apply hl hr hb t

/-- The correspondence commutes with the two quotient injections. -/
example (φ : S.Hom S') (q : Quotient (Setoid.ker (φ.mapFamily ![l, r]))) :
    Function.Pullback.observedMap (φ.naturality hl) (φ.naturality hr)
        (φ.observedBinaryEquiv hl hr hb q) =
      S'.binaryEquiv hl hr hb (Setoid.kerLift (φ.mapFamily ![l, r]) q) :=
  φ.observedMap_observedBinaryEquiv hl hr hb q

/-- The exact lifting criterion for binary families. -/
example (φ : S.Hom S') :
    Function.Bijective (Setoid.kerLift (φ.mapFamily ![l, r])) ↔
      ∀ y : S'.CompatibleFamily ![l, r],
        (S.res hl '' (φ.toFun l ⁻¹' {y.1 0}) ∩ S.res hr '' (φ.toFun r ⁻¹' {y.1 1})).Nonempty :=
  φ.bijective_kerLift_mapFamily_iff_forall hl hr hb

end BinaryRecovery

section SharedOverlap

variable {C : Type uC} [Preorder C] {S : RestrictionSystem.{uC, uS} C} {L M R B D : C}
  (hBL : B ≤ L) (hBM : B ≤ M) (hDM : D ≤ M) (hDR : D ≤ R)
  (hB : ∀ ⦃c : C⦄, c ≤ L → c ≤ M → c ≤ B) (hD : ∀ ⦃c : C⦄, c ≤ M → c ≤ R → c ≤ D)
  (hLR : ∀ ⦃c : C⦄, c ≤ L → c ≤ R → c ≤ M)

/-- On the shared-overlap shape compatibility is the two overlap equations. -/
example (x : ∀ i, S.State (![L, M, R] i)) :
    S.Compatible ![L, M, R] x ↔
      S.res hBL (x 0) = S.res hBM (x 1) ∧ S.res hDM (x 1) = S.res hDR (x 2) :=
  S.compatible_triple_iff hBL hBM hDM hDR hB hD hLR x

end SharedOverlap

/-! ### Two calibration cases -/

section SpanCalibration

open Amalgam.Models.Span

/-- `B` is coarser than `L` and than `R`, and is the greatest common coarser context. -/
example : Context.B ≤ Context.L := Context.B_le_L

example : Context.B ≤ Context.R := Context.B_le_R

example : ∀ ⦃c : Context⦄, c ≤ Context.L → c ≤ Context.R → c ≤ Context.B :=
  Context.le_B_of_le_L_of_le_R

/-- The fine system has two states at `L` and one state at `B` and at `R`. -/
example : fine.State Context.L = Bool := rfl

example : fine.State Context.B = Unit := rfl

example : fine.State Context.R = Unit := rfl

/-- The coarse system has one state at every context. -/
example (c : Context) : coarse.State c = Unit := rfl

/-- The observation is the unique map at every context. -/
example : fine.Hom coarse := φ

/-- The coarse compatible families over `![L, R]` are a singleton, whose element is `y₀`. -/
example : Unique (coarse.CompatibleFamily LR) := uniqueCoarseFamily LR

example : coarse.CompatibleFamily LR := y₀

/-- The fine compatible families over `![L, R]` are read by their left state. -/
example : fine.CompatibleFamily LR ≃ Bool := fineEquiv

/-- They are exactly `x₀` and `x₁`, which differ. -/
example (x : fine.CompatibleFamily LR) : x = x₀ ∨ x = x₁ := eq_x₀_or_eq_x₁ x

example : (x₀ : fine.CompatibleFamily LR) ≠ x₁ := x₀_ne_x₁

/-- Both are observed as `y₀`. -/
example : φ.mapFamily LR x₀ = y₀ := mapFamily_x₀

example : φ.mapFamily LR x₁ = y₀ := mapFamily_x₁

/-- The raw fiber over `y₀` is equivalent to `Bool`, with both round trips; this explicit
equivalence is the whole two-element description, with no counting package. -/
example : {x : fine.CompatibleFamily LR // φ.mapFamily LR x = y₀} ≃ Bool := fiberEquiv

example (x : {x : fine.CompatibleFamily LR // φ.mapFamily LR x = y₀}) :
    fiberEquiv.symm (fiberEquiv x) = x :=
  fiberEquiv_symm_apply_apply x

example (b : Bool) : fiberEquiv (fiberEquiv.symm b) = b := fiberEquiv_apply_symm_apply b

/-- The quotient fiber over `y₀` is a singleton, from inhabitedness and the subsingleton
property separately. -/
example : Nonempty {q : φ.observedFamily LR // φ.observedMapFamily LR q = y₀} :=
  nonempty_observedFiber

example : Subsingleton {q : φ.observedFamily LR // φ.observedMapFamily LR q = y₀} :=
  subsingleton_observedFiber

example : Unique {q : φ.observedFamily LR // φ.observedMapFamily LR q = y₀} :=
  uniqueObservedFiber

/-- There is exactly one observed class over the binary family. -/
example : Unique (φ.observedFamily LR) := uniqueObservedFamily

/-- The observed class of `x₀` is the observed class of `x₁`. -/
example :
    (Quotient.mk (Setoid.ker (φ.mapFamily LR)) x₀ : φ.observedFamily LR) =
      Quotient.mk (Setoid.ker (φ.mapFamily LR)) x₁ :=
  observed_x₀_eq_observed_x₁

/-- Under `binaryEquiv` the reduction comparison sends the pairs of `x₀` and `x₁` to one coarse
pair. -/
example :
    Function.Pullback.map (φ.naturality Context.B_le_L) (φ.naturality Context.B_le_R)
        (fine.binaryEquiv Context.B_le_L Context.B_le_R Context.le_B_of_le_L_of_le_R x₀) =
      Function.Pullback.map (φ.naturality Context.B_le_L) (φ.naturality Context.B_le_R)
        (fine.binaryEquiv Context.B_le_L Context.B_le_R Context.le_B_of_le_L_of_le_R x₁) :=
  map_binaryEquiv_x₀_eq

/-- `y₀` is attained, through the intersection criterion. -/
example : y₀ ∈ φ.image LR := y₀_mem_image_of_inter_nonempty

end SpanCalibration

section ZigzagCalibration

open Amalgam.Models.Zigzag

/-- The four generating inequalities of the shared-overlap shape. -/
example : Context.B ≤ Context.L := Context.B_le_L

example : Context.B ≤ Context.M := Context.B_le_M

example : Context.D ≤ Context.M := Context.D_le_M

example : Context.D ≤ Context.R := Context.D_le_R

/-- `B` is greatest among the common coarser contexts of `L` and `M`, `D` among those of `M`
and `R`, and `L` and `R` have no common coarser context. -/
example : ∀ ⦃c : Context⦄, c ≤ Context.L → c ≤ Context.M → c ≤ Context.B :=
  Context.le_B_of_le_L_of_le_M

example : ∀ ⦃c : Context⦄, c ≤ Context.M → c ≤ Context.R → c ≤ Context.D :=
  Context.le_D_of_le_M_of_le_R

example : ∀ ⦃c : Context⦄, c ≤ Context.L → c ≤ Context.R → False := Context.not_le_L_of_le_R

/-- Vacuously, every common coarser context of `L` and `R` lies below `M`, the hypothesis
`compatible_triple_iff` consumes. -/
example : ∀ ⦃c : Context⦄, c ≤ Context.L → c ≤ Context.R → c ≤ Context.M :=
  Context.le_M_of_le_L_of_le_R

/-- Singleton state types at `L`, `M` and `R`, two-point state types at `B` and `D`. -/
example : State Context.L = Unit := rfl

example : State Context.B = Bool := rfl

example : State Context.M = Unit := rfl

example : State Context.D = Bool := rfl

example : State Context.R = Unit := rfl

/-- The coarse system has a singleton state type at every context. -/
example (c : Context) : coarse.State c = Unit := rfl

/-- The two fine systems are the restriction values `(0, 0, 0, 1)` and `(0, 1, 0, 0)` in the
arrow order `L→B, M→B, M→D, R→D`. -/
example : sysA = sys false false false true := rfl

example : sysB = sys false true false false := rfl

/-- Both observations are surjective at every context. -/
example : ∀ c : Context, Function.Surjective (φA.toFun c) := surjective_φA

example : ∀ c : Context, Function.Surjective (φB.toFun c) := surjective_φB

/-- The declared restriction operations forget one view of the full family. -/
example : FamilyMap LMR LM := toLM

example : FamilyMap LMR MR := toMR

/-- Compatibility over each declared family is equations between restriction values. -/
example (lb mb md rd : Bool) (x : ∀ i : Fin 2, State (LM i)) :
    (sys lb mb md rd).Compatible LM x ↔ lb = mb :=
  compatible_LM_iff lb mb md rd x

example (lb mb md rd : Bool) (x : ∀ i : Fin 2, State (MR i)) :
    (sys lb mb md rd).Compatible MR x ↔ md = rd :=
  compatible_MR_iff lb mb md rd x

example (lb mb md rd : Bool) (x : ∀ i : Fin 3, State (LMR i)) :
    (sys lb mb md rd).Compatible LMR x ↔ lb = mb ∧ md = rd :=
  compatible_LMR_iff lb mb md rd x

/-- System A has a compatible family over `LM` and none over `MR` or `LMR`. -/
example : Nonempty (sysA.CompatibleFamily LM) := nonempty_LM_A

example : IsEmpty (sysA.CompatibleFamily MR) := isEmpty_MR_A

example : IsEmpty (sysA.CompatibleFamily LMR) := isEmpty_LMR_A

/-- System B has a compatible family over `MR` and none over `LM` or `LMR`. -/
example : Nonempty (sysB.CompatibleFamily MR) := nonempty_MR_B

example : IsEmpty (sysB.CompatibleFamily LM) := isEmpty_LM_B

example : IsEmpty (sysB.CompatibleFamily LMR) := isEmpty_LMR_B

/-- The table of attainable images, where `Set.univ` is the singleton of coarse families. -/
example : φA.image LM = (Set.univ : Set (coarse.CompatibleFamily LM)) := image_LM_A

example : φA.image MR = (∅ : Set (coarse.CompatibleFamily MR)) := image_MR_A

example : φA.image LMR = (∅ : Set (coarse.CompatibleFamily LMR)) := image_LMR_A

example : φB.image LM = (∅ : Set (coarse.CompatibleFamily LM)) := image_LM_B

example : φB.image MR = (Set.univ : Set (coarse.CompatibleFamily MR)) := image_MR_B

example : φB.image LMR = (∅ : Set (coarse.CompatibleFamily LMR)) := image_LMR_B

/-- The inclusion supplied by naturality is strict in both systems. -/
example : coarse.restrict toLM '' φA.image LMR ⊂ φA.image LM := ssubset_restrict_image_LMR_A

example : coarse.restrict toMR '' φB.image LMR ⊂ φB.image MR := ssubset_restrict_image_LMR_B

/-- Neither induced map on attainable images is surjective. -/
example : ¬Function.Surjective (φA.restrictImage toLM) := not_surjective_restrictImage_A

example : ¬Function.Surjective (φB.restrictImage toMR) := not_surjective_restrictImage_B

/-- Equal full-family images, different `LM` and `MR` images: full-family content does not
determine all-family content. -/
example : φA.image LMR = φB.image LMR := image_LMR_eq

example : φA.image LM ≠ φB.image LM := image_LM_ne

example : φA.image MR ≠ φB.image MR := image_MR_ne

end ZigzagCalibration

/-! ## Four comparison behaviors -/

section Behaviors

open Amalgam.Models.Overlap

/-- Each of the four comparison maps goes from its global type to the compatible pairs of the
common span. -/
example : G₁ → p.Pullback q := compare₁

example : G₂ → p.Pullback q := compare₂

example : G₃ → p.Pullback q := compare₃

example : G₄ → p.Pullback q := compare₄

/-- Each of the four is the comparison map of its commuting square. -/
example : compare₁ = Function.Pullback.lift f₁ g₁ comm₁ := rfl

example : compare₂ = Function.Pullback.lift f₂ g₂ comm₂ := rfl

example : compare₃ = Function.Pullback.lift f₃ g₃ comm₃ := rfl

example : compare₄ = Function.Pullback.lift f₄ g₄ comm₄ := rfl

/-- Two local views are compatible exactly when their overlap values agree. -/
example (l : L) (r : R) : p l = q r ↔ l.1 = r.1 := Iff.rfl

/-- The overlap is not a subsingleton, so compatibility is a genuine constraint. -/
example : ¬Subsingleton B := fun hB => Bool.false_ne_true (hB.allEq false true)

/-! ### Bijective -/

example : Function.Bijective compare₁ := bijective_compare₁

/-! ### Injective, not surjective -/

example : Function.Injective compare₂ := injective_compare₂

example : ¬Function.Surjective compare₂ := not_surjective_compare₂

example : ¬Function.Bijective compare₂ := not_bijective_compare₂

/-- The unreached pair is compatible. -/
example : p unreached₂.fst = q unreached₂.snd := Function.Pullback.comm unreached₂

/-- The unreached pair has no global extension. -/
example : IsEmpty {s // compare₂ s = unreached₂} := isEmpty_fiber_unreached₂

/-- Uniqueness without existence: the same empty fiber is a subsingleton. -/
example : Subsingleton {s // compare₂ s = unreached₂} :=
  (Function.Pullback.injective_lift_iff_forall_subsingleton (f := f₂) (g := g₂) comm₂).1
    injective_compare₂ unreached₂

/-! ### Surjective, not injective -/

example : Function.Surjective compare₃ := surjective_compare₃

example : ¬Function.Injective compare₃ := not_injective_compare₃

example : ¬Function.Bijective compare₃ := not_bijective_compare₃

/-- Two distinct global states with equal comparison value. -/
example : state₃ ≠ state₃' := state₃_ne_state₃'

example : compare₃ state₃ = compare₃ state₃' := compare₃_state₃_eq

/-! ### Neither -/

example : ¬Function.Injective compare₄ := not_injective_compare₄

example : ¬Function.Surjective compare₄ := not_surjective_compare₄

example : ¬Function.Bijective compare₄ := not_bijective_compare₄

/-- The unreached pair is compatible and has no global extension. -/
example : p unreached₄.fst = q unreached₄.snd := Function.Pullback.comm unreached₄

example : IsEmpty {s // compare₄ s = unreached₄} := isEmpty_fiber_unreached₄

/-- Two distinct global states with equal comparison value. -/
example : state₄ ≠ state₄' := state₄_ne_state₄'

example : compare₄ state₄ = compare₄ state₄' := compare₄_state₄_eq

end Behaviors

end Amalgam.Status
