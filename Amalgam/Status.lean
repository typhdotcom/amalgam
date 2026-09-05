import Amalgam.Core.Comparison
import Amalgam.Core.Fiber
import Amalgam.Core.Reduction
import Amalgam.Models.Lifting
import Amalgam.Models.Overlap

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

universe uX uY uZ uX' uY' uL' uR' uG' uB' uLf uRf uBf uLc uRc uBc

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
