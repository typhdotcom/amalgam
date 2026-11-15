import Amalgam.Core.Comparison
import Mathlib.Data.Fintype.Prod

/-!
# Four certified comparison behaviors

Explicit finite commuting squares realizing the four comparison behaviors: a comparison map that
is bijective, one that is injective but not surjective, one that is surjective but not injective,
and one that is neither.

All four squares share the same span `L ─p→ B ←q─ R` with `B = Bool`, `L = R = Bool × Bool` and
`p = q = Prod.fst`: a local view is an overlap value together with one private coordinate, and a
pair of local views is compatible exactly when the overlap values agree. The overlap therefore has
two elements and compatibility is a genuine constraint, discarding half of `L × R`. Only the global
type `G` and the two restriction maps `f`, `g` change between the four squares, so the four
behaviors are four different global realizations of one and the same local situation.

Failures of existence are certified by an explicit compatible pair together with `IsEmpty` for its
comparison fiber; failures of uniqueness by two distinct global states with equal comparison value.
The positive properties are obtained from the criteria of `Amalgam.Core.Comparison`.

The opposite extreme, a trivial overlap, needs no witness here: for `Subsingleton B` every pair of
local views is compatible and `Function.Pullback.equivProdOfSubsingleton` identifies the compatible
pairs with `L × R` generically.
-/

namespace Amalgam.Models.Overlap

/-! ### The common span -/

/-- The overlap: two admissible values. -/
abbrev B := Bool

/-- The left local view: an overlap value and one private coordinate; four elements. -/
abbrev L := Bool × Bool

/-- The right local view: an overlap value and one private coordinate; four elements. -/
abbrev R := Bool × Bool

/-- The left restriction to the overlap, `(b, x) ↦ b`. -/
def p : L → B := Prod.fst

/-- The right restriction to the overlap, `(b, y) ↦ b`. -/
def q : R → B := Prod.fst

/-! ### A bijective comparison -/

/-- Global states of the first square: an overlap value and both private coordinates; eight
elements. -/
abbrev G₁ := Bool × Bool × Bool

/-- Left view of a global state, `(b, x, y) ↦ (b, x)`. -/
def f₁ : G₁ → L := fun s => (s.1, s.2.1)

/-- Right view of a global state, `(b, x, y) ↦ (b, y)`. -/
def g₁ : G₁ → R := fun s => (s.1, s.2.2)

/-- The first square commutes: both views restrict to the overlap value `b`. -/
theorem comm₁ : ∀ s, p (f₁ s) = q (g₁ s) := fun _ => rfl

/-- The comparison map of the first square, from eight global states to eight compatible pairs. -/
def compare₁ : G₁ → p.Pullback q := Function.Pullback.lift f₁ g₁ comm₁

/-- Every compatible pair has exactly one global extension. -/
theorem bijective_compare₁ : Function.Bijective compare₁ :=
  (Function.Pullback.bijective_lift_iff (f := f₁) (g := g₁) comm₁).2 (by decide)

/-! ### An injective, nonsurjective comparison -/

/-- Global states of the second square: an overlap value and a single coordinate seen by both
views; four elements. -/
abbrev G₂ := Bool × Bool

/-- Left view of a global state, `(b, x) ↦ (b, x)`. -/
def f₂ : G₂ → L := fun s => s

/-- Right view of a global state, `(b, x) ↦ (b, x)`. -/
def g₂ : G₂ → R := fun s => s

/-- The second square commutes: both views restrict to the overlap value `b`. -/
theorem comm₂ : ∀ s, p (f₂ s) = q (g₂ s) := fun _ => rfl

/-- The comparison map of the second square, from four global states to eight compatible pairs. -/
def compare₂ : G₂ → p.Pullback q := Function.Pullback.lift f₂ g₂ comm₂

/-- Global extensions are unique when they exist. -/
theorem injective_compare₂ : Function.Injective compare₂ :=
  (Function.Pullback.injective_lift_iff (f := f₂) (g := g₂) comm₂).2 (by decide)

/-- The compatible pair whose two local views disagree on the private coordinate. -/
def unreached₂ : p.Pullback q := Function.Pullback.mk (true, true) (true, false) rfl

/-- The unreached pair has no global extension. -/
theorem isEmpty_fiber_unreached₂ : IsEmpty {s // compare₂ s = unreached₂} :=
  (Function.Pullback.isEmpty_fiber_lift_iff (f := f₂) (g := g₂) comm₂ unreached₂).2 (by decide)

/-- Existence fails: `unreached₂` is compatible but has no global extension. -/
theorem not_surjective_compare₂ : ¬Function.Surjective compare₂ := fun hs =>
  isEmpty_fiber_unreached₂.elim
    ((Function.Pullback.surjective_lift_iff_forall_nonempty (f := f₂) (g := g₂) comm₂).1 hs
      unreached₂).some

/-- The second comparison is not bijective. -/
theorem not_bijective_compare₂ : ¬Function.Bijective compare₂ := fun hb =>
  not_surjective_compare₂ hb.2

/-! ### A surjective, noninjective comparison -/

/-- Global states of the third square: the eight states of the first square together with an
invisible fourth coordinate; sixteen elements. -/
abbrev G₃ := Bool × Bool × Bool × Bool

/-- Left view of a global state, `(b, x, y, z) ↦ (b, x)`. -/
def f₃ : G₃ → L := fun s => (s.1, s.2.1)

/-- Right view of a global state, `(b, x, y, z) ↦ (b, y)`. -/
def g₃ : G₃ → R := fun s => (s.1, s.2.2.1)

/-- The third square commutes: both views restrict to the overlap value `b`. -/
theorem comm₃ : ∀ s, p (f₃ s) = q (g₃ s) := fun _ => rfl

/-- The comparison map of the third square, from sixteen global states to eight compatible
pairs. -/
def compare₃ : G₃ → p.Pullback q := Function.Pullback.lift f₃ g₃ comm₃

/-- Every compatible pair has a global extension. -/
theorem surjective_compare₃ : Function.Surjective compare₃ :=
  (Function.Pullback.surjective_lift_iff (f := f₃) (g := g₃) comm₃).2 (by decide)

/-- A global state whose fourth coordinate is `false`. -/
def state₃ : G₃ := (false, false, false, false)

/-- The same state with the invisible fourth coordinate flipped. -/
def state₃' : G₃ := (false, false, false, true)

/-- The two states are distinct. -/
theorem state₃_ne_state₃' : state₃ ≠ state₃' := by decide

/-- The two distinct states have the same comparison value. -/
theorem compare₃_state₃_eq : compare₃ state₃ = compare₃ state₃' := rfl

/-- Uniqueness fails: two distinct global states restrict to the same compatible pair. -/
theorem not_injective_compare₃ : ¬Function.Injective compare₃ := fun hi =>
  state₃_ne_state₃' (hi compare₃_state₃_eq)

/-- The third comparison is not bijective. -/
theorem not_bijective_compare₃ : ¬Function.Bijective compare₃ := fun hb =>
  not_injective_compare₃ hb.1

/-! ### A comparison that is neither -/

/-- Global states of the fourth square: an overlap value and a coordinate neither view sees; four
elements. -/
abbrev G₄ := Bool × Bool

/-- Left view of a global state, `(b, x) ↦ (b, false)`. -/
def f₄ : G₄ → L := fun s => (s.1, false)

/-- Right view of a global state, `(b, x) ↦ (b, false)`. -/
def g₄ : G₄ → R := fun s => (s.1, false)

/-- The fourth square commutes: both views restrict to the overlap value `b`. -/
theorem comm₄ : ∀ s, p (f₄ s) = q (g₄ s) := fun _ => rfl

/-- The comparison map of the fourth square, from four global states to eight compatible pairs. -/
def compare₄ : G₄ → p.Pullback q := Function.Pullback.lift f₄ g₄ comm₄

/-- A compatible pair whose local views both carry the private coordinate `true`. -/
def unreached₄ : p.Pullback q := Function.Pullback.mk (true, true) (true, true) rfl

/-- The unreached pair has no global extension. -/
theorem isEmpty_fiber_unreached₄ : IsEmpty {s // compare₄ s = unreached₄} :=
  (Function.Pullback.isEmpty_fiber_lift_iff (f := f₄) (g := g₄) comm₄ unreached₄).2 (by decide)

/-- Existence fails: `unreached₄` is compatible but has no global extension. -/
theorem not_surjective_compare₄ : ¬Function.Surjective compare₄ := fun hs =>
  isEmpty_fiber_unreached₄.elim
    ((Function.Pullback.surjective_lift_iff_forall_nonempty (f := f₄) (g := g₄) comm₄).1 hs
      unreached₄).some

/-- A global state whose second coordinate is `false`. -/
def state₄ : G₄ := (false, false)

/-- The same state with the invisible second coordinate flipped. -/
def state₄' : G₄ := (false, true)

/-- The two states are distinct. -/
theorem state₄_ne_state₄' : state₄ ≠ state₄' := by decide

/-- The two distinct states have the same comparison value. -/
theorem compare₄_state₄_eq : compare₄ state₄ = compare₄ state₄' := rfl

/-- Uniqueness fails: two distinct global states restrict to the same compatible pair. -/
theorem not_injective_compare₄ : ¬Function.Injective compare₄ := fun hi =>
  state₄_ne_state₄' (hi compare₄_state₄_eq)

/-- The fourth comparison is not bijective. -/
theorem not_bijective_compare₄ : ¬Function.Bijective compare₄ := fun hb =>
  not_injective_compare₄ hb.1

end Amalgam.Models.Overlap
