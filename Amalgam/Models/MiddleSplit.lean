import Amalgam.System.Binary
import Amalgam.System.Comparison
import Amalgam.System.Zigzag

/-!
# M3.1: a strict information-loss witness for the adjacent binary datum

Two candidate realizations over the same coarse system on `Zigzag.Context` with the same supplied
datum `(I_LM, I_MR)` and different full images `I_LMR`. The supplied datum therefore does not
determine the whole reconstruction target.

The coarse system `coarse` has one state at every context, so over every family its compatible
families form a singleton (`uniqueCoarseFamily`) and every attainable image is `∅` or `Set.univ`.

The fine system `split` has two middle states and is the whole content of the witness:

```text
Context    L       M        R       B       D
State      Unit    Bool     Unit    Bool    Bool
```

with restrictions `L→B : _ ↦ false`, `M→B : m ↦ m`, `M→D : m ↦ m`, `R→D : _ ↦ true`, the identity
on every reflexive arrow. Compatibility over `![L, M]` forces the middle state to be `false` and
over `![M, R]` forces it to be `true` (`compatible_LM_split_iff`, `compatible_MR_split_iff`), so
both adjacent binary lifts exist but use different fine middle states and no lift of the full
family exists (`compatible_LMR_split_iff`). The fine system `glue` has one state at every context
and lifts everything.

```text
System   I_LM    I_MR    I_LMR
split    univ    univ    ∅
glue     univ    univ    univ
```

Both observations `φsplit`, `φglue` are surjective at every context, and all four adjacent binary
comparisons are surjective onto the coarse binary families. The strict pair is
`image_LM_eq`, `image_MR_eq`, `image_LMR_ne`, with the coarse family `y₀` attained by `glue`
(`y₀_mem_image_glue`) and not by `split` (`y₀_notMem_image_split`).

The supplied datum records that each adjacent view lifts; it records no fine middle state and no
identification of the two independently chosen lifts. `split` exploits exactly that gap: the `LM`
lift uses the middle state `false`, the `MR` lift uses `true`, and nothing in `(I_LM, I_MR)`
distinguishes this from `glue`, where a single middle state serves both. No minimality claim is
made. The bounded finite sweep behind this choice is recorded in `scripts/zigzag_sweep.py`.
-/

open Zigzag Zigzag.Context

namespace Amalgam.Models.MiddleSplit

/-! ### The coarse system -/

/-- The coarse restriction system: one state at every context. -/
def coarse : RestrictionSystem Context where
  State _ := Unit
  res _ _ := ()
  res_refl _ _ := rfl
  res_trans _ _ _ := rfl

/-- Over any family of contexts the coarse compatible families form a singleton. -/
instance uniqueCoarseFamily {ι : Type*} (F : ι → Context) :
    Unique (coarse.CompatibleFamily F) where
  default := ⟨fun _ => (), fun _ _ _ _ _ => rfl⟩
  uniq _ := Subtype.ext (funext fun _ => rfl)

/-! ### The fine system with a split middle -/

/-- Fine state types of `split`: two middle states, two states at each overlap, singletons at the
outer views. -/
def State : Context → Type
  | L => Unit
  | B => Bool
  | M => Bool
  | D => Bool
  | R => Unit

/-- Fine restriction of `split`: `L→B ↦ false`, `M→B` and `M→D` the identity, `R→D ↦ true`, and
the identity on every reflexive arrow. -/
def res : ∀ {c d : Context}, c ≤ d → State d → State c
  | L, _, _, _ => ()
  | R, _, _, _ => ()
  | M, M, _, x => x
  | M, L, h, _ => False.elim h
  | M, B, h, _ => False.elim h
  | M, D, h, _ => False.elim h
  | M, R, h, _ => False.elim h
  | B, B, _, x => x
  | B, L, _, _ => false
  | B, M, _, x => x
  | B, D, h, _ => False.elim h
  | B, R, h, _ => False.elim h
  | D, D, _, x => x
  | D, M, _, x => x
  | D, R, _, _ => true
  | D, L, h, _ => False.elim h
  | D, B, h, _ => False.elim h

/-- The fine system whose two adjacent binary lifts are forced to use different middle states. -/
def split : RestrictionSystem Context where
  State := State
  res := res
  res_refl := by
    intro c h x
    cases c <;> rfl
  res_trans := by
    intro c d e h₁ h₂ x
    cases c <;> cases d <;> cases e <;> first | rfl | exact False.elim h₁ | exact False.elim h₂

/-- The fine states of the `LM` lift: middle state `false`. -/
def pointFalse : ∀ c, State c
  | L => ()
  | B => false
  | M => false
  | D => false
  | R => ()

/-- The fine states of the `MR` lift: middle state `true`. -/
def pointTrue : ∀ c, State c
  | L => ()
  | B => true
  | M => true
  | D => true
  | R => ()

/-- The observation of `split`: the unique map at every context; naturality holds on the nose. -/
def φsplit : split.Hom coarse where
  toFun _ _ := ()
  naturality _ _ := rfl

/-- Every component observation of `split` is surjective, hit by `pointFalse`. -/
theorem surjective_φsplit : ∀ c, Function.Surjective (φsplit.toFun c) :=
  fun c _ => ⟨pointFalse c, rfl⟩

/-! ### The fine system with a single middle state -/

/-- The fine system with one state at every context. -/
def glue : RestrictionSystem Context where
  State _ := Unit
  res _ _ := ()
  res_refl _ _ := rfl
  res_trans _ _ _ := rfl

/-- Every family of states of `glue` is compatible: all restrictions land in a singleton. -/
theorem compatible_glue {ι : Type*} (F : ι → Context) (x : ∀ i, glue.State (F i)) :
    glue.Compatible F x :=
  fun _ _ _ _ _ => rfl

/-- The observation of `glue`: the unique map at every context. -/
def φglue : glue.Hom coarse where
  toFun _ _ := ()
  naturality _ _ := rfl

/-- Every component observation of `glue` is surjective. -/
theorem surjective_φglue : ∀ c, Function.Surjective (φglue.toFun c) :=
  fun _ _ => ⟨(), rfl⟩

/-! ### Compatibility over each family -/

/-- A family of `split` over `![L, M]` is compatible exactly when its middle state is `false`, by
`compatible_pair_iff` at the greatest common coarser context `B`. -/
theorem compatible_LM_split_iff (x : ∀ i, State (LM i)) :
    split.Compatible LM x ↔ x 1 = false :=
  (split.compatible_pair_iff B_le_L B_le_M le_B_of_le_L_of_le_M x).trans eq_comm

/-- A family of `split` over `![M, R]` is compatible exactly when its middle state is `true`, by
`compatible_pair_iff` at the greatest common coarser context `D`. -/
theorem compatible_MR_split_iff (x : ∀ i, State (MR i)) :
    split.Compatible MR x ↔ x 0 = true :=
  split.compatible_pair_iff D_le_M D_le_R le_D_of_le_M_of_le_R x

/-- A family of `split` over `![L, M, R]` is compatible exactly when its middle state is both
`false` and `true`, by `compatible_triple_iff`. -/
theorem compatible_LMR_split_iff (x : ∀ i, State (LMR i)) :
    split.Compatible LMR x ↔ x 1 = false ∧ x 1 = true :=
  (split.compatible_triple_iff B_le_L B_le_M D_le_M D_le_R le_B_of_le_L_of_le_M
    le_D_of_le_M_of_le_R le_M_of_le_L_of_le_R x).trans (and_congr eq_comm Iff.rfl)

/-- No family of `split` over `![L, M, R]` is compatible: the two adjacent lifts disagree. -/
theorem not_compatible_LMR_split (x : ∀ i, State (LMR i)) : ¬ split.Compatible LMR x := fun h =>
  let hx := (compatible_LMR_split_iff x).1 h
  Bool.false_ne_true (hx.1.symm.trans hx.2)

/-! ### Fine compatible families -/

/-- `split` has a compatible family over `![L, M]`, with middle state `false`. -/
theorem nonempty_LM_split : Nonempty (split.CompatibleFamily LM) :=
  ⟨⟨fun i => pointFalse (LM i), (compatible_LM_split_iff _).2 rfl⟩⟩

/-- `split` has a compatible family over `![M, R]`, with middle state `true`. -/
theorem nonempty_MR_split : Nonempty (split.CompatibleFamily MR) :=
  ⟨⟨fun i => pointTrue (MR i), (compatible_MR_split_iff _).2 rfl⟩⟩

/-- `split` has no compatible family over `![L, M, R]`. -/
theorem isEmpty_LMR_split : IsEmpty (split.CompatibleFamily LMR) :=
  ⟨fun x => not_compatible_LMR_split x.1 x.2⟩

/-- `glue` has a compatible family over `![L, M, R]`. -/
theorem nonempty_LMR_glue : Nonempty (glue.CompatibleFamily LMR) :=
  ⟨⟨fun _ => (), compatible_glue LMR _⟩⟩

/-! ### The attainable images -/

/-- `I_LM` of `split` is everything: the only coarse family has the fine lift `pointFalse`. -/
theorem image_LM_split : φsplit.image LM = Set.univ :=
  Set.eq_univ_of_forall fun y =>
    (φsplit.mem_image_iff y).2
      ⟨fun i => pointFalse (LM i), (compatible_LM_split_iff _).2 rfl, fun _ => rfl⟩

/-- `I_MR` of `split` is everything: the only coarse family has the fine lift `pointTrue`. -/
theorem image_MR_split : φsplit.image MR = Set.univ :=
  Set.eq_univ_of_forall fun y =>
    (φsplit.mem_image_iff y).2
      ⟨fun i => pointTrue (MR i), (compatible_MR_split_iff _).2 rfl, fun _ => rfl⟩

/-- `I_LMR` of `split` is empty: there is no fine compatible family over `![L, M, R]`. -/
theorem image_LMR_split : φsplit.image LMR = ∅ := Set.range_eq_empty_iff.2 isEmpty_LMR_split

/-- `I_LM` of `glue` is everything. -/
theorem image_LM_glue : φglue.image LM = Set.univ :=
  Set.eq_univ_of_forall fun y =>
    (φglue.mem_image_iff y).2 ⟨fun _ => (), compatible_glue LM _, fun _ => rfl⟩

/-- `I_MR` of `glue` is everything. -/
theorem image_MR_glue : φglue.image MR = Set.univ :=
  Set.eq_univ_of_forall fun y =>
    (φglue.mem_image_iff y).2 ⟨fun _ => (), compatible_glue MR _, fun _ => rfl⟩

/-- `I_LMR` of `glue` is everything. -/
theorem image_LMR_glue : φglue.image LMR = Set.univ :=
  Set.eq_univ_of_forall fun y =>
    (φglue.mem_image_iff y).2 ⟨fun _ => (), compatible_glue LMR _, fun _ => rfl⟩

/-! ### The strict pair -/

/-- The two candidates supply the same `I_LM`. -/
theorem image_LM_eq : φsplit.image LM = φglue.image LM := by
  rw [image_LM_split, image_LM_glue]

/-- The two candidates supply the same `I_MR`. -/
theorem image_MR_eq : φsplit.image MR = φglue.image MR := by
  rw [image_MR_split, image_MR_glue]

/-- The two candidates have different `I_LMR`: equal supplied data conceal different full
images. -/
theorem image_LMR_ne : φsplit.image LMR ≠ φglue.image LMR := by
  rw [image_LMR_split, image_LMR_glue]
  exact Set.empty_ne_univ

/-- The unique coarse compatible family over `![L, M, R]`, separating the two candidates. -/
def y₀ : coarse.CompatibleFamily LMR := default

/-- `y₀` is attained by `glue`. -/
theorem y₀_mem_image_glue : y₀ ∈ φglue.image LMR :=
  Set.eq_univ_iff_forall.1 image_LMR_glue y₀

/-- `y₀` is not attained by `split`. -/
theorem y₀_notMem_image_split : y₀ ∉ φsplit.image LMR := by
  rw [image_LMR_split]
  exact Set.notMem_empty y₀

/-! ### Surjectivity of the adjacent binary comparisons -/

/-- The `LM` comparison of `split` is surjective onto the coarse binary families. -/
theorem surjective_observedMapFamily_LM_split :
    Function.Surjective (φsplit.observedMapFamily LM) :=
  Set.range_eq_univ.1 ((φsplit.range_observedMapFamily (F := LM)).trans image_LM_split)

/-- The `MR` comparison of `split` is surjective onto the coarse binary families. -/
theorem surjective_observedMapFamily_MR_split :
    Function.Surjective (φsplit.observedMapFamily MR) :=
  Set.range_eq_univ.1 ((φsplit.range_observedMapFamily (F := MR)).trans image_MR_split)

/-- The `LM` comparison of `glue` is surjective onto the coarse binary families. -/
theorem surjective_observedMapFamily_LM_glue :
    Function.Surjective (φglue.observedMapFamily LM) :=
  Set.range_eq_univ.1 ((φglue.range_observedMapFamily (F := LM)).trans image_LM_glue)

/-- The `MR` comparison of `glue` is surjective onto the coarse binary families. -/
theorem surjective_observedMapFamily_MR_glue :
    Function.Surjective (φglue.observedMapFamily MR) :=
  Set.range_eq_univ.1 ((φglue.range_observedMapFamily (F := MR)).trans image_MR_glue)

end Amalgam.Models.MiddleSplit
