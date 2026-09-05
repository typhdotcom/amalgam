import Amalgam.System.Binary
import Amalgam.System.Comparison
import Amalgam.System.Presentation
import Amalgam.System.Restriction
import Amalgam.System.Zigzag

/-!
# Candidate realizations and the reconstruction target on the zigzag

Fix a coarse restriction system `S'` on the shape `L → B ← M → D ← R` of
`Amalgam/System/Zigzag.lean`. A *candidate realization* (`Candidate S'`) is a fine restriction
system `S` with a morphism `φ : S.Hom S'` whose observation at every context is surjective. No
finiteness of the fine carriers, nonemptiness of global families, or surjectivity of family
restrictions is imposed.

The *supplied datum* of a candidate (`Candidate.datum`) is the ordered pair `(I_LM, I_MR)` of
attainable images over the declared binary families `LM` and `MR`, as subsets of the fixed coarse
compatible-family types. The *target* (`Candidate.target : Target S'`) collects the attainable
image `I_F` of every declared family

```text
empty, single L, single M, single R, LM, LR, MR, LMR
```

as a subset of the fixed coarse type over `F`. The target equivalence is equality of all eight
subsets (`Target.ext_iff`): not bijection of images, not presentation equivalence.

## Results

* `image_empty`, `image_single`, `image_LR`: every candidate has the full coarse image on the
  empty family, on each singleton, and on `LR`. The empty family has one compatible family on
  either side; a singleton family is a state, so surjectivity of the observation suffices; over
  `LR` every pair of states is compatible because `L` and `R` have no common coarser context
  (`compatible_LR`, from `Context.not_le_L_of_le_R`).
* `nonempty_LMR_iff_of_subsingleton_middle`: for a fine system whose middle carrier is a
  subsingleton, the full family has a compatible lift exactly when both adjacent pairs do. The
  forward direction restricts along `toLM`, `toMR` (`nonempty_LM_and_MR_of_nonempty_LMR`); the
  reverse combines the two supplied lifts at their common middle state
  (`exists_LMR_of_subsingleton_middle`, `nonempty_LMR_of_subsingleton_middle`). No finiteness,
  decidability, nonemptiness, or surjectivity is used.
* `Candidate.target_lm`, `Candidate.target_mr`: the remaining proper images are the supplied
  datum.
* `Candidate.target_eq_iff`: two candidates have the same target exactly when they have the same
  supplied datum and the same full image `I_LMR`. This licenses treating `I_LMR` as the remaining
  joint question at fixed datum. It is not an assumption that the full image projects onto any
  proper image; the naturality inclusion `restrict(I_F) ⊆ I_E` (`Hom.image_restrict_subset`) is
  all that relates the entries.
* `coe_restrictImage_eq`, `restrictImage_setCongr`, `Candidate.restrictImage_setCongr_of_target_eq`:
  the induced image restriction maps of two candidates agree on underlying coarse families, and
  commute with the identifications of equal images, because both restrict the fixed coarse map
  `S'.restrict m`. The set-level inclusion `S'.restrict m '' I_F ⊆ I_E` is literally the same
  statement for equal targets, so it is not restated.
-/

universe v v₁ v₂ w

namespace Zigzag

open Context RestrictionSystem

section Images

variable {S : RestrictionSystem.{0, v} Context} {S' : RestrictionSystem.{0, w} Context}

/-- A family over a single view is always compatible: the only comparisons are of a state with
itself. -/
theorem compatible_single (S : RestrictionSystem.{0, v} Context) (c : Context)
    (x : ∀ i, S.State (single c i)) : S.Compatible (single c) x := by
  intro _ i j _ _
  obtain rfl := Subsingleton.elim i j
  rfl

/-- A family over the two outer views is always compatible: `L` and `R` have no common coarser
context, so there is no cross condition. -/
theorem compatible_LR (S : RestrictionSystem.{0, v} Context) (x : ∀ i, S.State (LR i)) :
    S.Compatible LR x :=
  (S.compatible_fin_two_iff LR x).2 fun _ hl hr => (not_le_L_of_le_R hl hr).elim

/-! ### Collapse of the full family at a single fine middle state -/

/-- A compatible full family restricts to compatible families over both adjacent pairs, along
`toLM` and `toMR`. No hypothesis on the fine system is used. -/
theorem nonempty_LM_and_MR_of_nonempty_LMR (S : RestrictionSystem.{0, v} Context)
    (h : Nonempty (S.CompatibleFamily LMR)) :
    Nonempty (S.CompatibleFamily LM) ∧ Nonempty (S.CompatibleFamily MR) :=
  ⟨h.map (S.restrict toLM), h.map (S.restrict toMR)⟩

/-- With a single fine middle state, a compatible `LM`-family and a compatible `MR`-family
combine into a compatible full family restricting to both: their middle states agree by
`Subsingleton.elim`, so the two overlap equations of `compatible_triple_iff` are those of the two
pairs (`compatible_pair_iff`). -/
theorem exists_LMR_of_subsingleton_middle (S : RestrictionSystem.{0, v} Context)
    [Subsingleton (S.State M)] (a : S.CompatibleFamily LM) (a' : S.CompatibleFamily MR) :
    ∃ x : S.CompatibleFamily LMR, S.restrict toLM x = a ∧ S.restrict toMR x = a' := by
  have e : (a.1 1 : S.State M) = a'.1 0 := @Subsingleton.elim (S.State M) _ _ _
  refine ⟨⟨Fin.cons (a.1 0) (Fin.cons (a.1 1) (Fin.cons (a'.1 1) finZeroElim)),
    (S.compatible_triple_iff B_le_L B_le_M D_le_M D_le_R le_B_of_le_L_of_le_M
      le_D_of_le_M_of_le_R le_M_of_le_L_of_le_R _).2
      ⟨(S.compatible_pair_iff B_le_L B_le_M le_B_of_le_L_of_le_M a.1).1 a.2,
        (congrArg (S.res D_le_M) e).trans
          ((S.compatible_pair_iff D_le_M D_le_R le_D_of_le_M_of_le_R a'.1).1 a'.2)⟩⟩,
    Subtype.ext (funext fun i => match i with | 0 => S.res_refl _ _ | 1 => S.res_refl _ _),
    Subtype.ext (funext fun i => match i with
      | 0 => (S.res_refl _ _).trans e
      | 1 => S.res_refl _ _)⟩

/-- With a single fine middle state, the full family has a compatible lift as soon as both
adjacent pairs do. -/
theorem nonempty_LMR_of_subsingleton_middle (S : RestrictionSystem.{0, v} Context)
    [Subsingleton (S.State M)] (hLM : Nonempty (S.CompatibleFamily LM))
    (hMR : Nonempty (S.CompatibleFamily MR)) : Nonempty (S.CompatibleFamily LMR) :=
  let ⟨a⟩ := hLM
  let ⟨a'⟩ := hMR
  let ⟨x, _⟩ := exists_LMR_of_subsingleton_middle S a a'
  ⟨x⟩

/-- The collapse at a single fine middle state: for any fine system on the shape whose middle
carrier is a subsingleton, the full family has a compatible lift exactly when both adjacent pairs
do. No finiteness, decidability, nonemptiness, or surjectivity hypothesis is used. -/
theorem nonempty_LMR_iff_of_subsingleton_middle (S : RestrictionSystem.{0, v} Context)
    [Subsingleton (S.State M)] :
    Nonempty (S.CompatibleFamily LMR) ↔
      Nonempty (S.CompatibleFamily LM) ∧ Nonempty (S.CompatibleFamily MR) :=
  ⟨nonempty_LM_and_MR_of_nonempty_LMR S,
    fun h => nonempty_LMR_of_subsingleton_middle S h.1 h.2⟩

variable (φ : S.Hom S')

/-- The attainable image on the empty family is everything: both compatible-family types over
`Fin 0` are singletons. -/
theorem image_empty : φ.image empty = Set.univ :=
  Set.eq_univ_of_forall fun _ => ⟨default, Subsingleton.elim _ _⟩

/-- The attainable image on a single view is everything once the observation at that view is
surjective: a family over `Fin 1` is a state, and compatibility is automatic. -/
theorem image_single (c : Context) (h : Function.Surjective (φ.toFun c)) :
    φ.image (single c) = Set.univ :=
  Set.eq_univ_of_forall fun y => by
    obtain ⟨x, hx⟩ := h (y.1 0)
    exact ⟨⟨Fin.cons x finZeroElim, compatible_single S c _⟩,
      (φ.mapFamily_eq_iff _ y).2 (Fin.forall_fin_one.2 hx)⟩

/-- The attainable image on the two outer views is everything once the observations at `L` and
`R` are surjective: any two states form a compatible family over `LR`. -/
theorem image_LR (hL : Function.Surjective (φ.toFun L)) (hR : Function.Surjective (φ.toFun R)) :
    φ.image LR = Set.univ :=
  Set.eq_univ_of_forall fun y => by
    obtain ⟨a, ha⟩ := hL (y.1 0)
    obtain ⟨b, hb⟩ := hR (y.1 1)
    exact ⟨⟨Fin.cons a (Fin.cons b finZeroElim), compatible_LR S _⟩,
      (φ.mapFamily_eq_iff _ y).2 (Fin.forall_fin_two.2 ⟨ha, hb⟩)⟩

end Images

/-! ### Candidates, datum, and target -/

/-- A candidate realization of the coarse system `S'`: a fine restriction system with an
objectwise surjective observation. No finiteness of fine carriers, nonemptiness of global
families, or surjectivity of family restrictions is imposed. -/
structure Candidate (S' : RestrictionSystem.{0, w} Context) where
  /-- The fine restriction system. -/
  S : RestrictionSystem.{0, v} Context
  /-- The observation morphism. -/
  φ : S.Hom S'
  /-- The observation at every context is surjective. -/
  surjective : ∀ c, Function.Surjective (φ.toFun c)

/-- The reconstruction target: one subset of the fixed coarse compatible-family type per declared
family, in the order `empty, single L, single M, single R, LM, LR, MR, LMR`. The target
equivalence is equality of all eight subsets (`Target.ext_iff`); it is not bijection of images
and not presentation equivalence. -/
@[ext]
structure Target (S' : RestrictionSystem.{0, w} Context) where
  /-- The content over the empty family. -/
  empty : Set (S'.CompatibleFamily Zigzag.empty)
  /-- The content over the single view `L`. -/
  l : Set (S'.CompatibleFamily (single L))
  /-- The content over the single view `M`. -/
  m : Set (S'.CompatibleFamily (single M))
  /-- The content over the single view `R`. -/
  r : Set (S'.CompatibleFamily (single R))
  /-- The content over `LM`. -/
  lm : Set (S'.CompatibleFamily LM)
  /-- The content over `LR`. -/
  lr : Set (S'.CompatibleFamily LR)
  /-- The content over `MR`. -/
  mr : Set (S'.CompatibleFamily MR)
  /-- The content over the full family `LMR`. -/
  lmr : Set (S'.CompatibleFamily LMR)

/-- The labels of the eight declared families. -/
inductive Family
  /-- The empty family. -/
  | empty
  /-- The single view `L`. -/
  | l
  /-- The single view `M`. -/
  | m
  /-- The single view `R`. -/
  | r
  /-- The family `LM`. -/
  | lm
  /-- The family `LR`. -/
  | lr
  /-- The family `MR`. -/
  | mr
  /-- The full family `LMR`. -/
  | lmr

namespace Family

/-- The number of views of a declared family. -/
def arity : Family → ℕ
  | empty => 0
  | l | m | r => 1
  | lm | lr | mr => 2
  | lmr => 3

/-- The declared family carried by a label. -/
def fam : (f : Family) → Fin f.arity → Context
  | empty => Zigzag.empty
  | l => single L
  | m => single M
  | r => single R
  | lm => LM
  | lr => LR
  | mr => MR
  | lmr => LMR

end Family

variable {S' : RestrictionSystem.{0, w} Context}

/-- The entry of a target at a declared family label. -/
def Target.image (t : Target S') : (f : Family) → Set (S'.CompatibleFamily f.fam)
  | .empty => t.empty
  | .l => t.l
  | .m => t.m
  | .r => t.r
  | .lm => t.lm
  | .lr => t.lr
  | .mr => t.mr
  | .lmr => t.lmr

/-- Two targets are equal exactly when they agree at every declared family label. -/
theorem Target.ext_iff_image {t t' : Target S'} : t = t' ↔ ∀ f, t.image f = t'.image f where
  mp h _ := h ▸ rfl
  mpr h := Target.ext (h .empty) (h .l) (h .m) (h .r) (h .lm) (h .lr) (h .mr) (h .lmr)

namespace Candidate

variable (c : Candidate.{v, w} S')

/-- The supplied datum: the ordered pair `(I_LM, I_MR)` of attainable images over the declared
binary families, as subsets of the fixed coarse types. -/
def datum : Set (S'.CompatibleFamily LM) × Set (S'.CompatibleFamily MR) :=
  (c.φ.image LM, c.φ.image MR)

/-- The target of a candidate: its attainable image on every declared family. -/
def target : Target S' where
  empty := c.φ.image empty
  l := c.φ.image (single L)
  m := c.φ.image (single M)
  r := c.φ.image (single R)
  lm := c.φ.image LM
  lr := c.φ.image LR
  mr := c.φ.image MR
  lmr := c.φ.image LMR

/-- The target entry at a label is the attainable image of the labelled family. -/
theorem target_image (f : Family) : c.target.image f = c.φ.image f.fam := by
  cases f <;> rfl

/-- Every candidate has the full coarse content on the empty family. -/
theorem target_empty : c.target.empty = Set.univ := image_empty c.φ

/-- Every candidate has the full coarse content on the single view `L`. -/
theorem target_l : c.target.l = Set.univ := image_single c.φ L (c.surjective L)

/-- Every candidate has the full coarse content on the single view `M`. -/
theorem target_m : c.target.m = Set.univ := image_single c.φ M (c.surjective M)

/-- Every candidate has the full coarse content on the single view `R`. -/
theorem target_r : c.target.r = Set.univ := image_single c.φ R (c.surjective R)

/-- Every candidate has the full coarse content on the two outer views `LR`. -/
theorem target_lr : c.target.lr = Set.univ := image_LR c.φ (c.surjective L) (c.surjective R)

/-- The `LM` entry of the target is the first component of the supplied datum. -/
theorem target_lm : c.target.lm = c.datum.1 := rfl

/-- The `MR` entry of the target is the second component of the supplied datum. -/
theorem target_mr : c.target.mr = c.datum.2 := rfl

/-- The `LMR` entry of the target is the full image. -/
theorem target_lmr : c.target.lmr = c.φ.image LMR := rfl

/-- The closing equivalence: two candidates, with fine systems in possibly different
universes, have the same target exactly when they have the same supplied datum and the same full
image. The five other entries are fixed by `target_empty`, `target_l`, `target_m`, `target_r`,
and `target_lr`. -/
theorem target_eq_iff (c₁ : Candidate.{v₁, w} S') (c₂ : Candidate.{v₂, w} S') :
    c₁.target = c₂.target ↔ c₁.datum = c₂.datum ∧ c₁.φ.image LMR = c₂.φ.image LMR where
  mp h := ⟨Prod.ext (congrArg Target.lm h) (congrArg Target.mr h), congrArg Target.lmr h⟩
  mpr h :=
    Target.ext (c₁.target_empty.trans c₂.target_empty.symm) (c₁.target_l.trans c₂.target_l.symm)
      (c₁.target_m.trans c₂.target_m.symm) (c₁.target_r.trans c₂.target_r.symm)
      (congrArg Prod.fst h.1) (c₁.target_lr.trans c₂.target_lr.symm) (congrArg Prod.snd h.1) h.2

/-- Candidates with equal targets have equal attainable images on every declared family. -/
theorem image_eq_of_target_eq {c₁ : Candidate.{v₁, w} S'} {c₂ : Candidate.{v₂, w} S'}
    (h : c₁.target = c₂.target) (f : Family) : c₁.φ.image f.fam = c₂.φ.image f.fam :=
  (c₁.target_image f).symm.trans ((Target.ext_iff_image.1 h f).trans (c₂.target_image f))

end Candidate

/-! ### Agreement of the induced image restriction maps -/

section RestrictImage

variable {ι κ : Type*} {F : ι → Context} {E : κ → Context} (m : FamilyMap F E)

/-- The induced image restriction maps of any two morphisms into `S'` agree on underlying coarse
families: both are the fixed coarse map `S'.restrict m`. -/
theorem coe_restrictImage_eq {S₁ : RestrictionSystem.{0, v₁} Context}
    {S₂ : RestrictionSystem.{0, v₂} Context} (φ₁ : S₁.Hom S') (φ₂ : S₂.Hom S')
    (y : S'.CompatibleFamily F) (h₁ : y ∈ φ₁.image F) (h₂ : y ∈ φ₂.image F) :
    (φ₁.restrictImage m ⟨y, h₁⟩ : S'.CompatibleFamily E) = φ₂.restrictImage m ⟨y, h₂⟩ :=
  rfl

/-- Under equal attainable images over `F` and over `E`, the induced image restriction maps of two
morphisms into `S'` commute with the identifications `Equiv.setCongr` of the equal images. -/
theorem restrictImage_setCongr {S₁ : RestrictionSystem.{0, v₁} Context}
    {S₂ : RestrictionSystem.{0, v₂} Context} {φ₁ : S₁.Hom S'} {φ₂ : S₂.Hom S'}
    (hF : φ₁.image F = φ₂.image F) (hE : φ₁.image E = φ₂.image E) (y : φ₁.image F) :
    Equiv.setCongr hE (φ₁.restrictImage m y) = φ₂.restrictImage m (Equiv.setCongr hF y) :=
  Subtype.ext rfl

/-- For candidates with equal targets, the induced image restriction maps along every declared
operation between declared families (and along any other `FamilyMap` between them) commute with
the identifications of the equal images. -/
theorem Candidate.restrictImage_setCongr_of_target_eq {c₁ : Candidate.{v₁, w} S'}
    {c₂ : Candidate.{v₂, w} S'} (h : c₁.target = c₂.target) {f e : Family}
    (m : FamilyMap f.fam e.fam) (y : c₁.φ.image f.fam) :
    Equiv.setCongr (c₁.image_eq_of_target_eq h e) (c₁.φ.restrictImage m y) =
      c₂.φ.restrictImage m (Equiv.setCongr (c₁.image_eq_of_target_eq h f) y) :=
  restrictImage_setCongr m _ _ y

end RestrictImage

end Zigzag
