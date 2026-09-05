import Amalgam.System.Comparison
import Amalgam.System.Restriction
import Amalgam.System.Zigzag
import Amalgam.System.ZigzagRealization
import Amalgam.System.ZigzagTarget

/-!
# Classification of targets at fixed datum on the zigzag

Fix a coarse restriction system `S'` on the shape `L → B ← M → D ← R`. The supplied datum of a
candidate realization `c : Candidate S'` is the pair `c.datum = (I_LM, I_MR)` of attainable
binary images; the target `c.target : Target S'` is the attainable image on all eight declared
families, and the target equivalence is equality of all eight subsets (`Target.ext_iff`). No
refinement of the datum is introduced.

This module combines the fixed entries of `Amalgam/System/ZigzagTarget.lean` with the realization
of `Amalgam/System/ZigzagRealization.lean`.

* `Candidate.image_LMR_subset_join`, `subset_join_of_candidate`: for a candidate in any fine
  universe, `I_LMR ⊆ join I_LM I_MR`, by naturality of the family comparison.
* `realizeCandidate A A' T`: the tagged fine system of `(A, A', T)` packaged as a candidate, with
  full image `T` for every `A`, `A'`, `T` and datum `(A, A')` only when `T ⊆ join A A'`.
* `exists_candidate_iff`: a candidate with datum `(A, A')` and full image `T` exists exactly when
  `T ⊆ join A A'`.
* `Target.ofDatum A A' T`: the target with full coarse content on the empty family, on each
  singleton, and on `LR`, with `LM`-entry `A`, `MR`-entry `A'`, and `LMR`-entry `T`. Every
  candidate's target has this form at its own datum and full image (`Candidate.target_eq_ofDatum`),
  with that full image inside the join of the datum
  (`Candidate.exists_subset_join_target_eq_ofDatum`).
* `exists_candidate_target_iff`, `exists_candidate_target_iff'`: the classification at fixed
  datum. The targets of candidates with datum `(A, A')` are exactly `Target.ofDatum A A' T` for
  `T ⊆ join A A'`; in fields, exactly the targets with full content on the five fixed entries,
  `LM`-entry `A`, `MR`-entry `A'`, and `LMR`-entry contained in `join A A'`.
* `datum_determines_target_iff`, `target_eq_of_join_eq_empty`: the datum `(A, A')` determines
  a unique target exactly when `join A A' = ∅`. The datum records which coarse binary families
  lift, not whether the fine middle states used by an `LM`-lift and an `MR`-lift of one coarse
  full family coincide. When the join is nonempty, `Target.ofDatum A A' ∅` and
  `Target.ofDatum A A' (join A A')` are two distinct targets of candidates with this datum.
* `realizable_target_iff`: an abstract target arises from some candidate exactly when its five
  fixed entries are full and its `LMR`-entry lies in the join of its `LM`- and `MR`-entries.
  This is `exists_realization_iff` read at the level of targets, recorded as the realizability
  consequence (PROPOSAL Section 14) for this shape and datum.

## Universe convention

The coarse system lives in `RestrictionSystem.{0, w}`. Statements with a candidate as hypothesis
(`Candidate.image_LMR_subset_join`, `subset_join_of_candidate`, `Candidate.target_eq_ofDatum`,
`Candidate.exists_subset_join_target_eq_ofDatum`, `Candidate.target_realizable`,
`target_eq_of_join_eq_empty`) hold for a fine system in any
universe `v`. The first two consume naturality only; the others also consume the fixed-image
lemmas of `Amalgam/System/ZigzagTarget.lean` and the candidate's objectwise surjectivity. The
realization `realize A A' T` has
fine states in the coarse universe `w`, so the existential statements and the iff's quantify over
`Candidate.{w, w}`.
-/

universe v v₁ v₂ w

namespace Zigzag

open Context RestrictionSystem

variable {S' : RestrictionSystem.{0, w} Context}

/-! ### The necessary inclusion for candidates -/

/-- The full image of a candidate in any fine universe lies in the join of its datum. -/
theorem Candidate.image_LMR_subset_join (c : Candidate.{v, w} S') :
    c.φ.image LMR ⊆ join c.datum.1 c.datum.2 :=
  Zigzag.image_LMR_subset_join c.φ

/-- A candidate in any fine universe with datum `(A, A')` and full image `T` forces
`T ⊆ join A A'`. -/
theorem subset_join_of_candidate {A : Set (S'.CompatibleFamily LM)}
    {A' : Set (S'.CompatibleFamily MR)} {T : Set (S'.CompatibleFamily LMR)}
    {c : Candidate.{v, w} S'} (h₁ : c.datum = (A, A')) (h₂ : c.φ.image LMR = T) :
    T ⊆ join A A' :=
  subset_join_of_images c.φ (congrArg Prod.fst h₁) (congrArg Prod.snd h₁) h₂

/-! ### The realization as a candidate -/

/-- The tagged fine system `realize A A' T` with its objectwise surjective observation
`realizeHom A A' T`, packaged as a candidate. Its full image is `T` for every `A`, `A'`, `T`
(`realizeCandidate_image_LMR`); its datum is `(A, A')` only under `T ⊆ join A A'`
(`realizeCandidate_datum`). -/
def realizeCandidate (A : Set (S'.CompatibleFamily LM)) (A' : Set (S'.CompatibleFamily MR))
    (T : Set (S'.CompatibleFamily LMR)) : Candidate.{w, w} S' where
  S := realize A A' T
  φ := realizeHom A A' T
  surjective := surjective_realizeHom A A' T

/-- The datum of the realization is `(A, A')` when `T ⊆ join A A'`. -/
theorem realizeCandidate_datum {A : Set (S'.CompatibleFamily LM)}
    {A' : Set (S'.CompatibleFamily MR)} {T : Set (S'.CompatibleFamily LMR)}
    (hT : T ⊆ join A A') : (realizeCandidate A A' T).datum = (A, A') :=
  Prod.ext (image_LM_realize hT) (image_MR_realize hT)

/-- The full image of the realization is `T`, for every `A`, `A'`, `T`. -/
theorem realizeCandidate_image_LMR (A : Set (S'.CompatibleFamily LM))
    (A' : Set (S'.CompatibleFamily MR)) (T : Set (S'.CompatibleFamily LMR)) :
    (realizeCandidate A A' T).φ.image LMR = T :=
  image_LMR_realize A A' T

/-- A candidate with datum `(A, A')` and full image `T` exists exactly when `T ⊆ join A A'`. -/
theorem exists_candidate_iff (A : Set (S'.CompatibleFamily LM))
    (A' : Set (S'.CompatibleFamily MR)) (T : Set (S'.CompatibleFamily LMR)) :
    (∃ c : Candidate.{w, w} S', c.datum = (A, A') ∧ c.φ.image LMR = T) ↔ T ⊆ join A A' where
  mp := fun ⟨_, h₁, h₂⟩ => subset_join_of_candidate h₁ h₂
  mpr hT := ⟨realizeCandidate A A' T, realizeCandidate_datum hT, realizeCandidate_image_LMR A A' T⟩

/-! ### The classification of targets at fixed datum -/

/-- The target with full coarse content on the empty family, on each singleton, and on `LR`,
with `LM`-entry `A`, `MR`-entry `A'`, and `LMR`-entry `T`. -/
def Target.ofDatum (A : Set (S'.CompatibleFamily LM)) (A' : Set (S'.CompatibleFamily MR))
    (T : Set (S'.CompatibleFamily LMR)) : Target S' where
  empty := Set.univ
  l := Set.univ
  m := Set.univ
  r := Set.univ
  lm := A
  lr := Set.univ
  mr := A'
  lmr := T

/-- A target is `Target.ofDatum A A' T` exactly when its five fixed entries are full and its
`LM`-, `MR`-, and `LMR`-entries are `A`, `A'`, and `T`. -/
theorem Target.eq_ofDatum_iff (t : Target S') {A : Set (S'.CompatibleFamily LM)}
    {A' : Set (S'.CompatibleFamily MR)} {T : Set (S'.CompatibleFamily LMR)} :
    t = Target.ofDatum A A' T ↔
      t.empty = Set.univ ∧ t.l = Set.univ ∧ t.m = Set.univ ∧ t.r = Set.univ ∧
        t.lr = Set.univ ∧ t.lm = A ∧ t.mr = A' ∧ t.lmr = T where
  mp h := h ▸ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  mpr h := Target.ext h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.2.1
    h.2.2.2.2.2.2.2

/-- Every candidate's target is `Target.ofDatum` at its own datum and full image, by the five
fixed images `target_empty`, `target_l`, `target_m`, `target_r`, `target_lr`. -/
theorem Candidate.target_eq_ofDatum (c : Candidate.{v, w} S') :
    c.target = Target.ofDatum c.datum.1 c.datum.2 (c.φ.image LMR) :=
  Target.ext c.target_empty c.target_l c.target_m c.target_r rfl c.target_lr rfl rfl

/-- The forward direction of the classification for a candidate in any fine universe: its target
is `Target.ofDatum` at its own datum and some full image inside the join of that datum. -/
theorem Candidate.exists_subset_join_target_eq_ofDatum (c : Candidate.{v, w} S') :
    ∃ T, T ⊆ join c.datum.1 c.datum.2 ∧ c.target = Target.ofDatum c.datum.1 c.datum.2 T :=
  ⟨_, c.image_LMR_subset_join, c.target_eq_ofDatum⟩

/-- The classification at fixed datum: the targets of candidates with datum `(A, A')` are exactly
`Target.ofDatum A A' T` for `T ⊆ join A A'`. -/
theorem exists_candidate_target_iff (A : Set (S'.CompatibleFamily LM))
    (A' : Set (S'.CompatibleFamily MR)) (t : Target S') :
    (∃ c : Candidate.{w, w} S', c.datum = (A, A') ∧ c.target = t) ↔
      ∃ T, T ⊆ join A A' ∧ t = Target.ofDatum A A' T where
  mp := fun ⟨c, h₁, h₂⟩ =>
    ⟨c.φ.image LMR, subset_join_of_candidate h₁ rfl, by rw [← h₂, c.target_eq_ofDatum, h₁]⟩
  mpr := fun ⟨T, hT, ht⟩ =>
    ⟨realizeCandidate A A' T, realizeCandidate_datum hT, by
      rw [ht, Candidate.target_eq_ofDatum, realizeCandidate_datum hT, realizeCandidate_image_LMR]⟩

/-- The classification at fixed datum, in fields: a target is the target of a candidate with
datum `(A, A')` exactly when its five fixed entries are full, its `LM`-entry is `A`, its
`MR`-entry is `A'`, and its `LMR`-entry lies in `join A A'`. -/
theorem exists_candidate_target_iff' (A : Set (S'.CompatibleFamily LM))
    (A' : Set (S'.CompatibleFamily MR)) (t : Target S') :
    (∃ c : Candidate.{w, w} S', c.datum = (A, A') ∧ c.target = t) ↔
      t.empty = Set.univ ∧ t.l = Set.univ ∧ t.m = Set.univ ∧ t.r = Set.univ ∧
        t.lr = Set.univ ∧ t.lm = A ∧ t.mr = A' ∧ t.lmr ⊆ join A A' := by
  rw [exists_candidate_target_iff]
  constructor
  · rintro ⟨T, hT, rfl⟩
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, hT⟩
  · rintro ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈⟩
    exact ⟨t.lmr, h₈, (t.eq_ofDatum_iff).2 ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, rfl⟩⟩

/-! ### The exact uniqueness condition -/

/-- The datum `(A, A')` determines a unique target exactly when `join A A' = ∅`. The datum
records which coarse binary families lift, not whether the fine middle states used by an
`LM`-lift and an `MR`-lift of one coarse full family coincide: when the join is nonempty, both
`∅` and `join A A'` are realizable full images at this datum, so `Target.ofDatum A A' ∅` and
`Target.ofDatum A A' (join A A')` are two distinct targets of candidates with datum `(A, A')`. -/
theorem datum_determines_target_iff (A : Set (S'.CompatibleFamily LM))
    (A' : Set (S'.CompatibleFamily MR)) :
    (∀ c₁ c₂ : Candidate.{w, w} S',
      c₁.datum = (A, A') → c₂.datum = (A, A') → c₁.target = c₂.target) ↔
      join A A' = ∅ where
  mp h :=
    (image_LMR_determined_iff A A').1 fun S₁ S₂ φ₁ φ₂ hs₁ hs₂ hLM₁ hMR₁ hLM₂ hMR₂ =>
      ((Candidate.target_eq_iff ⟨S₁, φ₁, hs₁⟩ ⟨S₂, φ₂, hs₂⟩).1
        (h _ _ (Prod.ext hLM₁ hMR₁) (Prod.ext hLM₂ hMR₂))).2
  mpr h c₁ c₂ h₁ h₂ :=
    (Candidate.target_eq_iff c₁ c₂).2 ⟨h₁.trans h₂.symm,
      (image_LMR_determined_iff A A').2 h _ _ c₁.φ c₂.φ c₁.surjective c₂.surjective
        (congrArg Prod.fst h₁) (congrArg Prod.snd h₁) (congrArg Prod.fst h₂)
        (congrArg Prod.snd h₂)⟩

/-- Candidates with fine systems in any universes and the same datum `(A, A')` have the same
target when `join A A' = ∅`: the sufficiency direction of `datum_determines_target_iff`, from
empty join to determination, at arbitrary fine universes. -/
theorem target_eq_of_join_eq_empty {A : Set (S'.CompatibleFamily LM)}
    {A' : Set (S'.CompatibleFamily MR)} {c₁ : Candidate.{v₁, w} S'} {c₂ : Candidate.{v₂, w} S'}
    (h : join A A' = ∅) (h₁ : c₁.datum = (A, A')) (h₂ : c₂.datum = (A, A')) :
    c₁.target = c₂.target :=
  (Candidate.target_eq_iff c₁ c₂).2 ⟨h₁.trans h₂.symm, by
    have e₁ := subset_join_of_candidate h₁ rfl
    have e₂ := subset_join_of_candidate h₂ rfl
    rw [h, Set.subset_empty_iff] at e₁ e₂
    exact e₁.trans e₂.symm⟩

/-! ### Realizability of abstract targets -/

/-- Every candidate's target, in any fine universe, has full content on the five fixed entries
and `LMR`-entry contained in the join of its `LM`- and `MR`-entries. -/
theorem Candidate.target_realizable (c : Candidate.{v, w} S') :
    c.target.empty = Set.univ ∧ c.target.l = Set.univ ∧ c.target.m = Set.univ ∧
      c.target.r = Set.univ ∧ c.target.lr = Set.univ ∧
        c.target.lmr ⊆ join c.target.lm c.target.mr :=
  ⟨c.target_empty, c.target_l, c.target_m, c.target_r, c.target_lr, c.image_LMR_subset_join⟩

/-- Which abstract target collections arise from a candidate at all: exactly those with full
content on the empty family, on each singleton, and on `LR`, and with `LMR`-entry contained in
the join of the `LM`- and `MR`-entries. This is the realizability consequence of the
classification for this shape and datum, with no further condition. -/
theorem realizable_target_iff (t : Target S') :
    (∃ c : Candidate.{w, w} S', c.target = t) ↔
      t.empty = Set.univ ∧ t.l = Set.univ ∧ t.m = Set.univ ∧ t.r = Set.univ ∧
        t.lr = Set.univ ∧ t.lmr ⊆ join t.lm t.mr where
  mp := fun ⟨c, h⟩ => h ▸ c.target_realizable
  mpr := fun ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ =>
    let ⟨c, _, hc⟩ := (exists_candidate_target_iff' t.lm t.mr t).2
      ⟨h₁, h₂, h₃, h₄, h₅, rfl, rfl, h₆⟩
    ⟨c, hc⟩

end Zigzag
