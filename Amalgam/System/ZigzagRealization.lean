import Amalgam.System.Binary
import Amalgam.System.Comparison
import Amalgam.System.Restriction
import Amalgam.System.Zigzag

/-!
# Realizing full images on the zigzag `L → B ← M → D ← R`

Fix a coarse restriction system `S'` on `Zigzag.Context`. The datum is a pair of subsets
`A ⊆ S'.CompatibleFamily LM`, `A' ⊆ S'.CompatibleFamily MR`. A realization of `(A, A', T)` is a
fine system `S` with a morphism `φ : S.Hom S'`, surjective at every context, whose attainable
images are `φ.image LM = A`, `φ.image MR = A'`, `φ.image LMR = T`.

* `join A A'`: the coarse full families restricting into `A` along `toLM` and into `A'` along
  `toMR` (`mem_join_iff`).
* `image_LMR_subset_join`: for every morphism, `φ.image LMR ⊆ join (φ.image LM) (φ.image MR)`,
  by naturality of the family comparison (`mapsTo_restrict_image`). No surjectivity is used and
  the fine system may live in any universe (`subset_join_of_images`).
* `realize A A' T`, `realizeHom A A' T`: the tagged fine system with its observation. For every
  `A`, `A'`, `T` the observation is objectwise surjective (`surjective_realizeHom`) and has full
  image `T` (`image_LMR_realize`); under `T ⊆ join A A'` it also has binary images `A`, `A'`
  (`image_LM_realize`, `image_MR_realize`), so it is then a realization of `(A, A', T)`. A fine
  state is a tag with the coarse state it dictates: one `full` state per element of `T` at every
  context, one `lm` state per element of `A` at every context below `L` or `M`, one `mr` state
  per element of `A'` at every context below `M` or `R`, and a `solo` copy of every coarse state
  restricted to every coarser context, tagged by its origin, which makes the observation
  surjective. Restriction preserves tags, so fine states agree on an overlap exactly when they
  carry the same tag (`TaggedState.res_eq_res_LM_iff`, `TaggedState.res_eq_res_MR_iff`): the
  compatible fine
  families over `LM`, `MR`, `LMR` are the constant `full`- or `lm`-tagged, `full`- or `mr`-tagged,
  and `full`-tagged families, observed as `S'.restrict toLM y`, `a`, `S'.restrict toMR y`, `a'`,
  and `y`.
* `exists_realization_iff`: `(A, A', T)` is realized exactly when `T ⊆ join A A'`; the converse
  holds for arbitrary `A`, `A'` and every `T ⊆ join A A'` with no further hypothesis.
* `unique_full_image_iff`, `image_LMR_determined_iff`: the datum `(A, A')` determines the full
  image exactly when `join A A' = ∅`; otherwise `∅` and `join A A'` are two distinct realizable
  full images. The datum records which coarse binary families lift, not whether the fine middle
  states used by an `LM`-lift and an `MR`-lift of one coarse full family coincide.

The coarse system lives in `RestrictionSystem.{0, w}`. The necessary inclusion holds for a fine
system in any universe `v`; the realization has fine states in the coarse universe `w`, so the
existential statements quantify over fine systems in `RestrictionSystem.{0, w}`.
-/

universe v w

namespace Zigzag

open Context RestrictionSystem

namespace Context

/-- `L` lies below neither `M` nor `R`. -/
theorem not_L_le_MR : ¬(L ≤ M ∨ L ≤ R) := fun h => h.elim False.elim False.elim

/-- `R` lies below neither `L` nor `M`. -/
theorem not_R_le_LM : ¬(R ≤ L ∨ R ≤ M) := fun h => h.elim False.elim False.elim

/-- No context is finer than both `L` and `M`. -/
theorem not_L_le_of_M_le : ∀ {d : Context}, L ≤ d → M ≤ d → False := by
  intro d h h'
  cases d <;> first | exact False.elim h | exact False.elim h'

/-- No context is finer than both `M` and `R`. -/
theorem not_M_le_of_R_le : ∀ {d : Context}, M ≤ d → R ≤ d → False := by
  intro d h h'
  cases d <;> first | exact False.elim h | exact False.elim h'

end Context

variable {S' : RestrictionSystem.{0, w} Context}

/-! ### The coarse join and the necessary inclusion -/

/-- The coarse full families restricting into `A` along `toLM` and into `A'` along `toMR`. -/
def join (A : Set (S'.CompatibleFamily LM)) (A' : Set (S'.CompatibleFamily MR)) :
    Set (S'.CompatibleFamily LMR) :=
  {y | S'.restrict toLM y ∈ A ∧ S'.restrict toMR y ∈ A'}

/-- Membership in the coarse join. -/
theorem mem_join_iff {A : Set (S'.CompatibleFamily LM)} {A' : Set (S'.CompatibleFamily MR)}
    (y : S'.CompatibleFamily LMR) :
    y ∈ join A A' ↔ S'.restrict toLM y ∈ A ∧ S'.restrict toMR y ∈ A' :=
  Iff.rfl

/-- The necessary inclusion: the full image restricts into both binary images, by naturality of
the family comparison. No surjectivity of the observation is used. -/
theorem image_LMR_subset_join {S : RestrictionSystem.{0, v} Context} (φ : S.Hom S') :
    φ.image LMR ⊆ join (φ.image LM) (φ.image MR) :=
  fun _ hy => ⟨φ.mapsTo_restrict_image toLM hy, φ.mapsTo_restrict_image toMR hy⟩

/-- `image_LMR_subset_join` for named images: a fine system in any universe realizing
`(A, A', T)` forces `T ⊆ join A A'`. -/
theorem subset_join_of_images {S : RestrictionSystem.{0, v} Context} (φ : S.Hom S')
    {A : Set (S'.CompatibleFamily LM)} {A' : Set (S'.CompatibleFamily MR)}
    {T : Set (S'.CompatibleFamily LMR)} (hLM : φ.image LM = A) (hMR : φ.image MR = A')
    (hLMR : φ.image LMR = T) : T ⊆ join A A' := by
  subst hLM hMR hLMR
  exact image_LMR_subset_join φ

/-! ### Coarse states dictated by a compatible family -/

/-- The `L`-component of the restriction to `LM`. -/
theorem restrict_toLM_zero (y : S'.CompatibleFamily LMR) : (S'.restrict toLM y).1 0 = y.1 0 :=
  S'.res_refl _ _

/-- The `M`-component of the restriction to `LM`. -/
theorem restrict_toLM_one (y : S'.CompatibleFamily LMR) : (S'.restrict toLM y).1 1 = y.1 1 :=
  S'.res_refl _ _

/-- The `M`-component of the restriction to `MR`. -/
theorem restrict_toMR_zero (y : S'.CompatibleFamily LMR) : (S'.restrict toMR y).1 0 = y.1 1 :=
  S'.res_refl _ _

/-- The `R`-component of the restriction to `MR`. -/
theorem restrict_toMR_one (y : S'.CompatibleFamily LMR) : (S'.restrict toMR y).1 1 = y.1 2 :=
  S'.res_refl _ _

/-- The coarse state at every context dictated by a compatible full family. -/
def stateLMR (y : S'.CompatibleFamily LMR) : ∀ c, S'.State c
  | L => y.1 0
  | B => S'.res B_le_L (y.1 0)
  | M => y.1 1
  | D => S'.res D_le_M (y.1 1)
  | R => y.1 2

/-- `stateLMR` commutes with restriction, by compatibility at `B` and `D`. -/
theorem res_stateLMR (y : S'.CompatibleFamily LMR) {c d : Context} (h : c ≤ d) :
    S'.res h (stateLMR y d) = stateLMR y c := by
  cases c <;> cases d <;>
    first
    | exact False.elim h
    | exact S'.res_refl _ _
    | rfl
    | exact (y.2 (i := 0) (j := 1) B_le_L B_le_M).symm
    | exact (y.2 (i := 1) (j := 2) D_le_M D_le_R).symm

/-- The coarse state at every context below `L` or `M` dictated by a compatible `LM`-family. -/
def stateLM (a : S'.CompatibleFamily LM) : ∀ c, c ≤ L ∨ c ≤ M → S'.State c
  | L, _ => a.1 0
  | B, _ => S'.res B_le_L (a.1 0)
  | M, _ => a.1 1
  | D, _ => S'.res D_le_M (a.1 1)
  | R, h => (not_R_le_LM h).elim

/-- `stateLM` commutes with restriction, by compatibility at `B`. -/
theorem res_stateLM (a : S'.CompatibleFamily LM) {c d : Context} (h : c ≤ d)
    (hd : d ≤ L ∨ d ≤ M) : S'.res h (stateLM a d hd) = stateLM a c (hd.imp h.trans h.trans) := by
  cases c <;> cases d <;>
    first
    | exact False.elim h
    | exact (not_R_le_LM hd).elim
    | exact S'.res_refl _ _
    | rfl
    | exact (a.2 (i := 0) (j := 1) B_le_L B_le_M).symm

/-- The coarse state at every context below `M` or `R` dictated by a compatible `MR`-family. -/
def stateMR (a' : S'.CompatibleFamily MR) : ∀ c, c ≤ M ∨ c ≤ R → S'.State c
  | L, h => (not_L_le_MR h).elim
  | B, _ => S'.res B_le_M (a'.1 0)
  | M, _ => a'.1 0
  | D, _ => S'.res D_le_M (a'.1 0)
  | R, _ => a'.1 1

/-- `stateMR` commutes with restriction, by compatibility at `D`. -/
theorem res_stateMR (a' : S'.CompatibleFamily MR) {c d : Context} (h : c ≤ d)
    (hd : d ≤ M ∨ d ≤ R) : S'.res h (stateMR a' d hd) = stateMR a' c (hd.imp h.trans h.trans) := by
  cases c <;> cases d <;>
    first
    | exact False.elim h
    | exact (not_L_le_MR hd).elim
    | exact S'.res_refl _ _
    | rfl
    | exact (a'.2 (i := 0) (j := 1) D_le_M D_le_R).symm

/-! ### Tagged fine states -/

/-- The fine states at `c` of the realization of `(A, A', T)`: a tag naming the coarse family it
serves, or a `solo` copy of a coarse state tagged by its origin `p : Σ d, S'.State d` and
restricted to `c`. Restriction retains the origin, so two `solo` copies agree on an overlap only
when they copy the same coarse state at the same context; since no context is finer than both
`L` and `M`, or both `M` and `R`, this prevents unwanted compatible pairs. -/
inductive TaggedState (A : Set (S'.CompatibleFamily LM)) (A' : Set (S'.CompatibleFamily MR))
    (T : Set (S'.CompatibleFamily LMR)) (c : Context) : Type w
  /-- The state serving the full family `y`. -/
  | full (y : T)
  /-- The state serving the `LM`-family `a`, at a context below `L` or `M`. -/
  | lm (a : A) (h : c ≤ L ∨ c ≤ M)
  /-- The state serving the `MR`-family `a'`, at a context below `M` or `R`. -/
  | mr (a' : A') (h : c ≤ M ∨ c ≤ R)
  /-- The copy of the coarse state `p.2` at `p.1`, restricted to `c`. -/
  | solo (p : Σ d, S'.State d) (h : c ≤ p.1)

namespace TaggedState

variable {A : Set (S'.CompatibleFamily LM)} {A' : Set (S'.CompatibleFamily MR)}
  {T : Set (S'.CompatibleFamily LMR)}

/-- Restriction preserves tags. -/
def res {c d : Context} (h : c ≤ d) : TaggedState A A' T d → TaggedState A A' T c
  | full y => full y
  | lm a hd => lm a (hd.imp h.trans h.trans)
  | mr a' hd => mr a' (hd.imp h.trans h.trans)
  | solo p hd => solo p (h.trans hd)

/-- The observation: the coarse state dictated by the tag. -/
def obs : ∀ {c : Context}, TaggedState A A' T c → S'.State c
  | _, full y => stateLMR y.1 _
  | _, lm a hd => stateLM a.1 _ hd
  | _, mr a' hd => stateMR a'.1 _ hd
  | _, solo p hd => S'.res hd p.2

/-- The observation commutes with restriction. -/
theorem res_obs {c d : Context} (h : c ≤ d) (x : TaggedState A A' T d) :
    S'.res h x.obs = (x.res h).obs := by
  cases x with
  | full y => exact res_stateLMR y.1 h
  | lm a hd => exact res_stateLM a.1 h hd
  | mr a' hd => exact res_stateMR a'.1 h hd
  | solo p hd => exact S'.res_trans h hd p.2

/-- An `L`-state and an `M`-state agree at `B` exactly when they carry the same `full` or `lm`
tag. -/
theorem res_eq_res_LM_iff (u : TaggedState A A' T L) (v : TaggedState A A' T M) :
    u.res B_le_L = v.res B_le_M ↔
      (∃ y, u = full y ∧ v = full y) ∨
        ∃ a, u = lm a (Or.inl le_rfl) ∧ v = lm a (Or.inr le_rfl) := by
  constructor
  · intro h
    rcases u with y | ⟨a, hu⟩ | ⟨a', hu⟩ | ⟨p, hu⟩ <;>
      rcases v with y' | ⟨a'', hv⟩ | ⟨a'', hv⟩ | ⟨p', hv⟩ <;>
      cases h <;>
      first
      | exact Or.inl ⟨_, rfl, rfl⟩
      | exact Or.inr ⟨_, rfl, rfl⟩
      | exact (not_L_le_MR hu).elim
      | exact (not_L_le_of_M_le hu hv).elim
  · rintro (⟨y, rfl, rfl⟩ | ⟨a, rfl, rfl⟩) <;> rfl

/-- An `M`-state and an `R`-state agree at `D` exactly when they carry the same `full` or `mr`
tag. -/
theorem res_eq_res_MR_iff (v : TaggedState A A' T M) (w : TaggedState A A' T R) :
    v.res D_le_M = w.res D_le_R ↔
      (∃ y, v = full y ∧ w = full y) ∨
        ∃ a', v = mr a' (Or.inl le_rfl) ∧ w = mr a' (Or.inr le_rfl) := by
  constructor
  · intro h
    rcases v with y | ⟨a, hv⟩ | ⟨a', hv⟩ | ⟨p, hv⟩ <;>
      rcases w with y' | ⟨a'', hw⟩ | ⟨a'', hw⟩ | ⟨p', hw⟩ <;>
      cases h <;>
      first
      | exact Or.inl ⟨_, rfl, rfl⟩
      | exact Or.inr ⟨_, rfl, rfl⟩
      | exact (not_R_le_LM hw).elim
      | exact (not_M_le_of_R_le hv hw).elim
  · rintro (⟨y, rfl, rfl⟩ | ⟨a', rfl, rfl⟩) <;> rfl

/-- A compatible triple carries one `full` tag. -/
theorem eq_full_of_res_eq (u : TaggedState A A' T L) (v : TaggedState A A' T M)
    (w : TaggedState A A' T R) (h₁ : u.res B_le_L = v.res B_le_M)
    (h₂ : v.res D_le_M = w.res D_le_R) : ∃ y, u = full y ∧ v = full y ∧ w = full y := by
  rcases (res_eq_res_LM_iff u v).1 h₁ with ⟨y, rfl, rfl⟩ | ⟨a, rfl, rfl⟩ <;>
    rcases (res_eq_res_MR_iff _ w).1 h₂ with ⟨y', hy, rfl⟩ | ⟨a', hy, rfl⟩ <;> cases hy
  exact ⟨_, rfl, rfl, rfl⟩

end TaggedState

/-! ### The realization -/

/-- The tagged fine system of `(A, A', T)`: tagged states with tag-preserving restriction. For
every `A`, `A'`, `T`, its observation `realizeHom A A' T` is objectwise surjective
(`surjective_realizeHom`) and has full image `T` (`image_LMR_realize`); it has binary images `A`
and `A'` only under `T ⊆ join A A'` (`image_LM_realize`, `image_MR_realize`). Over the
all-singleton coarse system with `A = A' = ∅` and `T = Set.univ`, the datum of the packaged
candidate is not `(A, A')`, since a full family in `T` restricts into the actual binary images. -/
def realize (A : Set (S'.CompatibleFamily LM)) (A' : Set (S'.CompatibleFamily MR))
    (T : Set (S'.CompatibleFamily LMR)) : RestrictionSystem.{0, w} Context where
  State := TaggedState A A' T
  res h := TaggedState.res h
  res_refl _ x := by cases x <;> rfl
  res_trans _ _ x := by cases x <;> rfl

/-- The observation of the realization: the coarse state dictated by the tag. -/
def realizeHom (A : Set (S'.CompatibleFamily LM)) (A' : Set (S'.CompatibleFamily MR))
    (T : Set (S'.CompatibleFamily LMR)) : (realize A A' T).Hom S' where
  toFun _ := TaggedState.obs
  naturality := TaggedState.res_obs

/-- Every coarse state is observed from its `solo` copy. -/
theorem surjective_realizeHom (A : Set (S'.CompatibleFamily LM))
    (A' : Set (S'.CompatibleFamily MR)) (T : Set (S'.CompatibleFamily LMR)) (c : Context) :
    Function.Surjective ((realizeHom A A' T).toFun c) :=
  fun s => ⟨TaggedState.solo ⟨c, s⟩ le_rfl, S'.res_refl _ _⟩

namespace realize

variable {A : Set (S'.CompatibleFamily LM)} {A' : Set (S'.CompatibleFamily MR)}
  {T : Set (S'.CompatibleFamily LMR)}

/-- Every index of `LM` lies below `L` or `M`. -/
theorem LM_le : ∀ i : Fin 2, LM i ≤ L ∨ LM i ≤ M
  | 0 => Or.inl le_rfl
  | 1 => Or.inr le_rfl

/-- Every index of `MR` lies below `M` or `R`. -/
theorem MR_le : ∀ i : Fin 2, MR i ≤ M ∨ MR i ≤ R
  | 0 => Or.inl le_rfl
  | 1 => Or.inr le_rfl

/-- The constant `full`-tagged family over `LMR`. -/
def fullFamily (y : T) : (realize A A' T).CompatibleFamily LMR :=
  ⟨fun _ => TaggedState.full y, fun _ _ _ _ _ => rfl⟩

/-- The constant `full`-tagged family over `LM`. -/
def fullFamilyLM (y : T) : (realize A A' T).CompatibleFamily LM :=
  ⟨fun _ => TaggedState.full y, fun _ _ _ _ _ => rfl⟩

/-- The constant `full`-tagged family over `MR`. -/
def fullFamilyMR (y : T) : (realize A A' T).CompatibleFamily MR :=
  ⟨fun _ => TaggedState.full y, fun _ _ _ _ _ => rfl⟩

/-- The constant `lm`-tagged family over `LM`. -/
def lmFamily (a : A) : (realize A A' T).CompatibleFamily LM :=
  ⟨fun i => TaggedState.lm a (LM_le i), fun _ _ _ _ _ => rfl⟩

/-- The constant `mr`-tagged family over `MR`. -/
def mrFamily (a' : A') : (realize A A' T).CompatibleFamily MR :=
  ⟨fun i => TaggedState.mr a' (MR_le i), fun _ _ _ _ _ => rfl⟩

/-- The `full`-tagged full family is observed as `y`. -/
theorem mapFamily_fullFamily (y : T) : (realizeHom A A' T).mapFamily LMR (fullFamily y) = y.1 :=
  Subtype.ext (funext fun i => match i with | 0 => rfl | 1 => rfl | 2 => rfl)

/-- The `full`-tagged `LM`-family is observed as `S'.restrict toLM y`. -/
theorem mapFamily_fullFamilyLM (y : T) :
    (realizeHom A A' T).mapFamily LM (fullFamilyLM y) = S'.restrict toLM y.1 :=
  Subtype.ext (funext fun i => match i with
    | 0 => (restrict_toLM_zero y.1).symm
    | 1 => (restrict_toLM_one y.1).symm)

/-- The `full`-tagged `MR`-family is observed as `S'.restrict toMR y`. -/
theorem mapFamily_fullFamilyMR (y : T) :
    (realizeHom A A' T).mapFamily MR (fullFamilyMR y) = S'.restrict toMR y.1 :=
  Subtype.ext (funext fun i => match i with
    | 0 => (restrict_toMR_zero y.1).symm
    | 1 => (restrict_toMR_one y.1).symm)

/-- The `lm`-tagged family is observed as `a`. -/
theorem mapFamily_lmFamily (a : A) : (realizeHom A A' T).mapFamily LM (lmFamily a) = a.1 :=
  Subtype.ext (funext fun i => match i with | 0 => rfl | 1 => rfl)

/-- The `mr`-tagged family is observed as `a'`. -/
theorem mapFamily_mrFamily (a' : A') : (realizeHom A A' T).mapFamily MR (mrFamily a') = a'.1 :=
  Subtype.ext (funext fun i => match i with | 0 => rfl | 1 => rfl)

end realize

open realize

/-- The full image of the realization is `T`, for every `A`, `A'`, `T`. -/
theorem image_LMR_realize (A : Set (S'.CompatibleFamily LM)) (A' : Set (S'.CompatibleFamily MR))
    (T : Set (S'.CompatibleFamily LMR)) : (realizeHom A A' T).image LMR = T := by
  apply Set.Subset.antisymm
  · rintro _ ⟨x, rfl⟩
    obtain ⟨h₁, h₂⟩ := ((realize A A' T).compatible_triple_iff B_le_L B_le_M D_le_M D_le_R
      le_B_of_le_L_of_le_M le_D_of_le_M_of_le_R le_M_of_le_L_of_le_R x.1).1 x.2
    obtain ⟨y, h0, h1, h2⟩ := TaggedState.eq_full_of_res_eq _ _ _ h₁ h₂
    have hx : x = fullFamily y :=
      Subtype.ext (funext fun i => match i with | 0 => h0 | 1 => h1 | 2 => h2)
    rw [hx, mapFamily_fullFamily]
    exact y.2
  · intro y hy
    exact ⟨fullFamily ⟨y, hy⟩, mapFamily_fullFamily _⟩

/-- The `LM`-image of the realization is `A` when `T ⊆ join A A'`. -/
theorem image_LM_realize {A : Set (S'.CompatibleFamily LM)} {A' : Set (S'.CompatibleFamily MR)}
    {T : Set (S'.CompatibleFamily LMR)} (hT : T ⊆ join A A') :
    (realizeHom A A' T).image LM = A := by
  apply Set.Subset.antisymm
  · rintro _ ⟨x, rfl⟩
    have h := ((realize A A' T).compatible_pair_iff B_le_L B_le_M le_B_of_le_L_of_le_M x.1).1 x.2
    rcases (TaggedState.res_eq_res_LM_iff _ _).1 h with ⟨y, h0, h1⟩ | ⟨a, h0, h1⟩
    · have hx : x = fullFamilyLM y := Subtype.ext (funext fun i => match i with | 0 => h0 | 1 => h1)
      rw [hx, mapFamily_fullFamilyLM]
      exact (hT y.2).1
    · have hx : x = lmFamily a := Subtype.ext (funext fun i => match i with | 0 => h0 | 1 => h1)
      rw [hx, mapFamily_lmFamily]
      exact a.2
  · intro a ha
    exact ⟨lmFamily ⟨a, ha⟩, mapFamily_lmFamily _⟩

/-- The `MR`-image of the realization is `A'` when `T ⊆ join A A'`. -/
theorem image_MR_realize {A : Set (S'.CompatibleFamily LM)} {A' : Set (S'.CompatibleFamily MR)}
    {T : Set (S'.CompatibleFamily LMR)} (hT : T ⊆ join A A') :
    (realizeHom A A' T).image MR = A' := by
  apply Set.Subset.antisymm
  · rintro _ ⟨x, rfl⟩
    have h := ((realize A A' T).compatible_pair_iff D_le_M D_le_R le_D_of_le_M_of_le_R x.1).1 x.2
    rcases (TaggedState.res_eq_res_MR_iff _ _).1 h with ⟨y, h0, h1⟩ | ⟨a', h0, h1⟩
    · have hx : x = fullFamilyMR y := Subtype.ext (funext fun i => match i with | 0 => h0 | 1 => h1)
      rw [hx, mapFamily_fullFamilyMR]
      exact (hT y.2).2
    · have hx : x = mrFamily a' := Subtype.ext (funext fun i => match i with | 0 => h0 | 1 => h1)
      rw [hx, mapFamily_mrFamily]
      exact a'.2
  · intro a' ha'
    exact ⟨mrFamily ⟨a', ha'⟩, mapFamily_mrFamily _⟩

/-! ### The exact classification -/

/-- `(A, A', T)` is realized by a fine system with surjective observations exactly when
`T ⊆ join A A'`. -/
theorem exists_realization_iff (A : Set (S'.CompatibleFamily LM))
    (A' : Set (S'.CompatibleFamily MR)) (T : Set (S'.CompatibleFamily LMR)) :
    (∃ (S : RestrictionSystem.{0, w} Context) (φ : S.Hom S'),
      (∀ c, Function.Surjective (φ.toFun c)) ∧
        φ.image LM = A ∧ φ.image MR = A' ∧ φ.image LMR = T) ↔
      T ⊆ join A A' where
  mp := fun ⟨_, φ, _, hLM, hMR, hLMR⟩ => subset_join_of_images φ hLM hMR hLMR
  mpr hT := ⟨realize A A' T, realizeHom A A' T, surjective_realizeHom A A' T,
    image_LM_realize hT, image_MR_realize hT, image_LMR_realize A A' T⟩

/-- The datum `(A, A')` determines the realizable full image exactly when the join is empty. -/
theorem unique_full_image_iff (A : Set (S'.CompatibleFamily LM))
    (A' : Set (S'.CompatibleFamily MR)) :
    (∀ T₁ T₂ : Set (S'.CompatibleFamily LMR), T₁ ⊆ join A A' → T₂ ⊆ join A A' → T₁ = T₂) ↔
      join A A' = ∅ where
  mp h := (h ∅ (join A A') (Set.empty_subset _) Set.Subset.rfl).symm
  mpr h _ _ h₁ h₂ := by
    rw [h, Set.subset_empty_iff] at h₁ h₂
    exact h₁.trans h₂.symm

/-- Any two realizations of the datum `(A, A')` have the same full image exactly when the join is
empty: the datum does not record whether the fine middle states used by an `LM`-lift and an
`MR`-lift of one coarse full family coincide. -/
theorem image_LMR_determined_iff (A : Set (S'.CompatibleFamily LM))
    (A' : Set (S'.CompatibleFamily MR)) :
    (∀ (S₁ S₂ : RestrictionSystem.{0, w} Context) (φ₁ : S₁.Hom S') (φ₂ : S₂.Hom S'),
      (∀ c, Function.Surjective (φ₁.toFun c)) → (∀ c, Function.Surjective (φ₂.toFun c)) →
        φ₁.image LM = A → φ₁.image MR = A' → φ₂.image LM = A → φ₂.image MR = A' →
          φ₁.image LMR = φ₂.image LMR) ↔
      join A A' = ∅ where
  mp h := by
    have := h _ _ (realizeHom A A' ∅) (realizeHom A A' (join A A')) (surjective_realizeHom _ _ _)
      (surjective_realizeHom _ _ _) (image_LM_realize (Set.empty_subset _))
      (image_MR_realize (Set.empty_subset _)) (image_LM_realize Set.Subset.rfl)
      (image_MR_realize Set.Subset.rfl)
    rwa [image_LMR_realize, image_LMR_realize, eq_comm] at this
  mpr h _ _ φ₁ φ₂ _ _ hLM₁ hMR₁ hLM₂ hMR₂ := by
    have h₁ := image_LMR_subset_join φ₁
    have h₂ := image_LMR_subset_join φ₂
    rw [hLM₁, hMR₁, h, Set.subset_empty_iff] at h₁
    rw [hLM₂, hMR₂, h, Set.subset_empty_iff] at h₂
    exact h₁.trans h₂.symm

end Zigzag
