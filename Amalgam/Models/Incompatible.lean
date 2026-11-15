import Amalgam.Models.MiddleSplit
import Amalgam.System.Comparison
import Amalgam.System.Restriction
import Amalgam.System.Zigzag
import Amalgam.System.ZigzagClassification
import Amalgam.System.ZigzagRealization
import Amalgam.System.ZigzagTarget

/-!
# Strict incompatible targets on the zigzag

Six explicit abstract targets over the all-singleton coarse system `coarse` of
`Amalgam/Models/MiddleSplit.lean`, one for each condition of `Zigzag.realizable_target_iff`. Each
violates exactly its own condition and satisfies the other five, so every condition of the
criterion is necessary and none is implied by the rest.

Over `coarse` every coarse compatible-family type is a singleton (`uniqueCoarseFamily`), so each
`Target coarse` entry is `∅` or `Set.univ`.

| Target | Violated condition | Certificate |
| --- | --- | --- |
| `noEmpty` | `empty = Set.univ` | `noEmpty_empty_ne_univ` |
| `noL` | `l = Set.univ` | `noL_l_ne_univ` |
| `noM` | `m = Set.univ` | `noM_m_ne_univ` |
| `noR` | `r = Set.univ` | `noR_r_ne_univ` |
| `noLR` | `lr = Set.univ` | `noLR_lr_ne_univ` |
| `noJoin` | `lmr ⊆ join lm mr` | `noJoin_lmr_not_subset_join` |

The five satisfied conditions of each target are certified by `noEmpty_satisfies_others` and its
four analogues, and by `noJoin_satisfies_others`. Nonrealizability goes through the
criterion `Zigzag.realizable_target_iff`: `noEmpty_not_realizable` and its five analogues.
`ofDatum_univ_univ_empty_realizable` is the positive control, so the six conditions are jointly
satisfiable and no control is vacuous.

These are abstract targets, not candidate systems violating their own laws; `coarse` itself is a
lawful restriction system throughout. No minimality is claimed.

The adjacent datum carries no realizability condition of its own: `exists_candidate_datum` gives,
for any coarse system and any pair `(A, A')`, a candidate with that datum, namely
`Zigzag.exists_candidate_iff A A' ∅` applied to `Set.empty_subset`. Four separate things are
therefore recorded and must not be conflated: that each adjacent view lifts (the datum), that two
such lifts are compatible over the coarse overlap (membership in `Zigzag.join`), that the full
family lifts simultaneously in the fine system (the `LMR` entry), and how freely that entry may
sit inside the join (the residual at fixed datum). Two separate adjacent lifts supply no common
fine middle representative, and the join records coarse compatibility only, which is why the
`LMR` entry stays free below it rather than being determined by the datum.
-/

universe w

open Zigzag Zigzag.Context Amalgam.Models.MiddleSplit

namespace Amalgam.Models.Incompatible

/-! ### The two shared certificates -/

/-- The full coarse content on `LMR` lies in the join of the full contents on `LM` and `MR`. -/
theorem univ_subset_join_univ_univ :
    (Set.univ : Set (coarse.CompatibleFamily LMR)) ⊆
      join (Set.univ : Set (coarse.CompatibleFamily LM))
        (Set.univ : Set (coarse.CompatibleFamily MR)) :=
  fun y _ => (mem_join_iff y).2 ⟨Set.mem_univ _, Set.mem_univ _⟩

/-- For any coarse system, every pair of adjacent subsets is the datum of a candidate: take the
empty full image, which lies in every join. The adjacent datum has no extra condition. -/
theorem exists_candidate_datum {S' : RestrictionSystem.{0, w} Context}
    (A : Set (S'.CompatibleFamily LM)) (A' : Set (S'.CompatibleFamily MR)) :
    ∃ c : Candidate.{w, w} S', c.datum = (A, A') :=
  let ⟨c, hc, _⟩ := (exists_candidate_iff A A' ∅).2 (Set.empty_subset _)
  ⟨c, hc⟩

/-! ### Failure on the empty family -/

/-- The target that is empty on the empty family and full everywhere else. -/
def noEmpty : Target coarse where
  empty := ∅
  l := Set.univ
  m := Set.univ
  r := Set.univ
  lm := Set.univ
  lr := Set.univ
  mr := Set.univ
  lmr := Set.univ

/-- `noEmpty` violates the empty-family condition. -/
theorem noEmpty_empty_ne_univ : noEmpty.empty ≠ Set.univ := Set.empty_ne_univ

/-- `noEmpty` satisfies the other five conditions. -/
theorem noEmpty_satisfies_others :
    noEmpty.l = Set.univ ∧ noEmpty.m = Set.univ ∧ noEmpty.r = Set.univ ∧
      noEmpty.lr = Set.univ ∧ noEmpty.lmr ⊆ join noEmpty.lm noEmpty.mr :=
  ⟨rfl, rfl, rfl, rfl, univ_subset_join_univ_univ⟩

/-- No candidate realizes `noEmpty`. -/
theorem noEmpty_not_realizable : ¬ ∃ c : Candidate.{0, 0} coarse, c.target = noEmpty := fun h =>
  noEmpty_empty_ne_univ ((realizable_target_iff noEmpty).1 h).1

/-! ### Failure on the single view `L` -/

/-- The target that is empty on the single view `L` and full everywhere else. -/
def noL : Target coarse where
  empty := Set.univ
  l := ∅
  m := Set.univ
  r := Set.univ
  lm := Set.univ
  lr := Set.univ
  mr := Set.univ
  lmr := Set.univ

/-- `noL` violates the condition on the single view `L`. -/
theorem noL_l_ne_univ : noL.l ≠ Set.univ := Set.empty_ne_univ

/-- `noL` satisfies the other five conditions. -/
theorem noL_satisfies_others :
    noL.empty = Set.univ ∧ noL.m = Set.univ ∧ noL.r = Set.univ ∧
      noL.lr = Set.univ ∧ noL.lmr ⊆ join noL.lm noL.mr :=
  ⟨rfl, rfl, rfl, rfl, univ_subset_join_univ_univ⟩

/-- No candidate realizes `noL`. -/
theorem noL_not_realizable : ¬ ∃ c : Candidate.{0, 0} coarse, c.target = noL := fun h =>
  noL_l_ne_univ ((realizable_target_iff noL).1 h).2.1

/-! ### Failure on the single view `M` -/

/-- The target that is empty on the single view `M` and full everywhere else. -/
def noM : Target coarse where
  empty := Set.univ
  l := Set.univ
  m := ∅
  r := Set.univ
  lm := Set.univ
  lr := Set.univ
  mr := Set.univ
  lmr := Set.univ

/-- `noM` violates the condition on the single view `M`. -/
theorem noM_m_ne_univ : noM.m ≠ Set.univ := Set.empty_ne_univ

/-- `noM` satisfies the other five conditions. -/
theorem noM_satisfies_others :
    noM.empty = Set.univ ∧ noM.l = Set.univ ∧ noM.r = Set.univ ∧
      noM.lr = Set.univ ∧ noM.lmr ⊆ join noM.lm noM.mr :=
  ⟨rfl, rfl, rfl, rfl, univ_subset_join_univ_univ⟩

/-- No candidate realizes `noM`. -/
theorem noM_not_realizable : ¬ ∃ c : Candidate.{0, 0} coarse, c.target = noM := fun h =>
  noM_m_ne_univ ((realizable_target_iff noM).1 h).2.2.1

/-! ### Failure on the single view `R` -/

/-- The target that is empty on the single view `R` and full everywhere else. -/
def noR : Target coarse where
  empty := Set.univ
  l := Set.univ
  m := Set.univ
  r := ∅
  lm := Set.univ
  lr := Set.univ
  mr := Set.univ
  lmr := Set.univ

/-- `noR` violates the condition on the single view `R`. -/
theorem noR_r_ne_univ : noR.r ≠ Set.univ := Set.empty_ne_univ

/-- `noR` satisfies the other five conditions. -/
theorem noR_satisfies_others :
    noR.empty = Set.univ ∧ noR.l = Set.univ ∧ noR.m = Set.univ ∧
      noR.lr = Set.univ ∧ noR.lmr ⊆ join noR.lm noR.mr :=
  ⟨rfl, rfl, rfl, rfl, univ_subset_join_univ_univ⟩

/-- No candidate realizes `noR`. -/
theorem noR_not_realizable : ¬ ∃ c : Candidate.{0, 0} coarse, c.target = noR := fun h =>
  noR_r_ne_univ ((realizable_target_iff noR).1 h).2.2.2.1

/-! ### Failure on the two outer views -/

/-- The target that is empty on `LR` and full everywhere else. -/
def noLR : Target coarse where
  empty := Set.univ
  l := Set.univ
  m := Set.univ
  r := Set.univ
  lm := Set.univ
  lr := ∅
  mr := Set.univ
  lmr := Set.univ

/-- `noLR` violates the condition on the two outer views. -/
theorem noLR_lr_ne_univ : noLR.lr ≠ Set.univ := Set.empty_ne_univ

/-- `noLR` satisfies the other five conditions. -/
theorem noLR_satisfies_others :
    noLR.empty = Set.univ ∧ noLR.l = Set.univ ∧ noLR.m = Set.univ ∧
      noLR.r = Set.univ ∧ noLR.lmr ⊆ join noLR.lm noLR.mr :=
  ⟨rfl, rfl, rfl, rfl, univ_subset_join_univ_univ⟩

/-- No candidate realizes `noLR`. -/
theorem noLR_not_realizable : ¬ ∃ c : Candidate.{0, 0} coarse, c.target = noLR := fun h =>
  noLR_lr_ne_univ ((realizable_target_iff noLR).1 h).2.2.2.2.1

/-! ### Failure of the join inclusion -/

/-- The target that is full on the five fixed entries and on `MR` and `LMR`, and empty on `LM`,
so its join is empty while its full entry is not. -/
def noJoin : Target coarse where
  empty := Set.univ
  l := Set.univ
  m := Set.univ
  r := Set.univ
  lm := ∅
  lr := Set.univ
  mr := Set.univ
  lmr := Set.univ

/-- `noJoin` violates the join inclusion: the coarse family `y₀` lies in its `LMR` entry, but its
restriction along `toLM` is not in the empty `LM` entry, whereas the inclusion would force it
there. -/
theorem noJoin_lmr_not_subset_join : ¬ noJoin.lmr ⊆ join noJoin.lm noJoin.mr := fun h =>
  Set.notMem_empty _ ((mem_join_iff y₀).1 (h (Set.mem_univ y₀))).1

/-- `noJoin` satisfies the other five conditions. -/
theorem noJoin_satisfies_others :
    noJoin.empty = Set.univ ∧ noJoin.l = Set.univ ∧ noJoin.m = Set.univ ∧
      noJoin.r = Set.univ ∧ noJoin.lr = Set.univ :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- No candidate realizes `noJoin`. -/
theorem noJoin_not_realizable : ¬ ∃ c : Candidate.{0, 0} coarse, c.target = noJoin := fun h =>
  noJoin_lmr_not_subset_join ((realizable_target_iff noJoin).1 h).2.2.2.2.2

/-! ### The positive control -/

/-- The six conditions are jointly satisfiable: the target with full content on the five fixed
entries and on both adjacent entries, and empty full entry, is realized by a candidate. -/
theorem ofDatum_univ_univ_empty_realizable :
    ∃ c : Candidate.{0, 0} coarse, c.target = Target.ofDatum Set.univ Set.univ ∅ :=
  (realizable_target_iff (Target.ofDatum Set.univ Set.univ ∅)).2
    ⟨rfl, rfl, rfl, rfl, rfl, Set.empty_subset _⟩

end Amalgam.Models.Incompatible
