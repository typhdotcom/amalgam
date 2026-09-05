import Amalgam.Core.Reduction

/-!
# A surjective reduction that loses compatibility

The witness prescribed in PROPOSAL §10 for failure of the exact lifting criterion of
`Amalgam.Core.Reduction` under observation maps that are surjective on every object.

The fine span is `Unit ─p→ Bool ←q─ Unit` with `p _ = false` and `q _ = true`: the two local
views restrict to distinct overlap values, so no fine pair is compatible. Every coarse object is
`Unit`, so the coarse span has exactly one compatible pair `t₀`, and the three observation maps
onto singletons are surjective. The observed comparison therefore has empty source and misses
`t₀`, and the lifting criterion fails at `t₀` because the fine overlap values reachable from the
two sides are `{false}` and `{true}`.

Surjectivity of the observations is what makes this a reduction onto the coarse objects rather
than an arbitrary comparison, so it is the hypothesis whose insufficiency the witness records.
No minimality is claimed: nothing here excludes a smaller witness.
-/

namespace Amalgam.Models.Lifting

/-! ### The fine span -/

/-- The fine overlap: two distinct values. -/
abbrev B := Bool

/-- The fine left view: a single element. -/
abbrev L := Unit

/-- The fine right view: a single element. -/
abbrev R := Unit

/-- The left restriction, sending the only left view to `false`. -/
def p : L → B := fun _ => false

/-- The right restriction, sending the only right view to `true`. -/
def q : R → B := fun _ => true

/-! ### The coarse span -/

/-- The coarse overlap: a single element. -/
abbrev B' := Unit

/-- The coarse left view: a single element. -/
abbrev L' := Unit

/-- The coarse right view: a single element. -/
abbrev R' := Unit

/-- The coarse left restriction, the unique map. -/
def p' : L' → B' := fun _ => ()

/-- The coarse right restriction, the unique map. -/
def q' : R' → B' := fun _ => ()

/-! ### The observation maps -/

/-- The left observation, the unique map to a singleton. -/
def a : L → L' := fun _ => ()

/-- The overlap observation, collapsing the two fine overlap values. -/
def b : B → B' := fun _ => ()

/-- The right observation, the unique map to a singleton. -/
def c : R → R' := fun _ => ()

/-- The left square commutes. -/
theorem ha : ∀ l, p' (a l) = b (p l) := fun _ => rfl

/-- The right square commutes. -/
theorem hc : ∀ r, q' (c r) = b (q r) := fun _ => rfl

/-- The left observation is surjective. -/
theorem surjective_a : Function.Surjective a := fun _ => ⟨(), rfl⟩

/-- The overlap observation is surjective. -/
theorem surjective_b : Function.Surjective b := fun _ => ⟨false, rfl⟩

/-- The right observation is surjective. -/
theorem surjective_c : Function.Surjective c := fun _ => ⟨(), rfl⟩

/-! ### The two pullbacks -/

/-- No fine pair is compatible: a compatible pair would give `false = true`. -/
theorem isEmpty_pullback : IsEmpty (p.Pullback q) :=
  ⟨fun s => Bool.false_ne_true s.comm⟩

/-- The unique coarse compatible pair. -/
def t₀ : p'.Pullback q' := Function.Pullback.mk () () rfl

/-- The coarse compatible pairs are a singleton. -/
instance uniqueCoarsePullback : Unique (p'.Pullback q') where
  default := t₀
  uniq _ := Function.Pullback.ext rfl rfl

/-! ### Failure of the lifting criterion -/

/-- The lifting criterion fails at `t₀`: the fine overlap values reached from the left are
`{false}` and those reached from the right are `{true}`. -/
theorem not_nonempty_inter_t₀ :
    ¬(p '' (a ⁻¹' {t₀.fst}) ∩ q '' (c ⁻¹' {t₀.snd})).Nonempty := by
  rintro ⟨_, ⟨_, -, rfl⟩, _, -, hr⟩
  exact Bool.false_ne_true hr.symm

/-- `t₀` is not attained by the observed comparison. -/
theorem t₀_notMem_range_map : t₀ ∉ Set.range (Function.Pullback.map ha hc) := fun h =>
  not_nonempty_inter_t₀ ((Function.Pullback.mem_range_map_iff ha hc t₀).1 h)

/-- `t₀` is not attained by the induced comparison on the observed quotient. -/
theorem t₀_notMem_range_observedMap : t₀ ∉ Set.range (Function.Pullback.observedMap ha hc) :=
  fun h => not_nonempty_inter_t₀ ((Function.Pullback.mem_range_observedMap_iff ha hc t₀).1 h)

/-- `t₀` has no fine lift. -/
theorem isEmpty_fiber_t₀ : IsEmpty {s // Function.Pullback.map ha hc s = t₀} :=
  (Function.Pullback.isEmpty_fiber_map_iff ha hc t₀).2 not_nonempty_inter_t₀

/-- The observed quotient is empty, being a quotient of the empty fine pullback. -/
theorem isEmpty_observed : IsEmpty (Function.Pullback.Observed ha hc) :=
  ⟨fun x => Quotient.inductionOn x fun s => isEmpty_pullback.elim s⟩

/-- Existence fails: the observed comparison misses the only coarse compatible pair. -/
theorem not_surjective_map : ¬Function.Surjective (Function.Pullback.map ha hc) := fun hs =>
  not_nonempty_inter_t₀ ((Function.Pullback.surjective_map_iff ha hc).1 hs t₀)

/-- Surjective observations do not suffice: the induced comparison is not bijective. -/
theorem not_bijective_observedMap :
    ¬Function.Bijective (Function.Pullback.observedMap ha hc) := fun hb =>
  not_nonempty_inter_t₀ ((Function.Pullback.bijective_observedMap_iff ha hc).1 hb t₀)

end Amalgam.Models.Lifting
