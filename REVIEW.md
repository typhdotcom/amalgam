State: READY FOR REVIEW
Turn: reviewer
Candidate: 17913b28; accepted M0 candidate 6a33636f; accepted proposal baseline 7159fd31

# Submission

M1 — When local reduction preserves compatibility — is implemented at
`17913b28`. The exact binary lifting criterion, the observed quotient with
its injection and inverse laws, the surjective specialization with restriction
to images, and the prescribed finite failure witness are all compiled. No
`sorry`, no project axiom; classical choice appears only in the inverse
constructions named below. M0's API, Status coverage, and four witnesses are
unchanged. No M2 work was started.

# Accepted foundation

[PROPOSAL.md](PROPOSAL.md), especially Sections 10 and 26, owns this contract.

- Ordinary maps on arbitrary carriers with independent universes; empty types
  allowed. Commutation alone supports the constructions and the criterion.
  Objectwise surjectivity is a specialization; finiteness supplies witnesses.
- The generic fiber API and mathlib's `Function.Pullback` are reused; the raw
  comparison is an M0 `lift`, the quotient is `Setoid.ker`, and the quotient
  equivalence is `Setoid.quotientKerEquivRange`. No wrapper was introduced.
- Raw fibers of `k` (fine lifts) and subsingleton fibers of `k_bar` (observed
  classes) are kept distinct in the API and the README.
- The later target remains all admissible attainable images with their
  restriction maps. Finite-family indexing, M3's shape, profiles, and the
  Descent bridge are untouched.
- Toolchain, license, root exports, Status discipline, and tasks unchanged.

# Datum

Spans `p : L → B`, `q : R → B`, `p' : L' → B'`, `q' : R' → B'`, maps
`a : L → L'`, `b : B → B'`, `c : R → R'`, pointwise commutation
`ha : ∀ l, p' (a l) = b (p l)`, `hc : ∀ r, q' (c r) = b (q r)`. All carriers
are `Type*` with independent universes. `P = Function.Pullback p q`,
`P' = Function.Pullback p' q'`. Everything lives in `Amalgam/Core/Reduction.lean`
under `Function.Pullback`, except the witness.

# Closing evidence

## M1.1 — Canonical comparison and observed quotient

- `map ha hc : P → P'` := `lift (a ∘ fst) (c ∘ snd) _`; `map_eq_mapPullback`
  shows it is mathlib's `Function.mapPullback` on the funext'd laws.
  Projection laws `fst_map`, `snd_map`, `map_mk`; `map_eq_iff`,
  `map_eq_map_iff`; functoriality `map_id`, `map_map`, `map_lift`.
- Relation: `Setoid.ker (map ha hc)`. `observed_rel_iff` states it as
  agreement of both observed components; `observed_rel_iff_map_eq` as
  equality under `map`. `Observed ha hc := Quotient (Setoid.ker (map ha hc))`;
  `observed_mk_eq_iff`.
- `observedMap ha hc : Observed → P'` := `Setoid.kerLift`. Factorization
  `observedMap_mk` (simp), `observedMap_comp_mk`, `fst/snd_observedMap_mk`.
  `observedMap_injective` (`Setoid.kerLift_injective`), `range_observedMap`
  (`Setoid.range_kerLift_eq_range`).
- `observedEquivRange : Observed ≃ Set.range map`
  (`Setoid.quotientKerEquivRange`) with `coe_observedEquivRange_mk`,
  `coe_observedEquivRange`, and round trips
  `observedEquivRange_symm_apply_apply`, `observedEquivRange_apply_symm_apply`.
- `subsingleton_fiber_observedMap : ∀ t, Subsingleton {x // observedMap x = t}`
  via the generic `injective_iff_subsingleton_fiber`.

## M1.2 — Exact lifting criterion and inverse

- `mem_range_map_iff (t) : t ∈ Set.range map ↔ (p '' (a ⁻¹' {t.fst}) ∩ q '' (c ⁻¹' {t.snd})).Nonempty` — the displayed
  criterion verbatim, no hypotheses beyond commutation. Also
  `mem_range_map_iff_exists`, `mem_range_map_iff_exists_overlap` (explicit
  common overlap value `β`), and `mem_range_observedMap_iff`.
- Raw fiber identification: `fiberMapEquiv t : {s // map s = t} ≃ {s : P // a s.fst = t.fst ∧ c s.snd = t.snd}` (via `fiberLiftEquiv`) and
  `fiberMapEquivProd t : {s // map s = t} ≃ {x : L × R // p x.1 = q x.2 ∧ a x.1 = t.fst ∧ c x.2 = t.snd}` (the three conditions literally), and `fiberMapEquivPullback t : {s // map s = t} ≃ Function.Pullback (p restricted to {l // a l = t.fst}) (q restricted to {r // c r = t.snd})`,
  both with apply/symm computation lemmas.
- Existence and uniqueness of fine lifts, separately, via the fiber API:
  `nonempty_fiber_map_iff` (↔ criterion), `isEmpty_fiber_map_iff`,
  `subsingleton_fiber_map_iff`, `nonempty_unique_fiber_map_iff`.
- Closing theorem `bijective_observedMap_iff : Bijective observedMap ↔ ∀ t, (p '' (a ⁻¹' {t.fst}) ∩ q '' (c ⁻¹' {t.snd})).Nonempty`, with
  `surjective_map_iff`, `surjective_observedMap_iff_surjective_map`,
  `surjective_observedMap_iff`, `bijective_observedMap_iff_surjective`,
  `bijective_observedMap_iff_surjective_map`.
- Under `h : ∀ t, criterion`: `observedEquiv ha hc h : Observed ≃ P'`
  (`Equiv.ofBijective`, noncomputable; docstring says it selects an observed
  class, not a fine representative), `observedEquiv_apply` (simp),
  `observedEquiv_mk`, round trips `observedMap_observedEquiv_symm`,
  `observedEquiv_symm_observedMap`, uniqueness
  `eq_observedEquiv_symm_of_rightInverse`,
  `eq_observedEquiv_symm_of_leftInverse`. Converse packaging:
  `exists_inverse_observedMap_iff`, `inter_nonempty_of_rightInverse`.

## M1.3 — Surjective reductions and the finite failure

- Sufficient special case, labelled as such: `mem_range_map_iff_of_injective (hb : Injective b)` (criterion becomes componentwise) and
  `bijective_observedMap_of_injective hb (Surjective a) (Surjective c)`.
- Restriction to images: `Set.mapsTo_range_range`, `rangeRestrict ha : Set.range a → Set.range b` with `coe_rangeRestrict`, commutation
  `rangeFactorization_comm`, surjectivity by mathlib's
  `Set.rangeFactorization_surjective`, the restricted comparison
  `mapRangeFactorization`, the inclusion `rangeInclusion`,
  `rangeInclusion_mapRangeFactorization`, and
  `inter_nonempty_rangeFactorization_iff` /
  `mem_range_mapRangeFactorization_iff`: a restricted coarse pair is attained
  exactly when its underlying pair is.
- Witness `Amalgam/Models/Lifting.lean` (namespace `Amalgam.Models.Lifting`):
  `L = R = Unit`, `B = Bool`, `p _ = false`, `q _ = true`, coarse objects
  `Unit`, `a b c` the unique maps, `ha hc` by `rfl`. Theorems `surjective_a`,
  `surjective_b`, `surjective_c`; `isEmpty_pullback : IsEmpty (p.Pullback q)`;
  `t₀ := mk () () rfl` with `uniqueCoarsePullback : Unique (p'.Pullback q')`;
  `not_nonempty_inter_t₀` (the intersection `{false} ∩ {true}` is empty);
  `t₀_notMem_range_map` and `t₀_notMem_range_observedMap` through
  `mem_range_map_iff` / `mem_range_observedMap_iff`; `isEmpty_fiber_t₀` through
  `isEmpty_fiber_map_iff`; `isEmpty_observed`; `not_surjective_map` through
  `surjective_map_iff`; `not_bijective_observedMap` through
  `bijective_observedMap_iff`. No minimality is claimed.

## Root exports, README, Status

`Amalgam.lean` imports `Core.Comparison`, `Core.Fiber`, `Core.Reduction`,
`Models.Lifting`, `Models.Overlap`, `Status`. README gained the section
"Reduction across an overlap" with the subsection "A surjective reduction that
loses compatibility"; `Amalgam/Status.lean` mirrors each sentence under the
same headings at independent universes for generic claims and on the concrete
witness for the failure. Dependency direction: `Core` imports mathlib and
`Core`; `Models` import `Core`; only the root imports `Status`.

# Verification

- `nix fmt`: no changes. `nix develop -c lake build`: success, zero warnings.
- `nix flake check`: all checks passed. `rg sorry Amalgam`: none.
- Axioms (`#print axioms`): criterion theorems `mem_range_map_iff`,
  `bijective_observedMap_iff`, `subsingleton_fiber_map_iff`,
  `bijective_observedMap_of_injective`, `mem_range_mapRangeFactorization_iff`
  use only `propext`, `Quot.sound`; `fiberMapEquivPullback` uses none.
  `Classical.choice` appears in `observedEquivRange`, `observedEquiv` and its
  round-trip/uniqueness consequences, and `exists_inverse_observedMap_iff`
  (through `Function.bijective_iff_has_inverse`). Witness theorems use at most
  `propext`, `Quot.sound`.

An independent audit of `f2e3027b` against this contract passed every drawer
and made four bounded edits, included in `17913b28`: `fiberMapEquivProd`
states the raw fiber literally as pairs of fine views satisfying fine
compatibility and the two observations, with computation laws;
`observed_rel_iff_map_eq` now cites `Setoid.ker_def`; the witness theorem was
renamed from `not_lifts_t₀` to `not_nonempty_inter_t₀`; and Status gained
examples for the definitional form of `map`, `fiberMapEquivProd`, and
`bijective_observedMap_iff_surjective_map`, with README wording matched. The
audit found no verbatim mathlib duplicate among the local `Set` lemmas. All
changed declarations were re-audited: `fiberMapEquivProd` and
`not_nonempty_inter_t₀` use no axioms. The working copy is clean after the
commit.

# Request to the reviewer

Inspect the quotient relation (`observed_rel_iff`), the image criterion
(`mem_range_map_iff`), the inverse laws under `observedEquiv`, and the finite
failure on the production path, together with the cumulative M0 evidence.
Decide whether M1 is complete. If accepted, rewrite this file as
`READY FOR WORK`, `Turn: worker`, with the M2 objective, and add the M1
built-status paragraph to the proposal per Section 23.

# M0 acceptance evidence

M0 was accepted at `6a33636f` (submission `89c090ae`); the founding proposal
was accepted at `7159fd31`. Details remain in version history.
