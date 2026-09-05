# amalgam

Amalgam is a Lean 4 library studying what partial observations and their
admissible comparisons determine about possible global realizations. It
currently covers the fibers of an ordinary map, the compatible pairs of a
binary span, the comparison map that a commuting square induces from its
global states to those pairs, the reduction of compatible pairs across an
observed overlap, restriction systems over a preorder of contexts with their
compatible families, family comparison, and binary recovery, and the exact
classification of the attainable images on the five-context zigzag determined
by its adjacent binary datum. Everything
is stated for arbitrary types: carriers
and fibers may be empty, and no finiteness, decidability, or coverage hypothesis
appears in any criterion. [PROPOSAL.md](PROPOSAL.md) defines the mathematical
scope, roadmap, and completion criteria.

## Fibers

`Amalgam/Core/Fiber.lean` treats the fiber of `f : X → Y` over `y` as the
subtype `{x // f x = y}`, the convention of mathlib's `Equiv.sigmaFiberEquiv`.
No wrapper type is introduced.

The source decomposes as the dependent sum of the fibers. A fiber is nonempty
exactly over a value in the range and empty exactly over a value outside it, and
it is a subsingleton exactly when the value has at most one preimage. Globally,
a map is injective iff every fiber is a subsingleton, surjective iff every fiber
is nonempty, and bijective iff every fiber has a unique element, equivalently
iff every fiber is both nonempty and a subsingleton.

Fibers transport along equivalences of the source and target that intertwine two
maps (`Equiv.fiberCongr`). A fiber of a composite `g ∘ f` is the dependent sum,
over the fiber of `g`, of the fibers of `f`; precomposition with an equivalence
preserves fibers, and postcomposition transports them along its inverse. A fiber
is also the set preimage of a singleton.

## Compatible pairs and the comparison map

`Amalgam/Core/Comparison.lean` treats a binary span `L ─p→ B ←q─ R`. Its
compatible pairs are mathlib's fiber product `Function.Pullback p q`, the pairs
of local views that agree on the overlap, with projections
`Function.Pullback.fst` and `Function.Pullback.snd`. A compatible pair is
determined by its two projections. A commuting square, given by `f : G → L`,
`g : G → R` and a pointwise proof that `p ∘ f = q ∘ g`, induces the comparison
map `Function.Pullback.lift f g h : G → Function.Pullback p q`, whose two
projections are `f` and `g` and which is the only map with those projections.

The central identification is `Function.Pullback.fiberLiftEquiv`: the fiber of
the comparison over a compatible pair `c` is the type of global states whose two
restrictions are the two components of `c`. Pointwise, over a fixed compatible
pair:

- the fiber is empty iff no global state restricts to the pair;
- it is nonempty iff at least one does;
- it is a subsingleton iff any two that do coincide;
- it has a unique element iff exactly one does.

Globally, the comparison is injective iff the two local views jointly separate
global states, equivalently iff every fiber is a subsingleton; it is surjective
iff every compatible pair is amalgamated by some global state, equivalently iff
every fiber is nonempty; and it is bijective iff every compatible pair is
amalgamated by exactly one global state, equivalently iff every fiber has a
unique element. Uniqueness and existence stay separate: a subsingleton fiber
expresses uniqueness only when an extension exists, and the empty fiber over
`unreached₂` below is a subsingleton.

The fiber of the first projection over a left view is the fiber of `q` over its
overlap value, and symmetrically for the second projection. Exchanging the two
local views is an involutive equivalence that exchanges the two legs of the
comparison. A coherent equivalence of squares transports compatible pairs
(`Function.Pullback.congr`), matches comparison fibers
(`Function.Pullback.fiberLiftCongr`), and leaves injectivity, surjectivity, and
bijectivity of the comparison unchanged. At the opposite extreme, if the overlap
is a subsingleton then every pair of local views is compatible, the compatible
pairs are `L × R`, and the comparison is injective, surjective, or bijective
exactly when the joint map `x ↦ (f x, g x)` is.

## Reduction across an overlap

`Amalgam/Core/Reduction.lean` compares compatible pairs before and after a local
observation. The datum is two spans `L ─p→ B ←q─ R` and `L' ─p'→ B' ←q'─ R'`
together with observation maps `a : L → L'`, `b : B → B'` and `c : R → R'`, and
pointwise commutation proofs `p' (a l) = b (p l)` and `q' (c r) = b (q r)`.
Commutation is the only hypothesis below, except where the sufficient special
case names its own.

Commutation induces the raw comparison `Function.Pullback.map`, which sends a
fine compatible pair `(l, r)` to `(a l, c r)`. It is the lift of `a ∘ fst` and
`c ∘ snd`, so those are its two projections, and a fine pair lies over a coarse
pair exactly when both observed components match. It agrees with mathlib's
`Function.mapPullback`.

Two fine pairs are identified when both their observed components agree. That
relation is the kernel of the raw comparison, equivalently equality under it,
and `Function.Pullback.Observed` is the quotient by it. The induced
`Function.Pullback.observedMap`, the `k_bar` of the target statement, is the raw
comparison on any representative. It is injective, and its image is the image of
the raw comparison, so `Function.Pullback.observedEquivRange` identifies the
quotient with that common image, with both round-trip laws and the computation
law on a class.

The exact lifting criterion says which coarse compatible pairs are attained.
Coarse compatibility of `(u, v)` asserts only `p' u = q' v`, an equality of
coarse overlap values; `b` acts on fine overlap values and does not occur in it.
Only once fine representatives `a l = u` and `c r = v` are supplied does
commutation turn that equality into `b (p l) = b (q r)`. Such representatives
need not exist, because objectwise surjectivity is not assumed: every fine
object may be empty while the coarse objects are singletons. The criterion asks
for more, namely an actual common fine overlap value: a coarse compatible pair
`(u, v)` is attained if and only if

```text
{p(l) | a(l) = u} ∩ {q(r) | c(r) = v} ≠ ∅.
```

`Function.Pullback.mem_range_map_iff` states this in the displayed set form
`p '' (a ⁻¹' {u}) ∩ q '' (c ⁻¹' {v})`, and
`mem_range_map_iff_exists_overlap` in the equivalent form asserting a fine
overlap value reached both from a left view observed as `u` and from a right
view observed as `v`. `mem_range_observedMap_iff` is the same criterion for the
induced comparison.

The fiber of the raw comparison over a coarse pair is the type of fine
compatible pairs observed as it (`fiberMapEquiv`), equivalently the pairs of
fine views satisfying the three conditions of compatibility and the two
observations (`fiberMapEquivProd`), equivalently the compatible pairs of fine
lifts of its two components (`fiberMapEquivPullback`). These are
the fine lifts, and existence and uniqueness stay separate: the fiber is
nonempty exactly under the criterion, empty exactly when the criterion fails, a
subsingleton exactly when any two fine pairs observed as that coarse pair
coincide, and has a unique element exactly under unique existence.

The fibers of the induced comparison stand in an exact relation to these. Over a
coarse pair `t` the raw fiber `{s // map ha hc s = t}` and the quotient fiber
`{x // observedMap ha hc x = t}` are nonempty together, since the two
comparisons have the same image (`range_observedMap`); existence of a fine lift
of `t` and existence of an observed class over `t` are the same statement. What
the quotient discards is multiplicity: over an attained pair it identifies all
the fine lifts into a single observed class. Every quotient fiber is a
subsingleton whether or not the pair is attained
(`subsingleton_fiber_observedMap`), so a coarse pair carries either no observed
class or exactly one; that is a statement about observed classes and establishes
no uniqueness of a fine lift.

The closing theorem `bijective_observedMap_iff` is that the induced comparison
is bijective exactly when the criterion holds at every coarse compatible pair.
Equivalently the raw comparison is surjective, and the two comparisons are
surjective together. Under the criterion `Function.Pullback.observedEquiv` is
the equivalence `Observed ha hc ≃ p'.Pullback q'` extending the quotient
injection: its forward function is the induced comparison
(`observedEquiv_apply`). The inverse, which accepts a coarse compatible pair, is
`observedEquiv.symm` of type `p'.Pullback q' → Observed ha hc`. It satisfies
both round-trip laws (`observedMap_observedEquiv_symm` and
`observedEquiv_symm_observedMap`), and it is the only right inverse and the only
left inverse of the induced comparison
(`eq_observedEquiv_symm_of_rightInverse`,
`eq_observedEquiv_symm_of_leftInverse`). A two-sided inverse exists exactly
under the criterion, and any right inverse forces the criterion everywhere. That
inverse is obtained from bijectivity by classical choice, and it picks the
observed class over a coarse pair, never a fine representative; no uniqueness of
fine lifts follows from it.

As a sufficient special case only, an injective overlap observation makes the
criterion componentwise: a coarse pair is attained exactly when each of its
components is observed. Surjective `a` and `c` then make the induced comparison
bijective. The exact statement remains `bijective_observedMap_iff`.

Arbitrary observations restrict to their images.
`Function.Pullback.rangeRestrict` restricts the coarse leg to
`Set.range a → Set.range b`, the range factorizations commute with it, and they
are surjective by `Set.rangeFactorization_surjective`, so the restricted system
is a reduction. A restricted coarse pair is attained in the restricted system
exactly when its underlying coarse pair is attained in the original one.

### A surjective reduction that loses compatibility

`Amalgam/Models/Lifting.lean` certifies the witness prescribed for this failure.
The fine span is `Unit ─p→ Bool ←q─ Unit` with `p` constantly `false` and `q`
constantly `true`, so the two fine local views restrict to distinct overlap
values. Every coarse object is `Unit`, and `p'`, `q'`, `a`, `b` and `c` are the
unique maps to singletons. Both squares commute and all three observation maps
are surjective, so this is a reduction onto the coarse span.

The fine pullback is empty, since a compatible fine pair would give
`false = true`, and the observed quotient is empty with it. The coarse pullback
is a singleton, whose pair `t₀` is compatible. The criterion fails at `t₀`: the
fine overlap values reached from the left are `{false}` and those reached from
the right are `{true}`. So `t₀` lies in the image of neither comparison and has
no fine lift, the raw comparison is not surjective, and the induced comparison
is not bijective. Surjectivity of all three observations therefore does not
imply the criterion. No minimality is claimed for this witness.

## Restriction systems and compatible families

`Amalgam/System/Restriction.lean` fixes the datum. Contexts form a preorder
`C`, and `c ≤ d` reads as "`c` is coarser than `d`". A `RestrictionSystem`
assigns a state type `State c` to every context together with a restriction map
`res h : State d → State c` for every `h : c ≤ d`, subject to the identity and
composition laws `res_refl` and `res_trans`. For a family of contexts
`F : ι → C`, a compatible family is one state per index agreeing after
restriction to every common coarser context; `CompatibleFamily F` is the
subtype of assignments satisfying `Compatible F`. Finiteness of the index type
is never assumed and no decidability enters. The index type may be empty, in
which case there is exactly one compatible family (`uniqueOfIsEmpty`), and the
state types may be empty.

The declared restriction operations are the `FamilyMap`s: a reindexing
`index : κ → ι` together with an inequality `E k ≤ F (index k)` at every target
index. One datum covers both forgetting local views, by a reindexing that
misses indices, and restricting a view along a supplied context inequality.
`restrict m` acts on a compatible family by actual restriction of the supplied
states, `(restrict m x) k = res (m.le k) (x (m.index k))`; a map between
underlying products is not an operation. Restriction along the identity
operation is the identity (`restrict_id`, consuming `res_refl`), and
restriction along a composite is the composite of the restrictions
(`restrict_comp`, consuming `res_trans`).

A morphism `S.Hom S'` of restriction systems over the same contexts is an
observation `toFun c : S.State c → S'.State c` at every context commuting with
restriction. It carries compatible families to compatible families, and the raw
comparison `Hom.mapFamily F` observes each component. It is natural in the
family: `restrict_mapFamily` says that observing then restricting is
restricting then observing.

### Presentation invariance

`Amalgam/System/Presentation.lean` proves that presentations of the same shape
have equivalent compatible-family types. Everything rests on `restrict_endo`: a
declared operation from a family to itself is the identity on compatible
families, since compatibility already identifies each restricted state with the
state it is compared to. Hence declared operations in opposite directions
compose to the identity (`restrict_restrict`, consuming `restrict_comp` and so
`res_trans`), and two families with declared operations both ways have
equivalent compatible-family types (`restrictEquiv`).

Relabeling is the case of an equivalence of index types. For `e : κ ≃ ι`,
`relabel e` identifies the compatible families over `F` with those over
`F ∘ e`, reading the original family at `e k`, and both round trips hold
(`relabel_symm_relabel`, `relabel_relabel_symm`).

Redundancy is the case of added views. Given `σ : κ → ι` and
`h : ∀ k, G k ≤ F (σ k)`, so that every added view is obtained by restricting
an included context, `redundancyEquiv σ h` identifies the compatible families
over `Sum.elim F G` with those over `F`. Forgetting the added views is the
forward map and extending by `res (h k)` is the inverse. The added
compatibility conditions are discharged by `res_trans`, the extend-then-forget
round trip `forget_extend` by `res_refl`, and the forget-then-extend round trip
`extend_forget` by compatibility of the extended family together with
`res_refl`. Forgetting redundant views is therefore bijective
(`bijective_restrict_inl`). Adding a single view `c ≤ F i₀` (`addViewEquiv`)
and repeating an included view (`duplicateEquiv`) are the cases of a
one-element added index type.

The fiber of `restrict m` over a compatible family `z` is the type of
compatible families over the finer presentation whose declared restrictions are
the components of `z` (`restrictFiberEquiv`), the extension choices of `z`
along `m`. Under the redundancy hypothesis those choices form a subsingleton
(`subsingleton_fiber_restrict_inl`).

Two shapes are used below. A binary overlap is the family `![l, r]` over a
preorder carrying a context `b` with `b ≤ l` and `b ≤ r`, and
`compatible_fin_two_iff` reduces compatibility over `Fin 2` to the single cross
condition between the two views. The shared-overlap shape `L → B ← M → D ← R`
is the family `![L, M, R]` with `B ≤ L`, `B ≤ M`, `D ≤ M` and `D ≤ R`, whose
subfamilies are reached by the forgetful operations `FamilyMap.reindex`.

### Family comparison

`Amalgam/System/Comparison.lean` fixes a morphism `φ : S.Hom S'` and studies
the raw comparison `k_F = φ.mapFamily F` of each declared family.

`fiberMapFamilyEquiv` identifies the fiber of `k_F` over a coarse compatible
family `y` with the fine assignments that are compatible and satisfy every
component observation equation. The image criterion `mem_range_mapFamily_iff`
is therefore existence of such a simultaneous fine lift. Existence and
uniqueness stay separate: the fiber is nonempty exactly under the criterion,
empty exactly when it fails, a subsingleton exactly when any two fine families
observed as `y` coincide, and has a unique element exactly under unique
existence (`nonempty_fiber_mapFamily_iff`, `isEmpty_fiber_mapFamily_iff`,
`subsingleton_fiber_mapFamily_iff`, `nonempty_unique_fiber_mapFamily_iff`).

Two fine families are identified when all their observed components agree. That
relation is the kernel of the raw comparison (`observed_rel_family_iff`),
equivalently equality under it (`observed_rel_family_iff_mapFamily_eq`), and
`Hom.ObservedFamily F` is the quotient `Q_F` by it. The induced injection
`k_bar_F` is `Hom.observedMapFamily F`, the raw comparison on any
representative (`observedMapFamily_mk`). It is injective
(`observedMapFamily_injective`) and has the same image as the raw comparison
(`range_observedMapFamily`). The attainable image `I_F` is `Hom.image F`, whose
membership is the same criterion (`mem_image_iff`), and
`observedFamilyEquivImage` identifies `Q_F` with `I_F`, computing to the raw
comparison on a representative and satisfying both round trips.

Every fiber of the induced comparison is a subsingleton
(`subsingleton_fiber_observedMapFamily`), whether or not the coarse family is
attained, so a coarse family carries either no observed class or exactly one.
Raw and quotient fibers are nonempty together
(`nonempty_fiber_mapFamily_iff_nonempty_fiber_observedMapFamily`), because the
two comparisons have the same image. What the quotient discards is
multiplicity: it collapses all fine lifts of an attained family into one
observed class, which is no uniqueness statement about those lifts.

A declared family restriction `m : FamilyMap F E` acts at four levels. On fine
and coarse families it is `S.restrict m` and `S'.restrict m`, and the raw
square commutes: `restrict_comp_mapFamily` states
`S'.restrict m ∘ k_F = k_E ∘ S.restrict m`. On observed classes it is
`restrictObserved m`, well defined on classes and not on chosen fine
representatives, because equal observations restrict to equal observations
(`ker_mapFamily_restrict`); it computes as `S.restrict m` on a representative
(`restrictObserved_mk`) and its square with the induced comparisons commutes
(`observedMapFamily_restrictObserved`). On attainable images it is
`restrictImage m`, obtained from `mapsTo_restrict_image`, and
`restrictImage_observedFamilyEquivImage` is the square in which
`observedFamilyEquivImage` intertwines it with `restrictObserved m`. Identity
and composition are preserved at both levels: `restrictObserved_id`,
`restrictObserved_comp`, `restrictImage_id`, `restrictImage_comp`.

Naturality gives an inclusion of attainable images and nothing more
(`image_restrict_subset`):

```text
restrict_(F,E)(I_F) ⊆ I_E.
```

Equality of the restricted image with `I_E`, and surjectivity of
`restrictImage m`, are not claimed: a compatible family over `E` need not
extend to one over `F`.

Fine lifts are tracked along `m` by `fiberRestrict m y`, which sends a fine
lift of `y` to a fine lift of `S'.restrict m y` by restricting the same
supplied local states (`coe_fiberRestrict`), never by choosing an independent
lift.

### Binary recovery

`Amalgam/System/Binary.lean` identifies the binary case with the compatible
pairs and the reduction comparison above. Fix contexts `l` and `r` and a common
coarser context `b`, with `hl : b ≤ l`, `hr : b ≤ r` and
`hb : ∀ c, c ≤ l → c ≤ r → c ≤ b`. The three hypotheses say exactly that `b` is
greatest among the common coarser contexts of `l` and `r`
(`isGreatest_lowerBounds_pair_iff`); no lattice structure and no uniqueness of
`b` is assumed. Under `hb` agreement at every common coarser context reduces to
agreement at `b` (`compatible_pair_iff`), so `binaryEquiv` identifies the
compatible families over `![l, r]` with the compatible pairs
`Function.Pullback (res hl) (res hr)`, with both round trips.

Under that identification the family raw comparison is
`Function.Pullback.map` for the observations at `l`, `b` and `r`
(`binaryEquiv_mapFamily`). Fine-lift fibers correspond
(`fiberMapFamilyBinaryEquiv`), a coarse family is attained exactly when its
pair is (`mem_range_mapFamily_iff_mem_range_map`), the two attained images
agree as sets under `binaryEquiv` (`image_range_mapFamily`), and the observed
quotients correspond (`observedBinaryEquiv`) compatibly with the two injections
(`observedMap_observedBinaryEquiv`).

The intersection criterion is recovered for binary families:
`mem_range_mapFamily_iff_inter_nonempty` says a coarse family `y` is attained
exactly when the fine overlap values at `b` reached from states at `l` observed
as `y 0` meet those reached from states at `r` observed as `y 1`, and
`bijective_kerLift_mapFamily_iff_forall` says the family injection is bijective
exactly when that holds at every coarse compatible family.

For the shared-overlap shape, `compatible_triple_iff` reduces compatibility of
a family over `![L, M, R]` to the two overlap equations, under three
hypotheses: `B` is greatest among the common coarser contexts of `L` and `M`,
`D` is greatest among those of `M` and `R`, and every common coarser context of
`L` and `R` lies below `M`. The last holds in particular when `L` and `R` have
no common coarser context.

### Two calibration cases

`Amalgam/Models/Span.lean` carries the first case on the three-point span
preorder, where `B ≤ L` and `B ≤ R` and `B` is the greatest common coarser
context of `L` and `R` (`B_le_L`, `B_le_R`, `le_B_of_le_L_of_le_R`). The fine
system `fine` has state type `Bool` at `L` and `Unit` at `B` and at `R`, the
coarse system `coarse` has `Unit` at every context, and the observation
`φ : fine.Hom coarse` is the unique map at every context. Over `![L, R]` the
coarse compatible families are a singleton (`uniqueCoarseFamily`) whose element
is `y₀`, while the fine compatible families are read by their left state
(`fineEquiv`) and are exactly `x₀` and `x₁` (`eq_x₀_or_eq_x₁`), which differ
(`x₀_ne_x₁`). Both are observed as `y₀` (`mapFamily_x₀`, `mapFamily_x₁`).

The raw fiber over `y₀` is therefore equivalent to `Bool` (`fiberEquiv`), an
explicit equivalence with both round trips (`fiberEquiv_symm_apply_apply`,
`fiberEquiv_apply_symm_apply`); no counting package is used, and that
equivalence is the whole two-element description. The quotient fiber over `y₀`
is a singleton (`uniqueObservedFiber`), assembled from the separate facts that
it is inhabited (`nonempty_observedFiber`) and a subsingleton
(`subsingleton_observedFiber`), and the observed class of `x₀` is the observed
class of `x₁` (`observed_x₀_eq_observed_x₁`). Binary recovery agrees: under
`binaryEquiv` the reduction comparison `Function.Pullback.map` sends the pairs
of `x₀` and `x₁` to one coarse pair (`map_binaryEquiv_x₀_eq`), and `y₀` is
attained through the intersection criterion
(`y₀_mem_image_of_inter_nonempty`).

`Amalgam/Models/Zigzag.lean` carries the Section 12 witness on
`L → B ← M → D ← R`, over the five-point preorder shared from
`Amalgam/System/Zigzag.lean`, which has `B ≤ L`, `B ≤ M`, `D ≤ M` and
`D ≤ R` (`B_le_L`, `B_le_M`, `D_le_M`, `D_le_R`), with `B` greatest among the
common coarser contexts of `L` and `M`, `D` greatest among those of `M` and
`R`, and no common coarser context of `L` and `R`
(`le_B_of_le_L_of_le_M`, `le_D_of_le_M_of_le_R`, `not_le_L_of_le_R`); the last
gives vacuously the third hypothesis `compatible_triple_iff` consumes
(`le_M_of_le_L_of_le_R`). Every fine system
`sys lb mb md rd` has singleton state types at `L`, `M` and `R` and two-point
state types at `B` and `D`, and is determined by its four restriction values in
the arrow order `L→B, M→B, M→D, R→D`; the two fine systems of the witness are
`sysA` with values `(0, 0, 0, 1)` and `sysB` with values `(0, 1, 0, 0)`. The
coarse system has a singleton state type at every context, and the observations
`φA` and `φB` are the unique maps, which commute with restriction on the nose
and are surjective at every context (`surjective_φA`, `surjective_φB`). The
declared families are `LM`, `MR` and `LMR`, with the declared restriction
operations `toLM : FamilyMap LMR LM` and `toMR : FamilyMap LMR MR` forgetting
one view.

Compatibility over each family reduces to equations between restriction values
(`compatible_LM_iff`, `compatible_MR_iff`, `compatible_LMR_iff`). So system A
has a compatible family over `LM` and none over `MR` or `LMR`
(`nonempty_LM_A`, `isEmpty_MR_A`, `isEmpty_LMR_A`), and system B has one over
`MR` and none over `LM` or `LMR` (`nonempty_MR_B`, `isEmpty_LM_B`,
`isEmpty_LMR_B`), which is the table of attainable images.

| Attainable image | System A, values `(0, 0, 0, 1)` | System B, values `(0, 1, 0, 0)` |
| --- | --- | --- |
| `I_LM` | `Set.univ` (`image_LM_A`) | `∅` (`image_LM_B`) |
| `I_MR` | `∅` (`image_MR_A`) | `Set.univ` (`image_MR_B`) |
| `I_LMR` | `∅` (`image_LMR_A`) | `∅` (`image_LMR_B`) |

Here `Set.univ` is the singleton of coarse families. The inclusion supplied by
naturality is therefore strict in both systems,
`restrict toLM '' I_LMR ⊂ I_LM` for A (`ssubset_restrict_image_LMR_A`) and
`restrict toMR '' I_LMR ⊂ I_MR` for B (`ssubset_restrict_image_LMR_B`), and
neither induced map on attainable images is surjective
(`not_surjective_restrictImage_A`, `not_surjective_restrictImage_B`). The two
systems have equal full-family images (`image_LMR_eq`) while their `LM` and
`MR` images differ (`image_LM_ne`, `image_MR_ne`), so full-family content does
not determine all-family content. No smallest-shape claim is made, and no M3
datum is refuted.

## The zigzag information boundary

### Shape and admissible datum

`Amalgam/System/Zigzag.lean` fixes the shape and the admissible datum shared by
the concrete models and by the generic classification. `Zigzag.Context` is the
five-point preorder with `B ≤ L`, `B ≤ M`, `D ≤ M`, `D ≤ R`, reflexivity and no
other relation (`B_le_L`, `B_le_M`, `D_le_M`, `D_le_R`); `B` is the greatest
common coarser context of `L` and `M`, `D` that of `M` and `R`, and `L` and `R`
have no common coarser context (`le_B_of_le_L_of_le_M`, `le_D_of_le_M_of_le_R`,
`not_le_L_of_le_R`). The declared admissible families are the eight subfamilies
of the local views `L`, `M`, `R`, presented on `Fin n` in the order `L, M, R`:

```text
empty, single L, single M, single R, LM, LR, MR, LMR
```

Their declared operations are the forgetful restrictions along inclusions, each
a `FamilyMap` with reflexive context inequalities: `toLM`, `toMR` and `toLR`
from the full family to a pair, `LMR.toL`, `LMR.toM` and `LMR.toR` from the full
family to a single view, `LM.toL`, `LM.toM`, `LR.toL`, `LR.toR`, `MR.toM` and
`MR.toR` from a pair to its two views, and `toEmpty F` from any family to the
empty one. The overlap contexts `B` and `D` belong to the systems and to the
compatibility conditions, but they are not local views of this collection and
carry no reconstruction target of their own.

### Candidates, the supplied datum, and the target

`Amalgam/System/ZigzagTarget.lean` fixes an arbitrary coarse restriction system
`S'` on that shape. A candidate realization `Candidate S'` is a fine restriction
system `S` together with a morphism `φ : S.Hom S'` whose observation is
surjective at every context. No finiteness of the fine carriers, no
nonemptiness of global families, and no surjectivity of family restrictions is
imposed, and the fine system may live in any universe.

The supplied datum `Candidate.datum` is the ordered pair `(I_LM, I_MR)` of
attainable images over the two adjacent binary families, as subsets of the fixed
coarse compatible-family types. The target `Candidate.target : Target S'`
collects the attainable image of all eight declared families as subsets of those
same fixed coarse types. The target equivalence is equality of the eight subsets
(`Target.ext_iff`, equivalently agreement at every label of `Family` by
`Target.ext_iff_image`); it is neither a bijection of images nor presentation
equivalence.

Five of the eight entries are the same for every candidate. `image_empty` is the
full coarse image on the empty family, since both compatible-family types over
`Fin 0` are singletons; `image_single` is the full coarse image on a single
view, since a family over `Fin 1` is a state and is automatically compatible
(`compatible_single`), so surjectivity of the observation there suffices; and
`image_LR` is the full coarse image on the two outer views, since `L` and `R`
have no common coarser context, so every pair of states is compatible
(`compatible_LR`). On candidates these are `target_empty`, `target_l`,
`target_m`, `target_r` and `target_lr`, while `target_lm` and `target_mr` are
exactly the two components of the supplied datum.

Hence the closing equivalence `Candidate.target_eq_iff`: two candidates, whose
fine systems may live in independent universes, have the same target exactly
when they have the same supplied datum and the same full image `I_LMR`. That is
what licenses treating `I_LMR` as the remaining joint question at fixed datum;
it is not an assumption that the full image projects onto a proper image, for
which naturality supplies the inclusion `restrict(I_F) ⊆ I_E` and nothing more.
`image_eq_of_target_eq` reads the resulting agreement off at any label.

The induced maps on attainable images agree too, because both restrict the same
fixed coarse map `S'.restrict m`. `coe_restrictImage_eq` says that two morphisms
into `S'` induce the same map on underlying coarse families,
`restrictImage_setCongr` that the induced maps commute with the identifications
`Equiv.setCongr` of equal images, and
`Candidate.restrictImage_setCongr_of_target_eq` states that for candidates with
equal targets along every `FamilyMap` between declared families. The set-level
inclusion `S'.restrict m '' I_F ⊆ I_E` is literally the same statement for equal
targets, so it is not restated.

### The coarse join, the necessary inclusion, and the realization

`Amalgam/System/ZigzagRealization.lean` classifies the possible full images. For
arbitrary subsets `A` of the coarse `LM`-families and `A'` of the coarse
`MR`-families, `join A A'` is the coarse join

```text
J(A_LM, A_MR) =
  {y in P'_LMR | restrict_toLM(y) in A_LM and restrict_toMR(y) in A_MR}.
```

with membership `mem_join_iff`.

Necessity is naturality alone. `image_LMR_subset_join` says
`I_LMR ⊆ J(I_LM, I_MR)` for every morphism, consuming M2's
`mapsTo_restrict_image`; no surjectivity of the observation is used and the fine
system may live in any universe. `subset_join_of_images` is the same statement
for named images.

Sufficiency is an explicit construction of tagged copies. The fine states of
`realize A A' T` at a context are the `TaggedState` constructors: one `full y`
for each `y ∈ T` at every context, one `lm a h` for each `a ∈ A` at every context
below `L` or `M`, one `mr a' h` for each `a' ∈ A'` at every context below `M` or
`R`, and one `solo p h` for every coarse state at a finer context. A fine state
is therefore a coarse state carrying the witness it serves: `realizeHom A A' T`
observes a tagged state as the coarse state its witness dictates there
(`stateLMR`, `stateLM`, `stateMR`), and a `solo` copy as the restriction of the
coarse state it copies, which makes the observation surjective at every context
(`surjective_realizeHom`). Restriction preserves tags, so two fine
states agree on an overlap exactly when they carry the same tag
(`TaggedState.res_eq_res_LM_iff`, `TaggedState.res_eq_res_MR_iff`): the
compatible fine families over `LM` are the constant `full`- and `lm`-tagged
ones, those over `MR` the constant `full`- and `mr`-tagged ones, and those over
`LMR` the constant `full`-tagged ones (`eq_full_of_res_eq`). Reading their
observations gives `image_LM_realize` and `image_MR_realize`, which consume
`T ⊆ join A A'` because a `full`-tagged binary family is observed as a
restriction of its `y`, and `image_LMR_realize`, which holds for every `A`, `A'`
and `T`.

Together these are the exact classification `exists_realization_iff`: a triple
`(A, A', T)` is realized by a fine system with objectwise surjective
observations exactly when `T ⊆ join A A'`. It quantifies over an arbitrary
coarse system and all three subsets, and the converse carries no hypothesis
beyond that inclusion.

Uniqueness follows. `unique_full_image_iff` says the subsets of `join A A'` are
all equal exactly when `join A A' = ∅`, and `image_LMR_determined_iff` says any
two candidates supplying the datum `(A, A')` have the same full image exactly
when `join A A' = ∅`; otherwise `∅` and `join A A'` are two distinct realizable
full images of one datum. The gap is a missing agreement of fine middle states:
the datum records which coarse binary families lift, not whether the fine middle
state used by an `LM`-lift and the one used by an `MR`-lift of a single coarse
full family coincide.

### A strict finite witness and the finite sweep

`Amalgam/Models/MiddleSplit.lean` certifies that information loss on a finite
pair through the production family API. Its coarse system has one state at every
context, so every coarse compatible-family type is a singleton
(`uniqueCoarseFamily`) and every attainable image is `∅` or `Set.univ`. The fine
system `split` is

```text
Context    L       M        R       B       D
State      Unit    Bool     Unit    Bool    Bool
```

with restrictions `L→B : _ ↦ false`, `M→B` and `M→D` the identity,
`R→D : _ ↦ true`, and the identity on every reflexive arrow; the fine system
`glue` has one state at every context. Compatibility over `LM` forces the middle
state to be `false` and over `MR` forces it to be `true`
(`compatible_LM_split_iff`, `compatible_MR_split_iff`), so both adjacent binary
lifts exist while no lift of the full family does (`compatible_LMR_split_iff`,
`isEmpty_LMR_split`).

| Attainable image | `split` | `glue` |
| --- | --- | --- |
| `I_LM` | `Set.univ` (`image_LM_split`) | `Set.univ` (`image_LM_glue`) |
| `I_MR` | `Set.univ` (`image_MR_split`) | `Set.univ` (`image_MR_glue`) |
| `I_LMR` | `∅` (`image_LMR_split`) | `Set.univ` (`image_LMR_glue`) |

The two candidates therefore supply the same binary images (`image_LM_eq`,
`image_MR_eq`) and have different full images (`image_LMR_ne`), separated by the
named coarse family `y₀`, which `glue` attains (`y₀_mem_image_glue`) and `split`
does not (`y₀_notMem_image_split`). Both observations are surjective at every
context (`surjective_φsplit`, `surjective_φglue`), and all four adjacent binary
comparisons are surjective onto the coarse binary families
(`surjective_observedMapFamily_LM_split`, `surjective_observedMapFamily_MR_split`,
`surjective_observedMapFamily_LM_glue`, `surjective_observedMapFamily_MR_glue`).
No minimality is claimed for this pair.

`scripts/zigzag_sweep.py` records the bounded reconnaissance behind that choice.
It enumerates every fine system on the shape whose five carrier sizes lie
between one and two, with singleton coarse objects throughout, which is 872
systems. Under that degeneration each `I_F` is a boolean and the coarse join is
the conjunction, so the conjecture reads `I_LMR ≤ min(I_LM, I_MR)`. Five triples
`(I_LM, I_MR, I_LMR)` occur: `(1,1,1)`, `(1,1,0)`, `(1,0,0)`, `(0,1,0)` and
`(0,0,0)`. The necessary condition holds on all 872 systems, and all 5 of the 5
triples the conjecture allows are realized within the bound. The strict triple
`(1,1,0)` needs at least two fine middle states: with a single middle state `m`,
a left state with `r_LB l = r_MB m` and a right state with `r_MD m = r_RD r`
assemble into a compatible triple, forcing `I_LMR = 1`. Size shapes with an
empty carrier are excluded, since no map out of an empty set is onto a singleton
coarse state. The sweep covers only bounded carrier sizes and singleton coarse
objects, so no coarse family type in it has two elements; it can refute the
conjecture or guide the proof, and it cannot prove the universal law.

## Four comparison behaviors

`Amalgam/Models/Overlap.lean` gives four explicit finite commuting squares over
one span: the overlap is `Bool`, both local views are `Bool × Bool`, and both
restrictions are `Prod.fst`, so a pair of local views is compatible exactly when
the two overlap values agree. Only the global type and the two restriction maps
differ between the four squares, so the four behaviors are four global
realizations of the same local situation.

| Comparison | Behavior | Positive property | Negative property |
| --- | --- | --- | --- |
| `compare₁` | bijective | `bijective_compare₁` | — |
| `compare₂` | injective, not surjective | `injective_compare₂` | `not_surjective_compare₂` |
| `compare₃` | surjective, not injective | `surjective_compare₃` | `not_injective_compare₃` |
| `compare₄` | neither | — | `not_injective_compare₄`, `not_surjective_compare₄` |

Each failure carries a witness of the kind that failure asserts. Failure of
existence is certified by a named compatible pair together with a proof that its
comparison fiber is empty: `unreached₂` and `unreached₄`, with
`isEmpty_fiber_unreached₂` and `isEmpty_fiber_unreached₄`. Failure of uniqueness
is certified by two distinct global states with equal comparison value:
`state₃` and `state₃'`, and `state₄` and `state₄'`. The positive properties are
proved through the criteria above, so the witnesses certify the comparison
construction rather than an unrelated finite function.

## Status manifest

Every mathematical claim above is mirrored by a typed `example` in
`Amalgam/Status.lean`, at the generality claimed: arbitrary types, arbitrary
preorders of contexts, and arbitrary index types in arbitrary independent
universes for the generic statements, an arbitrary coarse system on the fixed
zigzag shape with candidates at explicit independent fine universes for the
information boundary, and the concrete finite models
for the four comparison behaviors, the surjective reduction, the two
calibration cases, and the strict middle-split witness. The root
`Amalgam` aggregator imports the manifest, so a full build checks it; no library
module imports it.

## Building

The Nix devshell supplies `elan`, which provides the `lake` and `lean` proxies
for the toolchain named in `lean-toolchain`.

```nushell
nix develop
lake build
```

`nu tasks.nu cache` runs `lake exe cache get`, which fetches prebuilt mathlib
artifacts for the pinned dependencies. Run it after changing `lean-toolchain`
or the mathlib revision, before `lake build`.

`nu tasks.nu` lists the shorthands for building, caching, formatting, and
running the flake checks.
