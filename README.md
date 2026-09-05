# amalgam

Amalgam is a Lean 4 library studying what partial observations and their
admissible comparisons determine about possible global realizations. It
currently covers the fibers of an ordinary map, the compatible pairs of a
binary span, the comparison map that a commuting square induces from its
global states to those pairs, the reduction of compatible pairs across an
observed overlap, and restriction systems over a preorder of contexts with
their compatible families, family comparison, and binary recovery. Everything
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
`Hom.observedFamily F` is the quotient `Q_F` by it. The induced injection
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
`D` is greatest among those of `M` and `R`, and `L` and `R` have no common
coarser context.

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
universes for the generic statements, and the concrete finite models
for the four comparison behaviors and the surjective reduction. The root
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
