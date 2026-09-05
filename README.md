# amalgam

Amalgam is a Lean 4 library studying what partial observations and their
admissible comparisons determine about possible global realizations. It
currently covers the fibers of an ordinary map, the compatible pairs of a
binary span, the comparison map that a commuting square induces from its
global states to those pairs, and the reduction of compatible pairs across an
observed overlap. Everything is stated for arbitrary types: carriers
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
`Amalgam/Status.lean`, at the generality claimed: arbitrary types in arbitrary
independent universes for the generic statements, and the concrete finite models
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
