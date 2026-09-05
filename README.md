# amalgam

Amalgam is a Lean 4 library studying what partial observations and their
admissible comparisons determine about possible global realizations. It
currently covers the fibers of an ordinary map, the compatible pairs of a
binary span, and the comparison map that a commuting square induces from its
global states to those pairs. Everything is stated for arbitrary types: carriers
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
expresses uniqueness only when an extension exists.

The fiber of the first projection over a left view is the fiber of `q` over its
overlap value, and symmetrically for the second projection. Exchanging the two
local views is an involutive equivalence that exchanges the two legs of the
comparison. A coherent equivalence of squares transports compatible pairs
(`Function.Pullback.congr`), matches comparison fibers
(`Function.Pullback.fiberLiftCongr`), and leaves injectivity, surjectivity, and
bijectivity of the comparison unchanged. At the opposite extreme, if the overlap
is a subsingleton then every pair of local views is compatible, the compatible
pairs are `L × R`, and the comparison is bijective exactly when the joint map
`x ↦ (f x, g x)` is.

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
universes for the generic statements, and the four concrete squares for the four
behaviors. The root `Amalgam` aggregator imports the manifest, so a full build
checks it; no library module imports it.

## Building

The Nix devshell supplies `elan`, which provides the `lake` and `lean` proxies
for the toolchain named in `lean-toolchain`.

```nushell
nix develop
lake build
```

`nu tasks.nu` lists the shorthands for building, formatting, and running the
flake checks.
