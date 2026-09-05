# Amalgam

## Proposal for a Formal Theory of Restriction, Compatibility, and Global Extension

### Status

This is the founding proposal for a new Lean 4 project.

The Lean implementation has not started. The theorem packages, criteria, and
witnesses below specify work to formalize; they are not a report of compiled
results.

The project begins from a clean repository and a clean mathematical context.
Earlier repositories are evidence and possible theorem donors, not inherited
ontology. Their names, namespaces, architectures, and interpretations do not
enter the foundation automatically.

The project name is **Amalgam**.

Mathematical notation uses readable Unicode and plain-text names in CommonMark
inline code and fenced `text` blocks. Subscripts use underscores, and a joint
index is parenthesized, as in `ext_(f,g)`. These are schematic formulas, not
Lean source. This convention needs no math-rendering extension and is preserved
by the configured Markdown formatter.

Its scope is not fixed by the name. In standard mathematical language, an
amalgamation is a global object realizing compatible local data. The project
studies existence, uniqueness, multiplicity, observational loss, and
reconstruction around that operation.

______________________________________________________________________

# 1. The stake

The project begins from one question:

> **Determine exactly what a system of partial observations, with its
> admissible comparisons, fixes about its possible global realizations.**

This has two obligations: reconstruct what the supplied datum determines and
characterize the freedom it leaves. Each investigation fixes its datum, class
of candidate realizations, and target equivalence before pursuing refinements.
Coherent diagram isomorphism is one target; equality of admissible observable
content is another. They need not distinguish the same realizations.

The forward construction is

```text
global states → partial observations → compatible local families
              → extension fibers → observables → reconstruction
```

An observation forgets distinctions.

Its fibers are the states it cannot distinguish.

Several observations can overlap. Their local outcomes may be mutually
compatible while admitting no global state, exactly one global state, or
several global states.

Those are different mathematical phenomena:

```text
nonexistence:       compatible local data has no global extension
uniqueness:         compatible local data has at most one extension
incidence:          extensions are distributed over local data
coarse obstruction: a summary records only part of that distribution
```

The project studies these levels separately. It must never identify a scalar
summary with the extension structure that produced it.

The research direction runs back from supplied local data to its possible
realizations. The central test is whether reducing local descriptions to their
observed content preserves the constraints on their joint realization. The
single-map and finite-profile theorems support this question; they do not
require an indefinite progression toward finer presentation invariants.

______________________________________________________________________

# 2. Why a new foundation

The immediate predecessor began with scalar fields on lattices and measured
failure of a valuation law. That was the correct primitive for its program.
Its formal development established three facts that change the next question.

First, finite scalar inclusion--exclusion observation has an exact ceiling.
Pairwise data suffices in distributive contexts; order 3 can add information
off distributivity; no higher finite order refines the cumulative observable
on any lattice.

Second, complete scalar defect data need not determine a realization. Two
finite restriction systems can have the same context cardinalities and hence
the same scalar defect data of every finite order while their comparison maps
have different incidence behavior.

Third, for a finite map

```text
f : A → B
```

the fiber-cardinality function

```text
ext_f(b) = |f⁻¹(b)|
```

recovers the map over the fixed codomain exactly up to relabeling inside its
fibers. The scalar comparison term is only a coarse statistic of this profile.

These are motivation, not imports.

They show that the information of interest lives first in maps and fibers, not
in a higher scalar defect. If the project were started today with those
results already known, a scalar field would not be chosen as primitive.

Amalgam therefore begins one level lower:

```text
restriction, compatibility, comparison, and extension
```

The old scalar calculus may reappear as a derived observation when it answers
a question raised by the reconstruction problem. It must not determine the
new architecture or its completion requirements in advance.

______________________________________________________________________

# 3. What is primitive

The first version should assume as little as possible.

Begin with ordinary types and maps.

A single observation is a function

```text
f : X → Y
```

For an observed value `y : Y`, its extension fiber is

```text
Ext_f(y) = {x : X | f(x) = y}
```

This is already an inverse object. It records every global state consistent
with the observation `y`.

The first genuinely local-to-global datum consists of local state spaces `L`
and `R`, an overlap space `B`, and restriction maps `L → B ← R`.
It can be supplied without a global state space. A candidate realization adds
global states `G` and maps forming a commuting square:

```text
G ───→ L
│      │
↓      ↓
R ───→ B
```

The compatible local pairs form the pullback-like type

```text
Compat(L, R; B) = {(l, r) : L × R | l|_B = r|_B}
```

Commutativity induces the comparison map

```text
compare : G → Compat(L, R; B)
```

For a compatible pair `p`, the fiber

```text
Ext_compare(p)
```

is the type of its global amalgamations. This notation is schematic; the Lean
API should use an existing standard fiber construction unless a new wrapper
materially improves later theorem statements.

No lattice is primitive.

No cardinality is primitive.

No scalar field is primitive.

No probability is primitive.

No category-theoretic framework is primitive.

All may enter later if theorems consume them.

The datum also specifies which families of observations may be compared or
combined. Initially this means the named binary overlap and its projections;
later it may mean named finite families with their restriction laws. Further
operations enter only with an explicit definition and laws. An available
product of types alone does not declare its joint observation admissible.

______________________________________________________________________

# 4. Existence, uniqueness, and incidence

The comparison map separates the principal failure modes exactly.

For compatible local data `p`:

- `Ext_compare(p)` is empty exactly when
  globalization fails;
- it is nonempty exactly when at least one globalization exists;
- it is a subsingleton exactly when globalization is unique when it exists;
- it has a unique element exactly when globalization exists uniquely.

Globally:

- injectivity of `compare` is uniqueness of amalgamation for every compatible
  family;
- surjectivity is existence of an amalgamation for every compatible family;
- bijectivity is unique existence for every compatible family.

The project should prove pointwise and global formulations and the exact
equivalences between them. It should not replace them by one vague predicate
such as “good gluing.”

Four finite witnesses belong near the foundation:

1. a bijective comparison;
2. an injective but nonsurjective comparison;
3. a surjective but noninjective comparison;
4. a comparison that is neither.

These examples prevent absence and identification from being conflated.

______________________________________________________________________

# 5. Observation as a mathematical map

An observation is not an interpretive metaphor in the core.

It is a map that identifies elements in the same fiber and may omit elements
of its codomain.

For `f : X → Y`, two global states are observationally indistinguishable
when

```text
f(x) = f(x')
```

This relation is represented by the kernel pair `X ×_Y X`. Reserve the
algebraic word `kernel` for contexts where a pointed or homomorphic kernel is
actually present; for a general observable, state the induced equality
relation explicitly.

For an observable on structures

```text
O : Systems → Data
```

the induced observational equivalence is

```text
S ∼_O T  ↔  O(S) = O(T)
```

Every observable introduced by the project must answer four questions:

1. What is its exact domain?
2. What datum does it return?
3. What equivalence relation does equality of that datum induce?
4. What structure can be reconstructed from the datum, up to what symmetry?

Calling something an observable before these are stated is premature.

For a class of realizations, observable content is specified by a declared
family of admissible observations and comparison operations. Two realizations
are equivalent relative to this datum when every declared observation agrees,
using a fixed convention for transporting labels when bases vary. State this
equivalence separately from coherent diagram isomorphism and prove their
relationship. Equality of data on a fixed labelled base must not silently
become isomorphism of unlabelled data.

Adding an admissible joint observation can change this equivalence. Any claim
that a reduction preserves observable content must cover the declared
combinations, not just the individual maps. The selection of those maps is
an input to the mathematics; agreement of one selected statistic does not
justify identifying states with respect to every other observation.

______________________________________________________________________

# 6. Refinement serves a declared reconstruction target

Suppose `O_0` and `O_1` observe the same class of
systems.

The second is at least as informative as the first only when

```text
O_1(S) = O_1(T)  ⇒  O_0(S) = O_0(T)
```

Prefer an explicit factorization

```text
O_0 = q ∘ O_1
```

when one exists. It identifies the forgetting map, not merely the resulting
implication.

A refinement is strictly stronger only after an explicit witness satisfies

```text
O_0(S) = O_0(T),    O_1(S) ≠ O_1(T)
```

A datum is complete relative to a target equivalence `≃` when

```text
O(S) = O(T)  ↔  S ≃ T
```

The target equivalence must be named. “Determines the system” is not an
acceptable theorem summary.

Minimality should be proved by deleting or coarsening a named measurement and
exhibiting failure, not inferred from a dimension count alone.

Strictness alone does not make a refinement a research priority. Name the
unresolved question it settles for the declared datum and target. If it
distinguishes presentations already equivalent under that target, it answers
a different question and must be justified as a change of scope.

For example, a one-element source and a two-element source mapping constantly
to the same singleton have the same observed image but different extension
profiles. The profile recovers hidden multiplicity for the fixed-base map
target. For an image-only target, that multiplicity is unconstrained. Whether
an admissible interaction can expose it is a further theorem about the supplied
operations, not a consequence of counting the fibers.

______________________________________________________________________

# 7. Fixed-base reconstruction is not system reconstruction

For maps `f : X → B` and `g : Y → B` into the same fixed codomain, the
appropriate residual symmetry is an equivalence over `B`:

```text
f ≃_B g  ↔  ∃ e : X ≃ Y, ∀ x : X, g(e(x)) = f(x)
```

This reconstructs a map while treating labels inside each fiber as
unobservable.

It does not reconstruct the codomain, the maps defining compatibility, or a
whole restriction system.

When bases vary, an equivalence must also transport the codomain. When several
maps share objects, componentwise equivalences must commute with every map.

The project must distinguish:

- a map over a fixed codomain;
- a map with codomain reconstructed up to equivalence;
- a family of maps reconstructed independently;
- a whole diagram reconstructed by one coherent family of equivalences.

Local equivalences are not a global equivalence until their coherence is a
theorem.

This distinction is the first place where Amalgam goes beyond its motivating
finite-map inverse theorem.

______________________________________________________________________

# 8. Finite profiles are derived observables

When `X` and `Y` are finite, the extension profile of `f : X → Y` is

```text
ext_f(y) = |Ext_f(y)|
```

Its foundational theorem package should include:

- total mass:
  `∑_y ext_f(y) = |X|`;
- reachedness:
  `y` is reached exactly when `ext_f(y) > 0`;
- missedness:
  `y` is missed exactly when `ext_f(y) = 0`;
- injectivity exactly when every count is at most one;
- surjectivity exactly when every count is positive;
- bijectivity exactly when every count is one;
- redundancy as total fiber excess;
- reconstruction over a fixed codomain:
  `ext_f = ext_g` exactly when
  `f ≃_Y g`.

This package is a known proof donor. It should be ported only after the new
repository independently arrives at the definitions above, with the minimum
dependencies and in the new vocabulary.

The natural-number profile and finite-sum package use finite carriers. The
classification mechanism itself extends to arbitrary unstructured types:
equality of cardinal-valued fiber profiles gives an equivalence of each pair
of corresponding fibers, and classical choice assembles these into an
equivalence over the fixed base. Conversely, an equivalence over the base gives
equal fiber cardinals. Compare cardinals in a common universe, using lifts
when necessary. The underlying cardinal equality criterion is mathlib's
[`Cardinal.eq`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/SetTheory/Cardinal/Defs.html#Cardinal.eq).

This is an existence classification; cardinal equality alone supplies no
computable inverse. Cardinality also forgets additional structure on fibers,
such as topology, measure, or group operations, so equal underlying cardinals
need not give structure-preserving equivalences. A coarser statistic than the
full cardinal-valued profile may lose even unstructured multiplicity. Infinitude
alone is not the source of that loss.

This boundary corrects the scope of the supporting theorem. It adds no
infinite-cardinal formalization milestone; port the finite package where
natural-number counting is consumed.

______________________________________________________________________

# 9. Marginals and joint incidence

Consider two observations of the same finite source:

```text
f : X → Y,    g : X → Z
```

Their joint observation is

```text
(f, g) : X → Y × Z
```

with joint extension profile

```text
ext_(f,g)(y, z) = |{x : X | f(x) = y and g(x) = z}|
```

The individual profiles are its marginals:

```text
ext_f(y) = ∑_z ext_(f,g)(y, z)
ext_g(z) = ∑_y ext_(f,g)(y, z)
```

Separate profiles therefore forget how the two observations co-occur on the
common source.

The marginal-blindness witness should exhibit two finite forks with identical
separate profiles but different joint profiles and no isomorphism of forks
over the fixed codomains.

The corresponding inverse theorem should prove that the joint profile
reconstructs the fork over fixed `Y` and `Z` exactly up to a relabeling of
`X` commuting with both observations.

This is an elementary instance of the project's pattern:

```text
coarse invariant → identified structures
                 → fiberwise refinement → recovered incidence
```

Do not infer an indefinite tower of named pairwise, triple, and higher joint
profiles. Once adjacent arities reveal a recurrence or a family-level object,
state the general construction or prove a saturation theorem before adding
another named layer.

______________________________________________________________________

# 10. Compatibility is more than a product

Independent observations land in `Y × Z`. Overlapping observations land
in a compatibility object.

Given

```text
p : Y → B,    q : Z → B
```

the compatible pairs are

```text
Y ×_B Z = {(y, z) : Y × Z | p(y) = q(z)}
```

A global state space `X`, maps `f : X → Y` and `g : X → Z`, and the law

```text
p ∘ f = q ∘ g
```

induce

```text
compare : X → Y ×_B Z
```

The project should identify exactly which results about independent joint
observation are instances of this compatibility shape, and which require the
overlap map.

The compatibility object must be observable in theorems. A structure field
that never changes a statement or proof does not belong in the interface.

## Reduction across an overlap

The first substantive target compares compatibility before and after local
observation. Fix spans of arbitrary types `L ─p→ B ←q─ R` and
`L' ─p'→ B' ←q'─ R'`, with maps `a : L → L'`, `b : B → B'`, and
`c : R → R'` satisfying `p' ∘ a = b ∘ p` and `q' ∘ c = b ∘ q`.
Commutation is the only hypothesis for the following constructions, fiber
descriptions, and image criterion. No finite carriers or surjectivity are
required.

Objectwise surjective maps specialize this setup to actual reductions onto
the coarse objects. Arbitrary observations can instead be restricted to their
images; the commutation laws restrict the coarse span to those images too.
State this specialization after the general theorem.

Write `P = L ×_B R` and `P' = L' ×_(B') R'`. Commutation gives
`k : P → P'`, with `k(l, r) = (a(l), c(r))`. On `P`, identify pairs exactly
when their two observed components agree, and write `Q` for the quotient.
The induced comparison `k_bar : Q → P'` is canonical and injective.
This construction and injectivity are calibration lemmas to formalize, not
additional hypotheses. Its image is the jointly attainable coarse content.

The exact lifting criterion to prove is: a coarse compatible pair `(u, v)`
lies in that image if and only if

```text
{p(l) | a(l) = u} ∩ {q(r) | c(r) = v} ≠ ∅.
```

Thus reduction and assembly agree precisely when this intersection is
nonempty for every coarse compatible pair. Coarse compatibility asserts only
equality after `b`; the criterion asks for an actual common fine overlap value.
The theorem must identify each fiber of `k` with its fine compatible lifts,
separating existence and uniqueness of representatives from the automatic
uniqueness of an observed class in `Q`. A two-sided inverse to `k_bar` on all of
`P'` exists exactly under the lifting criterion and is then unique, with both
round-trip laws. No preferred fine representative follows from that inverse.

A strict finite witness is prescribed: let `L` and `R` be singletons, let
`B = {0, 1}`, and restrict their elements to `0` and `1`, respectively. Reduce
all three objects to singletons. The reduction maps commute and are
surjective, but `P` is empty while `P'` is a singleton. Formalize this witness;
do not claim it is minimal without a separate exclusion proof.

This is a statement about compatible local descriptions. For a supplied
global realization `G → P`, its observed image in `P'` may be smaller
still. Keep failure of coarse pairs to lift to `P` separate from failure of
fine compatible pairs to extend to `G`.

The binary theorem calibrates the definitions. The central research question
is which supplied local lifting or incidence data suffices for the same
reconstruction to hold coherently across shared overlaps. Separate lifts may
use inconsistent representatives on a shared context.

______________________________________________________________________

# 11. Systems of restriction

Only after the binary comparison theory has exposed what it consumes should
the project introduce a system of contexts.

A first system may consist of:

- a finite or locally finite family of contexts;
- a state type at each context;
- restriction maps toward coarser contexts;
- identity and composition laws.

For a named finite family of local contexts, define compatible local states by
agreement under common restrictions. A more global context supplies a
comparison map into that compatible-family type.

The first implementation should use the weakest indexing structure required
by its theorems. A preorder may suffice. A category should not be introduced
merely because restriction maps can eventually be described functorially.

The finite-family interface must prove:

- presentation invariance of compatible families;
- degeneration when a local view is redundant;
- reduction to the binary comparison;
- naturality under maps of restriction systems;
- exact behavior under refinement or coarsening of a family;
- the relation between full-family extension fibers and fibers seen by
  subfamilies.

If theorems repeatedly consume a standard limit, presheaf, or sheaf interface,
the structure should migrate toward that established abstraction. Do not
announce this identification before the statements require it.

______________________________________________________________________

# 12. Coherent reconstruction

The central inverse problem concerns a fixed finite restriction shape with
shared overlaps and declared admissible comparisons. Supply the coarse local
datum first and define its candidate fine realizations and commuting
observation maps. For each declared admissible family `F`, let `P_F` and
`P'_F` be the fine and coarse compatible-family types. The raw comparison
`k_F : P_F → P'_F` records fine lifts. Quotienting its source by equality of
observed components gives `Q_F` and an injection `k_bar_F : Q_F → P'_F`.
Define the attainable image `I_F = image(k_F) = image(k_bar_F)`.

The initial reconstruction target is the collection of `I_F` for **every**
declared admissible family, with the maps induced by the declared coarse
restrictions between families. Over the fixed coarse datum, observable-content
equivalence means equality of these images as subsets of their respective
`P'_F`; their restriction maps then agree as restrictions of the fixed maps.
When bases vary, specify the coherent transport convention first.

For each declared restriction from `F` to `E`, naturality supplies

```text
restrict_(F,E)(I_F) ⊆ I_E.
```

It does not supply equality: a fine compatible family on `E` need not extend
to one on `F`. The full-family image is the distinguished joint question,
but it does not in general determine the proper-family images. M3 must record
which of these the supplied local datum already fixes and which still need
reconstruction. A theorem about the full image alone closes the target only
with a theorem that it, together with the supplied datum, determines all
remaining admissible images. Do not impose extension of all local families
as an implicit assumption.

A prospective finite witness uses `L → B ← M → D ← R`. Each of `L`, `M`, and
`R` is a singleton, each of `B` and `D` is `{0, 1}`, and all coarse objects are
singletons. All reduction maps are the unique surjections, so their squares
commute. Declare `LM`, `MR`, and `LMR` admissible, together with their local
views and restriction maps. List the fine restriction values in the order
`L→B`, `M→B`, `M→D`, `R→D`:

```text
System  Restriction values   I_LM       I_MR       I_LMR
A       (0, 0, 0, 1)         singleton  empty      empty
B       (0, 1, 0, 0)         empty      singleton  empty
```

This witness is to be certified with the finite-family theory. It separates
equality of full-family content from equality of all admissible content; it
makes no claim about completeness of the local input datum still to be chosen
in M3. No smallest-shape claim is made.

The project must classify what local data determines this collection of
images and what coherence information remains missing. Binary lifting
conditions may provide representatives separately without a single consistent
choice across the family. Fix one shape before stating the classification.

Presentation equivalence is a separate target: component equivalences commute
with every restriction and respect the supplied observation maps. Independently
reconstructed comparison maps need not yield such an equivalence, since their
equivalences may disagree on shared spaces. Investigate that gap when it
obstructs the declared target. Recovering further hidden presentation structure
is not an automatic obligation once observable content is reconstructed.

Closure requires an exact sufficiency theorem or a sharp obstruction for the
chosen local datum, with an explicit strict finite witness for every claimed
information loss. If a refinement is required, name the missing compatibility
datum and prove what it resolves for the entire target collection. A
classification of unavoidable ambiguity can settle this problem without
recovering a unique presentation.

______________________________________________________________________

# 13. The inverse-first doctrine

An inverse problem may start with local state spaces, restrictions, and
admissible comparisons, before any global realization is supplied. Declare
what counts as a realization, including any required coverage of local
outcomes. Neither a universal source nor surjectivity of every comparison is
implicit. Constructing the type of compatible families does not assert that
every family is realized.

Forward construction is easy to overvalue.

Given a restriction system, one can calculate compatible families, comparison
maps, fibers, profiles, counts, and scalar summaries.

The project should repeatedly reverse each map:

```text
scalar summary     ⇒ which profile quotient?
extension profile  ⇒ which comparison map?
comparison maps    ⇒ which restriction system?
local equivalences ⇒ which coherent equivalence?
```

Each arrow requires a theorem or an impossibility result.

Every inverse theorem must state:

1. the supplied datum;
2. which parts of the base or indexing shape are fixed;
3. the exact reconstructed object;
4. the residual equivalence;
5. whether the reconstruction is explicit;
6. a strict witness showing why weaker data fails, when applicable.

Record separately which features are fixed across all realizations and which
can vary without changing the declared observable content. Changing the datum
or target equivalence changes the inverse problem and must be stated as such.

Existence alone is not a reconstruction algorithm. A proof that constructs an
inverse should expose it as a named definition with both round-trip laws.

______________________________________________________________________

# 14. Realizability

An abstract profile or family of fibers may not arise from one coherent
restriction system.

The realizability problem asks:

> **Which abstract extension data is induced by an actual system of
> restrictions and comparison maps?**

The answer should be separated into levels.

For a single finite map, a natural-number-valued profile has an elementary
realization by a disjoint union of finite fibers. This solves only the
fixed-codomain, unstructured case.

For a finite fork, the first realizability theorem should construct a source
from an arbitrary natural-number-valued joint table and prove that prescribed
separate profiles are realized simultaneously exactly when they are its row
and column sums.

For a system of overlapping comparisons, independently realizable profiles
may fail to assemble because shared restrictions impose coherence conditions.

Theorems should distinguish:

- pointwise realizability of each fiber datum;
- simultaneous realizability over shared state spaces;
- realizability by a functorial restriction system;
- uniqueness up to coherent equivalence.

Realizability conditions belong alongside the coherent inverse problem. A
well-defined local datum need not possess a simultaneous global assignment.
Failure of such an assignment obstructs that specified global representation;
it does not by itself invalidate the local datum. Distinguish a restriction
diagram's existence, coverage by a candidate realization, and existence of a
global section. Each requires its own statement.

Do not introduce decorative state spaces whose internal organization no
theorem observes. If an interface records only aggregate masses or counts,
prove the resulting algebraic envelope and remove unconsumed structure.

______________________________________________________________________

# 15. Scalarization is a forgetting map

Counts, logarithms, defects, entropy-like quantities, and kernels may later be
useful. They are outputs.

The project should seek explicit factorizations such as

```text
extension fibers → fiber profile → incidence summary → scalar obstruction
```

At each arrow:

- define the map;
- characterize equality of its outputs;
- exhibit strict information loss when present;
- state conditions under which the map becomes complete.

Missing compatible local states and multiple global extensions can cancel in
a scalar ratio. A zero scalar obstruction therefore need not mean successful
or unique globalization.

No sign, convexity, entropy, metric, or probabilistic interpretation is
universal until proved from the exact extension hypotheses that imply it.

The word `conditioning` should be used in the core only for a literal
restriction to a fiber or subobject. Probabilistic conditioning belongs in a
module carrying probability data.

______________________________________________________________________

# 16. Descent as a possible downstream bridge

The prior scalar theory is a candidate realization of Amalgam, not a
foundation.

After the extension architecture stabilizes, a bridge may show that a finite
restriction system gives:

1. compatible-family types;
2. comparison maps;
3. extension profiles;
4. reached, missed, and redundant incidence counts;
5. logarithmic cardinality fields;
6. pairwise and order-3 scalar defects.

The bridge should factor the scalar observation through the richer incidence
data and reprove its blindness as an instance of a general forgetting theorem.

The desired relationship is

```text
Descent defect data is a cardinal statistic of amalgamation data.
```

That sentence is a research target until a theorem states the maps and exact
equivalence relations involved. It must not appear as a factual README claim
before then.

Do not depend on the entire prior repository merely to establish the bridge.
Port or import only the minimal stable interfaces after Amalgam's own objects
have earned their names.

This bridge is conditional follow-on work. Pursue it only for a named
information-boundary question arising from the central reconstruction result;
its absence does not prevent closure.

______________________________________________________________________

# 17. Relation to established mathematics

Compatible families and amalgamations already occur in sheaf theory. There,
at most one amalgamation is a separatedness condition and unique
amalgamation is the sheaf condition.

Amalgam should not rename those notions if its definitions converge on them.
It should also not begin by importing the full theory of sites and sheaves.

The initial contribution is different in emphasis:

- retain the entire extension fiber, not only existence or uniqueness;
- study observables of those fibers and their exact induced equivalences;
- reconstruct maps and systems from extension data;
- distinguish pointwise reconstruction from coherent reconstruction;
- determine when local reduction preserves jointly attainable descriptions;
- classify the information lost by marginalization and scalarization.

Other established subjects may later recognize the same structure. Use their
standard names when theorem statements establish the identification. Analogy
alone is not a dependency.

______________________________________________________________________

# 18. Exact-law discipline

For every important construction, seek the following anchors whenever the
mathematics permits:

1. **Exact map** — the actual comparison or forgetting map.
2. **Boundary** — necessary and sufficient conditions for existence,
   uniqueness, or exactness.
3. **Failure modes** — separate strict witnesses for nonexistence and
   nonuniqueness.
4. **Observable equivalence** — the exact relation induced by the datum.
5. **Inverse theorem** — what the datum reconstructs and up to which symmetry.
6. **Minimality** — a witness that a named coarsening loses information.
7. **Realizability** — which abstract data arises from a genuine structure.

An inequality, a cardinal coincidence, or a suggestive diagram is not a
replacement for this package.

A theorem that an object exists is not a theorem that it is observable.

A theorem that a datum is invariant is not a theorem that it is complete.

______________________________________________________________________

# 19. Theorem packages

Every substantial interface should accumulate a predictable API.

## For a map and its fibers

- extensionality and equality criteria;
- reached and missed values;
- injective, surjective, and bijective fiber characterizations;
- transport under equivalences of source and target;
- behavior under composition;
- behavior under pullback or base change;
- decomposition of the source as a dependent sum of fibers;
- finite cardinality formulas when finiteness is present.

## For a compatibility object

- projections and their equality laws;
- universal map induced by a commuting square;
- equivalence under maps of the constituent diagram;
- behavior under trivial overlap;
- symmetry under exchange of local views;
- associativity or presentation invariance only when a family-level theorem
  justifies it.

## For an observable

- invariance under the intended system equivalence;
- exact characterization of equality of data;
- factorization to every claimed coarser observable;
- strictness witnesses;
- reconstruction and both round trips;
- minimality of a proposed complete subdatum.

## For a restriction system

- identity and composition laws;
- compatibility under reindexing;
- comparison maps for the supported local families;
- naturality under morphisms of systems;
- componentwise and coherent equivalence criteria;
- realizability of proposed abstract data.

No README claim should outrun these theorem packages.

______________________________________________________________________

# 20. Falsify first

Finite reconnaissance is encouraged when its purpose is to kill a conjecture
cheaply or locate the smallest strict witness.

For an expensive universal claim:

1. identify the smallest nontrivial source, target, and diagram shape;
2. quotient the search by relabeling symmetries;
3. separate fixed-base from varying-base equivalence;
4. enumerate adversarial maps, not only balanced or injective examples;
5. search independently for failures of existence and uniqueness;
6. record the exact datum shared by a counterexample pair;
7. turn the result into a certified finite theorem before using it in prose.

Computational isomorphism tests must be validated by proved invariants or
explicit equivalences. A successful bounded search is not a universal proof.

If a conjecture fails, formalize the failure and change the ontology or
question. Do not weaken the meaning of the original claim while retaining its
name.

______________________________________________________________________

# 21. Formal architecture

The repository should enforce dependency direction.

A tentative initial architecture is:

```text
Amalgam/
  Core/
    Fiber.lean
    Comparison.lean
    Equivalence.lean
    Reduction.lean

  Finite/
    Profile.lean
    Reconstruction.lean
    Joint.lean

  System/
    Restriction.lean
    Compatibility.lean
    Reduction.lean
    Reconstruction.lean
    Realizable.lean

  Models/
    Fork.lean
    Overlap.lean

  Bridge/
    Descent.lean

  Status.lean
```

This is a starting hypothesis, not a directory quota.

`Core` must not import finiteness, arithmetic summaries, concrete models, or
bridges.

`Finite` may import `Core` and add `Fintype`, decidable equality, cardinality,
and explicit reconstruction.

`System` should appear only after multiple comparison theorems consume shared
restriction laws.

`Bridge` is downstream of both projects' independently meaningful interfaces.

Files should split or migrate when theorem dependencies reveal a smaller
structure. The import graph is part of the mathematical model.

Avoid duplicate elementary objects when mathlib already supplies the needed
fiber, pullback, equivalence, or finite-cardinality interface. A project-local
wrapper must improve theorem statements enough to justify itself.

______________________________________________________________________

# 22. Mathlib-quality naming and documentation

The code should read like a small downstream mathlib library.

- Files use `UpperCamelCase`.
- Types, structures, classes, and propositions use `UpperCamelCase`.
- Functions and data use `lowerCamelCase`.
- Theorems use `snake_case`.
- Prefer established American-English mathematical terminology.
- Theorem names describe formal content, not project history or motivation.
- Avoid abbreviations unless they are standard and genuinely improve use.

Use `amalgam` as the Lake package name and `Amalgam` as the root library and
namespace. Definitions intended for eventual upstreaming should nevertheless
use the mathematical namespace
their subject requires inside the project, rather than accumulating under one
flat branded namespace.

Docstrings should state the object's mathematical role, hypotheses,
convention, or non-obvious implementation choice tersely. They should not
contain submission history, philosophical motivation, reviewer dialogue, or
claims that are not encoded by declarations.

The README describes the repository as it exists. It is not a progress log.

The proposal carries the research contract and is curated when theorems revise
the ontology.

Reservoir readiness should be structural from the first commit: a root
`lake-manifest.json`, a public mathlib dependency, an OSI-approved license, and
no private dependency required to build the Lean library. Package metadata
should use the descriptive subtitle of this proposal rather than a placeholder.

______________________________________________________________________

# 23. Build truth, not conversational truth

Anything important that exists only in an agent's signoff will be lost.

From the first mathematical milestone, create `Amalgam/Status.lean`. Every
load-bearing factual claim in the README should be restated there as a typed
`example` with an explicit type.

The root `Amalgam.lean` aggregator should import the status manifest so that
every full build checks it. No library module imports `Status.lean`.

When a milestone changes the conceptual picture:

1. encode the mathematical fact as a theorem;
2. record the architectural consequence in a module docstring if it affects
   the API;
3. update the README's current description;
4. update the relevant proposal status and future direction;
5. add typed Status examples for new factual README claims;
6. remove superseded prospective language.

After a milestone is accepted, its proposal section gains a concise built-status
paragraph naming the implementing modules, closing theorems, strict witness or
collapse theorem, and remaining central question. The roadmap must describe the
mathematics now in the repository, not preserve the chronology of the plan.

Submission prose does not satisfy any of these requirements.

Milestone reports should name the exact theorem, module, assumptions, strict
witness, and verification performed. They must not be the only location where
a design decision or open question is recorded.

No accepted milestone contains `sorry` or a new project axiom. Use of standard
classical principles should be visible through ordinary Lean declarations,
not hidden behind an undocumented axiom. Every milestone finishes with a clean
working copy after `nix fmt`, `lake build`, and `nix flake check`.

A generic README statement requires a generic theorem and its exact typed
Status example. A concrete model corollary, a related inequality, or a nearby
valuation law cannot stand in for the asserted claim. Exact formulas and sharp
if-and-only-if statements should be mirrored at their stated strength.

______________________________________________________________________

# 24. The blank-slate agent protocol

This document must be sufficient initialization for an agent that has never
seen the earlier projects or the conversations that produced it.

### Rule 1 — Self-contained foundations

Do not assume knowledge of earlier repositories.

Introduce a definition when it is consumed by a stated theorem or
construction.

### Rule 2 — Start below the invariant

Do not begin from extension profiles, scalar defects, entropy, or another
summary. Begin from maps, compatibility, and fibers.

### Rule 3 — Abstract only after consumption

Implement the weakest structure currently needed. Do not begin with a general
category, site, sheaf, fibration, or higher object because the diagrams suggest
one.

When several theorems shed the same assumptions, migrate the shared structure
toward the root.

### Rule 4 — Search standard mathematics before defining it

Before introducing a generic fiber, pullback, equivalence, or amalgamation
interface, inspect mathlib. Reuse an established object when its theorem
statements are natural. Do not wrap it merely to make the repository look
self-contained.

### Rule 5 — The theorem statement is the design test

A good abstraction makes the desired theorem concise at its weakest natural
hypotheses. Remove structure fields that no theorem consumes.

### Rule 6 — Counterexamples outrank intentions

If the intended theorem is false, formalize the failure. Preserve the original
distinction rather than weakening a name until the theorem becomes true.

### Rule 7 — Every observable states its induced equivalence

Never introduce an observable without identifying what equality of its data
means. Reserve `kernel` for the appropriate formal setting; otherwise state
the kernel pair or equality relation.

### Rule 8 — Every refinement proves strictness or collapse

A proposed refinement must either have a strict witness showing that it
separates previously identified structures or a theorem proving that it adds
no information. Do not build indefinite layers while this is unknown.

### Rule 9 — Every inverse result names its datum and symmetry

State exactly what is supplied, what is fixed, what is reconstructed, and up
to which explicit equivalence. Distinguish fixed-base reconstruction from
whole-system reconstruction, and observable-content equivalence from coherent
presentation equivalence. A refinement must resolve a named uncertainty for
the chosen target.

### Rule 10 — Local equivalence is not coherent equivalence

Equivalences obtained independently for several maps do not form a system
equivalence until their commutation laws are proved.

### Rule 11 — Scalarization is downstream

Counts and scalar summaries are forgetting maps from extension structure.
Every use must state what is lost and when the summary is complete.

### Rule 12 — Application language stays local

Core names remain mathematical and application-neutral. Specialized language
belongs in the module defining the corresponding realization and is connected
to the core by a theorem.

### Rule 13 — Build truth, not prose truth

Important README claims compile through `Status.lean`. Important design
discoveries are committed to the repository before the milestone is accepted.

### Rule 14 — Generalize before growing an arity ladder

After two adjacent finite arities expose the same mechanism, seek the
family-level construction, recurrence, or saturation theorem. Do not create
`Profile4`, `Profile5`, or analogous layers by momentum.

### Rule 15 — A milestone has one research target

Do not present unrelated continuations as interchangeable choices. State the
strongest unresolved theorem forced by the current results. A milestone is
complete when that question is settled and encoded, whether the answer is
positive or negative.

### Rule 16 — General prose requires general theorems

Do not state a carrier-free, family-level, or unconditional result in the
README when the repository proves only a concrete, fixed-arity, or conditional
instance. First prove the advertised theorem, then derive the model result as
its corollary.

______________________________________________________________________

# 25. Policy for previous theorem libraries

Previous repositories are potential proof donors, not conceptual
dependencies.

The default rule is:

> **Do not import an old project merely to save work.**

The workflow for reuse is:

1. define the Amalgam object without consulting old names or narrative;
2. state the theorem wanted in Amalgam's vocabulary;
3. determine whether an old theorem has exactly the required content and
   hypotheses;
4. port or import the minimum proof and dependencies;
5. use current standard mathematical names;
6. record provenance outside the imported theorem graph when useful;
7. verify that the new object's meaning does not depend on the old project's
   interpretation.

The finite extension-profile reconstruction theorem is the first likely donor.
It should be treated as established mathematics that calibrates the new core,
not as evidence that the old architecture should be copied.

What should normally be rebuilt:

- foundational definitions;
- namespaces and module boundaries;
- equivalence notions;
- system interfaces;
- conceptual decompositions;
- application terminology.

What may be transplanted after convergence:

- generic finite-map fiber lemmas;
- finite cardinality identities;
- equivalence constructions between sigma types and fibers;
- explicit finite witnesses whose statements remain canonical;
- proof patterns matching the new hypotheses exactly.

______________________________________________________________________

# 26. Initial milestones

The milestones serve one reconstruction problem. M0 supplies the elementary
API, M1 calibrates reduction against compatibility, M2 develops the finite
family comparison, and M3--M4 settle its information boundary and realizability
for one chosen shape. Counts enter where these questions consume them.

## M0 — Maps, fibers, and binary compatibility

Create the Lean project and status manifest. Configure the Lake package
`amalgam`, the root library `Amalgam`, a pinned mathlib toolchain, and an
Apache-2.0 license. The README should state only the scope actually present.
Build `Amalgam/Status.lean` immediately.

Start with standard types, maps, and fibers. Package source decomposition,
transport under equivalences, and pointwise criteria for injectivity,
surjectivity, and bijectivity. Introduce the binary span, its compatible-pair
type, and the comparison from a candidate global source.

The closing theorem identifies comparison fibers with global extensions and
separates their exact existence and uniqueness conditions. Include projection
laws, transport of the span, trivial-overlap reduction, and the four finite
comparison behaviors. No counts or context hierarchy are required.

## M1 — When local reduction preserves compatibility

Use the binary setup of Section 10 with arbitrary types and commuting maps.
Prove the core statements without surjectivity, then specialize to objectwise
surjective reductions. Only the explicit witnesses require finite carriers.
The target is equality of attainable coarse compatible pairs; it does not
require recovery of fine multiplicities.

Construct `k : P → P'` and the induced injection `k_bar : Q → P'`.
Characterize the image of `k_bar` by the intersection of fine overlap values
available above each coarse pair. Prove that `k_bar` is an equivalence exactly when every
coarse compatible pair lifts, and give the inverse and both round trips under
that condition. Characterize the fibers of `k` separately.

Certify the singleton/two-point-overlap failure witness in Section 10.
The milestone closes with the necessary-and-sufficient lifting criterion,
not merely a sufficient condition such as injectivity of the overlap reduction.
Keep global extension through a supplied `G` separate from this local lifting.

## M2 — The comparison for finite families

Introduce the weakest restriction interface consumed by the binary result and
its extension to finite families with shared overlaps. Finiteness here concerns
the indexing families; state carriers remain arbitrary. Declare which families
are admissible and which restrictions between families are supplied.

For every admissible `F`, construct both maps from Section 12:

- `k_F : P_F → P'_F`, whose fiber over a coarse family is the type of its
  fine compatible lifts;
- `k_bar_F : Q_F → P'_F`, the injection from observed quotient classes, whose
  image is the attainable content `I_F` and whose fibers are subsingletons.

Prove naturality of both maps under the declared family restrictions, and
identify `Q_F` with `I_F`. Include binary reduction, presentation invariance,
and degeneration under redundant views as consequences. Prove the induced
restriction maps on images and the inclusion in Section 12; equality requires
an additional theorem.

Retain a calibration case with two fine compatible families mapping constantly
to one coarse family: the fiber of `k_F` has two elements, while the fiber of
`k_bar_F` has one observed class. The image-only target does not require
recovery of the first multiplicity. Also certify the Section 12 finite witness
separating full-family content from all admissible content.

Do not assert that binary surjectivity implies family surjectivity. That is
part of the next inverse problem. Do not build an arity-by-arity tower.

## M3 — The coherent information boundary

Use finite reconnaissance to select one explicit finite context shape with
shared overlaps. Then fix its admissible families, candidate realizations,
supplied local lifting or incidence datum, and target equivalence before the
classification work. The initial target is the entire collection of attainable
images `I_F`, with its restriction maps, as defined in Section 12. Any stronger
presentation target needs a named question that requires it. Explicitly list
which proper-family images the input datum already fixes and which remain to
be reconstructed.

The closing theorem classifies the equivalence on realizations induced by
the supplied datum and determines exactly whether it fixes that entire target
collection. Keep the full-family image as the distinguished joint question.
A full-image-only reconstruction theorem suffices only if a further theorem
shows that the full image together with the supplied datum determines every
remaining admissible image and its restriction maps.

If local data is insufficient, provide a strict finite pair with identical
supplied data and different target collections, and characterize the missing
compatibility information. Name the admissible family where the images differ.
Prove an exact criterion or a complete description of the remaining target
collections; an isolated counterexample alone does not close the classification.

Any proposed sufficient refinement must have a reconstruction theorem for the
declared target and an explicit witness for its claimed necessity. Preserve
unconstrained presentation freedom rather than silently changing the target
to coherent diagram isomorphism. Do not enlarge the context shape before
settling this question.

The finite-map profile theorem and marginal-blindness theorem of Sections 8--9
are supporting packages when the selected datum uses counts or joint incidence.
Their proofs should enter at the point of consumption. They are not separate
tracks or prerequisites for M1.

## M4 — Realizability and closure on the chosen shape

For exactly the shape, datum, and target fixed in M3, characterize which
abstract data arises from a coherent realization. Retain all admissible images
`I_F` with their restriction maps as the target; no substitution of just the
full-family image is allowed without the determination theorem required in M3.
Separate pointwise
realizability, overlap consistency, simultaneous realizability, and freedom
up to the target equivalence. Do not assume existence of a simultaneous global
assignment unless it belongs to the declared realization class.

The closing theorem gives necessary and sufficient realizability conditions
and the remaining possible target collections for realizable data. Every proper
condition needs
a strict incompatible datum; an unconditional realizability theorem discharges
that witness obligation. A constructor for positive examples alone is not a
classification.

Run the closure audit against M3's fixed reconstruction question. A sharp
negative classification can complete the program. Scalar shadows, larger
shapes, and stronger presentation invariants are follow-on work only when a
named unresolved question in that scope requires them.

______________________________________________________________________

# 27. Questions that should drive the project

The active question is when local reduction preserves constraints on joint
realization, and what supplied data determines the answer coherently. Q2--Q4
and Q6 support its classification on the chosen shape. The other questions
enter when that classification consumes them.

### Q1 — Single-observation reconstruction

For which classes of fibers does a fiber-valued or profile-valued datum
reconstruct a map over a fixed codomain, and up to which equivalence?

### Q2 — Marginal completeness

Which families of separate observations determine their joint incidence, and
what is the minimal joint datum when they do not?

### Q3 — Existence and uniqueness

Which coarse compatible families lift to fine compatible representatives,
and which fine families extend to a supplied global realization? What datum
determines existence and uniqueness at each step?

### Q4 — Coherent reconstruction

What local lifting or incidence data determines jointly attainable content
across shared overlaps? When the declared target is presentation equivalence,
when do reconstructed comparison equivalences assemble coherently?

### Q5 — Sparse observation

Which subfamilies of contexts or compatible-local configurations induce the
same observational equivalence as the complete extension datum?

### Q6 — Realizability

Which abstract families of extension fibers or cardinal profiles arise from a
single functorial restriction system?

### Q7 — Base change

How do extension fibers and their observables transform when the overlap,
local contexts, or indexing shape is refined or coarsened?

### Q8 — Symmetry

Which features, including multiplicity and automorphisms, can vary among
realizations with the same declared observable content? Which admissible
comparisons, if any, make those features detectable?

### Q9 — Scalarization

Which scalar summaries of extension structure are complete on restricted
classes, and what distinct combinations of nonexistence and nonuniqueness do
they identify in general?

### Q10 — Universality

Which theorems consume only maps and fibers, which require finite sets, which
require a restriction system, and which survive in richer target categories?

These questions are a research horizon, not a promise that every carrier-wide
classification must be exhausted before a coherent stopping point can be
recognized.

______________________________________________________________________

# 28. Success criteria

The project should not be judged by theorem count or abstraction depth.

It succeeds when the supplied observation datum has an exact information
boundary for the chosen realization class and target. The result must explain
both what every realization preserves and what can vary without changing the
declared content.

The principal evidence is:

- an exact comparison between reducing assembled descriptions and assembling
  reduced descriptions;
- a necessary-and-sufficient lifting criterion with a strict finite failure;
- a classification of the gap between local information and attainable images
  for all admissible families, with their restriction maps, on the chosen shape;
- a realizability boundary for the classified data;
- explicit witnesses justifying every claimed necessary refinement;
- a reconstruction theorem or sharp impossibility result naming its target
  equivalence and the residual freedom.

Finite profiles, sparse data, scalar factorizations, and migration to standard
interfaces are useful when they help settle these claims. They are not
additional completion requirements.

A theorem may force the project to enrich a datum, replace an abstraction, or
prove that a hidden distinction is unnecessary for the target. Let that result
control the architecture.

______________________________________________________________________

# 29. Failure criteria

The project should contract or change direction if:

- it merely repackages elementary finite-map counting without a coherent
  inverse problem;
- extension profiles are treated as fundamental after theorems expose richer
  fiber structure;
- the abstraction is only sheaf terminology restated without a new theorem;
- all reconstruction results require the complete original system as input;
- pointwise equivalences are called coherent without commutation proofs;
- an indefinite hierarchy of joint arities grows without strictness or
  saturation results;
- category-theoretic infrastructure dominates before elementary finite
  examples reveal what it buys;
- scalar or probabilistic interpretations outrun the maps that produce them;
- proposed observables accumulate without exact induced equivalence
  relations;
- refinements distinguish more presentations without resolving a question for
  the declared target;
- local reduction is called lossless without checking admissible joint
  comparisons;
- the target changes whenever a negative result or a stronger invariant appears;
- concrete models provide illustrations but no theorem unavailable at the
  abstract level.

A failed conjecture is acceptable.

An observable with an unnamed information boundary is not.

______________________________________________________________________

# 30. Milestone and review discipline

Milestones are binary research claims, not bundles of loosely related work.

Before implementation, each milestone should identify:

- its single central theorem or classification;
- the exact datum consumed;
- the intended residual equivalence and admissible comparisons;
- the strict witness required, with minimality only if claimed;
- the assumptions whose necessity is still uncertain.

At submission, every mathematical claim in the report must already exist as a
committed theorem or definition. Every claimed architectural consequence must
be recorded in the current module documentation, README, or proposal. Every
load-bearing factual README statement must have its committed typed Status
example. Every remaining research claim must be recorded explicitly as open.

A submission summary is an index into committed work. It is not documentation.

Reviews should decide whether the milestone is hit. If it is not, the response
should name the theorem-level gap. If it is, the proposal should identify the
next unresolved obligation within the declared scope, or record its closure.

Do not present unrelated future directions as interchangeable choices. When a
result changes the ontology, rewrite the roadmap around the stronger question.

______________________________________________________________________

# 31. Stopping and completion

The project is not complete merely because every planned file exists.

It reaches a legitimate stopping point when:

1. the observation datum, admissible comparisons, realization class, and target
   equivalence are fixed and recorded;
2. the equivalence on realizations induced by that datum is classified exactly;
3. the gap between local information and the entire target collection of
   admissible images `I_F`, with its restriction maps, is settled for the chosen
   shape by a positive theorem or sharp obstruction; a full-image-only result
   includes a theorem that the supplied datum and full image determine the
   remaining admissible images;
4. the chosen realizability problem has a necessary-and-sufficient boundary,
   with the residual freedom characterized;
5. every claimed necessary refinement has an explicit strict witness, and
   every constructive reconstruction has its round-trip laws;
6. a closure audit finds no load-bearing prose claim without a theorem.

A negative classification can discharge these obligations. Reconstruction of
observable content need not recover a unique presentation. Further distinctions
or larger shapes do not automatically reopen a completed question, even when
they use the same primitives.

The closure audit also checks the public surface: root imports are explicit,
module dependencies do not rely accidentally on transitive imports, assumptions
are no stronger than theorem statements require, names and docstrings describe
current mathematics, and no status or proposal prose overstates the compiled API.

Before declaring closure, perform one adversarial pass:

- list the obligations of the fixed reconstruction question and their theorems;
- identify any unresolved native theorem on which the classification depends;
- separate those gaps from stronger targets, larger shapes, or new observables;
- record the remaining research horizon without treating it as theorem debt.

If an obligation of the declared classification remains open, pursue it.
Otherwise close that scope explicitly. A subsequent program must state what
new question it asks; the existence of a plausible next theorem is not itself
an objection to completion.

______________________________________________________________________

# 32. Compact thesis

The proposal can be compressed to five claims.

### I. Observation is identification

An observation is a map. Its fibers are the distinctions it forgets.

### II. Compatibility is not globalization

Local descriptions may agree on every overlap without arising from any global
state.

### III. Existence and uniqueness are independent

A comparison map may miss compatible families, identify global states, or do
both. A scalar summary can conflate these failures.

### IV. An observable is defined by its information boundary

Every datum induces an equivalence relation. A refinement earns its place by
settling a named uncertainty for the declared reconstruction target.

### V. Reconstruction has a declared endpoint

Classify exactly what the supplied datum determines, up to its named target
equivalence, and what freedom remains. A sharp obstruction can finish the
question; recovering more of a presentation need not advance it.

______________________________________________________________________

# 33. North star

> **What does a system of partial observations, with its admissible
> comparisons, determine about its possible global realizations?**

The first concrete test is:

> **When can local descriptions be reduced to their observed content without
> losing constraints on their joint realization?**

Fix the datum and target. Reconstruct what they determine. Characterize the
freedom they leave. Stop when that question is settled.
