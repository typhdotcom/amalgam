State: READY FOR WORK
Turn: worker
Candidate: —; accepted M0 candidate 6a33636f, submission 89c090ae

# Verdict and active objective

M0 is accepted without remaining corrections. R1–R2 are closed. Its durable
built status and closing theorem names are recorded in
[the proposal's M0 section](PROPOSAL.md#26-initial-milestones).

The active objective is **M1 — When local reduction preserves compatibility**.
Determine exactly which compatible coarse pairs come from compatible fine
pairs. The closing result must identify the attainable image by an actual
common fine overlap value and characterize when the quotient of fine pairs
by observed equality is equivalent to all coarse compatible pairs.

This is a local lifting question. It does not assert extension to a separately
supplied global realization or recover hidden fine multiplicities from
observed classes.

# Accepted foundation

[PROPOSAL.md](PROPOSAL.md), especially Sections 10 and 26, owns this contract.

- Keep ordinary maps on arbitrary carriers, allowing empty types. Commutation
  alone supports the core constructions and image criterion. Objectwise
  surjectivity specializes them to reductions; finiteness supplies witnesses.
- Reuse the accepted generic fiber API and mathlib's `Function.Pullback`.
  Inspect `Function.mapPullback` and standard quotient/image constructions
  before introducing alternatives. Any wrapper must improve the statements.
- Preserve the distinction between the raw comparison's fine-lift fibers and
  the quotient injection's subsingleton fibers.
- The later target remains all admissible attainable images with their
  restriction maps. Finite-family indexing, M3's shape selection, profiles,
  and the Descent bridge remain outside this round.
- Keep the pinned toolchain, license, root exports, Status discipline, and
  development tasks. The Apache appendix placeholders are resolved and stay
  unchanged. `nu tasks.nu cache` is implemented and verified.

# Datum and target

Fix spans `L ─p→ B ←q─ R` and `L' ─p'→ B' ←q'─ R'`, with maps
`a : L → L'`, `b : B → B'`, and `c : R → R'` satisfying
`p' ∘ a = b ∘ p` and `q' ∘ c = b ∘ q`.

Write `P = Function.Pullback p q` and `P' = Function.Pullback p' q'`.
The raw map `k : P → P'` sends a fine compatible pair to its two observed
components. On `P`, declare two pairs equivalent exactly when both observed
components agree. Let `Q` be the quotient and `k_bar : Q → P'` its induced
map. The base `P'` and its labels are fixed. The target is equality of the
attainable coarse content with all of `P'`, not recovery of fine pairs.

# Current work and closing evidence

## M1.1 — Canonical comparison and observed quotient

Construct `k`, the observed-equality quotient, and `k_bar`. Prove the
projection and factorization laws, injectivity of `k_bar`, and equality of
the two maps' images. Identify `Q` with their common image using a named
equivalence with its round-trip laws. Do not assume injectivity or define
the quotient using any finer relation than agreement of observed components.

**Evidence:** declarations at arbitrary independent universes, with no
finiteness, decidability, or surjectivity hypotheses in these statements.
The quotient relation is proved equivalent to equality under `k`.
The API uses the accepted pullback/fiber constructions and standard quotient
machinery rather than duplicating them.

## M1.2 — Exact lifting criterion and inverse

For each coarse compatible pair `t = (u,v)`, prove equivalence between its
membership in the attainable image and:

```text
{p(l) | a(l) = u} ∩ {q(r) | c(r) = v} ≠ ∅.
```

Identify the fiber of `k` over `t` with fine pairs satisfying all three
conditions: fine compatibility, left observation `u`, and right observation
`v`. Use the fiber API to separate existence and uniqueness of fine lifts.

Prove that `k_bar` is bijective exactly when the displayed intersection is
nonempty for every coarse compatible pair. Under that condition expose the
equivalence or named inverse on all of `P'`, both round-trip laws, and
uniqueness of the inverse. The unique observed class must not be presented as
a preferred fine representative or as unique fine lifting.

**Evidence:** exact if-and-only-if statements at the generality of M1.1.
A sufficient special case such as injectivity of `b` does not close this
drawer. Status mirrors the image criterion, raw fiber identification, and
inverse laws with explicit types. Any use of classical choice is visible;
no computability claim follows merely from existence of the quotient inverse.

## M1.3 — Surjective reductions and a strict finite failure

Specialize the general setup to objectwise surjective observation maps, as
required for reductions onto the coarse objects. State how arbitrary
observations restrict to their images with induced commuting span maps,
using existing image machinery where applicable.

Certify the prescribed finite witness: `L` and `R` are singletons,
`B = {0,1}`, and their fine restrictions are the distinct overlap values.
All coarse objects are singletons and all observation maps are surjective.
The fine pullback is empty, the coarse pullback is a singleton, and its pair
is not in the image of `k` or `k_bar`. Show the overlap-value intersection
is empty through the actual M1 API. Do not claim minimality.

**Evidence:** named finite data, commutation and surjectivity proofs, the
unattainable coarse pair, and failure of the exact lifting criterion. Keep
these finite imports in the model layer. M0's four behaviors remain valid.

# Verification and submission

Update the root exports and concise module documentation for the new API.
Keep the README about compiled mathematics and mirror new mathematical claims
with explicitly typed `Amalgam/Status.lean` examples. Preserve the dependency
direction: generic fiber facts are consumed by comparisons and reduction;
finite witnesses stay downstream.

Run `nix fmt`, `lake build`, and `nix flake check`. Inspect the closing
declarations and their axioms, excluding `sorry` and new project axioms.
The next reviewer must inspect the quotient relation, image criterion,
inverse laws, and finite failure on the production path, as well as the
cumulative M0 evidence.

Work from this file and perform M1. Commit the candidate and rewrite
`REVIEW.md` as `READY FOR REVIEW`, `Turn: reviewer`, with the exact
committed candidate and evidence for M1.1–M1.3. Merely replying in chat is
not a submission. Do not advance to M2 before the M1 verdict.

# M0 acceptance evidence

The revised comparison criteria directly use the generic fiber criteria;
comparison-fiber transport uses `Equiv.fiberCongr` and the existing naturality
law. Precomposition specializes mathlib's `Equiv.subtypeEquivOfSubtype`.
Public statement strength and the computation laws are preserved; Status
and the four concrete witnesses are unchanged.

The reviewer reran the full build successfully (697 jobs, no warnings) and
the repository checks. A disposable Lean audit of the 12 changed or dependent
declarations reproduced the submitted axiom report: the three global fiber
criteria use no axioms; the transport and precomposition declarations use
only `propext` and `Quot.sound`. Independent `simp` probes confirmed both
precomposition computation laws.

The reviewer invoked the task listing and `nix develop -c nu tasks.nu cache`.
The task was listed and succeeded against the populated pinned cache,
reporting no files to download and 8690 already decompressed files.
Round-specific corrections remain in version history.
