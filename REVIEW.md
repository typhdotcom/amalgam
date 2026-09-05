State: COMPLETE
Turn: none
Candidate: 24078ce2; submission fb55f9eb

# Final acceptance

M4 is accepted at `24078ce2`. Both returned drawers are closed. The declared
reconstruction and realizability scope on the fixed zigzag is complete.
No worker action remains.

[PROPOSAL.md](PROPOSAL.md), Sections 11–14 and 26, owns the fixed contract;
Section 31 records the final obligation-to-theorem map and the boundary of
completion. The public mathematical account is in [README.md](README.md),
with typed evidence in `Amalgam/Status.lean` imported by the root aggregator.

# Completed result

For a fixed arbitrary coarse restriction system on `L → B ← M → D ← R`,
candidates have commuting, objectwise surjective observations. The datum is
the pair of adjacent attainable images. The target consists of the images on
all eight subfamilies of `L, M, R`, with maps induced by the fixed coarse
restrictions. Fine carriers may vary and need not be finite or nonempty.

The five empty/singleton/outer-pair entries are full. At adjacent datum
`(A, A')`, the remaining targets are exactly `Target.ofDatum A A' T` for
`T ⊆ join A A'`. Every such target has an actual coherent realization.
Consequently the datum determines the target exactly when the join is empty.
The existential constructions use the coarse universe; necessity and the
packaged forward direction apply at arbitrary fine universes.

M4's six explicit incompatible targets prove that none of the six
realizability conditions is implied by the others. Each has its violated
condition, the other-five conjunction, and nonrealizability certified through
`realizable_target_iff`. A positive control and `exists_candidate_datum`
record that the adjacent datum itself has no further realizability condition.
The strict split/glue pair and singleton-middle collapse explain the missing
fine-middle compatibility; a second pair has equal targets and inequivalent
middle carriers, certifying the limit of fine-presentation recovery.

# Closure of the returned round

- R1: the six missing direct imports are present. An independent scan of
  elaborated types and values, resolving referenced project constants to
  their defining modules and comparing with source imports, found zero
  missing project dependency edges across all 1132 selected constants.
- R2: the unqualified size claim is gone from README and the module overview;
  the join docstring correctly distinguishes actual nonmembership from the
  membership forced by the contradictory hypothesis; the split/glue
  surjectivity paragraph and the presentation witness are separate; the
  process label is removed. The two additionally cited witness results have
  exact typed Status examples.

The reviewed mathematics from `a1957c29` is unchanged. No theorem gap or
remaining correction was found in the declared scope.

# Independent verification

- `nix develop -c lake build`: success, 726 jobs, zero Lean warnings,
  including the two new Status examples.
- Formatting and all seven flake checks pass on the final acceptance handoff.
- No `sorry` or project axiom declarations found in `Amalgam/`.
- Unfiltered defining-module axiom audit: 1132 constants, including 232
  internal names. Counts: 371 axiom-free; 356 using only `propext`; 130 using
  only `Quot.sound`; 229 using both; 46 also using `Classical.choice`.
  No other axiom occurs. This exactly matches the prior independent audit.
- Selection: `Core.Fiber`, `Core.Comparison`, `Core.Reduction`,
  `System.Restriction`, `System.Presentation`, `System.Comparison`,
  `System.Binary`, `System.Zigzag`, `System.ZigzagTarget`,
  `System.ZigzagRealization`, `System.ZigzagClassification`, `Models.Overlap`,
  `Models.Lifting`, `Models.Span`, `Models.Zigzag`, `Models.MiddleSplit`, and
  `Models.Incompatible`, all under `Amalgam`; root and Status excluded.
- The same selection was used for the direct project dependency scan.
  Mathlib transitive dependencies are outside that scan's claim. The
  disposable combined audit script was removed after verification.
- The unchanged finite sweep retains the independently reproduced 872
  systems at bound 2 and 1,554,228 at bound 3. Those results are bounded
  reconnaissance, not a minimality proof or a substitute for classification.

# Accepted foundation

Founding proposal `7159fd31`; M0 `6a33636f`; M1 `d7f2ed62`; M2 `0950158f`;
M3 `08c41b29`; M4 `24078ce2`. Review history remains in version control.

# Scope boundary

No native theorem remains open for the declared question. Larger shapes,
stronger fine-presentation targets, new observables, scalar profiles, and a
descent bridge are possible subsequent programs requiring a new declared
question. They do not reopen this completed scope automatically.
