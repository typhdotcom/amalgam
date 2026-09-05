State: READY FOR REVIEW
Turn: reviewer
Candidate: 24078ce2; previous candidate a1957c29; accepted M3 candidate 08c41b29

# Submission

Both drawers of the returned round are closed at `24078ce2`. The completed
M4 mathematics is preserved: no theorem statement or proof changed. The
candidate adds six direct imports, four prose corrections, and two Status
mirrors for witness names the corrected README paragraph now cites.

# Accepted foundation

[PROPOSAL.md](PROPOSAL.md), Sections 11–14, 26, and 31, owns this contract.
M0 `6a33636f`, M1 `d7f2ed62`, M2 `0950158f`, M3 `08c41b29`; the M4
mathematics and obligation map inspected at `a1957c29` stand unchanged.

# Closing evidence

## R1 — Project dependency audit finished

Direct imports added exactly as listed: `Models/MiddleSplit` gains
`System.ZigzagRealization`; `Models/Incompatible` gains
`System.Comparison`, `System.Restriction`, `System.Zigzag`,
`System.ZigzagRealization`, `System.ZigzagTarget` (lists sorted). The scan
was then rerun on the resulting tree with the reviewer's selection: a Lean
script over `env.constants` restricted to constants defined in the
seventeen `Amalgam.*` library modules (root and Status excluded), collecting
every constant referenced in each elaborated type and value, resolving it to
its defining module, and comparing against the consumer module's direct
imports, ignoring mathlib. Result on the candidate:

```text
constants scanned: 1132
missing direct project imports: 0
```

## R2 — Public descriptions corrected

1. The size claim "as small as the shape allows" is deleted from README's
   "Strict incompatible targets" paragraph and from the
   `Models/Incompatible.lean` overview; the concrete all-singleton description
   is retained. No probe, model, or minimality theorem was added.
2. The docstring of `noJoin_lmr_not_subset_join` now says the restriction of
   `y₀` along `toLM` is not in the empty `LM` entry, whereas the hypothesized
   inclusion would force it there. The proof is unchanged.
3. README's strict-pair paragraph keeps `split`/`glue` together with the
   surjectivity claims that concern them; the presentation witness
   `exists_target_eq_not_nonempty_equiv` (`glueCandidate` versus the tagged
   realization of `(univ, univ, univ)`) is a separate following paragraph
   citing `target_realizeCandidate_eq_target_glue` and
   `not_subsingleton_realize_state_M`, which now have typed Status examples.
4. The module title of `Models/Incompatible.lean` no longer carries the
   `M4.1` label; `rg "M4\.1"` over README and `Amalgam/` returns nothing.

# Verification

- `nix fmt`: no changes. `nix develop -c lake build`: `Build completed successfully (726 jobs)`, zero warnings. `nix flake check`: all checks
  passed. `rg "sorry|^axiom" Amalgam`: none. No source line exceeds 100
  characters. Working copy clean after the commit.
- Axiom audit rerun on the candidate with the same unfiltered seventeen-module
  selection: 1132 constants, 232 internal; 371 no axioms, 356 `propext`,
  130 `Quot.sound`, 229 `propext, Quot.sound`, 46 with `Classical.choice`;
  unchanged from `a1957c29`, as expected since only imports and prose
  changed. No `sorryAx` or other axiom.

# Request to the reviewer

Confirm the dependency scan result and the four corrected descriptions against
their formulas and witnesses, then decide whether to close the declared scope
per Section 31.

# Prior acceptance evidence

M3 was accepted at `08c41b29` (submission `b88d4986`); M2 at `0950158f`;
M1 at `d7f2ed62`; M0 at `6a33636f`; the founding proposal at `7159fd31`.
