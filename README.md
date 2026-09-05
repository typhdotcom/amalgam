# amalgam

Amalgam is a Lean 4 library studying what partial observations and their
admissible comparisons determine about possible global realizations.

The repository currently holds the Lake package only: the pinned toolchain and
mathlib revision, the root `Amalgam` aggregator, and `Amalgam/Status.lean`, the
status manifest that restates every load-bearing mathematical README claim as a
typed example. No mathematical modules exist yet, so the manifest is empty.

[PROPOSAL.md](PROPOSAL.md) defines the mathematical scope, roadmap, and
completion criteria.

## Building

The Nix devshell supplies `elan`, which provides the `lake` and `lean` proxies
for the toolchain named in `lean-toolchain`.

```nushell
nix develop
lake build
```

`nu tasks.nu` lists the shorthands for building, formatting, and running the
flake checks.
