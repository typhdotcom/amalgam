import Mathlib.Logic.Equiv.Defs

/-!
# Status manifest

Every load-bearing mathematical claim `README.md` makes is restated here as an
`example` with an explicit type. Renaming, weakening, or deleting a result
breaks this file, which is what makes stale prose detectable.

No library module imports this file; only the root `Amalgam` aggregator does,
so the manifest compiles with every build.

The library has no mathematical content yet, so there is nothing to mirror.
The `Mathlib` import keeps the pinned dependency on the build path, so a plain
`lake build` still exercises the toolchain and mathlib revision the package
declares.
-/

namespace Amalgam.Status

end Amalgam.Status
