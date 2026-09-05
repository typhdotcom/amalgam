# /// script
# requires-python = ">=3.14"
# dependencies = []
# ///
"""Bounded finite reconnaissance for the zigzag M3 conjecture.

Shape: the five-point preorder ``B <= L``, ``B <= M``, ``D <= M``, ``D <= R``,
drawn as ``L -> B <- M -> D <- R`` (arrows are the restriction maps).

A fine restriction system is five nonempty finite state sets and the four
restriction functions.  Every coarse state set is a singleton, so each coarse
compatible-family type is a singleton, the unique observation maps are
surjective, and the attained image ``I_F`` of a family ``F`` degenerates to the
boolean "some compatible fine family over ``F`` exists".

Under that degeneration the coarse join is ``J(A_LM, A_MR) = A_LM and A_MR``,
so the conjecture reads ``I_LMR <= min(I_LM, I_MR)`` together with the claim
that every triple obeying that bound is realized.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from itertools import product

Fn = tuple[int, ...]
Triple = tuple[bool, bool, bool]

# Triples permitted by the conjecture: I_LMR implies both binary images.
ALLOWED: frozenset[Triple] = frozenset(
    (lm, mr, lmr)
    for lm in (False, True)
    for mr in (False, True)
    for lmr in (False, True)
    if not lmr or (lm and mr)
)


@dataclass(frozen=True)
class System:
    """A fine restriction system over the zigzag shape."""

    sizes: tuple[int, int, int, int, int]
    r_lb: Fn
    r_mb: Fn
    r_md: Fn
    r_rd: Fn

    @property
    def total(self) -> int:
        return sum(self.sizes)

    def carriers(self) -> str:
        names = ("L", "B", "M", "D", "R")
        letters = ("l", "b", "m", "d", "r")
        parts = [
            f"S_{name}={{{', '.join(f'{letter}{i}' for i in range(n))}}}"
            for name, letter, n in zip(names, letters, self.sizes, strict=True)
        ]
        return "  ".join(parts)

    def maps(self) -> str:
        specs = (
            ("r_LB", "l", "b", self.r_lb),
            ("r_MB", "m", "b", self.r_mb),
            ("r_MD", "m", "d", self.r_md),
            ("r_RD", "r", "d", self.r_rd),
        )
        parts = [
            f"{label}: " + " ".join(f"{src}{i}->{dst}{v}" for i, v in enumerate(fn))
            for label, src, dst, fn in specs
        ]
        return " | ".join(parts)


def attained(system: System) -> Triple:
    """Return ``(I_LM, I_MR, I_LMR)`` as booleans."""
    n_l, _, n_m, _, n_r = system.sizes
    lm = any(
        system.r_lb[left] == system.r_mb[mid]
        for left in range(n_l)
        for mid in range(n_m)
    )
    mr = any(
        system.r_md[mid] == system.r_rd[right]
        for mid in range(n_m)
        for right in range(n_r)
    )
    lmr = any(
        system.r_lb[left] == system.r_mb[mid] and system.r_md[mid] == system.r_rd[right]
        for left in range(n_l)
        for mid in range(n_m)
        for right in range(n_r)
    )
    return lm, mr, lmr


def systems(max_size: int, min_size: int = 1):
    """Enumerate every fine system within the bound, smallest total first."""
    shapes = sorted(
        product(range(min_size, max_size + 1), repeat=5),
        key=lambda s: (sum(s), s),
    )
    for sizes in shapes:
        n_l, n_b, n_m, n_d, n_r = sizes
        for r_lb in product(range(n_b), repeat=n_l):
            for r_mb in product(range(n_b), repeat=n_m):
                for r_md in product(range(n_d), repeat=n_m):
                    for r_rd in product(range(n_d), repeat=n_r):
                        yield System(sizes, r_lb, r_mb, r_md, r_rd)


@dataclass
class Sweep:
    count: int
    witness: dict[Triple, System]
    min_mid: dict[Triple, int]


def sweep(max_size: int) -> Sweep:
    count = 0
    witness: dict[Triple, System] = {}
    min_mid: dict[Triple, int] = {}
    for system in systems(max_size):
        count += 1
        triple = attained(system)
        if triple not in witness:
            witness[triple] = system
        mid = system.sizes[2]
        if mid < min_mid.get(triple, mid + 1):
            min_mid[triple] = mid
    return Sweep(count, witness, min_mid)


def show(label: str, triple: Triple, system: System) -> None:
    flags = "".join("1" if b else "0" for b in triple)
    print(
        f"  {label}: (I_LM,I_MR,I_LMR) = ({flags[0]},{flags[1]},{flags[2]}), "
        f"total states {system.total}"
    )
    print(f"       {system.carriers()}")
    print(f"       {system.maps()}")


def report(max_size: int) -> None:
    result = sweep(max_size)
    realized = sorted(result.witness, reverse=True)

    print("zigzag M3 finite sweep")
    print("  shape L -> B <- M -> D <- R; coarse objects all singletons, so every")
    print("  coarse family type is a singleton and observations are surjective")
    print(f"  size bound: 1 <= |S_X| <= {max_size} for X in L, B, M, D, R")
    print(f"  fine systems enumerated: {result.count}")

    print("realized (I_LM, I_MR, I_LMR), with the smallest realizing system:")
    for triple in realized:
        flags = ",".join("1" if b else "0" for b in triple)
        note = "" if triple in ALLOWED else "   <-- VIOLATES the conjecture"
        print(
            f"  ({flags})  min total states {result.witness[triple].total}, "
            f"min |S_M| {result.min_mid[triple]}{note}"
        )

    bad = [t for t in realized if t not in ALLOWED]
    verdict = "HOLDS" if not bad else f"FAILS on {bad}"
    print(
        f"necessary condition I_LMR <= min(I_LM, I_MR): {verdict} "
        f"on all {result.count} systems"
    )
    missing = sorted(ALLOWED - set(realized), reverse=True)
    print(
        f"converse within the bound: {len(ALLOWED) - len(missing)}/{len(ALLOWED)} "
        f"conjecture-allowed triples realized"
        + (f", missing {missing}" if missing else "")
    )

    full = (True, True, True)
    strict = (True, True, False)
    if full in result.witness and strict in result.witness:
        print("smallest witness pair, equal supplied datum I_LM = I_MR = 1:")
        show("A", full, result.witness[full])
        show("B", strict, result.witness[strict])
        print(
            f"  pair separates I_LMR while sharing (I_LM, I_MR); "
            f"minimal |S_M| for (1,1,0) is {result.min_mid[strict]}"
        )
        print("  |S_M| = 1 cannot give (1,1,0): the single middle state m carries")
        print("  both lifts, so l with r_LB l = r_MB m and r with r_MD m = r_RD r")
        print("  assemble into the triple (l, m, r), forcing I_LMR = 1")
    else:
        print("smallest witness pair: not available at this bound")

    empties = sum(1 for shape in product(range(max_size + 1), repeat=5) if 0 in shape)
    print(f"remark: {empties} size shapes in 0..{max_size} have an empty carrier; all")
    print("  are excluded, since no map from an empty set is onto a singleton coarse")
    print("  state, so the observation surjectivity hypothesis fails there")
    print("limits: bounded carrier sizes and singleton coarse objects only, so every")
    print("  I_F is a boolean and no coarse family type has two elements; this sweep")
    print("  can refute or guide, it cannot prove the universal law")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument(
        "--max-size",
        type=int,
        default=2,
        help="largest fine carrier size to enumerate (default: 2)",
    )
    args = parser.parse_args()
    if args.max_size < 1:
        parser.error("--max-size must be at least 1")
    report(args.max_size)


if __name__ == "__main__":
    main()
