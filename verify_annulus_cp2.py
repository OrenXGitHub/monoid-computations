#!/usr/bin/env python3
"""Exact finite checks used in the proof that B(M_122) is CP^2.

This file does not try to identify a homotopy type from finitely many
cohomology groups.  Instead it verifies the finite input to the proof in
ANNULUS_CP2_PROOF.md:

* the two-object category D and its retract structure;
* the finite simplicial annulus/circle diagram P through degree two;
* the frame and retract-generator hypotheses;
* equality of the resulting endomorphism monoid with the table constructed
  by annulus_cp2.py;
* the deck-transformation cocycle omega; and
* an explicit integral 2-cycle on which omega evaluates to -1.

The deductions from these checks to B(M_122) ~= CP^2 use standard results on
classifying spaces of categories, homotopy colimits, and oriented circle
bundles.  They are written out in ANNULUS_CP2_PROOF.md.
"""

from __future__ import annotations

from collections import Counter
from dataclasses import dataclass
from itertools import combinations_with_replacement

import annulus_cp2


A = "a"
B = "b"


@dataclass(frozen=True, order=True)
class Arrow:
    name: str
    source: str
    target: str


def arrows() -> tuple[Arrow, ...]:
    result = [Arrow("1a", A, A)]
    result.extend(Arrow(f"x{k}{j}", A, A) for k in range(2) for j in range(2))
    result.append(Arrow("1b", B, B))
    result.extend(Arrow(f"r{j}", A, B) for j in range(2))
    result.extend(Arrow(f"i{k}", B, A) for k in range(2))
    return tuple(result)


D = arrows()
BY_NAME = {arrow.name: arrow for arrow in D}


def compose(left: Arrow, right: Arrow) -> Arrow:
    """Return left after right."""
    if right.target != left.source:
        raise ValueError("arrows are not composable")
    if left.name in {"1a", "1b"}:
        return right
    if right.name in {"1a", "1b"}:
        return left
    if left.name.startswith("x") and right.name.startswith("x"):
        return BY_NAME[f"x{left.name[1]}{right.name[2]}"]
    if left.name.startswith("r") and right.name.startswith("i"):
        return BY_NAME["1b"]
    if left.name.startswith("i") and right.name.startswith("r"):
        return BY_NAME[f"x{left.name[1]}{right.name[1]}"]
    if left.name.startswith("x") and right.name.startswith("i"):
        return BY_NAME[f"i{left.name[1]}"]
    if left.name.startswith("r") and right.name.startswith("x"):
        return BY_NAME[f"r{right.name[2]}"]
    raise AssertionError((left, right))


def composable_pairs() -> tuple[tuple[Arrow, Arrow], ...]:
    return tuple((f, g) for f in D for g in D if g.target == f.source)


def composable_triples() -> tuple[tuple[Arrow, Arrow, Arrow], ...]:
    return tuple(
        (f, g, h)
        for f in D
        for g in D
        for h in D
        if h.target == g.source and g.target == f.source
    )


def verify_category() -> None:
    for arrow in D:
        identity_source = BY_NAME[f"1{arrow.source}"]
        identity_target = BY_NAME[f"1{arrow.target}"]
        assert compose(identity_target, arrow) == arrow
        assert compose(arrow, identity_source) == arrow
    for f, g, h in composable_triples():
        assert compose(compose(f, g), h) == compose(f, compose(g, h))

    # The second object is a retract of the first.
    assert compose(BY_NAME["r0"], BY_NAME["i0"]) == BY_NAME["1b"]
    assert {arrow.name for arrow in D if arrow.source == A and arrow.target == A} == {
        "1a",
        "x00",
        "x01",
        "x10",
        "x11",
    }


def monotone_maps(source_dimension: int, target_dimension: int) -> tuple[tuple[int, ...], ...]:
    return tuple(
        combinations_with_replacement(
            range(target_dimension + 1), source_dimension + 1
        )
    )


def compose_maps(left: tuple[int, ...], right: tuple[int, ...]) -> tuple[int, ...]:
    """Return the ordinary composition left after right."""
    return tuple(left[value] for value in right)


def normalize(simplex: tuple[int, ...], period: int) -> tuple[int, ...]:
    shift = period * (simplex[0] // period)
    return tuple(value - shift for value in simplex)


def quotient_simplices(obj: str, degree: int) -> tuple[tuple[int, ...], ...]:
    period = 2 if obj == A else 1
    width = period
    values = set()
    for first in range(period):
        for tail in combinations_with_replacement(
            range(first, first + width + 1), degree
        ):
            values.add((first,) + tail)
    return tuple(sorted(values))


def pullback(
    simplex: tuple[int, ...], alpha: tuple[int, ...], period: int
) -> tuple[int, ...]:
    return normalize(tuple(simplex[index] for index in alpha), period)


def apply_arrow(arrow: Arrow, simplex: tuple[int, ...]) -> tuple[int, ...]:
    if arrow.name in {"1a", "1b"}:
        return simplex
    if arrow.name.startswith("i"):
        k = int(arrow.name[1])
        return normalize(tuple(2 * value + k for value in simplex), 2)
    if arrow.name.startswith("r"):
        j = int(arrow.name[1])
        return normalize(tuple((value + j) // 2 for value in simplex), 1)
    if arrow.name.startswith("x"):
        k, j = int(arrow.name[1]), int(arrow.name[2])
        return normalize(
            tuple(2 * ((value + j) // 2) + k for value in simplex), 2
        )
    raise AssertionError(arrow)


def verify_simplicial_diagram() -> None:
    counts_a = tuple(len(quotient_simplices(A, degree)) for degree in range(3))
    counts_b = tuple(len(quotient_simplices(B, degree)) for degree in range(3))
    assert counts_a == (2, 6, 12)
    assert counts_b == (1, 2, 3)

    for arrow in D:
        for degree in range(3):
            source = quotient_simplices(arrow.source, degree)
            target = set(quotient_simplices(arrow.target, degree))
            for simplex in source:
                assert apply_arrow(arrow, simplex) in target

    # Functoriality in D.
    for left, right in composable_pairs():
        composite = compose(left, right)
        for degree in range(3):
            for simplex in quotient_simplices(right.source, degree):
                assert apply_arrow(left, apply_arrow(right, simplex)) == apply_arrow(
                    composite, simplex
                )

    # Naturality for every operator in Delta_{<=2}.
    for arrow in D:
        source_period = 2 if arrow.source == A else 1
        target_period = 2 if arrow.target == A else 1
        for degree in range(3):
            for new_degree in range(3):
                for alpha in monotone_maps(new_degree, degree):
                    for simplex in quotient_simplices(arrow.source, degree):
                        lhs = apply_arrow(
                            arrow, pullback(simplex, alpha, source_period)
                        )
                        rhs = pullback(
                            apply_arrow(arrow, simplex), alpha, target_period
                        )
                        assert lhs == rhs

    # In D x Delta_{<=2}^op, every object is a retract of (a,[2]).
    for dimension in range(3):
        found = False
        for collapse in monotone_maps(2, dimension):
            for inclusion in monotone_maps(dimension, 2):
                if compose_maps(collapse, inclusion) == tuple(
                    range(dimension + 1)
                ):
                    found = True
                    break
            if found:
                break
        assert found

    # The frame object is (b,[0]), whose value is a singleton.
    assert quotient_simplices(B, 0) == ((0,),)


def cover_period(obj: str) -> int:
    return 2 if obj == A else 1


def lift(arrow: Arrow, value: int) -> int:
    if arrow.name in {"1a", "1b"}:
        return value
    if arrow.name.startswith("i"):
        return 2 * value + int(arrow.name[1])
    if arrow.name.startswith("r"):
        return (value + int(arrow.name[1])) // 2
    if arrow.name.startswith("x"):
        k, j = int(arrow.name[1]), int(arrow.name[2])
        return 2 * ((value + j) // 2) + k
    raise AssertionError(arrow)


def deck_cocycle(left: Arrow, right: Arrow) -> int:
    composite = compose(left, right)
    source_period = cover_period(right.source)
    target_period = cover_period(left.target)
    shifts = set()
    for value in range(source_period):
        difference = lift(left, lift(right, value)) - lift(composite, value)
        assert difference % target_period == 0
        shifts.add(difference // target_period)
    assert len(shifts) == 1
    return shifts.pop()


def closed_formula_cocycle(left: Arrow, right: Arrow) -> int:
    first = left.name in {"r1", "x01", "x11"}
    second = right.name in {"i1", "x10", "x11"}
    return int(first and second)


def verify_cocycle() -> dict[tuple[Arrow, Arrow], int]:
    # Equivariance reduces every identity on the infinite covers to the
    # finitely many residue classes checked below.
    for arrow in D:
        source_period = cover_period(arrow.source)
        target_period = cover_period(arrow.target)
        for value in range(source_period):
            assert lift(arrow, value + source_period) == lift(
                arrow, value
            ) + target_period
            assert lift(arrow, value - source_period) == lift(
                arrow, value
            ) - target_period

    omega = {}
    for left, right in composable_pairs():
        value = deck_cocycle(left, right)
        assert value == closed_formula_cocycle(left, right)
        omega[left, right] = value

    for arrow in D:
        source_identity = BY_NAME[f"1{arrow.source}"]
        target_identity = BY_NAME[f"1{arrow.target}"]
        assert omega[target_identity, arrow] == 0
        assert omega[arrow, source_identity] == 0

    for f, g, h in composable_triples():
        lhs = omega[f, g] + omega[compose(f, g), h]
        rhs = omega[g, h] + omega[f, compose(g, h)]
        assert lhs == rhs

    # The chosen lifts induce the quotient maps in every simplicial degree.
    for arrow in D:
        target_period = cover_period(arrow.target)
        for degree in range(3):
            for simplex in quotient_simplices(arrow.source, degree):
                lifted = normalize(
                    tuple(lift(arrow, value) for value in simplex), target_period
                )
                assert lifted == apply_arrow(arrow, simplex)
    return omega


def verify_generator_pairing(omega: dict[tuple[Arrow, Arrow], int]) -> int:
    # This is the standard generator cycle for the rectangular-band model of
    # S^2, transported by x_kj -> x_(1-k)(1-j).
    cycle = {
        (BY_NAME["x11"], BY_NAME["x11"]): -1,
        (BY_NAME["x00"], BY_NAME["x00"]): -1,
        (BY_NAME["x10"], BY_NAME["x10"]): 1,
        (BY_NAME["x11"], BY_NAME["x00"]): 1,
    }
    boundary = Counter()
    for (left, right), coefficient in cycle.items():
        boundary[left] += coefficient
        boundary[compose(left, right)] -= coefficient
        boundary[right] += coefficient
    boundary = Counter({arrow: value for arrow, value in boundary.items() if value})
    assert not boundary

    pairing = sum(coefficient * omega[left, right] for (left, right), coefficient in cycle.items())
    assert pairing == -1
    return pairing


def l0_arrow(index: int) -> Arrow:
    if index == 0:
        return BY_NAME["1a"]
    k, j = divmod(index - 1, 2)
    return BY_NAME[f"x{k}{j}"]


def l0_index(arrow: Arrow) -> int:
    if arrow.name == "1a":
        return 0
    assert arrow.name.startswith("x")
    return 1 + 2 * int(arrow.name[1]) + int(arrow.name[2])


O3 = monotone_maps(2, 2)
ID_O3 = (0, 1, 2)
A2 = quotient_simplices(A, 2)


def framed_elements() -> tuple[tuple, ...]:
    endomorphisms = tuple(("n", x, theta) for x in range(5) for theta in O3)
    ideal = tuple(
        ("k", simplex, retraction, vertex)
        for simplex in A2
        for retraction in range(2)
        for vertex in range(3)
    )
    return endomorphisms + ideal


def framed_multiply(left: tuple, right: tuple) -> tuple:
    if left[0] == "n" and right[0] == "n":
        _, x, theta = left
        _, xp, thetap = right
        product = compose(l0_arrow(x), l0_arrow(xp))
        return ("n", l0_index(product), compose_maps(thetap, theta))
    if left[0] == "n":
        _, x, theta = left
        _, simplex, retraction, vertex = right
        pulled_back = pullback(simplex, theta, 2)
        return (
            "k",
            apply_arrow(l0_arrow(x), pulled_back),
            retraction,
            vertex,
        )
    if right[0] == "n":
        _, simplex, retraction, vertex = left
        _, x, theta = right
        composite = compose(BY_NAME[f"r{retraction}"], l0_arrow(x))
        assert composite.name.startswith("r")
        new_retraction = int(composite.name[1])
        return ("k", simplex, new_retraction, theta[vertex])
    _, simplex, _, _ = left
    _, _, retraction, vertex = right
    return ("k", simplex, retraction, vertex)


def verify_endomorphism_monoid() -> None:
    elements = framed_elements()
    assert len(O3) == 10
    assert len(A2) == 12
    assert len(elements) == 50 + 12 * 2 * 3 == 122

    # The six maps (r_j, i) are precisely Hom((a,[2]),(b,[0])).
    assert len([arrow for arrow in D if arrow.source == A and arrow.target == B]) == 2
    assert len(monotone_maps(0, 2)) == 3

    # Compare every labeled product with the independent implementation used
    # for the published multiplication table.
    assert set(elements) == set(annulus_cp2.els)
    table_index = {element: index for index, element in enumerate(annulus_cp2.els)}
    for left in elements:
        for right in elements:
            product = framed_multiply(left, right)
            assert product == annulus_cp2.mult(left, right)
            i = table_index[left]
            j = table_index[right]
            assert annulus_cp2.mul[i][j] == table_index[product]
    assert annulus_cp2.Monoid(annulus_cp2.mul).check()


def main() -> None:
    verify_category()
    verify_simplicial_diagram()
    omega = verify_cocycle()
    pairing = verify_generator_pairing(omega)
    verify_endomorphism_monoid()

    print(f"D: {len(D)} arrows, {len(composable_pairs())} composable pairs, category laws verified")
    print("P: |A_0,A_1,A_2| = 2,6,12 and |C_0,C_1,C_2| = 1,2,3")
    print("P: functoriality, all simplicial operators, frame, and retracts verified")
    print("M_122: framed endomorphism formula agrees with annulus_cp2.py in every product")
    print(f"omega: normalized integral 2-cocycle; generator-cycle pairing = {pairing}")
    print("All finite hypotheses in ANNULUS_CP2_PROOF.md passed.")


if __name__ == "__main__":
    main()
