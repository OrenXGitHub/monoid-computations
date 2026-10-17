#!/usr/bin/env python3
"""Check small monoids against the homology of S^2 wedge S^2.

The input files are the compressed multiplication-table files distributed by
the GAP Smallsemi package.  For each order n <= max_order, this script:

* reconstructs every semigroup table in the Smallsemi census;
* keeps precisely the tables having an identity and trivial group completion;
* computes H_2 of the normalized bar complex, first over F_2 and then exactly
  over Q for the surviving candidates.

The script also counts the aperiodic monoids.  Aperiodicity implies trivial
group completion, but the latter is the sharper necessary condition for a
monoid whose classifying space is simply connected.

Smallsemi identifies a semigroup with its opposite.  This is harmless for the
nonexistence test because B(M^op) is homeomorphic to BM.
"""

from __future__ import annotations

import argparse
from fractions import Fraction
import gzip
from pathlib import Path


SMALLSEMI_COUNTS = {1: 1, 2: 4, 3: 18, 4: 126, 5: 1160, 6: 15973}


def tables_of_order(data_dir: Path, order: int):
    if order == 1:
        yield 1, [[0]]
        return

    path = data_dir / f"data{order}.gl.gz"
    with gzip.open(path, "rt", encoding="ascii") as source:
        lines = [line.rstrip("\n") for line in source]

    coordinates = lines[1:]
    expected_coordinates = order * order - 1
    if len(coordinates) != expected_coordinates:
        raise ValueError(
            f"{path}: expected {expected_coordinates} coordinate strings, "
            f"found {len(coordinates)}"
        )

    count = len(coordinates[0])
    if count != SMALLSEMI_COUNTS[order]:
        raise ValueError(
            f"{path}: expected {SMALLSEMI_COUNTS[order]} tables, found {count}"
        )
    if any(len(line) != count for line in coordinates):
        raise ValueError(f"{path}: coordinate strings have unequal lengths")

    for table_id in range(count):
        flat = [0]
        flat.extend(ord(line[table_id]) - ord("0") for line in coordinates)
        table = [flat[i : i + order] for i in range(0, order * order, order)]
        yield table_id + 1, table


def identity_of(table: list[list[int]]) -> int | None:
    for identity in range(len(table)):
        if all(
            table[identity][x] == x and table[x][identity] == x
            for x in range(len(table))
        ):
            return identity
    return None


def is_aperiodic(table: list[list[int]]) -> bool:
    """Use the eventual stabilization criterion for finite monoids."""
    for x in range(len(table)):
        power = x
        seen = {power}
        while True:
            next_power = table[power][x]
            if next_power == power:
                break
            if next_power in seen:
                return False
            seen.add(next_power)
            power = next_power
    return True


def has_trivial_group_completion(
    table: list[list[int]], identity: int
) -> bool:
    """Test whether the universal group of a finite monoid is trivial.

    The least congruence identifying every idempotent with the identity has
    group quotient: every element of the finite quotient has an idempotent
    power, hence a power equal to the identity.  It is therefore the universal
    group quotient.
    """
    order = len(table)
    parent = list(range(order))

    def find(x: int) -> int:
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    def union(x: int, y: int) -> bool:
        x_root = find(x)
        y_root = find(y)
        if x_root == y_root:
            return False
        parent[y_root] = x_root
        return True

    for x in range(order):
        if table[x][x] == x:
            union(x, identity)

    changed = True
    while changed:
        changed = False
        for x in range(order):
            for y in range(x + 1, order):
                if find(x) != find(y):
                    continue
                for z in range(order):
                    changed |= union(table[z][x], table[z][y])
                    changed |= union(table[x][z], table[y][z])

    identity_class = find(identity)
    return all(find(x) == identity_class for x in range(order))


def normalized_bar_columns(table: list[list[int]], identity: int):
    nonunits = [x for x in range(len(table)) if x != identity]
    one_index = {x: i for i, x in enumerate(nonunits)}
    two_index = {
        (x, y): i
        for i, (x, y) in enumerate(
            (x, y) for x in nonunits for y in nonunits
        )
    }

    d2 = []
    for x in nonunits:
        for y in nonunits:
            column: dict[int, int] = {}
            for coefficient, value in ((1, y), (-1, table[x][y]), (1, x)):
                if value != identity:
                    row = one_index[value]
                    column[row] = column.get(row, 0) + coefficient
            d2.append({row: value for row, value in column.items() if value})

    d3 = []
    for x in nonunits:
        for y in nonunits:
            for z in nonunits:
                column = {}
                faces = (
                    (1, (y, z)),
                    (-1, (table[x][y], z)),
                    (1, (x, table[y][z])),
                    (-1, (x, y)),
                )
                for coefficient, pair in faces:
                    if identity not in pair:
                        row = two_index[pair]
                        column[row] = column.get(row, 0) + coefficient
                d3.append({row: value for row, value in column.items() if value})

    return len(nonunits), d2, d3


def rank_mod_2(columns: list[dict[int, int]]) -> int:
    pivots: dict[int, int] = {}
    for column in columns:
        vector = 0
        for row, coefficient in column.items():
            if coefficient % 2:
                vector ^= 1 << row
        while vector:
            pivot = vector.bit_length() - 1
            if pivot not in pivots:
                pivots[pivot] = vector
                break
            vector ^= pivots[pivot]
    return len(pivots)


def dense_rows(
    columns: list[dict[int, int]], number_of_rows: int
) -> list[list[Fraction]]:
    rows = [[Fraction(0) for _ in columns] for _ in range(number_of_rows)]
    for column_number, column in enumerate(columns):
        for row_number, coefficient in column.items():
            rows[row_number][column_number] = Fraction(coefficient)
    return rows


def rational_rank(rows: list[list[Fraction]]) -> int:
    if not rows:
        return 0
    row_count = len(rows)
    column_count = len(rows[0])
    pivot_row = 0
    for column in range(column_count):
        pivot = next(
            (row for row in range(pivot_row, row_count) if rows[row][column]),
            None,
        )
        if pivot is None:
            continue
        rows[pivot_row], rows[pivot] = rows[pivot], rows[pivot_row]
        pivot_value = rows[pivot_row][column]
        rows[pivot_row] = [value / pivot_value for value in rows[pivot_row]]
        for row in range(row_count):
            if row == pivot_row or not rows[row][column]:
                continue
            multiple = rows[row][column]
            rows[row] = [
                value - multiple * pivot_value
                for value, pivot_value in zip(rows[row], rows[pivot_row])
            ]
        pivot_row += 1
        if pivot_row == row_count:
            break
    return pivot_row


def second_betti_number(table: list[list[int]], identity: int) -> tuple[int, int]:
    generators, d2, d3 = normalized_bar_columns(table, identity)
    chain_two_dimension = generators * generators

    rank_d2_mod_2 = rank_mod_2(d2)
    rank_d3_mod_2 = rank_mod_2(d3)
    mod_2_dimension = chain_two_dimension - rank_d2_mod_2 - rank_d3_mod_2
    if mod_2_dimension < 2:
        return mod_2_dimension, -1

    rank_d2_q = rational_rank(dense_rows(d2, generators))
    rank_d3_q = rational_rank(dense_rows(d3, chain_two_dimension))
    rational_dimension = chain_two_dimension - rank_d2_q - rank_d3_q
    return mod_2_dimension, rational_dimension


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "data_dir",
        type=Path,
        help="Smallsemi's data/data2to7 directory",
    )
    parser.add_argument("--max-order", type=int, default=6)
    args = parser.parse_args()

    all_survivors: list[tuple[int, int, int, int, bool]] = []
    for order in range(1, args.max_order + 1):
        monoids = 0
        aperiodic_monoids = 0
        simply_connected_monoids = 0
        mod_2_shortlist = 0
        maximum_b2_mod_2 = 0
        rational_shortlist = []
        for table_id, table in tables_of_order(args.data_dir, order):
            identity = identity_of(table)
            if identity is None:
                continue
            monoids += 1
            aperiodic = is_aperiodic(table)
            if aperiodic:
                aperiodic_monoids += 1
            if not has_trivial_group_completion(table, identity):
                continue
            simply_connected_monoids += 1
            b2_mod_2, b2_q = second_betti_number(table, identity)
            maximum_b2_mod_2 = max(maximum_b2_mod_2, b2_mod_2)
            if b2_mod_2 >= 2:
                mod_2_shortlist += 1
                if b2_q >= 2:
                    survivor = (table_id, b2_mod_2, b2_q, aperiodic)
                    rational_shortlist.append(survivor)
                    all_survivors.append((order, *survivor))

        print(
            f"order {order}: tables={SMALLSEMI_COUNTS[order]}, "
            f"monoids={monoids}, group-completion-trivial="
            f"{simply_connected_monoids}, aperiodic={aperiodic_monoids}, "
            f"max dim H2(F2)={maximum_b2_mod_2}, "
            f"dim H2(F2)>=2: {mod_2_shortlist}, "
            f"dim H2(Q)>=2: {len(rational_shortlist)}"
        )
        if rational_shortlist:
            print(f"  rational survivors: {rational_shortlist}")

    print(f"all rational survivors through order {args.max_order}: {all_survivors}")


if __name__ == "__main__":
    main()
