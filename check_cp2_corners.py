#!/usr/bin/env python3
"""Check Quillen corner reductions in the two explicit CP^2 monoids.

The script performs no search over monoids.  It checks the right- and
left-collapsing criteria for the 122- and 1795-element multiplication tables,
then computes mod-2 cohomology through degree four for the proper idempotent
corners which could improve the bound of 122 elements.
"""

from __future__ import annotations

from array import array
from collections import Counter, defaultdict
import hashlib
import json

import annulus_cp2 as annulus
import cofiber_monoids as cofiber


def proper_idempotents(table):
    return [e for e in range(1, len(table)) if table[e][e] == e]


def corner_table(table, p):
    elements = {table[table[p][m]][p] for m in range(len(table))}
    ordered = [p] + sorted(elements - {p})
    index = {x: i for i, x in enumerate(ordered)}
    return [[index[table[x][y]] for y in ordered] for x in ordered]


def collapse_report(table):
    idempotents = [0] + proper_idempotents(table)
    right_domain = set().union(*(set(table[e]) for e in idempotents if e != 0))
    left_domain = {
        table[m][e]
        for e in idempotents
        if e != 0
        for m in range(len(table))
    }
    right = [
        p
        for p in idempotents
        if p != 0 and all(table[x][p] == x for x in right_domain)
    ]
    left = [
        p
        for p in idempotents
        if p != 0 and all(table[p][x] == x for x in left_domain)
    ]
    return {
        "order": len(table),
        "idempotents": len(idempotents),
        "right_domain": len(right_domain),
        "left_domain": len(left_domain),
        "right_collapsing": right,
        "left_collapsing": left,
    }


def mod2_betti_through_four(table):
    monoid = annulus.Monoid(table)
    assert monoid.check()
    resolution = annulus.Resolution(monoid, 2, 6)
    top = resolution.top - 1
    return [
        len(resolution.cohomology(k)[0]) if k <= top else 0
        for k in range(5)
    ]


def annulus_corner_signatures(table):
    signatures = Counter()
    for p in proper_idempotents(table):
        corner = corner_table(table, p)
        signatures[(len(corner), tuple(mod2_betti_through_four(corner)))] += 1
    return [
        {"order": order, "betti": list(betti), "multiplicity": multiplicity}
        for (order, betti), multiplicity in sorted(signatures.items())
    ]


def table_digest(table):
    entries = array("H", (x for row in table for x in row))
    return hashlib.sha256(entries.tobytes()).hexdigest()


def generic_corner_report(table, bound):
    orders = Counter()
    forms = defaultdict(list)
    representatives = {}
    for p in proper_idempotents(table):
        corner = corner_table(table, p)
        order = len(corner)
        orders[order] += 1
        if order < bound:
            digest = table_digest(corner)
            forms[(order, digest)].append(p)
            representatives[(order, digest)] = corner

    small_forms = []
    for key, ps in sorted(forms.items()):
        order, digest = key
        corner = representatives[key]
        small_forms.append(
            {
                "order": order,
                "multiplicity": len(ps),
                "representative_idempotent": ps[0],
                "table_sha256": digest,
                "betti": mod2_betti_through_four(corner),
            }
        )
    return {
        "corner_orders": dict(sorted(orders.items())),
        "distinct_natural_tables_below_122": small_forms,
    }


def main():
    generic_table, _, _ = cofiber.cofiber_monoid(
        cofiber.mulP,
        cofiber.ONE,
        lambda h: h[0],
        cofiber.L0,
        cofiber.HOPF_SPHERE,
        3,
    )

    result = {
        "annulus_122": {
            **collapse_report(annulus.mul),
            "proper_corner_signatures": annulus_corner_signatures(annulus.mul),
        },
        "generic_1795": {
            **collapse_report(generic_table),
            **generic_corner_report(generic_table, 122),
        },
    }

    assert not result["annulus_122"]["right_collapsing"]
    assert not result["annulus_122"]["left_collapsing"]
    assert not result["generic_1795"]["right_collapsing"]
    assert not result["generic_1795"]["left_collapsing"]
    assert all(
        item["betti"] != [1, 0, 1, 0, 1]
        for item in result["annulus_122"]["proper_corner_signatures"]
    )
    assert all(
        item["betti"] != [1, 0, 1, 0, 1]
        for item in result["generic_1795"]["distinct_natural_tables_below_122"]
    )
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
