#!/usr/bin/env python3
"""Exact finite checks for 00000001030; Python standard library only.

The field elements below represent a + b sqrt(5), with rational a and b.
Normalized vertices are raw vertices / r, where r is the positive square root
of R = phi + 2. Only even powers of r need field division: every odd-degree
moment in the expected table vanishes. No floating point arithmetic is used.

These checks supplement, and do not prove, the sphere-integral moment table,
its equivalence with polynomial exactness, the universal bound, or rigidity.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from hashlib import sha256
from itertools import combinations, product
import json
from pathlib import Path
import sys


@dataclass(frozen=True)
class Q5:
    a: Fraction = Fraction(0)
    b: Fraction = Fraction(0)

    def __post_init__(self):
        object.__setattr__(self, "a", Fraction(self.a))
        object.__setattr__(self, "b", Fraction(self.b))

    @staticmethod
    def coerce(value):
        return value if isinstance(value, Q5) else Q5(Fraction(value))

    def __add__(self, other):
        other = self.coerce(other)
        return Q5(self.a + other.a, self.b + other.b)

    __radd__ = __add__

    def __neg__(self):
        return Q5(-self.a, -self.b)

    def __sub__(self, other):
        return self + -self.coerce(other)

    def __rsub__(self, other):
        return self.coerce(other) - self

    def __mul__(self, other):
        other = self.coerce(other)
        return Q5(self.a * other.a + 5 * self.b * other.b,
                  self.a * other.b + self.b * other.a)

    __rmul__ = __mul__

    def inverse(self):
        denominator = self.a * self.a - 5 * self.b * self.b
        if denominator == 0:
            raise ZeroDivisionError("zero Q(sqrt(5)) element")
        return Q5(self.a / denominator, -self.b / denominator)

    def __truediv__(self, other):
        return self * self.coerce(other).inverse()

    def __rtruediv__(self, other):
        return self.coerce(other) / self

    def __pow__(self, exponent):
        if not isinstance(exponent, int):
            raise TypeError("only integer powers are supported")
        if exponent < 0:
            return self.inverse() ** (-exponent)
        result, base = Q5(1), self
        while exponent:
            if exponent & 1:
                result = result * base
            base = base * base
            exponent >>= 1
        return result

    def sign(self):
        """Exact sign, using rational square comparisons in the mixed case."""
        def rational_sign(x):
            return (x > 0) - (x < 0)

        if self.b == 0:
            return rational_sign(self.a)
        if self.a == 0:
            return rational_sign(self.b)
        if rational_sign(self.a) == rational_sign(self.b):
            return rational_sign(self.a)
        difference = self.a * self.a - 5 * self.b * self.b
        return rational_sign(difference) * rational_sign(self.a)

    def encoded(self):
        return {"rational": str(self.a), "sqrt5_coefficient": str(self.b)}


ZERO, ONE = Q5(0), Q5(1)
SQRT5 = Q5(0, 1)
PHI = (ONE + SQRT5) / 2
R = PHI + 2  # r^2; r itself is not assumed to belong to Q(sqrt(5)).
ALPHA = SQRT5 / 5


def vertices():
    """Three cyclic families; every pair of signs varies independently."""
    result = []
    for family in range(3):
        for s, t in product((-1, 1), repeat=2):
            result.append((
                (ZERO, Q5(s), t * PHI),
                (Q5(s), t * PHI, ZERO),
                (t * PHI, ZERO, Q5(s)),
            )[family])
    return result


def dot(u, v):
    return sum((x * y for x, y in zip(u, v)), ZERO)


def subtract(u, v):
    return tuple(x - y for x, y in zip(u, v))


def negate(u):
    return tuple(-x for x in u)


def cross(u, v):
    return (u[1] * v[2] - u[2] * v[1],
            u[2] * v[0] - u[0] * v[2],
            u[0] * v[1] - u[1] * v[0])


def exponent_triples():
    return [(a, b, d - a - b)
            for d in range(6) for a in range(d + 1)
            for b in range(d - a + 1)]


def target_moment(exponents):
    """The target table, whose surface-integral derivation belongs to Lean."""
    ordered = sorted(exponents, reverse=True)
    if any(e % 2 for e in exponents):
        return ZERO
    return {
        (0, 0, 0): ONE,
        (2, 0, 0): Q5(Fraction(1, 3)),
        (4, 0, 0): Q5(Fraction(1, 5)),
        (2, 2, 0): Q5(Fraction(1, 15)),
    }[tuple(ordered)]


def raw_monomial(v, exponents):
    value = ONE
    for coordinate, exponent in zip(v, exponents):
        value = value * coordinate ** exponent
    return value


def assess(points, target_overrides=None, include_geometry=False):
    """Return a full exact certificate; invalid inputs yield explicit failures."""
    if not points:
        raise ValueError("the design must be nonempty")
    target_overrides = target_overrides or {}
    checks = []

    def record(name, passed, details=None):
        checks.append({"name": name, "passed": bool(passed), "details": details})

    record("normalizer_positive", R.sign() > 0)
    record("cardinality_twelve", len(points) == 12, len(points))
    record("distinct_vertices", len(set(points)) == len(points), len(set(points)))
    norms = [dot(v, v) for v in points]
    record("common_squared_norm", all(n == R for n in norms),
           [n.encoded() for n in norms])

    moment_records = []
    for exponents in exponent_triples():
        degree = sum(exponents)
        raw_mean = sum((raw_monomial(v, exponents) for v in points), ZERO) / len(points)
        expected = target_overrides.get(exponents, target_moment(exponents))
        if degree % 2 == 0:
            normalized = raw_mean / R ** (degree // 2)
            agrees = normalized == expected
            encoded_actual = {"kind": "Qsqrt5", "value": normalized.encoded()}
        else:
            # r is positive. Equality raw_mean/r^d = expected is equivalent to
            # equality of squares plus equal signs; all standard odd targets
            # are zero, and then this is simply raw_mean == 0.
            agrees = (raw_mean ** 2 == expected ** 2 * R ** degree
                      and raw_mean.sign() == expected.sign())
            encoded_actual = ({"kind": "Qsqrt5", "value": ZERO.encoded()}
                              if raw_mean == ZERO else
                              {"kind": "positive_radical_quotient",
                               "numerator": raw_mean.encoded(),
                               "denominator": f"r^{degree}"})
        moment_records.append({
            "exponents": list(exponents), "total_degree": degree,
            "raw_mean": raw_mean.encoded(),
            "normalization_denominator": f"r^{degree}",
            "normalized_mean": encoded_actual,
            "target": expected.encoded(), "passed": agrees,
        })
    failed_exponents = [m["exponents"] for m in moment_records if not m["passed"]]
    record("all_56_moments", not failed_exponents, failed_exponents)
    record("moment_case_count", len(moment_records) == 56, len(moment_records))
    nonzero_targets = sum(m["target"] != ZERO.encoded() for m in moment_records)
    record("target_nonzero_zero_counts", nonzero_targets == 10,
           {"nonzero": nonzero_targets, "zero": len(moment_records) - nonzero_targets})

    pair_records = []
    vertex_counts = []
    for i, u in enumerate(points):
        antipodes = [j for j, v in enumerate(points) if v == negate(u)]
        upper = [j for j, v in enumerate(points) if dot(u, v) / R == ALPHA]
        lower = [j for j, v in enumerate(points) if dot(u, v) / R == -ALPHA]
        vertex_counts.append({"vertex": i, "antipodes": antipodes,
                              "upper": upper, "lower": lower})
    record("one_antipode_each", all(len(c["antipodes"]) == 1 for c in vertex_counts))
    record("five_upper_each", all(len(c["upper"]) == 5 for c in vertex_counts))
    record("five_lower_each", all(len(c["lower"]) == 5 for c in vertex_counts))
    for i, j in combinations(range(len(points)), 2):
        value = dot(points[i], points[j]) / R
        pair_records.append({"vertices": [i, j], "inner_product": value.encoded(),
                             "allowed": value in (-ONE, ALPHA, -ALPHA)})
    record("off_diagonal_inner_products", all(p["allowed"] for p in pair_records))

    geometry = None
    if include_geometry:
        geometry = assess_geometry(points)
        for name, passed in geometry["checks"].items():
            record("geometry_" + name, passed)

    return {"passed": all(c["passed"] for c in checks),
            "checks": checks, "moments": moment_records,
            "pair_inner_products": pair_records, "vertex_counts": vertex_counts,
            "geometry": geometry}


def assess_geometry(points):
    """Enumerate every supporting vertex plane through a noncollinear triple."""
    facets = set()
    witness_planes = {}
    for triple in combinations(range(len(points)), 3):
        p, q, s = [points[i] for i in triple]
        normal = cross(subtract(q, p), subtract(s, p))
        if normal == (ZERO, ZERO, ZERO):
            continue
        offsets = [dot(normal, subtract(v, p)) for v in points]
        signs = [value.sign() for value in offsets]
        if all(sign >= 0 for sign in signs) or all(sign <= 0 for sign in signs):
            facet = tuple(i for i, sign in enumerate(signs) if sign == 0)
            facets.add(facet)
            witness_planes.setdefault(facet, {
                "normal": [c.encoded() for c in normal],
                "offset": dot(normal, p).encoded(),
                "vertex_signed_offsets": [x.encoded() for x in offsets],
            })
    facets = sorted(facets)
    edges = sorted({tuple(sorted(edge)) for facet in facets
                    for edge in combinations(facet, 2)})
    lengths = [dot(subtract(points[i], points[j]), subtract(points[i], points[j]))
               for i, j in edges]
    edge_face_counts = [sum(i in f and j in f for f in facets) for i, j in edges]
    vertex_edge_counts = [sum(i in edge for edge in edges) for i in range(len(points))]
    vertex_face_counts = [sum(i in f for f in facets) for i in range(len(points))]
    affine_basis = None
    for indices in combinations(range(len(points)), 4):
        p, q, s, t = [points[i] for i in indices]
        determinant = dot(subtract(q, p), cross(subtract(s, p), subtract(t, p)))
        if determinant != ZERO:
            affine_basis = {"vertices": list(indices), "determinant": determinant.encoded()}
            break
    return {
        "checks": {
            "full_affine_dimension": affine_basis is not None,
            "twenty_facets": len(facets) == 20,
            "all_facets_triangular": all(len(f) == 3 for f in facets),
            "thirty_edges": len(edges) == 30,
            "all_raw_edge_lengths_squared_four": all(x == Q5(4) for x in lengths),
            "two_faces_per_edge": all(c == 2 for c in edge_face_counts),
            "five_edges_per_vertex": all(c == 5 for c in vertex_edge_counts),
            "five_faces_per_vertex": all(c == 5 for c in vertex_face_counts),
            "euler_characteristic_two": len(points) - len(edges) + len(facets) == 2,
        },
        "affine_basis_witness": affine_basis,
        "facets": [{"vertices": list(f), **witness_planes[f]} for f in facets],
        "edges": [list(e) for e in edges],
        "edge_face_counts": edge_face_counts,
        "vertex_edge_counts": vertex_edge_counts,
        "vertex_face_counts": vertex_face_counts,
    }


def failed_checks(result):
    return [c["name"] for c in result["checks"] if not c["passed"]]


def sensitivity_tests(base):
    """Independent expected outcomes: broken inputs rejected, symmetry accepted."""
    tests = []

    def run(name, points, should_pass, required_failures=(), overrides=None, geometry=False):
        result = assess(points, overrides, include_geometry=geometry)
        failures = failed_checks(result)
        success = (result["passed"] == should_pass
                   and set(required_failures).issubset(failures))
        tests.append({"name": name, "passed": success,
                      "expected_checker_acceptance": should_pass,
                      "actual_checker_acceptance": result["passed"],
                      "required_failures": list(required_failures),
                      "actual_failures": failures,
                      "failed_moment_exponents": [m["exponents"] for m in result["moments"]
                                                  if not m["passed"]]})

    run("delete_one_vertex", base[:-1], False,
        ("cardinality_twelve", "all_56_moments", "one_antipode_each"))

    changed_sign = list(base)
    u = changed_sign[0]
    changed_sign[0] = (u[0], -u[1], u[2])
    run("flip_one_coordinate_of_one_vertex", changed_sign, False,
        ("distinct_vertices", "all_56_moments"))

    tiny_change = list(base)
    u = tiny_change[0]
    tiny_change[0] = (u[0] + Fraction(1, 10 ** 30), u[1], u[2])
    run("tiny_exact_rational_perturbation", tiny_change, False,
        ("common_squared_norm", "all_56_moments", "off_diagonal_inner_products"))

    run("alter_second_moment_target", base, False, ("all_56_moments",),
        overrides={(2, 0, 0): Q5(Fraction(2, 5))})

    reflected = [(-u[0], u[1], u[2]) for u in base]
    run("valid_global_coordinate_reflection", reflected, True, geometry=True)

    # This exact rational orthogonal map is not merely a sign/permutation of
    # the coordinate list. It exercises mixed moments after a genuine rotation.
    rotated = [(Fraction(3, 5) * u[0] - Fraction(4, 5) * u[1],
                Fraction(4, 5) * u[0] + Fraction(3, 5) * u[1], u[2]) for u in base]
    run("valid_rational_plane_rotation", rotated, True, geometry=True)
    return tests


def arithmetic_checks():
    return {
        "sqrt5_square": SQRT5 ** 2 == Q5(5),
        "golden_ratio_equation": PHI ** 2 == PHI + 1,
        "normalizer_square_identity": R ** 2 == 5 * PHI ** 2,
        "fourth_power_identity": 1 + PHI ** 4 == 3 * PHI ** 2,
        "alpha_equivalence": PHI / R == ALPHA,
        "field_inverse": (3 - 2 * SQRT5) * (3 - 2 * SQRT5).inverse() == ONE,
        "positive_mixed_sign": (SQRT5 - 2).sign() == 1,
        "negative_mixed_sign": (2 - SQRT5).sign() == -1,
        "positive_rational_dominance": (3 - SQRT5).sign() == 1,
        "negative_rational_dominance": (SQRT5 - 3).sign() == -1,
        "zero_sign": ZERO.sign() == 0,
    }


def main():
    base = vertices()
    arithmetic = arithmetic_checks()
    baseline = assess(base, include_geometry=True)
    mutations = sensitivity_tests(base)
    success = all(arithmetic.values()) and baseline["passed"] and all(t["passed"] for t in mutations)
    output = {
        "schema": "icosahedron-exact-check-v1",
        "checker_source_sha256": sha256(Path(__file__).read_bytes()).hexdigest(),
        "passed": success,
        "arithmetic": "exact Fraction coefficients in Q(sqrt(5)); no floats",
        "field_representation": "rational + sqrt5_coefficient * sqrt(5)",
        "normalization": {"r_definition": "positive square root of R",
                          "R": R.encoded(), "phi": PHI.encoded(),
                          "normalized_vertex": "raw_vertex / r"},
        "scope_limit": "Finite coordinate evidence only; not a proof of sphere integration, "
                       "the universal cardinality lower bound, or equality-case rigidity.",
        "arithmetic_sanity_checks": arithmetic,
        "raw_vertices": [[c.encoded() for c in v] for v in base],
        "baseline": baseline,
        "sensitivity_tests": mutations,
    }
    encoded = (json.dumps(output, indent=2, sort_keys=True) + "\n").encode()
    destination = Path(__file__).resolve().parent
    (destination / "exact-check-results.json").write_bytes(encoded)
    lines = [
        "Exact icosahedron auxiliary checker",
        "Arithmetic: Python standard-library Fraction in Q(sqrt(5)); no floating point.",
        f"Arithmetic sanity checks: {sum(arithmetic.values())}/{len(arithmetic)} passed.",
        f"Baseline: {'PASS' if baseline['passed'] else 'FAIL'}.",
        "Coordinates: 12 distinct vertices, each raw squared norm R = (5+sqrt(5))/2.",
        "Normalized moments: 56 checked, 10 nonzero targets and 46 zero targets.",
        "Pairs: 66 off-diagonal products checked; one antipode, five upper and five lower per vertex.",
        "Geometry: full affine dimension, 20 supporting triangular facets, 30 equal edges; incidence checked.",
    ]
    for test in mutations:
        lines.append(f"Sensitivity {test['name']}: {'PASS' if test['passed'] else 'FAIL'} "
                     f"(checker accepted={test['actual_checker_acceptance']}; "
                     f"expected={test['expected_checker_acceptance']}).")
        if test["actual_failures"]:
            lines.append("  Rejected by: " + ", ".join(test["actual_failures"]) + ".")
    lines.extend([
        f"Overall: {'PASS' if success else 'FAIL'}.",
        "Checker source SHA-256: " + output["checker_source_sha256"],
        "JSON SHA-256: " + sha256(encoded).hexdigest(),
        "Scope: these finite checks supplement the accompanying Lean surface-integral and universal proof.",
        "They do not establish the target surface moments, minimum theorem, or congruence rigidity.",
    ])
    log = "\n".join(lines) + "\n"
    (destination / "exact-check.log").write_text(log)
    sys.stdout.write(log)
    return 0 if success else 1


if __name__ == "__main__":
    raise SystemExit(main())
