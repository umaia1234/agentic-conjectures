#!/usr/bin/env python3
"""Sparse exact CP-SAT search for the n=14 degree--sensitivity candidate.

The truth table is transformed by a shared fast Moebius circuit.  This avoids
expanding every high-degree coefficient into all of its submasks: there are
n*2^(n-1) three-term subtraction equations instead of millions of repeated
terms.  At the end of the circuit, entries indexed by masks of weight > d are
exactly the multilinear coefficients and are fixed to zero.
"""

from __future__ import annotations

import argparse
import json
from fractions import Fraction
from math import comb, log
from pathlib import Path

from ortools.sat.python import cp_model

try:
    from .degree_sensitivity_pair_bound import feasible_layer_profiles
except ImportError:
    from degree_sensitivity_pair_bound import feasible_layer_profiles


def subsets(mask: int):
    submask = mask
    while True:
        yield submask
        if submask == 0:
            return
        submask = (submask - 1) & mask


def polynomial_coefficients(values: list[int], n: int) -> list[int]:
    coefficients = values.copy()
    for bit in range(n):
        step = 1 << bit
        for mask in range(1 << n):
            if mask & step:
                coefficients[mask] -= coefficients[mask ^ step]
    return coefficients


def verify(values: list[int], n: int, degree_bound: int) -> tuple[int, list[int]]:
    assert len(values) == 1 << n
    assert set(values) <= {0, 1}
    assert values[0] == 0
    assert all(values[1 << bit] == 1 for bit in range(n))
    coefficients = polynomial_coefficients(values, n)
    degree = max(
        (mask.bit_count() for mask, value in enumerate(coefficients) if value),
        default=0,
    )
    assert degree <= degree_bound
    return degree, coefficients


def lagrange_coefficient(x: int, node: int, degree: int) -> Fraction:
    coefficient = Fraction(1)
    for other in range(degree + 1):
        if other != node:
            coefficient *= Fraction(x - other, node - other)
    return coefficient


def build_model(
    n: int, degree: int, max_zero_degree: int | None
) -> tuple[cp_model.CpModel, list[cp_model.IntVar]]:
    model = cp_model.CpModel()
    values = [model.new_bool_var(f"y_{mask}") for mask in range(1 << n)]
    model.add(values[0] == 0)
    for bit in range(n):
        model.add(values[1 << bit] == 1)

    # Redundant but strong aggregate equations.  The layer averages q(t) form
    # a degree-d polynomial, so interpolation from layers 0,...,d determines
    # every later layer.  Multiplication by binomial layer sizes makes all
    # coefficients integral for this Boolean-cube symmetrization.
    layer_sums = [
        sum(values[mask] for mask in range(1 << n) if mask.bit_count() == size)
        for size in range(n + 1)
    ]
    for target in range(degree + 1, n + 1):
        coefficients = [
            Fraction(comb(n, target), comb(n, node))
            * lagrange_coefficient(target, node, degree)
            for node in range(degree + 1)
        ]
        if any(coefficient.denominator != 1 for coefficient in coefficients):
            raise AssertionError("unexpected nonintegral layer interpolation")
        model.add(
            layer_sums[target]
            == sum(
                int(coefficient) * layer_sums[node]
                for node, coefficient in enumerate(coefficients)
            )
        )

    if (n, degree) == (14, 5):
        pair_values = [values[mask] for mask in range(1 << n) if mask.bit_count() == 2]
        # Exact layer-average interpolation gives B_2 >= 84.  The separate
        # degree_sensitivity_pair_bound.py file verifies the rational identity.
        pair_sum = sum(pair_values)
        model.add(pair_sum >= 84)
        triple_sum = layer_sums[3]
        # Two further exact Lagrange inequalities couple the second and third
        # Hamming layers.  They are especially strong near B_2=91.
        model.add(300 * triple_sum - 1925 * pair_sum >= -108801)
        model.add(21 * triple_sum - 180 * pair_sum <= -11375)

        # Integral interpolation leaves only 247 possible aggregate tuples
        # (B_2,B_3,B_4,B_5).  The linear layer equations above imply this
        # disjunction mathematically, but supplying it explicitly gives
        # CP-SAT substantially stronger finite-domain propagation.
        profile_variables = []
        for size in range(2, 6):
            variable = model.new_int_var(0, comb(n, size), f"B_{size}")
            model.add(variable == layer_sums[size])
            profile_variables.append(variable)
        profiles = feasible_layer_profiles()
        assert len(profiles) == 247
        model.add_allowed_assignments(profile_variables, profiles)

    if max_zero_degree is not None:
        if (n, degree) != (14, 5) or not 0 <= max_zero_degree <= 7:
            raise ValueError("--max-zero-degree is certified only for n=14,d=5 and 0..7")
        for j in range(1, n):
            model.add(
                values[1 | (1 << j)] == (0 if j <= max_zero_degree else 1)
            )
        one_degree_zero = sum(values[1 | (1 << j)] for j in range(1, n))
        for i in range(1, n):
            one_degree_i = sum(
                values[(1 << i) | (1 << j)] for j in range(n) if j != i
            )
            model.add(one_degree_i >= one_degree_zero)
    else:
        # Safe full relabelling symmetry break: nonincreasing degrees in the
        # graph whose edges are pair values equal to one.
        one_degrees = [
            sum(values[(1 << i) | (1 << j)] for j in range(n) if j != i)
            for i in range(n)
        ]
        for i in range(n - 1):
            model.add(one_degrees[i] >= one_degrees[i + 1])

    # Fast Boolean-lattice Moebius transform.  When processing bit b, entries
    # containing b are replaced by old[mask]-old[mask without b].
    transformed: list[cp_model.LinearExpr | cp_model.IntVar] = list(values)
    created = 0
    for bit in range(n):
        step = 1 << bit
        next_transformed = transformed.copy()
        processed_mask = (1 << (bit + 1)) - 1
        for mask in range(1 << n):
            if not mask & step:
                continue
            order = (mask & processed_mask).bit_count()
            magnitude = 1 << max(0, order - 1)
            target = model.new_int_var(-magnitude, magnitude, f"m_{bit}_{mask}")
            model.add(target == transformed[mask] - transformed[mask ^ step])
            next_transformed[mask] = target
            created += 1
        transformed = next_transformed

    assert created == n * (1 << (n - 1))
    for mask, coefficient in enumerate(transformed):
        if mask.bit_count() > degree:
            model.add(coefficient == 0)
    return model, values


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--n", type=int, default=14)
    parser.add_argument("--degree", type=int, default=5)
    parser.add_argument("--max-zero-degree", type=int, default=None)
    parser.add_argument("--time-limit", type=float, default=600.0)
    parser.add_argument("--workers", type=int, default=8)
    parser.add_argument("--seed", type=int, default=20260811)
    parser.add_argument(
        "--output",
        type=Path,
        default=Path(__file__).with_name("degree_sensitivity_certificate.json"),
    )
    args = parser.parse_args()
    if not 1 < args.degree < args.n:
        parser.error("require 1 < degree < n")
    if args.n <= args.degree ** (log(6) / log(3)):
        print("warning: these parameters do not improve the known exponent")

    model, value_variables = build_model(
        args.n, args.degree, args.max_zero_degree
    )
    print(
        f"built sparse Moebius model: n={args.n}, d<={args.degree}, "
        f"Booleans={1 << args.n}, subtractors={args.n * (1 << (args.n - 1))}",
        flush=True,
    )
    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = args.time_limit
    solver.parameters.num_search_workers = args.workers
    solver.parameters.random_seed = args.seed
    solver.parameters.log_search_progress = True
    status = solver.solve(model)
    print(
        f"status={solver.status_name(status)} wall_time={solver.wall_time:.3f}s "
        f"branches={solver.num_branches} conflicts={solver.num_conflicts}",
        flush=True,
    )
    if status not in (cp_model.FEASIBLE, cp_model.OPTIMAL):
        return

    values = [solver.value(variable) for variable in value_variables]
    actual_degree, coefficients = verify(values, args.n, args.degree)
    certificate = {
        "n": args.n,
        "degree": actual_degree,
        "sensitivity_at_zero": args.n,
        "max_zero_degree_branch": args.max_zero_degree,
        "truth_table": values,
        "nonzero_monomials": [
            {
                "variables": [
                    bit + 1 for bit in range(args.n) if mask & (1 << bit)
                ],
                "coefficient": coefficient,
            }
            for mask, coefficient in enumerate(coefficients)
            if coefficient
        ],
    }
    args.output.write_text(json.dumps(certificate, indent=2) + "\n", encoding="utf-8")
    print(
        f"independently verified certificate: degree={actual_degree}, "
        f"monomials={len(certificate['nonzero_monomials'])}, output={args.output}",
        flush=True,
    )


if __name__ == "__main__":
    main()
