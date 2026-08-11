#!/usr/bin/env python3
"""Exact MILP search for the FrontierMath degree--sensitivity problem.

We seek a Boolean function f on n variables such that f(0)=0, f(e_i)=1,
and its unique multilinear polynomial has degree at most d.  If y_X=f(1_X),
the coefficient of monomial X is the Boolean-lattice Moebius transform

    c_X = sum_{T subseteq X} (-1)^(|X|-|T|) y_T.

Thus degree(f) <= d is exactly the collection of integer linear equations
c_X=0 for every |X|>d.  All y_X are binary, so a feasible MILP solution is
already a finite, independently checkable certificate.
"""

from __future__ import annotations

import argparse
import json
from itertools import combinations
from math import comb
from pathlib import Path

import numpy as np
from scipy.optimize import Bounds, LinearConstraint, milp
from scipy.sparse import coo_array, vstack


def subsets(mask: int):
    submask = mask
    while True:
        yield submask
        if submask == 0:
            return
        submask = (submask - 1) & mask


def moebius_matrix(n: int, degree: int):
    rows: list[int] = []
    cols: list[int] = []
    data: list[int] = []
    row = 0
    for mask in range(1 << n):
        size = mask.bit_count()
        if size <= degree:
            continue
        for submask in subsets(mask):
            rows.append(row)
            cols.append(submask)
            data.append(-1 if (size - submask.bit_count()) & 1 else 1)
        row += 1
    return coo_array(
        (np.asarray(data, dtype=np.int8), (rows, cols)),
        shape=(row, 1 << n),
        dtype=np.int8,
    ).tocsr()


def degree_order_matrix(n: int):
    """Safe symmetry break: pair-graph degrees are nonincreasing."""
    rows: list[int] = []
    cols: list[int] = []
    data: list[int] = []
    for i in range(n - 1):
        for j in range(n):
            if i != j:
                rows.append(i)
                cols.append((1 << i) | (1 << j))
                data.append(1)
            if i + 1 != j:
                rows.append(i)
                cols.append((1 << (i + 1)) | (1 << j))
                data.append(-1)
    return coo_array(
        (np.asarray(data, dtype=np.int8), (rows, cols)),
        shape=(n - 1, 1 << n),
        dtype=np.int8,
    ).tocsr()


def monomial_masks(n: int, degree: int) -> list[int]:
    return [mask for mask in range(1 << n) if mask.bit_count() <= degree]


def zeta_evaluation_matrix(n: int, degree: int, masks: list[int]):
    """Map low-degree monomial coefficients to all cube evaluations."""
    column_of = {mask: column for column, mask in enumerate(masks)}
    rows: list[int] = []
    cols: list[int] = []
    for assignment in range(1 << n):
        for submask in subsets(assignment):
            if submask.bit_count() <= degree:
                rows.append(assignment)
                cols.append(column_of[submask])
    return coo_array(
        (np.ones(len(rows), dtype=np.int8), (rows, cols)),
        shape=(1 << n, len(masks)),
        dtype=np.int8,
    ).tocsr()


def coefficient_degree_order_matrix(n: int, masks: list[int]):
    """Safe symmetry break using degrees in the graph of pair evaluations."""
    column_of = {mask: column for column, mask in enumerate(masks)}
    rows: list[int] = []
    cols: list[int] = []
    data: list[int] = []
    for i in range(n - 1):
        for j in range(n):
            if i != j:
                rows.append(i)
                cols.append(column_of[(1 << i) | (1 << j)])
                data.append(1)
            if i + 1 != j:
                rows.append(i)
                cols.append(column_of[(1 << (i + 1)) | (1 << j)])
                data.append(-1)
    return coo_array(
        (np.asarray(data, dtype=np.int8), (rows, cols)),
        shape=(n - 1, len(masks)),
        dtype=np.int8,
    ).tocsr()


def max_zero_degree_matrix(n: int, masks: list[int]):
    """Make vertex 0 a maximum-degree vertex of the zero-valued pair graph.

    If p_i is the number of pair values equal to one at vertex i, then its
    degree in the complementary zero graph is n-1-p_i.  The safe symmetry
    break deg_zero(0) >= deg_zero(i) is therefore p_i-p_0 >= 0.
    """
    column_of = {mask: column for column, mask in enumerate(masks)}
    rows: list[int] = []
    cols: list[int] = []
    data: list[int] = []
    for i in range(1, n):
        row = i - 1
        for j in range(n):
            if j != i:
                rows.append(row)
                cols.append(column_of[(1 << i) | (1 << j)])
                data.append(1)
            if j != 0:
                rows.append(row)
                cols.append(column_of[1 | (1 << j)])
                data.append(-1)
    return coo_array(
        (np.asarray(data, dtype=np.int8), (rows, cols)),
        shape=(n - 1, len(masks)),
        dtype=np.int8,
    ).tocsr()


def pair_layer_matrix(n: int, masks: list[int]):
    """One row summing all Hamming-weight-two truth values."""
    column_of = {mask: column for column, mask in enumerate(masks)}
    pair_masks = [mask for mask in masks if mask.bit_count() == 2]
    return coo_array(
        (
            np.ones(len(pair_masks), dtype=np.int8),
            (np.zeros(len(pair_masks), dtype=np.int32),
             np.asarray([column_of[mask] for mask in pair_masks], dtype=np.int32)),
        ),
        shape=(1, len(masks)),
        dtype=np.int8,
    ).tocsr()


def low_value_extension_matrix(n: int, degree: int, masks: list[int]):
    """Evaluate the degree-d interpolant from cube values of weight at most d.

    For an assignment T with |T|>d, Boolean-lattice interpolation gives

      P(T) = sum_{U subseteq T, |U|<=d}
             (-1)^(d-|U|) C(|T|-|U|-1, d-|U|) f(U).

    Requiring every such integer to lie in [0,1] is therefore equivalent to
    requiring the degree-d interpolant to be Boolean on the entire cube.
    """
    column_of = {mask: column for column, mask in enumerate(masks)}
    rows: list[int] = []
    cols: list[int] = []
    data: list[int] = []
    row = 0
    for assignment in range(1 << n):
        assignment_size = assignment.bit_count()
        if assignment_size <= degree:
            continue
        for submask in subsets(assignment):
            submask_size = submask.bit_count()
            if submask_size <= degree:
                rows.append(row)
                cols.append(column_of[submask])
                data.append(
                    (-1 if (degree - submask_size) & 1 else 1)
                    * comb(assignment_size - submask_size - 1, degree - submask_size)
                )
        row += 1
    return coo_array(
        (np.asarray(data, dtype=np.int16), (rows, cols)),
        shape=(row, len(masks)),
        dtype=np.int16,
    ).tocsr()


def polynomial_coefficients(values: list[int], n: int) -> list[int]:
    coefficients = values.copy()
    for bit in range(n):
        step = 1 << bit
        for mask in range(1 << n):
            if mask & step:
                coefficients[mask] -= coefficients[mask ^ step]
    return coefficients


def verify(values: list[int], n: int, degree_bound: int) -> int:
    assert len(values) == 1 << n
    assert set(values) <= {0, 1}
    assert values[0] == 0
    assert all(values[1 << i] == 1 for i in range(n))
    coefficients = polynomial_coefficients(values, n)
    actual_degree = max(
        (mask.bit_count() for mask, coefficient in enumerate(coefficients) if coefficient),
        default=0,
    )
    assert actual_degree <= degree_bound
    return actual_degree


def search_truth_table(n: int, degree: int, time_limit: float, output: Path) -> None:
    variable_count = 1 << n
    lower = np.zeros(variable_count)
    upper = np.ones(variable_count)
    upper[0] = 0
    for bit in range(n):
        lower[1 << bit] = 1

    moebius = moebius_matrix(n, degree)
    ordered_degrees = degree_order_matrix(n)
    constraints = LinearConstraint(
        vstack([moebius, ordered_degrees], format="csr"),
        np.concatenate([np.zeros(moebius.shape[0]), np.zeros(n - 1)]),
        np.concatenate([np.zeros(moebius.shape[0]), np.full(n - 1, np.inf)]),
    )
    print(
        f"n={n} d<={degree}: {variable_count} binary variables, "
        f"{moebius.shape[0]} degree equations, {moebius.nnz} Moebius nonzeros",
        flush=True,
    )
    result = milp(
        c=np.zeros(variable_count),
        integrality=np.ones(variable_count, dtype=np.uint8),
        bounds=Bounds(lower, upper),
        constraints=constraints,
        options={
            "disp": True,
            "presolve": True,
            "time_limit": time_limit,
            "mip_rel_gap": 0.0,
        },
    )
    print(result.message, flush=True)
    if result.x is None:
        return
    values = np.rint(result.x).astype(int).tolist()
    actual_degree = verify(values, n, degree)
    coefficients = polynomial_coefficients(values, n)
    certificate = {
        "n": n,
        "degree": actual_degree,
        "sensitivity_at_zero": n,
        "truth_table": values,
        "nonzero_monomials": [
            {
                "variables": [i + 1 for i in range(n) if mask & (1 << i)],
                "coefficient": coefficient,
            }
            for mask, coefficient in enumerate(coefficients)
            if coefficient
        ],
    }
    output.write_text(json.dumps(certificate, indent=2) + "\n")
    print(
        f"verified feasible certificate: degree={actual_degree}, "
        f"monomials={len(certificate['nonzero_monomials'])}, output={output}",
        flush=True,
    )


def search_coefficients(n: int, degree: int, time_limit: float, output: Path) -> None:
    """Amano's smaller integer-coefficient formulation (IP (7) in his paper)."""
    masks = monomial_masks(n, degree)
    variable_count = len(masks)
    lower = np.empty(variable_count)
    upper = np.empty(variable_count)
    # Bounds use the fixed values f(0)=0 and f(e_i)=1.  Bounds in degrees
    # 4 and 5 are the exact extrema if all other lower-face values vary freely.
    bounds_by_size = {
        0: (0, 0),
        1: (1, 1),
        2: (-2, -1),
        3: (0, 4),
        4: (-8, 3),
        5: (-10, 16),
    }
    for column, mask in enumerate(masks):
        size = mask.bit_count()
        if size in bounds_by_size:
            low, high = bounds_by_size[size]
        else:
            low, high = -(1 << (size - 1)), 1 << (size - 1)
        lower[column] = low
        upper[column] = high

    evaluations = zeta_evaluation_matrix(n, degree, masks)
    ordered_degrees = coefficient_degree_order_matrix(n, masks)
    constraints = LinearConstraint(
        vstack([evaluations, ordered_degrees], format="csr"),
        np.concatenate([np.zeros(1 << n), np.zeros(n - 1)]),
        np.concatenate([np.ones(1 << n), np.full(n - 1, np.inf)]),
    )
    print(
        f"n={n} d<={degree}: {variable_count} bounded-integer coefficients, "
        f"{1 << n} Boolean-value constraints, {evaluations.nnz} evaluation nonzeros",
        flush=True,
    )
    result = milp(
        c=np.zeros(variable_count),
        integrality=np.ones(variable_count, dtype=np.uint8),
        bounds=Bounds(lower, upper),
        constraints=constraints,
        options={
            "disp": True,
            "presolve": True,
            "time_limit": time_limit,
            "mip_rel_gap": 0.0,
        },
    )
    print(result.message, flush=True)
    if result.x is None:
        return
    low_degree_coefficients = np.rint(result.x).astype(int).tolist()
    coefficients = [0] * (1 << n)
    for mask, coefficient in zip(masks, low_degree_coefficients, strict=True):
        coefficients[mask] = coefficient
    values = [
        sum(coefficients[submask] for submask in subsets(assignment))
        for assignment in range(1 << n)
    ]
    actual_degree = verify(values, n, degree)
    certificate = {
        "n": n,
        "degree": actual_degree,
        "sensitivity_at_zero": n,
        "truth_table": values,
        "nonzero_monomials": [
            {
                "variables": [i + 1 for i in range(n) if mask & (1 << i)],
                "coefficient": coefficient,
            }
            for mask, coefficient in enumerate(coefficients)
            if coefficient
        ],
    }
    output.write_text(json.dumps(certificate, indent=2) + "\n")
    print(
        f"verified feasible certificate: degree={actual_degree}, "
        f"monomials={len(certificate['nonzero_monomials'])}, output={output}",
        flush=True,
    )


def search_low_values(
    n: int,
    degree: int,
    time_limit: float,
    output: Path,
    max_zero_degree: int | None,
) -> None:
    """Binary formulation using only truth values of Hamming weight at most d."""
    masks = monomial_masks(n, degree)
    variable_count = len(masks)
    lower = np.zeros(variable_count)
    upper = np.ones(variable_count)
    column_of = {mask: column for column, mask in enumerate(masks)}
    upper[column_of[0]] = 0
    for bit in range(n):
        lower[column_of[1 << bit]] = 1

    if max_zero_degree is not None:
        if not 0 <= max_zero_degree <= 7:
            raise ValueError("--max-zero-degree must be between 0 and 7")
        if (n, degree) != (14, 5):
            raise ValueError("the zero-pair branches are certified only for n=14,d=5")
        # Relabel a maximum-degree zero-graph vertex as 0 and its neighbors as
        # 1,...,max_zero_degree.  Pair values are one off those zero edges.
        for j in range(1, n):
            column = column_of[1 | (1 << j)]
            if j <= max_zero_degree:
                upper[column] = 0
            else:
                lower[column] = 1

    extension = low_value_extension_matrix(n, degree, masks)
    matrices = [extension]
    lower_constraints = [np.zeros(extension.shape[0])]
    upper_constraints = [np.ones(extension.shape[0])]

    if (n, degree) == (14, 5):
        # Exact layer-average interpolation at t=2, using nodes
        # 0,1,5,9,13,14, gives q(2)>=11/12.  Hence at least 84 of the
        # C(14,2)=91 pair values are one.  See degree_sensitivity_pair_bound.py.
        pair_layer = pair_layer_matrix(n, masks)
        matrices.append(pair_layer)
        lower_constraints.append(np.asarray([84.0]))
        upper_constraints.append(np.asarray([np.inf]))

    if max_zero_degree is None:
        # Pair values themselves define the graph used for the safe degree-order
        # symmetry break, so coefficient_degree_order_matrix also has the right
        # incidence matrix here (the constant shift from coefficients cancels).
        symmetry = coefficient_degree_order_matrix(n, masks)
    else:
        symmetry = max_zero_degree_matrix(n, masks)
    matrices.append(symmetry)
    lower_constraints.append(np.zeros(n - 1))
    upper_constraints.append(np.full(n - 1, np.inf))

    constraints = LinearConstraint(
        vstack(matrices, format="csr"),
        np.concatenate(lower_constraints),
        np.concatenate(upper_constraints),
    )
    print(
        f"n={n} d<={degree}: {variable_count} low-weight binary values, "
        f"{extension.shape[0]} extension constraints, {extension.nnz} interpolation nonzeros",
        flush=True,
    )
    if max_zero_degree is not None:
        print(f"zero-pair maximum-degree branch: {max_zero_degree}", flush=True)
    result = milp(
        c=np.zeros(variable_count),
        integrality=np.ones(variable_count, dtype=np.uint8),
        bounds=Bounds(lower, upper),
        constraints=constraints,
        options={
            "disp": True,
            "presolve": True,
            "time_limit": time_limit,
            "mip_rel_gap": 0.0,
        },
    )
    print(result.message, flush=True)
    if result.x is None:
        return
    low_values = np.rint(result.x).astype(int).tolist()
    values = [0] * (1 << n)
    for mask, value in zip(masks, low_values, strict=True):
        values[mask] = value
    extended_values = extension @ np.asarray(low_values, dtype=np.int64)
    row = 0
    for mask in range(1 << n):
        if mask.bit_count() > degree:
            values[mask] = int(extended_values[row])
            row += 1
    actual_degree = verify(values, n, degree)
    coefficients = polynomial_coefficients(values, n)
    certificate = {
        "n": n,
        "degree": actual_degree,
        "sensitivity_at_zero": n,
        "truth_table": values,
        "nonzero_monomials": [
            {
                "variables": [i + 1 for i in range(n) if mask & (1 << i)],
                "coefficient": coefficient,
            }
            for mask, coefficient in enumerate(coefficients)
            if coefficient
        ],
    }
    output.write_text(json.dumps(certificate, indent=2) + "\n")
    print(
        f"verified feasible certificate: degree={actual_degree}, "
        f"monomials={len(certificate['nonzero_monomials'])}, output={output}",
        flush=True,
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--n", type=int, default=14)
    parser.add_argument("--degree", type=int, default=5)
    parser.add_argument("--time-limit", type=float, default=600.0)
    parser.add_argument(
        "--formulation",
        choices=("low-values", "coefficients", "truth-table"),
        default="low-values",
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=Path(__file__).with_name("degree_sensitivity_certificate.json"),
    )
    parser.add_argument(
        "--max-zero-degree",
        type=int,
        default=None,
        help="n=14,d=5 only: branch on maximum degree 0..7 of zero-pair graph",
    )
    args = parser.parse_args()
    assert 1 < args.degree < args.n
    assert comb(args.n, 1) > args.degree ** (np.log(6) / np.log(3))
    if args.formulation == "low-values":
        search_low_values(
            args.n,
            args.degree,
            args.time_limit,
            args.output,
            args.max_zero_degree,
        )
    elif args.formulation == "coefficients":
        search_coefficients(args.n, args.degree, args.time_limit, args.output)
    else:
        search_truth_table(args.n, args.degree, args.time_limit, args.output)


if __name__ == "__main__":
    main()
