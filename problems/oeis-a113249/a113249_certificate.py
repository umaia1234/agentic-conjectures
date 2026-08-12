#!/usr/bin/env python3
"""Independent finite sanity checks for the OEIS A113249 Lean proof.

The complete all-parameter result is proved in Lean.  This script separately
implements the source fourth-order recurrence and the auxiliary second-order
recurrence, compares their odd subsequences on a deterministic grid, and
checks the published m=3 prefix from OEIS revision 29.
"""

from math import isqrt


OEIS_M3_PREFIX = [
    -1,
    4,
    11,
    1,
    59,
    484,
    -1009,
    6241,
    -2761,
    13924,
    87251,
    57121,
    49139,
    4072324,
    -7165609,
    35058241,
    10350959,
    30492484,
    559712411,
    973502401,
    -1957852501,
    30450948004,
    -41421000289,
    174055005601,
    241428053159,
    9658565284,
    2872244917091,
    11300885699041,
    -25300162140061,
]


def fourth_order_terms(m: int, count: int) -> list[int]:
    """Evaluate the recurrence exactly as stated on OEIS A113249."""
    if count <= 0:
        return []
    values = [
        -1,
        4,
        -13 + 6 * (m - 1) + 3 * (m - 1) ** 2,
        (-8 + m**2) ** 2,
    ]
    for n in range(4, count):
        values.append(
            m**4 * values[n - 4]
            + (2 * m) ** 2 * values[n - 3]
            - 4 * values[n - 1]
        )
    return values[:count]


def auxiliary_terms(m: int, count: int) -> list[int]:
    """Evaluate Y(0)=2, Y(1)=8-m^2, Y(n+2)=4Y(n+1)-m^2Y(n)."""
    if count <= 0:
        return []
    values = [2, 8 - m**2]
    for n in range(2, count):
        values.append(4 * values[n - 1] - m**2 * values[n - 2])
    return values[:count]


def main() -> None:
    assert fourth_order_terms(3, len(OEIS_M3_PREFIX)) == OEIS_M3_PREFIX

    parameter_min, parameter_max = -25, 25
    odd_indices = 41
    checked = 0
    for m in range(parameter_min, parameter_max + 1):
        direct = fourth_order_terms(m, 2 * odd_indices)
        auxiliary = auxiliary_terms(m, odd_indices)
        for n, root in enumerate(auxiliary):
            term = direct[2 * n + 1]
            assert term == root * root
            assert term >= 0 and isqrt(term) ** 2 == term
            checked += 1

    print(
        "PASS A113249: published m=3 prefix and "
        f"{checked} odd terms agree for {parameter_min} <= m <= {parameter_max}"
    )


if __name__ == "__main__":
    main()
