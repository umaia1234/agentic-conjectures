#!/usr/bin/env python3
"""Independent finite checks for the proved OEIS A397621 identity.

The proof is algebraic.  This certificate checks it with both Berlekamp--
Massey and a separately implemented exhaustive GF(2) linear-system test.
"""

from __future__ import annotations


def pascal_word(n: int) -> list[int]:
    """Coefficients of (1+x)^n over GF(2), in MSB-first order."""
    polynomial = 1
    for j in range(n.bit_length()):
        if (n >> j) & 1:
            polynomial ^= polynomial << (1 << j)
    return [(polynomial >> i) & 1 for i in range(n, -1, -1)]


def berlekamp_massey(bits: list[int]) -> int:
    connection = [1]
    backup = [1]
    length = 0
    shift = 1
    for index in range(len(bits)):
        discrepancy = bits[index]
        for i in range(1, length + 1):
            if i < len(connection):
                discrepancy ^= connection[i] & bits[index - i]
        if not discrepancy:
            shift += 1
            continue
        old = connection[:]
        needed = len(backup) + shift
        connection += [0] * max(0, needed - len(connection))
        for i, bit in enumerate(backup):
            connection[i + shift] ^= bit
        if 2 * length <= index:
            length = index + 1 - length
            backup = old
            shift = 1
        else:
            shift += 1
    return length


def system_is_consistent(rows: list[int], variables: int) -> bool:
    pivot = 0
    for column in range(variables):
        hit = next(
            (i for i in range(pivot, len(rows)) if (rows[i] >> column) & 1),
            None,
        )
        if hit is None:
            continue
        rows[pivot], rows[hit] = rows[hit], rows[pivot]
        for i in range(pivot + 1, len(rows)):
            if (rows[i] >> column) & 1:
                rows[i] ^= rows[pivot]
        pivot += 1
    coefficient_mask = (1 << variables) - 1
    return all(
        (row & coefficient_mask) or not ((row >> variables) & 1)
        for row in rows
    )


def brute_linear_complexity(bits: list[int]) -> int:
    """Try every recurrence length, using GF(2) Gaussian elimination."""
    if not any(bits):
        return 0
    for length in range(1, len(bits) + 1):
        rows = []
        for i in range(length, len(bits)):
            row = sum(bits[i - j] << (j - 1) for j in range(1, length + 1))
            row |= bits[i] << length
            rows.append(row)
        if system_is_consistent(rows, length):
            return length
    raise AssertionError("no recurrence found")


def predicted(n: int) -> int:
    return (1 << n.bit_length()) - n


def check_explicit_connection(n: int) -> None:
    q = 1 << (n.bit_length() - 1)
    r = n - q
    degree = q - r
    s = list(reversed(pascal_word(n)))
    c = list(reversed(pascal_word(degree)))
    convolution = [0] * (len(s) + len(c) - 1)
    for i, left in enumerate(s):
        for j, right in enumerate(c):
            convolution[i + j] ^= left & right
    assert all(convolution[i] == 0 for i in range(degree, n + 1))
    assert s[q] == 1
    assert all(s[i] == 0 for i in range(r + 1, q))


def main() -> None:
    for n in range(1, 513):
        word = pascal_word(n)
        assert berlekamp_massey(word) == predicted(n)
        check_explicit_connection(n)

    for n in range(1, 81):
        word = pascal_word(n)
        assert brute_linear_complexity(word) == berlekamp_massey(word)

    boundary_values = [
        1000,
        1023,
        1024,
        1025,
        2047,
        2048,
        4095,
        4096,
        8191,
        8192,
        9999,
        10000,
    ]
    for n in boundary_values:
        assert berlekamp_massey(pascal_word(n)) == predicted(n)

    print("A397621 certificate: PASS")
    print("  Berlekamp--Massey: n=1..512 plus 12 boundary values")
    print("  independent GF(2) system solver: n=1..80")


if __name__ == "__main__":
    main()
