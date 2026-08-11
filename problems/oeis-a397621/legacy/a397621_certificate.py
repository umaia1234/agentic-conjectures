"""Independent finite checks for the proved OEIS A397621 identity.

The proof itself is algebraic; this file checks the identity using both the
Berlekamp--Massey algorithm and an unrelated GF(2) linear-system solver.
"""


def pascal_word(n: int) -> list[int]:
    """Binary coefficients of (1+x)^n over GF(2), most significant first."""
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
    """Try every recurrence length, solving its equations by GF(2) elimination."""
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
    raise AssertionError("No recurrence found")


def predicted(n: int) -> int:
    return (1 << n.bit_length()) - n


for n in range(1, 513):
    assert berlekamp_massey(pascal_word(n)) == predicted(n)

for n in range(1, 81):
    word = pascal_word(n)
    assert brute_linear_complexity(word) == berlekamp_massey(word) == predicted(n)

for n in [1000, 1023, 1024, 1025, 2047, 2048, 4095, 4096, 8191, 8192, 9999, 10000]:
    assert berlekamp_massey(pascal_word(n)) == predicted(n)

print("A397621 certificate checks passed")
