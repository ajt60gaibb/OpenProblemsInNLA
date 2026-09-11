"""Small-order, arbitrary-precision permanent routines; Python standard library only."""
from pathlib import Path
from typing import Sequence

Matrix = list[list[int]]

def read_matrix(path: str | Path) -> tuple[Matrix, int]:
    tokens = Path(path).read_text(encoding="utf-8").split()
    if len(tokens) < 2:
        raise ValueError("Expected an order, a claimed permanent, and square matrix entries")
    n, claim = map(int, tokens[:2])
    if n < 1 or len(tokens) != 2 + n * n:
        raise ValueError("Invalid order or number of matrix entries")
    flat = list(map(int, tokens[2:]))
    if any(x not in (-1, 1) for x in flat):
        raise ValueError("Every entry must be +1 or -1")
    return [flat[i*n:(i+1)*n] for i in range(n)], claim

def permanent(a: Sequence[Sequence[int]]) -> int:
    """Subset dynamic program, O(n*2**n) arithmetic operations; exact Python ints."""
    n = len(a)
    if any(len(row) != n for row in a):
        raise ValueError("The matrix must be square")
    d = [0] * (1 << n)
    d[0] = 1
    for mask in range(1, 1 << n):
        i = mask.bit_count() - 1
        remaining = mask
        value = 0
        while remaining:
            bit = remaining & -remaining
            remaining -= bit
            value += a[i][bit.bit_length() - 1] * d[mask ^ bit]
        d[mask] = value
    return d[-1]

def write_matrix(path: str | Path, a: Sequence[Sequence[int]], claim: int) -> None:
    Path(path).write_text(
        f"{len(a)} {claim}\n" + "".join(" ".join(map(str, row)) + "\n" for row in a),
        encoding="utf-8",
    )

def read_witnesses(path: str | Path) -> dict[int, Matrix]:
    result = {}
    for line_number, line in enumerate(Path(path).read_text().splitlines(), 1):
        fields = line.split()
        if not fields:
            continue
        value = int(fields[0])
        n = len(fields) - 1
        if any(len(row) != n or set(row) - {"+", "-"} for row in fields[1:]):
            raise ValueError(f"Invalid witness on line {line_number}")
        if value in result:
            raise ValueError(f"Duplicate value on line {line_number}")
        result[value] = [[1 if x == "+" else -1 for x in row] for row in fields[1:]]
    return result
