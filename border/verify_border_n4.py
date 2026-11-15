"""Check the border splitting of S_4 in border_n4.json with exact integer arithmetic.

U(t), V(t), G(t), H(t) are 16 x 3 integer matrices given by their coefficients of t^0, ..., t^3. With
B(t) = U(t) V(t)^T (rows (x, y), columns (u, v)) and C(t) defined by R(C(t)) = G(t) H(t)^T (rows (x, u),
columns (y, v)), the script checks that the coefficients of t^0, t^1, t^2 in B(t) + C(t) vanish and that the
coefficient of t^3 is c S_4, where S_4[(x, y), (u, v)] = [u = y][v = x].

Usage: python3 verify_border_n4.py [border_n4.json]
"""

import json
import sys
from pathlib import Path

N = 4
WIDTH = 3


def coefficient(data: dict, e: int) -> dict:
    """The coefficient of t^e in B(t) + C(t), as a dict over (x, y, u, v)."""
    tables = {name: {int(a): rows for a, rows in data[name].items()} for name in "UVGH"}
    pairs = [(x, y) for x in range(N) for y in range(N)]
    out = {}
    for x, y in pairs:
        for u, v in pairs:
            total = 0
            for a in range(e + 1):
                b = e - a
                if a in tables["U"] and b in tables["V"]:
                    total += sum(
                        tables["U"][a][N * x + y][i] * tables["V"][b][N * u + v][i]
                        for i in range(WIDTH)
                    )
                if a in tables["G"] and b in tables["H"]:
                    total += sum(
                        tables["G"][a][N * x + u][i] * tables["H"][b][N * y + v][i]
                        for i in range(WIDTH)
                    )
            out[(x, y, u, v)] = total
    return out


def main() -> None:
    path = Path(
        sys.argv[1] if len(sys.argv) > 1 else Path(__file__).with_name("border_n4.json")
    )
    data = json.loads(path.read_text())
    for name in "UVGH":
        for rows in data[name].values():
            if len(rows) != N * N or any(len(row) != WIDTH for row in rows):
                sys.exit(f"ERROR: table {name} is not 16 x 3.")
    c = data["c"]
    if c == 0:
        sys.exit("ERROR: c must be nonzero.")
    for e in range(3):
        if any(value != 0 for value in coefficient(data, e).values()):
            sys.exit(f"FAIL: the coefficient of t^{e} is not zero.")
    top = coefficient(data, 3)
    for (x, y, u, v), value in top.items():
        if value != (c if (u == y and v == x) else 0):
            sys.exit(
                f"FAIL: the coefficient of t^3 differs from c S_4 at ({x},{y}),({u},{v})."
            )
    print(
        f"OK: B(t) + C(t) = c t^3 S_4 + O(t^4) with c = {c}; rank B(t) <= 3 and rank R(C(t)) <= 3."
    )


if __name__ == "__main__":
    main()
