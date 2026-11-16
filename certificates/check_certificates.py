"""Check the two certificates of the paper with exact rational arithmetic (Python 3, standard library only).

L5_fifteen_elevenths.txt: 189 weighted inequalities for five slices; their weighted sum gives r + s >= 15n/11.
L7_sixtyseven_fortyninths.txt: 77 weighted inequalities for seven slices, each the average of a base inequality over
all relabelings of the seven indices; their weighted sum gives r + s >= 67n/49. The script recomputes every averaged
row from its base inequality and compares it with L7_orbit_rows.txt.

Variables: f(S) and g(S) are dimensions of sums of column spaces (A_i, C_i) of the system and of the transposed
system, m[i,j] are the ranks of X_i Y_j^T, r and k (= s) the widths. Every inequality reads  <linear form> <= b  with
b in {0, -1}, where -1 stands for -n (n normalized to 1). For variables x >= 0, a weight vector mu >= 0 with
sum_i mu_i a_i + c >= 0 componentwise gives c.x >= -mu.b, where c.x = r + k.
"""

import re
import sys
from fractions import Fraction
from pathlib import Path

HERE = Path(__file__).resolve().parent


def parse_set(text: str) -> frozenset:
    if text in ("", "0"):
        return frozenset()
    return frozenset(
        (0 if tok[0] == "A" else 1, int(tok[1:])) for tok in text.split("+")
    )


def check(weights_rows, objective, bound) -> None:
    total: dict = {}
    for mu, row, b in weights_rows:
        if mu < 0:
            sys.exit(f"ERROR: negative weight {mu}")
        for var, a in row.items():
            total[var] = total.get(var, Fraction(0)) + mu * a
    for var, a in objective.items():
        total[var] = total.get(var, Fraction(0)) + a
    negative = {v: a for v, a in total.items() if a < 0}
    if negative:
        sys.exit(f"ERROR: negative reduced costs {negative}")
    rhs = sum(mu * b for mu, _, b in weights_rows)
    if rhs != -bound:
        sys.exit(f"ERROR: mu.b = {rhs}, expected {-bound}")


def five_slices() -> None:
    rows = []
    for line in (HERE / "L5_fifteen_elevenths.txt").read_text().splitlines():
        m = re.match(r"\s*(\S+) x \[ (.*) <= (\S+) \]", line)
        if not m:
            continue
        row: dict = {}
        for sign, coef, name, arg in re.findall(
            r"([+-])(\d+)\*(f|g|m)[\[(]([^\])]*)[\])]", m[2]
        ):
            key = (name, parse_set(arg)) if name in "fg" else ("m", arg)
            if key[0] in "fg" and not key[1]:
                continue
            row[key] = row.get(key, 0) + int(sign + coef)
        for sign, coef, name in re.findall(r"([+-])(\d+)\*(r|k)\b", m[2]):
            row[(name,)] = row.get((name,), 0) + int(sign + coef)
        rows.append((Fraction(m[1]), row, Fraction(m[3])))
    assert len(rows) == 189, len(rows)
    check(rows, {("r",): 1, ("k",): 1}, Fraction(15, 11))
    print("15n/11: 189 rows, weights >= 0, reduced costs >= 0, bound 15/11: OK")


L = 7
TYPES = [
    (a, c, b)
    for a in range(L + 1)
    for c in range(L + 1 - a)
    for b in range(L + 1 - a - c)
]
INDEX = {t: j for j, t in enumerate(TYPES)}


def type_of(S: frozenset) -> tuple:
    A = {y for s, y in S if s == 0}
    C = {y for s, y in S if s == 1}
    return (len(A - C), len(C - A), len(A & C))


def averaged(base: dict, offset: int) -> dict:
    """Average of a base inequality over all relabelings of the seven indices, in orbit-average coordinates.

    The relabelings act transitively on the sets of one type (a, c, b), so the average of f(sigma S) over all sigma is
    the average of f over the sets of the type of S."""
    out: dict = {}
    for S, a in base.items():
        j = INDEX[type_of(S)] + offset
        out[j] = out.get(j, Fraction(0)) + a
    return {j: a for j, a in out.items() if a != 0}


def seven_slices() -> None:
    orbit_rows = []
    for line in (HERE / "L7_orbit_rows.txt").read_text().splitlines():
        m = re.match(r"\s*(\S+) x \[ (.*) <= (\S+) \]", line)
        if m:
            row = {}
            for t in re.finditer(r"([+-]\d+)\*v(\d+)", m[2]):
                row[int(t[2])] = row.get(int(t[2]), 0) + int(t[1])
            orbit_rows.append((Fraction(m[1]), row, Fraction(m[3])))
    explained = [
        l
        for l in (HERE / "L7_sixtyseven_fortyninths.txt").read_text().splitlines()
        if l.strip()
    ]
    assert len(orbit_rows) == len(explained) == 77, (len(orbit_rows), len(explained))
    matched = 0
    for (mu, row, b), line in zip(orbit_rows, explained):
        parts = line.split()
        if Fraction(parts[0]) != mu:
            sys.exit(f"ERROR: weight mismatch in {line}")
        if parts[1] != "orbit":
            continue
        m = re.search(
            r"(submod|mono) (f|g)\((.*?)\)(?: \+ \2\((.*?)\))? (>=|<=) \2\((.*?)\)(?: \+ \2\((.*?)\))?\s+<= 0",
            line,
        )
        if not m:
            sys.exit(f"ERROR: cannot parse {line}")
        kind, fn = m[1], m[2]
        offset = 0 if fn == "f" else 120
        if kind == "submod":
            S, T, U, I = (parse_set(x) for x in (m[3], m[4], m[6], m[7]))
            if S | T != U or S & T != I:
                sys.exit(f"ERROR: not a submodularity instance: {line}")
            base = {}
            for X, a in ((U, 1), (I, 1), (S, -1), (T, -1)):
                base[X] = base.get(X, 0) + a
        else:
            S, T = parse_set(m[3]), parse_set(m[6])
            if not S < T:
                sys.exit(f"ERROR: not a monotonicity instance: {line}")
            base = {S: 1, T: -1}
        if (
            averaged(base, offset) != {j: Fraction(a) for j, a in row.items() if a != 0}
            or b != 0
        ):
            sys.exit(f"ERROR: averaged base row does not match orbit row: {line}")
        matched += 1
    check(orbit_rows, {241: 1, 242: 1}, Fraction(67, 49))
    if matched + 6 != 77:
        sys.exit(
            f"ERROR: {matched} averaged rows; expected 71 averaged rows and 6 explicit rows"
        )
    print(
        f"67n/49: 77 rows ({matched} averaged rows match their base inequalities, 6 explicit rows), "
        "weights >= 0, reduced costs >= 0, bound 67/49: OK"
    )


if __name__ == "__main__":
    five_slices()
    seven_slices()
