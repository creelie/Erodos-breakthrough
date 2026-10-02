"""Check every base-2 witness n = 3511^2 * m listed in witness_m_values.txt.

For each m the script confirms that m is squarefree and prime to 3511, so that the
largest prime exponent of n is 2, and that 2^n is congruent to 4 modulo n.
Requires sympy for factoring.
"""
from sympy import factorint

P2 = 3511 ** 2
with open("witness_m_values.txt") as f:
    ms = [int(line) for line in f if line.strip()]

for i, m in enumerate(ms, 1):
    n = P2 * m
    fac = factorint(m)
    assert all(e == 1 for e in fac.values()), m
    assert m % 3511 != 0, m
    assert n % 2 == 1 and pow(2, n, n) == 4, m
    print(f"{i:2d}  n = {n}  m = {' * '.join(map(str, sorted(fac)))}")

print(f"all {len(ms)} witnesses verified")
