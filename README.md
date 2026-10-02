# Wieferich Primes in Ordowski's Congruences

Let `a(n)` be the largest exponent in the prime factorization of `n`
([OEIS A051903](https://oeis.org/A051903)). In December 2019 Thomas Ordowski asked:

* **(Q2)** Is there an odd `n` with `a(n) > 1` and `b^n ≡ b^a(n) (mod n)` for every `b`?
  (Equivalently `n ≡ a(n) (mod λ(n))`.)
* **(Q3)** Is there an odd `n` with `a(n) > 1` and `2^n ≡ 2^a(n) (mod n)`?

Both are stated in Lean in Google DeepMind's
[Formal Conjectures](https://github.com/google-deepmind/formal-conjectures) project as
`OeisA51903.conjecture2` and `OeisA51903.conjecture3`, marked open.

This repository answers both.

| Question | Answer | Lean theorem |
|---|---|---|
| (Q2) | **No.** If `p^a(n)` divides `n`, the base `p + 1` fails. | `OeisA51903.conjecture2` |
| (Q3) | **Yes.** The least witness is `n₀ = 7 · 631 · 881 · 3511² · 201961 = 9687963167864344937`. | `OeisA51903.conjecture3` |

The key step is a lifting-the-exponent bound: a prime that carries the largest exponent of a
witness for the base `b` must be a base-`b` Wieferich prime. For the base two this forces
`3511²` into every small witness. There are exactly 28 witnesses up to
`348634396442820771857`, and infinitely many in total.

## Contents

| Path | What it is |
|---|---|
| `paper/ordowski.pdf`, `paper/ordowski.tex` | The paper |
| `ErdosProofs/Ordowski.lean` | Lean 4 proofs (Mathlib v4.33.0), no `sorry`, no `native_decide` |
| `search/wief.c` | Lists the Wieferich primes below a bound (used up to 4.2·10⁹) |
| `search/least.c` | Exhaustive search for `m` with `n = 3511²·m` a witness (Montgomery arithmetic) |
| `search/least2.c` | Independent re-check of minimality (plain 128-bit arithmetic) |
| `search/construct_witness.py` | The residue construction that first produced a witness |
| `search/witness_m_values.txt`, `search/verify_witnesses.py` | The 28 witnesses and an exact check |

## What the Lean file proves

* `conjecture2 : False ↔ ∃ n, Odd n ∧ 1 < a n ∧ ∀ b, b ^ n ≡ b ^ (a n) [MOD n]`
* `conjecture3 : True ↔ ∃ n, Odd n ∧ 1 < a n ∧ 2 ^ n ≡ 2 ^ (a n) [MOD n]`
* `le_padicValNat_of_modEq`: `E ≤ v_p(b^(p-1) - 1) + v_p(n - E)` whenever `p^E ∣ n` and
  `b^n ≡ b^E (mod p^E)`, for an odd prime `p ∤ b`
* `wieferich_of_modEq`: under the same hypotheses with `E ≥ 2`, `p² ∣ b^(p-1) - 1`
* `base_two_wieferich`, `prime_factor_mod_eight`: the shape of base-two witnesses

The definition of `a` is copied verbatim from Formal Conjectures. The congruence
`2^n₀ ≡ 4 (mod n₀)` is evaluated by the Lean kernel through a verified binary modular
exponentiation, and the factorization of `n₀` is certified by Mathlib's `norm_num`.

The minimality of `n₀` and the list of 28 witnesses rest on the C searches in `search/`, not
on Lean.

## Building

```sh
lake exe cache get   # download prebuilt Mathlib
lake build
```

```sh
cd search
gcc -O3 -march=native -o wief wief.c -lm && ./wief 4200000000 1 0
gcc -O3 -march=native -o least least.c && ./least 785906390297 1 0
gcc -O3 -march=native -o least2 least2.c && ./least2 785906390297 1 0
python3 verify_witnesses.py
```

`least` and `least2` take `MMAX NTHREADS ID`; run one process per `ID` to split the work.

## License

Apache License 2.0. The definition of `a` comes from Formal Conjectures, which is also
licensed under Apache 2.0.
