import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.Multiplicity
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Simproc.Factors

/-!
# Ordowski's congruences for the largest prime exponent

For a positive integer `n` let `a n` be the largest exponent in the prime factorization of `n`
(OEIS A051903). In December 2019 Thomas Ordowski asked two questions about odd `n` with
`a n > 1`:

* is there such an `n` with `b ^ n ≡ b ^ (a n) (mod n)` for every integer `b`?
* is there such an `n` with `2 ^ n ≡ 2 ^ (a n) (mod n)`?

Both questions appear as `OeisA51903.conjecture2` and `OeisA51903.conjecture3` in the
Formal Conjectures repository, with the definition of `a` copied verbatim below.

We answer the first question negatively (`conjecture2`) and the second positively
(`conjecture3`). The negative answer rests on a lifting-the-exponent bound
(`le_padicValNat_of_modEq`): any prime `p` that attains the largest exponent of a witness for
the base `b` must be a base-`b` Wieferich prime (`wieferich_of_modEq`). The base `p + 1`
is never Wieferich at `p`, which rules out a witness for every base at once.

The witness for the base `2` is `n = 3511 ^ 2 * 7 * 631 * 881 * 201961`.
Every check below is carried out by the Lean kernel; no `native_decide` is used.
-/

namespace OeisA51903

/-- Maximum exponent in the prime factorization of `n` (as in Formal Conjectures). -/
def a (n : ℕ) : ℕ :=
  (n.primeFactorsList.map (n.primeFactorsList.count ·)).foldr max 0

/-! ### The largest exponent is attained -/

lemma foldr_max_mem (L : List ℕ) : L.foldr max 0 = 0 ∨ L.foldr max 0 ∈ L := by
  induction L with
  | nil => simp
  | cons x L ih =>
    simp only [List.foldr_cons, List.mem_cons]
    rcases le_total x (L.foldr max 0) with h | h
    · rw [max_eq_right h]
      rcases ih with h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inr h')
    · rw [max_eq_left h]
      exact Or.inr (Or.inl rfl)

/-- If `a n ≠ 0`, some prime `p` satisfies `p ^ a n ∣ n`. -/
lemma exists_prime_pow_a_dvd {n : ℕ} (h : a n ≠ 0) : ∃ p, p.Prime ∧ p ^ a n ∣ n := by
  rcases foldr_max_mem (n.primeFactorsList.map (n.primeFactorsList.count ·)) with h0 | hmem
  · exact absurd h0 h
  · obtain ⟨p, hp, hpc⟩ := List.mem_map.mp hmem
    refine ⟨p, Nat.prime_of_mem_primeFactorsList hp, ?_⟩
    have ha : a n = n.factorization p := by
      rw [← Nat.primeFactorsList_count_eq]
      exact hpc.symm
    rw [ha]
    exact Nat.ordProj_dvd n p

/-! ### Lifting the exponent -/

/-- **Main inequality.** Let `p` be an odd prime not dividing `b > 1`, and let `p ^ E ∣ n` with
`n > 0`. If `b ^ n ≡ b ^ E (mod p ^ E)`, then `E ≤ v_p(b ^ (p - 1) - 1) + v_p(n - E)`. -/
theorem le_padicValNat_of_modEq {p b n E : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hb : ¬p ∣ b)
    (hb1 : 1 < b) (hn : 0 < n) (hpn : p ^ E ∣ n) (h : b ^ n ≡ b ^ E [MOD p ^ E]) :
    E ≤ padicValNat p (b ^ (p - 1) - 1) + padicValNat p (n - E) := by
  have := Fact.mk hp
  have hEn : E < n := lt_of_lt_of_le (Nat.lt_pow_self hp.one_lt) (Nat.le_of_dvd hn hpn)
  -- cancel `b ^ E`
  have h1 : b ^ (n - E) ≡ 1 [MOD p ^ E] := by
    have hcop : Nat.gcd (p ^ E) (b ^ E) = 1 :=
      ((hp.coprime_pow_of_not_dvd (m := E) hb).pow_left E).symm
    apply Nat.ModEq.cancel_left_of_coprime hcop
    rw [mul_one, ← pow_add, Nat.add_sub_cancel' hEn.le]
    exact h
  -- raise to the power `p - 1`
  have h2 : (b ^ (p - 1)) ^ (n - E) ≡ 1 [MOD p ^ E] := by
    rw [← pow_mul, mul_comm, pow_mul]
    simpa using h1.pow (p - 1)
  have hx1 : 1 < b ^ (p - 1) := one_lt_pow₀ hb1 (by have := hp.two_le; omega)
  have hdvd : p ^ E ∣ (b ^ (p - 1)) ^ (n - E) - 1 :=
    (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by omega))).mp h2.symm
  have hfermat : p ∣ b ^ (p - 1) - 1 := by
    have := Nat.ModEq.pow_totient (hp.coprime_iff_not_dvd.mpr hb).symm
    rw [Nat.totient_prime hp] at this
    exact (Nat.modEq_iff_dvd' hx1.le).mp this.symm
  have hlte := padicValNat.pow_sub_pow (p := p) (hp.odd_of_ne_two hp2) (y := 1) hx1
    (by simpa using hfermat) (fun hd => hb (hp.dvd_of_dvd_pow hd)) (n := n - E) (by omega)
  rw [one_pow] at hlte
  have hne : (b ^ (p - 1)) ^ (n - E) - 1 ≠ 0 := by
    have : 1 < (b ^ (p - 1)) ^ (n - E) := one_lt_pow₀ hx1 (by omega)
    omega
  rw [padicValNat_dvd_iff_le hne, hlte] at hdvd
  exact hdvd

lemma two_mul_add_one_le_three_pow (k : ℕ) : 2 * k + 1 ≤ 3 ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ]; omega

/-- **Wieferich criterion.** If an odd prime `p` attains an exponent `E ≥ 2` in `n > 0` and
`b ^ n ≡ b ^ E (mod p ^ E)`, then `p` is a base-`b` Wieferich prime: `p ^ 2 ∣ b ^ (p - 1) - 1`. -/
theorem wieferich_of_modEq {p b n E : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hb : ¬p ∣ b)
    (hE : 2 ≤ E) (hn : 0 < n) (hpn : p ^ E ∣ n) (h : b ^ n ≡ b ^ E [MOD p ^ E]) :
    p ^ 2 ∣ b ^ (p - 1) - 1 := by
  have := Fact.mk hp
  rcases Nat.lt_or_ge 1 b with hb1 | hb1
  swap
  · interval_cases b
    · exact absurd (dvd_zero p) hb
    · simp
  by_contra hW
  have hx1 : 1 < b ^ (p - 1) := one_lt_pow₀ hb1 (by have := hp.two_le; omega)
  have hw : padicValNat p (b ^ (p - 1) - 1) ≤ 1 := by
    by_contra hw
    exact hW ((padicValNat_dvd_iff_le (by omega)).mpr (by omega))
  have hEn : E < n := lt_of_lt_of_le (Nat.lt_pow_self hp.one_lt) (Nat.le_of_dvd hn hpn)
  have key := le_padicValNat_of_modEq hp hp2 hb hb1 hn hpn h
  -- `p ^ (E - 1)` divides both `n - E` and `n`, hence `E`
  have hd1 : p ^ (E - 1) ∣ n - E :=
    (padicValNat_dvd_iff_le (by omega)).mpr (by omega)
  have hd2 : p ^ (E - 1) ∣ n := (pow_dvd_pow p (by omega)).trans hpn
  have hd : p ^ (E - 1) ∣ E := by
    have := Nat.dvd_sub hd2 hd1
    rwa [Nat.sub_sub_self hEn.le] at this
  have hle : p ^ (E - 1) ≤ E := Nat.le_of_dvd (by omega) hd
  have h3 : 3 ^ (E - 1) ≤ p ^ (E - 1) :=
    Nat.pow_le_pow_left (by have := hp.two_le; omega) _
  have := two_mul_add_one_le_three_pow (E - 1)
  omega

/-- For an odd prime `p`, the base `p + 1` is not Wieferich at `p`. -/
lemma not_wieferich_succ {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ¬p ^ 2 ∣ (p + 1) ^ (p - 1) - 1 := by
  have := Fact.mk hp
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hpb : ¬p ∣ p + 1 := by
    intro hd
    have := (Nat.dvd_add_right (dvd_refl p)).mp hd
    exact hp.one_lt.ne' (Nat.dvd_one.mp this)
  have hv := padicValNat.pow_sub_pow (p := p) (hp.odd_of_ne_two hp2) (x := p + 1) (y := 1)
    (by omega) (by simp) hpb (n := p - 1) (by omega)
  have h0 : padicValNat p (p - 1) = 0 :=
    padicValNat.eq_zero_of_not_dvd fun hd => by
      have := Nat.le_of_dvd (by omega) hd
      omega
  rw [one_pow, Nat.add_sub_cancel, padicValNat_self, h0] at hv
  have hne : (p + 1) ^ (p - 1) - 1 ≠ 0 := by
    have : 1 < (p + 1) ^ (p - 1) := one_lt_pow₀ (by omega) (by omega)
    omega
  rw [padicValNat_dvd_iff_le hne, hv]
  omega

/-! ### Ordowski's first question: no odd `n` works for every base -/

/-- There is no odd `n` with `a n > 1` and `b ^ n ≡ b ^ (a n) (mod n)` for every `b`. -/
theorem not_exists_all_bases :
    ¬∃ n : ℕ, Odd n ∧ 1 < a n ∧ ∀ b : ℕ, b ^ n ≡ b ^ (a n) [MOD n] := by
  rintro ⟨n, hodd, ha, hall⟩
  obtain ⟨p, hp, hpn⟩ := exists_prime_pow_a_dvd (n := n) (by omega)
  have hp2 : p ≠ 2 := by
    rintro rfl
    have h2 : 2 ∣ n := (dvd_pow_self 2 (by omega : a n ≠ 0)).trans hpn
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)
  have hpb : ¬p ∣ p + 1 := by
    intro hd
    have := (Nat.dvd_add_right (dvd_refl p)).mp hd
    exact hp.one_lt.ne' (Nat.dvd_one.mp this)
  exact not_wieferich_succ hp hp2
    (wieferich_of_modEq hp hp2 hpb (by omega) hodd.pos hpn ((hall (p + 1)).of_dvd hpn))

/-- `OeisA51903.conjecture2` with the answer filled in: the answer is **no**. -/
theorem conjecture2 :
    False ↔ ∃ n : ℕ, Odd n ∧ 1 < a n ∧ ∀ b : ℕ, b ^ n ≡ b ^ (a n) [MOD n] :=
  ⟨False.elim, fun h => not_exists_all_bases h⟩

/-! ### Fast modular exponentiation, verified -/

/-- Binary modular exponentiation `b ^ e % m`, with fuel `k` (enough when `e < 2 ^ k`). -/
def powModAux : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, _, m => 1 % m
  | k + 1, b, e, m =>
    if e % 2 = 1 then b * powModAux k (b * b % m) (e / 2) m % m
    else powModAux k (b * b % m) (e / 2) m

theorem powModAux_eq (m : ℕ) : ∀ k b e, e < 2 ^ k → powModAux k b e m = b ^ e % m
  | 0, b, e, h => by
    have he : e = 0 := by simpa using h
    simp [powModAux, he]
  | k + 1, b, e, h => by
    have he : e / 2 < 2 ^ k := by rw [pow_succ] at h; omega
    have ih := powModAux_eq m k (b * b % m) (e / 2) he
    have hsplit : b ^ e = (b * b) ^ (e / 2) * b ^ (e % 2) := by
      conv_lhs => rw [← Nat.div_add_mod e 2]
      rw [pow_add, pow_mul, sq]
    have hmod : (b * b % m) ^ (e / 2) % m = (b * b) ^ (e / 2) % m := (Nat.pow_mod _ _ _).symm
    simp only [powModAux, ih, hmod]
    rw [hsplit]
    split_ifs with hodd
    · rw [hodd, pow_one, Nat.mul_mod_mod, mul_comm]
    · have : e % 2 = 0 := by omega
      rw [this, pow_zero, mul_one]

/-! ### Ordowski's second question: a witness for the base `2` -/

/-- The witness `n = 3511 ^ 2 * 7 * 631 * 881 * 201961`. -/
def witness : ℕ := 9687963167864344937

lemma witness_eq : witness = 3511 ^ 2 * 7 * 631 * 881 * 201961 := by norm_num [witness]

lemma primeFactorsList_witness :
    witness.primeFactorsList = [7, 631, 881, 3511, 3511, 201961] := by
  simp only [witness, Nat.primeFactorsList_ofNat]

lemma a_witness : a witness = 2 := by
  rw [a, primeFactorsList_witness]
  decide

lemma odd_witness : Odd witness := by decide

lemma two_pow_witness : 2 ^ witness % witness = 4 := by
  rw [← powModAux_eq witness 64 2 witness (by norm_num [witness])]
  decide +kernel

/-- There is an odd `n` with `a n > 1` and `2 ^ n ≡ 2 ^ (a n) (mod n)`. -/
theorem exists_base_two :
    ∃ n : ℕ, Odd n ∧ 1 < a n ∧ 2 ^ n ≡ 2 ^ (a n) [MOD n] := by
  refine ⟨witness, odd_witness, by rw [a_witness]; norm_num, ?_⟩
  rw [a_witness]
  show 2 ^ witness % witness = 2 ^ 2 % witness
  rw [two_pow_witness]
  norm_num [witness]

/-- `OeisA51903.conjecture3` with the answer filled in: the answer is **yes**. -/
theorem conjecture3 : True ↔ ∃ n : ℕ, Odd n ∧ 1 < a n ∧ 2 ^ n ≡ 2 ^ (a n) [MOD n] :=
  ⟨fun _ => exists_base_two, fun _ => trivial⟩

/-! ### Shape of the base-2 witnesses -/

/-- Every prime attaining the largest exponent of a base-2 witness is a Wieferich prime. -/
theorem base_two_wieferich {n p : ℕ} (hodd : Odd n) (ha : 1 < a n)
    (h : 2 ^ n ≡ 2 ^ (a n) [MOD n]) (hp : p.Prime) (hpn : p ^ a n ∣ n) :
    p ^ 2 ∣ 2 ^ (p - 1) - 1 := by
  have hp2 : p ≠ 2 := by
    rintro rfl
    have h2 : 2 ∣ n := (dvd_pow_self 2 (by omega : a n ≠ 0)).trans hpn
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)
  have hb : ¬p ∣ 2 := fun hd => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hd)
  exact wieferich_of_modEq hp hp2 hb (by omega) hodd.pos hpn (h.of_dvd hpn)

/-- If `n` is odd, `E ≤ n` is even and `2 ^ n ≡ 2 ^ E (mod n)`, then every prime factor `q`
of `n` satisfies `q ≡ ±1 (mod 8)`. -/
theorem prime_factor_mod_eight {n E q : ℕ} (hodd : Odd n) (hE : Even E) (hEn : E ≤ n)
    (h : 2 ^ n ≡ 2 ^ E [MOD n]) (hq : q.Prime) (hqn : q ∣ n) :
    q % 8 = 1 ∨ q % 8 = 7 := by
  have := Fact.mk hq
  have hq2 : q ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hqn)
  have hcop : Nat.gcd q (2 ^ E) = 1 :=
    Nat.Coprime.pow_right E ((Nat.coprime_primes hq Nat.prime_two).mpr hq2)
  -- `2 ^ (n - E) ≡ 1 (mod q)` with `n - E` odd
  have h1 : 2 ^ (n - E) ≡ 1 [MOD q] := by
    apply Nat.ModEq.cancel_left_of_coprime hcop
    rw [mul_one, ← pow_add, Nat.add_sub_cancel' hEn]
    exact h.of_dvd hqn
  obtain ⟨k, hk⟩ : Odd (n - E) := by
    rcases hodd with ⟨r, hr⟩
    rcases hE with ⟨s, hs⟩
    exact ⟨r - s, by omega⟩
  -- so `2 = (2 ^ (k + 1)) ^ 2` in `ZMod q`
  have hsq : IsSquare (2 : ZMod q) := by
    refine ⟨(2 : ZMod q) ^ (k + 1), ?_⟩
    have h2 := (ZMod.natCast_eq_natCast_iff _ _ _).mpr (h1.mul_left 2)
    push_cast at h2
    rw [hk, ← pow_succ', show 2 * k + 1 + 1 = (k + 1) + (k + 1) by ring, pow_add] at h2
    exact h2.symm
  exact (ZMod.exists_sq_eq_two_iff hq2).mp hsq

end OeisA51903
