import FormalConjectures.OEIS.«103662»

-- Reduction OeisA103662.conjecture.variants.a_40.R1 of Smallest power with base>1 and exponent $n$ without digit 0 — a 40
-- Credit: @subham-n
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# A103662 at exponent 40: modular elimination + 2-adic split

Any base `b > 1` whose 40th power `b ^ 40` has no decimal digit `0` must satisfy `2 ∣ b` and
`¬ 5 ∣ b`. Indeed, `main` completely eliminates the other three `(mod 2, mod 5)` classes:

* `10 ∣ b`: `b ^ 40 ≡ 0 (mod 10)`, so the units digit is `0`.
* `¬ 2 ∣ b` and `¬ 5 ∣ b`: by Euler's theorem, `b ^ 40 ≡ 1 (mod 4)` and `b ^ 40 ≡ 1 (mod 25)`,
  hence `b ^ 40 ≡ 1 (mod 100)` with `b ^ 40 ≥ 2 ^ 40 ≥ 100`, so the tens digit is `0`.
* `¬ 2 ∣ b` and `5 ∣ b`: by Euler's theorem, `b ^ 40 ≡ 1 (mod 16)` while `5 ^ 4 = 625 ∣ b ^ 40`,
  hence `b ^ 40 ≡ 625 (mod 10000)` with `b ^ 40 ≥ 2 ^ 40 ≥ 10000`, so the thousands digit is `0`.

In the remaining class `2 ∣ b` and `¬ 5 ∣ b`, there is no 10-adic congruence obstruction (for every
`r`, infinitely many bases have zeroless last `r` digits of `b ^ 40`). Writing `b = 2 ^ k * m` with
`k ≥ 1`, `¬ 2 ∣ m`, `¬ 5 ∣ m` splits the genuinely open core into two distinct problems:

* `H1` (`m = 1`, pure powers of 2): `2 ^ (40 * k)` contains the digit `0` for all `k ≥ 1`. This is
  the `40 ∣ n` slice of Erdos's 86-conjecture (OEIS A007377), a one-parameter exponential problem.
* `H2` (`m > 1`, composite bases): `(2 ^ k * m) ^ 40` contains the digit `0` for all `k ≥ 1` and
  `m > 1` coprime to `10`.
-/

namespace OMA.R_OeisA103662_conjecture_variants_a_40_R1

open OeisA103662

/-- Pure powers of 2 (`b = 2 ^ k`, `k ≥ 1`): every power `2 ^ (40 * k)` contains the digit `0`
in base 10 (the `40 ∣ n` slice of the 86-conjecture, OEIS A007377). -/
def H1 : Prop :=
  ∀ k : ℕ, 1 ≤ k → 0 ∈ Nat.digits 10 (2 ^ (40 * k))

/-- Even bases coprime to 5 having an odd prime factor other than 5 (`b = 2 ^ k * m` with
`k ≥ 1`, `m > 1`, `¬ 2 ∣ m`, `¬ 5 ∣ m`): `(2 ^ k * m) ^ 40` contains the digit `0` in base 10. -/
def H2 : Prop :=
  ∀ k m : ℕ, 1 ≤ k → 1 < m → ¬ (2 ∣ m) → ¬ (5 ∣ m) →
    0 ∈ Nat.digits 10 ((2 ^ k * m) ^ 40)

lemma zero_mem_digits_of_div_mod_zero {n k : ℕ}
    (hpos : 0 < n / 10 ^ k) (hdig : (n / 10 ^ k) % 10 = 0) :
    0 ∈ Nat.digits 10 n := by
  induction k generalizing n with
  | zero =>
    simp only [pow_zero, Nat.div_one] at hpos hdig
    rw [Nat.digits_def' (by decide) hpos]
    simp [hdig]
  | succ k ih =>
    have hdiv : n / 10 ^ (k + 1) = (n / 10) / 10 ^ k := by
      rw [pow_succ', ← Nat.div_div_eq_div_mul]
    rw [hdiv] at hpos hdig
    have hn_pos : 0 < n := by
      by_contra h
      have hn0 : n = 0 := by omega
      subst hn0
      simp at hpos
    rw [Nat.digits_def' (by decide) hn_pos]
    exact List.mem_cons_of_mem _ (ih hpos hdig)

lemma pow_40_mod_16_of_odd {b : ℕ} (h2 : ¬ (2 ∣ b)) : b ^ 40 % 16 = 1 := by
  have hcop : Nat.Coprime b 16 := by
    have h2cop : Nat.Coprime b 2 :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 h2 |>.symm
    have hpow : Nat.Coprime b (2 ^ 4) := h2cop.pow_right 4
    simpa using hpow
  have heuler : b ^ 8 ≡ 1 [MOD 16] := by
    have h := Nat.ModEq.pow_totient hcop
    have htot : Nat.totient 16 = 8 := by decide
    rwa [htot] at h
  have h40 : b ^ 40 ≡ 1 [MOD 16] := by
    have hpow := heuler.pow 5
    rw [← pow_mul, one_pow] at hpow
    exact hpow
  simpa [Nat.ModEq] using h40

lemma pow_40_mod_25_of_not_dvd_five {b : ℕ} (h5 : ¬ (5 ∣ b)) : b ^ 40 % 25 = 1 := by
  have hcop : Nat.Coprime b 25 := by
    have h5cop : Nat.Coprime b 5 :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_five).2 h5 |>.symm
    have hpow : Nat.Coprime b (5 ^ 2) := h5cop.pow_right 2
    simpa using hpow
  have heuler : b ^ 20 ≡ 1 [MOD 25] := by
    have h := Nat.ModEq.pow_totient hcop
    have htot : Nat.totient 25 = 20 := by decide
    rwa [htot] at h
  have h40 : b ^ 40 ≡ 1 [MOD 25] := by
    have hpow := heuler.pow 2
    rw [← pow_mul, one_pow] at hpow
    exact hpow
  simpa [Nat.ModEq] using h40

lemma zero_mem_digits_of_dvd_two_and_five {b : ℕ} (hb : 1 < b)
    (h2 : 2 ∣ b) (h5 : 5 ∣ b) : 0 ∈ Nat.digits 10 (b ^ 40) := by
  have h10 : 10 ∣ b := by omega
  have h10pow : 10 ∣ b ^ 40 := dvd_pow h10 (by decide)
  have hpos : 0 < b ^ 40 := by positivity
  refine zero_mem_digits_of_div_mod_zero (k := 0) ?_ ?_
  · simpa using hpos
  · simpa using Nat.mod_eq_zero_of_dvd h10pow

lemma zero_mem_digits_of_odd_not_dvd_five {b : ℕ} (hb : 1 < b)
    (h2 : ¬ (2 ∣ b)) (h5 : ¬ (5 ∣ b)) : 0 ∈ Nat.digits 10 (b ^ 40) := by
  have h16 : b ^ 40 % 16 = 1 := pow_40_mod_16_of_odd h2
  have h25 : b ^ 40 % 25 = 1 := pow_40_mod_25_of_not_dvd_five h5
  have h100 : b ^ 40 % 100 = 1 := by omega
  have hge : 100 ≤ b ^ 40 := by
    calc
      100 ≤ 2 ^ 40 := by decide
      _ ≤ b ^ 40 := Nat.pow_le_pow_left (by omega) 40
  refine zero_mem_digits_of_div_mod_zero (k := 1) ?_ ?_
  · omega
  · omega

lemma zero_mem_digits_of_odd_dvd_five {b : ℕ} (hb : 1 < b)
    (h2 : ¬ (2 ∣ b)) (h5 : 5 ∣ b) : 0 ∈ Nat.digits 10 (b ^ 40) := by
  have h16 : b ^ 40 % 16 = 1 := pow_40_mod_16_of_odd h2
  have h625_dvd : 625 ∣ b ^ 40 := by
    have h4 : 5 ^ 4 ∣ b ^ 4 := pow_dvd_pow_of_dvd h5 4
    have h40 : b ^ 4 ∣ b ^ 40 := pow_dvd_pow b (by decide)
    exact dvd_trans h4 h40
  have h625 : b ^ 40 % 625 = 0 := Nat.mod_eq_zero_of_dvd h625_dvd
  have h10000 : b ^ 40 % 10000 = 625 := by omega
  have hge : 10000 ≤ b ^ 40 := by
    calc
      10000 ≤ 2 ^ 40 := by decide
      _ ≤ b ^ 40 := Nat.pow_le_pow_left (by omega) 40
  refine zero_mem_digits_of_div_mod_zero (k := 3) ?_ ?_
  · omega
  · omega

lemma exists_two_adic_split : ∀ b : ℕ, 0 < b → 2 ∣ b → ¬ (5 ∣ b) →
    ∃ k m : ℕ, 1 ≤ k ∧ 1 ≤ m ∧ ¬ (2 ∣ m) ∧ ¬ (5 ∣ m) ∧ b = 2 ^ k * m := by
  intro b
  induction b using Nat.strong_induction_on with
  | h b ih =>
    intro hb h2 h5
    rcases h2 with ⟨c, rfl⟩
    have hc_pos : 0 < c := by omega
    have hc_lt : c < 2 * c := by omega
    have hc5 : ¬ (5 ∣ c) := fun h => h5 (dvd_mul_of_dvd_right h 2)
    by_cases hc2 : 2 ∣ c
    · rcases ih c hc_lt hc_pos hc2 hc5 with ⟨k, m, hk, hm, hm2, hm5, hcm⟩
      refine ⟨k + 1, m, by omega, hm, hm2, hm5, ?_⟩
      rw [hcm, pow_succ', mul_assoc]
    · exact ⟨1, c, le_rfl, hc_pos, hc2, hc5, by ring⟩

theorem main : H1 → H2 → type_of% @OeisA103662.conjecture.variants.a_40 := by
  intro h1 h2
  rintro ⟨b, hb, hno0⟩
  apply hno0
  by_cases h2b : 2 ∣ b
  · by_cases h5b : 5 ∣ b
    · exact zero_mem_digits_of_dvd_two_and_five hb h2b h5b
    · rcases exists_two_adic_split b (by omega) h2b h5b with ⟨k, m, hk, hm, hm2, hm5, rfl⟩
      by_cases hm1 : m = 1
      · subst hm1
        simpa [mul_one, ← pow_mul, mul_comm] using h1 k hk
      · exact h2 k m hk (by omega) hm2 hm5
  · by_cases h5b : 5 ∣ b
    · exact zero_mem_digits_of_odd_dvd_five hb h2b h5b
    · exact zero_mem_digits_of_odd_not_dvd_five hb h2b h5b

end OMA.R_OeisA103662_conjecture_variants_a_40_R1
