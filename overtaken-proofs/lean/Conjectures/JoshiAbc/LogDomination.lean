import Mathlib

private theorem ja_bern (v : ℕ) : 2 * v + 1 ≤ 3 ^ v := by
  induction v with
  | zero => simp
  | succ k ih => rw [pow_succ]; omega

theorem Conjectures.JoshiAbc.LogDomination :
    ∀ (p n : ℕ), p.Prime → 2 ≤ n → let c : ℕ := if p=2 then 4 else p; multiplicity p n < (n-1)*multiplicity p c := by
  intro p n hp hn c
  have hn0 : n ≠ 0 := by omega
  have hdvd : p ^ multiplicity p n ∣ n := pow_multiplicity_dvd p n
  have hle : p ^ multiplicity p n ≤ n := Nat.le_of_dvd (by omega) hdvd
  set v := multiplicity p n with hv
  by_cases h2 : p = 2
  · subst h2
    have hc : multiplicity 2 c = 2 := by
      have : c = 2 ^ 2 := by simp [c]
      rw [this]
      exact multiplicity_pow_self_of_prime (Nat.prime_iff.mp Nat.prime_two) 2
    rw [hc]
    have : v < 2 ^ v := Nat.lt_two_pow_self
    omega
  · have hc : multiplicity p c = 1 := by
      have : c = p ^ 1 := by simp [c, h2]
      rw [this]
      exact multiplicity_pow_self_of_prime (Nat.prime_iff.mp hp) 1
    rw [hc]
    have hp3 : 3 ≤ p := by have := hp.two_le; omega
    have hb := ja_bern v
    have : 3 ^ v ≤ p ^ v := Nat.pow_le_pow_left hp3 v
    omega
