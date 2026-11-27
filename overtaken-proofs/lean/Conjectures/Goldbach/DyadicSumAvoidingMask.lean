import Mathlib

private lemma dsam_mod (t k : ℕ) (ht : 2 < t) :
    2 ^ k % (2 ^ (t + 3) - 1) ≤ 4 * 2 ^ t := by
  have hL : 1 ≤ 2 ^ t := Nat.one_le_two_pow
  have h8 : 2 ^ (t + 3) = 8 * 2 ^ t := by rw [pow_add]; ring
  have hM : 1 < 2 ^ (t + 3) - 1 := by omega
  have h1 : 2 ^ (t + 3) % (2 ^ (t + 3) - 1) = 1 := by
    generalize 2 ^ (t + 3) = N at hM ⊢
    obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at hM ⊢
    rw [Nat.add_mod_left, Nat.mod_eq_of_lt hM]
  have hk : 2 ^ k = (2 ^ (t + 3)) ^ (k / (t + 3)) * 2 ^ (k % (t + 3)) := by
    rw [← pow_mul, ← pow_add, Nat.div_add_mod]
  have hr : 2 ^ (k % (t + 3)) ≤ 4 * 2 ^ t := by
    have : k % (t + 3) ≤ t + 2 := by
      have := Nat.mod_lt k (show 0 < t + 3 by omega); omega
    calc 2 ^ (k % (t + 3)) ≤ 2 ^ (t + 2) := Nat.pow_le_pow_right (by norm_num) this
      _ = 4 * 2 ^ t := by rw [pow_add]; ring
  have : 2 ^ k % (2 ^ (t + 3) - 1) = 2 ^ (k % (t + 3)) % (2 ^ (t + 3) - 1) := by
    rw [hk, Nat.mul_mod, Nat.pow_mod, h1]
    simp [Nat.mod_mod]
  rw [this]
  calc _ ≤ 2 ^ (k % (t + 3)) := Nat.mod_le _ _
    _ ≤ _ := hr

private lemma dsam_cop (W t : ℕ) (hW : 0 < W) (ht : W < t + 3) (hp : (t + 3).Prime) :
    Nat.Coprime W (2 ^ (t + 3) - 1) := by
  apply Nat.coprime_of_dvd
  intro p hpp hpW hpM
  have hpos : 0 < 2 ^ (t + 3) := by positivity
  have hodd : p ≠ 2 := by
    rintro rfl
    have h2 : 2 ∣ 2 ^ (t + 3) := dvd_pow_self 2 (by omega)
    omega
  haveI : Fact p.Prime := ⟨hpp⟩
  have hz : ((2 ^ (t + 3) - 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hpM
  have h1 : (2 : ZMod p) ^ (t + 3) = 1 := by
    have : 1 ≤ 2 ^ (t + 3) := Nat.one_le_two_pow
    rw [Nat.cast_sub this] at hz
    push_cast at hz
    exact sub_eq_zero.1 hz
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at this
    have := (Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).1 this
    exact hodd this
  have hd : orderOf (2 : ZMod p) ∣ t + 3 := orderOf_dvd_of_pow_eq_one h1
  have hd2 : orderOf (2 : ZMod p) ∣ p - 1 := ZMod.orderOf_dvd_card_sub_one h2
  rcases (Nat.dvd_prime hp).1 hd with h | h
  · rw [orderOf_eq_one_iff] at h
    have : ((2 : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by exact_mod_cast h
    rw [ZMod.natCast_eq_natCast_iff'] at this
    have hp2 := hpp.two_le
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hpp.one_lt] at this
    omega
  · rw [h] at hd2
    have := Nat.le_of_dvd hW hpW
    have := Nat.le_of_dvd (by have := hpp.two_le; omega) hd2
    omega

theorem Conjectures.Goldbach.DyadicSumAvoidingMask :
    ∀ W : ℕ, 0 < W → ∃ M : ℕ, 1 < M ∧ Nat.Coprime W M ∧ ∃ S : Finset ℕ, S ⊆ Finset.range M ∧ M ≤ 8 * S.card ∧ ∀ (a b k : ℕ), a ∈ S → b ∈ S → (a+b)%M ≠ (2^k)%M := by
  intro W hW
  obtain ⟨s, hs, hsp⟩ := Nat.exists_infinite_primes (max W 5 + 1)
  have h1 := le_max_left W 5
  have h2 := le_max_right W 5
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 3 := ⟨s - 3, by omega⟩
  have hL : 1 ≤ 2 ^ t := Nat.one_le_two_pow
  have h8 : 2 ^ (t + 3) = 8 * 2 ^ t := by rw [pow_add]; ring
  refine ⟨2 ^ (t + 3) - 1, by omega, dsam_cop W t hW (by omega) hsp,
    Finset.Ico (3 * 2 ^ t) (4 * 2 ^ t), ?_, ?_, ?_⟩
  · intro x hx
    rw [Finset.mem_Ico] at hx
    rw [Finset.mem_range]; omega
  · rw [Nat.card_Ico]; omega
  · intro a b k ha hb
    rw [Finset.mem_Ico] at ha hb
    have := dsam_mod t k (by omega)
    have hlt : a + b < 2 ^ (t + 3) - 1 := by omega
    rw [Nat.mod_eq_of_lt hlt]
    omega
