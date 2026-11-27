import Mathlib

theorem Conjectures.JoshiAbc.RootUnit :
    ∀ (p l : ℕ) [Fact p.Prime] (z : ZMod p), p ≠ 2 → Odd l → z^l=1 → z+z⁻¹ ≠ 0 := by
  intro p l _ z hp hl hz h
  have hz0 : z ≠ 0 := by
    rintro rfl
    rcases hl with ⟨k, rfl⟩
    simp at hz
  have h2 : z ^ 2 = -1 := by
    have : z * (z + z⁻¹) = 0 := by rw [h]; simp
    rw [mul_add, mul_inv_cancel₀ hz0] at this
    linear_combination this
  have h3 : (-1 : ZMod p) = 1 := by
    have : (z ^ 2) ^ l = 1 := by rw [← pow_mul, mul_comm, pow_mul, hz, one_pow]
    rw [h2, hl.neg_one_pow] at this
    exact this
  have h4 : ((2 : ℕ) : ZMod p) = 0 := by
    push_cast
    linear_combination -h3
  rw [ZMod.natCast_eq_zero_iff] at h4
  exact hp ((Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_two).1 h4)
