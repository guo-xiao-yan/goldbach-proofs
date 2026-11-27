import Mathlib

theorem Conjectures.Goldbach.BeaumontPrimitiveCycle :
    ∀ m : ℕ, 2 ≤ m → (Nat.Prime m ↔ ∀ a : ZMod m, a ≠ 0 → Function.Surjective (fun k : ZMod m => a*k)) := by
  intro m hm
  constructor
  · intro hp
    haveI : Fact m.Prime := ⟨hp⟩
    intro a ha b
    exact ⟨a⁻¹ * b, by simp only; rw [← mul_assoc, mul_inv_cancel₀ ha, one_mul]⟩
  · intro h
    by_contra hnp
    obtain ⟨d, hd, h1, h2⟩ := (Nat.exists_dvd_of_not_prime2 hm hnp)
    haveI : NeZero m := ⟨by omega⟩
    have hne : (d : ZMod m) ≠ 0 := by
      intro h0
      rw [ZMod.natCast_eq_zero_iff] at h0
      have := Nat.le_of_dvd (by omega) h0
      omega
    obtain ⟨k, hk⟩ := h (d : ZMod m) hne 1
    simp only at hk
    have hu : IsUnit (d : ZMod m) := IsUnit.of_mul_eq_one k hk
    rw [ZMod.isUnit_iff_coprime] at hu
    have := Nat.Coprime.eq_one_of_dvd hu hd
    omega
