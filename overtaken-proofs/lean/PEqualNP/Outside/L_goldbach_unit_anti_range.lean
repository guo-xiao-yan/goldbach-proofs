import Mathlib.Data.Nat.Prime.Basic

theorem PEqualNP.Outside.L_goldbach_unit_anti_range :
    ∀ n a b : ℕ, 0<a → a<n → 0<b → b<n → (n ∣ a+b ↔ a+b=n) := by
  intro n a b ha han hb hbn
  constructor
  · rintro ⟨c, hc⟩
    have h1 : 0 < c := by
      rcases Nat.eq_zero_or_pos c with h | h
      · subst h; omega
      · exact h
    have h2 : c < 2 := by
      by_contra hh
      have : n * 2 ≤ n * c := Nat.mul_le_mul_left n (by omega)
      omega
    have : c = 1 := by omega
    subst this
    omega
  · intro h
    exact ⟨1, by omega⟩
