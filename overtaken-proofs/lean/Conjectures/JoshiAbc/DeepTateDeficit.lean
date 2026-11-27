import Mathlib

theorem Conjectures.JoshiAbc.DeepTateDeficit :
    ∀ v : Fin 3 → (Fin 14 → ZMod 29), 29^11 ≤ Nat.card ((Fin 14 → ZMod 29) ⧸ Submodule.span (ZMod 29) (Set.range v)) := by
  intro v
  have : Fact (Nat.Prime 29) := ⟨by norm_num⟩
  set S := Submodule.span (ZMod 29) (Set.range v)
  have hr : Module.finrank (ZMod 29) S ≤ 3 := by
    exact (finrank_range_le_card (R := ZMod 29) v).trans (by simp)
  have h1 : Nat.card (Fin 14 → ZMod 29) = 29 ^ 14 := by
    simp [Nat.card_eq_fintype_card, ZMod.card]
  have h2 : Nat.card S = 29 ^ Module.finrank (ZMod 29) S := by
    have : Fintype S := Fintype.ofFinite S
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 29), ZMod.card]
  have h3 : Nat.card (Fin 14 → ZMod 29) = Nat.card S * Nat.card ((Fin 14 → ZMod 29) ⧸ S) :=
    Submodule.card_eq_card_quotient_mul_card S
  have h4 : 29 ^ Module.finrank (ZMod 29) S ≤ 29 ^ 3 := Nat.pow_le_pow_right (by norm_num) hr
  rw [h1, h2] at h3
  by_contra hlt
  rw [not_le] at hlt
  have : 29 ^ Module.finrank (ZMod 29) S * Nat.card ((Fin 14 → ZMod 29) ⧸ S) < 29^3 * 29^11 :=
    Nat.mul_lt_mul_of_le_of_lt h4 hlt (by positivity)
  omega
