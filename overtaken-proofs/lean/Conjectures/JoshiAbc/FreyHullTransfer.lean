import Mathlib

theorem Conjectures.JoshiAbc.FreyHullTransfer :
    let rad := fun (n : ℕ) => n.primeFactors.prod id; let r := fun (a b : ℕ) => Real.log (rad (a*b*(a+b))); ∀ (l : ℕ) (K : ℝ) (Q R U δ A : ℕ → ℕ → ℝ), 7 ≤ l → let k := 4*(l:ℝ)/(((l:ℝ)-3)*(l+1)); let H := fun (a b : ℕ) => Real.log (16*((a:ℝ)^2+a*b+(b:ℝ)^2))/2; (∀ a b : ℕ, 0<a → 0<b → Nat.Coprime a b → -(((l:ℝ)+1)/4)*Q a b-δ a b ≤ R a b ∧ R a b ≤ -((l:ℝ)*(l+1)/12)*Q a b+U a b ∧ H a b ≤ 2*l*Q a b/6+A a b ∧ A a b + k*(U a b+δ a b) ≤ (1+k)*r a b+K) → ∀ a b : ℕ, 0<a → 0<b → Nat.Coprime a b → H a b ≤ (1+k)*r a b+K := by
  intro rad r l K Q R U δ A hl k H h a b ha hb hab
  obtain ⟨h1, h2, h3, h4⟩ := h a b ha hb hab
  have hl' : (7:ℝ) ≤ l := by exact_mod_cast hl
  have hc : 0 < ((l:ℝ)-3)*(l+1) := by nlinarith
  have hk : k = 4*(l:ℝ)/(((l:ℝ)-3)*(l+1)) := rfl
  have hk0 : 0 ≤ k := by rw [hk]; positivity
  have hQ : ((l:ℝ)-3)*(l+1)/12 * Q a b ≤ U a b + δ a b := by nlinarith
  have hkQ : k * (((l:ℝ)-3)*(l+1)/12 * Q a b) ≤ k * (U a b + δ a b) :=
    mul_le_mul_of_nonneg_left hQ hk0
  have he : k * (((l:ℝ)-3)*(l+1)/12 * Q a b) = (l:ℝ) * Q a b / 3 := by
    have hne : (l:ℝ) - 3 ≠ 0 := (by linarith : (0:ℝ) < (l:ℝ) - 3).ne'
    have hne2 : (l:ℝ) + 1 ≠ 0 := (by linarith : (0:ℝ) < (l:ℝ) + 1).ne'
    rw [hk]
    field_simp
    ring
  nlinarith
