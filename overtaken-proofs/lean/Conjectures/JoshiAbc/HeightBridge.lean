import Mathlib

theorem Conjectures.JoshiAbc.HeightBridge :
    (let rad := fun (n : ℕ) => n.primeFactors.prod id; let r := fun (a b : ℕ) => Real.log (rad (a*b*(a+b))); ∀ l : ℕ, l.Prime → 7 ≤ l → ∃ K : ℝ, ∀ a b : ℕ, 0<a → 0<b → Nat.Coprime a b → Real.log (16*((a:ℝ)^2+a*b+(b:ℝ)^2))/2 ≤ (1+4*(l:ℝ)/(((l:ℝ)-3)*(l+1)))*r a b+K) → (∀ ε : ℝ, 0 < ε → ∃ l : ℕ, l.Prime ∧ 7 ≤ l ∧ 4*(l:ℝ)/(((l:ℝ)-3)*(l+1)) ≤ ε) → (let h := fun (a b : ℕ) => Real.log ((a:ℝ)+b); ∀ a b : ℕ, 0 < a → 0 < b → 2*h a b + Real.log 12 ≤ Real.log (16*((a:ℝ)^2+a*b+(b:ℝ)^2))) → (let rad := fun (n : ℕ) => n.primeFactors.prod id; let h := fun (a b : ℕ) => Real.log ((a:ℝ)+b); let r := fun (a b : ℕ) => Real.log (rad (a*b*(a+b))); ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ a b : ℕ, 0<a → 0<b → Nat.Coprime a b → h a b ≤ (1+ε)*r a b+C) := by
  intro hfrey hl hh
  intro rad h r
  intro ε hε
  obtain ⟨l, hlp, hl7, hle⟩ := hl ε hε
  obtain ⟨K, hK⟩ := hfrey l hlp hl7
  refine ⟨K - Real.log 12 / 2, ?_⟩
  intro a b ha hb hab
  have h1 := hK a b ha hb hab
  have h2 := hh a b ha hb
  have hr : 0 ≤ r a b := by
    show 0 ≤ Real.log (((a*b*(a+b)).primeFactors.prod id : ℕ) : ℝ)
    apply Real.log_nonneg
    have : 0 < (a*b*(a+b)).primeFactors.prod id := by
      apply Finset.prod_pos
      intro p hp
      exact (Nat.prime_of_mem_primeFactors hp).pos
    exact_mod_cast this
  have h3 : 0 ≤ Real.log 12 := Real.log_nonneg (by norm_num)
  have h4 : (1 + 4*(l:ℝ)/(((l:ℝ)-3)*(l+1))) * r a b ≤ (1+ε) * r a b :=
    mul_le_mul_of_nonneg_right (by linarith) hr
  show Real.log ((a:ℝ)+b) ≤ _
  have h2' : 2 * Real.log ((a:ℝ)+b) + Real.log 12 ≤ Real.log (16*((a:ℝ)^2+a*b+(b:ℝ)^2)) := h2
  nlinarith
