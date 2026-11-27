import Mathlib

theorem Conjectures.JoshiAbc.WeakFromFrey :
    (let rad := fun (n : ℕ) => n.primeFactors.prod id; let r := fun (a b : ℕ) => Real.log (rad (a*b*(a+b))); ∃ K : ℝ, ∀ a b : ℕ, 0<a → 0<b → Nat.Coprime a b → Real.log (16*((a:ℝ)^2+a*b+(b:ℝ)^2))/2 ≤ (15/8 : ℝ)*r a b+K) → let rad := fun (n : ℕ) => n.primeFactors.prod id; let h := fun (a b : ℕ) => Real.log ((a:ℝ)+b); let r := fun (a b : ℕ) => Real.log (rad (a*b*(a+b))); ∃ C : ℝ, ∀ a b : ℕ, 0<a → 0<b → Nat.Coprime a b → h a b ≤ (15/8)*r a b+C := by
  intro H rad h r
  obtain ⟨K, hK⟩ := H
  refine ⟨K, fun a b ha hb hab => ?_⟩
  have h1 := hK a b ha hb hab
  have ha' : (0:ℝ) < a := by exact_mod_cast ha
  have hb' : (0:ℝ) < b := by exact_mod_cast hb
  have hle : ((a:ℝ)+b) ≤ Real.sqrt (16*((a:ℝ)^2+a*b+(b:ℝ)^2)) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith [mul_pos ha' hb', sq_nonneg ((a:ℝ)-b)]
  have h2 : Real.log ((a:ℝ)+b) ≤ Real.log (16*((a:ℝ)^2+a*b+(b:ℝ)^2))/2 := by
    calc Real.log ((a:ℝ)+b) ≤ Real.log (Real.sqrt (16*((a:ℝ)^2+a*b+(b:ℝ)^2))) :=
          Real.log_le_log (by positivity) hle
      _ = _ := by rw [Real.log_sqrt (by positivity)]
  show Real.log ((a:ℝ)+b) ≤ (15/8) * Real.log (rad (a*b*(a+b))) + K
  exact le_trans h2 h1
