import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality

private theorem gb_even_of_dvd_two (n : ℕ) [NeZero n] (χ : DirichletCharacter ℂ n) (c : ℕ)
    (hc : c ∣ 2) (hf : DirichletCharacter.FactorsThrough χ c) : χ (-1) = 1 := by
  obtain ⟨h, χ₀, hχ⟩ := hf
  have h2 : (2 : ZMod c) = 0 := by
    have := (ZMod.natCast_eq_zero_iff 2 c).mpr hc
    simpa using this
  have hm : (-1 : ZMod c) = 1 := by
    have : (1 : ZMod c) + 1 = 0 := by rw [one_add_one_eq_two]; exact h2
    exact neg_eq_iff_add_eq_zero.mpr this
  have key := DirichletCharacter.changeLevel_eq_cast_of_dvd χ₀ h (-1)
  rw [← hχ] at key
  have e : (((-1 : (ZMod n)ˣ) : ZMod n)) = -1 := by simp
  rw [e] at key
  rw [key, ZMod.cast_neg h, ZMod.cast_one h, hm]
  exact map_one _

theorem PEqualNP.Outside.L_goldbach_conductor_exception_small_level :
    ∀ (n : ℕ) [NeZero n], 2<n → let odd := (Finset.univ : Finset (DirichletCharacter ℂ n)).filter (fun χ => χ (-1) = -1); ∀ d:ℕ, d∣n → d≤2 → (odd.filter (fun χ => χ.conductor ∣ d)).card=0 := by
  intro n _ _ odd d _ hd2
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro χ hχ hcd
  have hodd : χ (-1) = -1 := (Finset.mem_filter.mp hχ).2
  have hc : χ.conductor ∣ 2 := dvd_trans hcd (by
    interval_cases d <;> simp_all)
  have := gb_even_of_dvd_two n χ _ hc (DirichletCharacter.factorsThrough_conductor χ)
  rw [hodd] at this
  norm_num at this
