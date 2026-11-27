import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Cast.Field

private theorem gb_layer_filter (n c p : ℕ) (hn : n ≠ 0) (hc : c ∣ n) (hp : p.Prime) :
    (Finset.Icc 1 (n.factorization p)).filter (fun j => c ∣ n / p ^ j) =
      Finset.Icc 1 (n.factorization p - c.factorization p) := by
  have hc0 : c ≠ 0 := fun h => hn (by simpa [h] using hc)
  have hle : c.factorization ≤ n.factorization := (Nat.factorization_le_iff_dvd hc0 hn).2 hc
  have hlep : c.factorization p ≤ n.factorization p := hle p
  ext j
  simp only [Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    have hpj : p ^ j ∣ n := (hp.pow_dvd_iff_le_factorization hn).2 h2
    have hne : n / p ^ j ≠ 0 := by
      have := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hpj) (pow_pos hp.pos j)
      omega
    have := (Nat.factorization_le_iff_dvd hc0 hne).2 h3 p
    rw [Nat.factorization_div hpj, hp.factorization_pow] at this
    simp only [Finsupp.tsub_apply, Finsupp.single_eq_same] at this
    omega
  · rintro ⟨h1, h2⟩
    have h2' : j ≤ n.factorization p := by omega
    refine ⟨⟨h1, h2'⟩, ?_⟩
    have hpj : p ^ j ∣ n := (hp.pow_dvd_iff_le_factorization hn).2 h2'
    have hne : n / p ^ j ≠ 0 := by
      have := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hpj) (pow_pos hp.pos j)
      omega
    rw [← Nat.factorization_le_iff_dvd hc0 hne, Nat.factorization_div hpj, hp.factorization_pow]
    intro q
    simp only [Finsupp.tsub_apply]
    by_cases hq : q = p
    · subst hq
      simp only [Finsupp.single_eq_same]
      omega
    · have h0 : (Finsupp.single p j) q = 0 := by simp [Finsupp.single_apply, Ne.symm hq]
      rw [h0]
      have := hle q
      omega

theorem PEqualNP.Outside.L_goldbach_conductor_deficit_layer :
    ∀ (n : ℕ) [NeZero n], 2<n → ∀ χ : DirichletCharacter ℂ n, Real.log ((n:ℝ)/(χ.conductor:ℝ)) = ∑ p ∈ n.primeFactors, (Real.log (p:ℝ)) * (((Finset.Icc 1 (n.factorization p)).filter (fun j => χ.conductor ∣ n/p^j)).card : ℝ) := by
  intro n inst _ χ
  have hn : n ≠ 0 := NeZero.ne n
  have hcd : χ.conductor ∣ n := DirichletCharacter.conductor_dvd_level χ
  have hc0 : χ.conductor ≠ 0 := DirichletCharacter.conductor_ne_zero χ
  have hcast : ((n:ℝ)/(χ.conductor:ℝ)) = ((n / χ.conductor : ℕ) : ℝ) := by
    rw [Nat.cast_div hcd (by exact_mod_cast hc0)]
  rw [hcast, Real.log_nat_eq_sum_factorization, Finsupp.sum, Nat.factorization_div hcd]
  have hsupp : (n.factorization - χ.conductor.factorization).support ⊆ n.primeFactors := by
    intro p hp
    rw [← Nat.support_factorization]
    exact Finsupp.support_tsub hp |> fun h => by simpa using h
  rw [Finset.sum_subset hsupp]
  · apply Finset.sum_congr rfl
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    rw [gb_layer_filter n _ p hn hcd hpp, Nat.card_Icc]
    simp only [Finsupp.tsub_apply]
    push_cast [Nat.add_sub_cancel]
    ring_nf
  · intro p _ hp
    simp only [Finsupp.mem_support_iff, not_not] at hp
    simp [hp]
