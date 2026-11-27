import Mathlib
import PEqualNP.Outside.L_twin_primes_ap_short_error

private theorem pw_mask (q n : ℕ) (hq : 0 < q) :
    ∑ d ∈ q.divisors, (if d ∣ n then ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0)
      = if Nat.Coprime n q then 1 else 0 := by
  rw [← Finset.sum_filter]
  have hg : 0 < Nat.gcd q n := Nat.gcd_pos_of_pos_left _ hq
  have hf : q.divisors.filter (fun d => d ∣ n) = (Nat.gcd q n).divisors := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff]
    constructor
    · rintro ⟨⟨h1, _⟩, h2⟩
      exact ⟨⟨h1, h2⟩, hg.ne'⟩
    · rintro ⟨⟨h1, h2⟩, _⟩
      exact ⟨⟨h1, hq.ne'⟩, h2⟩
  rw [hf]
  have h := ArithmeticFunction.coe_mul_zeta_apply
    (f := (ArithmeticFunction.moebius : ArithmeticFunction ℝ)) (x := Nat.gcd q n)
  rw [ArithmeticFunction.coe_moebius_mul_coe_zeta] at h
  simp only [ArithmeticFunction.intCoe_apply] at h
  rw [← h, ArithmeticFunction.one_apply]
  exact if_congr Nat.coprime_comm rfl rfl

private theorem pw_decomp (s : Finset ℕ) (q : ℕ) (hq : 0 < q) :
    (s.filter (fun p => p.Prime ∧ Nat.Coprime (p+2) q)).sum (fun p => Real.log p)
      = ∑ d ∈ q.divisors, (ArithmeticFunction.moebius d : ℝ) *
        (s.filter (fun p => p.Prime ∧ d ∣ p+2)).sum (fun p => Real.log p) := by
  have h1 : ∀ d : ℕ, (ArithmeticFunction.moebius d : ℝ) *
        (s.filter (fun p => p.Prime ∧ d ∣ p+2)).sum (fun p => Real.log p)
      = ∑ p ∈ s.filter (fun p => p.Prime),
          (if d ∣ p+2 then (ArithmeticFunction.moebius d : ℝ) else 0) * Real.log p := by
    intro d
    rw [Finset.mul_sum, Finset.sum_filter, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p _
    by_cases hp : p.Prime <;> by_cases hd : d ∣ p+2 <;> simp [hp, hd]
  simp_rw [h1]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, pw_mask q _ hq]
  rw [Finset.sum_filter, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : p.Prime <;> by_cases hc : Nat.Coprime (p+2) q <;> simp [hp, hc]

private noncomputable def pwG : ArithmeticFunction ℝ :=
  ⟨fun n => if n = 0 then 0 else 1 / (Nat.totient n : ℝ), by simp⟩

private theorem pwG_apply (n : ℕ) (hn : n ≠ 0) : pwG n = 1 / (Nat.totient n : ℝ) := by
  simp [pwG, hn]

private theorem pwG_mult : pwG.IsMultiplicative := by
  refine ⟨by simp [pwG_apply], ?_⟩
  intro m n h
  by_cases hm : m = 0
  · simp [pwG, hm]
  by_cases hn : n = 0
  · simp [pwG, hn]
  rw [pwG_apply _ hm, pwG_apply _ hn, pwG_apply _ (mul_ne_zero hm hn), Nat.totient_mul h]
  push_cast
  rw [one_div, one_div, one_div, mul_inv]

private theorem pw_main (q : ℕ) (hsq : Squarefree q) :
    ∑ d ∈ q.divisors, (ArithmeticFunction.moebius d : ℝ) * (1 / (Nat.totient d : ℝ))
      = q.primeFactors.prod (fun r => 1 - 1/((r:ℝ)-1)) := by
  set F : ArithmeticFunction ℝ :=
    ((ArithmeticFunction.moebius : ArithmeticFunction ℝ).pmul pwG) * ArithmeticFunction.zeta
    with hF
  have hmult : F.IsMultiplicative := by
    refine ArithmeticFunction.IsMultiplicative.mul ?_ ?_
    · exact ArithmeticFunction.IsMultiplicative.pmul
        (ArithmeticFunction.isMultiplicative_moebius.intCast) pwG_mult
    · exact ArithmeticFunction.isMultiplicative_zeta.natCast
  have hq : q ≠ 0 := hsq.ne_zero
  have hFq : F q = ∑ d ∈ q.divisors, (ArithmeticFunction.moebius d : ℝ) * (1 / (Nat.totient d : ℝ)) := by
    rw [hF, ArithmeticFunction.coe_mul_zeta_apply]
    apply Finset.sum_congr rfl
    intro d hd
    have hd0 : d ≠ 0 := (Nat.pos_of_mem_divisors hd).ne'
    rw [ArithmeticFunction.pmul_apply, pwG_apply d hd0]
    simp
  rw [← hFq, ← hmult.prod_primeFactors hsq]
  apply Finset.prod_congr rfl
  intro r hr
  have hrp : r.Prime := Nat.prime_of_mem_primeFactors hr
  rw [hF, ArithmeticFunction.coe_mul_zeta_apply, Nat.Prime.sum_divisors hrp]
  rw [ArithmeticFunction.pmul_apply, ArithmeticFunction.pmul_apply, pwG_apply r hrp.ne_zero,
    pwG_apply 1 one_ne_zero]
  simp [ArithmeticFunction.moebius_apply_prime hrp, Nat.totient_prime hrp]
  have : (r:ℝ) - 1 ≠ 0 := by
    have := hrp.one_lt
    have : (1:ℝ) < r := by exact_mod_cast this
    linarith
  rw [Nat.cast_sub hrp.one_le]
  simp
  ring

theorem Conjectures.TwinPrimes.PrimeWheelProgressionBudget :
    (∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ), 0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1/2) → (let w := fun (X : ℕ) => (Finset.range (2*X+1)).filter (fun n => X < n ∧ 50*n < 51*X); let S := fun (X q : ℕ) => ((w X).filter (fun p => p.Prime ∧ Nat.Coprime (p+2) q)).sum (fun p => Real.log p); let V := fun (q : ℕ) => q.primeFactors.prod (fun r => 1-1/((r:ℝ)-1)); ∃ C : ℝ, 0 < C ∧ ∀ (X q : ℕ), 2 ≤ X → q ≤ X → Odd q → Squarefree q → |S X q-(X:ℝ)/50*V q| ≤ C*(q.divisors.card:ℝ)*Real.sqrt X*(Real.log (2*(q:ℝ)*X))^2) := by
  intro hGRH
  have h := PEqualNP.Outside.L_twin_primes_ap_short_error hGRH
  dsimp only at h ⊢
  obtain ⟨C, hC, hAP⟩ := h
  refine ⟨C, hC, ?_⟩
  intro X q hX hqX hodd hsq
  have hq : 0 < q := hsq.ne_zero.bot_lt
  set s := (Finset.range (2*X+1)).filter (fun n => X < n ∧ 50*n < 51*X) with hs
  rw [pw_decomp s q hq, ← pw_main q hsq, Finset.mul_sum, ← Finset.sum_sub_distrib]
  have hterm : ∀ d ∈ q.divisors,
      |(ArithmeticFunction.moebius d : ℝ) *
        (s.filter (fun p => p.Prime ∧ d ∣ p+2)).sum (fun p => Real.log p)
        - (X:ℝ)/50 * ((ArithmeticFunction.moebius d : ℝ) * (1 / (Nat.totient d : ℝ)))|
      ≤ C * Real.sqrt X * (Real.log (2*(q:ℝ)*X))^2 := by
    intro d hd
    have hdq : d ∣ q := Nat.dvd_of_mem_divisors hd
    have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdq hq
    have hdX : d ≤ X := (Nat.le_of_dvd hq hdq).trans hqX
    have hodd' : Odd d := Odd.of_dvd_nat hodd hdq
    have h1 := hAP X d hX hdX hodd'
    have hdq' : (d:ℝ) ≤ q := by exact_mod_cast Nat.le_of_dvd hq hdq
    have hphi : (0:ℝ) < Nat.totient d := by exact_mod_cast Nat.totient_pos.mpr hd0
    have hd1 : (1:ℝ) ≤ d := by exact_mod_cast hd0
    have hX1 : (1:ℝ) ≤ X := by exact_mod_cast (by omega : 1 ≤ X)
    have hlog : Real.log (2*(d:ℝ)*X) ≤ Real.log (2*(q:ℝ)*X) := by
      apply Real.log_le_log (by positivity)
      have : (0:ℝ) ≤ X := by positivity
      nlinarith
    have hlog0 : 0 ≤ Real.log (2*(d:ℝ)*X) := by
      apply Real.log_nonneg; nlinarith
    have hsq2 : (Real.log (2*(d:ℝ)*X))^2 ≤ (Real.log (2*(q:ℝ)*X))^2 :=
      pow_le_pow_left₀ hlog0 hlog 2
    have hmu : |(ArithmeticFunction.moebius d : ℝ)| ≤ 1 := by
      have := ArithmeticFunction.abs_moebius_le_one (n := d)
      exact_mod_cast this
    have heq : (ArithmeticFunction.moebius d : ℝ) *
        (s.filter (fun p => p.Prime ∧ d ∣ p+2)).sum (fun p => Real.log p)
        - (X:ℝ)/50 * ((ArithmeticFunction.moebius d : ℝ) * (1 / (Nat.totient d : ℝ)))
        = (ArithmeticFunction.moebius d : ℝ) *
          ((s.filter (fun p => p.Prime ∧ d ∣ p+2)).sum (fun p => Real.log p)
            - (X:ℝ)/(50 * Nat.totient d)) := by
      field_simp
    rw [heq, abs_mul]
    have hB : 0 ≤ C * Real.sqrt X := by positivity
    calc |(ArithmeticFunction.moebius d : ℝ)| * _ ≤ 1 * (C * Real.sqrt X * (Real.log (2*(d:ℝ)*X))^2) := by
          apply mul_le_mul hmu h1 (abs_nonneg _) (by norm_num)
      _ ≤ _ := by
          rw [one_mul]
          exact mul_le_mul_of_nonneg_left hsq2 hB
  calc |∑ d ∈ q.divisors, _| ≤ ∑ d ∈ q.divisors, |_| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ q.divisors, C * Real.sqrt X * (Real.log (2*(q:ℝ)*X))^2 := Finset.sum_le_sum hterm
    _ = _ := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring
