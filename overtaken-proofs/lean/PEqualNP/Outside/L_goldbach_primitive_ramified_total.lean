import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Factorization.PrimePow

private theorem ramKey (n : ℕ) (g : ℝ → ℝ) (hg0 : g 0 = 0) (hg : ∀ x : ℝ, 0 ≤ x → 0 ≤ g x) :
    ∑ k ∈ (Finset.range (n+1)).filter (fun k => n ≤ 3*k ∧ 3*k ≤ 2*n ∧ ¬k.Coprime n),
      g (ArithmeticFunction.vonMangoldt k)
      ≤ 2 * ∑ p ∈ n.primeFactors, g (Real.log (p : ℝ)) := by
  set S := (Finset.range (n+1)).filter (fun k => n ≤ 3*k ∧ 3*k ≤ 2*n ∧ ¬k.Coprime n) with hS
  have h1 : ∑ k ∈ S, g (ArithmeticFunction.vonMangoldt k)
      = ∑ k ∈ S.filter (fun k => ArithmeticFunction.vonMangoldt k ≠ 0),
          g (ArithmeticFunction.vonMangoldt k) := by
    refine Eq.trans ?_ (Finset.sum_filter _ _).symm
    refine Finset.sum_congr rfl (fun k _ => ?_)
    by_cases h : ArithmeticFunction.vonMangoldt k = 0
    · simp [h, hg0]
    · simp [h]
  set T := S.filter (fun k => ArithmeticFunction.vonMangoldt k ≠ 0) with hT
  have hpp : ∀ k ∈ T, ∃ p a : ℕ, p.Prime ∧ 0 < a ∧ p ^ a = k := by
    intro k hk
    have hne : ArithmeticFunction.vonMangoldt k ≠ 0 := (Finset.mem_filter.mp hk).2
    rw [Ne, ArithmeticFunction.vonMangoldt_eq_zero_iff, not_not] at hne
    exact (isPrimePow_nat_iff k).mp hne
  have hmaps : ∀ k ∈ T, k.minFac ∈ n.primeFactors := by
    intro k hk
    obtain ⟨p, a, hp, ha, rfl⟩ := hpp k hk
    have hk2 := (Finset.mem_filter.mp (Finset.mem_filter.mp hk).1).2
    rw [hp.pow_minFac ha.ne', Nat.mem_primeFactors]
    refine ⟨hp, ?_, ?_⟩
    · by_contra hdiv
      exact hk2.2.2 (Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd hp).mpr hdiv))
    · intro h0
      have hpos : 0 < p ^ a := pow_pos hp.pos a
      have := hk2.2.1
      subst h0
      have := hk2.1
      omega
  have hval : ∀ k ∈ T, ArithmeticFunction.vonMangoldt k = Real.log (k.minFac : ℝ) := by
    intro k hk
    have hne : ArithmeticFunction.vonMangoldt k ≠ 0 := (Finset.mem_filter.mp hk).2
    rw [Ne, ArithmeticFunction.vonMangoldt_eq_zero_iff, not_not] at hne
    rw [ArithmeticFunction.vonMangoldt_apply, if_pos hne]
  have hcard : ∀ p : ℕ, (T.filter (fun k => k.minFac = p)).card ≤ 2 := by
    intro p
    by_contra hlt
    rw [not_le, Finset.two_lt_card_iff] at hlt
    obtain ⟨x, y, z, hx, hy, hz, hxy, hxz, hyz⟩ := hlt
    have hwin : ∀ x ∈ T.filter (fun k => k.minFac = p), n ≤ 3 * x ∧ 3 * x ≤ 2 * n := by
      intro x hx
      have := (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1).2
      exact ⟨this.1, this.2.1⟩
    have hkey : ∀ x ∈ T.filter (fun k => k.minFac = p), ∀ y ∈ T.filter (fun k => k.minFac = p),
        x < y → 2 * x ≤ y := by
      intro x hx y hy hxy
      obtain ⟨q1, a, hq1, ha, hxa⟩ := hpp x (Finset.mem_filter.mp hx).1
      obtain ⟨q2, b, hq2, hb, hyb⟩ := hpp y (Finset.mem_filter.mp hy).1
      have e1 : x.minFac = p := (Finset.mem_filter.mp hx).2
      have e2 : y.minFac = p := (Finset.mem_filter.mp hy).2
      have f1 : q1 = p := by rw [← hxa, hq1.pow_minFac ha.ne'] at e1; exact e1
      have f2 : q2 = p := by rw [← hyb, hq2.pow_minFac hb.ne'] at e2; exact e2
      subst f1
      subst f2
      have hab : a ≤ b := by
        by_contra h
        have : q2 ^ b ≤ q2 ^ a := Nat.pow_le_pow_right hq2.pos (by omega)
        omega
      have hdvd : x ∣ y := by rw [← hxa, ← hyb]; exact pow_dvd_pow _ hab
      obtain ⟨c, hc⟩ := hdvd
      have hxpos : 0 < x := by rw [← hxa]; exact pow_pos hq2.pos _
      rcases c with _ | _ | c
      · omega
      · omega
      · nlinarith
    have a1 := hwin x hx
    have a2 := hwin y hy
    have a3 := hwin z hz
    have k1 := hkey x hx y hy
    have k2 := hkey y hy x hx
    have k3 := hkey x hx z hz
    have k4 := hkey z hz x hx
    have k5 := hkey y hy z hz
    have k6 := hkey z hz y hy
    omega
  rw [h1, ← Finset.sum_fiberwise_of_maps_to hmaps, Finset.mul_sum]
  refine Finset.sum_le_sum (fun p hp => ?_)
  have hpp' : p.Prime := (Nat.mem_primeFactors.mp hp).1
  have hgp : 0 ≤ g (Real.log (p : ℝ)) :=
    hg _ (Real.log_nonneg (by exact_mod_cast hpp'.one_lt.le))
  calc ∑ k ∈ T.filter (fun k => k.minFac = p), g (ArithmeticFunction.vonMangoldt k)
      = ∑ k ∈ T.filter (fun k => k.minFac = p), g (Real.log (p : ℝ)) := by
        refine Finset.sum_congr rfl (fun k hk => ?_)
        have hk' := Finset.mem_filter.mp hk
        rw [hval k hk'.1, hk'.2]
    _ = ((T.filter (fun k => k.minFac = p)).card : ℝ) * g (Real.log (p : ℝ)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 2 * g (Real.log (p : ℝ)) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hcard p) hgp

private theorem ramLog (n : ℕ) (hn : 2 ≤ n) :
    ∑ p ∈ n.primeFactors, Real.log (p : ℝ) ≤ Real.log (n : ℝ) := by
  have hdvd : ∏ p ∈ n.primeFactors, p ∣ n := Nat.prod_primeFactors_dvd n
  have hle : ∏ p ∈ n.primeFactors, p ≤ n := Nat.le_of_dvd (by omega) hdvd
  have hne : ∀ p ∈ n.primeFactors, (p : ℝ) ≠ 0 := by
    intro p hp
    exact_mod_cast (Nat.mem_primeFactors.mp hp).1.ne_zero
  have hpos : 0 < ∏ p ∈ n.primeFactors, p :=
    Finset.prod_pos (fun p hp => (Nat.mem_primeFactors.mp hp).1.pos)
  rw [← Real.log_prod hne, ← Nat.cast_prod]
  exact Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast hle)


theorem PEqualNP.Outside.L_goldbach_primitive_ramified_total :
    ∀ n : ℕ, 2≤n → (∑ k ∈ (Finset.range (n+1)).filter (fun k => n≤3*k ∧ 3*k≤2*n ∧ ¬k.Coprime n), ArithmeticFunction.vonMangoldt k) ≤ 2*Real.log (n:ℝ) := by
  intro n hn
  have h := ramKey n (fun x => x) rfl (fun x hx => hx)
  have h2 := ramLog n hn
  try simp only at h
  linarith
