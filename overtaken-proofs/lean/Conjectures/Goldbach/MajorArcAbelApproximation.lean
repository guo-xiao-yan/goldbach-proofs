import Mathlib

private noncomputable def phase (x : ℝ) : ℂ := Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I)

section PartFold
open Finset
private def units (q : ℕ) := (range q).filter (fun a => Nat.Coprime a q)

private theorem complete_phase_sum (m a : ℕ) (hm : 0 < m) :
    ∑ b ∈ range m, phase ((a : ℝ) * (b : ℝ) / m) =
      if m ∣ a then (m : ℂ) else 0 := by
  let z : ℂ := Complex.exp (2 * Real.pi * Complex.I * a / m)
  have hz : z = 1 ↔ m ∣ a :=
    Complex.exp_two_pi_mul_I_mul_div_eq_one_iff hm.ne'
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hpow (b : ℕ) : phase ((a : ℝ) * (b : ℝ) / m) = z ^ b := by
    rw [← Complex.exp_nat_mul]
    unfold phase
    push_cast
    congr 1
    field_simp
  simp_rw [hpow]
  by_cases h : m ∣ a
  · simp [h, hz.mpr h]
  · simp only [h, ite_false]
    have hzm : z ^ m = 1 := by
      rw [← Complex.exp_nat_mul]
      have harg : (m : ℂ) * (2 * Real.pi * Complex.I * a / m) =
          a * (2 * Real.pi * Complex.I) := by
        field_simp
      rw [harg]
      exact Complex.exp_nat_mul_two_pi_mul_I a
    have hsum := geom_sum_mul z m
    rw [hzm, sub_self] at hsum
    exact (mul_eq_zero.mp hsum).resolve_right
      (sub_ne_zero.mpr (fun hz1 => h (hz.mp hz1)))

private theorem coprime_indicator (q b : ℕ) (hq : 0 < q) :
    (∑ d ∈ q.divisors, if d ∣ b then (ArithmeticFunction.moebius d : ℂ) else 0) =
      if Nat.Coprime b q then 1 else 0 := by
  have hg : Nat.gcd b q ≠ 0 := (Nat.gcd_pos_of_pos_right b hq).ne'
  have hs : q.divisors.filter (fun d => d ∣ b) = (Nat.gcd b q).divisors := by
    ext d
    simp [Nat.mem_divisors, hq.ne', hg, Nat.dvd_gcd_iff, and_comm]
  rw [← sum_filter, hs]
  have h := DFunLike.congr_fun
    (ArithmeticFunction.coe_zeta_mul_coe_moebius (R := ℂ)) (Nat.gcd b q)
  simpa only [ArithmeticFunction.coe_zeta_mul_apply, ArithmeticFunction.one_apply,
    ArithmeticFunction.intCoe_apply, Nat.Coprime] using h

private theorem multiples_phase_sum (q a d : ℕ) (hq : 0 < q) (hd : d ∣ q) :
    ∑ b ∈ (range q).filter (fun b => d ∣ b), phase ((a : ℝ) * (b : ℝ) / q) =
      if q / d ∣ a then ((q / d : ℕ) : ℂ) else 0 := by
  obtain ⟨m, rfl⟩ := hd
  have hd : 0 < d := Nat.pos_of_mul_pos_right hq
  have hm : 0 < m := Nat.pos_of_mul_pos_left hq
  rw [Nat.mul_div_cancel_left _ hd, ← complete_phase_sum m a hm]
  symm
  apply sum_nbij' (d * ·) (· / d)
  · intro j hj
    exact mem_filter.mpr
      ⟨mem_range.mpr (Nat.mul_lt_mul_of_pos_left (mem_range.mp hj) hd),
        dvd_mul_right d j⟩
  · intro k hk
    apply mem_range.mpr
    exact (Nat.div_lt_iff_lt_mul hd).mpr
      (by simpa [Nat.mul_comm] using mem_range.mp (mem_filter.mp hk).1)
  · intro j _
    exact Nat.mul_div_cancel_left j hd
  · intro k hk
    exact Nat.mul_div_cancel' (mem_filter.mp hk).2
  · intro j _
    unfold phase
    push_cast
    congr 1
    have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
    have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
    field_simp

private theorem ramanujan_sum (q a : ℕ) (hq : 0 < q) :
    ∑ b ∈ units q, phase ((a : ℝ) * (b : ℝ) / q) =
      ∑ d ∈ q.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℂ) *
        (if q / d ∣ a then ((q / d : ℕ) : ℂ) else 0) := by
  calc
    _ = ∑ b ∈ range q,
        (∑ d ∈ q.divisors,
          if d ∣ b then (ArithmeticFunction.moebius d : ℂ) else 0) *
          phase ((a : ℝ) * (b : ℝ) / q) := by
      simp only [coprime_indicator q _ hq, units, sum_filter]
      apply sum_congr rfl
      intro b _
      by_cases h : Nat.Coprime b q <;> simp [h]
    _ = ∑ d ∈ q.divisors, ∑ b ∈ range q,
        (if d ∣ b then (ArithmeticFunction.moebius d : ℂ) else 0) *
          phase ((a : ℝ) * (b : ℝ) / q) := by
      simp only [sum_mul]
      rw [sum_comm]
    _ = _ := by
      apply sum_congr rfl
      intro d hd
      rw [← multiples_phase_sum q a d hq (Nat.dvd_of_mem_divisors hd),
        mul_sum, sum_filter]
      apply sum_congr rfl
      intro b _
      by_cases h : d ∣ b <;> simp [h]


end PartFold

private theorem ram_coprime (q a : ℕ) (hq : 0 < q) (ha : Nat.Coprime a q) :
    ∑ b ∈ (Finset.range q).filter (fun b => Nat.Coprime b q), phase ((a : ℝ) * (b : ℝ) / q) =
      ((ArithmeticFunction.moebius q : ℤ) : ℂ) := by
  have h := ramanujan_sum q a hq
  unfold units at h
  rw [h]
  rw [Finset.sum_eq_single q]
  · have : q / q ∣ a := by rw [Nat.div_self hq]; exact one_dvd _
    simp [this, Nat.div_self hq]
  · intro d hd hne
    have hdq : d ∣ q := Nat.dvd_of_mem_divisors hd
    have : ¬ (q / d ∣ a) := by
      intro hdiv
      have h1 : q / d ∣ Nat.gcd a q := Nat.dvd_gcd hdiv (Nat.div_dvd_of_dvd hdq)
      rw [ha] at h1
      have : q / d = 1 := Nat.dvd_one.mp h1
      have : d = q := by
        have := Nat.div_mul_cancel hdq
        rw [‹q / d = 1›] at this
        omega
      exact hne this
    simp [this]
  · intro h; exact absurd (Nat.mem_divisors.mpr ⟨dvd_refl q, hq.ne'⟩) h

private noncomputable def pw (k : ℕ) : ℝ := if Nat.Prime k then Real.log (k : ℝ) else 0

private theorem pw_nonneg (k : ℕ) : 0 ≤ pw k := by
  unfold pw
  split_ifs with h
  · exact Real.log_nonneg (by exact_mod_cast h.one_lt.le)
  · exact le_refl _

private theorem phase_norm' (x : ℝ) : ‖phase x‖ = 1 := Complex.norm_exp_ofReal_mul_I _

private theorem phase_add' (x y : ℝ) : phase (x + y) = phase x * phase y := by
  simp only [phase, mul_add, Complex.ofReal_add, add_mul, Complex.exp_add]

private theorem phase_nat (x : ℝ) (m : ℕ) : phase (x + m) = phase x := by
  rw [phase_add']
  have : phase (m : ℝ) = 1 := by
    unfold phase
    have : (((2 * Real.pi * (m:ℝ) : ℝ)) : ℂ) * Complex.I = (m : ℂ) * (2 * Real.pi * Complex.I) := by
      push_cast; ring
    rw [this]
    exact Complex.exp_nat_mul_two_pi_mul_I m
  rw [this, mul_one]

private theorem phase_step (β : ℝ) (k : ℕ) :
    ‖phase (((k + 1 : ℕ) : ℝ) * β) - phase ((k : ℝ) * β)‖ ≤ 2 * Real.pi * |β| := by
  have h : phase (((k + 1 : ℕ) : ℝ) * β) = phase ((k : ℝ) * β) * phase β := by
    rw [← phase_add']; congr 1; push_cast; ring
  rw [h]
  have h2 : phase ((k : ℝ) * β) * phase β - phase ((k : ℝ) * β) = phase ((k : ℝ) * β) * (phase β - 1) := by ring
  rw [h2, norm_mul, phase_norm', one_mul]
  have := Real.norm_exp_I_mul_ofReal_sub_one_le (x := 2 * Real.pi * β)
  have e : Complex.exp (Complex.I * ((2 * Real.pi * β : ℝ) : ℂ)) = phase β := by
    unfold phase; rw [mul_comm]
  rw [e] at this
  refine this.trans ?_
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos Real.pi_pos]
  norm_num

private theorem abel_id (d : ℕ → ℝ) (z : ℕ → ℂ) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (d k : ℂ) * z k =
      ((∑ k ∈ Finset.range (n + 1), d k : ℝ) : ℂ) * z n -
        ∑ k ∈ Finset.range n, ((∑ i ∈ Finset.range (k + 1), d i : ℝ) : ℂ) * (z (k + 1) - z k) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ (fun k => ((∑ i ∈ Finset.range (k + 1), d i : ℝ) : ℂ) * (z (k + 1) - z k)) n, Finset.sum_range_succ d (n + 1)]
    push_cast
    ring

private theorem abel_bound (d : ℕ → ℝ) (z : ℕ → ℂ) (n : ℕ) (e c : ℝ)
    (hz : ∀ k, ‖z k‖ = 1) (hc : ∀ k, ‖z (k + 1) - z k‖ ≤ c)
    (hD : ∀ m, m ≤ n → |∑ k ∈ Finset.range (m + 1), d k| ≤ e) (he : 0 ≤ e) (hc0 : 0 ≤ c) :
    ‖∑ k ∈ Finset.range (n + 1), (d k : ℂ) * z k‖ ≤ e * (1 + n * c) := by
  rw [abel_id]
  refine (norm_sub_le _ _).trans ?_
  have h1 : ‖((∑ k ∈ Finset.range (n + 1), d k : ℝ) : ℂ) * z n‖ ≤ e := by
    rw [norm_mul, hz, mul_one, Complex.norm_real, Real.norm_eq_abs]
    exact hD n le_rfl
  have h2 : ‖∑ k ∈ Finset.range n, ((∑ i ∈ Finset.range (k + 1), d i : ℝ) : ℂ) * (z (k + 1) - z k)‖ ≤ n * (e * c) := by
    refine (norm_sum_le _ _).trans ?_
    have : ∀ k ∈ Finset.range n, ‖((∑ i ∈ Finset.range (k + 1), d i : ℝ) : ℂ) * (z (k + 1) - z k)‖ ≤ e * c := by
      intro k hk
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul (hD k (Finset.mem_range.mp hk).le) (hc k) (norm_nonneg _) he
    refine (Finset.sum_le_sum this).trans ?_
    simp
  nlinarith

private theorem class_bound (q r n : ℕ) (β e : ℝ) (hq : 1 ≤ q)
    (hap : ∀ m : ℕ, 1 ≤ m → m ≤ n →
      |(∑ k ∈ (Finset.range (m + 1)).filter (fun k => k % q = r), pw k) - (m : ℝ) / (Nat.totient q : ℝ)| ≤ e)
    (he : 0 ≤ e) :
    ‖∑ k ∈ Finset.range (n + 1),
        (((if k % q = r then pw k else 0) - (if k = 0 then 0 else 1 / (Nat.totient q : ℝ)) : ℝ) : ℂ) *
          phase ((k : ℝ) * β)‖ ≤ e * (1 + n * (2 * Real.pi * |β|)) := by
  refine abel_bound (fun k => (if k % q = r then pw k else 0) - (if k = 0 then 0 else 1 / (Nat.totient q : ℝ)))
    (fun k => phase ((k : ℝ) * β)) n e _ (fun k => phase_norm' _) (fun k => phase_step β k) ?_ he (by positivity)
  intro m hm
  have e1 : ∑ k ∈ Finset.range (m + 1), (if k % q = r then pw k else 0) =
      ∑ k ∈ (Finset.range (m + 1)).filter (fun k => k % q = r), pw k := by
    rw [Finset.sum_filter]
  have e2 : ∑ k ∈ Finset.range (m + 1), (if k = 0 then 0 else 1 / (Nat.totient q : ℝ)) =
      (m : ℝ) / (Nat.totient q : ℝ) := by
    rw [Finset.sum_range_succ']
    simp [Finset.sum_const]
    ring
  rw [Finset.sum_sub_distrib, e1, e2]
  rcases Nat.eq_zero_or_pos m with h0 | hpos
  · subst h0
    have hp0 : pw 0 = 0 := by simp [pw]
    simp [Finset.range_one, Finset.filter_singleton]
    by_cases h : 0 = r
    · subst h; simp [hp0, he]
    · simp [h, he]
  · exact hap m hpos hm

private theorem phase_mod (q a k : ℕ) (hq : 1 ≤ q) :
    phase ((k : ℝ) * ((a : ℝ) / q)) = phase (((k % q : ℕ) : ℝ) * ((a : ℝ) / q)) := by
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  have h : (k : ℝ) * ((a : ℝ) / q) = ((k % q : ℕ) : ℝ) * ((a : ℝ) / q) + ((k / q * a : ℕ) : ℝ) := by
    have hk : (k : ℝ) = ((k % q : ℕ) : ℝ) + q * ((k / q : ℕ) : ℝ) := by
      exact_mod_cast (Nat.mod_add_div k q).symm
    push_cast
    rw [hk]
    field_simp
  rw [h, phase_nat]

private theorem bad_sum (q n : ℕ) (hq : 1 ≤ q) :
    ∑ k ∈ Finset.range (n + 1), (if Nat.Coprime k q then 0 else pw k) ≤ Real.log (q : ℝ) := by
  have hg0 : ∀ k : ℕ, 0 ≤ (if Nat.Coprime k q then 0 else pw k) := by
    intro k; split_ifs
    · exact le_refl _
    · exact pw_nonneg k
  have h1 : ∑ k ∈ Finset.range (n + 1), (if Nat.Coprime k q then 0 else pw k) ≤
      ∑ k ∈ q.primeFactors, (if Nat.Coprime k q then 0 else pw k) := by
    have e1 : ∑ k ∈ Finset.range (n + 1), (if Nat.Coprime k q then 0 else pw k) =
        ∑ k ∈ Finset.range (n + 1) ∩ q.primeFactors, (if Nat.Coprime k q then 0 else pw k) := by
      symm
      apply Finset.sum_subset Finset.inter_subset_left
      intro k hk hk2
      have hkt : k ∉ q.primeFactors := fun h => hk2 (Finset.mem_inter.mpr ⟨hk, h⟩)
      by_cases hc : Nat.Coprime k q
      · simp [hc]
      · have : ¬ Nat.Prime k := by
          intro hp
          apply hkt
          rw [Nat.mem_primeFactors]
          refine ⟨hp, ?_, by omega⟩
          by_contra hnd
          exact hc ((Nat.Prime.coprime_iff_not_dvd hp).mpr hnd)
        simp [hc, pw, this]
    rw [e1]
    exact Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right (fun k _ _ => hg0 k)
  have h2 : ∑ k ∈ q.primeFactors, (if Nat.Coprime k q then 0 else pw k) ≤ ∑ k ∈ q.primeFactors, Real.log (k : ℝ) := by
    apply Finset.sum_le_sum
    intro k hk
    have hp : Nat.Prime k := Nat.prime_of_mem_primeFactors hk
    split_ifs
    · exact Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
    · simp [pw, hp]
  refine h1.trans (h2.trans ?_)
  rw [← Real.log_prod]
  · apply Real.log_le_log
    · apply Finset.prod_pos
      intro k hk
      exact_mod_cast (Nat.prime_of_mem_primeFactors hk).pos
    · have := Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd q)
      exact_mod_cast (by rw [← Nat.cast_prod]; exact_mod_cast this)
  · intro k hk
    exact_mod_cast (Nat.prime_of_mem_primeFactors hk).ne_zero

private theorem fiber (q a k : ℕ) (β c : ℝ) (hq : 1 ≤ q) :
    (if Nat.Coprime k q then (c : ℂ) * phase ((k : ℝ) * ((a : ℝ) / q + β)) else 0) =
      ∑ r ∈ (Finset.range q).filter (fun b => Nat.Coprime b q),
        phase ((r : ℝ) * ((a : ℝ) / q)) * ((if k % q = r then (c : ℂ) else 0) * phase ((k : ℝ) * β)) := by
  have e1 : ∑ r ∈ (Finset.range q).filter (fun b => Nat.Coprime b q),
        phase ((r : ℝ) * ((a : ℝ) / q)) * ((if k % q = r then (c : ℂ) else 0) * phase ((k : ℝ) * β)) =
      ∑ r ∈ (Finset.range q).filter (fun b => Nat.Coprime b q),
        (if k % q = r then phase ((r : ℝ) * ((a : ℝ) / q)) * ((c : ℂ) * phase ((k : ℝ) * β)) else 0) := by
    apply Finset.sum_congr rfl
    intro r _
    by_cases h : k % q = r
    · simp [h]
    · simp [h]
  rw [e1, Finset.sum_ite_eq]
  have hmem : k % q ∈ (Finset.range q).filter (fun b => Nat.Coprime b q) ↔ Nat.Coprime k q := by
    rw [Finset.mem_filter, Finset.mem_range, ZMod.coprime_mod_iff_coprime]
    exact ⟨fun h => h.2, fun h => ⟨Nat.mod_lt _ (by omega), h⟩⟩
  by_cases hc : Nat.Coprime k q
  · have hm := hmem.mpr hc
    rw [if_pos hc, if_pos hm]
    have : (k : ℝ) * ((a : ℝ) / q + β) = (k : ℝ) * ((a : ℝ) / q) + (k : ℝ) * β := by ring
    rw [this, phase_add', phase_mod q a k hq]
    ring
  · have hm : k % q ∉ (Finset.range q).filter (fun b => Nat.Coprime b q) := fun h => hc (hmem.mp h)
    rw [if_neg hc, if_neg hm]

private theorem icc_sum (n : ℕ) (f : ℕ → ℂ) (c : ℝ) :
    ∑ k ∈ Finset.range (n + 1), (((if k = 0 then 0 else c : ℝ)) : ℂ) * f k =
      (c : ℂ) * ∑ k ∈ Finset.Icc 1 n, f k := by
  have h : Finset.Icc 1 n = (Finset.range (n + 1)).filter (fun k => k ≠ 0) := by
    ext k; simp only [Finset.mem_Icc, Finset.mem_filter, Finset.mem_range]; omega
  rw [h, Finset.sum_filter, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : k = 0 <;> simp [hk]


theorem Conjectures.Goldbach.MajorArcAbelApproximation :
    let w (k : ℕ) := if Nat.Prime k then Real.log (k : ℝ) else 0; let E (x : ℝ) := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I); let S (n : ℕ) (t : ℝ) := ∑ k ∈ Finset.range (n + 1), (w k : ℂ) * E ((k : ℝ) * t); let ap (q r m : ℕ) := ∑ k ∈ (Finset.range (m + 1)).filter (fun k => k % q = r), w k; let K1 (n : ℕ) (b : ℝ) := ∑ k ∈ Finset.Icc 1 n, E ((k : ℝ) * b); ∀ (n q a : ℕ) (β e : ℝ), 1 ≤ q → Nat.Coprime a q → 0 ≤ e → (∀ m : ℕ, 1 ≤ m → m ≤ n → ∀ r < q, Nat.Coprime r q → |ap q r m - (m : ℝ) / (Nat.totient q : ℝ)| ≤ e) → ‖S n ((a : ℝ) / q + β) - ((ArithmeticFunction.moebius q : ℂ) / (Nat.totient q : ℂ)) * K1 n β‖ ≤ Real.log (q : ℝ) + (Nat.totient q : ℝ) * e * (1 + 2 * Real.pi * (n : ℝ) * |β|) := by
  intro w E S ap K1 n q a β e hq hcop he hap
  have hq0 : 0 < q := hq
  have hφpos : (0:ℝ) < (Nat.totient q : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq0
  have hRcard : (((Finset.range q).filter (fun b => Nat.Coprime b q)).card : ℝ) = (Nat.totient q : ℝ) := by
    have : (Finset.range q).filter (fun b => Nat.Coprime b q) = (Finset.range q).filter q.Coprime :=
      Finset.filter_congr (fun b _ => Nat.coprime_comm)
    rw [this]
    rfl
  have hS : S n ((a : ℝ) / q + β) = ∑ k ∈ Finset.range (n + 1), (pw k : ℂ) * phase ((k : ℝ) * ((a : ℝ) / q + β)) := rfl
  have hK : K1 n β = ∑ k ∈ Finset.Icc 1 n, phase ((k : ℝ) * β) := rfl
  set P1 : ℂ := ∑ k ∈ Finset.range (n + 1), (if Nat.Coprime k q then (pw k : ℂ) * phase ((k : ℝ) * ((a : ℝ) / q + β)) else 0) with hP1
  set P2 : ℂ := ∑ k ∈ Finset.range (n + 1), (if Nat.Coprime k q then 0 else (pw k : ℂ) * phase ((k : ℝ) * ((a : ℝ) / q + β))) with hP2
  have hsplit : S n ((a : ℝ) / q + β) = P1 + P2 := by
    rw [hS, hP1, hP2, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    split_ifs <;> simp
  have hB : ‖P2‖ ≤ Real.log (q : ℝ) := by
    refine (norm_sum_le _ _).trans ?_
    refine le_trans ?_ (bad_sum q n hq)
    apply Finset.sum_le_sum
    intro k _
    split_ifs
    · simp
    · rw [norm_mul, phase_norm', mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (pw_nonneg k)]
  have hP1' : P1 = ∑ r ∈ (Finset.range q).filter (fun b => Nat.Coprime b q),
      phase ((r : ℝ) * ((a : ℝ) / q)) * ∑ k ∈ Finset.range (n + 1), (if k % q = r then (pw k : ℂ) else 0) * phase ((k : ℝ) * β) := by
    rw [hP1]
    simp_rw [fiber q a _ β _ hq]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r _
    rw [Finset.mul_sum]
  have hram := ram_coprime q a hq0 hcop
  have hram' : ∑ r ∈ (Finset.range q).filter (fun b => Nat.Coprime b q), phase ((r : ℝ) * ((a : ℝ) / q)) =
      ((ArithmeticFunction.moebius q : ℤ) : ℂ) := by
    rw [← hram]
    apply Finset.sum_congr rfl
    intro r _
    rw [show ((r : ℝ) * ((a : ℝ) / q)) = (a : ℝ) * (r : ℝ) / q by ring]
  have hmain : P1 - ((ArithmeticFunction.moebius q : ℂ) / (Nat.totient q : ℂ)) * K1 n β =
      ∑ r ∈ (Finset.range q).filter (fun b => Nat.Coprime b q),
        phase ((r : ℝ) * ((a : ℝ) / q)) * ∑ k ∈ Finset.range (n + 1),
          (((if k % q = r then pw k else 0) - (if k = 0 then 0 else 1 / (Nat.totient q : ℝ)) : ℝ) : ℂ) * phase ((k : ℝ) * β) := by
    have e1 : ∀ r : ℕ, ∑ k ∈ Finset.range (n + 1),
          (((if k % q = r then pw k else 0) - (if k = 0 then 0 else 1 / (Nat.totient q : ℝ)) : ℝ) : ℂ) * phase ((k : ℝ) * β) =
        ∑ k ∈ Finset.range (n + 1), (if k % q = r then (pw k : ℂ) else 0) * phase ((k : ℝ) * β) -
          ((1 / (Nat.totient q : ℝ) : ℝ) : ℂ) * ∑ k ∈ Finset.Icc 1 n, phase ((k : ℝ) * β) := by
      intro r
      rw [← icc_sum n (fun k => phase ((k : ℝ) * β)) (1 / (Nat.totient q : ℝ)), ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro k _
      push_cast
      rw [← sub_mul]
      split_ifs <;> simp
    simp_rw [e1, mul_sub]
    rw [Finset.sum_sub_distrib, ← hP1', ← Finset.sum_mul, hram', hK]
    push_cast
    ring
  have hcl : ∀ r ∈ (Finset.range q).filter (fun b => Nat.Coprime b q),
      ‖phase ((r : ℝ) * ((a : ℝ) / q)) * ∑ k ∈ Finset.range (n + 1),
          (((if k % q = r then pw k else 0) - (if k = 0 then 0 else 1 / (Nat.totient q : ℝ)) : ℝ) : ℂ) * phase ((k : ℝ) * β)‖ ≤
        e * (1 + n * (2 * Real.pi * |β|)) := by
    intro r hr
    rw [Finset.mem_filter] at hr
    rw [norm_mul, phase_norm', one_mul]
    exact class_bound q r n β e hq (fun m hm1 hmn => hap m hm1 hmn r (Finset.mem_range.mp hr.1) hr.2) he
  have hsum : ‖P1 - ((ArithmeticFunction.moebius q : ℂ) / (Nat.totient q : ℂ)) * K1 n β‖ ≤
      (Nat.totient q : ℝ) * e * (1 + 2 * Real.pi * (n : ℝ) * |β|) := by
    rw [hmain]
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum hcl).trans ?_)
    rw [Finset.sum_const, nsmul_eq_mul, hRcard]
    apply le_of_eq
    ring
  have hfin : S n ((a : ℝ) / q + β) - ((ArithmeticFunction.moebius q : ℂ) / (Nat.totient q : ℂ)) * K1 n β =
      (P1 - ((ArithmeticFunction.moebius q : ℂ) / (Nat.totient q : ℂ)) * K1 n β) + P2 := by
    rw [hsplit]; ring
  rw [hfin]
  refine (norm_add_le _ _).trans ?_
  linarith
