import Mathlib

private noncomputable def ph (x : ℝ) : ℂ := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)
private noncomputable def pw (k : ℕ) : ℝ := if Nat.Prime k then Real.log (k : ℝ) else 0
private def Qf (n : ℕ) : ℕ := (Nat.log 2 (n + 2)) ^ 2
private noncomputable def wd (n q : ℕ) : ℝ := (Qf n : ℝ) / ((q : ℝ) * n)
private noncomputable def Kf (n : ℕ) (β : ℝ) : ℂ := ∑ k ∈ Finset.range (n + 1), ph ((k : ℝ) * β)
private noncomputable def Sf (n : ℕ) (t : ℝ) : ℂ := ∑ k ∈ Finset.range (n + 1), (pw k : ℂ) * ph ((k : ℝ) * t)
private noncomputable def ramf (q h : ℕ) : ℂ := ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), ph ((h : ℝ) * a / q)
private noncomputable def kmass (n : ℕ) (b : ℝ) : ℝ := intervalIntegral (fun β => ‖Kf n β‖ ^ 2) (-b) b MeasureTheory.volume
private noncomputable def modf (n : ℕ) : ℂ := ∑ q ∈ Finset.Icc 1 (Qf n), ((ramf q 1 / (q.totient : ℂ)) ^ 2 * (starRingEnd ℂ) (ramf q n)) * (kmass n (wd n q) : ℂ)
private noncomputable def cen (q a : ℕ) : ℝ := (a : ℝ) / q
private def arcf (n : ℕ) : Set ℝ := {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Qf n ∧ a ≤ q ∧ Nat.Coprime a q ∧ |t - cen q a| ≤ wd n q}
private noncomputable def majf (n : ℕ) : ℂ := intervalIntegral ((arcf n).indicator (fun t => (Sf n t) ^ 2 * ph (-(n : ℝ) * t))) (0 : ℝ) 1 MeasureTheory.volume
private noncomputable def cerr (m q b : ℕ) : ℝ := (∑ k ∈ (Finset.range m).filter (fun k => k % q = b), pw k) - (if Nat.Coprime b q then (m : ℝ) / q.totient else 0)
private noncomputable def discf (n q a : ℕ) : ℝ := (Finset.range (n + 2)).sup' ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ (n + 1))⟩ (fun m => ‖∑ b ∈ Finset.range q, (cerr m q b : ℂ) * ph ((b : ℝ) * cen q a)‖)
private noncomputable def umean (q a : ℕ) : ℂ := (∑ r ∈ (Finset.range q).filter (fun r => Nat.Coprime r q), ph ((r : ℝ) * cen q a)) / (q.totient : ℂ)
private noncomputable def lend (n q a : ℕ) : ℝ := max (cen q a - wd n q) 0 - cen q a
private noncomputable def rend (n q a : ℕ) : ℝ := min (cen q a + wd n q) 1 - cen q a
private noncomputable def ampf (n : ℕ) (D β : ℝ) : ℝ := D * (1 + 2 * Real.pi * n * |β|)
private noncomputable def pcost (n q a : ℕ) (D β : ℝ) : ℝ := ampf n D β * (2 * ‖umean q a * Kf n β‖ + ampf n D β)
private noncomputable def budf (n : ℕ) : ℝ := ∑ q ∈ Finset.Icc 1 (Qf n), ∑ a ∈ (Finset.range (q + 1)).filter (fun a => Nat.Coprime a q), intervalIntegral (pcost n q a (discf n q a)) (lend n q a) (rend n q a) MeasureTheory.volume

section PartFold
open Finset
private def units (q : ℕ) := (range q).filter (fun a => Nat.Coprime a q)

private theorem complete_ph_sum (m a : ℕ) (hm : 0 < m) :
    ∑ b ∈ range m, ph ((a : ℝ) * (b : ℝ) / m) =
      if m ∣ a then (m : ℂ) else 0 := by
  let z : ℂ := Complex.exp (2 * Real.pi * Complex.I * a / m)
  have hz : z = 1 ↔ m ∣ a :=
    Complex.exp_two_pi_mul_I_mul_div_eq_one_iff hm.ne'
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hpow (b : ℕ) : ph ((a : ℝ) * (b : ℝ) / m) = z ^ b := by
    rw [← Complex.exp_nat_mul]
    unfold ph
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

private theorem multiples_ph_sum (q a d : ℕ) (hq : 0 < q) (hd : d ∣ q) :
    ∑ b ∈ (range q).filter (fun b => d ∣ b), ph ((a : ℝ) * (b : ℝ) / q) =
      if q / d ∣ a then ((q / d : ℕ) : ℂ) else 0 := by
  obtain ⟨m, rfl⟩ := hd
  have hd : 0 < d := Nat.pos_of_mul_pos_right hq
  have hm : 0 < m := Nat.pos_of_mul_pos_left hq
  rw [Nat.mul_div_cancel_left _ hd, ← complete_ph_sum m a hm]
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
    unfold ph
    push_cast
    congr 1
    have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
    have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
    field_simp

private theorem ramanujan_sum (q a : ℕ) (hq : 0 < q) :
    ∑ b ∈ units q, ph ((a : ℝ) * (b : ℝ) / q) =
      ∑ d ∈ q.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℂ) *
        (if q / d ∣ a then ((q / d : ℕ) : ℂ) else 0) := by
  calc
    _ = ∑ b ∈ range q,
        (∑ d ∈ q.divisors,
          if d ∣ b then (ArithmeticFunction.moebius d : ℂ) else 0) *
          ph ((a : ℝ) * (b : ℝ) / q) := by
      simp only [coprime_indicator q _ hq, units, sum_filter]
      apply sum_congr rfl
      intro b _
      by_cases h : Nat.Coprime b q <;> simp [h]
    _ = ∑ d ∈ q.divisors, ∑ b ∈ range q,
        (if d ∣ b then (ArithmeticFunction.moebius d : ℂ) else 0) *
          ph ((a : ℝ) * (b : ℝ) / q) := by
      simp only [sum_mul]
      rw [sum_comm]
    _ = _ := by
      apply sum_congr rfl
      intro d hd
      rw [← multiples_ph_sum q a d hq (Nat.dvd_of_mem_divisors hd),
        mul_sum, sum_filter]
      apply sum_congr rfl
      intro b _
      by_cases h : d ∣ b <;> simp [h]


end PartFold

private theorem ram_coprime (q a : ℕ) (hq : 0 < q) (ha : Nat.Coprime a q) :
    ∑ b ∈ (Finset.range q).filter (fun b => Nat.Coprime b q), ph ((a : ℝ) * (b : ℝ) / q) =
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

private theorem ph_norm' (x : ℝ) : ‖ph x‖ = 1 := Complex.norm_exp_ofReal_mul_I _

private theorem ph_add' (x y : ℝ) : ph (x + y) = ph x * ph y := by
  simp only [ph, mul_add, Complex.ofReal_add, add_mul, Complex.exp_add]

private theorem ph_nat (x : ℝ) (m : ℕ) : ph (x + m) = ph x := by
  rw [ph_add']
  have : ph (m : ℝ) = 1 := by
    unfold ph
    have : (((2 * Real.pi * (m:ℝ) : ℝ)) : ℂ) * Complex.I = (m : ℂ) * (2 * Real.pi * Complex.I) := by
      push_cast; ring
    rw [this]
    exact Complex.exp_nat_mul_two_pi_mul_I m
  rw [this, mul_one]

private theorem ph_step (β : ℝ) (k : ℕ) :
    ‖ph (((k + 1 : ℕ) : ℝ) * β) - ph ((k : ℝ) * β)‖ ≤ 2 * Real.pi * |β| := by
  have h : ph (((k + 1 : ℕ) : ℝ) * β) = ph ((k : ℝ) * β) * ph β := by
    rw [← ph_add']; congr 1; push_cast; ring
  rw [h]
  have h2 : ph ((k : ℝ) * β) * ph β - ph ((k : ℝ) * β) = ph ((k : ℝ) * β) * (ph β - 1) := by ring
  rw [h2, norm_mul, ph_norm', one_mul]
  have := Real.norm_exp_I_mul_ofReal_sub_one_le (x := 2 * Real.pi * β)
  have e : Complex.exp (Complex.I * ((2 * Real.pi * β : ℝ) : ℂ)) = ph β := by
    unfold ph; rw [mul_comm]
  rw [e] at this
  refine this.trans ?_
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos Real.pi_pos]
  norm_num

private theorem ph_mod (q a k : ℕ) (hq : 1 ≤ q) :
    ph ((k : ℝ) * ((a : ℝ) / q)) = ph (((k % q : ℕ) : ℝ) * ((a : ℝ) / q)) := by
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  have h : (k : ℝ) * ((a : ℝ) / q) = ((k % q : ℕ) : ℝ) * ((a : ℝ) / q) + ((k / q * a : ℕ) : ℝ) := by
    have hk : (k : ℝ) = ((k % q : ℕ) : ℝ) + q * ((k / q : ℕ) : ℝ) := by
      exact_mod_cast (Nat.mod_add_div k q).symm
    push_cast
    rw [hk]
    field_simp
  rw [h, ph_nat]


private theorem abel_id_c (d z : ℕ → ℂ) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), d k * z k =
      (∑ k ∈ Finset.range (n + 1), d k) * z n -
        ∑ k ∈ Finset.range n, (∑ i ∈ Finset.range (k + 1), d i) * (z (k + 1) - z k) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ (fun k => (∑ i ∈ Finset.range (k + 1), d i) * (z (k + 1) - z k)) n, Finset.sum_range_succ d (n + 1)]
    ring

private theorem abel_bound_c (d z : ℕ → ℂ) (n : ℕ) (e c : ℝ)
    (hz : ∀ k, ‖z k‖ = 1) (hc : ∀ k, ‖z (k + 1) - z k‖ ≤ c)
    (hD : ∀ m, m ≤ n → ‖∑ k ∈ Finset.range (m + 1), d k‖ ≤ e) (he : 0 ≤ e) (hc0 : 0 ≤ c) :
    ‖∑ k ∈ Finset.range (n + 1), d k * z k‖ ≤ e * (1 + n * c) := by
  rw [abel_id_c]
  refine (norm_sub_le _ _).trans ?_
  have h1 : ‖(∑ k ∈ Finset.range (n + 1), d k) * z n‖ ≤ e := by
    rw [norm_mul, hz, mul_one]
    exact hD n le_rfl
  have h2 : ‖∑ k ∈ Finset.range n, (∑ i ∈ Finset.range (k + 1), d i) * (z (k + 1) - z k)‖ ≤ n * (e * c) := by
    refine (norm_sum_le _ _).trans ?_
    have : ∀ k ∈ Finset.range n, ‖(∑ i ∈ Finset.range (k + 1), d i) * (z (k + 1) - z k)‖ ≤ e * c := by
      intro k hk
      rw [norm_mul]
      exact mul_le_mul (hD k (Finset.mem_range.mp hk).le) (hc k) (norm_nonneg _) he
    refine (Finset.sum_le_sum this).trans ?_
    simp
  nlinarith

private theorem errsum (m q a : ℕ) (hq : 1 ≤ q) :
    ∑ b ∈ Finset.range q, (cerr m q b : ℂ) * ph ((b : ℝ) * cen q a) =
      ∑ k ∈ Finset.range m, (pw k : ℂ) * ph ((k : ℝ) * cen q a) - (m : ℂ) * umean q a := by
  have hφ : (q.totient : ℂ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr hq).ne'
  have e1 : ∑ b ∈ Finset.range q, (cerr m q b : ℂ) * ph ((b : ℝ) * cen q a) =
      ∑ b ∈ Finset.range q, ((∑ k ∈ (Finset.range m).filter (fun k => k % q = b), (pw k : ℂ)) * ph ((b : ℝ) * cen q a))
      - ∑ b ∈ Finset.range q, ((if Nat.Coprime b q then ((m : ℝ) / q.totient : ℝ) else 0 : ℝ) : ℂ) * ph ((b : ℝ) * cen q a) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro b _
    unfold cerr
    push_cast
    split_ifs <;> simp [sub_mul]
  rw [e1]
  congr 1
  · have : ∀ b ∈ Finset.range q, (∑ k ∈ (Finset.range m).filter (fun k => k % q = b), (pw k : ℂ)) * ph ((b : ℝ) * cen q a)
        = ∑ k ∈ (Finset.range m).filter (fun k => k % q = b), (pw k : ℂ) * ph ((k : ℝ) * cen q a) := by
      intro b _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k hk
      have hk' := (Finset.mem_filter.mp hk).2
      rw [cen, ph_mod q a k hq, hk']
    rw [Finset.sum_congr rfl this]
    exact Finset.sum_fiberwise_of_maps_to (g := fun k => k % q) (fun k _ => Finset.mem_range.mpr (Nat.mod_lt _ hq))
      (fun k => (pw k : ℂ) * ph ((k : ℝ) * cen q a))
  · unfold umean
    have h2 : ∑ b ∈ Finset.range q, ((if Nat.Coprime b q then ((m : ℝ) / q.totient : ℝ) else 0 : ℝ) : ℂ) * ph ((b : ℝ) * cen q a) =
        (((m : ℝ) / q.totient : ℝ) : ℂ) * ∑ r ∈ (Finset.range q).filter (fun r => Nat.Coprime r q), ph ((r : ℝ) * cen q a) := by
      rw [Finset.sum_filter, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      split_ifs <;> simp
    rw [h2]
    push_cast
    ring

private theorem err_le_disc (n q a m : ℕ) (hm : m ≤ n + 1) :
    ‖∑ b ∈ Finset.range q, (cerr m q b : ℂ) * ph ((b : ℝ) * cen q a)‖ ≤ discf n q a :=
  Finset.le_sup' (fun m => ‖∑ b ∈ Finset.range q, (cerr m q b : ℂ) * ph ((b : ℝ) * cen q a)‖)
    (Finset.mem_range.mpr (by omega))

private theorem disc_nonneg (n q a : ℕ) : 0 ≤ discf n q a :=
  (norm_nonneg _).trans (err_le_disc n q a 0 (by omega))

private theorem local_bound (n q a : ℕ) (hq : 1 ≤ q) (β : ℝ) :
    ‖Sf n (cen q a + β) - umean q a * Kf n β‖ ≤ ampf n (discf n q a) β := by
  have h1 : Sf n (cen q a + β) - umean q a * Kf n β =
      ∑ k ∈ Finset.range (n + 1), ((pw k : ℂ) * ph ((k : ℝ) * cen q a) - umean q a) * ph ((k : ℝ) * β) := by
    unfold Sf Kf
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    have : (k : ℝ) * (cen q a + β) = (k : ℝ) * cen q a + (k : ℝ) * β := by ring
    rw [this, ph_add']
    ring
  rw [h1]
  have hD := disc_nonneg n q a
  have := abel_bound_c (fun k => (pw k : ℂ) * ph ((k : ℝ) * cen q a) - umean q a)
    (fun k => ph ((k : ℝ) * β)) n (discf n q a) (2 * Real.pi * |β|) (fun k => ph_norm' _)
    (fun k => ph_step β k) ?_ hD (by positivity)
  · refine this.trans (le_of_eq ?_)
    unfold ampf; ring
  · intro m hm
    have e := errsum (m + 1) q a hq
    have e2 : ∑ k ∈ Finset.range (m + 1), ((pw k : ℂ) * ph ((k : ℝ) * cen q a) - umean q a) =
        ∑ b ∈ Finset.range q, (cerr (m + 1) q b : ℂ) * ph ((b : ℝ) * cen q a) := by
      rw [e, Finset.sum_sub_distrib]
      simp
    rw [e2]
    exact err_le_disc n q a (m + 1) (by omega)

private theorem pointwise_bound (n q a : ℕ) (hq : 1 ≤ q) (β : ℝ) :
    ‖(Sf n (cen q a + β) ^ 2 - (umean q a * Kf n β) ^ 2) * ph (-(n : ℝ) * (cen q a + β))‖ ≤
      pcost n q a (discf n q a) β := by
  rw [norm_mul, ph_norm', mul_one]
  have h := local_bound n q a hq β
  have hD := disc_nonneg n q a
  have hamp : 0 ≤ ampf n (discf n q a) β := by unfold ampf; positivity
  set S := Sf n (cen q a + β)
  set V := umean q a * Kf n β
  have e : S ^ 2 - V ^ 2 = (S - V) * ((S - V) + 2 * V) := by ring
  rw [e, norm_mul]
  have h2 : ‖(S - V) + 2 * V‖ ≤ ampf n (discf n q a) β + 2 * ‖V‖ := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul]
    simp only [Complex.norm_ofNat]
    linarith
  unfold pcost
  calc ‖S - V‖ * ‖(S - V) + 2 * V‖ ≤ ampf n (discf n q a) β * (ampf n (discf n q a) β + 2 * ‖V‖) :=
        mul_le_mul h h2 (norm_nonneg _) hamp
    _ = _ := by ring

private theorem arc_aux (k : ℕ) (hk : 19 ≤ k) : 2 * k ^ 4 + 3 ≤ 2 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have h1 : 19 ≤ k := hk
    have : 2 * (k + 1) ^ 4 + 3 ≤ 2 * (2 * k ^ 4 + 3) := by
      nlinarith [Nat.mul_le_mul h1 h1, pow_pos (show 0 < k by omega) 3, pow_pos (show 0 < k by omega) 2,
        pow_pos (show 0 < k by omega) 4]
    calc 2 * (k + 1) ^ 4 + 3 ≤ 2 * (2 * k ^ 4 + 3) := this
      _ ≤ 2 * 2 ^ k := by omega
      _ = 2 ^ (k + 1) := by ring

private theorem cutoff (n : ℕ) (hn : 1000000 ≤ n) : 2 * (Qf n) ^ 2 < n := by
  have hk : 19 ≤ Nat.log 2 (n + 2) := by
    apply Nat.le_log_of_pow_le (by norm_num)
    norm_num; omega
  have h2 := arc_aux _ hk
  have h3 : 2 ^ Nat.log 2 (n + 2) ≤ n + 2 := Nat.pow_log_le_self 2 (by omega)
  have : ((Nat.log 2 (n + 2)) ^ 2) ^ 2 = Nat.log 2 (n + 2) ^ 4 := by ring
  unfold Qf
  rw [this]; omega

private theorem frac_ne (q a q' a' : ℕ) (hq0 : 0 < q) (h : Nat.Coprime a q) (h' : Nat.Coprime a' q')
    (hne : (⟨q, a⟩ : Σ _ : ℕ, ℕ) ≠ ⟨q', a'⟩) : a * q' ≠ a' * q := by
  intro e
  have h1 : q ∣ q' := (Nat.Coprime.dvd_mul_left h.symm).mp ⟨a', by rw [e]; ring⟩
  have h2 : q' ∣ q := (Nat.Coprime.dvd_mul_left h'.symm).mp ⟨a, by rw [← e]; ring⟩
  have hqq : q = q' := Nat.dvd_antisymm h1 h2
  subst hqq
  apply hne
  have : a = a' := Nat.eq_of_mul_eq_mul_right hq0 e
  subst this
  rfl

private theorem spacing (q a q' a' : ℕ) (hq : 1 ≤ q) (hq' : 1 ≤ q') (hne : a * q' ≠ a' * q) :
    1 ≤ |cen q a - cen q' a'| * ((q : ℝ) * q') := by
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hqr' : (0 : ℝ) < q' := by exact_mod_cast hq'
  have e : cen q a - cen q' a' = ((a : ℝ) * q' - a' * q) / (q * q') := by
    unfold cen; field_simp
  rw [e, abs_div, abs_of_pos (show (0 : ℝ) < q * q' by positivity), div_mul_cancel₀ _ (by positivity)]
  have h0 : (a : ℤ) * q' - a' * q ≠ 0 := by
    intro h; apply hne; exact_mod_cast (by linarith : (a : ℤ) * q' = a' * q)
  have h1 : (1 : ℤ) ≤ |(a : ℤ) * q' - a' * q| := Int.one_le_abs h0
  have := (Int.cast_le (R := ℝ)).mpr h1
  push_cast at this
  exact this

private theorem core_disjoint (n : ℕ) (hn : 1000000 ≤ n) (q a q' a' : ℕ) (hq : 1 ≤ q) (hq' : 1 ≤ q')
    (hqQ : q ≤ Qf n) (hqQ' : q' ≤ Qf n) (h : Nat.Coprime a q) (h' : Nat.Coprime a' q')
    (hne : (⟨q, a⟩ : Σ _ : ℕ, ℕ) ≠ ⟨q', a'⟩) :
    Disjoint (Set.Icc (cen q a - wd n q) (cen q a + wd n q))
      (Set.Icc (cen q' a' - wd n q') (cen q' a' + wd n q')) := by
  rw [Set.disjoint_left]
  intro t h1 h2
  have hs := spacing q a q' a' hq hq' (frac_ne q a q' a' hq h h' hne)
  have hd : |cen q a - cen q' a'| ≤ wd n q + wd n q' := by
    rw [abs_le]; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hqr' : (0 : ℝ) < q' := by exact_mod_cast hq'
  have hnr : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hc := cutoff n hn
  have hnat : Qf n * (q + q') < n := by
    have : Qf n * (q + q') ≤ Qf n * (Qf n + Qf n) := Nat.mul_le_mul_left _ (by omega)
    nlinarith
  have hreal : (Qf n : ℝ) * ((q : ℝ) + q') < n := by exact_mod_cast hnat
  have hw : (wd n q + wd n q') * ((q : ℝ) * q') < 1 := by
    have : (wd n q + wd n q') * ((q : ℝ) * q') = (Qf n : ℝ) * ((q : ℝ) + q') / n := by
      unfold wd; field_simp; ring
    rw [this, div_lt_one hnr]
    exact hreal
  have := mul_le_mul_of_nonneg_right hd (by positivity : (0 : ℝ) ≤ (q : ℝ) * q')
  linarith

private theorem ph_conj (x : ℝ) : (starRingEnd ℂ) (ph x) = ph (-x) := by
  unfold ph
  rw [← Complex.exp_conj]
  congr 1
  rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

private theorem K_sq (n : ℕ) (β : ℝ) :
    Kf n β ^ 2 * ph (-(n : ℝ) * β) = ((‖Kf n β‖ ^ 2 : ℝ) : ℂ) := by
  have h1 : Kf n β * ph (-(n : ℝ) * β) = (starRingEnd ℂ) (Kf n β) := by
    unfold Kf
    rw [map_sum, Finset.sum_mul]
    simp_rw [ph_conj]
    rw [← Finset.sum_range_reflect (fun j : ℕ => ph (-((j : ℝ) * β))) (n + 1)]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' : k ≤ n := by have := Finset.mem_range.mp hk; omega
    rw [← ph_add']
    simp only [Nat.add_sub_cancel]
    congr 1
    rw [Nat.cast_sub hk']
    ring
  have h2 : Kf n β ^ 2 * ph (-(n : ℝ) * β) = Kf n β * (starRingEnd ℂ) (Kf n β) := by
    rw [← h1]; ring
  rw [h2, Complex.mul_conj, Complex.normSq_eq_norm_sq]

private theorem Kf_cont (n : ℕ) : Continuous (Kf n) := by
  unfold Kf ph
  fun_prop

private theorem Sf_cont (n : ℕ) : Continuous (Sf n) := by
  unfold Sf ph
  fun_prop

private def Pset (n : ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  (Finset.Icc 1 (Qf n)).sigma (fun q => (Finset.range (q + 1)).filter (fun a => Nat.Coprime a q))

private noncomputable def win (n : ℕ) (p : Σ _ : ℕ, ℕ) : Set ℝ :=
  Set.Icc (max (cen p.1 p.2 - wd n p.1) 0) (min (cen p.1 p.2 + wd n p.1) 1)

private noncomputable def gf (n : ℕ) (t : ℝ) : ℂ := Sf n t ^ 2 * ph (-(n : ℝ) * t)

private theorem gf_cont (n : ℕ) : Continuous (gf n) := by
  unfold gf
  have := Sf_cont n
  unfold ph
  fun_prop

private theorem wd_nonneg (n q : ℕ) : 0 ≤ wd n q := by unfold wd; positivity

private theorem wd_mul_lt (n : ℕ) (hn : 1000000 ≤ n) (q : ℕ) (hq : 1 ≤ q) : wd n q * q < 1 := by
  have hc := cutoff n hn
  have hQ : Qf n < n := by nlinarith
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hnr : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hQr : (Qf n : ℝ) < n := by exact_mod_cast hQ
  have : wd n q * q = (Qf n : ℝ) / n := by unfold wd; field_simp
  rw [this, div_lt_one hnr]
  exact hQr

private theorem arcf_eq (n : ℕ) :
    arcf n = ⋃ p ∈ Pset n, Set.Icc (cen p.1 p.2 - wd n p.1) (cen p.1 p.2 + wd n p.1) := by
  ext t
  simp only [arcf, Set.mem_setOf_eq, Set.mem_iUnion, Pset, Finset.mem_sigma, Finset.mem_Icc,
    Finset.mem_filter, Finset.mem_range, Set.mem_Icc, exists_prop]
  constructor
  · rintro ⟨q, a, h1, h2, h3, h4, h5⟩
    rw [abs_le] at h5
    exact ⟨⟨q, a⟩, ⟨⟨h1, h2⟩, by dsimp only; omega, h4⟩, by linarith [h5.1], by linarith [h5.2]⟩
  · rintro ⟨⟨q, a⟩, ⟨⟨h1, h2⟩, h3, h4⟩, h5, h6⟩
    exact ⟨q, a, h1, h2, by dsimp only at h3; omega, h4, abs_le.mpr ⟨by linarith, by linarith⟩⟩

private theorem arcf_meas (n : ℕ) : MeasurableSet (arcf n) := by
  rw [arcf_eq]
  exact Finset.measurableSet_biUnion _ (fun _ _ => measurableSet_Icc)

private theorem inter_eq (n : ℕ) : Set.Icc (0 : ℝ) 1 ∩ arcf n = ⋃ p ∈ Pset n, win n p := by
  rw [arcf_eq, Set.inter_iUnion₂]
  apply Set.iUnion₂_congr
  intro p _
  unfold win
  rw [Set.Icc_inter_Icc]
  rw [max_comm, min_comm]

private theorem win_le (n : ℕ) (p : Σ _ : ℕ, ℕ) (hp : p ∈ Pset n) :
    max (cen p.1 p.2 - wd n p.1) 0 ≤ min (cen p.1 p.2 + wd n p.1) 1 := by
  obtain ⟨q, a⟩ := p
  simp only [Pset, Finset.mem_sigma, Finset.mem_Icc, Finset.mem_filter, Finset.mem_range] at hp
  have hw := wd_nonneg n q
  have hc0 : 0 ≤ cen q a := by unfold cen; positivity
  have hqr : (0 : ℝ) < q := by exact_mod_cast hp.1.1
  have hc1 : cen q a ≤ 1 := by
    unfold cen
    rw [div_le_one hqr]
    exact_mod_cast (by omega : a ≤ q)
  simp only [max_le_iff, le_min_iff]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith

private theorem win_integral (n : ℕ) (p : Σ _ : ℕ, ℕ) (hp : p ∈ Pset n) :
    ∫ t in win n p, gf n t = ∫ β in lend n p.1 p.2..rend n p.1 p.2, gf n (cen p.1 p.2 + β) := by
  have hle := win_le n p hp
  unfold win
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hle]
  rw [intervalIntegral.integral_comp_add_left (fun t => gf n t) (cen p.1 p.2)]
  have e1 : cen p.1 p.2 + lend n p.1 p.2 = max (cen p.1 p.2 - wd n p.1) 0 := by unfold lend; ring
  have e2 : cen p.1 p.2 + rend n p.1 p.2 = min (cen p.1 p.2 + wd n p.1) 1 := by unfold rend; ring
  rw [e1, e2]

private theorem major_eq (n : ℕ) (hn : 1000000 ≤ n) :
    majf n = ∑ p ∈ Pset n, ∫ β in lend n p.1 p.2..rend n p.1 p.2, gf n (cen p.1 p.2 + β) := by
  have h1 : majf n = ∫ t in Set.Icc (0 : ℝ) 1, (arcf n).indicator (gf n) t := by
    unfold majf
    rw [intervalIntegral.integral_of_le zero_le_one, MeasureTheory.integral_Icc_eq_integral_Ioc]
    rfl
  rw [h1, MeasureTheory.setIntegral_indicator (arcf_meas n), inter_eq,
    MeasureTheory.integral_biUnion_finset]
  · exact Finset.sum_congr rfl (fun p hp => win_integral n p hp)
  · intro p _; exact measurableSet_Icc
  · intro p hp p' hp' hne
    simp only [Pset, Finset.coe_sigma, Set.mem_sigma_iff, Finset.coe_Icc, Set.mem_Icc,
      Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hp hp'
    obtain ⟨q, a⟩ := p
    obtain ⟨q', a'⟩ := p'
    have := core_disjoint n hn q a q' a' hp.1.1 hp'.1.1 hp.1.2 hp'.1.2 hp.2.2 hp'.2.2 hne
    refine this.mono ?_ ?_ <;>
    · unfold win
      exact Set.Icc_subset_Icc (le_max_left _ _) (min_le_left _ _)
  · intro p _
    exact (gf_cont n).integrableOn_Icc

private theorem term_eq (n q a : ℕ) (l r : ℝ) :
    ∫ β in l..r, (umean q a * Kf n β) ^ 2 * ph (-(n : ℝ) * (cen q a + β)) =
      umean q a ^ 2 * ph (-(n : ℝ) * cen q a) * ((∫ β in l..r, ‖Kf n β‖ ^ 2 : ℝ) : ℂ) := by
  have : ∀ β, (umean q a * Kf n β) ^ 2 * ph (-(n : ℝ) * (cen q a + β)) =
      (umean q a ^ 2 * ph (-(n : ℝ) * cen q a)) * ((‖Kf n β‖ ^ 2 : ℝ) : ℂ) := by
    intro β
    rw [← K_sq n β, show -(n : ℝ) * (cen q a + β) = -(n : ℝ) * cen q a + -(n : ℝ) * β by ring, ph_add']
    ring
  simp_rw [this]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal]

private theorem ramf_one (q : ℕ) (hq : 1 ≤ q) : ramf q 1 = ((ArithmeticFunction.moebius q : ℤ) : ℂ) := by
  have := ram_coprime q 1 hq (Nat.coprime_one_left q)
  rw [← this]
  unfold ramf
  rfl

private theorem umean_eq (q a : ℕ) (hq : 1 ≤ q) (h : Nat.Coprime a q) :
    umean q a = ((ArithmeticFunction.moebius q : ℤ) : ℂ) / (q.totient : ℂ) := by
  unfold umean
  congr 1
  rw [← ram_coprime q a hq h]
  apply Finset.sum_congr rfl
  intro r _
  unfold cen
  congr 1
  ring

private theorem modeled_ge2 (n : ℕ) (hn : 1000000 ≤ n) (q : ℕ) (hq2 : 2 ≤ q) :
    ∑ a ∈ (Finset.range (q + 1)).filter (fun a => Nat.Coprime a q),
      ∫ β in lend n q a..rend n q a, (umean q a * Kf n β) ^ 2 * ph (-(n : ℝ) * (cen q a + β)) =
    (ramf q 1 / (q.totient : ℂ)) ^ 2 * (starRingEnd ℂ) (ramf q n) * (kmass n (wd n q) : ℂ) := by
  have hq : 1 ≤ q := by omega
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hfil : (Finset.range (q + 1)).filter (fun a => Nat.Coprime a q) =
      (Finset.range q).filter (fun a => Nat.Coprime a q) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, h2⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp h1 with h | h
      · exact h
      · subst h
        have := Nat.coprime_self a |>.mp h2
        omega
    · rintro ⟨h1, h2⟩
      exact ⟨by omega, h2⟩
  rw [hfil]
  have hwq := wd_mul_lt n hn q hq
  have hw0 := wd_nonneg n q
  have key : ∀ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
      ∫ β in lend n q a..rend n q a, (umean q a * Kf n β) ^ 2 * ph (-(n : ℝ) * (cen q a + β)) =
      (ramf q 1 / (q.totient : ℂ)) ^ 2 * ph (-(n : ℝ) * cen q a) * (kmass n (wd n q) : ℂ) := by
    intro a ha
    rw [Finset.mem_filter, Finset.mem_range] at ha
    have ha0 : 1 ≤ a := by
      rcases Nat.eq_zero_or_pos a with h0 | h0
      · subst h0
        have := Nat.coprime_zero_left q |>.mp ha.2
        omega
      · exact h0
    have har : (1 : ℝ) ≤ a := by exact_mod_cast ha0
    have haq : (a : ℝ) + 1 ≤ q := by exact_mod_cast ha.1
    have hc1 : wd n q ≤ cen q a := by
      unfold cen
      rw [le_div_iff₀ hqr]
      nlinarith
    have hc2 : cen q a + wd n q ≤ 1 := by
      unfold cen
      have : (a : ℝ) / q + wd n q = ((a : ℝ) + wd n q * q) / q := by field_simp
      rw [this, div_le_one hqr]
      nlinarith
    have hl : lend n q a = -wd n q := by
      unfold lend
      rw [max_eq_left (by linarith)]; ring
    have hr : rend n q a = wd n q := by
      unfold rend
      rw [min_eq_left hc2]; ring
    rw [term_eq, hl, hr, umean_eq q a hq ha.2, ramf_one q hq]
    unfold kmass
    rfl
  have hconj : ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), ph (-(n : ℝ) * cen q a) =
      (starRingEnd ℂ) (ramf q n) := by
    unfold ramf
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [ph_conj]
    unfold cen
    congr 1
    ring
  rw [Finset.sum_congr rfl key, ← Finset.sum_mul, ← Finset.mul_sum, hconj]

private theorem modeled_one (n : ℕ) (hn : 1000000 ≤ n) :
    ∑ a ∈ (Finset.range (1 + 1)).filter (fun a => Nat.Coprime a 1),
      ∫ β in lend n 1 a..rend n 1 a, (umean 1 a * Kf n β) ^ 2 * ph (-(n : ℝ) * (cen 1 a + β)) =
    (ramf 1 1 / ((1 : ℕ).totient : ℂ)) ^ 2 * (starRingEnd ℂ) (ramf 1 n) * (kmass n (wd n 1) : ℂ) := by
  have hwq := wd_mul_lt n hn 1 le_rfl
  have hw0 := wd_nonneg n 1
  have hw1 : wd n 1 ≤ 1 := by simpa using hwq.le
  have hph0 : ph 0 = 1 := by simp [ph]
  have hphn : ph (-(n : ℝ)) = 1 := by
    have := ph_nat (-(n : ℝ)) n
    rw [neg_add_cancel, hph0] at this
    exact this.symm
  have hu : ∀ a, umean 1 a = 1 := by
    intro a; simp [umean, ph]
  have hr1 : ∀ h, ramf 1 h = 1 := by
    intro h; simp [ramf, ph]
  rw [Finset.filter_true_of_mem (fun a _ => Nat.coprime_one_right a), Finset.sum_range_succ,
    Finset.sum_range_one]
  rw [term_eq, term_eq]
  have e0 : lend n 1 0 = 0 := by
    unfold lend cen; simp [hw0]
  have e1 : rend n 1 0 = wd n 1 := by
    unfold rend cen; simp [min_eq_left hw1]
  have e2 : lend n 1 1 = -wd n 1 := by
    unfold lend cen; simp [max_eq_left (show (0 : ℝ) ≤ 1 - wd n 1 by linarith)]
  have e3 : rend n 1 1 = 0 := by
    unfold rend cen; simp [min_eq_right (show (1 : ℝ) ≤ 1 + wd n 1 by linarith)]
  rw [e0, e1, e2, e3, hu, hu, hr1, hr1]
  have hc0 : cen 1 0 = 0 := by simp [cen]
  have hc1 : cen 1 1 = 1 := by simp [cen]
  rw [hc0, hc1]
  have hi : ∀ a b : ℝ, IntervalIntegrable (fun β => ‖Kf n β‖ ^ 2) MeasureTheory.volume a b :=
    fun a b => ((Kf_cont n).norm.pow 2).intervalIntegrable _ _
  have hadj := intervalIntegral.integral_add_adjacent_intervals (hi (-wd n 1) 0) (hi 0 (wd n 1))
  unfold kmass
  rw [← hadj]
  simp [hph0, hphn]
  ring

private theorem modeled_eq (n : ℕ) (hn : 1000000 ≤ n) :
    modf n = ∑ p ∈ Pset n, ∫ β in lend n p.1 p.2..rend n p.1 p.2,
      (umean p.1 p.2 * Kf n β) ^ 2 * ph (-(n : ℝ) * (cen p.1 p.2 + β)) := by
  unfold Pset
  rw [Finset.sum_sigma]
  unfold modf
  apply Finset.sum_congr rfl
  intro q hq
  rw [Finset.mem_Icc] at hq
  symm
  rcases Nat.lt_or_ge q 2 with h | h
  · have : q = 1 := by omega
    subst this
    exact modeled_one n hn
  · exact modeled_ge2 n hn q h

private theorem pcost_cont (n q a : ℕ) (D : ℝ) : Continuous (pcost n q a D) := by
  have := Kf_cont n
  unfold pcost ampf
  fun_prop

private theorem key (n : ℕ) (hn : 1000000 ≤ n) : ‖majf n - modf n‖ ≤ budf n := by
  rw [major_eq n hn, modeled_eq n hn, ← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  have hb : budf n = ∑ p ∈ Pset n, ∫ β in lend n p.1 p.2..rend n p.1 p.2,
      pcost n p.1 p.2 (discf n p.1 p.2) β := by
    unfold budf Pset
    rw [Finset.sum_sigma]
  rw [hb]
  apply Finset.sum_le_sum
  intro p hp
  have hp' := hp
  obtain ⟨q, a⟩ := p
  simp only [Pset, Finset.mem_sigma, Finset.mem_Icc] at hp'
  have hq : 1 ≤ q := hp'.1.1
  have hle : lend n q a ≤ rend n q a := by
    have := win_le n ⟨q, a⟩ hp
    unfold lend rend
    simp only at this
    linarith
  have hKc := Kf_cont n
  have i1 : IntervalIntegrable (fun β => gf n (cen q a + β)) MeasureTheory.volume (lend n q a) (rend n q a) :=
    ((gf_cont n).comp (continuous_const.add continuous_id)).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun β => (umean q a * Kf n β) ^ 2 * ph (-(n : ℝ) * (cen q a + β)))
      MeasureTheory.volume (lend n q a) (rend n q a) := by
    apply Continuous.intervalIntegrable
    unfold ph
    fun_prop
  simp only
  rw [← intervalIntegral.integral_sub i1 i2]
  refine intervalIntegral.norm_integral_le_of_norm_le hle (Filter.Eventually.of_forall ?_)
    ((pcost_cont n q a _).intervalIntegrable _ _)
  intro β _
  have e : gf n (cen q a + β) - (umean q a * Kf n β) ^ 2 * ph (-(n : ℝ) * (cen q a + β)) =
      (Sf n (cen q a + β) ^ 2 - (umean q a * Kf n β) ^ 2) * ph (-(n : ℝ) * (cen q a + β)) := by
    unfold gf; ring
  show ‖gf n (cen q a + β) - (umean q a * Kf n β) ^ 2 * ph (-(n : ℝ) * (cen q a + β))‖ ≤ _
  rw [e]
  exact pointwise_bound n q a hq β

theorem Conjectures.Goldbach.ExplicitMajorProgressionBudget :
    let E (x : ℝ) := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I); let Q (n : ℕ) := (Nat.log 2 (n + 2)) ^ 2; let width (n q : ℕ) := (Q n : ℝ) / ((q : ℝ) * n); let K (n : ℕ) (β : ℝ) := ∑ k ∈ Finset.range (n + 1), E ((k : ℝ) * β); let ram (q h : ℕ) := ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), E ((h : ℝ) * a / q); let kernelMass (n : ℕ) (b : ℝ) := intervalIntegral (fun β => ‖K n β‖ ^ 2) (-b) b MeasureTheory.volume; let modeledMajor (n : ℕ) := ∑ q ∈ Finset.Icc 1 (Q n), ((ram q 1 / (q.totient : ℂ)) ^ 2 * (starRingEnd ℂ) (ram q n)) * (kernelMass n (width n q) : ℂ); let w (k : ℕ) := if Nat.Prime k then Real.log (k : ℝ) else 0; let S (n : ℕ) (t : ℝ) := ∑ k ∈ Finset.range (n + 1), (w k : ℂ) * E ((k : ℝ) * t); let center (q a : ℕ) := (a : ℝ) / q; let arcs (n : ℕ) := {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Q n ∧ a ≤ q ∧ Nat.Coprime a q ∧ |t - center q a| ≤ width n q}; let major (n : ℕ) := intervalIntegral ((arcs n).indicator (fun t => (S n t) ^ 2 * E (-(n : ℝ) * t))) (0 : ℝ) 1 MeasureTheory.volume; let classError (m q b : ℕ) := (∑ k ∈ (Finset.range m).filter (fun k => k % q = b), w k) - (if Nat.Coprime b q then (m : ℝ) / q.totient else 0); let discrepancy (n q a : ℕ) := (Finset.range (n + 2)).sup' ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ (n + 1))⟩ (fun m => ‖∑ b ∈ Finset.range q, (classError m q b : ℂ) * E ((b : ℝ) * center q a)‖); let unitMean (q a : ℕ) := (∑ r ∈ (Finset.range q).filter (fun r => Nat.Coprime r q), E ((r : ℝ) * center q a)) / (q.totient : ℂ); let leftEnd (n q a : ℕ) := max (center q a - width n q) 0 - center q a; let rightEnd (n q a : ℕ) := min (center q a + width n q) 1 - center q a; let amplified (n : ℕ) (D β : ℝ) := D * (1 + 2 * Real.pi * n * |β|); let prefixCost (n q a : ℕ) (D β : ℝ) := amplified n D β * (2 * ‖unitMean q a * K n β‖ + amplified n D β); let progressionBudget (n : ℕ) := ∑ q ∈ Finset.Icc 1 (Q n), ∑ a ∈ (Finset.range (q + 1)).filter (fun a => Nat.Coprime a q), intervalIntegral (prefixCost n q a (discrepancy n q a)) (leftEnd n q a) (rightEnd n q a) MeasureTheory.volume; ∀ n : ℕ, 1000000 ≤ n → ‖major n - modeledMajor n‖ ≤ progressionBudget n := by
  intro E Q width K ram kernelMass modeledMajor w S center arcs major classError discrepancy unitMean leftEnd rightEnd amplified prefixCost progressionBudget
  exact key
