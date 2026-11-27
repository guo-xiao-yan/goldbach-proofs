import Mathlib

private lemma normNat (p : ℕ) [Fact p.Prime] (m : ℕ) (hm : m ≠ 0) :
    ‖(m : ℚ_[p])‖ = ((p : ℝ)⁻¹) ^ (multiplicity p m) := by
  have h := padicValRat.of_nat (p := p) (n := m)
  rw [← Rat.cast_natCast, Padic.eq_padicNorm, padicNorm.eq_zpow_of_ne_zero (by exact_mod_cast hm),
    h]
  rw [Rat.cast_zpow, Rat.cast_natCast, zpow_neg, zpow_natCast, inv_pow]

private lemma val_facts (p : ℕ) [hp : Fact p.Prime] (m : ℕ) (hm : 1 ≤ m) :
    (p = 2 → multiplicity p m < m) ∧ (p ≠ 2 → 2 * multiplicity p m + 1 ≤ m) := by
  have hdvd : p ^ multiplicity p m ∣ m := pow_multiplicity_dvd p m
  have hle : p ^ multiplicity p m ≤ m := Nat.le_of_dvd (by omega) hdvd
  set v := multiplicity p m
  constructor
  · rintro rfl
    have : v < 2 ^ v := Nat.lt_two_pow_self
    omega
  · intro h2
    have hp3 : 3 ≤ p := by have := hp.out.two_le; omega
    have hb : ∀ n : ℕ, 2 * n + 1 ≤ 3 ^ n := by
      intro n
      induction n with
      | zero => simp
      | succ n ih => rw [pow_succ]; omega
    have := hb v
    have : 3 ^ v ≤ p ^ v := Nat.pow_le_pow_left hp3 v
    omega

private lemma normC (p : ℕ) [hp : Fact p.Prime] :
    ‖((if p = 2 then 4 else p : ℕ) : ℚ_[p])‖ = ((p : ℝ)⁻¹) ^ (if p = 2 then 2 else 1) := by
  by_cases h2 : p = 2
  · subst h2
    rw [if_pos rfl, if_pos rfl, normNat 2 4 (by norm_num)]
    have : multiplicity 2 4 = 2 := by
      have : (4:ℕ) = 2 ^ 2 := by norm_num
      rw [this]; exact multiplicity_pow_self_of_prime Nat.prime_two.prime 2
    rw [this]
  · rw [if_neg h2, if_neg h2, pow_one]
    exact Padic.norm_p

theorem Conjectures.JoshiAbc.PadicIsometry :
    ∀ (p : ℕ) [Fact p.Prime], let c : Padic p := if p=2 then 4 else (p:Padic p); let tau := fun (x : Padic p) => (∑' k : ℕ, (-1:Padic p)^k*(c*x)^(k+1)/((k+1:ℕ):Padic p))/c; ∀ x : Padic p, ‖x‖ ≤ 1 → ‖tau x‖ = ‖x‖ := by
  intro p hp c tau x hx
  have hpp : p.Prime := hp.out
  set q : ℝ := (p : ℝ)⁻¹ with hq
  have hp1 : (1:ℝ) < p := by exact_mod_cast hpp.one_lt
  have hq0 : 0 < q := by positivity
  have hq1 : q < 1 := inv_lt_one_of_one_lt₀ hp1
  set vc : ℕ := if p = 2 then 2 else 1 with hvc
  have hcc : c = ((if p = 2 then 4 else p : ℕ) : ℚ_[p]) := by
    simp only [c]; split_ifs <;> simp
  have hnc : ‖c‖ = q ^ vc := by rw [hcc]; exact normC p
  have hc0 : c ≠ 0 := by
    intro h; have := hnc; rw [h, norm_zero] at this
    exact (pow_pos hq0 vc).ne this
  have hcn : 0 < ‖c‖ := norm_pos_iff.2 hc0
  -- term norm
  have hterm : ∀ k : ℕ, ‖(-1:Padic p)^k*(c*x)^(k+1)/((k+1:ℕ):Padic p)‖
      = ‖c‖^(k+1) * ‖x‖^(k+1) / q ^ (multiplicity p (k+1)) := by
    intro k
    rw [norm_div, norm_mul, norm_pow, norm_pow, norm_neg, norm_one, one_pow, one_mul,
      normNat p (k+1) (by omega), norm_mul, mul_pow]
  have hbound : ∀ k : ℕ, ‖(-1:Padic p)^k*(c*x)^(k+1)/((k+1:ℕ):Padic p)‖
      ≤ q ^ (vc * (k+1) - multiplicity p (k+1)) := by
    intro k
    rw [hterm k, hnc]
    obtain ⟨h1, h2⟩ := val_facts p (k+1) (by omega)
    have hv : multiplicity p (k+1) ≤ vc * (k+1) := by
      by_cases h : p = 2
      · have := h1 h; simp only [hvc, if_pos h]; omega
      · have := h2 h; simp only [hvc, if_neg h]; omega
    have hx' : ‖x‖^(k+1) ≤ 1 := pow_le_one₀ (norm_nonneg _) hx
    rw [div_le_iff₀ (pow_pos hq0 _)]
    calc (q ^ vc) ^ (k+1) * ‖x‖^(k+1)
        ≤ (q ^ vc) ^ (k+1) * 1 := by gcongr
      _ = q ^ (vc * (k+1) - multiplicity p (k+1)) * q ^ (multiplicity p (k+1)) := by
        rw [← pow_add, Nat.sub_add_cancel hv, ← pow_mul]; ring
  have hhalf : ∀ k : ℕ, (k+1)/2 ≤ vc * (k+1) - multiplicity p (k+1) := by
    intro k
    obtain ⟨h1, h2⟩ := val_facts p (k+1) (by omega)
    by_cases h : p = 2
    · have := h1 h; simp only [hvc, if_pos h]; omega
    · have := h2 h; simp only [hvc, if_neg h]; omega
  have hsum : Summable (fun k : ℕ => (-1:Padic p)^k*(c*x)^(k+1)/((k+1:ℕ):Padic p)) := by
    apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
    rw [Nat.cofinite_eq_atTop]
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have h1 : Filter.Tendsto (fun k : ℕ => q ^ ((k+1)/2)) Filter.atTop (nhds 0) := by
      have := (tendsto_pow_atTop_nhds_zero_of_lt_one hq0.le hq1).comp
        ((Nat.tendsto_div_const_atTop (n := 2) (by norm_num)).comp (Filter.tendsto_add_atTop_nat 1))
      exact this
    refine squeeze_zero (fun k => norm_nonneg _) (fun k => ?_) h1
    exact (hbound k).trans (pow_le_pow_of_le_one hq0.le hq1.le (hhalf k))
  by_cases hx0 : x = 0
  · simp [tau, hx0]
  have hxn : 0 < ‖x‖ := norm_pos_iff.2 hx0
  have hcx : 0 < ‖c * x‖ := by rw [norm_mul]; positivity
  have h0 : ‖(-1:Padic p)^0*(c*x)^(0+1)/((0+1:ℕ):Padic p)‖ = ‖c * x‖ := by simp
  have hrest : ‖∑' k : ℕ, (-1:Padic p)^(k+1)*(c*x)^(k+1+1)/((k+1+1:ℕ):Padic p)‖ ≤ ‖c*x‖ * q := by
    apply IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (by positivity)
    intro k
    have e1 := hterm (k+1)
    rw [e1]
    obtain ⟨h1, h2⟩ := val_facts p (k+2) (by omega)
    have hv : multiplicity p (k+2) + 1 ≤ vc * (k+1) := by
      by_cases h : p = 2
      · have := h1 h; simp only [hvc, if_pos h]; omega
      · have := h2 h; simp only [hvc, if_neg h]; omega
    have hx' : ‖x‖^(k+1) ≤ 1 := pow_le_one₀ (norm_nonneg _) hx
    rw [div_le_iff₀ (pow_pos hq0 _), hnc, norm_mul, hnc]
    have : (q ^ vc) ^ (k + 1 + 1) * ‖x‖ ^ (k + 1 + 1)
        = (q ^ vc * ‖x‖) * ((q ^ vc) ^ (k + 1) * ‖x‖ ^ (k+1)) := by ring
    rw [this]
    have h3 : (q ^ vc) ^ (k + 1) * ‖x‖ ^ (k+1) ≤ q * q ^ (multiplicity p (k + 1 + 1)) := by
      calc (q ^ vc) ^ (k + 1) * ‖x‖ ^ (k+1) ≤ (q ^ vc) ^ (k + 1) * 1 := by gcongr
        _ = q ^ (vc * (k+1)) := by rw [mul_one, ← pow_mul]
        _ ≤ q ^ (1 + multiplicity p (k+2)) :=
            pow_le_pow_of_le_one hq0.le hq1.le (by omega)
        _ = _ := by rw [pow_add, pow_one]
    calc q ^ vc * ‖x‖ * ((q ^ vc) ^ (k + 1) * ‖x‖ ^ (k+1))
        ≤ q ^ vc * ‖x‖ * (q * q ^ (multiplicity p (k + 1 + 1))) := by gcongr
      _ = _ := by ring
  have hsplit := hsum.tsum_eq_zero_add
  have hlt : ‖∑' k : ℕ, (-1:Padic p)^(k+1)*(c*x)^(k+1+1)/((k+1+1:ℕ):Padic p)‖
      < ‖(-1:Padic p)^0*(c*x)^(0+1)/((0+1:ℕ):Padic p)‖ := by
    rw [h0]
    calc _ ≤ ‖c*x‖ * q := hrest
      _ < ‖c*x‖ * 1 := by gcongr
      _ = _ := mul_one _
  have hnorm : ‖∑' k : ℕ, (-1:Padic p)^k*(c*x)^(k+1)/((k+1:ℕ):Padic p)‖ = ‖c * x‖ := by
    rw [hsplit, add_comm]
    rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt.ne, max_eq_right hlt.le]
    exact h0
  simp only [tau]
  rw [norm_div, hnorm, norm_mul]
  field_simp
