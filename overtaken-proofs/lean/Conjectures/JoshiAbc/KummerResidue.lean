import Mathlib

private lemma kr_core (p : ℕ) [Fact p.Prime] (hp : Odd p) (e : ℤ_[p]) :
    ∃ N : ℤ_[p], (1 + (p:ℤ_[p]) * e)^p - 1 = (p:ℤ_[p]) * ((p:ℤ_[p]) * e) * (1 + (p:ℤ_[p]) * N) := by
  obtain ⟨q, hq⟩ := hp
  set s : ℤ_[p] := 1 + (p:ℤ_[p]) * e with hs
  have hterm : ∀ i : ℕ, ∃ m : ℤ_[p], s^i = 1 + (i:ℤ_[p]) * ((p:ℤ_[p]) * e) + (p:ℤ_[p])^2 * m := by
    intro i
    induction i with
    | zero => exact ⟨0, by simp⟩
    | succ n ih =>
      obtain ⟨m, hm⟩ := ih
      refine ⟨n * e^2 + m * (1 + (p:ℤ_[p]) * e), ?_⟩
      rw [pow_succ, hm, hs]
      push_cast
      ring
  choose m hm using hterm
  have hS : (∑ i ∈ Finset.range p, i) = p * q := by
    have h2 : (∑ i ∈ Finset.range p, i) * 2 = p * (p - 1) := Finset.sum_range_id_mul_two p
    have h3 : p - 1 = 2 * q := by omega
    rw [h3] at h2
    nlinarith
  have hS' : (∑ i ∈ Finset.range p, (i:ℤ_[p])) = (p:ℤ_[p]) * q := by
    have := congrArg (fun n : ℕ => (n : ℤ_[p])) hS
    simpa [Nat.cast_sum] using this
  refine ⟨q * e + ∑ i ∈ Finset.range p, m i, ?_⟩
  have hG : (∑ i ∈ Finset.range p, s^i) = (p:ℤ_[p]) * (1 + (p:ℤ_[p]) * (q * e + ∑ i ∈ Finset.range p, m i)) := by
    rw [Finset.sum_congr rfl (fun i _ => hm i), Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.sum_mul, ← Finset.mul_sum, hS']
    simp
    ring
  have := geom_sum_mul s p
  rw [hG] at this
  rw [← this, hs]
  ring

private lemma kr_lte (p : ℕ) [Fact p.Prime] (hp : Odd p) (s : ℤ_[p]) (hs : ‖s - 1‖ < 1) :
    ‖s^p - 1‖ = ‖s - 1‖ / p := by
  obtain ⟨e, he⟩ := (PadicInt.norm_lt_one_iff_dvd _).1 hs
  obtain ⟨N, hN⟩ := kr_core p hp e
  have hse : s = 1 + (p:ℤ_[p]) * e := by linear_combination he
  have hpl : ‖(p:ℤ_[p])‖ < 1 := by
    rw [PadicInt.norm_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt)
  have hn1 : ‖1 + (p:ℤ_[p]) * N‖ = 1 := by
    have hl : ‖(p:ℤ_[p]) * N‖ < 1 := by
      rw [mul_comm]; exact PadicInt.norm_lt_one_mul hpl
    rw [PadicInt.norm_add_eq_max_of_ne (by simpa using hl.ne'), norm_one, max_eq_left hl.le]
  rw [hse, hN, norm_mul, norm_mul, hn1, PadicInt.norm_p]
  have hse' : (1 + (p:ℤ_[p]) * e) - 1 = (p:ℤ_[p]) * e := by ring
  rw [hse']
  have : ((p:ℝ)) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  field_simp

private lemma kr_lte_pow (p : ℕ) [Fact p.Prime] (hp : Odd p) (s : ℤ_[p]) (hs : ‖s - 1‖ < 1) (k : ℕ) :
    ‖s^(p^k) - 1‖ = ‖s - 1‖ / (p:ℝ)^k := by
  induction k with
  | zero => simp
  | succ n ih =>
    have hp1 : (1:ℝ) ≤ (p:ℝ)^n := one_le_pow₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt.le)
    have hlt : ‖(s^(p^n)) - 1‖ < 1 := by
      rw [ih]
      calc ‖s - 1‖ / (p:ℝ)^n ≤ ‖s - 1‖ / 1 := by
            apply div_le_div_of_nonneg_left (norm_nonneg _) one_pos hp1
        _ < 1 := by simpa using hs
    rw [pow_succ, pow_mul, kr_lte p hp _ hlt, ih, pow_succ]
    have : ((p:ℝ)) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
    field_simp

private lemma kr_root (p : ℕ) [Fact p.Prime] (hp : Odd p) (j : ℕ) (hj : 1 ≤ j) (r : ℤ_[p])
    (hr : ‖r - 1‖ ≤ (p:ℝ)^(-((j+1 : ℕ):ℤ))) :
    ∃ s : ℤ_[p], s^p = r ∧ ‖s - 1‖ ≤ (p:ℝ)^(-((j : ℕ):ℤ)) := by
  have hpp : (1:ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hp0 : (0:ℝ) < p := by linarith
  have hpl : ‖(p:ℤ_[p])‖ < 1 := by
    rw [PadicInt.norm_p]
    exact inv_lt_one_of_one_lt₀ hpp
  obtain ⟨d, hd⟩ := (Ideal.mem_span_singleton.1
    ((PadicInt.norm_le_pow_iff_mem_span_pow (r - 1) (j+1)).1 hr))
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  obtain ⟨N, hN⟩ := kr_core p hp ((p:ℤ_[p])^j' * d)
  set a : ℤ_[p] := 1 + (p:ℤ_[p]) * ((p:ℤ_[p])^j' * d) with ha
  have hau : a - 1 = (p:ℤ_[p])^(j'+1) * d := by rw [ha]; ring
  have hal : ‖a - 1‖ < 1 := by
    rw [hau, norm_mul, norm_pow, PadicInt.norm_p]
    have : ‖d‖ ≤ 1 := PadicInt.norm_le_one d
    have h1 : ((p:ℝ)⁻¹)^(j'+1) ≤ (p:ℝ)⁻¹ := pow_le_of_le_one (by positivity) (inv_le_one_of_one_le₀ hpp.le) (by omega)
    have h2 : (p:ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hpp
    calc ((p:ℝ)⁻¹)^(j'+1) * ‖d‖ ≤ ((p:ℝ)⁻¹)^(j'+1) * 1 := by gcongr
      _ < 1 := by linarith
  have ha1 : ‖a‖ = 1 := by
    have : a = 1 + (a - 1) := by ring
    rw [this, PadicInt.norm_add_eq_max_of_ne (by simpa using hal.ne')]
    simp [hal.le]
  have hFa : a^p - r = (p:ℤ_[p])^(j'+1+2) * (d * N) := by
    have h1 : a^p - 1 = (p:ℤ_[p]) * ((p:ℤ_[p]) * ((p:ℤ_[p])^j' * d)) * (1 + (p:ℤ_[p]) * N) := hN
    have h2 : r = 1 + (p:ℤ_[p])^(j'+1+1) * d := by linear_combination hd
    rw [h2]
    linear_combination h1
  set F : Polynomial ℤ_[p] := Polynomial.X^p - Polynomial.C r with hF
  have hFv : F.aeval a = a^p - r := by simp [hF]
  have hFd : F.derivative.aeval a = (p:ℤ_[p]) * a^(p-1) := by simp [hF, Polynomial.derivative_X_pow]
  have hdn : ‖F.derivative.aeval a‖ = (p:ℝ)⁻¹ := by
    rw [hFd, norm_mul, norm_pow, ha1, PadicInt.norm_p]; simp
  have hnorm : ‖F.aeval a‖ < ‖F.derivative.aeval a‖^2 := by
    rw [hFv, hFa, hdn, norm_mul, norm_pow, PadicInt.norm_p]
    have hdN : ‖d * N‖ ≤ 1 := PadicInt.norm_le_one _
    have h2 : (p:ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hpp
    have h3 : ((p:ℝ)⁻¹)^(j'+1+2) < ((p:ℝ)⁻¹)^2 :=
      pow_lt_pow_right_of_lt_one₀ (by positivity) h2 (by omega)
    calc ((p:ℝ)⁻¹)^(j'+1+2) * ‖d * N‖ ≤ ((p:ℝ)⁻¹)^(j'+1+2) * 1 := by gcongr
      _ < _ := by linarith
  obtain ⟨z, hz, hza, -, -⟩ := hensels_lemma hnorm
  have hzr : z^p = r := by simpa [hF, sub_eq_zero] using hz
  have hzl : ‖z - 1‖ < 1 := by
    have : z - 1 = (z - a) + (a - 1) := by ring
    rw [this]
    apply PadicInt.norm_lt_one_add _ hal
    rw [hdn] at hza
    exact hza.trans (inv_lt_one_of_one_lt₀ hpp)
  refine ⟨z, hzr, ?_⟩
  have := kr_lte p hp z hzl
  rw [hzr] at this
  have hp' : ((p:ℝ)) ≠ 0 := hp0.ne'
  have h5 : ‖z - 1‖ = p * ‖r - 1‖ := by
    field_simp at this
    linarith
  rw [h5]
  have h6 : (p:ℝ)^(-((j'+1+1 : ℕ):ℤ)) = (p:ℝ)^(-((j'+1 : ℕ):ℤ)) / p := by
    rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast, pow_succ]
    field_simp
  calc (p:ℝ) * ‖r - 1‖ ≤ p * (p:ℝ)^(-((j'+1+1 : ℕ):ℤ)) := by gcongr
    _ = _ := by
      rw [h6]; field_simp

private lemma kr_exists (p : ℕ) [Fact p.Prime] (hp : Odd p) (k : ℕ) :
    ∀ r : ℤ_[p], ‖r - 1‖ ≤ (p:ℝ)^(-((k+1 : ℕ):ℤ)) → ∃ s : ℤ_[p], s^(p^k) = r := by
  induction k with
  | zero => intro r _; exact ⟨r, by simp⟩
  | succ n ih =>
    intro r hr
    obtain ⟨s, hs, hsl⟩ := kr_root p hp (n+1) (by omega) r hr
    obtain ⟨t, ht⟩ := ih s hsl
    exact ⟨t, by rw [pow_succ, pow_mul, ht, hs]⟩

theorem Conjectures.JoshiAbc.KummerResidue :
    ∀ (p k : ℕ) [Fact p.Prime], Odd p → ∀ x y : PadicInt p, let u := fun (z : PadicInt p) => 1+(p:Padic p)*(z:Padic p); (∃ v : Padic p, v^(p^k)=u x/u y) ↔ ‖(x:Padic p)-y‖ ≤ (1/(p:ℝ))^k := by
  intro p k _ hp x y u
  simp only [u]
  have hpp : (1:ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hp0 : (0:ℝ) < p := by linarith
  have hpl : ‖(p:ℤ_[p])‖ < 1 := by
    rw [PadicInt.norm_p]
    exact inv_lt_one_of_one_lt₀ hpp
  have hone : ∀ z : ℤ_[p], ‖1 + (p:ℤ_[p]) * z‖ = 1 := by
    intro z
    have hl : ‖(p:ℤ_[p]) * z‖ < 1 := by
      rw [mul_comm]; exact PadicInt.norm_lt_one_mul hpl
    rw [PadicInt.norm_add_eq_max_of_ne (by simpa using hl.ne'), norm_one, max_eq_left hl.le]
  have hYn := hone y
  have hXn := hone x
  obtain ⟨Yu, hYu'⟩ := (PadicInt.isUnit_iff.2 hYn)
  have hinv : (1 + (p:ℤ_[p]) * y) * ((Yu⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) = 1 := by
    rw [← hYu']; simp
  obtain ⟨r, hr⟩ : ∃ r : ℤ_[p], r = (1 + (p:ℤ_[p]) * x) * ((Yu⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) := ⟨_, rfl⟩
  have hrY : r * (1 + (p:ℤ_[p]) * y) = 1 + (p:ℤ_[p]) * x := by
    rw [hr]
    linear_combination (1 + (p:ℤ_[p]) * x) * hinv
  have hrsub : r - 1 = (p:ℤ_[p]) * (x - y) * ((Yu⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) := by
    rw [hr]
    linear_combination hinv
  have hrn : ‖r - 1‖ = (p:ℝ)⁻¹ * ‖x - y‖ := by
    rw [hrsub, norm_mul, norm_mul, PadicInt.norm_p, PadicInt.norm_units, mul_one]
  have hr1 : ‖r‖ = 1 := by
    rw [hr, norm_mul, hXn, PadicInt.norm_units, mul_one]
  have hY0 : ((1:ℚ_[p]) + (p:ℚ_[p]) * (y:ℚ_[p])) ≠ 0 := by
    intro h0
    have : (1 + (p:ℤ_[p]) * y : ℤ_[p]) = 0 := by
      apply Subtype.ext
      simpa using h0
    rw [this] at hYn
    simp at hYn
  have hcoe : ((1:ℚ_[p]) + (p:ℚ_[p]) * (x:ℚ_[p])) / (1 + (p:ℚ_[p]) * (y:ℚ_[p])) = (r:ℚ_[p]) := by
    rw [div_eq_iff hY0]
    have := congrArg (fun z : ℤ_[p] => (z : ℚ_[p])) hrY
    simpa using this.symm
  have hnorm_eq : ‖(x:ℚ_[p]) - y‖ = ‖x - y‖ := by
    have : ‖x - y‖ = ‖((x - y : ℤ_[p]) : ℚ_[p])‖ := PadicInt.norm_def
    push_cast at this
    exact this.symm
  rw [hnorm_eq, hcoe]
  constructor
  · rintro ⟨v, hv⟩
    have hv1 : ‖v‖ = 1 := by
      have h1 := congrArg norm hv
      rw [norm_pow, ← PadicInt.norm_def, hr1] at h1
      exact (pow_eq_one_iff_of_nonneg (norm_nonneg v) (pow_pos (Fact.out : p.Prime).pos k).ne').1 h1
    obtain ⟨w, hwv⟩ : ∃ w : ℤ_[p], (w:ℚ_[p]) = v := ⟨⟨v, hv1.le⟩, rfl⟩
    have hw : w^(p^k) = r := by
      apply Subtype.ext
      rw [← hwv] at hv
      simpa using hv
    have hrl : ‖r - 1‖ < 1 := by
      rw [hrn]
      calc (p:ℝ)⁻¹ * ‖x - y‖ ≤ (p:ℝ)⁻¹ * 1 := by gcongr; exact PadicInt.norm_le_one _
        _ < 1 := by simpa using inv_lt_one_of_one_lt₀ hpp
    have hwl : ‖w - 1‖ < 1 := by
      have h1 : PadicInt.toZMod (r - 1) = 0 := by
        rw [← RingHom.mem_ker, PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits]
        exact hrl
      rw [← hw] at h1
      have h2 : PadicInt.toZMod (w - 1) = 0 := by
        rw [map_sub, map_pow, ZMod.pow_card_pow, map_one] at h1
        rw [map_sub, map_one]
        exact h1
      have h3 : w - 1 ∈ RingHom.ker (PadicInt.toZMod : ℤ_[p] →+* ZMod p) := h2
      rwa [PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits] at h3
    have hlte := kr_lte_pow p hp w hwl k
    rw [hw] at hlte
    have hwle : ‖w - 1‖ ≤ (p:ℝ)⁻¹ := by
      have := (PadicInt.norm_lt_pow_iff_norm_le_pow_sub_one (w - 1) 0).1 (by simpa using hwl)
      simpa using this
    have hpk : (0:ℝ) < (p:ℝ)^k := by positivity
    have e1 : ‖x - y‖ = p * (‖w - 1‖ / (p:ℝ)^k) := by
      rw [← hlte, hrn]; field_simp
    rw [e1, one_div, inv_pow]
    calc (p:ℝ) * (‖w - 1‖ / (p:ℝ)^k) ≤ p * ((p:ℝ)⁻¹ / (p:ℝ)^k) := by gcongr
      _ = ((p:ℝ)^k)⁻¹ := by field_simp
  · intro h
    have hb : ‖r - 1‖ ≤ (p:ℝ)^(-((k+1 : ℕ):ℤ)) := by
      rw [hrn]
      have e2 : (p:ℝ)^(-((k+1 : ℕ):ℤ)) = (p:ℝ)⁻¹ * (1/(p:ℝ))^k := by
        rw [zpow_neg, zpow_natCast, pow_succ, one_div, inv_pow, mul_inv, mul_comm]
      rw [e2]
      gcongr
    obtain ⟨s, hs⟩ := kr_exists p hp k r hb
    refine ⟨(s:ℚ_[p]), ?_⟩
    rw [← PadicInt.coe_pow, hs]
