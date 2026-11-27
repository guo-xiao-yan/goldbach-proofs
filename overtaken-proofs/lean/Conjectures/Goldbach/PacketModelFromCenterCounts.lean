import Mathlib

open MeasureTheory

namespace PeakTails

section
open Finset

private theorem inv_totient_le_pairs (q : ℕ) (hq : 0 < q) :
    1 / (q.totient : ℝ) ≤ ∑ ab ∈ q.divisorsAntidiagonal, ((ab.1:ℝ)⁻¹ * (ab.2:ℝ)⁻¹) := by
  have hφ := Nat.totient_pos.mpr hq
  have hcount : q ≤ q.divisors.card * q.totient := by
    calc
      _ = ∑ d ∈ q.divisors, d.totient := (Nat.sum_totient q).symm
      _ ≤ ∑ _ ∈ q.divisors, q.totient := sum_le_sum (fun d hd =>
        Nat.le_of_dvd hφ (Nat.totient_dvd_of_dvd (Nat.dvd_of_mem_divisors hd)))
      _ = _ := by simp
  calc
    _ ≤ (q.divisors.card : ℝ) / q := (div_le_div_iff₀ (by exact_mod_cast hφ) (by exact_mod_cast hq)).mpr
      (by rw [one_mul]; exact_mod_cast hcount)
    _ = ∑ _ ∈ q.divisorsAntidiagonal, (q:ℝ)⁻¹ := by
      rw [Nat.sum_divisorsAntidiagonal (fun _ _ => (q:ℝ)⁻¹)]; simp [div_eq_mul_inv]
    _ = _ := by
      apply sum_congr rfl
      intro ab hab
      rw [← (Nat.mem_divisorsAntidiagonal.mp hab).1, Nat.cast_mul, mul_inv]

private theorem sum_inv_totient_le (Q : ℕ) :
    (∑ q ∈ Icc 1 Q, 1 / (q.totient : ℝ)) ≤ (1 + Real.log Q)^2 := by
  let S := Icc 1 Q
  let w := fun ab : ℕ × ℕ => (ab.1:ℝ)⁻¹ * (ab.2:ℝ)⁻¹
  have hf (q : ℕ) (hq : q ∈ S) :
      q.divisorsAntidiagonal = (S ×ˢ S).filter (fun ab : ℕ × ℕ => ab.1*ab.2=q) := by
    obtain ⟨hq0,hqQ⟩ := mem_Icc.mp hq
    ext ab
    constructor
    · intro hab
      have hf := Nat.fst_mem_divisors_of_mem_antidiagonal hab
      have hs := Nat.snd_mem_divisors_of_mem_antidiagonal hab
      have hm (a : ℕ) (ha : a ∈ q.divisors) : a ∈ S :=
        mem_Icc.mpr ⟨Nat.pos_of_mem_divisors ha,(Nat.le_of_dvd hq0 (Nat.dvd_of_mem_divisors ha)).trans hqQ⟩
      exact mem_filter.mpr ⟨mem_product.mpr ⟨hm _ hf,hm _ hs⟩,(Nat.mem_divisorsAntidiagonal.mp hab).1⟩
    · intro hab
      exact Nat.mem_divisorsAntidiagonal.mpr ⟨(mem_filter.mp hab).2,by omega⟩
  have hsum : (∑ i ∈ S, (i:ℝ)⁻¹) ≤ 1+Real.log Q := by
    simpa only [S,harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast] using harmonic_le_one_add_log Q
  calc
    _ ≤ ∑ q ∈ S, ∑ ab ∈ q.divisorsAntidiagonal, w ab :=
      sum_le_sum (fun q hq => inv_totient_le_pairs q (mem_Icc.mp hq).1)
    _ = ∑ q ∈ S, ∑ ab ∈ (S ×ˢ S).filter (fun ab : ℕ × ℕ => ab.1*ab.2=q), w ab :=
      sum_congr rfl (fun q hq => by rw [hf q hq])
    _ = ∑ ab ∈ (S ×ˢ S).filter (fun ab : ℕ × ℕ => ab.1*ab.2 ∈ S), w ab :=
      sum_fiberwise_eq_sum_filter _ _ _ _
    _ ≤ ∑ ab ∈ S ×ˢ S, w ab := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => by dsimp [w]; positivity)
    _ = (∑ i ∈ S, (i:ℝ)⁻¹)^2 := by rw [sq,sum_product,sum_mul_sum]
    _ ≤ _ := pow_le_pow_left₀ (sum_nonneg fun _ _ => by positivity) hsum 2


end

open Set

private theorem tail_left (c r K : ℝ) (hr : 0 < r) (hK : 0 ≤ K) (g : ℝ → ℝ)
    (hgb : ∀ t, t ≤ c - r → g t ≤ K / (c - t) ^ 2) (hgi : IntegrableOn g (Icc 0 (c - r))) :
    ∫ t in Ioc (0 : ℝ) (c - r), g t ≤ K / r := by
  by_cases h : c - r ≤ 0
  · rw [Set.Ioc_eq_empty (not_lt.mpr h), Measure.restrict_empty, integral_zero_measure]
    positivity
  · push_neg at h
    rw [← intervalIntegral.integral_of_le h.le]
    have hcr : r < c := by linarith
    have hG : ContinuousOn (fun t : ℝ => K / (c - t)) (Icc 0 (c - r)) := by
      refine ContinuousOn.div (f := fun _ : ℝ => K) (g := fun t : ℝ => c - t) continuousOn_const
        (continuous_const.sub continuous_id).continuousOn ?_
      intro t ht
      have := ht.2
      exact (show (0 : ℝ) < c - t by linarith).ne'
    have hD : ∀ t ∈ Ioo (0 : ℝ) (c - r),
        HasDerivWithinAt (fun t : ℝ => K / (c - t)) (K / (c - t) ^ 2) (Ioi t) t := by
      intro t ht
      have ht2 := ht.2
      have hne : c - t ≠ 0 := (show (0 : ℝ) < c - t by linarith).ne'
      have h1 : HasDerivAt (fun t : ℝ => c - t) (-1) t := by
        simpa using (hasDerivAt_id t).const_sub c
      have h2 := (hasDerivAt_const t K).div h1 hne
      have h3 : HasDerivAt (fun t : ℝ => K / (c - t)) (K / (c - t) ^ 2) t := by
        convert h2 using 1
        field_simp
        ring
      exact h3.hasDerivWithinAt
    have key := intervalIntegral.integral_le_sub_of_hasDeriv_right_of_le (a := 0) (b := c - r)
      (g := fun t : ℝ => K / (c - t)) (g' := fun t : ℝ => K / (c - t) ^ 2) (φ := g) h.le
      hG hD hgi (fun t ht => hgb t ht.2.le)
    refine key.trans ?_
    simp only [sub_sub_cancel, sub_zero]
    have : 0 ≤ K / c := by
      apply div_nonneg hK; linarith
    linarith

private theorem tail_right (c r K : ℝ) (hr : 0 < r) (hK : 0 ≤ K) (g : ℝ → ℝ)
    (hgb : ∀ t, c + r ≤ t → g t ≤ K / (t - c) ^ 2) (hgi : IntegrableOn g (Icc (c + r) 1)) :
    ∫ t in Ioc (c + r) 1, g t ≤ K / r := by
  by_cases h : 1 ≤ c + r
  · rw [Set.Ioc_eq_empty (not_lt.mpr h), Measure.restrict_empty, integral_zero_measure]
    positivity
  · push_neg at h
    rw [← intervalIntegral.integral_of_le h.le]
    have hG : ContinuousOn (fun t : ℝ => - K / (t - c)) (Icc (c + r) 1) := by
      refine ContinuousOn.div (f := fun _ : ℝ => - K) (g := fun t : ℝ => t - c) continuousOn_const
        (continuous_id.sub continuous_const).continuousOn ?_
      intro t ht
      have := ht.1
      exact (show (0 : ℝ) < t - c by linarith).ne'
    have hD : ∀ t ∈ Ioo (c + r) 1,
        HasDerivWithinAt (fun t : ℝ => - K / (t - c)) (K / (t - c) ^ 2) (Ioi t) t := by
      intro t ht
      have ht2 := ht.1
      have hne : t - c ≠ 0 := (show (0 : ℝ) < t - c by linarith).ne'
      have h1 : HasDerivAt (fun t : ℝ => t - c) 1 t := by
        simpa using (hasDerivAt_id t).sub_const c
      have h2 := (hasDerivAt_const t (-K)).div h1 hne
      have h3 : HasDerivAt (fun t : ℝ => - K / (t - c)) (K / (t - c) ^ 2) t := by
        convert h2 using 1
        field_simp
        ring
      exact h3.hasDerivWithinAt
    have key := intervalIntegral.integral_le_sub_of_hasDeriv_right_of_le (a := c + r) (b := 1)
      (g := fun t : ℝ => - K / (t - c)) (g' := fun t : ℝ => K / (t - c) ^ 2) (φ := g) h.le
      hG hD hgi (fun t ht => hgb t ht.1.le)
    refine key.trans ?_
    have hc1 : 0 < 1 - c := by linarith
    have : 0 ≤ K / (1 - c) := div_nonneg hK hc1.le
    have e : -K / (1 - c) - -K / (c + r - c) = K / r - K / (1 - c) := by
      rw [show c + r - c = r by ring]; ring
    rw [e]; linarith

private theorem tail_one (n c r w : ℝ) (hn : 0 < n) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hr : 0 < r)
    (hw : 0 < w) :
    intervalIntegral ({t : ℝ | r < |t - c|}.indicator
      (fun t => 4 * n ^ 2 / (w ^ 2 * (1 + (n * (t - c)) ^ 2)))) 0 1 volume ≤ 8 / (w ^ 2 * r) := by
  set g : ℝ → ℝ := fun t => 4 * n ^ 2 / (w ^ 2 * (1 + (n * (t - c)) ^ 2)) with hg
  have hgc : Continuous g := by
    have hden : Continuous (fun t : ℝ => w ^ 2 * (1 + (n * (t - c)) ^ 2)) := by fun_prop
    exact (continuous_const (y := 4 * n ^ 2)).div hden (fun t => by positivity)
  have hg0 : ∀ t, 0 ≤ g t := fun t => by simp only [hg]; positivity
  have hS : MeasurableSet {t : ℝ | r < |t - c|} :=
    measurableSet_lt measurable_const (by fun_prop)
  have hK : (0 : ℝ) ≤ 4 / w ^ 2 := by positivity
  have hbl : ∀ t, t ≤ c - r → g t ≤ (4 / w ^ 2) / (c - t) ^ 2 := by
    intro t ht
    have h1 : 0 < c - t := by linarith
    have e : (n * (t - c)) ^ 2 = n ^ 2 * (c - t) ^ 2 := by ring
    simp only [hg]
    rw [div_div, div_le_div_iff₀ (by positivity) (by positivity), e]
    nlinarith [sq_nonneg w]
  have hbr : ∀ t, c + r ≤ t → g t ≤ (4 / w ^ 2) / (t - c) ^ 2 := by
    intro t ht
    have h1 : 0 < t - c := by linarith
    simp only [hg]
    rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg w]
  rw [intervalIntegral.integral_of_le zero_le_one, setIntegral_indicator hS]
  have hT : Ioc (0 : ℝ) 1 ∩ {t | r < |t - c|} ⊆ Ioc 0 (c - r) ∪ Ioc (c + r) 1 := by
    intro t ht
    obtain ⟨⟨h0, h1⟩, h2⟩ := ht
    simp only [mem_setOf_eq] at h2
    rcases lt_abs.mp h2 with h | h
    · right; exact ⟨by linarith, h1⟩
    · left; exact ⟨h0, by linarith⟩
  have hdisj : Disjoint (Ioc (0 : ℝ) (c - r)) (Ioc (c + r) 1) := by
    rw [Set.disjoint_left]
    intro t h1 h2
    have := h1.2
    have := h2.1
    linarith
  have hi : ∀ a b : ℝ, IntegrableOn g (Ioc a b) := fun a b => hgc.integrableOn_Ioc
  calc ∫ t in Ioc (0 : ℝ) 1 ∩ {t | r < |t - c|}, g t
      ≤ ∫ t in Ioc (0 : ℝ) (c - r) ∪ Ioc (c + r) 1, g t :=
        setIntegral_mono_set ((hi _ _).union (hi _ _)) (ae_of_all _ hg0) (Filter.Eventually.of_forall fun x hx => hT hx)
    _ = (∫ t in Ioc (0 : ℝ) (c - r), g t) + ∫ t in Ioc (c + r) 1, g t :=
        setIntegral_union hdisj measurableSet_Ioc (hi _ _) (hi _ _)
    _ ≤ (4 / w ^ 2) / r + (4 / w ^ 2) / r :=
        (add_le_add (tail_left c r _ hr hK g hbl (hgc.integrableOn_Icc))
          (tail_right c r _ hr hK g hbr (hgc.integrableOn_Icc)))
    _ = 8 / (w ^ 2 * r) := by field_simp; ring

private noncomputable def QQ (n : ℕ) : ℕ := (Nat.log 2 (n + 2)) ^ 2

private theorem inner_bd (n q : ℕ) (hn : 0 < n) (hq : 1 ≤ q) (Qr : ℝ) (hQ : 0 < Qr) :
    ∑ a ∈ (Finset.range (q + 1)).filter (fun a => Nat.Coprime a q),
      intervalIntegral ({t : ℝ | Qr ^ 2 / (n : ℝ) < |t - (a : ℝ) / (q : ℝ)|}.indicator
        (fun t => 4 * (n : ℝ) ^ 2 / ((Nat.totient q : ℝ) ^ 2 *
          (1 + ((n : ℝ) * (t - (a : ℝ) / (q : ℝ))) ^ 2)))) 0 1 volume ≤
      16 * (n : ℝ) / ((Nat.totient q : ℝ) * Qr ^ 2) := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hφ : 0 < Nat.totient q := Nat.totient_pos.mpr hq
  have hφr : (0 : ℝ) < Nat.totient q := by exact_mod_cast hφ
  have hterm : ∀ a ∈ (Finset.range (q + 1)).filter (fun a => Nat.Coprime a q),
      intervalIntegral ({t : ℝ | Qr ^ 2 / (n : ℝ) < |t - (a : ℝ) / (q : ℝ)|}.indicator
        (fun t => 4 * (n : ℝ) ^ 2 / ((Nat.totient q : ℝ) ^ 2 *
          (1 + ((n : ℝ) * (t - (a : ℝ) / (q : ℝ))) ^ 2)))) 0 1 volume ≤
        8 * (n : ℝ) / ((Nat.totient q : ℝ) ^ 2 * Qr ^ 2) := by
    intro a ha
    have ha' := Finset.mem_range.mp (Finset.mem_filter.mp ha).1
    have h := tail_one (n : ℝ) ((a : ℝ) / q) (Qr ^ 2 / (n : ℝ)) (Nat.totient q : ℝ) hnr
      (by positivity) ((div_le_one hqr).mpr (by exact_mod_cast Nat.lt_succ_iff.mp ha'))
      (by positivity) hφr
    refine h.trans (le_of_eq ?_)
    field_simp
  have hcard : (((Finset.range (q + 1)).filter (fun a => Nat.Coprime a q)).card : ℝ) ≤
      2 * (Nat.totient q : ℝ) := by
    have hsub : (Finset.range (q + 1)).filter (fun a => Nat.Coprime a q) ⊆
        insert q ((Finset.range q).filter (Nat.Coprime q)) := by
      intro a ha
      rw [Finset.mem_filter, Finset.mem_range] at ha
      rw [Finset.mem_insert, Finset.mem_filter, Finset.mem_range]
      by_cases h : a = q
      · left; exact h
      · right; exact ⟨by omega, ha.2.symm⟩
    have h1 := (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
    have h2 : ((Finset.range q).filter (Nat.Coprime q)).card = Nat.totient q := rfl
    have h3 : ((Finset.range (q + 1)).filter (fun a => Nat.Coprime a q)).card ≤
        2 * Nat.totient q := by omega
    exact_mod_cast h3
  calc _ ≤ ∑ a ∈ (Finset.range (q + 1)).filter (fun a => Nat.Coprime a q),
        8 * (n : ℝ) / ((Nat.totient q : ℝ) ^ 2 * Qr ^ 2) := Finset.sum_le_sum hterm
    _ = (((Finset.range (q + 1)).filter (fun a => Nat.Coprime a q)).card : ℝ) *
        (8 * (n : ℝ) / ((Nat.totient q : ℝ) ^ 2 * Qr ^ 2)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 * (Nat.totient q : ℝ)) * (8 * (n : ℝ) / ((Nat.totient q : ℝ) ^ 2 * Qr ^ 2)) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = 16 * (n : ℝ) / ((Nat.totient q : ℝ) * Qr ^ 2) := by field_simp; ring

private theorem main_pt (ε : ℝ) (hε : 0 < ε) : ∃ N : ℕ, ∀ n ≥ N,
    (∑ q ∈ Finset.Icc 1 ((QQ n) ^ 2), ∑ a ∈ (Finset.range (q + 1)).filter
      (fun a => Nat.Coprime a q),
      intervalIntegral ({t : ℝ | (QQ n : ℝ) ^ 2 / (n : ℝ) < |t - (a : ℝ) / (q : ℝ)|}.indicator
        (fun t => 4 * (n : ℝ) ^ 2 / ((Nat.totient q : ℝ) ^ 2 *
          (1 + ((n : ℝ) * (t - (a : ℝ) / (q : ℝ))) ^ 2)))) 0 1 volume) ≤ ε * (n : ℝ) := by
  refine ⟨2 ^ ⌈256 / ε⌉₊, fun n hn => ?_⟩
  have hn0 : 0 < n := lt_of_lt_of_le (pow_pos (by norm_num) _) hn
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn0
  have hlog : ⌈256 / ε⌉₊ ≤ Nat.log 2 (n + 2) :=
    Nat.le_log_of_pow_le (by norm_num) (by omega)
  have h1 : ⌈256 / ε⌉₊ ≤ QQ n := by
    unfold QQ
    calc ⌈256 / ε⌉₊ ≤ Nat.log 2 (n + 2) := hlog
      _ ≤ (Nat.log 2 (n + 2)) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hQ1' : 1 ≤ ⌈256 / ε⌉₊ := Nat.ceil_pos.mpr (by positivity)
  have hQ1 : (1 : ℝ) ≤ (QQ n : ℝ) := by exact_mod_cast hQ1'.trans h1
  have hQ : 256 / ε ≤ (QQ n : ℝ) := by
    calc 256 / ε ≤ (⌈256 / ε⌉₊ : ℝ) := Nat.le_ceil _
      _ ≤ (QQ n : ℝ) := by exact_mod_cast h1
  have hQpos : (0 : ℝ) < (QQ n : ℝ) := lt_of_lt_of_le (by positivity) hQ
  set Qr : ℝ := (QQ n : ℝ) with hQr
  have hsum := sum_inv_totient_le (QQ n ^ 2)
  have hlogb : (1 + Real.log ((QQ n ^ 2 : ℕ) : ℝ)) ^ 2 ≤ 16 * Qr := by
    have h1 : Real.log Qr ≤ 2 * Real.sqrt Qr - 2 := by
      have := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hQpos)
      rw [Real.log_sqrt hQpos.le] at this
      linarith
    have h2 : Real.log ((QQ n ^ 2 : ℕ) : ℝ) = 2 * Real.log Qr := by
      push_cast; rw [Real.log_pow]; push_cast; ring
    rw [h2]
    have h3 : 0 ≤ 1 + 2 * Real.log Qr := by
      have := Real.log_nonneg (show (1 : ℝ) ≤ Qr from hQ1)
      linarith
    have h4 : 1 + 2 * Real.log Qr ≤ 4 * Real.sqrt Qr := by linarith [Real.sqrt_nonneg Qr]
    calc (1 + 2 * Real.log Qr) ^ 2 ≤ (4 * Real.sqrt Qr) ^ 2 := pow_le_pow_left₀ h3 h4 2
      _ = 16 * Qr := by rw [mul_pow, Real.sq_sqrt hQpos.le]; ring
  have hmain : (∑ q ∈ Finset.Icc 1 ((QQ n) ^ 2), ∑ a ∈ (Finset.range (q + 1)).filter
      (fun a => Nat.Coprime a q),
      intervalIntegral ({t : ℝ | Qr ^ 2 / (n : ℝ) < |t - (a : ℝ) / (q : ℝ)|}.indicator
        (fun t => 4 * (n : ℝ) ^ 2 / ((Nat.totient q : ℝ) ^ 2 *
          (1 + ((n : ℝ) * (t - (a : ℝ) / (q : ℝ))) ^ 2)))) 0 1 volume) ≤
      ∑ q ∈ Finset.Icc 1 ((QQ n) ^ 2), 16 * (n : ℝ) / Qr ^ 2 * (1 / (Nat.totient q : ℝ)) := by
    apply Finset.sum_le_sum
    intro q hq
    refine (inner_bd n q hn0 (Finset.mem_Icc.mp hq).1 Qr hQpos).trans (le_of_eq ?_)
    have hφ : (0 : ℝ) < Nat.totient q := by
      exact_mod_cast Nat.totient_pos.mpr (Finset.mem_Icc.mp hq).1
    field_simp
  refine hmain.trans ?_
  rw [← Finset.mul_sum]
  calc 16 * (n : ℝ) / Qr ^ 2 * ∑ q ∈ Finset.Icc 1 (QQ n ^ 2), 1 / (Nat.totient q : ℝ)
      ≤ 16 * (n : ℝ) / Qr ^ 2 * (16 * Qr) := by
        apply mul_le_mul_of_nonneg_left (hsum.trans hlogb) (by positivity)
    _ = 256 * n / Qr := by field_simp; ring
    _ ≤ ε * n := by
        rw [div_le_iff₀ hQpos]
        have : 256 ≤ ε * Qr := by
          have := (div_le_iff₀ hε).mp hQ
          linarith
        nlinarith

end PeakTails

private theorem peak_full (n q : ℕ) (c : ℝ) (hn : 0 < n) (hq : 1 ≤ q) :
    ∫ t in (0:ℝ)..1, 4*(n:ℝ)^2/((Nat.totient q:ℝ)^2*(1+((n:ℝ)*(t-c))^2)) ≤
      4*Real.pi*(n:ℝ)/(Nat.totient q:ℝ)^2 := by
  have hφ : (0:ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.mpr hq
  have hnr : (0:ℝ) < n := by exact_mod_cast hn
  set w : ℝ := (Nat.totient q : ℝ) with hw
  have hd : ∀ t ∈ Set.uIcc (0:ℝ) 1, HasDerivAt (fun x => 4*(n:ℝ)/w^2 * Real.arctan ((n:ℝ)*(x-c)))
      (4*(n:ℝ)^2/(w^2*(1+((n:ℝ)*(t-c))^2))) t := by
    intro t _
    have h1 : HasDerivAt (fun x:ℝ => (n:ℝ)*(x-c)) ((n:ℝ)*1) t :=
      ((hasDerivAt_id t).sub_const c).const_mul (n:ℝ)
    have h2 := (h1.arctan).const_mul (4*(n:ℝ)/w^2)
    convert h2 using 1
    field_simp
  have hc : Continuous (fun t : ℝ => 4*(n:ℝ)^2/(w^2*(1+((n:ℝ)*(t-c))^2))) := by
    have hden : Continuous (fun t : ℝ => w ^ 2 * (1 + ((n:ℝ) * (t - c)) ^ 2)) := by fun_prop
    exact (continuous_const (y := 4 * (n:ℝ) ^ 2)).div hden (fun t => by positivity)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable 0 1)]
  have a1 := Real.arctan_lt_pi_div_two ((n:ℝ)*(1-c))
  have a2 := Real.neg_pi_div_two_lt_arctan ((n:ℝ)*(0-c))
  have hk : 0 ≤ 4*(n:ℝ)/w^2 := by positivity
  have : 4*(n:ℝ)/w^2 * Real.arctan ((n:ℝ)*(1-c)) - 4*(n:ℝ)/w^2 * Real.arctan ((n:ℝ)*(0-c)) ≤ 4*(n:ℝ)/w^2 * Real.pi := by
    rw [← mul_sub]
    exact mul_le_mul_of_nonneg_left (by linarith) hk
  calc _ ≤ _ := this
    _ = _ := by ring

private theorem K_lip (L : ℕ) (hL : 1 ≤ L) (t c : ℝ) :
    |(∑ j ∈ Finset.range L, Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L:ℝ) -
      (∑ j ∈ Finset.range L, Real.cos (2*Real.pi*(2:ℝ)^(j+1)*c))/(L:ℝ)| ≤
      2*Real.pi*(2:ℝ)^L*|t-c| := by
  have hLr : (0:ℝ) < L := by exact_mod_cast hL
  rw [← sub_div, ← Finset.sum_sub_distrib, abs_div, abs_of_pos hLr, div_le_iff₀ hLr]
  calc |∑ j ∈ Finset.range L, (Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t) - Real.cos (2*Real.pi*(2:ℝ)^(j+1)*c))|
      ≤ ∑ j ∈ Finset.range L, |Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t) - Real.cos (2*Real.pi*(2:ℝ)^(j+1)*c)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range L, 2*Real.pi*(2:ℝ)^L*|t-c| := by
        apply Finset.sum_le_sum
        intro j hj
        refine (Real.abs_cos_sub_cos_le _ _).trans ?_
        have h1 : (2:ℝ)^(j+1) ≤ (2:ℝ)^L :=
          pow_le_pow_right₀ (by norm_num) (Finset.mem_range.mp hj)
        have : 2*Real.pi*(2:ℝ)^(j+1)*t - 2*Real.pi*(2:ℝ)^(j+1)*c = (2*Real.pi*(2:ℝ)^(j+1)) * (t-c) := by ring
        rw [this, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2*Real.pi*(2:ℝ)^(j+1))]
        apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
        have := Real.pi_pos
        nlinarith
    _ = 2*Real.pi*(2:ℝ)^L*|t-c| * L := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

private theorem twoL (n : ℕ) (hn : 4 ≤ n) :
    ((2:ℝ)^(max 1 (Nat.log 2 n / 2)))^2 ≤ n := by
  have h2 : 2 ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by norm_num) (by omega)
  have hm : max 1 (Nat.log 2 n / 2) = Nat.log 2 n / 2 := by
    apply max_eq_right; omega
  rw [hm, ← pow_mul]
  have h3 : Nat.log 2 n / 2 * 2 ≤ Nat.log 2 n := by omega
  have h4 : (2:ℕ)^(Nat.log 2 n / 2 * 2) ≤ n :=
    (Nat.pow_le_pow_right (by norm_num) h3).trans (Nat.pow_log_le_self 2 (by omega))
  exact_mod_cast h4

private theorem asym : ∃ N : ℕ, ∀ n ≥ N,
    (24*Real.pi*((Nat.log 2 (n+2):ℕ):ℝ)^4)^2 ≤ (n:ℝ) := by
  have hM : (0:ℝ) < (24*Real.pi)^2*4 := by positivity
  have ht := tendsto_pow_const_div_const_pow_of_one_lt 8 (one_lt_two : (1:ℝ) < 2)
  obtain ⟨l0, hl0⟩ := Filter.eventually_atTop.mp
    (ht.eventually (gt_mem_nhds (show (0:ℝ) < 1 / ((24*Real.pi)^2*4) by positivity)))
  refine ⟨2 ^ (max l0 2), fun n hn => ?_⟩
  have hl : max l0 2 ≤ Nat.log 2 (n+2) := Nat.le_log_of_pow_le (by norm_num) (by omega)
  set l := Nat.log 2 (n+2) with hl_def
  have h1 := hl0 l ((le_max_left _ _).trans hl)
  have h2 : ((24*Real.pi)^2*4) * (l:ℝ)^8 < 2^l := by
    rw [div_lt_div_iff₀ (by positivity) hM] at h1
    linarith
  have h3 : 2^l ≤ n + 2 := (Nat.pow_log_le_self 2 (by omega))
  have h4 : 4 ≤ 2^l := by
    calc 4 = 2^2 := by norm_num
      _ ≤ 2^l := Nat.pow_le_pow_right (by norm_num) ((le_max_right _ _).trans hl)
  have h3r : (2:ℝ)^l ≤ n + 2 := by exact_mod_cast h3
  have h4r : (4:ℝ) ≤ 2^l := by exact_mod_cast h4
  have : (24*Real.pi*(l:ℝ)^4)^2 = (24*Real.pi)^2 * (l:ℝ)^8 := by ring
  rw [this]
  have : 0 ≤ (24*Real.pi)^2 * (l:ℝ)^8 := by positivity
  nlinarith

private noncomputable def pk (n q a : ℕ) (t : ℝ) : ℝ :=
  4*(n:ℝ)^2/((Nat.totient q:ℝ)^2*(1+((n:ℝ)*(t-(a:ℝ)/(q:ℝ)))^2))

private noncomputable def nearU (n q a Qn : ℕ) (t : ℝ) : ℝ :=
  if q ≤ Qn then {t : ℝ | (Qn:ℝ)/((q:ℝ)*(n:ℝ)) < |t-(a:ℝ)/(q:ℝ)|}.indicator (pk n q a) t
  else pk n q a t

private noncomputable def farU (n q a Qn : ℕ) (t : ℝ) : ℝ :=
  {t : ℝ | (Qn:ℝ)^2/(n:ℝ) < |t-(a:ℝ)/(q:ℝ)|}.indicator (pk n q a) t

private theorem pk_nonneg (n q a : ℕ) (t : ℝ) : 0 ≤ pk n q a t := by
  unfold pk; positivity

private theorem pk_cont (n q a : ℕ) (hq : 1 ≤ q) : Continuous (pk n q a) := by
  have hφ : (0:ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.mpr hq
  unfold pk
  have hden : Continuous (fun t : ℝ => (Nat.totient q:ℝ)^2 * (1 + ((n:ℝ) * (t - (a:ℝ)/(q:ℝ))) ^ 2)) := by
    fun_prop
  exact (continuous_const (y := 4 * (n:ℝ) ^ 2)).div hden (fun t => by positivity)

private theorem nearU_ii (n q a Qn : ℕ) (hq : 1 ≤ q) :
    IntervalIntegrable (nearU n q a Qn) volume 0 1 := by
  unfold nearU
  split_ifs
  · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    exact ((pk_cont n q a hq).integrableOn_Ioc).indicator
      (measurableSet_lt measurable_const (by fun_prop))
  · exact (pk_cont n q a hq).intervalIntegrable 0 1

private theorem farU_ii (n q a Qn : ℕ) (hq : 1 ≤ q) :
    IntervalIntegrable (farU n q a Qn) volume 0 1 := by
  unfold farU
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  exact ((pk_cont n q a hq).integrableOn_Ioc).indicator
    (measurableSet_lt measurable_const (by fun_prop))

private theorem nearU_nonneg (n q a Qn : ℕ) (t : ℝ) : 0 ≤ nearU n q a Qn t := by
  unfold nearU
  split_ifs
  · exact Set.indicator_nonneg (fun s _ => pk_nonneg n q a s) t
  · exact pk_nonneg n q a t

private theorem farU_nonneg (n q a Qn : ℕ) (t : ℝ) : 0 ≤ farU n q a Qn t := by
  unfold farU
  exact Set.indicator_nonneg (fun s _ => pk_nonneg n q a s) t

private theorem nearU_int (n q a Qn : ℕ) (hn : 0 < n) (hq : 1 ≤ q) (ha : a ≤ q) (hQ : 1 ≤ Qn) :
    ∫ t in (0:ℝ)..1, nearU n q a Qn t ≤
      8*Real.pi*(n:ℝ)*min 1 ((q:ℝ)/(Qn:ℝ)) / (Nat.totient q:ℝ)^2 := by
  have hφ : (0:ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.mpr hq
  have hnr : (0:ℝ) < n := by exact_mod_cast hn
  have hqr : (0:ℝ) < q := by exact_mod_cast hq
  have hQr : (0:ℝ) < Qn := by exact_mod_cast hQ
  by_cases hqQ : q ≤ Qn
  · have hqQr : (q:ℝ) ≤ Qn := by exact_mod_cast hqQ
    have hmin : min 1 ((q:ℝ)/(Qn:ℝ)) = (q:ℝ)/(Qn:ℝ) :=
      min_eq_right ((div_le_one hQr).mpr hqQr)
    have hnu : nearU n q a Qn = {t : ℝ | (Qn:ℝ)/((q:ℝ)*(n:ℝ)) < |t-(a:ℝ)/(q:ℝ)|}.indicator
        (fun t => 4 * (n:ℝ) ^ 2 / ((Nat.totient q:ℝ) ^ 2 * (1 + ((n:ℝ) * (t - (a:ℝ)/(q:ℝ))) ^ 2))) := by
      funext t; unfold nearU pk; rw [if_pos hqQ]
    have hc0 : 0 ≤ (a:ℝ)/(q:ℝ) := by positivity
    have hc1 : (a:ℝ)/(q:ℝ) ≤ 1 := (div_le_one hqr).mpr (by exact_mod_cast ha)
    have := PeakTails.tail_one (n:ℝ) ((a:ℝ)/(q:ℝ)) ((Qn:ℝ)/((q:ℝ)*(n:ℝ))) (Nat.totient q:ℝ)
      hnr hc0 hc1 (by positivity) hφ
    rw [hnu, hmin]
    refine this.trans ?_
    have e : 8 / ((Nat.totient q:ℝ) ^ 2 * ((Qn:ℝ) / ((q:ℝ) * (n:ℝ)))) =
        8 * (n:ℝ) * ((q:ℝ)/(Qn:ℝ)) / (Nat.totient q:ℝ)^2 := by
      field_simp
    rw [e]
    have hp : (1:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
    have h0 : 0 ≤ 8 * (n:ℝ) * ((q:ℝ)/(Qn:ℝ)) := by positivity
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith
  · have hqQr : (Qn:ℝ) ≤ q := by exact_mod_cast (not_le.mp hqQ).le
    have hmin : min 1 ((q:ℝ)/(Qn:ℝ)) = 1 :=
      min_eq_left ((one_le_div hQr).mpr hqQr)
    have hnu : nearU n q a Qn = pk n q a := by
      funext t; unfold nearU; rw [if_neg hqQ]
    rw [hnu, hmin]
    have := peak_full n q ((a:ℝ)/(q:ℝ)) hn hq
    refine this.trans ?_
    have hp := Real.pi_pos
    rw [mul_one]
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith

private noncomputable def Kf (n : ℕ) (t : ℝ) : ℝ :=
  (∑ j ∈ Finset.range (max 1 (Nat.log 2 n / 2)), Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t)) /
    ((max 1 (Nat.log 2 n / 2) : ℕ) : ℝ)

private theorem ii_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ)
    (h : ∀ i ∈ s, IntervalIntegrable (f i) volume 0 1) :
    IntervalIntegrable (fun t => ∑ i ∈ s, f i t) volume 0 1 := by
  have := IntervalIntegrable.sum s h
  convert this using 1
  ext t
  simp [Finset.sum_apply]

private theorem ii_gate (p : Prop) [Decidable p] (f : ℝ → ℝ)
    (h : IntervalIntegrable f volume 0 1) :
    IntervalIntegrable (fun t => if p then f t else 0) volume 0 1 := by
  by_cases hp : p
  · simpa [hp] using h
  · simp [hp]

private theorem core (n Qn : ℕ) (hn : 4 ≤ n) (hQ : 1 ≤ Qn)
    (hsmall : 12*Real.pi*(2:ℝ)^(max 1 (Nat.log 2 n / 2))*(Qn:ℝ)^2 ≤ n) (B : Set ℝ)
    (hB1 : ∀ t ∈ B, 1/2 < Kf n t)
    (hB2 : ∀ t ∈ B, ∀ q a : ℕ, 1 ≤ q → q ≤ Qn → a ≤ q → Nat.Coprime a q →
      (Qn:ℝ)/((q:ℝ)*(n:ℝ)) < |t-(a:ℝ)/(q:ℝ)|) :
    intervalIntegral (B.indicator (fun t => ∑ q ∈ Finset.Icc 1 (Qn^2),
        ∑ a ∈ (Finset.range (q+1)).filter (fun a => Nat.Coprime a q), pk n q a t)) 0 1 volume ≤
      (∑ q ∈ Finset.Icc 1 (Qn^2), ∑ a ∈ (Finset.range (q+1)).filter (fun a => Nat.Coprime a q),
        intervalIntegral (farU n q a Qn) 0 1 volume) +
      8*Real.pi*(n:ℝ) * ∑ q ∈ Finset.Icc 1 (Qn^2),
        min (1:ℝ) ((q:ℝ)/(Qn:ℝ)) * (((Finset.range (q+1)).filter (fun a => Nat.Coprime a q ∧
          (1:ℝ)/3 < Kf n ((a:ℝ)/(q:ℝ)))).card : ℝ) / (Nat.totient q:ℝ)^2 := by
  classical
  have hn0 : 0 < n := by omega
  have hnr : (0:ℝ) < n := by exact_mod_cast hn0
  set U : ℕ → ℕ → ℝ → ℝ := fun q a t => farU n q a Qn t +
    (if (1:ℝ)/3 < Kf n ((a:ℝ)/(q:ℝ)) then nearU n q a Qn t else 0) with hU
  have hUii : ∀ q ∈ Finset.Icc 1 (Qn^2), ∀ a, IntervalIntegrable (U q a) volume 0 1 := by
    intro q hq a
    have hq1 := (Finset.mem_Icc.mp hq).1
    refine (farU_ii n q a Qn hq1).add ?_
    exact ii_gate _ _ (nearU_ii n q a Qn hq1)
  have hUnn : ∀ q a t, 0 ≤ U q a t := by
    intro q a t
    simp only [hU]
    have := farU_nonneg n q a Qn t
    have := nearU_nonneg n q a Qn t
    split_ifs <;> linarith
  have hpt : ∀ t, B.indicator (fun t => ∑ q ∈ Finset.Icc 1 (Qn^2),
        ∑ a ∈ (Finset.range (q+1)).filter (fun a => Nat.Coprime a q), pk n q a t) t ≤
      ∑ q ∈ Finset.Icc 1 (Qn^2), ∑ a ∈ (Finset.range (q+1)).filter (fun a => Nat.Coprime a q),
        U q a t := by
    intro t
    by_cases ht : t ∈ B
    · rw [Set.indicator_of_mem ht]
      apply Finset.sum_le_sum; intro q hq
      apply Finset.sum_le_sum; intro a ha
      obtain ⟨hq1, hq2⟩ := Finset.mem_Icc.mp hq
      obtain ⟨ha1, ha2⟩ := Finset.mem_filter.mp ha
      have haq : a ≤ q := by have := Finset.mem_range.mp ha1; omega
      by_cases hf : (Qn:ℝ)^2/(n:ℝ) < |t-(a:ℝ)/(q:ℝ)|
      · have hfar : farU n q a Qn t = pk n q a t := by
          unfold farU; exact Set.indicator_of_mem (show t ∈ {t : ℝ | (Qn:ℝ)^2/(n:ℝ) < |t-(a:ℝ)/(q:ℝ)|} from hf) _
        simp only [hU]
        have := nearU_nonneg n q a Qn t
        split_ifs <;> linarith
      · push_neg at hf
        have hL : 1 ≤ max 1 (Nat.log 2 n / 2) := le_max_left _ _
        have hlip := K_lip (max 1 (Nat.log 2 n / 2)) hL t ((a:ℝ)/(q:ℝ))
        have h6 : 2*Real.pi*(2:ℝ)^(max 1 (Nat.log 2 n / 2))*|t-(a:ℝ)/(q:ℝ)| ≤ 1/6 := by
          have h1 : 2*Real.pi*(2:ℝ)^(max 1 (Nat.log 2 n / 2))*|t-(a:ℝ)/(q:ℝ)| ≤
              2*Real.pi*(2:ℝ)^(max 1 (Nat.log 2 n / 2))*((Qn:ℝ)^2/(n:ℝ)) :=
            mul_le_mul_of_nonneg_left hf (by positivity)
          refine h1.trans ?_
          rw [← mul_div_assoc, div_le_iff₀ hnr]
          nlinarith
        have hKc : (1:ℝ)/3 < Kf n ((a:ℝ)/(q:ℝ)) := by
          have h2 := hB1 t ht
          have h3 := (abs_le.mp (hlip.trans h6)).2
          unfold Kf at h2 ⊢
          linarith
        have hnear : nearU n q a Qn t = pk n q a t := by
          unfold nearU
          by_cases hqQ : q ≤ Qn
          · rw [if_pos hqQ]
            exact Set.indicator_of_mem (hB2 t ht q a hq1 hqQ haq (Finset.mem_filter.mp ha).2) _
          · rw [if_neg hqQ]
        simp only [hU]
        rw [if_pos hKc, hnear]
        have := farU_nonneg n q a Qn t
        linarith
    · rw [Set.indicator_of_notMem ht]
      apply Finset.sum_nonneg; intro q _
      apply Finset.sum_nonneg; intro a _
      exact hUnn q a t
  have hsumii : IntervalIntegrable (fun t => ∑ q ∈ Finset.Icc 1 (Qn^2),
        ∑ a ∈ (Finset.range (q+1)).filter (fun a => Nat.Coprime a q), U q a t) volume 0 1 := by
    exact ii_sum _ _ (fun q hq => ii_sum _ _ (fun a _ => hUii q hq a))
  have hmono : intervalIntegral (B.indicator (fun t => ∑ q ∈ Finset.Icc 1 (Qn^2),
        ∑ a ∈ (Finset.range (q+1)).filter (fun a => Nat.Coprime a q), pk n q a t)) 0 1 volume ≤
      ∫ t in (0:ℝ)..1, ∑ q ∈ Finset.Icc 1 (Qn^2),
        ∑ a ∈ (Finset.range (q+1)).filter (fun a => Nat.Coprime a q), U q a t := by
    rw [intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le zero_le_one]
    refine integral_mono_of_nonneg ?_ ?_ ?_
    · refine Filter.Eventually.of_forall (fun t => ?_)
      by_cases ht : t ∈ B
      · rw [Pi.zero_apply, Set.indicator_of_mem ht]
        apply Finset.sum_nonneg; intro q _
        apply Finset.sum_nonneg; intro a _
        exact pk_nonneg n q a t
      · rw [Pi.zero_apply, Set.indicator_of_notMem ht]
    · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp hsumii
    · exact Filter.Eventually.of_forall hpt
  refine hmono.trans ?_
  rw [intervalIntegral.integral_finsetSum (fun q hq => ii_sum _ _ (fun a _ => hUii q hq a))]
  have hq_bd : ∀ q ∈ Finset.Icc 1 (Qn^2),
      ∫ t in (0:ℝ)..1, ∑ a ∈ (Finset.range (q+1)).filter (fun a => Nat.Coprime a q), U q a t ≤
      (∑ a ∈ (Finset.range (q+1)).filter (fun a => Nat.Coprime a q),
        intervalIntegral (farU n q a Qn) 0 1 volume) +
      8*Real.pi*(n:ℝ) * (min (1:ℝ) ((q:ℝ)/(Qn:ℝ)) * (((Finset.range (q+1)).filter
        (fun a => Nat.Coprime a q ∧ (1:ℝ)/3 < Kf n ((a:ℝ)/(q:ℝ)))).card : ℝ) /
        (Nat.totient q:ℝ)^2) := by
    intro q hq
    have hq1 := (Finset.mem_Icc.mp hq).1
    rw [intervalIntegral.integral_finsetSum (fun a _ => hUii q hq a)]
    have hsplit : ∀ a, intervalIntegral (U q a) 0 1 volume =
        intervalIntegral (farU n q a Qn) 0 1 volume +
        intervalIntegral (fun t => if (1:ℝ)/3 < Kf n ((a:ℝ)/(q:ℝ)) then nearU n q a Qn t else 0) 0 1 volume := by
      intro a
      apply intervalIntegral.integral_add (farU_ii n q a Qn hq1)
      exact ii_gate _ _ (nearU_ii n q a Qn hq1)
    simp only [hsplit]
    rw [Finset.sum_add_distrib]
    gcongr 1
    set bnd : ℝ := 8*Real.pi*(n:ℝ)*min (1:ℝ) ((q:ℝ)/(Qn:ℝ)) / (Nat.totient q:ℝ)^2 with hbnd
    have h1 : ∀ a ∈ (Finset.range (q+1)).filter (fun a => Nat.Coprime a q),
        intervalIntegral (fun t => if (1:ℝ)/3 < Kf n ((a:ℝ)/(q:ℝ)) then nearU n q a Qn t else 0) 0 1 volume ≤
        if (1:ℝ)/3 < Kf n ((a:ℝ)/(q:ℝ)) then bnd else 0 := by
      intro a ha
      obtain ⟨ha1, _⟩ := Finset.mem_filter.mp ha
      have haq : a ≤ q := by have := Finset.mem_range.mp ha1; omega
      by_cases h : (1:ℝ)/3 < Kf n ((a:ℝ)/(q:ℝ))
      · simp only [h, if_true]
        exact nearU_int n q a Qn hn0 hq1 haq hQ
      · simp only [if_neg h]
        simp
    refine (Finset.sum_le_sum h1).trans (le_of_eq ?_)
    rw [← Finset.sum_filter, Finset.filter_filter, Finset.sum_const, nsmul_eq_mul, hbnd]
    ring
  refine (Finset.sum_le_sum hq_bd).trans (le_of_eq ?_)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]

theorem Conjectures.Goldbach.PacketModelFromCenterCounts :
    (let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let L := fun n : ℕ => max 1 (Nat.log 2 n / 2); let K := fun (n : ℕ) (t : ℝ) => (∑ j ∈ Finset.range (L n), Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L n:ℝ); let o := fun n q : ℕ => q % 2 = 1 ∧ ((Finset.Icc 1 ((Nat.log 2 (Q n)+1)^2)).filter (fun j => q ∣ 2^j-1)).Nonempty; ∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ n ≥ N, (∑ q ∈ (Finset.Icc 1 ((Q n)^2)).filter (fun q => o n q), min (1:ℝ) ((q:ℝ)/(Q n:ℝ)) * (((Finset.range (q+1)).filter (fun a => Nat.Coprime a q ∧ (1:ℝ)/3 < K n ((a:ℝ)/(q:ℝ)))).card:ℝ) / (Nat.totient q:ℝ)^2) ≤ ε) → (let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let L := fun n : ℕ => max 1 (Nat.log 2 n / 2); let K := fun (n : ℕ) (t : ℝ) => (∑ j ∈ Finset.range (L n), Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L n:ℝ); let o := fun n q : ℕ => q % 2 = 1 ∧ ((Finset.Icc 1 ((Nat.log 2 (Q n)+1)^2)).filter (fun j => q ∣ 2^j-1)).Nonempty; ∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ n ≥ N, (∑ q ∈ (Finset.Icc 1 ((Q n)^2)).filter (fun q => ¬ o n q), min (1:ℝ) ((q:ℝ)/(Q n:ℝ)) * (((Finset.range (q+1)).filter (fun a => Nat.Coprime a q ∧ (1:ℝ)/3 < K n ((a:ℝ)/(q:ℝ)))).card:ℝ) / (Nat.totient q:ℝ)^2) ≤ ε) → (let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let L := fun n : ℕ => max 1 (Nat.log 2 n / 2); let K := fun (n : ℕ) (t : ℝ) => (∑ j ∈ Finset.range (L n), Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L n:ℝ); let B := fun n : ℕ => {t : ℝ | t ∉ arcs n ∧ (1:ℝ)/2 < K n t}; let G := fun (n : ℕ) (t : ℝ) => ∑ q ∈ Finset.Icc 1 ((Q n)^2), ∑ a ∈ (Finset.range (q+1)).filter (fun a => Nat.Coprime a q), 4*(n:ℝ)^2 / ((Nat.totient q:ℝ)^2 * (1+((n:ℝ)*(t-(a:ℝ)/(q:ℝ)))^2)); let m := fun (s : Set ℝ) (f : ℝ → ℝ) => intervalIntegral (s.indicator f) (0:ℝ) 1 MeasureTheory.volume; ∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ n ≥ N, m (B n) (G n) ≤ ε*(n:ℝ)) := by
  intro h1 h2
  dsimp only at h1 h2 ⊢
  intro ε hε
  have hπ := Real.pi_pos
  obtain ⟨N1, hN1⟩ := h1 (ε / (32 * Real.pi)) (by positivity)
  obtain ⟨N2, hN2⟩ := h2 (ε / (32 * Real.pi)) (by positivity)
  obtain ⟨N3, hN3⟩ := PeakTails.main_pt (ε / 2) (by positivity)
  obtain ⟨N4, hN4⟩ := asym
  refine ⟨max (max N1 N2) (max N3 (max N4 4)), fun n hn => ?_⟩
  have hn1 : n ≥ N1 := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hn2 : n ≥ N2 := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hn3 : n ≥ N3 := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hn4 : n ≥ N4 :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) hn
  have hn5 : 4 ≤ n :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)) hn
  have hnr : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hl1 : 1 ≤ Nat.log 2 (n+2) := Nat.le_log_of_pow_le (by norm_num) (by omega)
  have hQ : 1 ≤ (Nat.log 2 (n+2))^2 := Nat.one_le_pow _ _ (by omega)
  have hsmall : 12*Real.pi*(2:ℝ)^(max 1 (Nat.log 2 n / 2))*(((Nat.log 2 (n+2))^2 : ℕ):ℝ)^2 ≤ n := by
    have h4 := hN4 n hn4
    have h5 := twoL n hn5
    have hy : 0 ≤ (2:ℝ)^(max 1 (Nat.log 2 n / 2)) := by positivity
    have hx : 0 ≤ 24*Real.pi*((Nat.log 2 (n+2):ℕ):ℝ)^4 := by positivity
    have hxy : (24*Real.pi*((Nat.log 2 (n+2):ℕ):ℝ)^4) * (2:ℝ)^(max 1 (Nat.log 2 n / 2)) ≤ n := by
      nlinarith [sq_nonneg (24*Real.pi*((Nat.log 2 (n+2):ℕ):ℝ)^4 - (2:ℝ)^(max 1 (Nat.log 2 n / 2)))]
    have : 12*Real.pi*(2:ℝ)^(max 1 (Nat.log 2 n / 2))*(((Nat.log 2 (n+2))^2 : ℕ):ℝ)^2 =
        ((24*Real.pi*((Nat.log 2 (n+2):ℕ):ℝ)^4) * (2:ℝ)^(max 1 (Nat.log 2 n / 2))) / 2 := by
      push_cast; ring
    rw [this]
    linarith
  have hcore := core n ((Nat.log 2 (n+2))^2) hn5 hQ hsmall
    {t : ℝ | (¬ ∃ q a : ℕ, 1≤q ∧ q≤(Nat.log 2 (n+2))^2 ∧ a≤q ∧ Nat.Coprime a q ∧
        |t-(a:ℝ)/(q:ℝ)| ≤ (((Nat.log 2 (n+2))^2 : ℕ):ℝ)/((q:ℝ)*(n:ℝ))) ∧
      (1:ℝ)/2 < Kf n t}
    (fun t ht => ht.2)
    (fun t ht q a hq1 hqQ haq hcop => by
      by_contra hcon
      exact ht.1 ⟨q, a, hq1, hqQ, haq, hcop, not_lt.mp hcon⟩)
  have hfar := hN3 n hn3
  have hX1 := hN1 n hn1
  have hX2 := hN2 n hn2
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 (((Nat.log 2 (n+2))^2)^2))
    (fun q => q % 2 = 1 ∧ ((Finset.Icc 1 ((Nat.log 2 (((Nat.log 2 (n+2))^2)) + 1)^2)).filter
      (fun j => q ∣ 2^j-1)).Nonempty)
    (fun q => min (1:ℝ) ((q:ℝ)/(((Nat.log 2 (n+2))^2 : ℕ):ℝ)) *
      (((Finset.range (q+1)).filter (fun a => Nat.Coprime a q ∧
        (1:ℝ)/3 < Kf n ((a:ℝ)/(q:ℝ)))).card : ℝ) / (Nat.totient q:ℝ)^2)
  have hS := hsplit
  refine hcore.trans ?_
  have hS2 : (∑ q ∈ Finset.Icc 1 (((Nat.log 2 (n+2))^2)^2),
      min (1:ℝ) ((q:ℝ)/(((Nat.log 2 (n+2))^2 : ℕ):ℝ)) *
      (((Finset.range (q+1)).filter (fun a => Nat.Coprime a q ∧
        (1:ℝ)/3 < Kf n ((a:ℝ)/(q:ℝ)))).card : ℝ) / (Nat.totient q:ℝ)^2) ≤
      ε / (32 * Real.pi) + ε / (32 * Real.pi) := by
    rw [← hS]
    exact add_le_add hX1 hX2
  have h8 : 8*Real.pi*(n:ℝ) * (∑ q ∈ Finset.Icc 1 (((Nat.log 2 (n+2))^2)^2),
      min (1:ℝ) ((q:ℝ)/(((Nat.log 2 (n+2))^2 : ℕ):ℝ)) *
      (((Finset.range (q+1)).filter (fun a => Nat.Coprime a q ∧
        (1:ℝ)/3 < Kf n ((a:ℝ)/(q:ℝ)))).card : ℝ) / (Nat.totient q:ℝ)^2) ≤ ε / 2 * n := by
    calc _ ≤ 8*Real.pi*(n:ℝ) * (ε / (32 * Real.pi) + ε / (32 * Real.pi)) :=
          mul_le_mul_of_nonneg_left hS2 (by positivity)
      _ = ε / 2 * n := by field_simp; ring
  have hfar' : (∑ q ∈ Finset.Icc 1 (((Nat.log 2 (n+2))^2)^2),
      ∑ a ∈ (Finset.range (q+1)).filter (fun a => Nat.Coprime a q),
        intervalIntegral (farU n q a ((Nat.log 2 (n+2))^2)) 0 1 volume) ≤ ε / 2 * n := hfar
  linarith
