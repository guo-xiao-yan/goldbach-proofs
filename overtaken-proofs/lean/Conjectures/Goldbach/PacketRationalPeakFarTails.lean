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

theorem Conjectures.Goldbach.PacketRationalPeakFarTails :
    let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let m := fun (s : Set ℝ) (f : ℝ → ℝ) => intervalIntegral (s.indicator f) (0:ℝ) 1 MeasureTheory.volume; ∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ n ≥ N, (∑ q ∈ Finset.Icc 1 ((Q n)^2), ∑ a ∈ (Finset.range (q+1)).filter (fun a => Nat.Coprime a q), m {t : ℝ | (Q n:ℝ)^2/(n:ℝ) < |t-(a:ℝ)/(q:ℝ)|} (fun t => 4*(n:ℝ)^2 / ((Nat.totient q:ℝ)^2*(1+((n:ℝ)*(t-(a:ℝ)/(q:ℝ)))^2)))) ≤ ε*(n:ℝ) := by
  intro Q m ε hε
  obtain ⟨N, hN⟩ := PeakTails.main_pt ε hε
  exact ⟨N, hN⟩
