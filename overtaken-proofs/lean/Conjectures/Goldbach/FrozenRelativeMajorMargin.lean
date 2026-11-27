import Mathlib

open scoped BigOperators ComplexConjugate

private noncomputable def parsevalPhase (t : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I)

namespace PEqualNP.Outside

private theorem bulkParseval :
    let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t)); ∀ n w, intervalIntegral (fun t => ‖S n w t‖^2) (0:ℝ) 1 MeasureTheory.volume = Finset.sum (Finset.range (n+1)) (fun k => (w k)^2) := by
  dsimp only
  intro n w
  let T := Finset.range (n + 1)
  let S : ℝ → ℂ := fun t => ∑ k ∈ T, (w k : ℂ) * parsevalPhase ((k : ℝ) * t)
  let z : ℝ → ℂ := fun t => ∑ k ∈ T, ∑ j ∈ T,
    ((w k : ℂ) * (w j : ℂ)) * parsevalPhase (((j : ℝ) - (k : ℝ)) * t)
  change intervalIntegral (fun t => ‖S t‖ ^ 2) (0 : ℝ) 1 MeasureTheory.volume = _
  have hphase_mul : ∀ x y : ℝ, parsevalPhase (x + y) = parsevalPhase x * parsevalPhase y := by
    intro x y
    unfold parsevalPhase
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hphase_cont : Continuous parsevalPhase := by
    unfold parsevalPhase
    fun_prop
  have hphase_exp : ∀ m : ℤ, Complex.exp (2 * (Real.pi : ℂ) * (m : ℂ) * Complex.I) = 1 := by
    intro m
    have h : 2 * (Real.pi : ℂ) * (m : ℂ) * Complex.I =
        (m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by ring
    rw [h, Complex.exp_int_mul_two_pi_mul_I]
  have hphase_one : ∀ m : ℤ, parsevalPhase (m : ℝ) = 1 := by
    intro m
    unfold parsevalPhase
    have h : (((2 * Real.pi * (m : ℝ) : ℝ) : ℂ) * Complex.I) =
        2 * (Real.pi : ℂ) * (m : ℂ) * Complex.I := by
      push_cast
      ring
    rw [h, hphase_exp m]
  have hphase_conj : ∀ x : ℝ, conj (parsevalPhase x) = parsevalPhase (-x) := by
    intro x
    unfold parsevalPhase
    rw [← Complex.exp_conj]
    congr 1
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  have horth : ∀ m : ℤ, intervalIntegral (fun t : ℝ => parsevalPhase ((m : ℝ) * t))
      (0 : ℝ) 1 MeasureTheory.volume = if m = 0 then 1 else 0 := by
    intro m
    have hrewrite : intervalIntegral (fun t : ℝ => parsevalPhase ((m : ℝ) * t))
        (0 : ℝ) 1 MeasureTheory.volume =
        ∫ t in (0 : ℝ)..1, Complex.exp ((((2 * Real.pi * (m : ℝ) : ℝ) : ℂ) * Complex.I) * (t : ℂ)) := by
      refine intervalIntegral.integral_congr (fun t _ => ?_)
      unfold parsevalPhase
      congr 1
      push_cast
      ring
    rw [hrewrite]
    by_cases hm : m = 0
    · subst hm
      simp
    · have hmr : (m : ℝ) ≠ 0 := by
        intro hzero
        exact hm (by exact_mod_cast hzero)
      have h1 : (2 * Real.pi * (m : ℝ)) ≠ 0 :=
        mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) hmr
      have hc : (((2 * Real.pi * (m : ℝ) : ℝ) : ℂ) * Complex.I) ≠ 0 := by
        have h2 : ((2 * Real.pi * (m : ℝ) : ℝ) : ℂ) ≠ 0 := by
          simpa [Complex.ofReal_eq_zero] using h1
        exact mul_ne_zero h2 Complex.I_ne_zero
      have hval : Complex.exp ((((2 * Real.pi * (m : ℝ) : ℝ) : ℂ)) * Complex.I) = 1 := by
        have hone := hphase_one m
        simpa only [parsevalPhase] using hone
      rw [integral_exp_mul_complex hc]
      simp [hphase_exp m, hm]
  have hint_single : ∀ (c : ℂ) (a : ℝ),
      IntervalIntegrable (fun t : ℝ => c * parsevalPhase (a * t)) MeasureTheory.volume (0 : ℝ) 1 := by
    intro c a
    exact (continuous_const.mul (hphase_cont.comp (by fun_prop))).intervalIntegrable (0 : ℝ) 1
  have hpoint : ∀ t : ℝ, (Complex.normSq (S t) : ℂ) = z t := by
    intro t
    rw [Complex.normSq_eq_conj_mul_self]
    dsimp only [S, z]
    rw [map_sum, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro j hj
    simp only [map_mul, Complex.conj_ofReal, hphase_conj]
    have hmul : parsevalPhase (-((k : ℝ) * t)) * parsevalPhase ((j : ℝ) * t) =
        parsevalPhase (((j : ℝ) - (k : ℝ)) * t) := by
      rw [← hphase_mul]
      congr 1
      ring
    calc
      ((w k : ℂ) * parsevalPhase (-((k : ℝ) * t))) *
          ((w j : ℂ) * parsevalPhase ((j : ℝ) * t)) =
          ((w k : ℂ) * (w j : ℂ)) *
            (parsevalPhase (-((k : ℝ) * t)) * parsevalPhase ((j : ℝ) * t)) := by ring
      _ = ((w k : ℂ) * (w j : ℂ)) * parsevalPhase (((j : ℝ) - (k : ℝ)) * t) := by
        rw [hmul]
  have hint_z : IntervalIntegrable z MeasureTheory.volume (0 : ℝ) 1 := by
    dsimp only [z]
    exact (continuous_finsetSum _ (fun k _ => continuous_finsetSum _
      (fun j _ => continuous_const.mul (hphase_cont.comp (by fun_prop))))).intervalIntegrable (0 : ℝ) 1
  have hmain : intervalIntegral z (0 : ℝ) 1 MeasureTheory.volume =
      ((∑ k ∈ T, (w k) ^ 2 : ℝ) : ℂ) := by
    dsimp only [z]
    have houter (k : ℕ) (hk : k ∈ T) : IntervalIntegrable (fun t : ℝ => ∑ j ∈ T,
        ((w k : ℂ) * (w j : ℂ)) * parsevalPhase (((j : ℝ) - (k : ℝ)) * t))
        MeasureTheory.volume (0 : ℝ) 1 := by
      exact (continuous_finsetSum _ (fun j _ => continuous_const.mul
        (hphase_cont.comp (by fun_prop)))).intervalIntegrable (0 : ℝ) 1
    rw [intervalIntegral.integral_finsetSum houter]
    have hstep : ∀ k ∈ T, intervalIntegral (fun t : ℝ => ∑ j ∈ T,
        ((w k : ℂ) * (w j : ℂ)) * parsevalPhase (((j : ℝ) - (k : ℝ)) * t))
        (0 : ℝ) 1 MeasureTheory.volume = ∑ j ∈ T,
        ((w k : ℂ) * (w j : ℂ)) * (if ((j : ℤ) - (k : ℤ)) = 0 then 1 else 0) := by
      intro k hk
      rw [intervalIntegral.integral_finsetSum (fun j _ =>
        hint_single ((w k : ℂ) * (w j : ℂ)) (((j : ℝ) - (k : ℝ))))]
      apply Finset.sum_congr rfl
      intro j hj
      rw [intervalIntegral.integral_const_mul]
      congr 1
      have hm : ((j : ℝ) - (k : ℝ)) = (((j : ℤ) - (k : ℤ) : ℤ) : ℝ) := by
        push_cast
        ring
      simp_rw [hm]
      rw [horth]
    calc
      (∑ k ∈ T, intervalIntegral (fun t : ℝ => ∑ j ∈ T,
          ((w k : ℂ) * (w j : ℂ)) * parsevalPhase (((j : ℝ) - (k : ℝ)) * t))
          (0 : ℝ) 1 MeasureTheory.volume) =
          ∑ k ∈ T, ∑ j ∈ T, ((w k : ℂ) * (w j : ℂ)) *
            (if ((j : ℤ) - (k : ℤ)) = 0 then 1 else 0) := Finset.sum_congr rfl hstep
      _ = ((∑ k ∈ T, (w k) ^ 2 : ℝ) : ℂ) := by
        push_cast
        simp only [sub_eq_zero, Int.ofNat_inj]
        apply Finset.sum_congr rfl
        intro k hk
        simp [hk, pow_two]
  have hre : intervalIntegral (fun t => (z t).re) (0 : ℝ) 1 MeasureTheory.volume =
      (intervalIntegral z (0 : ℝ) 1 MeasureTheory.volume).re := by
    rw [intervalIntegral.intervalIntegral_eq_integral_uIoc,
      intervalIntegral.intervalIntegral_eq_integral_uIoc]
    simp only [show (0 : ℝ) ≤ 1 by norm_num, ite_true, one_smul]
    exact integral_re hint_z.def'
  calc
    intervalIntegral (fun t => ‖S t‖ ^ 2) (0 : ℝ) 1 MeasureTheory.volume =
        intervalIntegral (fun t => (z t).re) (0 : ℝ) 1 MeasureTheory.volume := by
      apply intervalIntegral.integral_congr
      intro t ht
      have hp := congrArg Complex.re (hpoint t)
      simpa only [Complex.ofReal_re, Complex.normSq_eq_norm_sq] using hp
    _ = (intervalIntegral z (0 : ℝ) 1 MeasureTheory.volume).re := hre
    _ = ∑ k ∈ T, (w k) ^ 2 := by rw [hmain]; exact Complex.ofReal_re _


private theorem highEnergy :
    let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t)); let low := fun (n k : ℕ) => if k^3≤n then w k else 0; let high := fun (n k : ℕ) => w k-low n k; ∀ n:ℕ,2≤n → intervalIntegral (fun t => ‖S n (high n) t‖^2) (0:ℝ) 1 MeasureTheory.volume≤((n:ℝ)+1)*(Real.log (n:ℝ))^2 := by
  dsimp only
  intro n hn
  rw [bulkParseval n]
  calc
    _ ≤ ∑ _k ∈ Finset.range (n + 1), (Real.log (n : ℝ)) ^ 2 := by
      apply Finset.sum_le_sum
      intro k hk
      have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      by_cases hcut : k ^ 3 ≤ n
      · simp [hcut, sq_nonneg]
      · by_cases hkprime : Nat.Prime k
        · have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hkprime.one_le
          have hlog : Real.log (k : ℝ) ≤ Real.log (n : ℝ) :=
            Real.log_le_log (by linarith) (by exact_mod_cast hkn)
          simpa [hcut, hkprime] using pow_le_pow_left₀ (Real.log_nonneg hk1) hlog 2
        · simp [hcut, hkprime, sq_nonneg]
    _ = _ := by simp

end PEqualNP.Outside

namespace PEqualNP.Outside

private theorem lowCap : let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t)); let low := fun (n k : ℕ) => if k^3≤n then w k else 0; ∀ (n:ℕ) (t:ℝ), 2≤n → ‖S n (low n) t‖≤((n:ℝ)^(1/3:ℝ)+1)*Real.log (n:ℝ) := by
  intro w E S low n t hn
  let f (k : ℕ) : ℂ := (low n k : ℂ) * E ((k : ℝ) * t)
  let K := (Finset.range (n + 1)).filter (fun k => k^3 ≤ n ∧ Nat.Prime k)
  let R : ℝ := (n : ℝ) ^ (1 / 3 : ℝ)
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  have hs : ∑ k ∈ K, f k = S n (low n) t := by
    apply Finset.sum_filter_of_ne
    intro k _ hk
    by_contra! h
    by_cases hc : k^3 ≤ n
    · exact hk (by simp [f, low, w, hc, h hc])
    · exact hk (by simp [f, low, hc])
  have hcard : (K.card : ℝ) ≤ R + 1 := by
    have hsub : K ⊆ Finset.range (⌊R⌋₊ + 1) := by
      intro k hk
      obtain ⟨_, hc, _⟩ := Finset.mem_filter.mp hk
      apply Finset.mem_range.mpr
      apply Nat.lt_succ_of_le
      apply Nat.le_floor
      dsimp [R]
      rw [one_div, Real.le_rpow_inv_iff_of_pos (by positivity) (by positivity) (by norm_num)]
      norm_cast
    have hc : K.card ≤ ⌊R⌋₊ + 1 := by simpa using Finset.card_le_card hsub
    calc
      (K.card : ℝ) ≤ (⌊R⌋₊ : ℝ) + 1 := by exact_mod_cast hc
      _ ≤ R + 1 := by gcongr; exact Nat.floor_le (by dsimp [R]; positivity)
  change ‖S n (low n) t‖ ≤ (R + 1) * Real.log n
  rw [← hs]
  calc
    ‖∑ k ∈ K, f k‖ ≤ ∑ k ∈ K, ‖f k‖ := norm_sum_le _ _
    _ ≤ ∑ _k ∈ K, Real.log (n : ℝ) := by
      apply Finset.sum_le_sum
      intro k hk
      obtain ⟨hkn, hc, hp⟩ := Finset.mem_filter.mp hk
      have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hp.one_le
      simp only [f, low, hc, ite_true, w, hp, E, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hk1), Complex.norm_exp_ofReal_mul_I, mul_one]
      exact Real.log_le_log (by linarith) (by exact_mod_cast Nat.le_of_lt_succ (Finset.mem_range.mp hkn))
    _ = (K.card : ℝ) * Real.log n := by simp
    _ ≤ (R + 1) * Real.log n := mul_le_mul_of_nonneg_right hcard hlog

end PEqualNP.Outside

open MeasureTheory Filter

namespace PEqualNP.Outside

private theorem unitMeanSq (f : ℝ → ℝ) (hf : Continuous f) :
    (∫ t in (0 : ℝ)..1, f t) ^ 2 ≤ ∫ t in (0 : ℝ)..1, (f t) ^ 2 := by
  let m := ∫ t in (0 : ℝ)..1, f t
  have hnon := intervalIntegral.integral_nonneg_of_forall (μ := volume)
    (show (0 : ℝ) ≤ 1 by norm_num) (fun t : ℝ => sq_nonneg (f t - m))
  have hexp (t : ℝ) : (f t - m)^2 = ((f t)^2 - (2*m)*f t) + m^2 := by ring
  simp_rw [hexp] at hnon
  rw [intervalIntegral.integral_add, intervalIntegral.integral_sub, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const] at hnon
  · simp only [sub_zero, one_smul] at hnon
    dsimp [m] at hnon
    nlinarith
  all_goals apply Continuous.intervalIntegrable; fun_prop

private theorem sbSaving :
    let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let low := fun (n k : ℕ) => if k^3≤n then w k else 0; let high := fun (n k : ℕ) => w k-low n k; let I := fun (n:ℕ) (a b:ℕ→ℝ) => intervalIntegral (fun t => (arcs n)ᶜ.indicator (fun u => S n a u*S n b u*E (-(n:ℝ)*u)) t) (0:ℝ) 1 MeasureTheory.volume; ∀ e:ℝ, 0<e → ∃ N:ℕ, ∀ n≥N, ‖I n (low n) (high n)‖≤e*(n:ℝ) := by
  intro w E S Q arcs low high I e he
  have hsmall := (isLittleO_log_rpow_rpow_atTop (2 : ℝ) (s := 1/6) (by norm_num)).comp_tendsto
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have hev := hsmall.bound (show 0 < e / 4 by positivity)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  refine ⟨max 2 N, ?_⟩
  intro n hn
  have hn2 : 2 ≤ n := le_trans (le_max_left _ _) hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hn0 : (0 : ℝ) < n := by linarith
  have hlog := Real.log_nonneg hn1
  let R : ℝ := (n : ℝ) ^ (1/3 : ℝ)
  let B : ℝ := (n : ℝ) ^ (1/2 : ℝ)
  let D : ℝ := (n : ℝ) ^ (1/6 : ℝ)
  have hR : 1 ≤ R := Real.one_le_rpow hn1 (by norm_num)
  have hR0 : 0 ≤ R := by linarith
  have hB : 0 ≤ B := Real.rpow_nonneg hn0.le _
  have hB2 : B^2 = (n : ℝ) := by
    dsimp [B]
    rw [← Real.sqrt_eq_rpow, Real.sq_sqrt hn0.le]
  have hRBD : R*B*D = (n : ℝ) := by
    dsimp [R,B,D]
    rw [← Real.rpow_add hn0, ← Real.rpow_add hn0]; norm_num
  let f := fun t : ℝ => ‖S n (high n) t‖
  have hcont : Continuous f := by
    dsimp only [f, S, E]
    fun_prop
  have hsquare := unitMeanSq f hcont
  have henergy : (∫ t in (0:ℝ)..1, (f t)^2) ≤ ((n:ℝ)+1) * (Real.log (n:ℝ))^2 := highEnergy n hn2
  have hmean : (∫ t in (0:ℝ)..1, f t) ≤ 2 * B * Real.log n := by
    apply le_of_sq_le_sq _ (by positivity)
    calc
      _ ≤ _ := hsquare.trans henergy
      _ ≤ (2 * B * Real.log n)^2 := by
        have hnum : (n:ℝ)+1 ≤ 4 * B^2 := by rw [hB2]; linarith
        nlinarith only [mul_le_mul_of_nonneg_right hnum (sq_nonneg (Real.log n))]
  let M := (R+1)*Real.log n
  have hM : 0 ≤ M := mul_nonneg (by linarith) hlog
  have hI : ‖I n (low n) (high n)‖ ≤ M * (∫ t in (0:ℝ)..1, f t) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.norm_integral_le_of_norm_le (by norm_num)
    · apply Filter.Eventually.of_forall
      intro t _
      by_cases ht : t ∈ (arcs n)ᶜ
      · rw [Set.indicator_of_mem ht]
        simp only [norm_mul, E, Complex.norm_exp_ofReal_mul_I, mul_one]
        exact mul_le_mul_of_nonneg_right (lowCap n t hn2) (norm_nonneg _)
      · rw [Set.indicator_of_notMem ht]
        simpa using mul_nonneg hM (norm_nonneg (S n (high n) t))
    · exact (continuous_const.mul hcont).intervalIntegrable _ _
  have hpow : (Real.log (n:ℝ))^2 ≤ e/4*D := by
    have h := hN n (le_trans (le_max_right _ _) hn)
    change ‖Real.log (n:ℝ) ^ (2:ℝ)‖ ≤ e / 4 * ‖D‖ at h
    rw [Real.rpow_two, Real.norm_of_nonneg (sq_nonneg _), Real.norm_of_nonneg (Real.rpow_nonneg hn0.le _)] at h
    exact h
  calc
    ‖I n (low n) (high n)‖ ≤ M * (∫ t in (0:ℝ)..1, f t) := hI
    _ ≤ M * (2*B*Real.log n) := mul_le_mul_of_nonneg_left hmean hM
    _ ≤ 4*R*B*(Real.log n)^2 := by
      dsimp [M]
      nlinarith only [mul_nonneg (mul_nonneg (sub_nonneg.mpr hR) hB) (sq_nonneg (Real.log n))]
    _ ≤ 4*R*B*(e/4*D) := mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = e*(n:ℝ) := by rw [← hRBD]; ring

end PEqualNP.Outside

open Filter

namespace PEqualNP.Outside

private theorem ssSaving : let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let low := fun (n k : ℕ) => if k^3≤n then w k else 0; let high := fun (n k : ℕ) => w k-low n k; let I := fun (n:ℕ) (a b:ℕ→ℝ) => intervalIntegral (fun t => (arcs n)ᶜ.indicator (fun u => S n a u*S n b u*E (-(n:ℝ)*u)) t) (0:ℝ) 1 MeasureTheory.volume; ∀ e:ℝ, 0<e → ∃ N:ℕ, ∀ n≥N, ‖I n (low n) (low n)‖≤e*(n:ℝ) := by
  intro w E S Q arcs low high I e he
  have cap (n : ℕ) (t : ℝ) (hn : 2 ≤ n) :
      ‖S n (low n) t‖ ≤ ((n : ℝ) ^ (1 / 3 : ℝ) + 1) * Real.log n := by
    let f (k : ℕ) : ℂ := (low n k : ℂ) * E ((k : ℝ) * t)
    let K := (Finset.range (n + 1)).filter (fun k => k^3 ≤ n ∧ Nat.Prime k)
    let R : ℝ := (n : ℝ) ^ (1 / 3 : ℝ)
    have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
    have hs : ∑ k ∈ K, f k = S n (low n) t := by
      apply Finset.sum_filter_of_ne
      intro k _ hk
      by_contra! h
      by_cases hc : k^3 ≤ n
      · exact hk (by simp [f, low, w, hc, h hc])
      · exact hk (by simp [f, low, hc])
    have hcard : (K.card : ℝ) ≤ R + 1 := by
      have hsub : K ⊆ Finset.range (⌊R⌋₊ + 1) := by
        intro k hk
        obtain ⟨_, hc, _⟩ := Finset.mem_filter.mp hk
        apply Finset.mem_range.mpr
        apply Nat.lt_succ_of_le
        apply Nat.le_floor
        dsimp [R]
        rw [one_div, Real.le_rpow_inv_iff_of_pos (by positivity) (by positivity) (by norm_num)]
        norm_cast
      have hc : K.card ≤ ⌊R⌋₊ + 1 := by simpa using Finset.card_le_card hsub
      calc
        (K.card : ℝ) ≤ (⌊R⌋₊ : ℝ) + 1 := by exact_mod_cast hc
        _ ≤ R + 1 := by gcongr; exact Nat.floor_le (by dsimp [R]; positivity)
    change ‖S n (low n) t‖ ≤ (R + 1) * Real.log n
    rw [← hs]
    calc
      ‖∑ k ∈ K, f k‖ ≤ ∑ k ∈ K, ‖f k‖ := norm_sum_le _ _
      _ ≤ ∑ _k ∈ K, Real.log (n : ℝ) := by
        apply Finset.sum_le_sum
        intro k hk
        obtain ⟨hkn, hc, hp⟩ := Finset.mem_filter.mp hk
        have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hp.one_le
        simp only [f, low, hc, ite_true, w, hp, E, norm_mul, Complex.norm_real,
          Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hk1), Complex.norm_exp_ofReal_mul_I, mul_one]
        exact Real.log_le_log (by linarith) (by exact_mod_cast Nat.le_of_lt_succ (Finset.mem_range.mp hkn))
      _ = (K.card : ℝ) * Real.log n := by simp
      _ ≤ (R + 1) * Real.log n := mul_le_mul_of_nonneg_right hcard hlog
  have asymp := (isLittleO_log_rpow_rpow_atTop 2 (by norm_num : (0 : ℝ) < 1 / 3)).comp_tendsto
    (tendsto_natCast_atTop_atTop (R := ℝ))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (asymp.bound (by positivity : 0 < e / 4))
  refine ⟨max N 2, ?_⟩
  intro n hn
  have hn2 : 2 ≤ n := le_trans (le_max_right _ _) hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  let R : ℝ := (n : ℝ) ^ (1 / 3 : ℝ)
  have hR : 1 ≤ R := Real.one_le_rpow hn1 (by norm_num)
  have hR0 : 0 ≤ R := by linarith
  have hcube : R^3 = n := by
    dsimp [R]
    rw [← Real.rpow_mul_natCast (by positivity)]
    norm_num
  have hlog : 0 ≤ Real.log n := Real.log_nonneg hn1
  have hlog2 : (Real.log n)^2 ≤ (e / 4) * R := by
    have h := hN n (le_trans (le_max_left _ _) hn)
    change ‖(Real.log n) ^ (2 : ℝ)‖ ≤ e / 4 * ‖R‖ at h
    simpa only [Real.rpow_two, Real.norm_of_nonneg (sq_nonneg _), Real.norm_of_nonneg hR0] using h
  let B : ℝ := (R + 1) * Real.log n
  have pointwise (t : ℝ) : ‖(arcs n)ᶜ.indicator (fun u => S n (low n) u * S n (low n) u * E (-(n : ℝ) * u)) t‖ ≤ B^2 := by
    by_cases hm : t ∈ (arcs n)ᶜ
    · rw [Set.indicator_of_mem hm, norm_mul, norm_mul]
      simp only [E, Complex.norm_exp_ofReal_mul_I, mul_one, ← sq]
      exact pow_le_pow_left₀ (norm_nonneg _) (cap n t hn2) _
    · rw [Set.indicator_of_notMem hm, norm_zero]; exact sq_nonneg _
  have hint : ‖I n (low n) (low n)‖ ≤ B^2 := by
    simpa only [I, sub_zero, abs_one, mul_one] using
      intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1) (fun t _ => pointwise t)
  calc
    ‖I n (low n) (low n)‖ ≤ B^2 := hint
    _ = (R + 1)^2 * (Real.log n)^2 := mul_pow _ _ _
    _ ≤ (2 * R)^2 * ((e / 4) * R) := by
      gcongr
      linarith
    _ = e * (n : ℝ) := by rw [← hcube]; ring

end PEqualNP.Outside

open MeasureTheory

namespace GRMM

private theorem ph_mul (x y : ℝ) : parsevalPhase (x + y) = parsevalPhase x * parsevalPhase y := by
  unfold parsevalPhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem ph_cont : Continuous parsevalPhase := by
  unfold parsevalPhase
  fun_prop

private theorem ph_orth (m : ℤ) : intervalIntegral (fun t : ℝ => parsevalPhase ((m : ℝ) * t))
    (0 : ℝ) 1 MeasureTheory.volume = if m = 0 then 1 else 0 := by
  have hphase_exp : Complex.exp (2 * (Real.pi : ℂ) * (m : ℂ) * Complex.I) = 1 := by
    have h : 2 * (Real.pi : ℂ) * (m : ℂ) * Complex.I =
        (m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by ring
    rw [h, Complex.exp_int_mul_two_pi_mul_I]
  have hrewrite : intervalIntegral (fun t : ℝ => parsevalPhase ((m : ℝ) * t))
      (0 : ℝ) 1 MeasureTheory.volume =
      ∫ t in (0 : ℝ)..1, Complex.exp ((((2 * Real.pi * (m : ℝ) : ℝ) : ℂ) * Complex.I) * (t : ℂ)) := by
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    unfold parsevalPhase
    congr 1
    push_cast
    ring
  rw [hrewrite]
  by_cases hm : m = 0
  · subst hm
    simp
  · have hmr : (m : ℝ) ≠ 0 := by
      intro hzero
      exact hm (by exact_mod_cast hzero)
    have h1 : (2 * Real.pi * (m : ℝ)) ≠ 0 :=
      mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) hmr
    have hc : (((2 * Real.pi * (m : ℝ) : ℝ) : ℂ) * Complex.I) ≠ 0 := by
      have h2 : ((2 * Real.pi * (m : ℝ) : ℝ) : ℂ) ≠ 0 := by
        simpa [Complex.ofReal_eq_zero] using h1
      exact mul_ne_zero h2 Complex.I_ne_zero
    rw [integral_exp_mul_complex hc]
    have h3 : (((2 * Real.pi * (m : ℝ) : ℝ) : ℂ) * Complex.I) = 2 * (Real.pi : ℂ) * (m : ℂ) * Complex.I := by
      push_cast
      ring
    rw [h3]
    simp [hphase_exp, hm]

private theorem corr (n : ℕ) (a b : ℕ → ℝ) :
    intervalIntegral (fun t : ℝ => (∑ k ∈ Finset.range (n+1), (a k : ℂ) * parsevalPhase ((k:ℝ)*t)) *
      (∑ k ∈ Finset.range (n+1), (b k : ℂ) * parsevalPhase ((k:ℝ)*t)) * parsevalPhase (-(n:ℝ)*t))
      (0:ℝ) 1 MeasureTheory.volume
      = ((∑ p ∈ Finset.range (n+1), a p * b (n-p) : ℝ) : ℂ) := by
  set T := Finset.range (n+1) with hT
  have hpt : ∀ t : ℝ, (∑ k ∈ T, (a k : ℂ) * parsevalPhase ((k:ℝ)*t)) *
      (∑ k ∈ T, (b k : ℂ) * parsevalPhase ((k:ℝ)*t)) * parsevalPhase (-(n:ℝ)*t)
      = ∑ k ∈ T, ∑ j ∈ T, ((a k : ℂ) * (b j : ℂ)) *
          parsevalPhase ((((k:ℤ) + (j:ℤ) - (n:ℤ) : ℤ) : ℝ) * t) := by
    intro t
    rw [Finset.sum_mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have h : parsevalPhase ((k:ℝ)*t) * parsevalPhase ((j:ℝ)*t) * parsevalPhase (-(n:ℝ)*t)
        = parsevalPhase ((((k:ℤ) + (j:ℤ) - (n:ℤ) : ℤ) : ℝ) * t) := by
      rw [← ph_mul, ← ph_mul]
      congr 1
      push_cast
      ring
    calc (a k : ℂ) * parsevalPhase ((k:ℝ)*t) * ((b j : ℂ) * parsevalPhase ((j:ℝ)*t)) * parsevalPhase (-(n:ℝ)*t)
        = ((a k : ℂ) * (b j : ℂ)) * (parsevalPhase ((k:ℝ)*t) * parsevalPhase ((j:ℝ)*t) * parsevalPhase (-(n:ℝ)*t)) := by ring
      _ = _ := by rw [h]
  have hcont : ∀ (c : ℂ) (x : ℝ), Continuous (fun t : ℝ => c * parsevalPhase (x * t)) :=
    fun c x => continuous_const.mul (ph_cont.comp (by fun_prop))
  calc _ = intervalIntegral (fun t : ℝ => ∑ k ∈ T, ∑ j ∈ T, ((a k : ℂ) * (b j : ℂ)) *
          parsevalPhase ((((k:ℤ) + (j:ℤ) - (n:ℤ) : ℤ) : ℝ) * t)) (0:ℝ) 1 MeasureTheory.volume :=
        intervalIntegral.integral_congr (fun t _ => hpt t)
    _ = ∑ k ∈ T, ∑ j ∈ T, ((a k : ℂ) * (b j : ℂ)) * (if ((k:ℤ) + (j:ℤ) - (n:ℤ)) = 0 then 1 else 0) := by
        rw [intervalIntegral.integral_finsetSum (fun k _ =>
          (continuous_finsetSum _ (fun j _ => hcont _ _)).intervalIntegrable 0 1)]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [intervalIntegral.integral_finsetSum (fun j _ => (hcont _ _).intervalIntegrable 0 1)]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [intervalIntegral.integral_const_mul, ph_orth]
    _ = _ := by
        push_cast
        refine Finset.sum_congr rfl (fun k hk => ?_)
        have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
        rw [Finset.sum_eq_single (n - k)]
        · have h0 : ((k:ℤ) + ((n - k : ℕ) : ℤ) - (n:ℤ)) = 0 := by omega
          simp [h0]
        · intro j _ hj
          have h0 : ¬ ((k:ℤ) + (j:ℤ) - (n:ℤ) = 0) := by omega
          simp [h0]
        · intro h
          exact absurd (Finset.mem_range.mpr (by omega)) h

private theorem arcs_meas (Qn n : ℕ) :
    MeasurableSet {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Qn ∧ a≤q ∧ Nat.Coprime a q ∧
      |t-(a:ℝ)/(q:ℝ)| ≤ (Qn:ℝ)/((q:ℝ)*(n:ℝ))} := by
  have h : {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Qn ∧ a≤q ∧ Nat.Coprime a q ∧
      |t-(a:ℝ)/(q:ℝ)| ≤ (Qn:ℝ)/((q:ℝ)*(n:ℝ))} =
      ⋃ q : ℕ, ⋃ a : ℕ, ({t : ℝ | 1≤q ∧ q≤Qn ∧ a≤q ∧ Nat.Coprime a q} ∩
        {t : ℝ | |t-(a:ℝ)/(q:ℝ)| ≤ (Qn:ℝ)/((q:ℝ)*(n:ℝ))}) := by
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · rintro ⟨q, a, h1, h2, h3, h4, h5⟩
      exact ⟨q, a, ⟨h1, h2, h3, h4⟩, h5⟩
    · rintro ⟨q, a, ⟨h1, h2, h3, h4⟩, h5⟩
      exact ⟨q, a, h1, h2, h3, h4, h5⟩
  rw [h]
  refine MeasurableSet.iUnion (fun q => MeasurableSet.iUnion (fun a => ?_))
  refine MeasurableSet.inter (MeasurableSet.const _) ?_
  exact measurableSet_le (by fun_prop) (by fun_prop)

private theorem indInt {A : Set ℝ} (hA : MeasurableSet A) {g : ℝ → ℂ} (hg : Continuous g) :
    IntervalIntegrable (A.indicator g) MeasureTheory.volume (0:ℝ) 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)]
  exact (hg.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self).indicator hA

private theorem int_add4 (f1 f2 f3 f4 : ℝ → ℂ)
    (h1 : IntervalIntegrable f1 MeasureTheory.volume (0:ℝ) 1)
    (h2 : IntervalIntegrable f2 MeasureTheory.volume (0:ℝ) 1)
    (h3 : IntervalIntegrable f3 MeasureTheory.volume (0:ℝ) 1)
    (h4 : IntervalIntegrable f4 MeasureTheory.volume (0:ℝ) 1) :
    intervalIntegral (fun t => f1 t + f2 t + f3 t + f4 t) (0:ℝ) 1 MeasureTheory.volume
      = intervalIntegral f1 (0:ℝ) 1 MeasureTheory.volume + intervalIntegral f2 (0:ℝ) 1 MeasureTheory.volume
        + intervalIntegral f3 (0:ℝ) 1 MeasureTheory.volume + intervalIntegral f4 (0:ℝ) 1 MeasureTheory.volume := by
  rw [intervalIntegral.integral_add (f := fun t => f1 t + f2 t + f3 t) (g := f4)
    ((h1.add h2).add h3) h4,
    intervalIntegral.integral_add (f := fun t => f1 t + f2 t) (g := f3) (h1.add h2) h3,
    intervalIntegral.integral_add h1 h2]

end GRMM

theorem Conjectures.Goldbach.FrozenRelativeMajorMargin :
    let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0;
    let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I);
    let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t));
    let Q := fun n : ℕ => (Nat.log 2 (n+2))^2;
    let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))};
    let f := fun (n : ℕ) (t : ℝ) => (S n w t)^2*E (-(n:ℝ)*t);
    let major := fun n : ℕ => intervalIntegral (fun t => (arcs n).indicator (f n) t) (0:ℝ) 1 MeasureTheory.volume;
    let low := fun (n k : ℕ) => if k^3≤n then w k else 0;
    let high := fun (n k : ℕ) => w k-low n k;
    let I := fun (n:ℕ) (a b:ℕ→ℝ) => intervalIntegral (fun t => (arcs n)ᶜ.indicator (fun u => S n a u*S n b u*E (-(n:ℝ)*u)) t) (0:ℝ) 1 MeasureTheory.volume;
    ∀ c : ℝ, 0 < c → (∃ N₁ : ℕ, ∀ n : ℕ, N₁ ≤ n → Even n → c * (n : ℝ) ≤ (major n).re) → (∃ N₂ : ℕ, ∀ n : ℕ, N₂ ≤ n → Even n → -(c * (n : ℝ) / 2) ≤ (I n (high n) (high n)).re) → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → c * (n : ℝ) / 4 ≤ Finset.sum (Finset.range (n + 1)) (fun p => w p * w (n - p)) := by
  intro w E S Q arcs f major low high I c hc h1 h2
  obtain ⟨N1, hN1⟩ := h1
  obtain ⟨N2, hN2⟩ := h2
  have hss : ∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n ≥ N, ‖I n (low n) (low n)‖ ≤ e * (n : ℝ) :=
    PEqualNP.Outside.ssSaving
  have hsb : ∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n ≥ N, ‖I n (low n) (high n)‖ ≤ e * (n : ℝ) :=
    PEqualNP.Outside.sbSaving
  obtain ⟨N3, hN3⟩ := hss (c / 12) (by positivity)
  obtain ⟨N4, hN4⟩ := hsb (c / 12) (by positivity)
  have hA : ∀ n, MeasurableSet (arcs n) := fun n => GRMM.arcs_meas (Q n) n
  have hcont : ∀ n (a b : ℕ → ℝ), Continuous (fun u : ℝ => S n a u * S n b u * E (-(n:ℝ) * u)) := by
    intro n a b
    simp only [S, E]
    fun_prop
  have hint : ∀ n (a b : ℕ → ℝ), IntervalIntegrable
      ((arcs n)ᶜ.indicator (fun u : ℝ => S n a u * S n b u * E (-(n:ℝ) * u)))
      MeasureTheory.volume (0:ℝ) 1 := fun n a b => GRMM.indInt (hA n).compl (hcont n a b)
  have hS : ∀ n t, S n w t = S n (low n) t + S n (high n) t := by
    intro n t
    simp only [S, high]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    push_cast
    ring
  have hsplit : ∀ n, I n w w = I n (low n) (low n) + I n (low n) (high n) + I n (low n) (high n)
      + I n (high n) (high n) := by
    intro n
    have e1 : I n w w = intervalIntegral (fun t =>
        (arcs n)ᶜ.indicator (fun u : ℝ => S n (low n) u * S n (low n) u * E (-(n:ℝ) * u)) t
        + (arcs n)ᶜ.indicator (fun u : ℝ => S n (low n) u * S n (high n) u * E (-(n:ℝ) * u)) t
        + (arcs n)ᶜ.indicator (fun u : ℝ => S n (low n) u * S n (high n) u * E (-(n:ℝ) * u)) t
        + (arcs n)ᶜ.indicator (fun u : ℝ => S n (high n) u * S n (high n) u * E (-(n:ℝ) * u)) t)
        (0:ℝ) 1 MeasureTheory.volume := by
      show intervalIntegral _ _ _ _ = _
      congr 1
      funext t
      by_cases ht : t ∈ (arcs n)ᶜ
      · simp only [Set.indicator_of_mem ht]
        rw [hS n t]
        ring
      · simp only [Set.indicator_of_notMem ht]
        simp
    rw [e1]
    exact GRMM.int_add4 _ _ _ _ (hint n _ _) (hint n _ _) (hint n _ _) (hint n _ _)
  have hfull : ∀ n, intervalIntegral (fun t => f n t) (0:ℝ) 1 MeasureTheory.volume
      = ((Finset.sum (Finset.range (n + 1)) (fun p => w p * w (n - p)) : ℝ) : ℂ) := by
    intro n
    rw [← GRMM.corr n w w]
    apply intervalIntegral.integral_congr
    intro t _
    simp only [f, pow_two]
    rfl
  have hmaj : ∀ n, major n + I n w w
      = intervalIntegral (fun t => f n t) (0:ℝ) 1 MeasureTheory.volume := by
    intro n
    have hfc : Continuous (f n) := by
      have := hcont n w w
      have h' : f n = fun u : ℝ => S n w u * S n w u * E (-(n:ℝ) * u) := by
        funext u
        simp only [f, pow_two]
      rw [h']
      exact this
    show intervalIntegral _ _ _ _ + intervalIntegral _ _ _ _ = _
    rw [← intervalIntegral.integral_add (GRMM.indInt (hA n) hfc) (hint n w w)]
    apply intervalIntegral.integral_congr
    intro t _
    by_cases ht : t ∈ arcs n
    · have ht' : t ∉ (arcs n)ᶜ := fun h => h ht
      simp only [Set.indicator_of_mem ht, Set.indicator_of_notMem ht', add_zero]
    · have ht' : t ∈ (arcs n)ᶜ := ht
      simp only [Set.indicator_of_notMem ht, Set.indicator_of_mem ht', zero_add]
      simp only [f, pow_two]
  refine ⟨max (max N1 N2) (max N3 N4), fun n hn hev => ?_⟩
  have hnN1 : N1 ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hnN2 : N2 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hnN3 : N3 ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hnN4 : N4 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  have a1 := hN1 n hnN1 hev
  have a2 := hN2 n hnN2 hev
  have a3 := hN3 n hnN3
  have a4 := hN4 n hnN4
  have r1' := abs_le.mp ((Complex.abs_re_le_norm (I n (low n) (low n))).trans a3)
  have r2' := abs_le.mp ((Complex.abs_re_le_norm (I n (low n) (high n))).trans a4)
  have hre := congrArg Complex.re ((hmaj n).trans (hfull n))
  rw [Complex.add_re, hsplit n] at hre
  simp only [Complex.add_re, Complex.ofReal_re] at hre
  have hn0 : (0:ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith [r1'.1, r1'.2, r2'.1, r2'.2, a1, a2, hre]
