import Mathlib
import PEqualNP.Outside.L_twin_primes_ap_short_error
import PEqualNP.Outside.L_twin_primes_hard_cutoff

open Filter Topology

private lemma an_pow (n : ℕ) {s : ℝ} (hs : 0 < s) :
    Tendsto (fun x : ℝ => (Real.log (2 + x)) ^ n / x ^ s) atTop (nhds 0) := by
  have h0 := (isLittleO_log_rpow_rpow_atTop (n : ℝ) hs).tendsto_div_nhds_zero
  have h1 : Tendsto (fun x : ℝ => (2:ℝ) ^ n * (Real.log x ^ (n:ℝ) / x ^ s)) atTop (nhds 0) := by
    simpa using h0.const_mul ((2:ℝ) ^ n)
  refine squeeze_zero' ?_ ?_ h1
  · filter_upwards [eventually_gt_atTop 0] with x hx
    have : 0 ≤ Real.log (2 + x) := Real.log_nonneg (by linarith)
    positivity
  · filter_upwards [eventually_ge_atTop 2] with x hx
    have hx0 : 0 < x := by linarith
    have hl : Real.log (2 + x) ≤ 2 * Real.log x := by
      have : Real.log (2 + x) ≤ Real.log (x ^ 2) :=
        Real.log_le_log (by linarith) (by nlinarith)
      rw [Real.log_pow] at this
      simpa using this
    have hl0 : 0 ≤ Real.log (2 + x) := Real.log_nonneg (by linarith)
    have hxs : 0 < x ^ s := Real.rpow_pos_of_pos hx0 s
    rw [Real.rpow_natCast, ← mul_div_assoc, ← mul_pow]
    gcongr

private lemma an_floorD :
    Tendsto (fun X : ℕ => Nat.floor (Real.sqrt X / (Real.log (2 + (X:ℝ))) ^ 5)) atTop atTop := by
  have h := an_pow 5 (s := 1/2) (by norm_num)
  have hp : Tendsto (fun x : ℝ => (Real.log (2 + x)) ^ 5 / x ^ (1/2:ℝ)) atTop (nhdsWithin 0 (Set.Ioi 0)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨h, ?_⟩
    filter_upwards [eventually_gt_atTop 0] with x hx
    have : 0 < Real.log (2 + x) := Real.log_pos (by linarith)
    simp only [Set.mem_Ioi]
    positivity
  have h2 := hp.inv_tendsto_nhdsGT_zero
  have h3 : Tendsto (fun x : ℝ => Real.sqrt x / (Real.log (2 + x)) ^ 5) atTop atTop := by
    refine h2.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with x hx
    simp only [Pi.inv_apply]
    rw [inv_div, Real.sqrt_eq_rpow]
  exact (tendsto_nat_floor_atTop).comp (h3.comp tendsto_natCast_atTop_atTop)

private lemma an_floorA :
    Tendsto (fun X : ℕ => Nat.floor ((X:ℝ) ^ (1/3:ℝ))) atTop atTop :=
  (tendsto_nat_floor_atTop).comp
    ((tendsto_rpow_atTop (by norm_num : (0:ℝ) < 1/3)).comp tendsto_natCast_atTop_atTop)

private lemma an_lim1 (C : ℝ) :
    Tendsto (fun X : ℕ => 9 * C / (Real.log (2 + (X:ℝ))) ^ 2) atTop (nhds 0) := by
  have h : Tendsto (fun X : ℕ => Real.log (2 + (X:ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (tendsto_atTop_add_const_left _ _ tendsto_natCast_atTop_atTop)
  have h2 := ((tendsto_pow_atTop (two_ne_zero)).comp h)
  simpa using (h2.inv_tendsto_atTop).const_mul (9 * C) |>.congr (fun X => by simp [div_eq_mul_inv])

private lemma an_lim2 (C : ℝ) :
    Tendsto (fun X : ℕ => 9 * C * (((X:ℝ) ^ (1/3:ℝ)) * (Real.log (2 + (X:ℝ))) ^ 3 / Real.sqrt X))
      atTop (nhds 0) := by
  have h := an_pow 3 (s := 1/6) (by norm_num)
  have h2 : Tendsto (fun X : ℕ => (Real.log (2 + (X:ℝ))) ^ 3 / (X:ℝ) ^ (1/6:ℝ)) atTop (nhds 0) :=
    h.comp tendsto_natCast_atTop_atTop
  have h3 := h2.const_mul (9 * C)
  rw [mul_zero] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with X hX
  have hx : (0:ℝ) < X := by exact_mod_cast hX
  congr 1
  have e : Real.sqrt X = (X:ℝ) ^ (1/3:ℝ) * (X:ℝ) ^ (1/6:ℝ) := by
    rw [← Real.rpow_add hx, Real.sqrt_eq_rpow]; norm_num
  rw [e]
  have : 0 < (X:ℝ) ^ (1/3:ℝ) := Real.rpow_pos_of_pos hx _
  have : 0 < (X:ℝ) ^ (1/6:ℝ) := Real.rpow_pos_of_pos hx _
  field_simp

private lemma co_split (S : Finset ℕ) (c : ℕ → ℝ) (A D : ℕ) (h : A ≤ D) :
    (S.filter (fun d => A < d ∧ d ≤ D)).sum c =
      (S.filter (fun d => d ≤ D)).sum c - (S.filter (fun d => d ≤ A)).sum c := by
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun d _ => ?_
  by_cases h1 : d ≤ A
  · have : d ≤ D := le_trans h1 h
    simp [h1, this]
  · by_cases h2 : d ≤ D
    · simp [h1, h2]
    · simp [h1, h2]

private lemma co_swap (P : Finset ℕ) (c : ℕ → ℝ) (B : ℕ) (hP : ∀ p ∈ P, Odd (p + 2)) :
    ∑ p ∈ P, Real.log p * ∑ d ∈ (p + 2).divisors.filter (fun d => d ≤ B), c d =
      ∑ d ∈ (Finset.Icc 1 B).filter Odd,
        c d * ∑ p ∈ P.filter (fun p => d ∣ p + 2), Real.log p := by
  have h1 : ∀ p ∈ P, ∑ d ∈ (p + 2).divisors.filter (fun d => d ≤ B), c d =
      ∑ d ∈ (Finset.Icc 1 B).filter Odd, if d ∣ p + 2 then c d else 0 := by
    intro p hp
    rw [← Finset.sum_filter]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hd, hne⟩, hB⟩
      exact ⟨⟨⟨Nat.pos_of_dvd_of_pos hd (by omega), hB⟩, Odd.of_dvd_nat (hP p hp) hd⟩, hd⟩
    · rintro ⟨⟨⟨h1, hB⟩, _⟩, hd⟩
      exact ⟨⟨hd, by omega⟩, hB⟩
  rw [Finset.sum_congr rfl (fun (p : ℕ) hp => congrArg (fun t => Real.log (p:ℝ) * t) (h1 p hp))]
  simp only [Finset.mul_sum, Finset.sum_filter]
  refine Finset.sum_comm.trans ?_
  refine Finset.sum_congr rfl fun d _ => ?_
  by_cases ho : Odd d
  · simp only [ho, ite_true]
    refine Finset.sum_congr rfl fun p _ => ?_
    split_ifs <;> simp [mul_comm]
  · simp [ho]

private lemma co_err (O : Finset ℕ) (c a : ℕ → ℝ) (phi : ℕ → ℝ) (X L E : ℝ) (B : ℕ)
    (hX : 0 < X) (hL : 0 ≤ L) (hE : 0 ≤ E) (hcard : O.card ≤ B)
    (hc : ∀ d ∈ O, |c d| ≤ L)
    (ha : ∀ d ∈ O, |a d - X / (50 * phi d)| ≤ E) (hphi : ∀ d ∈ O, 0 < phi d) :
    |(∑ d ∈ O, c d * a d) / X - (1 / 50) * ∑ d ∈ O, c d / phi d| ≤ B * (L * E) / X := by
  have h1 : ∑ d ∈ O, c d * (a d - X / (50 * phi d)) =
      (∑ d ∈ O, c d * a d) - X * ((1 / 50) * ∑ d ∈ O, c d / phi d) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun d hd => ?_
    have := hphi d hd
    field_simp
  have h2 : (∑ d ∈ O, c d * a d) / X - (1 / 50) * ∑ d ∈ O, c d / phi d =
      (∑ d ∈ O, c d * (a d - X / (50 * phi d))) / X := by
    rw [h1]; field_simp
  rw [h2, abs_div, abs_of_pos hX]
  gcongr
  calc |∑ d ∈ O, c d * (a d - X / (50 * phi d))|
      ≤ ∑ d ∈ O, |c d * (a d - X / (50 * phi d))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ O, L * E := by
        refine Finset.sum_le_sum fun d hd => ?_
        rw [abs_mul]
        exact mul_le_mul (hc d hd) (ha d hd) (abs_nonneg _) hL
    _ = O.card * (L * E) := by simp
    _ ≤ B * (L * E) := by
        have : (O.card : ℝ) ≤ B := by exact_mod_cast hcard
        have : 0 ≤ L * E := by positivity
        nlinarith

private lemma an_AleD :
    ∀ᶠ X : ℕ in atTop, Nat.floor ((X:ℝ) ^ (1/3:ℝ)) ≤
      Nat.floor (Real.sqrt X / (Real.log (2 + (X:ℝ))) ^ 5) := by
  have h := (an_pow 5 (s := 1/6) (by norm_num)).comp tendsto_natCast_atTop_atTop
  have h1 := h.eventually (Iio_mem_nhds (by norm_num : (0:ℝ) < 1))
  filter_upwards [h1, eventually_gt_atTop 0] with X hX hX0
  apply Nat.floor_le_floor
  have hx : (0:ℝ) < X := by exact_mod_cast hX0
  have hL : 0 < Real.log (2 + (X:ℝ)) := Real.log_pos (by linarith)
  have hs : 0 < (X:ℝ) ^ (1/6:ℝ) := Real.rpow_pos_of_pos hx _
  have hX' : (Real.log (2 + (X:ℝ))) ^ 5 ≤ (X:ℝ) ^ (1/6:ℝ) := by
    have : (Real.log (2 + (X:ℝ))) ^ 5 / (X:ℝ) ^ (1/6:ℝ) < 1 := hX
    rw [div_lt_one hs] at this
    exact this.le
  have e : Real.sqrt X = (X:ℝ) ^ (1/3:ℝ) * (X:ℝ) ^ (1/6:ℝ) := by
    rw [← Real.rpow_add hx, Real.sqrt_eq_rpow]; norm_num
  have hL5 : 0 < (Real.log (2 + (X:ℝ))) ^ 5 := by positivity
  rw [le_div_iff₀ hL5, e]
  have : 0 ≤ (X:ℝ) ^ (1/3:ℝ) := by positivity
  exact mul_le_mul_of_nonneg_left hX' this

theorem Conjectures.TwinPrimes.DivisorNearSquareRootStrip :
    RiemannHypothesis → (∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ), 0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1/2) → (let w := fun (X : ℕ) => (Finset.range (2*X+1)).filter (fun n => X < n ∧ 50*n < 51*X); let D := fun (X : ℕ) => Nat.floor (Real.sqrt X/(Real.log (2+(X:ℝ)))^5); let A := fun (X : ℕ) => Nat.floor ((X:ℝ)^(1/3:ℝ)); let c := fun (d : ℕ) => -(ArithmeticFunction.moebius d : ℝ)*Real.log d; let strip := fun (X : ℕ) => (((w X).filter Nat.Prime).sum (fun p => Real.log p * (((p+2).divisors.filter (fun d => A X < d ∧ d ≤ D X)).sum c)))/(X:ℝ); Filter.Tendsto strip Filter.atTop (nhds 0)) := by
  intro hRH hGRH w D A c strip
  have hAP := PEqualNP.Outside.L_twin_primes_ap_short_error hGRH
  dsimp only at hAP
  obtain ⟨C, hC, hAP⟩ := hAP
  have hHC := PEqualNP.Outside.L_twin_primes_hard_cutoff
  dsimp only at hHC
  have hlim := hHC hRH
  obtain ⟨T, hT⟩ : ∃ T : ℝ, Tendsto (fun D : ℕ =>
      ((Finset.Icc 1 D).filter (fun n => n % 2 = 1)).sum
        (fun n => -(ArithmeticFunction.moebius n : ℝ) * Real.log n / Nat.totient n))
      atTop (nhds T) := ⟨_, hlim⟩
  obtain ⟨sh, hsh⟩ : ∃ sh : ℕ → ℕ → ℝ, ∀ X B, sh X B =
      (((w X).filter Nat.Prime).sum (fun p => Real.log p *
        (((p + 2).divisors.filter (fun d => d ≤ B)).sum c))) / (X : ℝ) := ⟨_, fun _ _ => rfl⟩
  obtain ⟨mn, hmn⟩ : ∃ mn : ℕ → ℝ, ∀ B, mn B =
      (1 / 50) * ∑ d ∈ (Finset.Icc 1 B).filter Odd, c d / (Nat.totient d : ℝ) :=
    ⟨_, fun _ => rfl⟩
  have hmnT : Tendsto mn atTop (nhds (1 / 50 * T)) := by
    have := hT.const_mul (1 / 50 : ℝ)
    refine this.congr fun B => ?_
    rw [hmn]
    congr 1
  have hstrip : ∀ X, A X ≤ D X → strip X = sh X (D X) - sh X (A X) := by
    intro X hAD
    simp only [strip, hsh]
    rw [← sub_div]
    congr 1
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [co_split _ c (A X) (D X) hAD, mul_sub]
  have key : ∀ X : ℕ, 2 ≤ X → ∀ B : ℕ, B ≤ X →
      |sh X B - mn B| ≤ 9 * C * (B * (Real.log (2 + (X:ℝ))) ^ 3 / Real.sqrt X) := by
    intro X hX B hB
    have hX0 : (0:ℝ) < X := by exact_mod_cast (by omega : 0 < X)
    have hX2 : (2:ℝ) ≤ X := by exact_mod_cast hX
    have hXB : (B:ℝ) ≤ X := by exact_mod_cast hB
    set L := Real.log (2 + (X:ℝ)) with hLdef
    have hL0 : 0 ≤ L := Real.log_nonneg (by linarith)
    have hsq : 0 < Real.sqrt X := Real.sqrt_pos.2 hX0
    have hodd : ∀ p ∈ (w X).filter Nat.Prime, Odd (p + 2) := by
      intro p hp
      simp only [w, Finset.mem_filter, Finset.mem_range] at hp
      obtain ⟨⟨_, hXp, _⟩, hpr⟩ := hp
      have := hpr.eq_one_or_self_of_dvd 2
      rcases hpr.eq_two_or_odd' with h2 | h2
      · omega
      · exact h2.add_even even_two
    have hsw := co_swap ((w X).filter Nat.Prime) c B hodd
    have hshX : sh X B = (∑ d ∈ (Finset.Icc 1 B).filter Odd, c d *
        ∑ p ∈ (w X).filter (fun p => p.Prime ∧ d ∣ p + 2), Real.log p) / X := by
      rw [hsh, hsw]
      congr 1
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [Finset.filter_filter]
    rw [hshX, hmn]
    have hE : 0 ≤ C * Real.sqrt X * (3 * L) ^ 2 := by positivity
    have h := co_err ((Finset.Icc 1 B).filter Odd) c
      (fun d => ∑ p ∈ (w X).filter (fun p => p.Prime ∧ d ∣ p + 2), Real.log p)
      (fun d => (Nat.totient d : ℝ)) X L (C * Real.sqrt X * (3 * L) ^ 2) B hX0 hL0 hE
      (by
        refine le_trans (Finset.card_filter_le _ _) ?_
        simp)
      (by
        intro d hd
        simp only [Finset.mem_filter, Finset.mem_Icc] at hd
        have hd1 : (1:ℝ) ≤ d := by exact_mod_cast hd.1.1
        have hdX : (d:ℝ) ≤ X := le_trans (by exact_mod_cast hd.1.2) hXB
        have hμ : |(ArithmeticFunction.moebius d : ℝ)| ≤ 1 := by
          exact_mod_cast ArithmeticFunction.abs_moebius_le_one
        have hlog : Real.log d ≤ L := Real.log_le_log (by linarith) (by linarith)
        have hlog0 : 0 ≤ Real.log d := Real.log_nonneg hd1
        have : c d = -(ArithmeticFunction.moebius d : ℝ) * Real.log d := rfl
        rw [this, abs_mul, abs_neg, abs_of_nonneg hlog0]
        calc |(ArithmeticFunction.moebius d : ℝ)| * Real.log d ≤ 1 * Real.log d :=
              mul_le_mul_of_nonneg_right hμ hlog0
          _ ≤ L := by linarith)
      (by
        intro d hd
        simp only [Finset.mem_filter, Finset.mem_Icc] at hd
        have hd1 : (1:ℝ) ≤ d := by exact_mod_cast hd.1.1
        have hdX : (d:ℝ) ≤ X := le_trans (by exact_mod_cast hd.1.2) hXB
        have h1 := hAP X d hX (le_trans hd.1.2 hB) hd.2
        refine le_trans h1 ?_
        have hl0 : 0 ≤ Real.log (2 * (d:ℝ) * X) := Real.log_nonneg (by nlinarith)
        have hl3 : Real.log (2 * (d:ℝ) * X) ≤ 3 * L := by
          have : Real.log (2 * (d:ℝ) * X) ≤ Real.log ((2 + (X:ℝ)) ^ 3) :=
            Real.log_le_log (by nlinarith) (by nlinarith [sq_nonneg (X:ℝ)])
          rw [Real.log_pow] at this
          simpa using this
        have : (Real.log (2 * (d:ℝ) * X)) ^ 2 ≤ (3 * L) ^ 2 := by gcongr
        exact mul_le_mul_of_nonneg_left this (by positivity))
      (by
        intro d hd
        simp only [Finset.mem_filter, Finset.mem_Icc] at hd
        exact_mod_cast Nat.totient_pos.2 hd.1.1)
    have e1 : (∑ d ∈ (Finset.Icc 1 B).filter Odd, c d *
        ∑ p ∈ (w X).filter (fun p => p.Prime ∧ d ∣ p + 2), Real.log p) / X -
        1 / 50 * ∑ d ∈ (Finset.Icc 1 B).filter Odd, c d / (Nat.totient d : ℝ) =
        (∑ d ∈ (Finset.Icc 1 B).filter Odd, c d *
        ∑ p ∈ (w X).filter (fun p => p.Prime ∧ d ∣ p + 2), Real.log p) / X -
        1 / 50 * ∑ d ∈ (Finset.Icc 1 B).filter Odd, c d / (Nat.totient d : ℝ) := rfl
    refine le_trans h ?_
    have e2 : (B:ℝ) * (L * (C * Real.sqrt X * (3 * L) ^ 2)) / X =
        9 * C * (B * L ^ 3 / Real.sqrt X) := by
      have hs2 : Real.sqrt X * Real.sqrt X = X := Real.mul_self_sqrt hX0.le
      generalize Real.sqrt X = s at hsq hs2 ⊢
      rw [← hs2]
      field_simp
      norm_num
    rw [e2]

  have hL1 : Tendsto (fun X : ℕ => Real.log (2 + (X:ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (tendsto_atTop_add_const_left _ _ tendsto_natCast_atTop_atTop)
  have T1 : Tendsto (fun X : ℕ => sh X (D X) - mn (D X)) atTop (nhds 0) := by
    refine squeeze_zero_norm' ?_ (an_lim1 C)
    filter_upwards [hL1.eventually_ge_atTop 1, eventually_ge_atTop 2] with X hL hX
    have hX0 : (0:ℝ) < X := by exact_mod_cast (by omega : 0 < X)
    have hX1 : (1:ℝ) ≤ X := by exact_mod_cast (by omega : 1 ≤ X)
    set L := Real.log (2 + (X:ℝ)) with hLdef
    have hsq : 0 < Real.sqrt X := Real.sqrt_pos.2 hX0
    have hL5 : 1 ≤ L ^ 5 := one_le_pow₀ hL
    have hLp : 0 < L := by linarith
    have hDle : (D X : ℝ) ≤ Real.sqrt X / L ^ 5 := Nat.floor_le (by positivity)
    have hsX : Real.sqrt X ≤ X := Real.sqrt_le_iff.2 ⟨hX0.le, by nlinarith⟩
    have hDX : D X ≤ X := by
      have : (D X : ℝ) ≤ X := by
        refine le_trans hDle (le_trans ?_ hsX)
        exact div_le_self hsq.le hL5
      exact_mod_cast this
    have hk := key X hX (D X) hDX
    rw [Real.norm_eq_abs]
    refine le_trans hk ?_
    have e : Real.sqrt X / L ^ 5 * L ^ 3 / Real.sqrt X = 1 / L ^ 2 := by
      field_simp
    have : (D X : ℝ) * L ^ 3 / Real.sqrt X ≤ 1 / L ^ 2 := by
      rw [← e]
      gcongr
    calc 9 * C * ((D X : ℝ) * L ^ 3 / Real.sqrt X) ≤ 9 * C * (1 / L ^ 2) := by gcongr
      _ = 9 * C / L ^ 2 := by ring
  have T2 : Tendsto (fun X : ℕ => sh X (A X) - mn (A X)) atTop (nhds 0) := by
    refine squeeze_zero_norm' ?_ (an_lim2 C)
    filter_upwards [hL1.eventually_ge_atTop 1, eventually_ge_atTop 2] with X hL hX
    have hX0 : (0:ℝ) < X := by exact_mod_cast (by omega : 0 < X)
    have hX1 : (1:ℝ) ≤ X := by exact_mod_cast (by omega : 1 ≤ X)
    have hsq : 0 < Real.sqrt X := Real.sqrt_pos.2 hX0
    have hAle : (A X : ℝ) ≤ (X:ℝ) ^ (1/3:ℝ) := Nat.floor_le (by positivity)
    have hAX : A X ≤ X := by
      have h3 : (X:ℝ) ^ (1/3:ℝ) ≤ (X:ℝ) ^ (1:ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hX1 (by norm_num)
      rw [Real.rpow_one] at h3
      exact_mod_cast le_trans hAle h3
    have hk := key X hX (A X) hAX
    rw [Real.norm_eq_abs]
    refine le_trans hk ?_
    have hL3 : 0 ≤ Real.log (2 + (X:ℝ)) ^ 3 := by positivity
    have hC9 : 0 ≤ 9 * C := by positivity
    have : (A X : ℝ) * Real.log (2 + (X:ℝ)) ^ 3 / Real.sqrt X ≤
        (X:ℝ) ^ (1/3:ℝ) * Real.log (2 + (X:ℝ)) ^ 3 / Real.sqrt X := by
      gcongr
    exact mul_le_mul_of_nonneg_left this hC9
  have T3 : Tendsto (fun X : ℕ => mn (D X)) atTop (nhds (1 / 50 * T)) := hmnT.comp an_floorD
  have T4 : Tendsto (fun X : ℕ => mn (A X)) atTop (nhds (1 / 50 * T)) := hmnT.comp an_floorA
  have tot : Tendsto (fun X : ℕ => (sh X (D X) - mn (D X)) - (sh X (A X) - mn (A X)) +
      (mn (D X) - mn (A X))) atTop (nhds 0) := by
    have := (T1.sub T2).add (T3.sub T4)
    simpa using this
  refine tot.congr' ?_
  filter_upwards [an_AleD] with X hAD
  rw [hstrip X hAD]
  ring
