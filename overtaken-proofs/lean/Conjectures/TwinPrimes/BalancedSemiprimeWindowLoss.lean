import Mathlib

private lemma tp_minFac (r s : ℕ) (hr : r.Prime) (hs : s.Prime) (h : r < s) :
    (r*s).minFac = r := by
  have hne : r * s ≠ 1 := by
    have := hr.two_le
    have := hs.two_le
    nlinarith
  have hp : (r*s).minFac.Prime := Nat.minFac_prime hne
  have hd : (r*s).minFac ∣ r * s := Nat.minFac_dvd _
  have hle : (r*s).minFac ≤ r := Nat.minFac_le_of_dvd hr.two_le (Dvd.intro _ rfl)
  rcases (Nat.Prime.dvd_mul hp).1 hd with h1 | h1
  · exact (Nat.prime_dvd_prime_iff_eq hp hr).1 h1
  · have := (Nat.prime_dvd_prime_iff_eq hp hs).1 h1
    omega

private lemma tp_z (X : ℕ) (hX : 100 ≤ X) :
    5 ≤ Nat.sqrt X / 2 ∧ X < 6 * (Nat.sqrt X / 2)^2 ∧ X ≤ (Nat.sqrt X / 2)^8 := by
  have h10 : 10 ≤ Nat.sqrt X := by
    rw [Nat.le_sqrt]; omega
  have hlt := Nat.lt_succ_sqrt X
  have hz1 : 5 ≤ Nat.sqrt X / 2 := by omega
  have hz2 : Nat.sqrt X ≤ 2 * (Nat.sqrt X / 2) + 1 := by omega
  generalize Nat.sqrt X / 2 = z at hz1 hz2 ⊢
  have h3 : X < (2*z+2)*(2*z+2) := by
    calc X < (Nat.sqrt X).succ * (Nat.sqrt X).succ := hlt
     _ ≤ (2*z+2)*(2*z+2) := Nat.mul_le_mul (by omega) (by omega)
  have h4 : X < 6 * z^2 := by nlinarith
  refine ⟨hz1, h4, ?_⟩
  have h5 : X^4 < (6*z^2)^4 := Nat.pow_lt_pow_left h4 (by norm_num)
  have h3' : 1000000 ≤ X^3 := by
    calc 1000000 = 100^3 := by norm_num
      _ ≤ X^3 := Nat.pow_le_pow_left hX 3
  have h6 : 1296 * X ≤ X^4 := by
    have : X^4 = X * X^3 := by ring
    rw [this]; nlinarith
  have h7 : (6*z^2)^4 = 1296 * z^8 := by ring
  rw [h7] at h5
  omega

private lemma tp_R (X : ℕ) (hX : 100 ≤ X) : Nat.sqrt (2*X+2) ≤ 5 * (Nat.sqrt X / 2) := by
  obtain ⟨h1, h2, -⟩ := tp_z X hX
  have hR : Nat.sqrt (2*X+2) * Nat.sqrt (2*X+2) ≤ 2*X+2 := Nat.sqrt_le _
  generalize Nat.sqrt X / 2 = z at h1 h2 ⊢
  generalize Nat.sqrt (2*X+2) = R at hR ⊢
  by_contra hc
  push_neg at hc
  nlinarith

private lemma tp_Y (X r : ℕ) (hX : 100 ≤ X) (hr : 0 < r) (hrR : r ≤ Nat.sqrt (2*X+2)) :
    3 ≤ X / r ∧ X ≤ (X / r)^8 ∧ 3 * r ≤ X ∧ r * (X / r) ≤ X ∧ X < r * (X / r + 1) := by
  have hR : Nat.sqrt (2*X+2) * Nat.sqrt (2*X+2) ≤ 2*X+2 := Nat.sqrt_le _
  have hrr : r * r ≤ 2*X+2 := le_trans (Nat.mul_le_mul hrR hrR) hR
  have h3r : 3 * r ≤ X := by
    by_contra hc
    push_neg at hc
    nlinarith
  have hY1 : r * (X / r) ≤ X := Nat.mul_div_le X r
  have hY2 : X < r * (X / r + 1) := by
    have h1 := Nat.div_add_mod X r
    have h2 := Nat.mod_lt X hr
    nlinarith
  generalize X / r = Y at hY1 hY2 ⊢
  have a : X^2 < (r*(Y+1))^2 := Nat.pow_lt_pow_left hY2 (by norm_num)
  have b : (r*(Y+1))^2 = r^2*(Y+1)^2 := by ring
  have c : r^2*(Y+1)^2 ≤ (4*X)*(Y+1)^2 :=
    Nat.mul_le_mul_right _ (by nlinarith)
  have d : X < 4*(Y+1)^2 := by
    have : X * X < X * (4*(Y+1)^2) := by nlinarith
    exact Nat.lt_of_mul_lt_mul_left this
  have hY3 : 3 ≤ Y := by
    by_contra hc
    push_neg at hc
    have : (Y+1)^2 ≤ 3^2 := Nat.pow_le_pow_left (by omega) 2
    omega
  refine ⟨hY3, ?_, h3r, hY1, hY2⟩
  have e : X < 16 * Y^2 := by nlinarith
  have f : X^4 < (16*Y^2)^4 := Nat.pow_lt_pow_left e (by norm_num)
  have h3' : 1000000 ≤ X^3 := by
    calc 1000000 = 100^3 := by norm_num
      _ ≤ X^3 := Nat.pow_le_pow_left hX 3
  have h6 : 65536 * X ≤ X^4 := by
    have : X^4 = X * X^3 := by ring
    rw [this]; nlinarith
  have h7 : (16*Y^2)^4 = 65536 * Y^8 := by ring
  rw [h7] at f
  omega

private lemma tp_window (X r s p : ℕ) (hr3 : 3 * r ≤ X)
    (hY1 : r * (X / r) ≤ X) (hY2 : X < r * (X / r + 1)) (hp : X < p) (hp2 : 50 * p < 51 * X)
    (h : p + 2 = r * s) : X / r < s ∧ s ≤ 2 * (X / r) := by
  generalize X / r = Y at hY1 hY2 ⊢
  constructor
  · by_contra hc
    push_neg at hc
    have := Nat.mul_le_mul_left r hc
    omega
  · by_contra hc
    push_neg at hc
    have hc' : 2*Y+1 ≤ s := hc
    have h1 := Nat.mul_le_mul_left r hc'
    have h2 : r * (2*Y+1) = 2*(r*Y) + r := by ring
    have h3 : r * (Y+1) = r*Y + r := by ring
    omega

private lemma tp_fiber (C : ℝ) (hC : 0 < C)
    (hS : ∀ (Y r : ℕ), 3 ≤ Y → r.Prime → 2 < r → ((((Finset.Ioc Y (2*Y)).filter (fun s => s.Prime ∧ (r*s-2).Prime)).card:ℕ):ℝ) ≤ C*(Y:ℝ)/(Real.log Y)^2)
    (X r : ℕ) (hX : 100 ≤ X) (hr : r.Prime) (hr3 : 2 < r) (hrR : r ≤ Nat.sqrt (2*X+2))
    (F : Finset ℕ)
    (hF : ∀ p ∈ F, X < p ∧ 50*p < 51*X ∧ p.Prime ∧ ∃ s, s.Prime ∧ p+2 = r*s) :
    (F.card : ℝ) ≤ 64 * C * X / (r * (Real.log X)^2) := by
  obtain ⟨hY3, hY8, h3r, hY1, hY2⟩ := tp_Y X r hX (by omega) hrR
  have hcard : F.card ≤ ((Finset.Ioc (X / r) (2*(X / r))).filter
      (fun s => s.Prime ∧ (r*s-2).Prime)).card := by
    apply Finset.card_le_card_of_injOn (fun p => (p+2)/r)
    · intro p hp
      rw [Finset.mem_coe] at hp
      obtain ⟨hpX, hp50, hpp, s, hs, hps⟩ := hF p hp
      have hdiv : (p+2)/r = s := by
        rw [hps]; exact Nat.mul_div_cancel_left s (by omega)
      have hw := tp_window X r s p h3r hY1 hY2 hpX hp50 hps
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_Ioc]
      beta_reduce
      rw [hdiv]
      refine ⟨⟨hw.1, hw.2⟩, hs, ?_⟩
      have : r * s - 2 = p := by omega
      rw [this]; exact hpp
    · intro a ha b hb hab
      rw [Finset.mem_coe] at ha hb
      obtain ⟨-, -, -, sa, -, hsa⟩ := hF a ha
      obtain ⟨-, -, -, sb, -, hsb⟩ := hF b hb
      have h1 : (a+2)/r = sa := by
        rw [hsa]; exact Nat.mul_div_cancel_left sa (by omega)
      have h2 : (b+2)/r = sb := by
        rw [hsb]; exact Nat.mul_div_cancel_left sb (by omega)
      have : sa = sb := by
        have hab' : (a+2)/r = (b+2)/r := hab
        rw [h1, h2] at hab'; exact hab'
      subst this
      omega
  have h1 := hS (X / r) r hY3 hr hr3
  have hXpos : (0:ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have hL : 0 < Real.log X := Real.log_pos (by exact_mod_cast (by omega : 1 < X))
  have hrpos : (0:ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hYr : ((X / r : ℕ) : ℝ) * r ≤ X := by
    have : (X / r) * r ≤ X := by rw [mul_comm]; exact hY1
    exact_mod_cast this
  have hlogY : Real.log X / 8 ≤ Real.log ((X / r : ℕ) : ℝ) := by
    have h := Real.log_le_log hXpos (by exact_mod_cast hY8 : (X:ℝ) ≤ ((X / r : ℕ) : ℝ)^8)
    rw [Real.log_pow] at h
    push_cast at h
    linarith
  have hlogYpos : 0 < Real.log X / 8 := by positivity
  have hsq : (Real.log X / 8)^2 ≤ (Real.log ((X / r : ℕ) : ℝ))^2 :=
    pow_le_pow_left₀ hlogYpos.le hlogY 2
  have hYle : ((X / r : ℕ) : ℝ) ≤ X / r := by
    rw [le_div_iff₀ hrpos]; exact hYr
  have h2 : C * ((X / r : ℕ) : ℝ) / (Real.log ((X / r : ℕ) : ℝ))^2 ≤ C * (X / r) / ((Real.log X / 8)^2) := by
    apply div_le_div₀ (by positivity) _ (by positivity) hsq
    exact mul_le_mul_of_nonneg_left hYle hC.le
  have h3 : C * ((X:ℝ) / r) / ((Real.log X / 8)^2) = 64 * C * X / (r * (Real.log X)^2) := by
    field_simp
    ring
  calc (F.card : ℝ) ≤ ((((Finset.Ioc (X / r) (2*(X / r))).filter
      (fun s => s.Prime ∧ (r*s-2).Prime)).card : ℕ) : ℝ) := by exact_mod_cast hcard
    _ ≤ _ := h1
    _ ≤ _ := h2
    _ = _ := h3

private lemma tp_recip (z R : ℕ) (hz : 2 ≤ z) (hRz : R ≤ 5 * z) :
    ∑ r ∈ (Finset.Icc z R).filter Nat.Prime, (1 / (r:ℝ)) ≤ 5 * Real.log 4 / Real.log z := by
  have hzR : (0:ℝ) < z := by exact_mod_cast (by omega : 0 < z)
  have hlz : 0 < Real.log z := Real.log_pos (by exact_mod_cast (by omega : 1 < z))
  have hterm : ∀ r ∈ (Finset.Icc z R).filter Nat.Prime,
      1 / (r:ℝ) ≤ Real.log r / (z * Real.log z) := by
    intro r hr
    rw [Finset.mem_filter, Finset.mem_Icc] at hr
    have hzr : (z:ℝ) ≤ r := by exact_mod_cast hr.1.1
    have hrpos : (0:ℝ) < r := lt_of_lt_of_le hzR hzr
    have hlr : Real.log z ≤ Real.log r := Real.log_le_log hzR hzr
    rw [div_le_div_iff₀ hrpos (by positivity)]
    nlinarith
  have hsub : (Finset.Icc z R).filter Nat.Prime ⊆ R.primesLE := by
    intro q hq
    rw [Finset.mem_filter, Finset.mem_Icc] at hq
    rw [Nat.primesLE_eq_filter_range, Finset.mem_filter]
    exact ⟨Finset.mem_range.mpr (by omega), hq.2⟩
  have hnonneg : ∀ q ∈ R.primesLE, q ∉ (Finset.Icc z R).filter Nat.Prime → 0 ≤ Real.log (q:ℝ) := by
    intro q hq _
    rw [Nat.primesLE_eq_filter_range, Finset.mem_filter] at hq
    apply Real.log_nonneg
    exact_mod_cast (by have := hq.2.two_le; omega : 1 ≤ q)
  have hth : ∑ r ∈ (Finset.Icc z R).filter Nat.Prime, Real.log (r:ℝ) ≤ Real.log 4 * R := by
    calc ∑ r ∈ (Finset.Icc z R).filter Nat.Prime, Real.log (r:ℝ)
        ≤ ∑ q ∈ R.primesLE, Real.log (q:ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub hnonneg
      _ = Chebyshev.theta (R : ℝ) := (Chebyshev.theta_eq_sum_primesLE_log R).symm
      _ ≤ Real.log 4 * (R : ℝ) := Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg _)
  have hR5 : (R:ℝ) ≤ 5 * z := by exact_mod_cast hRz
  have hl4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  calc ∑ r ∈ (Finset.Icc z R).filter Nat.Prime, (1 / (r:ℝ))
      ≤ ∑ r ∈ (Finset.Icc z R).filter Nat.Prime, Real.log r / (z * Real.log z) :=
        Finset.sum_le_sum hterm
    _ = (∑ r ∈ (Finset.Icc z R).filter Nat.Prime, Real.log r) / (z * Real.log z) := by
        rw [Finset.sum_div]
    _ ≤ (Real.log 4 * R) / (z * Real.log z) :=
        div_le_div_of_nonneg_right hth (by positivity)
    _ ≤ (Real.log 4 * (5 * z)) / (z * Real.log z) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hR5 hl4.le) (by positivity)
    _ = 5 * Real.log 4 / Real.log z := by
        field_simp

theorem Conjectures.TwinPrimes.BalancedSemiprimeWindowLoss :
    let w := fun (X : ℕ) => (Finset.range (2*X+1)).filter (fun n => X < n ∧ 50*n < 51*X); let S := fun (X : ℕ) => @Finset.filter ℕ (fun p => p.Prime ∧ ∃ r s : ℕ, r.Prime ∧ s.Prime ∧ r < s ∧ Nat.sqrt X/2 ≤ r ∧ r ≤ Nat.sqrt (2*X+2) ∧ p+2=r*s) (fun _ => Classical.propDecidable _) (w X); (∃ C : ℝ, 0 < C ∧ ∀ (Y r : ℕ), 3 ≤ Y → r.Prime → 2 < r → ((((Finset.Ioc Y (2*Y)).filter (fun s => s.Prime ∧ (r*s-2).Prime)).card:ℕ):ℝ) ≤ C*(Y:ℝ)/(Real.log Y)^2) → (∃ K : ℝ, 0 < K ∧ ∀ X : ℕ, 100 ≤ X → (S X).sum (fun p => Real.log p * Real.log (p+2)) ≤ K*(X:ℝ)/Real.log X) := by
  intro w S hyp
  obtain ⟨C, hC, hS⟩ := hyp
  have hl4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  refine ⟨10240 * Real.log 4 * C, by positivity, ?_⟩
  intro X hX
  have hwmem : ∀ p, p ∈ w X ↔ p ∈ Finset.range (2*X+1) ∧ (X < p ∧ 50*p < 51*X) := by
    intro p; exact Finset.mem_filter
  have hSmem : ∀ p, p ∈ S X ↔ p ∈ w X ∧ (p.Prime ∧ ∃ r s : ℕ, r.Prime ∧ s.Prime ∧ r < s ∧
      Nat.sqrt X/2 ≤ r ∧ r ≤ Nat.sqrt (2*X+2) ∧ p+2=r*s) := by
    intro p; exact @Finset.mem_filter ℕ _ (fun _ => Classical.propDecidable _) (w X) p
  obtain ⟨hz5, hz6, hz8⟩ := tp_z X hX
  have hR5 := tp_R X hX
  have hXpos : (0:ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have hL : 0 < Real.log X := Real.log_pos (by exact_mod_cast (by omega : 1 < X))
  set z := Nat.sqrt X / 2 with hzdef
  set R := Nat.sqrt (2*X+2) with hRdef
  set P := (Finset.Icc z R).filter Nat.Prime with hP
  have hmaps : ∀ p ∈ S X, (p+2).minFac ∈ P := by
    intro p hp
    rw [hSmem] at hp
    obtain ⟨-, -, r, s, hr, hs, hrs, hzr, hrR, hps⟩ := hp
    rw [hps, tp_minFac r s hr hs hrs, hP, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨hzr, hrR⟩, hr⟩
  have hterm : ∀ p ∈ S X, Real.log p * Real.log (p+2) ≤ 4 * (Real.log X)^2 := by
    intro p hp
    rw [hSmem, hwmem, Finset.mem_range] at hp
    obtain ⟨⟨hp1, hp2, -⟩, hpp, -⟩ := hp
    have hp2' : (p:ℝ) + 2 ≤ (X:ℝ)^2 := by
      have : p + 2 ≤ X^2 := by nlinarith
      exact_mod_cast this
    have hp1' : (1:ℝ) ≤ p := by exact_mod_cast hpp.one_lt.le
    have ha : Real.log (p+2) ≤ 2 * Real.log X := by
      have := Real.log_le_log (by linarith : (0:ℝ) < p + 2) hp2'
      rw [Real.log_pow] at this
      push_cast at this
      linarith
    have hb : Real.log p ≤ Real.log (p+2) := Real.log_le_log (by linarith) (by linarith)
    have hc : 0 ≤ Real.log p := Real.log_nonneg hp1'
    nlinarith
  have hfib : ∀ r ∈ P, ∑ p ∈ (S X).filter (fun p => (p+2).minFac = r),
      Real.log p * Real.log (p+2) ≤ 256 * C * X / r := by
    intro r hr
    rw [hP, Finset.mem_filter, Finset.mem_Icc] at hr
    obtain ⟨⟨hzr, hrR⟩, hrp⟩ := hr
    have hr3 : 2 < r := by omega
    have hcard := tp_fiber C hC hS X r hX hrp hr3 hrR ((S X).filter (fun p => (p+2).minFac = r)) (by
      intro p hp
      rw [Finset.mem_filter, hSmem, hwmem, Finset.mem_range] at hp
      obtain ⟨⟨⟨-, hp2, hp3⟩, hpp, r', s', hr', hs', hrs', -, -, hps'⟩, hmin⟩ := hp
      rw [hps', tp_minFac r' s' hr' hs' hrs'] at hmin
      subst hmin
      exact ⟨hp2, hp3, hpp, s', hs', hps'⟩)
    have hrpos : (0:ℝ) < r := by exact_mod_cast (by omega : 0 < r)
    calc ∑ p ∈ (S X).filter (fun p => (p+2).minFac = r), Real.log p * Real.log (p+2)
        ≤ ((S X).filter (fun p => (p+2).minFac = r)).card • (4 * (Real.log X)^2) :=
          Finset.sum_le_card_nsmul _ _ _ (fun p hp => hterm p (Finset.mem_filter.1 hp).1)
      _ = (((S X).filter (fun p => (p+2).minFac = r)).card : ℝ) * (4 * (Real.log X)^2) := by
          rw [nsmul_eq_mul]
      _ ≤ (64 * C * X / (r * (Real.log X)^2)) * (4 * (Real.log X)^2) :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = 256 * C * X / r := by
          field_simp
          ring
  have hrec := tp_recip z R (by omega) hR5
  have hlz : Real.log X ≤ 8 * Real.log z := by
    have h := Real.log_le_log hXpos (by exact_mod_cast hz8 : (X:ℝ) ≤ (z:ℝ)^8)
    rw [Real.log_pow] at h
    push_cast at h
    linarith
  have hlzpos : 0 < Real.log z := by linarith
  calc ∑ p ∈ S X, Real.log p * Real.log (p+2)
      = ∑ r ∈ P, ∑ p ∈ (S X).filter (fun p => (p+2).minFac = r), Real.log p * Real.log (p+2) :=
        (Finset.sum_fiberwise_of_maps_to hmaps _).symm
    _ ≤ ∑ r ∈ P, 256 * C * X / r := Finset.sum_le_sum hfib
    _ = 256 * C * X * ∑ r ∈ P, (1 / (r:ℝ)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun r _ => ?_)
        ring
    _ ≤ 256 * C * X * (5 * Real.log 4 / Real.log z) :=
        mul_le_mul_of_nonneg_left hrec (by positivity)
    _ ≤ 256 * C * X * (5 * Real.log 4 * 8 / Real.log X) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [div_le_div_iff₀ hlzpos hL]
        nlinarith
    _ = 10240 * Real.log 4 * C * X / Real.log X := by
        field_simp
        ring
