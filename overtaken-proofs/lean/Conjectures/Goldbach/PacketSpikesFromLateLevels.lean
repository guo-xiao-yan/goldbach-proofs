import Mathlib

section PEM
open Real

private lemma pem_double (K : ℝ → ℝ) (hc : Continuous K) (hp : ∀ x, K (x + 1) = K x) :
    ∫ x in (0:ℝ)..1, K (2 * x) = ∫ x in (0:ℝ)..1, K x := by
  have h1 := intervalIntegral.integral_comp_mul_left (a := (0:ℝ)) (b := 1) K (c := 2) (by norm_num)
  have h2 : ∫ x in (0:ℝ)..2, K x = (∫ x in (0:ℝ)..1, K x) + ∫ x in (1:ℝ)..2, K x :=
    (intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)).symm
  have hper : Function.Periodic K 1 := hp
  have h3 : ∫ x in (1:ℝ)..(1+1), K x = ∫ x in (0:ℝ)..(0+1), K x := hper.intervalIntegral_add_eq 1 0
  simp only [mul_zero, mul_one, smul_eq_mul] at h1
  rw [h1, h2]
  have : ∫ x in (1:ℝ)..2, K x = ∫ x in (0:ℝ)..1, K x := by
    have e : (1:ℝ) + 1 = 2 := by norm_num
    rw [e, zero_add] at h3; exact h3
  rw [this]; ring

private lemma pem_key (K : ℝ → ℝ) (hc : Continuous K) (hp : ∀ x, K (x + 1) = K x)
    (hn : ∀ x, 0 ≤ K x) (s : ℝ) :
    ∫ x in (0:ℝ)..1, Real.exp (s * Real.cos (2 * π * x)) * K (2 * x)
      ≤ Real.cosh s * ∫ x in (0:ℝ)..1, K x := by
  set f : ℝ → ℝ := fun x => Real.exp (s * Real.cos (2 * π * x)) * K (2 * x) with hf
  have hfc : Continuous f := by
    have := hc
    simp only [hf]; fun_prop
  have hsplit : ∫ x in (0:ℝ)..1, f x = (∫ x in (0:ℝ)..(1/2), f x) + ∫ x in (1/2:ℝ)..1, f x :=
    (intervalIntegral.integral_add_adjacent_intervals (hfc.intervalIntegrable _ _) (hfc.intervalIntegrable _ _)).symm
  have hshift : ∫ x in (1/2:ℝ)..1, f x = ∫ x in (0:ℝ)..(1/2), Real.exp (-(s * Real.cos (2 * π * x))) * K (2 * x) := by
    have := intervalIntegral.integral_comp_add_right (a := (0:ℝ)) (b := 1/2) f (1/2)
    rw [zero_add, add_halves] at this
    rw [← this]
    apply intervalIntegral.integral_congr
    intro x _
    simp only [hf]
    have e1 : 2 * π * (x + 1/2) = 2 * π * x + π := by ring
    have e2 : 2 * (x + 1/2) = 2 * x + 1 := by ring
    rw [e1, e2, Real.cos_add_pi, hp]
    simp
  have hsum : ∫ x in (0:ℝ)..1, f x = ∫ x in (0:ℝ)..(1/2), 2 * Real.cosh (s * Real.cos (2 * π * x)) * K (2 * x) := by
    rw [hsplit, hshift, ← intervalIntegral.integral_add (hfc.intervalIntegrable _ _)
      (by apply Continuous.intervalIntegrable; have := hc; fun_prop)]
    apply intervalIntegral.integral_congr
    intro x _
    simp only [hf, Real.cosh_eq]
    ring
  have hle : ∫ x in (0:ℝ)..(1/2), 2 * Real.cosh (s * Real.cos (2 * π * x)) * K (2 * x)
      ≤ ∫ x in (0:ℝ)..(1/2), 2 * Real.cosh s * K (2 * x) := by
    apply intervalIntegral.integral_mono_on (by norm_num)
    · apply Continuous.intervalIntegrable; have := hc; fun_prop
    · apply Continuous.intervalIntegrable; have := hc; fun_prop
    · intro x _
      apply mul_le_mul_of_nonneg_right _ (hn _)
      have : Real.cosh (s * Real.cos (2 * π * x)) ≤ Real.cosh s := by
        rw [Real.cosh_le_cosh, abs_mul]
        have := Real.abs_cos_le_one (2 * π * x)
        nlinarith [abs_nonneg s, abs_nonneg (Real.cos (2 * π * x))]
      linarith
  have hc2 := intervalIntegral.integral_comp_mul_left (a := (0:ℝ)) (b := 1/2) K (c := 2) (by norm_num)
  have hc3 : ∫ x in (0:ℝ)..(1/2), 2 * Real.cosh s * K (2 * x)
      = Real.cosh s * ∫ x in (0:ℝ)..1, K x := by
    rw [intervalIntegral.integral_const_mul, hc2]
    norm_num
    ring
  show ∫ x in (0:ℝ)..1, f x ≤ _
  rw [hsum]; exact hle.trans hc3.le

private noncomputable def pemG (m : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range m, Real.cos (2 * π * (2:ℝ) ^ j * x)

private lemma pemG_cont (m : ℕ) : Continuous (pemG m) := by
  unfold pemG; fun_prop

private lemma pemG_per (m : ℕ) (x : ℝ) : pemG m (x + 1) = pemG m x := by
  unfold pemG
  apply Finset.sum_congr rfl
  intro j _
  have : 2 * π * (2:ℝ) ^ j * (x + 1) = 2 * π * (2:ℝ) ^ j * x + ((2 ^ j : ℕ) : ℝ) * (2 * π) := by
    push_cast; ring
  rw [this, Real.cos_add_nat_mul_two_pi]

private lemma pemG_succ (m : ℕ) (x : ℝ) :
    pemG (m + 1) x = Real.cos (2 * π * x) + pemG m (2 * x) := by
  unfold pemG
  have h : ∑ j ∈ Finset.range m, Real.cos (2 * π * (2:ℝ) ^ (j + 1) * x)
      = ∑ j ∈ Finset.range m, Real.cos (2 * π * (2:ℝ) ^ j * (2 * x)) :=
    Finset.sum_congr rfl (fun j _ => by congr 1; ring)
  rw [Finset.sum_range_succ', h, pow_zero, mul_one, add_comm]

private lemma pemG_bound (s : ℝ) (m : ℕ) :
    ∫ x in (0:ℝ)..1, Real.exp (s * pemG m x) ≤ Real.cosh s ^ m := by
  induction m with
  | zero => simp [pemG]
  | succ m ih =>
    have hK := pem_key (fun x => Real.exp (s * pemG m x)) (by have := pemG_cont m; fun_prop)
      (by intro x; simp only [pemG_per]) (fun x => (Real.exp_pos _).le) s
    have e : ∀ x, Real.exp (s * pemG (m + 1) x)
        = Real.exp (s * Real.cos (2 * π * x)) * Real.exp (s * pemG m (2 * x)) := by
      intro x; rw [pemG_succ, ← Real.exp_add]; congr 1; ring
    simp only [e]
    calc _ ≤ _ := hK
      _ ≤ Real.cosh s * Real.cosh s ^ m :=
        mul_le_mul_of_nonneg_left ih (Real.cosh_pos s).le
      _ = _ := by ring

private theorem pem_thm :
    let T := fun (m : ℕ) (t : ℝ) => ∑ j ∈ Finset.range m, Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t); ∀ (m : ℕ) (s : ℝ), intervalIntegral (fun t => Real.exp (s*T m t)) (0:ℝ) 1 MeasureTheory.volume ≤ (Real.cosh s)^m := by
  intro T m s
  have e : ∀ t, T m t = pemG m (2 * t) := by
    intro t
    simp only [T, pemG]
    apply Finset.sum_congr rfl
    intro j _
    congr 1; ring
  have h := pem_double (fun x => Real.exp (s * pemG m x)) (by have := pemG_cont m; fun_prop)
    (by intro x; simp only [pemG_per])
  have h2 := pemG_bound s m
  show ∫ t in (0:ℝ)..1, Real.exp (s * T m t) ≤ _
  simp only [e]
  rw [h]; exact h2

end PEM

open MeasureTheory

namespace PSL

private theorem bin_exists (y0 x : ℝ) (k : ℕ) (h0 : y0 < x) (hx : x ≤ y0 * 2 ^ k) :
    ∃ i < k, y0 * 2 ^ i < x ∧ x ≤ y0 * 2 ^ (i + 1) := by
  induction k with
  | zero => simp at hx; linarith
  | succ k ih =>
    by_cases h : x ≤ y0 * 2 ^ k
    · obtain ⟨i, hi, h1, h2⟩ := ih h
      exact ⟨i, by omega, h1, h2⟩
    · exact ⟨k, Nat.lt_succ_self k, not_le.mp h, hx⟩

private theorem meas_and (P : Prop) {X : ℝ → Prop} (hX : MeasurableSet {t : ℝ | X t}) :
    MeasurableSet {t : ℝ | P ∧ X t} := by
  by_cases hP : P
  · simpa [hP] using hX
  · simp [hP]

private theorem iunion2 (R : ℕ → ℕ → ℝ → Prop) (h : ∀ q a, MeasurableSet {t : ℝ | R q a t}) :
    MeasurableSet {t : ℝ | ∃ q a, R q a t} := by
  have : {t : ℝ | ∃ q a, R q a t} = ⋃ q : ℕ, ⋃ a : ℕ, {t : ℝ | R q a t} := by
    ext t; simp
  rw [this]
  exact MeasurableSet.iUnion (fun q => MeasurableSet.iUnion (fun a => h q a))

private theorem arcs_meas (Qn n : ℕ) :
    MeasurableSet {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Qn ∧ a≤q ∧ Nat.Coprime a q ∧
      |t-(a:ℝ)/(q:ℝ)| ≤ (Qn:ℝ)/((q:ℝ)*(n:ℝ))} := by
  refine iunion2 (fun q a t => 1≤q ∧ q≤Qn ∧ a≤q ∧ Nat.Coprime a q ∧
      |t-(a:ℝ)/(q:ℝ)| ≤ (Qn:ℝ)/((q:ℝ)*(n:ℝ))) (fun q a => ?_)
  refine meas_and _ (meas_and _ (meas_and _ (meas_and _ ?_)))
  exact measurableSet_le (by fun_prop) (by fun_prop)

private theorem W_meas (M n : ℕ) (R : ℝ) :
    MeasurableSet {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤M ∧ a≤q ∧ Nat.Coprime a q ∧ True ∧
      |t-(a:ℝ)/(q:ℝ)| ≤ R/((q:ℝ)*(n:ℝ))} := by
  refine iunion2 (fun q a t => 1≤q ∧ q≤M ∧ a≤q ∧ Nat.Coprime a q ∧ True ∧
      |t-(a:ℝ)/(q:ℝ)| ≤ R/((q:ℝ)*(n:ℝ))) (fun q a => ?_)
  refine meas_and _ (meas_and _ (meas_and _ (meas_and _ (meas_and _ ?_))))
  exact measurableSet_le (by fun_prop) (by fun_prop)

private theorem indInt {A : Set ℝ} (hA : MeasurableSet A) {g : ℝ → ℝ} (hg : Continuous g) :
    IntervalIntegrable (A.indicator g) MeasureTheory.volume (0:ℝ) 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)]
  exact (hg.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self).indicator hA

private theorem rho_le : Real.exp (-(1/2:ℝ)) * Real.cosh 1 ≤ 0.941 := by
  have he1 : (2.7182818283:ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have he2 : Real.exp 1 < (2.7182818286:ℝ) := Real.exp_one_lt_d9
  have hu : Real.exp (1/2) ^ 2 = Real.exp 1 := by
    rw [← Real.exp_nat_mul]; norm_num
  have hu0 := Real.exp_pos (1/2:ℝ)
  have hu1 : (1.648:ℝ) < Real.exp (1/2) := by
    by_contra h
    push_neg at h
    nlinarith
  have hn1 : Real.exp (-(1/2:ℝ)) * Real.exp (1/2) = 1 := by
    rw [← Real.exp_add]; simp
  have hn1' : Real.exp (-(1:ℝ)) * Real.exp 1 = 1 := by
    rw [← Real.exp_add]; simp
  have hp1 := Real.exp_pos (-(1/2:ℝ))
  have hp2 := Real.exp_pos (-(1:ℝ))
  have hv : Real.exp (-(1/2:ℝ)) ≤ 0.607 := by
    by_contra h
    push_neg at h
    nlinarith
  have hw : Real.exp (-(1:ℝ)) ≤ 0.3679 := by
    by_contra h
    push_neg at h
    nlinarith
  have hc : Real.cosh 1 ≤ 1.5432 := by
    rw [Real.cosh_eq]
    linarith
  have hc0 : 0 ≤ Real.cosh 1 := (Real.cosh_pos 1).le
  nlinarith

private theorem bmass (Bs : Set ℝ) (hB : MeasurableSet Bs) (L : ℕ) (hL : 1 ≤ L)
    (hsub : ∀ t ∈ Bs, (L:ℝ)/2 < ∑ j ∈ Finset.range L, Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t)) :
    intervalIntegral (Bs.indicator (fun _ => (1:ℝ))) (0:ℝ) 1 MeasureTheory.volume
      ≤ (0.941:ℝ) ^ L := by
  have hm : intervalIntegral (fun t : ℝ => Real.exp (1 * ∑ j ∈ Finset.range L,
      Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))) (0:ℝ) 1 MeasureTheory.volume ≤ (Real.cosh 1) ^ L :=
    pem_thm L 1
  have hcont : Continuous (fun t : ℝ => Real.exp (1 * ∑ j ∈ Finset.range L,
      Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))) := by fun_prop
  calc intervalIntegral (Bs.indicator (fun _ => (1:ℝ))) (0:ℝ) 1 MeasureTheory.volume
      ≤ intervalIntegral (fun t : ℝ => Real.exp (-((L:ℝ)/2)) * Real.exp (1 * ∑ j ∈ Finset.range L,
      Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))) (0:ℝ) 1 MeasureTheory.volume := by
        apply intervalIntegral.integral_mono_on (by norm_num)
        · exact indInt hB continuous_const
        · exact (continuous_const.mul hcont).intervalIntegrable _ _
        · intro t _
          by_cases ht : t ∈ Bs
          · rw [Set.indicator_of_mem ht, ← Real.exp_add]
            apply Real.one_le_exp
            have := hsub t ht
            linarith
          · rw [Set.indicator_of_notMem ht]
            positivity
    _ = Real.exp (-((L:ℝ)/2)) * intervalIntegral (fun t : ℝ => Real.exp (1 * ∑ j ∈ Finset.range L,
      Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))) (0:ℝ) 1 MeasureTheory.volume :=
        intervalIntegral.integral_const_mul _ _
    _ ≤ Real.exp (-((L:ℝ)/2)) * (Real.cosh 1) ^ L :=
        mul_le_mul_of_nonneg_left hm (Real.exp_pos _).le
    _ = (Real.exp (-(1/2:ℝ)) * Real.cosh 1) ^ L := by
        rw [mul_pow, ← Real.exp_nat_mul]
        congr 2
        ring
    _ ≤ (0.941:ℝ) ^ L :=
        pow_le_pow_left₀ (mul_nonneg (Real.exp_pos _).le (Real.cosh_pos 1).le) rho_le L

end PSL

theorem Conjectures.Goldbach.PacketSpikesFromLateLevels :
    (let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let low := fun (n k : ℕ) => if k^3≤n then w k else 0; let high := fun (n k : ℕ) => w k-low n k; let L := fun n : ℕ => max 1 (Nat.log 2 n / 2); let K := fun (n : ℕ) (t : ℝ) => (∑ j ∈ Finset.range (L n), Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L n:ℝ); let B := fun n : ℕ => {t : ℝ | t ∉ arcs n ∧ (1:ℝ)/2 < K n t}; let W := fun (n : ℕ) (p : ℕ → Prop) => {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ (Q n)^2 ∧ a ≤ q ∧ Nat.Coprime a q ∧ p q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ ((Q n:ℝ)^2)/((q:ℝ)*(n:ℝ))}; let F := fun (n : ℕ) (t : ℝ) => ‖S n (high n) t‖^2; let T := fun n : ℕ => (n:ℝ)*(1+Real.log (n:ℝ))^4; let m := fun (s : Set ℝ) (f : ℝ → ℝ) => intervalIntegral (s.indicator f) (0:ℝ) 1 MeasureTheory.volume; ∃ N : ℕ, ∀ n ≥ N, Even n → ∀ j : ℕ, L n / 16 ≤ j → j < Nat.log 2 n + 3 → let y := (2:ℝ)^j*T n; y * m ((B n \ (W n (fun _ => True))) ∩ {t : ℝ | y < F n t ∧ F n t ≤ 2*y}) (fun _ => (1:ℝ)) ≤ (n:ℝ)/(100000*(1+Real.log (n:ℝ))^2)) → (let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let low := fun (n k : ℕ) => if k^3≤n then w k else 0; let high := fun (n k : ℕ) => w k-low n k; let L := fun n : ℕ => max 1 (Nat.log 2 n / 2); let K := fun (n : ℕ) (t : ℝ) => (∑ j ∈ Finset.range (L n), Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L n:ℝ); let B := fun n : ℕ => {t : ℝ | t ∉ arcs n ∧ (1:ℝ)/2 < K n t}; let W := fun (n : ℕ) (p : ℕ → Prop) => {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ (Q n)^2 ∧ a ≤ q ∧ Nat.Coprime a q ∧ p q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ ((Q n:ℝ)^2)/((q:ℝ)*(n:ℝ))}; let F := fun (n : ℕ) (t : ℝ) => ‖S n (high n) t‖^2; let T := fun n : ℕ => (n:ℝ)*(1+Real.log (n:ℝ))^4; let m := fun (s : Set ℝ) (f : ℝ → ℝ) => intervalIntegral (s.indicator f) (0:ℝ) 1 MeasureTheory.volume; ∃ N : ℕ, ∀ n ≥ N, Even n → m ((B n \ (W n (fun _ => True))) ∩ {t : ℝ | T n < F n t}) (F n) ≤ (n:ℝ)/2304) := by
  intro hH
  obtain ⟨N0, hN0⟩ := hH
  intro w E S Q arcs low high L K B W F T m
  obtain ⟨L0, hL0⟩ : ∃ L0 : ℕ, ∀ L : ℕ, L0 ≤ L →
      (1.045:ℝ)^L * (5*(L:ℝ))^4 * (0.941:ℝ)^L ≤ 1/4608 := by
    have h := tendsto_pow_const_mul_const_pow_of_abs_lt_one 4 (r := (0.99:ℝ))
      (by rw [abs_of_pos (by norm_num)]; norm_num)
    have h2 := h.eventually (gt_mem_nhds (show (0:ℝ) < 1/(4608*625) by norm_num))
    obtain ⟨L0, hL0⟩ := Filter.eventually_atTop.mp h2
    refine ⟨L0, fun L hL => ?_⟩
    have hh := hL0 L hL
    have hmp : ((1.045:ℝ)*0.941)^L = (1.045:ℝ)^L * (0.941:ℝ)^L := mul_pow _ _ _
    calc (1.045:ℝ)^L * (5*(L:ℝ))^4 * (0.941:ℝ)^L
        = 625 * ((L:ℝ)^4 * ((1.045:ℝ)*0.941)^L) := by rw [hmp]; ring
      _ ≤ 625 * ((L:ℝ)^4 * (0.99:ℝ)^L) := by
          gcongr
          norm_num
      _ ≤ 1/4608 := by linarith
  refine ⟨max (max N0 (2^(2*L0+2))) 3, fun n hn hev => ?_⟩
  have hnN0 : N0 ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hn2k : 2^(2*L0+2) ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hn3 : 3 ≤ n := le_trans (le_max_right _ _) hn
  obtain ⟨k, hk⟩ : ∃ k, k = Nat.log 2 n := ⟨_, rfl⟩
  have hkL0 : 2*L0+2 ≤ k := by rw [hk]; exact Nat.le_log_of_pow_le (by norm_num) hn2k
  have hLdef : L n = max 1 (k/2) := by rw [hk]
  have hL1 : 1 ≤ L n := by rw [hLdef]; exact le_max_left _ _
  have hLk : k ≤ 2 * L n + 1 := by rw [hLdef]; omega
  have hLk2 : L n ≤ k + 1 := by rw [hLdef]; omega
  have hLL0 : L0 ≤ L n := by rw [hLdef]; omega
  have hn1 : (1:ℝ) < n := by exact_mod_cast (by omega : 1 < n)
  have hn0 : (0:ℝ) < n := by linarith
  have hlogpos : 0 < Real.log n := Real.log_pos hn1
  have hkpow : (2:ℝ)^k ≤ n := by
    have := Nat.pow_log_le_self 2 (by omega : n ≠ 0)
    rw [← hk] at this
    exact_mod_cast this
  have hnlt : (n:ℝ) < 2^(k+1) := by
    have := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) n
    rw [← hk] at this
    exact_mod_cast this
  have hlog2a := Real.log_two_gt_d9
  have hlog2b := Real.log_two_lt_d9
  have hk0 : (0:ℝ) ≤ k := Nat.cast_nonneg k
  have hk_log : (k:ℝ) ≤ 2 * Real.log n := by
    have h1 : Real.log ((2:ℝ)^k) ≤ Real.log n := Real.log_le_log (by positivity) hkpow
    rw [Real.log_pow] at h1
    nlinarith
  have hlog_k : Real.log n ≤ k + 1 := by
    have h1 : Real.log n ≤ Real.log ((2:ℝ)^(k+1)) := Real.log_le_log hn0 hnlt.le
    rw [Real.log_pow] at h1
    push_cast at h1
    nlinarith
  have hD : 1 ≤ 1 + Real.log n := by linarith
  have hKc : Continuous (K n) := by
    simp only [K]
    fun_prop
  have hFc : Continuous (F n) := by
    simp only [F, S, E]
    fun_prop
  have hBm : MeasurableSet (B n) := by
    have h1 : MeasurableSet (arcs n)ᶜ := (PSL.arcs_meas (Q n) n).compl
    have h2 : MeasurableSet {t : ℝ | (1:ℝ)/2 < K n t} :=
      measurableSet_lt measurable_const hKc.measurable
    exact h1.inter h2
  have hWm : MeasurableSet (W n (fun _ => True)) := PSL.W_meas ((Q n)^2) n ((Q n:ℝ)^2)
  have hAm : MeasurableSet (B n \ W n (fun _ => True)) := hBm.diff hWm
  obtain ⟨Tn, hTn⟩ : ∃ Tn : ℝ, Tn = T n := ⟨_, rfl⟩
  have hTeq : Tn = (n:ℝ) * (1 + Real.log n)^4 := hTn
  have hTpos : 0 < Tn := by rw [hTeq]; exact mul_pos hn0 (pow_pos (by linarith) 4)
  obtain ⟨Jn, hJn⟩ : ∃ Jn, Jn = L n / 16 := ⟨_, rfl⟩
  have hJ16 : 16 * Jn ≤ L n := by omega
  have hJk : Jn ≤ k + 3 := by omega
  obtain ⟨A, hAd⟩ : ∃ A, A = B n \ W n (fun _ => True) := ⟨_, rfl⟩
  rw [← hAd] at hAm
  have hbin : ∀ j : ℕ, Jn ≤ j → j < k + 3 →
      (2:ℝ)^j * Tn * intervalIntegral ((A ∩ {t : ℝ | (2:ℝ)^j * Tn < F n t ∧
        F n t ≤ 2 * ((2:ℝ)^j * Tn)}).indicator (fun _ => (1:ℝ))) (0:ℝ) 1 MeasureTheory.volume
        ≤ (n:ℝ) / (100000 * (1 + Real.log n)^2) := by
    intro j hj1 hj2
    rw [hAd, hTn]
    exact hN0 n hnN0 hev j (by rw [hJn] at hj1; exact hj1) (by rw [hk] at hj2; exact hj2)
  have hF : ∀ t, F n t ≤ ((n:ℝ)+1)^2 * (Real.log n)^2 := by
    intro t
    have hk' : ∀ i ∈ Finset.range (n+1), ‖((high n i : ℝ) : ℂ) * E ((i:ℝ) * t)‖ ≤ Real.log n := by
      intro i hi
      have hin : (i:ℝ) ≤ n := by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have hE : ‖E ((i:ℝ)*t)‖ = 1 := by
        simp only [E]
        exact Complex.norm_exp_ofReal_mul_I _
      rw [norm_mul, hE, mul_one, Complex.norm_real, Real.norm_eq_abs]
      simp only [high, low, w]
      by_cases hp : Nat.Prime i
      · have hi1 : (1:ℝ) ≤ i := by exact_mod_cast hp.one_le
        have h0 : 0 ≤ Real.log i := Real.log_nonneg hi1
        have h1 : Real.log i ≤ Real.log n := Real.log_le_log (by linarith) hin
        by_cases hc : i^3 ≤ n
        · rw [if_pos hp, if_pos hc, sub_self, abs_zero]
          exact hlogpos.le
        · rw [if_pos hp, if_neg hc, sub_zero, abs_of_nonneg h0]
          exact h1
      · simp only [if_neg hp, ite_self, sub_zero, abs_zero]
        exact hlogpos.le
    have hnorm : ‖S n (high n) t‖ ≤ ((n:ℝ)+1) * Real.log n := by
      calc ‖S n (high n) t‖
          ≤ ∑ i ∈ Finset.range (n+1), ‖((high n i : ℝ) : ℂ) * E ((i:ℝ) * t)‖ := norm_sum_le _ _
        _ ≤ ∑ _i ∈ Finset.range (n+1), Real.log n := Finset.sum_le_sum hk'
        _ = ((n:ℝ)+1) * Real.log n := by simp
    calc F n t = ‖S n (high n) t‖^2 := rfl
      _ ≤ (((n:ℝ)+1) * Real.log n)^2 := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
      _ = _ := by ring
  have hFtop : ∀ t, F n t ≤ (2:ℝ)^(k+3) * Tn := by
    intro t
    have h2 : ((n:ℝ)+1)^2 * (Real.log n)^2 ≤ 4 * (n:ℝ)^2 * (1 + Real.log n)^4 := by
      have h3 : (Real.log n)^2 ≤ (1 + Real.log n)^4 := by
        calc (Real.log n)^2 ≤ (1 + Real.log n)^2 := by nlinarith
          _ ≤ (1 + Real.log n)^4 := pow_le_pow_right₀ hD (by norm_num)
      have h4 : ((n:ℝ)+1)^2 ≤ 4 * (n:ℝ)^2 := by nlinarith
      calc ((n:ℝ)+1)^2 * (Real.log n)^2 ≤ (4 * (n:ℝ)^2) * (Real.log n)^2 :=
            mul_le_mul_of_nonneg_right h4 (sq_nonneg _)
        _ ≤ (4 * (n:ℝ)^2) * (1 + Real.log n)^4 := mul_le_mul_of_nonneg_left h3 (by positivity)
    have h5 : 4 * (n:ℝ) ≤ (2:ℝ)^(k+3) := by
      have : (2:ℝ)^(k+3) = 4 * 2^(k+1) := by ring
      rw [this]
      linarith
    calc F n t ≤ ((n:ℝ)+1)^2 * (Real.log n)^2 := hF t
      _ ≤ 4 * (n:ℝ)^2 * (1 + Real.log n)^4 := h2
      _ = (4 * (n:ℝ)) * Tn := by rw [hTeq]; ring
      _ ≤ (2:ℝ)^(k+3) * Tn := mul_le_mul_of_nonneg_right h5 hTpos.le
  have hmB : intervalIntegral ((B n).indicator (fun _ => (1:ℝ))) (0:ℝ) 1 MeasureTheory.volume
      ≤ (0.941:ℝ)^(L n) := by
    apply PSL.bmass (B n) hBm (L n) hL1
    intro t ht
    have ht' : t ∉ arcs n ∧ (1:ℝ)/2 < K n t := ht
    have hLpos : (0:ℝ) < L n := by exact_mod_cast hL1
    have h1 : (1:ℝ)/2 < (∑ j ∈ Finset.range (L n), Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t)) / (L n : ℝ) := ht'.2
    rw [lt_div_iff₀ hLpos] at h1
    linarith
  obtain ⟨c0, hc0d⟩ : ∃ c0 : ℝ, c0 = (2:ℝ)^Jn * Tn := ⟨_, rfl⟩
  have hc0 : 0 ≤ c0 := by rw [hc0d]; positivity
  have hI0 : ∀ s : Set ℝ, 0 ≤ intervalIntegral (s.indicator (fun _ => (1:ℝ))) (0:ℝ) 1 MeasureTheory.volume :=
    fun s => intervalIntegral.integral_nonneg (by norm_num)
      (fun t _ => Set.indicator_nonneg (fun _ _ => zero_le_one) t)
  have hP1 : c0 * intervalIntegral ((B n).indicator (fun _ => (1:ℝ))) (0:ℝ) 1 MeasureTheory.volume
      ≤ (n:ℝ) / 4608 := by
    have h2 : (2:ℝ)^Jn ≤ (1.045:ℝ)^(L n) := by
      calc (2:ℝ)^Jn ≤ ((1.045:ℝ)^16)^Jn := pow_le_pow_left₀ (by norm_num) (by norm_num) Jn
        _ = (1.045:ℝ)^(16*Jn) := by rw [← pow_mul]
        _ ≤ (1.045:ℝ)^(L n) := pow_le_pow_right₀ (by norm_num) hJ16
    have h3 : Tn ≤ n * (5*(L n:ℝ))^4 := by
      rw [hTeq]
      apply mul_le_mul_of_nonneg_left _ hn0.le
      apply pow_le_pow_left₀ (by linarith)
      have hLr : (1:ℝ) ≤ L n := by exact_mod_cast hL1
      have hkr : (k:ℝ) ≤ 2 * L n + 1 := by exact_mod_cast hLk
      linarith
    have h4 : c0 ≤ (1.045:ℝ)^(L n) * (n * (5*(L n:ℝ))^4) := by
      rw [hc0d]
      exact mul_le_mul h2 h3 hTpos.le (by positivity)
    have h5 := hL0 (L n) hLL0
    calc c0 * intervalIntegral ((B n).indicator (fun _ => (1:ℝ))) (0:ℝ) 1 MeasureTheory.volume
        ≤ ((1.045:ℝ)^(L n) * (n * (5*(L n:ℝ))^4)) * (0.941:ℝ)^(L n) :=
          mul_le_mul h4 hmB (hI0 _) (by positivity)
      _ = n * ((1.045:ℝ)^(L n) * (5*(L n:ℝ))^4 * (0.941:ℝ)^(L n)) := by ring
      _ ≤ n * (1/4608) := mul_le_mul_of_nonneg_left h5 hn0.le
      _ = (n:ℝ) / 4608 := by ring
  have hBinm : ∀ j : ℕ, MeasurableSet (A ∩ {t : ℝ | (2:ℝ)^j * Tn < F n t ∧
        F n t ≤ 2 * ((2:ℝ)^j * Tn)}) := by
    intro j
    exact hAm.inter ((measurableSet_lt measurable_const hFc.measurable).inter
      (measurableSet_le hFc.measurable measurable_const))
  have hP2 : ∑ j ∈ Finset.Ico Jn (k+3), (2 * ((2:ℝ)^j * Tn)) *
      intervalIntegral ((A ∩ {t : ℝ | (2:ℝ)^j * Tn < F n t ∧
        F n t ≤ 2 * ((2:ℝ)^j * Tn)}).indicator (fun _ => (1:ℝ))) (0:ℝ) 1 MeasureTheory.volume
      ≤ (n:ℝ) / 4608 := by
    have h1 : ∀ j ∈ Finset.Ico Jn (k+3), (2 * ((2:ℝ)^j * Tn)) *
        intervalIntegral ((A ∩ {t : ℝ | (2:ℝ)^j * Tn < F n t ∧
          F n t ≤ 2 * ((2:ℝ)^j * Tn)}).indicator (fun _ => (1:ℝ))) (0:ℝ) 1 MeasureTheory.volume
        ≤ 2 * ((n:ℝ) / (100000 * (1 + Real.log n)^2)) := by
      intro j hj
      obtain ⟨hj1, hj2⟩ := Finset.mem_Ico.mp hj
      have := hbin j hj1 hj2
      linarith
    calc _ ≤ ∑ _j ∈ Finset.Ico Jn (k+3), 2 * ((n:ℝ) / (100000 * (1 + Real.log n)^2)) :=
          Finset.sum_le_sum h1
      _ = ((k+3-Jn : ℕ):ℝ) * (2 * ((n:ℝ) / (100000 * (1 + Real.log n)^2))) := by
          simp
      _ ≤ (3 * (1 + Real.log n)) * (2 * ((n:ℝ) / (100000 * (1 + Real.log n)^2))) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          have : ((k+3-Jn : ℕ):ℝ) ≤ (k:ℝ) + 3 := by
            have : k + 3 - Jn ≤ k + 3 := Nat.sub_le _ _
            exact_mod_cast this
          linarith
      _ = 6 * n / (100000 * (1 + Real.log n)) := by
          have hDne : (1 + Real.log n) ≠ 0 := by linarith
          field_simp
          ring
      _ ≤ 6 * n / 100000 := by
          apply div_le_div_of_nonneg_left (by positivity) (by norm_num)
          nlinarith
      _ ≤ (n:ℝ) / 4608 := by linarith
  rw [← hAd]
  show intervalIntegral ((A ∩ {t : ℝ | T n < F n t}).indicator (F n)) (0:ℝ) 1 MeasureTheory.volume
      ≤ (n:ℝ) / 2304
  rw [← hTn]
  have hint_ind : ∀ s : Set ℝ, MeasurableSet s → IntervalIntegrable (s.indicator (fun _ => (1:ℝ)))
      MeasureTheory.volume (0:ℝ) 1 := fun s hs => PSL.indInt hs continuous_const
  have hintB : IntervalIntegrable (fun t => c0 * (B n).indicator (fun _ => (1:ℝ)) t)
      MeasureTheory.volume (0:ℝ) 1 := (hint_ind _ hBm).const_mul c0
  have hintj : ∀ j ∈ Finset.Ico Jn (k+3), IntervalIntegrable (fun t => (2 * ((2:ℝ)^j * Tn)) *
      (A ∩ {t : ℝ | (2:ℝ)^j * Tn < F n t ∧ F n t ≤ 2 * ((2:ℝ)^j * Tn)}).indicator
        (fun _ => (1:ℝ)) t) MeasureTheory.volume (0:ℝ) 1 :=
    fun j _ => (hint_ind _ (hBinm j)).const_mul _
  have hintS : IntervalIntegrable (fun t => ∑ j ∈ Finset.Ico Jn (k+3), (2 * ((2:ℝ)^j * Tn)) *
      (A ∩ {t : ℝ | (2:ℝ)^j * Tn < F n t ∧ F n t ≤ 2 * ((2:ℝ)^j * Tn)}).indicator
        (fun _ => (1:ℝ)) t) MeasureTheory.volume (0:ℝ) 1 := by
    have h := IntervalIntegrable.sum (Finset.Ico Jn (k+3)) hintj
    convert h using 1
    funext t
    simp only [Finset.sum_apply]
  have hind1 : IntervalIntegrable ((A ∩ {t : ℝ | Tn < F n t}).indicator (F n))
      MeasureTheory.volume (0:ℝ) 1 :=
    PSL.indInt (hAm.inter (measurableSet_lt measurable_const hFc.measurable)) hFc
  have hpt : ∀ t, (A ∩ {t : ℝ | Tn < F n t}).indicator (F n) t ≤
      c0 * (B n).indicator (fun _ => (1:ℝ)) t + ∑ j ∈ Finset.Ico Jn (k+3), (2 * ((2:ℝ)^j * Tn)) *
      (A ∩ {t : ℝ | (2:ℝ)^j * Tn < F n t ∧ F n t ≤ 2 * ((2:ℝ)^j * Tn)}).indicator
        (fun _ => (1:ℝ)) t := by
    intro t
    have hsn : 0 ≤ ∑ j ∈ Finset.Ico Jn (k+3), (2 * ((2:ℝ)^j * Tn)) *
      (A ∩ {t : ℝ | (2:ℝ)^j * Tn < F n t ∧ F n t ≤ 2 * ((2:ℝ)^j * Tn)}).indicator
        (fun _ => (1:ℝ)) t :=
      Finset.sum_nonneg (fun j _ => mul_nonneg (by positivity)
        (Set.indicator_nonneg (fun _ _ => zero_le_one) t))
    have hfn : 0 ≤ c0 * (B n).indicator (fun _ => (1:ℝ)) t :=
      mul_nonneg hc0 (Set.indicator_nonneg (fun _ _ => zero_le_one) t)
    by_cases ht : t ∈ A ∩ {t : ℝ | Tn < F n t}
    · rw [Set.indicator_of_mem ht]
      obtain ⟨htA, htT⟩ := ht
      have htA' : t ∈ B n \ W n (fun _ => True) := by rw [← hAd]; exact htA
      have htB : t ∈ B n := htA'.1
      by_cases hlow : F n t ≤ c0
      · rw [Set.indicator_of_mem htB]
        linarith
      · push_neg at hlow
        have hFle : F n t ≤ c0 * 2^(k+3-Jn) := by
          calc F n t ≤ (2:ℝ)^(k+3) * Tn := hFtop t
            _ = c0 * 2^(k+3-Jn) := by
                have hpow : (2:ℝ)^(k+3) = 2^Jn * 2^(k+3-Jn) := by
                  rw [← pow_add]
                  congr 1
                  omega
                rw [hc0d, hpow]
                ring
        obtain ⟨i, hi, h1, h2⟩ := PSL.bin_exists c0 (F n t) (k+3-Jn) hlow hFle
        have hj : Jn + i ∈ Finset.Ico Jn (k+3) := Finset.mem_Ico.mpr ⟨by omega, by omega⟩
        have hy : (2:ℝ)^(Jn+i) * Tn = c0 * 2^i := by rw [hc0d, pow_add]; ring
        have hmem : t ∈ A ∩ {t : ℝ | (2:ℝ)^(Jn+i) * Tn < F n t ∧ F n t ≤ 2 * ((2:ℝ)^(Jn+i) * Tn)} := by
          refine ⟨htA, ?_, ?_⟩
          · rw [hy]; exact h1
          · rw [hy]
            calc F n t ≤ c0 * 2^(i+1) := h2
              _ = 2 * (c0 * 2^i) := by ring
        have hsingle := Finset.single_le_sum (f := fun j => (2 * ((2:ℝ)^j * Tn)) *
          (A ∩ {t : ℝ | (2:ℝ)^j * Tn < F n t ∧ F n t ≤ 2 * ((2:ℝ)^j * Tn)}).indicator
            (fun _ => (1:ℝ)) t) (fun j _ => mul_nonneg (by positivity)
            (Set.indicator_nonneg (fun _ _ => zero_le_one) t)) hj
        simp only [Set.indicator_of_mem hmem, mul_one] at hsingle
        rw [hy] at hsingle
        have : F n t ≤ 2 * (c0 * 2^i) := by
          calc F n t ≤ c0 * 2^(i+1) := h2
            _ = 2 * (c0 * 2^i) := by ring
        linarith
    · rw [Set.indicator_of_notMem ht]
      linarith
  calc intervalIntegral ((A ∩ {t : ℝ | Tn < F n t}).indicator (F n)) (0:ℝ) 1 MeasureTheory.volume
      ≤ intervalIntegral (fun t => c0 * (B n).indicator (fun _ => (1:ℝ)) t +
        ∑ j ∈ Finset.Ico Jn (k+3), (2 * ((2:ℝ)^j * Tn)) *
        (A ∩ {t : ℝ | (2:ℝ)^j * Tn < F n t ∧ F n t ≤ 2 * ((2:ℝ)^j * Tn)}).indicator
          (fun _ => (1:ℝ)) t) (0:ℝ) 1 MeasureTheory.volume :=
        intervalIntegral.integral_mono_on (by norm_num) hind1 (hintB.add hintS)
          (fun t _ => hpt t)
    _ = c0 * intervalIntegral ((B n).indicator (fun _ => (1:ℝ))) (0:ℝ) 1 MeasureTheory.volume +
        ∑ j ∈ Finset.Ico Jn (k+3), (2 * ((2:ℝ)^j * Tn)) *
        intervalIntegral ((A ∩ {t : ℝ | (2:ℝ)^j * Tn < F n t ∧
          F n t ≤ 2 * ((2:ℝ)^j * Tn)}).indicator (fun _ => (1:ℝ))) (0:ℝ) 1 MeasureTheory.volume := by
        rw [intervalIntegral.integral_add hintB hintS, intervalIntegral.integral_const_mul,
          intervalIntegral.integral_finsetSum hintj]
        congr 1
        exact Finset.sum_congr rfl (fun j _ => intervalIntegral.integral_const_mul _ _)
    _ ≤ (n:ℝ) / 4608 + (n:ℝ) / 4608 := add_le_add hP1 hP2
    _ = (n:ℝ) / 2304 := by ring
