import Mathlib

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

theorem Conjectures.Goldbach.PacketExponentialMoment :
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
