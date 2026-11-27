import Mathlib

private lemma pwse_shift {G : Type*} [AddCommGroup G] (g : ℕ → G) (N : ℕ) :
    ∑ j ∈ Finset.range 30, g (N + 1 + j) - ∑ j ∈ Finset.range 30, g (N + j) = g (N + 30) - g N := by
  have h1 : ∑ j ∈ Finset.range 30, g (N + 1 + j) = ∑ j ∈ Finset.range 31, g (N + j) - g N := by
    rw [Finset.sum_range_succ' (fun j => g (N + j)) 30]
    simp only [add_zero]
    have : ∑ j ∈ Finset.range 30, g (N + (j + 1)) = ∑ j ∈ Finset.range 30, g (N + 1 + j) :=
      Finset.sum_congr rfl (fun j _ => by rw [show N + (j + 1) = N + 1 + j by ring])
    rw [this]
    abel
  have h2 : ∑ j ∈ Finset.range 31, g (N + j) = ∑ j ∈ Finset.range 30, g (N + j) + g (N + 30) :=
    Finset.sum_range_succ _ 30
  rw [h1, h2]; abel

private lemma pwse_tele {G : Type*} [AddCommGroup G] (g : ℕ → G) (N : ℕ) :
    ∑ k ∈ Finset.range N, (g (k + 30) - g k)
      = ∑ j ∈ Finset.range 30, g (N + j) - ∑ j ∈ Finset.range 30, g j := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    have := pwse_shift g N
    have e : g (N + 30) - g N = ∑ j ∈ Finset.range 30, g (N + 1 + j) - ∑ j ∈ Finset.range 30, g (N + j) := this.symm
    rw [e]; abel

private lemma pwse_per (k : ℕ) : Nat.Coprime (k + 30) 30 ↔ Nat.Coprime k 30 := by
  simp [Nat.Coprime]

private lemma pwse_w30 (w : ℕ → ℝ) (hw : ∀ k, w k = if Nat.Coprime k 30 then (30 : ℝ) / 8 else 0) (N : ℕ) :
    ∑ j ∈ Finset.range 30, w (N + j) = 30 := by
  induction N with
  | zero =>
    simp only [zero_add, hw]
    simp [Finset.sum_range_succ, Nat.Coprime]
    norm_num
  | succ N ih =>
    have := pwse_shift w N
    have hp : w (N + 30) = w N := by
      rw [hw, hw]; simp only [if_congr (pwse_per N) rfl rfl]
    linarith

theorem Conjectures.Goldbach.PacketWheelSmoothEnvelope :
    let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t)); let model := fun k : ℕ => if Nat.Coprime k 30 then (30:ℝ)/8 else 0; let D := fun (n : ℕ) (t : ℝ) => ((n:ℝ)+1)^2/(1+((n:ℝ)+1)^2*‖E (30*t)-1‖^2); ∀ (n : ℕ) (t : ℝ), ‖S n model t‖^2 ≤ 3616*D n t := by
  intro E S model D n t
  have hw : ∀ k, model k = if Nat.Coprime k 30 then (30 : ℝ) / 8 else 0 := fun k => rfl
  have hw0 : ∀ k, 0 ≤ model k := fun k => by rw [hw]; split_ifs <;> norm_num
  have hw1 : ∀ k, model k ≤ 15 / 4 := fun k => by rw [hw]; split_ifs <;> norm_num
  have hper : ∀ k, model (k + 30) = model k := fun k => by
    rw [hw, hw]; simp only [if_congr (pwse_per k) rfl rfl]
  have hE : ∀ x y, E (x + y) = E x * E y := by
    intro x y
    simp only [E, ← Complex.exp_add]
    congr 1
    push_cast; ring
  set z := E (30 * t) with hz
  set F : ℕ → ℂ := fun k => (model k : ℂ) * E ((k : ℝ) * t) with hF
  have hFs : ∀ k, F (k + 30) = F k * z := by
    intro k
    simp only [hF, hper]
    have : E (((k + 30 : ℕ) : ℝ) * t) = E ((k : ℝ) * t) * E (30 * t) := by
      rw [← hE]; congr 1; push_cast; ring
    rw [this]; ring
  have hS : S n model t = ∑ k ∈ Finset.range (n + 1), F k := rfl
  have h1 : (z - 1) * S n model t = ∑ k ∈ Finset.range (n + 1), (F (k + 30) - F k) := by
    rw [hS, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [hFs]; ring
  have hwin : ∀ N, ‖∑ j ∈ Finset.range 30, F (N + j)‖ ≤ 30 := by
    intro N
    refine (norm_sum_le _ _).trans ?_
    have : ∀ j ∈ Finset.range 30, ‖F (N + j)‖ = model (N + j) := by
      intro j _
      simp only [hF, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw0 _)]
      have : ‖E (((N + j : ℕ) : ℝ) * t)‖ = 1 := by
        simp only [E]
        rw [Complex.norm_exp_ofReal_mul_I]
      rw [this, mul_one]
    rw [Finset.sum_congr rfl this, pwse_w30 model hw N]
  have h2 : ‖z - 1‖ * ‖S n model t‖ ≤ 60 := by
    rw [← norm_mul, h1, pwse_tele F (n + 1)]
    refine (norm_sub_le _ _).trans ?_
    have := hwin (n + 1)
    have := hwin 0
    simp only [zero_add] at this
    linarith
  have h3 : ‖S n model t‖ ≤ 15 / 4 * ((n : ℝ) + 1) := by
    rw [hS]
    refine (norm_sum_le _ _).trans ?_
    have : ∀ k ∈ Finset.range (n + 1), ‖F k‖ ≤ 15 / 4 := by
      intro k _
      simp only [hF, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw0 _)]
      have : ‖E ((k : ℝ) * t)‖ = 1 := by
        simp only [E]
        rw [Complex.norm_exp_ofReal_mul_I]
      rw [this, mul_one]; exact hw1 k
    refine (Finset.sum_le_sum this).trans ?_
    simp
    linarith
  show ‖S n model t‖ ^ 2 ≤ 3616 * (((n : ℝ) + 1) ^ 2 / (1 + ((n : ℝ) + 1) ^ 2 * ‖z - 1‖ ^ 2))
  have hM : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hpos : (0 : ℝ) < 1 + ((n : ℝ) + 1) ^ 2 * ‖z - 1‖ ^ 2 := by positivity
  rw [← mul_div_assoc, le_div_iff₀ hpos]
  set X := ‖S n model t‖
  set d := ‖z - 1‖
  have hX : 0 ≤ X := norm_nonneg _
  have hd : 0 ≤ d := norm_nonneg _
  have a1 : X ^ 2 ≤ (15 / 4 * ((n : ℝ) + 1)) ^ 2 := pow_le_pow_left₀ hX h3 2
  have a2 : (d * X) ^ 2 ≤ 60 ^ 2 := pow_le_pow_left₀ (by positivity) h2 2
  have e : X ^ 2 * (1 + ((n : ℝ) + 1) ^ 2 * d ^ 2) = X ^ 2 + ((n : ℝ) + 1) ^ 2 * (d * X) ^ 2 := by ring
  rw [e]
  nlinarith [sq_nonneg ((n : ℝ) + 1)]
