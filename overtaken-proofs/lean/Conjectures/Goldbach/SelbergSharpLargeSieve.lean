import Mathlib

open Finset

namespace SelbergSharp

private theorem sep_sum {ι : Type*} [DecidableEq ι] (δ : ℝ) (hδ : 0 < δ) (s : ι → ℝ) :
    ∀ (n : ℕ) (S : Finset ι) (c : ℝ), 0 < c → S.card = n → (∀ j ∈ S, c ≤ s j) →
      (∀ j ∈ S, ∀ k ∈ S, j ≠ k → δ ≤ |s j - s k|) →
      ∑ j ∈ S, 1 / (s j) ^ 2 ≤ ∑ m ∈ Finset.range n, 1 / (c + m * δ) ^ 2 := by
  intro n
  induction n with
  | zero =>
    intro S c hc hS _ _
    rw [Finset.card_eq_zero] at hS
    subst hS; simp
  | succ n ih =>
    intro S c hc hS hle hsep
    have hne : S.Nonempty := by rw [← Finset.card_pos]; omega
    obtain ⟨j0, hj0, hmin⟩ := Finset.exists_min_image S s hne
    have hrest : ∀ k ∈ S.erase j0, c + δ ≤ s k := by
      intro k hk
      have hk' := Finset.mem_erase.mp hk
      have h1 := hsep k hk'.2 j0 hj0 hk'.1
      have h2 := hmin k hk'.2
      have h3 := hle j0 hj0
      rw [abs_of_nonneg (by linarith)] at h1
      linarith
    have hcard : (S.erase j0).card = n := by rw [Finset.card_erase_of_mem hj0]; omega
    have := ih (S.erase j0) (c + δ) (by linarith) hcard hrest
      (fun j hj k hk hjk => hsep j (Finset.mem_of_mem_erase hj) k (Finset.mem_of_mem_erase hk) hjk)
    rw [← Finset.add_sum_erase S _ hj0, Finset.sum_range_succ']
    have h0 : 1 / (s j0) ^ 2 ≤ 1 / (c + ((0:ℕ):ℝ) * δ) ^ 2 := by
      simp only [Nat.cast_zero, zero_mul, add_zero]
      apply one_div_le_one_div_of_le (by positivity)
      exact pow_le_pow_left₀ hc.le (hle j0 hj0) 2
    have h1 : ∑ m ∈ Finset.range n, 1 / (c + δ + (m:ℝ) * δ) ^ 2 =
        ∑ m ∈ Finset.range n, 1 / (c + ((m+1:ℕ):ℝ) * δ) ^ 2 := by
      apply Finset.sum_congr rfl; intro m _; push_cast; ring_nf
    linarith

private theorem zeta_bd (δ : ℝ) (hδ : 0 < δ) (n : ℕ) :
    ∑ m ∈ Finset.range n, 1 / (δ + (m:ℝ) * δ) ^ 2 ≤ Real.pi ^ 2 / 6 / δ ^ 2 := by
  have h1 : ∑ m ∈ Finset.range n, 1 / (δ + (m:ℝ) * δ) ^ 2 =
      (∑ m ∈ Finset.range n, 1 / ((m:ℝ) + 1) ^ 2) / δ ^ 2 := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl; intro m _
    have : (m : ℝ) + 1 > 0 := by positivity
    field_simp
    ring
  have h2 : ∑ m ∈ Finset.range n, 1 / ((m:ℝ) + 1) ^ 2 =
      ∑ m ∈ Finset.range (n + 1), 1 / (m:ℝ) ^ 2 := by
    rw [Finset.sum_range_succ' _ n]
    simp
  rw [h1, h2]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact sum_le_hasSum _ (fun m _ => by positivity) hasSum_zeta_two

private theorem circ_sum {M : ℕ} (x : Fin M → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hsep : ∀ i j : Fin M, i ≠ j → δ ≤ |x i - x j - ((round (x i - x j) : ℤ) : ℝ)|) (i : Fin M) :
    ∑ j ∈ Finset.univ.erase i, 1 / Real.sin (Real.pi * (x i - x j)) ^ 2 ≤
      Real.pi ^ 2 / 12 / δ ^ 2 := by
  set s : Fin M → ℝ := fun j => x i - x j - ((round (x i - x j) : ℤ) : ℝ) with hs
  have hsdelta : ∀ j, j ≠ i → δ ≤ |s j| := fun j hj => hsep i j (Ne.symm hj)
  have hshalf : ∀ j, |s j| ≤ 1/2 := fun j => abs_sub_round _
  have hpair : ∀ j k, j ≠ k → δ ≤ |s j - s k| := by
    intro j k hjk
    have h := hsep k j (Ne.symm hjk)
    have h2 := round_le (x k - x j) (round (x i - x j) - round (x i - x k))
    have : s j - s k = x k - x j - (((round (x i - x j) - round (x i - x k) : ℤ)) : ℝ) := by
      simp only [hs]; push_cast; ring
    rw [this]; linarith
  have hsin : ∀ j, j ≠ i →
      1 / Real.sin (Real.pi * (x i - x j)) ^ 2 ≤ 1 / (4 * (s j) ^ 2) := by
    intro j hj
    have hpos : 0 < |s j| := lt_of_lt_of_le hδ (hsdelta j hj)
    have e1 : x i - x j = s j + ((round (x i - x j) : ℤ) : ℝ) := by simp only [hs]; ring
    have e2 : Real.sin (Real.pi * (x i - x j)) ^ 2 = Real.sin (Real.pi * s j) ^ 2 := by
      rw [e1, mul_add, mul_comm Real.pi ((round (x i - x j) : ℤ) : ℝ), Real.sin_add_int_mul_pi]
      rw [mul_pow, ← zpow_natCast, ← zpow_mul]
      rw [Even.neg_one_zpow ⟨(round (x i - x j)), by ring⟩, one_mul]
    have e3 : Real.sin (Real.pi * s j) ^ 2 = Real.sin (Real.pi * |s j|) ^ 2 := by
      rcases abs_cases (s j) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h]
      simp [mul_neg, Real.sin_neg]
    have e4 : 2 * |s j| ≤ Real.sin (Real.pi * |s j|) := by
      have := Real.mul_le_sin (x := Real.pi * |s j|) (by positivity)
        (by nlinarith [Real.pi_pos, hshalf j])
      have e : 2 / Real.pi * (Real.pi * |s j|) = 2 * |s j| := by
        field_simp
      linarith
    rw [e2, e3]
    have hs0 : s j ≠ 0 := abs_pos.mp hpos
    apply one_div_le_one_div_of_le (by positivity)
    have : (2 * |s j|) ^ 2 ≤ Real.sin (Real.pi * |s j|) ^ 2 :=
      pow_le_pow_left₀ (by positivity) e4 2
    rw [mul_pow, sq_abs] at this
    linarith
  have hcard : ∀ T : Finset (Fin M), T ⊆ Finset.univ.erase i → ∀ t : Fin M → ℝ,
      (∀ j ∈ T, δ ≤ t j) → (∀ j ∈ T, ∀ k ∈ T, j ≠ k → δ ≤ |t j - t k|) →
      ∑ j ∈ T, 1 / (t j) ^ 2 ≤ Real.pi ^ 2 / 6 / δ ^ 2 := by
    intro T _ t ht hsp
    refine (sep_sum δ hδ t T.card T δ hδ rfl ht hsp).trans ?_
    have := zeta_bd δ hδ T.card
    exact this
  set P := (Finset.univ.erase i).filter (fun j => 0 < s j) with hP
  set Q := (Finset.univ.erase i).filter (fun j => ¬ 0 < s j) with hQ
  have hP' : ∑ j ∈ P, 1 / (s j) ^ 2 ≤ Real.pi ^ 2 / 6 / δ ^ 2 := by
    refine hcard P (Finset.filter_subset _ _) s ?_ (fun j _ k _ hjk => hpair j k hjk)
    intro j hj
    rw [hP, Finset.mem_filter, Finset.mem_erase] at hj
    have := hsdelta j hj.1.1
    rwa [abs_of_pos hj.2] at this
  have hQ' : ∑ j ∈ Q, 1 / (-s j) ^ 2 ≤ Real.pi ^ 2 / 6 / δ ^ 2 := by
    refine hcard Q (Finset.filter_subset _ _) (fun j => - s j) ?_ ?_
    · intro j hj
      rw [hQ, Finset.mem_filter, Finset.mem_erase] at hj
      have := hsdelta j hj.1.1
      have hneg : s j < 0 := lt_of_le_of_ne (not_lt.mp hj.2) (by
        intro h0; rw [h0] at this; simp at this; linarith)
      rwa [abs_of_neg hneg] at this
    · intro j _ k _ hjk
      have := hpair j k hjk
      rw [show -s j - -s k = -(s j - s k) by ring, abs_neg]; exact this
  calc ∑ j ∈ Finset.univ.erase i, 1 / Real.sin (Real.pi * (x i - x j)) ^ 2
      ≤ ∑ j ∈ Finset.univ.erase i, (1 / 4) * (1 / (s j) ^ 2) := by
        apply Finset.sum_le_sum; intro j hj
        refine (hsin j (Finset.mem_erase.mp hj).1).trans_eq ?_
        field_simp
    _ = (1 / 4) * (∑ j ∈ P, 1 / (s j) ^ 2 + ∑ j ∈ Q, 1 / (-s j) ^ 2) := by
        rw [← Finset.mul_sum]
        congr 1
        rw [← Finset.sum_filter_add_sum_filter_not (Finset.univ.erase i) (fun j => 0 < s j)]
        simp only [neg_sq, hP, hQ]
    _ ≤ (1 / 4) * (Real.pi ^ 2 / 6 / δ ^ 2 + Real.pi ^ 2 / 6 / δ ^ 2) := by
        gcongr
    _ = Real.pi ^ 2 / 12 / δ ^ 2 := by ring

private noncomputable def eE (x : ℝ) : ℂ := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

private theorem eE_add (x y : ℝ) : eE (x + y) = eE x * eE y := by
  unfold eE; rw [← Complex.exp_add]; congr 1; push_cast; ring

private theorem eE_zero : eE 0 = 1 := by simp [eE]

private theorem norm_eE (x : ℝ) : ‖eE x‖ = 1 := by
  unfold eE; exact Complex.norm_exp_ofReal_mul_I _

private theorem conj_eE (x : ℝ) : (starRingEnd ℂ) (eE x) = eE (-x) := by
  unfold eE; rw [← Complex.exp_conj]; congr 1
  rw [map_mul, Complex.conj_ofReal, Complex.conj_I]; push_cast; ring

private theorem eE_nat_mul (n : ℕ) (y : ℝ) : eE ((n : ℝ) * y) = (eE y) ^ n := by
  unfold eE; rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring

private theorem geom_bd (y : ℝ) (n : ℕ) (hy : Real.sin (Real.pi * y) ≠ 0) :
    ‖∑ m ∈ range n, eE ((m : ℝ) * y)‖ ≤ 1 / |Real.sin (Real.pi * y)| := by
  have hnorm : ‖eE y - 1‖ = 2 * |Real.sin (Real.pi * y)| := by
    have h1 : eE y = Complex.exp (Complex.I * ((2 * Real.pi * y : ℝ) : ℂ)) := by
      unfold eE; rw [mul_comm]
    rw [h1, Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs, abs_mul, abs_two,
      show 2 * Real.pi * y / 2 = Real.pi * y by ring]
  have hpos : 0 < |Real.sin (Real.pi * y)| := abs_pos.mpr hy
  have hne : eE y ≠ 1 := by
    intro h
    have h0 : ‖eE y - 1‖ = 0 := by rw [h]; simp
    linarith
  have hne' : eE y - 1 ≠ 0 := sub_ne_zero.mpr hne
  simp_rw [eE_nat_mul]
  rw [geom_sum_eq hne, norm_div, hnorm]
  have : ‖eE y ^ n - 1‖ ≤ 2 := by
    calc ‖eE y ^ n - 1‖ ≤ ‖eE y ^ n‖ + ‖(1:ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, norm_eE]; simp; norm_num
  rw [div_le_div_iff₀ (by positivity) hpos]
  nlinarith

private noncomputable def Kf {M : ℕ} (x : Fin M → ℝ) (N L : ℕ) (i j : Fin M) : ℝ :=
  if i = j then ((N : ℝ) + L) * L else 1 / Real.sin (Real.pi * (x i - x j)) ^ 2

private theorem Kf_nonneg {M : ℕ} (x : Fin M → ℝ) (N L : ℕ) (i j : Fin M) : 0 ≤ Kf x N L i j := by
  unfold Kf; split_ifs
  · positivity
  · positivity

private theorem Kf_symm {M : ℕ} (x : Fin M → ℝ) (N L : ℕ) (i j : Fin M) :
    Kf x N L i j = Kf x N L j i := by
  unfold Kf
  by_cases h : i = j
  · subst h; rfl
  · rw [if_neg h, if_neg (Ne.symm h)]
    have : Real.sin (Real.pi * (x j - x i)) = - Real.sin (Real.pi * (x i - x j)) := by
      rw [← Real.sin_neg]; congr 1; ring
    rw [this, neg_sq]

private theorem sum4 {α β γ δ : Type*} (s : Finset α) (t : Finset β) (u : Finset γ) (v : Finset δ)
    (T : α → β → γ → δ → ℂ) :
    ∑ a ∈ s, ∑ b ∈ t, ∑ c ∈ u, ∑ d ∈ v, T a b c d =
      ∑ c ∈ u, ∑ d ∈ v, ∑ a ∈ s, ∑ b ∈ t, T a b c d := by
  calc ∑ a ∈ s, ∑ b ∈ t, ∑ c ∈ u, ∑ d ∈ v, T a b c d
      = ∑ a ∈ s, ∑ c ∈ u, ∑ d ∈ v, ∑ b ∈ t, T a b c d := by
        apply Finset.sum_congr rfl; intro a _
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro c _
        rw [Finset.sum_comm]
    _ = ∑ c ∈ u, ∑ a ∈ s, ∑ d ∈ v, ∑ b ∈ t, T a b c d := Finset.sum_comm
    _ = ∑ c ∈ u, ∑ d ∈ v, ∑ a ∈ s, ∑ b ∈ t, T a b c d := by
        apply Finset.sum_congr rfl; intro c _
        rw [Finset.sum_comm]

private theorem shift_bd (g : ℕ → ℕ → ℝ) (hg : ∀ m l, 0 ≤ g m l) (h : ℕ → ℝ) (N L : ℕ)
    (hgh : ∀ k l, g (l + k) l = h k) :
    (L : ℝ) * ∑ k ∈ range (N + 1), h k ≤ ∑ l ∈ range L, ∑ m ∈ range (N + L), g m l := by
  have h1 : (L : ℝ) * ∑ k ∈ range (N + 1), h k = ∑ l ∈ range L, ∑ k ∈ range (N + 1), h k := by
    simp
  rw [h1]
  apply Finset.sum_le_sum
  intro l hl
  have hl' := Finset.mem_range.mp hl
  have h2 : ∑ k ∈ range (N + 1), h k = ∑ k ∈ range (N + 1), g (l + k) l :=
    Finset.sum_congr rfl fun k _ => (hgh k l).symm
  have h3 : ∑ k ∈ range (N + 1), g (l + k) l = ∑ m ∈ Finset.Ico l (l + (N + 1)), g m l := by
    rw [Finset.sum_Ico_eq_sum_range]; simp
  rw [h2, h3]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro m hm
    rw [Finset.mem_Ico] at hm
    rw [Finset.mem_range]; omega
  · intro m _ _; exact hg _ _

private theorem quad_bd {M : ℕ} (p : Fin M → ℝ) (K : Fin M → Fin M → ℝ)
    (hK0 : ∀ i j, 0 ≤ K i j) (hsym : ∀ i j, K i j = K j i) (C : ℝ)
    (hrow : ∀ i, ∑ j, K i j ≤ C) :
    ∑ i, ∑ j, p i * p j * K i j ≤ C * ∑ i, p i ^ 2 := by
  have h1 : ∑ i, ∑ j, p i * p j * K i j ≤ ∑ i, ∑ j, (p i ^ 2 / 2 + p j ^ 2 / 2) * K i j := by
    apply Finset.sum_le_sum; intro i _
    apply Finset.sum_le_sum; intro j _
    exact mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg (p i - p j)]) (hK0 _ _)
  have h2 : ∑ i, ∑ j, (p i ^ 2 / 2 + p j ^ 2 / 2) * K i j =
      ∑ i, (p i ^ 2 / 2) * ∑ j, K i j + ∑ i, (p i ^ 2 / 2) * ∑ j, K i j := by
    simp only [add_mul, Finset.sum_add_distrib]
    congr 1
    · apply Finset.sum_congr rfl; intro i _; rw [Finset.mul_sum]
    · rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro j _
      rw [hsym i j]
  have h3 : ∑ i, (p i ^ 2 / 2) * ∑ j, K i j ≤ ∑ i, (p i ^ 2 / 2) * C :=
    Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hrow i) (by positivity)
  have h4 : ∑ i, (p i ^ 2 / 2) * C = (C / 2) * ∑ i, p i ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _
    ring
  linarith [h1, h2, h3, h4]

private theorem expand_bd {M : ℕ} (x : Fin M → ℝ) (b : Fin M → ℂ) (N L : ℕ) :
    (((∑ l ∈ range L, ∑ m ∈ range (N + L),
        ‖∑ i, b i * eE (((m : ℝ) - (l : ℝ)) * x i)‖ ^ 2 : ℝ)) : ℂ) =
      ∑ i, ∑ j, b i * (starRingEnd ℂ) (b j) *
        ((∑ m ∈ range (N + L), eE ((m : ℝ) * (x i - x j))) *
          (∑ l ∈ range L, eE ((l : ℝ) * (x j - x i)))) := by
  have hterm : ∀ l m : ℕ, (((‖∑ i, b i * eE (((m : ℝ) - (l : ℝ)) * x i)‖ ^ 2 : ℝ)) : ℂ) =
      ∑ i, ∑ j, b i * (starRingEnd ℂ) (b j) *
        (eE ((m : ℝ) * (x i - x j)) * eE ((l : ℝ) * (x j - x i))) := by
    intro l m
    have h0 : (((‖∑ i, b i * eE (((m : ℝ) - (l : ℝ)) * x i)‖ ^ 2 : ℝ)) : ℂ) =
        (∑ i, b i * eE (((m : ℝ) - (l : ℝ)) * x i)) *
          (starRingEnd ℂ) (∑ i, b i * eE (((m : ℝ) - (l : ℝ)) * x i)) := by
      rw [RCLike.mul_conj]; push_cast; rfl
    rw [h0]
    simp only [map_sum, map_mul, conj_eE]
    rw [Finset.sum_mul_sum]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    have : eE (((m : ℝ) - l) * x i) * eE (-(((m : ℝ) - l) * x j)) =
        eE ((m : ℝ) * (x i - x j)) * eE ((l : ℝ) * (x j - x i)) := by
      rw [← eE_add, ← eE_add]; congr 1; ring
    calc b i * eE (((m : ℝ) - l) * x i) * ((starRingEnd ℂ) (b j) * eE (-(((m : ℝ) - l) * x j)))
        = b i * (starRingEnd ℂ) (b j) *
          (eE (((m : ℝ) - l) * x i) * eE (-(((m : ℝ) - l) * x j))) := by ring
      _ = _ := by rw [this]
  have e1 : ∀ i j, b i * (starRingEnd ℂ) (b j) *
      ((∑ m ∈ range (N + L), eE ((m : ℝ) * (x i - x j))) *
        (∑ l ∈ range L, eE ((l : ℝ) * (x j - x i)))) =
      ∑ l ∈ range L, ∑ m ∈ range (N + L), b i * (starRingEnd ℂ) (b j) *
        (eE ((m : ℝ) * (x i - x j)) * eE ((l : ℝ) * (x j - x i))) := by
    intro i j
    rw [Finset.sum_mul_sum, Finset.mul_sum, Finset.sum_comm]
    apply Finset.sum_congr rfl; intro l _
    rw [Finset.mul_sum]
  rw [Complex.ofReal_sum]
  simp only [Complex.ofReal_sum, hterm, e1]
  exact sum4 _ _ _ _ _

private theorem entry_bd {M : ℕ} (x : Fin M → ℝ) (N L : ℕ)
    (hsin : ∀ i j : Fin M, i ≠ j → Real.sin (Real.pi * (x i - x j)) ≠ 0) (i j : Fin M) :
    ‖∑ m ∈ range (N + L), eE ((m : ℝ) * (x i - x j))‖ *
      ‖∑ l ∈ range L, eE ((l : ℝ) * (x j - x i))‖ ≤ Kf x N L i j := by
  by_cases hij : i = j
  · subst hij
    have a1 : ‖∑ m ∈ range (N + L), eE ((m : ℝ) * (x i - x i))‖ ≤ (N : ℝ) + L := by
      refine (norm_sum_le _ _).trans ?_
      simp [norm_eE]
    have a2 : ‖∑ l ∈ range L, eE ((l : ℝ) * (x i - x i))‖ ≤ (L : ℝ) := by
      refine (norm_sum_le _ _).trans ?_
      simp [norm_eE]
    simp only [Kf, if_true]
    exact mul_le_mul a1 a2 (norm_nonneg _) (by positivity)
  · have hs := hsin i j hij
    have hs' : Real.sin (Real.pi * (x j - x i)) ≠ 0 := by
      intro h
      apply hs
      have : Real.sin (Real.pi * (x j - x i)) = - Real.sin (Real.pi * (x i - x j)) := by
        rw [← Real.sin_neg]; congr 1; ring
      rw [this] at h; linarith
    have a1 := geom_bd (x i - x j) (N + L) hs
    have a2 := geom_bd (x j - x i) L hs'
    have hab : |Real.sin (Real.pi * (x j - x i))| = |Real.sin (Real.pi * (x i - x j))| := by
      rw [← abs_neg, ← Real.sin_neg]; congr 2; ring
    rw [hab] at a2
    have hpos : 0 < |Real.sin (Real.pi * (x i - x j))| := abs_pos.mpr hs
    simp only [Kf, hij, if_false]
    calc _ ≤ (1 / |Real.sin (Real.pi * (x i - x j))|) * (1 / |Real.sin (Real.pi * (x i - x j))|) :=
            mul_le_mul a1 a2 (norm_nonneg _) (by positivity)
      _ = 1 / Real.sin (Real.pi * (x i - x j)) ^ 2 := by
          rw [← sq_abs (Real.sin _)]; field_simp

private theorem dual_bd {M : ℕ} (x : Fin M → ℝ) (b : Fin M → ℂ) (N L : ℕ) (hL : 0 < L) (R : ℝ)
    (hsin : ∀ i j : Fin M, i ≠ j → Real.sin (Real.pi * (x i - x j)) ≠ 0)
    (hR : ∀ i, ∑ j ∈ Finset.univ.erase i, 1 / Real.sin (Real.pi * (x i - x j)) ^ 2 ≤ R) :
    ∑ k ∈ range (N + 1), ‖∑ i, b i * eE ((k : ℝ) * x i)‖ ^ 2 ≤
      (((N : ℝ) + L) + R / L) * ∑ i, ‖b i‖ ^ 2 := by
  classical
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have step1 := shift_bd (fun m l => ‖∑ i, b i * eE (((m : ℝ) - (l : ℝ)) * x i)‖ ^ 2)
    (fun m l => by positivity) (fun k => ‖∑ i, b i * eE ((k : ℝ) * x i)‖ ^ 2) N L
    (fun k l => by
      show ‖∑ i, b i * eE ((((l + k : ℕ) : ℝ) - (l : ℝ)) * x i)‖ ^ 2 =
        ‖∑ i, b i * eE ((k : ℝ) * x i)‖ ^ 2
      simp only [Nat.cast_add, add_sub_cancel_left])
  have step2 := expand_bd x b N L
  have hQ0 : 0 ≤ ∑ l ∈ range L, ∑ m ∈ range (N + L),
      ‖∑ i, b i * eE (((m : ℝ) - (l : ℝ)) * x i)‖ ^ 2 :=
    Finset.sum_nonneg fun l _ => Finset.sum_nonneg fun m _ => by positivity
  have step3 : ∑ l ∈ range L, ∑ m ∈ range (N + L),
      ‖∑ i, b i * eE (((m : ℝ) - (l : ℝ)) * x i)‖ ^ 2 ≤
      ∑ i, ∑ j, ‖b i‖ * ‖b j‖ * Kf x N L i j := by
    calc _ = ‖((∑ l ∈ range L, ∑ m ∈ range (N + L),
          ‖∑ i, b i * eE (((m : ℝ) - (l : ℝ)) * x i)‖ ^ 2 : ℝ) : ℂ)‖ := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hQ0]
      _ = _ := by rw [step2]
      _ ≤ _ := norm_sum_le _ _
      _ ≤ _ := Finset.sum_le_sum fun i _ => norm_sum_le _ _
      _ ≤ _ := by
          apply Finset.sum_le_sum; intro i _
          apply Finset.sum_le_sum; intro j _
          calc _ = ‖b i‖ * ‖b j‖ *
                (‖∑ m ∈ range (N + L), eE ((m : ℝ) * (x i - x j))‖ *
                  ‖∑ l ∈ range L, eE ((l : ℝ) * (x j - x i))‖) := by
                simp only [norm_mul, RCLike.norm_conj] <;> ring
            _ ≤ _ := mul_le_mul_of_nonneg_left (entry_bd x N L hsin i j) (by positivity)
  have hrow : ∀ i, ∑ j, Kf x N L i j ≤ ((N : ℝ) + L) * L + R := by
    intro i
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    have h1 : Kf x N L i i = ((N : ℝ) + L) * L := by simp [Kf]
    have h2 : ∑ j ∈ Finset.univ.erase i, Kf x N L i j =
        ∑ j ∈ Finset.univ.erase i, 1 / Real.sin (Real.pi * (x i - x j)) ^ 2 := by
      apply Finset.sum_congr rfl; intro j hj
      simp only [Kf, (Finset.mem_erase.mp hj).1.symm, if_false]
    rw [h1, h2]
    linarith [hR i]
  have step4 := quad_bd (fun i => ‖b i‖) (Kf x N L) (Kf_nonneg x N L) (Kf_symm x N L) _ hrow
  have hfin : (L : ℝ) * ∑ k ∈ range (N + 1), ‖∑ i, b i * eE ((k : ℝ) * x i)‖ ^ 2 ≤
      L * ((((N : ℝ) + L) + R / L) * ∑ i, ‖b i‖ ^ 2) := by
    calc _ ≤ _ := step1
      _ ≤ _ := step3
      _ ≤ _ := step4
      _ = _ := by field_simp
  exact le_of_mul_le_mul_left hfin hLr

private theorem duality {M : ℕ} (x : Fin M → ℝ) (N : ℕ) (a : ℕ → ℂ) (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (hdual : ∀ b : Fin M → ℂ, ∑ k ∈ range (N + 1), ‖∑ i, b i * eE ((k : ℝ) * x i)‖ ^ 2 ≤
      Δ * ∑ i, ‖b i‖ ^ 2) :
    ∑ i, ‖∑ k ∈ range (N + 1), a k * eE ((k : ℝ) * x i)‖ ^ 2 ≤
      Δ * ∑ k ∈ range (N + 1), ‖a k‖ ^ 2 := by
  obtain ⟨c, hc⟩ : ∃ c : Fin M → ℂ, ∀ i, c i = ∑ k ∈ range (N + 1), a k * eE ((k : ℝ) * x i) :=
    ⟨_, fun _ => rfl⟩
  simp only [← hc]
  have hX : (((∑ i, ‖c i‖ ^ 2 : ℝ)) : ℂ) =
      ∑ k ∈ range (N + 1), a k * ∑ i, (starRingEnd ℂ) (c i) * eE ((k : ℝ) * x i) := by
    have h1 : ∀ i, (((‖c i‖ ^ 2 : ℝ)) : ℂ) = c i * (starRingEnd ℂ) (c i) := by
      intro i; rw [RCLike.mul_conj]; push_cast; rfl
    rw [Complex.ofReal_sum]
    simp only [h1]
    have h2 : ∀ i, c i * (starRingEnd ℂ) (c i) =
        ∑ k ∈ range (N + 1), a k * ((starRingEnd ℂ) (c i) * eE ((k : ℝ) * x i)) := by
      intro i
      generalize (starRingEnd ℂ) (c i) = z
      rw [hc i, Finset.sum_mul]
      apply Finset.sum_congr rfl; intro k _
      ring
    simp only [h2]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro k _
    rw [Finset.mul_sum]
  have hX0 : 0 ≤ ∑ i, ‖c i‖ ^ 2 := Finset.sum_nonneg fun i _ => by positivity
  have hP : ∑ i, ‖c i‖ ^ 2 ≤ ∑ k ∈ range (N + 1),
      ‖a k‖ * ‖∑ i, (starRingEnd ℂ) (c i) * eE ((k : ℝ) * x i)‖ := by
    calc ∑ i, ‖c i‖ ^ 2 = ‖(((∑ i, ‖c i‖ ^ 2 : ℝ)) : ℂ)‖ := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hX0]
      _ = ‖∑ k ∈ range (N + 1), a k * ∑ i, (starRingEnd ℂ) (c i) * eE ((k : ℝ) * x i)‖ := by
          rw [hX]
      _ ≤ _ := (norm_sum_le _ _).trans (by simp only [norm_mul]; exact le_rfl)
  have hD := hdual (fun i => (starRingEnd ℂ) (c i))
  simp only [RCLike.norm_conj] at hD
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq (range (N + 1)) (fun k => ‖a k‖)
    (fun k => ‖∑ i, (starRingEnd ℂ) (c i) * eE ((k : ℝ) * x i)‖)
  have hA : 0 ≤ ∑ k ∈ range (N + 1), ‖a k‖ ^ 2 := Finset.sum_nonneg fun i _ => by positivity
  have hsq : (∑ i, ‖c i‖ ^ 2) ^ 2 ≤ (∑ k ∈ range (N + 1), ‖a k‖ ^ 2) *
      (Δ * ∑ i, ‖c i‖ ^ 2) := by
    calc (∑ i, ‖c i‖ ^ 2) ^ 2 ≤ (∑ k ∈ range (N + 1),
          ‖a k‖ * ‖∑ i, (starRingEnd ℂ) (c i) * eE ((k : ℝ) * x i)‖) ^ 2 :=
          pow_le_pow_left₀ hX0 hP 2
      _ ≤ _ := hCS
      _ ≤ _ := mul_le_mul_of_nonneg_left hD hA
  by_cases h0 : ∑ i, ‖c i‖ ^ 2 = 0
  · rw [h0]; positivity
  · have hpos : 0 < ∑ i, ‖c i‖ ^ 2 := lt_of_le_of_ne hX0 (Ne.symm h0)
    refine le_of_mul_le_mul_right ?_ hpos
    nlinarith [hsq]

private theorem sin_ne {M : ℕ} (x : Fin M → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hsep : ∀ i j : Fin M, i ≠ j → δ ≤ |x i - x j - ((round (x i - x j) : ℤ) : ℝ)|)
    (i j : Fin M) (hij : i ≠ j) : Real.sin (Real.pi * (x i - x j)) ≠ 0 := by
  intro h
  obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp h
  have h1 : (n : ℝ) = x i - x j := by
    have := Real.pi_pos
    have h2 : (n : ℝ) * Real.pi = (x i - x j) * Real.pi := by rw [hn]; ring
    exact mul_right_cancel₀ this.ne' h2
  have h3 := round_le (x i - x j) n
  have h4 := hsep i j hij
  have h5 : |x i - x j - (n : ℝ)| = 0 := by rw [← h1]; simp
  linarith

private theorem main_bd (M N : ℕ) (x : Fin M → ℝ) (δ : ℝ) (a : ℕ → ℂ) (hδ : 0 < δ)
    (hsep : ∀ i j : Fin M, i ≠ j → δ ≤ |x i - x j - ((round (x i - x j) : ℤ) : ℝ)|) :
    ∑ i, ‖∑ k ∈ range (N + 1), a k * eE ((k : ℝ) * x i)‖ ^ 2 ≤
      ((N : ℝ) + max 1 (2 / δ)) * ∑ k ∈ range (N + 1), ‖a k‖ ^ 2 := by
  have hsin := sin_ne x δ hδ hsep
  by_cases hM : M ≤ 1
  · have hdual := fun b => dual_bd x b N 1 Nat.one_pos 0 hsin (by
      intro i
      have : Finset.univ.erase i = (∅ : Finset (Fin M)) := by
        rw [← Finset.card_eq_zero, Finset.card_erase_of_mem (Finset.mem_univ i)]
        simp; omega
      rw [this]; simp) 
    have := duality x N a (((N : ℝ) + 1) + 0 / (1 : ℕ)) (by positivity) hdual
    refine this.trans ?_
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun k _ => by positivity)
    simp
  · push_neg at hM
    have hδ2 : δ ≤ 1 / 2 := by
      have := hsep ⟨0, by omega⟩ ⟨1, hM⟩ (by simp [Fin.ext_iff])
      exact this.trans (abs_sub_round _)
    have hmax : max 1 (2 / δ) = 2 / δ := by
      apply max_eq_right
      rw [le_div_iff₀ hδ]; linarith
    rw [hmax]
    obtain ⟨t, ht⟩ : ∃ t : ℝ, t = 1 / δ := ⟨_, rfl⟩
    have ht2 : 2 ≤ t := by rw [ht, le_div_iff₀ hδ]; linarith
    set L : ℕ := ⌊t⌋₊ with hL
    have hL2 : 2 ≤ L := Nat.le_floor (by exact_mod_cast ht2)
    have hLt : (L : ℝ) ≤ t := Nat.floor_le (by linarith)
    have htL : t < L + 1 := Nat.lt_floor_add_one t
    have hL2r : (2 : ℝ) ≤ L := by exact_mod_cast hL2
    have hLpos : (0 : ℝ) < L := by linarith
    have hpi : Real.pi ^ 2 / 12 ≤ 0.827 := by
      have := Real.pi_lt_d2
      have := Real.pi_pos
      nlinarith
    have key : (t - L) ^ 2 ≤ 0.173 * t ^ 2 := by
      by_cases h : 2.5 ≤ t
      · nlinarith
      · nlinarith
    have hineq : (L : ℝ) + Real.pi ^ 2 / 12 / δ ^ 2 / L ≤ 2 / δ := by
      have e1 : Real.pi ^ 2 / 12 / δ ^ 2 / L = (Real.pi ^ 2 / 12) * t ^ 2 / L := by
        rw [ht]; field_simp
      have e2 : 2 / δ = 2 * t := by rw [ht]; ring
      rw [e1, e2, ← sub_nonneg]
      have : 2 * t - (L + Real.pi ^ 2 / 12 * t ^ 2 / L) =
          (2 * t * L - L ^ 2 - Real.pi ^ 2 / 12 * t ^ 2) / L := by
        have hL0 : (L : ℝ) ≠ 0 := hLpos.ne'
        first | (field_simp; done) | (field_simp; ring)
      rw [this]
      apply div_nonneg _ hLpos.le
      nlinarith [sq_nonneg t]
    have hdual := fun b => dual_bd x b N L (by omega) (Real.pi ^ 2 / 12 / δ ^ 2) hsin
      (fun i => circ_sum x δ hδ hsep i)
    have := duality x N a (((N : ℝ) + L) + Real.pi ^ 2 / 12 / δ ^ 2 / L) (by positivity) hdual
    refine this.trans ?_
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun k _ => by positivity)
    linarith

end SelbergSharp

theorem Conjectures.Goldbach.SelbergSharpLargeSieve :
    let E (x : ℝ) := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I); ∀ (M N : ℕ) (x : Fin M → ℝ) (δ : ℝ) (a : ℕ → ℂ), 0 < δ → (∀ i j : Fin M, i ≠ j → δ ≤ |x i - x j - ((round (x i - x j) : ℤ) : ℝ)|) → (∑ i : Fin M, ‖∑ k ∈ Finset.range (N + 1), a k * E ((k : ℝ) * x i)‖ ^ 2) ≤ ((N : ℝ) + max 1 (2 / δ)) * ∑ k ∈ Finset.range (N + 1), ‖a k‖ ^ 2 := by
  intro E M N x δ a hδ hsep
  exact SelbergSharp.main_bd M N x δ a hδ hsep
