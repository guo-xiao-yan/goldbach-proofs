import Mathlib

private lemma dcw_ident (H : ℕ) (hH : 0 < H) (a b : ℕ → ℝ) :
    (∑ s ∈ Finset.range H, ∑ t ∈ Finset.range H, (a s - a t) * (b s - b t)) / (2 * (H:ℝ))
      = (∑ t ∈ Finset.range H, a t * b t) - (∑ t ∈ Finset.range H, a t) * (∑ t ∈ Finset.range H, b t) / H := by
  have hH' : (H:ℝ) ≠ 0 := by positivity
  have e : (∑ s ∈ Finset.range H, ∑ t ∈ Finset.range H, (a s - a t) * (b s - b t))
      = 2 * H * (∑ t ∈ Finset.range H, a t * b t) - 2 * ((∑ t ∈ Finset.range H, a t) * (∑ t ∈ Finset.range H, b t)) := by
    have h1 : ∀ s t : ℕ, (a s - a t) * (b s - b t) = a s * b s + a t * b t - a s * b t - a t * b s := by
      intro s t; ring
    simp only [h1, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, ← Finset.mul_sum, ← Finset.sum_mul]
    ring
  rw [e]; field_simp

private lemma dcw_core (H B n : ℕ) (hn : n = 8 * (H * B)) (hH : 0 < H) (w : ℕ → ℝ) (hw : ∀ p, 0 ≤ w p)
    (hwin : ∀ x : ℕ, n ≤ 3*x → 3*x ≤ 2*n → (H:ℝ)/2 ≤ ∑ t ∈ Finset.range H, w (x+t)) :
    (n:ℝ)/32 + (∑ j ∈ Finset.range B, (∑ s ∈ Finset.range H, ∑ t ∈ Finset.range H,
        (w (n/2+j*H+s) - w (n/2+j*H+t)) * (w (n - (n/2+j*H+s)) - w (n - (n/2+j*H+t)))) / (2*(H:ℝ)))
      ≤ ∑ p ∈ (Finset.range (n+1)).filter (fun p => n ≤ 3*p ∧ 3*p ≤ 2*n), w p * w (n-p) := by
  have hn2 : n / 2 = 4 * (H * B) := by omega
  have hcell : ∀ j ∈ Finset.range B, (H:ℝ)/2 * ((H:ℝ)/2) / H ≤
      (∑ t ∈ Finset.range H, w (n/2+j*H+t)) * (∑ t ∈ Finset.range H, w (n - (n/2+j*H+t))) / H := by
    intro j hj
    have hj' : j + 1 ≤ B := Finset.mem_range.mp hj
    have hjH : (j+1) * H ≤ B * H := Nat.mul_le_mul_right H hj'
    have hjH' : j * H + H ≤ B * H := by nlinarith
    have hHB : H * B = B * H := mul_comm _ _
    have hA := hwin (n/2+j*H) (by omega) (by omega)
    have hB := hwin (n - (n/2+j*H+(H-1)) ) (by omega) (by omega)
    have hrefl : ∑ t ∈ Finset.range H, w (n - (n/2+j*H+t)) =
        ∑ t ∈ Finset.range H, w (n - (n/2+j*H+(H-1)) + t) := by
      rw [← Finset.sum_range_reflect]
      apply Finset.sum_congr rfl
      intro t ht
      have := Finset.mem_range.mp ht
      congr 1
      omega
    rw [hrefl]
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply mul_le_mul hA hB (by positivity) (Finset.sum_nonneg (fun _ _ => hw _))
  have hsum : (n:ℝ)/32 ≤ ∑ j ∈ Finset.range B, (∑ t ∈ Finset.range H, w (n/2+j*H+t)) * (∑ t ∈ Finset.range H, w (n - (n/2+j*H+t))) / H := by
    have := Finset.sum_le_sum hcell
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at this
    have hHr : (H:ℝ) ≠ 0 := by positivity
    have : (n:ℝ)/32 = B * ((H:ℝ)/2 * ((H:ℝ)/2) / H) := by
      rw [hn]; push_cast; field_simp; ring
    linarith [this]
  have hsub : ∑ j ∈ Finset.range B, ∑ t ∈ Finset.range H, w (n/2+j*H+t) * w (n - (n/2+j*H+t))
      ≤ ∑ p ∈ (Finset.range (n+1)).filter (fun p => n ≤ 3*p ∧ 3*p ≤ 2*n), w p * w (n-p) := by
    rw [← Finset.sum_product' (f := fun j t => w (n/2+j*H+t) * w (n - (n/2+j*H+t)))]
    have hinj : Set.InjOn (fun x : ℕ × ℕ => n/2 + x.1*H + x.2) (↑(Finset.range B ×ˢ Finset.range H)) := by
      rintro ⟨j1, t1⟩ h1 ⟨j2, t2⟩ h2 h
      simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_range] at h1 h2
      simp only at h
      have h' : j1 * H + t1 = j2 * H + t2 := by omega
      rcases lt_trichotomy j1 j2 with hl | hl | hl
      · have : (j1+1)*H ≤ j2*H := Nat.mul_le_mul_right _ hl
        nlinarith
      · subst hl
        have : t1 = t2 := by omega
        subst this; rfl
      · have : (j2+1)*H ≤ j1*H := Nat.mul_le_mul_right _ hl
        nlinarith
    have himg := Finset.sum_image (f := fun p => w p * w (n - p)) hinj
    rw [← himg]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p hp
      simp only [Finset.mem_image, Finset.mem_product, Finset.mem_range] at hp
      obtain ⟨⟨j, t⟩, ⟨hj, ht⟩, rfl⟩ := hp
      have hjH : (j+1) * H ≤ B * H := Nat.mul_le_mul_right H hj
      have hHB : H * B = B * H := mul_comm _ _
      simp only [Finset.mem_filter, Finset.mem_range]
      constructor <;> [skip; constructor] <;> nlinarith
    · intro p _ _
      exact mul_nonneg (hw _) (hw _)
  have hid : ∑ j ∈ Finset.range B, (∑ s ∈ Finset.range H, ∑ t ∈ Finset.range H,
        (w (n/2+j*H+s) - w (n/2+j*H+t)) * (w (n - (n/2+j*H+s)) - w (n - (n/2+j*H+t)))) / (2*(H:ℝ))
      = ∑ j ∈ Finset.range B, ((∑ t ∈ Finset.range H, w (n/2+j*H+t) * w (n - (n/2+j*H+t)))
          - (∑ t ∈ Finset.range H, w (n/2+j*H+t)) * (∑ t ∈ Finset.range H, w (n - (n/2+j*H+t))) / H) := by
    apply Finset.sum_congr rfl
    intro j _
    exact dcw_ident H hH (fun t => w (n/2+j*H+t)) (fun t => w (n - (n/2+j*H+t)))
  rw [hid, Finset.sum_sub_distrib]
  linarith

theorem Conjectures.Goldbach.DyadicCellWindowTransfer :
    let w := fun p : ℕ => if Nat.Prime p then Real.log (p : ℝ) else 0; ∀ k : ℕ, 12 ≤ k → let n : ℕ := 2^k; let H : ℕ := 2^(k-k/4); let B : ℕ := 2^(k/4-3); let p := fun j t : ℕ => n/2+j*H+t; let a := fun j t : ℕ => w (p j t); let b := fun j t : ℕ => w (n-p j t); (∀ x : ℕ, n ≤ 3*x → 3*x ≤ 2*n → (H:ℝ)/2 ≤ ∑ t ∈ Finset.range H, w (x+t)) → (n:ℝ)/32 + (∑ j ∈ Finset.range B, (∑ s ∈ Finset.range H, ∑ t ∈ Finset.range H, (a j s-a j t)*(b j s-b j t)) / (2*(H:ℝ))) ≤ (∑ p ∈ (Finset.range (n+1)).filter (fun p => n ≤ 3*p ∧ 3*p ≤ 2*n), w p * w (n-p)) := by
  intro w k hk n H B p a b hwin
  have hw : ∀ q, 0 ≤ w q := by
    intro q
    simp only [w]
    split_ifs with h
    · exact Real.log_nonneg (by exact_mod_cast h.one_lt.le)
    · exact le_refl _
  have hn : n = 8 * (H * B) := by
    have : k = (k - k/4) + (k/4 - 3) + 3 := by omega
    simp only [n, H, B]
    conv_lhs => rw [this]
    rw [pow_add, pow_add]; ring
  exact dcw_core H B n hn (by positivity) w hw hwin
