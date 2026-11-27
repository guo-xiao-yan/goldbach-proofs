import Mathlib

private theorem vert_bad (p X X' i k : ℤ) (hp : 0 < p) (hX : 0 ≤ X ∧ X < p) (hX' : 0 ≤ X' ∧ X' < p)
    (hn : X ≠ X') (hi : 0 ≤ i ∧ i ≤ 1) (hk : 0 ≤ k ∧ k ≤ 1) (h : X' + k * p - X - i * p = 0) : False := by
  obtain ⟨h1, h2⟩ := hi
  obtain ⟨h3, h4⟩ := hk
  obtain rfl | rfl : i = 0 ∨ i = 1 := by omega
  all_goals obtain rfl | rfl : k = 0 ∨ k = 1 := by omega
  all_goals omega

private theorem diag_bad (p T a Y X a' Y' X' k l : ℤ)
    (hp : p = 2 * T + 1) (hT : 1 ≤ T)
    (ha : 1 ≤ a ∧ a < p) (hY : 1 ≤ Y ∧ Y < p) (hX0 : 0 ≤ X ∧ X < p)
    (ha' : 1 ≤ a' ∧ a' < p) (hY' : 1 ≤ Y' ∧ Y' < p) (hX0' : 0 ≤ X' ∧ X' < p)
    (hX : (X = a + T ∧ a + T < p) ∨ (X + p = a + T ∧ p ≤ a + T))
    (hX' : (X' = a' + T ∧ a' + T < p) ∨ (X' + p = a' + T ∧ p ≤ a' + T))
    (hna : a ≠ a') (hnY : Y ≠ Y') (hnX : X ≠ X')
    (hM : (Y' - Y - (X' - X) = -p ∨ Y' - Y - (X' - X) = 0 ∨ Y' - Y - (X' - X) = p) →
      (a' + Y = p ∧ Y' + a = p))
    (hk : 0 ≤ k ∧ k ≤ 1) (hl : 0 ≤ l ∧ l ≤ 1)
    (c1 : ¬ (a ≤ T ∧ T < Y)) (c2 : ¬ (T < a ∧ Y ≤ T))
    (cy : ¬ (T < a' ∧ T < Y' ∧ k = 1 ∧ l = 0) ∧ ¬ (T < a' ∧ Y' ≤ T ∧ k = 1 ∧ l = 1) ∧
          ¬ (a' ≤ T ∧ T < Y' ∧ k = 0 ∧ l = 0) ∧ ¬ (a' ≤ T ∧ Y' ≤ T ∧ k = 0 ∧ l = 1))
    (h : (Y' - Y) - (X' - X) + (l - k) * p = 0) : False := by
  obtain ⟨h1, h2⟩ := hk
  obtain ⟨h3, h4⟩ := hl
  obtain rfl | rfl : k = 0 ∨ k = 1 := by omega
  all_goals obtain rfl | rfl : l = 0 ∨ l = 1 := by omega
  all_goals (have h1 := hM (by omega); omega)

private theorem anti_bad (p T a Y X a' Y' X' k l : ℤ)
    (hp : p = 2 * T + 1) (hT : 1 ≤ T)
    (ha : 1 ≤ a ∧ a < p) (hY : 1 ≤ Y ∧ Y < p) (hX0 : 0 ≤ X ∧ X < p)
    (ha' : 1 ≤ a' ∧ a' < p) (hY' : 1 ≤ Y' ∧ Y' < p) (hX0' : 0 ≤ X' ∧ X' < p)
    (hX : (X = a + T ∧ a + T < p) ∨ (X + p = a + T ∧ p ≤ a + T))
    (hX' : (X' = a' + T ∧ a' + T < p) ∨ (X' + p = a' + T ∧ p ≤ a' + T))
    (hna : a ≠ a') (hnY : Y ≠ Y') (hnX : X ≠ X')
    (hA : ((X' - X) + (Y' - Y) = -p ∨ (X' - X) + (Y' - Y) = 0 ∨ (X' - X) + (Y' - Y) = p) →
      (a' = Y ∧ Y' = a))
    (hk : 0 ≤ k ∧ k ≤ 1) (hl : 0 ≤ l ∧ l ≤ 1)
    (c1 : ¬ (a ≤ T ∧ Y ≤ T)) (c2 : ¬ (T < a ∧ T < Y))
    (cy : ¬ (T < a' ∧ T < Y' ∧ k = 1 ∧ l = 0) ∧ ¬ (T < a' ∧ Y' ≤ T ∧ k = 1 ∧ l = 1) ∧
          ¬ (a' ≤ T ∧ T < Y' ∧ k = 0 ∧ l = 0) ∧ ¬ (a' ≤ T ∧ Y' ≤ T ∧ k = 0 ∧ l = 1))
    (h : (Y' - Y) + (X' - X) + (l + k - 1) * p = 0) : False := by
  obtain ⟨h1, h2⟩ := hk
  obtain ⟨h3, h4⟩ := hl
  obtain rfl | rfl : k = 0 ∨ k = 1 := by omega
  all_goals obtain rfl | rfl : l = 0 ∨ l = 1 := by omega
  all_goals (have h1 := hA (by omega); omega)

set_option maxHeartbeats 1000000 in
private theorem key_arith (p T a Y X a' Y' X' i j i' j' k l : ℤ)
    (hp : p = 2 * T + 1) (hT : 1 ≤ T)
    (ha : 1 ≤ a ∧ a < p) (hY : 1 ≤ Y ∧ Y < p) (hX0 : 0 ≤ X ∧ X < p)
    (ha' : 1 ≤ a' ∧ a' < p) (hY' : 1 ≤ Y' ∧ Y' < p) (hX0' : 0 ≤ X' ∧ X' < p)
    (hX : (X = a + T ∧ a + T < p) ∨ (X + p = a + T ∧ p ≤ a + T))
    (hX' : (X' = a' + T ∧ a' + T < p) ∨ (X' + p = a' + T ∧ p ≤ a' + T))
    (hna : a ≠ a') (hnY : Y ≠ Y') (hnX : X ≠ X')
    (hM : (Y' - Y - (X' - X) = -p ∨ Y' - Y - (X' - X) = 0 ∨ Y' - Y - (X' - X) = p) →
      (a' + Y = p ∧ Y' + a = p))
    (hA : ((X' - X) + (Y' - Y) = -p ∨ (X' - X) + (Y' - Y) = 0 ∨ (X' - X) + (Y' - Y) = p) →
      (a' = Y ∧ Y' = a))
    (hi : 0 ≤ i ∧ i ≤ 1) (hj : 0 ≤ j ∧ j ≤ 1) (hi' : 0 ≤ i' ∧ i' ≤ 1) (hj' : 0 ≤ j' ∧ j' ≤ 1)
    (hk : 0 ≤ k ∧ k ≤ 1) (hl : 0 ≤ l ∧ l ≤ 1)
    (hne : ¬ (i = i' ∧ j = j'))
    (cx : ¬ (T < a ∧ T < Y ∧ i = 1 ∧ j = 0) ∧ ¬ (T < a ∧ Y ≤ T ∧ i = 1 ∧ j = 1) ∧
          ¬ (a ≤ T ∧ T < Y ∧ i = 0 ∧ j = 0) ∧ ¬ (a ≤ T ∧ Y ≤ T ∧ i = 0 ∧ j = 1))
    (cx' : ¬ (T < a ∧ T < Y ∧ i' = 1 ∧ j' = 0) ∧ ¬ (T < a ∧ Y ≤ T ∧ i' = 1 ∧ j' = 1) ∧
          ¬ (a ≤ T ∧ T < Y ∧ i' = 0 ∧ j' = 0) ∧ ¬ (a ≤ T ∧ Y ≤ T ∧ i' = 0 ∧ j' = 1))
    (cy : ¬ (T < a' ∧ T < Y' ∧ k = 1 ∧ l = 0) ∧ ¬ (T < a' ∧ Y' ≤ T ∧ k = 1 ∧ l = 1) ∧
          ¬ (a' ≤ T ∧ T < Y' ∧ k = 0 ∧ l = 0) ∧ ¬ (a' ≤ T ∧ Y' ≤ T ∧ k = 0 ∧ l = 1))
    (hdet : (i' - i) * (Y' + l * p - Y - j * p) - (j' - j) * (X' + k * p - X - i * p) = 0) :
    False := by
  have hp0 : 0 < p := by omega
  obtain ⟨hi0, hi1⟩ := hi
  obtain ⟨hj0, hj1⟩ := hj
  obtain ⟨hi0', hi1'⟩ := hi'
  obtain ⟨hj0', hj1'⟩ := hj'
  rcases (by omega : i = 0 ∨ i = 1) with hi | hi <;>
  rcases (by omega : j = 0 ∨ j = 1) with hj | hj <;>
  rcases (by omega : i' = 0 ∨ i' = 1) with hi' | hi' <;>
  rcases (by omega : j' = 0 ∨ j' = 1) with hj' | hj'
  · exact absurd ⟨by omega, by omega⟩ hne
  · exact vert_bad p X X' i k hp0 hX0 hX0' hnX (by omega) hk
      (by simp only [hi, hj, hi', hj'] at hdet ⊢; linarith)
  · exact vert_bad p Y Y' j l hp0 (by omega) (by omega) hnY (by omega) hl
      (by simp only [hi, hj, hi', hj'] at hdet ⊢; linarith)
  · exact diag_bad p T a Y X a' Y' X' k l hp hT ha hY hX0 ha' hY' hX0' hX hX' hna hnY hnX hM hk hl
      (by clear hM hA hX hX' hdet hna hnY hnX hX0 hX0' hY hY' ha ha' cy; omega) (by clear hM hA hX hX' hdet hna hnY hnX hX0 hX0' hY hY' ha ha' cy; omega) cy
      (by simp only [hi, hj, hi', hj'] at hdet; linarith)
  · exact vert_bad p X X' i k hp0 hX0 hX0' hnX (by omega) hk
      (by simp only [hi, hj, hi', hj'] at hdet ⊢; linarith)
  · exact absurd ⟨by omega, by omega⟩ hne
  · exact anti_bad p T a Y X a' Y' X' k l hp hT ha hY hX0 ha' hY' hX0' hX hX' hna hnY hnX hA hk hl
      (by clear hM hA hX hX' hdet hna hnY hnX hX0 hX0' hY hY' ha ha' cy; omega) (by clear hM hA hX hX' hdet hna hnY hnX hX0 hX0' hY hY' ha ha' cy; omega) cy
      (by simp only [hi, hj, hi', hj'] at hdet; linarith)
  · exact vert_bad p Y Y' j l hp0 (by omega) (by omega) hnY (by omega) hl
      (by simp only [hi, hj, hi', hj'] at hdet ⊢; linarith)
  · exact vert_bad p Y Y' j l hp0 (by omega) (by omega) hnY (by omega) hl
      (by simp only [hi, hj, hi', hj'] at hdet ⊢; linarith)
  · exact anti_bad p T a Y X a' Y' X' k l hp hT ha hY hX0 ha' hY' hX0' hX hX' hna hnY hnX hA hk hl
      (by clear hM hA hX hX' hdet hna hnY hnX hX0 hX0' hY hY' ha ha' cy; omega) (by clear hM hA hX hX' hdet hna hnY hnX hX0 hX0' hY hY' ha ha' cy; omega) cy
      (by simp only [hi, hj, hi', hj'] at hdet; linarith)
  · exact absurd ⟨by omega, by omega⟩ hne
  · exact vert_bad p X X' i k hp0 hX0 hX0' hnX (by omega) hk
      (by simp only [hi, hj, hi', hj'] at hdet ⊢; linarith)
  · exact diag_bad p T a Y X a' Y' X' k l hp hT ha hY hX0 ha' hY' hX0' hX hX' hna hnY hnX hM hk hl
      (by clear hM hA hX hX' hdet hna hnY hnX hX0 hX0' hY hY' ha ha' cy; omega) (by clear hM hA hX hX' hdet hna hnY hnX hX0 hX0' hY hY' ha ha' cy; omega) cy
      (by simp only [hi, hj, hi', hj'] at hdet; linarith)
  · exact vert_bad p Y Y' j l hp0 (by omega) (by omega) hnY (by omega) hl
      (by simp only [hi, hj, hi', hj'] at hdet ⊢; linarith)
  · exact vert_bad p X X' i k hp0 hX0 hX0' hnX (by omega) hk
      (by simp only [hi, hj, hi', hj'] at hdet ⊢; linarith)
  · exact absurd ⟨by omega, by omega⟩ hne


private theorem xval (p T : ℕ) [NeZero p] (hpT : p = 2 * T + 1) (x : ZMod p) :
    ((x + (T : ZMod p)).val = x.val + T ∧ x.val + T < p) ∨
     ((x + (T : ZMod p)).val + p = x.val + T ∧ p ≤ x.val + T) := by
  have h1 := ZMod.val_add x (T : ZMod p)
  rw [ZMod.val_natCast] at h1
  have hx := ZMod.val_lt x
  have hlt : T % p = T := Nat.mod_eq_of_lt (by omega)
  rw [hlt] at h1
  by_cases h : x.val + T < p
  · left
    rw [h1, Nat.mod_eq_of_lt h]
    exact ⟨rfl, h⟩
  · right
    have h2 : (x.val + T) % p = x.val + T - p := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    refine ⟨by omega, by omega⟩

private theorem mainrel (p T : ℕ) [Fact p.Prime] (x y : ZMod p) (hx : x ≠ 0) (hy : y ≠ 0)
    (hxy : x ≠ y) (m : ℤ)
    (h : ((y⁻¹).val : ℤ) - ((x⁻¹).val : ℤ) - (((y + (T : ZMod p)).val : ℤ) - ((x + (T : ZMod p)).val : ℤ)) = m * p) :
    y.val + (x⁻¹).val = p ∧ (y⁻¹).val + x.val = p := by
  have h1 := congrArg (Int.cast : ℤ → ZMod p) h
  push_cast at h1
  simp only [ZMod.natCast_zmod_val, ZMod.natCast_self, mul_zero] at h1
  have h2 : (x - y) * (1 + x * y) = 0 := by
    have e : (x - y) * (1 + x * y) = x * y * (y⁻¹ - x⁻¹ - (y + T - (x + T))) := by
      field_simp
      ring
    rw [e, h1, mul_zero]
  have h3 : x * y = -1 := by
    rcases mul_eq_zero.1 h2 with h | h
    · exact absurd (sub_eq_zero.1 h) hxy
    · linear_combination h
  have h4 : y = -x⁻¹ := by
    have : y = x⁻¹ * (x * y) := by field_simp
    rw [this, h3]; ring
  have hx' : x⁻¹ ≠ 0 := inv_ne_zero hx
  have h5 : y⁻¹ = -x := by rw [h4, inv_neg, inv_inv]
  have hnx : x⁻¹.val ≠ 0 := (ZMod.val_ne_zero _).2 hx'
  have hlt := ZMod.val_lt x⁻¹
  have hlt2 := ZMod.val_lt x
  have hnx2 : x.val ≠ 0 := (ZMod.val_ne_zero _).2 hx
  haveI : NeZero x⁻¹ := ⟨hx'⟩
  haveI : NeZero x := ⟨hx⟩
  constructor
  · rw [h4]
    have := ZMod.val_neg_of_ne_zero (x⁻¹)
    omega
  · rw [h5]
    have := ZMod.val_neg_of_ne_zero x
    omega

private theorem antirel (p T : ℕ) [Fact p.Prime] (x y : ZMod p) (hx : x ≠ 0) (hy : y ≠ 0)
    (hxy : x ≠ y) (m : ℤ)
    (h : (((y + (T : ZMod p)).val : ℤ) - ((x + (T : ZMod p)).val : ℤ)) + (((y⁻¹).val : ℤ) - ((x⁻¹).val : ℤ)) = m * p) :
    y.val = (x⁻¹).val ∧ (y⁻¹).val = x.val := by
  have h1 := congrArg (Int.cast : ℤ → ZMod p) h
  push_cast at h1
  simp only [ZMod.natCast_zmod_val, ZMod.natCast_self, mul_zero] at h1
  have h2 : (x - y) * (1 - x * y) = 0 := by
    have e : (x - y) * (1 - x * y) = x * y * ((y + T - (x + T)) + (y⁻¹ - x⁻¹)) := by
      field_simp
      ring
    rw [e, h1, mul_zero]
  have h3 : x * y = 1 := by
    rcases mul_eq_zero.1 h2 with h | h
    · exact absurd (sub_eq_zero.1 h) hxy
    · linear_combination -h
  have h4 : y = x⁻¹ := eq_inv_of_mul_eq_one_right h3
  have h5 : y⁻¹ = x := by rw [h4, inv_inv]
  subst h4
  exact ⟨rfl, by rw [inv_inv]⟩

private theorem cc (T a Y i j : ℕ)
    (h : ¬ (T < a ∧ T < Y ∧ i = 1 ∧ j = 0) ∧ ¬ (T < a ∧ Y ≤ T ∧ i = 1 ∧ j = 1) ∧
          ¬ (a ≤ T ∧ T < Y ∧ i = 0 ∧ j = 0) ∧ ¬ (a ≤ T ∧ Y ≤ T ∧ i = 0 ∧ j = 1)) :
    ¬ ((T : ℤ) < a ∧ (T : ℤ) < Y ∧ (i : ℤ) = 1 ∧ (j : ℤ) = 0) ∧
      ¬ ((T : ℤ) < a ∧ (Y : ℤ) ≤ T ∧ (i : ℤ) = 1 ∧ (j : ℤ) = 1) ∧
      ¬ ((a : ℤ) ≤ T ∧ (T : ℤ) < Y ∧ (i : ℤ) = 0 ∧ (j : ℤ) = 0) ∧
      ¬ ((a : ℤ) ≤ T ∧ (Y : ℤ) ≤ T ∧ (i : ℤ) = 0 ∧ (j : ℤ) = 1) := by
  omega

private theorem c2 (i : ℕ) (h : i < 2) : (0 : ℤ) ≤ i ∧ (i : ℤ) ≤ 1 := by omega

private theorem cne (i j i' j' : ℕ) (h : ¬ (i = i' ∧ j = j')) : ¬ ((i : ℤ) = i' ∧ (j : ℤ) = j') := by omega

set_option maxHeartbeats 1000000 in
private theorem key (p T : ℕ) [hp : Fact p.Prime] (hpT : p = 2 * T + 1) (hT : 1 ≤ T)
    (x y : ZMod p) (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x ≠ y) (i j i' j' k l : ℕ)
    (hi : i < 2) (hj : j < 2) (hi' : i' < 2) (hj' : j' < 2) (hk : k < 2) (hl : l < 2)
    (hne : ¬ (i = i' ∧ j = j'))
    (cx : ¬ (T < x.val ∧ T < (x⁻¹).val ∧ i = 1 ∧ j = 0) ∧ ¬ (T < x.val ∧ (x⁻¹).val ≤ T ∧ i = 1 ∧ j = 1) ∧
          ¬ (x.val ≤ T ∧ T < (x⁻¹).val ∧ i = 0 ∧ j = 0) ∧ ¬ (x.val ≤ T ∧ (x⁻¹).val ≤ T ∧ i = 0 ∧ j = 1))
    (cx' : ¬ (T < x.val ∧ T < (x⁻¹).val ∧ i' = 1 ∧ j' = 0) ∧ ¬ (T < x.val ∧ (x⁻¹).val ≤ T ∧ i' = 1 ∧ j' = 1) ∧
          ¬ (x.val ≤ T ∧ T < (x⁻¹).val ∧ i' = 0 ∧ j' = 0) ∧ ¬ (x.val ≤ T ∧ (x⁻¹).val ≤ T ∧ i' = 0 ∧ j' = 1))
    (cy : ¬ (T < y.val ∧ T < (y⁻¹).val ∧ k = 1 ∧ l = 0) ∧ ¬ (T < y.val ∧ (y⁻¹).val ≤ T ∧ k = 1 ∧ l = 1) ∧
          ¬ (y.val ≤ T ∧ T < (y⁻¹).val ∧ k = 0 ∧ l = 0) ∧ ¬ (y.val ≤ T ∧ (y⁻¹).val ≤ T ∧ k = 0 ∧ l = 1))
    (hdet : ((i' : ℤ) - i) * p * ((((y⁻¹).val : ℤ) + l * p) - (((x⁻¹).val : ℤ) + j * p)) -
      ((j' : ℤ) - j) * p * ((((y + (T : ZMod p)).val : ℤ) + k * p) - (((x + (T : ZMod p)).val : ℤ) + i * p)) = 0) :
    False := by
  have hp0 : (0 : ℤ) < p := by omega
  have hdet' : ((i' : ℤ) - i) * (((y⁻¹).val : ℤ) + l * p - ((x⁻¹).val : ℤ) - j * p) -
      ((j' : ℤ) - j) * (((y + (T : ZMod p)).val : ℤ) + k * p - ((x + (T : ZMod p)).val : ℤ) - i * p) = 0 := by
    have h' : (p : ℤ) * (((i' : ℤ) - i) * (((y⁻¹).val : ℤ) + l * p - ((x⁻¹).val : ℤ) - j * p) -
      ((j' : ℤ) - j) * (((y + (T : ZMod p)).val : ℤ) + k * p - ((x + (T : ZMod p)).val : ℤ) - i * p)) = 0 := by
      rw [← hdet]; ring
    exact (mul_eq_zero.1 h').resolve_left (by omega)
  have hxv := (ZMod.val_pos).2 hx
  have hyv := (ZMod.val_pos).2 hy
  have hxiv := (ZMod.val_pos).2 (inv_ne_zero hx)
  have hyiv := (ZMod.val_pos).2 (inv_ne_zero hy)
  have l1 := ZMod.val_lt x
  have l2 := ZMod.val_lt y
  have l3 := ZMod.val_lt (x⁻¹)
  have l4 := ZMod.val_lt (y⁻¹)
  have l5 := ZMod.val_lt (x + (T : ZMod p))
  have l6 := ZMod.val_lt (y + (T : ZMod p))
  have xv := xval p T hpT x
  have yv := xval p T hpT y
  have hna : (x.val : ℤ) ≠ (y.val : ℤ) := by
    intro h
    exact hxy (ZMod.val_injective p (by omega))
  have hnY : ((x⁻¹).val : ℤ) ≠ ((y⁻¹).val : ℤ) := by
    intro h
    have h2 : (x⁻¹).val = (y⁻¹).val := by omega
    exact hxy (inv_injective (ZMod.val_injective p h2))
  have hnX : ((x + (T : ZMod p)).val : ℤ) ≠ ((y + (T : ZMod p)).val : ℤ) := by
    intro h
    have h2 : (x + (T : ZMod p)).val = (y + (T : ZMod p)).val := by omega
    exact hxy (add_right_cancel (ZMod.val_injective p h2))
  have hM : (((y⁻¹).val : ℤ) - ((x⁻¹).val : ℤ) - (((y + (T : ZMod p)).val : ℤ) - ((x + (T : ZMod p)).val : ℤ)) = -(p : ℤ) ∨
      ((y⁻¹).val : ℤ) - ((x⁻¹).val : ℤ) - (((y + (T : ZMod p)).val : ℤ) - ((x + (T : ZMod p)).val : ℤ)) = 0 ∨
      ((y⁻¹).val : ℤ) - ((x⁻¹).val : ℤ) - (((y + (T : ZMod p)).val : ℤ) - ((x + (T : ZMod p)).val : ℤ)) = (p : ℤ)) →
      ((y.val : ℤ) + ((x⁻¹).val : ℤ) = p ∧ ((y⁻¹).val : ℤ) + (x.val : ℤ) = p) := by
    intro h
    have h2 : y.val + (x⁻¹).val = p ∧ (y⁻¹).val + x.val = p := by
      rcases h with h | h | h
      · exact mainrel p T x y hx hy hxy (-1) (by rw [h]; ring)
      · exact mainrel p T x y hx hy hxy 0 (by rw [h]; ring)
      · exact mainrel p T x y hx hy hxy 1 (by rw [h]; ring)
    omega
  have hA : ((((y + (T : ZMod p)).val : ℤ) - ((x + (T : ZMod p)).val : ℤ)) + (((y⁻¹).val : ℤ) - ((x⁻¹).val : ℤ)) = -(p : ℤ) ∨
      (((y + (T : ZMod p)).val : ℤ) - ((x + (T : ZMod p)).val : ℤ)) + (((y⁻¹).val : ℤ) - ((x⁻¹).val : ℤ)) = 0 ∨
      (((y + (T : ZMod p)).val : ℤ) - ((x + (T : ZMod p)).val : ℤ)) + (((y⁻¹).val : ℤ) - ((x⁻¹).val : ℤ)) = (p : ℤ)) →
      ((y.val : ℤ) = ((x⁻¹).val : ℤ) ∧ ((y⁻¹).val : ℤ) = (x.val : ℤ)) := by
    intro h
    have h2 : y.val = (x⁻¹).val ∧ (y⁻¹).val = x.val := by
      rcases h with h | h | h
      · exact antirel p T x y hx hy hxy (-1) (by rw [h]; ring)
      · exact antirel p T x y hx hy hxy 0 (by rw [h]; ring)
      · exact antirel p T x y hx hy hxy 1 (by rw [h]; ring)
    omega
  exact key_arith (p : ℤ) (T : ℤ) (x.val : ℤ) ((x⁻¹).val : ℤ) ((x + (T : ZMod p)).val : ℤ)
    (y.val : ℤ) ((y⁻¹).val : ℤ) ((y + (T : ZMod p)).val : ℤ) i j i' j' k l
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) hna hnY hnX hM hA (c2 i hi) (c2 j hj) (c2 i' hi') (c2 j' hj')
    (c2 k hk) (c2 l hl) (cne i j i' j' hne) (cc T _ _ i j cx) (cc T _ _ i' j' cx') (cc T _ _ k l cy) hdet'

private theorem same3 (p : ℕ) (hp : 0 < p) (i j i' j' i'' j'' : Fin 2) (X Y : ℤ)
    (h12 : ¬ (i = i' ∧ j = j')) (h13 : ¬ (i = i'' ∧ j = j'')) (h23 : ¬ (i' = i'' ∧ j' = j'')) :
    ((X + (i'.val : ℤ) * p) - (X + (i.val : ℤ) * p)) * ((Y + (j''.val : ℤ) * p) - (Y + (j.val : ℤ) * p)) -
      ((Y + (j'.val : ℤ) * p) - (Y + (j.val : ℤ) * p)) * ((X + (i''.val : ℤ) * p) - (X + (i.val : ℤ) * p)) ≠ 0 := by
  have hD : ∀ i j i' j' i'' j'' : Fin 2, ¬ (i = i' ∧ j = j') → ¬ (i = i'' ∧ j = j'') →
      ¬ (i' = i'' ∧ j' = j'') →
      ((i'.val : ℤ) - i.val) * ((j''.val : ℤ) - j.val) - ((j'.val : ℤ) - j.val) * ((i''.val : ℤ) - i.val) ≠ 0 := by
    decide
  have e : ((X + (i'.val : ℤ) * p) - (X + (i.val : ℤ) * p)) * ((Y + (j''.val : ℤ) * p) - (Y + (j.val : ℤ) * p)) -
      ((Y + (j'.val : ℤ) * p) - (Y + (j.val : ℤ) * p)) * ((X + (i''.val : ℤ) * p) - (X + (i.val : ℤ) * p)) =
      (p : ℤ) ^ 2 * (((i'.val : ℤ) - i.val) * ((j''.val : ℤ) - j.val) - ((j'.val : ℤ) - j.val) * ((i''.val : ℤ) - i.val)) := by
    ring
  rw [e]
  exact mul_ne_zero (pow_ne_zero 2 (by exact_mod_cast hp.ne')) (hD i j i' j' i'' j'' h12 h13 h23)

private theorem dist3 (p T : ℕ) [Fact p.Prime] (x y z : ZMod p) (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) (i j i2 j2 i3 j3 : ℕ) :
    ((((y + (T : ZMod p)).val : ℤ) + i2 * p) - (((x + (T : ZMod p)).val : ℤ) + i * p)) *
      ((((z⁻¹).val : ℤ) + j3 * p) - (((x⁻¹).val : ℤ) + j * p)) -
    ((((y⁻¹).val : ℤ) + j2 * p) - (((x⁻¹).val : ℤ) + j * p)) *
      ((((z + (T : ZMod p)).val : ℤ) + i3 * p) - (((x + (T : ZMod p)).val : ℤ) + i * p)) ≠ 0 := by
  intro h
  have h1 := congrArg (Int.cast : ℤ → ZMod p) h
  push_cast at h1
  simp only [ZMod.natCast_zmod_val, ZMod.natCast_self, mul_zero, add_zero] at h1
  have h2 : (y - x) * (x - z) * (y - z) / (x * y * z) = 0 := by
    rw [← h1]
    field_simp
    ring
  have h3 : (y - x) * (x - z) * (y - z) = 0 := by
    rcases div_eq_zero_iff.1 h2 with h | h
    · exact h
    · exact absurd h (mul_ne_zero (mul_ne_zero hx hy) hz)
  rcases mul_eq_zero.1 h3 with h | h
  · rcases mul_eq_zero.1 h with h | h
    · exact hxy (sub_eq_zero.1 h).symm
    · exact hxz (sub_eq_zero.1 h)
  · exact hyz (sub_eq_zero.1 h)

private theorem memR (T a Y : ℕ) (ij : Fin 2 × Fin 2)
    (h : ij ∈ (Finset.univ : Finset (Fin 2 × Fin 2)).erase
      (if T < a then (if T < Y then ((1 : Fin 2), (0 : Fin 2)) else (1, 1))
        else (if T < Y then (0, 0) else (0, 1)))) :
    ¬ (T < a ∧ T < Y ∧ ij.1.val = 1 ∧ ij.2.val = 0) ∧ ¬ (T < a ∧ Y ≤ T ∧ ij.1.val = 1 ∧ ij.2.val = 1) ∧
      ¬ (a ≤ T ∧ T < Y ∧ ij.1.val = 0 ∧ ij.2.val = 0) ∧ ¬ (a ≤ T ∧ Y ≤ T ∧ ij.1.val = 0 ∧ ij.2.val = 1) := by
  obtain ⟨i, j⟩ := ij
  have h' := (Finset.mem_erase.1 h).1
  fin_cases i <;> fin_cases j <;> by_cases h1 : T < a <;> by_cases h2 : T < Y <;>
    simp_all <;> omega

private theorem sumR (p : ℕ) [Fact p.Prime] (R : ZMod p → Finset (Fin 2 × Fin 2))
    (hR : ∀ x, (R x).card = 3) :
    (∑ x ∈ Finset.univ.filter (fun x : ZMod p => x ≠ 0), (R x).card) = 3 * (p - 1) := by
  rw [Finset.sum_congr rfl (fun x _ => hR x), Finset.sum_const, smul_eq_mul, mul_comm]
  congr 1
  rw [Finset.filter_ne' , Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ZMod.card]

private theorem main_core (p T : ℕ) [hp : Fact p.Prime] (hpT : p = 2 * T + 1) (hT : 1 ≤ T)
    (R : ZMod p → Finset (Fin 2 × Fin 2))
    (hR : ∀ x : ZMod p, x ≠ 0 → ∀ ij ∈ R x,
      ¬ (T < x.val ∧ T < (x⁻¹).val ∧ ij.1.val = 1 ∧ ij.2.val = 0) ∧
      ¬ (T < x.val ∧ (x⁻¹).val ≤ T ∧ ij.1.val = 1 ∧ ij.2.val = 1) ∧
      ¬ (x.val ≤ T ∧ T < (x⁻¹).val ∧ ij.1.val = 0 ∧ ij.2.val = 0) ∧
      ¬ (x.val ≤ T ∧ (x⁻¹).val ≤ T ∧ ij.1.val = 0 ∧ ij.2.val = 1)) :
    ∀ a ∈ (Finset.univ.filter (fun x : ZMod p => x ≠ 0)).biUnion (fun x => (R x).image
        (fun ij => (((x + (T : ZMod p)).val : ℤ) + (ij.1.val : ℤ) * (p : ℤ),
          ((x⁻¹).val : ℤ) + (ij.2.val : ℤ) * (p : ℤ)))),
    ∀ b ∈ (Finset.univ.filter (fun x : ZMod p => x ≠ 0)).biUnion (fun x => (R x).image
        (fun ij => (((x + (T : ZMod p)).val : ℤ) + (ij.1.val : ℤ) * (p : ℤ),
          ((x⁻¹).val : ℤ) + (ij.2.val : ℤ) * (p : ℤ)))),
    ∀ c ∈ (Finset.univ.filter (fun x : ZMod p => x ≠ 0)).biUnion (fun x => (R x).image
        (fun ij => (((x + (T : ZMod p)).val : ℤ) + (ij.1.val : ℤ) * (p : ℤ),
          ((x⁻¹).val : ℤ) + (ij.2.val : ℤ) * (p : ℤ)))),
    a ≠ b → a ≠ c → b ≠ c →
      (b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1) ≠ 0 := by
  intro a ha b hb c hc hab hac hbc hd
  simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image] at ha hb hc
  obtain ⟨x, hx, ⟨i, j⟩, hij, rfl⟩ := ha
  obtain ⟨y, hy, ⟨i2, j2⟩, hij2, rfl⟩ := hb
  obtain ⟨z, hz, ⟨i3, j3⟩, hij3, rfl⟩ := hc
  dsimp only at hd hij hij2 hij3
  have hp0 : 0 < p := by omega
  by_cases hxy : x = y
  · subst hxy
    have h12 : ¬ (i = i2 ∧ j = j2) := by
      rintro ⟨rfl, rfl⟩
      exact hab rfl
    by_cases hxz : x = z
    · subst hxz
      have h13 : ¬ (i = i3 ∧ j = j3) := by
        rintro ⟨rfl, rfl⟩
        exact hac rfl
      have h23 : ¬ (i2 = i3 ∧ j2 = j3) := by
        rintro ⟨rfl, rfl⟩
        exact hbc rfl
      exact same3 p hp0 i j i2 j2 i3 j3 _ _ h12 h13 h23 hd
    · refine key p T hpT hT x z hx hz hxz i.val j.val i2.val j2.val i3.val j3.val i.isLt j.isLt
        i2.isLt j2.isLt i3.isLt j3.isLt ?_ (hR x hx _ hij) (hR x hx _ hij2) (hR z hz _ hij3) ?_
      · intro h
        exact h12 ⟨Fin.ext h.1, Fin.ext h.2⟩
      · linear_combination hd
  · by_cases hxz : x = z
    · subst hxz
      have h13 : ¬ (i = i3 ∧ j = j3) := by
        rintro ⟨rfl, rfl⟩
        exact hac rfl
      refine key p T hpT hT x y hx hy hxy i.val j.val i3.val j3.val i2.val j2.val i.isLt j.isLt
        i3.isLt j3.isLt i2.isLt j2.isLt ?_ (hR x hx _ hij) (hR x hx _ hij3) (hR y hy _ hij2) ?_
      · intro h
        exact h13 ⟨Fin.ext h.1, Fin.ext h.2⟩
      · linear_combination -hd
    · by_cases hyz : y = z
      · subst hyz
        have h23 : ¬ (i2 = i3 ∧ j2 = j3) := by
          rintro ⟨rfl, rfl⟩
          exact hbc rfl
        refine key p T hpT hT y x hy hx (Ne.symm hxy) i2.val j2.val i3.val j3.val i.val j.val
          i2.isLt j2.isLt i3.isLt j3.isLt i.isLt j.isLt ?_ (hR y hy _ hij2) (hR y hy _ hij3)
          (hR x hx _ hij) ?_
        · intro h
          exact h23 ⟨Fin.ext h.1, Fin.ext h.2⟩
        · linear_combination hd
      · exact dist3 p T x y z hx hy hz hxy hxz hyz i.val j.val i2.val j2.val i3.val j3.val hd

theorem Conjectures.NoThreeInLine.FoldOptimalityAttained :
    ∀ (p : ℕ) [NeZero p] (hp : Nat.Prime p), p ≠ 2 → (let det3 : ℤ × ℤ → ℤ × ℤ → ℤ × ℤ → ℤ := fun P Q R => (Q.1 - P.1) * (R.2 - P.2) - (Q.2 - P.2) * (R.1 - P.1); let cap : ZMod p → ZMod p → ZMod p × ZMod p := fun t x => (x + t, x⁻¹); let lift : ZMod p → ZMod p → Fin 2 → Fin 2 → ℤ × ℤ := fun t x i j => (((cap t x).1.val : ℤ) + (i.val : ℤ) * (p : ℤ), ((cap t x).2.val : ℤ) + (j.val : ℤ) * (p : ℤ)); let Mask : Type := ZMod p → Finset (Fin 2 × Fin 2); let points : ZMod p → Mask → Finset (ℤ × ℤ) := fun t R => (Finset.univ.filter (fun x : ZMod p => x ≠ 0)).biUnion (fun x => (R x).image (fun ij => lift t x ij.1 ij.2)); let NoThreeCollinear : Finset (ℤ × ℤ) → Prop := fun S => ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a ≠ b → a ≠ c → b ≠ c → det3 a b c ≠ 0; ∃ t : ZMod p, ∃ R : Mask, NoThreeCollinear (points t R) ∧ (∑ x ∈ Finset.univ.filter (fun x : ZMod p => x ≠ 0), (R x).card) = 3 * (p - 1)) := by
  intro p _ hp hp2
  haveI : Fact p.Prime := ⟨hp⟩
  have hodd : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · exact absurd h hp2
    · exact h
  obtain ⟨T, hpT⟩ : ∃ T, p = 2 * T + 1 := ⟨p / 2, by omega⟩
  have hT : 1 ≤ T := by
    have := hp.two_le
    omega
  intro det3 cap lift Mask points NoThreeCollinear
  refine ⟨(T : ZMod p), fun x => (Finset.univ : Finset (Fin 2 × Fin 2)).erase
    (if T < x.val then (if T < (x⁻¹).val then ((1 : Fin 2), (0 : Fin 2)) else (1, 1))
      else (if T < (x⁻¹).val then (0, 0) else (0, 1))), ?_, ?_⟩
  · exact main_core p T hpT hT _ (fun x _ ij hij => memR T x.val (x⁻¹).val ij hij)
  · refine sumR p _ (fun x => ?_)
    rw [Finset.card_erase_of_mem (Finset.mem_univ _)]
    simp
