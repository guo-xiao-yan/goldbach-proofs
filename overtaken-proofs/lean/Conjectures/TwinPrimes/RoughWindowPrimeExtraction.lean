import Mathlib

private theorem rwpe_key (X p : ℕ) (hX : 4096 ≤ X) (hp : p ≤ 2 * X)
    (hz : Nat.sqrt X / 2 ≤ (p + 2).minFac) :
    (p + 2).Prime ∨
    ((Nat.sqrt (p + 2)).Prime ∧ p + 2 = (Nat.sqrt (p + 2)) ^ 2) ∨
    ∃ r s : ℕ, r.Prime ∧ s.Prime ∧ r < s ∧ Nat.sqrt X / 2 ≤ r ∧
      r ≤ Nat.sqrt (2 * X + 2) ∧ p + 2 = r * s := by
  have hs : 64 ≤ Nat.sqrt X := Nat.le_sqrt.mpr (by omega)
  have hlt := Nat.lt_succ_sqrt X
  set s := Nat.sqrt X with hsdef
  set z := s / 2 with hzdef
  have hz32 : 32 ≤ z := by omega
  have hs2 : s + 1 ≤ 2 * z + 2 := by omega
  have hX2 : X < (2 * z + 2) * (2 * z + 2) := by
    calc X < Nat.succ s * Nat.succ s := hlt
      _ ≤ (2 * z + 2) * (2 * z + 2) := Nat.mul_le_mul hs2 hs2
  have hn : p + 2 < z ^ 3 := by nlinarith
  set n := p + 2 with hndef
  set r := n.minFac with hrdef
  have hn1 : n ≠ 1 := by omega
  have hrp : r.Prime := Nat.minFac_prime hn1
  have hrn : r ∣ n := Nat.minFac_dvd n
  obtain ⟨m, hm⟩ := hrn
  have hr0 : 0 < r := hrp.pos
  by_cases hm1 : m = 1
  · left
    have : n = r := by rw [hm, hm1]; ring
    rw [this]; exact hrp
  · have hm0 : m ≠ 0 := by
      rintro rfl; omega
    have hm2 : 2 ≤ m := by omega
    have hmn : m ∣ n := ⟨r, by rw [hm]; ring⟩
    have hrm : r ≤ m := Nat.minFac_le_of_dvd hm2 hmn
    have hmp : m.Prime := by
      by_contra hnp
      have h1 := Nat.minFac_sq_le_self (by omega : 0 < m) hnp
      have h2 : m.minFac ∣ n := (Nat.minFac_dvd m).trans hmn
      have h3 : r ≤ m.minFac := Nat.minFac_le_of_dvd (Nat.minFac_prime (by omega)).two_le h2
      have h4 : z ≤ m.minFac := le_trans hz h3
      have h5 : z * z ≤ m := by nlinarith
      have : z * (z * z) ≤ r * m := Nat.mul_le_mul (le_trans hz (le_refl _)) h5
      nlinarith
    rcases Nat.eq_or_lt_of_le hrm with h | h
    · right; left
      have hn2 : n = r ^ 2 := by rw [hm, ← h]; ring
      rw [hn2, Nat.sqrt_eq']
      exact ⟨hrp, rfl⟩
    · right; right
      refine ⟨r, m, hrp, hmp, h, hz, ?_, hm⟩
      apply Nat.le_sqrt.mpr
      have : r * r ≤ r * m := Nat.mul_le_mul_left r hrm
      omega

theorem Conjectures.TwinPrimes.RoughWindowPrimeExtraction :
    let w := fun (X : ℕ) => (Finset.range (2*X+1)).filter (fun n => X < n ∧ 50*n < 51*X); let z := fun (X : ℕ) => Nat.sqrt X / 2; let R := fun (X : ℕ) => ((w X).filter (fun p => p.Prime ∧ z X ≤ (p+2).minFac)); let T := fun (X : ℕ) => ((w X).filter (fun p => p.Prime ∧ (p+2).Prime)); let Q := fun (X : ℕ) => ((w X).filter (fun p => p.Prime ∧ (Nat.sqrt (p+2)).Prime ∧ p+2=(Nat.sqrt (p+2))^2)); let S := fun (X : ℕ) => @Finset.filter ℕ (fun p => p.Prime ∧ ∃ r s : ℕ, r.Prime ∧ s.Prime ∧ r < s ∧ Nat.sqrt X/2 ≤ r ∧ r ≤ Nat.sqrt (2*X+2) ∧ p+2=r*s) (fun _ => Classical.propDecidable _) (w X); let L := fun (p : ℕ) => Real.log p * Real.log (p+2); ∀ (X : ℕ) (M E F : ℝ), 4096 ≤ X → M ≤ (R X).sum L → (Q X).sum L ≤ E → (S X).sum L ≤ F → M-E-F ≤ (T X).sum L := by
  intro w z R T Q S L X M E F hX hM hQ hS
  have hL : ∀ p : ℕ, 0 ≤ L p := by
    intro p
    show 0 ≤ Real.log (p:ℝ) * Real.log ((p:ℝ)+2)
    rcases Nat.eq_zero_or_pos p with h | h
    · subst h; simp
    · apply mul_nonneg
      · exact Real.log_nonneg (by exact_mod_cast h)
      · have h1 : (1:ℝ) ≤ p := by exact_mod_cast h
        exact Real.log_nonneg (by linarith)
  have hsub : R X ⊆ T X ∪ (Q X ∪ S X) := by
    intro p hp
    simp only [R, T, Q, S, w, Finset.mem_filter, Finset.mem_range, Finset.mem_union] at hp ⊢
    obtain ⟨⟨hr, hw⟩, hpp, hz⟩ := hp
    rcases rwpe_key X p hX (by omega) hz with h | h | h
    · left; exact ⟨⟨hr, hw⟩, hpp, h⟩
    · right; left; exact ⟨⟨hr, hw⟩, hpp, h⟩
    · right; right; exact ⟨⟨hr, hw⟩, hpp, h⟩
  have h1 : (R X).sum L ≤ (T X ∪ (Q X ∪ S X)).sum L :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => hL i)
  have h2 : (T X ∪ (Q X ∪ S X)).sum L ≤ (T X).sum L + (Q X ∪ S X).sum L := by
    have := Finset.sum_union_inter (s₁ := T X) (s₂ := Q X ∪ S X) (f := L)
    have h0 : 0 ≤ (T X ∩ (Q X ∪ S X)).sum L := Finset.sum_nonneg (fun i _ => hL i)
    linarith
  have h3 : (Q X ∪ S X).sum L ≤ (Q X).sum L + (S X).sum L := by
    have := Finset.sum_union_inter (s₁ := Q X) (s₂ := S X) (f := L)
    have h0 : 0 ≤ (Q X ∩ S X).sum L := Finset.sum_nonneg (fun i _ => hL i)
    linarith
  linarith
