import Mathlib

private lemma ratio_aux (z : ℕ) (hz : 2 ≤ z) : ∀ y : ℕ, z ≤ y →
    0 < ∏ p ∈ Finset.Ioc z y, (if p.Prime then (1 - 2/(p:ℝ)) else 1) ∧
    (∏ p ∈ Finset.Ioc z y, (if p.Prime then (1 - 1/(p:ℝ)) else 1))^2 * ((z:ℝ)-1) * y ≤
      (∏ p ∈ Finset.Ioc z y, (if p.Prime then (1 - 2/(p:ℝ)) else 1)) * z * ((y:ℝ)-1) := by
  intro y hy
  induction y, hy using Nat.le_induction with
  | base => simp; nlinarith
  | succ y hzy ih =>
    obtain ⟨hpos, hle⟩ := ih
    rw [Finset.prod_Ioc_succ_top hzy, Finset.prod_Ioc_succ_top hzy]
    have hz' : (2:ℝ) ≤ z := by exact_mod_cast hz
    have hy' : (z:ℝ) ≤ y := by exact_mod_cast hzy
    set B := ∏ p ∈ Finset.Ioc z y, (if p.Prime then (1 - 2/(p:ℝ)) else 1)
    set Q := ∏ p ∈ Finset.Ioc z y, (if p.Prime then (1 - 1/(p:ℝ)) else 1)
    push_cast
    by_cases hp : (y+1).Prime
    · simp only [hp, ite_true]
      have hy2 : (2:ℝ) ≤ y := by linarith
      have hy0 : (0:ℝ) < y := by linarith
      have hy1 : (0:ℝ) < y + 1 := by linarith
      have e1 : (1 - 2/((y:ℝ)+1)) = (y-1)/(y+1) := by field_simp; ring
      have e2 : (1 - 1/((y:ℝ)+1)) = y/(y+1) := by field_simp; ring
      rw [e1, e2]
      refine ⟨mul_pos hpos (div_pos (by linarith) hy1), ?_⟩
      have : (Q * (y / (y+1)))^2 * ((z:ℝ)-1) * (y+1) = (Q^2 * ((z:ℝ)-1) * y) * (y / (y+1)) := by
        field_simp
      rw [this]
      have : B * ((y-1)/(y+1)) * z * ((y:ℝ)+1-1) = (B * z * ((y:ℝ)-1)) * (y / (y+1)) := by
        field_simp; ring
      rw [this]
      exact mul_le_mul_of_nonneg_right hle (by positivity)
    · simp only [hp, ite_false, mul_one]
      refine ⟨hpos, ?_⟩
      have hy0 : (0:ℝ) < y := by linarith
      have h1 : Q^2 * ((z:ℝ)-1) * y * (y+1) ≤ B * z * ((y:ℝ)-1) * (y+1) :=
        mul_le_mul_of_nonneg_right hle (by linarith)
      have hBz : 0 ≤ B * z := by positivity
      have h2 : B * z * ((y:ℝ)-1) * (y+1) ≤ B * z * y * y := by
        have : ((y:ℝ)-1)*(y+1) ≤ y*y := by nlinarith
        calc B * z * ((y:ℝ)-1) * (y+1) = B * z * (((y:ℝ)-1)*(y+1)) := by ring
          _ ≤ B * z * (y*y) := mul_le_mul_of_nonneg_left this hBz
          _ = _ := by ring
      have h3 : (Q^2 * ((z:ℝ)-1) * (y+1)) * y ≤ (B * z * y) * y := by nlinarith
      have := le_of_mul_le_mul_right h3 hy0
      linarith

private lemma split_prod (z y : ℕ) (hzy : z ≤ y) (hz : 2 ≤ z) (g : ℕ → ℝ) (R : ℕ → Prop) [DecidablePred R] :
    ∏ p ∈ (Finset.Icc 2 y).filter R, g p =
      (∏ p ∈ (Finset.Icc 2 z).filter R, g p) * ∏ p ∈ (Finset.Ioc z y).filter R, g p := by
  have hU : Finset.Icc 2 y = Finset.Icc 2 z ∪ Finset.Ioc z y := by
    ext a
    simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]
    omega
  rw [hU, Finset.filter_union, Finset.prod_union]
  refine Finset.disjoint_filter_filter ?_
  rw [Finset.disjoint_left]
  intro a ha hb
  simp only [Finset.mem_Icc, Finset.mem_Ioc] at ha hb
  omega

theorem Conjectures.Goldbach.FareySieveCutoffRatio :
    let I := fun n : ℕ => Finset.Icc ((n+2)/3) ((2*n)/3); let P := fun z : ℕ => (Finset.Icc 2 z).filter Nat.Prime; let M := fun z : ℕ => ∏ p ∈ P z, (1-(p:ℝ)⁻¹); let V := fun n z : ℕ => ((I n).card:ℝ)*(n.totient:ℝ)/n * ∏ p ∈ (P z).filter (fun p => ¬ p ∣ n), (1-2/(p:ℝ)); ∀ n z y : ℕ, 12 ≤ n → Even n → 2 ≤ z → z ≤ y → V n z ≤ 2*(M z/M y)^2 * V n y := by
  intro I P M V n z y _ _ hz hzy
  have hz' : (2:ℝ) ≤ z := by exact_mod_cast hz
  obtain ⟨hB, hle⟩ := ratio_aux z hz y hzy
  have hy0 : (0:ℝ) < y := by
    have : (z:ℝ) ≤ y := by exact_mod_cast hzy
    linarith
  simp only [← Finset.prod_filter] at hB hle
  have hQ : ∀ p ∈ (Finset.Ioc z y).filter Nat.Prime, 0 < (1 - 1/(p:ℝ)) := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hp
    have : (2:ℝ) ≤ p := by exact_mod_cast hp.2.two_le
    rw [sub_pos, div_lt_one (by linarith)]; linarith
  have hQpos : 0 < ∏ p ∈ (Finset.Ioc z y).filter Nat.Prime, (1 - 1/(p:ℝ)) :=
    Finset.prod_pos hQ
  have hMz : 0 < ∏ p ∈ (Finset.Icc 2 z).filter Nat.Prime, (1 - (p:ℝ)⁻¹) := by
    refine Finset.prod_pos ?_
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_Icc] at hp
    have : (2:ℝ) ≤ p := by exact_mod_cast hp.2.two_le
    rw [sub_pos]
    exact inv_lt_one_of_one_lt₀ (by linarith)
  have hBz : 0 ≤ ∏ p ∈ (Finset.Icc 2 z).filter (fun p => Nat.Prime p ∧ ¬ p ∣ n), (1 - 2/(p:ℝ)) := by
    refine Finset.prod_nonneg ?_
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_Icc] at hp
    have : (2:ℝ) ≤ p := by exact_mod_cast hp.2.1.two_le
    rw [sub_nonneg, div_le_one (by linarith)]; linarith
  have hBact : 0 ≤ ∏ p ∈ (Finset.Ioc z y).filter (fun p => Nat.Prime p ∧ ¬ p ∣ n), (1 - 2/(p:ℝ)) := by
    refine Finset.prod_nonneg ?_
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hp
    have : (2:ℝ) ≤ p := by exact_mod_cast hp.2.1.two_le
    rw [sub_nonneg, div_le_one (by linarith)]; linarith
  have hcmp : ∏ p ∈ (Finset.Ioc z y).filter Nat.Prime, (1 - 2/(p:ℝ)) ≤
      ∏ p ∈ (Finset.Ioc z y).filter (fun p => Nat.Prime p ∧ ¬ p ∣ n), (1 - 2/(p:ℝ)) := by
    rw [Finset.prod_filter, Finset.prod_filter]
    refine Finset.prod_le_prod₀ ?_ ?_
    · intro p hp
      simp only [Finset.mem_Ioc] at hp
      split_ifs with h
      · have : (2:ℝ) ≤ p := by exact_mod_cast h.two_le
        rw [sub_nonneg, div_le_one (by linarith)]; linarith
      · exact zero_le_one
    · intro p hp
      simp only [Finset.mem_Ioc] at hp
      have h3 : (3:ℝ) ≤ p := by exact_mod_cast (by omega : 3 ≤ p)
      have : 0 ≤ 2/(p:ℝ) := by positivity
      by_cases h1 : Nat.Prime p <;> by_cases h2 : p ∣ n <;> simp [h1, h2] <;> linarith
  have hMy : ∏ p ∈ (Finset.Icc 2 y).filter Nat.Prime, (1 - (p:ℝ)⁻¹) =
      (∏ p ∈ (Finset.Icc 2 z).filter Nat.Prime, (1 - (p:ℝ)⁻¹)) *
        ∏ p ∈ (Finset.Ioc z y).filter Nat.Prime, (1 - 1/(p:ℝ)) := by
    rw [split_prod z y hzy hz (fun p => 1 - (p:ℝ)⁻¹) Nat.Prime]
    simp only [one_div]
  have hVy : ∏ p ∈ ((Finset.Icc 2 y).filter Nat.Prime).filter (fun p => ¬ p ∣ n), (1 - 2/(p:ℝ)) =
      (∏ p ∈ (Finset.Icc 2 z).filter (fun p => Nat.Prime p ∧ ¬ p ∣ n), (1 - 2/(p:ℝ))) *
        ∏ p ∈ (Finset.Ioc z y).filter (fun p => Nat.Prime p ∧ ¬ p ∣ n), (1 - 2/(p:ℝ)) := by
    rw [Finset.filter_filter]
    exact split_prod z y hzy hz (fun p => 1 - 2/(p:ℝ)) (fun p => Nat.Prime p ∧ ¬ p ∣ n)
  have hVz : ∏ p ∈ ((Finset.Icc 2 z).filter Nat.Prime).filter (fun p => ¬ p ∣ n), (1 - 2/(p:ℝ)) =
      ∏ p ∈ (Finset.Icc 2 z).filter (fun p => Nat.Prime p ∧ ¬ p ∣ n), (1 - 2/(p:ℝ)) := by
    rw [Finset.filter_filter]
  simp only [V, M, P]
  rw [hMy, hVy, hVz]
  generalize ∏ p ∈ (Finset.Ioc z y).filter Nat.Prime, (1 - 1/(p:ℝ)) = Q at *
  generalize ∏ p ∈ (Finset.Ioc z y).filter Nat.Prime, (1 - 2/(p:ℝ)) = B at *
  generalize ∏ p ∈ (Finset.Ioc z y).filter (fun p => Nat.Prime p ∧ ¬ p ∣ n), (1 - 2/(p:ℝ)) = A at *
  generalize ∏ p ∈ (Finset.Icc 2 z).filter (fun p => Nat.Prime p ∧ ¬ p ∣ n), (1 - 2/(p:ℝ)) = Bz at *
  generalize ∏ p ∈ (Finset.Icc 2 z).filter Nat.Prime, (1 - (p:ℝ)⁻¹) = Mz at *
  have hcc : 0 ≤ (((I n).card:ℝ) * (n.totient:ℝ) / n) := by positivity
  generalize (((I n).card:ℝ) * (n.totient:ℝ) / n) = cc at hcc ⊢
  have hz1 : (0:ℝ) < (z:ℝ) - 1 := by linarith
  have hQB : Q^2 ≤ 2 * B := by
    have h1 : Q^2 * ((z:ℝ)-1) * y ≤ B * z * ((y:ℝ)-1) := hle
    have h2 : Q^2 * ((z:ℝ)-1) * y ≤ B * z * y := by nlinarith
    have h3 : Q^2 * ((z:ℝ)-1) ≤ B * z := le_of_mul_le_mul_right (by linarith) hy0
    nlinarith
  have hkey : 1 ≤ 2 * (Mz / (Mz * Q))^2 * A := by
    have : Mz / (Mz * Q) = 1 / Q := by field_simp
    rw [this, div_pow, one_pow, mul_div_assoc', div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    nlinarith
  have h := mul_le_mul_of_nonneg_left hkey (mul_nonneg hcc hBz)
  calc cc * Bz = cc * Bz * 1 := by ring
    _ ≤ cc * Bz * (2 * (Mz / (Mz * Q))^2 * A) := h
    _ = _ := by ring
