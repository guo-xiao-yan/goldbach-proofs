import Mathlib

private theorem dynEnergy_aux :
    ∀ (E : Finset ℕ) (r b : ℕ → ℝ) (L : ℝ), 0 < L → (∀ n ∈ E, L ≤ b n) → ((E.filter (fun n => r n=0)).card:ℝ)*L^2 ≤ ∑ n ∈ E, (r n-b n)^2 := by
  intro E r b L hL hb
  calc ((E.filter (fun n => r n=0)).card:ℝ)*L^2
      = ∑ n ∈ E.filter (fun n => r n=0), L^2 := by simp
    _ ≤ ∑ n ∈ E.filter (fun n => r n=0), (r n-b n)^2 := by
        apply Finset.sum_le_sum
        intro n hn
        rw [Finset.mem_filter] at hn
        rw [hn.2, zero_sub, neg_sq]
        exact pow_le_pow_left₀ hL.le (hb n hn.1) 2
    _ ≤ ∑ n ∈ E, (r n-b n)^2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => sq_nonneg _)

theorem Conjectures.Goldbach.BeaumontCentralPredictionTransfer :
    let H := fun n : ℕ => ((Finset.range (n+1)).filter (fun p => p.Prime ∧ p ≤ n ∧ (n-p).Prime ∧ n ≤ 3*p ∧ 3*p ≤ 2*n)).card; let E := fun X : ℕ => (Finset.Icc X (2*X)).filter (fun n => Even n); let M := fun X : ℕ => (X:ℝ)/(Real.log (X:ℝ))^2; let R := fun n : ℕ => ((H n + H (n+2)):ℝ); (∀ ε : ℝ, 0 < ε → ∃ X₀ : ℕ, ∀ X ≥ X₀, ∃ b : ℕ → ℝ, (∀ n ∈ E X, M X ≤ b n) ∧ (∑ n ∈ E X, (R n-b n)^2) ≤ ε*(X:ℝ)*(M X)^2) → (∀ ε : ℝ, 0 < ε → ∃ X₀ : ℕ, ∀ X ≥ X₀, (((Finset.Icc X (2*X)).filter (fun n => Even n ∧ H n=0 ∧ H (n+2)=0)).card:ℝ) ≤ ε*(X:ℝ)) := by
  intro H E M R h ε hε
  obtain ⟨X₀, hX₀⟩ := h ε hε
  refine ⟨max X₀ 3, fun X hX => ?_⟩
  have hX0 : X₀ ≤ X := le_trans (le_max_left _ _) hX
  have hX3 : 3 ≤ X := le_trans (le_max_right _ _) hX
  obtain ⟨b, hb, hs⟩ := hX₀ X hX0
  have hXr : (3:ℝ) ≤ X := by exact_mod_cast hX3
  have hlog : 0 < Real.log (X:ℝ) := Real.log_pos (by linarith)
  have hM : 0 < M X := by
    show 0 < (X:ℝ) / (Real.log (X:ℝ))^2
    positivity
  have key := dynEnergy_aux (E X) R b (M X) hM hb
  have hsub : ((Finset.Icc X (2*X)).filter (fun n => Even n ∧ H n=0 ∧ H (n+2)=0)) ⊆ (E X).filter (fun n => R n = 0) := by
    intro n hn
    rw [Finset.mem_filter] at hn
    obtain ⟨h1, h2, h3, h4⟩ := hn
    rw [Finset.mem_filter]
    refine ⟨?_, ?_⟩
    · show n ∈ (Finset.Icc X (2*X)).filter (fun n => Even n)
      rw [Finset.mem_filter]; exact ⟨h1, h2⟩
    · show (H n : ℝ) + (H (n+2) : ℝ) = 0
      rw [h3, h4]; simp
  have hcard : (((Finset.Icc X (2*X)).filter (fun n => Even n ∧ H n=0 ∧ H (n+2)=0)).card:ℝ) ≤ (((E X).filter (fun n => R n = 0)).card:ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  have h2 : (((E X).filter (fun n => R n = 0)).card:ℝ) * (M X)^2 ≤ ε*(X:ℝ)*(M X)^2 := le_trans key hs
  have hM2 : 0 < (M X)^2 := by positivity
  have h3 := le_of_mul_le_mul_right h2 hM2
  exact le_trans hcard h3
