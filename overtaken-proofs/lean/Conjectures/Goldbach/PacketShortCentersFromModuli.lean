import Mathlib

private lemma psc_card (q : ℕ) (hq : 1 ≤ q) (P : ℕ → Prop) [DecidablePred P] :
    (((Finset.range (q+1)).filter (fun a => Nat.Coprime a q ∧ P a)).card : ℝ) ≤ 2 * (Nat.totient q : ℝ) := by
  have h1 : ((Finset.range (q+1)).filter (fun a => Nat.Coprime a q ∧ P a)).card
      ≤ ((Finset.range (q+1)).filter (fun a => Nat.Coprime a q)).card := by
    apply Finset.card_le_card
    intro a ha
    simp only [Finset.mem_filter] at ha ⊢
    exact ⟨ha.1, ha.2.1⟩
  have h2 : ((Finset.range (q+1)).filter (fun a => Nat.Coprime a q)).card ≤ Nat.totient q + 1 := by
    rw [Finset.range_add_one, Finset.filter_insert]
    have : ((Finset.range q).filter (fun a => Nat.Coprime a q)).card = Nat.totient q := by
      rw [Nat.totient_eq_card_coprime]
      congr 1
      apply Finset.filter_congr
      intro a _
      exact Nat.coprime_comm
    split_ifs
    · exact (Finset.card_insert_le _ _).trans (by omega)
    · omega
  have h3 : 1 ≤ Nat.totient q := Nat.totient_pos.mpr (by omega)
  have : ((Finset.range (q+1)).filter (fun a => Nat.Coprime a q ∧ P a)).card ≤ 2 * Nat.totient q := by
    omega
  exact_mod_cast this

private lemma psc_split (S : Finset ℕ) (o sm : ℕ → Prop) [DecidablePred o] [DecidablePred sm]
    (g : ℕ → ℝ) (hg : ∀ q, 0 ≤ g q) :
    ∑ q ∈ S.filter o, g q ≤ ∑ q ∈ S.filter sm, g q + ∑ q ∈ S.filter (fun q => o q ∧ ¬ sm q), g q := by
  rw [← Finset.sum_filter_add_sum_filter_not (S.filter o) sm, Finset.filter_filter, Finset.filter_filter]
  apply add_le_add
  · apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro q hq
      simp only [Finset.mem_filter] at hq ⊢
      exact ⟨hq.1, hq.2.2⟩
    · intro q _ _; exact hg q
  · exact le_refl _

theorem Conjectures.Goldbach.PacketShortCentersFromModuli :
    (let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let smooth := fun n q : ℕ => ∀ p ∈ q.primeFactors, p ≤ (1+Nat.log 2 (Q n))^8; ∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ n ≥ N, (∑ q ∈ (Finset.Icc 1 ((Q n)^2)).filter (fun q => smooth n q), min (1:ℝ) ((q:ℝ)/(Q n:ℝ))/(Nat.totient q:ℝ)) ≤ ε) → (let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let o := fun n q : ℕ => q % 2 = 1 ∧ ((Finset.Icc 1 ((Nat.log 2 (Q n)+1)^2)).filter (fun j => q ∣ 2^j-1)).Nonempty; let smooth := fun n q : ℕ => ∀ p ∈ q.primeFactors, p ≤ (1+Nat.log 2 (Q n))^8; ∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ n ≥ N, (∑ q ∈ (Finset.Icc 1 ((Q n)^2)).filter (fun q => o n q ∧ ¬smooth n q), min (1:ℝ) ((q:ℝ)/(Q n:ℝ))/(Nat.totient q:ℝ)) ≤ ε) → (let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let L := fun n : ℕ => max 1 (Nat.log 2 n / 2); let K := fun (n : ℕ) (t : ℝ) => (∑ j ∈ Finset.range (L n), Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L n:ℝ); let o := fun n q : ℕ => q % 2 = 1 ∧ ((Finset.Icc 1 ((Nat.log 2 (Q n)+1)^2)).filter (fun j => q ∣ 2^j-1)).Nonempty; ∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ n ≥ N, (∑ q ∈ (Finset.Icc 1 ((Q n)^2)).filter (fun q => o n q), min (1:ℝ) ((q:ℝ)/(Q n:ℝ)) * (((Finset.range (q+1)).filter (fun a => Nat.Coprime a q ∧ (1:ℝ)/3 < K n ((a:ℝ)/(q:ℝ)))).card:ℝ) / (Nat.totient q:ℝ)^2) ≤ ε) := by
  intro h1 h2
  dsimp only at h1 h2 ⊢
  intro ε hε
  obtain ⟨N1, hN1⟩ := h1 (ε/4) (by positivity)
  obtain ⟨N2, hN2⟩ := h2 (ε/4) (by positivity)
  refine ⟨max N1 N2, fun n hn => ?_⟩
  have a := hN1 n (le_trans (le_max_left _ _) hn)
  have b := hN2 n (le_trans (le_max_right _ _) hn)
  have key := psc_split (Finset.Icc 1 ((Nat.log 2 (n+2) ^ 2) ^ 2))
    (fun q => q % 2 = 1 ∧ ((Finset.Icc 1 ((Nat.log 2 (Nat.log 2 (n+2) ^ 2) + 1) ^ 2)).filter (fun j => q ∣ 2 ^ j - 1)).Nonempty)
    (fun q => ∀ p ∈ q.primeFactors, p ≤ (1 + Nat.log 2 (Nat.log 2 (n + 2) ^ 2)) ^ 8)
    (fun q => min (1:ℝ) ((q:ℝ) / ((Nat.log 2 (n + 2) ^ 2 : ℕ):ℝ)) / (Nat.totient q : ℝ))
    (fun q => by positivity)
  have hterm : ∀ q ∈ (Finset.Icc 1 ((Nat.log 2 (n+2) ^ 2) ^ 2)).filter
      (fun q => q % 2 = 1 ∧ ((Finset.Icc 1 ((Nat.log 2 (Nat.log 2 (n+2) ^ 2) + 1) ^ 2)).filter (fun j => q ∣ 2 ^ j - 1)).Nonempty),
      min (1:ℝ) ((q:ℝ) / ((Nat.log 2 (n + 2) ^ 2 : ℕ):ℝ)) *
          (((Finset.range (q+1)).filter (fun a => Nat.Coprime a q ∧ 1 / 3 <
                    (∑ j ∈ Finset.range (max 1 (Nat.log 2 n / 2)), Real.cos (2 * Real.pi * 2 ^ (j + 1) * ((a:ℝ) / (q:ℝ)))) /
                      ((max 1 (Nat.log 2 n / 2) : ℕ) : ℝ))).card : ℝ) / (Nat.totient q : ℝ) ^ 2
        ≤ 2 * (min (1:ℝ) ((q:ℝ) / ((Nat.log 2 (n + 2) ^ 2 : ℕ):ℝ)) / (Nat.totient q : ℝ)) := by
    intro q hq
    have hq1 : 1 ≤ q := (Finset.mem_Icc.mp (Finset.mem_filter.mp hq).1).1
    have hc := psc_card q hq1 (fun a => 1 / 3 <
                    (∑ j ∈ Finset.range (max 1 (Nat.log 2 n / 2)), Real.cos (2 * Real.pi * 2 ^ (j + 1) * ((a:ℝ) / (q:ℝ)))) /
                      ((max 1 (Nat.log 2 n / 2) : ℕ) : ℝ))
    have hφ : (0:ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.mpr (by omega)
    have hm : 0 ≤ min (1:ℝ) ((q:ℝ) / ((Nat.log 2 (n + 2) ^ 2 : ℕ):ℝ)) := by positivity
    rw [div_le_iff₀ (by positivity)]
    calc _ ≤ min (1:ℝ) ((q:ℝ) / ((Nat.log 2 (n + 2) ^ 2 : ℕ):ℝ)) * (2 * (Nat.totient q : ℝ)) :=
          mul_le_mul_of_nonneg_left hc hm
      _ = _ := by field_simp
  calc _ ≤ _ := Finset.sum_le_sum hterm
    _ = 2 * ∑ q ∈ (Finset.Icc 1 ((Nat.log 2 (n+2) ^ 2) ^ 2)).filter
      (fun q => q % 2 = 1 ∧ ((Finset.Icc 1 ((Nat.log 2 (Nat.log 2 (n+2) ^ 2) + 1) ^ 2)).filter (fun j => q ∣ 2 ^ j - 1)).Nonempty),
      (min (1:ℝ) ((q:ℝ) / ((Nat.log 2 (n + 2) ^ 2 : ℕ):ℝ)) / (Nat.totient q : ℝ)) := by
      rw [Finset.mul_sum]
    _ ≤ ε := by linarith
