import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Nat.ModEq

private theorem cam_key (n q k l : ℕ) (hq : 0 < q) :
    (k + l) % q = n % q ↔ l % q = (n + q - k % q) % q := by
  have hr : k % q < q := Nat.mod_lt _ hq
  have h1 : k + (n + q - k % q) ≡ n [MOD q] :=
    calc k + (n + q - k % q) ≡ k % q + (n + q - k % q) [MOD q] :=
          Nat.ModEq.add_right _ (Nat.mod_modEq k q).symm
      _ = n + q := by omega
      _ ≡ n [MOD q] := by
          show (n + q) % q = n % q
          exact Nat.add_mod_right n q
  constructor
  · intro h
    have h2 : k + l ≡ k + (n + q - k % q) [MOD q] := Nat.ModEq.trans h h1.symm
    exact Nat.ModEq.add_left_cancel' k h2
  · intro h
    exact Nat.ModEq.trans (Nat.ModEq.add_left k h) h1

private theorem cam_main (w : ℕ → ℝ) (n q : ℕ) (hq : 0 < q) :
    ∑ s ∈ (Finset.range (2*n+1)).filter (fun s => s % q = n % q),
        ∑ k ∈ (Finset.range (n+1)).filter (fun k => k ≤ s ∧ s - k ≤ n), w k * w (s - k) =
      ∑ r ∈ Finset.range q,
        (∑ k ∈ (Finset.range (n+1)).filter (fun k => k % q = r), w k) *
        (∑ k ∈ (Finset.range (n+1)).filter (fun k => k % q = (n + q - r) % q), w k) := by
  set P : Finset (ℕ × ℕ) := ((Finset.range (n+1)) ×ˢ (Finset.range (n+1))).filter
    (fun p => (p.1 + p.2) % q = n % q) with hP
  have hL : ∑ p ∈ P, w p.1 * w p.2 =
      ∑ s ∈ (Finset.range (2*n+1)).filter (fun s => s % q = n % q),
        ∑ k ∈ (Finset.range (n+1)).filter (fun k => k ≤ s ∧ s - k ≤ n), w k * w (s - k) := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := P)
      (t := (Finset.range (2*n+1)).filter (fun s => s % q = n % q)) (g := fun p => p.1 + p.2)]
    · refine Finset.sum_congr rfl ?_
      intro s hs
      simp only [Finset.mem_filter, Finset.mem_range] at hs
      refine Finset.sum_nbij' (fun p => p.1) (fun k => (k, s - k)) ?_ ?_ ?_ ?_ ?_
      · intro p hp
        simp only [hP, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
          Finset.mem_coe] at hp ⊢
        omega
      · intro k hk
        simp only [hP, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
          Finset.mem_coe] at hk ⊢
        have : k + (s - k) = s := by omega
        exact ⟨⟨⟨by omega, by omega⟩, by rw [this]; exact hs.2⟩, this⟩
      · intro p hp
        simp only [hP, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
          Finset.mem_coe] at hp
        ext <;> simp only <;> omega
      · intro k hk
        rfl
      · intro p hp
        simp only [hP, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
          Finset.mem_coe] at hp
        have : p.2 = s - p.1 := by omega
        rw [this]
    · intro p hp
      simp only [hP, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp ⊢
      exact ⟨by omega, hp.2⟩
  have hR : ∑ p ∈ P, w p.1 * w p.2 =
      ∑ r ∈ Finset.range q,
        (∑ k ∈ (Finset.range (n+1)).filter (fun k => k % q = r), w k) *
        (∑ k ∈ (Finset.range (n+1)).filter (fun k => k % q = (n + q - r) % q), w k) := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := P) (t := Finset.range q)
      (g := fun p => p.1 % q)]
    · refine Finset.sum_congr rfl ?_
      intro r hr
      rw [Finset.sum_mul_sum, ← Finset.sum_product']
      refine Finset.sum_congr ?_ (fun _ _ => rfl)
      ext p
      simp only [hP, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
      rw [Finset.mem_range] at hr
      constructor
      · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
        refine ⟨⟨h1, h4⟩, h2, ?_⟩
        rw [cam_key n q p.1 p.2 hq] at h3
        rw [h3, h4]
      · rintro ⟨⟨h1, h4⟩, h2, h3⟩
        refine ⟨⟨⟨h1, h2⟩, ?_⟩, h4⟩
        rw [cam_key n q p.1 p.2 hq, h4]
        exact h3
    · intro p hp
      simp only [Finset.mem_range]
      exact Nat.mod_lt _ hq
  rw [← hL, hR]

theorem PEqualNP.Outside.L_goldbach_coset_alias_mass :
    let F := fun n q r : ℕ => (Finset.range (n+1)).filter (fun k => k % q=r); let w := fun k : ℕ => if k.Prime then Real.log (k:ℝ) else 0; let A := fun n q r : ℕ => ∑ k ∈ F n q r, w k; let j := fun n q r : ℕ => (n+q-r) % q; let B := fun n s : ℕ => ∑ k ∈ (Finset.range (n+1)).filter (fun k => k ≤ s ∧ s-k ≤ n), w k*w (s-k); let Z := fun n q : ℕ => ∑ s ∈ (Finset.range (2*n+1)).filter (fun s => s % q=n % q), B n s; ∀ n q : ℕ, 0<q → Z n q = ∑ r ∈ Finset.range q, A n q r*A n q (j n q r) := by
  intro F w A j B Z n q hq
  exact cam_main w n q hq
