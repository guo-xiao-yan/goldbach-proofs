import Mathlib

theorem Conjectures.Goldbach.DynIncidenceFirst :
    let E := fun X : ℕ => (Finset.Icc X (2*X)).filter (fun n => Even n); let P := fun X : ℕ => (Finset.Icc (Nat.sqrt X) (2*Nat.sqrt X)).filter Nat.Prime; let H := fun (X n : ℕ) => ((P X).filter (fun p => p ≤ n ∧ Nat.Prime (n-p))).card; ∀ X : ℕ, ∑ n ∈ E X, H X n = ∑ p ∈ P X, ((E X).filter (fun n => p≤n ∧ Nat.Prime (n-p))).card := by
  intro E P H X
  simp only [H, Finset.card_filter]
  exact Finset.sum_comm
