import Mathlib

theorem Conjectures.JoshiAbc.TowerWeights :
    ∀ (m n : ℕ) (v : Fin n → Fin m) (w : Fin n → ℝ) (d f : Fin m → ℝ), (∀ i, ((Finset.univ : Finset (Fin n)).filter (fun j => v j=i)).sum w = d i) → (∑ j, w j*f (v j)) = ∑ i, d i*f i := by
  intro m n v w d f h
  rw [← Finset.sum_fiberwise Finset.univ v (fun j => w j * f (v j))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← h i, Finset.sum_mul]
  exact Finset.sum_congr rfl fun j hj => by
    rw [(Finset.mem_filter.1 hj).2]
