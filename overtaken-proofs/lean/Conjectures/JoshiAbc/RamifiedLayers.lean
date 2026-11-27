import Mathlib

theorem Conjectures.JoshiAbc.RamifiedLayers :
    ∀ (p f n m : ℕ), p.Prime → n ≤ m → (p^f)^n * p^(f*(m-n)) = (p^f)^m := by
  intro p f n m _ h
  have h2 : f * n + f * (m - n) = f * m := by
    rw [← mul_add, Nat.add_sub_cancel' h]
  rw [← pow_mul, ← pow_mul, ← pow_add, h2]
