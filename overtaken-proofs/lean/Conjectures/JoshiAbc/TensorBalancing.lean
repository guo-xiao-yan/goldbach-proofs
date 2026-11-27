import Mathlib

theorem Conjectures.JoshiAbc.TensorBalancing :
    ∀ (p : ℕ) [Fact p.Prime] (E F : Type) [Field E] [Field F] [Algebra (Padic p) E] [Algebra (Padic p) F] (x : E) (y : F), TensorProduct.tmul (Padic p) ((p:Padic p) • x) y = TensorProduct.tmul (Padic p) x ((p:Padic p) • y) := by
  intro p _ E F _ _ _ _ x y
  exact TensorProduct.smul_tmul _ _ _
