import Mathlib

theorem Conjectures.JoshiAbc.RadicalSupport :
    let rad := fun (n : ℕ) => n.primeFactors.prod id; ∀ a b : ℕ, 0<a → 0<b → Nat.Coprime a b → rad (a*b*(a+b)) = rad a * rad b * rad (a+b) := by
  intro rad a b ha hb hc
  have key : ∀ m n : ℕ, Nat.Coprime m n → rad (m*n) = rad m * rad n := by
    intro m n h
    show (m*n).primeFactors.prod id = m.primeFactors.prod id * n.primeFactors.prod id
    rw [Nat.Coprime.primeFactors_mul h, Finset.prod_union h.disjoint_primeFactors]
  have h1 : Nat.Coprime a (a+b) := by simpa using hc
  have h2 : Nat.Coprime b (a+b) := by
    have := hc.symm
    simpa using this
  rw [key _ _ (Nat.Coprime.mul_left h1 h2), key _ _ hc]
