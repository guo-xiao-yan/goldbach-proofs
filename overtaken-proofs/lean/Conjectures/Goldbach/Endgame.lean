import Mathlib


theorem Conjectures.Goldbach.Endgame :
    let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let low := fun (n k : ℕ) => if k^3≤n then w k else 0; let high := fun (n k : ℕ) => w k-low n k; let f := fun (n : ℕ) (t : ℝ) => (S n w t)^2*E (-(n:ℝ)*t); let I := fun (n:ℕ) (a b:ℕ→ℝ) => intervalIntegral (fun t => (arcs n)ᶜ.indicator (fun u => S n a u*S n b u*E (-(n:ℝ)*u)) t) (0:ℝ) 1 MeasureTheory.volume; let minor := fun n : ℕ => intervalIntegral (fun t => (arcs n)ᶜ.indicator (fun t => (S n w t)^2*E (-(n:ℝ)*t)) t) (0:ℝ) 1 MeasureTheory.volume; let major := fun n : ℕ => intervalIntegral (fun t => (arcs n).indicator (f n) t) (0:ℝ) 1 MeasureTheory.volume; (((∃ (c : ℝ) (N : ℕ), 0<c ∧ ∀ n : ℕ, N≤n → Even n → c*(n:ℝ) ≤ (major n).re) → (∀ e : ℝ, 0<e → ∃ N : ℕ, ∀ n : ℕ, N≤n → Even n → -(e*(n:ℝ)) ≤ (minor n).re) → ∃ N : ℕ, ∀ n : ℕ, N≤n → Even n → ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p+q=n)) → ((∃ (c : ℝ) (N : ℕ), 0<c ∧ ∀ n : ℕ, N≤n → Even n → c*(n:ℝ) ≤ (major n).re)) → (∀ n:ℕ, I n w w=I n (low n) (low n)+2*I n (low n) (high n)+I n (high n) (high n)) → (∀ e:ℝ, 0<e → ∃ N:ℕ, ∀ n:ℕ, N≤n → ‖I n (low n) (low n)‖≤e*(n:ℝ)) → (∀ e:ℝ, 0<e → ∃ N:ℕ, ∀ n:ℕ, N≤n → ‖I n (low n) (high n)‖≤e*(n:ℝ)) → (∀ e:ℝ, 0<e → ∃ N:ℕ, ∀ n:ℕ, N≤n → Even n → -(e*(n:ℝ))≤(I n (high n) (high n)).re) → ∃ N:ℕ, ∀ n:ℕ, N≤n → Even n → ∃ p q:ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p+q=n := by
  intro w E S Q arcs low high f I minor major H hmaj hsplit h1 h2 h3
  refine H hmaj ?_
  intro e he
  obtain ⟨N1, hN1⟩ := h1 (e / 4) (by positivity)
  obtain ⟨N2, hN2⟩ := h2 (e / 4) (by positivity)
  obtain ⟨N3, hN3⟩ := h3 (e / 4) (by positivity)
  refine ⟨max N1 (max N2 N3), fun n hn hev => ?_⟩
  have e1 := hN1 n (le_trans (le_max_left _ _) hn)
  have e2 := hN2 n (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn)
  have e3 := hN3 n (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn) hev
  have hm : minor n = I n (fun k => w k) (fun k => w k) := by
    simp only [minor, I]
    congr 1
    funext t
    simp only [sq]
  have hs := hsplit n
  have a1 := Complex.abs_re_le_norm (I n (low n) (low n))
  have a2 := Complex.abs_re_le_norm (I n (low n) (high n))
  have a1' := neg_abs_le (I n (low n) (low n)).re
  have a2' := neg_abs_le (I n (low n) (high n)).re
  have hr : (minor n).re = (I n (low n) (low n)).re + 2 * (I n (low n) (high n)).re + (I n (high n) (high n)).re := by
    rw [hm]
    have : I n w w = I n (fun k => w k) (fun k => w k) := rfl
    rw [← this, hs]
    simp
  rw [hr]
  nlinarith
