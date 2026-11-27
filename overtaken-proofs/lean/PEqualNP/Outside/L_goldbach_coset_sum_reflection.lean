import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Totient

private theorem refl_aux (n q k a : ℕ) (hk : k ≤ n) (ha : a ≤ n + q) (h : k % q = a % q) :
    (n - k) % q = (n + q - a) % q := by
  have h1 : k ≡ a [MOD q] := h
  have h2 : n - k + k ≡ n + q - a + a [MOD q] := by
    have e1 : n - k + k = n := Nat.sub_add_cancel hk
    have e2 : n + q - a + a = n + q := Nat.sub_add_cancel ha
    rw [e1, e2]
    show n % q = (n + q) % q
    simp
  exact Nat.ModEq.add_right_cancel h1 h2

theorem PEqualNP.Outside.L_goldbach_coset_sum_reflection :
    let F := fun n q r : ℕ => (Finset.range (n+1)).filter (fun k => k % q=r); let j := fun n q r : ℕ => (n+q-r)%q; ∀ n q r : ℕ, 0<q → r<q → (F n q r).card=(F n q (j n q r)).card := by
  intro F j n q r hq hr
  simp only [F, j]
  apply Finset.card_bij' (fun k _ => n - k) (fun k _ => n - k)
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk ⊢
    obtain ⟨h1, h2⟩ := hk
    refine ⟨by omega, ?_⟩
    have := refl_aux n q k r (by omega) (by omega) (by rw [h2, Nat.mod_eq_of_lt hr])
    exact this
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk ⊢
    obtain ⟨h1, h2⟩ := hk
    refine ⟨by omega, ?_⟩
    have := refl_aux n q k (n + q - r) (by omega) (by omega) h2
    rw [this]
    have e : n + q - (n + q - r) = r := by omega
    rw [e, Nat.mod_eq_of_lt hr]
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk
    omega
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk
    omega
