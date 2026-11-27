import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp

private theorem step_aux (q N r : ℕ) (hq : 0 < q) (hr : r < q) :
    (N + 1) / q + (if r < (N + 1) % q then 1 else 0) =
      N / q + (if r < N % q then 1 else 0) + (if N % q = r then 1 else 0) := by
  have hm : N % q < q := Nat.mod_lt N hq
  have hN : N = q * (N / q) + N % q := (Nat.div_add_mod N q).symm
  generalize N / q = a at hN ⊢
  generalize N % q = m at hN hm ⊢
  subst hN
  have e0 : q * a + m + 1 = q * a + (m + 1) := by omega
  rw [e0, Nat.mul_add_div hq, Nat.mul_add_mod]
  by_cases h : m + 1 < q
  · rw [Nat.div_eq_of_lt h, Nat.mod_eq_of_lt h]
    split_ifs <;> omega
  · have hmq : m + 1 = q := by omega
    rw [hmq, Nat.div_self hq, Nat.mod_self]
    split_ifs <;> omega

private theorem card_aux (q r : ℕ) (hq : 0 < q) (hr : r < q) (N : ℕ) :
    ((Finset.range N).filter (fun k => k % q = r)).card =
      N / q + (if r < N % q then 1 else 0) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.range_add_one, Finset.filter_insert]
    have := step_aux q N r hq hr
    by_cases h : N % q = r
    · rw [if_pos h, Finset.card_insert_of_notMem (by simp), ih]
      rw [if_pos h] at this
      omega
    · rw [if_neg h, ih]
      rw [if_neg h] at this
      omega

private theorem sum_aux (q s : ℕ) (hq : 0 < q) (hs : s < q) :
    (∑ r ∈ Finset.range q, (if r < s then 1 - (s:ℝ)/q else -((s:ℝ)/q))^2) =
      (s:ℝ)*((q:ℝ)-s)/q := by
  have hqr : (q:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
  have e : Finset.range q = Finset.range (s + (q - s)) := by
    congr 1
    omega
  rw [e, Finset.sum_range_add]
  have h1 : (∑ x ∈ Finset.range s, (if x < s then 1 - (s:ℝ)/q else -((s:ℝ)/q))^2) =
      ∑ x ∈ Finset.range s, (1 - (s:ℝ)/q)^2 := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [if_pos (Finset.mem_range.mp hx)]
  have h2 : (∑ x ∈ Finset.range (q - s), (if s + x < s then 1 - (s:ℝ)/q else -((s:ℝ)/q))^2) =
      ∑ x ∈ Finset.range (q - s), ((s:ℝ)/q)^2 := by
    apply Finset.sum_congr rfl
    intro x _
    rw [if_neg (by omega)]
    ring
  rw [h1, h2, Finset.sum_const, Finset.sum_const, Finset.card_range, Finset.card_range]
  simp only [nsmul_eq_mul]
  have hc : ((q - s : ℕ) : ℝ) = (q:ℝ) - s := by
    rw [Nat.cast_sub hs.le]
  rw [hc]
  field_simp
  ring

theorem PEqualNP.Outside.L_goldbach_coset_rounding_profile :
    let F := fun n q r : ℕ => (Finset.range (n+1)).filter (fun k => k % q=r); ∀ n q : ℕ, 0<q → let s := (n+1)%q; (∑ r ∈ Finset.range q, (((F n q r).card:ℝ)-(n+1:ℕ)/(q:ℝ))^2) = (s:ℝ)*((q:ℝ)-s)/q := by
  intro F n q hq s
  have hs : s < q := Nat.mod_lt _ hq
  have hqr : (q:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
  have hN : (n + 1) = q * ((n + 1) / q) + s := (Nat.div_add_mod (n + 1) q).symm
  have hNr : ((n + 1 : ℕ) : ℝ) = (q:ℝ) * (((n + 1) / q : ℕ) : ℝ) + (s:ℝ) := by
    exact_mod_cast hN
  have hc : ∀ r ∈ Finset.range q, (((F n q r).card : ℝ) - ((n + 1 : ℕ) : ℝ) / (q:ℝ)) =
      if r < s then 1 - (s:ℝ)/q else -((s:ℝ)/q) := by
    intro r _
    have hcard : (F n q r).card = (n + 1) / q + (if r < s then 1 else 0) :=
      card_aux q r hq (by simpa using ‹r ∈ Finset.range q›) (n + 1)
    rw [hcard, hNr]
    split_ifs <;> push_cast <;> field_simp <;> ring
  rw [Finset.sum_congr rfl (fun r hr => by rw [hc r hr])]
  exact sum_aux q s hq hs
