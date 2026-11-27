import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

private theorem cosetCardGe (n q r : ℕ) (hq : 0 < q) (hr : r < q) :
    (n + 1) / q ≤ ((Finset.range (n+1)).filter (fun k => k % q = r)).card := by
  have h1 : (Finset.range ((n + 1) / q)).card ≤
      ((Finset.range (n+1)).filter (fun k => k % q = r)).card := by
    apply Finset.card_le_card_of_injOn (fun i => r + i * q)
    · intro i hi
      have hi' : i < (n + 1) / q := by simpa using hi
      have h2 : (i + 1) * q ≤ (n + 1) / q * q := Nat.mul_le_mul_right q hi'
      have h3 : (n + 1) / q * q ≤ n + 1 := Nat.div_mul_le_self _ _
      simp only [Finset.coe_filter, Finset.mem_range]
      constructor
      · nlinarith
      · rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr]
    · intro i _ j _ h
      have : i * q = j * q := by simpa using h
      exact Nat.eq_of_mul_eq_mul_right hq this
  simpa using h1

theorem PEqualNP.Outside.L_goldbach_coset_full_period_floor :
    let F := fun n q r : ℕ => (Finset.range (n+1)).filter (fun k => k % q=r); let w := fun k : ℕ => if k.Prime then Real.log (k:ℝ) else 0; let A := fun n q r : ℕ => ∑ k ∈ F n q r, w k; let μ := fun q r : ℕ => if r.Coprime q then (q:ℝ)/(q.totient:ℝ) else 0; let v := fun n q r : ℕ => A n q r-((F n q r).card:ℝ)*μ q r; let E := fun n q => ∑ r ∈ Finset.range q, (v n q r)^2/((F n q r).card:ℝ); ∀ n q : ℕ, 0<q → 2*q≤n → E n q ≤ (2*(q:ℝ)/(n:ℝ))*∑ r ∈ Finset.range q, (v n q r)^2 := by
  intro F w A μ v E n q hq hn
  have hnpos : (0:ℝ) < n := by
    have : 0 < n := by omega
    exact_mod_cast this
  show ∑ r ∈ Finset.range q, (v n q r)^2/((F n q r).card:ℝ) ≤ _
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro r hr
  have hrq : r < q := Finset.mem_range.mp hr
  have hc : (n + 1) / q ≤ (F n q r).card := cosetCardGe n q r hq hrq
  have hm : n ≤ 2 * ((n + 1) / q) * q := by
    have h1 : (n + 1) / q * q + (n + 1) % q = n + 1 := Nat.div_add_mod' (n + 1) q
    have h2 : (n + 1) % q < q := Nat.mod_lt _ hq
    nlinarith
  have hc2 : n ≤ 2 * (F n q r).card * q := by
    calc n ≤ 2 * ((n + 1) / q) * q := hm
      _ ≤ 2 * (F n q r).card * q := by
        apply Nat.mul_le_mul_right; omega
  have hcpos : (0:ℝ) < ((F n q r).card:ℝ) := by
    have : 0 < (F n q r).card := by
      rcases Nat.eq_zero_or_pos (F n q r).card with h | h
      · rw [h] at hc2; omega
      · exact h
    exact_mod_cast this
  have hc3 : (n:ℝ) ≤ 2 * ((F n q r).card:ℝ) * q := by exact_mod_cast hc2
  rw [div_le_iff₀ hcpos]
  have key : 1 ≤ (2*(q:ℝ)/(n:ℝ)) * ((F n q r).card:ℝ) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hnpos]; linarith
  calc (v n q r)^2 = 1 * (v n q r)^2 := by ring
    _ ≤ ((2*(q:ℝ)/(n:ℝ)) * ((F n q r).card:ℝ)) * (v n q r)^2 := by gcongr
    _ = _ := by ring
