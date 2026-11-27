import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Data.Finset.Insert
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

private lemma floor_rat (a b x : ℕ) (r : ℚ) (hb : 0 < b) (hr : r = (a:ℚ)/(b:ℚ)) :
    ⌊(r:ℝ) * (x:ℝ)⌋₊ = a*x/b := by
  have hb' : (b:ℝ) ≠ 0 := by positivity
  have : (r:ℝ) * (x:ℝ) = ((a*x : ℕ):ℝ) / (b:ℝ) := by
    subst hr
    push_cast
    field_simp
  rw [this]
  exact Nat.floor_div_eq_div (K := ℝ) (a*x) b

theorem PEqualNP.Outside.L_goldbach_bulk_rounded_cover :
    let J := fun x : ℕ => (Finset.range (2*x+1)).filter (fun n => Even n ∧ 13*x≤12*n ∧ 4*n≤5*x); ∃ S : Finset ℚ, (∀ r∈S, 0<r) ∧ ∃ X : ℕ, ∀ x≥X, ∀ n∈Finset.Icc x (2*x), Even n → ∃ r∈S, n∈J ⌊(r:ℝ)*(x:ℝ)⌋₊ := by
  intro J
  refine ⟨{17/20, 19/20, 27/25, 61/50, 139/100, 79/50, 9/5}, ?_, 10000, ?_⟩
  · intro r hr
    simp only [Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with h | h | h | h | h | h | h <;> subst h <;> norm_num
  · intro x hx n hn he
    rw [Finset.mem_Icc] at hn
    obtain ⟨h1, h2⟩ := hn
    by_cases c17 : 25*n<26*x
    · refine ⟨17/20, by simp, ?_⟩
      simp only [J, Finset.mem_filter, Finset.mem_range, floor_rat 17 20 x (17/20) (by norm_num) (by norm_num)]
      refine ⟨by omega, he, by omega, by omega⟩
    by_cases c19 : 50*n<59*x
    · refine ⟨19/20, by simp, ?_⟩
      simp only [J, Finset.mem_filter, Finset.mem_range, floor_rat 19 20 x (19/20) (by norm_num) (by norm_num)]
      refine ⟨by omega, he, by omega, by omega⟩
    by_cases c27 : 200*n<267*x
    · refine ⟨27/25, by simp, ?_⟩
      simp only [J, Finset.mem_filter, Finset.mem_range, floor_rat 27 25 x (27/25) (by norm_num) (by norm_num)]
      refine ⟨by omega, he, by omega, by omega⟩
    by_cases c61 : 200*n<303*x
    · refine ⟨61/50, by simp, ?_⟩
      simp only [J, Finset.mem_filter, Finset.mem_range, floor_rat 61 50 x (61/50) (by norm_num) (by norm_num)]
      refine ⟨by omega, he, by omega, by omega⟩
    by_cases c139 : 40*n<69*x
    · refine ⟨139/100, by simp, ?_⟩
      simp only [J, Finset.mem_filter, Finset.mem_range, floor_rat 139 100 x (139/100) (by norm_num) (by norm_num)]
      refine ⟨by omega, he, by omega, by omega⟩
    by_cases c79 : 25*n<49*x
    · refine ⟨79/50, by simp, ?_⟩
      simp only [J, Finset.mem_filter, Finset.mem_range, floor_rat 79 50 x (79/50) (by norm_num) (by norm_num)]
      refine ⟨by omega, he, by omega, by omega⟩
    · refine ⟨9/5, by simp, ?_⟩
      simp only [J, Finset.mem_filter, Finset.mem_range, floor_rat 9 5 x (9/5) (by norm_num) (by norm_num)]
      refine ⟨by omega, he, by omega, by omega⟩
