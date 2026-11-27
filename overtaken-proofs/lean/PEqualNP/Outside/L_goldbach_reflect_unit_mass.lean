import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Ring.Finset


theorem PEqualNP.Outside.L_goldbach_reflect_unit_mass :
    let w := fun k : ℕ => if k.Prime then Real.log (k : ℝ) else 0; ∀ n : ℕ, 4 ≤ n → Even n → (∑ k ∈ Finset.range (n+1), w k*w (n-k)) = (∑ k ∈ (Finset.range (n+1)).filter (fun k => Nat.Coprime k n), w k*w (n-k)) + (w (n/2))^2 := by
  intro w n hn hev
  obtain ⟨m, hm⟩ := hev
  have hn2 : n / 2 = m := by omega
  have hnm : n - m = m := by omega
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (n+1)) (fun k => Nat.Coprime k n)]
  congr 1
  rw [Finset.sum_eq_single_of_mem (n / 2)]
  · rw [hn2, hnm, sq]
  · rw [Finset.mem_filter, Finset.mem_range, hn2]
    refine ⟨by omega, ?_⟩
    intro hc
    have hd : m ∣ n := ⟨2, by omega⟩
    have h1 : Nat.gcd m n = m := Nat.gcd_eq_left hd
    have h2 : Nat.gcd m n = 1 := hc
    omega
  · intro k hk hne
    rw [Finset.mem_filter, Finset.mem_range] at hk
    obtain ⟨hk1, hk2⟩ := hk
    by_contra hz
    have hwk : w k ≠ 0 := fun h => hz (by rw [h, zero_mul])
    have hwk' : w (n - k) ≠ 0 := fun h => hz (by rw [h, mul_zero])
    have hkp : k.Prime := by
      by_contra h
      exact hwk (by simp only [w]; rw [if_neg h])
    have hnkp : (n - k).Prime := by
      by_contra h
      exact hwk' (by simp only [w]; rw [if_neg h])
    have hkd : k ∣ n := by
      by_contra h
      exact hk2 ((Nat.Prime.coprime_iff_not_dvd hkp).mpr h)
    have hkd2 : k ∣ n - k := Nat.dvd_sub hkd (dvd_refl k)
    rcases (Nat.Prime.eq_one_or_self_of_dvd hnkp k hkd2) with h | h
    · exact hkp.one_lt.ne' h
    · apply hne
      rw [hn2]
      omega
