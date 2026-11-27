import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Order.Interval.Finset.Nat

private theorem cbs_set (n q : ℕ) (hq : 0 < q) :
    ((Finset.range (2*n+1)).filter (fun s => s % q = n % q)).erase n =
      (Finset.Icc 1 (n/q)).image (fun h => n - h*q) ∪ (Finset.Icc 1 (n/q)).image (fun h => n + h*q) := by
  ext s
  simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_range, Finset.mem_union,
    Finset.mem_image, Finset.mem_Icc]
  constructor
  · rintro ⟨hne, hs, hmod⟩
    rcases lt_or_gt_of_ne hne with h | h
    · left
      have hd : q ∣ n - s := (Nat.modEq_iff_dvd' h.le).1 hmod
      obtain ⟨h0, hh⟩ := hd
      have hpos : 1 ≤ h0 := by
        rcases Nat.eq_zero_or_pos h0 with e | e
        · subst e; simp at hh; omega
        · exact e
      refine ⟨h0, ⟨hpos, ?_⟩, ?_⟩
      · rw [Nat.le_div_iff_mul_le hq]
        have : h0 * q = n - s := by rw [hh]; ring
        omega
      · have : h0 * q = n - s := by rw [hh]; ring
        omega
    · right
      have hd : q ∣ s - n := (Nat.modEq_iff_dvd' h.le).1 hmod.symm
      obtain ⟨h0, hh⟩ := hd
      have hpos : 1 ≤ h0 := by
        rcases Nat.eq_zero_or_pos h0 with e | e
        · subst e; simp at hh; omega
        · exact e
      have : h0 * q = s - n := by rw [hh]; ring
      refine ⟨h0, ⟨hpos, ?_⟩, ?_⟩
      · rw [Nat.le_div_iff_mul_le hq]
        omega
      · omega
  · rintro (⟨h0, ⟨h1, h2⟩, rfl⟩ | ⟨h0, ⟨h1, h2⟩, rfl⟩)
    · rw [Nat.le_div_iff_mul_le hq] at h2
      have : 1 * q ≤ h0 * q := Nat.mul_le_mul_right q h1
      refine ⟨by omega, by omega, ?_⟩
      have e : n = (n - h0 * q) + h0 * q := by omega
      conv_rhs => rw [e]
      rw [Nat.add_mul_mod_self_right]
    · rw [Nat.le_div_iff_mul_le hq] at h2
      have : 1 * q ≤ h0 * q := Nat.mul_le_mul_right q h1
      refine ⟨by omega, by omega, ?_⟩
      rw [Nat.add_mul_mod_self_right]

private theorem cbs_switch :
    ∀ d Q : ℕ, 0<d → (∑ q ∈ (Finset.Ioc Q (2*Q)).filter (fun q => q∣d), (q:ℝ)) = (d:ℝ)* ∑ h ∈ d.divisors.filter (fun h => Q*h<d ∧ d≤2*Q*h), 1/(h:ℝ) := by
  intro d Q hd
  rw [Finset.mul_sum]
  refine Finset.sum_nbij' (fun q => d / q) (fun h => d / h) ?_ ?_ ?_ ?_ ?_
  · intro q hq
    simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_coe, Nat.mem_divisors] at hq ⊢
    obtain ⟨⟨h1, h2⟩, c, hc⟩ := hq
    have hq0 : 0 < q := by
      rcases Nat.eq_zero_or_pos q with h | h
      · subst h; simp at hc; omega
      · exact h
    have hc0 : 0 < c := by
      rcases Nat.eq_zero_or_pos c with h | h
      · subst h; simp at hc; omega
      · exact h
    have e : d / q = c := by rw [hc]; exact Nat.mul_div_cancel_left c hq0
    rw [e]
    refine ⟨⟨⟨q, by rw [hc]; ring⟩, by omega⟩, ?_, ?_⟩
    · rw [hc]; nlinarith
    · rw [hc]; nlinarith
  · intro h hh
    simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_coe, Nat.mem_divisors] at hh ⊢
    obtain ⟨⟨⟨c, hc⟩, _⟩, h1, h2⟩ := hh
    have hh0 : 0 < h := by
      rcases Nat.eq_zero_or_pos h with e | e
      · subst e; simp at hc; omega
      · exact e
    have e : d / h = c := by rw [hc]; exact Nat.mul_div_cancel_left c hh0
    rw [e]
    refine ⟨⟨?_, ?_⟩, ⟨h, by rw [hc]; ring⟩⟩
    · rw [hc] at h1; nlinarith
    · rw [hc] at h2; nlinarith
  · intro q hq
    simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_coe] at hq
    obtain ⟨⟨h1, h2⟩, c, hc⟩ := hq
    have hq0 : 0 < q := by
      rcases Nat.eq_zero_or_pos q with h | h
      · subst h; simp at hc; omega
      · exact h
    have e : d / q = c := by rw [hc]; exact Nat.mul_div_cancel_left c hq0
    have hc0 : 0 < c := by
      rcases Nat.eq_zero_or_pos c with h | h
      · subst h; simp at hc; omega
      · exact h
    simp only [e]
    rw [hc]; exact Nat.mul_div_cancel q hc0
  · intro h hh
    simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_coe] at hh
    obtain ⟨⟨⟨c, hc⟩, _⟩, _, _⟩ := hh
    have hh0 : 0 < h := by
      rcases Nat.eq_zero_or_pos h with e | e
      · subst e; simp at hc; omega
      · exact e
    have e : d / h = c := by rw [hc]; exact Nat.mul_div_cancel_left c hh0
    simp only [e]
    rw [hc]; exact Nat.mul_div_cancel h (by
      rcases Nat.eq_zero_or_pos c with e | e
      · subst e; simp at hc; omega
      · exact e)
  · intro q hq
    simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_coe] at hq
    obtain ⟨⟨h1, h2⟩, c, hc⟩ := hq
    have hq0 : 0 < q := by
      rcases Nat.eq_zero_or_pos q with h | h
      · subst h; simp at hc; omega
      · exact h
    have hc0 : 0 < c := by
      rcases Nat.eq_zero_or_pos c with h | h
      · subst h; simp at hc; omega
      · exact h
    have e : d / q = c := by rw [hc]; exact Nat.mul_div_cancel_left c hq0
    rw [e, hc]
    have : (c:ℝ) ≠ 0 := by exact_mod_cast hc0.ne'
    push_cast
    field_simp

private theorem cbs_shift (f : ℕ → ℝ) (n q : ℕ) (hq : 0 < q) :
    (∑ s ∈ (Finset.range (2*n+1)).filter (fun s => s % q = n % q), f s) - f n
      = ∑ h ∈ Finset.Icc 1 (n/q), (f (n-h*q) + f (n+h*q)) := by
  have hn : n ∈ (Finset.range (2*n+1)).filter (fun s => s % q = n % q) := by
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, trivial⟩
  rw [← Finset.add_sum_erase _ _ hn, cbs_set n q hq, add_sub_cancel_left,
    Finset.sum_union, Finset.sum_image, Finset.sum_image, Finset.sum_add_distrib]
  · intro a ha b hb hab
    simp only [Finset.mem_coe, Finset.mem_Icc, Nat.le_div_iff_mul_le hq] at ha hb
    have : a * q = b * q := by simp only at hab; omega
    exact Nat.eq_of_mul_eq_mul_right hq this
  · intro a ha b hb hab
    simp only [Finset.mem_coe, Finset.mem_Icc, Nat.le_div_iff_mul_le hq] at ha hb
    have : a * q = b * q := by simp only at hab; omega
    exact Nat.eq_of_mul_eq_mul_right hq this
  · rw [Finset.disjoint_left]
    intro s h1 h2
    simp only [Finset.mem_image, Finset.mem_Icc, Nat.le_div_iff_mul_le hq] at h1 h2
    obtain ⟨a, ⟨ha1, ha2⟩, rfl⟩ := h1
    obtain ⟨b, ⟨hb1, hb2⟩, hb⟩ := h2
    have : 1 * q ≤ b * q := Nat.mul_le_mul_right q hb1
    omega

private theorem cbs_inner (c : ℕ → ℝ) (n q : ℕ) (hq : 0 < q) :
    ∑ h ∈ Finset.Icc 1 (n/q), c (h*q) = ∑ d ∈ (Finset.Icc 1 n).filter (fun d => q ∣ d), c d := by
  refine Finset.sum_nbij' (fun h => h*q) (fun d => d/q) ?_ ?_ ?_ ?_ ?_
  · intro h hh
    simp only [Finset.mem_coe, Finset.mem_Icc, Finset.mem_filter, Nat.le_div_iff_mul_le hq] at hh ⊢
    refine ⟨⟨?_, hh.2⟩, ⟨h, by ring⟩⟩
    have : 1 * q ≤ h * q := Nat.mul_le_mul_right q hh.1
    omega
  · intro d hd
    simp only [Finset.mem_Icc, Finset.mem_filter] at hd
    obtain ⟨⟨h1, h2⟩, c', hc⟩ := hd
    have e : d / q = c' := by rw [hc]; exact Nat.mul_div_cancel_left c' hq
    have hc0 : 0 < c' := by
      rcases Nat.eq_zero_or_pos c' with h | h
      · subst h; simp at hc; omega
      · exact h
    have hle : c' ≤ n / q := by
      rw [Nat.le_div_iff_mul_le hq, mul_comm, ← hc]; exact h2
    simp only [Finset.mem_Icc, e]
    exact ⟨hc0, hle⟩
  · intro h hh
    simp only [Nat.mul_div_cancel _ hq]
  · intro d hd
    simp only [Finset.mem_coe, Finset.mem_filter] at hd
    obtain ⟨_, c', hc⟩ := hd
    have e : d / q = c' := by rw [hc]; exact Nat.mul_div_cancel_left c' hq
    simp only [e]; rw [hc]; ring
  · intro h hh
    rfl

private theorem cbs_pair (c : ℕ → ℝ) (n Q : ℕ) :
    (∑ q ∈ Finset.Ioc Q (2*Q), (q:ℝ) * ∑ h ∈ Finset.Icc 1 (n/q), c (h*q))
      = ∑ d ∈ Finset.Icc 1 n, c d * ∑ q ∈ (Finset.Ioc Q (2*Q)).filter (fun q => q ∣ d), (q:ℝ) := by
  have h1 : ∀ q ∈ Finset.Ioc Q (2*Q), (q:ℝ) * ∑ h ∈ Finset.Icc 1 (n/q), c (h*q)
      = ∑ d ∈ Finset.Icc 1 n, if q ∣ d then (q:ℝ) * c d else 0 := by
    intro q hq
    have hq0 : 0 < q := lt_of_le_of_lt (Nat.zero_le Q) (Finset.mem_Ioc.1 hq).1
    rw [cbs_inner c n q hq0, Finset.mul_sum, Finset.sum_filter]
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro d _
  rw [Finset.sum_filter, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro q _
  split_ifs <;> simp [mul_comm]

theorem PEqualNP.Outside.L_goldbach_coset_block_shift_transform :
    let w := fun k : ℕ => if k.Prime then Real.log (k:ℝ) else 0; let B := fun n s : ℕ => ∑ k ∈ (Finset.range (n+1)).filter (fun k => k ≤ s ∧ s-k ≤ n), w k*w (s-k); let Z := fun n q : ℕ => ∑ s ∈ (Finset.range (2*n+1)).filter (fun s => s % q=n % q), B n s; ∀ n Q : ℕ, 0<Q → (∑ q ∈ Finset.Ioc Q (2*Q), (q:ℝ)*(Z n q-B n n)) = ∑ d ∈ Finset.Icc 1 n, (B n (n-d)+B n (n+d))*(d:ℝ)*(∑ h ∈ d.divisors.filter (fun h => Q*h<d ∧ d≤2*Q*h), 1/(h:ℝ)) := by
  intro w B Z n Q _
  have h1 : ∀ q ∈ Finset.Ioc Q (2*Q), (q:ℝ) * (Z n q - B n n)
      = (q:ℝ) * ∑ h ∈ Finset.Icc 1 (n/q), (fun d => B n (n-d) + B n (n+d)) (h*q) := by
    intro q hq
    have hq0 : 0 < q := lt_of_le_of_lt (Nat.zero_le Q) (Finset.mem_Ioc.1 hq).1
    exact congrArg _ (cbs_shift (B n) n q hq0)
  rw [Finset.sum_congr rfl h1, cbs_pair (fun d => B n (n-d) + B n (n+d)) n Q]
  refine Finset.sum_congr rfl ?_
  intro d hd
  have hd0 : 0 < d := (Finset.mem_Icc.1 hd).1
  rw [cbs_switch d Q hd0]
  ring
