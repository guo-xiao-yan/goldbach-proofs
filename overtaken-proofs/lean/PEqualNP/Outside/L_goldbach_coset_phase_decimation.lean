import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Field.GeomSum
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Order.Interval.Finset.Nat

private theorem zss_set (n q : ℕ) (hq : 0 < q) :
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

private theorem shift_sum {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n q : ℕ) (hq : 0 < q) :
    ∑ s ∈ (Finset.range (2*n+1)).filter (fun s => s % q = n % q), f s =
      f n + ∑ h ∈ Finset.Icc 1 (n/q), (f (n + h*q) + f (n - h*q)) := by
  have hn : n ∈ (Finset.range (2*n+1)).filter (fun s => s % q = n % q) := by
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, trivial⟩
  rw [← Finset.add_sum_erase _ _ hn, zss_set n q hq, Finset.sum_union, Finset.sum_image, Finset.sum_image,
    ← Finset.sum_add_distrib]
  · congr 1
    exact Finset.sum_congr rfl (fun h _ => add_comm _ _)
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

private theorem geom_root (L : ℕ) (y : ℂ) (hy : y^L = 1) :
    ∑ j ∈ Finset.range L, y^j = if y = 1 then (L:ℂ) else 0 := by
  by_cases h : y = 1
  · simp [h]
  · rw [if_neg h, geom_sum_eq h, hy, sub_self, zero_div]

private theorem root_sums (L : ℕ) (z : ℂ) (hz : IsPrimitiveRoot z L) (h : ℕ) :
    (∑ j ∈ Finset.range L, (z^j)^h = if L ∣ h then (L:ℂ) else 0) ∧
    (∑ j ∈ Finset.range L, ((z^j)⁻¹)^h = if L ∣ h then (L:ℂ) else 0) := by
  have hzL : z^L = 1 := hz.pow_eq_one
  have hy : (z^h)^L = 1 := by rw [← pow_mul, mul_comm, pow_mul, hzL, one_pow]
  have hiff : z^h = 1 ↔ L ∣ h := hz.pow_eq_one_iff_dvd h
  constructor
  · have e : ∀ j, (z^j)^h = (z^h)^j := fun j => by rw [← pow_mul, ← pow_mul, mul_comm]
    simp_rw [e]
    rw [geom_root L _ hy]
    simp only [hiff]
  · have e : ∀ j, ((z^j)⁻¹)^h = ((z^h)⁻¹)^j := fun j => by
      rw [inv_pow, inv_pow, ← pow_mul, ← pow_mul, mul_comm]
    simp_rw [e]
    rw [geom_root L _ (by rw [inv_pow, hy, inv_one])]
    simp only [inv_eq_one, hiff]

private theorem decim (B : ℕ → ℝ) (n q L : ℕ) (z : ℂ) (hq : 0 < q) (hL : 0 < L)
    (hz : IsPrimitiveRoot z L) :
    (∑ j ∈ Finset.range L, ((B n : ℂ) + ∑ h ∈ Finset.Icc 1 (n/q),
        ((B (n+h*q) : ℂ) * (z^j)^h + (B (n-h*q) : ℂ) * ((z^j)⁻¹)^h))) / (L:ℂ) =
    ∑ s ∈ (Finset.range (2*n+1)).filter (fun s => s % (q*L) = n % (q*L)), (B s : ℂ) := by
  have hqL : 0 < q * L := Nat.mul_pos hq hL
  have hL' : (L:ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  rw [shift_sum (fun s => (B s : ℂ)) n (q*L) hqL]
  have h1 : ∑ j ∈ Finset.range L, ((B n : ℂ) + ∑ h ∈ Finset.Icc 1 (n/q),
        ((B (n+h*q) : ℂ) * (z^j)^h + (B (n-h*q) : ℂ) * ((z^j)⁻¹)^h)) =
      (L:ℂ) * (B n : ℂ) + ∑ h ∈ Finset.Icc 1 (n/q),
        (if L ∣ h then (L:ℂ) * ((B (n+h*q) : ℂ) + (B (n-h*q) : ℂ)) else 0) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, Finset.sum_comm]
    congr 1
    refine Finset.sum_congr rfl (fun h _ => ?_)
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, (root_sums L z hz h).1,
      (root_sums L z hz h).2]
    by_cases hd : L ∣ h
    · simp only [hd, if_true]; ring
    · simp [hd]
  have h2 : ∑ h ∈ Finset.Icc 1 (n/q),
        (if L ∣ h then (L:ℂ) * ((B (n+h*q) : ℂ) + (B (n-h*q) : ℂ)) else 0) =
      (L:ℂ) * ∑ h ∈ Finset.Icc 1 (n/(q*L)), ((B (n + h*(q*L)) : ℂ) + (B (n - h*(q*L)) : ℂ)) := by
    rw [← Finset.sum_filter, ← Finset.mul_sum]
    have hset : (Finset.Icc 1 (n/q)).filter (fun h => L ∣ h) =
        (Finset.Icc 1 (n/(q*L))).image (fun h => h * L) := by
      ext h
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image, Nat.le_div_iff_mul_le hq,
        Nat.le_div_iff_mul_le hqL]
      constructor
      · rintro ⟨⟨h1, h2⟩, ⟨c, rfl⟩⟩
        refine ⟨c, ⟨?_, ?_⟩, by ring⟩
        · rcases Nat.eq_zero_or_pos c with e | e
          · subst e; simp at h1
          · exact e
        · have : c * (q * L) = L * c * q := by ring
          omega
      · rintro ⟨c, ⟨h1, h2⟩, rfl⟩
        refine ⟨⟨?_, ?_⟩, ⟨c, by ring⟩⟩
        · nlinarith
        · have : c * (q * L) = c * L * q := by ring
          omega
    rw [hset, Finset.sum_image]
    · congr 1
      refine Finset.sum_congr rfl (fun h _ => ?_)
      have e : h * L * q = h * (q * L) := by ring
      rw [e]
    · intro a _ b _ hab
      exact Nat.eq_of_mul_eq_mul_right hL hab
  rw [h1, h2, ← mul_add, mul_div_cancel_left₀ _ hL']

theorem PEqualNP.Outside.L_goldbach_coset_phase_decimation :
    let w := fun k : ℕ => if k.Prime then Real.log (k:ℝ) else 0; let B := fun n s : ℕ => ∑ k ∈ (Finset.range (n+1)).filter (fun k => k ≤ s ∧ s-k ≤ n), w k*w (s-k); let Z := fun n q : ℕ => ∑ s ∈ (Finset.range (2*n+1)).filter (fun s => s % q = n % q), B n s; let Y := fun (n q : ℕ) (z : ℂ) => (B n n:ℂ) + ∑ h ∈ Finset.Icc 1 (n/q), ((B n (n+h*q):ℂ)*z^h + (B n (n-h*q):ℂ)*(z⁻¹)^h); ∀ (n q L : ℕ) (z : ℂ), 0<q → 0<L → IsPrimitiveRoot z L → (∑ j ∈ Finset.range L, Y n q (z^j))/(L:ℂ)=(Z n (q*L):ℂ) := by
  intro w B Z Y n q L z hq hL hz
  have h := decim (B n) n q L z hq hL hz
  have e : (Z n (q*L) : ℂ) = ∑ s ∈ (Finset.range (2*n+1)).filter (fun s => s % (q*L) = n % (q*L)), (B n s : ℂ) :=
    Complex.ofReal_sum _ _
  rw [e]
  exact h
