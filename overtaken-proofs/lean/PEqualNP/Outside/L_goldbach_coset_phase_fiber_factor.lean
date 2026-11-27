import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Intervals
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

private theorem mod_iff (k l n q : ℕ) (hq : 0 < q) :
    l % q = (n + q - k % q) % q ↔ (k + l) % q = n % q := by
  have ht : k % q < q := Nat.mod_lt _ hq
  have hk : k ≡ k % q [MOD q] := (Nat.mod_modEq k q).symm
  constructor
  · intro h
    have h1 : k + l ≡ k % q + (n + q - k % q) [MOD q] := hk.add h
    have h2 : k % q + (n + q - k % q) = n + q := by omega
    rw [h2] at h1
    have h3 : n + q ≡ n [MOD q] := by
      unfold Nat.ModEq
      exact Nat.add_mod_right n q
    exact h1.trans h3
  · intro h
    have h1 : k + l ≡ n [MOD q] := h
    have h2 : k % q + l ≡ n [MOD q] := (hk.symm.add_right l).trans h1
    have h3 : n + q ≡ n [MOD q] := by
      unfold Nat.ModEq
      exact Nat.add_mod_right n q
    have h4 : k % q + l ≡ k % q + (n + q - k % q) [MOD q] := by
      have h5 : k % q + (n + q - k % q) = n + q := by omega
      rw [h5]
      exact h2.trans h3.symm
    exact Nat.ModEq.add_left_cancel' _ h4

private theorem reindex (w : ℕ → ℝ) (u : ℂ) (n q : ℕ) :
    ∑ k ∈ Finset.range (n+1), ∑ l ∈ Finset.range (n+1),
      (if (k + l) % q = n % q then ((w k : ℂ) * u^k) * ((w l : ℂ) * u^l) else 0) =
    ∑ s ∈ (Finset.range (2*n+1)).filter (fun s => s % q = n % q),
      ((∑ k ∈ (Finset.range (n+1)).filter (fun k => k ≤ s ∧ s-k ≤ n), w k * w (s-k) : ℝ) : ℂ) * u^s := by
  let G : ℕ → ℕ → ℂ := fun k s =>
    if (s % q = n % q ∧ (k ≤ s ∧ s - k ≤ n)) then (w k : ℂ) * (w (s-k) : ℂ) * u^s else 0
  have h1 : ∀ s, (if s % q = n % q then
      ((∑ k ∈ (Finset.range (n+1)).filter (fun k => k ≤ s ∧ s-k ≤ n), w k * w (s-k) : ℝ) : ℂ) * u^s else 0)
      = ∑ k ∈ Finset.range (n+1), G k s := by
    intro s
    by_cases h : s % q = n % q
    · simp only [h, if_true, true_and, G]
      push_cast
      rw [Finset.sum_mul, Finset.sum_filter]
    · simp [G, h]
  conv_rhs => rw [Finset.sum_filter]
  simp_rw [h1]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  rw [Finset.mem_range] at hk
  have hsub : (Finset.range (n+1)).image (fun l => k + l) ⊆ Finset.range (2*n+1) := by
    intro s hs
    simp only [Finset.mem_image, Finset.mem_range] at hs ⊢
    omega
  rw [← Finset.sum_subset hsub, Finset.sum_image]
  · refine Finset.sum_congr rfl (fun l hl => ?_)
    rw [Finset.mem_range] at hl
    have e : k + l - k = l := by omega
    simp only [G, e]
    by_cases h : (k + l) % q = n % q
    · have : k ≤ k + l ∧ l ≤ n := ⟨by omega, by omega⟩
      simp only [h, this, and_self, if_true]
      ring
    · simp [h]
  · intro a _ b _ hab
    simpa using hab
  · intro s hs hns
    simp only [G]
    rw [if_neg]
    rintro ⟨_, h2, h3⟩
    apply hns
    simp only [Finset.mem_image, Finset.mem_range]
    exact ⟨s - k, by omega, by omega⟩

private theorem phase_main (w : ℕ → ℝ) (B : ℕ → ℝ) (n q : ℕ) (u : ℂ) (hq : 0 < q) (hu : u ≠ 0)
    (hB : ∀ s, B s = ∑ k ∈ (Finset.range (n+1)).filter (fun k => k ≤ s ∧ s-k ≤ n), w k * w (s-k)) :
    u^n * ((B n : ℂ) + ∑ h ∈ Finset.Icc 1 (n/q),
        ((B (n+h*q) : ℂ) * (u^q)^h + (B (n-h*q) : ℂ) * ((u^q)⁻¹)^h)) =
    ∑ r ∈ Finset.range q,
      (∑ k ∈ (Finset.range (n+1)).filter (fun k => k % q = r), (w k : ℂ) * u^k) *
      (∑ k ∈ (Finset.range (n+1)).filter (fun k => k % q = (n + q - r) % q), (w k : ℂ) * u^k) := by
  have hterm : ∀ k l : ℕ, ∑ r ∈ Finset.range q,
      ((if k % q = r then (w k : ℂ) * u^k else 0) *
        (if l % q = (n + q - r) % q then (w l : ℂ) * u^l else 0)) =
      if (k + l) % q = n % q then ((w k : ℂ) * u^k) * ((w l : ℂ) * u^l) else 0 := by
    intro k l
    have e : ∀ r, ((if k % q = r then (w k : ℂ) * u^k else 0) *
        (if l % q = (n + q - r) % q then (w l : ℂ) * u^l else 0)) =
        if k % q = r then (if l % q = (n + q - k % q) % q then ((w k : ℂ) * u^k) * ((w l : ℂ) * u^l) else 0) else 0 := by
      intro r
      by_cases h : k % q = r
      · subst h
        by_cases h2 : l % q = (n + q - k % q) % q <;> simp [h2]
      · simp [h]
    simp only [e]
    rw [Finset.sum_ite_eq]
    simp only [Finset.mem_range, Nat.mod_lt _ hq, if_true, mod_iff k l n q hq]
  have hR : ∑ r ∈ Finset.range q,
      (∑ k ∈ (Finset.range (n+1)).filter (fun k => k % q = r), (w k : ℂ) * u^k) *
      (∑ k ∈ (Finset.range (n+1)).filter (fun k => k % q = (n + q - r) % q), (w k : ℂ) * u^k) =
      ∑ k ∈ Finset.range (n+1), ∑ l ∈ Finset.range (n+1),
        (if (k + l) % q = n % q then ((w k : ℂ) * u^k) * ((w l : ℂ) * u^l) else 0) := by
    have e : ∀ r, (∑ k ∈ (Finset.range (n+1)).filter (fun k => k % q = r), (w k : ℂ) * u^k) *
      (∑ k ∈ (Finset.range (n+1)).filter (fun k => k % q = (n + q - r) % q), (w k : ℂ) * u^k) =
      ∑ k ∈ Finset.range (n+1), ∑ l ∈ Finset.range (n+1),
        ((if k % q = r then (w k : ℂ) * u^k else 0) *
        (if l % q = (n + q - r) % q then (w l : ℂ) * u^l else 0)) := by
      intro r
      rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_mul_sum]
    simp only [e]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun l _ => hterm k l)
  rw [hR, reindex w u n q]
  have hB' : ∀ s, ((∑ k ∈ (Finset.range (n+1)).filter (fun k => k ≤ s ∧ s-k ≤ n), w k * w (s-k) : ℝ) : ℂ)
      = (B s : ℂ) := fun s => by rw [hB]
  simp only [hB']
  rw [shift_sum (fun s => (B s : ℂ) * u^s) n q hq, mul_add, Finset.mul_sum]
  congr 1
  · ring
  · refine Finset.sum_congr rfl (fun h hh => ?_)
    rw [Finset.mem_Icc, Nat.le_div_iff_mul_le hq] at hh
    have hle : h * q ≤ n := hh.2
    have e1 : (u^q)^h = u^(h*q) := by rw [← pow_mul, mul_comm]
    have e2 : u^n = u^(n-h*q) * u^(h*q) := by
      rw [← pow_add]; congr 1; omega
    have ha : u^(h*q) ≠ 0 := pow_ne_zero _ hu
    rw [inv_pow, e1, pow_add, e2]
    field_simp

theorem PEqualNP.Outside.L_goldbach_coset_phase_fiber_factor :
    let F := fun n q r : ℕ => (Finset.range (n+1)).filter (fun k => k % q = r); let w := fun k : ℕ => if k.Prime then Real.log (k:ℝ) else 0; let A := fun n q r : ℕ => ∑ k ∈ F n q r, w k; let j := fun n q r : ℕ => (n+q-r) % q; let B := fun n s : ℕ => ∑ k ∈ (Finset.range (n+1)).filter (fun k => k ≤ s ∧ s-k ≤ n), w k*w (s-k); let Y := fun (n q : ℕ) (z : ℂ) => (B n n:ℂ) + ∑ h ∈ Finset.Icc 1 (n/q), ((B n (n+h*q):ℂ)*z^h + (B n (n-h*q):ℂ)*(z⁻¹)^h); ∀ (n q : ℕ) (u : ℂ), 0<q → u≠0 → u^n*Y n q (u^q) = ∑ r ∈ Finset.range q, (∑ k ∈ F n q r, (w k:ℂ)*u^k)*(∑ k ∈ F n q (j n q r), (w k:ℂ)*u^k) := by
  intro F w A j B Y n q u hq hu
  exact phase_main w (B n) n q u hq hu (fun s => rfl)
