import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Sqrt
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr

open Classical in
private lemma pp_card (n : ℕ) :
    ((Finset.range (n+1)).filter (fun k => ∃ b a : ℕ, 2 ≤ b ∧ 2 ≤ a ∧ b^a = k)).card
      ≤ Nat.sqrt n * Nat.log 2 n := by
  have hsub : (Finset.range (n+1)).filter (fun k => ∃ b a : ℕ, 2 ≤ b ∧ 2 ≤ a ∧ b^a = k) ⊆
      (Finset.Icc 2 (Nat.sqrt n) ×ˢ Finset.Icc 2 (Nat.log 2 n)).image (fun p : ℕ × ℕ => p.1 ^ p.2) := by
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk
    obtain ⟨hkn, b, a, hb, ha, rfl⟩ := hk
    have hkn' : b ^ a ≤ n := by omega
    rw [Finset.mem_image]
    refine ⟨(b, a), ?_, rfl⟩
    rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
    refine ⟨⟨hb, ?_⟩, ha, ?_⟩
    · rw [Nat.le_sqrt']
      exact le_trans (Nat.pow_le_pow_right (by omega) ha) hkn'
    · apply Nat.le_log_of_pow_le Nat.one_lt_two
      exact le_trans (Nat.pow_le_pow_left hb a) hkn'
  calc _ ≤ _ := Finset.card_le_card hsub
    _ ≤ _ := Finset.card_image_le
    _ = (Nat.sqrt n + 1 - 2) * (Nat.log 2 n + 1 - 2) := by simp
    _ ≤ Nat.sqrt n * Nat.log 2 n := Nat.mul_le_mul (by omega) (by omega)

private lemma log2_le (n : ℕ) (hn : 1 ≤ n) : (Nat.log 2 n : ℝ) ≤ 2 * Real.log (n : ℝ) := by
  have h1 : (2 : ℕ) ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 (by omega)
  have h2 : ((2 : ℝ)) ^ Nat.log 2 n ≤ (n : ℝ) := by exact_mod_cast h1
  have h3 : Real.log ((2 : ℝ) ^ Nat.log 2 n) ≤ Real.log (n : ℝ) :=
    Real.log_le_log (by positivity) h2
  rw [Real.log_pow] at h3
  have h4 := Real.log_two_gt_d9
  have h5 : (0 : ℝ) ≤ (Nat.log 2 n : ℝ) := Nat.cast_nonneg _
  nlinarith

open Classical in
private lemma diff_total (n : ℕ) :
    ∑ k ∈ Finset.range (n+1), (ArithmeticFunction.vonMangoldt k - (if k.Prime then Real.log (k:ℝ) else 0))
      ≤ ((Nat.sqrt n * Nat.log 2 n : ℕ) : ℝ) * Real.log (n : ℝ) := by
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_natCast_nonneg n
  have hpt : ∀ k ∈ Finset.range (n+1),
      ArithmeticFunction.vonMangoldt k - (if k.Prime then Real.log (k:ℝ) else 0)
        ≤ if (∃ b a : ℕ, 2 ≤ b ∧ 2 ≤ a ∧ b^a = k) then Real.log (n : ℝ) else 0 := by
    intro k hk
    have hkn : k ≤ n := by simp only [Finset.mem_range] at hk; omega
    by_cases hp : k.Prime
    · rw [if_pos hp, ArithmeticFunction.vonMangoldt_apply_prime hp]
      split_ifs <;> linarith
    · rw [if_neg hp, sub_zero]
      by_cases h0 : ArithmeticFunction.vonMangoldt k = 0
      · rw [h0]; split_ifs <;> linarith
      · have hpp : IsPrimePow k := ArithmeticFunction.vonMangoldt_ne_zero_iff.mp h0
        obtain ⟨p, a, hpr, ha, hpa⟩ := (isPrimePow_nat_iff k).mp hpp
        have ha2 : 2 ≤ a := by
          by_contra hlt
          have : a = 1 := by omega
          subst this
          have hkp : k = p := by simpa using hpa.symm
          exact hp (hkp ▸ hpr)
        rw [if_pos ⟨p, a, hpr.two_le, ha2, hpa⟩]
        have hk0 : 0 < k := hpp.pos
        calc ArithmeticFunction.vonMangoldt k ≤ Real.log (k : ℝ) := ArithmeticFunction.vonMangoldt_le_log
          _ ≤ Real.log (n : ℝ) := Real.log_le_log (by exact_mod_cast hk0) (by exact_mod_cast hkn)
  calc _ ≤ ∑ k ∈ Finset.range (n+1), (if (∃ b a : ℕ, 2 ≤ b ∧ 2 ≤ a ∧ b^a = k) then Real.log (n : ℝ) else 0) :=
        Finset.sum_le_sum hpt
    _ = (((Finset.range (n+1)).filter (fun k => ∃ b a : ℕ, 2 ≤ b ∧ 2 ≤ a ∧ b^a = k)).card : ℝ) * Real.log (n : ℝ) := by
        rw [← Finset.sum_filter]; simp
    _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ hlog
        exact_mod_cast pp_card n

private lemma total_bound (n : ℕ) (hn : 2 ≤ n) :
    ∑ k ∈ Finset.range (n+1), (ArithmeticFunction.vonMangoldt k - (if k.Prime then Real.log (k:ℝ) else 0))
      ≤ 2 * Real.sqrt (n:ℝ) * (Real.log (2 * (n:ℝ)))^2 := by
  refine le_trans (diff_total n) ?_
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_natCast_nonneg n
  have hl2 : Real.log (n : ℝ) ≤ Real.log (2 * (n : ℝ)) :=
    Real.log_le_log (by linarith) (by linarith)
  have hs : (Nat.sqrt n : ℝ) ≤ Real.sqrt (n : ℝ) := Real.nat_sqrt_le_real_sqrt
  have hs0 : (0 : ℝ) ≤ (Nat.sqrt n : ℝ) := Nat.cast_nonneg _
  have hL := log2_le n (by omega)
  have hL0 : (0 : ℝ) ≤ (Nat.log 2 n : ℝ) := Nat.cast_nonneg _
  push_cast
  have h1 : (Nat.sqrt n : ℝ) * (Nat.log 2 n : ℝ) ≤ Real.sqrt (n : ℝ) * (2 * Real.log (2 * (n : ℝ))) :=
    mul_le_mul hs (by linarith) hL0 (Real.sqrt_nonneg _)
  have h2 : 0 ≤ Real.log (2 * (n : ℝ)) := hlog.trans hl2
  have h3 := Real.sqrt_nonneg (n : ℝ)
  calc (Nat.sqrt n : ℝ) * (Nat.log 2 n : ℝ) * Real.log (n : ℝ)
      ≤ (Real.sqrt (n : ℝ) * (2 * Real.log (2 * (n : ℝ)))) * Real.log (2 * (n : ℝ)) :=
        mul_le_mul h1 hl2 hlog (by positivity)
    _ = 2 * Real.sqrt (n:ℝ) * (Real.log (2 * (n:ℝ)))^2 := by ring


private lemma gnn (k : ℕ) : 0 ≤ ArithmeticFunction.vonMangoldt k - (if k.Prime then Real.log (k:ℝ) else 0) := by
  by_cases hp : k.Prime
  · simp only [if_pos hp, ArithmeticFunction.vonMangoldt_apply_prime hp]; simp
  · simp only [if_neg hp, sub_zero]; exact ArithmeticFunction.vonMangoldt_nonneg

private lemma glog (k n : ℕ) (hk : k ≤ n) :
    ArithmeticFunction.vonMangoldt k - (if k.Prime then Real.log (k:ℝ) else 0) ≤ Real.log (n:ℝ) := by
  have h1 : (if k.Prime then Real.log (k:ℝ) else 0) ≥ 0 := by
    split_ifs with hp
    · exact Real.log_natCast_nonneg k
    · exact le_refl _
  by_cases hk0 : k = 0
  · subst hk0; simp [Real.log_natCast_nonneg]
  · have : Real.log (k:ℝ) ≤ Real.log (n:ℝ) :=
      Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hk0) (by exact_mod_cast hk)
    have h2 := ArithmeticFunction.vonMangoldt_le_log (n := k)
    linarith

private lemma fiber_sum (g : ℕ → ℝ) (n q : ℕ) (hq : 0 < q) :
    ∑ r ∈ Finset.range q, ∑ k ∈ (Finset.range (n+1)).filter (fun k => k % q = r), g k
      = ∑ k ∈ Finset.range (n+1), g k :=
  Finset.sum_fiberwise_of_maps_to (fun k _ => Finset.mem_range.2 (Nat.mod_lt k hq)) g

private lemma card_cls (n q r : ℕ) (hq : 0 < q) :
    ((Finset.range (n+1)).filter (fun k => k % q = r)).card ≤ n / q + 1 := by
  have := Finset.card_le_card_of_injOn (s := (Finset.range (n+1)).filter (fun k => k % q = r))
    (t := Finset.range (n / q + 1)) (fun k => k / q)
    (by
      intro k hk
      have hk := Finset.mem_filter.1 (Finset.mem_coe.1 hk)
      simp only [Finset.mem_range, Finset.coe_range, Set.mem_Iio] at hk ⊢
      have : k / q ≤ n / q := Nat.div_le_div_right (by omega)
      omega)
    (by
      intro a ha b hb hab
      have ha := Finset.mem_filter.1 (Finset.mem_coe.1 ha)
      have hb := Finset.mem_filter.1 (Finset.mem_coe.1 hb)
      have h1 := Nat.div_add_mod a q
      have h2 := Nat.div_add_mod b q
      simp only at hab
      rw [hab] at h1
      rw [ha.2] at h1
      rw [hb.2] at h2
      omega)
  simpa using this

private lemma block_bound (g : ℕ → ℝ) (n q : ℕ) (hq : 0 < q) (T : ℝ) (L : ℕ)
    (hg0 : ∀ k, 0 ≤ g k) (hgM : ∀ k, k ≤ n → g k ≤ Real.log (n:ℝ))
    (hT : ∑ k ∈ Finset.range (n+1), g k ≤ T) (hL : n / q + 1 ≤ L) :
    ∑ r ∈ Finset.range q, (∑ k ∈ (Finset.range (n+1)).filter (fun k => k % q = r), g k)^2
      ≤ (L:ℝ) * Real.log (n:ℝ) * T := by
  have hlog : 0 ≤ Real.log (n:ℝ) := Real.log_natCast_nonneg n
  have hM : 0 ≤ (L:ℝ) * Real.log (n:ℝ) := by positivity
  have hS0 : ∀ r, 0 ≤ ∑ k ∈ (Finset.range (n+1)).filter (fun k => k % q = r), g k :=
    fun r => Finset.sum_nonneg (fun k _ => hg0 k)
  have hSM : ∀ r, ∑ k ∈ (Finset.range (n+1)).filter (fun k => k % q = r), g k
      ≤ (L:ℝ) * Real.log (n:ℝ) := by
    intro r
    have h1 : ∑ k ∈ (Finset.range (n+1)).filter (fun k => k % q = r), g k
        ≤ ((Finset.range (n+1)).filter (fun k => k % q = r)).card • Real.log (n:ℝ) := by
      apply Finset.sum_le_card_nsmul
      intro k hk
      simp only [Finset.mem_filter, Finset.mem_range] at hk
      exact hgM k (by omega)
    rw [nsmul_eq_mul] at h1
    have h2 : (((Finset.range (n+1)).filter (fun k => k % q = r)).card : ℝ) ≤ (L:ℝ) := by
      exact_mod_cast (card_cls n q r hq).trans hL
    calc _ ≤ _ := h1
      _ ≤ _ := mul_le_mul_of_nonneg_right h2 hlog
  calc ∑ r ∈ Finset.range q, (∑ k ∈ (Finset.range (n+1)).filter (fun k => k % q = r), g k)^2
      ≤ ∑ r ∈ Finset.range q, ((L:ℝ) * Real.log (n:ℝ)) *
          (∑ k ∈ (Finset.range (n+1)).filter (fun k => k % q = r), g k) := by
        apply Finset.sum_le_sum
        intro r _
        rw [sq]
        exact mul_le_mul_of_nonneg_right (hSM r) (hS0 r)
    _ = ((L:ℝ) * Real.log (n:ℝ)) * ∑ k ∈ Finset.range (n+1), g k := by
        rw [← Finset.mul_sum, fiber_sum g n q hq]
    _ ≤ _ := mul_le_mul_of_nonneg_left hT hM

private lemma companion_aux : ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
    ∑ k ∈ Finset.range (n+1), (ArithmeticFunction.vonMangoldt k - (if k.Prime then Real.log (k:ℝ) else 0))
      ≤ C * Real.sqrt (n:ℝ) * (Real.log (2*(n:ℝ)))^2 :=
  ⟨2, by norm_num, fun n hn => total_bound n hn⟩

private lemma log_poly_small (K : ℝ) (hK : 0 < K) :
    ∃ X : ℕ, ∀ n : ℕ, X ≤ n → K * (Real.log (n:ℝ))^11 ≤ Real.sqrt (n:ℝ) := by
  have h := (Real.isLittleO_pow_log_id_atTop (n := 22)).bound (c := 1 / K^2) (by positivity)
  have h2 := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually h
  have h3 := h2.and (Filter.eventually_ge_atTop 1)
  obtain ⟨X, hX⟩ := Filter.eventually_atTop.1 h3
  refine ⟨X, fun n hn => ?_⟩
  obtain ⟨hb, hn1⟩ := hX n hn
  have hn0 : (0:ℝ) ≤ n := Nat.cast_nonneg n
  simp only [id, Real.norm_eq_abs] at hb
  rw [abs_of_nonneg hn0] at hb
  have hev : Even 22 := by decide
  rw [abs_of_nonneg (hev.pow_nonneg _)] at hb
  apply Real.le_sqrt_of_sq_le
  have : (K * Real.log (n:ℝ) ^ 11)^2 = K^2 * Real.log (n:ℝ) ^ 22 := by ring
  rw [this]
  have hK2 : 0 < K^2 := by positivity
  calc (K^2 * Real.log (n:ℝ) ^ 22 : ℝ) ≤ K^2 * (1 / K^2 * (n:ℝ)) := by gcongr
    _ = (n:ℝ) := by field_simp

private lemma final_bound (C : ℝ) (hC : 0 < C) :
    ∃ X : ℕ, ∀ n : ℕ, X ≤ n →
      ((Nat.log 2 n : ℕ) : ℝ)^8 * Real.log (n:ℝ) * (C * Real.sqrt (n:ℝ) * (Real.log (2*(n:ℝ)))^2)
        ≤ (n:ℝ) := by
  obtain ⟨X, hX⟩ := log_poly_small (C * 2^8 * 4) (by positivity)
  refine ⟨max X 2, fun n hn => ?_⟩
  have hn2 : 2 ≤ n := le_trans (le_max_right _ _) hn
  have hnX : X ≤ n := le_trans (le_max_left _ _) hn
  have hs := hX n hnX
  have hn1 : (2:ℝ) ≤ n := by exact_mod_cast hn2
  have hlog : 0 ≤ Real.log (n:ℝ) := Real.log_natCast_nonneg n
  have hL := log2_le n (by omega)
  have hL0 : (0 : ℝ) ≤ (Nat.log 2 n : ℝ) := Nat.cast_nonneg _
  have hl2 : Real.log (2 * (n:ℝ)) ≤ 2 * Real.log (n:ℝ) := by
    rw [Real.log_mul (by norm_num) (by linarith)]
    have : Real.log 2 ≤ Real.log (n:ℝ) := Real.log_le_log (by norm_num) hn1
    linarith
  have hl2' : 0 ≤ Real.log (2 * (n:ℝ)) := Real.log_nonneg (by linarith)
  have hsq := Real.sqrt_nonneg (n:ℝ)
  have hss : Real.sqrt (n:ℝ) * Real.sqrt (n:ℝ) = n := Real.mul_self_sqrt (by linarith)
  have h8 : ((Nat.log 2 n : ℕ) : ℝ)^8 ≤ (2 * Real.log (n:ℝ))^8 := by gcongr
  have h9 : (Real.log (2 * (n:ℝ)))^2 ≤ (2 * Real.log (n:ℝ))^2 := by gcongr
  have key : ((Nat.log 2 n : ℕ) : ℝ)^8 * Real.log (n:ℝ) * (C * (Real.log (2*(n:ℝ)))^2)
      ≤ C * 2^8 * 4 * Real.log (n:ℝ) ^ 11 := by
    calc _ ≤ (2 * Real.log (n:ℝ))^8 * Real.log (n:ℝ) * (C * (2 * Real.log (n:ℝ))^2) := by gcongr
      _ = _ := by ring
  calc ((Nat.log 2 n : ℕ) : ℝ)^8 * Real.log (n:ℝ) * (C * Real.sqrt (n:ℝ) * (Real.log (2*(n:ℝ)))^2)
      = Real.sqrt (n:ℝ) * (((Nat.log 2 n : ℕ) : ℝ)^8 * Real.log (n:ℝ) * (C * (Real.log (2*(n:ℝ)))^2)) := by ring
    _ ≤ Real.sqrt (n:ℝ) * Real.sqrt (n:ℝ) := mul_le_mul_of_nonneg_left (key.trans hs) hsq
    _ = n := hss

theorem PEqualNP.Outside.L_goldbach_coset_sparse_power_block :
    let F := fun n q r : ℕ => (Finset.range (n+1)).filter (fun k => k % q=r); let w := fun k : ℕ => if k.Prime then Real.log (k:ℝ) else 0; let A := fun n q r : ℕ => ∑ k ∈ F n q r, w k; let Q := fun n : ℕ => n/(Nat.log 2 n)^8; ∃ X : ℕ, ∀ n≥X, (∑ q ∈ Finset.Ioc (Q n) (2*Q n), ∑ r ∈ Finset.range q, ((∑ k ∈ F n q r, ArithmeticFunction.vonMangoldt k)-A n q r)^2) ≤ (n:ℝ)*(Q n:ℝ) := by
  intro F w A Q
  obtain ⟨C, hC, hcomp⟩ := companion_aux
  obtain ⟨X, hX⟩ := final_bound C hC
  refine ⟨max X 2, fun n hn => ?_⟩
  have hn2 : 2 ≤ n := le_trans (le_max_right _ _) hn
  have hnX : X ≤ n := le_trans (le_max_left _ _) hn
  have hfin := hX n hnX
  set L := Nat.log 2 n with hLdef
  have hL1 : 1 ≤ L := Nat.log_pos (by norm_num) hn2
  have hLpos : 0 < L ^ 8 := by positivity
  have hterm : ∀ q ∈ Finset.Ioc (Q n) (2 * Q n),
      ∑ r ∈ Finset.range q, ((∑ k ∈ F n q r, ArithmeticFunction.vonMangoldt k) - A n q r)^2
        ≤ ((L:ℝ)^8 * Real.log (n:ℝ) * (C * Real.sqrt (n:ℝ) * (Real.log (2*(n:ℝ)))^2)) := by
    intro q hq
    rw [Finset.mem_Ioc] at hq
    have hq0 : 0 < q := by omega
    have hlt : n < L^8 * q := by
      have h1 : n < L^8 * (n / L^8 + 1) := by
        have := Nat.div_add_mod n (L^8)
        have := Nat.mod_lt n hLpos
        nlinarith
      have h2 : L^8 * (n / L^8 + 1) ≤ L^8 * q := Nat.mul_le_mul_left _ (by simpa [Q] using hq.1)
      omega
    have hdiv : n / q + 1 ≤ L^8 := by
      have : n / q < L^8 := by
        rw [Nat.div_lt_iff_lt_mul hq0]; linarith [mul_comm (L^8) q]
      omega
    have := block_bound (fun k => ArithmeticFunction.vonMangoldt k - (if k.Prime then Real.log (k:ℝ) else 0))
      n q hq0 (C * Real.sqrt (n:ℝ) * (Real.log (2*(n:ℝ)))^2) (L^8) gnn (fun k hk => glog k n hk)
      (hcomp n hn2) hdiv
    simp only [Finset.sum_sub_distrib] at this
    push_cast at this
    simpa [F, A, w] using this
  calc _ ≤ ∑ q ∈ Finset.Ioc (Q n) (2 * Q n),
        ((L:ℝ)^8 * Real.log (n:ℝ) * (C * Real.sqrt (n:ℝ) * (Real.log (2*(n:ℝ)))^2)) :=
        Finset.sum_le_sum hterm
    _ = (Q n : ℝ) * ((L:ℝ)^8 * Real.log (n:ℝ) * (C * Real.sqrt (n:ℝ) * (Real.log (2*(n:ℝ)))^2)) := by
        rw [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul]
        congr 2
        push_cast
        have : 2 * Q n - Q n = Q n := by omega
        rw [this]
    _ ≤ (Q n : ℝ) * n := mul_le_mul_of_nonneg_left hfin (Nat.cast_nonneg _)
    _ = _ := mul_comm _ _
