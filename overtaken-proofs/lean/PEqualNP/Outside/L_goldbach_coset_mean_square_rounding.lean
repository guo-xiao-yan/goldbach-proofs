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

private theorem cosetCardLe (n q r : ℕ) (hq : 0 < q) :
    ((Finset.range (n+1)).filter (fun k => k % q = r)).card ≤ (n + 1) / q + 1 := by
  have h1 : ((Finset.range (n+1)).filter (fun k => k % q = r)).card ≤
      (Finset.range ((n + 1) / q + 1)).card := by
    apply Finset.card_le_card_of_injOn (fun k => k / q)
    · intro k hk
      have hk := Finset.mem_filter.mp (Finset.mem_coe.mp hk)
      simp only [Finset.coe_range, Set.mem_Iio, Finset.mem_range] at hk ⊢
      have : k / q ≤ (n + 1) / q := Nat.div_le_div_right (by omega)
      omega
    · intro k hk l hl h
      have hk := Finset.mem_filter.mp (Finset.mem_coe.mp hk)
      have hl := Finset.mem_filter.mp (Finset.mem_coe.mp hl)
      have h' : k / q = l / q := h
      have e1 := Nat.div_add_mod k q
      have e2 := Nat.div_add_mod l q
      rw [h', hk.2] at e1
      rw [hl.2] at e2
      omega
  simpa using h1

private theorem cosetCardDev (n q r : ℕ) (hq : 0 < q) (hr : r < q) :
    (((n + 1 : ℕ) : ℝ) - (((Finset.range (n+1)).filter (fun k => k % q = r)).card : ℝ) * q) ^ 2 ≤ (q:ℝ) ^ 2 := by
  have h1 := cosetCardGe n q r hq hr
  have h2 := cosetCardLe n q r hq
  have e1 := Nat.div_add_mod (n + 1) q
  have e2 : (n + 1) % q < q := Nat.mod_lt _ hq
  set c := ((Finset.range (n+1)).filter (fun k => k % q = r)).card with hc
  set m := (n + 1) / q with hm
  have a1 : m * q ≤ c * q := Nat.mul_le_mul_right q h1
  have a2 : c * q ≤ (m + 1) * q := Nat.mul_le_mul_right q h2
  have b1 : ((c * q : ℕ) : ℝ) ≤ (((m + 1) * q : ℕ) : ℝ) := by exact_mod_cast a2
  have b2 : ((m * q : ℕ) : ℝ) ≤ ((c * q : ℕ) : ℝ) := by exact_mod_cast a1
  have b3 : ((q * m + (n + 1) % q : ℕ) : ℝ) = ((n + 1 : ℕ) : ℝ) := by exact_mod_cast e1
  have b4 : (((n + 1) % q : ℕ) : ℝ) < q := by exact_mod_cast e2
  push_cast at b1 b2 b3 b4 ⊢
  have b5 : (0:ℝ) ≤ (((n + 1) % q : ℕ) : ℝ) := Nat.cast_nonneg _
  have hq' : (0:ℝ) < q := by exact_mod_cast hq
  apply sq_le_sq' <;> linarith

theorem PEqualNP.Outside.L_goldbach_coset_mean_square_rounding :
    let F := fun n q r : ℕ => (Finset.range (n+1)).filter (fun k => k % q=r); let w := fun k : ℕ => if k.Prime then Real.log (k:ℝ) else 0; let A := fun n q r : ℕ => ∑ k ∈ F n q r, w k; let μ := fun q r : ℕ => if r.Coprime q then (q:ℝ)/(q.totient:ℝ) else 0; let v := fun n q r : ℕ => A n q r-((F n q r).card:ℝ)*μ q r; ∀ n q : ℕ, 0<q → let t := fun r : ℕ => if r.Coprime q then ((n+1:ℕ):ℝ)/(q.totient:ℝ) else 0; (∑ r ∈ Finset.range q, (v n q r)^2) ≤ 2*(∑ r ∈ Finset.range q, (A n q r-t r)^2) + 2*((q:ℝ)/(q.totient:ℝ))^2*(q:ℝ) := by
  intro F w A μ v n q hq t
  have hφ : (0:ℝ) < (q.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq
  have hterm : ∀ r ∈ Finset.range q, (v n q r)^2 ≤ 2*(A n q r - t r)^2 + 2*((q:ℝ)/(q.totient:ℝ))^2 := by
    intro r hr
    have hrq : r < q := Finset.mem_range.mp hr
    have hd := cosetCardDev n q r hq hrq
    have key : (t r - ((F n q r).card:ℝ) * μ q r)^2 ≤ ((q:ℝ)/(q.totient:ℝ))^2 := by
      by_cases hco : r.Coprime q
      · have e1 : t r = ((n+1:ℕ):ℝ)/(q.totient:ℝ) := by simp only [t, if_pos hco]
        have e2 : μ q r = (q:ℝ)/(q.totient:ℝ) := by simp only [μ, if_pos hco]
        rw [e1, e2]
        have : ((n+1:ℕ):ℝ)/(q.totient:ℝ) - ((F n q r).card:ℝ) * ((q:ℝ)/(q.totient:ℝ))
            = (((n + 1 : ℕ) : ℝ) - ((F n q r).card : ℝ) * q) / (q.totient:ℝ) := by
          field_simp
        rw [this, div_pow, div_pow]
        exact div_le_div_of_nonneg_right hd (by positivity)
      · have e1 : t r = 0 := by simp only [t, if_neg hco]
        have e2 : μ q r = 0 := by simp only [μ, if_neg hco]
        rw [e1, e2]; simp; positivity
    have : v n q r = (A n q r - t r) + (t r - ((F n q r).card:ℝ) * μ q r) := by
      show A n q r - ((F n q r).card:ℝ) * μ q r = _
      ring
    rw [this]
    nlinarith [sq_nonneg ((A n q r - t r) - (t r - ((F n q r).card:ℝ) * μ q r))]
  calc (∑ r ∈ Finset.range q, (v n q r)^2)
      ≤ ∑ r ∈ Finset.range q, (2*(A n q r - t r)^2 + 2*((q:ℝ)/(q.totient:ℝ))^2) := Finset.sum_le_sum hterm
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring
