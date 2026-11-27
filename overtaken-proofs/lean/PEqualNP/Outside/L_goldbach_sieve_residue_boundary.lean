import Mathlib.Data.Nat.Periodic
import Mathlib.Data.Nat.Count
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

private theorem sieve_bd_step (p : ℕ → Prop) [DecidablePred p] (q : ℕ) (hp : Function.Periodic p q) (y : ℕ) :
    Nat.count p (y + q) = Nat.count p y + Nat.count p q := by
  rw [← Nat.filter_Ico_card_eq_of_periodic y q p hp]
  rw [Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range, Finset.range_eq_Ico, Finset.range_eq_Ico]
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    rw [← Finset.filter_union, Finset.Ico_union_Ico_eq_Ico (Nat.zero_le y) (Nat.le_add_right y q)]
  · refine Finset.disjoint_filter_filter ?_
    exact Finset.Ico_disjoint_Ico_consecutive 0 y (y + q)

private theorem sieve_bd_mul (p : ℕ → Prop) [DecidablePred p] (q : ℕ) (hp : Function.Periodic p q) (t : ℕ) :
    Nat.count p (q * t) = t * Nat.count p q := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Nat.mul_succ, sieve_bd_step p q hp, ih]
    ring

theorem PEqualNP.Outside.L_goldbach_sieve_residue_boundary :
    let r := fun n q : ℕ => ((Finset.range q).filter (fun k => q ∣ k*(k+n))).card; ∀ x n q : ℕ, 0<q → |((((Finset.range x).filter (fun k => q ∣ k*(k+n))).card : ℝ) - (x:ℝ)*(r n q:ℝ)/q)| ≤ (r n q:ℝ) := by
  intro r x n q hq
  have hper : Function.Periodic (fun k => q ∣ k*(k+n)) q := by
    intro k
    have h : (k+q)*((k+q)+n) = k*(k+n) + q*(2*k+q+n) := by ring
    apply propext
    show q ∣ (k+q)*((k+q)+n) ↔ q ∣ k*(k+n)
    rw [h]
    exact Nat.dvd_add_left (dvd_mul_right q _)
  have hc : ∀ y, ((Finset.range y).filter (fun k => q ∣ k*(k+n))).card = Nat.count (fun k => q ∣ k*(k+n)) y := by
    intro y
    rw [Nat.count_eq_card_filter_range]
  have hr : r n q = Nat.count (fun k => q ∣ k*(k+n)) q := hc q
  show |((((Finset.range x).filter (fun k => q ∣ k*(k+n))).card : ℝ) - (x:ℝ)*(r n q:ℝ)/q)| ≤ (r n q:ℝ)
  rw [hc x, hr]
  set R := Nat.count (fun k => q ∣ k*(k+n)) q with hR
  set t := x / q with ht
  set s := x % q with hs
  have hx : x = q * t + s := (Nat.div_add_mod x q).symm
  have hsq : s < q := Nat.mod_lt _ hq
  have hlo : t * R ≤ Nat.count (fun k => q ∣ k*(k+n)) x := by
    rw [← sieve_bd_mul _ q hper t]
    exact Nat.count_monotone _ (by omega)
  have hhi : Nat.count (fun k => q ∣ k*(k+n)) x ≤ (t + 1) * R := by
    have : Nat.count (fun k => q ∣ k*(k+n)) (q * (t + 1)) = (t + 1) * R :=
      sieve_bd_mul _ q hper (t + 1)
    rw [← this]
    exact Nat.count_monotone _ (by rw [Nat.mul_succ]; omega)
  have hqpos : (0:ℝ) < q := by exact_mod_cast hq
  have hxr : (x:ℝ) = q * t + s := by exact_mod_cast hx
  have hlo' : (t:ℝ) * R ≤ (Nat.count (fun k => q ∣ k*(k+n)) x : ℝ) := by exact_mod_cast hlo
  have hhi' : (Nat.count (fun k => q ∣ k*(k+n)) x : ℝ) ≤ ((t:ℝ) + 1) * R := by exact_mod_cast hhi
  have hs0 : (0:ℝ) ≤ s := Nat.cast_nonneg _
  have hs1 : (s:ℝ) ≤ q := by exact_mod_cast hsq.le
  have hR0 : (0:ℝ) ≤ R := Nat.cast_nonneg _
  have hdiv : (x:ℝ) * R / q = t * R + s * R / q := by
    rw [hxr]; field_simp
  have h1 : 0 ≤ (s:ℝ) * R / q := by positivity
  have h2 : (s:ℝ) * R / q ≤ R := by
    rw [div_le_iff₀ hqpos]; nlinarith
  rw [hdiv, abs_le]
  constructor <;> nlinarith
