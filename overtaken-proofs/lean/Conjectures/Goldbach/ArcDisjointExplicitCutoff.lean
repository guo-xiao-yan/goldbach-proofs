import Mathlib

private theorem arc_aux (k : ℕ) (hk : 19 ≤ k) : 2 * k ^ 4 + 3 ≤ 2 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have h1 : 19 ≤ k := hk
    have : 2 * (k + 1) ^ 4 + 3 ≤ 2 * (2 * k ^ 4 + 3) := by
      nlinarith [Nat.mul_le_mul h1 h1, pow_pos (show 0 < k by omega) 3, pow_pos (show 0 < k by omega) 2,
        pow_pos (show 0 < k by omega) 4]
    calc 2 * (k + 1) ^ 4 + 3 ≤ 2 * (2 * k ^ 4 + 3) := this
      _ ≤ 2 * 2 ^ k := by omega
      _ = 2 ^ (k + 1) := by ring

theorem Conjectures.Goldbach.ArcDisjointExplicitCutoff :
    ∀ n : ℕ, 1000000 ≤ n → 2 * ((Nat.log 2 (n + 2)) ^ 2) ^ 2 < n := by
  intro n hn
  have hk : 19 ≤ Nat.log 2 (n + 2) := by
    apply Nat.le_log_of_pow_le (by norm_num)
    norm_num; omega
  have h2 := arc_aux _ hk
  have h3 : 2 ^ Nat.log 2 (n + 2) ≤ n + 2 := Nat.pow_log_le_self 2 (by omega)
  have : ((Nat.log 2 (n + 2)) ^ 2) ^ 2 = Nat.log 2 (n + 2) ^ 4 := by ring
  rw [this]; omega
