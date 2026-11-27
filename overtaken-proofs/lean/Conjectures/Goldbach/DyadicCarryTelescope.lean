import Mathlib

private lemma dy_mod_cases (t q : ℕ) (hq : 0 < q) :
    (t % (2 * q) < q ∧ t % q = t % (2 * q) ∧ (t + q) % (2 * q) = t % (2 * q) + q) ∨
    (q ≤ t % (2 * q) ∧ t % q = t % (2 * q) - q ∧ (t + q) % (2 * q) = t % (2 * q) - q) := by
  have hx : t % (2 * q) < 2 * q := Nat.mod_lt _ (by omega)
  have hxq : t % (2 * q) % q = t % q := Nat.mod_mod_of_dvd t (Dvd.intro_left 2 rfl)
  have hadd : (t + q) % (2 * q) = (t % (2 * q) + q) % (2 * q) := by
    rw [Nat.add_mod, Nat.mod_eq_of_lt (show q < 2 * q by omega)]
  by_cases h : t % (2 * q) < q
  · left
    refine ⟨h, ?_, ?_⟩
    · rw [← hxq, Nat.mod_eq_of_lt h]
    · rw [hadd, Nat.mod_eq_of_lt (by omega)]
  · right
    push_neg at h
    refine ⟨h, ?_, ?_⟩
    · rw [← hxq, Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]
    · rw [hadd]
      generalize t % (2 * q) = x at *
      rw [Nat.mod_eq_sub_mod (by omega), show x + q - 2 * q = x - q by omega]
      exact Nat.mod_eq_of_lt (by omega)

private lemma dy_nat_facts (N q r : ℕ) (hq : 0 < q) (hr : r < q) :
    ((N + 2 * q - r) % (2 * q) < q ∧ (N + 2 * q - r) % (2 * q) = (N + q - r) % q ∧
      (N + 2 * q - (r + q)) % (2 * q) = (N + q - r) % q + q) ∨
    (q ≤ (N + 2 * q - r) % (2 * q) ∧ (N + 2 * q - r) % (2 * q) = (N + q - r) % q + q ∧
      (N + 2 * q - (r + q)) % (2 * q) = (N + q - r) % q) := by
  have h1 : N + 2 * q - r = (N + q - r) + q := by omega
  have h2 : N + 2 * q - (r + q) = N + q - r := by omega
  rw [h1, h2]
  generalize N + q - r = t
  have hx : t % (2 * q) < 2 * q := Nat.mod_lt _ (by omega)
  rcases dy_mod_cases t q hq with ⟨a, b, c⟩ | ⟨a, b, c⟩
  · right
    refine ⟨by omega, by omega, by omega⟩
  · left
    refine ⟨by omega, by omega, by omega⟩

private lemma dy_split (N q : ℕ) (w : ℕ → ℝ) (hq : 0 < q) (r : ℕ) (hr : r < q) :
    (∑ n ∈ (Finset.range (N+1)).filter (fun n => n % q = r), w n) =
    (∑ n ∈ (Finset.range (N+1)).filter (fun n => n % (2 * q) = r), w n) +
    (∑ n ∈ (Finset.range (N+1)).filter (fun n => n % (2 * q) = r + q), w n) := by
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  rcases dy_mod_cases n q hq with ⟨a, b, c⟩ | ⟨a, b, c⟩
  · by_cases h : n % q = r
    · rw [if_pos h, if_pos (by omega), if_neg (by omega)]; ring
    · rw [if_neg h, if_neg (by omega), if_neg (by omega)]; ring
  · by_cases h : n % q = r
    · rw [if_pos h, if_neg (by omega), if_pos (by omega)]; ring
    · rw [if_neg h, if_neg (by omega), if_neg (by omega)]; ring

private lemma dy_level_sum (A2 : ℕ → ℝ) (N q : ℕ) (hq : 0 < q) :
    2 * (∑ x ∈ Finset.range (2 * q), A2 x * A2 ((N + 2 * q - x) % (2 * q))) -
      ∑ r ∈ Finset.range q, (A2 r + A2 (r + q)) * (A2 ((N + q - r) % q) + A2 ((N + q - r) % q + q)) =
    ∑ r ∈ Finset.range q,
      (if (N + 2 * q - r) % (2 * q) < q then (1 : ℝ) else -1) * (A2 r - A2 (r + q)) *
        (A2 ((N + q - r) % q) - A2 ((N + q - r) % q + q)) := by
  have hs : ∀ f : ℕ → ℝ, ∑ x ∈ Finset.range (2 * q), f x =
      ∑ r ∈ Finset.range q, (f r + f (q + r)) := by
    intro f
    rw [two_mul, Finset.sum_range_add, Finset.sum_add_distrib]
  rw [hs (fun x => A2 x * A2 ((N + 2 * q - x) % (2 * q))), Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun r hr => ?_
  have hr' := Finset.mem_range.mp hr
  simp only [add_comm q r]
  rcases dy_nat_facts N q r hq hr' with ⟨a, b, c⟩ | ⟨a, b, c⟩
  · rw [if_pos a, b, c]; ring
  · rw [if_neg (by omega), b, c]; ring

private lemma dy_level (N q : ℕ) (hq : 0 < q) (M : ℝ) (A : ℕ → ℕ → ℝ)
    (hs : ∀ r, r < q → A q r = A (2 * q) r + A (2 * q) (r + q)) :
    (((2 * q : ℕ) : ℝ) / M * ∑ r ∈ Finset.range (2 * q), A (2 * q) r * A (2 * q) ((N + 2 * q - r) % (2 * q))) -
      ((q : ℕ) : ℝ) / M * ∑ r ∈ Finset.range q, A q r * A q ((N + q - r) % q) =
    (q : ℝ) / M * ∑ r ∈ Finset.range q,
      (if (N + 2 * q - r) % (2 * q) < q then (1 : ℝ) else -1) *
        (A (2 * q) r - A (2 * q) (r + q)) *
        (A (2 * q) ((N + q - r) % q) - A (2 * q) ((N + q - r) % q + q)) := by
  have h := dy_level_sum (A (2 * q)) N q hq
  have e : ∑ r ∈ Finset.range q, A q r * A q ((N + q - r) % q) =
      ∑ r ∈ Finset.range q, (A (2 * q) r + A (2 * q) (r + q)) *
        (A (2 * q) ((N + q - r) % q) + A (2 * q) ((N + q - r) % q + q)) := by
    refine Finset.sum_congr rfl fun r hr => ?_
    rw [hs r (Finset.mem_range.mp hr), hs _ (Nat.mod_lt _ hq)]
  rw [e, ← h]
  push_cast
  ring

theorem Conjectures.Goldbach.DyadicCarryTelescope :
    ∀ (N K : ℕ) (w : ℕ → ℝ), N < 2^K →
  let M : ℕ := 2^K
  let A := fun (d r : ℕ) => ∑ n ∈ (Finset.range (N+1)).filter (fun n => n % d = r), w n
  let C := fun k : ℕ =>
    let q : ℕ := 2^k
    let D := fun r : ℕ => A (2*q) r - A (2*q) (r+q)
    (q : ℝ) / M * ∑ r ∈ Finset.range q,
      (if (N+2*q-r)%(2*q) < q then (1 : ℝ) else -1) * D r * D ((N+q-r)%q)
  (∑ n ∈ Finset.range (N+1), w n * w (N-n)) =
    (∑ n ∈ Finset.range (N+1), w n)^2 / M + ∑ k ∈ Finset.range K, C k := by
  intro N K w hN M A C
  have hM : (0 : ℝ) < M := by positivity
  let T : ℕ → ℝ := fun m =>
    (m : ℝ) / M * ∑ r ∈ Finset.range m, A m r * A m ((N + m - r) % m)
  have htel : ∀ j, j ≤ K → T (2 ^ j) - T 1 = ∑ k ∈ Finset.range j, C k := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      have h1 := ih (by omega)
      have h2 := dy_level N (2 ^ j) (by positivity) (M : ℝ) A
        (fun r hr => dy_split N (2 ^ j) w (by positivity) r hr)
      rw [Finset.sum_range_succ, ← h1]
      have e : T (2 ^ (j + 1)) = T (2 * 2 ^ j) := by rw [pow_succ']
      rw [e]
      have : T (2 * 2 ^ j) - T (2 ^ j) = C j := h2
      linarith
  have hT1 : T 1 = (∑ n ∈ Finset.range (N+1), w n)^2 / M := by
    have : A 1 0 = ∑ n ∈ Finset.range (N+1), w n := by
      show ∑ n ∈ (Finset.range (N+1)).filter (fun n => n % 1 = 0), w n = _
      rw [Finset.filter_true_of_mem (fun n _ => Nat.mod_one n)]
    simp only [T, Finset.sum_range_one, Nat.cast_one, one_div]
    have h0 : (N + 1 - 0) % 1 = 0 := Nat.mod_one _
    rw [h0, this]
    ring
  have hg : ∀ r, A M r = if r ≤ N then w r else 0 := by
    intro r
    show ∑ n ∈ (Finset.range (N+1)).filter (fun n => n % 2 ^ K = r), w n = _
    have hf : (Finset.range (N+1)).filter (fun n => n % 2 ^ K = r) =
        (Finset.range (N+1)).filter (fun n => n = r) := by
      refine Finset.filter_congr fun n hn => ?_
      rw [Nat.mod_eq_of_lt (by have := Finset.mem_range.mp hn; omega)]
    rw [hf]
    by_cases h : r ≤ N
    · rw [if_pos h, Finset.filter_eq' ]
      simp [h, Nat.lt_succ_of_le h]
    · rw [if_neg h]
      apply Finset.sum_eq_zero
      intro n hn
      have := Finset.mem_filter.mp hn
      have := Finset.mem_range.mp this.1
      omega
  have hTM : T M = ∑ n ∈ Finset.range (N+1), w n * w (N-n) := by
    have hM1 : ((M : ℕ) : ℝ) / M = 1 := div_self hM.ne'
    simp only [T]
    rw [hM1, one_mul]
    have hterm : ∀ r ∈ Finset.range M, A M r * A M ((N + M - r) % M) =
        if r ≤ N then w r * w (N - r) else 0 := by
      intro r hr
      by_cases h : r ≤ N
      · have : (N + M - r) % M = N - r := by
          have : N + M - r = (N - r) + M := by omega
          rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        rw [this, hg, hg, if_pos h, if_pos (by omega), if_pos h]
      · rw [hg r, if_neg h, if_neg h, zero_mul]
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter]
    apply Finset.sum_congr
    · ext r
      simp only [Finset.mem_filter, Finset.mem_range]
      omega
    · intros; rfl
  have := htel K le_rfl
  have e : (2 ^ K) = M := rfl
  rw [e] at this
  linarith
