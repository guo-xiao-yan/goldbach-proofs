import Mathlib

private lemma ratio_aux (p : ℕ) (hp : p.Prime) :
    (p : ℝ) / ((p : ℝ) - 1) ≤ (if p < 64 then (2:ℝ) else 1) * (p : ℝ) ^ (1/6 : ℝ) := by
  have hp2 : (2:ℝ) ≤ p := by exact_mod_cast hp.two_le
  have h1 : (1:ℝ) ≤ (p : ℝ) ^ (1/6 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  have h2 : (p : ℝ) / ((p : ℝ) - 1) ≤ 2 := by
    rw [div_le_iff₀ (by linarith)]; linarith
  split_ifs with h
  · nlinarith
  · push Not at h
    have h64 : (64:ℝ) ≤ p := by exact_mod_cast h
    have : (2:ℝ) ≤ (p : ℝ) ^ (1/6 : ℝ) := by
      calc (2:ℝ) = (64:ℝ) ^ (1/6 : ℝ) := by
            rw [show (64:ℝ) = 2 ^ (6:ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]; norm_num
        _ ≤ _ := Real.rpow_le_rpow (by norm_num) h64 (by norm_num)
    linarith

private lemma ratio_bound (q : ℕ) (hq : 1 ≤ q) :
    (q : ℝ) / (q.totient : ℝ) ≤ 2 ^ 64 * (q : ℝ) ^ (1/6 : ℝ) := by
  have hq0 : q ≠ 0 := by omega
  have hφ : (0:ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  have key := Nat.totient_mul_prod_primeFactors q
  have keyR : (q.totient : ℝ) * ∏ p ∈ q.primeFactors, (p : ℝ) = (q : ℝ) * ∏ p ∈ q.primeFactors, ((p : ℝ) - 1) := by
    have := congrArg (fun x : ℕ => (x : ℝ)) key
    simp only [Nat.cast_mul, Nat.cast_prod] at this
    rw [this]
    congr 1
    apply Finset.prod_congr rfl
    intro p hp
    have := (Nat.prime_of_mem_primeFactors hp).one_le
    rw [Nat.cast_sub this]; simp
  have hpos : ∀ p ∈ q.primeFactors, (0:ℝ) < (p : ℝ) - 1 := by
    intro p hp
    have := (Nat.prime_of_mem_primeFactors hp).two_le
    have : (2:ℝ) ≤ p := by exact_mod_cast this
    linarith
  have hP : 0 < ∏ p ∈ q.primeFactors, ((p : ℝ) - 1) := Finset.prod_pos hpos
  have hratio : (q : ℝ) / (q.totient : ℝ) = ∏ p ∈ q.primeFactors, ((p : ℝ) / ((p : ℝ) - 1)) := by
    rw [Finset.prod_div_distrib]
    have hP2 : 0 < ∏ p ∈ q.primeFactors, (p : ℝ) := Finset.prod_pos (fun p hp => by
      have := (Nat.prime_of_mem_primeFactors hp).pos; exact_mod_cast this)
    rw [div_eq_div_iff hφ.ne' hP.ne']
    rw [mul_comm (q:ℝ)]
    linarith [keyR]
  rw [hratio]
  calc ∏ p ∈ q.primeFactors, ((p : ℝ) / ((p : ℝ) - 1))
      ≤ ∏ p ∈ q.primeFactors, ((if p < 64 then (2:ℝ) else 1) * (p : ℝ) ^ (1/6 : ℝ)) := by
        refine Finset.prod_le_prod₀ ?_ ?_
        · intro p hp
          have h1 := hpos p hp
          have h2 : (0:ℝ) < p := by have := (Nat.prime_of_mem_primeFactors hp).pos; exact_mod_cast this
          exact (div_pos h2 h1).le
        · intro p hp; exact ratio_aux p (Nat.prime_of_mem_primeFactors hp)
    _ = (∏ p ∈ q.primeFactors, (if p < 64 then (2:ℝ) else 1)) * ∏ p ∈ q.primeFactors, (p : ℝ) ^ (1/6 : ℝ) :=
        Finset.prod_mul_distrib
    _ ≤ 2 ^ 64 * (q : ℝ) ^ (1/6 : ℝ) := by
        apply mul_le_mul
        · rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
          apply pow_le_pow_right₀ (by norm_num)
          calc (q.primeFactors.filter (fun p => p < 64)).card ≤ (Finset.range 64).card := by
                apply Finset.card_le_card
                intro p hp
                simp only [Finset.mem_filter] at hp
                simpa using hp.2
            _ = 64 := by simp
        · rw [Real.finsetProd_rpow _ _ (fun p hp => by positivity)]
          apply Real.rpow_le_rpow (Finset.prod_nonneg (fun p hp => by positivity)) _ (by norm_num)
          have := Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd q)
          have h2 : ((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) ≤ q := by exact_mod_cast this
          simpa using h2
        · exact Finset.prod_nonneg (fun p hp => by positivity)
        · positivity

private lemma geom_id (z : ℂ) (n : ℕ) :
    (z - 1) * ∑ k ∈ Finset.Icc 1 n, z ^ k = z ^ (n+1) - z := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega), mul_add, ih]; ring

private lemma exp_sub_one_lower (β : ℝ) (h0 : 0 < |β|) (h1 : |β| ≤ 1/2) :
    4 * |β| ≤ ‖Complex.exp (((2 * Real.pi * β : ℝ) : ℂ) * Complex.I) - 1‖ := by
  have := Complex.norm_exp_I_mul_ofReal_sub_one (2 * Real.pi * β)
  rw [mul_comm ((((2 * Real.pi * β : ℝ)) : ℂ)) Complex.I, this]
  rw [Real.norm_eq_abs]
  have hs : 2 / Real.pi * (Real.pi * |β|) ≤ Real.sin (Real.pi * |β|) :=
    Real.mul_le_sin (by positivity) (by nlinarith [Real.pi_pos])
  have e : 2 * Real.pi * β / 2 = Real.pi * β := by ring
  rw [e]
  have : Real.sin (Real.pi * |β|) ≤ |Real.sin (Real.pi * β)| := by
    rcases abs_cases β with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]; exact le_abs_self _
    · rw [h, mul_neg, Real.sin_neg]; exact neg_le_abs _
  have e2 : 2 / Real.pi * (Real.pi * |β|) = 2 * |β| := by field_simp
  rw [abs_mul, abs_two]
  nlinarith

private lemma geom_bound (n : ℕ) (β : ℝ) (h0 : 0 < |β|) (h1 : |β| ≤ 1/2) :
    ‖∑ k ∈ Finset.Icc 1 n, Complex.exp ((((2 * Real.pi * ((k : ℝ) * β) : ℝ)) : ℂ) * Complex.I)‖
      ≤ 1 / (2 * |β|) := by
  set z : ℂ := Complex.exp (((2 * Real.pi * β : ℝ) : ℂ) * Complex.I) with hz
  have hk : ∀ k : ℕ, Complex.exp ((((2 * Real.pi * ((k : ℝ) * β) : ℝ)) : ℂ) * Complex.I) = z ^ k := by
    intro k
    rw [hz, ← Complex.exp_nat_mul]
    congr 1
    push_cast; ring
  simp_rw [hk]
  have hl := exp_sub_one_lower β h0 h1
  have hz1 : ‖z‖ = 1 := by
    rw [hz]; exact Complex.norm_exp_ofReal_mul_I _
  have hid := geom_id z n
  have hnorm : ‖z - 1‖ * ‖∑ k ∈ Finset.Icc 1 n, z ^ k‖ ≤ 2 := by
    rw [← norm_mul, hid]
    calc ‖z ^ (n+1) - z‖ ≤ ‖z^(n+1)‖ + ‖z‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, hz1]; norm_num
  have hp : 0 < 4 * |β| := by positivity
  rw [div_eq_mul_inv, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  nlinarith [norm_nonneg (∑ k ∈ Finset.Icc 1 n, z ^ k), norm_nonneg (z - 1)]

private lemma dirichlet_sqrt (N : ℕ) (hN : 4 ≤ N) (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) :
    ∃ q a : ℕ, 1 ≤ q ∧ (q : ℝ) ≤ Real.sqrt N ∧ a ≤ q ∧ Nat.Coprime a q ∧
      |t - (a : ℝ) / (q : ℝ)| ≤ 1 / ((q : ℝ) * Real.sqrt N) := by
  obtain ⟨ht0, ht1⟩ := ht
  set M := ⌊Real.sqrt N⌋₊ with hM
  have hsq : (2:ℝ) ≤ Real.sqrt N := by
    rw [show (2:ℝ) = Real.sqrt 4 by
      rw [show (4:ℝ) = 2^2 by norm_num]; exact (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hN)
  have hMpos : 0 < M := by
    rw [hM]; exact Nat.floor_pos.mpr (by linarith)
  have hMle : (M : ℝ) ≤ Real.sqrt N := Nat.floor_le (by positivity)
  have hMlt : Real.sqrt N < (M : ℝ) + 1 := Nat.lt_floor_add_one _
  obtain ⟨q', hq', hden⟩ := Real.exists_rat_abs_sub_le_and_den_le t (n := M) hMpos
  set d := q'.den with hd
  set m := q'.num with hm
  have hdpos : 0 < d := q'.den_pos
  have hdR : (0 : ℝ) < d := by exact_mod_cast hdpos
  have hqr : (q' : ℝ) = (m : ℝ) / d := by rw [Rat.cast_def]
  rw [hqr] at hq'
  have hdM : (d : ℝ) ≤ M := by exact_mod_cast hden
  have hsqpos : 0 < Real.sqrt N := by linarith
  have hfin : |t - (m : ℝ) / d| ≤ 1 / ((d : ℝ) * Real.sqrt N) := by
    refine le_trans hq' ?_
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  have hb : |t * d - m| ≤ 1 / 2 := by
    have : t * d - m = d * (t - m / d) := by field_simp
    rw [this, abs_mul, abs_of_pos hdR]
    calc (d : ℝ) * |t - m / d| ≤ d * (1 / ((d : ℝ) * Real.sqrt N)) :=
          mul_le_mul_of_nonneg_left hfin hdR.le
      _ = 1 / Real.sqrt N := by field_simp
      _ ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hsq
  have hb' := abs_le.mp hb
  have htd0 : 0 ≤ t * d := by positivity
  have htd1 : t * d ≤ d := by nlinarith
  have hm0 : 0 ≤ m := by
    by_contra h
    push Not at h
    have : (m : ℝ) ≤ -1 := by exact_mod_cast (by omega : m ≤ -1)
    linarith
  have hmd : m ≤ d := by
    by_contra h
    push Not at h
    have : (d : ℝ) + 1 ≤ m := by exact_mod_cast (by omega : (d : ℤ) + 1 ≤ m)
    linarith
  have hmcast : ((m.toNat : ℕ) : ℝ) = (m : ℝ) := by
    have : ((m.toNat : ℕ) : ℤ) = m := Int.toNat_of_nonneg hm0
    exact_mod_cast this
  have hcop : Nat.Coprime m.toNat d := by
    have h5 : m.toNat = m.natAbs := by omega
    rw [h5]
    exact q'.reduced
  have hmle : m.toNat ≤ d := by omega
  refine ⟨d, m.toNat, hdpos, by linarith, hmle, hcop, ?_⟩
  rw [hmcast]; exact hfin

private lemma main_real (n q Q₁ H : ℕ) (β x : ℝ) (hn : 8 ≤ n) (hq : 1 ≤ q)
    (hqn : (q : ℝ) ≤ Real.sqrt n) (hQ₁ : Q₁ = ⌊(n : ℝ) ^ (1/3 : ℝ)⌋₊) (hH : Q₁ ≤ H)
    (hcase : Q₁ < q ∨ (H : ℝ) < q * n * |β|) (hx0 : 0 ≤ x) (hxn : x ≤ n)
    (hxβ : 0 < |β| → x ≤ 1 / (2 * |β|)) :
    x / (q.totient : ℝ) ≤ 2 ^ 64 * (n : ℝ) ^ (3/4 : ℝ) := by
  have hnR : (8:ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0:ℝ) < n := by linarith
  set c : ℝ := (n : ℝ) ^ (1/3 : ℝ) with hc
  have hc3 : c ^ 3 = n := by
    rw [hc, ← Real.rpow_natCast, ← Real.rpow_mul hnpos.le]; norm_num
  have hc2 : (2:ℝ) ≤ c := by
    have h8 : (8:ℝ) ^ (1/3 : ℝ) = 2 := by
      rw [show (8:ℝ) = 2 ^ (3:ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]; norm_num
    calc (2:ℝ) = (8:ℝ) ^ (1/3 : ℝ) := h8.symm
      _ ≤ c := Real.rpow_le_rpow (by norm_num) hnR (by norm_num)
  have hcpos : 0 < c := by linarith
  have hQ1le : (Q₁ : ℝ) ≤ c := by rw [hQ₁]; exact Nat.floor_le hcpos.le
  have hQ1lt : c < (Q₁ : ℝ) + 1 := by rw [hQ₁]; exact Nat.lt_floor_add_one _
  have hqR : (1:ℝ) ≤ q := by exact_mod_cast hq
  have hqpos : (0:ℝ) < q := by linarith
  have hHR : (Q₁ : ℝ) ≤ H := by exact_mod_cast hH
  have hxq : x / q ≤ c ^ 2 := by
    rcases hcase with h | h
    · have h' : c < q := by
        have : (Q₁ : ℝ) + 1 ≤ q := by exact_mod_cast h
        linarith
      rw [div_le_iff₀ hqpos]
      have : n = c ^ 3 := hc3.symm
      calc x ≤ n := hxn
        _ = c ^ 2 * c := by rw [this]; ring
        _ ≤ c ^ 2 * q := by apply mul_le_mul_of_nonneg_left h'.le (by positivity)
    · have hβpos : 0 < |β| := by
        by_contra hh
        have : |β| = 0 := le_antisymm (not_lt.mp hh) (abs_nonneg _)
        rw [this] at h
        have : (0:ℝ) ≤ H := by positivity
        simp at h; linarith
      have h1 := hxβ hβpos
      have hHpos : (0:ℝ) < H := by linarith
      have h2 : c ≤ 2 * H := by linarith
      rw [div_le_iff₀ hqpos]
      have h3 : x * (2 * |β|) ≤ 1 := by
        have := mul_le_mul_of_nonneg_right h1 (by positivity : (0:ℝ) ≤ 2 * |β|)
        rwa [div_mul_cancel₀ _ (by positivity)] at this
      have h4 : (H : ℝ) * (2 * x) ≤ q * n * |β| * (2 * x) := by
        apply mul_le_mul_of_nonneg_right h.le (by positivity)
      have h5 : (H : ℝ) * (2 * x) ≤ q * n := by nlinarith
      have h6 : c * x ≤ q * n := by nlinarith
      have : n = c ^ 3 := hc3.symm
      rw [this] at h6
      have : c * (x) ≤ c * (c ^ 2 * q) := by nlinarith
      exact le_of_mul_le_mul_left this hcpos
  have hR := ratio_bound q hq
  have hqle : (q : ℝ) ^ (1/6 : ℝ) ≤ (n : ℝ) ^ (1/12 : ℝ) := by
    calc (q : ℝ) ^ (1/6 : ℝ) ≤ (Real.sqrt n) ^ (1/6 : ℝ) :=
          Real.rpow_le_rpow hqpos.le hqn (by norm_num)
      _ = (n : ℝ) ^ (1/12 : ℝ) := by
          rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hnpos.le]; norm_num
  have hφ : (0:ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  have e1 : x / (q.totient : ℝ) = ((q : ℝ) / (q.totient : ℝ)) * (x / q) := by
    field_simp
  have e2 : c ^ 2 = (n : ℝ) ^ (2/3 : ℝ) := by
    rw [hc, ← Real.rpow_natCast, ← Real.rpow_mul hnpos.le]; norm_num
  have e3 : (n : ℝ) ^ (3/4 : ℝ) = (n : ℝ) ^ (1/12 : ℝ) * (n : ℝ) ^ (2/3 : ℝ) := by
    rw [← Real.rpow_add hnpos]; norm_num
  rw [e1]
  have hx : 0 ≤ x / q := by positivity
  calc ((q : ℝ) / (q.totient : ℝ)) * (x / q) ≤ (2 ^ 64 * (n : ℝ) ^ (1/12 : ℝ)) * (c ^ 2) := by
        apply mul_le_mul _ hxq hx (by positivity)
        calc _ ≤ 2 ^ 64 * (q : ℝ) ^ (1/6 : ℝ) := hR
          _ ≤ _ := by gcongr
    _ = 2 ^ 64 * (n : ℝ) ^ (3/4 : ℝ) := by rw [e2, e3]; ring

private lemma err_real (n q : ℕ) (β K : ℝ) (hn : 8 ≤ n) (hq : 1 ≤ q) (hK : 0 < K)
    (hqn : (q : ℝ) ≤ Real.sqrt n) (hβ : |β| ≤ 1 / ((q : ℝ) * Real.sqrt n)) :
    K * (Real.sqrt ((q : ℝ) * n) * Real.log n * (Real.log n + Real.sqrt (n * |β|)))
      ≤ 2 * K * (Real.log n) ^ 2 * (n : ℝ) ^ (3/4 : ℝ) := by
  have hnR : (8:ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0:ℝ) < n := by linarith
  have hqR : (1:ℝ) ≤ q := by exact_mod_cast hq
  have hqpos : (0:ℝ) < q := by linarith
  have hL : 1 ≤ Real.log n := by
    have : Real.exp 1 ≤ 8 := by
      have := Real.exp_one_lt_d9; linarith
    calc (1:ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log n := Real.log_le_log (Real.exp_pos 1) (by linarith)
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnpos
  have hs2 : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hnpos.le
  have h34 : (n : ℝ) ^ (3/4 : ℝ) = (n:ℝ) / (n : ℝ) ^ (1/4 : ℝ) := by
    rw [eq_div_iff (by positivity), ← Real.rpow_add hnpos]; norm_num
  have hp : ((n : ℝ) ^ (3/4 : ℝ)) ^ 2 = n * Real.sqrt n := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hnpos.le, Real.sqrt_eq_rpow]
    rw [show (n:ℝ) * (n:ℝ) ^ (1/2:ℝ) = (n:ℝ) ^ (1:ℝ) * (n:ℝ) ^ (1/2:ℝ) by rw [Real.rpow_one],
      ← Real.rpow_add hnpos]
    norm_num
  have hA : Real.sqrt ((q : ℝ) * n) ≤ (n : ℝ) ^ (3/4 : ℝ) := by
    have : (q : ℝ) * n ≤ ((n : ℝ) ^ (3/4 : ℝ)) ^ 2 := by
      rw [hp, mul_comm (n:ℝ)]
      exact mul_le_mul_of_nonneg_right hqn hnpos.le
    calc Real.sqrt ((q : ℝ) * n) ≤ Real.sqrt (((n : ℝ) ^ (3/4 : ℝ)) ^ 2) := Real.sqrt_le_sqrt this
      _ = _ := Real.sqrt_sq (by positivity)
  have hB : Real.sqrt ((q : ℝ) * n) * Real.sqrt (n * |β|) ≤ (n : ℝ) ^ (3/4 : ℝ) := by
    rw [← Real.sqrt_mul (by positivity)]
    have h1 : (q : ℝ) * n * (n * |β|) ≤ ((n : ℝ) ^ (3/4 : ℝ)) ^ 2 := by
      have hqb : (q:ℝ) * |β| ≤ 1 / Real.sqrt n := by
        calc (q:ℝ) * |β| ≤ q * (1 / ((q : ℝ) * Real.sqrt n)) :=
              mul_le_mul_of_nonneg_left hβ hqpos.le
          _ = 1 / Real.sqrt n := by field_simp
      have : (q : ℝ) * n * (n * |β|) = n * n * ((q:ℝ) * |β|) := by ring
      rw [this]
      calc (n:ℝ) * n * ((q:ℝ) * |β|) ≤ n * n * (1 / Real.sqrt n) :=
            mul_le_mul_of_nonneg_left hqb (by positivity)
        _ = (n:ℝ) * Real.sqrt n := by
            field_simp; nlinarith
        _ = ((n : ℝ) ^ (3/4 : ℝ)) ^ 2 := hp.symm
    calc Real.sqrt ((q : ℝ) * n * (n * |β|)) ≤ Real.sqrt (((n : ℝ) ^ (3/4 : ℝ)) ^ 2) :=
          Real.sqrt_le_sqrt h1
      _ = _ := Real.sqrt_sq (by positivity)
  have hn34 : 0 < (n : ℝ) ^ (3/4 : ℝ) := by positivity
  set L := Real.log n
  set s1 := Real.sqrt ((q : ℝ) * n)
  set s2 := Real.sqrt (n * |β|)
  have hs1 : 0 ≤ s1 := Real.sqrt_nonneg _
  have hs2' : 0 ≤ s2 := Real.sqrt_nonneg _
  have : s1 * L * (L + s2) = L * (s1 * L) + L * (s1 * s2) := by ring
  have h5 : s1 * L * (L + s2) ≤ L * ((n:ℝ)^(3/4:ℝ) * L) + L * (n:ℝ)^(3/4:ℝ) := by
    rw [this]
    have := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ L)
    nlinarith [mul_le_mul_of_nonneg_left this (by linarith : 0 ≤ L),
      mul_le_mul_of_nonneg_left hB (by linarith : 0 ≤ L)]
  have hLL : L ≤ L ^ 2 := by nlinarith
  have h6 : s1 * L * (L + s2) ≤ 2 * L ^ 2 * (n:ℝ)^(3/4:ℝ) := by
    nlinarith [mul_le_mul_of_nonneg_right hLL hn34.le]
  nlinarith

theorem Conjectures.Goldbach.DeepThreeQuartersFromFareyError :
    let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (u : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (u k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let Q₁ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊; let H := fun n : ℕ => 256 * Q₁ n * Q n; let wideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q₁ n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))}; let I := fun (n : ℕ) (β : ℝ) => ∑ k ∈ Finset.Icc 1 n, E ((k : ℝ) * β); (∃ K : ℝ, 0 < K ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ a q : ℕ, 1 ≤ q → a ≤ q → a.Coprime q → (q : ℝ) ≤ Real.sqrt n → ∀ β : ℝ, |β| ≤ 1 / ((q : ℝ) * Real.sqrt n) → ‖S n w ((a : ℝ) / (q : ℝ) + β) - (ArithmeticFunction.moebius q : ℂ) / (q.totient : ℂ) * I n β‖ ≤ K * (Real.sqrt ((q : ℝ) * n) * Real.log n * (Real.log n + Real.sqrt (n * |β|)))) → ∀ η : ℝ, 0 < η → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ t ∈ Set.Icc (0 : ℝ) 1, t ∉ wideArcs n → ‖S n w t‖ ≤ (n : ℝ) ^ (3 / 4 + η) := by
  intro w E S Q Q₁ H wideArcs I hyp η hη
  obtain ⟨K, hK, N₀, hN₀⟩ := hyp
  have hI1 : ∀ (n : ℕ) (β : ℝ), ‖I n β‖ ≤ n := by
    intro n β
    show ‖∑ k ∈ Finset.Icc 1 n, Complex.exp ((((2 * Real.pi * ((k : ℝ) * β) : ℝ)) : ℂ) * Complex.I)‖ ≤ n
    refine le_trans (norm_sum_le _ _) ?_
    have : ∀ k ∈ Finset.Icc 1 n, ‖Complex.exp ((((2 * Real.pi * ((k : ℝ) * β) : ℝ)) : ℂ) * Complex.I)‖ = 1 :=
      fun k _ => Complex.norm_exp_ofReal_mul_I _
    rw [Finset.sum_congr rfl this]
    simp
  have hI2 : ∀ (n : ℕ) (β : ℝ), 0 < |β| → |β| ≤ 1 / 2 → ‖I n β‖ ≤ 1 / (2 * |β|) :=
    fun n β h0 h1 => geom_bound n β h0 h1
  have hQ1 : ∀ n : ℕ, Q₁ n = ⌊(n : ℝ) ^ (1/3 : ℝ)⌋₊ := fun n => rfl
  have hHle : ∀ n : ℕ, Q₁ n ≤ H n := by
    intro n
    have h1 : 1 ≤ Q n := by
      show 1 ≤ (Nat.log 2 (n+2))^2
      have : 1 ≤ Nat.log 2 (n+2) := Nat.log_pos (by norm_num) (by omega)
      nlinarith
    show Q₁ n ≤ 256 * Q₁ n * Q n
    nlinarith [Nat.zero_le (Q₁ n)]
  have hmem : ∀ (n : ℕ) (t : ℝ) (q a : ℕ), 1 ≤ q → q ≤ Q₁ n → a ≤ q → Nat.Coprime a q →
      |t - (a : ℝ) / (q : ℝ)| ≤ (H n : ℝ) / ((q : ℝ) * (n : ℝ)) → t ∈ wideArcs n :=
    fun n t q a h1 h2 h3 h4 h5 => ⟨q, a, h1, h2, h3, h4, h5⟩
  clear_value w E S Q Q₁ H wideArcs I
  have hη2 : 0 < η / 2 := by linarith
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = 2 ^ 64 := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = 32 * K / η ^ 2 := ⟨_, rfl⟩
  have hBpos : 0 < B := by rw [hB]; positivity
  have hApos : 0 < A := by rw [hA]; positivity
  have hev : ∀ᶠ n : ℕ in Filter.atTop, A + B + 1 ≤ (n : ℝ) ^ (η / 2) :=
    ((tendsto_rpow_atTop hη2).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop _
  obtain ⟨N1, hN1⟩ := Filter.eventually_atTop.mp hev
  refine ⟨max (max N₀ 8) N1, ?_⟩
  intro n hn t ht hnot
  have hnN₀ : N₀ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hn8 : 8 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hnN1 : N1 ≤ n := le_trans (le_max_right _ _) hn
  have hPn := hN1 n hnN1
  have hnR : (8:ℝ) ≤ n := by exact_mod_cast hn8
  have hnpos : (0:ℝ) < n := by linarith
  obtain ⟨q, a, hq1, hqn, haq, hcop, hβ⟩ := dirichlet_sqrt n (by omega) t ht
  set β : ℝ := t - (a : ℝ) / (q : ℝ) with hβdef
  have hqpos : (0:ℝ) < q := by exact_mod_cast hq1
  have hqR : (1:ℝ) ≤ q := by exact_mod_cast hq1
  have hsq2 : (2:ℝ) ≤ Real.sqrt n := by
    rw [show (2:ℝ) = Real.sqrt 4 by
      rw [show (4:ℝ) = 2^2 by norm_num]; exact (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by linarith)
  have hβ' : |β| ≤ 1 / ((q : ℝ) * Real.sqrt n) := hβ
  have hβhalf : |β| ≤ 1 / 2 := by
    refine le_trans hβ' ?_
    have : (2:ℝ) ≤ (q : ℝ) * Real.sqrt n := by
      have := mul_le_mul hqR hsq2 (by norm_num) (by linarith)
      linarith
    exact one_div_le_one_div_of_le (by norm_num) this
  have hS := hN₀ n hnN₀ a q hq1 haq hcop hqn β hβ'
  have htβ : (a : ℝ) / (q : ℝ) + β = t := by
    rw [hβdef]
    ring
  rw [htβ] at hS
  have hIn : ‖I n β‖ ≤ n := hI1 n β
  have hIβ : 0 < |β| → ‖I n β‖ ≤ 1 / (2 * |β|) := fun h0 => hI2 n β h0 hβhalf
  have hcase : Q₁ n < q ∨ (H n : ℝ) < q * n * |β| := by
    by_cases hqQ : Q₁ n < q
    · exact Or.inl hqQ
    · right
      push Not at hqQ
      by_contra hle
      push Not at hle
      apply hnot
      refine hmem n t q a hq1 hqQ haq hcop ?_
      have : |β| ≤ (H n : ℝ) / ((q : ℝ) * n) := by
        rw [le_div_iff₀ (by positivity), mul_comm]; exact hle
      exact this
  have hmain : ‖(ArithmeticFunction.moebius q : ℂ) / (q.totient : ℂ) * I n β‖ ≤ A * (n : ℝ) ^ (3/4 : ℝ) := by
    rw [hA]
    have hφ : (0:ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr (by omega)
    have hμ : ‖(ArithmeticFunction.moebius q : ℂ)‖ ≤ 1 := by
      have := ArithmeticFunction.abs_moebius_le_one (n := q)
      have h2 : ‖(ArithmeticFunction.moebius q : ℂ)‖ = |((ArithmeticFunction.moebius q : ℤ) : ℝ)| := by
        simp
      rw [h2]; exact_mod_cast this
    have h1 : ‖(ArithmeticFunction.moebius q : ℂ) / (q.totient : ℂ) * I n β‖
        ≤ ‖I n β‖ / (q.totient : ℝ) := by
      rw [norm_mul, norm_div, Complex.norm_natCast]
      rw [div_mul_eq_mul_div]
      apply div_le_div_of_nonneg_right _ hφ.le
      calc ‖(ArithmeticFunction.moebius q : ℂ)‖ * ‖I n β‖ ≤ 1 * ‖I n β‖ :=
            mul_le_mul_of_nonneg_right hμ (norm_nonneg _)
        _ = _ := one_mul _
    refine le_trans h1 ?_
    exact main_real n q (Q₁ n) (H n) β ‖I n β‖ hn8 hq1 hqn (hQ1 n) (hHle n)
      hcase (norm_nonneg _) hIn hIβ
  have herr := err_real n q β K hn8 hq1 hK hqn hβ'
  have herr2 : ‖S n w t - (ArithmeticFunction.moebius q : ℂ) / (q.totient : ℂ) * I n β‖
      ≤ 2 * K * (Real.log n) ^ 2 * (n : ℝ) ^ (3/4 : ℝ) := le_trans hS herr
  have hSn : ‖S n w t‖ ≤ A * (n : ℝ) ^ (3/4 : ℝ) + 2 * K * (Real.log n) ^ 2 * (n : ℝ) ^ (3/4 : ℝ) := by
    calc ‖S n w t‖ = ‖(S n w t - (ArithmeticFunction.moebius q : ℂ) / (q.totient : ℂ) * I n β)
          + (ArithmeticFunction.moebius q : ℂ) / (q.totient : ℂ) * I n β‖ := by congr 1; ring
      _ ≤ _ := norm_add_le _ _
      _ ≤ _ := by linarith
  have hlog : (Real.log n) ^ 2 ≤ 16 / η ^ 2 * (n : ℝ) ^ (η / 2) := by
    have h := Real.log_le_rpow_div hnpos.le (show 0 < η / 4 by linarith)
    have hL0 : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
    have h2 : (Real.log n) ^ 2 ≤ ((n : ℝ) ^ (η / 4) / (η / 4)) ^ 2 := by gcongr
    refine le_trans h2 ?_
    have e : ((n : ℝ) ^ (η / 4)) ^ 2 = (n : ℝ) ^ (η / 2) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hnpos.le]; congr 1; push_cast; ring
    rw [div_pow, e]
    apply le_of_eq
    field_simp; ring
  obtain ⟨P, hP⟩ : ∃ P : ℝ, P = (n : ℝ) ^ (η / 2) := ⟨_, rfl⟩
  rw [← hP] at hlog hPn
  have hP1 : 1 ≤ P := by linarith
  have hn34 : 0 < (n : ℝ) ^ (3/4 : ℝ) := by positivity
  have hfinal : (n : ℝ) ^ (3 / 4 + η) = (n : ℝ) ^ (3/4 : ℝ) * (P * P) := by
    rw [hP, ← Real.rpow_add hnpos, ← Real.rpow_add hnpos]; congr 1; ring
  rw [hfinal]
  have hK2 : 2 * K * (Real.log n) ^ 2 ≤ B * P := by
    calc 2 * K * (Real.log n) ^ 2 ≤ 2 * K * (16 / η ^ 2 * P) :=
          mul_le_mul_of_nonneg_left hlog (by positivity)
      _ = B * P := by rw [hB]; field_simp; ring
  have hAB : A + B * P ≤ P * P := by
    have h1 : A ≤ A * P := le_mul_of_one_le_right hApos.le hP1
    have h2 : (A + B + 1) * P ≤ P * P := mul_le_mul_of_nonneg_right hPn (by linarith)
    linarith
  calc ‖S n w t‖ ≤ (A + 2 * K * (Real.log n) ^ 2) * (n : ℝ) ^ (3/4 : ℝ) := by
        linarith
    _ ≤ (A + B * P) * (n : ℝ) ^ (3/4 : ℝ) := by
        apply mul_le_mul_of_nonneg_right _ hn34.le; linarith
    _ ≤ (P * P) * (n : ℝ) ^ (3/4 : ℝ) := mul_le_mul_of_nonneg_right hAB hn34.le
    _ = _ := by ring
