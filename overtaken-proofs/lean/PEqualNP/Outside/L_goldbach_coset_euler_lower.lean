import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

private theorem unit_crt_product :
    let U := fun q n : ℕ => (Finset.range q).filter (fun a => Nat.Coprime a q ∧ Nat.Coprime (n+q-a) q); ∀ q r n, 0<q → 0<r → Nat.Coprime q r → (U (q*r) n).card=(U q n).card*(U r n).card := by
  intro U q r n hq hr hqr
  have res : ∀ m N a : ℕ, 0 < m → m ∣ N → a ≤ n + N →
      (Nat.Coprime a m ↔ Nat.Coprime (a % m) m) ∧
      (Nat.Coprime (n + N - a) m ↔ Nat.Coprime (n + m - a % m) m) := by
    intro m N a hm hdvd han
    have hlt : a % m < m := Nat.mod_lt _ hm
    have e1 : a ≡ a % m [MOD m] := (Nat.mod_modEq a m).symm
    have hN : N ≡ 0 [MOD m] := (Nat.modEq_zero_iff_dvd).2 hdvd
    have hm0 : m ≡ 0 [MOD m] := (Nat.modEq_zero_iff_dvd).2 (dvd_refl m)
    have e2 : n + N - a ≡ n + m - a % m [MOD m] := by
      have h1 : (n + N - a) + a = n + N := by omega
      have h2 : (n + m - a % m) + a % m = n + m := by omega
      have h3 : (n + N - a) + a ≡ (n + m - a % m) + a % m [MOD m] := by
        rw [h1, h2]
        exact (Nat.ModEq.refl n).add (hN.trans hm0.symm)
      exact Nat.ModEq.add_right_cancel e1 h3
    constructor
    · unfold Nat.Coprime
      rw [e1.gcd_eq]
    · unfold Nat.Coprime
      rw [e2.gcd_eq]
  have hmem : ∀ a, a < q * r → (a ∈ U (q*r) n ↔ (a % q ∈ U q n ∧ a % r ∈ U r n)) := by
    intro a ha
    have hq1 := res q (q * r) a hq (dvd_mul_right q r) (by omega)
    have hr1 := res r (q * r) a hr (dvd_mul_left r q) (by omega)
    have hq2 := res q q (a % q) hq (dvd_refl q) (by have := Nat.mod_lt a hq; omega)
    have hr2 := res r r (a % r) hr (dvd_refl r) (by have := Nat.mod_lt a hr; omega)
    have hq3 : a % q % q = a % q := Nat.mod_mod _ _
    have hr3 : a % r % r = a % r := Nat.mod_mod _ _
    rw [hq3] at hq2
    rw [hr3] at hr2
    simp only [U, Finset.mem_filter, Finset.mem_range]
    have hqa := Nat.mod_lt a hq
    have hra := Nat.mod_lt a hr
    have c1 : Nat.Coprime a (q * r) ↔ Nat.Coprime a q ∧ Nat.Coprime a r := Nat.coprime_mul_iff_right
    have c2 : Nat.Coprime (n + q * r - a) (q * r) ↔
        Nat.Coprime (n + q * r - a) q ∧ Nat.Coprime (n + q * r - a) r := Nat.coprime_mul_iff_right
    rw [c1, c2, hq1.1, hr1.1, hq1.2, hr1.2]
    constructor
    · rintro ⟨_, ⟨h1, h2⟩, h3, h4⟩
      exact ⟨⟨hqa, h1, h3⟩, hra, h2, h4⟩
    · rintro ⟨⟨_, h1, h3⟩, _, h2, h4⟩
      exact ⟨ha, ⟨h1, h2⟩, h3, h4⟩
  show (U (q*r) n).card = (U q n).card * (U r n).card
  rw [← Finset.card_product]
  apply Finset.card_bij (fun a _ => (a % q, a % r))
  · intro a ha
    have ha' : a < q * r := Finset.mem_range.1 (Finset.mem_filter.1 ha).1
    have := (hmem a ha').1 ha
    exact Finset.mem_product.2 this
  · intro a ha b hb h
    have ha' : a < q * r := Finset.mem_range.1 (Finset.mem_filter.1 ha).1
    have hb' : b < q * r := Finset.mem_range.1 (Finset.mem_filter.1 hb).1
    have h1 : a % q = b % q := (Prod.mk.inj h).1
    have h2 : a % r = b % r := (Prod.mk.inj h).2
    have := (Nat.modEq_and_modEq_iff_modEq_mul hqr).1 ⟨h1, h2⟩
    unfold Nat.ModEq at this
    rwa [Nat.mod_eq_of_lt ha', Nat.mod_eq_of_lt hb'] at this
  · intro p hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.1 hp
    have hp1' : p.1 < q := Finset.mem_range.1 (Finset.mem_filter.1 hp1).1
    have hp2' : p.2 < r := Finset.mem_range.1 (Finset.mem_filter.1 hp2).1
    let c := Nat.chineseRemainder hqr p.1 p.2
    have hc : c.1 < q * r := Nat.chineseRemainder_lt_mul hqr p.1 p.2 hq.ne' hr.ne'
    have hcq : c.1 % q = p.1 := by
      have := c.2.1
      unfold Nat.ModEq at this
      rw [this, Nat.mod_eq_of_lt hp1']
    have hcr : c.1 % r = p.2 := by
      have := c.2.2
      unfold Nat.ModEq at this
      rw [this, Nat.mod_eq_of_lt hp2']
    have hcm : c.1 ∈ U (q*r) n := (hmem c.1 hc).2 (by rw [hcq, hcr]; exact ⟨hp1, hp2⟩)
    exact ⟨c.1, hcm, by rw [hcq, hcr]⟩

private theorem unit_power_lift :
    let U := fun q n : ℕ => (Finset.range q).filter (fun a => Nat.Coprime a q ∧ Nat.Coprime (n+q-a) q); ∀ p k n, Nat.Prime p → (U (p^(k+1)) n).card=p^k*(U p n).card := by
  intro U p k n hp
  have hp0 : 0 < p := hp.pos
  have hpow : p^(k+1) = p * p^k := by ring
  have helper : ∀ b j : ℕ, b < p → j < p^k →
      (Nat.Coprime (b + p*j) (p^(k+1)) ↔ Nat.Coprime b p) ∧
      (Nat.Coprime (n + p^(k+1) - (b + p*j)) (p^(k+1)) ↔ Nat.Coprime (n + p - b) p) := by
    intro b j hb hj
    obtain ⟨m, hm⟩ : ∃ m, p^k = j + 1 + m := ⟨p^k - j - 1, by omega⟩
    have e : p^(k+1) = p*j + p + p*m := by rw [hpow, hm]; ring
    have e2 : n + p^(k+1) - (b + p*j) = (n + p - b) + p*m := by omega
    constructor
    · rw [Nat.coprime_pow_right_iff (Nat.succ_pos k), Nat.coprime_add_mul_left_left]
    · rw [Nat.coprime_pow_right_iff (Nat.succ_pos k), e2, Nat.coprime_add_mul_left_left]
  have hmem : ∀ q a : ℕ, a ∈ U q n ↔ a < q ∧ Nat.Coprime a q ∧ Nat.Coprime (n+q-a) q := by
    intro q a
    simp only [U, Finset.mem_filter, Finset.mem_range]
  have hk : (U p n ×ˢ Finset.range (p^k)).card = (U (p^(k+1)) n).card := by
    apply Finset.card_bij (fun x _ => x.1 + p * x.2)
    · intro x hx
      rw [Finset.mem_product, hmem, Finset.mem_range] at hx
      obtain ⟨⟨hb, hc1, hc2⟩, hj⟩ := hx
      have h := helper x.1 x.2 hb hj
      rw [hmem]
      refine ⟨?_, h.1.2 hc1, h.2.2 hc2⟩
      have : p * (x.2 + 1) ≤ p * p^k := Nat.mul_le_mul_left p hj
      rw [hpow]
      nlinarith
    · intro x hx y hy hxy
      rw [Finset.mem_product, hmem, Finset.mem_range] at hx hy
      have hb1 := hx.1.1
      have hb2 := hy.1.1
      have hxy : x.1 + p * x.2 = y.1 + p * y.2 := hxy
      have m1 : (x.1 + p * x.2) % p = x.1 := by
        rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hb1]
      have m2 : (y.1 + p * y.2) % p = y.1 := by
        rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hb2]
      have d1 : (x.1 + p * x.2) / p = x.2 := by
        rw [Nat.add_mul_div_left _ _ hp0, Nat.div_eq_of_lt hb1]; simp
      have d2 : (y.1 + p * y.2) / p = y.2 := by
        rw [Nat.add_mul_div_left _ _ hp0, Nat.div_eq_of_lt hb2]; simp
      rw [hxy] at m1 d1
      exact Prod.ext (m1.symm.trans m2) (d1.symm.trans d2)
    · intro a ha
      rw [hmem] at ha
      obtain ⟨ha1, ha2, ha3⟩ := ha
      have hb : a % p < p := Nat.mod_lt _ hp0
      have hj : a / p < p^k := by
        apply Nat.div_lt_of_lt_mul
        rw [← hpow]; exact ha1
      have hdecomp : a % p + p * (a / p) = a := Nat.mod_add_div a p
      have h := helper (a % p) (a / p) hb hj
      rw [hdecomp] at h
      refine ⟨(a % p, a / p), ?_, hdecomp⟩
      rw [Finset.mem_product, hmem, Finset.mem_range]
      exact ⟨⟨hb, h.1.1 ha2, h.2.1 ha3⟩, hj⟩
  rw [← hk, Finset.card_product, Finset.card_range, mul_comm]

private theorem unit_prime_card (p n : ℕ) (hp : p.Prime) :
    ((Finset.range p).filter (fun a => Nat.Coprime a p ∧ Nat.Coprime (n+p-a) p)).card
      = if p ∣ n then p - 1 else p - 2 := by
  have hp2 := hp.two_le
  have hpos : 0 < p := hp.pos
  have key : (Finset.range p).filter (fun a => Nat.Coprime a p ∧ Nat.Coprime (n+p-a) p)
      = Finset.range p \ {0, n % p} := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_sdiff, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · rintro ⟨ha, h1, h2⟩
      refine ⟨ha, ?_⟩
      rintro (h | h)
      · subst h
        simp at h1
        exact hp.one_lt.ne' (by simpa using h1)
      · subst h
        have : p ∣ n + p - n % p := by
          have hd := Nat.mod_add_div n p
          have : n + p - n % p = p * (n / p + 1) := by
            have : p * (n / p + 1) = p * (n / p) + p := by ring
            omega
          rw [this]; exact dvd_mul_right _ _
        have := (Nat.Prime.coprime_iff_not_dvd hp).1 h2.symm
        exact this ‹_›
    · rintro ⟨ha, hn⟩
      push_neg at hn
      refine ⟨ha, ?_, ?_⟩
      · exact (Nat.Prime.coprime_iff_not_dvd hp).2 (fun h => hn.1 (by
          have := Nat.eq_zero_of_dvd_of_lt h ha
          exact this)) |>.symm
      · apply Nat.Coprime.symm
        rw [Nat.Prime.coprime_iff_not_dvd hp]
        intro hd
        have hb := Nat.mod_lt n hpos
        have hdec := Nat.mod_add_div n p
        have e : n + p - a = p * (n / p) + (n % p + p - a) := by omega
        rw [e] at hd
        have hd2 : p ∣ n % p + p - a := (Nat.dvd_add_right (dvd_mul_right p _)).1 hd
        obtain ⟨k, hk⟩ := hd2
        have hk1 : k = 1 := by
          rcases k with _ | _ | k
          · omega
          · rfl
          · have : p * (k+1+1) ≥ p*2 := Nat.mul_le_mul_left p (by omega)
            omega
        subst hk1
        exact hn.2 (by omega)
  rw [key]
  have hsub : ({0, n % p} : Finset ℕ) ⊆ Finset.range p := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Finset.mem_range]
    rcases hx with h | h
    · omega
    · rw [h]; exact Nat.mod_lt _ hpos
  rw [Finset.card_sdiff_of_subset hsub, Finset.card_range]
  by_cases hd : p ∣ n
  · have : n % p = 0 := Nat.mod_eq_zero_of_dvd hd
    rw [this]
    simp only [hd, if_true]
    simp
  · have : n % p ≠ 0 := fun h => hd (Nat.dvd_of_mod_eq_zero h)
    simp only [hd, if_false]
    rw [Finset.card_pair (Ne.symm this)]

private theorem norm_aux (n : ℕ) : ∀ q : ℕ, 0 < q →
    (q:ℝ) * (((Finset.range q).filter (fun a => Nat.Coprime a q ∧ Nat.Coprime (n+q-a) q)).card : ℝ)
      / (q.totient:ℝ)^2
    = ∏ p ∈ q.primeFactors, (p:ℝ) * (if p ∣ n then (p:ℝ) - 1 else (p:ℝ) - 2) / ((p:ℝ) - 1)^2 := by
  intro q
  induction q using Nat.recOnPosPrimePosCoprime with
  | zero => intro h; omega
  | one =>
    intro _
    simp
  | prime_pow p k hp hk =>
    intro _
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have h := unit_power_lift p j n hp
    dsimp only at h
    rw [h, Nat.totient_prime_pow_succ hp, Nat.primeFactors_prime_pow (by omega) hp,
      Finset.prod_singleton, unit_prime_card p n hp]
    have hp2 : (2:ℝ) ≤ p := by exact_mod_cast hp.two_le
    have hp1 : (p:ℝ) - 1 ≠ 0 := by linarith
    have hp0 : (p:ℝ) ≠ 0 := by linarith
    have hc : ((if p ∣ n then p - 1 else p - 2 : ℕ) : ℝ)
        = if p ∣ n then (p:ℝ) - 1 else (p:ℝ) - 2 := by
      split_ifs
      · rw [Nat.cast_sub hp.one_le]; simp
      · rw [Nat.cast_sub hp.two_le]; simp
    rw [Nat.cast_mul, Nat.cast_pow, hc]
    push_cast [Nat.cast_sub hp.one_le]
    rw [pow_succ]
    field_simp
  | coprime a b ha hb hab iha ihb =>
    intro _
    have ha0 : 0 < a := by omega
    have hb0 : 0 < b := by omega
    have h := unit_crt_product a b n ha0 hb0 hab
    dsimp only at h
    have ht : ((a*b).totient : ℝ) = (a.totient:ℝ) * (b.totient:ℝ) := by
      rw [Nat.totient_mul hab]; push_cast; rfl
    have hta : (a.totient:ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.2 ha0).ne'
    have htb : (b.totient:ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.2 hb0).ne'
    rw [Nat.Coprime.primeFactors_mul hab, Finset.prod_union hab.disjoint_primeFactors,
      ← iha ha0, ← ihb hb0, h, ht]
    push_cast
    field_simp

private theorem unit_rcount (n q : ℕ) :
    ((Finset.range q).filter (fun r => r.Coprime q ∧ ((n+q-r)%q).Coprime q))
    = (Finset.range q).filter (fun a => Nat.Coprime a q ∧ Nat.Coprime (n+q-a) q) := by
  apply Finset.filter_congr
  intro r _
  have : Nat.gcd ((n+q-r)%q) q = Nat.gcd (n+q-r) q := (Nat.mod_modEq _ _).gcd_eq
  unfold Nat.Coprime
  rw [this]

private theorem tele_prod (M : ℕ) (hM : 1 ≤ M) :
    ∏ m ∈ Finset.Icc 2 M, (1 - 1 / (m:ℝ)^2) = ((M:ℝ) + 1) / (2 * M) := by
  induction M, hM using Nat.le_induction with
  | base => norm_num
  | succ M hM ih =>
    rw [Finset.prod_Icc_succ_top (by omega), ih]
    have hM' : (1:ℝ) ≤ M := by exact_mod_cast hM
    push_cast
    field_simp
    ring

private theorem sub_prod_ge (M : ℕ) (hM : 1 ≤ M) (T : Finset ℕ) (hT : T ⊆ Finset.Icc 2 M) :
    (1:ℝ) / 2 ≤ ∏ m ∈ T, (1 - 1 / (m:ℝ)^2) := by
  have hfac : ∀ m ∈ Finset.Icc 2 M, 0 ≤ 1 - 1 / (m:ℝ)^2 ∧ 1 - 1 / (m:ℝ)^2 ≤ 1 := by
    intro m hm
    have h2 : (2:ℝ) ≤ m := by exact_mod_cast (Finset.mem_Icc.1 hm).1
    have : (1:ℝ) ≤ (m:ℝ)^2 := by nlinarith
    constructor
    · rw [sub_nonneg, div_le_one (by positivity)]; exact this
    · have : 0 ≤ 1 / (m:ℝ)^2 := by positivity
      linarith
  have h1 : ∏ m ∈ Finset.Icc 2 M \ T, (1 - 1 / (m:ℝ)^2) ≤ 1 :=
    Finset.prod_le_one₀ (fun m hm => (hfac m (Finset.mem_sdiff.1 hm).1).1)
      (fun m hm => (hfac m (Finset.mem_sdiff.1 hm).1).2)
  have h2 : 0 ≤ ∏ m ∈ T, (1 - 1 / (m:ℝ)^2) :=
    Finset.prod_nonneg (fun m hm => (hfac m (hT hm)).1)
  have h3 := Finset.prod_sdiff (f := fun m : ℕ => (1 - 1 / (m:ℝ)^2)) hT
  have h4 : ∏ m ∈ Finset.Icc 2 M, (1 - 1 / (m:ℝ)^2) ≤ ∏ m ∈ T, (1 - 1 / (m:ℝ)^2) := by
    rw [← h3]
    nlinarith
  rw [tele_prod M hM] at h4
  have hM' : (1:ℝ) ≤ M := by exact_mod_cast hM
  have : (1:ℝ) / 2 ≤ ((M:ℝ) + 1) / (2 * M) := by
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    nlinarith
  linarith

theorem PEqualNP.Outside.L_goldbach_coset_euler_lower :
    let R := fun n q : ℕ => ((Finset.range q).filter (fun r => r.Coprime q ∧ ((n+q-r) % q).Coprime q)).card; ∀ n q : ℕ, Even n → 0<q → (1:ℝ)/2 ≤ (q:ℝ)*(R n q:ℝ)/(q.totient:ℝ)^2 := by
  intro R n q hn hq
  have hmain : (q:ℝ) * (R n q : ℝ) / (q.totient:ℝ)^2
      = ∏ p ∈ q.primeFactors, (p:ℝ) * (if p ∣ n then (p:ℝ) - 1 else (p:ℝ) - 2) / ((p:ℝ) - 1)^2 := by
    show (q:ℝ) * (((Finset.range q).filter (fun r => r.Coprime q ∧ ((n+q-r) % q).Coprime q)).card : ℝ) / (q.totient:ℝ)^2 = _
    rw [unit_rcount]
    exact norm_aux n q hq
  rw [hmain]
  set f : ℕ → ℝ := fun p => (p:ℝ) * (if p ∣ n then (p:ℝ) - 1 else (p:ℝ) - 2) / ((p:ℝ) - 1)^2 with hf
  have hprime : ∀ p ∈ q.primeFactors, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  have hf0 : ∀ p ∈ q.primeFactors, 0 ≤ f p := by
    intro p hp
    have hp2 : (2:ℝ) ≤ p := by exact_mod_cast (hprime p hp).two_le
    simp only [hf]
    apply div_nonneg _ (by positivity)
    split_ifs <;> nlinarith
  have hlow : ∀ p ∈ q.primeFactors.erase 2,
      1 - 1 / (((p - 1 : ℕ) : ℝ))^2 ≤ f p := by
    intro p hp
    have hpq := Finset.mem_erase.1 hp
    have hpp := hprime p hpq.2
    have hp3 : 3 ≤ p := by
      have := hpp.two_le
      omega
    have hp3' : (3:ℝ) ≤ p := by exact_mod_cast hp3
    rw [Nat.cast_sub (by omega)]
    push_cast
    have hp1 : (0:ℝ) < (p:ℝ) - 1 := by linarith
    simp only [hf]
    have hx : (1 - 1 / ((p:ℝ) - 1)^2) * ((p:ℝ) - 1)^2 = ((p:ℝ) - 1)^2 - 1 := by
      field_simp
    split_ifs
    · rw [le_div_iff₀ (by positivity), hx]
      nlinarith
    · rw [le_div_iff₀ (by positivity), hx]
      nlinarith
  have hinj : Set.InjOn (fun p : ℕ => p - 1) (q.primeFactors.erase 2 : Finset ℕ) := by
    intro a ha b hb hab
    have h1 := (hprime a (Finset.mem_erase.1 ha).2).pos
    have h2 := (hprime b (Finset.mem_erase.1 hb).2).pos
    simp only at hab
    omega
  have himg : (q.primeFactors.erase 2).image (fun p : ℕ => p - 1) ⊆ Finset.Icc 2 (q + 1) := by
    intro m hm
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hm
    have hpq := Finset.mem_erase.1 hp
    have hpp := hprime p hpq.2
    have hp3 : 3 ≤ p := by
      have := hpp.two_le
      omega
    have hple : p ≤ q := Nat.le_of_dvd hq (Nat.dvd_of_mem_primeFactors hpq.2)
    rw [Finset.mem_Icc]
    omega
  have hA : (1:ℝ) / 2 ≤ ∏ p ∈ q.primeFactors.erase 2, f p := by
    calc (1:ℝ) / 2 ≤ ∏ m ∈ (q.primeFactors.erase 2).image (fun p : ℕ => p - 1), (1 - 1 / (m:ℝ)^2) :=
          sub_prod_ge (q + 1) (by omega) _ himg
      _ = ∏ p ∈ q.primeFactors.erase 2, (1 - 1 / (((p - 1 : ℕ) : ℝ))^2) :=
          Finset.prod_image hinj
      _ ≤ ∏ p ∈ q.primeFactors.erase 2, f p := by
          apply Finset.prod_le_prod₀
          · intro p hp
            have hpq := Finset.mem_erase.1 hp
            have hpp := hprime p hpq.2
            have hp3 : 3 ≤ p := by
              have := hpp.two_le
              omega
            have : (2:ℝ) ≤ ((p - 1 : ℕ) : ℝ) := by
              have : 2 ≤ p - 1 := by omega
              exact_mod_cast this
            have : (1:ℝ) ≤ ((p - 1 : ℕ) : ℝ)^2 := by nlinarith
            rw [sub_nonneg, div_le_one (by positivity)]; exact this
          · exact hlow
  by_cases h2 : 2 ∈ q.primeFactors
  · rw [← Finset.mul_prod_erase _ f h2]
    have hf2 : f 2 = 2 := by
      have : 2 ∣ n := even_iff_two_dvd.1 hn
      simp only [hf, this, if_true]
      norm_num
    rw [hf2]
    have : 0 ≤ ∏ p ∈ q.primeFactors.erase 2, f p :=
      Finset.prod_nonneg (fun p hp => hf0 p (Finset.mem_of_mem_erase hp))
    linarith
  · rw [Finset.erase_eq_of_notMem h2] at hA
    exact hA
