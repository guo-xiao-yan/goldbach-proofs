import Mathlib

private lemma dsam_mod (t k : ℕ) (ht : 2 < t) :
    2 ^ k % (2 ^ (t + 3) - 1) ≤ 4 * 2 ^ t := by
  have hL : 1 ≤ 2 ^ t := Nat.one_le_two_pow
  have h8 : 2 ^ (t + 3) = 8 * 2 ^ t := by rw [pow_add]; ring
  have hM : 1 < 2 ^ (t + 3) - 1 := by omega
  have h1 : 2 ^ (t + 3) % (2 ^ (t + 3) - 1) = 1 := by
    generalize 2 ^ (t + 3) = N at hM ⊢
    obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at hM ⊢
    rw [Nat.add_mod_left, Nat.mod_eq_of_lt hM]
  have hk : 2 ^ k = (2 ^ (t + 3)) ^ (k / (t + 3)) * 2 ^ (k % (t + 3)) := by
    rw [← pow_mul, ← pow_add, Nat.div_add_mod]
  have hr : 2 ^ (k % (t + 3)) ≤ 4 * 2 ^ t := by
    have : k % (t + 3) ≤ t + 2 := by
      have := Nat.mod_lt k (show 0 < t + 3 by omega); omega
    calc 2 ^ (k % (t + 3)) ≤ 2 ^ (t + 2) := Nat.pow_le_pow_right (by norm_num) this
      _ = 4 * 2 ^ t := by rw [pow_add]; ring
  have : 2 ^ k % (2 ^ (t + 3) - 1) = 2 ^ (k % (t + 3)) % (2 ^ (t + 3) - 1) := by
    rw [hk, Nat.mul_mod, Nat.pow_mod, h1]
    simp [Nat.mod_mod]
  rw [this]
  calc _ ≤ 2 ^ (k % (t + 3)) := Nat.mod_le _ _
    _ ≤ _ := hr

private lemma dsam_cop (W t : ℕ) (hW : 0 < W) (ht : W < t + 3) (hp : (t + 3).Prime) :
    Nat.Coprime W (2 ^ (t + 3) - 1) := by
  apply Nat.coprime_of_dvd
  intro p hpp hpW hpM
  have hpos : 0 < 2 ^ (t + 3) := by positivity
  have hodd : p ≠ 2 := by
    rintro rfl
    have h2 : 2 ∣ 2 ^ (t + 3) := dvd_pow_self 2 (by omega)
    omega
  haveI : Fact p.Prime := ⟨hpp⟩
  have hz : ((2 ^ (t + 3) - 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hpM
  have h1 : (2 : ZMod p) ^ (t + 3) = 1 := by
    have : 1 ≤ 2 ^ (t + 3) := Nat.one_le_two_pow
    rw [Nat.cast_sub this] at hz
    push_cast at hz
    exact sub_eq_zero.1 hz
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at this
    have := (Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).1 this
    exact hodd this
  have hd : orderOf (2 : ZMod p) ∣ t + 3 := orderOf_dvd_of_pow_eq_one h1
  have hd2 : orderOf (2 : ZMod p) ∣ p - 1 := ZMod.orderOf_dvd_card_sub_one h2
  rcases (Nat.dvd_prime hp).1 hd with h | h
  · rw [orderOf_eq_one_iff] at h
    have : ((2 : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by exact_mod_cast h
    rw [ZMod.natCast_eq_natCast_iff'] at this
    have hp2 := hpp.two_le
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hpp.one_lt] at this
    omega
  · rw [h] at hd2
    have := Nat.le_of_dvd hW hpW
    have := Nat.le_of_dvd (by have := hpp.two_le; omega) hd2
    omega

private lemma dsam_main :
    ∀ W : ℕ, 0 < W → ∃ M : ℕ, 1 < M ∧ Nat.Coprime W M ∧ ∃ S : Finset ℕ, S ⊆ Finset.range M ∧ M ≤ 8 * S.card ∧ ∀ (a b k : ℕ), a ∈ S → b ∈ S → (a+b)%M ≠ (2^k)%M := by
  intro W hW
  obtain ⟨s, hs, hsp⟩ := Nat.exists_infinite_primes (max W 5 + 1)
  have h1 := le_max_left W 5
  have h2 := le_max_right W 5
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 3 := ⟨s - 3, by omega⟩
  have hL : 1 ≤ 2 ^ t := Nat.one_le_two_pow
  have h8 : 2 ^ (t + 3) = 8 * 2 ^ t := by rw [pow_add]; ring
  refine ⟨2 ^ (t + 3) - 1, by omega, dsam_cop W t hW (by omega) hsp,
    Finset.Ico (3 * 2 ^ t) (4 * 2 ^ t), ?_, ?_, ?_⟩
  · intro x hx
    rw [Finset.mem_Ico] at hx
    rw [Finset.mem_range]; omega
  · rw [Nat.card_Ico]; omega
  · intro a b k ha hb
    rw [Finset.mem_Ico] at ha hb
    have := dsam_mod t k (by omega)
    have hlt : a + b < 2 ^ (t + 3) - 1 := by omega
    rw [Nat.mod_eq_of_lt hlt]
    omega

private lemma pdc_full (M W : ℕ) (hM : 0 < M) (hcop : Nat.Coprime W M) (S : Finset ℕ)
    (hS : S ⊆ Finset.range M) (y : ℕ) :
    ((Finset.range M).filter (fun j => (y + j * W) % M ∈ S)).card = S.card := by
  have hinj : ∀ j ∈ Finset.range M, ∀ j' ∈ Finset.range M,
      (y + j * W) % M = (y + j' * W) % M → j = j' := by
    intro j hj j' hj' h
    have h1 : y + j * W ≡ y + j' * W [MOD M] := h
    have h2 : j * W ≡ j' * W [MOD M] := Nat.ModEq.add_left_cancel' y h1
    have h3 : j ≡ j' [MOD M] :=
      Nat.ModEq.cancel_right_of_coprime (by simpa [Nat.Coprime, Nat.gcd_comm] using hcop) h2
    have h4 : j % M = j' % M := h3
    rw [Nat.mod_eq_of_lt (Finset.mem_range.1 hj), Nat.mod_eq_of_lt (Finset.mem_range.1 hj')] at h4
    exact h4
  have himg : (Finset.range M).image (fun j => (y + j * W) % M) = Finset.range M := by
    apply Finset.eq_of_subset_of_card_le
    · intro z hz
      simp only [Finset.mem_image] at hz
      obtain ⟨j, _, rfl⟩ := hz
      exact Finset.mem_range.2 (Nat.mod_lt _ hM)
    · rw [Finset.card_image_of_injOn (fun a ha b hb h => hinj a ha b hb h)]
  apply Finset.card_bij (fun j _ => (y + j * W) % M)
  · intro j hj; exact (Finset.mem_filter.1 hj).2
  · intro a ha b hb h
    exact hinj a (Finset.mem_filter.1 ha).1 b (Finset.mem_filter.1 hb).1 h
  · intro z hz
    have : z ∈ (Finset.range M).image (fun j => (y + j * W) % M) := by
      rw [himg]; exact hS hz
    obtain ⟨j, hj, hjz⟩ := Finset.mem_image.1 this
    exact ⟨j, Finset.mem_filter.2 ⟨hj, hjz ▸ hz⟩, hjz⟩

private lemma pdc_add (M W : ℕ) (hM : 0 < M) (hcop : Nat.Coprime W M) (S : Finset ℕ)
    (hS : S ⊆ Finset.range M) (x H : ℕ) :
    ((Finset.range (H + M)).filter (fun j => (x + j * W) % M ∈ S)).card
      = ((Finset.range H).filter (fun j => (x + j * W) % M ∈ S)).card + S.card := by
  rw [Finset.card_filter, Finset.card_filter, Finset.sum_range_add, ← pdc_full M W hM hcop S hS (x + H * W),
    Finset.card_filter]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  have : x + (H + j) * W = x + H * W + j * W := by ring
  rw [this]

private lemma pdc_count (M W : ℕ) (hM : 0 < M) (hcop : Nat.Coprime W M) (S : Finset ℕ)
    (hS : S ⊆ Finset.range M) (x q r : ℕ) :
    ((Finset.range (r + q * M)).filter (fun j => (x + j * W) % M ∈ S)).card
      = ((Finset.range r).filter (fun j => (x + j * W) % M ∈ S)).card + q * S.card := by
  induction q with
  | zero => simp
  | succ q ih =>
    have : r + (q + 1) * M = (r + q * M) + M := by ring
    rw [this, pdc_add M W hM hcop S hS, ih]
    ring

private lemma pdc_part (M W : ℕ) (S : Finset ℕ) (x r : ℕ) (hr : r ≤ M) (hS : S ⊆ Finset.range M)
    (hM : 0 < M) (hcop : Nat.Coprime W M) :
    ((Finset.range r).filter (fun j => (x + j * W) % M ∈ S)).card ≤ S.card := by
  have h1 : ((Finset.range r).filter (fun j => (x + j * W) % M ∈ S)).card
      ≤ ((Finset.range M).filter (fun j => (x + j * W) % M ∈ S)).card := by
    apply Finset.card_le_card
    intro j hj
    rw [Finset.mem_filter] at hj ⊢
    exact ⟨Finset.mem_range.2 (lt_of_lt_of_le (Finset.mem_range.1 hj.1) hr), hj.2⟩
  have := pdc_full M W hM hcop S hS x
  omega

theorem Conjectures.Goldbach.DyadicProgressionCountermodel :
    ∀ W : ℕ, 0 < W → ∀ u : ℕ → ℝ, (∀ x, 0 ≤ u x) → (∀ x, u (x+W) = u x) → ∃ (f : ℕ → ℝ) (C : ℝ), 0 < C ∧ (∀ x, 0 ≤ f x ∧ f x ≤ 8 * u x) ∧ (∀ x H : ℕ, |(∑ j ∈ Finset.range H, f (x+j*W)) - (H:ℝ)*u x| ≤ C*u x) ∧ ∀ a b k : ℕ, a+b = 2^k → f a * f b = 0 := by
  intro W hW u hu0 hup
  obtain ⟨M, hM1, hcop, S, hS, hcard, havoid⟩ := dsam_main W hW
  have hM : 0 < M := by omega
  have hSpos : 0 < S.card := by omega
  have hSr : (0:ℝ) < S.card := by exact_mod_cast hSpos
  set c : ℝ := (M:ℝ) / S.card with hc
  have hc0 : 0 ≤ c := by positivity
  have hc8 : c ≤ 8 := by
    rw [hc, div_le_iff₀ hSr]
    exact_mod_cast hcard
  have hcS : c * S.card = M := by rw [hc]; field_simp
  have huj : ∀ x j : ℕ, u (x + j * W) = u x := by
    intro x j
    induction j with
    | zero => simp
    | succ j ih =>
      have : x + (j + 1) * W = (x + j * W) + W := by ring
      rw [this, hup, ih]
  classical
  refine ⟨fun x => if x % M ∈ S then c * u x else 0, M, by exact_mod_cast hM, ?_, ?_, ?_⟩
  · intro x
    by_cases h : x % M ∈ S
    · simp only [h, if_true]
      exact ⟨mul_nonneg hc0 (hu0 x), by nlinarith [hu0 x]⟩
    · simp only [h, if_false]
      exact ⟨le_refl _, by nlinarith [hu0 x]⟩
  · intro x H
    set N : ℕ → ℕ := fun H => ((Finset.range H).filter (fun j => (x + j * W) % M ∈ S)).card with hN
    have hsum : ∑ j ∈ Finset.range H, (if (x + j * W) % M ∈ S then c * u (x + j * W) else 0)
        = c * u x * (N H : ℝ) := by
      rw [hN]
      simp only [huj, Finset.card_filter]
      push_cast
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      split_ifs <;> simp
    show |(∑ j ∈ Finset.range H, (if (x + j * W) % M ∈ S then c * u (x + j * W) else 0))
      - (H:ℝ) * u x| ≤ (M:ℝ) * u x
    rw [hsum]
    have hH : H = H % M + (H / M) * M := by
      have := Nat.mod_add_div H M
      linarith [mul_comm M (H / M)]
    have hcnt : N H = N (H % M) + (H / M) * S.card := by
      conv_lhs => rw [hH]
      exact pdc_count M W hM hcop S hS x (H / M) (H % M)
    have hrM : H % M < M := Nat.mod_lt _ hM
    have hNle := pdc_part M W S x (H % M) hrM.le hS hM hcop
    have hNle2 : N (H % M) ≤ S.card := hNle
    have hHr : (H : ℝ) = (H % M : ℕ) + (H / M : ℕ) * M := by
      exact_mod_cast hH
    have hNr : (N H : ℝ) = (N (H % M) : ℝ) + (H / M : ℕ) * S.card := by
      exact_mod_cast hcnt
    have key : c * (N H : ℝ) - H = c * (N (H % M) : ℝ) - (H % M : ℕ) := by
      rw [hNr, hHr]
      have : c * ((H / M : ℕ) * (S.card : ℝ)) = (H / M : ℕ) * M := by rw [← hcS]; ring
      nlinarith [this]
    have hr0 : (0:ℝ) ≤ (H % M : ℕ) := Nat.cast_nonneg _
    have hrM' : ((H % M : ℕ) : ℝ) ≤ M := by exact_mod_cast hrM.le
    have hN0 : (0:ℝ) ≤ (N (H % M) : ℝ) := Nat.cast_nonneg _
    have hN1 : (N (H % M) : ℝ) ≤ S.card := by exact_mod_cast hNle2
    have hbd : |c * (N H : ℝ) - H| ≤ M := by
      rw [key, abs_le]
      constructor
      · nlinarith [mul_nonneg hc0 hN0]
      · nlinarith [mul_le_mul_of_nonneg_left hN1 hc0]
    calc |c * u x * (N H : ℝ) - (H : ℝ) * u x| = |c * (N H : ℝ) - H| * u x := by
          rw [← abs_of_nonneg (hu0 x), ← abs_mul, abs_of_nonneg (hu0 x)]
          congr 1; ring
      _ ≤ M * u x := mul_le_mul_of_nonneg_right hbd (hu0 x)
  · intro a b k hab
    by_cases ha : a % M ∈ S
    · by_cases hb : b % M ∈ S
      · exfalso
        apply havoid (a % M) (b % M) k ha hb
        rw [← Nat.add_mod, hab]
      · simp [hb]
    · simp [ha]
