import Mathlib

namespace BCLPR

private noncomputable def theta (a : ℕ) (x : ℝ) : ℝ :=
  ∑ p ∈ Finset.Ioc 0 ⌊x⌋₊ with p.Prime ∧ p ≡ a [MOD 30], Real.log p

private lemma theta_lim (δ : ℝ) (hδ : 0 < δ) :
    ∃ Y : ℕ, ∀ a, a < 30 → a.Coprime 30 → ∀ n : ℕ, Y ≤ n →
      (1/8 - δ) * n ≤ theta a n ∧ theta a n ≤ (1/8 + δ) * n := by
  have h : ∀ᶠ x : ℝ in Filter.atTop, ∀ a ∈ Finset.range 30, a.Coprime 30 →
      |(theta a x) / x - 1/8| < δ := by
    rw [Filter.eventually_all_finset]
    intro a _
    by_cases ha : a.Coprime 30
    · have hp := Chebyshev.tendsto_sum_log_prime_modEq_div_atTop (q := 30) (a := a) ha
      have ht : Nat.totient 30 = 8 := by decide
      rw [ht] at hp
      have := (Metric.tendsto_nhds.1 hp) δ hδ
      filter_upwards [this] with x hx _
      rw [Real.dist_eq] at hx
      have e : (((8:ℕ):ℝ))⁻¹ = 1/8 := by norm_num
      rw [e] at hx
      exact hx
    · exact Filter.Eventually.of_forall fun x h => absurd h ha
  obtain ⟨X, hX⟩ := Filter.eventually_atTop.1 h
  refine ⟨max 1 ⌈X⌉₊, fun a ha hc n hn => ?_⟩
  have hXn : X ≤ (n:ℝ) := by
    have : ⌈X⌉₊ ≤ n := le_trans (le_max_right _ _) hn
    exact (Nat.ceil_le).1 this
  have hn1 : (0:ℝ) < n := by
    have : 1 ≤ n := le_trans (le_max_left _ _) hn
    exact_mod_cast this
  have := hX n hXn a (Finset.mem_range.2 ha) hc
  rw [abs_lt, lt_sub_iff_add_lt, sub_lt_iff_lt_add, lt_div_iff₀ hn1, div_lt_iff₀ hn1] at this
  constructor <;> nlinarith [this.1, this.2]


private lemma theta_diff (a u v : ℕ) (huv : u ≤ v) :
    theta a v - theta a u = ∑ p ∈ Finset.Ioc u v with p.Prime ∧ p ≡ a [MOD 30], Real.log p := by
  unfold theta
  simp only [Nat.floor_natCast, Finset.sum_filter]
  rw [← Finset.sum_Ioc_consecutive _ (Nat.zero_le u) huv]
  ring

private lemma count_le (δ : ℝ) (hδ : 0 < δ) :
    ∃ Y : ℕ, 1 ≤ Y ∧ ∀ a, a < 30 → a.Coprime 30 → ∀ u v : ℕ, Y ≤ u → u ≤ v →
      (((Finset.Ioc u v).filter (fun p => p.Prime ∧ p % 30 = a)).card : ℝ) * Real.log u
        ≤ ((v:ℝ) - u) / 8 + δ * ((u:ℝ) + v) := by
  obtain ⟨Y, hY⟩ := theta_lim δ hδ
  refine ⟨max Y 1, le_max_right _ _, fun a ha hc u v hu huv => ?_⟩
  have hu' : Y ≤ u := le_trans (le_max_left _ _) hu
  have hv' : Y ≤ v := le_trans hu' huv
  have h1 := (hY a ha hc u hu').1
  have h2 := (hY a ha hc v hv').2
  have hd := theta_diff a u v huv
  have hu1 : (1:ℝ) ≤ u := by exact_mod_cast le_trans (le_max_right _ _) hu
  have hlog : 0 ≤ Real.log u := Real.log_nonneg hu1
  have hfil : ((Finset.Ioc u v).filter (fun p => p.Prime ∧ p % 30 = a)) =
      ((Finset.Ioc u v).filter (fun p => p.Prime ∧ p ≡ a [MOD 30])) := by
    apply Finset.filter_congr
    intro p _
    unfold Nat.ModEq
    rw [Nat.mod_eq_of_lt ha]
  rw [hfil]
  have h3 : (((Finset.Ioc u v).filter (fun p => p.Prime ∧ p ≡ a [MOD 30])).card : ℝ) * Real.log u
      ≤ ∑ p ∈ Finset.Ioc u v with p.Prime ∧ p ≡ a [MOD 30], Real.log p := by
    rw [← nsmul_eq_mul]
    rw [← Finset.sum_const]
    apply Finset.sum_le_sum
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hp
    apply Real.log_le_log (by linarith)
    exact_mod_cast hp.1.1.le
  nlinarith [h3, hd, h1, h2]


private def Hc (n : ℕ) : ℕ :=
  ((Finset.range (n+1)).filter (fun p => p.Prime ∧ p ≤ n ∧ (n-p).Prime ∧ n ≤ 3*p ∧ 3*p ≤ 2*n)).card

private def S (r : ℕ) : Finset ℕ :=
  (Finset.range 30).filter (fun a => a.Coprime 30 ∧ ((r+30-a)%30).Coprime 30)

private lemma S26 : (S 26).card = 3 := by decide
private lemma S28 : (S 28).card = 3 := by decide

private lemma prime_coprime30 (p : ℕ) (hp : p.Prime) (h6 : 6 ≤ p) : (p % 30).Coprime 30 := by
  have h : p.Coprime 30 := by
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    intro hd
    have := Nat.le_of_dvd (by norm_num) hd
    interval_cases p <;> simp_all (config := {decide := true})
  unfold Nat.Coprime at h ⊢
  rw [Nat.gcd_comm, Nat.gcd_rec] at h
  exact h


private lemma inj_card (Z W p r a : ℕ) (hp : 2 * (Z+W) / 3 < Z + 1) (hpp : p ≤ 2 * (Z+W) / 3) :
    (((Finset.Icc Z (Z+W)).filter (fun n => n % 30 = r)).filter
      (fun n => (n-p).Prime ∧ (n-p) % 30 = (r+30-a)%30)).card ≤
    ((Finset.Ioc (Z-p-1) (Z+W-p)).filter (fun q => q.Prime ∧ q % 30 = (r+30-a)%30)).card := by
  have hpZ : p ≤ Z := by omega
  apply Finset.card_le_card_of_injOn (fun n => n - p)
  · intro n hn
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_filter, Finset.mem_Icc] at hn
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Ioc]
    obtain ⟨⟨⟨hn1, hn2⟩, _⟩, hn3, hn4⟩ := hn
    have := hn3.two_le
    exact ⟨⟨by omega, by omega⟩, hn3, hn4⟩
  · intro n hn m hm hnm
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_filter, Finset.mem_Icc] at hn hm
    have hnm' : n - p = m - p := hnm
    omega

private lemma comb (X Z W r : ℕ) (hr : r < 30) (hX : 24 ≤ X) (hZ : X ≤ Z) (hW : 2 * W ≤ X) :
    ∑ n ∈ (Finset.Icc Z (Z+W)).filter (fun n => n % 30 = r), Hc n ≤
      ∑ a ∈ S r, ∑ p ∈ (Finset.Ioc (X/3-1) (2*(Z+W)/3)).filter (fun p => p.Prime ∧ p % 30 = a),
        ((Finset.Ioc (Z-p-1) (Z+W-p)).filter
          (fun q => q.Prime ∧ q % 30 = (r+30-a)%30)).card := by
  calc ∑ n ∈ (Finset.Icc Z (Z+W)).filter (fun n => n % 30 = r), Hc n
      ≤ ∑ n ∈ (Finset.Icc Z (Z+W)).filter (fun n => n % 30 = r), ∑ a ∈ S r,
          ∑ p ∈ (Finset.Ioc (X/3-1) (2*(Z+W)/3)).filter (fun p => p.Prime ∧ p % 30 = a),
            (if ((n-p).Prime ∧ (n-p) % 30 = (r+30-a)%30) then 1 else 0) := by
        apply Finset.sum_le_sum
        intro n hn
        simp only [Finset.mem_filter, Finset.mem_Icc] at hn
        obtain ⟨⟨hn1, hn2⟩, hn3⟩ := hn
        unfold Hc
        rw [Finset.card_eq_sum_card_fiberwise (f := fun p => p % 30) (t := S r)]
        · apply Finset.sum_le_sum
          intro a ha
          rw [← Finset.card_filter]
          apply Finset.card_le_card
          intro p hp
          simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc] at hp ⊢
          obtain ⟨⟨_, hp1, hp2, hp3, hp4, hp5⟩, hp6⟩ := hp
          refine ⟨⟨⟨by omega, by omega⟩, hp1, hp6⟩, hp3, by omega⟩
        · intro p hp
          simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hp
          obtain ⟨_, hp1, hp2, hp3, hp4, hp5⟩ := hp
          simp only [S, Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
          refine ⟨by omega, prime_coprime30 p hp1 (by omega), ?_⟩
          have e : (r + 30 - p % 30) % 30 = (n - p) % 30 := by omega
          rw [e]
          exact prime_coprime30 _ hp3 (by omega)
    _ = ∑ a ∈ S r, ∑ p ∈ (Finset.Ioc (X/3-1) (2*(Z+W)/3)).filter (fun p => p.Prime ∧ p % 30 = a),
          ∑ n ∈ (Finset.Icc Z (Z+W)).filter (fun n => n % 30 = r),
            (if ((n-p).Prime ∧ (n-p) % 30 = (r+30-a)%30) then 1 else 0) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_comm]
    _ ≤ _ := by
        apply Finset.sum_le_sum
        intro a ha
        apply Finset.sum_le_sum
        intro p hp
        rw [← Finset.card_filter]
        simp only [Finset.mem_filter, Finset.mem_Ioc] at hp
        obtain ⟨⟨hp1, hp2⟩, hp3, hp4⟩ := hp
        exact inj_card Z W p r a (by omega) (by omega)


private noncomputable def Lg (X : ℕ) : ℝ := Real.log ((X / 4 : ℕ) : ℝ)

private lemma window_bound : ∃ X1 : ℕ, ∀ r X Z W : ℕ, r < 30 → (S r).card = 3 → X1 ≤ X → X ≤ Z → Z ≤ X + 2 →
    256 * W ≤ X → X < 256 * W + 256 →
    (∑ n ∈ (Finset.Icc Z (Z+W)).filter (fun n => n % 30 = r), (Hc n : ℝ)) ≤
      3 * ((0.0422 * (X:ℝ)) / Lg X) * ((0.000495 * (X:ℝ)) / Lg X) := by
  obtain ⟨Y, hY1, hY⟩ := count_le (1/10000000) (by norm_num)
  refine ⟨4 * Y + 30000, fun r X Z W hr hS hX hXZ hZX hW1 hW2 => ?_⟩
  have hx : (X:ℝ) ≥ 30000 := by
    have : 30000 ≤ X := by omega
    exact_mod_cast this
  have hL : 0 < Lg X := by
    unfold Lg
    apply Real.log_pos
    have : 2 ≤ X / 4 := by omega
    have : (2:ℝ) ≤ ((X/4 : ℕ):ℝ) := by exact_mod_cast this
    linarith
  have hcomb := comb X Z W r hr (by omega) hXZ (by omega)
  have hcomb' : (∑ n ∈ (Finset.Icc Z (Z+W)).filter (fun n => n % 30 = r), (Hc n : ℝ)) ≤
      ∑ a ∈ S r, ∑ p ∈ (Finset.Ioc (X/3-1) (2*(Z+W)/3)).filter (fun p => p.Prime ∧ p % 30 = a),
        (((Finset.Ioc (Z-p-1) (Z+W-p)).filter
          (fun q => q.Prime ∧ q % 30 = (r+30-a)%30)).card : ℝ) := by
    exact_mod_cast hcomb
  refine le_trans hcomb' ?_
  set Amax : ℝ := 0.0422 * (X:ℝ) with hAmax
  set Bmax : ℝ := 0.000495 * (X:ℝ) with hBmax
  have hAm : 0 ≤ Amax := by rw [hAmax]; positivity
  have hBm : 0 ≤ Bmax := by rw [hBmax]; positivity
  have hq : ∀ a ∈ S r, ∀ p ∈ (Finset.Ioc (X/3-1) (2*(Z+W)/3)).filter (fun p => p.Prime ∧ p % 30 = a),
      (((Finset.Ioc (Z-p-1) (Z+W-p)).filter
          (fun q => q.Prime ∧ q % 30 = (r+30-a)%30)).card : ℝ) ≤ Bmax / Lg X := by
    intro a ha p hp
    simp only [S, Finset.mem_filter, Finset.mem_range] at ha
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hp
    obtain ⟨⟨hp1, hp2⟩, _, _⟩ := hp
    have hk := hY ((r+30-a)%30) (Nat.mod_lt _ (by norm_num)) ha.2.2 (Z-p-1) (Z+W-p)
      (by omega) (by omega)
    have h1 : (Lg X) ≤ Real.log ((Z-p-1 : ℕ):ℝ) := by
      unfold Lg
      apply Real.log_le_log
      · have : 1 ≤ X / 4 := by omega
        exact_mod_cast this
      · have : X / 4 ≤ Z - p - 1 := by omega
        exact_mod_cast this
    have hv : ((Z+W-p : ℕ):ℝ) = ((Z-p-1 : ℕ):ℝ) + W + 1 := by
      have : Z + W - p = (Z - p - 1) + W + 1 := by omega
      rw [this]; push_cast; ring
    have hu : ((Z-p-1 : ℕ):ℝ) ≤ Z := by
      have : Z - p - 1 ≤ Z := by omega
      exact_mod_cast this
    have hZr : (Z:ℝ) ≤ X + 2 := by exact_mod_cast hZX
    have hWr : 256 * (W:ℝ) ≤ X := by exact_mod_cast hW1
    have hB0 : (((Z+W-p : ℕ):ℝ) - ((Z-p-1 : ℕ):ℝ)) / 8 +
        1/10000000 * (((Z-p-1 : ℕ):ℝ) + ((Z+W-p : ℕ):ℝ)) ≤ Bmax := by
      rw [hv, hBmax]
      have hWx : (W:ℝ) ≤ X / 256 := by linarith
      nlinarith
    have hc0 : (0:ℝ) ≤ (((Finset.Ioc (Z-p-1) (Z+W-p)).filter
          (fun q => q.Prime ∧ q % 30 = (r+30-a)%30)).card : ℝ) := Nat.cast_nonneg _
    rw [le_div_iff₀ hL]
    nlinarith
  have hp : ∀ a ∈ S r, (((Finset.Ioc (X/3-1) (2*(Z+W)/3)).filter (fun p => p.Prime ∧ p % 30 = a)).card : ℝ)
      ≤ Amax / Lg X := by
    intro a ha
    simp only [S, Finset.mem_filter, Finset.mem_range] at ha
    have hk := hY a ha.1 ha.2.1 (X/3-1) (2*(Z+W)/3) (by omega) (by omega)
    have h1 : (Lg X) ≤ Real.log ((X/3-1 : ℕ):ℝ) := by
      unfold Lg
      apply Real.log_le_log
      · have : 1 ≤ X / 4 := by omega
        exact_mod_cast this
      · have : X / 4 ≤ X / 3 - 1 := by omega
        exact_mod_cast this
    have hu3 : (X:ℝ) ≤ 3 * ((X/3-1 : ℕ):ℝ) + 5 := by
      have : X ≤ 3 * (X/3-1) + 5 := by omega
      exact_mod_cast this
    have hv3 : 3 * ((2*(Z+W)/3 : ℕ):ℝ) ≤ 2 * ((Z:ℝ) + W) := by
      have : 3 * (2*(Z+W)/3) ≤ 2 * (Z + W) := by omega
      exact_mod_cast this
    have hZr : (Z:ℝ) ≤ X + 2 := by exact_mod_cast hZX
    have hWr : 256 * (W:ℝ) ≤ X := by exact_mod_cast hW1
    have hA0 : (((2*(Z+W)/3 : ℕ):ℝ) - ((X/3-1 : ℕ):ℝ)) / 8 +
        1/10000000 * (((X/3-1 : ℕ):ℝ) + ((2*(Z+W)/3 : ℕ):ℝ)) ≤ Amax := by
      rw [hAmax]
      nlinarith
    have hc0 : (0:ℝ) ≤ (((Finset.Ioc (X/3-1) (2*(Z+W)/3)).filter (fun p => p.Prime ∧ p % 30 = a)).card : ℝ) := Nat.cast_nonneg _
    rw [le_div_iff₀ hL]
    nlinarith
  calc ∑ a ∈ S r, ∑ p ∈ (Finset.Ioc (X/3-1) (2*(Z+W)/3)).filter (fun p => p.Prime ∧ p % 30 = a),
        (((Finset.Ioc (Z-p-1) (Z+W-p)).filter
          (fun q => q.Prime ∧ q % 30 = (r+30-a)%30)).card : ℝ)
      ≤ ∑ a ∈ S r, (Amax / Lg X) * (Bmax / Lg X) := by
        apply Finset.sum_le_sum
        intro a ha
        calc _ ≤ ∑ p ∈ (Finset.Ioc (X/3-1) (2*(Z+W)/3)).filter (fun p => p.Prime ∧ p % 30 = a),
                (Bmax / Lg X) := Finset.sum_le_sum fun p hp' => hq a ha p hp'
          _ = (((Finset.Ioc (X/3-1) (2*(Z+W)/3)).filter (fun p => p.Prime ∧ p % 30 = a)).card : ℝ) * (Bmax / Lg X) := by
                rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ _ := mul_le_mul_of_nonneg_right (hp a ha) (by positivity)
    _ = 3 * ((Amax / Lg X) * (Bmax / Lg X)) := by
        rw [Finset.sum_const, hS]; simp
    _ = _ := by ring


private lemma card_C (X W : ℕ) :
    (W - 29) / 30 ≤ ((Finset.Icc X (X+W)).filter (fun n => n % 30 = 26)).card := by
  have h := Finset.card_le_card_of_injOn (s := Finset.range ((W-29)/30))
    (t := (Finset.Icc X (X+W)).filter (fun n => n % 30 = 26))
    (fun k => X + (56 - X % 30) % 30 + 30 * k) ?_ ?_
  · simpa using h
  · intro k hk
    rw [Finset.mem_coe, Finset.mem_range] at hk
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨by omega, by omega⟩, by omega⟩
  · intro k _ m _ hkm
    have : X + (56 - X % 30) % 30 + 30 * k = X + (56 - X % 30) % 30 + 30 * m := hkm
    omega

private lemma Lg_ge (X : ℕ) (hX : 100 ≤ X) : Real.log (X:ℝ) - 4 ≤ Lg X := by
  unfold Lg
  have hX0 : (0:ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have h1 : (X:ℝ) / 5 ≤ ((X/4 : ℕ):ℝ) := by
    have : X ≤ 5 * (X/4) := by omega
    have : (X:ℝ) ≤ 5 * ((X/4 : ℕ):ℝ) := by exact_mod_cast this
    linarith
  have h2 := Real.log_le_log (by positivity) h1
  rw [Real.log_div hX0.ne' (by norm_num)] at h2
  have h3 : Real.log 5 ≤ 4 := by
    have := Real.log_le_sub_one_of_pos (x := 5) (by norm_num)
    linarith
  linarith

private lemma fin_ineq (X : ℕ) (Cc : ℝ) (hX : 100 ≤ X) (hlog : 4000 ≤ Real.log (X:ℝ))
    (hCc : 0.999 * (X:ℝ) / 7680 ≤ Cc) :
    3 * ((0.0422 * (X:ℝ)) / Lg X) * ((0.000495 * (X:ℝ)) / Lg X)
      ≤ 0.495 * Cc * ((X:ℝ) / (Real.log (X:ℝ))^2) := by
  have hl := Lg_ge X hX
  set l := Real.log (X:ℝ) with hl0
  have hX0 : (100:ℝ) ≤ X := by exact_mod_cast hX
  have hL : 0.999 * l ≤ Lg X := by linarith
  have hL0 : 0 < 0.999 * l := by positivity
  have hLp : 0 < Lg X := lt_of_lt_of_le hL0 hL
  have e1 : 3 * ((0.0422 * (X:ℝ)) / Lg X) * ((0.000495 * (X:ℝ)) / Lg X)
      = (3 * 0.0422 * 0.000495 * (X:ℝ)^2) / (Lg X)^2 := by
    field_simp
  rw [e1]
  have e2 : (3 * 0.0422 * 0.000495 * (X:ℝ)^2) / (Lg X)^2 ≤
      (3 * 0.0422 * 0.000495 * (X:ℝ)^2) / (0.999 * l)^2 := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    nlinarith
  refine le_trans e2 ?_
  rw [div_le_iff₀ (by positivity)]
  have e3 : 0.495 * Cc * ((X:ℝ) / l^2) * (0.999 * l)^2 = 0.495 * 0.998001 * Cc * X := by
    have : l ≠ 0 := by positivity
    field_simp
    ring
  rw [e3]
  nlinarith [mul_le_mul_of_nonneg_right hCc (by positivity : (0:ℝ) ≤ X)]


private lemma main_ineq : ∃ X2 : ℕ, ∀ X : ℕ, X2 ≤ X → ∀ b : ℕ → ℝ,
    (∀ n ∈ (Finset.Icc X (2*X)).filter (fun n => Even n), (X:ℝ) / (Real.log (X:ℝ))^2 ≤ b n) →
    (1/1000000000 : ℝ) * (X:ℝ) * ((X:ℝ) / (Real.log (X:ℝ))^2)^2 <
      ∑ n ∈ (Finset.Icc X (2*X)).filter (fun n => Even n),
        (((Hc n : ℝ) + (Hc (n+2) : ℝ)) - b n)^2 := by
  obtain ⟨X1, hX1⟩ := window_bound
  refine ⟨max (max X1 100000000) ⌈Real.exp 4000⌉₊, fun X hX b hb => ?_⟩
  have hXa : X1 ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX
  have hXb : 100000000 ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX
  have hXc : ⌈Real.exp 4000⌉₊ ≤ X := le_trans (le_max_right _ _) hX
  have hX0 : (0:ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have hexp : Real.exp 4000 ≤ (X:ℝ) := (Nat.ceil_le).1 hXc
  have hlog : 4000 ≤ Real.log (X:ℝ) := (Real.le_log_iff_exp_le hX0).2 hexp
  have hlogp : 0 < Real.log (X:ℝ) := by linarith
  set M : ℝ := (X:ℝ) / (Real.log (X:ℝ))^2 with hM
  have hMp : 0 < M := by positivity
  set W := X / 256 with hW
  set C := (Finset.Icc X (X+W)).filter (fun n => n % 30 = 26) with hC
  have hcard : 0.999 * (X:ℝ) / 7680 ≤ (C.card : ℝ) := by
    have h1 : (W - 29) / 30 ≤ C.card := card_C X W
    have h2 : W ≤ 30 * C.card + 58 := by omega
    have h3 : W ≤ 30 * C.card + 58 := h2
    have h4 : (W:ℝ) ≤ 30 * (C.card:ℝ) + 58 := by exact_mod_cast h3
    have h5 : (X:ℝ) ≤ 256 * W + 255 := by
      have : X ≤ 256 * W + 255 := by omega
      exact_mod_cast this
    have h6 : (100000000:ℝ) ≤ X := by exact_mod_cast hXb
    linarith
  have hS1 : (∑ n ∈ C, (Hc n : ℝ)) ≤ 0.495 * (C.card:ℝ) * M := by
    have := hX1 26 X X W (by norm_num) S26 hXa le_rfl (by omega) (by omega) (by omega)
    exact le_trans this (fin_ineq X _ (by omega) hlog hcard)
  have hS2 : (∑ n ∈ C, (Hc (n+2) : ℝ)) ≤ 0.495 * (C.card:ℝ) * M := by
    have := hX1 28 X (X+2) W (by norm_num) S28 hXa (by omega) le_rfl (by omega) (by omega)
    have himg : C.image (fun n => n + 2) =
        (Finset.Icc (X+2) (X+2+W)).filter (fun n => n % 30 = 28) := by
      ext m
      simp only [hC, Finset.mem_image, Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨n, ⟨⟨h1, h2⟩, h3⟩, rfl⟩
        omega
      · rintro ⟨⟨h1, h2⟩, h3⟩
        exact ⟨m - 2, ⟨⟨by omega, by omega⟩, by omega⟩, by omega⟩
    have hsum : (∑ n ∈ C, (Hc (n+2) : ℝ)) =
        ∑ n ∈ (Finset.Icc (X+2) (X+2+W)).filter (fun n => n % 30 = 28), (Hc n : ℝ) := by
      rw [← himg, Finset.sum_image]
      intro a _ b _ hab
      simpa using hab
    rw [hsum]
    exact le_trans this (fin_ineq X _ (by omega) hlog hcard)
  have hCE : C ⊆ (Finset.Icc X (2*X)).filter (fun n => Even n) := by
    intro n hn
    simp only [hC, Finset.mem_filter, Finset.mem_Icc] at hn ⊢
    refine ⟨⟨hn.1.1, by omega⟩, ?_⟩
    rw [Nat.even_iff]
    omega
  have hCpos : 0 < (C.card : ℝ) := lt_of_lt_of_le (by positivity) hcard
  have hsumf : 0.01 * (C.card:ℝ) * M ≤ ∑ n ∈ C, (b n - ((Hc n : ℝ) + (Hc (n+2) : ℝ))) := by
    rw [Finset.sum_sub_distrib]
    have h1 : (C.card:ℝ) * M ≤ ∑ n ∈ C, b n := by
      have := Finset.sum_le_sum (s := C) (f := fun _ => M) (g := b)
        (fun n hn => hb n (hCE hn))
      simpa using this
    have h2 : (∑ n ∈ C, ((Hc n : ℝ) + (Hc (n+2) : ℝ))) ≤ 0.99 * (C.card:ℝ) * M := by
      rw [Finset.sum_add_distrib]
      linarith
    linarith
  have hcs := sq_sum_le_card_mul_sum_sq (s := C)
    (f := fun n => b n - ((Hc n : ℝ) + (Hc (n+2) : ℝ)))
  have hpos : 0 ≤ 0.01 * (C.card:ℝ) * M := by positivity
  have hsq := pow_le_pow_left₀ hpos hsumf 2
  have hsub : ∑ n ∈ C, (b n - ((Hc n : ℝ) + (Hc (n+2) : ℝ)))^2 ≤
      ∑ n ∈ (Finset.Icc X (2*X)).filter (fun n => Even n),
        (((Hc n : ℝ) + (Hc (n+2) : ℝ)) - b n)^2 := by
    have e : ∀ n : ℕ, (b n - ((Hc n : ℝ) + (Hc (n+2) : ℝ)))^2 =
        (((Hc n : ℝ) + (Hc (n+2) : ℝ)) - b n)^2 := fun n => by ring
    simp_rw [e]
    exact Finset.sum_le_sum_of_subset_of_nonneg hCE (fun n _ _ => sq_nonneg _)
  have hmain : 0.0001 * (C.card:ℝ) * M^2 ≤ ∑ n ∈ C, (b n - ((Hc n : ℝ) + (Hc (n+2) : ℝ)))^2 := by
    by_contra hcon
    push Not at hcon
    have : (C.card:ℝ) * ∑ n ∈ C, (b n - ((Hc n : ℝ) + (Hc (n+2) : ℝ)))^2 <
        (C.card:ℝ) * ((C.card:ℝ) * M^2 * 0.0001) := by
      apply mul_lt_mul_of_pos_left _ hCpos
      linarith
    nlinarith
  have hfin : (1/1000000000 : ℝ) * (X:ℝ) < 0.0001 * (C.card:ℝ) := by linarith
  have : (1/1000000000 : ℝ) * (X:ℝ) * M^2 < 0.0001 * (C.card:ℝ) * M^2 :=
    mul_lt_mul_of_pos_right hfin (by positivity)
  linarith

end BCLPR

theorem Conjectures.Goldbach.BeaumontCentralLocalPredictionRefute :
    ¬ (let H := fun n : ℕ => ((Finset.range (n+1)).filter (fun p => p.Prime ∧ p ≤ n ∧ (n-p).Prime ∧ n ≤ 3*p ∧ 3*p ≤ 2*n)).card; let E := fun X : ℕ => (Finset.Icc X (2*X)).filter (fun n => Even n); let M := fun X : ℕ => (X:ℝ)/(Real.log (X:ℝ))^2; let R := fun n : ℕ => ((H n + H (n+2)):ℝ); ∀ ε : ℝ, 0 < ε → ∃ X₀ : ℕ, ∀ X ≥ X₀, ∃ b : ℕ → ℝ, (∀ n ∈ E X, M X ≤ b n) ∧ (∑ n ∈ E X, (R n-b n)^2) ≤ ε*(X:ℝ)*(M X)^2) := by
  intro h
  dsimp only at h
  obtain ⟨X2, hX2⟩ := BCLPR.main_ineq
  obtain ⟨X0, hX0⟩ := h (1/1000000000 : ℝ) (by norm_num)
  obtain ⟨b, hb1, hb2⟩ := hX0 (max X0 X2) (le_max_left _ _)
  exact absurd hb2 (not_le.2 (hX2 (max X0 X2) (le_max_right _ _) b hb1))
