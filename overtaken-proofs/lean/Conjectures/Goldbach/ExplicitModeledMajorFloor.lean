import Mathlib

open Finset Filter MeasureTheory

namespace GoldbachExplicitModeledMajor
noncomputable section

def phase (x : ℝ) : ℂ := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

def cutoff (n : ℕ) : ℕ := (Nat.log 2 (n + 2)) ^ 2

def kernel (n : ℕ) (β : ℝ) : ℂ := ∑ k ∈ range (n + 1), phase ((k : ℝ) * β)

def width (n q : ℕ) : ℝ := (cutoff n : ℝ) / ((q : ℝ) * n)

def kernelMass (n : ℕ) (b : ℝ) : ℝ := ∫ β in -b..b, ‖kernel n β‖ ^ 2

private theorem continuous_kernel (n : ℕ) : Continuous (kernel n) := by
  unfold kernel phase
  fun_prop

theorem kernelMass_mono {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (n : ℕ) :
    kernelMass n u ≤ kernelMass n v :=
  intervalIntegral.integral_mono_interval (neg_le_neg huv) (by linarith) huv
    (Eventually.of_forall fun _ => sq_nonneg _) (((continuous_kernel n).norm.pow 2).intervalIntegrable _ _)

private theorem kernel_on_zero_arc {n : ℕ} (hn : 0 < n) {t : ℝ}
    (ht : t ∈ Set.Icc 0 (1 / (6 * (n : ℝ)))) : (n : ℝ) / 2 ≤ ‖kernel n t‖ := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hnt := (le_div_iff₀ (show 0 < 6 * (n : ℝ) by positivity)).mp ht.2
  have hc (k : ℕ) (hk : k ∈ range (n + 1)) :
      1 / 2 ≤ (phase ((k : ℝ) * t)).re := by
    rw [phase, Complex.exp_ofReal_mul_I_re, ← Real.cos_pi_div_three]
    apply Real.cos_le_cos_of_nonneg_of_le_pi
    · exact mul_nonneg (by positivity) (mul_nonneg (Nat.cast_nonneg _) ht.1)
    · linarith [Real.pi_pos]
    have hk' : (k : ℝ) ≤ n := by exact_mod_cast Nat.lt_succ_iff.mp (mem_range.mp hk)
    have hkt := mul_le_mul_of_nonneg_right hk' ht.1
    nlinarith only [mul_le_mul_of_nonneg_left hnt Real.pi_pos.le,
      mul_le_mul_of_nonneg_left hkt Real.pi_pos.le]
  calc
    _ ≤ ∑ _k ∈ range (n + 1), (1 / 2 : ℝ) := by simp; linarith
    _ ≤ ∑ k ∈ range (n + 1), (phase ((k : ℝ) * t)).re := sum_le_sum hc
    _ = (kernel n t).re := by rw [kernel, Complex.re_sum]
    _ ≤ _ := Complex.re_le_norm _

theorem kernelMass_floor {n : ℕ} (hn : 0 < n) {b : ℝ} (hb : 1 / (6 * (n : ℝ)) ≤ b) :
    (n : ℝ) / 24 ≤ kernelMass n b := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  let u : ℝ := 1 / (6 * (n : ℝ))
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hb0 : 0 ≤ b := hu.trans hb
  have hc := (continuous_kernel n).norm.pow 2
  calc
    _ = ∫ _t in (0 : ℝ)..u, ((n : ℝ) / 2) ^ 2 := by
      rw [intervalIntegral.integral_const]
      simp only [sub_zero, smul_eq_mul, u]
      field_simp
      ring
    _ ≤ ∫ t in (0 : ℝ)..u, ‖kernel n t‖ ^ 2 :=
      intervalIntegral.integral_mono_on hu (by simp) (hc.intervalIntegrable _ _) fun _ ht =>
        pow_le_pow_left₀ (by positivity) (kernel_on_zero_arc hn ht) 2
    _ ≤ _ := intervalIntegral.integral_mono_interval (neg_nonpos.mpr hb0) hu hb
      (Eventually.of_forall fun _ => sq_nonneg _) (hc.intervalIntegrable _ _)

theorem cutoff_positive (n : ℕ) : 1 ≤ cutoff n :=
  Nat.one_le_iff_ne_zero.mpr (pow_ne_zero 2 (Nat.log_pos (by decide : 1 < 2) (by omega : 2 ≤ n+2)).ne')

theorem width_nonneg (n q : ℕ) : 0 ≤ width n q := by unfold width; positivity

end
end GoldbachExplicitModeledMajor

namespace GoldbachExplicitModeledMajor.RamanujanCRT
private def unitsBelow (m : ℕ) := (Finset.range m).filter (fun a => Nat.Coprime a m)

private theorem unitsBelow_card (m : ℕ) : (unitsBelow m).card = m.totient := by
  unfold unitsBelow
  rw [Nat.totient_eq_card_coprime]
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_range]
  exact and_congr_right (fun _ => Nat.coprime_comm)

private noncomputable def phase (m h a : ℕ) : ℂ :=
  Complex.exp (((2 * Real.pi * ((h : ℝ) * a / m) : ℝ) : ℂ) * Complex.I)

private theorem phase_character (m h a : ℕ) [NeZero m] :
    phase m h a = ZMod.stdAddChar ((h : ZMod m) * (a : ZMod m)) := by
  have ch := ZMod.stdAddChar_coe (N := m) ((h * a : ℕ) : ℤ)
  push_cast at ch
  rw [ch]
  unfold phase
  push_cast
  congr 1
  ring

private theorem phase_modulus (m h a : ℕ) [NeZero m] :
    phase m h (a % m) = phase m h a := by
  simp only [phase_character, ZMod.natCast_mod]

private theorem phase_pair (q r h a b : ℕ) (hq : 0 < q) (hr : 0 < r) :
    phase (q*r) h ((r*a + q*b) % (q*r)) = phase q h a * phase r h b := by
  have : NeZero (q*r) := ⟨Nat.ne_of_gt (Nat.mul_pos hq hr)⟩
  rw [phase_modulus]
  unfold phase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  have qnz : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have rnz : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  field_simp

theorem crt :
    let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let ram := fun (q h : ℕ) => Finset.sum ((Finset.range q).filter (fun a => Nat.Coprime a q)) (fun a => E ((h:ℝ)*(a:ℝ)/(q:ℝ))); ∀ q r h, 0<q → 0<r → Nat.Coprime q r → ram (q*r) h=ram q h*ram r h := by
  dsimp only
  intro q r h hq hr cop
  let combine (x : ℕ × ℕ) := (r*x.1 + q*x.2) % (q*r)
  let pairs := unitsBelow q ×ˢ unitsBelow r
  have member {m a : ℕ} : a ∈ unitsBelow m ↔ a < m ∧ Nat.Coprime a m := by
    simp only [unitsBelow, Finset.mem_filter, Finset.mem_range]
  have maps : pairs.image combine ⊆ unitsBelow (q*r) := by
    intro z hz
    obtain ⟨⟨a,b⟩, hab, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨ha,hb⟩ := Finset.mem_product.mp hab
    apply member.mpr
    refine ⟨Nat.mod_lt _ (Nat.mul_pos hq hr), ?_⟩
    change Nat.gcd ((r*a + q*b) % (q*r)) (q*r) = 1
    rw [← Nat.gcd_rec]
    change Nat.Coprime (q*r) (r*a + q*b)
    apply Nat.coprime_mul_iff_left.mpr
    constructor
    · rw [Nat.coprime_add_mul_left_right]
      exact cop.mul_right (member.mp ha).2.symm
    · rw [add_comm, Nat.coprime_add_mul_left_right]
      exact cop.symm.mul_right (member.mp hb).2.symm
  have injective : Set.InjOn combine (↑pairs) := by
    rintro ⟨a,b⟩ hab ⟨c,d⟩ hcd he
    obtain ⟨ha,hb⟩ := Finset.mem_product.mp hab
    obtain ⟨hc,hd⟩ := Finset.mem_product.mp hcd
    have congruence : r*a + q*b ≡ r*c + q*d [MOD q*r] := he
    apply Prod.ext
    · have hmod := congruence.of_dvd (dvd_mul_right q r)
      have reduced : r*a ≡ r*c [MOD q] := by
        simpa only [Nat.ModEq, Nat.add_mod, Nat.mul_mod_right, add_zero, Nat.mod_mod] using hmod
      exact (Nat.ModEq.cancel_left_of_coprime cop reduced).eq_of_lt_of_lt
        (member.mp ha).1 (member.mp hc).1
    · have hmod := congruence.of_dvd (dvd_mul_left r q)
      have reduced : q*b ≡ q*d [MOD r] := by
        simpa only [Nat.ModEq, Nat.add_mod, Nat.mul_mod_right, zero_add, Nat.mod_mod] using hmod
      exact (Nat.ModEq.cancel_left_of_coprime cop.symm reduced).eq_of_lt_of_lt
        (member.mp hb).1 (member.mp hd).1
  have covers : pairs.image combine = unitsBelow (q*r) := by
    apply Finset.eq_of_subset_of_card_le maps
    rw [Finset.card_image_of_injOn injective, unitsBelow_card, Nat.totient_mul cop]
    simp only [pairs, Finset.card_product, unitsBelow_card]
    exact le_rfl
  change (∑ z ∈ unitsBelow (q*r), phase (q*r) h z) =
    (∑ a ∈ unitsBelow q, phase q h a) * ∑ b ∈ unitsBelow r, phase r h b
  rw [← covers, Finset.sum_image injective, Finset.sum_mul_sum]
  rw [← Finset.sum_product']
  exact Finset.sum_congr rfl (fun x _ => phase_pair q r h x.1 x.2 hq hr)

end GoldbachExplicitModeledMajor.RamanujanCRT
namespace GoldbachExplicitModeledMajor.RamanujanPower
open Finset

theorem primePower :
    let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let ram := fun (q h : ℕ) => Finset.sum ((Finset.range q).filter (fun a => Nat.Coprime a q)) (fun a => E ((h:ℝ)*(a:ℝ)/(q:ℝ))); ∀ p j h, Nat.Prime p → ram (p^(j+1)) h = (if p^(j+1) ∣ h then ((p^(j+1):ℕ):ℂ) else 0) - (if p^j ∣ h then ((p^j:ℕ):ℂ) else 0) := by
  intro E ram p j h hp
  have full (q : ℕ) (hq : 0 < q) :
      ∑ a ∈ range q, E ((h:ℝ) * a / q) = if q ∣ h then (q:ℂ) else 0 := by
    let : NeZero q := ⟨hq.ne'⟩
    calc
      _ = ∑ x : ZMod q, ZMod.stdAddChar ((h : ZMod q) * x) := by
        apply Finset.sum_bij (fun (a : ℕ) _ => (a : ZMod q))
        · intro a ha
          exact mem_univ _
        · intro a ha b hb hab
          simpa only [ZMod.val_natCast_of_lt (mem_range.mp ha),
            ZMod.val_natCast_of_lt (mem_range.mp hb)] using congrArg ZMod.val hab
        · intro x _
          exact ⟨x.val, mem_range.mpr x.val_lt, ZMod.natCast_zmod_val x⟩
        · intro a _
          have cast_eq : (h : ZMod q) * a = ((h * a : ℕ) : ℤ) := by push_cast; rfl
          rw [cast_eq, ZMod.stdAddChar_coe]
          dsimp [E]
          congr 1
          push_cast
          ring
      _ = _ := by
        by_cases hd : q ∣ h
        · have hz : (h : ZMod q) = 0 := (ZMod.natCast_eq_zero_iff h q).mpr hd
          simp [hd, hz, ZMod.card]
        · have hz : (h : ZMod q) ≠ 0 := fun hz => hd ((ZMod.natCast_eq_zero_iff h q).mp hz)
          rw [ite_eq_right hd]
          exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar q hz)
  let m := p ^ j
  have hm : 0 < m := pow_pos hp.pos _
  let mult := (range m).image (fun b => p * b)
  have hsub : mult ⊆ range (p^(j+1)) := by
    intro a ha
    obtain ⟨b, hb, rfl⟩ := mem_image.mp ha
    rw [mem_range, pow_succ']
    exact Nat.mul_lt_mul_of_pos_left (mem_range.mp hb) hp.pos
  have hfilter : (range (p^(j+1))).filter (fun a => Nat.Coprime a (p^(j+1))) =
      range (p^(j+1)) \ mult := by
    rw [sdiff_eq_filter]
    apply filter_congr
    intro a ha
    rw [Nat.coprime_pow_right_iff (Nat.succ_pos j), Nat.coprime_comm, hp.coprime_iff_not_dvd]
    apply not_congr
    constructor
    · rintro ⟨b, rfl⟩
      apply mem_image.mpr
      refine ⟨b, mem_range.mpr ?_, rfl⟩
      rw [mem_range, pow_succ'] at ha
      exact (Nat.mul_lt_mul_left hp.pos).mp ha
    · intro ha'
      obtain ⟨b, _, rfl⟩ := mem_image.mp ha'
      exact dvd_mul_right _ _
  have removed : ∑ a ∈ mult, E ((h:ℝ)*a/(p^(j+1):ℕ)) =
      ∑ b ∈ range m, E ((h:ℝ)*b/m) := by
    rw [show mult = (range m).image (fun b => p * b) from rfl,
      sum_image (mul_right_injective₀ hp.ne_zero).injOn]
    apply sum_congr rfl
    intro b _
    congr 1
    rw [pow_succ']
    push_cast
    dsimp [m]
    push_cast
    field_simp [show (p : ℝ) ≠ 0 by exact_mod_cast hp.ne_zero]
  change ∑ a ∈ (range (p^(j+1))).filter _, E ((h:ℝ)*a/(p^(j+1):ℕ)) = _
  rw [hfilter, ← full _ (pow_pos hp.pos (j+1)), ← full _ hm, ← removed]
  exact eq_sub_of_add_eq (sum_sdiff hsub)

end GoldbachExplicitModeledMajor.RamanujanPower

namespace GoldbachExplicitModeledMajor

open Finset
open scoped ComplexConjugate
noncomputable section

def ram (q h : ℕ) : ℂ :=
  ∑ a ∈ (range q).filter (fun a => a.Coprime q), phase ((h : ℝ) * a / q)

theorem ram_mul {q r : ℕ} (hq : 0 < q) (hr : 0 < r) (hc : q.Coprime r) (h : ℕ) :
    ram (q * r) h = ram q h * ram r h := RamanujanCRT.crt q r h hq hr hc

theorem ram_primePower (p j h : ℕ) (hp : p.Prime) :
    ram (p ^ (j + 1)) h = (if p ^ (j + 1) ∣ h then ((p ^ (j + 1) : ℕ) : ℂ) else 0) -
      (if p ^ j ∣ h then ((p ^ j : ℕ) : ℂ) else 0) := RamanujanPower.primePower p j h hp

theorem ram_one (h : ℕ) : ram 1 h = 1 := by simp [ram, phase]

theorem ram_prime {p : ℕ} (hp : p.Prime) (h : ℕ) :
    ram p h = (if p ∣ h then (p : ℂ) else 0) - 1 := by
  simpa using ram_primePower p 0 h hp

private theorem ram_unit_power {p : ℕ} (hp : p.Prime) (j h : ℕ) (hc : h.Coprime p) :
    ram (p ^ (j + 1)) h = if j = 0 then -1 else 0 := by
  have hd := hp.coprime_iff_not_dvd.mp hc.symm
  have hpow (k : ℕ) : ¬ p ^ (k + 1) ∣ h :=
    fun hh => hd ((dvd_pow_self p (Nat.succ_ne_zero k)).trans hh)
  rw [ram_primePower p j h hp, ite_eq_right (hpow j)]
  cases j with
  | zero => simp
  | succ k => simp [hpow k]

def localCoefficient (p n : ℕ) : ℝ :=
  if p ∣ n then 1 / ((p : ℝ) - 1) else -(1 / ((p : ℝ) - 1) ^ 2)

def coefficient (q n : ℕ) : ℂ := (ram q 1 / (q.totient : ℂ)) ^ 2 * conj (ram q n)

theorem coefficient_one (n : ℕ) : coefficient 1 n = 1 := by simp [coefficient, ram_one]

theorem coefficient_mul {q r : ℕ} (hq : 0 < q) (hr : 0 < r) (hc : q.Coprime r) (n : ℕ) :
    coefficient (q * r) n = coefficient q n * coefficient r n := by
  unfold coefficient
  rw [ram_mul hq hr hc, ram_mul hq hr hc, Nat.totient_mul hc, Nat.cast_mul, map_mul]
  ring

theorem coefficient_prime {p : ℕ} (hp : p.Prime) (n : ℕ) :
    coefficient p n = (localCoefficient p n : ℂ) := by
  have hone : ¬ p ∣ 1 := fun h => hp.ne_one (Nat.dvd_one.mp h)
  have hne : (p : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hp.ne_one)
  rw [coefficient, ram_prime hp, ram_prime hp, ite_eq_right hone, Nat.totient_prime hp,
    Nat.cast_sub hp.one_le, Nat.cast_one]
  by_cases hd : p ∣ n <;> simp [localCoefficient, hd] <;> field_simp

theorem coefficient_higher_power {p : ℕ} (hp : p.Prime) (k n : ℕ) :
    coefficient (p ^ (k + 2)) n = 0 := by
  have h := ram_unit_power hp (k + 1) 1 (by simp)
  simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false] at h
  simp [coefficient, h]

end
end GoldbachExplicitModeledMajor

namespace GoldbachExplicitModeledMajor

open Finset

noncomputable section
theorem coefficient_not_squarefree {q : ℕ} (n : ℕ) (hq : 0 < q)
    (hs : ¬ Squarefree q) : coefficient q n = 0 := by
  induction q using Nat.recOnPosPrimePosCoprime with
  | zero => omega
  | one => exact (hs squarefree_one).elim
  | prime_pow p k hp hk =>
    cases k with
    | zero => omega
    | succ k =>
      cases k with
      | zero => exact (hs (by simpa using hp.squarefree)).elim
      | succ j => exact coefficient_higher_power hp j n
  | coprime a b ha hb hab ia ib =>
    rw [coefficient_mul (by omega) (by omega) hab]
    by_cases h : Squarefree a
    · rw [ib (by omega) (fun h' => hs ((Nat.squarefree_mul hab).mpr ⟨h,h'⟩)), mul_zero]
    · rw [ia (by omega) h, zero_mul]

theorem coefficient_prime_product (n : ℕ) (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime) :
    coefficient (∏ p ∈ s, p) n = ((∏ p ∈ s, localCoefficient p n : ℝ) : ℂ) := by
  induction s using Finset.induction_on with
  | empty => simp [coefficient_one]
  | @insert p s hp ih =>
    have hprime := hs p (mem_insert_self _ _)
    have hs' : ∀ r ∈ s, r.Prime := fun r hr => hs r (mem_insert_of_mem hr)
    have hcop : p.Coprime (∏ r ∈ s, r) := Nat.coprime_prod_right_iff.mpr fun r hr =>
      (Nat.coprime_primes hprime (hs' r hr)).mpr fun he => hp (he ▸ hr)
    rw [prod_insert hp, prod_insert hp, coefficient_mul hprime.pos (prod_pos fun r hr => (hs' r hr).pos) hcop,
      coefficient_prime hprime, ih hs', Complex.ofReal_mul]




end
end GoldbachExplicitModeledMajor

namespace GoldbachExplicitModeledMajor
open Finset ArithmeticFunction
open scoped ComplexConjugate
noncomputable section

private theorem cc_real {q : ℕ} (hq : 0 < q) (n : ℕ) :
    coefficient q n = (((coefficient q n).re : ℝ) : ℂ) := by
  by_cases hsf : Squarefree q
  · have he := coefficient_prime_product n q.primeFactors (fun _ hp => Nat.prime_of_mem_primeFactors hp)
    rw [Nat.prod_primeFactors_of_squarefree hsf] at he
    rw [he]; rfl
  · rw [coefficient_not_squarefree n hq hsf]; simp

def cc (n : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun q => (coefficient q n).re, by simp [coefficient, ram]⟩

theorem cc_apply (n q : ℕ) : cc n q = (coefficient q n).re := rfl

private theorem cc_mult (n : ℕ) : IsMultiplicative (cc n) := by
  refine ⟨by simp [cc_apply, coefficient_one], fun {a b} hab => ?_⟩
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  rcases eq_or_ne b 0 with rfl | hb
  · simp
  have hzero : (coefficient a n).im = 0 := by rw [cc_real ha.bot_lt n]; rfl
  simp [cc_apply, coefficient_mul ha.bot_lt hb.bot_lt hab, Complex.mul_re, hzero]

private def restr (n : ℕ) (P : ℕ → Prop) [DecidablePred P] : ArithmeticFunction ℝ :=
  ⟨fun q => if q = 0 then 0 else if (∀ p ∈ q.primeFactors, P p) then cc n q else 0, by simp⟩

private theorem restr_apply (n : ℕ) (P : ℕ → Prop) [DecidablePred P] {q : ℕ} (hq : q ≠ 0) :
    restr n P q = if (∀ p ∈ q.primeFactors, P p) then cc n q else 0 := by
  simp [restr, hq]

private theorem restr_mult (n : ℕ) (P : ℕ → Prop) [DecidablePred P] : IsMultiplicative (restr n P) := by
  refine ⟨by simp [restr, (cc_mult n).map_one], fun {a b} hab => ?_⟩
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  rcases eq_or_ne b 0 with rfl | hb
  · simp
  have hs : (∀ p ∈ (a * b).primeFactors, P p) ↔
      (∀ p ∈ a.primeFactors, P p) ∧ (∀ p ∈ b.primeFactors, P p) := by
    simp only [Nat.primeFactors_mul ha hb, mem_union]
    constructor
    · intro h; exact ⟨fun p hp => h p (Or.inl hp), fun p hp => h p (Or.inr hp)⟩
    · rintro ⟨x, y⟩ p (h | h)
      · exact x p h
      · exact y p h
  rw [restr_apply n P (mul_ne_zero ha hb), restr_apply n P ha, restr_apply n P hb,
    (cc_mult n).map_mul_of_coprime hab]
  by_cases h1 : ∀ p ∈ a.primeFactors, P p
  · by_cases h2 : ∀ p ∈ b.primeFactors, P p
    · rw [if_pos (hs.2 ⟨h1, h2⟩), if_pos h1, if_pos h2]
    · rw [if_neg (fun h => h2 (hs.1 h).2), if_neg h2, mul_zero]
  · rw [if_neg (fun h => h1 (hs.1 h).1), if_neg h1, zero_mul]

private theorem cc_higher (n p k : ℕ) (hp : p.Prime) : cc n (p ^ (k + 2)) = 0 := by
  simp [cc_apply, coefficient_higher_power hp k n]

private theorem cc_prime (n p : ℕ) (hp : p.Prime) : cc n p = localCoefficient p n := by
  simp [cc_apply, coefficient_prime hp]

private theorem restr_prime (n p : ℕ) (P : ℕ → Prop) [DecidablePred P] (hp : p.Prime) :
    restr n P p = if P p then cc n p else 0 := by
  rw [restr_apply n P hp.ne_zero]
  simp [hp.primeFactors]

private theorem restr_higher (n p k : ℕ) (P : ℕ → Prop) [DecidablePred P] (hp : p.Prime) :
    restr n P (p ^ (k + 2)) = 0 := by
  rw [restr_apply n P (pow_ne_zero _ hp.ne_zero), cc_higher n p k hp]
  simp

private theorem restr_conv (n : ℕ) :
    restr n (fun p => p ∣ n) * restr n (fun p => ¬ p ∣ n) = cc n := by
  rw [IsMultiplicative.eq_iff_eq_on_prime_powers _ ((restr_mult n _).mul (restr_mult n _)) _ (cc_mult n)]
  intro p k hp
  rcases k with _ | _ | k
  · simp [(restr_mult n (fun p => p ∣ n)).map_one, (restr_mult n (fun p => ¬ p ∣ n)).map_one,
      (cc_mult n).map_one]
  · rw [pow_one, ArithmeticFunction.mul_apply,
      Nat.sum_divisorsAntidiagonal (fun a b => restr n (fun p => p ∣ n) a * restr n (fun p => ¬ p ∣ n) b),
      Nat.Prime.sum_divisors hp]
    simp only [Nat.div_self hp.pos, Nat.div_one, (restr_mult n (fun p => p ∣ n)).map_one,
      (restr_mult n (fun p => ¬ p ∣ n)).map_one, restr_prime n p _ hp]
    by_cases h : p ∣ n <;> simp [h]
  · rw [cc_higher n p k hp, ArithmeticFunction.mul_apply,
      Nat.sum_divisorsAntidiagonal (fun a b => restr n (fun p => p ∣ n) a * restr n (fun p => ¬ p ∣ n) b),
      Nat.sum_divisors_prime_pow hp]
    apply sum_eq_zero
    intro i hi
    have hi' := mem_range.mp hi
    rw [Nat.pow_div (by omega) hp.pos]
    rcases i with _ | _ | i
    · simp [restr_higher n p k _ hp]
    · rcases k with _ | k
      · simp only [zero_add, pow_one]
        by_cases h : p ∣ n <;> simp [restr_prime n p _ hp, h]
      · rw [show k + 1 + 2 - 1 = k + 2 by omega, restr_higher n p k _ hp, mul_zero]
    · rw [restr_higher n p i _ hp, zero_mul]

end
end GoldbachExplicitModeledMajor

namespace GoldbachExplicitModeledMajor
open Finset ArithmeticFunction
open scoped ComplexConjugate
noncomputable section

private theorem sum_conv (f g : ArithmeticFunction ℝ) (X : ℕ) :
    ∑ q ∈ Icc 1 X, (f * g) q = ∑ d ∈ Icc 1 X, f d * ∑ k ∈ Icc 1 (X / d), g k := by
  classical
  let S := Icc 1 X
  let F := fun v : ℕ × ℕ => f v.1 * g v.2
  have hf (q : ℕ) (hq : q ∈ S) :
      q.divisorsAntidiagonal = (S ×ˢ S).filter (fun ab : ℕ × ℕ => ab.1 * ab.2 = q) := by
    obtain ⟨hq0, hqQ⟩ := mem_Icc.mp hq
    ext ab
    constructor
    · intro hab
      have hm (a : ℕ) (ha : a ∈ q.divisors) : a ∈ S :=
        mem_Icc.mpr ⟨Nat.pos_of_mem_divisors ha, (Nat.le_of_dvd hq0 (Nat.dvd_of_mem_divisors ha)).trans hqQ⟩
      exact mem_filter.mpr ⟨mem_product.mpr ⟨hm _ (Nat.fst_mem_divisors_of_mem_antidiagonal hab),
        hm _ (Nat.snd_mem_divisors_of_mem_antidiagonal hab)⟩, (Nat.mem_divisorsAntidiagonal.mp hab).1⟩
    · intro hh; exact Nat.mem_divisorsAntidiagonal.mpr ⟨(mem_filter.mp hh).2, by omega⟩
  calc
    _ = ∑ q ∈ S, ∑ v ∈ q.divisorsAntidiagonal, F v := by
      simp [S, ArithmeticFunction.mul_apply, F]
    _ = ∑ q ∈ S, ∑ v ∈ (S ×ˢ S).filter (fun ab : ℕ × ℕ => ab.1 * ab.2 = q), F v :=
      sum_congr rfl (fun q hq => by rw [hf q hq])
    _ = ∑ v ∈ (S ×ˢ S).filter (fun ab : ℕ × ℕ => ab.1 * ab.2 ∈ S), F v :=
      sum_fiberwise_eq_sum_filter _ _ _ _
    _ = _ := by
      rw [sum_filter, sum_product]
      apply sum_congr rfl
      intro d hd
      have hd0 := (mem_Icc.mp hd).1
      have hkd : (S.filter fun k => d * k ∈ S) = Icc 1 (X / d) := by
        ext k
        simp only [S, mem_filter, mem_Icc]
        constructor
        · rintro ⟨⟨hk, _⟩, _, hdk⟩
          exact ⟨hk, (Nat.le_div_iff_mul_le hd0).mpr (by simpa [mul_comm] using hdk)⟩
        · rintro ⟨hk, hkx⟩
          exact ⟨⟨hk, hkx.trans (Nat.div_le_self _ _)⟩, Nat.mul_pos hd0 hk,
            by simpa [mul_comm] using (Nat.le_div_iff_mul_le hd0).mp hkx⟩
      simp only [F, mul_sum]
      rw [← sum_filter, hkd]

private theorem cc_eq_prod (n q : ℕ) (hq : q ≠ 0) (hs : Squarefree q) :
    cc n q = ∏ p ∈ q.primeFactors, localCoefficient p n := by
  have he := coefficient_prime_product n q.primeFactors (fun _ hp => Nat.prime_of_mem_primeFactors hp)
  rw [Nat.prod_primeFactors_of_squarefree hs] at he
  rw [cc_apply, he, Complex.ofReal_re]

private theorem uu_nonneg (n q : ℕ) : 0 ≤ restr n (fun p => p ∣ n) q := by
  rcases eq_or_ne q 0 with rfl | hq
  · simp
  rw [restr_apply _ _ hq]
  split_ifs with h
  · by_cases hs : Squarefree q
    · rw [cc_eq_prod n q hq hs]
      apply prod_nonneg
      intro p hp
      have hp' := Nat.prime_of_mem_primeFactors hp
      have : (1 : ℝ) ≤ p := by exact_mod_cast hp'.one_le
      simp only [localCoefficient, if_pos (h p hp)]
      apply div_nonneg zero_le_one
      linarith
    · rw [cc_apply, coefficient_not_squarefree n (Nat.pos_of_ne_zero hq) hs]; simp
  · exact le_rfl

private theorem vv_abs (n q : ℕ) (h : restr n (fun p => ¬ p ∣ n) q ≠ 0) :
    Squarefree q ∧ (∀ p ∈ q.primeFactors, ¬ p ∣ n) ∧
      |restr n (fun p => ¬ p ∣ n) q| = ∏ p ∈ q.primeFactors, (1 / ((p : ℝ) - 1) ^ 2) := by
  have hq : q ≠ 0 := by rintro rfl; simp at h
  rw [restr_apply _ _ hq] at h
  have hc : ∀ p ∈ q.primeFactors, ¬ p ∣ n := by
    by_contra hc
    rw [if_neg hc] at h; exact h rfl
  rw [if_pos hc] at h
  have hs : Squarefree q := by
    by_contra hs
    apply h
    rw [cc_apply, coefficient_not_squarefree n (Nat.pos_of_ne_zero hq) hs]; simp
  refine ⟨hs, hc, ?_⟩
  rw [restr_apply _ _ hq, if_pos hc, cc_eq_prod n q hq hs, abs_prod]
  apply prod_congr rfl
  intro p hp
  simp [localCoefficient, if_neg (hc p hp)]

private theorem invSquares (U : ℕ) : (∑ k ∈ Icc 1 U, ((k : ℝ) ^ 2)⁻¹) ≤ 2 := by
  rcases U with _ | u
  · simp
  · have hUU : 1 ≤ u + 1 := by omega
    have H := sum_Ioc_inv_sq_le_sub (α := ℝ) (by decide : 1 ≠ 0) hUU
    rw [← Finset.sum_Ioc_add_eq_sum_Icc hUU]
    norm_num at H ⊢
    linarith [show 0 ≤ ((u : ℝ) + 1)⁻¹ by positivity]

private theorem odd_sum (X : ℕ) :
    ∑ p ∈ (Icc 1 X).filter (fun p => p.Prime ∧ p ≠ 2), (1 / ((p : ℝ) - 1) ^ 2) ≤ 1 / 2 := by
  set P := (Icc 1 X).filter (fun p => p.Prime ∧ p ≠ 2) with hP
  have hodd (p : ℕ) (hp : p ∈ P) : ∃ k, p = 2 * k + 1 ∧ 1 ≤ k := by
    obtain ⟨hp1, hp2, hp3⟩ := mem_filter.mp hp
    obtain ⟨k, hk⟩ := (hp2.eq_two_or_odd'.resolve_left hp3)
    refine ⟨k, hk, ?_⟩
    have := hp2.two_le
    omega
  have h1 : ∑ p ∈ P, (1 / ((p : ℝ) - 1) ^ 2) = ∑ p ∈ P, (1 / 4) * ((((p - 1) / 2 : ℕ) : ℝ) ^ 2)⁻¹ := by
    apply sum_congr rfl
    intro p hp
    obtain ⟨k, rfl, hk⟩ := hodd p hp
    have : (2 * k + 1 - 1) / 2 = k := by omega
    rw [this]
    have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
    push_cast
    field_simp
    ring
  rw [h1, ← mul_sum]
  have h2 : ∑ p ∈ P, ((((p - 1) / 2 : ℕ) : ℝ) ^ 2)⁻¹ ≤ ∑ k ∈ Icc 1 X, ((k : ℝ) ^ 2)⁻¹ := by
    rw [← sum_image (s := P) (g := fun p => (p - 1) / 2) (f := fun k : ℕ => ((k : ℝ) ^ 2)⁻¹)]
    · apply sum_le_sum_of_subset_of_nonneg
      · intro k hk
        obtain ⟨p, hp, rfl⟩ := mem_image.mp hk
        obtain ⟨k, rfl, hk1⟩ := hodd p hp
        have hpX := (mem_Icc.mp (mem_filter.mp hp).1).2
        simp only [mem_Icc]
        omega
      · intros; positivity
    · intro a ha b hb hab
      obtain ⟨k, rfl, _⟩ := hodd a ha
      obtain ⟨l, rfl, _⟩ := hodd b hb
      simp only at hab
      omega
  have := invSquares X
  linarith

end
end GoldbachExplicitModeledMajor

namespace GoldbachExplicitModeledMajor
open Finset ArithmeticFunction
open scoped ComplexConjugate
noncomputable section

private theorem T_bound (n X : ℕ) (hn : Even n) :
    ∑ d ∈ Icc 1 X, |restr n (fun p => ¬ p ∣ n) d| ≤ 5 / 3 := by
  classical
  set P := (Icc 1 X).filter (fun p => p.Prime ∧ p ≠ 2) with hP
  set w : ℕ → ℝ := fun p => 1 / ((p : ℝ) - 1) ^ 2 with hw
  have hw0 : ∀ p, 0 ≤ w p := fun p => by simp only [hw]; positivity
  set D := (Icc 1 X).filter (fun d => restr n (fun p => ¬ p ∣ n) d ≠ 0) with hD
  have h1 : ∑ d ∈ Icc 1 X, |restr n (fun p => ¬ p ∣ n) d| =
      ∑ d ∈ D, |restr n (fun p => ¬ p ∣ n) d| := by
    rw [hD, sum_filter]
    apply sum_congr rfl
    intro d _
    by_cases h : restr n (fun p => ¬ p ∣ n) d = 0 <;> simp [h]
  have h2 : ∑ d ∈ D, |restr n (fun p => ¬ p ∣ n) d| = ∑ d ∈ D, ∏ p ∈ d.primeFactors, w p :=
    sum_congr rfl (fun d hd => (vv_abs n d (mem_filter.mp hd).2).2.2)
  have hinj : Set.InjOn Nat.primeFactors (D : Set ℕ) := by
    intro a ha b hb hab
    have sa := (vv_abs n a (mem_filter.mp ha).2).1
    have sb := (vv_abs n b (mem_filter.mp hb).2).1
    rw [← Nat.prod_primeFactors_of_squarefree sa, ← Nat.prod_primeFactors_of_squarefree sb]
    simp only [hab]
  have h3 : ∑ d ∈ D, ∏ p ∈ d.primeFactors, w p = ∑ T ∈ D.image Nat.primeFactors, ∏ p ∈ T, w p :=
    (sum_image (f := fun T : Finset ℕ => ∏ p ∈ T, w p) hinj).symm
  have h4 : ∑ T ∈ D.image Nat.primeFactors, ∏ p ∈ T, w p ≤ ∑ T ∈ P.powerset, ∏ p ∈ T, w p := by
    apply sum_le_sum_of_subset_of_nonneg
    · intro T hT
      obtain ⟨d, hd, rfl⟩ := mem_image.mp hT
      rw [mem_powerset]
      intro p hp
      obtain ⟨hdI, hne⟩ := mem_filter.mp hd
      have hc := (vv_abs n d hne).2.1 p hp
      have pp := Nat.prime_of_mem_primeFactors hp
      have hpd := Nat.dvd_of_mem_primeFactors hp
      have hd0 := mem_Icc.mp hdI
      refine mem_filter.mpr ⟨mem_Icc.mpr ⟨pp.one_le, (Nat.le_of_dvd hd0.1 hpd).trans hd0.2⟩, pp, ?_⟩
      rintro rfl
      exact hc (even_iff_two_dvd.mp hn)
    · intros; exact prod_nonneg (fun p _ => hw0 p)
  have h5 : ∑ T ∈ P.powerset, ∏ p ∈ T, w p = ∏ p ∈ P, (1 + w p) := (prod_one_add P).symm
  have h6 := Real.prod_one_add_le_exp_sum P hw0
  have h7 : ∑ p ∈ P, w p ≤ 1 / 2 := odd_sum X
  have h8 : Real.exp (1 / 2) ≤ 5 / 3 := by
    have he := Real.exp_one_lt_d9
    have hsq : Real.exp (1 / 2) * Real.exp (1 / 2) = Real.exp 1 := by
      rw [← Real.exp_add]; norm_num
    have hp := Real.exp_pos (1 / 2)
    nlinarith
  have h9 := Real.exp_le_exp.mpr h7
  linarith

private theorem prefix_ge (n X : ℕ) (hn : Even n) (hX : 1 ≤ X) :
    1 / 3 ≤ ∑ q ∈ Icc 1 X, cc n q := by
  have hc : cc n = restr n (fun p => ¬ p ∣ n) * restr n (fun p => p ∣ n) := by
    rw [← restr_conv n, mul_comm]
  rw [hc, sum_conv]
  set V := restr n (fun p => ¬ p ∣ n) with hV
  set U := restr n (fun p => p ∣ n) with hU
  have hUmono : ∀ Y, Y ≤ X → ∑ k ∈ Icc 1 Y, U k ≤ ∑ k ∈ Icc 1 X, U k := fun Y hY =>
    sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_right hY) (fun k _ _ => uu_nonneg n k)
  have hU1 : 1 ≤ ∑ k ∈ Icc 1 X, U k := by
    have : U 1 ≤ ∑ k ∈ Icc 1 X, U k :=
      single_le_sum (f := U) (fun k _ => uu_nonneg n k) (mem_Icc.mpr ⟨le_rfl, hX⟩)
    rwa [(restr_mult n _).map_one] at this
  have hV1 : V 1 = 1 := (restr_mult n _).map_one
  have hterm : ∀ d ∈ Icc 1 X, -|V d| * (∑ k ∈ Icc 1 X, U k) + (if d = 1 then 2 * ∑ k ∈ Icc 1 X, U k else 0)
      ≤ V d * ∑ k ∈ Icc 1 (X / d), U k := by
    intro d hd
    by_cases h1 : d = 1
    · subst h1
      rw [if_pos rfl, hV1]
      simp
      linarith
    · rw [if_neg h1]
      have hm := hUmono (X / d) (Nat.div_le_self _ _)
      have hn0 : 0 ≤ ∑ k ∈ Icc 1 (X / d), U k := sum_nonneg (fun k _ => uu_nonneg n k)
      have hab := neg_abs_le (V d)
      nlinarith [abs_nonneg (V d), mul_le_mul_of_nonneg_left hm (abs_nonneg (V d)),
        mul_le_mul_of_nonneg_right hab hn0]
  have hsum := sum_le_sum hterm
  rw [sum_add_distrib, ← sum_mul, sum_neg_distrib, sum_ite_eq' ] at hsum
  have hT := T_bound n X hn
  have h1X : (1 : ℕ) ∈ Icc 1 X := mem_Icc.mpr ⟨le_rfl, hX⟩
  rw [if_pos h1X] at hsum
  nlinarith [hsum, hT, hU1]

end
end GoldbachExplicitModeledMajor

namespace GoldbachExplicitModeledMajor
open Finset ArithmeticFunction
open scoped ComplexConjugate
noncomputable section

private theorem mass_nonneg (n q : ℕ) : 0 ≤ kernelMass n (width n q) := by
  apply intervalIntegral.integral_nonneg
  · linarith only [width_nonneg n q]
  · intro t _; positivity

private theorem weighted_prefix_lower (A B : ℕ) (f w : ℕ → ℝ) (k : ℝ)
    (hab : A ≤ B) (hk : 0 ≤ k) (hw : ∀ i ≥ A,0 ≤ w i) (hm : ∀ i ≥ A,w (i+1) ≤ w i)
    (hp : ∀ i ≥ A,i ≤ B → -k ≤ ∑ j ∈ Ioc A i,f j) :
    -(k*w A) ≤ ∑ j ∈ Ioc A B,f j*w j := by
  have strong (i : ℕ) (hi : A ≤ i) (hiB : i ≤ B) :
      w i*((∑ j ∈ Ioc A i,f j)+k) ≤ (∑ j ∈ Ioc A i,f j*w j)+k*w A := by
    induction i,hi using Nat.le_induction with
    | base => simp [mul_comm]
    | succ i hi ih =>
      have h := ih (by omega)
      have hmono := hm i hi
      have hx := hp i hi (by omega)
      rw [sum_Ioc_succ_top hi,sum_Ioc_succ_top hi]
      nlinarith only [h,mul_nonneg (sub_nonneg.mpr hmono) (show 0 ≤ (∑ j ∈ Ioc A i,f j)+k by linarith)]
  have h := strong B hab le_rfl
  have v := hp B hab le_rfl
  nlinarith only [h,mul_nonneg (hw B hab) (show 0 ≤ (∑ j ∈ Ioc A B, f j)+k by linarith)]


private theorem mass_anti (n i : ℕ) (hi : 1 ≤ i) :
    kernelMass n (width n (i + 1)) ≤ kernelMass n (width n i) := by
  have hi' : (0 : ℝ) < i := by exact_mod_cast hi
  have hw : width n (i + 1) ≤ width n i := by
    by_cases hn : n = 0
    · simp [width, hn]
    · unfold width
      have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
      have : (i : ℝ) ≤ ((i + 1 : ℕ) : ℝ) := by push_cast; linarith
      gcongr
  exact kernelMass_mono (width_nonneg n _) hw n

private theorem icc_split (f : ℕ → ℝ) {i : ℕ} (hi : 1 ≤ i) :
    ∑ q ∈ Icc 1 i, f q = f 1 + ∑ q ∈ Ioc 1 i, f q := by
  have : Icc 1 i = insert 1 (Ioc 1 i) := by
    ext k; simp only [mem_Icc, mem_insert, mem_Ioc]; omega
  rw [this, sum_insert (by simp)]

theorem major_floor (n : ℕ) (hn : 1 ≤ n) (he : Even n) :
    (n : ℝ) / 72 ≤ ∑ q ∈ Icc 1 (cutoff n), cc n q * kernelMass n (width n q) := by
  have hQ := cutoff_positive n
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hm1 : (n : ℝ) / 24 ≤ kernelMass n (width n 1) := by
    apply kernelMass_floor hn
    unfold width
    have : (1 : ℝ) ≤ cutoff n := by exact_mod_cast hQ
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    push_cast
    nlinarith
  have hlow := weighted_prefix_lower 1 (cutoff n) (fun j => cc n j) (fun j => kernelMass n (width n j))
    (2 / 3) hQ (by norm_num) (fun i _ => mass_nonneg n i)
    (fun i hi => mass_anti n i hi)
    (fun i hi hiQ => by
      have h1 := prefix_ge n i he hi
      have hs := icc_split (fun q => cc n q) hi
      rw [hs, (cc_mult n).map_one] at h1
      linarith)
  have hs : ∑ q ∈ Icc 1 (cutoff n), cc n q * kernelMass n (width n q) =
      cc n 1 * kernelMass n (width n 1) + ∑ q ∈ Ioc 1 (cutoff n), cc n q * kernelMass n (width n q) := by
    exact icc_split (fun q => cc n q * kernelMass n (width n q)) hQ
  rw [hs, (cc_mult n).map_one]
  linarith

end
end GoldbachExplicitModeledMajor

theorem Conjectures.Goldbach.ExplicitModeledMajorFloor :
    let E (x : ℝ) := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I); let Q (n : ℕ) := (Nat.log 2 (n + 2)) ^ 2; let width (n q : ℕ) := (Q n : ℝ) / ((q : ℝ) * n); let K (n : ℕ) (β : ℝ) := ∑ k ∈ Finset.range (n + 1), E ((k : ℝ) * β); let ram (q h : ℕ) := ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), E ((h : ℝ) * a / q); let kernelMass (n : ℕ) (b : ℝ) := intervalIntegral (fun β => ‖K n β‖ ^ 2) (-b) b MeasureTheory.volume; let modeledMajor (n : ℕ) := ∑ q ∈ Finset.Icc 1 (Q n), ((ram q 1 / (q.totient : ℂ)) ^ 2 * (starRingEnd ℂ) (ram q n)) * (kernelMass n (width n q) : ℂ); ∀ n : ℕ, 1000000 ≤ n → Even n → (n : ℝ) / 72 ≤ (modeledMajor n).re := by
  intro E Q width K ram kernelMass modeledMajor n hn he
  have key := GoldbachExplicitModeledMajor.major_floor n (by omega) he
  refine key.trans (le_of_eq ?_)
  have h : modeledMajor n = ∑ q ∈ Finset.Icc 1 (GoldbachExplicitModeledMajor.cutoff n),
      GoldbachExplicitModeledMajor.coefficient q n *
        ((GoldbachExplicitModeledMajor.kernelMass n (GoldbachExplicitModeledMajor.width n q) : ℝ) : ℂ) := rfl
  rw [h, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro q _
  simp [GoldbachExplicitModeledMajor.cc_apply]
