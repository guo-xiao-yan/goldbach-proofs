import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Linarith

private theorem R_eq (n q : ℕ) : (Finset.range q).filter (fun r => r.Coprime q ∧ ((n+q-r)%q).Coprime q) = (Finset.range q).filter (fun a => Nat.Coprime a q ∧ Nat.Coprime (n+q-a) q) := by
  apply Finset.filter_congr
  intro r _
  have h : Nat.Coprime ((n+q-r) % q) q ↔ Nat.Coprime (n+q-r) q := by
    unfold Nat.Coprime
    rw [(Nat.mod_modEq _ _).gcd_eq]
  rw [h]

private theorem crtU_aux :
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

theorem PEqualNP.Outside.L_goldbach_coset_unit_crt :
    let R := fun n q : ℕ => ((Finset.range q).filter (fun r => r.Coprime q ∧ ((n+q-r)%q).Coprime q)).card; ∀ n a b : ℕ, 0<a → 0<b → a.Coprime b → R n (a*b)=R n a*R n b := by
  intro R n a b ha hb hab
  show ((Finset.range (a*b)).filter (fun r => r.Coprime (a*b) ∧ ((n+(a*b)-r)%(a*b)).Coprime (a*b))).card = ((Finset.range a).filter (fun r => r.Coprime a ∧ ((n+a-r)%a).Coprime a)).card * ((Finset.range b).filter (fun r => r.Coprime b ∧ ((n+b-r)%b).Coprime b)).card
  rw [R_eq n (a*b), R_eq n a, R_eq n b]
  exact crtU_aux a b n ha hb hab
