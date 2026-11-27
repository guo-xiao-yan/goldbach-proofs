import Mathlib

namespace ThetaResidueOverlapAux

private theorem K (H L b i j : ℕ) (hb : b < L) (hij : i + j = 2*H) :
    i % L = b ↔ j % L = (2*H+L-b) % L := by
  have hL : 0 < L := by omega
  constructor
  · intro h
    have h1 := Nat.div_add_mod' i L
    have e : 2*H+L-b = j + L*(i/L+1) := by
      rw [mul_add, mul_one, mul_comm L (i/L)]; omega
    rw [e, Nat.add_mul_mod_self_left]
  · intro h
    have h1 := Nat.div_add_mod' j L
    have h2 := Nat.div_add_mod' (2*H+L-b) L
    rw [h] at h1
    have hlt : j / L < (2*H+L-b) / L := by
      by_contra hc
      have hc' : (2*H+L-b) / L ≤ j / L := not_lt.1 hc
      have := Nat.mul_le_mul_right L hc'
      omega
    obtain ⟨d, hd⟩ : ∃ d, (2*H+L-b) / L = j / L + 1 + d := ⟨(2*H+L-b) / L - j / L - 1, by omega⟩
    rw [hd, add_mul, add_mul, one_mul] at h2
    have hi : i = b + d * L := by omega
    rw [hi, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hb]

private theorem Q1 (H L b i : ℕ) (hb : b < L) (hi : i % L = b) (hle : i ≤ 2*H) :
    i / L < (2*H+L-b) / L := by
  have hL : 0 < L := by omega
  show i / L + 1 ≤ _
  rw [Nat.le_div_iff_mul_le hL, add_mul, one_mul]
  have := Nat.div_add_mod' i L
  omega

private theorem P (H L b : ℕ) (hb : b < L) (Q : ℕ → Prop) [DecidablePred Q] :
    ((Finset.univ : Finset (Fin (2*H+1))).filter (fun i => i.val % L = b ∧ Q (i.val / L))).card
      = ((Finset.range ((2*H+L-b)/L)).filter Q).card := by
  have hL : 0 < L := by omega
  refine Finset.card_nbij' (fun i => i.val / L)
    (fun t => (⟨min (b + L*t) (2*H), by omega⟩ : Fin (2*H+1))) ?_ ?_ ?_ ?_
  · intro i hi
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq, Finset.mem_filter, Finset.mem_range] at hi ⊢
    exact ⟨Q1 H L b i.val hb hi.1 (by omega), hi.2⟩
  · intro t ht
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq, Finset.mem_filter, Finset.mem_range, Finset.mem_coe] at ht ⊢
    have h1 : (t + 1) * L ≤ 2*H+L-b := (Nat.le_div_iff_mul_le hL).1 ht.1
    rw [add_mul, one_mul] at h1
    have e : min (b + L*t) (2*H) = b + t * L := by rw [mul_comm L t]; omega
    simp only [e]
    refine ⟨?_, ?_⟩
    · rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hb]
    · rw [Nat.add_mul_div_right _ _ hL, Nat.div_eq_of_lt hb]; simpa using ht.2
  · intro i hi
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hi
    have := Nat.div_add_mod' i.val L
    apply Fin.ext
    show min (b + L * (i.val / L)) (2*H) = i.val
    have h3 : i.val ≤ 2*H := by omega
    rw [mul_comm L]
    omega
  · intro t ht
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq, Finset.mem_filter, Finset.mem_range, Finset.mem_coe] at ht
    have h1 : (t + 1) * L ≤ 2*H+L-b := (Nat.le_div_iff_mul_le hL).1 ht.1
    rw [add_mul, one_mul] at h1
    have e : min (b + L*t) (2*H) = b + t * L := by rw [mul_comm L t]; omega
    show min (b + L*t) (2*H) / L = t
    rw [e, Nat.add_mul_div_right _ _ hL, Nat.div_eq_of_lt hb]; simp

private theorem E (H L b : ℕ) (hb : b < L) :
    ((Finset.univ : Finset (Fin (2*H+1))).filter (fun i => i.val % L = b)).card
      = ((Finset.univ : Finset (Fin (2*H+1))).filter (fun i => i.val % L = (2*H+L-b) % L)).card := by
  refine Finset.card_nbij' Fin.rev Fin.rev ?_ ?_ ?_ ?_
  · intro i hi
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hi ⊢
    exact (K H L b i.val (Fin.rev i).val hb (by simp [Fin.val_rev]; omega)).1 hi
  · intro i hi
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hi ⊢
    exact (K H L b (Fin.rev i).val i.val hb (by simp [Fin.val_rev]; omega)).2 hi
  · intro i _; simp
  · intro i _; simp

private theorem N1 (H L b : ℕ) (hb : b < L) :
    ((Finset.univ : Finset (Fin (2*H+1))).filter (fun i => i.val % L = b)).card = (2*H+L-b)/L := by
  have := P H L b hb (fun _ => True)
  simpa using this

private theorem H1 (H L b : ℕ) (hb : b < L) (U : Finset (Fin (2*H+1))) :
    (U.filter (fun i => i.val % L = b)).card + (U.filter (fun i => i.val % L = (2*H+L-b) % L)).card
      ≤ ((Finset.univ : Finset (Fin (2*H+1))).filter (fun i => i.val % L = b)).card
        + (U.filter (fun i => i.val % L = b ∧ i.rev ∈ U)).card := by
  set Ub := U.filter (fun i => i.val % L = b) with hUb
  set Uc := U.filter (fun i => i.val % L = (2*H+L-b) % L) with hUc
  have hV : Uc.image Fin.rev ⊆ (Finset.univ : Finset (Fin (2*H+1))).filter (fun i => i.val % L = b) := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨j, hj, rfl⟩ := hx
    rw [hUc, Finset.mem_filter] at hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (K H L b (Fin.rev j).val j.val hb (by simp [Fin.val_rev]; omega)).2 hj.2
  have hsub : Ub ∪ Uc.image Fin.rev ⊆ (Finset.univ : Finset (Fin (2*H+1))).filter (fun i => i.val % L = b) := by
    refine Finset.union_subset ?_ hV
    intro x hx
    simp only [hUb, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact hx.2
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_union_add_card_inter Ub (Uc.image Fin.rev)
  have h3 : (Uc.image Fin.rev).card = Uc.card := Finset.card_image_of_injective _ Fin.rev_injective
  have h4 : Ub ∩ Uc.image Fin.rev ⊆ U.filter (fun i => i.val % L = b ∧ i.rev ∈ U) := by
    intro x hx
    rw [Finset.mem_inter, Finset.mem_image] at hx
    obtain ⟨hx1, j, hj, hjx⟩ := hx
    rw [hUb, Finset.mem_filter] at hx1
    rw [hUc, Finset.mem_filter] at hj
    rw [Finset.mem_filter]
    refine ⟨hx1.1, hx1.2, ?_⟩
    rw [← hjx, Fin.rev_rev]; exact hj.1
  have h5 := Finset.card_le_card h4
  omega

private theorem R (H L b i j : ℕ) (hb : b < L) (hi : i % L = b) (hij : i + j = 2*H) :
    j / L = (2*H+L-b)/L - 1 - i/L := by
  have hL : 0 < L := by omega
  have hlt := Q1 H L b i hb hi (by omega)
  have h1 := Nat.div_add_mod' i L
  have h2 := Nat.div_add_mod' (2*H+L-b) L
  have hm : j % L = (2*H+L-b) % L := (K H L b i j hb hij).1 hi
  have hc : (2*H+L-b) % L < L := Nat.mod_lt _ hL
  obtain ⟨s, hs⟩ : ∃ s, (2*H+L-b) / L = i / L + 1 + s := ⟨(2*H+L-b) / L - i / L - 1, by omega⟩
  rw [hs, add_mul, add_mul, one_mul] at h2
  have hj : j = (2*H+L-b) % L + s * L := by omega
  rw [hj, Nat.add_mul_div_right _ _ hL, Nat.div_eq_of_lt hc]
  omega

private theorem LB (H L : ℕ) (hL : 0 < L) (A U : Finset (Fin (2*H+1)))
    (hs : ∀ b : Fin L, (U.filter (fun i => i.val % L = b.val)).card = (A.filter (fun i => i.val % L = b.val)).card) :
    ∑ b : Fin L, ((A.filter (fun i => i.val % L = b.val)).card
        + (A.filter (fun i => i.val % L = (2*H+L-b.val) % L)).card
        - ((Finset.univ : Finset (Fin (2*H+1))).filter (fun i => i.val % L = b.val)).card)
      ≤ (U.filter (fun i => i.rev ∈ U)).card := by
  have hd : (U.filter (fun i => i.rev ∈ U)).card
      = ∑ b ∈ Finset.range L, (U.filter (fun i => i.val % L = b ∧ i.rev ∈ U)).card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := fun i : Fin (2*H+1) => i.val % L) (t := Finset.range L)
      (fun x _ => Finset.mem_range.2 (Nat.mod_lt _ hL))]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.filter_filter]
    congr 1
    ext x; simp [and_comm]
  rw [hd, ← Fin.sum_univ_eq_sum_range (fun b => (U.filter (fun i => i.val % L = b ∧ i.rev ∈ U)).card) L]
  refine Finset.sum_le_sum fun b _ => ?_
  have h1 := H1 H L b.val b.2 U
  have h2 := hs b
  have h3 := hs ⟨(2*H+L-b.val) % L, Nat.mod_lt _ hL⟩
  simp only at h3
  omega

private theorem EQ (H L : ℕ) (hL : 0 < L) (A : Finset (Fin (2*H+1))) :
    ∃ U : Finset (Fin (2*H+1)),
      (∀ b : Fin L, (U.filter (fun i => i.val % L = b.val)).card = (A.filter (fun i => i.val % L = b.val)).card) ∧
      (U.filter (fun i => i.rev ∈ U)).card =
      ∑ b : Fin L, ((A.filter (fun i => i.val % L = b.val)).card
        + (A.filter (fun i => i.val % L = (2*H+L-b.val) % L)).card
        - ((Finset.univ : Finset (Fin (2*H+1))).filter (fun i => i.val % L = b.val)).card) := by
  set k : ℕ → ℕ := fun b => (A.filter (fun i => i.val % L = b)).card with hk
  have hkle : ∀ b, b < L → k b ≤ (2*H+L-b)/L := by
    intro b hb
    rw [← N1 H L b hb]
    exact Finset.card_le_card (fun x hx => by
      simp only [hk, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢; exact hx.2)
  refine ⟨Finset.univ.filter (fun i : Fin (2*H+1) => i.val / L < k (i.val % L)), ?_, ?_⟩
  · intro b
    have hb := b.2
    have e : (Finset.univ.filter (fun i : Fin (2*H+1) => i.val / L < k (i.val % L))).filter (fun i => i.val % L = b.val)
        = Finset.univ.filter (fun i : Fin (2*H+1) => i.val % L = b.val ∧ i.val / L < k b.val) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨h1, h2⟩; rw [h2] at h1; exact ⟨h2, h1⟩
      · rintro ⟨h1, h2⟩; exact ⟨by rw [h1]; exact h2, h1⟩
    rw [e, P H L b.val hb (fun t => t < k b.val)]
    have : (Finset.range ((2*H+L-b.val)/L)).filter (fun t => t < k b.val) = Finset.range (k b.val) := by
      have := hkle b.val hb
      ext t; simp only [Finset.mem_filter, Finset.mem_range]; omega
    rw [this, Finset.card_range]
  · have hd : (Finset.univ.filter (fun i : Fin (2*H+1) => i.val / L < k (i.val % L))).filter (fun i => i.rev ∈ Finset.univ.filter (fun i : Fin (2*H+1) => i.val / L < k (i.val % L)))
        = Finset.univ.filter (fun i : Fin (2*H+1) => i.val / L < k (i.val % L) ∧ i.rev.val / L < k (i.rev.val % L)) := by
      ext x; simp [Finset.mem_filter]
    rw [hd, Finset.card_eq_sum_card_fiberwise (f := fun i : Fin (2*H+1) => i.val % L) (t := Finset.range L)
      (fun x _ => Finset.mem_range.2 (Nat.mod_lt _ hL))]
    have hr : ∑ b : Fin L, ((A.filter (fun i => i.val % L = b.val)).card
        + (A.filter (fun i => i.val % L = (2*H+L-b.val) % L)).card
        - ((Finset.univ : Finset (Fin (2*H+1))).filter (fun i => i.val % L = b.val)).card)
        = ∑ b ∈ Finset.range L, (k b + k ((2*H+L-b) % L)
          - ((Finset.univ : Finset (Fin (2*H+1))).filter (fun i => i.val % L = b)).card) :=
      Fin.sum_univ_eq_sum_range (fun b => k b + k ((2*H+L-b) % L)
          - ((Finset.univ : Finset (Fin (2*H+1))).filter (fun i => i.val % L = b)).card) L
    rw [hr]
    refine Finset.sum_congr rfl fun b hb' => ?_
    have hb := Finset.mem_range.1 hb'
    have hcL : (2*H+L-b) % L < L := Nat.mod_lt _ hL
    have hN := N1 H L b hb
    have hkb := hkle b hb
    have hkc := hkle ((2*H+L-b) % L) hcL
    rw [← N1 H L ((2*H+L-b) % L) hcL, ← E H L b hb, hN] at hkc
    have e : (Finset.univ.filter (fun i : Fin (2*H+1) => i.val / L < k (i.val % L) ∧ i.rev.val / L < k (i.rev.val % L))).filter (fun i => i.val % L = b)
        = Finset.univ.filter (fun i : Fin (2*H+1) => i.val % L = b ∧
            (i.val / L < k b ∧ (2*H+L-b)/L - 1 - i.val / L < k ((2*H+L-b) % L))) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have hij : x.val + x.rev.val = 2*H := by simp [Fin.val_rev]; omega
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        rw [h3] at h1
        rw [(K H L b x.val x.rev.val hb hij).1 h3, R H L b x.val x.rev.val hb h3 hij] at h2
        exact ⟨h3, h1, h2⟩
      · rintro ⟨h3, h1, h2⟩
        refine ⟨⟨by rw [h3]; exact h1, ?_⟩, h3⟩
        rw [(K H L b x.val x.rev.val hb hij).1 h3, R H L b x.val x.rev.val hb h3 hij]
        exact h2
    rw [e, P H L b hb (fun t => t < k b ∧ (2*H+L-b)/L - 1 - t < k ((2*H+L-b) % L)), hN]
    have e2 : (Finset.range ((2*H+L-b)/L)).filter (fun t => t < k b ∧ (2*H+L-b)/L - 1 - t < k ((2*H+L-b) % L))
        = Finset.Ico ((2*H+L-b)/L - k ((2*H+L-b) % L)) (k b) := by
      ext t; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
    rw [e2, Nat.card_Ico]
    omega

end ThetaResidueOverlapAux

theorem Conjectures.Goldbach.ThetaResidueOverlapMinimum :
    ∀ (H L : ℕ), 0 < L → ∀ A : Finset (Fin (2*H+1)), let cnt := fun (U : Finset (Fin (2*H+1))) (b : ℕ) => (U.filter (fun i => i.val % L=b)).card; let hit := fun (U : Finset (Fin (2*H+1))) => (U.filter (fun i => i.rev ∈ U)).card; let same := fun (U : Finset (Fin (2*H+1))) => ∀ b : Fin L, cnt U b.val=cnt A b.val; let lower := ∑ b : Fin L, (cnt A b.val + cnt A ((2*H+L-b.val) % L) - cnt Finset.univ b.val); (∀ U, same U → lower ≤ hit U) ∧ ∃ U, same U ∧ hit U=lower := by
  intro H L hL A
  intro cnt hit same lower
  refine ⟨fun U hU => ThetaResidueOverlapAux.LB H L hL A U hU, ?_⟩
  obtain ⟨U, h1, h2⟩ := ThetaResidueOverlapAux.EQ H L hL A
  exact ⟨U, h1, h2⟩
