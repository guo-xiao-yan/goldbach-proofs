import Mathlib

private theorem rpi_act {α : Type*} [Fintype α] [DecidableEq α] (σ : α → α) (A : Finset α)
    (K : Matrix α α ℂ) (h1 : ∀ x ∈ A, K x (σ x) = 1)
    (h0 : ∀ x y, ¬(x ∈ A ∧ y = σ x) → K x y = 0) (v : α → ℂ) (x : α) :
    K.mulVecLin v x = if x ∈ A then v (σ x) else 0 := by
  rw [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct]
  by_cases hx : x ∈ A
  · rw [if_pos hx, Finset.sum_eq_single (σ x)]
    · simp [h1 x hx]
    · intro y _ hy
      rw [h0 x y (fun h => hy h.2)]
      simp
    · intro h
      exact absurd (Finset.mem_univ _) h
  · rw [if_neg hx]
    apply Finset.sum_eq_zero
    intro y _
    rw [h0 x y (fun h => hx h.1)]
    simp

private theorem rpi_sq {α : Type*} [Fintype α] [DecidableEq α] (σ : α → α)
    (hσ : ∀ x, σ (σ x) = x) (A : Finset α) (hA : ∀ x, σ x ∈ A ↔ x ∈ A)
    (K : Matrix α α ℂ) (h1 : ∀ x ∈ A, K x (σ x) = 1)
    (h0 : ∀ x y, ¬(x ∈ A ∧ y = σ x) → K x y = 0) :
    K * K = Matrix.diagonal (fun x => if x ∈ A then (1 : ℂ) else 0) := by
  ext x z
  rw [Matrix.mul_apply, Matrix.diagonal_apply]
  by_cases hx : x ∈ A
  · rw [Finset.sum_eq_single (σ x)]
    · rw [h1 x hx]
      have hsx : σ x ∈ A := (hA x).2 hx
      by_cases hz : z = x
      · subst hz
        rw [if_pos rfl, if_pos hx, one_mul]
        have := h1 (σ z) hsx
        rw [hσ] at this
        exact this
      · rw [if_neg (Ne.symm hz), one_mul]
        apply h0
        rintro ⟨_, h⟩
        exact hz (by rw [h, hσ])
    · intro y _ hy
      rw [h0 x y (fun h => hy h.2)]
      simp
    · intro h
      exact absurd (Finset.mem_univ _) h
  · rw [Finset.sum_eq_zero]
    · split_ifs <;> simp_all
    · intro y _
      rw [h0 x y (fun h => hx h.1)]
      simp

private theorem rpi_mem {α : Type*} [Fintype α] [DecidableEq α] (σ : α → α) (A : Finset α)
    (K : Matrix α α ℂ) (h1 : ∀ x ∈ A, K x (σ x) = 1)
    (h0 : ∀ x y, ¬(x ∈ A ∧ y = σ x) → K x y = 0) (s : ℂ) (v : α → ℂ) :
    v ∈ Module.End.eigenspace K.mulVecLin s ↔
      ∀ x, (if x ∈ A then v (σ x) else 0) = s * v x := by
  rw [Module.End.mem_eigenspace_iff]
  constructor
  · intro h x
    have := congrFun h x
    rw [rpi_act σ A K h1 h0] at this
    simpa using this
  · intro h
    funext x
    rw [rpi_act σ A K h1 h0]
    simpa using h x

private theorem rpi_dim {α : Type*} [Fintype α] [DecidableEq α] (σ : α → α)
    (hσ : ∀ x, σ (σ x) = x) (A : Finset α) (hA : ∀ x, σ x ∈ A ↔ x ∈ A)
    (K : Matrix α α ℂ) (h1 : ∀ x ∈ A, K x (σ x) = 1)
    (h0 : ∀ x y, ¬(x ∈ A ∧ y = σ x) → K x y = 0) (s : ℂ) (hs : s * s = 1)
    (T : Finset α) (hTA : ∀ x ∈ T, x ∈ A) (hTb : ∀ x ∈ A, x ∈ T ∨ σ x ∈ T ∨ (σ x = x ∧ s ≠ 1))
    (hTc : ∀ x ∈ T, σ x ∈ T → σ x = x) (hTe : ∀ x ∈ T, σ x = x → s = 1) :
    Module.finrank ℂ (Module.End.eigenspace K.mulVecLin s) = T.card := by
  classical
  have hs0 : s ≠ 0 := by
    rintro rfl
    simp at hs
  let f : Module.End.eigenspace K.mulVecLin s →ₗ[ℂ] (T → ℂ) :=
    (LinearMap.funLeft ℂ ℂ (Subtype.val : T → α)).comp (Submodule.subtype _)
  have hf : Function.Bijective f := by
    constructor
    · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro v hv
      apply Subtype.ext
      funext x
      have hmem := (rpi_mem σ A K h1 h0 s v.1).1 v.2
      have hT : ∀ y ∈ T, v.1 y = 0 := by
        intro y hy
        have := congrFun hv ⟨y, hy⟩
        simpa [f] using this
      by_cases hx : x ∈ A
      · rcases hTb x hx with h | h | ⟨hfix, hs1⟩
        · exact hT x h
        · have := hmem x
          rw [if_pos hx, hT _ h] at this
          rcases mul_eq_zero.1 this.symm with h' | h'
          · exact absurd h' hs0
          · exact h'
        · have := hmem x
          rw [if_pos hx, hfix] at this
          have h2 : (1 - s) * v.1 x = 0 := by linear_combination this
          rcases mul_eq_zero.1 h2 with h' | h'
          · exact absurd (by linear_combination -h') hs1
          · exact h'
      · have := hmem x
        rw [if_neg hx] at this
        rcases mul_eq_zero.1 this.symm with h' | h'
        · exact absurd h' hs0
        · exact h'
    · intro w
      let w' : α → ℂ := fun x => if h : x ∈ T then w ⟨x, h⟩ else 0
      let v : α → ℂ := fun x =>
        if x ∈ T then w' x else if x ∈ A then s * w' (σ x) else 0
      have hv : v ∈ Module.End.eigenspace K.mulVecLin s := by
        rw [rpi_mem σ A K h1 h0]
        intro x
        by_cases hx : x ∈ A
        · rw [if_pos hx]
          have hsx : σ x ∈ A := (hA x).2 hx
          have hσx : σ (σ x) = x := hσ x
          by_cases h2 : x ∈ T
          · by_cases h3 : σ x ∈ T
            · have hfix := hTc x h2 h3
              have hs1 := hTe x h2 hfix
              simp only [v, if_pos h2, if_pos h3, hs1, hfix, one_mul]
            · simp only [v, if_pos h2, if_neg h3, if_pos hsx, hσx]
          · by_cases h3 : σ x ∈ T
            · simp only [v, if_pos h3, if_neg h2, if_pos hx]
              calc w' (σ x) = (s * s) * w' (σ x) := by rw [hs, one_mul]
                _ = s * (s * w' (σ x)) := by ring
            · obtain ⟨hfix, _⟩ := (hTb x hx).resolve_left h2 |>.resolve_left h3
              have hw : w' x = 0 := by simp [w', h2]
              simp [v, hfix, h2, hx, hw]
        · rw [if_neg hx]
          have h2 : x ∉ T := fun h => hx (hTA x h)
          simp only [v, if_neg h2, if_neg hx, mul_zero]
      refine ⟨⟨v, hv⟩, ?_⟩
      funext ⟨y, hy⟩
      simp [f, v, w', hy]
  have e := LinearEquiv.ofBijective f hf
  rw [e.finrank_eq, Module.finrank_fintype_fun_eq_card, Fintype.card_coe]

private theorem rpi_count {α : Type*} [Fintype α] [DecidableEq α] (σ : α → α)
    (hσ : ∀ x, σ (σ x) = x) (A : Finset α) (hA : ∀ x, σ x ∈ A ↔ x ∈ A)
    (val : α → ℕ) (hval : Function.Injective val) :
    2 * (A.filter (fun x => val x ≤ val (σ x))).card = A.card + (A.filter (fun x => σ x = x)).card ∧
    2 * (A.filter (fun x => val x < val (σ x))).card = A.card - (A.filter (fun x => σ x = x)).card := by
  have hQ : (A.filter (fun x => val (σ x) < val x)).card = (A.filter (fun x => val x < val (σ x))).card := by
    apply Finset.card_nbij' σ σ
    · intro x hx
      simp only [Finset.mem_coe, Finset.mem_filter] at hx ⊢
      exact ⟨(hA x).2 hx.1, by rw [hσ]; exact hx.2⟩
    · intro x hx
      simp only [Finset.mem_coe, Finset.mem_filter] at hx ⊢
      exact ⟨(hA x).2 hx.1, by rw [hσ]; exact hx.2⟩
    · intro x _; exact hσ x
    · intro x _; exact hσ x
  have hsplit := Finset.card_filter_add_card_filter_not (s := A) (fun x => val (σ x) < val x)
  have hT1 : (A.filter (fun x => ¬ val (σ x) < val x)) = A.filter (fun x => val x ≤ val (σ x)) := by
    apply Finset.filter_congr
    intro x _
    omega
  rw [hT1, hQ] at hsplit
  have hsplit2 := Finset.card_filter_add_card_filter_not
    (s := A.filter (fun x => val x ≤ val (σ x))) (fun x => val x < val (σ x))
  have hP : (A.filter (fun x => val x ≤ val (σ x))).filter (fun x => val x < val (σ x))
      = A.filter (fun x => val x < val (σ x)) := by
    ext x
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨h, _⟩, h2⟩; exact ⟨h, h2⟩
    · rintro ⟨h, h2⟩; exact ⟨⟨h, h2.le⟩, h2⟩
  have hF : (A.filter (fun x => val x ≤ val (σ x))).filter (fun x => ¬ val x < val (σ x))
      = A.filter (fun x => σ x = x) := by
    ext x
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨h, h1⟩, h2⟩
      exact ⟨h, hval (by omega)⟩
    · rintro ⟨h, h2⟩
      refine ⟨⟨h, ?_⟩, ?_⟩ <;> rw [h2] <;> omega
  rw [hP, hF] at hsplit2
  have hle : (A.filter (fun x => σ x = x)).card ≤ A.card := Finset.card_le_card (Finset.filter_subset _ _)
  omega


theorem Conjectures.Goldbach.ReflectionPartialInvolution :
    ∀ (m : ℕ) [NeZero m] (N : ZMod m),
  let A := (Finset.univ : Finset (ZMod m)).filter (fun x => IsUnit x ∧ IsUnit (N-x))
  let F := A.filter (fun x => N-x=x)
  let K : Matrix (ZMod m) (ZMod m) ℂ := fun x y => if x ∈ A ∧ y=N-x then 1 else 0
  (K*K = Matrix.diagonal (fun x => if x ∈ A then (1 : ℂ) else 0)) ∧
    2 * Module.finrank ℂ (Module.End.eigenspace K.mulVecLin 1) = A.card+F.card ∧
    2 * Module.finrank ℂ (Module.End.eigenspace K.mulVecLin (-1)) = A.card-F.card := by
  intro m _ N A F K
  have hσ : ∀ x : ZMod m, N - (N - x) = x := fun x => sub_sub_cancel N x
  have hA : ∀ x : ZMod m, N - x ∈ A ↔ x ∈ A := by
    intro x
    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and, hσ]
    exact and_comm
  have h1 : ∀ x ∈ A, K x (N - x) = 1 := by
    intro x hx
    simp [K, hx]
  have h0 : ∀ x y, ¬(x ∈ A ∧ y = N - x) → K x y = 0 := by
    intro x y h
    simp only [K, if_neg h]
  have hc := rpi_count (fun x : ZMod m => N - x) hσ A hA ZMod.val (ZMod.val_injective m)
  set T1 := A.filter (fun x => ZMod.val x ≤ ZMod.val (N - x)) with hT1
  set T2 := A.filter (fun x => ZMod.val x < ZMod.val (N - x)) with hT2
  have hFeq : A.filter (fun x => N - x = x) = F := rfl
  have d1 : Module.finrank ℂ (Module.End.eigenspace K.mulVecLin 1) = T1.card := by
    apply rpi_dim (fun x : ZMod m => N - x) hσ A hA K h1 h0 1 (by norm_num) T1
    · intro x hx; exact (Finset.mem_filter.1 hx).1
    · intro x hx
      by_cases h : ZMod.val x ≤ ZMod.val (N - x)
      · exact Or.inl (Finset.mem_filter.2 ⟨hx, h⟩)
      · refine Or.inr (Or.inl (Finset.mem_filter.2 ⟨(hA x).2 hx, ?_⟩))
        show ZMod.val (N - x) ≤ ZMod.val (N - (N - x))
        rw [hσ]; omega
    · intro x hx hx'
      have a := (Finset.mem_filter.1 hx).2
      have b := (Finset.mem_filter.1 hx').2
      simp only [hσ] at b
      exact ZMod.val_injective m (by omega) |>.symm
    · intro _ _ _; rfl
  have d2 : Module.finrank ℂ (Module.End.eigenspace K.mulVecLin (-1)) = T2.card := by
    apply rpi_dim (fun x : ZMod m => N - x) hσ A hA K h1 h0 (-1) (by norm_num) T2
    · intro x hx; exact (Finset.mem_filter.1 hx).1
    · intro x hx
      by_cases h : ZMod.val x < ZMod.val (N - x)
      · exact Or.inl (Finset.mem_filter.2 ⟨hx, h⟩)
      · by_cases h' : N - x = x
        · exact Or.inr (Or.inr ⟨h', by norm_num⟩)
        · right
          left
          refine Finset.mem_filter.2 ⟨(hA x).2 hx, ?_⟩
          show ZMod.val (N - x) < ZMod.val (N - (N - x))
          rw [hσ]
          have : ZMod.val x ≠ ZMod.val (N - x) := fun e => h' (ZMod.val_injective m e).symm
          omega
    · intro x hx hx'
      have a := (Finset.mem_filter.1 hx).2
      have b := (Finset.mem_filter.1 hx').2
      simp only [hσ] at b
      omega
    · intro x hx hfix
      have a := (Finset.mem_filter.1 hx).2
      have hfix' : N - x = x := hfix
      rw [hfix'] at a
      omega
  refine ⟨?_, ?_, ?_⟩
  · exact rpi_sq (fun x : ZMod m => N - x) hσ A hA K h1 h0
  · rw [d1]; exact hc.1
  · rw [d2]; exact hc.2
