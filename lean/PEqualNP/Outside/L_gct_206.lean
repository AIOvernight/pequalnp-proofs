import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.Gct206

open Finset

abbrev KSub (n k : ℕ) := {S : Finset (Fin n) // S.card = k}

def emb {n k : ℕ} (S : KSub n k) (σ : Equiv.Perm (Fin k)) : Fin k ↪ Fin n :=
  ⟨fun b => S.1.orderEmbOfFin S.2 (σ b), (S.1.orderEmbOfFin S.2).injective.comp σ.injective⟩

theorem range_emb {n k : ℕ} (S : KSub n k) (σ : Equiv.Perm (Fin k)) :
    Set.range (emb S σ) = (S.1 : Set (Fin n)) := by
  change Set.range ((S.1.orderEmbOfFin S.2) ∘ σ) = _
  rw [σ.surjective.range_comp, Finset.range_orderEmbOfFin]

theorem emb_bijective (n k : ℕ) :
    Function.Bijective (fun p : KSub n k × Equiv.Perm (Fin k) => emb p.1 p.2) := by
  constructor
  · rintro ⟨S, σ⟩ ⟨T, τ⟩ h
    simp only at h
    have hST : S = T := by
      apply Subtype.ext
      apply Finset.coe_injective
      rw [← range_emb S σ, ← range_emb T τ, h]
    subst hST
    have hστ : σ = τ := by
      ext b
      have := DFunLike.congr_fun h b
      exact congrArg Fin.val ((S.1.orderEmbOfFin S.2).injective this)
    rw [hστ]
  · intro i
    let S : KSub n k := ⟨Finset.univ.map i, by simp⟩
    have hmem : ∀ b, i b ∈ S.1 := fun b => by simp [S]
    let f : Fin k → Fin k := fun b => (S.1.orderIsoOfFin S.2).symm ⟨i b, hmem b⟩
    have hf : Function.Injective f := by
      intro b c hbc
      have := congrArg (fun x => ((S.1.orderIsoOfFin S.2 x : S.1) : Fin n)) hbc
      simp only [f, OrderIso.apply_symm_apply] at this
      exact i.injective this
    refine ⟨(S, Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf)), ?_⟩
    ext b
    simp only [emb, Function.Embedding.coeFn_mk, Equiv.ofBijective_apply]
    rw [← Finset.coe_orderIsoOfFin_apply]
    simp [f]

theorem sum_emb (n k : ℕ) (F : (Fin k ↪ Fin n) → ℂ) :
    ∑ i, F i = ∑ S : KSub n k, ∑ σ : Equiv.Perm (Fin k), F (emb S σ) := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_bijective _ (emb_bijective n k) (fun p => F (emb p.1 p.2)) F
    (fun _ => rfl)).symm

theorem sum_perm_perm (k : ℕ) (M : Matrix (Fin k) (Fin k) ℂ) :
    ∑ σ : Equiv.Perm (Fin k), ∑ τ : Equiv.Perm (Fin k), ∏ a, M (σ a) (τ a)
      = (k.factorial : ℂ) * M.permanent := by
  rw [Finset.sum_comm]
  have h : ∀ τ : Equiv.Perm (Fin k),
      ∑ σ : Equiv.Perm (Fin k), ∏ a, M (σ a) (τ a) = M.permanent := by
    intro τ
    have h1 : ∀ σ : Equiv.Perm (Fin k),
        ∏ a, M (σ a) (τ a) = ∏ b, M ((σ * τ⁻¹) b) b := by
      intro σ
      exact Fintype.prod_equiv τ _ _ (fun a => by simp)
    simp_rw [h1]
    unfold Matrix.permanent
    exact Fintype.sum_equiv (Equiv.mulRight τ⁻¹) _ _ (fun _ => rfl)
  simp_rw [h]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]

theorem injForm (n m k : ℕ) (t : Fin n × Fin m → ℂ) :
    (k.factorial : ℂ) * (∑ S : KSub n k, ∑ T : KSub m k,
      Matrix.permanent (Matrix.of fun i j : Fin k => t (S.1.orderEmbOfFin S.2 i,
        T.1.orderEmbOfFin T.2 j)))
      = ∑ i : Fin k ↪ Fin n, ∑ j : Fin k ↪ Fin m, ∏ a, t (i a, j a) := by
  rw [sum_emb n k]
  simp_rw [sum_emb m k (fun j => ∏ a, t (_, j a))]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun S _ => ?_)
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun T _ => ?_)
  rw [← sum_perm_perm]
  rfl

theorem sum_dite_card {n k : ℕ} (G : KSub n k → ℂ) :
    (∑ R : Finset (Fin n), if h : R.card = k then G ⟨R, h⟩ else 0) = ∑ S : KSub n k, G S := by
  have h1 : (∑ R : Finset (Fin n), if h : R.card = k then G ⟨R, h⟩ else 0)
      = ∑ R ∈ Finset.univ.filter (fun R : Finset (Fin n) => R.card = k),
          if h : R.card = k then G ⟨R, h⟩ else 0 := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun R _ => ?_)
    by_cases h : R.card = k <;> simp [h]
  rw [h1, Finset.sum_subtype (Finset.univ.filter (fun R : Finset (Fin n) => R.card = k))
    (p := fun R : Finset (Fin n) => R.card = k) (by simp)]
  refine Fintype.sum_congr _ _ (fun S => ?_)
  rw [dif_pos S.2]

theorem dite_form (n m k : ℕ) (t : Fin n × Fin m → ℂ) :
    (∑ R : Finset (Fin n), ∑ C : Finset (Fin m), if h : R.card = k ∧ C.card = k then
      Matrix.permanent (Matrix.of fun a b => t (R.orderEmbOfFin h.1 a, C.orderEmbOfFin h.2 b))
      else 0)
    = ∑ S : KSub n k, ∑ T : KSub m k,
      Matrix.permanent (Matrix.of fun i j : Fin k => t (S.1.orderEmbOfFin S.2 i,
        T.1.orderEmbOfFin T.2 j)) := by
  rw [← sum_dite_card (fun S : KSub n k => ∑ T : KSub m k,
      Matrix.permanent (Matrix.of fun i j : Fin k => t (S.1.orderEmbOfFin S.2 i,
        T.1.orderEmbOfFin T.2 j)))]
  refine Finset.sum_congr rfl (fun R _ => ?_)
  by_cases hR : R.card = k
  · rw [dif_pos hR]
    rw [← sum_dite_card (fun T : KSub m k =>
      Matrix.permanent (Matrix.of fun i j : Fin k => t (R.orderEmbOfFin hR i,
        T.1.orderEmbOfFin T.2 j)))]
    refine Finset.sum_congr rfl (fun C _ => ?_)
    by_cases hC : C.card = k
    · rw [dif_pos hC, dif_pos ⟨hR, hC⟩]
    · rw [dif_neg hC, dif_neg (fun h => hC h.2)]
  · rw [dif_neg hR]
    refine Finset.sum_eq_zero (fun C _ => ?_)
    rw [dif_neg (fun h => hR h.1)]

theorem sum_emb_fun {k : ℕ} {β : Type} [Fintype β] [DecidableEq β] (F : (Fin k → β) → ℂ) :
    (∑ j : Fin k ↪ β, F j) = ∑ f : Fin k → β, if Function.Injective f then F f else 0 := by
  rw [← Finset.sum_filter]
  rw [Finset.sum_subtype (Finset.univ.filter (fun f : Fin k → β => Function.Injective f))
    (p := fun f : Fin k → β => Function.Injective f) (by simp)]
  exact Fintype.sum_equiv (Equiv.subtypeInjectiveEquivEmbedding (Fin k) β).symm _ _ (fun _ => rfl)

theorem sum_one {β : Type} [Fintype β] [DecidableEq β] (F : β → ℂ) :
    (∑ j : Fin 1 ↪ β, F (j 0)) = ∑ b, F b := by
  rw [sum_emb_fun (fun f => F (f 0))]
  rw [← Fintype.sum_equiv (Equiv.funUnique (Fin 1) β).symm (fun b => F b)
    (fun f : Fin 1 → β => if Function.Injective f then F (f 0) else 0)]
  intro b
  have hinj : Function.Injective ((Equiv.funUnique (Fin 1) β).symm b) :=
    Function.injective_of_subsingleton _
  rw [if_pos hinj]
  rfl

theorem sum_two {β : Type} [Fintype β] [DecidableEq β] (F : β → β → ℂ) :
    (∑ j : Fin 2 ↪ β, F (j 0) (j 1)) = ∑ b, ∑ c, if b ≠ c then F b c else 0 := by
  rw [sum_emb_fun (fun f => F (f 0) (f 1))]
  rw [← Fintype.sum_prod_type']
  rw [← Fintype.sum_equiv (finTwoArrowEquiv β).symm (fun p : β × β => if p.1 ≠ p.2 then F p.1 p.2 else 0)
    (fun f : Fin 2 → β => if Function.Injective f then F (f 0) (f 1) else 0)]
  rintro ⟨b, c⟩
  have hiff : Function.Injective ((finTwoArrowEquiv β).symm (b, c)) ↔ b ≠ c := by
    constructor
    · intro h hbc
      have := @h 0 1 (by simpa [finTwoArrowEquiv] using hbc)
      exact absurd this (by decide)
    · intro h x y hxy
      fin_cases x <;> fin_cases y <;> simp_all [finTwoArrowEquiv]
  by_cases h : b ≠ c
  · rw [if_pos h, if_pos (hiff.2 h)]
    simp [finTwoArrowEquiv]
  · rw [if_neg h, if_neg (fun h' => h (hiff.1 h'))]

theorem sum_offdiag {β : Type} [Fintype β] [DecidableEq β] (f g : β → ℂ) :
    (∑ b, ∑ c, if b ≠ c then f b * g c else 0) = (∑ b, f b) * (∑ c, g c) - ∑ b, f b * g b := by
  have h : ∀ b c : β, (if b ≠ c then f b * g c else 0)
      = f b * g c - (if b = c then f b * g c else 0) := by
    intro b c
    by_cases hbc : b = c <;> simp [hbc]
  simp_rw [h, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [Finset.sum_mul_sum]

section cross
variable {n m : ℕ} (t : Fin (n + 1) × Fin (m + 1) → ℂ)
  (P1 : ∀ (i : Fin n) (j : Fin m), t (i.succ, j.succ) = 0)
  (P2 : ∑ j : Fin m, t (0, j.succ) = 0)
  (P3 : t (0, 0) + ∑ i : Fin n, t (i.succ, 0) = 0)

include P1 P2 in
theorem rowsum (i : Fin (n + 1)) : ∑ j, t (i, j) = t (i, 0) := by
  rw [Fin.sum_univ_succ]
  refine Fin.cases ?_ (fun i' => ?_) i
  · rw [P2, add_zero]
  · simp [P1]

include P1 in
theorem rowdot (i0 i1 : Fin (n + 1)) (h : i0 ≠ i1) :
    ∑ j, t (i0, j) * t (i1, j) = t (i0, 0) * t (i1, 0) := by
  rw [Fin.sum_univ_succ]
  have hz : ∀ j : Fin m, t (i0, j.succ) * t (i1, j.succ) = 0 := by
    intro j
    by_cases h0 : i0 = 0
    · have h1 : i1 ≠ 0 := fun h1 => h (h0.trans h1.symm)
      obtain ⟨i', rfl⟩ := Fin.exists_succ_eq.2 h1
      rw [P1, mul_zero]
    · obtain ⟨i', rfl⟩ := Fin.exists_succ_eq.2 h0
      rw [P1, zero_mul]
  simp [hz]

include P1 P2 P3 in
theorem inj_zero (k : ℕ) (hk : 1 ≤ k) :
    ∑ i : Fin k ↪ Fin (n + 1), ∑ j : Fin k ↪ Fin (m + 1), ∏ a, t (i a, j a) = 0 := by
  obtain rfl | rfl | h3 : k = 1 ∨ k = 2 ∨ 3 ≤ k := by omega
  · simp only [Fin.prod_univ_one]
    rw [sum_one (fun b => ∑ j : Fin 1 ↪ Fin (m + 1), t (b, j 0))]
    have hrow : ∀ b : Fin (n + 1), ∑ j : Fin 1 ↪ Fin (m + 1), t (b, j 0) = t (b, 0) := fun b => by
      rw [sum_one (fun c => t (b, c)), rowsum t P1 P2]
    simp only [hrow]
    rw [Fin.sum_univ_succ]
    exact P3
  · simp only [Fin.prod_univ_two]
    rw [sum_two (fun b c => ∑ j : Fin 2 ↪ Fin (m + 1), t (b, j 0) * t (c, j 1))]
    refine Finset.sum_eq_zero (fun b _ => Finset.sum_eq_zero (fun c _ => ?_))
    by_cases hbc : b ≠ c
    · rw [if_pos hbc, sum_two (fun x y => t (b, x) * t (c, y)),
        sum_offdiag (fun x => t (b, x)) (fun y => t (c, y)), rowsum t P1 P2, rowsum t P1 P2,
        rowdot t P1 b c hbc, sub_self]
    · rw [if_neg hbc]
  · refine Finset.sum_eq_zero (fun i _ => Finset.sum_eq_zero (fun j _ => ?_))
    have hex : ∃ a : Fin k, i a ≠ 0 ∧ j a ≠ 0 := by
      by_contra hno
      push Not at hno
      let a0 : Fin k := ⟨0, by omega⟩
      let a1 : Fin k := ⟨1, by omega⟩
      let a2 : Fin k := ⟨2, by omega⟩
      have h01 : a0 ≠ a1 := by simp [a0, a1, Fin.ext_iff]
      have h02 : a0 ≠ a2 := by simp [a0, a2, Fin.ext_iff]
      have h12 : a1 ≠ a2 := by simp [a1, a2, Fin.ext_iff]
      have key : ∀ x y : Fin k, x ≠ y → ¬ (i x = 0 ∧ i y = 0) ∧ ¬ (j x = 0 ∧ j y = 0) := by
        intro x y hxy
        exact ⟨fun h => hxy (i.injective (h.1.trans h.2.symm)),
          fun h => hxy (j.injective (h.1.trans h.2.symm))⟩
      have c0 := hno a0
      have c1 := hno a1
      have c2 := hno a2
      have k01 := key a0 a1 h01
      have k02 := key a0 a2 h02
      have k12 := key a1 a2 h12
      by_cases e0 : i a0 = 0 <;> by_cases e1 : i a1 = 0 <;> by_cases e2 : i a2 = 0 <;> simp_all
    obtain ⟨a, hi, hj⟩ := hex
    obtain ⟨i', hi'⟩ := Fin.exists_succ_eq.2 hi
    obtain ⟨j', hj'⟩ := Fin.exists_succ_eq.2 hj
    apply Finset.prod_eq_zero (Finset.mem_univ a)
    rw [← hi', ← hj', P1]

include P1 P2 P3 in
theorem level (k : ℕ) (hk : 1 ≤ k) :
    (∑ R : Finset (Fin (n + 1)), ∑ C : Finset (Fin (m + 1)), if h : R.card = k ∧ C.card = k then
      Matrix.permanent (Matrix.of fun a b => t (R.orderEmbOfFin h.1 a, C.orderEmbOfFin h.2 b))
      else 0) = 0 := by
  rw [dite_form]
  have h := injForm (n + 1) (m + 1) k t
  rw [inj_zero t P1 P2 P3 k hk] at h
  have hf : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero k)
  exact (mul_eq_zero.1 h).resolve_left hf

end cross

def row0 {m : ℕ} (w : ℂ) (u : Fin m → ℂ) : Fin (m + 2) → ℂ :=
  Fin.cons w (Fin.snoc u (-∑ j, u j))

def crossFun {n m : ℕ} (x : (Fin m → ℂ) × (Fin n → ℂ)) : Fin (n + 1) × Fin (m + 2) → ℂ :=
  fun p => Fin.cases (row0 (-∑ i, x.2 i) x.1 p.2)
    (fun i' => Fin.cases (x.2 i') (fun _ => 0) p.2) p.1

def crossMap (n m : ℕ) : ((Fin m → ℂ) × (Fin n → ℂ)) →ₗ[ℂ] (Fin (n + 1) × Fin (m + 2) → ℂ) where
  toFun := crossFun
  map_add' := by
    intro x y
    funext p
    obtain ⟨i, j⟩ := p
    refine Fin.cases ?_ (fun i' => ?_) i
    · refine Fin.cases ?_ (fun j' => ?_) j
      · simp [crossFun, row0, Finset.sum_add_distrib]
        ring
      · refine Fin.lastCases ?_ (fun j'' => ?_) j'
        · simp [crossFun, row0, Finset.sum_add_distrib]
          ring
        · simp [crossFun, row0]
    · refine Fin.cases ?_ (fun j' => ?_) j
      · simp [crossFun]
      · simp [crossFun]
  map_smul' := by
    intro c x
    funext p
    obtain ⟨i, j⟩ := p
    refine Fin.cases ?_ (fun i' => ?_) i
    · refine Fin.cases ?_ (fun j' => ?_) j
      · simp [crossFun, row0, Finset.mul_sum]
      · refine Fin.lastCases ?_ (fun j'' => ?_) j'
        · simp [crossFun, row0, Finset.mul_sum]
        · simp [crossFun, row0]
    · refine Fin.cases ?_ (fun j' => ?_) j
      · simp [crossFun]
      · simp [crossFun]

theorem crossMap_inj (n m : ℕ) : Function.Injective (crossMap n m) := by
  intro x y h
  have h' : crossFun x = crossFun y := h
  apply Prod.ext
  · funext j
    have := congrFun h' (0, j.castSucc.succ)
    simpa [crossFun, row0] using this
  · funext i
    have := congrFun h' (i.succ, 0)
    simpa [crossFun] using this

theorem cross_P1 {n m : ℕ} (x : (Fin m → ℂ) × (Fin n → ℂ)) (i : Fin n) (j : Fin (m + 1)) :
    crossFun x (i.succ, j.succ) = 0 := by
  simp [crossFun]

theorem cross_P2 {n m : ℕ} (x : (Fin m → ℂ) × (Fin n → ℂ)) :
    ∑ j : Fin (m + 1), crossFun x (0, j.succ) = 0 := by
  rw [Fin.sum_univ_castSucc]
  simp [crossFun, row0]

theorem cross_P3 {n m : ℕ} (x : (Fin m → ℂ) × (Fin n → ℂ)) :
    crossFun x (0, 0) + ∑ i : Fin n, crossFun x (i.succ, 0) = 0 := by
  simp [crossFun, row0]

end PEqualNP.Outside.Gct206

theorem PEqualNP.Outside.L_gct_206 : ∃ L : Submodule ℂ (Fin 4 × Fin 6 → ℂ), Module.finrank ℂ L = 7 ∧ (∀ t ∈ L, ∀ k : ℕ, 1 ≤ k → k ≤ 4 → (∑ R : Finset (Fin 4), ∑ C : Finset (Fin 6), if h : R.card = k ∧ C.card = k then Matrix.permanent (Matrix.of fun a b => t (R.orderEmbOfFin h.1 a, C.orderEmbOfFin h.2 b)) else 0) = 0) := by
  refine ⟨LinearMap.range (PEqualNP.Outside.Gct206.crossMap 3 4), ?_, ?_⟩
  · rw [LinearMap.finrank_range_of_inj (PEqualNP.Outside.Gct206.crossMap_inj 3 4)]
    simp
  · rintro t ⟨x, rfl⟩ k hk _
    exact PEqualNP.Outside.Gct206.level (PEqualNP.Outside.Gct206.crossFun x)
      (PEqualNP.Outside.Gct206.cross_P1 x) (PEqualNP.Outside.Gct206.cross_P2 x)
      (PEqualNP.Outside.Gct206.cross_P3 x) k hk
