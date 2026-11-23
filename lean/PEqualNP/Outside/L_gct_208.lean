import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.Gct208

theorem cons_inj {n m : ℕ} (j : Fin (m + 1)) (g : Fin n ↪ Fin m) :
    Function.Injective (Fin.cons j (fun i => j.succAbove (g i)) : Fin (n + 1) → Fin (m + 1)) := by
  intro a b
  refine Fin.cases ?_ (fun a' => ?_) a <;> refine Fin.cases ?_ (fun b' => ?_) b <;> intro h
  · rfl
  · simp only [Fin.cons_zero, Fin.cons_succ] at h
    exact absurd h.symm (Fin.succAbove_ne _ _)
  · simp only [Fin.cons_zero, Fin.cons_succ] at h
    exact absurd h (Fin.succAbove_ne _ _)
  · simp only [Fin.cons_succ] at h
    rw [g.injective (Fin.succAbove_right_injective h)]

def mk1 {n m : ℕ} (p : Fin (m + 1) × (Fin n ↪ Fin m)) : Fin (n + 1) ↪ Fin (m + 1) :=
  ⟨Fin.cons p.1 (fun i => p.1.succAbove (p.2 i)), cons_inj p.1 p.2⟩

theorem mk1_injective {n m : ℕ} : Function.Injective (mk1 (n := n) (m := m)) := by
  rintro ⟨j, g⟩ ⟨j', g'⟩ h
  have h0 : j = j' := by
    have := DFunLike.congr_fun h 0
    simpa [mk1] using this
  subst h0
  have hg : g = g' := by
    ext i
    have := DFunLike.congr_fun h i.succ
    simp only [mk1, Function.Embedding.coeFn_mk, Fin.cons_succ] at this
    exact congrArg Fin.val (Fin.succAbove_right_injective this)
  rw [hg]

theorem mk1_bijective {n m : ℕ} : Function.Bijective (mk1 (n := n) (m := m)) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨mk1_injective, ?_⟩
  rw [Fintype.card_prod, Fintype.card_embedding_eq, Fintype.card_embedding_eq]
  simp only [Fintype.card_fin]
  rw [Nat.succ_descFactorial_succ]

theorem emb_succ_sum {n m : ℕ} (F : (Fin (n + 1) → Fin (m + 1)) → ℂ) :
    (∑ f : Fin (n + 1) ↪ Fin (m + 1), F f) = ∑ j : Fin (m + 1), ∑ g : Fin n ↪ Fin m,
      F (Fin.cons j (fun i => j.succAbove (g i))) := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_bijective mk1 mk1_bijective
    (fun p => F (Fin.cons p.1 (fun i => p.1.succAbove (p.2 i)))) (fun f => F f)
    (fun _ => rfl)).symm

theorem emb_zero_sum {m : ℕ} (F : (Fin 0 → Fin m) → ℂ) :
    (∑ f : Fin 0 ↪ Fin m, F f) = F Fin.elim0 := by
  have hcard : Fintype.card (Fin 0 ↪ Fin m) = 1 := by
    rw [Fintype.card_embedding_eq]
    simp
  obtain ⟨f0, hf0⟩ := Fintype.card_eq_one_iff.1 hcard
  rw [Fintype.sum_eq_single f0 (fun f hf => absurd (hf0 f) hf)]
  congr 1
  funext i
  exact i.elim0

theorem emb4 (F : (Fin 4 → Fin 6) → ℂ) :
    (∑ f : Fin 4 ↪ Fin 6, F f) = ∑ j1 : Fin 6, ∑ j2 : Fin 5, ∑ j3 : Fin 4, ∑ j4 : Fin 3,
      F (Fin.cons j1 (fun i => j1.succAbove ((Fin.cons j2 (fun i => j2.succAbove
        ((Fin.cons j3 (fun i => j3.succAbove ((Fin.cons j4 (fun i => j4.succAbove
          ((Fin.elim0 : Fin 0 → Fin 2) i)) : Fin 1 → Fin 3) i)) : Fin 2 → Fin 4) i)) :
            Fin 3 → Fin 5) i))) := by
  rw [emb_succ_sum F]
  refine Finset.sum_congr rfl (fun j1 _ => ?_)
  rw [emb_succ_sum (fun g : Fin 3 → Fin 5 => F (Fin.cons j1 (fun i => j1.succAbove (g i))))]
  refine Finset.sum_congr rfl (fun j2 _ => ?_)
  rw [emb_succ_sum (fun g : Fin 2 → Fin 4 => F (Fin.cons j1 (fun i => j1.succAbove
    ((Fin.cons j2 (fun i => j2.succAbove (g i)) : Fin 3 → Fin 5) i))))]
  refine Finset.sum_congr rfl (fun j3 _ => ?_)
  rw [emb_succ_sum (fun g : Fin 1 → Fin 3 => F (Fin.cons j1 (fun i => j1.succAbove
    ((Fin.cons j2 (fun i => j2.succAbove ((Fin.cons j3 (fun i => j3.succAbove (g i)) :
      Fin 2 → Fin 4) i)) : Fin 3 → Fin 5) i))))]
  refine Finset.sum_congr rfl (fun j4 _ => ?_)
  rw [emb_zero_sum (fun g : Fin 0 → Fin 2 => F (Fin.cons j1 (fun i => j1.succAbove
    ((Fin.cons j2 (fun i => j2.succAbove ((Fin.cons j3 (fun i => j3.succAbove
      ((Fin.cons j4 (fun i => j4.succAbove (g i)) : Fin 1 → Fin 3) i)) :
        Fin 2 → Fin 4) i)) : Fin 3 → Fin 5) i))))]

def tfun (x : Fin 7 → ℂ) (p : Fin 4 × Fin 6) : ℂ :=
  if p.1.val = 0 then
    (if p.2.val = 0 then -(x 4 + x 5 + x 6) else if p.2.val = 1 then x 0 else if p.2.val = 2 then x 1
      else if p.2.val = 3 then x 2 else if p.2.val = 4 then x 3 else -(x 0 + x 1 + x 2 + x 3))
  else if p.2.val = 0 then (if p.1.val = 1 then x 4 else if p.1.val = 2 then x 5 else x 6)
  else 0

def tmap : (Fin 7 → ℂ) →ₗ[ℂ] (Fin 4 × Fin 6 → ℂ) where
  toFun := tfun
  map_add' := by
    intro x y
    funext p
    simp only [tfun, Pi.add_apply]
    split_ifs <;> ring
  map_smul' := by
    intro c x
    funext p
    simp only [tfun, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

theorem tmap_inj : Function.Injective tmap := by
  intro x y h
  have h' : tfun x = tfun y := h
  funext i
  have e0 := congrFun h' (0, 1)
  have e1 := congrFun h' (0, 2)
  have e2 := congrFun h' (0, 3)
  have e3 := congrFun h' (0, 4)
  have e4 := congrFun h' (1, 0)
  have e5 := congrFun h' (2, 0)
  have e6 := congrFun h' (3, 0)
  simp +decide only [tfun, reduceIte] at e0 e1 e2 e3 e4 e5 e6
  fin_cases i <;> assumption

set_option maxRecDepth 50000 in
set_option maxHeartbeats 20000000 in
theorem level (x : Fin 7 → ℂ) :
    (∑ f : Fin 4 ↪ Fin 6, ∏ i, (1 + tfun x (i, f i))) = 360 := by
  rw [emb4 (fun f => ∏ i, (1 + tfun x (i, f i)))]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.prod_univ_succ, Fin.prod_univ_zero,
    Fin.cons_zero, Fin.cons_succ]
  simp +decide only [tfun, reduceIte]
  ring

end PEqualNP.Outside.Gct208

theorem PEqualNP.Outside.L_gct_208 : ∃ L : Submodule ℂ (Fin 4 × Fin 6 → ℂ), (∀ t ∈ L, (∑ f : Fin 4 ↪ Fin 6, ∏ i, (1 + t (i, f i))) = 360) ∧ Module.finrank ℂ L = 7 := by
  refine ⟨LinearMap.range PEqualNP.Outside.Gct208.tmap, ?_, ?_⟩
  · rintro t ⟨x, rfl⟩
    exact PEqualNP.Outside.Gct208.level x
  · rw [LinearMap.finrank_range_of_inj PEqualNP.Outside.Gct208.tmap_inj]
    simp
