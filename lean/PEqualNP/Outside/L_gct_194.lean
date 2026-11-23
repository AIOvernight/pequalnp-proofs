import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.Gct194

def mk (p : Fin 5 × Equiv.Perm (Fin 4)) : Fin 4 ↪ Fin 5 :=
  ⟨fun j => p.1.succAbove (p.2 j), Fin.succAbove_right_injective.comp p.2.injective⟩

theorem mk_injective : Function.Injective mk := by
  rintro ⟨m, σ⟩ ⟨m', σ'⟩ h
  have hfun : ∀ j, m.succAbove (σ j) = m'.succAbove (σ' j) := fun j => DFunLike.congr_fun h j
  have hm : m = m' := by
    by_contra hne
    obtain ⟨z, hz⟩ := Fin.exists_succAbove_eq (Ne.symm hne)
    have h1 := hfun (σ.symm z)
    rw [Equiv.apply_symm_apply, hz] at h1
    exact Fin.succAbove_ne m' _ h1.symm
  subst hm
  have hσ : σ = σ' := by
    ext j
    exact congrArg Fin.val (Fin.succAbove_right_injective (hfun j))
  rw [hσ]

theorem mk_bijective : Function.Bijective mk := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨mk_injective, ?_⟩
  rw [Fintype.card_prod, Fintype.card_perm, Fintype.card_embedding_eq]
  simp [Fintype.card_fin]
  decide

theorem emb_sum (F : (Fin 4 → Fin 5) → ℂ) :
    (∑ f : Fin 4 ↪ Fin 5, F f) = ∑ m : Fin 5, ∑ σ : Equiv.Perm (Fin 4),
      F (fun j => m.succAbove (σ j)) := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_bijective mk mk_bijective
    (fun p => F (fun j => p.1.succAbove (p.2 j))) (fun f => F f) (fun _ => rfl)).symm

end PEqualNP.Outside.Gct194

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_gct_194 : ∀ c d : ℂ, (∑ f : Fin 4 ↪ Fin 5, ∏ j : Fin 4, (1 + (if (f j).val = 4 then d * (if j.val = 0 then (1 : ℂ) else if j.val = 1 then -1 else 0) else c * (if j.val = (f j).val then (1 : ℂ) else if j.val = ((f j).val + 1) % 4 then Complex.I else if j.val = ((f j).val + 2) % 4 then -Complex.I else -1)))) = 120 := by
  intro c d
  refine (PEqualNP.Outside.Gct194.emb_sum (fun f => ∏ j : Fin 4, (1 + (if (f j).val = 4 then d * (if j.val = 0 then (1 : ℂ) else if j.val = 1 then -1 else 0) else c * (if j.val = (f j).val then (1 : ℂ) else if j.val = ((f j).val + 1) % 4 then Complex.I else if j.val = ((f j).val + 2) % 4 then -Complex.I else -1))))).trans ?_
  simp only [← (Equiv.Perm.decomposeFin (n := 3)).symm.sum_comp, Fintype.sum_prod_type,
    Fin.prod_univ_succ, Equiv.Perm.decomposeFin_symm_apply_zero,
    Equiv.Perm.decomposeFin_symm_apply_succ]
  simp only [← (Equiv.Perm.decomposeFin (n := 2)).symm.sum_comp, Fintype.sum_prod_type,
    Equiv.Perm.decomposeFin_symm_apply_zero, Equiv.Perm.decomposeFin_symm_apply_succ]
  simp only [← (Equiv.Perm.decomposeFin (n := 1)).symm.sum_comp, Fintype.sum_prod_type,
    Equiv.Perm.decomposeFin_symm_apply_zero, Equiv.Perm.decomposeFin_symm_apply_succ]
  simp only [← (Equiv.Perm.decomposeFin (n := 0)).symm.sum_comp, Fintype.sum_prod_type,
    Equiv.Perm.decomposeFin_symm_apply_zero, Equiv.Perm.decomposeFin_symm_apply_succ]
  simp only [Fin.sum_univ_succ, Fin.prod_univ_zero, Fintype.sum_unique]
  simp +decide only [reduceIte]
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  have hI3 : Complex.I ^ 3 = -Complex.I := by rw [pow_succ, hI]; ring
  have hI4 : Complex.I ^ 4 = 1 := by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hI]; norm_num
  ring_nf
  simp only [hI, hI3, hI4]
  ring
