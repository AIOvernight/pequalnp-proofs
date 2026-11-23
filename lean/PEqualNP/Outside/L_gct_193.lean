import Mathlib
import PEqualNP.Defs

set_option maxRecDepth 8000 in
theorem PEqualNP.Outside.L_gct_193 : ∀ c : ℂ, (∑ σ : Equiv.Perm (Fin 4), ∏ i : Fin 4, (1 + c * (if (σ i).val = i.val then (1 : ℂ) else if (σ i).val = (i.val + 1) % 4 then Complex.I else if (σ i).val = (i.val + 2) % 4 then -Complex.I else -1))) = 24 := by
  intro c
  rw [← (Equiv.Perm.decomposeFin (n := 3)).symm.sum_comp]
  simp only [Fintype.sum_prod_type]
  simp only [Fin.prod_univ_succ, Equiv.Perm.decomposeFin_symm_apply_zero,
    Equiv.Perm.decomposeFin_symm_apply_succ]
  simp only [← (Equiv.Perm.decomposeFin (n := 2)).symm.sum_comp, Fintype.sum_prod_type,
    Equiv.Perm.decomposeFin_symm_apply_zero, Equiv.Perm.decomposeFin_symm_apply_succ]
  simp only [← (Equiv.Perm.decomposeFin (n := 1)).symm.sum_comp, Fintype.sum_prod_type,
    Equiv.Perm.decomposeFin_symm_apply_zero, Equiv.Perm.decomposeFin_symm_apply_succ]
  simp only [← (Equiv.Perm.decomposeFin (n := 0)).symm.sum_comp, Fintype.sum_prod_type,
    Equiv.Perm.decomposeFin_symm_apply_zero, Equiv.Perm.decomposeFin_symm_apply_succ]
  simp only [Fin.sum_univ_succ, Fin.prod_univ_zero, Fintype.sum_unique]
  simp +decide only [Equiv.swap_apply_def, Fin.val_succ, Fin.val_zero, if_true, if_false, reduceIte]
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  have hI3 : Complex.I ^ 3 = -Complex.I := by rw [pow_succ, hI]; ring
  have hI4 : Complex.I ^ 4 = 1 := by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hI]; norm_num
  ring_nf
  simp only [hI, hI3, hI4]
  ring
