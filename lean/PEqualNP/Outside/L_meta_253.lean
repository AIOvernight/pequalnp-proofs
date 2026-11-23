import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_253 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (v : Fin n) (x : Fin n → Bool), decide (∃ u w : Fin n, G.Adj u w ∧ Function.update x v false u = true ∧ Function.update x v false w = true) = decide (∃ u w : Fin n, u ≠ v ∧ w ≠ v ∧ G.Adj u w ∧ x u = true ∧ x w = true) := by
  intro n G _ v x
  rw [decide_eq_decide]
  constructor
  · rintro ⟨u, w, huw, hu, hw⟩
    have hne1 : u ≠ v := by
      intro h
      rw [h, Function.update_self] at hu
      cases hu
    have hne2 : w ≠ v := by
      intro h
      rw [h, Function.update_self] at hw
      cases hw
    rw [Function.update_of_ne hne1] at hu
    rw [Function.update_of_ne hne2] at hw
    exact ⟨u, w, hne1, hne2, huw, hu, hw⟩
  · rintro ⟨u, w, hne1, hne2, huw, hu, hw⟩
    refine ⟨u, w, huw, ?_, ?_⟩
    · rw [Function.update_of_ne hne1]
      exact hu
    · rw [Function.update_of_ne hne2]
      exact hw
