import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_gct_152 : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (B : LinearMap.BilinForm ℂ V) (v : V) (A : Submodule ℂ V), B.Nondegenerate → B.IsSymm → B v v ≠ 0 → (∀ a ∈ A, B v a = 0) → (∀ a ∈ A, ∀ a' ∈ A, B a a' = 0) → 2 * Module.finrank ℂ A + 1 ≤ Module.finrank ℂ V := by
  intro V _ _ _ B v A hnd hsymm hv hvA hiso
  have hle : A ≤ B.orthogonal A := by
    intro a ha
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro a' ha'
    exact hiso a' ha' a ha
  have hvmem : v ∈ B.orthogonal A := by
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro a ha
    show B a v = 0
    rw [hsymm.eq a v]
    exact hvA a ha
  have hvnot : v ∉ A := fun h => hv (hiso v h v h)
  have hlt : A < B.orthogonal A := lt_of_le_of_ne hle (fun h => hvnot (h ▸ hvmem))
  have h1 := Submodule.finrank_lt_finrank_of_lt hlt
  have h2 := LinearMap.BilinForm.finrank_orthogonal hnd A
  have h3 := Submodule.finrank_le A
  omega
