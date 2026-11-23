import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.Meta345

def E0 : List (Fin 5 × Fin 5) := [(0, 1), (0, 2), (1, 2), (0, 3), (0, 4), (3, 4)]

def sel (b0 b1 b2 b3 b4 b5 : Bool) (e : Fin 5 × Fin 5) : Bool :=
  (decide (e = (0, 1)) && b0) || (decide (e = (0, 2)) && b1) || (decide (e = (1, 2)) && b2) ||
    (decide (e = (0, 3)) && b3) || (decide (e = (0, 4)) && b4) || (decide (e = (3, 4)) && b5)

def Sb (b0 b1 b2 b3 b4 b5 : Bool) : Finset (Fin 5 × Fin 5) :=
  E0.toFinset.filter (fun e => sel b0 b1 b2 b3 b4 b5 e = true)

def wit (b0 b1 b2 b3 b4 b5 : Bool) : Finset (Fin 5) :=
  ([∅, {0}, {0}, {1}, {1}, {0}, {0}, {0, 1}, {0}, {1}, {2}, {1}, {0}, {2}, {1}, {3}, {0}, {1}, {2}, {1}, {0}, {2}, {1}, {4}, {3}, {1}, {2}, {1}, {1}, {2}, {1}, {3}, {3}, {0}, {0}, {1}, {1}, {0}, {0}, {3}, {0}, {1}, {2}, {1}, {0}, {2}, {1}, {4}, {0}, {1}, {2}, {1}, {0}, {2}, {1}, {3}, {0, 3}, {1}, {2}, {1}, {1}, {2}, {1}, {1, 2}] : List (Finset (Fin 5))).getD
    (b0.toNat + 2 * b1.toNat + 4 * b2.toNat + 8 * b3.toNat + 16 * b4.toNat + 32 * b5.toNat) ∅

def Pd (S : Finset (Fin 5 × Fin 5)) (C : Finset (Fin 5)) : Prop :=
  (∀ A ∈ C.powerset, A.Nonempty → A ≠ C → ∃ e ∈ S, (e.1 ∈ A ∧ e.2 ∈ C ∧ e.2 ∉ A) ∨ (e.2 ∈ A ∧ e.1 ∈ C ∧ e.1 ∉ A)) ∧ (∀ a b : Fin 5, a ∉ C → b ∉ C → (∃ x ∈ C, (x, a) ∈ S ∨ (a, x) ∈ S) → (∃ y ∈ C, (y, b) ∈ S ∨ (b, y) ∈ S) → ¬ ((a, b) ∈ E0 ∨ (b, a) ∈ E0)) ∧ (S.filter (fun e => e.1 ∈ C ∨ e.2 ∈ C)).card % 2 = 1

theorem S_eq (S : Finset (Fin 5 × Fin 5)) (hS : ∀ e ∈ S, e ∈ E0) :
    S = Sb (decide ((0, 1) ∈ S)) (decide ((0, 2) ∈ S)) (decide ((1, 2) ∈ S))
      (decide ((0, 3) ∈ S)) (decide ((0, 4) ∈ S)) (decide ((3, 4) ∈ S)) := by
  ext e
  simp only [Sb, Finset.mem_filter, List.mem_toFinset]
  constructor
  · intro he
    refine ⟨hS e he, ?_⟩
    have h := hS e he
    simp only [E0, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [sel, he]
  · rintro ⟨h, hsel⟩
    simp only [E0, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> simpa [sel] using hsel

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 4000000 in
theorem key : ∀ b0 b1 b2 b3 b4 b5 : Bool, (Sb b0 b1 b2 b3 b4 b5).Nonempty →
    Pd (Sb b0 b1 b2 b3 b4 b5) (wit b0 b1 b2 b3 b4 b5) := by
  intro b0 b1 b2 b3 b4 b5
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;>
    simp only [Pd] <;> decide

end PEqualNP.Outside.Meta345

theorem PEqualNP.Outside.L_meta_345 : ∀ E : List (Fin 5 × Fin 5), E = [(0, 1), (0, 2), (1, 2), (0, 3), (0, 4), (3, 4)] → ∀ S : Finset (Fin 5 × Fin 5), (∀ e ∈ S, e ∈ E) → S.Nonempty → ∃ C : Finset (Fin 5), (∀ A ⊆ C, A.Nonempty → A ≠ C → ∃ e ∈ S, (e.1 ∈ A ∧ e.2 ∈ C ∧ e.2 ∉ A) ∨ (e.2 ∈ A ∧ e.1 ∈ C ∧ e.1 ∉ A)) ∧ (∀ a b : Fin 5, a ∉ C → b ∉ C → (∃ x ∈ C, (x, a) ∈ S ∨ (a, x) ∈ S) → (∃ y ∈ C, (y, b) ∈ S ∨ (b, y) ∈ S) → ¬ ((a, b) ∈ E ∨ (b, a) ∈ E)) ∧ (S.filter (fun e => e.1 ∈ C ∨ e.2 ∈ C)).card % 2 = 1 := by
  intro E hE S hS hne
  subst hE
  have hS' : ∀ e ∈ S, e ∈ PEqualNP.Outside.Meta345.E0 := hS
  have hSeq := PEqualNP.Outside.Meta345.S_eq S hS'
  have hk := PEqualNP.Outside.Meta345.key (decide ((0, 1) ∈ S)) (decide ((0, 2) ∈ S))
    (decide ((1, 2) ∈ S)) (decide ((0, 3) ∈ S)) (decide ((0, 4) ∈ S)) (decide ((3, 4) ∈ S))
  rw [← hSeq] at hk
  obtain ⟨h1, h2, h3⟩ := hk hne
  exact ⟨_, fun A hA => h1 A (Finset.mem_powerset.2 hA), h2, h3⟩
