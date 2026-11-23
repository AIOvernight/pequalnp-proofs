import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_349 : ∀ (n b : ℕ) (G : SimpleGraph (Fin n)) (PV RV : Fin b → Finset (Fin n)) (PG RG : Fin b → Finset (Fin b)) (OV : Finset (Fin n)) (OG : Finset (Fin b)) (val : Finset (Fin n) → Fin b → Prop), (∀ i : Fin b, ∀ j ∈ PG i, j < i) → (∀ i : Fin b, ∀ j ∈ RG i, j < i) → (∀ (X : Finset (Fin n)) (i : Fin b), val X i ↔ (((∃ v ∈ PV i, v ∈ X) ∨ ∃ j ∈ PG i, val X j) ∧ ((∃ v ∈ RV i, v ∈ X) ∨ ∃ j ∈ RG i, val X j))) → (∀ X : Finset (Fin n), ((∃ v ∈ OV, v ∈ X) ∨ ∃ j ∈ OG, val X j) ↔ ∃ a ∈ X, ∃ c ∈ X, G.Adj a c) → ∀ (g H : Fin b) (u : Fin n), g ≠ H → u ∈ PV g → u ∉ RV g → (∀ i : Fin b, (u ∈ PV i ∨ u ∈ RV i) → i = g ∨ i = H) → ∀ I : Finset (Fin n), (∀ a ∈ I, ∀ c ∈ I, ¬ G.Adj a c) → u ∉ I → (∃ w ∈ I, G.Adj u w) → val I H → (∀ v ∈ PV g, v ∉ I) ∧ (∀ j ∈ PG g, ¬ val I j) ∧ H ∉ PG g := by
  intro n b G PV RV PG RG OV OG val hPG hRG hval hout g H u hgH huP huR hu I hI huI hw hH
  have hnotP : ¬ ((∃ v ∈ PV g, v ∈ I) ∨ ∃ j ∈ PG g, val I j) := by
    intro hP
    have D : ∀ N : ℕ, ∀ i : Fin b, i.val = N → (val (insert u I) i ↔ val I i) := by
      intro N
      induction N using Nat.strong_induction_on with
      | _ N ih =>
        intro i hi
        have IH : ∀ j : Fin b, j < i → (val (insert u I) j ↔ val I j) := fun j hj =>
          ih j.val (by rw [← hi]; exact hj) j rfl
        rw [hval (insert u I) i, hval I i]
        constructor
        · rintro ⟨h1, h2⟩
          by_cases hiH : i = H
          · rw [hiH]
            exact (hval I H).1 hH
          · by_cases hig : i = g
            · rw [hig] at h2 IH ⊢
              refine ⟨hP, ?_⟩
              rcases h2 with ⟨v, hv, hvI⟩ | ⟨j, hj, hjv⟩
              · rcases Finset.mem_insert.1 hvI with hvu | hvI
                · rw [hvu] at hv
                  exact absurd hv huR
                · exact Or.inl ⟨v, hv, hvI⟩
              · exact Or.inr ⟨j, hj, (IH j (hRG g j hj)).1 hjv⟩
            · have hnoP : u ∉ PV i := fun h => (hu i (Or.inl h)).elim hig hiH
              have hnoR : u ∉ RV i := fun h => (hu i (Or.inr h)).elim hig hiH
              refine ⟨?_, ?_⟩
              · rcases h1 with ⟨v, hv, hvI⟩ | ⟨j, hj, hjv⟩
                · rcases Finset.mem_insert.1 hvI with hvu | hvI
                  · rw [hvu] at hv
                    exact absurd hv hnoP
                  · exact Or.inl ⟨v, hv, hvI⟩
                · exact Or.inr ⟨j, hj, (IH j (hPG i j hj)).1 hjv⟩
              · rcases h2 with ⟨v, hv, hvI⟩ | ⟨j, hj, hjv⟩
                · rcases Finset.mem_insert.1 hvI with hvu | hvI
                  · rw [hvu] at hv
                    exact absurd hv hnoR
                  · exact Or.inl ⟨v, hv, hvI⟩
                · exact Or.inr ⟨j, hj, (IH j (hRG i j hj)).1 hjv⟩
        · rintro ⟨h1, h2⟩
          refine ⟨?_, ?_⟩
          · rcases h1 with ⟨v, hv, hvI⟩ | ⟨j, hj, hjv⟩
            · exact Or.inl ⟨v, hv, Finset.mem_insert_of_mem hvI⟩
            · exact Or.inr ⟨j, hj, (IH j (hPG i j hj)).2 hjv⟩
          · rcases h2 with ⟨v, hv, hvI⟩ | ⟨j, hj, hjv⟩
            · exact Or.inl ⟨v, hv, Finset.mem_insert_of_mem hvI⟩
            · exact Or.inr ⟨j, hj, (IH j (hRG i j hj)).2 hjv⟩
    have huOV : u ∉ OV := by
      intro h
      obtain ⟨a, ha, c, hc, hac⟩ := (hout {u}).1 (Or.inl ⟨u, h, Finset.mem_singleton_self u⟩)
      rw [Finset.mem_singleton] at ha hc
      rw [ha, hc] at hac
      exact G.irrefl hac
    obtain ⟨w, hwI, huw⟩ := hw
    have h1 : (∃ v ∈ OV, v ∈ insert u I) ∨ ∃ j ∈ OG, val (insert u I) j :=
      (hout (insert u I)).2 ⟨u, Finset.mem_insert_self u I, w, Finset.mem_insert_of_mem hwI, huw⟩
    have h2 : (∃ v ∈ OV, v ∈ I) ∨ ∃ j ∈ OG, val I j := by
      rcases h1 with ⟨v, hv, hvI⟩ | ⟨j, hj, hjv⟩
      · rcases Finset.mem_insert.1 hvI with hvu | hvI
        · rw [hvu] at hv
          exact absurd hv huOV
        · exact Or.inl ⟨v, hv, hvI⟩
      · exact Or.inr ⟨j, hj, (D j.val j rfl).1 hjv⟩
    obtain ⟨a, ha, c, hc, hac⟩ := (hout I).1 h2
    exact hI a ha c hc hac
  exact ⟨fun v hv hvI => hnotP (Or.inl ⟨v, hv, hvI⟩),
    fun j hj hjv => hnotP (Or.inr ⟨j, hj, hjv⟩),
    fun hmem => hnotP (Or.inr ⟨H, hmem, hH⟩)⟩
