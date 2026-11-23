import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.Meta289

theorem dm_unique (q a a' i i' : ℕ) (hi : i < q) (hi' : i' < q) (h : q * a + i = q * a' + i') :
    a = a' ∧ i = i' := by
  have h1 : (q * a + i) / q = a := by
    rw [Nat.mul_add_div (by omega), Nat.div_eq_of_lt hi, add_zero]
  have h2 : (q * a' + i') / q = a' := by
    rw [Nat.mul_add_div (by omega), Nat.div_eq_of_lt hi', add_zero]
  have h3 : a = a' := by rw [← h1, h, h2]
  subst h3
  exact ⟨rfl, by omega⟩

theorem pairsum (f : ℕ → ℕ) (k : ℕ) (h : ∀ i, i + 1 < 2 * k → 1 ≤ f i + f (i + 1)) :
    k ≤ ∑ i ∈ Finset.range (2 * k), f i := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e : 2 * (k + 1) = 2 * k + 1 + 1 := by ring
    rw [e, Finset.sum_range_succ, Finset.sum_range_succ]
    have h1 := ih (fun i hi => h i (by omega))
    have h2 := h (2 * k) (by omega)
    omega

theorem pairsum' (f : ℕ → ℕ) (k : ℕ) (hk : 1 ≤ k)
    (h : ∀ i, i + 1 < 2 * k → 1 ≤ f i + f (i + 1)) (h0 : f 0 = 1) (hl : f (2 * k - 1) = 1) :
    k + 1 ≤ ∑ i ∈ Finset.range (2 * k), f i := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have e : 2 * (k' + 1) = 2 * k' + 1 + 1 := by ring
  have e' : 2 * (k' + 1) - 1 = 2 * k' + 1 := by omega
  rw [e'] at hl
  rw [e, Finset.sum_range_succ, Finset.sum_range_succ', hl, h0]
  have h1 := pairsum (fun i => f (i + 1)) k' (fun i hi => h (i + 1) (by omega))
  omega

theorem base_exists (k m : ℕ) (hk : 1 ≤ k) : ∃ B : Fin m × Fin m → ℕ,
    (∀ p, m ≤ B p) ∧ (∀ p, B p + 2 * k ≤ m + 2 * k * m * m) ∧
    (∀ p p' i i', i < 2 * k → i' < 2 * k → B p + i = B p' + i' → p = p' ∧ i = i') ∧
    (∀ p, B p = m + 2 * k * (p.1.val * m + p.2.val)) := by
  refine ⟨fun p => m + 2 * k * (p.1.val * m + p.2.val), fun p => Nat.le_add_right _ _, ?_, ?_,
    fun p => rfl⟩
  · intro p
    have h1 : p.1.val * m + p.2.val + 1 ≤ m * m := by
      have ha := Nat.mul_le_mul_right m (Nat.succ_le_of_lt p.1.isLt)
      have hb := p.2.isLt
      have e : (p.1.val + 1) * m = p.1.val * m + m := by ring
      rw [Nat.succ_eq_add_one, e] at ha
      omega
    have h2 := Nat.mul_le_mul_left (2 * k) h1
    have e2 : 2 * k * (p.1.val * m + p.2.val + 1) = 2 * k * (p.1.val * m + p.2.val) + 2 * k := by
      ring
    have e3 : 2 * k * m * m = 2 * k * (m * m) := by ring
    rw [e2] at h2
    rw [e3]
    show m + 2 * k * (p.1.val * m + p.2.val) + 2 * k ≤ m + 2 * k * (m * m)
    omega
  · intro p p' i i' hi hi' h
    have h' : 2 * k * (p.1.val * m + p.2.val) + i = 2 * k * (p'.1.val * m + p'.2.val) + i' := by
      simp only at h
      omega
    obtain ⟨hx, hii⟩ := dm_unique (2 * k) _ _ i i' hi hi' h'
    have hx' : m * p.1.val + p.2.val = m * p'.1.val + p'.2.val := by
      rw [Nat.mul_comm m, Nat.mul_comm m]
      exact hx
    obtain ⟨ha, hb⟩ := dm_unique m _ _ _ _ p.2.isLt p'.2.isLt hx'
    exact ⟨Prod.ext (Fin.ext ha) (Fin.ext hb), hii⟩

end PEqualNP.Outside.Meta289

theorem PEqualNP.Outside.L_meta_289 : ∀ (k m : ℕ) (H : SimpleGraph (Fin m)), 1 ≤ k → ∀ S : SimpleGraph (Fin (m + 2 * k * m * m)), S = SimpleGraph.fromRel (fun x y : Fin (m + 2 * k * m * m) => ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ i : Fin (2 * k), x.val = m + 2 * k * (u.val * m + v.val) + i.val ∧ ((i.val = 0 ∧ y.val = u.val) ∨ (i.val + 1 < 2 * k ∧ y.val = m + 2 * k * (u.val * m + v.val) + i.val + 1) ∨ (i.val + 1 = 2 * k ∧ y.val = v.val))) → ∀ U : Finset (Fin (m + 2 * k * m * m)), (∀ x y : Fin (m + 2 * k * m * m), S.Adj x y → x ∈ U ∨ y ∈ U) → ∀ R : Finset (Fin m), (∀ u : Fin m, u ∈ R ↔ (∃ x ∈ U, x.val = u.val) ∨ ∃ v : Fin m, u < v ∧ H.Adj u v ∧ (∀ x ∈ U, x.val ≠ u.val) ∧ (∀ x ∈ U, x.val ≠ v.val)) → (∀ u v : Fin m, H.Adj u v → u ∈ R ∨ v ∈ R) ∧ R.card + k * H.edgeSet.ncard ≤ U.card := by
  intro k m H hk S hS U hU R hR
  classical
  subst hS
  obtain ⟨B, hBge, hBle, hBinj, hBdef⟩ := PEqualNP.Outside.Meta289.base_exists k m hk
  let UN : Finset ℕ := U.image Fin.val
  have hUNcard : UN.card = U.card := Finset.card_image_of_injective _ Fin.val_injective
  have hcovN : ∀ x y : Fin (m + 2 * k * m * m), (SimpleGraph.fromRel (fun x y : Fin (m + 2 * k * m * m) => ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ i : Fin (2 * k), x.val = m + 2 * k * (u.val * m + v.val) + i.val ∧ ((i.val = 0 ∧ y.val = u.val) ∨ (i.val + 1 < 2 * k ∧ y.val = m + 2 * k * (u.val * m + v.val) + i.val + 1) ∨ (i.val + 1 = 2 * k ∧ y.val = v.val)))).Adj x y →
      x.val ∈ UN ∨ y.val ∈ UN := fun x y h =>
    (hU x y h).imp (Finset.mem_image_of_mem _) (Finset.mem_image_of_mem _)
  let E : Finset (Fin m × Fin m) := Finset.univ.filter (fun p => p.1 < p.2 ∧ H.Adj p.1 p.2)
  have hE : ∀ p, p ∈ E ↔ p.1 < p.2 ∧ H.Adj p.1 p.2 := fun p => by simp [E]
  have F0 : ∀ p ∈ E, B p + 0 ∈ UN ∨ p.1.val ∈ UN := by
    intro p hp
    have hp' := (hE p).1 hp
    have h1 := hBle p
    have h2 := hBge p
    have h3 := p.1.isLt
    exact hcovN ⟨B p + 0, by omega⟩ ⟨p.1.val, by omega⟩ (by
      rw [SimpleGraph.fromRel_adj]
      refine ⟨?_, Or.inl ⟨p.1, p.2, hp'.1, hp'.2, ⟨0, by omega⟩, ?_, Or.inl ⟨rfl, rfl⟩⟩⟩
      · intro h
        rw [Fin.mk.injEq] at h
        omega
      · show B p + 0 = _
        rw [hBdef])
  have Fi : ∀ p ∈ E, ∀ i, i + 1 < 2 * k → B p + i ∈ UN ∨ B p + (i + 1) ∈ UN := by
    intro p hp i hi
    have hp' := (hE p).1 hp
    have h1 := hBle p
    exact hcovN ⟨B p + i, by omega⟩ ⟨B p + (i + 1), by omega⟩ (by
      rw [SimpleGraph.fromRel_adj]
      refine ⟨?_, Or.inl ⟨p.1, p.2, hp'.1, hp'.2, ⟨i, by omega⟩, ?_, Or.inr (Or.inl ⟨hi, ?_⟩)⟩⟩
      · intro h
        rw [Fin.mk.injEq] at h
        omega
      · show B p + i = _
        rw [hBdef]
      · show B p + (i + 1) = _
        rw [hBdef]
        exact (Nat.add_assoc _ _ _).symm)
  have Fl : ∀ p ∈ E, B p + (2 * k - 1) ∈ UN ∨ p.2.val ∈ UN := by
    intro p hp
    have hp' := (hE p).1 hp
    have h1 := hBle p
    have h2 := hBge p
    have h3 := p.2.isLt
    exact hcovN ⟨B p + (2 * k - 1), by omega⟩ ⟨p.2.val, by omega⟩ (by
      rw [SimpleGraph.fromRel_adj]
      refine ⟨?_, Or.inl ⟨p.1, p.2, hp'.1, hp'.2, ⟨2 * k - 1, by omega⟩, ?_,
        Or.inr (Or.inr ⟨?_, rfl⟩)⟩⟩
      · intro h
        rw [Fin.mk.injEq] at h
        omega
      · show B p + (2 * k - 1) = _
        rw [hBdef]
      · show 2 * k - 1 + 1 = 2 * k
        omega)
  let f : Fin m × Fin m → ℕ → ℕ := fun p i => if B p + i ∈ UN then 1 else 0
  let Bad : Finset (Fin m × Fin m) := E.filter (fun p => p.1.val ∉ UN ∧ p.2.val ∉ UN)
  have hsum : ∀ p ∈ E, k + (if p.1.val ∉ UN ∧ p.2.val ∉ UN then 1 else 0)
      ≤ ∑ i ∈ Finset.range (2 * k), f p i := by
    intro p hp
    have hpair : ∀ i, i + 1 < 2 * k → 1 ≤ f p i + f p (i + 1) := by
      intro i hi
      rcases Fi p hp i hi with h | h
      · have : f p i = 1 := if_pos h
        omega
      · have : f p (i + 1) = 1 := if_pos h
        omega
    by_cases hbad : p.1.val ∉ UN ∧ p.2.val ∉ UN
    · rw [if_pos hbad]
      refine PEqualNP.Outside.Meta289.pairsum' (f p) k hk hpair ?_ ?_
      · exact if_pos ((F0 p hp).resolve_right hbad.1)
      · exact if_pos ((Fl p hp).resolve_right hbad.2)
    · rw [if_neg hbad]
      exact PEqualNP.Outside.Meta289.pairsum (f p) k hpair
  let W : Finset ((Fin m × Fin m) × ℕ) :=
    (E ×ˢ Finset.range (2 * k)).filter (fun q => B q.1 + q.2 ∈ UN)
  have hWcard : k * E.card + Bad.card ≤ W.card := by
    have h1 : W.card = ∑ p ∈ E, ∑ i ∈ Finset.range (2 * k), f p i := by
      rw [Finset.card_filter, Finset.sum_product]
    have h2 : ∑ p ∈ E, (k + (if p.1.val ∉ UN ∧ p.2.val ∉ UN then 1 else 0))
        ≤ ∑ p ∈ E, ∑ i ∈ Finset.range (2 * k), f p i := Finset.sum_le_sum hsum
    rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, ← Finset.card_filter] at h2
    rw [h1]
    have e : E.card * k = k * E.card := Nat.mul_comm _ _
    have hb : (Finset.filter (fun p : Fin m × Fin m => p.1.val ∉ UN ∧ p.2.val ∉ UN) E).card = Bad.card := rfl
    omega
  let A : Finset ℕ := UN.filter (fun x => x < m)
  have hUN : A.card + W.card ≤ UN.card := by
    have hinj : Set.InjOn (fun q : (Fin m × Fin m) × ℕ => B q.1 + q.2) (W : Set _) := by
      intro q hq q' hq' h
      have hq1 := (Finset.mem_filter.1 hq).1
      have hq1' := (Finset.mem_filter.1 hq').1
      rw [Finset.mem_product, Finset.mem_range] at hq1 hq1'
      obtain ⟨h1, h2⟩ := hBinj q.1 q'.1 q.2 q'.2 hq1.2 hq1'.2 h
      exact Prod.ext h1 h2
    rw [← Finset.card_image_of_injOn hinj, ← Finset.card_union_of_disjoint]
    · apply Finset.card_le_card
      intro x hx
      rcases Finset.mem_union.1 hx with hx | hx
      · exact (Finset.mem_filter.1 hx).1
      · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hx
        exact (Finset.mem_filter.1 hq).2
    · rw [Finset.disjoint_left]
      intro x hx hx'
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hx'
      have h1 := (Finset.mem_filter.1 hx).2
      have h2 := hBge q.1
      omega
  let T : Finset (Fin m) := (Finset.univ.filter (fun u : Fin m => u.val ∈ UN)) ∪ Bad.image Prod.fst
  have hTcov : ∀ u v : Fin m, H.Adj u v → u ∈ T ∨ v ∈ T := by
    have key : ∀ u v : Fin m, u < v → H.Adj u v → u ∈ T ∨ v ∈ T := by
      intro u v huv hadj
      by_cases hu : u.val ∈ UN
      · exact Or.inl (Finset.mem_union_left _ (by simp [hu]))
      · by_cases hv : v.val ∈ UN
        · exact Or.inr (Finset.mem_union_left _ (by simp [hv]))
        · refine Or.inl (Finset.mem_union_right _ (Finset.mem_image.2 ⟨(u, v), ?_, rfl⟩))
          exact Finset.mem_filter.2 ⟨(hE (u, v)).2 ⟨huv, hadj⟩, hu, hv⟩
    intro u v hadj
    rcases lt_trichotomy u v with h | h | h
    · exact key u v h hadj
    · exact absurd (h ▸ hadj) H.irrefl
    · exact (key v u h hadj.symm).symm
  have hT : T.card ≤ A.card + Bad.card := by
    refine (Finset.card_union_le _ _).trans (Nat.add_le_add ?_ Finset.card_image_le)
    rw [← Finset.card_image_of_injective _ Fin.val_injective]
    apply Finset.card_le_card
    intro x hx
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hx
    exact Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hu).2, u.isLt⟩
  have hEdge : H.edgeSet.ncard ≤ E.card := by
    have hsub : H.edgeSet ⊆ (fun p : Fin m × Fin m => s(p.1, p.2)) '' (E : Set (Fin m × Fin m)) := by
      intro e
      refine Sym2.ind (fun a b => ?_) e
      intro hab
      rw [SimpleGraph.mem_edgeSet] at hab
      rcases lt_trichotomy a b with h | h | h
      · exact ⟨(a, b), Finset.mem_coe.2 ((hE (a, b)).2 ⟨h, hab⟩), rfl⟩
      · exact absurd (h ▸ hab) H.irrefl
      · exact ⟨(b, a), Finset.mem_coe.2 ((hE (b, a)).2 ⟨h, hab.symm⟩), Sym2.eq_swap⟩
    refine (Set.ncard_le_ncard hsub ((Finset.finite_toSet E).image _)).trans ?_
    refine (Set.ncard_image_le (Finset.finite_toSet E)).trans ?_
    rw [Set.ncard_coe_finset]
  have hRT : R = T := by
    ext u
    rw [hR u]
    constructor
    · rintro (⟨x, hx, hxu⟩ | ⟨v, huv, hadj, h1, h2⟩)
      · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨Finset.mem_univ _,
          Finset.mem_image.2 ⟨x, hx, hxu⟩⟩)
      · refine Finset.mem_union_right _ (Finset.mem_image.2 ⟨(u, v), Finset.mem_filter.2
          ⟨(hE (u, v)).2 ⟨huv, hadj⟩, ?_, ?_⟩, rfl⟩)
        · intro hmem
          obtain ⟨x, hx, hxu⟩ := Finset.mem_image.1 hmem
          exact h1 x hx hxu
        · intro hmem
          obtain ⟨x, hx, hxv⟩ := Finset.mem_image.1 hmem
          exact h2 x hx hxv
    · intro hu
      rcases Finset.mem_union.1 hu with hu | hu
      · obtain ⟨x, hx, hxu⟩ := Finset.mem_image.1 (Finset.mem_filter.1 hu).2
        exact Or.inl ⟨x, hx, hxu⟩
      · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hu
        obtain ⟨hpE, hb1, hb2⟩ := Finset.mem_filter.1 hp
        have hp' := (hE p).1 hpE
        exact Or.inr ⟨p.2, hp'.1, hp'.2,
          fun x hx hxu => hb1 (Finset.mem_image.2 ⟨x, hx, hxu⟩),
          fun x hx hxv => hb2 (Finset.mem_image.2 ⟨x, hx, hxv⟩)⟩
  rw [hRT]
  refine ⟨hTcov, ?_⟩
  have hmul : k * H.edgeSet.ncard ≤ k * E.card := Nat.mul_le_mul_left k hEdge
  omega
