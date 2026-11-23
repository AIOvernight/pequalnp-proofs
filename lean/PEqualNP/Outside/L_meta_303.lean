import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.Meta303

theorem dm_unique (q a a' i i' : ℕ) (hi : i < q) (hi' : i' < q) (h : q * a + i = q * a' + i') :
    a = a' ∧ i = i' := by
  have h1 : (q * a + i) / q = a := by
    rw [Nat.mul_add_div (by omega), Nat.div_eq_of_lt hi, add_zero]
  have h2 : (q * a' + i') / q = a' := by
    rw [Nat.mul_add_div (by omega), Nat.div_eq_of_lt hi', add_zero]
  have h3 : a = a' := by rw [← h1, h, h2]
  subst h3
  exact ⟨rfl, by omega⟩

theorem parity_count (k : ℕ) :
    ((Finset.range (2 * k)).filter (fun i => i % 2 = 1)).card = k := by
  rw [Finset.card_filter]
  induction k with
  | zero => simp
  | succ k ih =>
    have e : 2 * (k + 1) = 2 * k + 1 + 1 := by ring
    have h0 : (2 * k) % 2 = 0 := by omega
    have h1 : (2 * k + 1) % 2 = 1 := by omega
    rw [e, Finset.sum_range_succ, Finset.sum_range_succ, ih, h0, h1]
    simp

theorem parity_count' (k : ℕ) :
    ((Finset.range (2 * k)).filter (fun i => ¬ i % 2 = 1)).card = k := by
  have h := Finset.card_filter_add_card_filter_not (s := Finset.range (2 * k))
    (fun i => i % 2 = 1)
  rw [parity_count, Finset.card_range] at h
  omega

theorem base_exists (k m : ℕ) : ∃ B : Fin m × Fin m → ℕ,
    (∀ p, m ≤ B p) ∧ (∀ p, B p + 2 * k ≤ m + 2 * k * (m * m)) ∧
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
    rw [e2] at h2
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

end PEqualNP.Outside.Meta303

theorem PEqualNP.Outside.L_meta_303 : ∀ (m k : ℕ) (H : SimpleGraph (Fin m)) (T : Finset (Fin m)) (T' : Finset (Fin (m + 2 * k * (m * m)))), (∀ x : Fin (m + 2 * k * (m * m)), x ∈ T' ↔ (∃ u ∈ T, x.val = u.val) ∨ ∃ u v : Fin m, ∃ i : ℕ, i < 2 * k ∧ u < v ∧ H.Adj u v ∧ x.val = m + 2 * k * (u.val * m + v.val) + i ∧ (i % 2 = 1 ↔ u ∈ T)) → T'.card = T.card + k * H.edgeSet.ncard := by
  intro m k H T T' hmem
  classical
  obtain ⟨B, hBge, hBle, hBinj, hBdef⟩ := PEqualNP.Outside.Meta303.base_exists k m
  let E : Finset (Fin m × Fin m) := Finset.univ.filter (fun p => p.1 < p.2 ∧ H.Adj p.1 p.2)
  have hE : ∀ p, p ∈ E ↔ p.1 < p.2 ∧ H.Adj p.1 p.2 := fun p => by simp [E]
  have hEdge : H.edgeSet.ncard = E.card := by
    have himg : H.edgeSet = (fun p : Fin m × Fin m => s(p.1, p.2)) '' (E : Set (Fin m × Fin m)) := by
      apply Set.Subset.antisymm
      · intro e
        refine Sym2.ind (fun a b => ?_) e
        intro hab
        rw [SimpleGraph.mem_edgeSet] at hab
        rcases lt_trichotomy a b with h | h | h
        · exact ⟨(a, b), Finset.mem_coe.2 ((hE (a, b)).2 ⟨h, hab⟩), rfl⟩
        · exact absurd (h ▸ hab) H.irrefl
        · exact ⟨(b, a), Finset.mem_coe.2 ((hE (b, a)).2 ⟨h, hab.symm⟩), Sym2.eq_swap⟩
      · rintro e ⟨p, hp, rfl⟩
        rw [SimpleGraph.mem_edgeSet]
        exact ((hE p).1 (Finset.mem_coe.1 hp)).2
    have hinj : Set.InjOn (fun p : Fin m × Fin m => s(p.1, p.2)) (E : Set (Fin m × Fin m)) := by
      intro p hp q hq h
      have hp' := (hE p).1 (Finset.mem_coe.1 hp)
      have hq' := (hE q).1 (Finset.mem_coe.1 hq)
      rcases Sym2.eq_iff.1 h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Prod.ext h1 h2
      · have := hp'.1
        have := hq'.1
        rw [h1, h2] at hp'
        exact absurd hp'.1 (not_lt.2 (le_of_lt hq'.1))
    rw [himg, hinj.ncard_image, Set.ncard_coe_finset]
  let A : Finset ℕ := T.image Fin.val
  let W : Finset ((Fin m × Fin m) × ℕ) :=
    (E ×ˢ Finset.range (2 * k)).filter (fun q => (q.2 % 2 = 1 ↔ q.1.1 ∈ T))
  let Wimg : Finset ℕ := W.image (fun q => B q.1 + q.2)
  have hW : ∀ q, q ∈ W ↔ (q.1 ∈ E ∧ q.2 < 2 * k) ∧ (q.2 % 2 = 1 ↔ q.1.1 ∈ T) := fun q => by
    simp [W]
  have hinjW : Set.InjOn (fun q : (Fin m × Fin m) × ℕ => B q.1 + q.2) (W : Set _) := by
    intro q hq q' hq' h
    have h1 := ((hW q).1 (Finset.mem_coe.1 hq)).1.2
    have h2 := ((hW q').1 (Finset.mem_coe.1 hq')).1.2
    obtain ⟨e1, e2⟩ := hBinj q.1 q'.1 q.2 q'.2 h1 h2 h
    exact Prod.ext e1 e2
  have hWcard : W.card = k * E.card := by
    have h1 : W.card = ∑ p ∈ E, ((Finset.range (2 * k)).filter
        (fun i => (i % 2 = 1 ↔ p.1 ∈ T))).card := by
      rw [Finset.card_filter, Finset.sum_product]
      refine Finset.sum_congr rfl (fun p _ => ?_)
      rw [Finset.card_filter]
    rw [h1]
    have h2 : ∀ p ∈ E, ((Finset.range (2 * k)).filter
        (fun i => (i % 2 = 1 ↔ p.1 ∈ T))).card = k := by
      intro p _
      by_cases hp : p.1 ∈ T
      · have : (Finset.range (2 * k)).filter (fun i => (i % 2 = 1 ↔ p.1 ∈ T))
            = (Finset.range (2 * k)).filter (fun i => i % 2 = 1) := by
          refine Finset.filter_congr (fun i _ => ?_)
          simp [hp]
        rw [this, PEqualNP.Outside.Meta303.parity_count]
      · have : (Finset.range (2 * k)).filter (fun i => (i % 2 = 1 ↔ p.1 ∈ T))
            = (Finset.range (2 * k)).filter (fun i => ¬ i % 2 = 1) := by
          refine Finset.filter_congr (fun i _ => ?_)
          simp [hp]
        rw [this, PEqualNP.Outside.Meta303.parity_count']
    rw [Finset.sum_congr rfl h2, Finset.sum_const, smul_eq_mul, Nat.mul_comm]
  have himage : T'.image Fin.val = A ∪ Wimg := by
    ext n
    constructor
    · intro hn
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hn
      rcases (hmem x).1 hx with ⟨u, hu, hxu⟩ | ⟨u, v, i, hi, huv, hadj, hxv, hpar⟩
      · exact Finset.mem_union_left _ (Finset.mem_image.2 ⟨u, hu, hxu.symm⟩)
      · refine Finset.mem_union_right _ (Finset.mem_image.2 ⟨((u, v), i), ?_, ?_⟩)
        · exact (hW _).2 ⟨⟨(hE (u, v)).2 ⟨huv, hadj⟩, hi⟩, hpar⟩
        · show B (u, v) + i = x.val
          rw [hBdef, hxv]
    · intro hn
      rcases Finset.mem_union.1 hn with hn | hn
      · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hn
        have hlt : u.val < m + 2 * k * (m * m) := by
          have := u.isLt
          omega
        exact Finset.mem_image.2 ⟨⟨u.val, hlt⟩, (hmem _).2 (Or.inl ⟨u, hu, rfl⟩), rfl⟩
      · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hn
        have hq' := (hW q).1 hq
        have hlt : B q.1 + q.2 < m + 2 * k * (m * m) := by
          have := hBle q.1
          have := hq'.1.2
          omega
        have hEq := (hE q.1).1 hq'.1.1
        refine Finset.mem_image.2 ⟨⟨B q.1 + q.2, hlt⟩, (hmem _).2 (Or.inr
          ⟨q.1.1, q.1.2, q.2, hq'.1.2, hEq.1, hEq.2, ?_, hq'.2⟩), rfl⟩
        show B q.1 + q.2 = _
        rw [hBdef]
  have hdisj : Disjoint A Wimg := by
    rw [Finset.disjoint_left]
    intro n hn hn'
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.1 hn
    obtain ⟨q, _, hq⟩ := Finset.mem_image.1 hn'
    have h1 := hBge q.1
    have h2 := u.isLt
    have hq' : B q.1 + q.2 = u.val := hq
    omega
  have hcard : T'.card = (T'.image Fin.val).card :=
    (Finset.card_image_of_injective _ Fin.val_injective).symm
  have hA : A.card = T.card := Finset.card_image_of_injective _ Fin.val_injective
  have hWi : Wimg.card = W.card := Finset.card_image_of_injOn hinjW
  rw [hcard, himage, Finset.card_union_of_disjoint hdisj, hA, hWi, hWcard, hEdge]
