import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.Meta449

theorem dm_unique (q a a' i i' : ℕ) (hi : i < q) (hi' : i' < q) (h : q * a + i = q * a' + i') :
    a = a' ∧ i = i' := by
  have h1 : (q * a + i) / q = a := by
    rw [Nat.mul_add_div (by omega), Nat.div_eq_of_lt hi, add_zero]
  have h2 : (q * a' + i') / q = a' := by
    rw [Nat.mul_add_div (by omega), Nat.div_eq_of_lt hi', add_zero]
  have h3 : a = a' := by rw [← h1, h, h2]
  subst h3
  exact ⟨rfl, by omega⟩

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

theorem edge_key (D m b b' u v u' v' p p' : ℕ) (hD : 2 ≤ D) (hu : u < m) (hv : v < m)
    (hu' : u' < m) (hv' : v' < m) (hb : m ≤ b) (hb' : m ≤ b') (hp : p ≤ D) (hp' : p' ≤ D)
    (hblk : b = b' ∨ b + D ≤ b' ∨ b' + D ≤ b)
    (h : ((if p = 0 then u else b + p - 1) = (if p' = 0 then u' else b' + p' - 1) ∧
        (if p = D then v else b + p) = (if p' = D then v' else b' + p')) ∨
      ((if p = 0 then u else b + p - 1) = (if p' = D then v' else b' + p') ∧
        (if p = D then v else b + p) = (if p' = 0 then u' else b' + p' - 1))) :
    b = b' ∧ p = p' := by
  split_ifs at h <;> omega

end PEqualNP.Outside.Meta449

theorem PEqualNP.Outside.L_meta_449 : ∀ (m k : ℕ) (H : SimpleGraph (Fin m)) (Q : Fin m → Fin m → ℕ → Fin (m + 2 * k * (m * m)) → Prop) (S : SimpleGraph (Fin (m + 2 * k * (m * m)))), 1 ≤ k → (∀ (u v : Fin m) (p : ℕ) (x : Fin (m + 2 * k * (m * m))), Q u v p x ↔ (p = 0 ∧ x.val = u.val) ∨ (p = 2 * k + 1 ∧ x.val = v.val) ∨ (1 ≤ p ∧ p ≤ 2 * k ∧ x.val + 1 = m + 2 * k * (u.val * m + v.val) + p)) → (∀ x y : Fin (m + 2 * k * (m * m)), S.Adj x y ↔ ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ p : ℕ, p ≤ 2 * k ∧ ((Q u v p x ∧ Q u v (p + 1) y) ∨ (Q u v p y ∧ Q u v (p + 1) x))) → S.edgeSet.ncard = (2 * k + 1) * H.edgeSet.ncard := by
  intro m k H Q S hk hQ hS
  classical
  obtain ⟨B, hBge, hBle, hBinj, hBdef⟩ := PEqualNP.Outside.Meta449.base_exists k m
  have hblk : ∀ p p' : Fin m × Fin m, B p = B p' ∨ B p + 2 * k ≤ B p' ∨ B p' + 2 * k ≤ B p := by
    intro p p'
    rw [hBdef, hBdef]
    rcases lt_trichotomy (p.1.val * m + p.2.val) (p'.1.val * m + p'.2.val) with h | h | h
    · have := Nat.mul_le_mul_left (2 * k) (Nat.succ_le_of_lt h)
      rw [Nat.mul_succ] at this
      omega
    · rw [h]
      exact Or.inl rfl
    · have := Nat.mul_le_mul_left (2 * k) (Nat.succ_le_of_lt h)
      rw [Nat.mul_succ] at this
      omega
  have hBeq : ∀ p p' : Fin m × Fin m, B p = B p' → p = p' := by
    intro p p' h
    exact (hBinj p p' 0 0 (by omega) (by omega) (by omega)).1
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
  let av : Fin m × Fin m → ℕ → ℕ := fun e p => if p = 0 then e.1.val else B e + p - 1
  let cv : Fin m × Fin m → ℕ → ℕ := fun e p => if p = 2 * k then e.2.val else B e + p
  have hav : ∀ (e : Fin m × Fin m) (p : ℕ), p ≤ 2 * k → av e p < m + 2 * k * (m * m) := by
    intro e p hp
    have h1 := hBle e
    have h2 := e.1.isLt
    show (if p = 0 then e.1.val else B e + p - 1) < _
    split_ifs <;> omega
  have hcv : ∀ (e : Fin m × Fin m) (p : ℕ), p ≤ 2 * k → cv e p < m + 2 * k * (m * m) := by
    intro e p hp
    have h1 := hBle e
    have h2 := e.2.isLt
    show (if p = 2 * k then e.2.val else B e + p) < _
    split_ifs <;> omega
  have hQa : ∀ (e : Fin m × Fin m) (p : ℕ) (z : Fin (m + 2 * k * (m * m))), p ≤ 2 * k →
      (Q e.1 e.2 p z ↔ z.val = av e p) := by
    intro e p z hp
    have hb := hBdef e
    rw [hQ]
    show _ ↔ z.val = (if p = 0 then e.1.val else B e + p - 1)
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2, h3⟩) <;> split_ifs <;> omega
    · intro h
      split_ifs at h with h0
      · exact Or.inl ⟨h0, h⟩
      · exact Or.inr (Or.inr ⟨by omega, hp, by omega⟩)
  have hQc : ∀ (e : Fin m × Fin m) (p : ℕ) (z : Fin (m + 2 * k * (m * m))), p ≤ 2 * k →
      (Q e.1 e.2 (p + 1) z ↔ z.val = cv e p) := by
    intro e p z hp
    have hb := hBdef e
    rw [hQ]
    show _ ↔ z.val = (if p = 2 * k then e.2.val else B e + p)
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2, h3⟩) <;> split_ifs <;> omega
    · intro h
      split_ifs at h with h0
      · exact Or.inr (Or.inl ⟨by omega, h⟩)
      · exact Or.inr (Or.inr ⟨by omega, by omega, by omega⟩)
  let W : Finset ((Fin m × Fin m) × ℕ) := E ×ˢ Finset.range (2 * k + 1)
  have hW : ∀ q, q ∈ W ↔ q.1 ∈ E ∧ q.2 ≤ 2 * k := by
    intro q
    simp only [W, Finset.mem_product, Finset.mem_range]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by omega⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by omega⟩
  let phi : (Fin m × Fin m) × ℕ → Sym2 (Fin (m + 2 * k * (m * m))) := fun q =>
    if h : q.2 ≤ 2 * k then s((⟨av q.1 q.2, hav q.1 q.2 h⟩ : Fin (m + 2 * k * (m * m))),
      (⟨cv q.1 q.2, hcv q.1 q.2 h⟩ : Fin (m + 2 * k * (m * m)))) else s((⟨av q.1 0, hav q.1 0 (by omega)⟩ : Fin (m + 2 * k * (m * m))),
      (⟨cv q.1 0, hcv q.1 0 (by omega)⟩ : Fin (m + 2 * k * (m * m))))
  have hphi : ∀ q (h : q.2 ≤ 2 * k), phi q = s((⟨av q.1 q.2, hav q.1 q.2 h⟩ : Fin (m + 2 * k * (m * m))),
      (⟨cv q.1 q.2, hcv q.1 q.2 h⟩ : Fin (m + 2 * k * (m * m)))) := by
    intro q h
    show (if h : q.2 ≤ 2 * k then _ else _) = _
    rw [dif_pos h]
  have himg : S.edgeSet = phi '' (W : Set ((Fin m × Fin m) × ℕ)) := by
    apply Set.Subset.antisymm
    · intro e
      refine Sym2.ind (fun a b => ?_) e
      intro hab
      rw [SimpleGraph.mem_edgeSet] at hab
      obtain ⟨u, v, hlt, hadj, p, hp, h⟩ := (hS a b).1 hab
      refine ⟨((u, v), p), Finset.mem_coe.2 ((hW _).2 ⟨(hE (u, v)).2 ⟨hlt, hadj⟩, hp⟩), ?_⟩
      rw [hphi _ hp]
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have e1 := (hQa (u, v) p a hp).1 h1
        have e2 := (hQc (u, v) p b hp).1 h2
        rw [show a = ⟨av (u, v) p, hav (u, v) p hp⟩ from Fin.ext e1,
          show b = ⟨cv (u, v) p, hcv (u, v) p hp⟩ from Fin.ext e2]
      · have e1 := (hQa (u, v) p b hp).1 h1
        have e2 := (hQc (u, v) p a hp).1 h2
        rw [show b = ⟨av (u, v) p, hav (u, v) p hp⟩ from Fin.ext e1,
          show a = ⟨cv (u, v) p, hcv (u, v) p hp⟩ from Fin.ext e2]
        exact Sym2.eq_swap
    · rintro e ⟨q, hq, rfl⟩
      obtain ⟨hqE, hqp⟩ := (hW q).1 (Finset.mem_coe.1 hq)
      have hq' := (hE q.1).1 hqE
      rw [hphi q hqp, SimpleGraph.mem_edgeSet, hS]
      exact ⟨q.1.1, q.1.2, hq'.1, hq'.2, q.2, hqp, Or.inl
        ⟨(hQa q.1 q.2 _ hqp).2 rfl, (hQc q.1 q.2 _ hqp).2 rfl⟩⟩
  have hinj : Set.InjOn phi (W : Set ((Fin m × Fin m) × ℕ)) := by
    intro q hq q' hq' h
    obtain ⟨hqE, hqp⟩ := (hW q).1 (Finset.mem_coe.1 hq)
    obtain ⟨hqE', hqp'⟩ := (hW q').1 (Finset.mem_coe.1 hq')
    rw [hphi q hqp, hphi q' hqp'] at h
    have h' : (av q.1 q.2 = av q'.1 q'.2 ∧ cv q.1 q.2 = cv q'.1 q'.2) ∨
        (av q.1 q.2 = cv q'.1 q'.2 ∧ cv q.1 q.2 = av q'.1 q'.2) := by
      rcases Sym2.eq_iff.1 h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨congrArg Fin.val h1, congrArg Fin.val h2⟩
      · exact Or.inr ⟨congrArg Fin.val h1, congrArg Fin.val h2⟩
    obtain ⟨r1, r2⟩ := PEqualNP.Outside.Meta449.edge_key (2 * k) m (B q.1) (B q'.1) q.1.1.val q.1.2.val
      q'.1.1.val q'.1.2.val q.2 q'.2 (by omega) q.1.1.isLt q.1.2.isLt q'.1.1.isLt q'.1.2.isLt
      (hBge q.1) (hBge q'.1) hqp hqp' (hblk q.1 q'.1) h'
    exact Prod.ext (hBeq _ _ r1) r2
  rw [himg, hinj.ncard_image, Set.ncard_coe_finset, Finset.card_product, Finset.card_range, hEdge,
    Nat.mul_comm]
