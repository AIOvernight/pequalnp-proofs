import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.Meta456

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

theorem walk_lip {V : Type} (G : SimpleGraph V) (l : V → ℕ)
    (h : ∀ a b, G.Adj a b → l b ≤ l a + 1) : ∀ {a b : V} (w : G.Walk a b), l b ≤ l a + w.length := by
  intro a b w
  induction w with
  | nil => simp
  | cons hadj p ih =>
    have := h _ _ hadj
    rw [SimpleGraph.Walk.length_cons]
    omega

end PEqualNP.Outside.Meta456

theorem PEqualNP.Outside.L_meta_456 : ∀ (m k : ℕ) (H : SimpleGraph (Fin m)) (Q : Fin m → Fin m → ℕ → Fin (m + 2 * k * (m * m)) → Prop) (S : SimpleGraph (Fin (m + 2 * k * (m * m)))), 1 ≤ k → (∀ (u v : Fin m) (p : ℕ) (x : Fin (m + 2 * k * (m * m))), Q u v p x ↔ (p = 0 ∧ x.val = u.val) ∨ (p = 2 * k + 1 ∧ x.val = v.val) ∨ (1 ≤ p ∧ p ≤ 2 * k ∧ x.val + 1 = m + 2 * k * (u.val * m + v.val) + p)) → (∀ x y : Fin (m + 2 * k * (m * m)), S.Adj x y ↔ ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ p : ℕ, p ≤ 2 * k ∧ ((Q u v p x ∧ Q u v (p + 1) y) ∨ (Q u v p y ∧ Q u v (p + 1) x))) → ∀ x y : Fin (m + 2 * k * (m * m)), x.val < m → y.val < m → x ≠ y → ∀ p : S.Walk x y, 2 * k + 1 ≤ p.length := by
  intro m k H Q S hk hQ hS x y hx hy hxy w
  classical
  obtain ⟨B, hBge, hBle, hBinj, hBdef⟩ := PEqualNP.Outside.Meta456.base_exists k m
  let a : ℕ → ℕ := fun n => if n = x.val then 0 else 2 * k + 1
  let g : Fin m → Fin m → ℕ → ℕ := fun u v p => min (p + a u.val) (2 * k + 1 - p + a v.val)
  have ha : ∀ n, a n = 0 ∨ a n = 2 * k + 1 := by
    intro n
    by_cases h : n = x.val
    · exact Or.inl (if_pos h)
    · exact Or.inr (if_neg h)
  obtain ⟨l, hl0, hlint⟩ : ∃ l : Fin (m + 2 * k * (m * m)) → ℕ,
      (∀ z, z.val < m → l z = a z.val) ∧
      (∀ z u v p, 1 ≤ p → p ≤ 2 * k → z.val + 1 = B (u, v) + p → l z = g u v p) := by
    refine ⟨fun z => if hz : z.val < m then a z.val else
      if h : ∃ q : (Fin m × Fin m) × ℕ, 1 ≤ q.2 ∧ q.2 ≤ 2 * k ∧ z.val + 1 = B q.1 + q.2 then
        g h.choose.1.1 h.choose.1.2 h.choose.2 else 0, ?_, ?_⟩
    · intro z hz
      simp only [dif_pos hz]
    · intro z u v p hp1 hp2 hz
      have hnot : ¬ z.val < m := by
        have := hBge (u, v)
        omega
      have hex : ∃ q : (Fin m × Fin m) × ℕ, 1 ≤ q.2 ∧ q.2 ≤ 2 * k ∧ z.val + 1 = B q.1 + q.2 :=
        ⟨((u, v), p), hp1, hp2, hz⟩
      simp only [dif_neg hnot, dif_pos hex]
      obtain ⟨c1, c2, c3⟩ := hex.choose_spec
      obtain ⟨e1, e2⟩ := hBinj hex.choose.1 (u, v) (hex.choose.2 - 1) (p - 1) (by omega) (by omega)
        (by omega)
      have e3 : hex.choose.2 = p := by omega
      rw [e1, e3]
  have hQl : ∀ (u v : Fin m) (p : ℕ) (z : Fin (m + 2 * k * (m * m))), Q u v p z → l z = g u v p := by
    intro u v p z hq
    rcases (hQ u v p z).1 hq with ⟨rfl, hz⟩ | ⟨rfl, hz⟩ | ⟨hp1, hp2, hz⟩
    · rw [hl0 z (by rw [hz]; exact u.isLt), hz]
      have h1 := ha u.val
      have h2 := ha v.val
      show a u.val = min (0 + a u.val) (2 * k + 1 - 0 + a v.val)
      omega
    · rw [hl0 z (by rw [hz]; exact v.isLt), hz]
      have h1 := ha u.val
      have h2 := ha v.val
      show a v.val = min (2 * k + 1 + a u.val) (2 * k + 1 - (2 * k + 1) + a v.val)
      omega
    · exact hlint z u v p hp1 hp2 (by rw [hBdef]; exact hz)
  have hlip : ∀ z z' : Fin (m + 2 * k * (m * m)), S.Adj z z' → l z' ≤ l z + 1 := by
    intro z z' hadj
    obtain ⟨u, v, _, _, p, hp, h⟩ := (hS z z').1 hadj
    have hstep : g u v (p + 1) ≤ g u v p + 1 ∧ g u v p ≤ g u v (p + 1) + 1 := by
      show min (p + 1 + a u.val) (2 * k + 1 - (p + 1) + a v.val) ≤
          min (p + a u.val) (2 * k + 1 - p + a v.val) + 1 ∧
        min (p + a u.val) (2 * k + 1 - p + a v.val) ≤
          min (p + 1 + a u.val) (2 * k + 1 - (p + 1) + a v.val) + 1
      omega
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [hQl u v p z h1, hQl u v (p + 1) z' h2]
      exact hstep.1
    · rw [hQl u v p z' h1, hQl u v (p + 1) z h2]
      exact hstep.2
  have hw := PEqualNP.Outside.Meta456.walk_lip S l hlip w
  have hlx : l x = 0 := by
    rw [hl0 x hx]
    exact if_pos rfl
  have hly : l y = 2 * k + 1 := by
    rw [hl0 y hy]
    exact if_neg (fun h => hxy (Fin.ext h.symm))
  omega
