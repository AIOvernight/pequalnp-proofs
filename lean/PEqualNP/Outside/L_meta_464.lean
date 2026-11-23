import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.Meta464

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

theorem mem_tail {V : Type} {G : SimpleGraph V} : ∀ {u v : V} (p : G.Walk u v) (z : V),
    z ∈ p.support → z = u ∨ z ∈ p.support.tail := by
  intro u v p z h
  cases p with
  | nil =>
    simp at h
    exact Or.inl h
  | cons hadj q =>
    simp at h ⊢
    exact h

theorem pair_unique (a b f1 f2 g1 g2 : ℕ) (hab : a ≠ b) (hf : f1 < f2) (hg : g1 < g2)
    (h1 : a = f1 ∨ a = f2) (h2 : b = f1 ∨ b = f2) (h3 : a = g1 ∨ a = g2) (h4 : b = g1 ∨ b = g2) :
    f1 = g1 ∧ f2 = g2 := by
  omega

end PEqualNP.Outside.Meta464

theorem PEqualNP.Outside.L_meta_464 : ∀ (m k : ℕ) (H : SimpleGraph (Fin m)) (Q : Fin m → Fin m → ℕ → Fin (m + 2 * k * (m * m)) → Prop) (S : SimpleGraph (Fin (m + 2 * k * (m * m)))), 1 ≤ k → (∀ (u v : Fin m) (p : ℕ) (x : Fin (m + 2 * k * (m * m))), Q u v p x ↔ (p = 0 ∧ x.val = u.val) ∨ (p = 2 * k + 1 ∧ x.val = v.val) ∨ (1 ≤ p ∧ p ≤ 2 * k ∧ x.val + 1 = m + 2 * k * (u.val * m + v.val) + p)) → (∀ x y : Fin (m + 2 * k * (m * m)), S.Adj x y ↔ ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ p : ℕ, p ≤ 2 * k ∧ ((Q u v p x ∧ Q u v (p + 1) y) ∨ (Q u v p y ∧ Q u v (p + 1) x))) → ∀ (x : Fin (m + 2 * k * (m * m))) (c : S.Walk x x), c.IsCycle → 6 * k + 3 ≤ c.length := by
  intro m k H Q S hk hQ hS x c hc
  classical
  obtain ⟨B, hBge, hBle, hBinj, hBdef⟩ := PEqualNP.Outside.Meta464.base_exists k m
  have hQ0 : ∀ (u v : Fin m) (z : Fin (m + 2 * k * (m * m))), Q u v 0 z ↔ z.val = u.val := by
    intro u v z
    rw [hQ]
    constructor
    · rintro (⟨_, h⟩ | ⟨h, _⟩ | ⟨h, _⟩)
      · exact h
      · omega
      · omega
    · intro h
      exact Or.inl ⟨rfl, h⟩
  have hQl : ∀ (u v : Fin m) (z : Fin (m + 2 * k * (m * m))),
      Q u v (2 * k + 1) z ↔ z.val = v.val := by
    intro u v z
    rw [hQ]
    constructor
    · rintro (⟨h, _⟩ | ⟨_, h⟩ | ⟨_, h, _⟩)
      · omega
      · exact h
      · omega
    · intro h
      exact Or.inr (Or.inl ⟨rfl, h⟩)
  have hQi : ∀ (u v : Fin m) (p : ℕ) (z : Fin (m + 2 * k * (m * m))), 1 ≤ p → p ≤ 2 * k →
      (Q u v p z ↔ z.val + 1 = B (u, v) + p) := by
    intro u v p z h1 h2
    rw [hQ, hBdef]
    constructor
    · rintro (⟨h, _⟩ | ⟨h, _⟩ | ⟨_, _, h⟩)
      · omega
      · omega
      · exact h
    · intro h
      exact Or.inr (Or.inr ⟨h1, h2, h⟩)
  have hQuniq : ∀ (u v : Fin m) (p : ℕ) (z z' : Fin (m + 2 * k * (m * m))),
      Q u v p z → Q u v p z' → z = z' := by
    intro u v p z z' h1 h2
    rw [hQ] at h1 h2
    rcases h1 with ⟨a1, a2⟩ | ⟨a1, a2⟩ | ⟨a1, a2, a3⟩ <;>
      rcases h2 with ⟨b1, b2⟩ | ⟨b1, b2⟩ | ⟨b1, b2, b3⟩ <;> exact Fin.ext (by omega)
  let Vc : Finset (Fin (m + 2 * k * (m * m))) := c.support.toFinset
  have hVc : ∀ z, z ∈ Vc ↔ z ∈ c.support := fun z => List.mem_toFinset
  have hlen : Vc.card ≤ c.length := by
    have hsub : Vc ⊆ c.support.tail.toFinset := by
      intro z hz
      rw [List.mem_toFinset]
      rcases PEqualNP.Outside.Meta464.mem_tail c z ((hVc z).1 hz) with h | h
      · rw [h]
        exact SimpleGraph.Walk.end_mem_tail_support hc.not_nil
      · exact h
    refine (Finset.card_le_card hsub).trans ((List.toFinset_card_le _).trans ?_)
    rw [List.length_tail, SimpleGraph.Walk.length_support]
    omega
  have hN : ∀ z ∈ Vc, ∃ y1 y2, y1 ≠ y2 ∧ y1 ∈ Vc ∧ y2 ∈ Vc ∧ S.Adj z y1 ∧ S.Adj z y2 := by
    intro z hz
    have h2 := hc.ncard_neighborSet_toSubgraph_eq_two ((hVc z).1 hz)
    obtain ⟨y1, y2, hne, hset⟩ := Set.ncard_eq_two.1 h2
    have a1 : c.toSubgraph.Adj z y1 := by
      have : y1 ∈ c.toSubgraph.neighborSet z := by rw [hset]; simp
      exact this
    have a2 : c.toSubgraph.Adj z y2 := by
      have : y2 ∈ c.toSubgraph.neighborSet z := by rw [hset]; simp
      exact this
    exact ⟨y1, y2, hne, (hVc y1).2 ((c.mem_verts_toSubgraph).1 a1.snd_mem),
      (hVc y2).2 ((c.mem_verts_toSubgraph).1 a2.snd_mem), a1.adj_sub, a2.adj_sub⟩
  let On : Fin m → Fin m → ℕ → Prop := fun u v q => ∃ y ∈ Vc, Q u v q y
  have hI : ∀ (u v : Fin m) (p : ℕ) (z : Fin (m + 2 * k * (m * m))), 1 ≤ p → p ≤ 2 * k →
      z ∈ Vc → Q u v p z → On u v (p - 1) ∧ On u v (p + 1) := by
    intro u v p z h1 h2 hz hq
    have hzv := (hQi u v p z h1 h2).1 hq
    have hnb : ∀ y, S.Adj z y → Q u v (p - 1) y ∨ Q u v (p + 1) y := by
      intro y hy
      obtain ⟨u', v', _, _, p', hp', h⟩ := (hS z y).1 hy
      have hge := hBge (u, v)
      rcases h with ⟨hz', hy'⟩ | ⟨hy', hz'⟩
      · have hz'' := (hQ u' v' p' z).1 hz'
        rcases hz'' with ⟨_, e⟩ | ⟨e, _⟩ | ⟨e1, e2, e3⟩
        · have := u'.isLt
          omega
        · omega
        · replace e3 : z.val + 1 = B (u', v') + p' := by rw [hBdef]; exact e3
          obtain ⟨e4, e5⟩ := hBinj (u, v) (u', v') (p - 1) (p' - 1) (by omega) (by omega) (by omega)
          have e6 : p' = p := by omega
          have eu : u' = u := (congrArg Prod.fst e4).symm
          have ev : v' = v := (congrArg Prod.snd e4).symm
          rw [eu, ev, e6] at hy'
          exact Or.inr hy'
      · have hz'' := (hQ u' v' (p' + 1) z).1 hz'
        rcases hz'' with ⟨e, _⟩ | ⟨_, e⟩ | ⟨e1, e2, e3⟩
        · omega
        · have := v'.isLt
          omega
        · replace e3 : z.val + 1 = B (u', v') + (p' + 1) := by rw [hBdef]; exact e3
          obtain ⟨e4, e5⟩ := hBinj (u, v) (u', v') (p - 1) p' (by omega) (by omega) (by omega)
          have e6 : p' = p - 1 := by omega
          have eu : u' = u := (congrArg Prod.fst e4).symm
          have ev : v' = v := (congrArg Prod.snd e4).symm
          rw [eu, ev, e6] at hy'
          exact Or.inl hy'
    obtain ⟨y1, y2, hne, hy1, hy2, ha1, ha2⟩ := hN z hz
    rcases hnb y1 ha1 with q1 | q1 <;> rcases hnb y2 ha2 with q2 | q2
    · exact absurd (hQuniq u v _ y1 y2 q1 q2) hne
    · exact ⟨⟨y1, hy1, q1⟩, ⟨y2, hy2, q2⟩⟩
    · exact ⟨⟨y2, hy2, q2⟩, ⟨y1, hy1, q1⟩⟩
    · exact absurd (hQuniq u v _ y1 y2 q1 q2) hne
  have hup : ∀ (u v : Fin m) (p : ℕ), 1 ≤ p → p ≤ 2 * k → On u v p →
      ∀ d, p + d ≤ 2 * k + 1 → On u v (p + d) := by
    intro u v p h1 h2 hon d
    induction d with
    | zero => intro _; exact hon
    | succ d ih =>
      intro hd
      obtain ⟨y, hy, hq⟩ := ih (by omega)
      exact (hI u v (p + d) y (by omega) (by omega) hy hq).2
  have hdown : ∀ (u v : Fin m) (p : ℕ), 1 ≤ p → p ≤ 2 * k → On u v p →
      ∀ d, d ≤ p → On u v (p - d) := by
    intro u v p h1 h2 hon d
    induction d with
    | zero => intro _; exact hon
    | succ d ih =>
      intro hd
      obtain ⟨y, hy, hq⟩ := ih (by omega)
      have := (hI u v (p - d) y (by omega) (by omega) hy hq).1
      have e : p - d - 1 = p - (d + 1) := by omega
      rw [e] at this
      exact this
  have hall : ∀ (u v : Fin m) (p : ℕ), 1 ≤ p → p ≤ 2 * k → On u v p →
      ∀ q, q ≤ 2 * k + 1 → On u v q := by
    intro u v p h1 h2 hon q hq
    by_cases hqp : p ≤ q
    · have := hup u v p h1 h2 hon (q - p) (by omega)
      have e : p + (q - p) = q := by omega
      rw [e] at this
      exact this
    · have := hdown u v p h1 h2 hon (p - q) (by omega)
      have e : p - (p - q) = q := by omega
      rw [e] at this
      exact this
  let InF : Fin m × Fin m → Prop := fun e => e.1 < e.2 ∧ ∀ q, q ≤ 2 * k + 1 → On e.1 e.2 q
  have hO : ∀ (z y : Fin (m + 2 * k * (m * m))), z.val < m → y ∈ Vc → S.Adj z y →
      ∃ e : Fin m × Fin m, InF e ∧ ((z.val = e.1.val ∧ Q e.1 e.2 1 y) ∨
        (z.val = e.2.val ∧ Q e.1 e.2 (2 * k) y)) := by
    intro z y hz hyV hy
    obtain ⟨u, v, hlt, _, p, hp, h⟩ := (hS z y).1 hy
    have hge := hBge (u, v)
    rcases h with ⟨hz', hy'⟩ | ⟨hy', hz'⟩
    · rcases (hQ u v p z).1 hz' with ⟨e0, e⟩ | ⟨e, _⟩ | ⟨e1, e2, e3⟩
      · rw [e0] at hy'
        exact ⟨(u, v), ⟨hlt, hall u v 1 (by omega) (by omega) ⟨y, hyV, hy'⟩⟩, Or.inl ⟨e, hy'⟩⟩
      · omega
      · replace e3 : z.val + 1 = B (u, v) + p := by rw [hBdef]; exact e3
        omega
    · rcases (hQ u v (p + 1) z).1 hz' with ⟨e, _⟩ | ⟨e0, e⟩ | ⟨e1, e2, e3⟩
      · omega
      · have e4 : p = 2 * k := by omega
        rw [e4] at hy'
        exact ⟨(u, v), ⟨hlt, hall u v (2 * k) (by omega) (by omega) ⟨y, hyV, hy'⟩⟩,
          Or.inr ⟨e, hy'⟩⟩
      · replace e3 : z.val + 1 = B (u, v) + (p + 1) := by rw [hBdef]; exact e3
        omega
  have hC : ∀ z ∈ Vc, z.val < m → ∃ e1 e2 : Fin m × Fin m, e1 ≠ e2 ∧ InF e1 ∧ InF e2 ∧
      (z.val = e1.1.val ∨ z.val = e1.2.val) ∧ (z.val = e2.1.val ∨ z.val = e2.2.val) := by
    intro z hz hzm
    obtain ⟨y1, y2, hne, hy1, hy2, ha1, ha2⟩ := hN z hz
    obtain ⟨e1, hF1, hc1⟩ := hO z y1 hzm hy1 ha1
    obtain ⟨e2, hF2, hc2⟩ := hO z y2 hzm hy2 ha2
    refine ⟨e1, e2, ?_, hF1, hF2, hc1.imp (fun h => h.1) (fun h => h.1),
      hc2.imp (fun h => h.1) (fun h => h.1)⟩
    intro heq
    rw [← heq] at hc2 hF2
    have hlt := hF1.1
    rcases hc1 with ⟨a1, q1⟩ | ⟨a1, q1⟩ <;> rcases hc2 with ⟨a2, q2⟩ | ⟨a2, q2⟩
    · exact hne (hQuniq _ _ _ y1 y2 q1 q2)
    · have : e1.1.val < e1.2.val := hlt
      omega
    · have : e1.1.val < e1.2.val := hlt
      omega
    · exact hne (hQuniq _ _ _ y1 y2 q1 q2)
  have hBv : ∀ e : Fin m × Fin m, InF e → (∃ z ∈ Vc, z.val = e.1.val) ∧ (∃ z ∈ Vc, z.val = e.2.val) := by
    intro e he
    obtain ⟨z0, hz0, q0⟩ := he.2 0 (by omega)
    obtain ⟨z1, hz1, q1⟩ := he.2 (2 * k + 1) (by omega)
    exact ⟨⟨z0, hz0, (hQ0 _ _ _).1 q0⟩, ⟨z1, hz1, (hQl _ _ _).1 q1⟩⟩
  have hx : x ∈ Vc := (hVc x).2 c.start_mem_support
  obtain ⟨e0, he0⟩ : ∃ e : Fin m × Fin m, InF e := by
    obtain ⟨y1, y2, _, hy1, _, ha1, _⟩ := hN x hx
    obtain ⟨u, v, hlt, _, p, hp, h⟩ := (hS x y1).1 ha1
    have key : ∀ a b : Fin (m + 2 * k * (m * m)), a ∈ Vc → b ∈ Vc → Q u v p a → Q u v (p + 1) b →
        ∃ e : Fin m × Fin m, InF e := by
      intro a b ha hb qa qb
      by_cases hp0 : p = 0
      · rw [hp0] at qb
        exact ⟨(u, v), hlt, hall u v 1 (by omega) (by omega) ⟨b, hb, qb⟩⟩
      · exact ⟨(u, v), hlt, hall u v p (by omega) hp ⟨a, ha, qa⟩⟩
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact key x y1 hx hy1 h1 h2
    · exact key y1 x hy1 hx h1 h2
  obtain ⟨⟨zu, hzu, hzuv⟩, ⟨zv, hzv, hzvv⟩⟩ := hBv e0 he0
  obtain ⟨f1, f2, hf12, hF1, hF2, hi1, hi2⟩ := hC zu hzu (by rw [hzuv]; exact e0.1.isLt)
  obtain ⟨g1, g2, hg12, hG1, hG2, hj1, hj2⟩ := hC zv hzv (by rw [hzvv]; exact e0.2.isLt)
  rw [hzuv] at hi1 hi2
  rw [hzvv] at hj1 hj2
  have h0lt : e0.1.val < e0.2.val := he0.1
  have hpu : ∀ f f' : Fin m × Fin m, InF f → InF f' → ∀ a b : ℕ, a ≠ b →
      (a = f.1.val ∨ a = f.2.val) → (b = f.1.val ∨ b = f.2.val) →
      (a = f'.1.val ∨ a = f'.2.val) → (b = f'.1.val ∨ b = f'.2.val) → f = f' := by
    intro f f' hf hf' a b hab h1 h2 h3 h4
    have l1 : f.1.val < f.2.val := hf.1
    have l2 : f'.1.val < f'.2.val := hf'.1
    obtain ⟨r1, r2⟩ := PEqualNP.Outside.Meta464.pair_unique a b _ _ _ _ hab l1 l2 h1 h2 h3 h4
    exact Prod.ext (Fin.ext r1) (Fin.ext r2)
  obtain ⟨g, hG, hgf1, hgf2⟩ : ∃ g : Fin m × Fin m, InF g ∧ g ≠ f1 ∧ g ≠ f2 := by
    by_cases c1 : g1 ≠ f1 ∧ g1 ≠ f2
    · exact ⟨g1, hG1, c1.1, c1.2⟩
    · by_cases c2 : g2 ≠ f1 ∧ g2 ≠ f2
      · exact ⟨g2, hG2, c2.1, c2.2⟩
      · exfalso
        apply hf12
        have t1 : (e0.2.val = f1.1.val ∨ e0.2.val = f1.2.val) ∧
            (e0.2.val = f2.1.val ∨ e0.2.val = f2.2.val) := by
          by_cases d1 : g1 = f1
          · have d2 : g2 = f2 := by
              by_contra d2
              apply c2
              refine ⟨?_, d2⟩
              intro d3
              exact hg12 (d1.trans d3.symm)
            rw [d1] at hj1
            rw [d2] at hj2
            exact ⟨hj1, hj2⟩
          · have d3 : g1 = f2 := by
              by_contra d3
              exact c1 ⟨d1, d3⟩
            have d2 : g2 = f1 := by
              by_contra d2
              apply c2
              refine ⟨d2, ?_⟩
              intro d4
              exact hg12 (d3.trans d4.symm)
            rw [d3] at hj1
            rw [d2] at hj2
            exact ⟨hj2, hj1⟩
        exact hpu f1 f2 hF1 hF2 e0.1.val e0.2.val (by omega) hi1 t1.1 hi2 t1.2
  obtain ⟨w1, hw1V, hw1ne, hw1inc⟩ : ∃ w : ℕ, (∃ z ∈ Vc, z.val = w) ∧ w ≠ e0.1.val ∧
      (w = f1.1.val ∨ w = f1.2.val) := by
    have l1 : f1.1.val < f1.2.val := hF1.1
    rcases hi1 with h | h
    · exact ⟨f1.2.val, (hBv f1 hF1).2, by omega, Or.inr rfl⟩
    · exact ⟨f1.1.val, (hBv f1 hF1).1, by omega, Or.inl rfl⟩
  obtain ⟨w2, hw2V, hw2ne, hw2inc⟩ : ∃ w : ℕ, (∃ z ∈ Vc, z.val = w) ∧ w ≠ e0.1.val ∧
      (w = f2.1.val ∨ w = f2.2.val) := by
    have l1 : f2.1.val < f2.2.val := hF2.1
    rcases hi2 with h | h
    · exact ⟨f2.2.val, (hBv f2 hF2).2, by omega, Or.inr rfl⟩
    · exact ⟨f2.1.val, (hBv f2 hF2).1, by omega, Or.inl rfl⟩
  have hw12 : w1 ≠ w2 := by
    intro h
    apply hf12
    rw [← h] at hw2inc
    exact hpu f1 f2 hF1 hF2 e0.1.val w1 (Ne.symm hw1ne) hi1 hw1inc hi2 hw2inc
  let VN : Finset ℕ := Vc.image Fin.val
  have hVN : VN.card = Vc.card := Finset.card_image_of_injective _ Fin.val_injective
  have hVNmem : ∀ w : ℕ, (∃ z ∈ Vc, z.val = w) → w ∈ VN := by
    rintro w ⟨z, hz, rfl⟩
    exact Finset.mem_image_of_mem _ hz
  let A3 : Finset ℕ := {e0.1.val, w1, w2}
  have hA3 : A3.card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · simpa using hw12
    · simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
  let F3 : Finset (Fin m × Fin m) := {f1, f2, g}
  have hF3 : F3.card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · simpa using (Ne.symm hgf2)
    · simp only [Finset.mem_insert, Finset.mem_singleton]
      rintro (h | h)
      · exact hf12 h
      · exact hgf1 h.symm
  have hF3in : ∀ f ∈ F3, InF f := by
    intro f hf
    simp only [F3, Finset.mem_insert, Finset.mem_singleton] at hf
    rcases hf with rfl | rfl | rfl
    · exact hF1
    · exact hF2
    · exact hG
  let W : Finset ℕ := (F3 ×ˢ Finset.range (2 * k)).image (fun q => B q.1 + q.2)
  have hWcard : W.card = 3 * (2 * k) := by
    rw [Finset.card_image_of_injOn, Finset.card_product, hF3, Finset.card_range]
    intro q hq q' hq' h
    have h1 := (Finset.mem_product.1 (Finset.mem_coe.1 hq)).2
    have h2 := (Finset.mem_product.1 (Finset.mem_coe.1 hq')).2
    rw [Finset.mem_range] at h1 h2
    obtain ⟨r1, r2⟩ := hBinj q.1 q'.1 q.2 q'.2 h1 h2 h
    exact Prod.ext r1 r2
  have hsubV : A3 ∪ W ⊆ VN := by
    intro w hw
    rcases Finset.mem_union.1 hw with hw | hw
    · simp only [A3, Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl | rfl
      · exact hVNmem _ ⟨zu, hzu, hzuv⟩
      · exact hVNmem _ hw1V
      · exact hVNmem _ hw2V
    · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hw
      obtain ⟨hq1, hq2⟩ := Finset.mem_product.1 hq
      rw [Finset.mem_range] at hq2
      obtain ⟨y, hy, hqy⟩ := (hF3in q.1 hq1).2 (q.2 + 1) (by omega)
      have := (hQi q.1.1 q.1.2 (q.2 + 1) y (by omega) (by omega)).1 hqy
      refine hVNmem _ ⟨y, hy, ?_⟩
      show y.val = B q.1 + q.2
      have e : B (q.1.1, q.1.2) = B q.1 := rfl
      omega
  have hdisj : Disjoint A3 W := by
    rw [Finset.disjoint_left]
    intro w hw hw'
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hw'
    have hge := hBge q.1
    simp only [A3, Finset.mem_insert, Finset.mem_singleton] at hw
    have b0 := e0.1.isLt
    have b1 : w1 < m := by
      rcases hw1inc with h | h
      · rw [h]; exact f1.1.isLt
      · rw [h]; exact f1.2.isLt
    have b2 : w2 < m := by
      rcases hw2inc with h | h
      · rw [h]; exact f2.1.isLt
      · rw [h]; exact f2.2.isLt
    omega
  have hfin := Finset.card_le_card hsubV
  rw [Finset.card_union_of_disjoint hdisj, hA3, hWcard, hVN] at hfin
  omega
