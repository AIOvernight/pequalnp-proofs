import Mathlib
import PEqualNP.Defs

private lemma L1349.divpow (h j : ℕ) (hj : j ≤ h) :
    2 ^ h * (2 ^ h + 1) / 2 ^ j = 2 ^ (h - j) * (2 ^ h + 1) := by
  have e1 : (2 : ℕ) ^ h = 2 ^ j * 2 ^ (h - j) := by
    rw [← pow_add]
    congr 1
    omega
  have e2 : (2 : ℕ) ^ h * (2 ^ h + 1) = 2 ^ j * (2 ^ (h - j) * (2 ^ h + 1)) := by
    rw [← mul_assoc, ← e1]
  rw [e2]
  exact Nat.mul_div_cancel_left _ (by positivity)

private lemma L1349.untop (S : Finset ℕ) (hS : S.Nonempty) (c : ℕ) (hc : ∀ x ∈ S, c ≤ x) :
    c ≤ WithTop.untopD 0 S.min := by
  obtain ⟨m, hm⟩ := Finset.min_of_nonempty hS
  rw [hm]
  exact hc m (Finset.mem_of_min hm)

private lemma L1349.window (n g k : ℕ) (P : Finset ℕ) (hg : 0 < g) (hn : k * g ≤ n)
    (hP : P.card < k) : ∃ s, s + g ≤ n ∧ ∀ w ∈ P, ¬ (s < w ∧ w ≤ s + g) := by
  by_contra hcon
  push_neg at hcon
  have hsub : Finset.range k ⊆ P.image (fun w => (w - 1) / g) := by
    intro i hi
    have hi' : i < k := Finset.mem_range.mp hi
    have h1 : i * g + g ≤ n := by
      have : (i + 1) * g ≤ k * g := Nat.mul_le_mul_right g hi'
      nlinarith
    obtain ⟨w, hw, hlo, hhi⟩ := hcon (i * g) h1
    refine Finset.mem_image.mpr ⟨w, hw, ?_⟩
    apply Nat.div_eq_of_lt_le
    · omega
    · have : (i + 1) * g = i * g + g := by ring
      omega
  have := Finset.card_le_card hsub
  have h2 := Finset.card_image_le (s := P) (f := fun w => (w - 1) / g)
  rw [Finset.card_range] at this
  omega

private lemma L1349.midmid (Q C V E M : ℕ) (hCV : C * V = Q) (hV : 4 ≤ V) (hE : 1 ≤ E)
    (hM : 2 * M ≤ Q * Q) (hC : 1 ≤ C) :
    M * (E - 1) ≤ (C * (2 * E) * (Q + 1) - Q - (C * (Q + 1) - Q)) * (V - 1) := by
  obtain ⟨E1, rfl⟩ : ∃ E1, E = E1 + 1 := ⟨E - 1, by omega⟩
  obtain ⟨V1, rfl⟩ : ∃ V1, V = V1 + 1 := ⟨V - 1, by omega⟩
  have hY : Q ≤ C * (Q + 1) := by nlinarith
  have hd : C * (2 * (E1 + 1)) * (Q + 1) - Q - (C * (Q + 1) - Q)
      = C * (Q + 1) * (2 * E1 + 1) := by
    have : C * (2 * (E1 + 1)) * (Q + 1) = C * (Q + 1) * (2 * E1 + 1) + C * (Q + 1) := by ring
    omega
  rw [hd]
  simp only [Nat.add_sub_cancel]
  have hQ : Q = C * V1 + C := by rw [← hCV]; ring
  have h4 : 4 * C ≤ Q := by nlinarith
  have hMV : M ≤ C * (Q + 1) * V1 := by
    have : C * (Q + 1) * V1 = (Q + 1) * (C * V1) := by ring
    rw [this]
    have h3 : 2 * (C * V1) ≥ Q := by omega
    nlinarith
  calc M * E1 ≤ C * (Q + 1) * V1 * (2 * E1 + 1) := by
        have := Nat.mul_le_mul hMV (show E1 ≤ 2 * E1 + 1 by omega)
        exact this
    _ = C * (Q + 1) * (2 * E1 + 1) * V1 := by ring

private lemma L1349.key (h e u : ℕ) (he : 1 ≤ e) (huv : u + (e + 1) ≤ h + 2) :
    (2 ^ h * 2 ^ h / 2) * (2 ^ e - 1) ≤
      ((if u = 0 then (2 ^ h * 2 ^ h + 2 ^ h + 1) else if u = h + 2 then 0
          else 2 ^ h * (2 ^ h + 1) / 2 ^ (u - 1) - 2 ^ h)
        - (if u + (e + 1) = 0 then (2 ^ h * 2 ^ h + 2 ^ h + 1) else if u + (e + 1) = h + 2 then 0
          else 2 ^ h * (2 ^ h + 1) / 2 ^ (u + (e + 1) - 1) - 2 ^ h))
      * (if u + (e + 1) = h + 2 then 2 ^ h else 2 ^ (u + (e + 1) - 1) - 1) := by
  have hM : 2 * (2 ^ h * 2 ^ h / 2) ≤ 2 ^ h * 2 ^ h := Nat.mul_div_le _ _
  have hQ1 : 1 ≤ 2 ^ h := Nat.one_le_two_pow
  have hE2 : 2 ≤ 2 ^ e := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he
  generalize hMdef : 2 ^ h * 2 ^ h / 2 = M at hM ⊢
  rw [if_neg (show ¬ (u + (e + 1) = 0) by omega)]
  by_cases hu0 : u = 0
  · subst hu0
    rw [if_pos rfl]
    by_cases hv : 0 + (e + 1) = h + 2
    · rw [if_pos hv, if_pos hv]
      have hh : h = e - 1 + 0 ∧ e = h + 1 := by omega
      obtain ⟨-, rfl⟩ := hh
      rw [pow_succ] at hE2 ⊢
      generalize 2 ^ h = Q at *
      simp only [Nat.sub_zero]
      obtain ⟨Q1, rfl⟩ : ∃ Q1, Q = Q1 + 1 := ⟨Q - 1, by omega⟩
      have : (Q1 + 1) * 2 - 1 = 2 * Q1 + 1 := by omega
      rw [this]
      nlinarith
    · rw [if_neg hv, if_neg hv]
      rw [L1349.divpow h (0 + (e + 1) - 1) (by omega)]
      have hpw : (2 : ℕ) ^ h = 2 ^ (h - (0 + (e + 1) - 1)) * 2 ^ e := by
        rw [← pow_add]
        congr 1
        omega
      generalize 2 ^ (h - (0 + (e + 1) - 1)) = C at *
      have hee : 0 + (e + 1) - 1 = e := by omega
      rw [hee]
      generalize 2 ^ e = E at *
      generalize 2 ^ h = Q at *
      obtain ⟨E1, rfl⟩ : ∃ E1, E = E1 + 2 := ⟨E - 2, by omega⟩
      have hC : 2 * C ≤ Q := by nlinarith
      have h1 : C * (Q + 1) - Q ≤ C * (Q + 1) := Nat.sub_le _ _
      have h2 : 2 * (C * (Q + 1)) ≤ Q * Q + Q := by nlinarith
      have h3 : M ≤ Q * Q + Q + 1 - (C * (Q + 1) - Q) := by omega
      have h4 : E1 + 2 - 1 = E1 + 1 := by omega
      rw [h4]
      exact Nat.mul_le_mul h3 (by omega)
  · rw [if_neg hu0, if_neg (show ¬ (u = h + 2) by omega)]
    rw [L1349.divpow h (u - 1) (by omega)]
    by_cases hv : u + (e + 1) = h + 2
    · rw [if_pos hv, if_pos hv]
      have hue : h - (u - 1) = e := by omega
      rw [hue]
      generalize 2 ^ e = E at *
      generalize 2 ^ h = Q at *
      simp only [Nat.sub_zero]
      obtain ⟨E1, rfl⟩ : ∃ E1, E = E1 + 1 := ⟨E - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      have h1 : (E1 + 1) * (Q + 1) - Q = E1 * Q + E1 + 1 := by
        have : (E1 + 1) * (Q + 1) = E1 * Q + E1 + 1 + Q := by ring
        omega
      rw [h1]
      nlinarith
    · rw [if_neg hv, if_neg hv]
      rw [L1349.divpow h (u + (e + 1) - 1) (by omega)]
      have hpu : (2 : ℕ) ^ (h - (u - 1)) = 2 ^ (h - (u + (e + 1) - 1)) * (2 * 2 ^ e) := by
        rw [← pow_succ', ← pow_add]
        congr 1
        omega
      have hpq : 2 ^ (h - (u + (e + 1) - 1)) * 2 ^ (u + (e + 1) - 1) = 2 ^ h := by
        rw [← pow_add]
        congr 1
        omega
      have hV : 4 ≤ 2 ^ (u + (e + 1) - 1) := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ (u + (e + 1) - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [hpu]
      exact L1349.midmid _ _ _ _ _ hpq hV (by omega) hM Nat.one_le_two_pow

theorem PEqualNP.Outside.L_meta_1349 : ∀ h t : ℕ, 1 ≤ h → (2 ^ h * 2 ^ h / 2) * (2 ^ ((h + 3 + 2 ^ t - 1) / 2 ^ t - 1 - 1) - 1) ≤ (WithTop.untopD 0 (((Finset.range (h + 3)).powerset.filter (fun P : Finset ℕ => P.card + 1 ≤ 2 ^ t)).image (fun P : Finset ℕ => ((Finset.range (h + 3) ×ˢ Finset.range (h + 3)).filter (fun uv : ℕ × ℕ => uv.1 ≤ uv.2 ∧ ∀ w ∈ P, ¬ (uv.1 < w ∧ w ≤ uv.2))).sup (fun uv : ℕ × ℕ => ((if uv.1 = 0 then (2 ^ h * 2 ^ h + 2 ^ h + 1) else if uv.1 = h + 2 then 0 else 2 ^ h * (2 ^ h + 1) / 2 ^ (uv.1 - 1) - 2 ^ h) - (if uv.2 = 0 then (2 ^ h * 2 ^ h + 2 ^ h + 1) else if uv.2 = h + 2 then 0 else 2 ^ h * (2 ^ h + 1) / 2 ^ (uv.2 - 1) - 2 ^ h)) * (if uv.2 = h + 2 then 2 ^ h else 2 ^ (uv.2 - 1) - 1)))).min) := by
  intro h t hh
  apply L1349.untop
  · refine ⟨_, Finset.mem_image.mpr ⟨∅, ?_, rfl⟩⟩
    simp
  intro x hx
  obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨-, hcard⟩ := Finset.mem_filter.mp hP
  rcases Nat.eq_zero_or_pos ((h + 3 + 2 ^ t - 1) / 2 ^ t - 1 - 1) with he | he
  · rw [he]
    simp
  generalize hedef : (h + 3 + 2 ^ t - 1) / 2 ^ t - 1 - 1 = e at he ⊢
  have ht : 0 < 2 ^ t := by positivity
  have hmul : (e + 2) * 2 ^ t ≤ h + 3 + 2 ^ t - 1 := by
    have : e + 2 ≤ (h + 3 + 2 ^ t - 1) / 2 ^ t := by omega
    exact (Nat.le_div_iff_mul_le ht).mp this
  have hn : 2 ^ t * (e + 1) ≤ h + 2 := by
    have : (e + 2) * 2 ^ t = 2 ^ t * (e + 1) + 2 ^ t := by ring
    omega
  obtain ⟨s, hs, hfree⟩ := L1349.window (h + 2) (e + 1) (2 ^ t) P (by omega) hn (by omega)
  refine le_trans (L1349.key h e s he hs) ?_
  exact Finset.le_sup (f := fun uv : ℕ × ℕ => ((if uv.1 = 0 then (2 ^ h * 2 ^ h + 2 ^ h + 1) else if uv.1 = h + 2 then 0 else 2 ^ h * (2 ^ h + 1) / 2 ^ (uv.1 - 1) - 2 ^ h) - (if uv.2 = 0 then (2 ^ h * 2 ^ h + 2 ^ h + 1) else if uv.2 = h + 2 then 0 else 2 ^ h * (2 ^ h + 1) / 2 ^ (uv.2 - 1) - 2 ^ h)) * (if uv.2 = h + 2 then 2 ^ h else 2 ^ (uv.2 - 1) - 1)) (b := (s, s + (e + 1))) (by
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    exact ⟨⟨by omega, by omega⟩, by omega, hfree⟩)
