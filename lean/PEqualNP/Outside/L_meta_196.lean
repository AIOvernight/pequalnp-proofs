import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.Meta196

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem step_or2 (w : List Bool) (a h : ℕ) :
    step w ⟨GateOp.or, [a, h]⟩ = w ++ [w.getD a false || w.getD h false] := by
  simp [step, GateOp.eval]

theorem step_or1 (w : List Bool) (a : ℕ) :
    step w ⟨GateOp.or, [a]⟩ = w ++ [w.getD a false] := by
  simp [step, GateOp.eval]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

theorem foldl_length : ∀ (G : List Gate) (w : List Bool),
    (G.foldl step w).length = w.length + G.length := by
  intro G
  induction G with
  | nil => intro w; simp
  | cons g G ih =>
    intro w
    rw [List.foldl_cons, ih]
    simp [step]
    omega

theorem getD_app (w : List Bool) (v : Bool) (i : ℕ) (hi : i < w.length) :
    (w ++ [v]).getD i false = w.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem getD_last (w : List Bool) (v : Bool) (i : ℕ) (hi : i = w.length) :
    (w ++ [v]).getD i false = v := by
  subst hi
  simp [List.getD_eq_getElem?_getD]

theorem foldl_getD : ∀ (G : List Gate) (w : List Bool) (i : ℕ), i < w.length →
    (G.foldl step w).getD i false = w.getD i false := by
  intro G
  induction G with
  | nil => intro w i _; rfl
  | cons g G ih =>
    intro w i hi
    rw [List.foldl_cons, ih _ i (by simp [step]; omega)]
    exact getD_app w _ i hi

theorem split_at : ∀ (l : List Gate) (j : ℕ) (g : Gate), l[j]? = some g →
    ∃ G1 G2 : List Gate, l = G1 ++ g :: G2 ∧ G1.length = j := by
  intro l
  induction l with
  | nil => intro j g h; simp at h
  | cons b l ih =>
    intro j g h
    cases j with
    | zero =>
      simp at h
      exact ⟨[], l, by simp [h], rfl⟩
    | succ j =>
      simp at h
      obtain ⟨G1, G2, h1, h2⟩ := ih j g h
      exact ⟨b :: G1, G2, by simp [h1], by simp [h2]⟩

theorem set_mid : ∀ (G1 G2 : List Gate) (g g' : Gate),
    (G1 ++ g :: G2).set G1.length g' = G1 ++ g' :: G2 := by
  intro G1
  induction G1 with
  | nil => intro G2 g g'; rfl
  | cons b G1 ih => intro G2 g g'; simp [ih]

end PEqualNP.Outside.Meta196

theorem PEqualNP.Outside.L_meta_196 : ∀ (n j a h : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (f : (Fin n → Bool) → Bool), C.gates[j]? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [a, h]⟩ → h < n + j → ∀ x : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun n { gates := C.gates.set j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [a]⟩ ++ [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [C.output, h]⟩], output := n + C.size } x ≠ f x → PEqualNP.MetaComplexity.circuitFun n C x ≠ f x ∨ ((C.wires (List.ofFn x)).getD h false = true ∧ f x = false) := by
  intro n j a h C f hj hh x hne
  obtain ⟨G1, G2, hC, hlen⟩ := PEqualNP.Outside.Meta196.split_at C.gates j _ hj
  have hset : C.gates.set j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [a]⟩
      = G1 ++ ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [a]⟩ :: G2 := by
    rw [hC, ← hlen]
    exact PEqualNP.Outside.Meta196.set_mid G1 G2 _ _
  let w1 := G1.foldl PEqualNP.Outside.Meta196.step (List.ofFn x)
  have hw1len : w1.length = n + j := by
    show (G1.foldl PEqualNP.Outside.Meta196.step (List.ofFn x)).length = n + j
    rw [PEqualNP.Outside.Meta196.foldl_length, List.length_ofFn, hlen]
  have hh1 : h < w1.length := by omega
  let va := w1.getD a false
  let vh := w1.getD h false
  have hwC : C.wires (List.ofFn x)
      = G2.foldl PEqualNP.Outside.Meta196.step (w1 ++ [va || vh]) := by
    rw [PEqualNP.Outside.Meta196.wires_eq, hC, List.foldl_append, List.foldl_cons,
      PEqualNP.Outside.Meta196.step_or2]
  have hhC : (C.wires (List.ofFn x)).getD h false = vh := by
    rw [hwC, PEqualNP.Outside.Meta196.foldl_getD _ _ h (by simp; omega)]
    exact PEqualNP.Outside.Meta196.getD_app w1 _ h hh1
  let wm := G2.foldl PEqualNP.Outside.Meta196.step (w1 ++ [va])
  have hwmlen : wm.length = n + C.size := by
    show (G2.foldl PEqualNP.Outside.Meta196.step (w1 ++ [va])).length = n + C.gates.length
    rw [PEqualNP.Outside.Meta196.foldl_length, hC]
    simp
    omega
  have hhm : wm.getD h false = vh := by
    show (G2.foldl PEqualNP.Outside.Meta196.step (w1 ++ [va])).getD h false = vh
    rw [PEqualNP.Outside.Meta196.foldl_getD _ _ h (by simp; omega)]
    exact PEqualNP.Outside.Meta196.getD_app w1 _ h hh1
  have hnew : PEqualNP.MetaComplexity.circuitFun n { gates := C.gates.set j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [a]⟩ ++ [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [C.output, h]⟩], output := n + C.size } x
      = (wm.getD C.output false || vh) := by
    show (List.foldl PEqualNP.Outside.Meta196.step (List.ofFn x)
      (C.gates.set j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [a]⟩ ++ [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [C.output, h]⟩])).getD (n + C.size) false = _
    rw [hset, List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_cons,
      List.foldl_nil, PEqualNP.Outside.Meta196.step_or1, PEqualNP.Outside.Meta196.step_or2]
    show (wm ++ [wm.getD C.output false || wm.getD h false]).getD (n + C.size) false = _
    rw [PEqualNP.Outside.Meta196.getD_last wm _ _ hwmlen.symm, hhm]
  rw [hnew] at hne
  by_cases hv : vh = true
  · right
    refine ⟨by rw [hhC]; exact hv, ?_⟩
    rw [hv, Bool.or_true] at hne
    cases hfx : f x
    · rfl
    · exact absurd hfx.symm hne
  · left
    have hvf : vh = false := by simpa using hv
    have hsame : wm = C.wires (List.ofFn x) := by
      rw [hwC]
      show G2.foldl PEqualNP.Outside.Meta196.step (w1 ++ [va]) = _
      rw [hvf, Bool.or_false]
    rw [hvf, Bool.or_false, hsame] at hne
    exact hne
