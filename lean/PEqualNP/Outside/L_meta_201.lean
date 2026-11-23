import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.Meta201

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

theorem val_input (C : Circuit) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (C.wires x).getD i false = x.getD i false := by
  rw [wires_eq]
  exact foldl_getD _ _ i hi

theorem val_true_lt (C : Circuit) (x : List Bool) (i : ℕ)
    (h : (C.wires x).getD i false = true) : i < x.length + C.gates.length := by
  by_contra hn
  have hlen : (C.wires x).length ≤ i := by
    rw [wires_eq, foldl_length]
    omega
  rw [List.getD_eq_default _ _ hlen] at h
  cases h

theorem gate_val (C : Circuit) (x : List Bool) (j : ℕ) (g : Gate) (hg : C.gates[j]? = some g) :
    (C.wires x).getD (x.length + j) false = g.op.eval (g.inputs.map fun i =>
      if i < x.length + j then (C.wires x).getD i false else false) := by
  obtain ⟨G1, G2, hC, hlen⟩ := split_at C.gates j g hg
  have hl : (G1.foldl step x).length = x.length + j := by rw [foldl_length, hlen]
  have hw : C.wires x = G2.foldl step (step (G1.foldl step x) g) := by
    rw [wires_eq, hC, List.foldl_append, List.foldl_cons]
  have hpre : ∀ i, i < x.length + j →
      (C.wires x).getD i false = (G1.foldl step x).getD i false := by
    intro i hi
    rw [hw, foldl_getD _ _ i (by simp [step]; omega)]
    exact getD_app _ _ i (by omega)
  have hmap : (g.inputs.map fun i =>
      if i < x.length + j then (C.wires x).getD i false else false)
      = g.inputs.map fun i => (G1.foldl step x).getD i false := by
    apply List.map_congr_left
    intro i _
    by_cases hi : i < x.length + j
    · rw [if_pos hi, hpre i hi]
    · rw [if_neg hi, List.getD_eq_default _ _ (by omega)]
  rw [hmap, hw, foldl_getD _ _ _ (by simp [step]; omega)]
  exact getD_last _ _ _ hl.symm

theorem ofFn_getD {n : ℕ} (f : Fin n → Bool) (i : ℕ) (hi : i < n) :
    (List.ofFn f).getD i false = f ⟨i, hi⟩ := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi)]
  simp

end PEqualNP.Outside.Meta201

theorem PEqualNP.Outside.L_meta_201 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo C → (∀ g ∈ C.gates, g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not) → PEqualNP.MetaComplexity.circuitFun n C = (fun x : Fin n → Bool => decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) → ∀ u v : Fin n, G.Adj u v → ∃ j : ℕ, (∃ (g : PEqualNP.CircuitLowerBounds.Gate) (a b : ℕ), C.gates[j]? = some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ g.inputs = [a, b] ∧ a < n + j ∧ b < n + j ∧ (((C.wires (List.ofFn (fun i : Fin n => decide (i = u)))).getD a false = true ∧ (C.wires (List.ofFn (fun i : Fin n => decide (i = v)))).getD a false = false ∧ (C.wires (List.ofFn (fun i : Fin n => decide (i = v)))).getD b false = true ∧ (C.wires (List.ofFn (fun i : Fin n => decide (i = u)))).getD b false = false) ∨ ((C.wires (List.ofFn (fun i : Fin n => decide (i = v)))).getD a false = true ∧ (C.wires (List.ofFn (fun i : Fin n => decide (i = u)))).getD a false = false ∧ (C.wires (List.ofFn (fun i : Fin n => decide (i = u)))).getD b false = true ∧ (C.wires (List.ofFn (fun i : Fin n => decide (i = v)))).getD b false = false))) := by
  intro n G _ C hfan hnot hfun u v huv
  let xu : List Bool := List.ofFn (fun i : Fin n => decide (i = u))
  let xv : List Bool := List.ofFn (fun i : Fin n => decide (i = v))
  let xw : List Bool := List.ofFn (fun i : Fin n => decide (i = u) || decide (i = v))
  have lu : xu.length = n := List.length_ofFn
  have lv : xv.length = n := List.length_ofFn
  have lw : xw.length = n := List.length_ofFn
  let P : ℕ → Prop := fun w => (C.wires xw).getD w false = true ∧
    (C.wires xu).getD w false = false ∧ (C.wires xv).getD w false = false
  have hne : u ≠ v := fun h => G.irrefl (h ▸ huv)
  have hout : P C.output := by
    refine ⟨?_, ?_, ?_⟩
    · have := congrFun hfun (fun i : Fin n => decide (i = u) || decide (i = v))
      show C.eval xw = true
      rw [show C.eval xw = PEqualNP.MetaComplexity.circuitFun n C _ from rfl, this]
      simp only [decide_eq_true_eq]
      exact ⟨u, v, huv, by simp, by simp⟩
    · have := congrFun hfun (fun i : Fin n => decide (i = u))
      show C.eval xu = false
      rw [show C.eval xu = PEqualNP.MetaComplexity.circuitFun n C _ from rfl, this]
      simp only [decide_eq_false_iff_not, decide_eq_true_eq]
      rintro ⟨i, j, hij, rfl, rfl⟩
      exact G.irrefl hij
    · have := congrFun hfun (fun i : Fin n => decide (i = v))
      show C.eval xv = false
      rw [show C.eval xv = PEqualNP.MetaComplexity.circuitFun n C _ from rfl, this]
      simp only [decide_eq_false_iff_not, decide_eq_true_eq]
      rintro ⟨i, j, hij, rfl, rfl⟩
      exact G.irrefl hij
  classical
  have hex : ∃ w, P w := ⟨C.output, hout⟩
  have hP0 := Nat.find_spec hex
  have hmin : ∀ w, w < Nat.find hex → ¬ P w := fun w hw => Nat.find_min hex hw
  generalize Nat.find hex = w0 at hP0 hmin
  obtain ⟨h1, h2, h3⟩ := hP0
  have hge : n ≤ w0 := by
    by_contra hlt
    have hlt' : w0 < n := by omega
    rw [PEqualNP.Outside.Meta201.val_input C xw w0 (by omega),
      PEqualNP.Outside.Meta201.ofFn_getD _ w0 hlt'] at h1
    rw [PEqualNP.Outside.Meta201.val_input C xu w0 (by omega),
      PEqualNP.Outside.Meta201.ofFn_getD _ w0 hlt'] at h2
    rw [PEqualNP.Outside.Meta201.val_input C xv w0 (by omega),
      PEqualNP.Outside.Meta201.ofFn_getD _ w0 hlt'] at h3
    rw [h2, h3] at h1
    cases h1
  have hlt := PEqualNP.Outside.Meta201.val_true_lt C xw w0 h1
  obtain ⟨j, rfl⟩ : ∃ j, w0 = n + j := ⟨w0 - n, by omega⟩
  have hj : j < C.gates.length := by omega
  have hg : C.gates[j]? = some C.gates[j] := List.getElem?_eq_getElem hj
  have hmem : C.gates[j] ∈ C.gates := List.getElem_mem hj
  generalize C.gates[j] = g at hg hmem
  have gw := PEqualNP.Outside.Meta201.gate_val C xw j g hg
  have gu := PEqualNP.Outside.Meta201.gate_val C xu j g hg
  have gv := PEqualNP.Outside.Meta201.gate_val C xv j g hg
  rw [lw] at gw
  rw [lu] at gu
  rw [lv] at gv
  rw [gw] at h1
  rw [gu] at h2
  rw [gv] at h3
  have K : ∀ i, (if i < n + j then (C.wires xw).getD i false else false) = true →
      i < n + j ∧ ((C.wires xw).getD i false = true) ∧
        ((C.wires xu).getD i false = true ∨ (C.wires xv).getD i false = true) := by
    intro i hi
    by_cases hlt : i < n + j
    · rw [if_pos hlt] at hi
      refine ⟨hlt, hi, ?_⟩
      by_contra hno
      apply hmin i hlt
      refine ⟨hi, ?_, ?_⟩
      · cases hc : (C.wires xu).getD i false
        · rfl
        · exact absurd (Or.inl hc) hno
      · cases hc : (C.wires xv).getD i false
        · rfl
        · exact absurd (Or.inr hc) hno
    · rw [if_neg hlt] at hi
      cases hi
  obtain ⟨hop, hlen⟩ := hfan g hmem
  have hnn := hnot g hmem
  obtain ⟨op, ins⟩ := g
  simp only at hop hlen hnn h1 h2 h3
  rcases hop with rfl | rfl | rfl
  · match ins, hlen with
    | [], _ =>
      simp [PEqualNP.CircuitLowerBounds.GateOp.eval] at h2
    | [a], _ =>
      simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, List.map_cons, List.map_nil,
        List.all_cons, List.all_nil, Bool.and_true, id] at h1 h2 h3
      obtain ⟨ha, _, hor⟩ := K a h1
      rw [if_pos ha] at h2 h3
      rcases hor with hor | hor
      · rw [hor] at h2
        cases h2
      · rw [hor] at h3
        cases h3
    | [a, b], _ =>
      simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, List.map_cons, List.map_nil,
        List.all_cons, List.all_nil, Bool.and_true, id, Bool.and_eq_true] at h1
      simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, List.map_cons, List.map_nil,
        List.all_cons, List.all_nil, Bool.and_true, id] at h2 h3
      obtain ⟨ha, _, hora⟩ := K a h1.1
      obtain ⟨hb, _, horb⟩ := K b h1.2
      rw [if_pos ha, if_pos hb] at h2 h3
      refine ⟨j, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [a, b]⟩, a, b, hg, rfl, rfl, ha, hb, ?_⟩
      show ((C.wires xu).getD a false = true ∧ (C.wires xv).getD a false = false ∧
          (C.wires xv).getD b false = true ∧ (C.wires xu).getD b false = false) ∨
        ((C.wires xv).getD a false = true ∧ (C.wires xu).getD a false = false ∧
          (C.wires xu).getD b false = true ∧ (C.wires xv).getD b false = false)
      revert h2 h3 hora horb
      cases (C.wires xu).getD a false <;> cases (C.wires xv).getD a false <;>
        cases (C.wires xu).getD b false <;> cases (C.wires xv).getD b false <;> simp
    | _ :: _ :: _ :: _, h => simp at h
  · have hany : ∃ i ∈ ins, (if i < n + j then (C.wires xw).getD i false else false) = true := by
      simpa [PEqualNP.CircuitLowerBounds.GateOp.eval] using h1
    obtain ⟨i, hi, hiv⟩ := hany
    obtain ⟨hlt', _, hor⟩ := K i hiv
    rcases hor with hor | hor
    · have : PEqualNP.CircuitLowerBounds.GateOp.or.eval (ins.map fun i =>
          if i < n + j then (C.wires xu).getD i false else false) = true := by
        simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, List.any_map, List.any_eq_true]
        refine ⟨i, hi, ?_⟩
        show (if i < n + j then (C.wires xu).getD i false else false) = true
        rw [if_pos hlt']
        exact hor
      rw [this] at h2
      cases h2
    · have : PEqualNP.CircuitLowerBounds.GateOp.or.eval (ins.map fun i =>
          if i < n + j then (C.wires xv).getD i false else false) = true := by
        simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, List.any_map, List.any_eq_true]
        refine ⟨i, hi, ?_⟩
        show (if i < n + j then (C.wires xv).getD i false else false) = true
        rw [if_pos hlt']
        exact hor
      rw [this] at h3
      cases h3
  · exact absurd rfl hnn
