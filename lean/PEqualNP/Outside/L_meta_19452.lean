import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19452

open PEqualNP.CircuitLowerBounds

lemma foldl_len {α β : Type} (h : List α → β → α) (gs : List β) (init : List α) :
    (gs.foldl (fun w g => w ++ [h w g]) init).length = init.length + gs.length := by
  induction gs generalizing init with
  | nil => simp
  | cons g gs ih => rw [List.foldl_cons, ih]; simp; omega

lemma foldl_prefix {α β : Type} (h : List α → β → α) (gs : List β) (init : List α) :
    init <+: gs.foldl (fun w g => w ++ [h w g]) init := by
  induction gs generalizing init with
  | nil => simp
  | cons g gs ih => exact (List.prefix_append _ _).trans (ih _)

lemma foldl_get {α β : Type} (h : List α → β → α) (gs : List β) (init : List α) (j : ℕ)
    (hj : j < gs.length) :
    (gs.foldl (fun w g => w ++ [h w g]) init)[init.length + j]? =
      some (h ((gs.take j).foldl (fun w g => w ++ [h w g]) init) gs[j]) := by
  induction gs generalizing init j with
  | nil => simp at hj
  | cons g gs ih =>
    cases j with
    | zero =>
      simp only [List.foldl_cons, List.take_zero, List.foldl_nil, List.getElem_cons_zero,
        Nat.add_zero]
      obtain ⟨t, ht⟩ := foldl_prefix h gs (init ++ [h init g])
      rw [← ht]; simp
    | succ j =>
      simp only [List.foldl_cons, List.take_succ_cons, List.getElem_cons_succ]
      have := ih (init ++ [h init g]) j (by simpa using hj)
      simp only [List.length_append, List.length_singleton] at this
      rw [show init.length + (j + 1) = init.length + 1 + j by omega, this]

lemma getD_of_prefix {l l' : List Bool} (hp : l <+: l') (i : ℕ) :
    l.getD i false = if i < l.length then l'.getD i false else false := by
  obtain ⟨t, rfl⟩ := hp
  split_ifs with hi
  · simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl

def wh (w : List Bool) (g : Gate) : Bool := g.op.eval (g.inputs.map fun i => w.getD i false)

lemma wires_eq (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl (fun w g => w ++ [wh w g]) x := rfl

lemma wire_gate (C : Circuit) (x : List Bool) (j : ℕ) (hj : j < C.gates.length) :
    (C.wires x).getD (x.length + j) false =
      C.gates[j].op.eval (C.gates[j].inputs.map fun i =>
        if i < x.length + j then (C.wires x).getD i false else false) := by
  rw [wires_eq, List.getD_eq_getElem?_getD, foldl_get _ _ _ _ hj]
  simp only [Option.getD_some, wh]
  congr 1
  apply List.map_congr_left
  intro i _
  have hp : (C.gates.take j).foldl (fun w g => w ++ [wh w g]) x <+:
      C.gates.foldl (fun w g => w ++ [wh w g]) x := by
    have := foldl_prefix wh (C.gates.drop j) ((C.gates.take j).foldl (fun w g => w ++ [wh w g]) x)
    rwa [← List.foldl_append, List.take_append_drop] at this
  simp only [wh] at hp
  rw [getD_of_prefix hp, foldl_len, List.length_take, min_eq_left hj.le]

def ch (n : ℕ) (cs : List (List ℕ)) (g : Gate) : List ℕ :=
  (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
    (fun w => (w - n) :: cs.getD (w - n) [])

lemma cones_eq (n : ℕ) (C : Circuit) :
    PEqualNP.EdgeOwnership.cones n C = C.gates.foldl (fun w g => w ++ [ch n w g]) [] := rfl

lemma cone_sub (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length) (w : ℕ)
    (hw : w ∈ C.gates[j].inputs) (h1 : n ≤ w) (h2 : w < n + j) :
    ∀ k, (k = w - n ∨ k ∈ (PEqualNP.EdgeOwnership.cones n C).getD (w - n) []) →
      k ∈ (PEqualNP.EdgeOwnership.cones n C).getD j [] := by
  intro k hk
  have e := foldl_get (ch n) C.gates [] j hj
  simp only [List.length_nil, Nat.zero_add] at e
  set Q := (C.gates.take j).foldl (fun w g => w ++ [ch n w g]) [] with hQ
  have hQl : Q.length = j := by
    rw [hQ, foldl_len, List.length_take, min_eq_left hj.le]; simp
  have hp : Q <+: C.gates.foldl (fun w g => w ++ [ch n w g]) [] := by
    have := foldl_prefix (ch n) (C.gates.drop j) Q
    rwa [hQ, ← List.foldl_append, List.take_append_drop] at this
  rw [cones_eq, List.getD_eq_getElem?_getD, e, Option.getD_some, ch]
  rw [List.mem_flatMap]
  refine ⟨w, ?_, ?_⟩
  · rw [List.mem_filter]; refine ⟨hw, ?_⟩; simp [hQl]; omega
  · have hq : Q.getD (w - n) [] = (C.gates.foldl (fun w g => w ++ [ch n w g]) []).getD (w - n) [] := by
      obtain ⟨t, ht⟩ := hp
      rw [← ht, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_append_left (by omega)]
    rw [hq, ← cones_eq]
    rcases hk with hk | hk
    · simp [hk]
    · exact List.mem_cons_of_mem _ hk

lemma x_prefix (C : Circuit) (x : List Bool) : x <+: C.wires x := by
  rw [wires_eq]; exact foldl_prefix _ _ _

lemma wires_len (C : Circuit) (x : List Bool) : (C.wires x).length = x.length + C.gates.length := by
  rw [wires_eq]; exact foldl_len _ _ _

lemma main (C : Circuit) (N : ℕ) (x x' : List Bool) (hx : x.length = N) (hx' : x'.length = N)
    (Good : ℕ → Prop)
    (hgood : ∀ k (hk : k < C.gates.length), Good k → ∀ i ∈ C.gates[k].inputs, i < N →
      x.getD i false = x'.getD i false) :
    ∀ j, j < C.gates.length → Good j →
      (∀ k ∈ (PEqualNP.EdgeOwnership.cones N C).getD j [], Good k) →
      (C.wires x).getD (N + j) false = (C.wires x').getD (N + j) false := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
  intro hj hg hc
  have e := wire_gate C x j hj
  have e' := wire_gate C x' j hj
  rw [hx] at e
  rw [hx'] at e'
  rw [e, e']
  congr 1
  apply List.map_congr_left
  intro i hi
  by_cases h1 : i < N + j
  · simp only [h1, ite_true]
    by_cases h0 : i < N
    · have a := getD_of_prefix (x_prefix C x) i
      have a' := getD_of_prefix (x_prefix C x') i
      rw [hx] at a
      simp only [h0, ite_true] at a
      rw [hx'] at a'
      simp only [h0, ite_true] at a'
      rw [← a, ← a']
      exact hgood j hj hg i hi h0
    · have hk := cone_sub N C j hj i hi (by omega) h1
      have := ih (i - N) (by omega) (by omega) (hc _ (hk _ (Or.inl rfl)))
        (fun k hk' => hc _ (hk _ (Or.inr hk')))
      rwa [show N + (i - N) = i by omega] at this
  · simp [h1]

lemma oneEach_diff {n m : ℕ} (u u' : Fin n) (v : Fin m) (i : ℕ) (h1 : i ≠ u.val)
    (h2 : i ≠ u'.val) :
    (PEqualNP.Represents.oneEach u v).getD i false =
      (PEqualNP.Represents.oneEach u' v).getD i false := by
  unfold PEqualNP.Represents.oneEach
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  by_cases hi : i < n
  · rw [List.getElem?_append_left (by simpa using hi), List.getElem?_append_left (by simpa using hi)]
    simp only [List.getElem?_ofFn]
    simp [hi, Fin.ext_iff, h1, h2]
  · rw [List.getElem?_append_right (by simp; omega), List.getElem?_append_right (by simp; omega)]
    simp

end PEqualNP.Outside.L_meta_19452

open PEqualNP.Outside.L_meta_19452

theorem PEqualNP.Outside.L_meta_19452 : (∀ (n m : ℕ) (A : Fin n → Fin m → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit) (u u' : Fin n), PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.Represents.Represents A C → (C.output ≠ u.val ∧ ∀ g < C.gates.length, (C.output = n + m + g ∨ (n + m ≤ C.output ∧ PEqualNP.EdgeOwnership.InCone (n + m) C g (C.output - (n + m)))) → u.val ∉ (C.gates.getD g ⟨PEqualNP.CircuitLowerBounds.GateOp.and, []⟩).inputs) → (C.output ≠ u'.val ∧ ∀ g < C.gates.length, (C.output = n + m + g ∨ (n + m ≤ C.output ∧ PEqualNP.EdgeOwnership.InCone (n + m) C g (C.output - (n + m)))) → u'.val ∉ (C.gates.getD g ⟨PEqualNP.CircuitLowerBounds.GateOp.and, []⟩).inputs) → ∀ v : Fin m, A u v = A u' v) := by
  intro n m A C u u' _ hR hu hu' v
  have key : C.eval (PEqualNP.Represents.oneEach u v) = C.eval (PEqualNP.Represents.oneEach u' v) := by
    have hl : (PEqualNP.Represents.oneEach u v).length = n + m := by
      simp [PEqualNP.Represents.oneEach]
    have hl' : (PEqualNP.Represents.oneEach u' v).length = n + m := by
      simp [PEqualNP.Represents.oneEach]
    unfold PEqualNP.CircuitLowerBounds.Circuit.eval
    rcases lt_or_ge C.output (n + m) with ho | ho
    · have a := getD_of_prefix (x_prefix C (PEqualNP.Represents.oneEach u v)) C.output
      have a' := getD_of_prefix (x_prefix C (PEqualNP.Represents.oneEach u' v)) C.output
      rw [hl] at a
      rw [hl'] at a'
      simp only [ho, ite_true] at a a'
      rw [← a, ← a']
      exact oneEach_diff u u' v _ hu.1 hu'.1
    · rcases lt_or_ge (C.output - (n + m)) C.gates.length with hj | hj
      · have ho' : C.output = n + m + (C.output - (n + m)) := by omega
        have := main C (n + m) _ _ hl hl'
          (fun k => u.val ∉ (C.gates.getD k ⟨PEqualNP.CircuitLowerBounds.GateOp.and, []⟩).inputs ∧
            u'.val ∉ (C.gates.getD k ⟨PEqualNP.CircuitLowerBounds.GateOp.and, []⟩).inputs)
          (by
            intro k hk hg i hi hiN
            rw [List.getD_eq_getElem _ _ hk] at hg
            exact oneEach_diff u u' v i (fun h => hg.1 (h ▸ hi)) (fun h => hg.2 (h ▸ hi)))
          (C.output - (n + m)) hj ⟨hu.2 _ hj (Or.inl ho'), hu'.2 _ hj (Or.inl ho')⟩
          (by
            intro k hk
            by_cases hkl : k < C.gates.length
            · exact ⟨hu.2 k hkl (Or.inr ⟨ho, hk⟩), hu'.2 k hkl (Or.inr ⟨ho, hk⟩)⟩
            · rw [List.getD_eq_default _ _ (by omega)]
              simp)
        rwa [← ho'] at this
      · rw [List.getD_eq_default _ _ (by rw [wires_len]; omega),
          List.getD_eq_default _ _ (by rw [wires_len]; omega)]
  rw [← hR, ← hR]
  exact key
