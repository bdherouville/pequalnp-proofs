import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24544

open PEqualNP.CircuitLowerBounds

def circ : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [1, 2]⟩,
        ⟨GateOp.or, [3, 4]⟩,
        ⟨GateOp.and, [6, 7]⟩,
        ⟨GateOp.and, [1, 2]⟩,
        ⟨GateOp.and, [3, 4]⟩,
        ⟨GateOp.or, [8, 9]⟩,
        ⟨GateOp.or, [10, 0]⟩,
        ⟨GateOp.or, [11, 12]⟩ ],
    output := 13 }

end PEqualNP.Outside.L_meta_24544

theorem PEqualNP.Outside.L_meta_24544 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (4294463 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_24544.circ, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_24544.circ, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
