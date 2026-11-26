import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents in
theorem PEqualNP.Outside.L_meta_19986 :
    (PEqualNP.Represents.RepSizeAtMost
      (fun u v : Fin 8 => (7413361890700106610 : ℕ).testBit (8 * u.val + v.val)) 31) := by
  refine ⟨⟨[
    ⟨.or, [9, 12]⟩,
    ⟨.or, [13, 14]⟩,
    ⟨.or, [8, 11]⟩,
    ⟨.or, [8, 15]⟩,
    ⟨.or, [11, 12]⟩,
    ⟨.or, [9, 13]⟩,
    ⟨.or, [10, 15]⟩,
    ⟨.or, [10, 14]⟩,
    ⟨.or, [16, 17]⟩,
    ⟨.or, [18, 16]⟩,
    ⟨.or, [19, 20]⟩,
    ⟨.or, [21, 22]⟩,
    ⟨.or, [23, 20]⟩,
    ⟨.or, [18, 22]⟩,
    ⟨.or, [19, 17]⟩,
    ⟨.or, [21, 23]⟩,
    ⟨.and, [0, 24]⟩,
    ⟨.and, [1, 25]⟩,
    ⟨.and, [2, 26]⟩,
    ⟨.and, [3, 27]⟩,
    ⟨.and, [4, 28]⟩,
    ⟨.and, [5, 29]⟩,
    ⟨.and, [6, 30]⟩,
    ⟨.and, [7, 31]⟩,
    ⟨.or, [32, 33]⟩,
    ⟨.or, [34, 35]⟩,
    ⟨.or, [36, 37]⟩,
    ⟨.or, [38, 39]⟩,
    ⟨.or, [40, 41]⟩,
    ⟨.or, [42, 43]⟩,
    ⟨.or, [44, 45]⟩], 46⟩, ?_, ?_, ?_⟩
  · intro g hg
    fin_cases hg <;> simp
  · decide
  · decide
