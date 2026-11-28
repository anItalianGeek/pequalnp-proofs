import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.L_meta_54742 :
    ∃ C : Circuit, FanInTwo C ∧ C.size ≤ 10 ∧
      ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
        (270649663 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  let witness : Circuit :=
    ⟨[⟨.or, [2, 5]⟩, ⟨.and, [1, 6]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [5, 8]⟩,
      ⟨.or, [1, 9]⟩, ⟨.not, [10]⟩, ⟨.or, [7, 11]⟩, ⟨.or, [0, 12]⟩], 13⟩
  refine ⟨witness, ?_, by decide, by decide⟩
  simp [FanInTwo, witness]
