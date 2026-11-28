import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.L_meta_58302 :
    ∃ C : Circuit, FanInTwo C ∧ C.size ≤ 13 ∧
      ∀ i j : Fin 6,
        C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
          (274843946 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  let W : Circuit :=
    ⟨[⟨.or, [3, 5]⟩, ⟨.and, [0, 6]⟩, ⟨.or, [1, 5]⟩,
      ⟨.or, [0, 8]⟩, ⟨.not, [9]⟩, ⟨.or, [2, 5]⟩,
      ⟨.or, [0, 11]⟩, ⟨.and, [1, 12]⟩, ⟨.or, [10, 13]⟩,
      ⟨.or, [7, 14]⟩], 15⟩
  refine ⟨W, ?_, by decide +kernel, by decide +kernel⟩
  intro g hg
  simp only [W, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
