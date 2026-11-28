import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.L_meta_58226 :
    (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 13 ∧
      ∀ i j : Fin 6,
        C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (270582950 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  let W : Circuit :=
    ⟨[⟨.or, [2, 5]⟩, ⟨.or, [1, 6]⟩, ⟨.and, [0, 7]⟩,
      ⟨.or, [1, 4]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [9, 10]⟩,
      ⟨.or, [5, 11]⟩, ⟨.or, [0, 12]⟩, ⟨.not, [13]⟩,
      ⟨.or, [8, 14]⟩], 15⟩
  refine ⟨W, ?_, by decide +kernel, by decide +kernel⟩
  intro g hg
  simp only [W, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
