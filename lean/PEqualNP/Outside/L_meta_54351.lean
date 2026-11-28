import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.L_meta_54351 :
    PEqualNP.Represents.RepSizeAtMost
      (fun (u : Fin 4) (v : Fin 6) => (291326 : ℕ).testBit (6 * u.val + v.val)) 11 := by
  let witness : Circuit :=
    ⟨[⟨.or, [1, 2]⟩, ⟨.or, [3, 10]⟩, ⟨.and, [4, 11]⟩,
      ⟨.or, [5, 6]⟩, ⟨.or, [0, 10]⟩, ⟨.and, [13, 14]⟩,
      ⟨.or, [8, 9]⟩, ⟨.or, [7, 16]⟩, ⟨.and, [0, 17]⟩,
      ⟨.or, [12, 18]⟩, ⟨.or, [15, 19]⟩], 20⟩
  refine ⟨witness, ?_, by decide, by decide⟩
  simp [Monotone2, witness]
