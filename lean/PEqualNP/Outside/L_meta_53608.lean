import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.L_meta_53608 :
    PEqualNP.Represents.RepSizeAtMost
      (fun (u : Fin 4) (v : Fin 6) => (1865339 : ℕ).testBit (6 * u.val + v.val)) 11 := by
  let witness : Circuit :=
    ⟨[⟨.or, [5, 6]⟩, ⟨.or, [5, 9]⟩, ⟨.and, [0, 11]⟩,
      ⟨.or, [2, 3]⟩, ⟨.and, [10, 13]⟩, ⟨.or, [8, 12]⟩,
      ⟨.or, [7, 15]⟩, ⟨.or, [0, 1]⟩, ⟨.and, [16, 17]⟩,
      ⟨.or, [14, 18]⟩, ⟨.or, [4, 19]⟩], 20⟩
  refine ⟨witness, ?_, by decide, by decide⟩
  simp [Monotone2, witness]
