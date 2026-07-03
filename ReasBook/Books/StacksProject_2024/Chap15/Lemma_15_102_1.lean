import Mathlib
import StacksProject_2024.Chap04.Example_4_22_6
import StacksProject_2024.Chap12.Definition_12_31_2
import StacksProject_2024.Chap15.Lemma_15_102_Basic

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open Limits
open Opposite
open SequentialProObjectMorphismRep
open scoped IdealPowerSubmodule

noncomputable section

universe u v

namespace CategoryTheory.ShortComplex

variable {A : Type u} [CommRing A]

local notation "Mod" => ModuleCat A
local notation "SeqMod" => SequentialInverseSystem Mod

/- Domain-style sampling for `15.102.1`:
- primary domain: homology of short complexes of finite modules and the induced `I`-adic inverse
  systems;
- sampled core/canonical owners:
  `ShortComplex.leftHomology`,
  `ShortComplex.leftHomologyMap`,
  `ShortComplex.map`,
  `ShortComplex.mapNatTrans`,
  `Functor.ofOpSequence`,
  `SequentialProObjectMorphismRep.IsProIsomorphism`,
  `Submodule.pow_smul_top_le`;
- best owner abstraction: the ambient short complex `S : ShortComplex (ModuleCat A)` should own
  the ideal-power stage complexes, the ambient homology `S.leftHomology`, and the induced towers;
  the ideal-power stage maps should be induced from the owner-level short-complex APIs
  `ShortComplex.map` and `ShortComplex.mapNatTrans`, the inverse systems should use the canonical
  owner `Functor.ofOpSequence`, and the resulting pro-comparison should live in
  `SequentialProObjectMorphismRep` with owner property `r.IsProIsomorphism`;
- primitive data: the short complex `S` together with the ideal-power submodules
  `I^n S.X₁`, `I^n S.X₂`, and `I^n S.X₃`;
- derived API: the stage homology objects, their transition maps, the map to the ambient
  homology, and the eventual comparison data;
-- source/core/bridge triage:
  `source-facing`: the eventual comparison between filtered homology and the `I`-adic filtration on
    ambient homology;
  `core/canonical`: `ShortComplex.leftHomology`, `ShortComplex.leftHomologyMap`,
    `ShortComplex.map`, `ShortComplex.mapNatTrans`, `Functor.ofOpSequence`,
    `idealPowerSubmodule`, and
    `SequentialProObjectMorphismRep.IsProIsomorphism`;
  `bridge/view`: the ideal-power stage complexes and the induced maps from those stages to `S`. -/

section Comparison

variable (S : ShortComplex Mod) (I : Ideal A)

/-- The `n`th ideal-power subcomplex of `S`. -/
abbrev idealPowerSubmoduleStageComplex
    (S : ShortComplex Mod) (I : Ideal A) (n : ℕ) : ShortComplex Mod :=
  S.map (idealPowerSubmoduleFunctor I n)

instance idealPowerSubmoduleStageComplex_hasLeftHomology
    (S : ShortComplex Mod) (I : Ideal A) (n : ℕ) :
    (S.idealPowerSubmoduleStageComplex I n).HasLeftHomology := by
  let T : ShortComplex Mod := S.idealPowerSubmoduleStageComplex I n
  let _ : HasKernel T.g := inferInstance
  let _ : HasCokernel (kernel.lift T.g T.f T.zero) := inferInstance
  exact HasLeftHomology.mk' (LeftHomologyData.ofHasKernelOfHasCokernel T)

/-- The homology object `H[n]` of the `n`th ideal-power subcomplex of `S`. -/
abbrev idealPowerSubmoduleHomologyStage
    (S : ShortComplex Mod) (I : Ideal A) (n : ℕ) : Mod :=
  (S.idealPowerSubmoduleStageComplex I n).leftHomology

/-- The canonical map from the homology of the `n`th ideal-power subcomplex to the ambient left
homology of `S`, induced by the inclusion `I^[n] S ⟶ S`. -/
abbrev idealPowerSubmoduleHomologyToLeftHomology
    (S : ShortComplex Mod) (I : Ideal A) (n : ℕ) :
    S.idealPowerSubmoduleHomologyStage I n ⟶ S.leftHomology :=
  leftHomologyMap <| S.mapNatTrans (idealPowerSubtypeNatTrans I n)

/-- The transition map `(H[n+1]) ⟶ H[n]` on the homology tower of the ideal-power subcomplexes of
`S`. -/
abbrev idealPowerSubmoduleHomologyStep
    (S : ShortComplex Mod) (I : Ideal A) (n : ℕ) :
    S.idealPowerSubmoduleHomologyStage I (n + 1) ⟶
      S.idealPowerSubmoduleHomologyStage I n :=
  leftHomologyMap <| S.mapNatTrans (idealPowerSubmoduleInclusionNatTrans I (Nat.le_succ n))

/-- The inverse system `(H[n])_n` obtained by taking left homology of the ideal-power
subcomplexes of `S`. -/
abbrev idealPowerSubmoduleHomologyTower
    (S : ShortComplex Mod) (I : Ideal A) : SeqMod :=
  Functor.ofOpSequence (fun n ↦ S.idealPowerSubmoduleHomologyStep I n)

/-- The `n`th ideal-power stage `I^[n] H` of the ambient left homology `H = S.leftHomology`. -/
abbrev leftHomologyIdealPowerStage
    (S : ShortComplex Mod) (I : Ideal A) (n : ℕ) : Mod :=
  idealPowerStage I n S.leftHomology

/-- The transition map `I^[n+1] H ⟶ I^[n] H` on the ideal-power tower of the ambient left homology
`H = S.leftHomology`. -/
abbrev leftHomologyIdealPowerStep
    (S : ShortComplex Mod) (I : Ideal A) (n : ℕ) :
    S.leftHomologyIdealPowerStage I (n + 1) ⟶ S.leftHomologyIdealPowerStage I n :=
  ModuleCat.ofHom <|
    Submodule.inclusion
      (show I^[n + 1] S.leftHomology ≤ I^[n] S.leftHomology from
        idealPowerSubmodule_mono I (Nat.le_succ n))

/-- The inverse system `(I^[n] H)_n` on the ambient left homology `H = S.leftHomology`. -/
abbrev leftHomologyIdealPowerTower
    (S : ShortComplex Mod) (I : Ideal A) : SeqMod :=
  Functor.ofOpSequence (fun n ↦ S.leftHomologyIdealPowerStep I n)

variable [IsNoetherianRing A]
variable [Module.Finite A S.X₁] [Module.Finite A S.X₂] [Module.Finite A S.X₃]

/-- Arithmetic helper for the shifted transition maps in Lemma 15.102.1. -/
theorem shiftComparison_le (n c : ℕ) :
    n ≤ c + (c + n) := by
  exact (Nat.le_add_left n c).trans (Nat.le_add_left (c + n) c)

/-- Lemma 15.102.1: for a complex `K ⟶ L ⟶ M` of finite `A`-modules over a Noetherian ring and an
ideal `I`, the filtered homology groups `H[n]` are eventually compared with the `I`-adic
filtration on `H = ker β / im α` by shifted natural transformations in both directions whose
stagewise composites are the canonical transition morphisms. -/
theorem exists_idealPowerSubmoduleHomologyComparison
    (S : ShortComplex Mod) (I : Ideal A)
    [Module.Finite A S.X₁] [Module.Finite A S.X₂] [Module.Finite A S.X₃] :
    ∃ c : ℕ, 0 < c ∧
      ∃ toPower :
        (S.idealPowerSubmoduleHomologyTower I).shift c ⟶ S.leftHomologyIdealPowerTower I,
        ∃ fromPower :
          (S.leftHomologyIdealPowerTower I).shift c ⟶ S.idealPowerSubmoduleHomologyTower I,
          (∀ n : ℕ,
            toPower.app (Opposite.op n) ≫ ModuleCat.ofHom (idealPowerSubtype I n S.leftHomology) =
              S.idealPowerSubmoduleHomologyToLeftHomology I (c + n)) ∧
            (∀ n : ℕ,
              ((fromPower.app (Opposite.op (c + n))) :
                  S.leftHomologyIdealPowerStage I (c + (c + n)) ⟶
                    S.idealPowerSubmoduleHomologyStage I (c + n)) ≫
                toPower.app (Opposite.op n) =
                SequentialInverseSystem.transitionMap (S.leftHomologyIdealPowerTower I)
                  (shiftComparison_le n c)) ∧
            ∀ n : ℕ,
              ((toPower.app (Opposite.op (c + n))) :
                  S.idealPowerSubmoduleHomologyStage I (c + (c + n)) ⟶
                    S.leftHomologyIdealPowerStage I (c + n)) ≫
                fromPower.app (Opposite.op n) =
                SequentialInverseSystem.transitionMap (S.idealPowerSubmoduleHomologyTower I)
                  (shiftComparison_le n c) := sorry

/-- Companion to Lemma 15.102.1: the filtered homology tower `(H[n])_n` and the `I`-adic tower
`(H^[n])_n`, with `H^[n] = I^n H`, are pro-isomorphic via the explicit shift representative coming
from the forward comparison natural transformation. -/
theorem idealPowerSubmoduleHomologyTower_isProIsomorphic_to_leftHomologyIdealPowerTower
    (S : ShortComplex Mod) (I : Ideal A)
    [Module.Finite A S.X₁] [Module.Finite A S.X₂] [Module.Finite A S.X₃] :
    ∃ c : ℕ, 0 < c ∧
      ∃ comparison :
        (S.idealPowerSubmoduleHomologyTower I).shift c ⟶ S.leftHomologyIdealPowerTower I,
        (ofShiftNatTrans c comparison).IsProIsomorphism := sorry

end Comparison

end CategoryTheory.ShortComplex
