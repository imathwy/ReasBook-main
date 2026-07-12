import Mathlib
import StacksProject_2024.Chap31.Definition_31_14_1
import StacksProject_2024.Chap31.Definition_31_21_1
import StacksProject_2024.Chap31.Lemma_31_13_7

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}}

local notation "ModX" => SheafOfModules X.ringCatSheaf
local notation "𝒪X" => (SheafOfModules.unit X.ringCatSheaf : ModX)
local notation "EffectiveCartierIdeal" =>
  (fun I : Subobject 𝒪X ↦
    Functor.IsEquivalence (tensorRight (Subobject.underlying.obj I)))

-- Semantic recall: `lean_leansearch` surfaced the canonical
-- `Scheme.IdealSheafData.subscheme` and `ShortComplex.ShortExact` owners; local Chapter 31
-- precedent supplies `effectiveCartierDivisorNegSheaf`, `closedImmersionIdealSubobject`, and
-- `effectiveCartierDivisorSum` for the divisor notation in this statement.

/-- Lemma 31.14.3: if `D ⊆ D'` are effective Cartier divisors on `X`, encoded by the
ideal-sheaf inequality `D' ≤ D`, and `D' = D + C` for an effective Cartier divisor `C`, then the
`O_X`-modules `\mathcal O_X(-D)|_C`, `\mathcal O_{D'}`, and `\mathcal O_D` fit into a short
exact sequence. The closed-subscheme modules are viewed on `X` by pushforward along their closed
immersions. -/
@[stacks 0C4T]
theorem exists_negSheaf_restrict_structureSheaf_shortExact
    [MonoidalCategory (SheafOfModules X.ringCatSheaf)]
    [SymmetricCategory (SheafOfModules X.ringCatSheaf)]
    [MonoidalClosed (SheafOfModules X.ringCatSheaf)]
    (D D' C : X.IdealSheafData)
    [Fact (EffectiveCartierIdeal (closedImmersionIdealSubobject D.subschemeι))]
    [Fact (EffectiveCartierIdeal (closedImmersionIdealSubobject D'.subschemeι))]
    [Fact (EffectiveCartierIdeal (closedImmersionIdealSubobject C.subschemeι))]
    (hsubset : D' ≤ D) (hsum : D' = effectiveCartierDivisorSum D C) :
    ∃ (f :
        (Scheme.Modules.pushforward C.subschemeι).obj
            ((Scheme.Modules.pullback C.subschemeι).obj
              (effectiveCartierDivisorNegSheaf
                (closedImmersionIdealSubobject D.subschemeι))) ⟶
          (Scheme.Modules.pushforward D'.subschemeι).obj
            (SheafOfModules.unit D'.subscheme.ringCatSheaf : D'.subscheme.Modules))
      (g :
        (Scheme.Modules.pushforward D'.subschemeι).obj
            (SheafOfModules.unit D'.subscheme.ringCatSheaf : D'.subscheme.Modules) ⟶
          (Scheme.Modules.pushforward D.subschemeι).obj
            (SheafOfModules.unit D.subscheme.ringCatSheaf : D.subscheme.Modules))
      (hfg : f ≫ g = 0),
      (ShortComplex.mk f g hfg).ShortExact := sorry

end AlgebraicGeometry.Scheme
