import Mathlib
import StacksProject_2024.Chap15.Remark_15_94_7
import StacksProject_2024.Chap20.Lemma_20_36_1
import StacksProject_2024.Chap20.Lemma_20_36_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open TopologicalSpace
open AlgebraicGeometry
open CategoryTheory.SequentialInverseSystem

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}

/-- A global section of the structure sheaf determines an element of the global-sections ring
`Γ(X, \mathcal O_X)` by evaluation on the top open subset. -/
abbrev globalSectionAsRingElement
    (f : StructureSheafGlobalSection X) : globalSectionsRing X :=
  show globalSectionsRing X from globalSectionRestrict f (op (⊤ : Opens X.carrier))

-- Proof sketch: unfold `globalSectionAsRingElement`; it is the value of `f` on the top open.
/-- Evaluating a global section on the top open recovers the corresponding element of
`Γ(X, \mathcal O_X)`. -/
theorem globalSectionAsRingElement_def
    (f : StructureSheafGlobalSection X) :
    globalSectionAsRingElement f =
      (show globalSectionsRing X from globalSectionRestrict f (op (⊤ : Opens X.carrier))) :=
  rfl

/-- The standard Milnor cokernel model for `R^1 \!\varprojlim` of a sequential inverse system of
modules. -/
abbrev sequentialModuleR1Lim {A : Type u} [CommRing A]
    (M : SequentialInverseSystem (ModuleCat A)) : ModuleCat A :=
  cokernel <|
    Pi.lift fun n ↦
      Pi.π (fun k ↦ M.obj (op k)) n -
        Pi.π (fun k ↦ M.obj (op k)) (n + 1) ≫ M.map ((homOfLE (Nat.le_succ n)).op)

-- Proof sketch: unfold `sequentialModuleR1Lim`; it is defined as the cokernel of the Milnor
-- difference map on the product of the stages of `M`.
/-- The Milnor model for `R^1 \!\varprojlim M_n` is the cokernel of the usual difference map on
`∏_n M_n`. -/
theorem sequentialModuleR1Lim_def {A : Type u} [CommRing A]
    (M : SequentialInverseSystem (ModuleCat A)) :
    sequentialModuleR1Lim M =
      cokernel
        (Pi.lift fun n ↦
          Pi.π (fun k ↦ M.obj (op k)) n -
            Pi.π (fun k ↦ M.obj (op k)) (n + 1) ≫ M.map ((homOfLE (Nat.le_succ n)).op)) :=
  rfl

section

variable (f : StructureSheafGlobalSection X) (ℱ : (RingedSpace.Modules X))
variable (quotTower : ℕᵒᵖ ⥤ (RingedSpace.Modules X)) (p : ℕ)

local notation "f₀" => globalSectionAsRingElement f
local notation "Hp" => moduleGlobalCohomology X (p : ℤ) ℱ
local notation "Hp1" => moduleGlobalCohomology X (((p + 1 : ℕ) : ℤ)) ℱ
local notation "Qsys" => principalPowerQuotientTower f₀ Hp
local notation "Bsys" => moduleGlobalCohomologyTower (p : ℤ) quotTower
local notation "Tsys" => principalPowerTorsionTower f₀ Hp1

-- Proof sketch: apply the long exact cohomology sequence to the short exact sequences
-- `0 → \mathcal F/f^n\mathcal F → \mathcal F/f^(n+1)\mathcal F → H^{p+1}(X,\mathcal F)[f^(n+1)]`
-- furnished by the `f`-torsion-free quotient-tower condition, and assemble the resulting maps
-- functorially in `n`.
/-- Remark 20.36.6 (1): if `quotTower` models the quotient tower
`n ↦ \mathcal F / f^(n+1)\mathcal F` of an `f`-torsion-free `\mathcal O_X`-module `\mathcal F`,
then for every `p` there is a short exact sequence of inverse systems
`0 → (H^p(X,\mathcal F)/f^(n+1)H^p(X,\mathcal F))_n →
 (H^p(X,\mathcal F/f^(n+1)\mathcal F))_n →
 (H^{p+1}(X,\mathcal F)[f^(n+1)])_n → 0`.
This is the source tower reindexed from powers `f^n` with `n ≥ 1` to powers `f^(n+1)` with
`n : ℕ`. -/
theorem exists_cohomology_shortExact_of_torsionFreeQuotientTower
    (hquot : torsionFreeQuotientTowerCondition f quotTower) :
    ∃ (ι : Qsys ⟶ Bsys) (π : Bsys ⟶ Tsys) (h : ι ≫ π = 0),
      (ShortComplex.mk ι π h).ShortExact := sorry

-- Proof sketch: each transition map in the quotient tower
-- `H^p(X,\mathcal F)/f^(n+2)H^p(X,\mathcal F) → H^p(X,\mathcal F)/f^(n+1)H^p(X,\mathcal F)` is
-- surjective, so the images into any fixed stage stabilize immediately.
/-- Remark 20.36.6 (2): the inverse system
`n ↦ H^p(X,\mathcal F)/f^(n+1)H^p(X,\mathcal F)` is Mittag-Leffler. Equivalently, the source
inverse system `{H^p(X,\mathcal F)/f^nH^p(X,\mathcal F)}` is Mittag-Leffler after the same
reindexing shift. -/
theorem cohomology_principalPowerQuotientTower_isMittagLeffler :
    IsMittagLeffler Qsys := by
  simpa using principalPowerQuotientTower_isMittagLeffler f₀ Hp

-- Proof sketch: combine the short exact sequence of inverse systems from part `(1)` with the
-- Mittag-Leffler property from part `(2)`, then apply inverse-limit exactness for sequential
-- systems to obtain the short exact sequence on limits.
/-- Remark 20.36.6 (3): under the same quotient-tower hypothesis, there is a short exact sequence
`0 → \widehat{H^p(X,\mathcal F)} → \varprojlim_n H^p(X,\mathcal F/f^(n+1)\mathcal F) →
 T_f(H^{p+1}(X,\mathcal F)) → 0`,
where the left term is the usual `f`-adic completion, modeled by the inverse limit of the quotient
tower, and the right term is the principal Tate module, modeled by the inverse limit of the
torsion tower. -/
theorem exists_cohomology_completion_shortExact_of_torsionFreeQuotientTower
    (hquot : torsionFreeQuotientTowerCondition f quotTower) :
    ∃ (ι : limit Qsys ⟶ limit Bsys)
      (π : limit Bsys ⟶ limit Tsys)
      (h : ι ≫ π = 0),
      (ShortComplex.mk ι π h).ShortExact := sorry

-- Proof sketch: use the six-term exact sequence for derived inverse limits on the short exact
-- system from part `(1)`. The left quotient tower is Mittag-Leffler by part `(2)`, so its
-- `R^1 \!\varprojlim` term vanishes and the remaining two `R^1 \!\varprojlim` terms identify.
/-- Remark 20.36.6 (4): under the same quotient-tower hypothesis, the standard Milnor models for
`R^1 \!\varprojlim_n H^p(X,\mathcal F/f^(n+1)\mathcal F)` and
`R^1 \!\varprojlim_n H^{p+1}(X,\mathcal F)[f^(n+1)]` are canonically isomorphic. -/
theorem cohomologyTower_R1Lim_iso_torsion_of_torsionFreeQuotientTower
    (hquot : torsionFreeQuotientTowerCondition f quotTower) :
    IsIsomorphic (sequentialModuleR1Lim Bsys) (sequentialModuleR1Lim Tsys) := sorry

-- Proof sketch: apply Remark `15.94.7` to the short exact sequence of cohomology towers from part
-- `(1)`. Since the left quotient tower is Mittag-Leffler by part `(2)`, the middle tower is
-- Mittag-Leffler exactly when the right torsion tower is.
/-- Remark 20.36.6 (5): under the same quotient-tower hypothesis, the inverse system
`n ↦ H^{p+1}(X,\mathcal F)[f^(n+1)]` is Mittag-Leffler if and only if the inverse system
`n ↦ H^p(X,\mathcal F/f^(n+1)\mathcal F)` is Mittag-Leffler. -/
theorem cohomologyTower_isMittagLeffler_iff_torsion_of_torsionFreeQuotientTower
    (hquot : torsionFreeQuotientTowerCondition f quotTower) :
    IsMittagLeffler Bsys ↔ IsMittagLeffler Tsys := by
  rcases exists_cohomology_shortExact_of_torsionFreeQuotientTower f ℱ quotTower p hquot with
    ⟨ι, π, h, hShort⟩
  simpa using
    principalPower_shortExact_middle_isMittagLeffler_iff_torsion f₀ Hp Hp1 Bsys ι π h hShort

end

end AlgebraicGeometry.RingedSpace
