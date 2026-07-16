import Mathlib.AlgebraicGeometry.Morphisms.Proper
import StacksProject_2024.stacks_project.Chap17.Definition_17_12_1
import StacksProject_2024.stacks_project.Chap28.Definition_28_26_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry DirectSum

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/- Semantic recall: `lean_leansearch` found the canonical `IsProper` morphism owner and the
additive sheaf cohomology owner `Sheaf.H'`. Local Chapter 28 precedent supplies the
`Invertible`/`IsAmple` owner for ample invertible sheaves; the integral tensor powers below are
the concrete powers of the tensor-right autoequivalence stored by `Invertible`. The displayed
section ring and truncated twisted section module are represented by explicit direct-sum carriers,
with their source-induced algebra/module structures kept as typeclass inputs. The Stacks tag
evidence is consistent for tag `0B5T`. -/

/-- The Chapter 28 `Invertible` owner exposes the tensor-right autoequivalence used for integral
tensor powers. -/
instance instTensorRightIsEquivalenceOfInvertible {X : Scheme.{u}}
    [MonoidalCategory X.Modules] (L : X.Modules) [hL : Invertible L] :
    Functor.IsEquivalence (tensorRight L) :=
  hL.tensorRight_isEquivalence

/-- Sheaf cohomology of a scheme module on the top open. -/
abbrev schemeModuleCohomology {X : Scheme.{u}} (F : X.Modules) (p : ℕ) : AddCommGrpCat :=
  (((SheafOfModules.toSheaf X.ringCatSheaf).obj F).H' p (⊤ : Opens X))

/-- The defining normal form for sheaf cohomology of a scheme module on the top open. -/
theorem schemeModuleCohomology_def {X : Scheme.{u}} (F : X.Modules) (p : ℕ) :
    schemeModuleCohomology F p =
      (((SheafOfModules.toSheaf X.ringCatSheaf).obj F).H' p (⊤ : Opens X)) := sorry

/-- Integral tensor powers of an invertible scheme module, as powers of tensoring on the right by
that module applied to the structure sheaf. -/
abbrev schemeModuleTensorPower {X : Scheme.{u}} [MonoidalCategory X.Modules]
    (L : X.Modules) [Invertible L] (d : ℤ) : X.Modules :=
  (((tensorRight L).asEquivalence ^ d).functor.obj
    (SheafOfModules.unit X.ringCatSheaf : X.Modules))

/-- The defining normal form for integral tensor powers of an invertible scheme module. -/
theorem schemeModuleTensorPower_def {X : Scheme.{u}} [MonoidalCategory X.Modules]
    (L : X.Modules) [Invertible L] (d : ℤ) :
    schemeModuleTensorPower L d =
      (((tensorRight L).asEquivalence ^ d).functor.obj
        (SheafOfModules.unit X.ringCatSheaf : X.Modules)) := sorry

/-- The twist `F ⊗ L^{\otimes d}` of a scheme module by an integral tensor power. -/
abbrev schemeModuleTwistByTensorPower {X : Scheme.{u}} [MonoidalCategory X.Modules]
    (L F : X.Modules) [Invertible L] (d : ℤ) : X.Modules :=
  tensorObj F (schemeModuleTensorPower L d)

/-- The defining normal form for twisting by an integral tensor power. -/
theorem schemeModuleTwistByTensorPower_def {X : Scheme.{u}} [MonoidalCategory X.Modules]
    (L F : X.Modules) [Invertible L] (d : ℤ) :
    schemeModuleTwistByTensorPower L F d = tensorObj F (schemeModuleTensorPower L d) := sorry

/-- The displayed section ring carrier `⊕_{d ≥ 0} H^0(X, L^{\otimes d})`. -/
abbrev schemeModuleSectionRing {X : Scheme.{u}} [MonoidalCategory X.Modules]
    (L : X.Modules) [Invertible L] : Type u :=
  DirectSum ℕ fun d ↦
    (schemeModuleCohomology (schemeModuleTensorPower L (d : ℤ)) 0 : Type u)

/-- The defining normal form for the displayed section ring carrier. -/
theorem schemeModuleSectionRing_def {X : Scheme.{u}} [MonoidalCategory X.Modules]
    (L : X.Modules) [Invertible L] :
    schemeModuleSectionRing L =
      DirectSum ℕ fun d ↦
        (schemeModuleCohomology (schemeModuleTensorPower L (d : ℤ)) 0 : Type u) := sorry

/-- The truncated direct sum `⊕_{d ≥ k} H^0(X, F ⊗ L^{\otimes d})`. -/
abbrev schemeModuleTwistedGlobalSectionsFrom {X : Scheme.{u}} [MonoidalCategory X.Modules]
    (L F : X.Modules) [Invertible L] (k : ℤ) : Type u :=
  DirectSum {d : ℤ // k ≤ d} fun d ↦
    (schemeModuleCohomology (schemeModuleTwistByTensorPower L F d.1) 0 : Type u)

/-- The defining normal form for the truncated direct sum of twisted global sections. -/
theorem schemeModuleTwistedGlobalSectionsFrom_def {X : Scheme.{u}}
    [MonoidalCategory X.Modules] (L F : X.Modules) [Invertible L] (k : ℤ) :
    schemeModuleTwistedGlobalSectionsFrom L F k =
      DirectSum {d : ℤ // k ≤ d} fun d ↦
        (schemeModuleCohomology (schemeModuleTwistByTensorPower L F d.1) 0 : Type u) := sorry

section

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable {X : Scheme.{u}}
variable [MonoidalCategory X.Modules]
variable (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]
variable (L F : X.Modules) [hL : Invertible L] [IsAmple L] [F.IsCoherent]

/-- Lemma 30.16.1 (1): for a proper morphism `X → Spec(R)` with `R` Noetherian and an ample
invertible sheaf `L` on `X`, the section ring
`A = ⊕_{d ≥ 0} H^0(X, L^{\otimes d})` is a finitely generated `R`-algebra for the
source-induced ring and algebra structures. -/
@[stacks 0B5T]
theorem properAmpleSectionRing_finiteType
    [CommRing (schemeModuleSectionRing L)] [Algebra R (schemeModuleSectionRing L)] :
    Algebra.FiniteType R (schemeModuleSectionRing L) := sorry

/-- Lemma 30.16.1 (2): for a coherent module `F` on `X`, finitely many integral tensor powers of
the ample invertible sheaf `L` admit an epimorphism from their coproduct onto `F`. -/
@[stacks 0B5T]
theorem properAmpleCoherent_exists_epi_from_tensorPowers :
    ∃ (r : ℕ) (d : Fin r → ℤ)
      (π : (∐ fun j : Fin r ↦ schemeModuleTensorPower L (d j)) ⟶ F), Epi π := sorry

/-- Lemma 30.16.1 (3): for every degree `p`, the cohomology group `H^p(X, F)` of a coherent
module on `X` is finite as an `R`-module for the source-induced module structure. -/
@[stacks 0B5T]
theorem properCoherentSheafCohomology_finite
    (p : ℕ) [Module R (schemeModuleCohomology F p)] :
    Module.Finite R (schemeModuleCohomology F p) := sorry

/-- Lemma 30.16.1 (4): positive-degree cohomology of sufficiently positive twists
`F ⊗ L^{\otimes d}` vanishes. -/
@[stacks 0B5T]
theorem properAmpleCoherentTwistCohomology_eventually_isZero
    (p : ℕ) (hp : 0 < p) :
    ∃ b : ℤ, ∀ d : ℤ, b ≤ d →
      IsZero (schemeModuleCohomology (schemeModuleTwistByTensorPower L F d) p) := sorry

/-- Lemma 30.16.1 (5): for every integer `k`, the graded module
`⊕_{d ≥ k} H^0(X, F ⊗ L^{\otimes d})` is finite over the section ring `A` for the
source-induced graded-module structure. -/
@[stacks 0B5T]
theorem properAmpleCoherentTwistedGlobalSections_finite
    (k : ℤ) [CommRing (schemeModuleSectionRing L)]
    [Module (schemeModuleSectionRing L) (schemeModuleTwistedGlobalSectionsFrom L F k)] :
    Module.Finite (schemeModuleSectionRing L) (schemeModuleTwistedGlobalSectionsFrom L F k) := sorry

end

end AlgebraicGeometry.Scheme.Modules
