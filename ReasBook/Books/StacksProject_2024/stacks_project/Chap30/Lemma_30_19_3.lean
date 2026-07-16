import Mathlib.CategoryTheory.Presentable.Finite
import StacksProject_2024.stacks_project.Chap24.Definition_24_4_1
import StacksProject_2024.stacks_project.Chap30.Lemma_30_14_3
import StacksProject_2024.stacks_project.Chap30.Lemma_30_16_2
import StacksProject_2024.stacks_project.Chap30.Lemma_30_19_2

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open SheafOfModules.RingedSite
open scoped AlgebraicGeometry DirectSum SheafOfModules.RingedSite.GradedModuleSheaf

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- The commutative-ring-valued structure sheaf of a scheme, as a sheaf on its open subsets. -/
private abbrev schemeCommRingSheaf (X : Scheme.{u}) :
    CategoryTheory.Sheaf (Opens.grothendieckTopology X) CommRingCat.{u} :=
  X.sheaf

/- Semantic recall: `lean_leansearch` surfaced the canonical `IsProper` owner and the categorical
finite-presentability API. Local Chapter 24 provides `GradedAlgebraSheaf` and
`GradedModuleSheaf`, while Chapter 30 represents scheme-module cohomology by
`schemeModuleCohomology` and twists by `schemeModuleTwistByTensorPower`. The current project does
not yet expose a concrete construction of the graded algebra sheaf `f^* \widetilde B`, so the
source-facing declarations take that chosen owner as the parameter `pullbackTildeB`. The tag
evidence is consistent for Stacks tag `0897`. -/

/-- The graded cohomology carrier `H^p(X, ℱ)` of a graded module sheaf, with degree `n` part
`H^p(X, ℱ_n)`. -/
abbrev gradedModuleSheafCohomology {X : Scheme.{u}}
    {pullbackTildeB : GradedAlgebraSheaf.{u, u} (schemeCommRingSheaf X)}
    (ℱ : GradedModuleSheaf.{u, u} pullbackTildeB) (p : ℕ) :
    Type u :=
  DirectSum ℤ fun n ↦ (schemeModuleCohomology (ℱ n) p : Type u)

/-- The defining normal form for graded cohomology of a graded module sheaf. -/
theorem gradedModuleSheafCohomology_def {X : Scheme.{u}}
    {pullbackTildeB : GradedAlgebraSheaf.{u, u} (schemeCommRingSheaf X)}
    (ℱ : GradedModuleSheaf.{u, u} pullbackTildeB) (p : ℕ) :
    gradedModuleSheafCohomology ℱ p =
      DirectSum ℤ fun n ↦ (schemeModuleCohomology (ℱ n) p : Type u) := sorry

/-- The graded cohomology carrier of the twist `ℱ ⊗ L^{\otimes d}`, with degree `n` part
`H^p(X, ℱ_n ⊗ L^{\otimes d})`. -/
abbrev gradedModuleSheafTwistCohomology {X : Scheme.{u}} [MonoidalCategory X.Modules]
    {pullbackTildeB : GradedAlgebraSheaf.{u, u} (schemeCommRingSheaf X)}
    (L : X.Modules) [Invertible L]
    (ℱ : GradedModuleSheaf.{u, u} pullbackTildeB) (d : ℤ) (p : ℕ) : Type u :=
  DirectSum ℤ fun n ↦
    (schemeModuleCohomology (schemeModuleTwistByTensorPower L (ℱ n) d) p : Type u)

/-- The defining normal form for graded cohomology of an integral twist of a graded module sheaf. -/
theorem gradedModuleSheafTwistCohomology_def {X : Scheme.{u}} [MonoidalCategory X.Modules]
    {pullbackTildeB : GradedAlgebraSheaf.{u, u} (schemeCommRingSheaf X)}
    (L : X.Modules) [Invertible L]
    (ℱ : GradedModuleSheaf.{u, u} pullbackTildeB) (d : ℤ) (p : ℕ) :
    gradedModuleSheafTwistCohomology L ℱ d p =
      DirectSum ℤ fun n ↦
        (schemeModuleCohomology (schemeModuleTwistByTensorPower L (ℱ n) d) p : Type u) := sorry

/-- Lemma 30.19.3 (1): let `A` be a Noetherian ring, let `B` be a finitely generated graded
`A`-algebra, let `f : X ⟶ Spec(A)` be proper, and let `ℱ` be a quasi-coherent finite-type graded
module over the chosen graded algebra sheaf `pullbackTildeB = f^* \widetilde B`. Then every graded
cohomology module `H^p(X, ℱ)` is finite over `B`, for the source-induced graded `B`-module
structure. -/
@[stacks 0897]
theorem properPullbackTildeFiniteTypeGradedModuleCohomology_finite
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [IsNoetherianRing A]
    (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜] [Algebra.FiniteType A B]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]
    (pullbackTildeB : GradedAlgebraSheaf.{u, u} (schemeCommRingSheaf X))
    (ℱ : GradedModuleSheaf.{u, u} pullbackTildeB)
    (hℱQuasicoherent : ∀ n : ℤ, (ℱ n).IsQuasicoherent)
    (hℱFiniteType : CategoryTheory.IsFinitelyPresentable ℱ)
    (p : ℕ)
    [DirectSum.Gmodule (fun i ↦ 𝒜 i)
      (fun n : ℤ ↦ (schemeModuleCohomology (ℱ n) p : Type u))]
    [Module B (gradedModuleSheafCohomology ℱ p)] :
    Module.Finite B (gradedModuleSheafCohomology ℱ p) := sorry

/-- Lemma 30.19.3 (2): in the setting of Lemma 30.19.3 (1), if `L` is an ample invertible
`\mathcal O_X`-module, then all positive-degree cohomology of the twists
`ℱ ⊗ L^{\otimes d}` vanishes for all sufficiently large integers `d`. -/
@[stacks 0897]
theorem properPullbackTildeFiniteTypeGradedModuleAmpleTwistCohomology_eventually_isZero
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [IsNoetherianRing A]
    (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜] [Algebra.FiniteType A B]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]
    (pullbackTildeB : GradedAlgebraSheaf.{u, u} (schemeCommRingSheaf X))
    (ℱ : GradedModuleSheaf.{u, u} pullbackTildeB)
    (hℱQuasicoherent : ∀ n : ℤ, (ℱ n).IsQuasicoherent)
    (hℱFiniteType : CategoryTheory.IsFinitelyPresentable ℱ)
    [MonoidalCategory X.Modules] (L : X.Modules) [Invertible L] [IsAmple L] :
    ∃ d0 : ℤ, ∀ d : ℤ, d0 ≤ d → ∀ p : ℕ, 0 < p →
      IsZero (AddCommGrpCat.of (gradedModuleSheafTwistCohomology L ℱ d p)) := sorry

end AlgebraicGeometry.Scheme.Modules
