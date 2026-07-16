import Mathlib
import StacksProject_2024.stacks_project.Chap28.Lemma_28_17_2

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry DirectSum

noncomputable section

/- Semantic recall:
`lean_leansearch` surfaced the absolute `AlgebraicGeometry.Proj` and
`ProjectiveSpectrum.Proj.structureSheaf` owners. Local Chapter 17/28 inspection found the
dependency-closed graded twisted-global-sections owners `Γ_*(ℒ, ℱ)` and the principal-open
localization bridges used in Lemma 28.17.2. The current project does not yet package the
projective twist family `𝒪_X(n)` on `Proj(S)`, the associated sheaf `\widetilde M` of a graded
module on `Proj(S)`, or the comparison map from Constructions, Lemma 27.10.7 as concrete
declarations. -/

/- Lemma 28.28.5: let `S` be a graded ring such that `X = Proj(S)` is quasi-compact, and let
`\mathcal F` be a quasi-coherent `\mathcal O_X`-module. Set
`M = ⊕_{n ∈ ℤ} Γ(X, \mathcal F(n))` as the graded `S`-module from Constructions, Section 27.10.
The map `\widetilde M → \mathcal F` of Constructions, Lemma 27.10.7 is an isomorphism. If `X` is
covered by standard opens `D_+(f)` with `f` of degree `1`, then the induced maps
`M_n → Γ(X, \mathcal F(n))` are the identity maps.

The exact source-facing theorem awaits concrete owners for the projective twist sheaves and the
associated graded-module sheaf on `Proj`. The available dependency-closed API relevant to the
statement is recalled below rather than introducing a fake arbitrary comparison map. -/
#check AlgebraicGeometry.Proj
#check AlgebraicGeometry.Proj.basicOpen
#check AlgebraicGeometry.Proj.basicOpenIsoSpec
#check AlgebraicGeometry.Proj.affineOpenCoverOfIrrelevantLESpan
#check AlgebraicGeometry.RingedSpace.gradedTwistedGlobalSections
#check AlgebraicGeometry.RingedSpace.gradedTwistedGlobalSectionsDegree
#check AlgebraicGeometry.RingedSpace.gradedTwistedGlobalSections_module
#check SheafOfModules.IsQuasicoherent
#check AlgebraicGeometry.Γ_restrict_isLocalization
#check fun {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] (f : Γ(X, ⊤)) ↦
  (inferInstance :
    IsLocalizedModule (.powers f)
      (ModuleCat.Hom.hom (ℱ.val.map (CategoryTheory.homOfLE (X.basicOpen_le f)).op)))
