import Mathlib
import StacksProject_2024.stacks_project.Chap24.Lemma_24_24_1

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]

local notation "ModO" => ringedSiteModuleCategory J 𝒪
local notation "DGAO" => DifferentialGradedAlgebra (C := C) (J := J) (𝒪 := 𝒪)
local notation "DGMod" =>
  _root_.SheafOfModules.RingedSite.DifferentialGradedModule (C := C) (J := J) (𝒪 := 𝒪)

-- Semantic search note: `lean_leansearch` only surfaced generic adjunction/acyclicity owners such
-- as `HomologicalComplex.Acyclic` and shift/counit lemmas. The statement below therefore stays on
-- the local Chapter 24 functors from `Lemma_24_24_1`, while expressing the shifted-cokernel
-- clause degreewise in `ModO`, where cokernels are already canonical.

namespace DifferentialGradedModule

open UnderlyingGradedModule

/-- The left adjoint `G` from Lemma `24.24.1`, obtained canonically from the right-adjoint
structure on `forgetToGraded 𝒜`. -/
noncomputable abbrev gradedHull (𝒜 : DGAO) :
    UnderlyingGradedModule.moduleCategory 𝒜 ⥤ DifferentialGradedModule.moduleCategory 𝒜 :=
  Functor.leftAdjoint (forgetToGraded 𝒜)

/-- The adjunction `G ⊣ F` attached to the differential graded hull functor `gradedHull 𝒜`. -/
noncomputable abbrev gradedHullAdjunction (𝒜 : DGAO) :
    gradedHull 𝒜 ⊣ forgetToGraded 𝒜 :=
  Adjunction.ofIsRightAdjoint (forgetToGraded 𝒜)

/-- The canonical map `\mathcal N \to F(G(\mathcal N))`, which the Stacks Project proof calls the
counit although it is the unit of the adjunction `G ⊣ F` in mathlib's conventions. -/
noncomputable abbrev gradedHullUnit (𝒜 : DGAO) :
    𝟭 (UnderlyingGradedModule.moduleCategory 𝒜) ⟶
      gradedHull 𝒜 ⋙ forgetToGraded 𝒜 :=
  (gradedHullAdjunction 𝒜).unit

/-- The degree-`n` component of the source's map
`\overline{\mathrm d} : \mathcal N \to \operatorname{Coker}(\mathcal N \to F(G(\mathcal N)))[1]`,
written directly in `ModO` as the differential on `G(\mathcal N)` followed by the cokernel
projection in degree `n + 1`. -/
noncomputable def gradedHullBarDComponent
    (𝒜 : DGAO) (𝒩 : UnderlyingGradedModule.moduleCategory 𝒜) (n : ℤ) :
    𝒩.obj n ⟶ cokernel (((gradedHullUnit 𝒜).app 𝒩).hom (n + 1)) :=
  ((gradedHullUnit 𝒜).app 𝒩).hom n ≫
    ((gradedHull 𝒜).obj 𝒩).toComplex.d n (n + 1) ≫
      cokernel.π (((gradedHullUnit 𝒜).app 𝒩).hom (n + 1))

/-- Lemma 24.24.2 (1): for a graded `\mathcal A`-module `\mathcal N`, the canonical map
`\mathcal N \to F(G(\mathcal N))` is injective, formalized as a monomorphism in the category of
graded `\mathcal A`-modules. -/
theorem gradedHullUnit_mono
    (𝒜 : DGAO) (𝒩 : UnderlyingGradedModule.moduleCategory 𝒜) :
    Mono ((gradedHullUnit 𝒜).app 𝒩) := sorry

/-- Lemma 24.24.2 (2): for a graded `\mathcal A`-module `\mathcal N`, the source's map
`\overline{\mathrm d} : \mathcal N \to \operatorname{Coker}(\mathcal N \to F(G(\mathcal N)))[1]`
is an isomorphism. In the current Chapter 24 owner this is recorded degreewise: the degree-`n`
component lands in the cokernel of the degree-`n + 1` component of the canonical map. -/
theorem gradedHullBarDComponent_isIso
    (𝒜 : DGAO) (𝒩 : UnderlyingGradedModule.moduleCategory 𝒜) (n : ℤ) :
    IsIso (gradedHullBarDComponent 𝒜 𝒩 n) := sorry

/-- Lemma 24.24.2 (3): for a graded `\mathcal A`-module `\mathcal N`, its differential graded
hull `G(\mathcal N)` is acyclic, formalized on the underlying cochain complex. -/
theorem gradedHull_acyclic
    (𝒜 : DGAO) (𝒩 : UnderlyingGradedModule.moduleCategory 𝒜) :
    HomologicalComplex.Acyclic ((gradedHull 𝒜).obj 𝒩).toComplex := sorry

end DifferentialGradedModule

end

end SheafOfModules.RingedSite
