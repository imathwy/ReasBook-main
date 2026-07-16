import StacksProject_2024.stacks_project.Chap29.Lemma_29_11_5_Core

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry
namespace Scheme

variable {S : Scheme.{u}}

local notation "J" => Opens.grothendieckTopology S
local notation "Mod(" 𝒪 ")" => ringedSiteModuleCategory J 𝒪

/- Semantic recall: on a scheme, module-sheaf quasi-coherence is exposed by the canonical
object-level predicate `ℱ.IsQuasicoherent`, and the forgetful functor from `\mathcal A`-modules
to `\mathcal O_S`-modules is `restrictionAlong`. The canonical owner for quasi-coherent
`\mathcal O_S`-algebras is `S.QcAlgebraUnder`. -/

namespace QcAlgebraUnder

/-- Lemma 29.11.6: let `S` be a scheme and let `\mathcal A` be a quasi-coherent
`\mathcal O_S`-algebra. Then an `\mathcal A`-module is quasi-coherent as an
`\mathcal O_S`-module if and only if it is quasi-coherent as an `\mathcal A`-module. -/
@[stacks 0H88]
theorem isQuasicoherent_iff
    (A : S.QcAlgebraUnder) (ℱ : Mod(A.obj.right)) :
    ((restrictionAlong A.obj.hom).obj ℱ).IsQuasicoherent ↔ ℱ.IsQuasicoherent := by
  letI :
      ((restrictionAlong A.obj.hom).obj
        (unitModule J A.obj.right)).IsQuasicoherent := by
    simpa using A.isQuasicoherent_restrictedUnit
  sorry

/-- If an `\mathcal A`-module is quasi-coherent after restricting scalars to
`\mathcal O_S`, then it is quasi-coherent as an `\mathcal A`-module. -/
theorem isQuasicoherent_of_restrictionAlong
    (A : S.QcAlgebraUnder) {ℱ : Mod(A.obj.right)}
    (hℱ : ((restrictionAlong A.obj.hom).obj ℱ).IsQuasicoherent) :
    ℱ.IsQuasicoherent :=
  (A.isQuasicoherent_iff ℱ).mp hℱ

/-- If an `\mathcal A`-module is quasi-coherent, then its restriction of scalars to
`\mathcal O_S` is quasi-coherent. -/
theorem restrictionAlong_obj_isQuasicoherent
    (A : S.QcAlgebraUnder) {ℱ : Mod(A.obj.right)} [ℱ.IsQuasicoherent] :
    ((restrictionAlong A.obj.hom).obj ℱ).IsQuasicoherent :=
  (A.isQuasicoherent_iff ℱ).mpr inferInstance

end QcAlgebraUnder

section RestrictionAlong

variable {𝒜 : Sheaf J CommRingCat.{u}} (α : S.sheaf ⟶ 𝒜)
variable (h𝒜 : ((restrictionAlong α).obj (unitModule J 𝒜)).IsQuasicoherent)

include h𝒜

/-- Bridge form of `QcAlgebraUnder.isQuasicoherent_iff` for a raw
`\mathcal O_S`-algebra structure map together with its quasi-coherence witness. -/
theorem restrictionAlong_isQuasicoherent_iff
    (ℱ : Mod(𝒜)) :
    ((restrictionAlong α).obj ℱ).IsQuasicoherent ↔ ℱ.IsQuasicoherent := by
  let A : S.QcAlgebraUnder := ⟨Under.mk α, h𝒜⟩
  exact A.isQuasicoherent_iff ℱ

/-- Raw-map companion to `QcAlgebraUnder.isQuasicoherent_of_restrictionAlong`. -/
theorem isQuasicoherent_of_restrictionAlong'
    {ℱ : Mod(𝒜)} (hℱ : ((restrictionAlong α).obj ℱ).IsQuasicoherent) :
    ℱ.IsQuasicoherent :=
  (restrictionAlong_isQuasicoherent_iff α h𝒜 ℱ).mp hℱ

/-- Raw-map companion to `QcAlgebraUnder.restrictionAlong_obj_isQuasicoherent`. -/
theorem restrictionAlong_obj_isQuasicoherent
    {ℱ : Mod(𝒜)} [ℱ.IsQuasicoherent] :
    ((restrictionAlong α).obj ℱ).IsQuasicoherent :=
  (restrictionAlong_isQuasicoherent_iff α h𝒜 ℱ).mpr inferInstance

end RestrictionAlong

end Scheme
end AlgebraicGeometry
