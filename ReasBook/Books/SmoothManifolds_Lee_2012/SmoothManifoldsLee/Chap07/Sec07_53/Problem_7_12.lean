import Mathlib
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap07.Sec07_47.Definition_7_47_extra_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Manifold ContDiff

universe u𝕜 uEG uHG uG uEH uHH uH

-- Domain sampling for this refine pass:
-- `MulAction.compHom`
-- `MulActionHom`
-- `ContMDiffMul.contMDiffSMul`
-- `MulAction.contMDiffSMul_compHom`
-- `ContMDiffMonoidMorphism`

section LieGroupHomomorphisms

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {EG : Type uEG} [NormedAddCommGroup EG] [NormedSpace 𝕜 EG]
variable {HG : Type uHG} [TopologicalSpace HG]
variable {EH : Type uEH} [NormedAddCommGroup EH] [NormedSpace 𝕜 EH]
variable {HH : Type uHH} [TopologicalSpace HH]
variable {I : ModelWithCorners 𝕜 EG HG} {J : ModelWithCorners 𝕜 EH HH}
variable {G : Type uG} [Monoid G] [TopologicalSpace G] [ChartedSpace HG G]
variable {H : Type uH} [Monoid H] [TopologicalSpace H] [ChartedSpace HH H]

namespace ContMDiffMonoidMorphism

/-- Problem 7-12: every smooth monoid homomorphism, hence in particular every Lie group
homomorphism, is equivariant for the canonical left-translation actions, with the target action
viewed through `F.toMonoidHom`. -/
def toMulActionHom (F : ContMDiffMonoidMorphism I J ∞ G H) :
    G →ₑ[F.toMonoidHom] H where
  toFun := F
  map_smul' := F.map_mul

/-- Source-facing textbook form of `toMulActionHom`. -/
theorem toMulActionHom_map_smul
    (F : ContMDiffMonoidMorphism I J ∞ G H) (g x : G) :
    let _ : MulAction G H := MulAction.compHom H F.toMonoidHom
    F (g • x) = g • F x :=
  F.toMulActionHom.map_smul' g x

/-- If multiplication on `H` is smooth, then the `G`-action on `H` obtained from `F.toMonoidHom`
by `MulAction.compHom` is smooth. -/
theorem toMonoidHom_contMDiffSMul
    [ContMDiffMul J ∞ H] (F : ContMDiffMonoidMorphism I J ∞ G H) :
    let _ : MulAction G H := MulAction.compHom H F.toMonoidHom
    ContMDiffSMul I J ∞ G H :=
  MulAction.contMDiffSMul_compHom F.contMDiff_toFun

end ContMDiffMonoidMorphism

end LieGroupHomomorphisms
