import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Tactic.Recall

open scoped Manifold ContDiff

universe u𝕜 uE uH uM uE' uH' uM'

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type uH} [TopologicalSpace H]
variable (I : ModelWithCorners 𝕜 E H)
variable (M : Type uM) [TopologicalSpace M] [ChartedSpace H M]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
variable {H' : Type uH'} [TopologicalSpace H']
variable (I' : ModelWithCorners 𝕜 E' H')
variable (M' : Type uM') [TopologicalSpace M'] [ChartedSpace H' M']

/- Problem 3-3 (1): the canonical equivalence between the tangent bundle of a product manifold
and the product of the tangent bundles is `equivTangentBundleProd`. -/
recall equivTangentBundleProd :
    TangentBundle (I.prod I') (M × M') ≃ TangentBundle I M × TangentBundle I' M'

/- Problem 3-3 (2): the canonical equivalence `equivTangentBundleProd` is smooth. -/
recall contMDiff_equivTangentBundleProd

/- Problem 3-3 (3): the inverse of `equivTangentBundleProd` is smooth. -/
recall contMDiff_equivTangentBundleProd_symm

/- The pointwise formula is already the canonical `@[simps]` lemma attached to
`equivTangentBundleProd`; this is a bridge/view recall rather than a new local owner. -/
recall equivTangentBundleProd_apply (p : TangentBundle (I.prod I') (M × M')) :
    equivTangentBundleProd I M I' M' p = (⟨p.1.1, p.2.1⟩, ⟨p.1.2, p.2.2⟩)
