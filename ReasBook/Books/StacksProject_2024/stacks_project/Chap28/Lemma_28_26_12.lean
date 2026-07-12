import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
import StacksProject_2024.Chap28.Lemma_28_26_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u v

namespace AlgebraicGeometry.Scheme.Modules

variable {A : Type u} {σ : Type v}
variable [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]
variable {X : Scheme} [MonoidalCategory X.Modules]

/- Semantic recall: the source-facing content of Lemma 28.26.12 uses the canonical projective
spectrum owner `Proj 𝒜`, the scheme-module pullback owner `j^*`, and the Chapter 28 ampleness
owners `Invertible` and `IsAmple`. In the current repository, the projective twisting family on
`Proj 𝒜` and the specific ample witness used by the Stacks proof are not yet packaged as concrete
API, so this item is kept as a recall block rather than introducing a noncanonical existential
wrapper over arbitrary pulled-back modules. -/

/- Lemma 28.26.12: if a quasi-compact scheme `X` admits an open immersion `j : X ⟶ Proj(S)`,
then some pullback `j^*\mathcal O_{Proj(S)}(d)` is an invertible ample `\mathcal O_X`-module.
The current dependency-closed API already provides the ambient owners for `Proj`, pullback of
modules, open immersions, invertibility, and ampleness, but it does not yet package the twisting
sheaves on `Proj(S)` or the specific witness used in the source proof. -/
#check fun (j : X ⟶ Proj 𝒜) ↦ IsOpenImmersion j
#check fun (j : X ⟶ Proj 𝒜) ↦ Scheme.Modules.pullback j
#check fun (j : X ⟶ Proj 𝒜) (ℒ : (Proj 𝒜).Modules) [Invertible ℒ] ↦
  (inferInstance : Invertible ((j^*).obj ℒ))
#check fun (j : X ⟶ Proj 𝒜) (ℒ : (Proj 𝒜).Modules) [Invertible ℒ] ↦
  IsAmple ((j^*).obj ℒ)

end AlgebraicGeometry.Scheme.Modules
