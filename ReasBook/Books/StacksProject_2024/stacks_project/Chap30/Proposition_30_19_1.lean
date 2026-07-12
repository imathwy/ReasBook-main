import StacksProject_2024.Chap30.Lemma_30_16_3

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {X S : Scheme.{u}}

/- Semantic recall: `lean_leansearch` surfaced the canonical `IsProper` morphism owner. Local
Chapter 30 precedent represents higher direct images of module sheaves as
`((Scheme.Modules.pushforward f).rightDerived i).obj ℱ`, and coherence as `ℱ.IsCoherent`.
The tag evidence is consistent for Stacks tag `02O5`. -/

/-- Proposition 30.19.1: let `S` be a locally Noetherian scheme, let `f : X ⟶ S` be a proper
morphism, and let `ℱ` be a coherent `\mathcal O_X`-module. Then every higher direct image
`R^i f_* ℱ` is a coherent `\mathcal O_S`-module. -/
@[stacks 02O5]
theorem higherDirectImageModule_isCoherent_of_proper
    (f : X ⟶ S) [IsLocallyNoetherian S] [IsProper f]
    [HasInjectiveResolutions X.Modules]
    (ℱ : X.Modules) [ℱ.IsCoherent] (i : ℕ) :
    (((Scheme.Modules.pushforward f).rightDerived i).obj ℱ).IsCoherent := sorry

end AlgebraicGeometry.Scheme
