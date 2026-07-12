import StacksProject_2024.Chap30.Lemma_30_4_5
import StacksProject_2024.Chap31.Definition_31_31_6
import StacksProject_2024.Chap17.Definition_17_12_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {X S : Scheme.{u}}

-- Semantic recall: `lean_leansearch` surfaced the scheme-side `IsLocallyNoetherian` owner. The
-- checked-in `LocallyProjective` owner currently imports a broken relative-ampleness dependency,
-- so the source hypothesis is spelled out using the Chapter 29 open-cover/projective-bundle
-- definition. Local Chapter 30 precedent writes higher direct images as
-- `((Scheme.Modules.pushforward f).rightDerived i).obj ℱ`.

/-- A projective-bundle presentation of the restriction of `f` over one member of a source open
cover, spelling out the Chapter 29 locally projective hypothesis without a conjunction package. -/
structure OpenCoverProjectivePresentation
    (f : X ⟶ S) (𝒰 : Scheme.OpenCover.{u} S) (j : 𝒰.I₀) where
  P : Scheme.{u}
  π : P ⟶ ((𝒰.f j).opensRange).toScheme
  ℰ : ((𝒰.f j).opensRange).toScheme.Modules
  isFiniteType : ℰ.IsFiniteType
  isQuasicoherent : ℰ.IsQuasicoherent
  isProjectiveBundle : Scheme.IsProjectiveBundle π ℰ
  i : (f ⁻¹ᵁ ((𝒰.f j).opensRange)).toScheme ⟶ P
  isClosedImmersion : IsClosedImmersion i
  fac : i ≫ π = f ∣_ ((𝒰.f j).opensRange)

/-- Lemma 30.16.3: if `S` is locally Noetherian, `f : X ⟶ S` is locally projective (spelled out
as an open cover of the target on which the restricted morphisms admit projective-bundle
presentations), and `\mathcal F` is a coherent `\mathcal O_X`-module, then every higher direct
image `R^i f_* \mathcal F` is a coherent `\mathcal O_S`-module. -/
@[stacks 02O4]
theorem higherDirectImageModule_isCoherent_of_locallyProjective
    (f : X ⟶ S)
    (h_locallyProjective : ∃ 𝒰 : Scheme.OpenCover.{u} S, ∀ j : 𝒰.I₀,
      Nonempty (OpenCoverProjectivePresentation f 𝒰 j))
    [IsLocallyNoetherian S]
    [HasInjectiveResolutions X.Modules]
    (ℱ : X.Modules) [ℱ.IsCoherent] (i : ℕ) :
    (((Scheme.Modules.pushforward f).rightDerived i).obj ℱ).IsCoherent := sorry

end AlgebraicGeometry.Scheme
