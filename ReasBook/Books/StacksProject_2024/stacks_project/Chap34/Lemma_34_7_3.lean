import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v w

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` identified the generic `Pretopology` closure axioms, and
-- local Chapter 34 precedent uses `Scheme.fppfPrecoverage` as the canonical fppf-cover owner.

/-- Lemma 34.7.3 (1): if `T' ⟶ T` is an isomorphism, then the singleton family
`{T' ⟶ T}` is an fppf covering of `T`. -/
@[stacks 021O]
theorem fppfCoveringSingletonOfIsIso {T T' : Scheme.{u}} (f : T' ⟶ T) [IsIso f] :
    Presieve.singleton f ∈ Scheme.fppfPrecoverage.coverings T := sorry

/-- Lemma 34.7.3 (2): if `{T_i ⟶ T}` is an fppf covering and each `T_i` has an
fppf covering `{T_{ij} ⟶ T_i}`, then the sigma-indexed composite family
`{T_{ij} ⟶ T_i ⟶ T}` is an fppf covering of `T`. -/
@[stacks 021O]
theorem fppfCoveringSigmaComposite {T : Scheme.{u}} {ι : Type v} {J : ι → Type w}
    {Tᵢ : ι → Scheme.{u}} (f : (i : ι) → Tᵢ i ⟶ T)
    {Tᵢⱼ : (i : ι) → J i → Scheme.{u}}
    (g : (i : ι) → (j : J i) → Tᵢⱼ i j ⟶ Tᵢ i)
    (hf : Presieve.ofArrows Tᵢ f ∈ Scheme.fppfPrecoverage.coverings T)
    (hg : ∀ i, Presieve.ofArrows (Tᵢⱼ i) (g i) ∈
      Scheme.fppfPrecoverage.coverings (Tᵢ i)) :
    Presieve.ofArrows (fun ij : Sigma J ↦ Tᵢⱼ ij.1 ij.2)
      (fun ij : Sigma J ↦ g ij.1 ij.2 ≫ f ij.1) ∈
        Scheme.fppfPrecoverage.coverings T := sorry

/-- Lemma 34.7.3 (3): if `{T_i ⟶ T}` is an fppf covering and `T' ⟶ T` is any
morphism of schemes, then the pullback family `{T' ×_T T_i ⟶ T'}` is an fppf covering
of `T'`. -/
@[stacks 021O]
theorem fppfCoveringPullback {T T' : Scheme.{u}} {ι : Type v}
    {Tᵢ : ι → Scheme.{u}} (f : (i : ι) → Tᵢ i ⟶ T)
    (hf : Presieve.ofArrows Tᵢ f ∈ Scheme.fppfPrecoverage.coverings T)
    (g : T' ⟶ T) :
    Presieve.ofArrows (fun i ↦ pullback g (f i))
      (fun i ↦ pullback.fst g (f i)) ∈ Scheme.fppfPrecoverage.coverings T' := sorry

end AlgebraicGeometry
