import Mathlib
import StacksProject_2024.Chap34.Definition_34_9_10

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced `Flat.comp` and
-- `Flat.isStableUnderBaseChange` as the relevant closure facts. Local Chapter 34 precedent
-- `Lemma_34_6_3` handles the analogous pretopology axioms by writing down the singleton,
-- composite, and pullback families explicitly. In statement stage, the concrete finite families
-- are kept visible in the theorem statements instead of being hidden behind structure-valued data.

section

variable {T T' : Scheme.{u}} (hT : IsAffine T)

/-- Lemma 34.9.11 (1): if `T` is affine and `f : T' ⟶ T` is an isomorphism, then the singleton
family `{T' ⟶ T}` is a standard fpqc covering of `T`. -/
@[stacks 03LA]
theorem singletonFamily_isStandardFpqc_of_isIso
    {T' : Scheme.{u}} (hT' : IsAffine T') (f : T' ⟶ T) [IsIso f] :
    let U : Fin 1 → Scheme.{u} := fun _ ↦ T'
    let map : (j : Fin 1) → U j ⟶ T := fun _ ↦ f
    (∀ j, IsAffine (U j)) ∧
      Presieve.ofArrows U map ∈
        (Scheme.precoverage (fun {_ _} g ↦ Flat g)).coverings T := sorry

/-- Lemma 34.9.11 (2): if `𝒰` is a standard fpqc covering of `T` and each member `𝒰.U i` carries
a standard fpqc covering `𝒱 i`, then the sigma-indexed composite family
`{(𝒱 i).U j ⟶ 𝒰.U i ⟶ T}` is a standard fpqc covering of `T`. -/
@[stacks 03LA]
theorem sigmaCompositeFamily_isStandardFpqc
    (𝒰 : StandardFpqcCover T)
    (𝒱 : ∀ i : Fin 𝒰.n, StandardFpqcCover (𝒰.U i)) :
    let U : (Sigma fun i : Fin 𝒰.n ↦ Fin (𝒱 i).n) → Scheme.{u} :=
      fun ij ↦ (𝒱 ij.1).U ij.2
    let map : (ij : Sigma fun i : Fin 𝒰.n ↦ Fin (𝒱 i).n) → U ij ⟶ T :=
      fun ij ↦ (𝒱 ij.1).map ij.2 ≫ 𝒰.map ij.1
    (∀ ij, IsAffine (U ij)) ∧
      Presieve.ofArrows U map ∈
        (Scheme.precoverage (fun {_ _} g ↦ Flat g)).coverings T := sorry

/-- Lemma 34.9.11 (3): if `𝒰` is a standard fpqc covering of the affine scheme `T` and
`f : T' ⟶ T` is a morphism from an affine scheme `T'`, then the pullback family
`{T' ×[T] 𝒰.U i ⟶ T'}` is a standard fpqc covering of `T'`. -/
@[stacks 03LA]
theorem pullbackFamily_isStandardFpqc
    {T' : Scheme.{u}} (hT' : IsAffine T')
    (𝒰 : StandardFpqcCover T) (f : T' ⟶ T) :
    let U : Fin 𝒰.n → Scheme.{u} := fun i ↦ pullback f (𝒰.map i)
    let map : (i : Fin 𝒰.n) → U i ⟶ T' := fun i ↦ pullback.fst f (𝒰.map i)
    (∀ i, IsAffine (U i)) ∧
      Presieve.ofArrows U map ∈
        (Scheme.precoverage (fun {_ _} g ↦ Flat g)).coverings T' := sorry

end

end AlgebraicGeometry
