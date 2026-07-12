import StacksProject_2024.Chap34.Definition_34_9_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry

noncomputable section

universe u v

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced the coproduct-family API around `Limits.Sigma.desc`,
-- and local Chapter 34 precedent uses the same sigma-coproduct packaging for the analogous ph and
-- `V`-covering singleton-family reformulations.

variable {T : Scheme.{u}} {ι : Type v}

/-- The singleton source scheme `∐ i, (X i).left` over `T` attached to the family `X`. -/
abbrev sigmaDescSingletonObj (X : ι → Over T) [HasCoproduct fun i ↦ (X i).left] :
    PUnit → Scheme.{u} :=
  fun _ ↦ ∐ fun i ↦ (X i).left

/-- The unique morphism in the singleton family attached to `X`, namely the coproduct morphism
`∐ i, (X i).left ⟶ T` induced by the family `X`. -/
abbrev sigmaDescSingletonMap (X : ι → Over T) [HasCoproduct fun i ↦ (X i).left] :
    ∀ p : PUnit, sigmaDescSingletonObj X p ⟶ T :=
  fun _ ↦ Limits.Sigma.desc fun i ↦ (X i).hom

/-- The singleton family over `T` whose sole morphism is the coproduct morphism
`∐ i, (X i).left ⟶ T` induced by the family `X`. This is the canonical singleton-family bridge
for the family `X`. -/
abbrev sigmaDescSingleton (X : ι → Over T) [HasCoproduct fun i ↦ (X i).left] : PUnit → Over T :=
  fun p ↦ Over.mk (sigmaDescSingletonMap X p)

@[simp] theorem sigmaDescSingleton_hom (X : ι → Over T) [HasCoproduct fun i ↦ (X i).left]
    (p : PUnit) :
    (sigmaDescSingleton X p).hom = sigmaDescSingletonMap X p :=
  rfl

/-- Lemma 34.9.4: a family of morphisms `Tᵢ ⟶ T` is an fpqc covering if and only if the singleton
family whose unique member is the induced coproduct morphism `∐ i, Tᵢ ⟶ T` is an fpqc covering. -/
@[stacks 040I]
theorem isFpqcCovering_iff_sigmaDesc (X : ι → Over T)
    [HasCoproduct fun i ↦ (X i).left] :
    IsFpqcCovering X ↔
      IsFpqcCovering (sigmaDescSingleton X) := sorry

/-- An fpqc covering remains fpqc after replacing the family by the singleton family whose sole
member is the induced coproduct morphism. -/
theorem IsFpqcCovering.sigmaDescSingleton (X : ι → Over T)
    [HasCoproduct fun i ↦ (X i).left] (hX : IsFpqcCovering X) :
    IsFpqcCovering (sigmaDescSingleton X) :=
  (isFpqcCovering_iff_sigmaDesc X).mp hX

/-- If the singleton family whose unique member is the induced coproduct morphism is fpqc, then
the original family is fpqc. -/
theorem IsFpqcCovering.of_sigmaDescSingleton (X : ι → Over T)
    [HasCoproduct fun i ↦ (X i).left]
    (hX : IsFpqcCovering (AlgebraicGeometry.sigmaDescSingleton X)) :
    IsFpqcCovering X :=
  (isFpqcCovering_iff_sigmaDesc X).mpr hX

end AlgebraicGeometry
