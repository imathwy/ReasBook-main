import Mathlib
import StacksProject_2024.Chap34.Definition_34_6_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme

noncomputable section

variable {T T' : Scheme.{u}}

-- The source-facing layer here is the syntomic-specialized `Scheme.Cover
-- (Scheme.precoverage (@Syntomic))` API. Clause (1) is the canonical singleton-family
-- covering statement from the precoverage `HasIsos` owner, while clauses (2) and (3) are already
-- the canonical `Scheme.Cover` transitivity and pullback operations.

namespace SyntomicCover

/-- Lemma 34.6.3 (1): if `f : T' ⟶ T` is an isomorphism, then the singleton family `{T' ⟶ T}` is
a syntomic covering of `T`. -/
theorem ofIsIso (f : T' ⟶ T) [IsIso f] :
    Presieve.singleton f ∈ (Scheme.precoverage (@Syntomic)).coverings T := by
  simpa using (Scheme.precoverage (@Syntomic)).mem_coverings_of_isIso f

/- Lemma 34.6.3 (2): refining each member of a syntomic covering by a syntomic covering produces
another syntomic covering of the base scheme, namely the canonical bind `𝒰.bind 𝒱`. -/
#check
  (fun {T : Scheme.{u}} (𝒰 : SyntomicCover T)
    (𝒱 : ∀ i : 𝒰.I₀, SyntomicCover (𝒰.X i)) ↦ 𝒰.bind 𝒱 :
      {T : Scheme.{u}} → (𝒰 : SyntomicCover T) →
        (∀ i : 𝒰.I₀, SyntomicCover (𝒰.X i)) →
          SyntomicCover T)

/- Lemma 34.6.3 (3): pulling a syntomic covering of `T` back along `T' ⟶ T` yields the canonical
pullback cover `𝒰.pullback₂ f` of `T'`, whose members are the fiber products `T' ×[T] Tᵢ`. -/
#check
  (fun {T T' : Scheme.{u}} (𝒰 : SyntomicCover T) (f : T' ⟶ T) ↦ 𝒰.pullback₂ f :
      {T T' : Scheme.{u}} → (𝒰 : SyntomicCover T) → (T' ⟶ T) →
        SyntomicCover T')

end SyntomicCover

end

end Scheme

end AlgebraicGeometry
