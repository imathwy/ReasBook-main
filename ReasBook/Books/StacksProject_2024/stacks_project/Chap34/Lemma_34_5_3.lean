import Mathlib

open CategoryTheory
open CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme

noncomputable section

-- The source-facing layer here is the smooth-specialized `Scheme.Cover (Scheme.precoverage
-- @Smooth)` API. Clause (1) needs an explicit singleton cover construction, while clauses (2) and
-- (3) are already the canonical `Scheme.Cover` transitivity and pullback operations.

/-- Lemma 34.5.3 (1): if `f : T' ⟶ T` is an isomorphism, then the singleton family `{T' ⟶ T}` is
a smooth covering of `T`. -/
def smoothCoverOfIsIso {T T' : Scheme.{u}} (f : T' ⟶ T) [IsIso f] :
    T.Cover (precoverage @Smooth) :=
  (Cover.mkOfCovers PUnit (fun _ ↦ T') (fun _ ↦ f)
      (fun x ↦ ⟨PUnit.unit, inv f x, by simp [← Hom.comp_apply]⟩)
      (fun _ ↦ by infer_instance) : T.Cover (precoverage @Smooth))

/- Lemma 34.5.3 (2): if `𝒰` is a smooth covering of `T` and each component `𝒰.X i` carries a
smooth covering `𝒱 i`, then the composite family `{𝒱 i j ⟶ 𝒰.X i ⟶ T}` is the canonical bind
`𝒰.bind 𝒱`. -/
#check
  (fun {T : Scheme.{u}} (𝒰 : T.Cover (precoverage @Smooth))
    (𝒱 : ∀ i : 𝒰.I₀, (𝒰.X i).Cover (precoverage @Smooth)) ↦ 𝒰.bind 𝒱 :
      {T : Scheme.{u}} → (𝒰 : T.Cover (precoverage @Smooth)) →
        (∀ i : 𝒰.I₀, (𝒰.X i).Cover (precoverage @Smooth)) →
          T.Cover (precoverage @Smooth))

/- Lemma 34.5.3 (3): if `𝒰` is a smooth covering of `T` and `f : T' ⟶ T`, then the pullback
family with components `pullback (𝒰.f i) f`, canonically identified with `T' ×[T] 𝒰.X i`, is the
canonical pullback cover `𝒰.pullback₂ f`. -/
#check
  (fun {T T' : Scheme.{u}} (𝒰 : T.Cover (precoverage @Smooth)) (f : T' ⟶ T) ↦ 𝒰.pullback₂ f :
      {T T' : Scheme.{u}} → (𝒰 : T.Cover (precoverage @Smooth)) → (T' ⟶ T) →
        T'.Cover (precoverage @Smooth))

end

end AlgebraicGeometry.Scheme
