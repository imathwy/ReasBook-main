import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

-- Semantic recall / local analogue check:
-- - `lean_leansearch` recalled `AlgebraicGeometry.QuasiCompact` for quasi-compact morphisms
--   and the sober-space owners `genericPoints.ofComponent` / `genericPoints.isGenericPoint`.
-- - Nearby Chapter 29 dominant-morphism files phrase the source image as `Set.range f.base` and
--   generic points of irreducible components through `irreducibleComponents` and `IsGenericPoint`.

/-- Lemma 29.8.6: let `f : X ⟶ S` be a quasi-compact morphism of schemes. Let `η ∈ S` be a
generic point of an irreducible component of `S`. If `η` is not in the image of `f`, then there is
an open neighbourhood `V ⊆ S` of `η` such that `f^{-1}(V)` is empty. -/
@[stacks 02NE]
theorem exists_open_preimage_eq_bot_of_genericPoint_not_mem_range
    {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f]
    {η : S} {Z : irreducibleComponents S} (hηZ : IsGenericPoint η (Z : Set S))
    (hη : η ∉ Set.range f.base) :
    ∃ V : S.Opens, η ∈ V ∧ f ⁻¹ᵁ V = ⊥ := sorry

end AlgebraicGeometry
