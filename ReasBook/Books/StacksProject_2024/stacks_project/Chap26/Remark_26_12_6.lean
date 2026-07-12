import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

noncomputable section

-- Semantic recall: `lean_leansearch` surfaced `IsLocallyClosed` and `coborder`; mathlib defines
-- `coborder T = (closure T \ T)ᶜ`, exactly the open complement of the boundary used here.
-- Definition 26.12.5 is represented by `Scheme.IdealSheafData.vanishingIdeal` on a closed subset.

variable {X : Scheme.{u}}

/-- The boundary of a subset in the sense used for a locally closed subset: `∂T = closure T \ T`. -/
@[stacks 0F2L]
abbrev locallyClosedBoundary (T : Set X) : Set X :=
  closure T \ T

/-- The boundary abbreviation unfolds to the set-theoretic closure difference. -/
@[stacks 0F2L]
theorem locallyClosedBoundary_def (T : Set X) :
    locallyClosedBoundary T = closure T \ T := sorry

/-- The open subscheme `X \ ∂T` attached to a locally closed subset `T`. -/
@[stacks 0F2L]
def locallyClosedBoundaryComplementOpen (T : Set X) (hT : IsLocallyClosed T) : X.Opens :=
  ⟨(locallyClosedBoundary T)ᶜ, hT.isOpen_coborder⟩

/-- The underlying open subset of `locallyClosedBoundaryComplementOpen` is the complement of
`closure T \ T`. -/
@[stacks 0F2L]
theorem coe_locallyClosedBoundaryComplementOpen (T : Set X) (hT : IsLocallyClosed T) :
    (locallyClosedBoundaryComplementOpen T hT : Set X) = (closure T \ T)ᶜ := sorry

/-- The subset `T`, viewed as a closed subset of the open subscheme `X \ ∂T`. -/
@[stacks 0F2L]
def locallyClosedSubsetAsClosed (T : Set X) (hT : IsLocallyClosed T) :
    TopologicalSpace.Closeds (locallyClosedBoundaryComplementOpen T hT).toScheme :=
  ⟨(Subtype.val : (locallyClosedBoundaryComplementOpen T hT).toScheme → X) ⁻¹' T,
    isClosed_preimage_val_coborder⟩

/-- The closed subset in `X \ ∂T` is the preimage of `T` under the open-subscheme inclusion. -/
@[stacks 0F2L]
theorem coe_locallyClosedSubsetAsClosed (T : Set X) (hT : IsLocallyClosed T) :
    (locallyClosedSubsetAsClosed T hT :
      Set (locallyClosedBoundaryComplementOpen T hT).toScheme) =
      ((Subtype.val : (locallyClosedBoundaryComplementOpen T hT).toScheme → X) ⁻¹' T) := sorry

/-- Remark 26.12.6: for a locally closed subset `T ⊆ X`, the phrase "reduced induced
scheme structure on `T`" means the reduced induced scheme structure on the closed subset `T` of
the open subscheme `X \ ∂T`, where `∂T = closure T \ T`. -/
@[stacks 0F2L]
abbrev locallyClosedReducedInducedSchemeStructure (T : Set X) (hT : IsLocallyClosed T) :
    (locallyClosedBoundaryComplementOpen T hT).toScheme.IdealSheafData :=
  IdealSheafData.vanishingIdeal (locallyClosedSubsetAsClosed T hT)

/-- The locally closed reduced induced scheme structure is the vanishing-ideal construction on
the closed subset `T ⊆ X \ ∂T`. -/
@[stacks 0F2L]
theorem locallyClosedReducedInducedSchemeStructure_eq_vanishingIdeal
    (T : Set X) (hT : IsLocallyClosed T) :
    locallyClosedReducedInducedSchemeStructure T hT =
      IdealSheafData.vanishingIdeal (locallyClosedSubsetAsClosed T hT) := sorry

/-- The support of the locally closed reduced induced scheme structure is the closed subset
`T ⊆ X \ ∂T`. -/
@[stacks 0F2L]
theorem support_locallyClosedReducedInducedSchemeStructure
    (T : Set X) (hT : IsLocallyClosed T) :
    (locallyClosedReducedInducedSchemeStructure T hT).support =
      locallyClosedSubsetAsClosed T hT := sorry

end

end AlgebraicGeometry.Scheme
