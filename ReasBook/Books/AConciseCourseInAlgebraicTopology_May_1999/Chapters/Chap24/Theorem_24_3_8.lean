import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap23.Definition_23_5_3
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap24.Definition_24_1_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap24.Definition_24_3_7
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap24.Proposition_24_1_8

open scoped ComplexKTheory

noncomputable section

universe u

section

variable {X : Type u} [TopologicalSpace X]
variable {n : ℕ} {E : ComplexPlaneBundle n X}

section

variable (E : ComplexPlaneBundle n X) [TopologicalSpace (ThomSpace n E.fiber)]

/-- The reduced `K`-theory owner for the Thom space of `E`, written canonically as the kernel of
the dimension map on `ThomSpace n E.fiber`. Since `complexKTheoryDimensionAt` is independent of
the chosen basepoint and `thomInfinitySubset_eq_singleton` identifies all fiberwise points at
infinity, this is the choice-free reduced `K`-theory owner for `ThomSpace n E.fiber`. -/
abbrev complexBundleThomReducedKTheory :=
  AddMonoidHom.ker (complexKTheoryDimension (ThomSpace n E.fiber))

/-- The canonical Thom-space reduced `K`-theory owner agrees with the source-facing based model
obtained from any chosen fiberwise point at infinity. -/
theorem complexBundleThomReducedKTheory_eq_reducedComplexKTheory (b_inf : X) :
    complexBundleThomReducedKTheory E =
      K̃(ThomSpace n E.fiber,
        thomSpaceMk n E.fiber b_inf (OnePoint.infty : OnePoint (E.fiber b_inf))) := by
  simp [complexBundleThomReducedKTheory, reducedComplexKTheory, complexKTheoryDimensionAt_eq]

/-- A Thom class and the canonical pullback map send every class on `X` to reduced `K`-theory of
`ThomSpace n E.fiber` after multiplication by `lambda_E`. -/
theorem complexBundleThomMap_mem_reducedKTheory
    (projMap : TopCat.of (ThomSpace n E.fiber) ⟶ TopCat.of X)
    (projStar : K(X) →+* K(ThomSpace n E.fiber))
    (lambda_E : K(ThomSpace n E.fiber))
    (hThomClass : IsComplexBundleThomClass E projMap.hom lambda_E)
    (hProjStar : IsComplexKTheoryPresentationPullback projMap projStar)
    (ξ : K(X)) :
    projStar ξ * lambda_E ∈ AddMonoidHom.ker (complexKTheoryDimension (ThomSpace n E.fiber)) := by
  sorry

/-- `complexBundleThomMap` is the source-facing multiplication map
`K(X) → K̃(T(E))` obtained by multiplying the chosen pullback class `projStar ξ` by the Thom class
`lambda_E`, and then regarding the product in the canonical reduced `K`-theory of the Thom
space. -/
def complexBundleThomMap
    (projMap : TopCat.of (ThomSpace n E.fiber) ⟶ TopCat.of X)
    (projStar : K(X) →+* K(ThomSpace n E.fiber))
    (lambda_E : K(ThomSpace n E.fiber))
    (hThomClass : IsComplexBundleThomClass E projMap.hom lambda_E)
    (hProjStar : IsComplexKTheoryPresentationPullback projMap projStar) :
    K(X) →+ complexBundleThomReducedKTheory E where
  toFun ξ :=
    ⟨projStar ξ * lambda_E,
      complexBundleThomMap_mem_reducedKTheory
        E projMap projStar lambda_E hThomClass hProjStar ξ⟩
  map_zero' := sorry
  map_add' := sorry

/-- On an input `ξ ∈ K(X)`, `complexBundleThomMap` is the product of the pullback class
`projStar ξ` with the Thom class `lambda_E`, viewed in the canonical reduced `K`-theory of
`ThomSpace n E`. -/
theorem complexBundleThomMap_apply
    (projMap : TopCat.of (ThomSpace n E.fiber) ⟶ TopCat.of X)
    (projStar : K(X) →+* K(ThomSpace n E.fiber))
    (lambda_E : K(ThomSpace n E.fiber))
    (hThomClass : IsComplexBundleThomClass E projMap.hom lambda_E)
    (hProjStar : IsComplexKTheoryPresentationPullback projMap projStar)
    (ξ : K(X)) :
    (complexBundleThomMap E projMap projStar lambda_E hThomClass hProjStar ξ :
        K(ThomSpace n E.fiber)) =
      projStar ξ * lambda_E := rfl

section

variable [CompactSpace X]
variable [CompactSpace (ThomSpace n E.fiber)]

/-- Companion to Theorem 24.3.8: multiplication by `lambda_E`, for any Thom class
`hThomClass : IsComplexBundleThomClass E projMap.hom lambda_E`, makes the explicit Thom
multiplication map `complexBundleThomMap E projMap projStar lambda_E hThomClass hProjStar`
bijective. -/
theorem complexBundleThomMap_bijective
    (projMap : TopCat.of (ThomSpace n E.fiber) ⟶ TopCat.of X)
    (projStar : K(X) →+* K(ThomSpace n E.fiber))
    (lambda_E : K(ThomSpace n E.fiber))
    (hThomClass : IsComplexBundleThomClass E projMap.hom lambda_E)
    (hProjStar : IsComplexKTheoryPresentationPullback projMap projStar) :
    Function.Bijective
      (complexBundleThomMap E projMap projStar lambda_E hThomClass hProjStar) := sorry

/-- Theorem 24.3.8. K-theory Thom isomorphism: multiplication by `lambda_E`, for any Thom class
`hThomClass : IsComplexBundleThomClass E projMap.hom lambda_E`, yields an additive equivalence
`K(X) ≃+ K̃(T(E))` whose underlying homomorphism is the explicit Thom multiplication map. -/
theorem complexBundleThom_isomorphism
    (projMap : TopCat.of (ThomSpace n E.fiber) ⟶ TopCat.of X)
    (projStar : K(X) →+* K(ThomSpace n E.fiber))
    (lambda_E : K(ThomSpace n E.fiber))
    (hThomClass : IsComplexBundleThomClass E projMap.hom lambda_E)
    (hProjStar : IsComplexKTheoryPresentationPullback projMap projStar) :
    ∃ thomEquiv : K(X) ≃+ complexBundleThomReducedKTheory E,
      thomEquiv.toAddMonoidHom =
        complexBundleThomMap E projMap projStar lambda_E hThomClass hProjStar := by
  sorry

end

end

end
