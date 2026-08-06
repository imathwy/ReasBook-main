import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap24.Proposition_24_5_3
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap24.Theorem_24_3_8

open scoped ComplexKTheory ComplexKTheoryAdams

noncomputable section

universe u

section

variable {X : Type u} [TopologicalSpace X]
variable {n : ℕ}
variable (E : ComplexPlaneBundle n X) [TopologicalSpace (ThomSpace n E.fiber)]

/-- The canonical reduced `K`-theory owner of `ThomSpace n E.fiber` agrees additively with the
chosen based reduced model obtained from the fiberwise point at infinity over `b_inf`. -/
def complexBundleThomReducedKTheoryBasedEquiv
    (b_inf : X) :
    complexBundleThomReducedKTheory E ≃+
      K̃(ThomSpace n E.fiber,
        thomSpaceMk n E.fiber b_inf (OnePoint.infty : OnePoint (E.fiber b_inf))) where
  toEquiv :=
    Equiv.setCongr
      (congrArg
        (fun S : AddSubgroup (K(ThomSpace n E.fiber)) ↦ (S : Set (K(ThomSpace n E.fiber))))
        (complexBundleThomReducedKTheory_eq_reducedComplexKTheory E b_inf))
  map_add' := by
    intro ξ η
    rfl

/-- Coercing `complexBundleThomReducedKTheoryBasedEquiv E b_inf ξ` back to `K(T(E))` recovers
the original reduced class `ξ`. -/
@[simp] theorem complexBundleThomReducedKTheoryBasedEquiv_coe_apply
    (b_inf : X) (ξ : complexBundleThomReducedKTheory E) :
    (complexBundleThomReducedKTheoryBasedEquiv E b_inf ξ : K(ThomSpace n E.fiber)) = ξ := rfl

/-- Coercing the inverse bridge from the chosen based reduced model back to `K(T(E))` also
recovers the original class. -/
@[simp] theorem complexBundleThomReducedKTheoryBasedEquiv_symm_coe_apply
    (b_inf : X)
    (ξ : K̃(ThomSpace n E.fiber,
        thomSpaceMk n E.fiber b_inf (OnePoint.infty : OnePoint (E.fiber b_inf)))) :
    ((complexBundleThomReducedKTheoryBasedEquiv E b_inf).symm ξ : K(ThomSpace n E.fiber)) = ξ := rfl

section

variable {ψ : ComplexKTheoryAdamsFamily}

namespace IsComplexKTheoryAdams

section

variable (hψ : IsComplexKTheoryAdams ψ)
variable [CompactSpace (ThomSpace n E.fiber)]

/-- Adams operations preserve the canonical Thom-space reduced `K`-theory owner, viewed directly
as the kernel of `complexKTheoryDimension (ThomSpace n E.fiber)`. -/
theorem map_mem_complexBundleThomReducedKTheory
    (hψ : IsComplexKTheoryAdams ψ)
    (k : NonzeroInt)
    (ξ : complexBundleThomReducedKTheory E) :
    (ψ ^[k]) ξ ∈ complexBundleThomReducedKTheory E := by
  sorry

/-- The ambient Adams operation `ψ^[k]` canonically restricts to a self-map of the Thom reduced
`K`-theory owner `complexBundleThomReducedKTheory E`. -/
def complexBundleThomReducedOp
    (hψ : IsComplexKTheoryAdams ψ)
    (k : NonzeroInt) :
    complexBundleThomReducedKTheory E → complexBundleThomReducedKTheory E :=
  fun ξ ↦ ⟨(ψ ^[k]) ξ, hψ.map_mem_complexBundleThomReducedKTheory E k ξ⟩

/-- Applying `complexBundleThomReducedOp` is just the ambient Adams operation together with the
fact that the image remains in the canonical Thom reduced `K`-theory owner. -/
@[simp] theorem complexBundleThomReducedOp_apply
    (hψ : IsComplexKTheoryAdams ψ)
    (k : NonzeroInt)
    (ξ : complexBundleThomReducedKTheory E) :
    complexBundleThomReducedOp E hψ k ξ =
      ⟨(ψ ^[k]) ξ, hψ.map_mem_complexBundleThomReducedKTheory E k ξ⟩ := rfl

/-- For any chosen fiberwise point at infinity, the canonical Thom reduced Adams operator agrees
with transport of the based reduced Adams endomorphism across
`complexBundleThomReducedKTheoryBasedEquiv`. -/
theorem complexBundleThomReducedOp_eq_basedReducedOp
    (hψ : IsComplexKTheoryAdams ψ)
    (b_inf : X)
    (k : NonzeroInt)
    (ξ : complexBundleThomReducedKTheory E) :
    complexBundleThomReducedOp E hψ k ξ =
      (complexBundleThomReducedKTheoryBasedEquiv E b_inf).symm
        (hψ.reducedOp (ThomSpace n E.fiber)
          (thomSpaceMk n E.fiber b_inf (OnePoint.infty : OnePoint (E.fiber b_inf))) k
          (complexBundleThomReducedKTheoryBasedEquiv E b_inf ξ)) := by
  ext
  simp [complexBundleThomReducedOp]

/-- Coercing `complexBundleThomReducedOp` back to `K(T(E))` recovers the ambient Adams operation on
the underlying Thom-space `K`-theory class. -/
@[simp] theorem complexBundleThomReducedOp_coe_apply
    (hψ : IsComplexKTheoryAdams ψ)
    (k : NonzeroInt)
    (ξ : complexBundleThomReducedKTheory E) :
    (complexBundleThomReducedOp E hψ k ξ : K(ThomSpace n E.fiber)) =
      (ψ ^[k]) ξ := rfl

end

end IsComplexKTheoryAdams

variable (hψ : IsComplexKTheoryAdams ψ)
variable [CompactSpace (ThomSpace n E.fiber)]

/-- Remark 24.5.5. Conjugating the Adams operation `ψ^k` through the Thom isomorphism defines the
associated `K`-theoretic characteristic class on `X`; here the reduced Thom-space Adams
operator is the canonical self-map `hψ.complexBundleThomReducedOp E k` on the
canonical Thom-space reduced `K`-theory owner, evaluated at `1 ∈ K(X)`.
-/
def complexBundleThomAdamsCharacteristicClass
    (hψ : IsComplexKTheoryAdams ψ)
    (thomEquiv : K(X) ≃+ complexBundleThomReducedKTheory E)
    (k : NonzeroInt) :
    K(X) :=
  thomEquiv.symm (IsComplexKTheoryAdams.complexBundleThomReducedOp E hψ k (thomEquiv 1))

/-- The `K`-theoretic characteristic class from Remark 24.5.5 is the transported reduced
Thom-space operator evaluated at `1 ∈ K(X)`. -/
@[simp] theorem complexBundleThomAdamsCharacteristicClass_def
    (hψ : IsComplexKTheoryAdams ψ)
    (thomEquiv : K(X) ≃+ complexBundleThomReducedKTheory E)
    (k : NonzeroInt) :
    complexBundleThomAdamsCharacteristicClass E hψ thomEquiv k =
      thomEquiv.symm (IsComplexKTheoryAdams.complexBundleThomReducedOp E hψ k (thomEquiv 1)) := rfl

end

end
