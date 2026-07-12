import Mathlib
import StacksProject_2024.Chap17.Definition_17_5_1
import StacksProject_2024.Chap17.Definition_17_12_1
import StacksProject_2024.Chap31.Definition_31_4_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open Set TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (ℱ : X.Modules)

-- Semantic recall: `lean_leansearch` did not surface a dedicated mathlib owner for this Stacks
-- lemma; the local Chapter 31 owner for the embedded-point clause is
-- `Scheme.Modules.embeddedAssociatedPoints`, while the ambient interfaces stay the canonical
-- `moduleSupport`, `Subobject`, `cokernel`, and restriction APIs.

/-- A coherent subsheaf of `ℱ` whose support is nowhere dense inside `Supp(ℱ)`, expressed on the
support subtype of `ℱ`. -/
def isCoherentSubsheafWithNowhereDenseSupport (K : Subobject ℱ) : Prop :=
  ((K : X.Modules)).IsCoherent ∧
    IsNowhereDense
      (Subtype.val ⁻¹' moduleSupport ((K : X.Modules)) : Set (moduleSupport ℱ))

/-- Expansion of `isCoherentSubsheafWithNowhereDenseSupport`. -/
theorem isCoherentSubsheafWithNowhereDenseSupport_iff (K : Subobject ℱ) :
    ℱ.isCoherentSubsheafWithNowhereDenseSupport K ↔
      ((K : X.Modules)).IsCoherent ∧
        IsNowhereDense
          (Subtype.val ⁻¹' moduleSupport ((K : X.Modules)) : Set (moduleSupport ℱ)) :=
  Iff.rfl

theorem isCoherentSubsheafWithNowhereDenseSupport.isCoherent {K : Subobject ℱ}
    (hK : ℱ.isCoherentSubsheafWithNowhereDenseSupport K) :
    ((K : X.Modules)).IsCoherent :=
  hK.1

theorem isCoherentSubsheafWithNowhereDenseSupport.isNowhereDense {K : Subobject ℱ}
    (hK : ℱ.isCoherentSubsheafWithNowhereDenseSupport K) :
    IsNowhereDense
      (Subtype.val ⁻¹' moduleSupport ((K : X.Modules)) : Set (moduleSupport ℱ)) :=
  hK.2

variable [IsLocallyNoetherian X] [ℱ.IsCoherent]

/-- Lemma 31.4.6 (1): a coherent sheaf on a locally Noetherian scheme has a maximal coherent
subsheaf whose support is nowhere dense inside the support of the ambient sheaf. -/
theorem exists_maximalCoherentSubsheafWithNowhereDenseSupport :
    ∃ K : Subobject ℱ,
      Maximal (ℱ.isCoherentSubsheafWithNowhereDenseSupport) K := sorry

/-- Lemma 31.4.6 (2): if `K` is maximal among coherent subsheaves with support nowhere dense in
`Supp(ℱ)`, then the quotient `ℱ / K` has the same support as `ℱ`. -/
theorem support_cokernel_eq_of_maximalCoherentSubsheafWithNowhereDenseSupport
    (K : Subobject ℱ)
    (hK : Maximal (ℱ.isCoherentSubsheafWithNowhereDenseSupport) K) :
    moduleSupport (cokernel K.arrow) = moduleSupport ℱ := sorry

/-- Lemma 31.4.6 (3): if `K` is maximal among coherent subsheaves with support nowhere dense in
`Supp(ℱ)`, then the quotient `ℱ / K` has no embedded associated points. -/
theorem no_embeddedAssociatedPoints_of_cokernel_of_maximalCoherentSubsheafWithNowhereDenseSupport
    (K : Subobject ℱ)
    (hK : Maximal (ℱ.isCoherentSubsheafWithNowhereDenseSupport) K) :
    embeddedAssociatedPoints (cokernel K.arrow) = (∅ : Set X) := sorry

/-- Lemma 31.4.6 (4): if `K` is maximal among coherent subsheaves with support nowhere dense in
`Supp(ℱ)`, then on some open subset meeting `Supp(ℱ)` densely the quotient `ℱ / K` restricts to
`ℱ`. -/
theorem exists_denseOpen_restrictIso_cokernel_of_maximalCoherentSubsheafWithNowhereDenseSupport
    (K : Subobject ℱ)
    (hK : Maximal (ℱ.isCoherentSubsheafWithNowhereDenseSupport) K) :
    ∃ (U : X.Opens), ∃ e : (cokernel K.arrow).restrict U.ι ≅ ℱ.restrict U.ι,
      moduleSupport ℱ ⊆ closure ((U : Set X) ∩ moduleSupport ℱ) := sorry

end AlgebraicGeometry.Scheme.Modules
