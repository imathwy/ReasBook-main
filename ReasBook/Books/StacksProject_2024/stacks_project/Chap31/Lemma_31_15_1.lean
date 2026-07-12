import Mathlib
import StacksProject_2024.Chap17.SectionNonvanishingLocus
import StacksProject_2024.Chap31.Definition_31_2_1
import StacksProject_2024.Chap31.Definition_31_14_6

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} [IsLocallyNoetherian X]
variable [MonoidalCategory (RingedSpace.Modules X.toRingedSpace)]

local notation "ModX" => RingedSpace.Modules X.toRingedSpace
local notation "IsInvertibleX" =>
  (fun ℒ : ModX ↦ Functor.IsEquivalence (tensorRight ℒ))

-- The source-facing nonvanishing condition already has the Chapter 17 owner
-- `RingedSpace.sectionNonvanishingLocus`; this lemma bridges it to the Chapter 31 owners
-- `X.associatedPoints` and `LocallyRingedSpace.IsRegularSection`.

/-- Lemma 31.15.1: let `X` be a locally Noetherian scheme, let `\mathcal L` be an invertible
`\mathcal O_X`-module, and let `s ∈ Γ(X, \mathcal L)`. Then `s` is a regular section if and only
if `s` does not vanish at any associated point of `X`, equivalently if every associated point lies
in the section nonvanishing locus of `s`. -/
@[stacks 0AYL]
theorem isRegularSection_iff_associatedPoints_subset_sectionNonvanishingLocus
    (ℒ : ModX) [IsInvertibleX ℒ] (s : ℒ.sections) :
    LocallyRingedSpace.IsRegularSection ℒ s ↔
      X.associatedPoints ⊆ RingedSpace.sectionNonvanishingLocus X.toRingedSpace ℒ s :=
  sorry

/-- Pointwise form of Lemma 31.15.1: a regular section of an invertible sheaf is nonvanishing at
every associated point, and conversely it suffices to check nonvanishing pointwise on associated
points. -/
theorem isRegularSection_iff_forall_mem_associatedPoints_mem_sectionNonvanishingLocus
    (ℒ : ModX) [IsInvertibleX ℒ] (s : ℒ.sections) :
    LocallyRingedSpace.IsRegularSection ℒ s ↔
      ∀ x : X, x ∈ X.associatedPoints →
        x ∈ RingedSpace.sectionNonvanishingLocus X.toRingedSpace ℒ s := by
  simpa [Set.subset_def] using
    isRegularSection_iff_associatedPoints_subset_sectionNonvanishingLocus ℒ s

end AlgebraicGeometry.Scheme
