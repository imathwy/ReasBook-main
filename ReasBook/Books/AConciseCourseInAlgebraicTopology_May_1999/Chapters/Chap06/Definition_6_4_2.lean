import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap04.Definition_4_2_6
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap06.Definition_6_4_1

universe u

variable {X : Type u} [TopologicalSpace X]

-- Semantic recall via `lean_leansearch`: no mathlib owner for DR-pairs was found in the current
-- environment, while the local bundled owners `NDRPair` and `DeformationRetract` already encode
-- the two sides of the textbook equivalence.

/-- Data witnessing that `A ⊆ X` is a DR-pair. -/
structure DRPair (A : Set X) extends NDRPair A where
  /-- The control map satisfies `control x < 1` at every point of `X`. -/
  control_lt_one : ∀ x, control x < 1

/-- Definition 6.4.2. A subspace `A ⊆ X` is a DR-pair if it admits a witness `DRPair A`;
its endpoint map is therefore a deformation retract of `A`. -/
def IsDRPair (A : Set X) : Prop :=
  Nonempty (DRPair A)

namespace DRPair

/-- A DR-pair witness can be evaluated as its endpoint map `X → X`. -/
instance {A : Set X} : CoeFun (DRPair A) (fun _ ↦ X → X) where
  coe h := h.retract

/-- Evaluating a DR-pair witness agrees with evaluating its endpoint map. -/
@[simp]
theorem coe_apply {A : Set X} (h : DRPair A) (x : X) : h x = h.retract x := rfl

/-- A DR-pair witness is in particular an NDR-pair witness. -/
theorem toIsNDRPair {A : Set X} (h : DRPair A) : IsNDRPair A :=
  h.toNDRPair.toIsNDRPair

/-- The endpoint map of a DR-pair witness lands in `A` at every point of `X`. -/
theorem retract_mem {A : Set X} (h : DRPair A) (x : X) : h.retract x ∈ A :=
  h.endpoint_mem x (h.control_lt_one x)

/-- The endpoint map of a DR-pair witness has image contained in `A`. -/
theorem range_subset {A : Set X} (h : DRPair A) : Set.range h.retract ⊆ A := by
  rintro y ⟨x, rfl⟩
  exact h.retract_mem x

/-- A DR-pair witness determines a deformation retract witness. -/
def toDeformationRetract {A : Set X} (h : DRPair A) : DeformationRetract A :=
  DeformationRetract.ofMem h.retract h.homotopy h.retract_mem

/-- A DR-pair witness determines a deformation retract. -/
theorem toIsDeformationRetract {A : Set X} (h : DRPair A) : IsDeformationRetract A :=
  h.toDeformationRetract.toIsDeformationRetract

/-- A DR-pair witness determines the corresponding source-level property. -/
theorem toIsDRPair {A : Set X} (h : DRPair A) : IsDRPair A :=
  ⟨h⟩

end DRPair

/-- The existential formulation is equivalent to the existence of a bundled DR-pair witness. -/
theorem isDRPair_iff_nonempty_drPair {A : Set X} :
    IsDRPair A ↔ Nonempty (DRPair A) :=
  Iff.rfl

/-- A DR-pair is in particular an NDR-pair. -/
theorem isNDRPair_of_isDRPair {A : Set X} (hA : IsDRPair A) : IsNDRPair A := by
  rcases hA with ⟨hA⟩
  exact hA.toIsNDRPair

/-- A DR-pair determines a deformation retract. -/
theorem isDeformationRetract_of_isDRPair {A : Set X} (hA : IsDRPair A) :
    IsDeformationRetract A := by
  rcases hA with ⟨h⟩
  exact h.toIsDeformationRetract
