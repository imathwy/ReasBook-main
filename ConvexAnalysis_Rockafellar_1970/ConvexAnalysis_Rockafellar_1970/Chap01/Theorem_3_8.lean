import ConvexAnalysis_Rockafellar_1970.Chap01.Corollary_2_6_11
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_2_3_10
import ConvexAnalysis_Rockafellar_1970.Chap01.Text_3_6_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open scoped Pointwise
open scoped Rockafellar

/-
Source/core/bridge triage:
- `source-facing`: Theorem 3.8 states two set identities for convex cones containing the origin:
  the Minkowski sum equals the convex hull of the union, and the chapter's source-facing inverse
  addition notation `#[R]` equals the intersection.
- `core/canonical`: the owner layer is `PointedCone R E` over an ordered semiring layer;
  the canonical ambient operations are the lattice supremum/infimum on pointed cones and the
  generated-cone owner `PointedCone.hull R`.
- `bridge/view`: the theorem remains source-facing as a pair of set identities on the underlying
  sets of pointed cones; the first keeps the textbook Minkowski sum `((K₁ : Set E) + (K₂ : Set E))`
  explicit while routing it through the canonical supremum `K₁ ⊔ K₂`, the owner equality
  `Submodule.span_union`, and the earlier chapter theorem
  `PointedCone.hull_eq_convexHull_nonnegativeRay`; the second keeps the source notation
  `#[R]` on set carriers and internally identifies the right-hand side with the pointed-cone
  infimum.
- Primitive data vs derived API: the pointed cones are primitive; the two equalities are direct
  set-theoretic conclusions and should remain explicit set identities rather than a packaged
  wrapper.
- Domain-style sampling: the owner abstractions are `PointedCone R E` together with the
  supporting API `Submodule.coe_sup`, `Submodule.coe_inf`, `Submodule.span_union`,
  `PointedCone.hull_eq_convexHull_nonnegativeRay`, and `Set.mem_inverseAddition_primitive_iff`.
-/

namespace PointedCone

section OrderedSemiringHull

variable {R : Type v} [Semiring R] [PartialOrder R] [IsOrderedRing R]
variable {E : Type u} [AddCommMonoid E] [Module R E]

/-- Primitive owner form for Theorem 3.8 (1): the supremum of two pointed cones is the generated
cone of the union of their carriers. -/
theorem sup_eq_hull_union (K₁ K₂ : PointedCone R E) :
    (K₁ ⊔ K₂ : PointedCone R E) = cone[R] ((K₁ : Set E) ∪ K₂) := by
  ext x
  rw [hull, Submodule.span_union]
  simp

end OrderedSemiringHull

section OrderedSemifieldHull

variable {R : Type v} [Semifield R] [PartialOrder R] [IsOrderedRing R] [PosMulReflectLT R]
variable {E : Type u} [AddCommMonoid E] [Module R E]

/-- Source-facing form of Theorem 3.8 (1): the carrier of the supremum of two pointed cones is
the convex hull of the union of their carriers. -/
-- Proof sketch: first use the primitive owner identity `sup_eq_hull_union`, then apply
-- `hull_eq_convexHull_nonnegativeRay` and simplify because the union of pointed cones is already
-- closed under nonnegative scaling.
theorem sup_eq_convexHull_union (K₁ K₂ : PointedCone R E) :
    ((K₁ ⊔ K₂ : PointedCone R E) : Set E) = conv[R] ((K₁ : Set E) ∪ K₂) := by
  let U : Set E := (K₁ : Set E) ∪ K₂
  have hU :
      (Set.Ici (0 : R)) • U = U := by
    ext x
    constructor
    · rintro ⟨r, hr, y, hy, rfl⟩
      rcases hy with hy | hy
      · exact Or.inl <| K₁.smul_mem hr hy
      · exact Or.inr <| K₂.smul_mem hr hy
    · intro hx
      simpa using Set.smul_mem_smul (show (1 : R) ∈ Set.Ici (0 : R) by simp) hx
  calc
    ((K₁ ⊔ K₂ : PointedCone R E) : Set E) =
        (cone[R] ((K₁ : Set E) ∪ K₂) : Set E) := by
      exact congrArg (fun K : PointedCone R E => (K : Set E))
        (sup_eq_hull_union (K₁ := K₁) (K₂ := K₂))
    _ = (cone[R] U : Set E) := by
      rfl
    _ = convexHull R ((Set.Ici (0 : R)) • U) := by
      simpa [U] using hull_eq_convexHull_nonnegativeRay (R := R) (S := U) ⟨0, Or.inl K₁.zero_mem⟩
    _ = conv[R] U := by
      simp [hU]

/-- Theorem 3.8 (1): for pointed convex cones in a module over an ordered semifield, the
Minkowski sum is the convex hull of the union. -/
theorem add_eq_convexHull_union (K₁ K₂ : PointedCone R E) :
    ((K₁ : Set E) + (K₂ : Set E)) = conv[R] ((K₁ : Set E) ∪ K₂) := by
  calc
    ((K₁ : Set E) + (K₂ : Set E)) = ((K₁ ⊔ K₂ : PointedCone R E) : Set E) := by
      simpa using (Submodule.coe_sup K₁ K₂).symm
    _ = conv[R] ((K₁ : Set E) ∪ K₂) := sup_eq_convexHull_union K₁ K₂

end OrderedSemifieldHull

section OrderedDivisionSemiringInverseAddition

variable {R : Type v} [DivisionSemiring R] [PartialOrder R] [IsOrderedRing R] [PosMulReflectLT R]
variable {E : Type u} [AddCommMonoid E] [Module R E]

/-- Owner form of Theorem 3.8 (2): inverse addition of two pointed-cone carriers equals the
carrier of their infimum. -/
-- Proof sketch: unfold membership in inverse addition using the primitive two-coefficient owner
-- theorem `Set.mem_inverseAddition_primitive_iff`; one direction uses cone closure
-- under nonnegative
-- scaling, and the other uses the canonical symmetric witness `((2 : R)⁻¹, (2 : R)⁻¹)`.
theorem inverseAddition_eq_coe_inf (K₁ K₂ : PointedCone R E) :
    (K₁ #[R] K₂ : Set E) = ((K₁ ⊓ K₂ : PointedCone R E) : Set E) := by
  ext x
  rw [Set.mem_inverseAddition_primitive_iff]
  constructor
  · rintro ⟨t₁, t₂, ht₁, ht₂, -, hx⟩
    rcases hx with ⟨hx₁, hx₂⟩
    refine ⟨?_, ?_⟩
    · rcases Set.mem_smul_set.mp hx₁ with ⟨y, hy, rfl⟩
      exact K₁.smul_mem ht₁.le hy
    · rcases Set.mem_smul_set.mp hx₂ with ⟨y, hy, rfl⟩
      exact K₂.smul_mem ht₂.le hy
  · rintro ⟨hx₁, hx₂⟩
    have htwo_pos : (0 : R) < 2 := zero_lt_two
    have htwo_ne : (2 : R) ≠ 0 := ne_of_gt htwo_pos
    have hhalf_pos : (0 : R) < (2 : R)⁻¹ := inv_pos.mpr htwo_pos
    refine ⟨(2 : R)⁻¹, (2 : R)⁻¹, hhalf_pos, hhalf_pos, ?_, ?_⟩
    · calc
        ((2 : R)⁻¹ + (2 : R)⁻¹ : R) = (2 : R) * (2 : R)⁻¹ := by
          simp [two_mul]
        _ = 1 := by simp [htwo_ne]
    · constructor
      · refine Set.mem_smul_set.mpr ⟨(2 : R) • x, K₁.smul_mem (le_of_lt htwo_pos) hx₁, ?_⟩
        calc
          ((2 : R)⁻¹ : R) • ((2 : R) • x) = (((2 : R)⁻¹ * 2) : R) • x := by
            rw [smul_smul]
          _ = x := by simp [htwo_ne]
      · refine Set.mem_smul_set.mpr ⟨(2 : R) • x, K₂.smul_mem (le_of_lt htwo_pos) hx₂, ?_⟩
        calc
          ((2 : R)⁻¹ : R) • ((2 : R) • x) = (((2 : R)⁻¹ * 2) : R) • x := by
            rw [smul_smul]
          _ = x := by simp [htwo_ne]

/-- Theorem 3.8 (2): for pointed convex cones in a module over an ordered division semiring,
`K₁ #[R] K₂ = (K₁ : Set E) ∩ (K₂ : Set E)`. -/
-- Proof sketch: combine the owner-level identity `inverseAddition_eq_coe_inf` with the standard
-- carrier description of infimum as set intersection.
theorem inverseAddition_eq_inter (K₁ K₂ : PointedCone R E) :
    (K₁ #[R] K₂ : Set E) = (K₁ ∩ K₂ : Set E) := by
  calc
    (K₁ #[R] K₂ : Set E) = ((K₁ ⊓ K₂ : PointedCone R E) : Set E) := by
      exact inverseAddition_eq_coe_inf K₁ K₂
    _ = (K₁ ∩ K₂ : Set E) := by
      exact (Submodule.coe_inf :
        ((K₁ ⊓ K₂ : PointedCone R E) : Set E) = (K₁ : Set E) ∩ (K₂ : Set E))

end OrderedDivisionSemiringInverseAddition

end PointedCone
