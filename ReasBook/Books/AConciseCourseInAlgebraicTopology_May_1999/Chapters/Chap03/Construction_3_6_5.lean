import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap03.Construction_3_6_3
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap03.Lemma_3_4_8

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open CategoryTheory
open CategoryTheory.Groupoid (homMulAction_smul)
open QuotientGroup

variable {B : Type u} [Groupoid.{v} B]
variable [IsConnected B]

section

variable (b : B) {H K : O(End b)} (α : H ⟶ K)

/- Construction 3.6.5: a morphism `α : H ⟶ K` in the orbit category induces the canonical
morphism `((orbitCategoryToConnectedCovering b).map α)` between the associated connected
coverings over `B`, with the commutative triangle over `B` carried by the underlying
`GroupoidFunctorOver.Hom` data. -/
#check ((orbitCategoryToConnectedCovering b).map α)

end

/-- The induced covering morphism sends the source-facing object `fH` to the canonical class whose
quotient coordinate is `α(eH)`. -/
@[simp] theorem orbitCategoryToConnectedCovering_map_objOfHom (b : B)
    {H K : O(End b)} (α : H ⟶ K) {x : B} (f : b ⟶ x) :
    (((orbitCategoryToConnectedCovering b).map α).hom.left).obj
      (orbitSubgroupCoveringObjOfHom b (H : Subgroup (End b)) f) =
        (⟨x, Quotient.mk'' (f, (orbitCategory.homEvalOne H K α : End b ⧸ K))⟩ :
          (associatedAction b (End b ⧸ K)).Elements) := by
  rfl

/-- If `α (eH) = γK`, then the canonical covering morphism induced by `α : H ⟶ K` sends the
source-facing object `fH` of `E(G/H)` to the source-facing object `(γ ≫ f)K` of `E(G/K)`. -/
-- Proof sketch: on category-of-elements representatives the induced functor fixes the arrow `f`
-- and applies `α` to the quotient coordinate, so `fH` goes to the class of `(f, γK)`. That class
-- is exactly the source-facing object `(γ ≫ f)K`, since the diagonal `π(B,b)`-action identifies
-- `(γ ≫ f, K)` with `(f, γK)`.
theorem orbitCategoryToConnectedCovering_map_objOfHom_of_apply_one (b : B)
    {H K : O(End b)} (α : H ⟶ K)
    {γ : End b}
    (hα : (orbitCategory.homEvalOne H K α : End b ⧸ K) = (γ : End b ⧸ K))
    {x : B} (f : b ⟶ x) :
    (((orbitCategoryToConnectedCovering b).map α).hom.left).obj
      (orbitSubgroupCoveringObjOfHom b (H : Subgroup (End b)) f) =
        orbitSubgroupCoveringObjOfHom b (K : Subgroup (End b)) (γ ≫ f) := by
  rw [orbitCategoryToConnectedCovering_map_objOfHom]
  rw [hα]
  congr 1
  apply Quotient.sound
  change
    MulAction.orbitRel (End b) ((b ⟶ x) × (End b ⧸ K))
      (f, (γ : End b ⧸ K)) (γ ≫ f, ((1 : End b) : End b ⧸ K))
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_symm]
  refine ⟨γ⁻¹, ?_⟩
  change ((γ⁻¹ : End b) • f, (γ⁻¹ : End b) • (γ : End b ⧸ K)) =
      (γ ≫ f, ((1 : End b) : End b ⧸ K))
  ext
  · change (γ⁻¹ : End b) • f = γ ≫ f
    rw [homMulAction_smul]
    have hγ : CategoryTheory.inv (γ⁻¹) = γ := by
      simp
    exact congrArg (fun η : End b ↦ η ≫ f) hγ
  · change (((γ⁻¹ : End b) * γ : End b) : End b ⧸ K) = ((1 : End b) : End b ⧸ K)
    simp
