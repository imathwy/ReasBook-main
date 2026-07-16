import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap03.Definition_3_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

open Bornology

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Theorem 3.1 is a `bridge/view` item in the chapter subdifferential API. The owner declaration
is `subdifferential : Set (Module.Dual ℝ E)` from Definition 3.2, while the closedness statement
in this theorem lives on the topologized continuous-dual view. Owner-level convexity already lives
in `convex_subdifferential`, so the only primitive
data here is the canonical preimage of `subdifferential` along
`StrongDual ℝ E → Module.Dual ℝ E`; membership lemmas are derived API. -/
recall subdifferential
recall convex_subdifferential

/-- The continuous-dual view of `subdifferential f x`, obtained by restricting the chapter's
source-facing subdifferential along the canonical coercion `StrongDual ℝ E → Module.Dual ℝ E`. -/
abbrev strongDualSubdifferential (f : E → EReal) (x : E) : Set (StrongDual ℝ E) :=
  ((↑) : StrongDual ℝ E → Module.Dual ℝ E) ⁻¹' ∂ f(x)

notation "∂ₛ" f "(" x ")" => strongDualSubdifferential f x

/-- Membership in `strongDualSubdifferential f x` means that the underlying algebraic-dual
functional belongs to the owner subdifferential `subdifferential f x`. -/
@[simp] theorem mem_strongDualSubdifferential
    {f : E → EReal} {x : E} {g : StrongDual ℝ E} :
    g ∈ ∂ₛ f(x) ↔ (g : Module.Dual ℝ E) ∈ ∂ f(x) :=
  Iff.rfl

-- Proof sketch: write `∂ₛ f(x)` as the intersection, over `y : E`, of the closed
-- half-spaces cut out by the affine functionals `g ↦ (g (y - x) : EReal)`, together
-- with the constant condition `x ∈ effective_domain f`; arbitrary intersections of closed sets are
-- closed.
/-- Theorem 3.1 (1): for an extended-real-valued function, the continuous-dual subdifferential
`∂ₛ f(x)` is a closed subset of the dual space. -/
theorem isClosed_subdifferential (f : E → EReal) (x : E) :
    IsClosed (∂ₛ f(x)) := sorry

/-- Theorem 3.1 (2): for an extended-real-valued function, the continuous-dual subdifferential
`∂ₛ f(x)` is a convex subset of the dual space. -/
theorem convex_strongDualSubdifferential (f : E → EReal) (x : E) :
    Convex ℝ (∂ₛ f(x)) := sorry

end

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- In finite dimensions, every algebraic functional is continuous, so the strong-dual view of
`subdifferential f x` is exactly its image under the canonical equivalence
`LinearMap.toContinuousLinearMap`. -/
theorem strongDualSubdifferential_eq_image_subdifferential
    (f : E → EReal) (x : E) :
    ∂ₛ f(x) =
      (LinearMap.toContinuousLinearMap : (Module.Dual ℝ E) ≃ₗ[ℝ] StrongDual ℝ E) ''
        ∂ f(x) := by
  let e : (Module.Dual ℝ E) ≃ₗ[ℝ] StrongDual ℝ E := LinearMap.toContinuousLinearMap
  ext g
  constructor
  · intro hg
    exact ⟨e.symm g, hg, e.apply_symm_apply g⟩
  · rintro ⟨g', hg', rfl⟩
    simpa [e] using hg'

end

section

open InnerProductSpace (toDualMap)

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The Euclidean/vector-side view of `subdifferential f x`, obtained by transporting the Chapter
3 strong-dual bridge `strongDualSubdifferential f x` back to vectors through the Riesz map. This
is a `bridge/view` API; `subdifferential` remains the owner abstraction. -/
abbrev euclideanSubdifferential (f : E → EReal) (x : E) : Set E :=
  (toDualMap ℝ E) ⁻¹' strongDualSubdifferential f x

/-- Membership in `euclideanSubdifferential f x` is definitionally membership of the corresponding
Riesz functional in `strongDualSubdifferential f x`. -/
@[simp] theorem mem_euclideanSubdifferential_iff
    {f : E → EReal} {x z : E} :
    z ∈ euclideanSubdifferential f x ↔
      toDualMap ℝ E z ∈ strongDualSubdifferential f x :=
  Iff.rfl

end
