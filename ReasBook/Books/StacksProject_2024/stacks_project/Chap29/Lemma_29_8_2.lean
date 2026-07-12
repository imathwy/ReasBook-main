import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.Topology.Sober

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry

-- Semantic recall / local analogue check:
-- - `IsDominant f` together with `isDominant_iff` is the canonical dominant-morphism owner.
-- - `genericPoints.ofComponent` / `genericPoints.isGenericPoint_ofComponent` provide the canonical
--   generic point of an irreducible component of the sober underlying space of a scheme.
-- - `exists_mem_irreducibleComponents_subset_of_isIrreducible` is the topological owner used to
--   place an arbitrary point of the target inside an irreducible component.

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- If every generic point witness on every irreducible component of `S` lies in the image of `f`,
then in particular the canonical chosen generic point of each irreducible component lies in the
image of `f`. -/
theorem forall_genericPointOfComponent_mem_range_of_forall_genericPoint_mem_range
    (hgeneric :
      ∀ Z : irreducibleComponents S, ∀ ⦃s : S⦄,
        IsGenericPoint s (Z : Set S) → s ∈ Set.range f.base) :
    ∀ Z : irreducibleComponents S, (genericPoints.ofComponent Z : S) ∈ Set.range f.base :=
  fun Z ↦ hgeneric Z (genericPoints.isGenericPoint_ofComponent Z)

/-- If the canonical generic point of an irreducible component `Z` lies in the image of `f`, then
every point of `Z` lies in the closure of the image of `f`. -/
theorem mem_closure_range_of_mem_irreducibleComponent
    (hgeneric :
      ∀ Z : irreducibleComponents S, (genericPoints.ofComponent Z : S) ∈ Set.range f.base)
    (Z : irreducibleComponents S) {s : S} (hs : s ∈ (Z : Set S)) :
    s ∈ closure (Set.range f.base) := by
  have hη : (genericPoints.ofComponent Z : S) ∈ closure (Set.range f.base) :=
    Set.subset_closure (hgeneric Z)
  exact ((genericPoints.isGenericPoint_ofComponent Z).specializes hs).mem_closed
    isClosed_closure hη

/-- If the canonical generic point of every irreducible component of `S` lies in the image of
`f`, then `f` is dominant. -/
theorem isDominant_of_forall_genericPointOfComponent_mem_range
    (hgeneric :
      ∀ Z : irreducibleComponents S, (genericPoints.ofComponent Z : S) ∈ Set.range f.base) :
    IsDominant f := by
  rw [isDominant_iff, denseRange_iff_closure_range, ← Set.univ_subset_iff]
  intro s hs
  rcases exists_mem_irreducibleComponents_subset_of_isIrreducible ({s} : Set S)
      (by simpa using isIrreducible_singleton s) with ⟨Z, hZ, hsZ⟩
  let Z' : irreducibleComponents S := ⟨Z, hZ⟩
  exact mem_closure_range_of_mem_irreducibleComponent f hgeneric Z' (hsZ hs)

/-- Lemma 29.8.2: if every generic point of every irreducible component of the target scheme lies
in the image of `f`, then `f` is dominant. -/
@[stacks 01RK]
theorem isDominant_of_genericPoint_mem_range_of_irreducibleComponents
    (hgeneric :
      ∀ Z : irreducibleComponents S, ∀ ⦃s : S⦄,
        IsGenericPoint s (Z : Set S) → s ∈ Set.range f.base) :
    IsDominant f :=
  isDominant_of_forall_genericPointOfComponent_mem_range f
    (forall_genericPointOfComponent_mem_range_of_forall_genericPoint_mem_range f hgeneric)

end AlgebraicGeometry
