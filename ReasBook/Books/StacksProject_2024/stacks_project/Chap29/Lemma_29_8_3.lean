import StacksProject_2024.Chap29.Lemma_29_8_2
import StacksProject_2024.Chap29.Lemma_29_8_6

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open TopologicalSpace

universe u

namespace AlgebraicGeometry

-- Semantic recall / analogue check:
-- - `lean_leansearch` surfaced the canonical scheme-side owner `AlgebraicGeometry.IsDominant`
--   together with the dense-range bridge `AlgebraicGeometry.isDominant_iff`.
-- - For the generic points of irreducible components, mathlib's sober-space API already provides
--   the canonical owner `genericPoints S`, with `genericPoints.ofComponent` and
--   `genericPoints.equiv` as the source-facing bridge to `irreducibleComponents S`.
-- - Nearby Chapter 29 files phrase quasi-compactness as a typeclass hypothesis `[QuasiCompact f]`
--   and dominant morphisms by the canonical owner `AlgebraicGeometry.IsDominant`.
-- - The Stacks tag evidence is consistent: item tag `01RL` agrees with the source URL ending in
--   `/tag/01RL`.

/- The source-facing componentwise generic-point criterion is a bridge to the canonical owner
`genericPoints S`. -/
theorem forall_genericPointOfComponent_mem_range_iff_genericPoints_subset_range
    {X S : Scheme.{u}} (f : X ⟶ S) :
    (∀ Z : irreducibleComponents S, (genericPoints.ofComponent Z : S) ∈ Set.range f.base) ↔
      genericPoints S ⊆ Set.range f.base := by
  constructor
  · intro h s
    simpa using h (genericPoints.equiv s)
  · intro h Z
    exact h (genericPoints.ofComponent Z).2

/-- Lemma 29.8.3: a quasi-compact morphism of schemes is dominant if and only if every generic
point of the target lies in its image. -/
@[stacks 01RL]
theorem isDominant_iff_genericPoints_subset_range {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] :
    IsDominant f ↔ genericPoints S ⊆ Set.range f.base := by
  rw [forall_genericPointOfComponent_mem_range_iff_genericPoints_subset_range]
  constructor
  · intro hf Z
    by_contra hη
    rcases exists_open_preimage_eq_bot_of_genericPoint_not_mem_range f
        (genericPoints.isGenericPoint_ofComponent Z) hη with ⟨V, hηV, hpre⟩
    have hdense : DenseRange f.base := (isDominant_iff f).mp hf
    rcases hdense.mem_nhds (genericPoints.ofComponent Z : S) (V.2 hηV) with ⟨x, hx⟩
    have hx' : x ∈ (f ⁻¹ᵁ V : Set X) := hx
    simpa [hpre] using hx'
  · exact isDominant_of_forall_genericPointOfComponent_mem_range f

/-- Lemma 29.8.3, source-facing component form: a quasi-compact morphism of schemes is dominant if
and only if the generic point of every irreducible component of the target lies in its image. -/
@[stacks 01RL]
theorem isDominant_iff_forall_genericPointOfComponent_mem_range {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] :
    IsDominant f ↔
      ∀ Z : irreducibleComponents S, (genericPoints.ofComponent Z : S) ∈ Set.range f.base := by
  rw [isDominant_iff_genericPoints_subset_range,
    forall_genericPointOfComponent_mem_range_iff_genericPoints_subset_range]

end AlgebraicGeometry
