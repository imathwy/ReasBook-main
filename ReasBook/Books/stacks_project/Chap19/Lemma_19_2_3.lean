import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

section

variable {J : Type v} [SmallCategory J]

/- Domain-style sampling for Lemma 19.2.3:
- primary domain: filtered colimits in `Type` and represented Hom-functors `Hom(A, -)`;
- sampled owner declarations:
  `colimit.post`,
  `CategoryTheory.Types.isCardinalPresentable_iff`,
  `CategoryTheory.isFinitelyPresentable_iff_preservesFilteredColimits`,
  `CategoryTheory.Limits.preservesFilteredColimitsOfSize_shrink`;
- best owner abstraction: the source-facing comparison map is the canonical owner
  `colimit.post B (coyoneda.obj (op A))`, while the core/canonical input controlling its
  bijectivity is `IsFinitelyPresentable A`;
- primitive data: the finite type `A` and the filtered diagram `B`;
- derived API: preservation of the colimit of `B` by `coyoneda.obj (op A)`, hence the bijectivity
  of `colimit.post B (coyoneda.obj (op A))`.

Source/core/bridge triage:
- `source-facing`: the displayed bijection
  `colim_j Hom(A, B_j) → Hom(A, colim_j B_j)` for finite `A`;
- `core/canonical`: `IsFinitelyPresentable A`;
- `bridge/view`: the `Type`-specific cardinal characterization of finite presentability and the
  specialization of preservation to the fixed comparison map `colimit.post`.
-/

-- Proof sketch: use that finite sets are finitely presentable in `Type`, so `coyoneda.obj (op A)`
-- preserves filtered colimits; then the displayed comparison map is the comparison morphism from
-- the preserved colimit cocone and hence is bijective.
/-- Lemma 19.2.3: for a filtered diagram of sets and a finite set `A`, the canonical map
`colim_j Hom(A, B_j) → Hom(A, colim_j B_j)` is bijective. -/
theorem finite_hom_to_colimit_comparison_bijective [IsFiltered J] (A : Type (max u v))
    [Finite A] (B : J ⥤ Type (max u v)) :
    Function.Bijective (colimit.post B (coyoneda.obj (op A))) := by
  letI : Fact Cardinal.aleph0.IsRegular := ⟨Cardinal.isRegular_aleph0⟩
  letI : IsFinitelyPresentable.{max u v} A := by
    exact (CategoryTheory.Types.isCardinalPresentable_iff Cardinal.aleph0).2 <| by
      rw [hasCardinalLT_aleph0_iff]
      infer_instance
  letI : PreservesFilteredColimitsOfSize.{v, v} (coyoneda.obj (op A)) :=
    preservesFilteredColimitsOfSize_shrink (coyoneda.obj (op A))
  letI : PreservesColimit B (coyoneda.obj (op A)) := by
    infer_instance
  exact (isIso_iff_bijective (colimit.post B (coyoneda.obj (op A)))).1 inferInstance

end
