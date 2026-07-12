import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_3_6
import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_2_5
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_2_6_10
import ConvexAnalysis_Rockafellar_1970.Chap08.Definition_39_0_1

open scoped SetRel Rockafellar

universe u v w z

namespace SetRel

/-!
Source/core/bridge triage:

- `source-facing`: Proposition 39.0.11 gives two one-sided distributivity inclusions for the
  product of convex processes with the fiberwise Minkowski sum, then asserts that convex processes
  `R^n ⥤ R^n` form a complete lattice under graph inclusion.
- `core/canonical`: the chapter owner for a convex process is `A.IsConvexProcess R` on a relation
  `A : SetRel U X`; the product is the canonical relation composition `○`, the source sum is the
  chapter fiberwise-sum owner `+ᶠ`, infima live on `sInf` of relation graphs, and suprema are
  realized by the canonical generated-cone owner `cone[R]` of the graph union. The class of convex
  processes is the canonical owner `SetRel.convexProcessSet R`.
- `bridge/view`: the textbook graph-inclusion language is exactly the subset order on
  `SetRel U X = Set (U × X)`, while the lattice clause is expressed through `lowerBounds`,
  `upperBounds`, `IsGreatest`, and `IsLeast`.

Primary mathematical domain:
- convex processes viewed as pointed convex cones in the graph space `U × X`.

Domain-style sampling used here:
- `SetRel.comp`, `SetRel.mem_comp`, and `SetRel.comp_subset_comp` from `Mathlib.Data.Rel`;
- `Set.fiberwiseSum` and `Set.mem_fiberwiseSum` from `Chap01.Theorem_3_6`;
- the convex-process owner surface `A.IsConvexProcess R` from `Chap08.Definition_39_0_1`;
- `PointedCone.hull`, `PointedCone.subset_hull`, and the complete-lattice API on `PointedCone`
  from `Chap01.Definition_2_6_10` / mathlib.

Primitive data vs derived API:
- primitive raw relations: typed composition chains and process graphs `A : SetRel U X`;
- primitive source operations: composition `○` and fiberwise sum `+ᶠ`;
- derived order-theoretic API: the greatest lower bound `sInf 𝒜` and the least upper bound
  `cone[R] (⋃₀ 𝒜)` for families of convex-process graphs, expressed against the owner
  `SetRel.convexProcessSet R`.

Layer target:
- clauses (1) and (2) are `source-facing` raw graph-inclusion statements on the canonical relation
  owners;
- clauses (3) and (4) are `bridge/view` order-theoretic formulations of the source complete-lattice
  claim on the family owner `SetRel.convexProcessSet R`.
-/

section DistributiveInclusions

section RightFactor

variable {U : Type v}
variable {X : Type w}
variable {Y : Type z}
variable {A₁ A₂ : SetRel U X} {A : SetRel X Y}

-- Proof sketch: unpack membership in the left fiberwise sum using
-- `Set.mem_fiberwiseSum`, split both composite witnesses with `SetRel.mem_comp`, add the
-- two middle witnesses using additive closure of the common right factor `A`, and repack
-- the source witnesses into the fiberwise sum before composing again.
/- Proposition 39.0.11 (1), primitive owner form: this inclusion only needs additive graph closure
of the common right factor. -/
theorem fiberwiseSum_comp_subset_comp_fiberwiseSum_of_add_mem
    [Add X] [Add Y]
    (hAadd :
      ∀ {x₁ x₂ : X} {y₁ y₂ : Y},
        x₁ ~[A] y₁ → x₂ ~[A] y₂ → x₁ + x₂ ~[A] (y₁ + y₂)) :
    ((A₁ ○ A) +ᶠ (A₂ ○ A)) ⊆ (A₁ +ᶠ A₂) ○ A := by
  rintro ⟨u, y⟩ hy
  rcases (Set.mem_fiberwiseSum (C₁ := A₁ ○ A) (C₂ := A₂ ○ A) (x := (u, y))).mp hy with
    ⟨y₁, y₂, hy₁, hy₂, rfl⟩
  rcases SetRel.mem_comp.mp hy₁ with ⟨x₁, hx₁, hAy₁⟩
  rcases SetRel.mem_comp.mp hy₂ with ⟨x₂, hx₂, hAy₂⟩
  refine SetRel.mem_comp.mpr ⟨x₁ + x₂, ?_, hAadd hAy₁ hAy₂⟩
  exact (Set.mem_fiberwiseSum (C₁ := (A₁ : Set (U × X))) (C₂ := (A₂ : Set (U × X)))
      (x := (u, x₁ + x₂))).mpr
    ⟨x₁, x₂, hx₁, hx₂, rfl⟩

/-- Proposition 39.0.11 (1), primitive owner form: relation composition distributes over the
fiberwise source sum on the right under additive graph closure of the common right factor. -/
theorem fiberwiseSum_comp_subset_comp_fiberwiseSum
    [Add X] [Add Y]
    (hAadd :
      ∀ {x₁ x₂ : X} {y₁ y₂ : Y},
        x₁ ~[A] y₁ → x₂ ~[A] y₂ → x₁ + x₂ ~[A] (y₁ + y₂)) :
    ((A₁ ○ A) +ᶠ (A₂ ○ A)) ⊆ (A₁ +ᶠ A₂) ○ A :=
  fiberwiseSum_comp_subset_comp_fiberwiseSum_of_add_mem
    (A₁ := A₁) (A₂ := A₂) (A := A) hAadd

section ConvexProcessBridge

variable {R : Type u} [DivisionSemiring R] [PartialOrder R]
variable [PosMulReflectLT R] [ZeroLEOneClass R] [AddLeftMono R]
variable [AddCommMonoid X] [Module R X]
variable [AddCommMonoid Y] [Module R Y]

/-- Proposition 39.0.11 (1): if the common right factor `A` is a convex process, then translating
the textbook convention `BA = A ○ B`, the inclusion `A(A₁ + A₂) ⊇ AA₁ + AA₂` becomes
`(A₁ ○ A) +ᶠ (A₂ ○ A) ⊆ (A₁ +ᶠ A₂) ○ A` on relation graphs. -/
theorem fiberwiseSum_comp_subset_comp_fiberwiseSum_of_isConvexProcess
    (hA : A.IsConvexProcess R) :
    ((A₁ ○ A) +ᶠ (A₂ ○ A)) ⊆ (A₁ +ᶠ A₂) ○ A := by
  exact fiberwiseSum_comp_subset_comp_fiberwiseSum
    (A₁ := A₁) (A₂ := A₂) (A := A) (fun hAy₁ hAy₂ ↦ hA.add_mem hAy₁ hAy₂)

end ConvexProcessBridge

end RightFactor

section LeftFactor

variable {U : Type u} {X : Type v} {Y : Type w}
variable [Add Y]
variable {A : SetRel U X} {A₁ A₂ : SetRel X Y}

-- Proof sketch: unpack membership in `A ○ (A₁ +ᶠ A₂)` via `SetRel.mem_comp`, split the terminal
-- witness with `Set.mem_fiberwiseSum`, and then use the same middle point from `A` to build
-- witnesses in `A ○ A₁` and `A ○ A₂`, which repack into the fiberwise sum.
/-- Proposition 39.0.11 (2): translating the textbook convention `BA = A ○ B`, the inclusion
`(A₁ + A₂)A ⊆ A₁A + A₂A` becomes
`A ○ (A₁ +ᶠ A₂) ⊆ (A ○ A₁) +ᶠ (A ○ A₂)` on relation graphs. -/
theorem comp_fiberwiseSum_subset_fiberwiseSum_comp :
    A ○ (A₁ +ᶠ A₂) ⊆ ((A ○ A₁) +ᶠ (A ○ A₂)) := by
  rintro ⟨u, y⟩ hy
  rcases SetRel.mem_comp.mp hy with ⟨x, hAx, hx⟩
  rcases (Set.mem_fiberwiseSum (C₁ := (A₁ : Set (X × Y))) (C₂ := (A₂ : Set (X × Y)))
      (x := (x, y))).mp hx with
    ⟨y₁, y₂, hy₁, hy₂, rfl⟩
  exact (Set.mem_fiberwiseSum (C₁ := A ○ A₁) (C₂ := A ○ A₂) (x := (u, y₁ + y₂))).mpr
    ⟨y₁, y₂, SetRel.mem_comp.mpr ⟨x, hAx, hy₁⟩, SetRel.mem_comp.mpr ⟨x, hAx, hy₂⟩, rfl⟩

end LeftFactor

end DistributiveInclusions

namespace IsConvexProcess

section InfCompleteLattice

variable {R : Type u} [Semiring R] [PartialOrder R]
variable {U : Type v} [AddCommMonoid U] [SMul R U]
variable {X : Type w} [AddCommMonoid X] [SMul R X]
variable {𝒜 : Set (SetRel U X)}

-- Proof sketch: `sInf 𝒜 = ⋂₀ 𝒜`, so the graph is again a convex cone by
-- `Set.IsConvexCone.sInter`; the distinguished origin belongs to every member of `𝒜`, hence also
-- to their intersection.
/-- Owner-level infimum closure: the intersection of any family of convex-process graphs is again
a convex process. -/
theorem sInf_isConvexProcess (h𝒜 : 𝒜 ⊆ convexProcessSet R) :
    (sInf 𝒜).IsConvexProcess R := by
  refine ⟨?_, ?_⟩
  · simpa using Set.IsConvexCone.sInter fun A hA ↦ (h𝒜 hA).isConvexCone
  · simpa using Set.mem_sInter.mpr (fun A hA ↦ (h𝒜 hA).zero_mem)

-- Proof sketch: the graph intersection `sInf 𝒜 = ⋂₀ 𝒜` preserves the convex-cone part by
-- `Set.IsConvexCone.sInter`, and it preserves the distinguished origin because every member of
-- `𝒜` contains `(0, 0)`. The lower-bound and maximality clauses are then the standard
-- order-theoretic facts about intersections.
/-- Proposition 39.0.11 (3): the family of convex processes `U ⇸ X` has arbitrary infima under graph
inclusion; concretely, for any family `𝒜`, the graph intersection `sInf 𝒜` is the greatest convex
process contained in every member of `𝒜`. -/
theorem isGreatest_lowerBounds_sInf
    (h𝒜 : 𝒜 ⊆ convexProcessSet R) :
    IsGreatest (convexProcessSet R ∩ lowerBounds 𝒜) (sInf 𝒜) := by
  refine ⟨?_, ?_⟩
  · constructor
    · exact sInf_isConvexProcess h𝒜
    · intro A hA x hx
      exact Set.mem_sInter.mp hx A hA
  · intro A hA x hx
    exact Set.mem_sInter.mpr (fun B hB ↦ hA.2 hB hx)

end InfCompleteLattice

section SupClosure

variable {R : Type u} [Semiring R] [PartialOrder R] [IsOrderedRing R]
variable {U : Type v} [AddCommMonoid U] [Module R U]
variable {X : Type w} [AddCommMonoid X] [Module R X]
variable {𝒜 : Set (SetRel U X)}

-- Proof sketch: `cone[R] (⋃₀ 𝒜)` is a pointed cone by construction, hence a convex-process graph.
-- Its zero element is the distinguished point of the pointed-cone owner.
/-- Owner-level supremum closure: the pointed-cone hull of the union of any family of
convex-process graphs is again a convex process. -/
theorem cone_sUnion_isConvexProcess :
    SetRel.IsConvexProcess R
      (((cone[R] (⋃₀ 𝒜) : PointedCone R (U × X)) : SetRel U X)) := by
  refine ⟨?_, ?_⟩
  · simpa using
      (((cone[R] (⋃₀ 𝒜) : PointedCone R (U × X)) : ConvexCone R (U × X)).isConvexCone)
  · exact (cone[R] (⋃₀ 𝒜) : PointedCone R (U × X)).zero_mem

end SupClosure

section SupCompleteLattice

variable {R : Type u} [DivisionSemiring R] [PartialOrder R] [IsOrderedRing R]
variable [PosMulReflectLT R]
variable {U : Type v} [AddCommMonoid U] [Module R U]
variable {X : Type w} [AddCommMonoid X] [Module R X]
variable {𝒜 : Set (SetRel U X)}

-- Proof sketch: every member of `𝒜` contains the origin, so the graph union `⋃₀ 𝒜` does as well;
-- applying the pointed-cone hull `cone[R]` gives the smallest pointed convex cone
-- containing that union. Its carrier is therefore the least convex-process graph containing every
-- member of `𝒜`, i.e. the supremum under inclusion.
/-- Proposition 39.0.11 (4): the family of convex processes `U ⇸ X` has arbitrary suprema under
graph inclusion; concretely, for any family `𝒜`, the pointed-cone hull of the graph union
`⋃₀ 𝒜` is the least convex process containing every member of `𝒜`.
The extra scalar assumptions beyond `cone_sUnion_isConvexProcess` are exactly those required by
`Set.IsConvexCone.add_mem`, used here to package an arbitrary convex-process upper bound as a
`PointedCone`. -/
theorem isLeast_upperBounds_cone_sUnion :
    IsLeast (convexProcessSet R ∩ upperBounds 𝒜)
      (cone[R] (⋃₀ 𝒜) : SetRel U X) := by
  refine ⟨?_, ?_⟩
  · constructor
    · exact cone_sUnion_isConvexProcess
    · intro A hA x hx
      exact PointedCone.subset_hull <| Set.mem_sUnion.mpr ⟨A, hA, hx⟩
  · intro B hB
    let Bp : PointedCone R (U × X) := {
      carrier := B
      smul_mem' := fun c x hx ↦ by
        rcases eq_or_lt_of_le c.property with hzero | hc
        · have hc : c = 0 := Subtype.ext hzero.symm
          have hcx : c • x = (0 : U × X) := by
            simp [hc]
          exact hcx ▸ hB.1.zero_mem
        · exact hB.1.isConvexCone.isCone.smul_mem hc hx
      add_mem' := fun hx hy ↦ hB.1.add_mem hx hy
      zero_mem' := hB.1.zero_mem
    }
    have hsUnion_subset : ⋃₀ 𝒜 ⊆ (Bp : Set (U × X)) := by
      intro x hx
      rcases Set.mem_sUnion.mp hx with ⟨A, hA, hxA⟩
      exact hB.2 hA hxA
    have hhull_le : PointedCone.hull R (⋃₀ 𝒜) ≤ Bp :=
      Submodule.span_le.mpr hsUnion_subset
    change (PointedCone.hull R (⋃₀ 𝒜) : Set (U × X)) ⊆ B
    simpa [Bp] using hhull_le

end SupCompleteLattice

end IsConvexProcess

end SetRel
