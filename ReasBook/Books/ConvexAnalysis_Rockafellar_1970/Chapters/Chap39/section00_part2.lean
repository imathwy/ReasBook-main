import Mathlib
import Mathlib.Data.Rel
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Proposition_39_0_9 (from Chap08) -/
noncomputable section

open scoped Rockafellar SetRel

universe u v w

namespace SetRel

section FunctionImage

variable {U : Type u} {X : Type v} {α : Type w}
variable [ConditionallyCompleteLattice α]

/-- The Chapter 39 process image `Af` of a function `f` under a process `A`, defined directly as
the infimum of `f` over the inverse fibers of `A`. -/
abbrev functionImage (A : SetRel U X) (f : U → WithBotTop α) : X → WithBotTop α :=
  fun x ↦ sInf (f '' A.preimage ({x} : Set X))

/- Source-facing image notation for Chapter 39: `A ◁ f` denotes the process image `Af`,
implemented by the canonical owner `SetRel.functionImage`. -/
scoped[Rockafellar] infixr:65 " ◁ " => SetRel.functionImage

/-- At `x`, the process image `Af` is the infimum of the values of `f` on the inverse fiber
`A.preimage {x}`. -/
theorem functionImage_apply_eq_sInf_image_preimage_singleton
    (A : SetRel U X) (f : U → WithBotTop α) (x : X) :
    (A ◁ f) x =
      sInf (f '' A.preimage ({x} : Set X)) := rfl

private theorem mem_preimage_singleton_iff_mem_image_singleton
    (A : SetRel U X) (u : U) (x : X) :
    u ∈ A.preimage ({x} : Set X) ↔ x ∈ A.image ({u} : Set U) := by
  simp [SetRel.preimage, SetRel.image]

section Bridge

variable [Add α] [Zero α]

/-- The direct process-image owner agrees with the Chapter 38 image of the fiber indicator when
`f` never takes the value `⊥`. -/
theorem functionImage_eq_image_indicatorFibers_of_ne_bot
    (A : SetRel U X) (f : U → WithBotTop α) (hf_ne_bot : ∀ u : U, f u ≠ ⊥) :
    A ◁ f = Bifunction.image (indicatorFibers α A) f := by
  ext x
  let fiber : Set U := A.preimage ({x} : Set X)
  let g : U → WithBotTop α := fun u ↦ f u + indicatorFibers α A u x
  rw [Bifunction.image_apply_eq_sInf_range]
  change sInf (f '' fiber) = sInf (Set.range g)
  have himage_subset : f '' fiber ⊆ Set.range g := by
    intro r hr
    rcases hr with ⟨u, hu, rfl⟩
    have hx_image : x ∈ A.image ({u} : Set U) :=
      (mem_preimage_singleton_iff_mem_image_singleton A u x).mp hu
    refine ⟨u, ?_⟩
    simp [g, indicatorFibers, indicator_def, hx_image]
  have hrange_subset : Set.range g ⊆ insert ⊤ (f '' fiber) := by
    intro r hr
    rcases hr with ⟨u, rfl⟩
    by_cases hu : u ∈ fiber
    · right
      have hx_image : x ∈ A.image ({u} : Set U) :=
        (mem_preimage_singleton_iff_mem_image_singleton A u x).mp hu
      exact ⟨u, hu, by simp [g, indicatorFibers, indicator_def, hx_image]⟩
    · left
      have hx_image : x ∉ A.image ({u} : Set U) := by
        exact mt (mem_preimage_singleton_iff_mem_image_singleton A u x).mpr hu
      have htop : f u + (⊤ : WithBotTop α) = ⊤ :=
        WithBotTop.add_top_of_ne_bot (hf_ne_bot u)
      simpa [g, indicatorFibers, indicator_def, hx_image] using
        htop
  by_cases hfiber : fiber.Nonempty
  · have himage_nonempty : (f '' fiber).Nonempty := hfiber.image f
    have hsInf_insert_top :
        sInf (insert ⊤ (f '' fiber)) = sInf (f '' fiber) := by
      have hsInf_insert :
          sInf (insert (⊤ : WithBotTop α) (f '' fiber)) =
            (⊤ : WithBotTop α) ⊓ sInf (f '' fiber) :=
        csInf_insert (OrderBot.bddBelow (f '' fiber)) himage_nonempty
      calc
        sInf (insert ⊤ (f '' fiber))
            = (⊤ : WithBotTop α) ⊓ sInf (f '' fiber) := hsInf_insert
        _ = sInf (f '' fiber) := by simp
    apply le_antisymm
    · calc
        sInf (f '' fiber) = sInf (insert ⊤ (f '' fiber)) := hsInf_insert_top.symm
        _ ≤ sInf (Set.range g) := sInf_le_sInf hrange_subset
    · exact sInf_le_sInf himage_subset
  · have hfiber_eq : fiber = ∅ := Set.not_nonempty_iff_eq_empty.mp hfiber
    have hg_top : ∀ u : U, g u = (⊤ : WithBotTop α) := by
      intro u
      have hu : u ∉ fiber := by simp [hfiber_eq]
      have hx_image : x ∉ A.image ({u} : Set U) := by
        exact mt (mem_preimage_singleton_iff_mem_image_singleton A u x).mpr hu
      have htop : f u + (⊤ : WithBotTop α) = ⊤ :=
        WithBotTop.add_top_of_ne_bot (hf_ne_bot u)
      simpa [g, indicatorFibers, indicator_def, hx_image] using
        htop
    have hsInf_range : sInf (Set.range g) = (⊤ : WithBotTop α) := by
      apply top_unique
      refine le_sInf ?_
      rintro _ ⟨u, rfl⟩
      simp [hg_top u]
    calc
      sInf (f '' fiber) = (⊤ : WithBotTop α) := by simp [hfiber_eq]
      _ = sInf (Set.range g) := hsInf_range.symm

/-- Compatibility wrapper of `functionImage_eq_image_indicatorFibers_of_ne_bot` using the
strictly-positive/non-bottom hypothesis format. -/
theorem functionImage_eq_image_indicatorFibers_of_bot_lt
    (A : SetRel U X) (f : U → WithBotTop α) (hf_bot : ∀ u : U, ⊥ < f u) :
    A ◁ f = Bifunction.image (indicatorFibers α A) f :=
  functionImage_eq_image_indicatorFibers_of_ne_bot A f (fun u ↦ (hf_bot u).ne')

end Bridge

end FunctionImage

section Convexity

variable {𝕜 : Type u} [Ring 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [IsStrictOrderedRing 𝕜] [DenselyOrdered 𝕜]
variable {U : Type v} [AddCommMonoid U] [SMul 𝕜 U]
variable {X : Type w} [AddCommMonoid X] [SMul 𝕜 X]
variable {A : SetRel U X} {f : U → WithBotTop 𝕜}

-- Proof sketch: use the strict affine-upper-bound owner criterion for convexity. A strict upper
-- bound on `Af x` or `Af y` yields witnesses `u₁ ∈ A⁻¹ x`, `u₂ ∈ A⁻¹ y` with correspondingly
-- strict bounds on `f u₁`, `f u₂`. Convexity of the process graph sends the convex combination of
-- `u₁, u₂` into the fiber over the convex combination of `x, y`, and convexity of `f` then gives
-- the desired strict bound on `Af`.
/-- Graph-convex bridge for the process image owner `A ◁ f`. -/
theorem isConvex_functionImage_of_convex (hA : Convex 𝕜 A) (hf : f.IsConvex 𝕜) :
    (A ◁ f).IsConvex 𝕜 := by
  rw [Function.isConvex_iff_lt_affine_upper_bound]
  intro x y α β t hx hy ht0 ht1
  rcases sInf_lt_iff.mp (by simpa [functionImage] using hx) with ⟨rx, hrx, hrx_lt⟩
  rcases hrx with ⟨ux, hux, rfl⟩
  rcases sInf_lt_iff.mp (by simpa [functionImage] using hy) with ⟨ry, hry, hry_lt⟩
  rcases hry with ⟨uy, huy, rfl⟩
  let z := (1 - t) • x + t • y
  let u := (1 - t) • ux + t • uy
  have huzA : u ~[A] z := by
    simpa [u, z, Prod.smul_mk, Prod.mk_add_mk] using
      hA (by simpa using hux) (by simpa using huy)
        (sub_nonneg.mpr ht1.le) ht0.le (by simp)
  have huz : u ∈ A.preimage ({z} : Set X) := by
    simpa [z] using huzA
  have hle : (A ◁ f) z ≤ f u := by
    simpa [functionImage, z] using
      (sInf_le (show f u ∈ f '' A.preimage ({z} : Set X) from ⟨u, huz, rfl⟩))
  have hfu_lt : f u < (((1 - t) * α + t * β : 𝕜) : WithBotTop 𝕜) := by
    simpa [u] using hf.lt_affine_upper_bound ux uy α β t hrx_lt hry_lt ht0 ht1
  simpa [z] using lt_of_le_of_lt hle hfu_lt

/-- Proposition 39.0.9: if `f` is convex and `A` is a convex process, then the process image
`Af`, rendered here as `A ◁ f`, is convex. -/
theorem isConvex_functionImage (hA : A.IsConvexProcess 𝕜) (hf : f.IsConvex 𝕜) :
    (A ◁ f).IsConvex 𝕜 :=
  isConvex_functionImage_of_convex (A := A) hA.convex hf

end Convexity

namespace IsConvexProcess

section Convexity

variable {𝕜 : Type u} [Ring 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [IsStrictOrderedRing 𝕜] [DenselyOrdered 𝕜]
variable {U : Type v} [AddCommMonoid U] [SMul 𝕜 U]
variable {X : Type w} [AddCommMonoid X] [SMul 𝕜 X]
variable {A : SetRel U X} {f : U → WithBotTop 𝕜}

/-- Convex-process specialization of `SetRel.isConvex_functionImage`. -/
theorem isConvex_functionImage (hA : A.IsConvexProcess 𝕜) (hf : f.IsConvex 𝕜) :
    (A ◁ f).IsConvex 𝕜 :=
  SetRel.isConvex_functionImage (A := A) hA hf

end Convexity

end IsConvexProcess

end SetRel

/-! ### Proposition_39_0_10 (from Chap08) -/
open scoped SetRel

universe u v w z

/-!
Source/core/bridge triage:

- `source-facing`: Proposition 39.0.10 says the product of convex processes is again a convex
  process, and identifies the inverse of that product with the product of the inverses.
- `core/canonical`: the project owner for convex processes is `A.IsConvexProcess R` on
  `A : SetRel U X`, while the product `BA` is exactly the canonical relation composition `A ○ B`.
- `bridge/view`: the inverse clause is already the exact canonical `SetRel` theorem
  `SetRel.inv_comp`, so only the convex-process closure under composition needs a new declaration
  here.

Domain-style sampling used here:
- `SetRel.comp`, `SetRel.mem_comp`, and `SetRel.inv_comp` from `Mathlib.Data.Rel`;
- `Set.IsConvexCone` from `Chap01.Definition_2_5_10`;
- `SetRel.IsConvexProcess` and `SetRel.IsConvexProcess.isConvexCone` from
  `Chap08.Definition_39_0_1`.

Primitive data vs derived API:
- primitive owners: relations `A : SetRel U X` and `B : SetRel X Y`;
- primitive operation: the canonical composition `A ○ B`;
- primitive closure theorem: `SetRel.isConvexCone_comp` on graph owners;
- derived API here: closure of `IsConvexProcess R` under that composition.

Layer target: `source-facing`, stated directly on the canonical `SetRel` owner.
-/

namespace SetRel

section

variable {R : Type u} [Semiring R] [PartialOrder R]
variable {U : Type v} [AddCommMonoid U] [SMul R U]
variable {X : Type w} [AddCommMonoid X] [SMul R X]
variable {Y : Type z} [AddCommMonoid Y] [SMul R Y]
variable {A : SetRel U X} {B : SetRel X Y}

-- Proof sketch: this is the graph-level convex-cone closure under relation composition. For
-- positive-scalar closure, scale the middle witness in `SetRel.mem_comp`; for convexity, combine
-- two middle witnesses by the same affine combination and use convexity of each graph.
/-- Primitive relation owner: composition preserves graph convex-cone structure on relations. -/
theorem isConvexCone_comp (hA : Set.IsConvexCone R A) (hB : Set.IsConvexCone R B) :
    Set.IsConvexCone R (A ○ B) := by
  refine ⟨?_, ?_⟩
  · intro c p hc hp
    rcases SetRel.mem_comp.mp hp with ⟨x, hAx, hBx⟩
    exact SetRel.mem_comp.mpr ⟨c • x, hA.isCone.smul_mem hc hAx, hB.isCone.smul_mem hc hBx⟩
  · intro p hp q hq a b ha hb hab
    rcases SetRel.mem_comp.mp hp with ⟨x₁, hAx₁, hBx₁⟩
    rcases SetRel.mem_comp.mp hq with ⟨x₂, hAx₂, hBx₂⟩
    refine SetRel.mem_comp.mpr ?_
    exact ⟨a • x₁ + b • x₂, hA.convex hAx₁ hAx₂ ha hb hab, hB.convex hBx₁ hBx₂ ha hb hab⟩

end

end SetRel

namespace SetRel.IsConvexProcess

section

variable {R : Type u} [Semiring R] [PartialOrder R]
variable {U : Type v} [AddCommMonoid U] [SMul R U]
variable {X : Type w} [AddCommMonoid X] [SMul R X]
variable {Y : Type z} [AddCommMonoid Y] [SMul R Y]
variable {A : SetRel U X} {B : SetRel X Y}

-- Proof sketch: first compose the graph convex-cone owners via `SetRel.isConvexCone_comp`, then
-- provide the origin witness in the composite graph using the origin witnesses from the factors.
/-- Proposition 39.0.10: the product of two convex processes is again a convex process. In the
canonical `SetRel` owner, the textbook product `(BA)` is the relation composition `A ○ B`. -/
theorem comp (hA : A.IsConvexProcess R) (hB : B.IsConvexProcess R) :
    (A ○ B).IsConvexProcess R := by
  refine ⟨SetRel.isConvexCone_comp hA.isConvexCone hB.isConvexCone, ?_⟩
  · exact SetRel.mem_comp.mpr ⟨0, hA.zero_mem, hB.zero_mem⟩

end

end SetRel.IsConvexProcess

namespace SetRel

section

variable {U : Type v} {X : Type w} {Y : Type z}
variable {A : SetRel U X} {B : SetRel X Y}

/- Proposition 39.0.10 (inverse clause): with the textbook convention `(BA) = A ○ B`, the
canonical relation identity `SetRel.inv_comp` is exactly `(BA)⁻¹ = A⁻¹B⁻¹`. -/
recall SetRel.inv_comp

end

end SetRel

/-! ### Proposition_39_0_11 (from Chap08) -/
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

/-! ### Definition_39_0_12 (from Chap08) -/
noncomputable section

open scoped Rockafellar

universe u

section PairingSwap

variable {X : Type u} {XStar : Type*} {α : Type*}
variable [Neg XStar]
variable [AddCommGroup α] [ConditionallyCompleteLattice α] [IsOrderedAddMonoid α]
variable [HasPairing X XStar α] [HasPairing XStar X α]
variable [HasPairingSwap X XStar α] [HasPairingNegRight X XStar α]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Definition 39.0.12 distinguishes the two readings of the same convex-set
  pairing, through the convex indicator `δ[α](· | C)` on the supremum side and the concave
  function `-δ[α](· | C)` on the infimum side.
- `core/canonical`: the chapter already owns those two readings as the support-function owner
  `supportFunction C`, written `δᵛ[WithBotTop α](· | C)`, together with the concave conjugate
  `concaveConjugate (-(δ[α](· | C) : X → WithBotTop α))`.
- `bridge/view`: this file is therefore a pure bridge file. It does not introduce a separate
  orientation owner, because the mathematics already lives on those canonical function owners.
  The public surface is direct recall of the supremum-side equality plus the infimum-side bridge
  to `-δᵛ[WithBotTop α](-xStar | C)` and its `sInf` formula.

Primary mathematical domain:
- support-function and infimum-pairing views of a convex set at the pairing level.

Domain-style sampling used here:
- `convexConjugate_indicatorFunction_eq_supportFunction` from `Chap03.Text_13_1_4`;
- `concaveConjugate` from `Chap06.Definition_6_30_4`;
- `supportFunction` and `supportFunction_def` from `Chap01.Defintion_4_8_2`;
- `neg_supportFunction_neg_eq_sInf_image_pairing` from `Chap03.Text_13_0_2`.

Primitive data vs derived API:
- primitive data introduced here: none beyond the ambient set `C`;
- derived API: the supremum-side direct recall
  `convexConjugate_indicatorFunction_eq_supportFunction`, together with the
  infimum-side bridge from `concaveConjugate (-(δ[α](· | C) : X → WithBotTop α))` to the sign-dual support
  function formula and its pointwise `sInf` specialization.

Abstraction-layer choice:
- the canonical owner is the generic pairing bridge on `(X, XStar)`;
- this file intentionally avoids extra self-pairing wrapper declarations, since they are strict
  specializations of the generic owner and do not add new mathematical structure.

Layer target: `bridge/view`.

Notation evaluation:
- the source writes the same bracket notation `⟨C, x⋆⟩` for both readings, with the choice of
  branch supplied by context;
- because this file deliberately avoids introducing a second owner object for that contextual
  choice, no new notation is added here;
- the public surface remains the explicit owner formulas already used elsewhere in the chapter.
-/

/-- In the infimum orientation, the concave conjugate of the negative indicator is the sign-dual
support-function pairing `xStar ↦ -δᵛ[WithBotTop α](-xStar | C)`. -/
@[simp]
theorem concaveConjugate_neg_indicatorFunction_eq_neg_supportFunction_neg (C : Set X) :
    concaveConjugate (-(δ(· | C) : X → WithBotTop α)) =
      fun xStar : XStar ↦ -δᵛ(-xStar | C) := by
  have hnegfun : (-(-(δ(· | C) : X → WithBotTop α))) = (δ(· | C)) := by
    funext x
    simp
  ext xStar
  calc
    concaveConjugate (-(δ(· | C) : X → WithBotTop α)) xStar
        = -((-(-(δ(· | C) : X → WithBotTop α)))⋆ (-xStar)) := by
          simpa using
            concaveConjugate_eq_neg_convexConjugate_neg_apply
              (-(δ(· | C) : X → WithBotTop α)) xStar
    _ = -((δ(· | C))⋆ (-xStar : XStar)) := by
          congr 1
          exact
            congrArg
              (fun f : X → WithBotTop α ↦ (f⋆ : XStar → WithBotTop α) (-xStar))
              hnegfun
    _ = -δᵛ(-xStar | C) := by
          congr 1
          simpa using
            (convexConjugate_indicatorFunction_eq_supportFunction_pointwise
              (C := C) (xStar := -xStar))

@[simp]
theorem concaveConjugate_neg_indicatorFunction_eq_neg_supportFunction_neg_pointwise
    (C : Set X) (xStar : XStar) :
    concaveConjugate (-(δ(· | C) : X → WithBotTop α)) xStar =
      -δᵛ(-xStar | C) := by
  simpa using
    congrFun
      (concaveConjugate_neg_indicatorFunction_eq_neg_supportFunction_neg
        C) xStar

/-- In the infimum orientation, the oriented-set pairing is exactly the infimum of the pairings
`⟪xStar, x⟫ₚ` over `x ∈ C`. -/
theorem concaveConjugate_neg_indicatorFunction_eq_sInf_image_pairing
    (C : Set X) (xStar : XStar) :
    concaveConjugate (-(δ(· | C) : X → WithBotTop α)) xStar =
      sInf ((fun x ↦ (⟪xStar, x⟫ₚ : WithBotTop α)) '' C) := by
  rw [concaveConjugate_neg_indicatorFunction_eq_neg_supportFunction_neg_pointwise (C := C)]
  simpa using
    neg_supportFunction_neg_eq_sInf_image_pairing (C := C) (xStar := xStar)

end PairingSwap

end

/-! ### Proposition_39_0_13 (from Chap08) -/
noncomputable section

open scoped Rockafellar SetRel

universe u v

namespace SetRel

/-!
Source/core/bridge triage:

- `source-facing`: Proposition 39.0.13 attaches to a supremum-oriented convex process `A` the
  canonical slice-indicator owner `indicatorFibers α A` and states its domain,
  graph convexity, properness, and the lower-semicontinuity/graph-closedness equivalence.
- `core/canonical`: the process itself already lives on the relation owner `A : SetRel U X` via
  `A.IsConvexProcess 𝕜`; the bifunction/process owners already present in the chapter are
  `dom F`, `Bifunction.IsProper F`, the graph-owner notations `convᵇ[𝕜](F)` / `closedᵇ(F)`, and
  `A.IsClosed`.
- `bridge/view`: the only extra bridge kept here is the uncurrying identity from the canonical
  slice-indicator owner to the graph indicator of `A`.

Primary mathematical domain:
- convex processes and their indicator bifunctions.

Domain-style sampling used here:
- `SetRel.IsConvexProcess` from `Definition_39_0_1`;
- the Chapter 6 canonical bifunction surface
  `#check (indicatorFibers α A : U → X → WithBotTop α)`;
- `Bifunction.dom` and `Bifunction.IsProper` from `Definition_6_29_8` and `Theorem_38_1`;
- `indicator` notation `δ[α](x | C)` from `Defintion_4_8_1`;
- `indicator_isConvex_iff` from `Remark_4_8_1`;
- `SetRel.IsClosed` from `Definition_39_0_5`.

Primitive data vs derived API:
- primitive source-facing data: the relation `A : SetRel U X`;
- primitive source-facing owner: `indicatorFibers α A`;
- derived API: the uncurrying bridge, the domain identity, the owner-level properness criterion in
  terms of `A.dom`, its convex-process specialization, convexity on the Chapter 6 owner surface
  `convᵇ[𝕜](indicatorFibers α A)`, and the closedness/graph-closedness equivalence on
  `closedᵇ(indicatorFibers α A)`.

Layer target: `source-facing`, stated directly on the canonical `SetRel` and `Bifunction` owners,
with a short owner (`indicatorFibers`) for the recurring slice-indicator surface.
-/

section Indicator

variable {U : Type u} {X : Type v}
variable {α : Type*}
variable [Zero α]

/-- The canonical slice-indicator bifunction of a relation. -/
abbrev indicatorFibers (α : Type*) [Zero α] (A : SetRel U X) : U → X → WithBotTop α :=
  fun u ↦ (δ[α](· | A.image ({u} : Set U)) : X → WithBotTop α)

/-- Uncurrying `indicatorFibers α A` gives the indicator of the graph of `A`. -/
theorem uncurry_indicatorFibers_eq_indicator
    (A : SetRel U X) :
    Function.uncurry (indicatorFibers α A) =
      (δ[α](· | (A : Set (U × X)))) := by
  funext p
  rcases p with ⟨u, x⟩
  simp [indicatorFibers, indicator_def, SetRel.image]

end Indicator

section Domain

variable {U : Type u} {X : Type v}
variable {α : Type*} [Preorder α] [Zero α]

-- Proof sketch: unfold `Bifunction.dom` and `Function.IsProper` for the slice
-- `x ↦ δ[α](x | A.image ({u} : Set U))`. The effective domain of an indicator is exactly the
-- underlying set, and the indicator never takes the value `⊥`, so the slice is proper exactly
-- when the singleton fiber is nonempty, i.e. exactly when `u ∈ A.dom`.
/-- The parameter-domain of the indicator bifunction is exactly the domain of the underlying
process. -/
theorem dom_indicatorFibers_eq_dom (A : SetRel U X) :
    dom (indicatorFibers α A) = A.dom := sorry

end Domain

section Convexity

variable {U : Type u} {X : Type v}
variable {𝕜 : Type*} [Semiring 𝕜] [PartialOrder 𝕜]
variable [AddCommMonoid U] [SMul 𝕜 U]
variable [AddCommMonoid X] [SMul 𝕜 X]
variable {α : Type*}
variable [Preorder α] [AddCommMonoid α] [IsOrderedAddMonoid α]
variable [SMulZeroClass 𝕜 α] [PosSMulMono 𝕜 α]
variable {A : SetRel U X}

-- Proof sketch: identify the uncurried slice-wise indicator expression with the indicator of the
-- graph `A ⊆ U × X`. Then apply `indicator_isConvex_iff` on the product space. Only graph
-- convexity is used, so the convex-process zero-membership field is not part of this theorem's
-- public input.
/-- The graph function of the fiber-indicator bifunction is convex whenever the graph of the
underlying relation is convex. -/
private theorem indicator_graph_isConvex
    (hA : Convex 𝕜 (A : Set (U × X))) :
    (δ[α](· | (A : Set (U × X)))).IsConvex 𝕜 := by
  exact (indicator_isConvex_iff (𝕜 := 𝕜) (α := α) (C := (A : Set (U × X)))).2 hA

/-- Bridge form of `indicator_graph_isConvex` on the chapter bifunction owner
`indicatorFibers α A`, stated on the canonical Chapter 6 surface `convᵇ[𝕜](·)`. -/
theorem uncurry_indicatorFibers_isConvex
    (hA : Convex 𝕜 (A : Set (U × X))) :
    convᵇ[𝕜](indicatorFibers α A) := by
  simpa [uncurry_indicatorFibers_eq_indicator (α := α) (A := A)] using
    (indicator_graph_isConvex (𝕜 := 𝕜) (α := α) (A := A) hA)

end Convexity

section Proper

variable {U : Type u} {X : Type v}
variable {α : Type*} [Zero α] [Preorder α]
variable {A : SetRel U X}

-- Proof sketch: `Bifunction.IsProper` is definitionally nonemptiness of the slice-domain, and
-- `dom_indicatorFibers_eq_dom` identifies that slice-domain with `A.dom`.
/-- The indicator bifunction is proper exactly when the underlying process has nonempty domain. -/
theorem indicatorFibers_isProper (hA_dom : A.dom.Nonempty) :
    Bifunction.IsProper (indicatorFibers α A) := by
  rw [Bifunction.IsProper, dom_indicatorFibers_eq_dom]
  exact hA_dom

namespace IsConvexProcess

variable {𝕜 : Type*} [Semiring 𝕜] [PartialOrder 𝕜]
variable [AddCommMonoid U] [SMul 𝕜 U]
variable [AddCommMonoid X] [SMul 𝕜 X]

-- Proof sketch: the convex-process owner supplies the primitive domain witness `0 ∈ A.dom`
-- through `hA.zero_mem`, so the owner-level properness criterion applies immediately.
/-- Convex-process specialization of `indicatorFibers_isProper`. -/
theorem indicatorFibers_isProper (hA : A.IsConvexProcess 𝕜) :
    Bifunction.IsProper (indicatorFibers α A) :=
  SetRel.indicatorFibers_isProper ⟨0, ⟨0, hA.zero_mem⟩⟩

end IsConvexProcess

end Proper

section Closed

variable {U : Type u} {X : Type v}
variable {α : Type*}
variable [TopologicalSpace (U × X)]
variable [Zero α] [Preorder α]
variable (A : SetRel U X)

-- Proof sketch: view the uncurried slice-wise indicator expression as the indicator of the graph
-- set `A ⊆ U × X`. For indicator functions, lower semicontinuity is equivalent to closedness of
-- the underlying set, so the closedness of the bifunction is exactly closedness of the graph of
-- `A`.
/-- The indicator bifunction is closed exactly when the graph of the underlying process is
closed. -/
private theorem lowerSemicontinuous_indicator_graph_iff_isClosed :
    LowerSemicontinuous (δ[α](· | (A : Set (U × X)))) ↔
      A.IsClosed := sorry

/-- Bridge form of `lowerSemicontinuous_indicator_graph_iff_isClosed` on
`indicatorFibers α A`, stated on the canonical Chapter 6 surface `closedᵇ(·)`. -/
theorem lowerSemicontinuous_uncurry_indicatorFibers_iff_isClosed :
    closedᵇ(indicatorFibers α A) ↔
      A.IsClosed := by
  simpa [uncurry_indicatorFibers_eq_indicator (α := α) (A := A)] using
    (lowerSemicontinuous_indicator_graph_iff_isClosed (α := α) (A := A))

end Closed

end SetRel

/-! ### Definition_39_0_14 (from Chap08) -/
noncomputable section

universe u v w z ℓ

open scoped Rockafellar SetRel

namespace SetRel

/-!
Source/core/bridge triage:

- `source-facing`: Definition 39.0.14 introduces the adjoint `A*` of an oriented convex process by
  the fiberwise pairing inequality `⟪u, u⋆⟫ ≥ ⟪x, x⋆⟫` for every graph point `(u, x)` of `A`.
- `core/canonical`: the chapter already owns convex processes on the relation owner
  `A : SetRel U X`, and the present item uses the canonical pairing owner
  `HasPairing U UStar L` and `HasPairing X XStar L` from `Chap01.HasPairing`.
- `bridge/view`: the parenthetical infimum-oriented clause is not a second owner here; it is the
  same relation-level owner read in the order-dual codomain `Lᵒᵈ`, where the displayed inequality
  is automatically reversed.

Primary mathematical domain:
- convex processes and pairing-based adjoint relations.

Domain-style sampling used here:
- `SetRel` from `Mathlib.Data.Rel` as the canonical graph owner;
- the canonical pairing owner `HasPairing` and its order-dual lift;
- `SetRel.IsConvexProcess` from `Chap08.Definition_39_0_1`, which shows that Chapter 39 already
  treats convex processes directly as relations rather than through a wrapper structure.

Primitive data vs derived API:
- primitive source data: a relation `A : SetRel U X`;
- primitive owner introduced here:
  `SetRel.adjoint (XStar := XStar) (UStar := UStar) (L := L) A : SetRel XStar UStar`;
- derived API: the pointwise membership criterion `mem_adjoint_iff`.

Owner and notation decision:
- the raw owner is `SetRel.adjoint`, not a new packaged “adjoint process” structure;
- the source-facing operator notation is the lightweight `Rockafellar`-scoped notation
  `A∗[XStar, UStar; L]` (explicit dual carriers) together with the low-noise notation `A∗[L]`
  when the surrounding context already fixes the dual carriers; both expand directly to the same
  canonical raw owner
  `SetRel.adjoint (XStar := XStar) (UStar := UStar) (L := L) A`
  (no wrapper owner and no macro parser layer);
- the dual carrier types `XStar`, `UStar` and the pairing codomain `L` are core owner
  parameters and are therefore explicit on the owner surface (typically via named arguments),
  since they are not recoverable from `A : SetRel U X` alone.

Layer target: `source-facing`, stated directly on the canonical relation owner with explicit dual
space parameters, since those parameters are not recoverable from `A : SetRel U X` alone.
-/

section Adjoint

variable {U : Type u} {X : Type v} {XStar : Type w} {UStar : Type z} {L : Type ℓ}
variable [LE L]
variable [HasPairing U UStar L] [HasPairing X XStar L]

/-- Definition 39.0.14: for a supremum-oriented convex process `A`, its adjoint `A*` is the
relation on dual points `(x⋆, u⋆)` cut out by the inequalities `⟪u, u⋆⟫ ≥ ⟪x, x⋆⟫` for every
graph point `(u, x)` of `A`. The parenthetical infimum-oriented clause is recovered by reading
the same owner in the order-dual codomain `Lᵒᵈ`, which reverses the inequality. -/
def adjoint (A : SetRel U X) : SetRel XStar UStar :=
  { p : XStar × UStar | ∀ ⦃u : U⦄ ⦃x : X⦄, u ~[A] x → (⟪u, p.2⟫ₚ : L) ≥ ⟪x, p.1⟫ₚ }

/-- Canonical theorem-surface notation for Definition 39.0.14:
`A∗[L]` denotes the process adjoint relation in pairing codomain `L`.
When typeclass inference needs help fixing dual carriers, use the explicit disambiguation form
`A∗[XStar, UStar; L]`. -/
scoped[Rockafellar] notation:100 A "∗[" K "]" =>
  SetRel.adjoint (L := K) A
scoped[Rockafellar] notation:100 A "∗[" Xs ", " Us "; " K "]" =>
  SetRel.adjoint (XStar := Xs) (UStar := Us) (L := K) A

/-- Evaluating the adjoint relation at `(x⋆, u⋆)` is exactly the defining universal pairing
inequality against every graph point of `A`. -/
@[simp] theorem mem_adjoint_iff (A : SetRel U X) {xStar : XStar} {uStar : UStar} :
    xStar ~[A∗[L]] uStar ↔
      ∀ ⦃u : U⦄ ⦃x : X⦄, u ~[A] x → (⟪u, uStar⟫ₚ : L) ≥ ⟪x, xStar⟫ₚ := Iff.rfl

/-- Reading `SetRel.adjoint` in the order-dual codomain `Lᵒᵈ` gives the infimum-oriented branch
of Definition 39.0.14, where the defining inequality is reversed. -/
-- Proof sketch: apply `mem_adjoint_iff` in the order-dual codomain; the order dual turns `≥`
-- in `Lᵒᵈ` into `≤` in `L`.
@[simp] theorem mem_adjoint_orderDual_iff (A : SetRel U X) {xStar : XStar} {uStar : UStar} :
    xStar ~[A∗[Lᵒᵈ]] uStar ↔
      ∀ ⦃u : U⦄ ⦃x : X⦄, u ~[A] x → (⟪u, uStar⟫ₚ : L) ≤ ⟪x, xStar⟫ₚ := Iff.rfl

end Adjoint

end SetRel

/-! ### Proposition_39_0_15 (from Chap08) -/
noncomputable section

open scoped Rockafellar SetRel InnerProduct

universe u v w z ℓ

namespace SetRel

/-!
Source/core/bridge triage:

- `source-facing`: Proposition 39.0.15 states that process adjunction commutes with relation
  inverse, and that for an actual linear transformation this process adjoint recovers the usual
  Hilbert-space adjoint operator.
- `core/canonical`: the chapter already owns the process adjoint as `SetRel.adjoint` with notation
  `A∗[...]`, the inverse relation as `SetRel.inv` with notation `A⁻¹`, and single-valued maps as
  relation graphs `Function.graph`.
- `bridge/view`: the second clause is a bridge from the relation-level adjoint owner to the
  linear-algebra owner `ContinuousLinearMap.adjoint`.

Primary mathematical domain:
- convex processes and pairing-based adjoint relations.

Domain-style sampling used here:
- `SetRel.adjoint` and `SetRel.mem_adjoint_iff` from `Definition_39_0_14`;
- `SetRel.inv` and `SetRel.mem_inv` from `Definition_26_0_2` / mathlib;
- `Function.graph` from `Mathlib.Data.Rel`;
- `ContinuousLinearMap.adjoint` and `ContinuousLinearMap.adjoint_inner_left` from mathlib's
  inner-product API.

Primitive data vs derived API:
- primitive owner data: a relation `A : SetRel U X`;
- primitive source operators: inverse and adjoint on relation graphs;
- derived bridge: when `A` is the graph of a linear map, the adjoint relation is again a graph,
  namely the graph of the usual Hilbert-space adjoint operator.

Layer target:
- clause (1) is a direct owner-level identity on relations and pairings;
- clause (2) is a bridge from the source relation owner to the canonical bounded-operator owner.

Redundant-assumption note:
- the source phrases clause (1) for oriented convex processes, but the inverse/adjoint commutation
  law depends only on the relation and the pairing data, so no convex-process hypothesis is kept in
  the public statement.
-/

section InverseAdjoint

variable {U : Type u} {X : Type v} {XStar : Type w} {UStar : Type z} {L : Type ℓ}
variable [LE L]
variable [HasPairing U UStar L] [HasPairing X XStar L]

-- Proof sketch: ext on a dual pair `(u⋆, x⋆)` and rewrite both sides with `SetRel.mem_inv` and
-- `mem_adjoint_iff`. After swapping the graph variables of `A`, the two universal pairing
-- inequalities are definitionally the same.
/-- Proposition 39.0.15 (1): the inverse of the process adjoint equals the adjoint of the inverse
relation. The convex-process hypothesis from the source is redundant for this relation identity, so
the statement is given directly on the canonical relation owner. -/
theorem inv_adjoint_eq_adjoint_inv
    (A : SetRel U X) :
    (A∗[XStar, UStar; L])⁻¹ = (A⁻¹)∗[UStar, XStar; L] := sorry

end InverseAdjoint

section ContinuousLinearMapBridge

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [CompleteSpace E]
variable {F : Type v} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
variable [CompleteSpace F]

-- Proof sketch: ext on a pair `(y, x)` in `F × E`. Membership in the adjoint of
-- `Function.graph A` says that `⟪u, x⟫ ≥ ⟪A u, y⟫` for every `u`; replacing `u` by `-u` forces
-- equality for all `u`. The defining property of `ContinuousLinearMap.adjoint`, via
-- `ContinuousLinearMap.adjoint_inner_left`, then identifies this with `x = (A†) y`.
/-- Proposition 39.0.15 (2): when the process is the graph of a continuous linear map, its process
adjoint is
exactly the graph of the usual Hilbert-space adjoint operator. -/
theorem adjoint_graph_eq_graph_adjoint
    (A : E →L[ℝ] F) :
    (Function.graph A)∗[ℝ] = Function.graph (A†) := sorry

end ContinuousLinearMapBridge

end SetRel
