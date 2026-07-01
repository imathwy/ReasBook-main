import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap08.Theorem_38_4
import ConvexAnalysis_Rockafellar_1970.Chap08.Proposition_39_0_13

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
