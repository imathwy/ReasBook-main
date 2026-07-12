import StacksProject_2024.Chap07.Lemma_7_39_2.PackagedStages

open CategoryTheory
open CategoryTheory.SemiRepresentableFamily.Over
open GrothendieckTopology.Point.ofIsCofiltered

universe u v w

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

attribute [local instance] initiallySmall_of_essentiallySmall

variable {J : GrothendieckTopology C}
variable {ι : Type w} [Preorder ι]

namespace ScheduledSaturation

section

variable {ℱ : Sheaf J (Type (max u v w))} {S' : ιᵒᵖ ⥤ C}
  {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
    (fiber.{max u v w} S').presheafFiber).obj ℱ}
variable {M : Type w} [Preorder M]

local notation "Ω" => WithBot M

/-- Helper for Chap07 Lemma 7 39 2/ScheduledSaturation: a global bottom-indexed saturation
diagram for a fixed request enumeration on one packaged stage.  Each concrete request is
realized at its own scheduled node, and the `fromBase` maps keep all nodes as compatible
refinements of the original stage. -/
structure SaturationDiagram
    (A : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (req : M → finite_cover_lift_request J A.T) where
  stage : Ω → refinement_stage (J := J) S' (ℱ := ℱ) s s'
  hom : ∀ ⦃x y : Ω⦄, x ≤ y → refinement_stage_hom (J := J) (stage x) (stage y)
  hom_refl :
    ∀ x : Ω, hom (show x ≤ x from le_rfl) = refinement_stage_hom_refl (J := J) (stage x)
  hom_comp :
    ∀ ⦃x y z : Ω⦄ (hxy : x ≤ y) (hyz : y ≤ z),
      hom (le_trans hxy hyz) =
        refinement_stage_hom.comp (J := J) (hom hxy) (hom hyz)
  hom_original_compatible :
    ∀ ⦃x y : Ω⦄ (hxy : x ≤ y), (hom hxy).original_compatible
  fromBase : ∀ x : Ω, refinement_stage_hom (J := J) A (stage x)
  fromBase_compatible : ∀ x : Ω, (fromBase x).original_compatible
  fromBase_comp :
    ∀ ⦃x y : Ω⦄ (hxy : x ≤ y),
      fromBase y = refinement_stage_hom.comp (J := J) (fromBase x) (hom hxy)
  realizes_at :
    ∀ m : M, request_realized (J := J) ((fromBase (m : Ω)).map_request (req m))

namespace SaturationDiagram

variable {A : refinement_stage (J := J) S' (ℱ := ℱ) s s'}
variable {req : M → finite_cover_lift_request J A.T}

/-- Helper for Chap07 Lemma 7 39 2/ScheduledSaturation: the stage function of a constant
bottom-indexed saturation diagram. -/
def constantStage
    (B : refinement_stage (J := J) S' (ℱ := ℱ) s s') :
    Ω → refinement_stage (J := J) S' (ℱ := ℱ) s s' :=
  fun _ => B

/-- Helper for Chap07 Lemma 7 39 2/ScheduledSaturation: the comparison morphisms of a
constant bottom-indexed saturation diagram. -/
noncomputable def constantHom
    (B : refinement_stage (J := J) S' (ℱ := ℱ) s s') :
    ∀ ⦃x y : Ω⦄, x ≤ y →
      refinement_stage_hom (J := J) (constantStage (J := J) B x)
        (constantStage (J := J) B y) :=
  fun {_ _} _ => refinement_stage_hom_refl (J := J) B

/-- Helper for Chap07 Lemma 7 39 2/ScheduledSaturation: the base morphisms of a constant
bottom-indexed saturation diagram. -/
def constantFromBase
    (B : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (h : refinement_stage_hom (J := J) A B) :
    ∀ x : Ω, refinement_stage_hom (J := J) A (constantStage (J := J) B x) :=
  fun _ => h

/-- Helper for Chap07 Lemma 7 39 2/ScheduledSaturation: constant comparison morphisms are
identities on each node. -/
theorem constantHom_refl
    (B : refinement_stage (J := J) S' (ℱ := ℱ) s s') :
    ∀ x : Ω,
      constantHom (J := J) B (show x ≤ x from le_rfl) =
        refinement_stage_hom_refl (J := J) (constantStage (J := J) B x) := by
  intro x
  rfl

/-- Helper for Chap07 Lemma 7 39 2/ScheduledSaturation: constant identity comparisons compose
as identity comparisons. -/
theorem constantHom_comp
    (B : refinement_stage (J := J) S' (ℱ := ℱ) s s') :
    ∀ ⦃x y z : Ω⦄ (hxy : x ≤ y) (hyz : y ≤ z),
      constantHom (J := J) B (le_trans hxy hyz) =
        refinement_stage_hom.comp (J := J) (constantHom (J := J) B hxy)
          (constantHom (J := J) B hyz) := by
  intro x y z hxy hyz
  exact (refinement_stage_hom.refl_comp (J := J) (refinement_stage_hom_refl (J := J) B)).symm

/-- Helper for Chap07 Lemma 7 39 2/ScheduledSaturation: constant identity comparisons are
compatible with the original refinement data. -/
theorem constantHom_original_compatible
    (B : refinement_stage (J := J) S' (ℱ := ℱ) s s') :
    ∀ ⦃x y : Ω⦄ (hxy : x ≤ y), (constantHom (J := J) B hxy).original_compatible := by
  intro x y hxy
  exact refinement_stage_hom.original_compatible_refl (J := J) B

omit [Preorder M] in
/-- Helper for Chap07 Lemma 7 39 2/ScheduledSaturation: constant base morphisms are compatible
whenever the fixed base morphism is compatible. -/
theorem constantFromBase_compatible
    (B : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (h : refinement_stage_hom (J := J) A B) (hcompat : h.original_compatible) :
    ∀ x : Ω, (constantFromBase (J := J) B h x).original_compatible := by
  intro x
  exact hcompat

/-- Helper for Chap07 Lemma 7 39 2/ScheduledSaturation: a constant base morphism composes
trivially with a constant identity comparison. -/
theorem constantFromBase_comp
    (B : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (h : refinement_stage_hom (J := J) A B) :
    ∀ ⦃x y : Ω⦄ (hxy : x ≤ y),
      constantFromBase (J := J) B h y =
        refinement_stage_hom.comp (J := J) (constantFromBase (J := J) B h x)
          (constantHom (J := J) B hxy) := by
  intro x y hxy
  exact (refinement_stage_hom.comp_refl (J := J) h).symm

omit [Preorder M] in
/-- Helper for Chap07 Lemma 7 39 2/ScheduledSaturation: a fixed realization hypothesis supplies
the realization field of a constant saturation diagram. -/
theorem constantRealizes_at
    (B : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (h : refinement_stage_hom (J := J) A B)
    (hreal : ∀ m : M, request_realized (J := J) (h.map_request (req m))) :
    ∀ m : M,
      request_realized (J := J)
        (((constantFromBase (J := J) B h (m : Ω))).map_request (req m)) := by
  intro m
  exact hreal m

/-- Helper for Chap07 Lemma 7 39 2/ScheduledSaturation: one compatible refinement stage
realizing every scheduled request gives the constant bottom-indexed saturation diagram. -/
theorem nonempty_of_stage_realizing_all
    (B : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (h : refinement_stage_hom (J := J) A B) (hcompat : h.original_compatible)
    (hreal : ∀ m : M, request_realized (J := J) (h.map_request (req m))) :
    Nonempty (SaturationDiagram (J := J) A req) := by
  -- Use `B` at every schedule node; all comparison morphisms are identities.
  refine ⟨
    { stage := constantStage (J := J) B
      hom := constantHom (J := J) B
      hom_refl := constantHom_refl (J := J) B
      hom_comp := constantHom_comp (J := J) B
      hom_original_compatible := constantHom_original_compatible (J := J) B
      fromBase := constantFromBase (J := J) B h
      fromBase_compatible := constantFromBase_compatible (J := J) B h hcompat
      fromBase_comp := constantFromBase_comp (J := J) B h
      realizes_at := constantRealizes_at (J := J) B h hreal }⟩

end SaturationDiagram

end

end ScheduledSaturation

end CategoryTheory
