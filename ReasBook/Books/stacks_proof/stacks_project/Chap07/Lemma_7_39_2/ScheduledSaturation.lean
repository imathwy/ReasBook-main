import StacksProject_2024.Chap07.Lemma_7_39_2.PackagedStages

/-
The former aggregate module carried an abandoned exact open-prefix saturation route.  This
item keeps only the constant `SaturationDiagram` adapter and the finite frontier construction,
so the proof avoids the heavier open-tower equivalence layer.
-/

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

section Diagram

variable {M : Type w}

local notation "Ω" => WithBot M

/-- Helper for Chap07 Lemma 7 39 2/ScheduledSaturation: a global bottom-indexed saturation
diagram for a fixed request enumeration on one packaged stage. Each concrete request is
realized at its own scheduled node, and the `fromBase` maps keep all nodes as compatible
refinements of the original stage. -/
structure SaturationDiagram
    (A : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (req : M → finite_cover_lift_request J A.T) where
  stage : Ω → refinement_stage (J := J) S' (ℱ := ℱ) s s'
  fromBase : ∀ x : Ω, refinement_stage_hom (J := J) A (stage x)
  fromBase_compatible : ∀ x : Ω, (fromBase x).original_compatible
  realizes_at :
    ∀ m : M, request_realized (J := J) ((fromBase (m : Ω)).map_request (req m))

namespace SaturationDiagram

variable {A : refinement_stage (J := J) S' (ℱ := ℱ) s s'}
variable {req : M → finite_cover_lift_request J A.T}

/-- Helper for Chap07 Lemma 7 39 2/ScheduledSaturation: one compatible refinement stage
realizing every scheduled request gives the constant bottom-indexed saturation diagram. -/
theorem nonempty_of_stage_realizing_all
    (B : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (h : refinement_stage_hom (J := J) A B) (hcompat : h.original_compatible)
    (hreal : ∀ m : M, request_realized (J := J) (h.map_request (req m))) :
    Nonempty (SaturationDiagram (J := J) A req) := by
  -- Use `B` at every schedule node and the fixed compatible map from the base stage.
  refine ⟨
    { stage := fun _ => B
      fromBase := fun _ => h
      fromBase_compatible := ?_
      realizes_at := ?_ }⟩
  · intro x
    exact hcompat
  · intro m
    exact hreal m

end SaturationDiagram

end Diagram

variable [Limits.HasPullbacks C]
variable {M : Type w} [LinearOrder M] [WellFoundedLT M] [SuccOrder (WithBot M)] [Finite M]

/-- Helper for Chap07 Lemma 7 39 2/ScheduledSaturation: a finite list of a prescribed length
of requests on one packaged stage is realized after one compatible further refinement. -/
lemma existsCompatibleStageRealizingListOfLength
    (n : Nat)
    (A : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (rs : List (finite_cover_lift_request J A.T)) (hlen : rs.length = n) :
    ∃ B : refinement_stage (J := J) S' (ℱ := ℱ) s s',
      ∃ h : refinement_stage_hom (J := J) A B,
        h.original_compatible ∧
          ∀ ⦃r : finite_cover_lift_request J A.T⦄, r ∈ rs →
            request_realized (J := J) (h.map_request r) := by
  induction n generalizing A with
  | zero =>
      cases rs with
      | nil =>
          refine ⟨A, refinement_stage_hom_refl (J := J) A, ?_, ?_⟩
          · exact refinement_stage_hom.original_compatible_refl A
          · intro r hr
            cases hr
      | cons r rs =>
          cases hlen
  | succ n ih =>
      cases rs with
      | nil =>
          cases hlen
      | cons r rs =>
          rcases extend_stage_by_request_original_compatible (J := J) A r with
            ⟨B₁, h₁, hsolved₁, hcompat₁⟩
          have hlen_tail : rs.length = n := Nat.succ.inj hlen
          rcases ih B₁ (rs.map h₁.map_request)
              (by simpa [List.length_map] using hlen_tail) with
            ⟨B₂, h₂, hcompat₂, hreal₂⟩
          refine ⟨B₂, refinement_stage_hom.comp (J := J) h₁ h₂, ?_, ?_⟩
          · -- Compatibility is preserved when the successor morphism is followed by the tail
            -- frontier morphism.
            exact refinement_stage_hom.original_compatible_comp h₁ h₂ hcompat₁ hcompat₂
          · intro r₀ hr₀
            rcases List.mem_cons.mp hr₀ with hhead | htail
            · -- The head request is solved at `B₁` and remains realized after transport to `B₂`.
              have hreal₁ : request_realized (J := J) (h₁.map_request r₀) := by
                rw [hhead]
                exact B₁.solved_realized hsolved₁
              have hreal₁₂ :
                  request_realized (J := J) (h₂.map_request (h₁.map_request r₀)) :=
                refinement_stage_hom.map_request_realized (J := J) h₂ (h₁.map_request r₀)
                  hreal₁
              simpa [refinement_stage_hom.map_request_comp] using hreal₁₂
            · -- Each tail request was included in the recursively solved transported tail list.
              have hmem : h₁.map_request r₀ ∈ rs.map h₁.map_request :=
                List.mem_map_of_mem (f := h₁.map_request) htail
              have hreal_tail :
                  request_realized (J := J) (h₂.map_request (h₁.map_request r₀)) :=
                hreal₂ hmem
              simpa [refinement_stage_hom.map_request_comp] using hreal_tail

/-- Helper for Chap07 Lemma 7 39 2/ScheduledSaturation: a finite list of requests on one
packaged stage is realized after one compatible further refinement. -/
theorem existsCompatibleStageRealizingList
    (A : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (rs : List (finite_cover_lift_request J A.T)) :
    ∃ B : refinement_stage (J := J) S' (ℱ := ℱ) s s',
      ∃ h : refinement_stage_hom (J := J) A B,
        h.original_compatible ∧
          ∀ ⦃r : finite_cover_lift_request J A.T⦄, r ∈ rs →
            request_realized (J := J) (h.map_request r) := by
  exact existsCompatibleStageRealizingListOfLength (J := J) rs.length A rs rfl

/-- Chap07 Lemma 7 39 2/ScheduledSaturation: finite request schedules also admit a
bottom-indexed saturation diagram. -/
theorem existsSaturationDiagram_of_finite_schedule
    (A : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (req : M → finite_cover_lift_request J A.T) :
    Nonempty (SaturationDiagram (J := J) A req) := by
  have _ : WellFoundedLT M := inferInstance
  have _ : SuccOrder (WithBot M) := inferInstance
  -- Realize the finite list of scheduled requests by the finite frontier construction.
  letI : Fintype M := Fintype.ofFinite M
  let rs : List (finite_cover_lift_request J A.T) :=
    (Finset.univ : Finset M).toList.map req
  rcases existsCompatibleStageRealizingList (J := J) (S' := S') (ℱ := ℱ) A rs with
    ⟨B, h, hcompat, hreal⟩
  refine SaturationDiagram.nonempty_of_stage_realizing_all (J := J) B h hcompat ?_
  intro m
  have hm : req m ∈ rs := by
    -- Every schedule index occurs in the list underlying `Finset.univ`.
    have hmem : m ∈ (Finset.univ : Finset M).toList := by
      simpa using Finset.mem_univ m
    exact List.mem_map_of_mem (f := req) hmem
  exact hreal hm

end

end ScheduledSaturation

end CategoryTheory
