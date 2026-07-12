import StacksProject_2024.Chap07.Lemma_7_39_2.ScheduledSaturation.LimitTransport
import StacksProject_2024.Chap07.Lemma_7_39_2.ScheduledSaturation.RecursiveNodes

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
variable [Limits.HasPullbacks C]
variable {M : Type w} [LinearOrder M] [WellFoundedLT M] [SuccOrder (WithBot M)]

local notation "Ω" => WithBot M
local notation "CutΩ" => WithTop Ω


/-- Helper for Lemma 7.39.2: a coherent saturation diagram is equivalent to a compatible
terminal stage realizing every scheduled request. -/
theorem nonempty_iff_exists_stage_realizing_all
    (A : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (req : M → finite_cover_lift_request J A.T) :
    Nonempty (SaturationDiagram (J := J) A req) ↔
      ∃ B : refinement_stage (J := J) S' (ℱ := ℱ) s s',
        ∃ h : refinement_stage_hom (J := J) A B,
          h.original_compatible ∧
            ∀ m : M, request_realized (J := J) (h.map_request (req m)) := by
  constructor
  · -- Project a saturation diagram to its directed-union terminal stage.
    intro hD
    rcases hD with ⟨D⟩
    exact exists_stage_realizing_all_of_saturationDiagram (J := J) A req D
  · -- Conversely, a terminal realizing stage gives the constant saturation diagram.
    intro hterminal
    exact SaturationDiagram.nonempty_of_exists_stage_realizing_all (J := J) hterminal

/-- Helper for Lemma 7.39.2: a coherent bottom-indexed saturation diagram gives the open-cut
tower by first taking its directed-union terminal stage and then using the constant-tower
adapter. -/
theorem OpenSaturationTower.nonempty_of_saturationDiagram
    (A : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (req : M → finite_cover_lift_request J A.T)
    (hD : Nonempty (SaturationDiagram (J := J) A req)) :
    Nonempty (OpenSaturationTower (J := J) A req) := by
  -- Project the coherent bottom-indexed diagram to its terminal realizing stage.
  rcases hD with ⟨D⟩
  rcases exists_stage_realizing_all_of_saturationDiagram (J := J) A req D with
    ⟨B, h, hcompat, hreal⟩
  -- The terminal realizing stage supports the constant open-cut tower.
  exact OpenSaturationTower.nonempty_of_stage_realizing_all (J := J) B h hcompat hreal

/-- Helper for Lemma 7.39.2: the top cut of a global open-cut tower is a compatible terminal
stage realizing every scheduled request. -/
theorem OpenSaturationTower.exists_stage_realizing_all
    (A : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (req : M → finite_cover_lift_request J A.T)
    (T : OpenSaturationTower (J := J) A req) :
    ∃ B : refinement_stage (J := J) S' (ℱ := ℱ) s s',
      ∃ h : refinement_stage_hom (J := J) A B,
        h.original_compatible ∧
          ∀ m : M, request_realized (J := J) (h.map_request (req m)) := by
  -- Project the tower at the terminal cut; every concrete request cut lies strictly below it.
  refine ⟨T.stage (⊤ : CutΩ), T.fromBase (⊤ : CutΩ),
    T.fromBase_compatible (⊤ : CutΩ), ?_⟩
  intro m
  exact T.realizes_lt (⊤ : CutΩ) m (WithTop.coe_lt_top (m : Ω))

/-- Helper for Lemma 7.39.2: an existential compatible terminal stage realizing every scheduled
request supplies the constant open-cut saturation tower. -/
theorem OpenSaturationTower.nonempty_of_exists_stage_realizing_all
    {A : refinement_stage (J := J) S' (ℱ := ℱ) s s'}
    {req : M → finite_cover_lift_request J A.T}
    (hterminal :
      ∃ B : refinement_stage (J := J) S' (ℱ := ℱ) s s',
        ∃ h : refinement_stage_hom (J := J) A B,
          h.original_compatible ∧
            ∀ m : M, request_realized (J := J) (h.map_request (req m))) :
    Nonempty (OpenSaturationTower (J := J) A req) := by
  -- Unpack the terminal compatible stage and feed it to the constant-tower adapter.
  rcases hterminal with ⟨B, h, hcompat, hreal⟩
  exact OpenSaturationTower.nonempty_of_stage_realizing_all (J := J) B h hcompat hreal

/-- Helper for Lemma 7.39.2: a global open-cut tower supplies the bottom-indexed saturation
diagram by forgetting to its terminal realizing stage. -/
theorem OpenSaturationTower.toSaturationDiagram
    (A : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (req : M → finite_cover_lift_request J A.T)
    (T : OpenSaturationTower (J := J) A req) :
    Nonempty (SaturationDiagram (J := J) A req) := by
  -- Turn the tower's top stage into the constant bottom-indexed saturation diagram.
  exact SaturationDiagram.nonempty_of_exists_stage_realizing_all (J := J)
    (OpenSaturationTower.exists_stage_realizing_all (J := J) A req T)

/-- Helper for Lemma 7.39.2: existence of a global open-cut saturation tower is equivalent to
existence of one compatible terminal stage realizing every scheduled request. -/
theorem OpenSaturationTower.nonempty_iff_exists_stage_realizing_all
    (A : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (req : M → finite_cover_lift_request J A.T) :
    Nonempty (OpenSaturationTower (J := J) A req) ↔
      ∃ B : refinement_stage (J := J) S' (ℱ := ℱ) s s',
        ∃ h : refinement_stage_hom (J := J) A B,
          h.original_compatible ∧
            ∀ m : M, request_realized (J := J) (h.map_request (req m)) := by
  constructor
  · -- Read the terminal realizing stage from the top cut of the tower.
    intro hT
    rcases hT with ⟨T⟩
    exact OpenSaturationTower.exists_stage_realizing_all (J := J) A req T
  · -- Conversely, the terminal stage gives the constant open-cut tower.
    intro hterminal
    exact OpenSaturationTower.nonempty_of_exists_stage_realizing_all (J := J) hterminal

/-- Helper for Lemma 7.39.2: the open-cut tower normal form and the bottom-indexed saturation
diagram normal form are equivalent. -/
theorem openSaturationTower_nonempty_iff_saturationDiagram_nonempty
    (A : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (req : M → finite_cover_lift_request J A.T) :
    Nonempty (OpenSaturationTower (J := J) A req) ↔
      Nonempty (SaturationDiagram (J := J) A req) := by
  constructor
  · -- Forget the open tower to the terminal stage, then to the constant saturation diagram.
    intro hT
    rcases hT with ⟨T⟩
    exact T.toSaturationDiagram (J := J) A req
  · -- A saturation diagram projects to a terminal realizing stage and hence to a constant tower.
    intro hD
    exact OpenSaturationTower.nonempty_of_saturationDiagram (J := J) A req hD

/-- Helper for Lemma 7.39.2: a finite request schedule has one compatible terminal stage
realizing every scheduled request. -/
theorem exists_stage_realizing_all_of_fintype_schedule
    [Fintype M]
    (A : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (req : M → finite_cover_lift_request J A.T) :
    ∃ B : refinement_stage (J := J) S' (ℱ := ℱ) s s',
      ∃ h : refinement_stage_hom (J := J) A B,
        h.original_compatible ∧
          ∀ m : M, request_realized (J := J) (h.map_request (req m)) := by
  let rs : List (finite_cover_lift_request J A.T) :=
    (Finset.univ : Finset M).toList.map req
  -- Realize the finite list of all scheduled requests by the existing frontier construction.
  refine ⟨listFrontierStage (J := J) A rs, listFrontierHom (J := J) A rs, ?_, ?_⟩
  · exact listFrontierHom_original_compatible (J := J) A rs
  · intro m
    have hm : req m ∈ rs := by
      -- Every schedule index occurs in the list underlying `Finset.univ`.
      exact List.mem_map_of_mem (f := req) (by simpa [rs] using Finset.mem_univ m)
    exact listFrontierHom_realizes_mem (J := J) A rs hm

/-- Helper for Lemma 7.39.2: finite schedules admit the constant open-cut tower obtained from
the finite terminal-stage frontier. -/
theorem existsOpenSaturationTower_of_fintype_schedule
    [Fintype M]
    (A : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (req : M → finite_cover_lift_request J A.T) :
    Nonempty (OpenSaturationTower (J := J) A req) := by
  -- Convert the finite terminal frontier into the already checked constant tower.
  exact OpenSaturationTower.nonempty_of_exists_stage_realizing_all (J := J)
    (exists_stage_realizing_all_of_fintype_schedule (J := J) A req)

/-- Helper for Lemma 7.39.2: a terminal open-cut node packages as one compatible stage
realizing every request in the schedule. -/
theorem compatibleStageRealizingRequestFamily_of_topOpenSaturationNode
    (A : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (req : M → finite_cover_lift_request J A.T)
    (htop :
      ∃ prevStage : {y : CutΩ // y < (⊤ : CutΩ)} →
          refinement_stage (J := J) S' (ℱ := ℱ) s s',
        ∃ prevHom :
            ∀ ⦃y z : {y : CutΩ // y < (⊤ : CutΩ)}⦄, (y : CutΩ) ≤ z →
              refinement_stage_hom (J := J) (prevStage y) (prevStage z),
          ∃ prevFromBase :
              ∀ y : {y : CutΩ // y < (⊤ : CutΩ)},
                refinement_stage_hom (J := J) A (prevStage y),
            Nonempty
              (OpenSaturationNode (J := J) A req (⊤ : CutΩ)
                prevStage prevHom prevFromBase)) :
    ∃ B : refinement_stage (J := J) S' (ℱ := ℱ) s s',
      ∃ h : refinement_stage_hom (J := J) A B,
        h.original_compatible ∧
          ∀ m : M, request_realized (J := J) (h.map_request (req m)) := by
  -- Unpack the terminal node data and use its checked top-cut projection theorem.
  rcases htop with ⟨prevStage, prevHom, prevFromBase, hN⟩
  rcases hN with ⟨N⟩
  exact N.exists_stage_realizing_all_of_top

/-- Helper for Lemma 7.39.2: a terminal open-cut prefix packages as one compatible stage
realizing every request in the schedule. -/
theorem compatibleStageRealizingRequestFamily_of_topOpenSaturationPrefix
    (A : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (req : M → finite_cover_lift_request J A.T)
    (hP : Nonempty (OpenSaturationPrefix (J := J) A req (⊤ : CutΩ))) :
    ∃ B : refinement_stage (J := J) S' (ℱ := ℱ) s s',
      ∃ h : refinement_stage_hom (J := J) A B,
        h.original_compatible ∧
          ∀ m : M, request_realized (J := J) (h.map_request (req m)) := by
  -- Read the terminal top stage from the prefix; the open invariant realizes every concrete cut
  -- because each concrete request cut lies strictly below `⊤`.
  rcases hP with ⟨P⟩
  exact OpenSaturationPrefix.top_yields_exists_stage_realizing_all (J := J) P
end

end ScheduledSaturation

end CategoryTheory
