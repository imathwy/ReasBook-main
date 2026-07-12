import StacksProject_2024.Chap07.Lemma_7_39_2.ScheduledSaturation.Prefixes

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


/-- Helper for Lemma 7.39.2: one bottom-indexed recursive request-saturation node stores the
current stage, maps from all strict predecessor nodes, and realization of all requests at or below
the current concrete schedule node.  Coherence is recorded at the transported-request level, which
is the stable normal form for direct-union inclusions. -/
structure RequestSaturationNode
    (A : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (req : M → finite_cover_lift_request J A.T) (x : Ω)
    (prevStage : {y : Ω // y < x} →
      refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (prevHom : ∀ ⦃y z : {y : Ω // y < x}⦄, (y : Ω) ≤ z →
      refinement_stage_hom (J := J) (prevStage y) (prevStage z))
    (prevFromBase : ∀ y : {y : Ω // y < x},
      refinement_stage_hom (J := J) A (prevStage y)) where
  stage : refinement_stage (J := J) S' (ℱ := ℱ) s s'
  homFrom :
    ∀ y : {y : Ω // y < x}, refinement_stage_hom (J := J) (prevStage y) stage
  homFrom_compatible : ∀ y : {y : Ω // y < x}, (homFrom y).original_compatible
  homFrom_map_request_comp :
    ∀ ⦃y z : {y : Ω // y < x}⦄ (hyz : (y : Ω) ≤ z)
      (r : finite_cover_lift_request J (prevStage y).T),
        (homFrom y).map_request r =
          (homFrom z).map_request ((prevHom hyz).map_request r)
  fromBase : refinement_stage_hom (J := J) A stage
  fromBase_compatible : fromBase.original_compatible
  fromBase_map_request_comp :
    ∀ (y : {y : Ω // y < x}) (r : finite_cover_lift_request J A.T),
      fromBase.map_request r = (homFrom y).map_request ((prevFromBase y).map_request r)
  realizes_le :
    ∀ m : M, (m : Ω) ≤ x →
      request_realized (J := J) (fromBase.map_request (req m))

/-- Helper for Lemma 7.39.2: the bottom request-saturation node is the original stage, since no
concrete request is at or below the adjoined bottom node. -/
theorem requestSaturationNode_nonempty_bot
    {A : refinement_stage (J := J) S' (ℱ := ℱ) s s'}
    {req : M → finite_cover_lift_request J A.T}
    (prevStage : {y : Ω // y < (⊥ : Ω)} →
      refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (prevHom : ∀ ⦃y z : {y : Ω // y < (⊥ : Ω)}⦄, (y : Ω) ≤ z →
      refinement_stage_hom (J := J) (prevStage y) (prevStage z))
    (prevFromBase : ∀ y : {y : Ω // y < (⊥ : Ω)},
      refinement_stage_hom (J := J) A (prevStage y)) :
    Nonempty (RequestSaturationNode (J := J) A req (⊥ : Ω)
      prevStage prevHom prevFromBase) := by
  -- At the bottom cut there are no strict predecessor nodes, so all predecessor-map fields are
  -- discharged by contradiction and the current stage is just the base stage.
  refine ⟨
    { stage := A
      homFrom := ?_
      homFrom_compatible := ?_
      homFrom_map_request_comp := ?_
      fromBase := refinement_stage_hom_refl (J := J) A
      fromBase_compatible := refinement_stage_hom.original_compatible_refl (J := J) A
      fromBase_map_request_comp := ?_
      realizes_le := ?_ }⟩
  · intro y
    exact False.elim ((not_lt_of_ge (bot_le : (⊥ : Ω) ≤ y.1)) y.2)
  · intro y
    exact False.elim ((not_lt_of_ge (bot_le : (⊥ : Ω) ≤ y.1)) y.2)
  · intro y z hyz r
    exact False.elim ((not_lt_of_ge (bot_le : (⊥ : Ω) ≤ y.1)) y.2)
  · intro y r
    exact False.elim ((not_lt_of_ge (bot_le : (⊥ : Ω) ≤ y.1)) y.2)
  · intro m hm
    -- A concrete request node is strictly above `⊥`, contradicting `m ≤ ⊥`.
    exact False.elim ((not_lt_of_ge hm) (WithBot.bot_lt_coe m))

/-- Helper for Lemma 7.39.2: a request-saturation node realizes every request indexed by a
strict predecessor of the node. -/
theorem RequestSaturationNode.realizes_of_lt
    {A : refinement_stage (J := J) S' (ℱ := ℱ) s s'}
    {req : M → finite_cover_lift_request J A.T} {x : Ω}
    {prevStage : {y : Ω // y < x} →
      refinement_stage (J := J) S' (ℱ := ℱ) s s'}
    {prevHom : ∀ ⦃y z : {y : Ω // y < x}⦄, (y : Ω) ≤ z →
      refinement_stage_hom (J := J) (prevStage y) (prevStage z)}
    {prevFromBase : ∀ y : {y : Ω // y < x},
      refinement_stage_hom (J := J) A (prevStage y)}
    (N : RequestSaturationNode (J := J) A req x prevStage prevHom prevFromBase)
    (m : M) (hm : (m : Ω) < x) :
    request_realized (J := J) (N.fromBase.map_request (req m)) := by
  -- The node invariant is stored for closed cuts; strict membership supplies that hypothesis.
  exact N.realizes_le m (le_of_lt hm)

/-- Helper for Lemma 7.39.2: request-level coherence in a request-saturation node transports
realization from a later predecessor comparison to an earlier predecessor inclusion. -/
theorem RequestSaturationNode.homFrom_realizes_of_le
    {A : refinement_stage (J := J) S' (ℱ := ℱ) s s'}
    {req : M → finite_cover_lift_request J A.T} {x : Ω}
    {prevStage : {y : Ω // y < x} →
      refinement_stage (J := J) S' (ℱ := ℱ) s s'}
    {prevHom : ∀ ⦃y z : {y : Ω // y < x}⦄, (y : Ω) ≤ z →
      refinement_stage_hom (J := J) (prevStage y) (prevStage z)}
    {prevFromBase : ∀ y : {y : Ω // y < x},
      refinement_stage_hom (J := J) A (prevStage y)}
    (N : RequestSaturationNode (J := J) A req x prevStage prevHom prevFromBase)
    {y z : {y : Ω // y < x}} (hyz : (y : Ω) ≤ z)
    {r : finite_cover_lift_request J (prevStage y).T}
    (hreal : request_realized (J := J) ((prevHom hyz).map_request r)) :
    request_realized (J := J) ((N.homFrom y).map_request r) := by
  -- Move the later-predecessor realization across the current node's comparison map.
  have htransport :
      request_realized (J := J)
        ((N.homFrom z).map_request ((prevHom hyz).map_request r)) :=
    refinement_stage_hom.map_request_realized (J := J) (N.homFrom z)
      ((prevHom hyz).map_request r) hreal
  -- The node's request-level coherence rewrites that transport as the earlier inclusion.
  rwa [N.homFrom_map_request_comp hyz r]

/-- Helper for Lemma 7.39.2: realization stored in a request-saturation node is preserved after
mapping the node to any later packaged refinement stage. -/
theorem RequestSaturationNode.realizes_map_of_le
    {A B : refinement_stage (J := J) S' (ℱ := ℱ) s s'}
    {req : M → finite_cover_lift_request J A.T} {x : Ω}
    {prevStage : {y : Ω // y < x} →
      refinement_stage (J := J) S' (ℱ := ℱ) s s'}
    {prevHom : ∀ ⦃y z : {y : Ω // y < x}⦄, (y : Ω) ≤ z →
      refinement_stage_hom (J := J) (prevStage y) (prevStage z)}
    {prevFromBase : ∀ y : {y : Ω // y < x},
      refinement_stage_hom (J := J) A (prevStage y)}
    (N : RequestSaturationNode (J := J) A req x prevStage prevHom prevFromBase)
    (g : refinement_stage_hom (J := J) N.stage B) (m : M) (hm : (m : Ω) ≤ x) :
    request_realized (J := J)
      ((refinement_stage_hom.comp (J := J) N.fromBase g).map_request (req m)) := by
  -- First use the node's realization field, then transport it through the later morphism.
  have hbase : request_realized (J := J) (N.fromBase.map_request (req m)) :=
    N.realizes_le m hm
  have hlater :
      request_realized (J := J) (g.map_request (N.fromBase.map_request (req m))) :=
    refinement_stage_hom.map_request_realized (J := J) g (N.fromBase.map_request (req m))
      hbase
  simpa [refinement_stage_hom.map_request_comp] using hlater

/-- Helper for Lemma 7.39.2: if a predecessor base map realizes a request, then the current
request-saturation node realizes the same request through its stored predecessor comparison map. -/
theorem RequestSaturationNode.realizes_of_prev_realizes
    {A : refinement_stage (J := J) S' (ℱ := ℱ) s s'}
    {req : M → finite_cover_lift_request J A.T} {x : Ω}
    {prevStage : {y : Ω // y < x} →
      refinement_stage (J := J) S' (ℱ := ℱ) s s'}
    {prevHom : ∀ ⦃y z : {y : Ω // y < x}⦄, (y : Ω) ≤ z →
      refinement_stage_hom (J := J) (prevStage y) (prevStage z)}
    {prevFromBase : ∀ y : {y : Ω // y < x},
      refinement_stage_hom (J := J) A (prevStage y)}
    (N : RequestSaturationNode (J := J) A req x prevStage prevHom prevFromBase)
    (y : {y : Ω // y < x}) (m : M)
    (hreal : request_realized (J := J) ((prevFromBase y).map_request (req m))) :
    request_realized (J := J) (N.fromBase.map_request (req m)) := by
  -- Transport the predecessor realization across the stored map into the current node.
  have htransport :
      request_realized (J := J)
        ((N.homFrom y).map_request ((prevFromBase y).map_request (req m))) :=
    refinement_stage_hom.map_request_realized (J := J) (N.homFrom y)
      ((prevFromBase y).map_request (req m)) hreal
  -- The node stores exactly the request-level base-map comparison needed here.
  rw [N.fromBase_map_request_comp y (req m)]
  exact htransport

/-- Helper for Lemma 7.39.2: a request-saturation node whose cut bounds every scheduled
request supplies a compatible terminal stage realizing the whole request family. -/
theorem RequestSaturationNode.exists_stage_realizing_all_of_bounds
    {A : refinement_stage (J := J) S' (ℱ := ℱ) s s'}
    {req : M → finite_cover_lift_request J A.T} {x : Ω}
    {prevStage : {y : Ω // y < x} →
      refinement_stage (J := J) S' (ℱ := ℱ) s s'}
    {prevHom : ∀ ⦃y z : {y : Ω // y < x}⦄, (y : Ω) ≤ z →
      refinement_stage_hom (J := J) (prevStage y) (prevStage z)}
    {prevFromBase : ∀ y : {y : Ω // y < x},
      refinement_stage_hom (J := J) A (prevStage y)}
    (N : RequestSaturationNode (J := J) A req x prevStage prevHom prevFromBase)
    (hx : ∀ m : M, (m : Ω) ≤ x) :
    ∃ B : refinement_stage (J := J) S' (ℱ := ℱ) s s',
      ∃ h : refinement_stage_hom (J := J) A B,
        h.original_compatible ∧
          ∀ m : M, request_realized (J := J) (h.map_request (req m)) := by
  -- Project the terminal data stored in the node and use the bound to activate `realizes_le`.
  refine ⟨N.stage, N.fromBase, N.fromBase_compatible, ?_⟩
  intro m
  exact N.realizes_le m (hx m)

/-- Helper for Lemma 7.39.2: one recursive open-cut node stores the current stage together
with maps from all already-built strict predecessor stages into it. -/
structure OpenSaturationNode
    (A : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (req : M → finite_cover_lift_request J A.T) (x : CutΩ)
    (prevStage : {y : CutΩ // y < x} →
      refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (prevHom : ∀ ⦃y z : {y : CutΩ // y < x}⦄, (y : CutΩ) ≤ z →
      refinement_stage_hom (J := J) (prevStage y) (prevStage z))
    (prevFromBase : ∀ y : {y : CutΩ // y < x},
      refinement_stage_hom (J := J) A (prevStage y)) where
  stage : refinement_stage (J := J) S' (ℱ := ℱ) s s'
  homFrom :
    ∀ y : {y : CutΩ // y < x}, refinement_stage_hom (J := J) (prevStage y) stage
  homFrom_compatible : ∀ y : {y : CutΩ // y < x}, (homFrom y).original_compatible
  homFrom_comp :
    ∀ ⦃y z : {y : CutΩ // y < x}⦄ (hyz : (y : CutΩ) ≤ z),
      homFrom y = refinement_stage_hom.comp (J := J) (prevHom hyz) (homFrom z)
  fromBase : refinement_stage_hom (J := J) A stage
  fromBase_compatible : fromBase.original_compatible
  fromBase_comp :
    ∀ y : {y : CutΩ // y < x},
      fromBase = refinement_stage_hom.comp (J := J) (prevFromBase y) (homFrom y)
  realizes_lt :
    ∀ m : M, ((m : Ω) : CutΩ) < x →
      request_realized (J := J) (fromBase.map_request (req m))

/-- Helper for Lemma 7.39.2: the recursive open-cut node at a minimal cut is the original
stage, since both predecessor-map and realization obligations are empty. -/
theorem openSaturationNode_nonempty_of_isMin
    {A : refinement_stage (J := J) S' (ℱ := ℱ) s s'}
    {req : M → finite_cover_lift_request J A.T} {x : CutΩ} (hx : IsMin x)
    (prevStage : {y : CutΩ // y < x} →
      refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (prevHom : ∀ ⦃y z : {y : CutΩ // y < x}⦄, (y : CutΩ) ≤ z →
      refinement_stage_hom (J := J) (prevStage y) (prevStage z))
    (prevFromBase : ∀ y : {y : CutΩ // y < x},
      refinement_stage_hom (J := J) A (prevStage y)) :
    Nonempty (OpenSaturationNode (J := J) A req x prevStage prevHom prevFromBase) := by
  -- At a minimal cut every strict-predecessor field is eliminated by order-theoretic
  -- impossibility, so the original stage and identity base map form the node.
  refine ⟨
    { stage := A
      homFrom := ?_
      homFrom_compatible := ?_
      homFrom_comp := ?_
      fromBase := refinement_stage_hom_refl (J := J) A
      fromBase_compatible := refinement_stage_hom.original_compatible_refl (J := J) A
      fromBase_comp := ?_
      realizes_lt := ?_ }⟩
  · intro y
    exact False.elim (not_lt_of_isMin_cut (M := M) hx y.2)
  · intro y
    exact False.elim (not_lt_of_isMin_cut (M := M) hx y.2)
  · intro y z hyz
    exact False.elim (not_lt_of_isMin_cut (M := M) hx y.2)
  · intro y
    exact False.elim (not_lt_of_isMin_cut (M := M) hx y.2)
  · intro m hm
    exact False.elim (not_lt_of_isMin_cut (M := M) hx hm)

/-- Helper for Lemma 7.39.2: an open-cut node packages one compatible stage realizing every
scheduled request strictly below its cut. -/
theorem OpenSaturationNode.exists_stage_realizing_lt
    {A : refinement_stage (J := J) S' (ℱ := ℱ) s s'}
    {req : M → finite_cover_lift_request J A.T} {x : CutΩ}
    {prevStage : {y : CutΩ // y < x} →
      refinement_stage (J := J) S' (ℱ := ℱ) s s'}
    {prevHom : ∀ ⦃y z : {y : CutΩ // y < x}⦄, (y : CutΩ) ≤ z →
      refinement_stage_hom (J := J) (prevStage y) (prevStage z)}
    {prevFromBase : ∀ y : {y : CutΩ // y < x},
      refinement_stage_hom (J := J) A (prevStage y)}
    (N : OpenSaturationNode (J := J) A req x prevStage prevHom prevFromBase) :
    ∃ B : refinement_stage (J := J) S' (ℱ := ℱ) s s',
      ∃ h : refinement_stage_hom (J := J) A B,
        h.original_compatible ∧
          ∀ m : M, ((m : Ω) : CutΩ) < x →
            request_realized (J := J) (h.map_request (req m)) := by
  -- Project the node's current stage and base map; its invariant is already exactly the
  -- open-cut realization statement.
  refine ⟨N.stage, N.fromBase, N.fromBase_compatible, ?_⟩
  intro m hm
  exact N.realizes_lt m hm

/-- Helper for Lemma 7.39.2: an open-cut node gives the constant open-cut prefix at the same
cut by forgetting its predecessor comparison data. -/
theorem OpenSaturationNode.nonempty_openSaturationPrefix
    {A : refinement_stage (J := J) S' (ℱ := ℱ) s s'}
    {req : M → finite_cover_lift_request J A.T} {x : CutΩ}
    {prevStage : {y : CutΩ // y < x} →
      refinement_stage (J := J) S' (ℱ := ℱ) s s'}
    {prevHom : ∀ ⦃y z : {y : CutΩ // y < x}⦄, (y : CutΩ) ≤ z →
      refinement_stage_hom (J := J) (prevStage y) (prevStage z)}
    {prevFromBase : ∀ y : {y : CutΩ // y < x},
      refinement_stage_hom (J := J) A (prevStage y)}
    (N : OpenSaturationNode (J := J) A req x prevStage prevHom prevFromBase) :
    Nonempty (OpenSaturationPrefix (J := J) A req x) := by
  -- Use the node's projected realizing stage as a constant prefix over the closed cut.
  exact OpenSaturationPrefix.nonempty_of_stage_realizing_lt (J := J) N.stage N.fromBase
    N.fromBase_compatible N.realizes_lt

/-- Helper for Lemma 7.39.2: a recursive open-cut node at the terminal cut is already one
compatible terminal stage realizing every scheduled request. -/
theorem OpenSaturationNode.exists_stage_realizing_all_of_top
    {A : refinement_stage (J := J) S' (ℱ := ℱ) s s'}
    {req : M → finite_cover_lift_request J A.T}
    {prevStage : {y : CutΩ // y < (⊤ : CutΩ)} →
      refinement_stage (J := J) S' (ℱ := ℱ) s s'}
    {prevHom : ∀ ⦃y z : {y : CutΩ // y < (⊤ : CutΩ)}⦄, (y : CutΩ) ≤ z →
      refinement_stage_hom (J := J) (prevStage y) (prevStage z)}
    {prevFromBase : ∀ y : {y : CutΩ // y < (⊤ : CutΩ)},
      refinement_stage_hom (J := J) A (prevStage y)}
    (N : OpenSaturationNode (J := J) A req (⊤ : CutΩ) prevStage prevHom prevFromBase) :
    ∃ B : refinement_stage (J := J) S' (ℱ := ℱ) s s',
      ∃ h : refinement_stage_hom (J := J) A B,
        h.original_compatible ∧
          ∀ m : M, request_realized (J := J) (h.map_request (req m)) := by
  -- First project the node to the open-cut realization statement, then specialize it at the
  -- terminal cut where every concrete request cut is strictly below top.
  rcases N.exists_stage_realizing_lt (J := J) with ⟨B, h, hcompat, hreal⟩
  refine ⟨B, h, hcompat, ?_⟩
  intro m
  exact hreal m (WithTop.coe_lt_top (m : Ω))

/-- Helper for Lemma 7.39.2: realization stored in an open-cut node is preserved after
mapping that node to any later packaged refinement stage. -/
theorem OpenSaturationNode.realizes_map_of_lt
    {A B : refinement_stage (J := J) S' (ℱ := ℱ) s s'}
    {req : M → finite_cover_lift_request J A.T} {x : CutΩ}
    {prevStage : {y : CutΩ // y < x} →
      refinement_stage (J := J) S' (ℱ := ℱ) s s'}
    {prevHom : ∀ ⦃y z : {y : CutΩ // y < x}⦄, (y : CutΩ) ≤ z →
      refinement_stage_hom (J := J) (prevStage y) (prevStage z)}
    {prevFromBase : ∀ y : {y : CutΩ // y < x},
      refinement_stage_hom (J := J) A (prevStage y)}
    (N : OpenSaturationNode (J := J) A req x prevStage prevHom prevFromBase)
    (g : refinement_stage_hom (J := J) N.stage B) (m : M)
    (hm : ((m : Ω) : CutΩ) < x) :
    request_realized (J := J)
      ((refinement_stage_hom.comp (J := J) N.fromBase g).map_request (req m)) := by
  -- Use the node invariant first, then transport the realized request across the later map.
  have hbase : request_realized (J := J) (N.fromBase.map_request (req m)) :=
    N.realizes_lt m hm
  have hlater :
      request_realized (J := J) (g.map_request (N.fromBase.map_request (req m))) :=
    refinement_stage_hom.map_request_realized (J := J) g (N.fromBase.map_request (req m))
      hbase
  -- Normalize the composite base map to the two-step transport used above.
  simpa [refinement_stage_hom.map_request_comp] using hlater

/-- Helper for Lemma 7.39.2: a request realized at a predecessor base map remains realized at
the current open-cut node. -/
theorem OpenSaturationNode.realizes_of_prev_realizes
    {A : refinement_stage (J := J) S' (ℱ := ℱ) s s'}
    {req : M → finite_cover_lift_request J A.T} {x : CutΩ}
    {prevStage : {y : CutΩ // y < x} →
      refinement_stage (J := J) S' (ℱ := ℱ) s s'}
    {prevHom : ∀ ⦃y z : {y : CutΩ // y < x}⦄, (y : CutΩ) ≤ z →
      refinement_stage_hom (J := J) (prevStage y) (prevStage z)}
    {prevFromBase : ∀ y : {y : CutΩ // y < x},
      refinement_stage_hom (J := J) A (prevStage y)}
    (N : OpenSaturationNode (J := J) A req x prevStage prevHom prevFromBase)
    (y : {y : CutΩ // y < x}) (m : M)
    (hreal : request_realized (J := J) ((prevFromBase y).map_request (req m))) :
    request_realized (J := J) (N.fromBase.map_request (req m)) := by
  -- Transport the predecessor realization through the node's stored predecessor inclusion.
  have htransport :
      request_realized (J := J)
        ((N.homFrom y).map_request ((prevFromBase y).map_request (req m))) :=
    refinement_stage_hom.map_request_realized (J := J) (N.homFrom y)
      ((prevFromBase y).map_request (req m)) hreal
  -- The node's base-map coherence identifies that transport with the current base map.
  rw [N.fromBase_comp y]
  simpa [refinement_stage_hom.map_request_comp] using htransport

/-- Helper for Lemma 7.39.2: realization after a predecessor comparison can be transported
through the current open-cut node's comparison map. -/
theorem OpenSaturationNode.homFrom_realizes_of_le
    {A : refinement_stage (J := J) S' (ℱ := ℱ) s s'}
    {req : M → finite_cover_lift_request J A.T} {x : CutΩ}
    {prevStage : {y : CutΩ // y < x} →
      refinement_stage (J := J) S' (ℱ := ℱ) s s'}
    {prevHom : ∀ ⦃y z : {y : CutΩ // y < x}⦄, (y : CutΩ) ≤ z →
      refinement_stage_hom (J := J) (prevStage y) (prevStage z)}
    {prevFromBase : ∀ y : {y : CutΩ // y < x},
      refinement_stage_hom (J := J) A (prevStage y)}
    (N : OpenSaturationNode (J := J) A req x prevStage prevHom prevFromBase)
    {y z : {y : CutΩ // y < x}} (hyz : (y : CutΩ) ≤ z)
    {r : finite_cover_lift_request J (prevStage y).T}
    (hreal : request_realized (J := J) ((prevHom hyz).map_request r)) :
    request_realized (J := J) ((N.homFrom y).map_request r) := by
  -- Move the later-predecessor realization across the current node's map from `z`.
  have htransport :
      request_realized (J := J)
        ((N.homFrom z).map_request ((prevHom hyz).map_request r)) :=
    refinement_stage_hom.map_request_realized (J := J) (N.homFrom z)
      ((prevHom hyz).map_request r) hreal
  -- Coherence of the node's predecessor inclusions rewrites the target to that transport.
  rw [N.homFrom_comp hyz]
  simpa [refinement_stage_hom.map_request_comp] using htransport

/-- Helper for Lemma 7.39.2: an open-cut node canonically extends to one compatible stage
realizing every request strictly below the successor cut. -/
theorem OpenSaturationNode.exists_stage_realizing_lt_succ
    {A : refinement_stage (J := J) S' (ℱ := ℱ) s s'}
    {req : M → finite_cover_lift_request J A.T} {x : CutΩ} (hx : ¬ IsMax x)
    {prevStage : {y : CutΩ // y < x} →
      refinement_stage (J := J) S' (ℱ := ℱ) s s'}
    {prevHom : ∀ ⦃y z : {y : CutΩ // y < x}⦄, (y : CutΩ) ≤ z →
      refinement_stage_hom (J := J) (prevStage y) (prevStage z)}
    {prevFromBase : ∀ y : {y : CutΩ // y < x},
      refinement_stage_hom (J := J) A (prevStage y)}
    (N : OpenSaturationNode (J := J) A req x prevStage prevHom prevFromBase) :
    ∃ B : refinement_stage (J := J) S' (ℱ := ℱ) s s',
      ∃ h : refinement_stage_hom (J := J) A B,
        h.original_compatible ∧
          ∀ m : M, ((m : Ω) : CutΩ) < Order.succ x →
            request_realized (J := J) (h.map_request (req m)) := by
  -- The successor cut is never above `⊤`; split the predecessor cut into bottom/concrete cases.
  obtain - | xΩ := x
  · exact (hx isMax_top).elim
  · induction xΩ using WithBot.recBotCoe with
    | bot =>
        -- Below the successor of the adjoined bottom there are no concrete request cuts.
        refine ⟨N.stage, N.fromBase, N.fromBase_compatible, ?_⟩
        intro m hm
        have hm_le :
            ((m : Ω) : CutΩ) ≤ ((⊥ : Ω) : CutΩ) :=
          (Order.lt_succ_iff_of_not_isMax hx).1 hm
        have hbot_lt_m : ((⊥ : Ω) : CutΩ) < ((m : Ω) : CutΩ) :=
          WithTop.coe_lt_coe.mpr (WithBot.bot_lt_coe m)
        exact False.elim ((not_lt_of_ge hm_le) hbot_lt_m)
    | coe m₀ =>
        -- At a concrete predecessor cut, solve the new request and transport all older ones.
        let r : finite_cover_lift_request J A.T := req m₀
        let step : refinement_stage_hom (J := J) N.stage
            (next_stage_for_scheduled_request (J := J) A N.stage N.fromBase r) :=
          next_stage_for_scheduled_request_hom (J := J) A N.stage N.fromBase r
        let h' : refinement_stage_hom (J := J) A
            (next_stage_for_scheduled_request (J := J) A N.stage N.fromBase r) :=
          refinement_stage_hom.comp (J := J) N.fromBase step
        refine ⟨next_stage_for_scheduled_request (J := J) A N.stage N.fromBase r,
          h', ?_, ?_⟩
        · -- Compatibility composes the old node base map with the one-request extension.
          exact refinement_stage_hom.original_compatible_comp (J := J) N.fromBase step
            N.fromBase_compatible
            (next_stage_for_scheduled_request_original_compatible (J := J) A N.stage
              N.fromBase r)
        · intro m hm
          have hm_le_cut :
              ((m : Ω) : CutΩ) ≤ ((m₀ : Ω) : CutΩ) :=
            (Order.lt_succ_iff_of_not_isMax hx).1 hm
          have hm_le_withBot : (m : Ω) ≤ (m₀ : Ω) :=
            WithTop.coe_le_coe.mp hm_le_cut
          have hm_le : m ≤ m₀ :=
            WithBot.coe_le_coe.mp hm_le_withBot
          rcases hm_le.lt_or_eq with hlt | heq
          · -- Older requests are already realized by `N` and remain realized after `step`.
            have hm_lt_cut : ((m : Ω) : CutΩ) < ((m₀ : Ω) : CutΩ) :=
              WithTop.coe_lt_coe.mpr (WithBot.coe_lt_coe.mpr hlt)
            simpa [h'] using
              OpenSaturationNode.realizes_map_of_lt (J := J) N step m hm_lt_cut
          · -- The new request is exactly the one used to build the successor stage.
            subst m
            simpa [h', r] using
              next_stage_for_scheduled_request_comp_realized (J := J) A N.stage N.fromBase r
end

end ScheduledSaturation

end CategoryTheory
