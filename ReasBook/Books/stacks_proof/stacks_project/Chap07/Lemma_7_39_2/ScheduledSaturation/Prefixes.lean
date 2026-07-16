import stacks_proof.stacks_project.Chap07.Lemma_7_39_2.ScheduledSaturation.Basic
import stacks_proof.stacks_project.Chap07.Lemma_7_39_2.FiniteFrontier
import stacks_proof.stacks_project.Chap07.Lemma_7_39_2.DiagramUnionCore
import stacks_proof.stacks_project.Chap07.Lemma_7_39_2.DiagramUnionLimit

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


/-- Helper for Lemma 7.39.2: the bottom-adjoined request schedule is directed by taking
the maximum of two cuts. -/
theorem withBot_directed : IsDirected (WithBot M) (· ≤ ·) where
  directed x y := by
    -- The maximum dominates both entries in the linear order on `WithBot M`.
    exact ⟨max x y, le_max_left x y, le_max_right x y⟩

/-- Helper for Lemma 7.39.2: every concrete request node has the adjoined bottom as a strict
predecessor. -/
theorem withBot_predecessorCut_nonempty (m : M) :
    Nonempty {x : WithBot M // x < (m : WithBot M)} := by
  -- The strict predecessor cut below a concrete node always contains `⊥`.
  exact ⟨⟨⊥, WithBot.bot_lt_coe m⟩⟩

/-- Helper for Lemma 7.39.2: strict predecessor cuts below a concrete request node are directed
by taking maxima inside the cut. -/
theorem withBot_predecessorCut_directed (m : M) :
    IsDirected {x : WithBot M // x < (m : WithBot M)} (· ≤ ·) where
  directed x y := by
    -- The maximum of two strict predecessors is still a strict predecessor and dominates both.
    refine ⟨⟨max x.1 y.1, ?_⟩, ?_, ?_⟩
    · exact max_lt x.2 y.2
    · exact le_max_left _ _
    · exact le_max_right _ _

/-- Helper for Lemma 7.39.2: every node in the closed cut below a concrete request is either
the adjoined bottom node or a concrete request node no later than the cut. -/
theorem withBot_closedCut_cases (m : M) (x : {x : WithBot M // x ≤ (m : WithBot M)}) :
    x.1 = ⊥ ∨ ∃ n : M, x.1 = (n : WithBot M) ∧ n ≤ m := by
  -- Split the `WithBot` value into the base node and the concrete-node case.
  rcases x with ⟨x, hx⟩
  induction x using WithBot.recBotCoe with
  | bot =>
      left
      rfl
  | coe n =>
      right
      refine ⟨n, rfl, ?_⟩
      exact WithBot.coe_le_coe.mp hx

/-- Helper for Lemma 7.39.2: every strict predecessor of a concrete request is either the
adjoined bottom node or a concrete request node strictly earlier than the cut. -/
theorem withBot_predecessorCut_cases (m : M)
    (x : {x : WithBot M // x < (m : WithBot M)}) :
    x.1 = ⊥ ∨ ∃ n : M, x.1 = (n : WithBot M) ∧ n < m := by
  -- Split the strict predecessor just as for the closed cut, now preserving strict inequality.
  rcases x with ⟨x, hx⟩
  induction x using WithBot.recBotCoe with
  | bot =>
      left
      rfl
  | coe n =>
      right
      refine ⟨n, rfl, ?_⟩
      exact WithBot.coe_lt_coe.mp hx

namespace SaturationDiagram

variable {A : refinement_stage (J := J) S' (ℱ := ℱ) s s'}
variable {req : M → finite_cover_lift_request J A.T}

/-- Helper for Lemma 7.39.2: in a saturation diagram, the later base map transports a request
as the earlier base map followed by the stored comparison morphism. -/
theorem fromBase_map_request_comp
    (D : SaturationDiagram (J := J) A req) {x y : Ω} (hxy : x ≤ y)
    (r : finite_cover_lift_request J A.T) :
    (D.fromBase y).map_request r = (D.hom hxy).map_request ((D.fromBase x).map_request r) := by
  -- Normalize the stored base-map composition through the public request-transport computation.
  rw [D.fromBase_comp hxy]
  exact refinement_stage_hom.map_request_comp (J := J) (D.fromBase x) (D.hom hxy) r

/-- Helper for Lemma 7.39.2: realization of a scheduled request persists from its own node to
any later node in a saturation diagram. -/
theorem realizes_at_of_le
    (D : SaturationDiagram (J := J) A req) {m : M} {x : Ω} (hmx : (m : Ω) ≤ x) :
    request_realized (J := J) ((D.fromBase x).map_request (req m)) := by
  -- First transport the realization stored at the scheduled node along the comparison to `x`.
  have htransport :
      request_realized (J := J)
        ((D.hom hmx).map_request ((D.fromBase (m : Ω)).map_request (req m))) :=
    refinement_stage_hom.map_request_realized (J := J) (D.hom hmx)
      ((D.fromBase (m : Ω)).map_request (req m)) (D.realizes_at m)
  -- The base-map coherence rewrites that transported request as the direct base map to `x`.
  rw [← D.fromBase_map_request_comp hmx (req m)] at htransport
  exact htransport

/-- Helper for Lemma 7.39.2: an existential compatible terminal stage realizing every scheduled
request supplies the constant bottom-indexed saturation diagram. -/
theorem nonempty_of_exists_stage_realizing_all
    (hterminal :
      ∃ B : refinement_stage (J := J) S' (ℱ := ℱ) s s',
        ∃ h : refinement_stage_hom (J := J) A B,
          h.original_compatible ∧
            ∀ m : M, request_realized (J := J) (h.map_request (req m))) :
    Nonempty (SaturationDiagram (J := J) A req) := by
  -- Unpack the terminal compatible stage and feed it to the checked constant-diagram adapter.
  rcases hterminal with ⟨B, h, hcompat, hreal⟩
  exact nonempty_of_stage_realizing_all (J := J) B h hcompat hreal

end SaturationDiagram

/-- Helper for Lemma 7.39.2: a coherent saturation diagram restricted to the closed initial
segment `↓x` of the bottom-adjoined request schedule.  The fields mirror `SaturationDiagram`,
but only for nodes bounded by `x`; this is the stronger invariant needed for a canonical
transfinite construction. -/
structure SaturationPrefix
    (A : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (req : M → finite_cover_lift_request J A.T) (x : Ω) where
  stage : {y : Ω // y ≤ x} → refinement_stage (J := J) S' (ℱ := ℱ) s s'
  hom :
    ∀ ⦃y z : {y : Ω // y ≤ x}⦄, (y : Ω) ≤ z →
      refinement_stage_hom (J := J) (stage y) (stage z)
  hom_refl :
    ∀ y : {y : Ω // y ≤ x},
      hom (show (y : Ω) ≤ y from le_rfl) = refinement_stage_hom_refl (J := J) (stage y)
  hom_comp :
    ∀ ⦃y z t : {y : Ω // y ≤ x}⦄ (hyz : (y : Ω) ≤ z) (hzt : (z : Ω) ≤ t),
      hom (le_trans hyz hzt) =
        refinement_stage_hom.comp (J := J) (hom hyz) (hom hzt)
  hom_original_compatible :
    ∀ ⦃y z : {y : Ω // y ≤ x}⦄ (hyz : (y : Ω) ≤ z), (hom hyz).original_compatible
  fromBase : ∀ y : {y : Ω // y ≤ x}, refinement_stage_hom (J := J) A (stage y)
  fromBase_compatible : ∀ y : {y : Ω // y ≤ x}, (fromBase y).original_compatible
  fromBase_comp :
    ∀ ⦃y z : {y : Ω // y ≤ x}⦄ (hyz : (y : Ω) ≤ z),
      fromBase z = refinement_stage_hom.comp (J := J) (fromBase y) (hom hyz)
  realizes_at :
    ∀ (m : M) (hmx : (m : Ω) ≤ x),
      request_realized (J := J) ((fromBase ⟨(m : Ω), hmx⟩).map_request (req m))

namespace SaturationPrefix

variable {A : refinement_stage (J := J) S' (ℱ := ℱ) s s'}
variable {req : M → finite_cover_lift_request J A.T}

/-- Helper for Lemma 7.39.2: the bottom closed initial segment carries the constant prefix on
the original packaged stage. -/
theorem nonempty_bot (A : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (req : M → finite_cover_lift_request J A.T) :
    Nonempty (SaturationPrefix (J := J) A req (⊥ : Ω)) := by
  refine ⟨
    { stage := fun _ => A
      hom := fun {_ _} _ => refinement_stage_hom_refl (J := J) A
      hom_refl := ?_
      hom_comp := ?_
      hom_original_compatible := ?_
      fromBase := fun _ => refinement_stage_hom_refl (J := J) A
      fromBase_compatible := ?_
      fromBase_comp := ?_
      realizes_at := ?_ }⟩
  · -- Every comparison in the bottom prefix is represented by the identity morphism.
    intro y
    rfl
  · -- Composition in the constant prefix reduces to identity-left-composition.
    intro y z t hyz hzt
    exact (refinement_stage_hom.refl_comp (J := J) (refinement_stage_hom_refl (J := J) A)).symm
  · -- Identity morphisms are compatible with the original refinement data.
    intro y z hyz
    exact refinement_stage_hom.original_compatible_refl (J := J) A
  · -- The bottom base map is the identity, hence compatible.
    intro y
    exact refinement_stage_hom.original_compatible_refl (J := J) A
  · -- The stored base-map composition is again the identity-left-composition law.
    intro y z hyz
    exact (refinement_stage_hom.refl_comp (J := J) (refinement_stage_hom_refl (J := J) A)).symm
  · -- No concrete scheduled request lies at or below the adjoined bottom node.
    intro m hm
    exact False.elim ((not_lt_of_ge hm) (WithBot.bot_lt_coe m))

/-- Helper for Lemma 7.39.2: a closed saturation prefix restricts to any smaller closed
initial segment. -/
noncomputable def restrict {x y : Ω} (P : SaturationPrefix (J := J) A req x) (hyx : y ≤ x) :
    SaturationPrefix (J := J) A req y where
  stage z := P.stage ⟨z.1, le_trans z.2 hyx⟩
  hom := fun {z t} hzt =>
    P.hom (y := ⟨z.1, le_trans z.2 hyx⟩) (z := ⟨t.1, le_trans t.2 hyx⟩) hzt
  hom_refl z := P.hom_refl ⟨z.1, le_trans z.2 hyx⟩
  hom_comp := fun {z t u} hzt htu =>
    P.hom_comp (y := ⟨z.1, le_trans z.2 hyx⟩)
      (z := ⟨t.1, le_trans t.2 hyx⟩) (t := ⟨u.1, le_trans u.2 hyx⟩) hzt htu
  hom_original_compatible := fun {z t} hzt =>
    P.hom_original_compatible (y := ⟨z.1, le_trans z.2 hyx⟩)
      (z := ⟨t.1, le_trans t.2 hyx⟩) hzt
  fromBase z := P.fromBase ⟨z.1, le_trans z.2 hyx⟩
  fromBase_compatible z := P.fromBase_compatible ⟨z.1, le_trans z.2 hyx⟩
  fromBase_comp := fun {z t} hzt =>
    P.fromBase_comp (y := ⟨z.1, le_trans z.2 hyx⟩)
      (z := ⟨t.1, le_trans t.2 hyx⟩) hzt
  realizes_at m hmy := P.realizes_at m (le_trans hmy hyx)

/-- Helper for Lemma 7.39.2: within a closed saturation prefix, later base maps transport
requests as the earlier base map followed by the stored comparison morphism. -/
theorem fromBase_map_request_comp {x : Ω} (P : SaturationPrefix (J := J) A req x)
    {y z : {y : Ω // y ≤ x}} (hyz : (y : Ω) ≤ z)
    (r : finite_cover_lift_request J A.T) :
    (P.fromBase z).map_request r = (P.hom hyz).map_request ((P.fromBase y).map_request r) := by
  -- Project the prefix's base-map composition through the public request-transport computation.
  rw [P.fromBase_comp hyz]
  exact refinement_stage_hom.map_request_comp (J := J) (P.fromBase y) (P.hom hyz) r

/-- Helper for Lemma 7.39.2: realization recorded at a scheduled node of a closed prefix
persists at every later node inside that prefix. -/
theorem realizes_at_of_le {x : Ω} (P : SaturationPrefix (J := J) A req x)
    {m : M} {y : {y : Ω // y ≤ x}} (hmy : (m : Ω) ≤ y) :
    request_realized (J := J) ((P.fromBase y).map_request (req m)) := by
  -- Transport the realization at the scheduled node through the stored comparison to `y`.
  have htransport :
      request_realized (J := J)
        ((P.hom hmy).map_request
          ((P.fromBase ⟨(m : Ω), le_trans hmy y.2⟩).map_request (req m))) :=
    refinement_stage_hom.map_request_realized (J := J) (P.hom hmy)
      ((P.fromBase ⟨(m : Ω), le_trans hmy y.2⟩).map_request (req m))
      (P.realizes_at m (le_trans hmy y.2))
  -- The prefix base-map coherence identifies this transport with the direct base map to `y`.
  rw [← P.fromBase_map_request_comp hmy (req m)] at htransport
  exact htransport

/-- Helper for Lemma 7.39.2: a closed saturation prefix whose top bounds every schedule node
projects to a global saturation diagram. -/
noncomputable def toSaturationDiagramOfBounded {x : Ω}
    (P : SaturationPrefix (J := J) A req x) (hx : ∀ y : Ω, y ≤ x) :
    SaturationDiagram (J := J) A req where
  stage y := P.stage ⟨y, hx y⟩
  hom := fun {y z} hyz => P.hom (y := ⟨y, hx y⟩) (z := ⟨z, hx z⟩) hyz
  hom_refl y := P.hom_refl ⟨y, hx y⟩
  hom_comp := fun {y z t} hyz hzt =>
    P.hom_comp (y := ⟨y, hx y⟩) (z := ⟨z, hx z⟩) (t := ⟨t, hx t⟩) hyz hzt
  hom_original_compatible := fun {y z} hyz =>
    P.hom_original_compatible (y := ⟨y, hx y⟩) (z := ⟨z, hx z⟩) hyz
  fromBase y := P.fromBase ⟨y, hx y⟩
  fromBase_compatible y := P.fromBase_compatible ⟨y, hx y⟩
  fromBase_comp := fun {y z} hyz =>
    P.fromBase_comp (y := ⟨y, hx y⟩) (z := ⟨z, hx z⟩) hyz
  realizes_at m := P.realizes_at m (hx (m : Ω))

end SaturationPrefix

/-- Helper for Lemma 7.39.2: a coherent open-cut saturation prefix over the request schedule
with an added terminal top.  The realization invariant is open in the cut, so the terminal top
realizes every concrete scheduled request without forcing a limit node to solve its own request. -/
structure OpenSaturationPrefix
    (A : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (req : M → finite_cover_lift_request J A.T) (x : CutΩ) where
  stage : {y : CutΩ // y ≤ x} → refinement_stage (J := J) S' (ℱ := ℱ) s s'
  hom :
    ∀ ⦃y z : {y : CutΩ // y ≤ x}⦄, (y : CutΩ) ≤ z →
      refinement_stage_hom (J := J) (stage y) (stage z)
  hom_refl :
    ∀ y : {y : CutΩ // y ≤ x},
      hom (show (y : CutΩ) ≤ y from le_rfl) = refinement_stage_hom_refl (J := J) (stage y)
  hom_comp :
    ∀ ⦃y z t : {y : CutΩ // y ≤ x}⦄ (hyz : (y : CutΩ) ≤ z) (hzt : (z : CutΩ) ≤ t),
      hom (le_trans hyz hzt) =
        refinement_stage_hom.comp (J := J) (hom hyz) (hom hzt)
  hom_original_compatible :
    ∀ ⦃y z : {y : CutΩ // y ≤ x}⦄ (hyz : (y : CutΩ) ≤ z), (hom hyz).original_compatible
  fromBase : ∀ y : {y : CutΩ // y ≤ x}, refinement_stage_hom (J := J) A (stage y)
  fromBase_compatible : ∀ y : {y : CutΩ // y ≤ x}, (fromBase y).original_compatible
  fromBase_comp :
    ∀ ⦃y z : {y : CutΩ // y ≤ x}⦄ (hyz : (y : CutΩ) ≤ z),
      fromBase z = refinement_stage_hom.comp (J := J) (fromBase y) (hom hyz)
  realizes_lt :
    ∀ (y : {y : CutΩ // y ≤ x}) (m : M), ((m : Ω) : CutΩ) < y.1 →
      request_realized (J := J) ((fromBase y).map_request (req m))

namespace OpenSaturationPrefix

variable {A : refinement_stage (J := J) S' (ℱ := ℱ) s s'}
variable {req : M → finite_cover_lift_request J A.T}

/-- Helper for Lemma 7.39.2: an open-cut saturation prefix restricts to any smaller closed
initial segment. -/
noncomputable def restrict {x y : CutΩ} (P : OpenSaturationPrefix (J := J) A req x)
    (hyx : y ≤ x) :
    OpenSaturationPrefix (J := J) A req y where
  stage z := P.stage ⟨z.1, le_trans z.2 hyx⟩
  hom := fun {z t} hzt =>
    P.hom (y := ⟨z.1, le_trans z.2 hyx⟩) (z := ⟨t.1, le_trans t.2 hyx⟩) hzt
  hom_refl z := P.hom_refl ⟨z.1, le_trans z.2 hyx⟩
  hom_comp := fun {z t u} hzt htu =>
    P.hom_comp (y := ⟨z.1, le_trans z.2 hyx⟩)
      (z := ⟨t.1, le_trans t.2 hyx⟩) (t := ⟨u.1, le_trans u.2 hyx⟩) hzt htu
  hom_original_compatible := fun {z t} hzt =>
    P.hom_original_compatible (y := ⟨z.1, le_trans z.2 hyx⟩)
      (z := ⟨t.1, le_trans t.2 hyx⟩) hzt
  fromBase z := P.fromBase ⟨z.1, le_trans z.2 hyx⟩
  fromBase_compatible z := P.fromBase_compatible ⟨z.1, le_trans z.2 hyx⟩
  fromBase_comp := fun {z t} hzt =>
    P.fromBase_comp (y := ⟨z.1, le_trans z.2 hyx⟩)
      (z := ⟨t.1, le_trans t.2 hyx⟩) hzt
  realizes_lt z m hmz := P.realizes_lt ⟨z.1, le_trans z.2 hyx⟩ m hmz

/-- Helper for Lemma 7.39.2: within an open-cut saturation prefix, later base maps transport
requests as the earlier base map followed by the stored comparison morphism. -/
theorem fromBase_map_request_comp {x : CutΩ} (P : OpenSaturationPrefix (J := J) A req x)
    {y z : {y : CutΩ // y ≤ x}} (hyz : (y : CutΩ) ≤ z)
    (r : finite_cover_lift_request J A.T) :
    (P.fromBase z).map_request r = (P.hom hyz).map_request ((P.fromBase y).map_request r) := by
  -- Project the prefix's base-map composition through the public request-transport computation.
  rw [P.fromBase_comp hyz]
  exact refinement_stage_hom.map_request_comp (J := J) (P.fromBase y) (P.hom hyz) r

/-- Helper for Lemma 7.39.2: one compatible stage realizing every request strictly below an
open cut gives a constant open-cut prefix at that cut. -/
theorem nonempty_of_stage_realizing_lt {x : CutΩ}
    (B : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (h : refinement_stage_hom (J := J) A B) (hcompat : h.original_compatible)
    (hreal : ∀ m : M, ((m : Ω) : CutΩ) < x →
      request_realized (J := J) (h.map_request (req m))) :
    Nonempty (OpenSaturationPrefix (J := J) A req x) := by
  -- Use the same terminal stage at every stored cut; all transition morphisms are identities.
  refine ⟨
    { stage := fun _ => B
      hom := fun {_ _} _ => refinement_stage_hom_refl (J := J) B
      hom_refl := ?_
      hom_comp := ?_
      hom_original_compatible := ?_
      fromBase := fun _ => h
      fromBase_compatible := ?_
      fromBase_comp := ?_
      realizes_lt := ?_ }⟩
  · -- Every constant-prefix self-comparison is the identity morphism.
    intro y
    rfl
  · -- Identity comparisons compose to the identity comparison.
    intro y z t hyz hzt
    exact (refinement_stage_hom.refl_comp (J := J) (refinement_stage_hom_refl (J := J) B)).symm
  · -- Identity comparison morphisms preserve the original refinement data.
    intro y z hyz
    exact refinement_stage_hom.original_compatible_refl (J := J) B
  · -- The fixed base morphism is compatible by hypothesis.
    intro y
    exact hcompat
  · -- The constant base morphism composes trivially with an identity comparison.
    intro y z hyz
    exact (refinement_stage_hom.comp_refl (J := J) h).symm
  · -- A request below a stored node is below the ambient cut, where `hreal` applies.
    intro y m hmy
    exact hreal m (lt_of_lt_of_le hmy y.2)

/-- Helper for Lemma 7.39.2: a minimal open cut carries the constant prefix on the original
packaged stage. -/
theorem nonempty_of_isMin {x : CutΩ} (hx : IsMin x) :
    Nonempty (OpenSaturationPrefix (J := J) A req x) := by
  -- At a minimal cut, every node in the closed initial segment is represented by the base stage.
  refine ⟨
    { stage := fun _ => A
      hom := fun {_ _} _ => refinement_stage_hom_refl (J := J) A
      hom_refl := ?_
      hom_comp := ?_
      hom_original_compatible := ?_
      fromBase := fun _ => refinement_stage_hom_refl (J := J) A
      fromBase_compatible := ?_
      fromBase_comp := ?_
      realizes_lt := ?_ }⟩
  · -- Every self-comparison in the constant prefix is the identity morphism.
    intro y
    rfl
  · -- Identity comparisons compose to the identity comparison.
    intro y z t hyz hzt
    exact (refinement_stage_hom.refl_comp (J := J) (refinement_stage_hom_refl (J := J) A)).symm
  · -- Identity comparison morphisms preserve the original refinement data.
    intro y z hyz
    exact refinement_stage_hom.original_compatible_refl (J := J) A
  · -- The base morphism at every node is the identity, hence compatible.
    intro y
    exact refinement_stage_hom.original_compatible_refl (J := J) A
  · -- The constant base map composes trivially with an identity comparison.
    intro y z hyz
    exact (refinement_stage_hom.refl_comp (J := J) (refinement_stage_hom_refl (J := J) A)).symm
  · -- No scheduled request lies strictly below a minimal cut.
    intro y m hmy
    have hmx : ((m : Ω) : CutΩ) < x := lt_of_lt_of_le hmy y.2
    exact False.elim ((not_lt_of_ge (hx (le_of_lt hmx))) hmx)

/-- Helper for Lemma 7.39.2: an open-cut prefix extends across a successor cut by solving the
new concrete scheduled request, if the predecessor cut is a concrete request node. -/
theorem nonempty_succ {x : CutΩ} (hx : ¬ IsMax x)
    (P : OpenSaturationPrefix (J := J) A req x) :
    Nonempty (OpenSaturationPrefix (J := J) A req (Order.succ x)) := by
  -- Work only with the top stage of the old prefix; the new successor prefix is constant.
  let topCut : {y : CutΩ // y ≤ x} := ⟨x, le_rfl⟩
  obtain - | xΩ := x
  · -- The top cut is maximal, so it cannot appear in the successor branch.
    exact (hx isMax_top).elim
  · induction xΩ using WithBot.recBotCoe with
    | bot =>
        -- No concrete request lies strictly below the successor of the adjoined bottom cut.
        refine nonempty_of_stage_realizing_lt (J := J) (A := A) (req := req)
          (P.stage topCut) (P.fromBase topCut) (P.fromBase_compatible topCut) ?_
        intro m hm
        have hm_le :
            ((m : Ω) : CutΩ) ≤ ((⊥ : Ω) : CutΩ) :=
          (Order.lt_succ_iff_of_not_isMax hx).1 hm
        have hbot_lt_m : ((⊥ : Ω) : CutΩ) < ((m : Ω) : CutΩ) :=
          WithTop.coe_lt_coe.mpr (WithBot.bot_lt_coe m)
        exact False.elim ((not_lt_of_ge hm_le) hbot_lt_m)
    | coe m₀ =>
        -- At a concrete predecessor cut, solve exactly the request indexed by that predecessor.
        let r : finite_cover_lift_request J A.T := req m₀
        let step : refinement_stage_hom (J := J) (P.stage topCut)
            (next_stage_for_scheduled_request (J := J) A (P.stage topCut)
              (P.fromBase topCut) r) :=
          next_stage_for_scheduled_request_hom (J := J) A (P.stage topCut)
            (P.fromBase topCut) r
        let h' : refinement_stage_hom (J := J) A
            (next_stage_for_scheduled_request (J := J) A (P.stage topCut)
              (P.fromBase topCut) r) :=
          refinement_stage_hom.comp (J := J) (P.fromBase topCut) step
        refine nonempty_of_stage_realizing_lt (J := J) (A := A) (req := req)
          (next_stage_for_scheduled_request (J := J) A (P.stage topCut)
            (P.fromBase topCut) r) h' ?_ ?_
        · -- Compatibility composes the old top base map with the one-request extension.
          exact refinement_stage_hom.original_compatible_comp (J := J) (P.fromBase topCut) step
            (P.fromBase_compatible topCut)
            (next_stage_for_scheduled_request_original_compatible (J := J) A
              (P.stage topCut) (P.fromBase topCut) r)
        · intro m hm
          have hm_le_cut :
              ((m : Ω) : CutΩ) ≤ ((m₀ : Ω) : CutΩ) :=
            (Order.lt_succ_iff_of_not_isMax hx).1 hm
          have hm_le_withBot : (m : Ω) ≤ (m₀ : Ω) :=
            WithTop.coe_le_coe.mp hm_le_cut
          have hm_le : m ≤ m₀ :=
            WithBot.coe_le_coe.mp hm_le_withBot
          rcases hm_le.lt_or_eq with hlt | heq
          · -- Older requests were already realized at the old top and persist through `step`.
            have hm_lt_cut : ((m : Ω) : CutΩ) < ((m₀ : Ω) : CutΩ) :=
              WithTop.coe_lt_coe.mpr (WithBot.coe_lt_coe.mpr hlt)
            have hold :
                request_realized (J := J) ((P.fromBase topCut).map_request (req m)) :=
              P.realizes_lt topCut m hm_lt_cut
            have hstep :
                request_realized (J := J)
                  (step.map_request ((P.fromBase topCut).map_request (req m))) :=
              refinement_stage_hom.map_request_realized (J := J) step
                ((P.fromBase topCut).map_request (req m)) hold
            simpa [h', refinement_stage_hom.map_request_comp] using hstep
          · -- The only remaining request is the one used to construct the successor stage.
            subst m
            simpa [h', r] using
              next_stage_for_scheduled_request_comp_realized (J := J) A
                (P.stage topCut) (P.fromBase topCut) r

/-- Helper for Lemma 7.39.2: strict open cuts below a terminal schedule cut are directed by
taking maxima inside the ambient linear order. -/
theorem openCutDirected (x : CutΩ) : IsDirected {y : CutΩ // y < x} (· ≤ ·) where
  directed y z := by
    -- The maximum stays below the same cut and dominates both predecessor cuts.
    refine ⟨⟨max y.1 z.1, ?_⟩, ?_, ?_⟩
    · exact max_lt y.2 z.2
    · exact le_max_left _ _
    · exact le_max_right _ _

/-- Helper for Lemma 7.39.2: strict predecessors of a successor open cut are either already
below the predecessor cut or are exactly the predecessor cut. -/
theorem openCut_lt_succ_cases {x y : CutΩ} (hx : ¬ IsMax x)
    (hy : y < Order.succ x) : y < x ∨ y = x := by
  -- The successor-order comparison first downgrades strict predecessor of `succ x` to `≤ x`.
  have hyx : y ≤ x := (Order.lt_succ_iff_of_not_isMax hx).1 hy
  -- Linearity splits the weak comparison into the old open cut and the new top point.
  exact hyx.lt_or_eq

/-- Helper for Lemma 7.39.2: a successor-limit schedule cut has at least one strict
predecessor, giving a base index for the direct-union limit construction. -/
theorem succLimitOpenCut_nonempty {x : CutΩ} (hx : Order.IsSuccLimit x) :
    Nonempty {y : CutΩ // y < x} := by
  -- Successor-limits are not minimal, so their open predecessor set is inhabited.
  rcases hx.nonempty_Iio with ⟨y, hy⟩
  exact ⟨⟨y, hy⟩⟩

/-- Helper for Lemma 7.39.2: below a successor-limit schedule cut, every predecessor is
strictly dominated by a larger predecessor of the same cut. -/
theorem succLimitOpenCut_cofinal {x y : CutΩ} (hx : Order.IsSuccLimit x) (hy : y < x) :
    ∃ z : {z : CutΩ // z < x}, y < z.1 := by
  -- Move one successor step above `y`; successor-limits remain closed under that step.
  have hnotMax : ¬ IsMax y := not_isMax_iff.mpr ⟨x, hy⟩
  exact ⟨⟨Order.succ y, hx.succ_lt hy⟩, Order.lt_succ_of_not_isMax hnotMax⟩

/-- Helper for Lemma 7.39.2: the terminal cut is bounded by itself in the open-cut schedule. -/
theorem cutTop_le_top : (⊤ : CutΩ) ≤ (⊤ : CutΩ) :=
  le_rfl

/-- Helper for Lemma 7.39.2: the top node of an open-cut prefix is one compatible terminal
stage realizing every scheduled request. -/
theorem top_yields_exists_stage_realizing_all
    (P : OpenSaturationPrefix (J := J) A req (⊤ : CutΩ)) :
    ∃ B : refinement_stage (J := J) S' (ℱ := ℱ) s s',
      ∃ h : refinement_stage_hom (J := J) A B,
        h.original_compatible ∧
          ∀ m : M, request_realized (J := J) (h.map_request (req m)) := by
  -- Project the terminal top cut and use the open realization invariant there.
  let topCut : {y : CutΩ // y ≤ (⊤ : CutΩ)} := ⟨⊤, cutTop_le_top (M := M)⟩
  refine ⟨P.stage topCut, P.fromBase topCut, P.fromBase_compatible topCut, ?_⟩
  intro m
  exact P.realizes_lt topCut m (WithTop.coe_lt_top (m : Ω))

/-- Helper for Lemma 7.39.2: a top open-cut prefix supplies the bottom-indexed saturation
diagram through the constant-diagram adapter. -/
theorem nonempty_top_yields_saturationDiagram
    (hP : Nonempty (OpenSaturationPrefix (J := J) A req (⊤ : CutΩ))) :
    Nonempty (SaturationDiagram (J := J) A req) := by
  -- First forget the open-cut transition data to the terminal compatible stage.
  rcases hP with ⟨P⟩
  rcases top_yields_exists_stage_realizing_all (J := J) P with ⟨B, h, hcompat, hreal⟩
  -- The existing checked adapter turns that terminal stage into a constant saturation diagram.
  exact SaturationDiagram.nonempty_of_stage_realizing_all (J := J) B h hcompat hreal

end OpenSaturationPrefix

namespace SaturationDiagram

variable {A : refinement_stage (J := J) S' (ℱ := ℱ) s s'}
variable {req : M → finite_cover_lift_request J A.T}

/-- Helper for Lemma 7.39.2: a global saturation diagram restricts to the closed initial
segment below any chosen schedule node. -/
noncomputable def restrictPrefix (D : SaturationDiagram (J := J) A req) (x : Ω) :
    SaturationPrefix (J := J) A req x where
  stage y := D.stage y.1
  hom := fun {_ _} hyz => D.hom hyz
  hom_refl y := D.hom_refl y.1
  hom_comp := fun {_ _ _} hyz hzt => D.hom_comp hyz hzt
  hom_original_compatible := fun {_ _} hyz => D.hom_original_compatible hyz
  fromBase y := D.fromBase y.1
  fromBase_compatible y := D.fromBase_compatible y.1
  fromBase_comp := fun {_ _} hyz => D.fromBase_comp hyz
  realizes_at m _hmx := D.realizes_at m

/-- Helper for Lemma 7.39.2: restricting a global saturation diagram preserves the top stage of
the chosen closed segment. -/
theorem restrictPrefix_top_stage (D : SaturationDiagram (J := J) A req) (x : Ω) :
    (D.restrictPrefix x).stage ⟨x, le_rfl⟩ = D.stage x := by
  -- The restriction adapter only reindexes the global diagram along the closed-cut inclusion.
  rfl

/-- Helper for Lemma 7.39.2: restricting a global saturation diagram preserves the top base map
of the chosen closed segment. -/
theorem restrictPrefix_top_fromBase (D : SaturationDiagram (J := J) A req) (x : Ω) :
    (D.restrictPrefix x).fromBase ⟨x, le_rfl⟩ = D.fromBase x := by
  -- The base map is projected through the same tautological closed-cut inclusion.
  rfl

end SaturationDiagram

/-- Helper for Lemma 7.39.2: a single coherent open-cut saturation tower over all cuts of
`WithTop (WithBot M)`.  Unlike independent prefix witnesses, this package stores comparison maps
between every pair of comparable cuts before any limit node is formed. -/
structure OpenSaturationTower
    (A : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (req : M → finite_cover_lift_request J A.T) where
  stage : CutΩ → refinement_stage (J := J) S' (ℱ := ℱ) s s'
  hom :
    ∀ ⦃x y : CutΩ⦄, x ≤ y →
      refinement_stage_hom (J := J) (stage x) (stage y)
  hom_refl :
    ∀ x : CutΩ, hom (show x ≤ x from le_rfl) = refinement_stage_hom_refl (J := J) (stage x)
  hom_comp :
    ∀ ⦃x y z : CutΩ⦄ (hxy : x ≤ y) (hyz : y ≤ z),
      hom (le_trans hxy hyz) =
        refinement_stage_hom.comp (J := J) (hom hxy) (hom hyz)
  hom_original_compatible :
    ∀ ⦃x y : CutΩ⦄ (hxy : x ≤ y), (hom hxy).original_compatible
  fromBase : ∀ x : CutΩ, refinement_stage_hom (J := J) A (stage x)
  fromBase_compatible : ∀ x : CutΩ, (fromBase x).original_compatible
  fromBase_comp :
    ∀ ⦃x y : CutΩ⦄ (hxy : x ≤ y),
      fromBase y = refinement_stage_hom.comp (J := J) (fromBase x) (hom hxy)
  realizes_lt :
    ∀ (x : CutΩ) (m : M), ((m : Ω) : CutΩ) < x →
      request_realized (J := J) ((fromBase x).map_request (req m))

namespace OpenSaturationTower

variable {A : refinement_stage (J := J) S' (ℱ := ℱ) s s'}
variable {req : M → finite_cover_lift_request J A.T}

/-- Helper for Lemma 7.39.2: one compatible terminal stage realizing every scheduled request
gives the constant open-cut saturation tower. -/
theorem nonempty_of_stage_realizing_all
    (B : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (h : refinement_stage_hom (J := J) A B) (hcompat : h.original_compatible)
    (hreal : ∀ m : M, request_realized (J := J) (h.map_request (req m))) :
    Nonempty (OpenSaturationTower (J := J) A req) := by
  -- Use the same terminal stage at every cut; all comparison morphisms are identities.
  refine ⟨
    { stage := fun _ => B
      hom := fun {_ _} _ => refinement_stage_hom_refl (J := J) B
      hom_refl := ?_
      hom_comp := ?_
      hom_original_compatible := ?_
      fromBase := fun _ => h
      fromBase_compatible := ?_
      fromBase_comp := ?_
      realizes_lt := ?_ }⟩
  · -- Every self-comparison in the constant tower is the identity morphism.
    intro x
    rfl
  · -- Identity comparisons compose to the identity comparison.
    intro x y z hxy hyz
    exact (refinement_stage_hom.refl_comp (J := J) (refinement_stage_hom_refl (J := J) B)).symm
  · -- Identity comparison morphisms preserve the original refinement data.
    intro x y hxy
    exact refinement_stage_hom.original_compatible_refl (J := J) B
  · -- The fixed base morphism is compatible by hypothesis.
    intro x
    exact hcompat
  · -- The constant base morphism composes trivially with an identity comparison.
    intro x y hxy
    exact (refinement_stage_hom.comp_refl (J := J) h).symm
  · -- The open-cut realization invariant follows from the terminal-stage hypothesis.
    intro x m hmx
    exact hreal m

/-- Helper for Lemma 7.39.2: a global open-cut tower restricts to the terminal top prefix used
by the existing saturation-diagram adapter. -/
def toTopPrefix (T : OpenSaturationTower (J := J) A req) :
    OpenSaturationPrefix (J := J) A req (⊤ : CutΩ) :=
  -- Reindex the global tower along the tautological inclusion of each cut into the terminal cut.
  { stage := fun y => T.stage y.1
    hom := fun {_ _} hyz => T.hom hyz
    hom_refl := fun y => T.hom_refl y.1
    hom_comp := fun {_ _ _} hyz hzt => T.hom_comp hyz hzt
    hom_original_compatible := fun {_ _} hyz => T.hom_original_compatible hyz
    fromBase := fun y => T.fromBase y.1
    fromBase_compatible := fun y => T.fromBase_compatible y.1
    fromBase_comp := fun {_ _} hyz => T.fromBase_comp hyz
    realizes_lt := fun y m hmy => T.realizes_lt y.1 m hmy }

end OpenSaturationTower

/-- Helper for Lemma 7.39.2: a coherent open-cut prefix at the terminal cut reindexes to a
global open-cut saturation tower. -/
theorem nonemptyOpenSaturationTowerOfTopPrefix
    (A : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (req : M → finite_cover_lift_request J A.T)
    (hP : Nonempty (OpenSaturationPrefix (J := J) A req (⊤ : CutΩ))) :
    Nonempty (OpenSaturationTower (J := J) A req) := by
  -- Reindex the terminal prefix along the unique comparison of every cut with `⊤`.
  rcases hP with ⟨P⟩
  refine ⟨
    { stage := fun x => P.stage ⟨x, le_top⟩
      hom := fun {x y} hxy => P.hom (y := ⟨x, le_top⟩) (z := ⟨y, le_top⟩) hxy
      hom_refl := ?_
      hom_comp := ?_
      hom_original_compatible := ?_
      fromBase := fun x => P.fromBase ⟨x, le_top⟩
      fromBase_compatible := ?_
      fromBase_comp := ?_
      realizes_lt := ?_ }⟩
  · -- Self-comparisons are inherited from the corresponding terminal-prefix self-comparisons.
    intro x
    exact P.hom_refl ⟨x, le_top⟩
  · -- Composition is inherited from the terminal prefix after the same reindexing.
    intro x y z hxy hyz
    exact P.hom_comp (y := ⟨x, le_top⟩) (z := ⟨y, le_top⟩)
      (t := ⟨z, le_top⟩) hxy hyz
  · -- Compatibility of transition morphisms is a stored prefix field.
    intro x y hxy
    exact P.hom_original_compatible (y := ⟨x, le_top⟩) (z := ⟨y, le_top⟩) hxy
  · -- The base maps are exactly the prefix base maps at the same cuts.
    intro x
    exact P.fromBase_compatible ⟨x, le_top⟩
  · -- Base-map factorization is inherited pointwise from the terminal prefix.
    intro x y hxy
    exact P.fromBase_comp (y := ⟨x, le_top⟩) (z := ⟨y, le_top⟩) hxy
  · -- The open realization invariant is unchanged by the terminal-cut reindexing.
    intro x m hmx
    exact P.realizes_lt ⟨x, le_top⟩ m hmx

/-- Helper for Lemma 7.39.2: a minimal open schedule cut has no strict predecessors. -/
theorem not_lt_of_isMin_cut {x y : CutΩ} (hx : IsMin x) : ¬ y < x := by
  intro hy
  -- Minimality turns `y ≤ x` into `x ≤ y`, contradicting the strict predecessor relation.
  exact (not_lt_of_ge (hx (le_of_lt hy))) hy
end

end ScheduledSaturation

end CategoryTheory
