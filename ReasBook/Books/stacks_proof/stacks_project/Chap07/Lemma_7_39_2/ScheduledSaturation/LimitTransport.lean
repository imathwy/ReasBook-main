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


/-- A coherent compatible diagram on the closed down-set `↓x ⊆ WithBot M`, refining the fixed
stage `A`: the data needed to feed `refinementStageDiagramLimitStage`, plus a base node `⊥ ↦ A`. -/
structure Chain (A : refinement_stage (J := J) S' (ℱ := ℱ) s s') (x : Ω) where
  obj : {y : Ω // y ≤ x} → refinement_stage (J := J) S' (ℱ := ℱ) s s'
  /-- the base node is the fixed stage `A` -/
  obj_bot : obj ⟨⊥, bot_le⟩ = A
  mono : ∀ ⦃y z : {y : Ω // y ≤ x}⦄, (y : Ω) ≤ z →
    refinement_stage_hom (J := J) (obj y) (obj z)
  mono_refl : ∀ y : {y : Ω // y ≤ x},
    mono (le_refl (y : Ω)) = refinement_stage_hom_refl (J := J) (obj y)
  mono_comp : ∀ ⦃y z t : {y : Ω // y ≤ x}⦄ (hyz : (y : Ω) ≤ z) (hzt : (z : Ω) ≤ t),
    mono (le_trans hyz hzt) = refinement_stage_hom.comp (J := J) (mono hyz) (mono hzt)
  mono_compat : ∀ ⦃y z : {y : Ω // y ≤ x}⦄ (hyz : (y : Ω) ≤ z), (mono hyz).original_compatible

namespace Chain

variable {A : refinement_stage (J := J) S' (ℱ := ℱ) s s'}

/-- The compatible morphism from the base stage `A` into any node of the chain. -/
noncomputable def homFromBase {x : Ω} (D : Chain (J := J) A x) (y : {y : Ω // y ≤ x}) :
    refinement_stage_hom (J := J) A (D.obj y) := by
  have h := D.mono (show ((⟨⊥, bot_le⟩ : {y : Ω // y ≤ x}) : Ω) ≤ y from bot_le)
  rw [D.obj_bot] at h
  exact h

end Chain

/-! ### Bot case: the one-node chain over `↓⊥ = {⊥}`. -/

/-- The trivial chain on `↓⊥`: a single node equal to `A`. -/
noncomputable def chainBot (A : refinement_stage (J := J) S' (ℱ := ℱ) s s') :
    Chain (J := J) A (⊥ : Ω) where
  obj _ := A
  obj_bot := rfl
  mono _ _ _ := refinement_stage_hom_refl (J := J) A
  mono_refl _ := rfl
  mono_comp := by
    intro y z t hyz hzt
    -- All three nodes are `A` and all maps are the identity self-refinement.
    simp [refinement_stage_hom.refl_comp]
  mono_compat := by
    intro y z hyz
    exact refinement_stage_hom.original_compatible_refl (J := J) A

/-! ### Successor case: extend `Chain A j` by solving one request at `succ j`. -/

/-- In a `SuccOrder`, an element `≤ succ j` is either `≤ j` or equal to `succ j`
(when `j` is not maximal). -/
private theorem le_succ_cases {j : Ω} (hj : ¬ IsMax j) {y : Ω} (hy : y ≤ Order.succ j) :
    y ≤ j ∨ y = Order.succ j := by
  rcases hy.lt_or_eq with hlt | heq
  · exact Or.inl ((Order.lt_succ_iff_of_not_isMax hj).1 hlt)
  · exact Or.inr heq

/-- The successor chain's top node: solve the request `r` on the current top node of `D`. -/
noncomputable def succTop (A : refinement_stage (J := J) S' (ℱ := ℱ) s s') {j : Ω}
    (D : Chain (J := J) A j) (r : finite_cover_lift_request J A.T) :
    refinement_stage (J := J) S' (ℱ := ℱ) s s' :=
  next_stage_for_scheduled_request (J := J) A (D.obj ⟨j, le_rfl⟩)
    (D.homFromBase ⟨j, le_rfl⟩) r

/-- The compatible step from the current top node into the successor top node. -/
noncomputable def succStepHom (A : refinement_stage (J := J) S' (ℱ := ℱ) s s') {j : Ω}
    (D : Chain (J := J) A j) (r : finite_cover_lift_request J A.T) :
    refinement_stage_hom (J := J) (D.obj ⟨j, le_rfl⟩) (succTop (J := J) A D r) :=
  next_stage_for_scheduled_request_hom (J := J) A (D.obj ⟨j, le_rfl⟩)
    (D.homFromBase ⟨j, le_rfl⟩) r

theorem succStepHom_compat (A : refinement_stage (J := J) S' (ℱ := ℱ) s s') {j : Ω}
    (D : Chain (J := J) A j) (r : finite_cover_lift_request J A.T) :
    (succStepHom (J := J) A D r).original_compatible :=
  next_stage_for_scheduled_request_original_compatible (J := J) A (D.obj ⟨j, le_rfl⟩)
    (D.homFromBase ⟨j, le_rfl⟩) r

/-- Helper for Lemma 7.39.2: the base morphism into the successor top is the old top base map
followed by the one-request extension. -/
noncomputable def succTopFromBase (A : refinement_stage (J := J) S' (ℱ := ℱ) s s') {j : Ω}
    (D : Chain (J := J) A j) (r : finite_cover_lift_request J A.T) :
    refinement_stage_hom (J := J) A (succTop (J := J) A D r) :=
  refinement_stage_hom.comp (J := J) (D.homFromBase ⟨j, le_rfl⟩)
    (succStepHom (J := J) A D r)

/-- Helper for Lemma 7.39.2: the successor top realizes the request used to build it. -/
theorem succTopFromBase_realizes (A : refinement_stage (J := J) S' (ℱ := ℱ) s s') {j : Ω}
    (D : Chain (J := J) A j) (r : finite_cover_lift_request J A.T) :
    request_realized (J := J) ((succTopFromBase (J := J) A D r).map_request r) := by
  -- This is exactly the computation lemma for `next_stage_for_scheduled_request`.
  exact next_stage_for_scheduled_request_comp_realized (J := J) A (D.obj ⟨j, le_rfl⟩)
    (D.homFromBase ⟨j, le_rfl⟩) r

/-- Helper for Lemma 7.39.2: requests already realized on the current top stage remain realized
after the one-step successor morphism. -/
theorem succStepHom_preserves_realized (A : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    {j : Ω} (D : Chain (J := J) A j) (rNew : finite_cover_lift_request J A.T)
    {r : finite_cover_lift_request J (D.obj ⟨j, le_rfl⟩).T}
    (hr : request_realized (J := J) r) :
    request_realized (J := J) ((succStepHom (J := J) A D rNew).map_request r) := by
  -- Realization is monotone under every packaged-stage morphism; apply it to the successor step.
  exact refinement_stage_hom.map_request_realized (J := J) (succStepHom (J := J) A D rNew)
    r hr

/-- Helper for Lemma 7.39.2: the canonical map from a chosen stage of a coherent directed
diagram to its direct-union limit is compatible with the original refinement data. -/
theorem stageHomToLimit_original_compatible
    {δ : Type w} [Preorder δ] [IsDirected δ (· ≤ ·)]
    (Aδ : δ → refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (hom : ∀ {a b : δ}, a ≤ b → refinement_stage_hom (J := J) (Aδ a) (Aδ b))
    (hom_refl :
      ∀ a : δ, hom (show a ≤ a from le_rfl) = refinement_stage_hom_refl (J := J) (Aδ a))
    (hom_comp :
      ∀ {a b c : δ} (hab : a ≤ b) (hbc : b ≤ c),
        hom (le_trans hab hbc) =
          refinement_stage_hom.comp (J := J) (hom hab) (hom hbc))
    (a0 : δ)
    (hsep :
      letI : Preorder (refinementStageDiagramIndex (J := J) Aδ) :=
        refinementStageDiagramIndexPreorder (J := J) Aδ hom hom_refl hom_comp
      let TΔ := refinementStageDiagramSystem (J := J) Aδ hom hom_refl hom_comp
      let jΔ := refinementStageDiagramSystemOriginalEmbedding
        (J := J) Aδ hom hom_refl hom_comp a0
      let eΔ := refinementStageDiagramSystemOriginalIso
        (J := J) Aδ hom hom_refl hom_comp a0
      ((refinementFiber jΔ TΔ eΔ).presheafFiber).app ((sheafToPresheaf J
        (Type (max u v w))).obj ℱ) s ≠
        ((refinementFiber jΔ TΔ eΔ).presheafFiber).app ((sheafToPresheaf J
          (Type (max u v w))).obj ℱ) s') :
    (refinementStageDiagramStageHomToLimit
      (J := J) Aδ hom hom_refl hom_comp a0 a0 hsep).original_compatible := by
  -- The packaged limit uses the chosen base stage's original data followed by the canonical
  -- direct-union inclusion, so compatibility is projection-wise definitional.
  constructor
  · ext i
    rfl
  · exact HEq.rfl

/-- Helper for Lemma 7.39.2: transporting a request to a direct-union limit through a later
diagram stage agrees with transporting it directly from the earlier stage. -/
theorem stageHomToLimit_map_request_comp_of_le
    {δ : Type w} [Preorder δ] [IsDirected δ (· ≤ ·)]
    (Aδ : δ → refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (hom : ∀ {a b : δ}, a ≤ b → refinement_stage_hom (J := J) (Aδ a) (Aδ b))
    (hom_refl :
      ∀ a : δ, hom (show a ≤ a from le_rfl) = refinement_stage_hom_refl (J := J) (Aδ a))
    (hom_comp :
      ∀ {a b c : δ} (hab : a ≤ b) (hbc : b ≤ c),
        hom (le_trans hab hbc) =
          refinement_stage_hom.comp (J := J) (hom hab) (hom hbc))
    (a0 : δ)
    (hsep :
      letI : Preorder (refinementStageDiagramIndex (J := J) Aδ) :=
        refinementStageDiagramIndexPreorder (J := J) Aδ hom hom_refl hom_comp
      let TΔ := refinementStageDiagramSystem (J := J) Aδ hom hom_refl hom_comp
      let jΔ := refinementStageDiagramSystemOriginalEmbedding
        (J := J) Aδ hom hom_refl hom_comp a0
      let eΔ := refinementStageDiagramSystemOriginalIso
        (J := J) Aδ hom hom_refl hom_comp a0
      ((refinementFiber jΔ TΔ eΔ).presheafFiber).app ((sheafToPresheaf J
        (Type (max u v w))).obj ℱ) s ≠
        ((refinementFiber jΔ TΔ eΔ).presheafFiber).app ((sheafToPresheaf J
          (Type (max u v w))).obj ℱ) s')
    {a b : δ} (hab : a ≤ b) (r : finite_cover_lift_request J (Aδ a).T) :
    (refinement_stage_hom.comp (J := J) (hom hab)
      (refinementStageDiagramStageHomToLimit
        (J := J) Aδ hom hom_refl hom_comp a0 b hsep)).map_request r =
    (refinementStageDiagramStageHomToLimit
      (J := J) Aδ hom hom_refl hom_comp a0 a hsep).map_request r := by
  letI : Preorder (refinementStageDiagramIndex (J := J) Aδ) :=
    refinementStageDiagramIndexPreorder (J := J) Aδ hom hom_refl hom_comp
  -- Route correction: the corresponding `refinement_stage_hom` equality is too strong because
  -- the two record values use different embeddings into the diagram index.  Requests have the
  -- right extensional normal form, supplied by the direct-union transport lemma.
  have htransport := refinementStageDiagramSystem_transport_request_of_le
    (J := J) Aδ hom hom_refl hom_comp hab r
  -- First unfold request transport along the composite, then identify the two limit inclusions.
  calc
    (refinement_stage_hom.comp (J := J) (hom hab)
        (refinementStageDiagramStageHomToLimit
          (J := J) Aδ hom hom_refl hom_comp a0 b hsep)).map_request r =
        (refinementStageDiagramStageHomToLimit
          (J := J) Aδ hom hom_refl hom_comp a0 b hsep).map_request
          ((hom hab).map_request r) := by
          exact refinement_stage_hom.map_request_comp (J := J) (hom hab)
            (refinementStageDiagramStageHomToLimit
              (J := J) Aδ hom hom_refl hom_comp a0 b hsep) r
    _ = (refinementStageDiagramStageHomToLimit
          (J := J) Aδ hom hom_refl hom_comp a0 a hsep).map_request r := by
          simpa [refinement_stage_hom.map_request, refinementStageDiagramStageHomToLimit]
            using htransport.symm

/-- Helper for Lemma 7.39.2: if a base morphism into a coherent directed diagram factors through
a later stage, then transporting a request to the direct-union limit through the base stage agrees
with transporting it through that later stage. -/
theorem stageHomToLimit_map_request_base_comp_of_le
    {δ : Type w} [Preorder δ] [IsDirected δ (· ≤ ·)]
    (Aδ : δ → refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (hom : ∀ {a b : δ}, a ≤ b → refinement_stage_hom (J := J) (Aδ a) (Aδ b))
    (hom_refl :
      ∀ a : δ, hom (show a ≤ a from le_rfl) = refinement_stage_hom_refl (J := J) (Aδ a))
    (hom_comp :
      ∀ {a b c : δ} (hab : a ≤ b) (hbc : b ≤ c),
        hom (le_trans hab hbc) =
          refinement_stage_hom.comp (J := J) (hom hab) (hom hbc))
    (a0 : δ)
    (hsep :
      letI : Preorder (refinementStageDiagramIndex (J := J) Aδ) :=
        refinementStageDiagramIndexPreorder (J := J) Aδ hom hom_refl hom_comp
      let TΔ := refinementStageDiagramSystem (J := J) Aδ hom hom_refl hom_comp
      let jΔ := refinementStageDiagramSystemOriginalEmbedding
        (J := J) Aδ hom hom_refl hom_comp a0
      let eΔ := refinementStageDiagramSystemOriginalIso
        (J := J) Aδ hom hom_refl hom_comp a0
      ((refinementFiber jΔ TΔ eΔ).presheafFiber).app ((sheafToPresheaf J
        (Type (max u v w))).obj ℱ) s ≠
        ((refinementFiber jΔ TΔ eΔ).presheafFiber).app ((sheafToPresheaf J
          (Type (max u v w))).obj ℱ) s')
    {d : δ} (had : a0 ≤ d)
    {A : refinement_stage (J := J) S' (ℱ := ℱ) s s'}
    (hA0 : refinement_stage_hom (J := J) A (Aδ a0))
    (hAd : refinement_stage_hom (J := J) A (Aδ d))
    (hcoh : hAd = refinement_stage_hom.comp (J := J) hA0 (hom had))
    (r : finite_cover_lift_request J A.T) :
    (refinement_stage_hom.comp (J := J) hA0
      (refinementStageDiagramStageHomToLimit
        (J := J) Aδ hom hom_refl hom_comp a0 a0 hsep)).map_request r =
      (refinementStageDiagramStageHomToLimit
        (J := J) Aδ hom hom_refl hom_comp a0 d hsep).map_request
          (hAd.map_request r) := by
  letI : Preorder (refinementStageDiagramIndex (J := J) Aδ) :=
    refinementStageDiagramIndexPreorder (J := J) Aδ hom hom_refl hom_comp
  -- Normalize the later base morphism through the coherent factorization hypothesis.
  have hAd_map :
      hAd.map_request r = (hom had).map_request (hA0.map_request r) := by
    rw [hcoh]
    exact refinement_stage_hom.map_request_comp (J := J) hA0 (hom had) r
  -- Compare the two direct-union inclusions using the canonical transport lemma for diagrams.
  have htransport := refinementStageDiagramSystem_transport_request_of_le
    (J := J) Aδ hom hom_refl hom_comp had (hA0.map_request r)
  calc
    (refinement_stage_hom.comp (J := J) hA0
        (refinementStageDiagramStageHomToLimit
          (J := J) Aδ hom hom_refl hom_comp a0 a0 hsep)).map_request r =
        (refinementStageDiagramStageHomToLimit
          (J := J) Aδ hom hom_refl hom_comp a0 a0 hsep).map_request
          (hA0.map_request r) := by
          exact refinement_stage_hom.map_request_comp (J := J) hA0
            (refinementStageDiagramStageHomToLimit
              (J := J) Aδ hom hom_refl hom_comp a0 a0 hsep) r
    _ = (refinementStageDiagramStageHomToLimit
          (J := J) Aδ hom hom_refl hom_comp a0 d hsep).map_request
          ((hom had).map_request (hA0.map_request r)) := by
          simpa [refinement_stage_hom.map_request, refinementStageDiagramStageHomToLimit]
            using htransport
    _ = (refinementStageDiagramStageHomToLimit
          (J := J) Aδ hom hom_refl hom_comp a0 d hsep).map_request
          (hAd.map_request r) := by
          rw [hAd_map]

/-- Helper for Lemma 7.39.2: a request realized after factoring the base map through a later
stage of a coherent direct-union diagram is realized after transporting directly from the base
stage to the limit. -/
theorem stageHomToLimit_realizes_base_request_of_le
    {δ : Type w} [Preorder δ] [IsDirected δ (· ≤ ·)]
    (Aδ : δ → refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (hom : ∀ {a b : δ}, a ≤ b → refinement_stage_hom (J := J) (Aδ a) (Aδ b))
    (hom_refl :
      ∀ a : δ, hom (show a ≤ a from le_rfl) = refinement_stage_hom_refl (J := J) (Aδ a))
    (hom_comp :
      ∀ {a b c : δ} (hab : a ≤ b) (hbc : b ≤ c),
        hom (le_trans hab hbc) =
          refinement_stage_hom.comp (J := J) (hom hab) (hom hbc))
    (a0 : δ)
    (hsep :
      letI : Preorder (refinementStageDiagramIndex (J := J) Aδ) :=
        refinementStageDiagramIndexPreorder (J := J) Aδ hom hom_refl hom_comp
      let TΔ := refinementStageDiagramSystem (J := J) Aδ hom hom_refl hom_comp
      let jΔ := refinementStageDiagramSystemOriginalEmbedding
        (J := J) Aδ hom hom_refl hom_comp a0
      let eΔ := refinementStageDiagramSystemOriginalIso
        (J := J) Aδ hom hom_refl hom_comp a0
      ((refinementFiber jΔ TΔ eΔ).presheafFiber).app ((sheafToPresheaf J
        (Type (max u v w))).obj ℱ) s ≠
        ((refinementFiber jΔ TΔ eΔ).presheafFiber).app ((sheafToPresheaf J
          (Type (max u v w))).obj ℱ) s')
    {d : δ} (had : a0 ≤ d)
    {A : refinement_stage (J := J) S' (ℱ := ℱ) s s'}
    (hA0 : refinement_stage_hom (J := J) A (Aδ a0))
    (hAd : refinement_stage_hom (J := J) A (Aδ d))
    (hcoh : hAd = refinement_stage_hom.comp (J := J) hA0 (hom had))
    (r : finite_cover_lift_request J A.T)
    (hreal : request_realized (J := J) (hAd.map_request r)) :
    request_realized (J := J)
      ((refinement_stage_hom.comp (J := J) hA0
        (refinementStageDiagramStageHomToLimit
          (J := J) Aδ hom hom_refl hom_comp a0 a0 hsep)).map_request r) := by
  -- First transport the later-stage realization along the canonical inclusion into the limit.
  have hlimit :
      request_realized (J := J)
        ((refinementStageDiagramStageHomToLimit
          (J := J) Aδ hom hom_refl hom_comp a0 d hsep).map_request
            (hAd.map_request r)) :=
    refinement_stage_hom.map_request_realized (J := J)
      (refinementStageDiagramStageHomToLimit
        (J := J) Aδ hom hom_refl hom_comp a0 d hsep)
      (hAd.map_request r) hreal
  -- The comparison lemma rewrites direct base-to-limit transport through that later stage.
  rw [stageHomToLimit_map_request_base_comp_of_le
    (J := J) Aδ hom hom_refl hom_comp a0 hsep had hA0 hAd hcoh r]
  exact hlimit

/-- Helper for Lemma 7.39.2: if a request from an earlier diagram stage is realized after
transport to a later stage, then it is realized after transport to the direct-union limit. -/
theorem stageHomToLimit_realizes_request_of_le
    {δ : Type w} [Preorder δ] [IsDirected δ (· ≤ ·)]
    (Aδ : δ → refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (hom : ∀ {a b : δ}, a ≤ b → refinement_stage_hom (J := J) (Aδ a) (Aδ b))
    (hom_refl :
      ∀ a : δ, hom (show a ≤ a from le_rfl) = refinement_stage_hom_refl (J := J) (Aδ a))
    (hom_comp :
      ∀ {a b c : δ} (hab : a ≤ b) (hbc : b ≤ c),
        hom (le_trans hab hbc) =
          refinement_stage_hom.comp (J := J) (hom hab) (hom hbc))
    (a0 : δ)
    (hsep :
      letI : Preorder (refinementStageDiagramIndex (J := J) Aδ) :=
        refinementStageDiagramIndexPreorder (J := J) Aδ hom hom_refl hom_comp
      let TΔ := refinementStageDiagramSystem (J := J) Aδ hom hom_refl hom_comp
      let jΔ := refinementStageDiagramSystemOriginalEmbedding
        (J := J) Aδ hom hom_refl hom_comp a0
      let eΔ := refinementStageDiagramSystemOriginalIso
        (J := J) Aδ hom hom_refl hom_comp a0
      ((refinementFiber jΔ TΔ eΔ).presheafFiber).app ((sheafToPresheaf J
        (Type (max u v w))).obj ℱ) s ≠
        ((refinementFiber jΔ TΔ eΔ).presheafFiber).app ((sheafToPresheaf J
          (Type (max u v w))).obj ℱ) s')
    {a b : δ} (hab : a ≤ b) (r : finite_cover_lift_request J (Aδ a).T)
    (hreal : request_realized (J := J) ((hom hab).map_request r)) :
    request_realized (J := J)
      ((refinementStageDiagramStageHomToLimit
        (J := J) Aδ hom hom_refl hom_comp a0 a hsep).map_request r) := by
  -- First transport the already-realized later-stage request through the canonical inclusion
  -- of the later stage into the directed-union limit.
  have hlimit :
      request_realized (J := J)
        ((refinementStageDiagramStageHomToLimit
          (J := J) Aδ hom hom_refl hom_comp a0 b hsep).map_request
            ((hom hab).map_request r)) :=
    refinement_stage_hom.map_request_realized (J := J)
      (refinementStageDiagramStageHomToLimit
        (J := J) Aδ hom hom_refl hom_comp a0 b hsep)
      ((hom hab).map_request r) hreal
  -- The direct-union comparison lemma identifies that transport with the direct inclusion of
  -- the earlier stage.
  have hcomp :
      request_realized (J := J)
        ((refinement_stage_hom.comp (J := J) (hom hab)
          (refinementStageDiagramStageHomToLimit
            (J := J) Aδ hom hom_refl hom_comp a0 b hsep)).map_request r) := by
    rw [refinement_stage_hom.map_request_comp]
    exact hlimit
  rw [stageHomToLimit_map_request_comp_of_le
    (J := J) Aδ hom hom_refl hom_comp a0 hsep hab r] at hcomp
  exact hcomp

/-- Helper for Lemma 7.39.2: a coherent diagram on the strict predecessors of a successor-limit
cut has a direct-union stage realizing every request below that cut. -/
theorem exists_stage_realizing_lt_of_isSuccLimit
    {A : refinement_stage (J := J) S' (ℱ := ℱ) s s'}
    {req : M → finite_cover_lift_request J A.T} {x : CutΩ}
    (hx : Order.IsSuccLimit x)
    (prevStage : {y : CutΩ // y < x} →
      refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (prevHom : ∀ ⦃y z : {y : CutΩ // y < x}⦄, (y : CutΩ) ≤ z →
      refinement_stage_hom (J := J) (prevStage y) (prevStage z))
    (prevHom_refl :
      ∀ y : {y : CutΩ // y < x},
        prevHom (show (y : CutΩ) ≤ y from le_rfl) =
          refinement_stage_hom_refl (J := J) (prevStage y))
    (prevHom_comp :
      ∀ ⦃y z t : {y : CutΩ // y < x}⦄ (hyz : (y : CutΩ) ≤ z)
        (hzt : (z : CutΩ) ≤ t),
          prevHom (le_trans hyz hzt) =
            refinement_stage_hom.comp (J := J) (prevHom hyz) (prevHom hzt))
    (prevHom_compatible :
      ∀ ⦃y z : {y : CutΩ // y < x}⦄ (hyz : (y : CutΩ) ≤ z),
        (prevHom hyz).original_compatible)
    (prevFromBase : ∀ y : {y : CutΩ // y < x},
      refinement_stage_hom (J := J) A (prevStage y))
    (prevFromBase_compatible :
      ∀ y : {y : CutΩ // y < x}, (prevFromBase y).original_compatible)
    (prevFromBase_comp :
      ∀ ⦃y z : {y : CutΩ // y < x}⦄ (hyz : (y : CutΩ) ≤ z),
        prevFromBase z = refinement_stage_hom.comp (J := J) (prevFromBase y) (prevHom hyz))
    (realizes_lt :
      ∀ (y : {y : CutΩ // y < x}) (m : M), ((m : Ω) : CutΩ) < y →
        request_realized (J := J) ((prevFromBase y).map_request (req m))) :
    ∃ B : refinement_stage (J := J) S' (ℱ := ℱ) s s',
      ∃ h : refinement_stage_hom (J := J) A B,
        h.original_compatible ∧
          ∀ m : M, ((m : Ω) : CutΩ) < x →
            request_realized (J := J) (h.map_request (req m)) := by
  classical
  let δ : Type w := {y : CutΩ // y < x}
  let hom : ∀ {y z : δ}, y ≤ z →
      refinement_stage_hom (J := J) (prevStage y) (prevStage z) :=
    fun {y z} hyz => prevHom hyz
  have hom_refl :
      ∀ y : δ, hom (show y ≤ y from le_rfl) =
        refinement_stage_hom_refl (J := J) (prevStage y) := by
    intro y
    exact prevHom_refl y
  have hom_comp :
      ∀ {y z t : δ} (hyz : y ≤ z) (hzt : z ≤ t),
        hom (le_trans hyz hzt) =
          refinement_stage_hom.comp (J := J) (hom hyz) (hom hzt) := by
    intro y z t hyz hzt
    exact prevHom_comp hyz hzt
  have hom_compatible :
      ∀ {y z : δ} (hyz : y ≤ z), (hom hyz).original_compatible := by
    intro y z hyz
    exact prevHom_compatible hyz
  letI : IsDirected δ (· ≤ ·) := OpenSaturationPrefix.openCutDirected (M := M) x
  let a0 : δ := Classical.choice (OpenSaturationPrefix.succLimitOpenCut_nonempty (M := M) hx)
  -- Build the direct union of the coherent predecessor diagram.
  have hsep := refinementStageDiagramLimitStage_separated_of_compatible
    (J := J) prevStage hom hom_refl hom_comp hom_compatible a0
  let L : refinement_stage (J := J) S' (ℱ := ℱ) s s' :=
    refinementStageDiagramLimitStage
      (J := J) prevStage hom hom_refl hom_comp a0 hsep
  let toLimit : ∀ y : δ, refinement_stage_hom (J := J) (prevStage y) L :=
    fun y =>
      refinementStageDiagramStageHomToLimit
        (J := J) prevStage hom hom_refl hom_comp a0 y hsep
  let h : refinement_stage_hom (J := J) A L :=
    refinement_stage_hom.comp (J := J) (prevFromBase a0) (toLimit a0)
  refine ⟨L, h, ?_, ?_⟩
  · -- Compatibility of the base-to-limit map follows from compatibility of both factors.
    exact refinement_stage_hom.original_compatible_comp (J := J) (prevFromBase a0)
      (toLimit a0) (prevFromBase_compatible a0)
      (stageHomToLimit_original_compatible
        (J := J) prevStage hom hom_refl hom_comp a0 hsep)
  · intro m hm
    -- Choose a predecessor cut above the request cut, then a common upper bound with `a0`.
    rcases OpenSaturationPrefix.succLimitOpenCut_cofinal (M := M) hx hm with ⟨z, hmz⟩
    rcases (OpenSaturationPrefix.openCutDirected (M := M) x).directed a0 z with
      ⟨d, ha0d, hzd⟩
    have hmd : ((m : Ω) : CutΩ) < d :=
      lt_of_lt_of_le hmz hzd
    have hdreal : request_realized (J := J) ((prevFromBase d).map_request (req m)) :=
      realizes_lt d m hmd
    -- The direct-union transport lemma rewrites realization at `d` to realization in `L`.
    exact stageHomToLimit_realizes_base_request_of_le
      (J := J) prevStage hom hom_refl hom_comp a0 hsep ha0d
      (prevFromBase a0) (prevFromBase d) (prevFromBase_comp ha0d) (req m) hdreal

/-- Helper for Lemma 7.39.2: a coherent bottom-indexed saturation diagram has a direct-union
terminal stage whose base morphism realizes every scheduled request. -/
theorem exists_stage_realizing_all_of_saturationDiagram
    (A : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (req : M → finite_cover_lift_request J A.T)
    (D : SaturationDiagram (J := J) A req) :
    ∃ B : refinement_stage (J := J) S' (ℱ := ℱ) s s',
      ∃ h : refinement_stage_hom (J := J) A B,
        h.original_compatible ∧
          ∀ m : M, request_realized (J := J) (h.map_request (req m)) := by
  letI : IsDirected (WithBot M) (· ≤ ·) := withBot_directed (M := M)
  let homD : ∀ {x y : WithBot M}, x ≤ y →
      refinement_stage_hom (J := J) (D.stage x) (D.stage y) :=
    fun {x y} hxy => D.hom hxy
  have homD_refl :
      ∀ x : WithBot M, homD (show x ≤ x from le_rfl) =
        refinement_stage_hom_refl (J := J) (D.stage x) := by
    intro x
    exact D.hom_refl x
  have homD_comp :
      ∀ {x y z : WithBot M} (hxy : x ≤ y) (hyz : y ≤ z),
        homD (le_trans hxy hyz) =
          refinement_stage_hom.comp (J := J) (homD hxy) (homD hyz) := by
    intro x y z hxy hyz
    exact D.hom_comp hxy hyz
  have homD_original_compatible :
      ∀ {x y : WithBot M} (hxy : x ≤ y), (homD hxy).original_compatible := by
    intro x y hxy
    exact D.hom_original_compatible hxy
  -- Take the directed union of the coherent scheduled diagram.
  have hsep := refinementStageDiagramLimitStage_separated_of_compatible
    (J := J) D.stage homD homD_refl homD_comp homD_original_compatible
      (⊥ : WithBot M)
  let L : refinement_stage (J := J) S' (ℱ := ℱ) s s' :=
    refinementStageDiagramLimitStage
      (J := J) D.stage homD homD_refl homD_comp (⊥ : WithBot M) hsep
  let toLimit : ∀ x : WithBot M, refinement_stage_hom (J := J) (D.stage x) L :=
    fun x =>
      refinementStageDiagramStageHomToLimit
        (J := J) D.stage homD homD_refl homD_comp (⊥ : WithBot M) x hsep
  let h : refinement_stage_hom (J := J) A L :=
    refinement_stage_hom.comp (J := J) (D.fromBase ⊥) (toLimit ⊥)
  refine ⟨L, h, ?_, ?_⟩
  · -- Compatibility of the terminal base map is inherited from the base node and limit map.
    exact refinement_stage_hom.original_compatible_comp (J := J) (D.fromBase ⊥) (toLimit ⊥)
      (D.fromBase_compatible ⊥)
      (stageHomToLimit_original_compatible
        (J := J) D.stage homD homD_refl homD_comp (⊥ : WithBot M) hsep)
  · intro m
    -- A request realized at its scheduled node remains realized after inclusion into the limit.
    have hstage :
        request_realized (J := J) ((D.fromBase (m : WithBot M)).map_request (req m)) :=
      D.realizes_at m
    have hlimit :
        request_realized (J := J)
          ((toLimit (m : WithBot M)).map_request
            ((D.fromBase (m : WithBot M)).map_request (req m))) :=
      refinement_stage_hom.map_request_realized (J := J) (toLimit (m : WithBot M))
        ((D.fromBase (m : WithBot M)).map_request (req m)) hstage
    -- The direct-union transport adapter rewrites the limit transport as the terminal base map.
    have hmap := stageHomToLimit_map_request_base_comp_of_le
      (J := J) D.stage homD homD_refl homD_comp (⊥ : WithBot M) hsep
      (bot_le : (⊥ : WithBot M) ≤ (m : WithBot M)) (D.fromBase ⊥)
      (D.fromBase (m : WithBot M))
      (D.fromBase_comp (bot_le : (⊥ : WithBot M) ≤ (m : WithBot M))) (req m)
    rw [← hmap] at hlimit
    exact hlimit
end

end ScheduledSaturation

end CategoryTheory
