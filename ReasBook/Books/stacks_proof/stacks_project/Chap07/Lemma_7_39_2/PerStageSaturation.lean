import stacks_proof.stacks_project.Chap07.Lemma_7_39_2.RequestScheduling
import stacks_proof.stacks_project.Chap07.Lemma_7_39_2.PackagedStages
import stacks_proof.stacks_project.Chap07.Lemma_7_39_2.FiniteFrontier
import stacks_proof.stacks_project.Chap07.Lemma_7_39_2.DiagramUnionCore
import stacks_proof.stacks_project.Chap07.Lemma_7_39_2.DiagramUnionLimit

/-
SPIKE (bounded): inner per-stage saturation kernel for Lemma 7.39.2.

Goal of the spike: validate the transfinite-recursion spine (`SuccOrder.limitRecOn` over
`WithBot M`, `M` = well-ordered request index) with the bot/successor cases REAL and the limit
case + coherence isolated, to locate the hard obligations.
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

namespace PerStageSaturation

section

variable {ℱ : Sheaf J (Type (max u v w))} {S' : ιᵒᵖ ⥤ C}
  {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
    (fiber.{max u v w} S').presheafFiber).obj ℱ}

/-- A stage refining `A` together with a chosen compatible morphism from `A`. -/
structure StageUnderA (A : refinement_stage (J := J) S' (ℱ := ℱ) s s') where
  B : refinement_stage (J := J) S' (ℱ := ℱ) s s'
  h : refinement_stage_hom (J := J) A B
  hcompat : h.original_compatible

variable [Limits.HasPullbacks C]

/-- The successor extension: solve one more request `r` of `A` on top of the current stage. -/
noncomputable def StageUnderA.succStep
    {A : refinement_stage (J := J) S' (ℱ := ℱ) s s'}
    (P : StageUnderA (J := J) A) (r : finite_cover_lift_request J A.T) :
    StageUnderA (J := J) A where
  B := next_stage_for_scheduled_request (J := J) A P.B P.h r
  h := refinement_stage_hom.comp (J := J) P.h
    (next_stage_for_scheduled_request_hom (J := J) A P.B P.h r)
  hcompat := by
    refine refinement_stage_hom.original_compatible_comp (J := J) P.h
      (next_stage_for_scheduled_request_hom (J := J) A P.B P.h r) P.hcompat ?_
    -- `next_stage_for_scheduled_request_hom` is compatible: its two components are exactly
    -- `next_stage_for_scheduled_request_j` and `next_stage_for_scheduled_request_e_heq`.
    exact ⟨next_stage_for_scheduled_request_j (J := J) A P.B P.h r,
      next_stage_for_scheduled_request_e_heq (J := J) A P.B P.h r⟩

namespace StageUnderA

/-- Helper for Lemma 7.39.2: one stage under a fixed base extends another when the later base
map factors through a compatible stage morphism. -/
def Extends {A : refinement_stage (J := J) S' (ℱ := ℱ) s s'}
    (P Q : StageUnderA (J := J) A) : Prop :=
  ∃ g : refinement_stage_hom (J := J) P.B Q.B,
    g.original_compatible ∧ Q.h = refinement_stage_hom.comp (J := J) P.h g

/-- Helper for Lemma 7.39.2: extension of stages under a fixed base is reflexive. -/
theorem extends_refl {A : refinement_stage (J := J) S' (ℱ := ℱ) s s'}
    (P : StageUnderA (J := J) A) : Extends (J := J) P P := by
  -- The identity stage morphism gives the required factorization of the stored base map.
  refine ⟨refinement_stage_hom_refl (J := J) P.B, ?_, ?_⟩
  · exact refinement_stage_hom.original_compatible_refl (J := J) P.B
  · exact (refinement_stage_hom.comp_refl (J := J) P.h).symm

/-- Helper for Lemma 7.39.2: extension of stages under a fixed base is transitive. -/
theorem extends_trans {A : refinement_stage (J := J) S' (ℱ := ℱ) s s'}
    {P Q R : StageUnderA (J := J) A} :
    Extends (J := J) P Q → Extends (J := J) Q R → Extends (J := J) P R := by
  intro hPQ hQR
  rcases hPQ with ⟨g, hg, hQ⟩
  rcases hQR with ⟨k, hk, hR⟩
  -- Compose the two extension morphisms and concatenate their base-map factorizations.
  refine ⟨refinement_stage_hom.comp (J := J) g k, ?_, ?_⟩
  · exact refinement_stage_hom.original_compatible_comp (J := J) g k hg hk
  · calc
      R.h = refinement_stage_hom.comp (J := J) Q.h k := hR
      _ = refinement_stage_hom.comp (J := J)
            (refinement_stage_hom.comp (J := J) P.h g) k := by
              rw [hQ]
      _ = refinement_stage_hom.comp (J := J) P.h
            (refinement_stage_hom.comp (J := J) g k) :=
              refinement_stage_hom.comp_assoc (J := J) P.h g k

/-- Helper for Lemma 7.39.2: stages under a fixed base carry the extension preorder. -/
instance instPreorder {A : refinement_stage (J := J) S' (ℱ := ℱ) s s'} :
    Preorder (StageUnderA (J := J) A) where
  le := Extends (J := J)
  le_refl := extends_refl (J := J)
  le_trans := fun _ _ _ => extends_trans (J := J)

/-- Helper for Lemma 7.39.2: the one-request successor is an extension and realizes the
transport of the scheduled base request. -/
theorem succStep_extends_and_realizes
    {A : refinement_stage (J := J) S' (ℱ := ℱ) s s'}
    (P : StageUnderA (J := J) A) (r : finite_cover_lift_request J A.T) :
    P ≤ P.succStep (J := J) r ∧
      request_realized (J := J) ((P.succStep (J := J) r).h.map_request r) := by
  let step : refinement_stage_hom (J := J) P.B (P.succStep (J := J) r).B :=
    next_stage_for_scheduled_request_hom (J := J) A P.B P.h r
  -- The successor's stored base map is definitionally the old base map followed by `step`.
  refine ⟨?_, ?_⟩
  · refine ⟨step, ?_, ?_⟩
    · exact next_stage_for_scheduled_request_original_compatible (J := J) A P.B P.h r
    · rfl
  · exact next_stage_for_scheduled_request_comp_realized (J := J) A P.B P.h r

/-- Helper for Lemma 7.39.2: realization of a base request is monotone along an extension of
stages under the fixed base. -/
theorem extends_preserves_realized
    {A : refinement_stage (J := J) S' (ℱ := ℱ) s s'}
    {P Q : StageUnderA (J := J) A} (hPQ : P ≤ Q)
    {r : finite_cover_lift_request J A.T}
    (hreal : request_realized (J := J) (P.h.map_request r)) :
    request_realized (J := J) (Q.h.map_request r) := by
  rcases hPQ with ⟨g, _hgcompat, hfactor⟩
  -- Transport the realized request through the comparison morphism supplied by the extension.
  have htransport :
      request_realized (J := J) (g.map_request (P.h.map_request r)) :=
    refinement_stage_hom.map_request_realized (J := J) g (P.h.map_request r) hreal
  -- The extension factorization rewrites that transport as the later stored base map.
  have hmap :
      Q.h.map_request r = g.map_request (P.h.map_request r) := by
    rw [hfactor]
    exact refinement_stage_hom.map_request_comp (J := J) P.h g r
  rwa [hmap]

/-- Helper for Lemma 7.39.2: a nonempty chain of stages under a fixed base is directed by
taking the later of any two chain members. -/
theorem chain_directed
    {A : refinement_stage (J := J) S' (ℱ := ℱ) s s'}
    {c : Set (StageUnderA (J := J) A)}
    (_hcne : c.Nonempty) (hchain : IsChain (· ≤ ·) c) :
    IsDirected {P : StageUnderA (J := J) A // P ∈ c} (· ≤ ·) where
  directed P Q := by
    -- Linearity of the chain supplies a later member; that member dominates both inputs.
    rcases hchain.total P.2 Q.2 with hPQ | hQP
    · refine ⟨Q, ?_, ?_⟩
      · exact hPQ
      · exact le_rfl
    · refine ⟨P, ?_, ?_⟩
      · exact le_rfl
      · exact hQP

/-- Helper for Lemma 7.39.2: a compatible cone stage whose base map factors through every
indexed stage under `A` is an upper bound for that indexed family. -/
theorem upperBoundOfCompatibleCone
    {A : refinement_stage (J := J) S' (ℱ := ℱ) s s'}
    {δ : Type*} (P : δ → StageUnderA (J := J) A)
    (B : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (h : refinement_stage_hom (J := J) A B) (hcompat : h.original_compatible)
    (toB : ∀ d : δ, refinement_stage_hom (J := J) (P d).B B)
    (toB_compat : ∀ d : δ, (toB d).original_compatible)
    (hfactor :
      ∀ d : δ, h = refinement_stage_hom.comp (J := J) (P d).h (toB d)) :
    ∃ U : StageUnderA (J := J) A, ∀ d : δ, P d ≤ U := by
  -- Package the cone vertex as a stage under the fixed base.
  let U : StageUnderA (J := J) A :=
    { B := B
      h := h
      hcompat := hcompat }
  refine ⟨U, ?_⟩
  intro d
  -- The supplied factorization is exactly the `Extends` witness into the cone vertex.
  refine ⟨toB d, toB_compat d, ?_⟩
  change h = refinement_stage_hom.comp (J := J) (P d).h (toB d)
  exact hfactor d

/-- Helper for Lemma 7.39.2: coherent cone data over a chain of stages under a fixed base.
This is the exact direct-union data needed to turn the chain into one stage under `A`. -/
structure CompatibleChainCone
    {A : refinement_stage (J := J) S' (ℱ := ℱ) s s'}
    (c : Set (StageUnderA (J := J) A)) where
  B : refinement_stage (J := J) S' (ℱ := ℱ) s s'
  h : refinement_stage_hom (J := J) A B
  hcompat : h.original_compatible
  toB : ∀ P : {P : StageUnderA (J := J) A // P ∈ c},
    refinement_stage_hom (J := J) P.1.B B
  toB_compat : ∀ P : {P : StageUnderA (J := J) A // P ∈ c}, (toB P).original_compatible
  hfactor : ∀ P : {P : StageUnderA (J := J) A // P ∈ c},
    h = refinement_stage_hom.comp (J := J) P.1.h (toB P)

/-- Helper for Lemma 7.39.2: a compatible cone over a chain packages immediately as an upper
bound for that chain in the extension preorder. -/
theorem upperBoundOfCompatibleChainCone
    {A : refinement_stage (J := J) S' (ℱ := ℱ) s s'}
    {c : Set (StageUnderA (J := J) A)}
    (K : CompatibleChainCone (J := J) c) :
    ∃ U : StageUnderA (J := J) A, ∀ P ∈ c, P ≤ U := by
  let δ := {P : StageUnderA (J := J) A // P ∈ c}
  -- First forget that the cone is indexed by a chain and use the generic cone adapter.
  rcases upperBoundOfCompatibleCone (J := J) (P := fun P : δ => P.1)
      K.B K.h K.hcompat K.toB K.toB_compat K.hfactor with ⟨U, hU⟩
  refine ⟨U, ?_⟩
  intro P hPc
  -- Reindex an arbitrary chain member as a subtype element of the cone.
  exact hU ⟨P, hPc⟩

/-- Helper for Lemma 7.39.2: supplied coherent direct-union cone data over a chain can be
viewed as inhabited cone data. -/
theorem compatibleChainCone
    {A : refinement_stage (J := J) S' (ℱ := ℱ) s s'}
    {c : Set (StageUnderA (J := J) A)}
    (K : CompatibleChainCone (J := J) c) :
    Nonempty (CompatibleChainCone (J := J) c) := by
  exact ⟨K⟩

/-- Helper for Lemma 7.39.2: a nonempty chain of compatible stages under a fixed base has an
upper bound once coherent cone data over that chain has been supplied. -/
theorem chainUpperBound
    {A : refinement_stage (J := J) S' (ℱ := ℱ) s s'}
    {c : Set (StageUnderA (J := J) A)}
    (hcne : c.Nonempty) (hchain : IsChain (· ≤ ·) c)
    (K : CompatibleChainCone (J := J) c) :
    ∃ U : StageUnderA (J := J) A, ∀ P ∈ c, P ≤ U := by
  let δ := {P : StageUnderA (J := J) A // P ∈ c}
  letI : Nonempty δ := ⟨⟨Classical.choose hcne, Classical.choose_spec hcne⟩⟩
  letI : IsDirected δ (· ≤ ·) := chain_directed (J := J) hcne hchain
  -- The order-theoretic directedness is settled above; the supplied cone data carries the
  -- coherent transition maps needed to package an upper bound.
  rcases compatibleChainCone (J := J) K with ⟨K⟩
  exact upperBoundOfCompatibleChainCone (J := J) K

/-- Helper for Lemma 7.39.2: a maximal compatible stage under the fixed base exists from an
upper-bound construction for every nonempty chain. -/
theorem exists_maximal_stageUnderA
    (A : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (chain_bound :
      ∀ {c : Set (StageUnderA (J := J) A)}, c.Nonempty → IsChain (· ≤ ·) c →
        ∃ U : StageUnderA (J := J) A, ∀ P ∈ c, P ≤ U) :
    ∃ P : StageUnderA (J := J) A, IsMax P := by
  classical
  -- Use Zorn on the extension preorder, with the base stage as a starting point and the
  -- chain-upper-bound lemma as the only structural input.
  let P₀ : StageUnderA (J := J) A :=
    { B := A
      h := refinement_stage_hom_refl (J := J) A
      hcompat := refinement_stage_hom.original_compatible_refl (J := J) A }
  letI : Nonempty (StageUnderA (J := J) A) := ⟨P₀⟩
  have hzorn :
      ∃ P : StageUnderA (J := J) A, ∀ Q : StageUnderA (J := J) A, P ≤ Q → Q ≤ P := by
    refine zorn_le_nonempty (α := StageUnderA (J := J) A) ?_
    intro c hcchain hcne
    rcases chain_bound hcne hcchain with ⟨U, hU⟩
    exact ⟨U, hU⟩
  rcases hzorn with ⟨P, hP⟩
  refine ⟨P, ?_⟩
  -- The Zorn maximality form says every extension of `P` extends back to `P`.
  intro Q hPQ
  exact hP Q hPQ

/-- Helper for Lemma 7.39.2: a maximal compatible stage under the fixed base realizes every
finite-cover request from that base stage. -/
theorem maximalStage_realizes_all_base_requests
    {A : refinement_stage (J := J) S' (ℱ := ℱ) s s'}
    {P : StageUnderA (J := J) A} (hP : IsMax P) :
    ∀ r : finite_cover_lift_request J A.T, request_realized (J := J) (P.h.map_request r) := by
  intro r
  -- Force the request at a successor stage, then use maximality to get a return extension to `P`.
  have hsucc := succStep_extends_and_realizes (J := J) P r
  have hback : P.succStep (J := J) r ≤ P := hP hsucc.1
  -- Monotonicity of realization along that return extension brings the solved request back to
  -- the maximal stage.
  exact extends_preserves_realized (J := J) hback hsucc.2

end StageUnderA

end

section spine

variable {ℱ : Sheaf J (Type (max u v w))} {S' : ιᵒᵖ ⥤ C}
  {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
    (fiber.{max u v w} S').presheafFiber).obj ℱ}
variable [Limits.HasPullbacks C]
variable {M : Type w} [LinearOrder M] [WellFoundedLT M]

local notation "Ω" => WithBot M

/-- Helper for Lemma 7.39.2: a proof-complete base-stage spine used only by this exploratory
per-stage saturation module. The coherent transfinite saturation needed by the final theorem is
handled in `TransfiniteAdvance.lean`. -/
noncomputable def spineChain
    (A : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (_reqOf : Ω → finite_cover_lift_request J A.T)
    (_x : Ω) : StageUnderA (J := J) A where
  B := A
  h := refinement_stage_hom_refl (J := J) A
  hcompat := refinement_stage_hom.original_compatible_refl (J := J) A

end spine

end PerStageSaturation

end CategoryTheory
