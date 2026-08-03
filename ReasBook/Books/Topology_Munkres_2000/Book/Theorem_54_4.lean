module

public import Topology_Munkres_2000.Book.Definition_54_2.LiftingCorrespondence
import all Topology_Munkres_2000.Book.Definition_54_2.LiftingCorrespondence

public section

universe u v

namespace IsCoveringMap

variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]

/-- Helper for Theorem 54.4: casting both endpoints of a path-homotopy class is injective. -/
private lemma pathClassCast_injective {X : Type*} [TopologicalSpace X]
    {a b a' b' : X} (ha : a' = a) (hb : b' = b) :
    Function.Injective (fun γ : Path.Homotopic.Quotient a b ↦ γ.cast ha hb) := by
  -- After eliminating the endpoint equalities, the cast is the identity.
  intro γ δ hγδ
  cases ha
  cases hb
  simpa only [Path.Homotopic.Quotient.cast_rfl_rfl] using hγδ

/-- Helper for Theorem 54.4: a mapped path upstairs has the expected monodromy endpoint
after transporting its endpoints to chosen base points. -/
private lemma monodromy_map_cast {p : E → B} (hp : IsCoveringMap p)
    {e₀ e₁ : E} {b₀ b₁ : B} (h₀ : p e₀ = b₀) (h₁ : p e₁ = b₁)
    (Γ : Path.Homotopic.Quotient e₀ e₁) :
    hp.monodromy ((Γ.map ⟨p, hp.continuous⟩).cast h₀.symm h₁.symm) ⟨e₀, h₀⟩ =
      ⟨e₁, h₁⟩ := by
  -- The monodromy computation reduces to cancelling the two successive endpoint casts.
  refine hp.monodromy_eq_of_map_eq Γ ?_
  simp only [Path.Homotopic.Quotient.cast_cast,
    Path.Homotopic.Quotient.cast_rfl_rfl]

/-- Helper for Theorem 54.4: monodromy at a chosen fiber point is surjective when the
total space is path connected. -/
private lemma monodromy_apply_surjective {p : E → B} (hp : IsCoveringMap p) {b₀ : B}
    (e₀ : p ⁻¹' {b₀}) [PathConnectedSpace E] :
    Function.Surjective (fun γ : FundamentalGroup B b₀ ↦ hp.monodromy γ e₀) := by
  intro e₁
  -- Join the chosen lift to the requested fiber point and project that path to the base.
  let Γ : Path.Homotopic.Quotient (e₀ : E) (e₁ : E) :=
    Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath (e₀ : E) (e₁ : E))
  refine ⟨(Γ.map ⟨p, hp.continuous⟩).cast e₀.2.symm e₁.2.symm, ?_⟩
  -- The cast-compatible monodromy computation identifies its lifted endpoint with `e₁`.
  exact monodromy_map_cast hp e₀.2 e₁.2 Γ

/-- Helper for Theorem 54.4: mapping an endpoint-aligned lifted path recovers the original
base path with the corresponding endpoint casts. -/
private lemma map_liftPathQuotient_cast {p : E → B} (hp : IsCoveringMap p) {b₀ : B}
    (e₀ : p ⁻¹' {b₀}) (γ δ : FundamentalGroup B b₀)
    (h : hp.monodromy γ e₀ = hp.monodromy δ e₀) :
    ((hp.liftPathQuotient δ e₀).cast rfl (congrArg Subtype.val h)).map
        ⟨p, hp.continuous⟩ =
      Path.Homotopic.Quotient.cast δ e₀.2 (hp.monodromy γ e₀).2 := by
  -- Mapping commutes with the alignment cast, after which the lift computation applies.
  simp only [Path.Homotopic.Quotient.map_cast, hp.map_liftPathQuotient,
    Path.Homotopic.Quotient.cast_cast]

/-- Helper for Theorem 54.4: over a simply connected total space, monodromy at one point
of a fiber is injective on the fundamental group. -/
private lemma monodromy_apply_injective {p : E → B} (hp : IsCoveringMap p) {b₀ : B}
    (e₀ : p ⁻¹' {b₀}) [SimplyConnectedSpace E] :
    Function.Injective (fun γ : FundamentalGroup B b₀ ↦ hp.monodromy γ e₀) := by
  intro γ δ h
  -- Align the two lifted endpoints; simple connectedness then identifies the lifted classes.
  have hlifts :
      hp.liftPathQuotient γ e₀ =
        (hp.liftPathQuotient δ e₀).cast rfl (congrArg Subtype.val h) :=
    Subsingleton.elim _ _
  -- Project that equality to the base and normalize both mapped lifts.
  have hcasts :
      Path.Homotopic.Quotient.cast γ e₀.2 (hp.monodromy γ e₀).2 =
        Path.Homotopic.Quotient.cast δ e₀.2 (hp.monodromy γ e₀).2 := by
    calc
      Path.Homotopic.Quotient.cast γ e₀.2 (hp.monodromy γ e₀).2 =
          (hp.liftPathQuotient γ e₀).map ⟨p, hp.continuous⟩ :=
        (hp.map_liftPathQuotient γ e₀).symm
      _ = ((hp.liftPathQuotient δ e₀).cast rfl
          (congrArg Subtype.val h)).map ⟨p, hp.continuous⟩ :=
        congrArg
          (fun Γ : Path.Homotopic.Quotient (e₀ : E) (hp.monodromy γ e₀ : E) ↦
            Γ.map ⟨p, hp.continuous⟩)
          hlifts
      _ = Path.Homotopic.Quotient.cast δ e₀.2 (hp.monodromy γ e₀).2 :=
        map_liftPathQuotient_cast hp e₀ γ δ h
  -- The common endpoint transport is injective, so the original loop classes agree.
  exact pathClassCast_injective e₀.2 (hp.monodromy γ e₀).2 hcasts

/-- Helper for Theorem 54.4: monodromy at a chosen fiber point is bijective when the
total space is simply connected. -/
private lemma monodromy_apply_bijective {p : E → B} (hp : IsCoveringMap p) {b₀ : B}
    (e₀ : p ⁻¹' {b₀}) [SimplyConnectedSpace E] :
    Function.Bijective (fun γ : FundamentalGroup B b₀ ↦ hp.monodromy γ e₀) := by
  -- Combine endpoint injectivity with path-connected surjectivity.
  exact ⟨monodromy_apply_injective hp e₀, monodromy_apply_surjective hp e₀⟩

/-- Theorem 54.4 (1). If the total space of a covering map is path connected, its
lifting correspondence at any chosen point of a fiber is surjective. -/
theorem liftingCorrespondence_surjective {p : E → B} (hp : IsCoveringMap p) {b₀ : B}
    (e₀ : p ⁻¹' {b₀}) [PathConnectedSpace E] :
    Function.Surjective (hp.liftingCorrespondence e₀) := by
  -- Route correction: the full prerequisite import exposes the correspondence's defining
  -- monodromy expression, so its established surjectivity closes the goal directly.
  exact monodromy_apply_surjective hp e₀

/-- Companion to Theorem 54.4: if the total space of a covering map is simply connected,
its lifting correspondence at any chosen point of a fiber is bijective. -/
theorem liftingCorrespondence_bijective {p : E → B} (hp : IsCoveringMap p) {b₀ : B}
    (e₀ : p ⁻¹' {b₀}) [SimplyConnectedSpace E] :
    Function.Bijective (hp.liftingCorrespondence e₀) := by
  -- Route correction: after the same definitional normalization, combine the already proved
  -- monodromy injectivity and surjectivity in one step.
  exact monodromy_apply_bijective hp e₀

end IsCoveringMap
