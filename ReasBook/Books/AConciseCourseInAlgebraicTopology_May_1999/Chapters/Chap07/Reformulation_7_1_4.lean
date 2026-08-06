import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap06.Reformulation_6_1_6
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap07.Definition_7_1_2

open scoped unitInterval

universe u v w

variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]

-- Semantic recall via `lean_leansearch`: `ContinuousMap.curry` models homotopies as maps
-- `A → C(I, B)`, and `ContinuousMap.continuous_postcomp` gives the canonical postcomposition map
-- on path spaces. Chapter 6 already uses `pathSpaceEvalAtZero` for evaluation at `0`, while
-- `Definition 7.1.2` now owns the source-facing class `HasCoveringHomotopyProperty`.

/-- Postcomposition by `p` sends a path in `E` to its image path in `B`. -/
abbrev pathSpacePostcompose (p : C(E, B)) : C(C(I, E), C(I, B)) where
  toFun γ := p.comp γ
  continuous_toFun := ContinuousMap.continuous_postcomp p

/-- Applying `pathSpacePostcompose p` to a path is composition with `p`. -/
@[simp] theorem pathSpacePostcompose_apply (p : C(E, B)) (γ : C(I, E)) :
    pathSpacePostcompose p γ = p.comp γ := rfl

/-- Evaluating the image path under `p` at time `t` agrees with first evaluating the original path
at `t` and then applying `p`. -/
@[simp] theorem pathSpaceEvalAt_comp_pathSpacePostcompose (p : C(E, B)) (t : I) :
    (pathSpaceEvalAt t B).comp (pathSpacePostcompose p) = p.comp (pathSpaceEvalAt t E) := by
  ext γ
  rfl

/-- Reformulation 7.1.4: the CHP for `p` is equivalent to the path-space lifting problem in which
`pathSpaceEvalAtZero` evaluates paths at their initial point. -/
theorem hasCoveringHomotopyProperty_iff_lift_pathSpaceEvalAtZero (p : C(E, B)) :
    HasCoveringHomotopyProperty.{u, v, w} p ↔
      ∀ ⦃A : Type w⦄ [TopologicalSpace A]
        [CompactlyGeneratedWeakHausdorffSpace.{w, w} A]
        (g₀ : C(A, E)) (d : C(A, C(I, B))),
        (pathSpaceEvalAtZero B).comp d = p.comp g₀ →
          ∃ D : C(A, C(I, E)),
            (pathSpaceEvalAtZero E).comp D = g₀ ∧ (pathSpacePostcompose p).comp D = d := by
  constructor
  · intro hp A hA hAcg g₀ d hd
    let H : (p.comp g₀).Homotopy ((pathSpaceEvalAt 1 B).comp d) :=
      ContinuousMap.Homotopy.ofPathSpaceMap d hd rfl
    have hLift : ∃ g₁ : C(A, E), ∃ G : g₀.Homotopy g₁,
        p.comp G.toContinuousMap = H.toContinuousMap := by
      simpa [H] using hp.homotopyLift H rfl
    obtain ⟨_, G, hG⟩ := hLift
    refine ⟨G.toPathSpaceMap, G.pathSpaceEvalAtZero_comp_toPathSpaceMap, ?_⟩
    ext a t
    simpa using ContinuousMap.congr_fun hG (t, a)
  · intro h
    refine ⟨fun {A} _ _ {f₀ f₁} H {g₀} hg₀ ↦ ?_⟩
    obtain ⟨D, hD₀, hD⟩ :=
      h g₀ H.toPathSpaceMap (H.pathSpaceEvalAtZero_comp_toPathSpaceMap.trans hg₀.symm)
    refine ⟨(pathSpaceEvalAt 1 E).comp D, ContinuousMap.Homotopy.ofPathSpaceMap D hD₀ rfl, ?_⟩
    ext z
    rcases z with ⟨t, a⟩
    simpa using ContinuousMap.congr_fun (ContinuousMap.congr_fun hD a) t
