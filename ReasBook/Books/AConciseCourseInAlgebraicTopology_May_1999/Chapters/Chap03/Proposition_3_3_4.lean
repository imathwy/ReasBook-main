import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic
import Mathlib.CategoryTheory.FiberedCategory.Fiber
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap03.Definition_3_1_5
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap03.Theorem_3_2_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap03.Definition_3_3_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open CategoryTheory FundamentalGroupoid Path.Homotopic.Quotient

variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]

namespace IsPathConnectedCoveringMap

variable {p : E → B}

/-- The functor on fundamental groupoids induced by a path-connected covering map. -/
noncomputable abbrev fundamentalGroupoidMap (hp : IsPathConnectedCoveringMap p) :
    FundamentalGroupoid E ⥤ FundamentalGroupoid B :=
  FundamentalGroupoid.map ⟨p, hp.isCoveringMap.continuous⟩

/-- On objects, `hp.fundamentalGroupoidMap` sends `e` to `p e`. -/
@[simp] theorem fundamentalGroupoidMap_obj_mk (hp : IsPathConnectedCoveringMap p) (e : E) :
    hp.fundamentalGroupoidMap.obj (mk e) = mk (p e) := rfl

/-- The underlying point of the image of an object under `hp.fundamentalGroupoidMap` is its image
under `p`. -/
@[simp] theorem fundamentalGroupoidMap_obj_as (hp : IsPathConnectedCoveringMap p)
    (x : FundamentalGroupoid E) :
    FundamentalGroupoid.as (hp.fundamentalGroupoidMap.obj x) = p x.as := by
  cases x
  rfl

private theorem fundamentalGroupoidMap_obj_eq (hp : IsPathConnectedCoveringMap p) {b : B}
    (e : p ⁻¹' {b}) : hp.fundamentalGroupoidMap.obj (mk e.1) = mk b := by
  simpa using congrArg mk e.2

/-- The fiber of the induced functor on fundamental groupoids over `mk b` identifies with the
ordinary fiber of the covering map over `b`. -/
noncomputable def fundamentalGroupoidMapFiberEquiv (hp : IsPathConnectedCoveringMap p) (b : B) :
    hp.fundamentalGroupoidMap.Fiber (mk b) ≃ p ⁻¹' {b} where
  toFun x := ⟨x.1.as, by
    simpa using congrArg FundamentalGroupoid.as x.2⟩
  invFun e := ⟨mk e.1, fundamentalGroupoidMap_obj_eq hp e⟩
  left_inv x := by
    rcases x with ⟨x, hx⟩
    apply Subtype.ext
    ext
    rfl
  right_inv e := by
    apply Subtype.ext
    rfl

/-- Helper for Proposition 3.3.4: once the endpoint is fixed, the induced map on fundamental-
groupoid morphisms is injective. -/
private theorem fundamentalGroupoidMap_hom_injective (hp : IsPathConnectedCoveringMap p) (e y : E) :
    Function.Injective fun f : mk e ⟶ mk y ↦ hp.fundamentalGroupoidMap.map f := by
  -- This is Theorem 3.2.3 in the fundamental-groupoid language.
  simpa [IsPathConnectedCoveringMap.fundamentalGroupoidMap, FundamentalGroupoid.map_eq] using
    hp.isCoveringMap.injective_path_homotopic_map e y

/-- The endpoint of the lifted representative path lies over the target endpoint of the base
path. -/
theorem liftPath_endpoint_eq_target (hp : IsPathConnectedCoveringMap p) {b : B}
    (e : E) (γ : Path (p e) b) :
    p (hp.isCoveringMap.liftPath γ e γ.source 1) = b := by
  -- Evaluate the projection of the lifted path at the endpoint.
  simpa using (congr_fun (hp.isCoveringMap.liftPath_lifts γ e γ.source) 1).trans γ.target

/-- Projecting the chosen lifted path back to the base recovers the original representative path
after the canonical endpoint cast. -/
theorem liftPath_projection_eq_path (hp : IsPathConnectedCoveringMap p) {b : B}
    (e : E) (γ : Path (p e) b) :
    ((Path.mk (hp.isCoveringMap.liftPath γ e γ.source)
      (hp.isCoveringMap.liftPath_zero γ e γ.source) rfl).map hp.isCoveringMap.continuous).cast rfl
      (liftPath_endpoint_eq_target hp e γ).symm = γ := by
  -- The lifted path was defined so that its projection agrees pointwise with `γ`.
  ext t
  simpa using congr_fun (hp.isCoveringMap.liftPath_lifts γ e γ.source) t

/-- On homotopy classes, the projected lifted path class is the original base path class after the
canonical endpoint cast. -/
theorem liftPath_projection_eq_quotient (hp : IsPathConnectedCoveringMap p) {b : B}
    (e : E) (γ : Path (p e) b) :
    Path.Homotopic.Quotient.mk
        ((((Path.mk (hp.isCoveringMap.liftPath γ e γ.source)
            (hp.isCoveringMap.liftPath_zero γ e γ.source) rfl).map
          hp.isCoveringMap.continuous).cast rfl
          (liftPath_endpoint_eq_target hp e γ).symm)) =
      Path.Homotopic.Quotient.mk γ := by
  exact congrArg Path.Homotopic.Quotient.mk (liftPath_projection_eq_path hp e γ)

/-- Helper for Proposition 3.3.4: transport of a path-homotopy class along an endpoint equality
agrees with the explicit `Path.Homotopic.Quotient.cast`. -/
private theorem quotient_cast_eq {x y z : B} (q : Path.Homotopic.Quotient x z) (h : y = z) :
    cast (congrArg (Path.Homotopic.Quotient x) h.symm) q = q.cast rfl h := by
  -- Both sides are the same transport; only the packaging differs.
  apply eq_of_heq
  cases h
  simp

/-- Changing the endpoint of a path class by an equality only changes the codomain bookkeeping of
the corresponding `Under.mk` object. -/
theorem under_mk_fromPath_cast_eq {x y z : B} (q : Path.Homotopic.Quotient x z)
    (h : y = z) :
    (Under.mk (fromPath q) : Under (mk x)) = Under.mk (fromPath (q.cast rfl h)) := by
  -- After identifying the endpoints, the cast is trivial.
  cases h
  simp

/-- Helper for Proposition 3.3.4: every arrow in the star of `mk (p e)` has a preimage obtained by
lifting a representative path from `e`. -/
private theorem fundamentalGroupoidMap_star_surjective (hp : IsPathConnectedCoveringMap p) (e : E) :
    Function.Surjective
      ((Under.post hp.fundamentalGroupoidMap : Under (mk e) ⥤ Under (mk (p e))).obj) := by
  intro y
  -- Reduce the target star object to a single representative path in the base.
  obtain ⟨⟨b⟩, f, rfl⟩ := Under.mk_surjective y
  obtain ⟨γ, rfl⟩ := mk_surjective f
  let δ : Path e (hp.isCoveringMap.liftPath γ e γ.source 1) :=
    Path.mk (hp.isCoveringMap.liftPath γ e γ.source)
      (hp.isCoveringMap.liftPath_zero γ e γ.source) rfl
  let qδ : Path.Homotopic.Quotient e (hp.isCoveringMap.liftPath γ e γ.source 1) := ⟦δ⟧
  refine ⟨Under.mk (fromPath qδ), ?_⟩
  have hproj_eq :
      (qδ.map
          ⟨p, hp.isCoveringMap.continuous⟩).cast rfl
        (liftPath_endpoint_eq_target hp e γ).symm =
        ⟦γ⟧ := by
    -- Move the map through the quotient and use the pointwise projection identity.
    change ⟦(((Path.mk (hp.isCoveringMap.liftPath γ e γ.source)
          (hp.isCoveringMap.liftPath_zero γ e γ.source) rfl).map
            hp.isCoveringMap.continuous).cast rfl
          (liftPath_endpoint_eq_target hp e γ).symm)⟧ =
      ⟦γ⟧
    exact congrArg (fun η ↦ ⟦η⟧) (liftPath_projection_eq_path hp e γ)
  have hleft :
      Under.mk (fromPath (qδ.map
        ⟨p, hp.isCoveringMap.continuous⟩)) =
        Under.mk (fromPath ((qδ.map
          ⟨p, hp.isCoveringMap.continuous⟩).cast rfl
            (liftPath_endpoint_eq_target hp e γ).symm)) :=
    -- Replace the literal codomain by the endpoint identified from the lifted path.
    under_mk_fromPath_cast_eq _ (liftPath_endpoint_eq_target hp e γ).symm
  -- The chosen lifted representative maps back to the original base-star object.
  exact (by
    simpa [Under.post, FundamentalGroupoid.fromPath, qδ] using
      hleft.trans (congrArg Under.mk (congrArg fromPath hproj_eq)))

/-- Helper for Proposition 3.3.4: uniqueness of lifted representatives makes the induced star map
injective. -/
private theorem fundamentalGroupoidMap_star_injective (hp : IsPathConnectedCoveringMap p) (e : E) :
    Function.Injective
      ((Under.post hp.fundamentalGroupoidMap : Under (mk e) ⥤ Under (mk (p e))).obj) := by
  intro u v h
  -- Write both star objects as actual path classes starting at `e`.
  obtain ⟨⟨e₁⟩, fu, rfl⟩ := Under.mk_surjective u
  obtain ⟨⟨e₂⟩, fv, rfl⟩ := Under.mk_surjective v
  obtain ⟨γu, rfl⟩ := mk_surjective fu
  obtain ⟨γv, rfl⟩ := mk_surjective fv
  let qγu : Path.Homotopic.Quotient e e₁ := ⟦γu⟧
  let qγv : Path.Homotopic.Quotient e e₂ := ⟦γv⟧
  have hs :
      Under.mk (fromPath (qγu.map
        ⟨p, hp.isCoveringMap.continuous⟩)) =
        Under.mk (fromPath (qγv.map
          ⟨p, hp.isCoveringMap.continuous⟩)) := by
    simpa only [Under.post, fundamentalGroupoidMap, qγu, qγv] using h
  injections hs
  rename_i hmap hb
  let hβα : Path.Homotopic.Quotient (p e) (p e₂) = Path.Homotopic.Quotient (p e) (p e₁) :=
    congrArg (Path.Homotopic.Quotient (p e)) hb.symm
  have htype :
      type_eq_of_heq hmap.symm = congrArg (fun y ↦ mk (p e) ⟶ mk y) hb.symm := by
    apply Subsingleton.elim
  have hEq :
      fromPath (qγu.map
        ⟨p, hp.isCoveringMap.continuous⟩) =
        cast (congrArg (fun y ↦ mk (p e) ⟶ mk y) hb.symm)
          (fromPath (qγv.map
            ⟨p, hp.isCoveringMap.continuous⟩)) := by
    -- Convert the heterogeneous equality from `injections` into an ordinary equality with cast.
    rw [← htype]
    exact (eq_cast_iff_heq).2 hmap
  let qγu_proj : Path.Homotopic.Quotient (p e) (p e₁) := ⟦γu.map hp.isCoveringMap.continuous⟧
  let qγv_proj : Path.Homotopic.Quotient (p e) (p e₂) := ⟦γv.map hp.isCoveringMap.continuous⟧
  have hproj_eq0 :
      qγu_proj = cast hβα qγv_proj := by
    simpa [FundamentalGroupoid.fromPath, hβα, mk_map, qγu_proj, qγv_proj] using hEq
  have hproj_eq :
      qγu_proj = qγv_proj.cast rfl hb := by
    -- Replace the generic transport by the explicit quotient cast.
    exact hproj_eq0.trans (quotient_cast_eq _ hb)
  have hproj_hom :
      (γu.map hp.isCoveringMap.continuous).Homotopic
        ((γv.map hp.isCoveringMap.continuous).cast rfl hb) := by
    -- Equal projected path classes are homotopic representatives.
    exact eq.1 hproj_eq
  have hγu :
      γu.toContinuousMap =
        hp.isCoveringMap.liftPath (γu.map hp.isCoveringMap.continuous) e
          (γu.map hp.isCoveringMap.continuous).source := by
    -- `γu` is itself the canonical lift of its projection starting at `e`.
    exact (hp.isCoveringMap.eq_liftPath_iff'
      (γu.map hp.isCoveringMap.continuous).source).2 ⟨rfl, γu.source⟩
  have hγv_cast :
      γv.toContinuousMap =
        hp.isCoveringMap.liftPath ((γv.map hp.isCoveringMap.continuous).cast rfl hb) e
          ((γv.map hp.isCoveringMap.continuous).cast rfl hb).source := by
    -- The same uniqueness statement applies to the recast projection of `γv`.
    refine (hp.isCoveringMap.eq_liftPath_iff'
      ((γv.map hp.isCoveringMap.continuous).cast rfl hb).source).2 ?_
    constructor
    · ext t
      simp [Path.cast]
    · exact γv.source
  have hend : e₁ = e₂ := by
    have hγu1 :
        e₁ =
          hp.isCoveringMap.liftPath (γu.map hp.isCoveringMap.continuous) e
            (γu.map hp.isCoveringMap.continuous).source 1 := by
      simpa using congrArg (fun f : C(↑unitInterval, E) ↦ f 1) hγu
    have hγv1 :
        hp.isCoveringMap.liftPath ((γv.map hp.isCoveringMap.continuous).cast rfl hb) e
            ((γv.map hp.isCoveringMap.continuous).cast rfl hb).source 1 = e₂ := by
      simpa using congrArg (fun f : C(↑unitInterval, E) ↦ f 1) hγv_cast.symm
    -- Theorem 3.2.2 identifies the endpoints of the two lifted representatives.
    calc
      e₁ =
          hp.isCoveringMap.liftPath (γu.map hp.isCoveringMap.continuous) e
            (γu.map hp.isCoveringMap.continuous).source 1 := hγu1
      _ =
          hp.isCoveringMap.liftPath ((γv.map hp.isCoveringMap.continuous).cast rfl hb) e
            ((γv.map hp.isCoveringMap.continuous).cast rfl hb).source 1 := by
          exact hp.isCoveringMap.liftPath_apply_one_eq_of_homotopic hproj_hom e rfl
      _ = e₂ := hγv1
  subst e₁
  have hmap_eq_same :
      fromPath (qγu.map
        ⟨p, hp.isCoveringMap.continuous⟩) =
        fromPath (qγv.map
          ⟨p, hp.isCoveringMap.continuous⟩) := by
    -- Once the endpoints coincide, the heterogeneous image equality becomes ordinary equality.
    exact eq_of_heq hmap
  have horig :
      fromPath ⟦γu⟧ =
        fromPath ⟦γv⟧ :=
    fundamentalGroupoidMap_hom_injective hp e e₂ hmap_eq_same
  -- Injectivity on the fixed-endpoint Hom-set recovers equality in the original star.
  simpa [FundamentalGroupoid.fromPath] using congrArg Under.mk horig

/-- Proposition 3.3.4: a covering space `p : E → B` induces a covering functor
`hp.fundamentalGroupoidMap : Π(E) ⥤ Π(B)` of fundamental groupoids. -/
-- Proof sketch: surjectivity on objects comes from `hp.surjective`. For each `e : E`, unique path
-- lifting gives existence and uniqueness of lifts of arrows in the star of `p e`, while
-- homotopy-invariance of lifted endpoints makes the lifted star map well defined on fundamental
-- groupoid morphisms.
theorem fundamentalGroupoidMap_isCovering (hp : IsPathConnectedCoveringMap p) :
    Functor.IsCovering hp.fundamentalGroupoidMap := by
  classical
  refine ⟨?_, ?_⟩
  · -- Surjectivity on objects comes directly from surjectivity of the covering map.
    intro y
    rcases y with ⟨b⟩
    obtain ⟨e, rfl⟩ := hp.surjective b
    exact ⟨mk e, rfl⟩
  · -- For a fixed source point, the star map encodes unique lifting of path classes.
    rintro ⟨e⟩
    -- Route correction: prove bijectivity on the star by separate surjectivity and injectivity,
    -- avoiding the older transport-heavy attempt to construct a global inverse on `Under`.
    exact ⟨fundamentalGroupoidMap_star_injective hp e, fundamentalGroupoidMap_star_surjective hp e⟩

attribute [instance] fundamentalGroupoidMap_isCovering

end IsPathConnectedCoveringMap
