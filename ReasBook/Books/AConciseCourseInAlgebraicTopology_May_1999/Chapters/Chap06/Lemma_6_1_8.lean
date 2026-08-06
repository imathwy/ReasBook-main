import Mathlib.Topology.Category.TopCat.Limits.Basic
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap06.Definition_6_1_4
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap06.Definition_6_1_7
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap06.Reformulation_6_1_6

open CategoryTheory CategoryTheory.Limits
open scoped unitInterval

universe u

variable {A B X : Type u} [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace X]

-- Semantic recall via `lean_leansearch`: mathlib has the model-categorical cobase-change
-- cofibration pattern, while Chapter 6 uses the source-faithful topological owner
-- `IsCofibration`, so the main statement is the corresponding theorem for `pushout.inl g i`.

/-- Helper for Lemma 6.1.8: the two canonical pushout maps commute after restriction to `A`. -/
lemma pushoutInl_comp_eq_pushoutInr_comp {g : C(A, B)} {i : C(A, X)} :
    ((pushout.inl (TopCat.ofHom g) (TopCat.ofHom i)).hom).comp g =
      ((pushout.inr (TopCat.ofHom g) (TopCat.ofHom i)).hom).comp i := by
  -- Transport the categorical pushout relation once into `ContinuousMap` form.
  simpa [TopCat.ofHom_comp] using
    congrArg TopCat.Hom.hom (pushout.condition (f := TopCat.ofHom g) (g := TopCat.ofHom i))

/-- Helper for Lemma 6.1.8: a commuting square of continuous maps yields the compatibility needed
for `pushout.desc` in `TopCat`. -/
lemma topCatOfHom_comp_of_continuousMapEq {W : Type u} [TopologicalSpace W] {g : C(A, B)}
    {i : C(A, X)} {u : C(B, W)} {v : C(X, W)} (h : u.comp g = v.comp i) :
    TopCat.ofHom g ≫ TopCat.ofHom u = TopCat.ofHom i ≫ TopCat.ofHom v := by
  -- Rewrite the continuous-map square as a square of morphisms in `TopCat`.
  simpa [TopCat.ofHom_comp] using congrArg TopCat.ofHom h

/-- Helper for Lemma 6.1.8: the glued map from a pushout restricts on the left leg to the
prescribed map from `B`. -/
lemma pushoutDesc_comp_inl {W : Type u} [TopologicalSpace W] {g : C(A, B)} {i : C(A, X)}
    {u : C(B, W)} {v : C(X, W)} (h : u.comp g = v.comp i) :
    (pushout.desc (TopCat.ofHom u) (TopCat.ofHom v)
        (topCatOfHom_comp_of_continuousMapEq (g := g) (i := i) h)).hom.comp
      (pushout.inl (TopCat.ofHom g) (TopCat.ofHom i)).hom = u := by
  -- Unpack the universal property of `pushout.desc` on the left coprojection.
  simpa [TopCat.ofHom_comp] using
    congrArg TopCat.Hom.hom
      (pushout.inl_desc (TopCat.ofHom u) (TopCat.ofHom v)
        (topCatOfHom_comp_of_continuousMapEq (g := g) (i := i) h))

/-- Helper for Lemma 6.1.8: the glued map from a pushout restricts on the right leg to the
prescribed map from `X`. -/
lemma pushoutDesc_comp_inr {W : Type u} [TopologicalSpace W] {g : C(A, B)} {i : C(A, X)}
    {u : C(B, W)} {v : C(X, W)} (h : u.comp g = v.comp i) :
    (pushout.desc (TopCat.ofHom u) (TopCat.ofHom v)
        (topCatOfHom_comp_of_continuousMapEq (g := g) (i := i) h)).hom.comp
      (pushout.inr (TopCat.ofHom g) (TopCat.ofHom i)).hom = v := by
  -- Unpack the universal property of `pushout.desc` on the right coprojection.
  simpa [TopCat.ofHom_comp] using
    congrArg TopCat.Hom.hom
      (pushout.inr_desc (TopCat.ofHom u) (TopCat.ofHom v)
        (topCatOfHom_comp_of_continuousMapEq (g := g) (i := i) h))

/-- Helper for Lemma 6.1.8: restricting the path-space lifting square for the pushout leg along
`g` produces the lifting square needed for the original cofibration `i`. -/
lemma pushoutPathSpaceZeroCompat {Y : Type u} [TopologicalSpace Y] {g : C(A, B)} {i : C(A, X)}
    {f₀ : C((pushout (TopCat.ofHom g) (TopCat.ofHom i) : TopCat), Y)} {d : C(B, C(I, Y))}
    (hd :
      (pathSpaceEvalAtZero Y).comp d =
        f₀.comp (pushout.inl (TopCat.ofHom g) (TopCat.ofHom i)).hom) :
    (pathSpaceEvalAtZero Y).comp (d.comp g) =
      (f₀.comp (pushout.inr (TopCat.ofHom g) (TopCat.ofHom i)).hom).comp i := by
  -- Move the square to `A` and replace the left pushout leg with the right one.
  calc
    (pathSpaceEvalAtZero Y).comp (d.comp g) = ((pathSpaceEvalAtZero Y).comp d).comp g := by
      rw [ContinuousMap.comp_assoc]
    _ = (f₀.comp (pushout.inl (TopCat.ofHom g) (TopCat.ofHom i)).hom).comp g := by
      rw [hd]
    _ = f₀.comp
          (((pushout.inl (TopCat.ofHom g) (TopCat.ofHom i)).hom).comp g) := by
      rw [← ContinuousMap.comp_assoc]
    _ = f₀.comp
          (((pushout.inr (TopCat.ofHom g) (TopCat.ofHom i)).hom).comp i) := by
      rw [pushoutInl_comp_eq_pushoutInr_comp (g := g) (i := i)]
    _ = (f₀.comp (pushout.inr (TopCat.ofHom g) (TopCat.ofHom i)).hom).comp i := by
      rw [ContinuousMap.comp_assoc]

/-- Helper for Lemma 6.1.8: the path-space map obtained by gluing the left and right lifts has the
required time-`0` endpoint. -/
lemma pushoutPathSpaceDesc_evalZero {Y : Type u} [TopologicalSpace Y] {g : C(A, B)} {i : C(A, X)}
    {f₀ : C((pushout (TopCat.ofHom g) (TopCat.ofHom i) : TopCat), Y)} {d : C(B, C(I, Y))}
    {DX : C(X, C(I, Y))}
    (hcompat : d.comp g = DX.comp i)
    (hzeroB :
      (pathSpaceEvalAtZero Y).comp d =
        f₀.comp (pushout.inl (TopCat.ofHom g) (TopCat.ofHom i)).hom)
    (hzeroX :
      (pathSpaceEvalAtZero Y).comp DX =
        f₀.comp (pushout.inr (TopCat.ofHom g) (TopCat.ofHom i)).hom) :
    (pathSpaceEvalAtZero Y).comp
        (pushout.desc (TopCat.ofHom d) (TopCat.ofHom DX)
          (topCatOfHom_comp_of_continuousMapEq (g := g) (i := i) hcompat)).hom =
      f₀ := by
  let D : C((pushout (TopCat.ofHom g) (TopCat.ofHom i) : TopCat), C(I, Y)) :=
    (pushout.desc (TopCat.ofHom d) (TopCat.ofHom DX)
      (topCatOfHom_comp_of_continuousMapEq (g := g) (i := i) hcompat)).hom
  have hcat : TopCat.ofHom ((pathSpaceEvalAtZero Y).comp D) = TopCat.ofHom f₀ := by
    -- The pushout universal property reduces the endpoint check to the two coprojections.
    apply pushout.hom_ext
    · simpa [D, TopCat.ofHom_comp] using
        congrArg TopCat.ofHom
          (by
            rw [ContinuousMap.comp_assoc, pushoutDesc_comp_inl (g := g) (i := i) (h := hcompat),
              hzeroB] :
            ((pathSpaceEvalAtZero Y).comp D).comp
                (pushout.inl (TopCat.ofHom g) (TopCat.ofHom i)).hom =
              f₀.comp (pushout.inl (TopCat.ofHom g) (TopCat.ofHom i)).hom)
    · simpa [D, TopCat.ofHom_comp] using
        congrArg TopCat.ofHom
          (by
            rw [ContinuousMap.comp_assoc, pushoutDesc_comp_inr (g := g) (i := i) (h := hcompat),
              hzeroX] :
            ((pathSpaceEvalAtZero Y).comp D).comp
                (pushout.inr (TopCat.ofHom g) (TopCat.ofHom i)).hom =
              f₀.comp (pushout.inr (TopCat.ofHom g) (TopCat.ofHom i)).hom)
  -- Return from `TopCat` morphisms to the underlying `ContinuousMap`s.
  simpa [D] using congrArg TopCat.Hom.hom hcat

/-- Lemma 6.1.8. Pushouts of cofibrations are cofibrations: if `i : C(A, X)` is a cofibration and
`g : C(A, B)` is any map, then the canonical map `B → B ∪_g X`, implemented as the left pushout
leg of `pushout (TopCat.ofHom g) (TopCat.ofHom i)`, is a cofibration. -/
theorem IsCofibration.pushout_inl {g : C(A, B)} {i : C(A, X)}
    (hi : IsCofibration.{u, u, u} i) :
    IsCofibration.{u, u, u} (pushout.inl (TopCat.ofHom g) (TopCat.ofHom i)).hom := by
  -- Use the path-space lifting characterization to reduce the pushout claim to one lift of `i`.
  refine (isCofibration_iff_lift_pathSpaceEvalAtZero).2 ?_
  intro Y _ f₀ d hd
  -- Restrict the pushout lifting problem along `g`, where the cofibration hypothesis applies.
  obtain ⟨DX, hDX, hDX0⟩ :=
    (isCofibration_iff_lift_pathSpaceEvalAtZero.mp hi) (f₀ := f₀.comp
      (pushout.inr (TopCat.ofHom g) (TopCat.ofHom i)).hom) (d := d.comp g)
      (pushoutPathSpaceZeroCompat (g := g) (i := i) (f₀ := f₀) (d := d) hd)
  let D : C((pushout (TopCat.ofHom g) (TopCat.ofHom i) : TopCat), C(I, Y)) :=
    (pushout.desc (TopCat.ofHom d) (TopCat.ofHom DX)
      (topCatOfHom_comp_of_continuousMapEq (g := g) (i := i) hDX.symm)).hom
  refine ⟨D, ?_, ?_⟩
  · -- The glued lift restricts on `B` to the original path-space map.
    simpa [D] using pushoutDesc_comp_inl (g := g) (i := i) (u := d) (v := DX) hDX.symm
  · -- The endpoint of the glued lift is the prescribed map `f₀`.
    simpa [D] using
      pushoutPathSpaceDesc_evalZero (g := g) (i := i) (f₀ := f₀) (d := d) (DX := DX)
        hDX.symm hd hDX0
