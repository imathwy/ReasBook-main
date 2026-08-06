import Mathlib.Topology.Homotopy.Equiv
import Mathlib.CategoryTheory.Comma.Over.Pullback
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap02.Definition_2_4_5
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap06.Definition_6_1_4
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap06.Definition_6_5_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap06.Lemma_6_1_8
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap06.Lemma_6_3_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap06.Reformulation_6_1_6
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap07.Theorem_7_6_5
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap10.Definition_10_7_7

open CategoryTheory CategoryTheory.HomRel CategoryTheory.Limits
open scoped ContinuousMap unitInterval

universe u

variable {A B C : Type u} [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]

noncomputable section

-- Semantic recall via `lean_leansearch`: `ContinuousMap.HomotopyEquiv` is the canonical owner for
-- ordinary homotopy equivalences. Here the proposition-level bridge uses the ordinary homotopy
-- relation on morphisms in `TopCat`, while Chapter 10 packages `M(i, j)` and its quotient map via
-- `doubleMappingCylinder` and `doubleMappingCylinderQuotientMap`, and Chapter 6 supplies the
-- source cofibration hypothesis `IsCofibration`.

namespace ContinuousMap

/-- Helper for Lemma 10.7.8: the left coproduct summand inclusion `A ⟶ A ⊕ B`. -/
private abbrev sumLeftInclusion : C(A, A ⊕ B) :=
  ⟨Sum.inl, continuous_inl⟩

/-- Helper for Lemma 10.7.8: the right coproduct summand inclusion `B ⟶ A ⊕ B`. -/
private abbrev sumRightInclusion : C(B, A ⊕ B) :=
  ⟨Sum.inr, continuous_inr⟩

/-- Helper for Lemma 10.7.8: the mapping-cylinder projection, viewed as a morphism under `C`
from the source-faithful factorization map `mappingCylinderFactorizationIn i` to `i`. -/
def mappingCylinderProjectionFactorizationUnder {i : C(C, A)} :
    (Under.mk (TopCat.ofHom (mappingCylinderFactorizationIn i)) : Under (TopCat.of C)) ⟶
      (Under.mk (TopCat.ofHom i) : Under (TopCat.of C)) :=
  Under.homMk (TopCat.ofHom (mappingCylinderProjection i))
    (congrArg TopCat.ofHom (mappingCylinderProjection_comp_factorizationIn i))

/-- Helper for Lemma 10.7.8: pushing a morphism in `Under (TopCat.of C)` forward along
`g : C(C, B)` produces the corresponding map between ordinary pushouts. -/
abbrev pushoutMapOfUnderHom {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    {i₁ : C(C, X)} {i₂ : C(C, Y)} (g : C(C, B))
    (f :
      (Under.mk (TopCat.ofHom i₁) : Under (TopCat.of C)) ⟶
        (Under.mk (TopCat.ofHom i₂) : Under (TopCat.of C))) :
    C((pushout (TopCat.ofHom i₁) (TopCat.ofHom g) : TopCat),
      (pushout (TopCat.ofHom i₂) (TopCat.ofHom g) : TopCat)) :=
  ((Under.pushout (TopCat.ofHom g)).map f).right.hom

/-- Helper for Lemma 10.7.8: the pushed-out map restricts on the left pushout leg to the
underlying right map of the original under-morphism. -/
@[simp] theorem pushoutMapOfUnderHom_comp_inl {X Y : Type u} [TopologicalSpace X]
    [TopologicalSpace Y] {i₁ : C(C, X)} {i₂ : C(C, Y)} (g : C(C, B))
    (f :
      (Under.mk (TopCat.ofHom i₁) : Under (TopCat.of C)) ⟶
        (Under.mk (TopCat.ofHom i₂) : Under (TopCat.of C))) :
    (pushoutMapOfUnderHom g f).comp (pushout.inl (TopCat.ofHom i₁) (TopCat.ofHom g)).hom =
      (pushout.inl (TopCat.ofHom i₂) (TopCat.ofHom g)).hom.comp f.right.hom := by
  -- Unfold the pushout functor once and read off the left computation rule of `pushout.desc`.
  simpa [pushoutMapOfUnderHom, Under.pushout] using
    congrArg TopCat.Hom.hom <|
      pushout.inl_desc
        (f.right ≫ pushout.inl (TopCat.ofHom i₂) (TopCat.ofHom g))
        (pushout.inr (TopCat.ofHom i₂) (TopCat.ofHom g))
        (by
          calc
            TopCat.ofHom i₁ ≫ f.right ≫ pushout.inl (TopCat.ofHom i₂) (TopCat.ofHom g) =
                TopCat.ofHom i₂ ≫ pushout.inl (TopCat.ofHom i₂) (TopCat.ofHom g) := by
                  simpa [Category.assoc] using
                    congrArg
                      (fun k :
                        TopCat.of C ⟶ TopCat.of Y =>
                          k ≫ pushout.inl (TopCat.ofHom i₂) (TopCat.ofHom g))
                      (Under.w f)
            _ = TopCat.ofHom g ≫ pushout.inr (TopCat.ofHom i₂) (TopCat.ofHom g) :=
              pushout.condition)

/-- Helper for Lemma 10.7.8: the pushed-out map restricts on the right pushout leg to the
identity on the added `B`-summand. -/
@[simp] theorem pushoutMapOfUnderHom_comp_inr {X Y : Type u} [TopologicalSpace X]
    [TopologicalSpace Y] {i₁ : C(C, X)} {i₂ : C(C, Y)} (g : C(C, B))
    (f :
      (Under.mk (TopCat.ofHom i₁) : Under (TopCat.of C)) ⟶
        (Under.mk (TopCat.ofHom i₂) : Under (TopCat.of C))) :
    (pushoutMapOfUnderHom g f).comp (pushout.inr (TopCat.ofHom i₁) (TopCat.ofHom g)).hom =
      (pushout.inr (TopCat.ofHom i₂) (TopCat.ofHom g)).hom := by
  -- The right pushout leg is carried along unchanged by `Under.pushout`.
  simpa [pushoutMapOfUnderHom, Under.pushout] using
    congrArg TopCat.Hom.hom <|
      pushout.inr_desc
        (f.right ≫ pushout.inl (TopCat.ofHom i₂) (TopCat.ofHom g))
        (pushout.inr (TopCat.ofHom i₂) (TopCat.ofHom g))
        (by
          calc
            TopCat.ofHom i₁ ≫ f.right ≫ pushout.inl (TopCat.ofHom i₂) (TopCat.ofHom g) =
                TopCat.ofHom i₂ ≫ pushout.inl (TopCat.ofHom i₂) (TopCat.ofHom g) := by
                  simpa [Category.assoc] using
                    congrArg
                      (fun k :
                        TopCat.of C ⟶ TopCat.of Y =>
                          k ≫ pushout.inl (TopCat.ofHom i₂) (TopCat.ofHom g))
                      (Under.w f)
            _ = TopCat.ofHom g ≫ pushout.inr (TopCat.ofHom i₂) (TopCat.ofHom g) :=
              pushout.condition)

/-- Helper for Lemma 10.7.8: evaluating a path-space-valued `pushout.desc` commutes with the
pushout descent. -/
theorem pathSpaceEvalAt_comp_pushoutDesc {X Z : Type u} [TopologicalSpace X]
    [TopologicalSpace Z] {i : C(C, X)} {g : C(C, B)}
    {l : C(X, C(I, Z))} {r : C(B, C(I, Z))} (hcompat : l.comp i = r.comp g) (t : I) :
    (pathSpaceEvalAt t Z).comp
        ((pushout.desc (TopCat.ofHom l) (TopCat.ofHom r)
          (topCatOfHom_comp_of_continuousMapEq (g := i) (i := g) hcompat)).hom) =
      (pushout.desc
        (TopCat.ofHom ((pathSpaceEvalAt t Z).comp l))
        (TopCat.ofHom ((pathSpaceEvalAt t Z).comp r))
        (topCatOfHom_comp_of_continuousMapEq (g := i) (i := g) <| by
          simpa [ContinuousMap.comp_assoc] using
            congrArg (fun u : C(C, C(I, Z)) ↦ (pathSpaceEvalAt t Z).comp u) hcompat)).hom := by
  -- Evaluate both descended maps on the two pushout legs; both restrictions are forced by the
  -- same endpoint maps obtained from `l` and `r` by evaluation at time `t`.
  have hcompatEval :
      ((pathSpaceEvalAt t Z).comp l).comp i = ((pathSpaceEvalAt t Z).comp r).comp g := by
    simpa [ContinuousMap.comp_assoc] using
      congrArg (fun u : C(C, C(I, Z)) ↦ (pathSpaceEvalAt t Z).comp u) hcompat
  have hcat :
      TopCat.ofHom
          ((pathSpaceEvalAt t Z).comp
            ((pushout.desc (TopCat.ofHom l) (TopCat.ofHom r)
              (topCatOfHom_comp_of_continuousMapEq (g := i) (i := g) hcompat)).hom)) =
        TopCat.ofHom
          ((pushout.desc
            (TopCat.ofHom ((pathSpaceEvalAt t Z).comp l))
            (TopCat.ofHom ((pathSpaceEvalAt t Z).comp r))
            (topCatOfHom_comp_of_continuousMapEq (g := i) (i := g) hcompatEval)).hom) := by
    -- The pushout universal property reduces the comparison to the left and right coprojections.
    apply pushout.hom_ext
    · simpa [TopCat.ofHom_comp] using
        congrArg TopCat.ofHom
          (by
            rw [ContinuousMap.comp_assoc, pushoutDesc_comp_inl (g := i) (i := g) (h := hcompat),
              pushoutDesc_comp_inl (g := i) (i := g) (h := hcompatEval)] :
            ((pathSpaceEvalAt t Z).comp
                ((pushout.desc (TopCat.ofHom l) (TopCat.ofHom r)
                  (topCatOfHom_comp_of_continuousMapEq (g := i) (i := g) hcompat)).hom)).comp
                (pushout.inl (TopCat.ofHom i) (TopCat.ofHom g)).hom =
              ((pushout.desc
                (TopCat.ofHom ((pathSpaceEvalAt t Z).comp l))
                (TopCat.ofHom ((pathSpaceEvalAt t Z).comp r))
                (topCatOfHom_comp_of_continuousMapEq (g := i) (i := g) hcompatEval)).hom).comp
                (pushout.inl (TopCat.ofHom i) (TopCat.ofHom g)).hom)
    · simpa [TopCat.ofHom_comp] using
        congrArg TopCat.ofHom
          (by
            rw [ContinuousMap.comp_assoc, pushoutDesc_comp_inr (g := i) (i := g) (h := hcompat),
              pushoutDesc_comp_inr (g := i) (i := g) (h := hcompatEval)] :
            ((pathSpaceEvalAt t Z).comp
                ((pushout.desc (TopCat.ofHom l) (TopCat.ofHom r)
                  (topCatOfHom_comp_of_continuousMapEq (g := i) (i := g) hcompat)).hom)).comp
                (pushout.inr (TopCat.ofHom i) (TopCat.ofHom g)).hom =
              ((pushout.desc
                (TopCat.ofHom ((pathSpaceEvalAt t Z).comp l))
                (TopCat.ofHom ((pathSpaceEvalAt t Z).comp r))
                (topCatOfHom_comp_of_continuousMapEq (g := i) (i := g) hcompatEval)).hom).comp
                (pushout.inr (TopCat.ofHom i) (TopCat.ofHom g)).hom)
  -- Return to the `ContinuousMap` level after the categorical extensionality step.
  simpa using congrArg TopCat.Hom.hom hcat

/-- Helper for Lemma 10.7.8: pushing out along `g` preserves composition of under-morphisms. -/
@[simp] theorem pushoutMapOfUnderHom_comp {X Y Z : Type u} [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace Z] {i₁ : C(C, X)} {i₂ : C(C, Y)} {i₃ : C(C, Z)}
    (g : C(C, B))
    (f :
      (Under.mk (TopCat.ofHom i₁) : Under (TopCat.of C)) ⟶
        (Under.mk (TopCat.ofHom i₂) : Under (TopCat.of C)))
    (k :
      (Under.mk (TopCat.ofHom i₂) : Under (TopCat.of C)) ⟶
        (Under.mk (TopCat.ofHom i₃) : Under (TopCat.of C))) :
    pushoutMapOfUnderHom g (f ≫ k) =
      (pushoutMapOfUnderHom g k).comp (pushoutMapOfUnderHom g f) := by
  -- Read off the right component of `Functor.map_comp` for `Under.pushout`.
  have hright :
      ((Under.pushout (TopCat.ofHom g)).map (f ≫ k)).right =
        (((Under.pushout (TopCat.ofHom g)).map f) ≫ ((Under.pushout (TopCat.ofHom g)).map k)).right :=
    congrArg (fun m ↦ m.right) ((Under.pushout (TopCat.ofHom g)).map_comp f k)
  simpa [pushoutMapOfUnderHom, TopCat.ofHom_comp] using congrArg TopCat.Hom.hom hright

/-- Helper for Lemma 10.7.8: pushing out the identity under-map gives the identity on the
corresponding pushout. -/
@[simp] theorem pushoutMapOfUnderHom_id {X : Type u} [TopologicalSpace X] {i : C(C, X)}
    (g : C(C, B)) :
    pushoutMapOfUnderHom g
        (𝟙 (Under.mk (TopCat.ofHom i) : Under (TopCat.of C))) =
      ContinuousMap.id (pushout (TopCat.ofHom i) (TopCat.ofHom g) : TopCat) := by
  -- This is `Functor.map_id` for `Under.pushout`.
  simpa [pushoutMapOfUnderHom] using
    congrArg TopCat.Hom.hom
      ((Under.pushout (TopCat.ofHom g)).map_id
        (Under.mk (TopCat.ofHom i) : Under (TopCat.of C)))

/-- Helper for Lemma 10.7.8: a homotopy under `C` descends to an ordinary homotopy after pushing
out along `g : C(C, B)`. -/
theorem pushoutMapOfUnderHom_homotopic {X Y : Type u} [TopologicalSpace X]
    [TopologicalSpace Y] {i₁ : C(C, X)} {i₂ : C(C, Y)} (g : C(C, B))
    {f₀ f₁ :
      (Under.mk (TopCat.ofHom i₁) : Under (TopCat.of C)) ⟶
        (Under.mk (TopCat.ofHom i₂) : Under (TopCat.of C))}
    (h : HomotopicUnder f₀ f₁) :
    (pushoutMapOfUnderHom g f₀).Homotopic (pushoutMapOfUnderHom g f₁) := by
  rcases h with ⟨H⟩
  let Z : TopCat := (pushout (TopCat.ofHom i₂) (TopCat.ofHom g) : TopCat)
  let leftPathMap : C(X, C(I, Z)) :=
    (pathSpacePostcompose (pushout.inl (TopCat.ofHom i₂) (TopCat.ofHom g)).hom).comp
      H.toHomotopy.toPathSpaceMap
  let rightPathMap : C(B, C(I, Z)) :=
    (((pushout.inr (TopCat.ofHom i₂) (TopCat.ofHom g)).hom).comp ContinuousMap.fst).curry
  -- Route correction: descend one path-space map through the pushout and read its endpoints only
  -- after fixing the normal form on each pushout leg.
  have hcompatPath : leftPathMap.comp i₁ = rightPathMap.comp g := by
    -- On `C`, every time-slice of `H` is a map under `C`, so the left leg agrees with the
    -- constant right leg pointwise.
    ext c t
    have hslice : H.toHomotopy.toPathSpaceMap (i₁ c) t = i₂ c := by
      calc
        H.toHomotopy.toPathSpaceMap (i₁ c) t = H.toHomotopy.curry t (i₁ c) := by
          simpa using
            ContinuousMap.congr_fun (H.toHomotopy.pathSpaceEvalAt_comp_toPathSpaceMap t) (i₁ c)
        _ = i₂ c := ContinuousMap.congr_fun (UnderHomotopy.w H t) c
    calc
      leftPathMap (i₁ c) t =
          (pushout.inl (TopCat.ofHom i₂) (TopCat.ofHom g)).hom
            (H.toHomotopy.toPathSpaceMap (i₁ c) t) := by
            rfl
      _ = (pushout.inl (TopCat.ofHom i₂) (TopCat.ofHom g)).hom (i₂ c) := by
            rw [hslice]
      _ = (pushout.inr (TopCat.ofHom i₂) (TopCat.ofHom g)).hom (g c) := by
            simpa [ContinuousMap.comp_apply] using
              ContinuousMap.congr_fun
                (pushoutInl_comp_eq_pushoutInr_comp (g := i₂) (i := g)) c
      _ = rightPathMap (g c) t := by
            simp [rightPathMap]
  let D : C((pushout (TopCat.ofHom i₁) (TopCat.ofHom g) : TopCat), C(I, Z)) :=
    (pushout.desc (TopCat.ofHom leftPathMap) (TopCat.ofHom rightPathMap)
      (topCatOfHom_comp_of_continuousMapEq (g := i₁) (i := g) hcompatPath)).hom
  have hleftEvalZero :
      (pathSpaceEvalAt 0 Z).comp leftPathMap =
        (pushout.inl (TopCat.ofHom i₂) (TopCat.ofHom g)).hom.comp f₀.right.hom := by
    -- The left leg at time `0` is the pushed-out image of the initial endpoint `f₀`.
    ext x
    change
      (pushout.inl (TopCat.ofHom i₂) (TopCat.ofHom g)).hom (H.toHomotopy.toPathSpaceMap x 0) =
        (pushout.inl (TopCat.ofHom i₂) (TopCat.ofHom g)).hom (f₀.right.hom x)
    rw [H.toHomotopy.toPathSpaceMap_apply, H.toHomotopy.apply_zero]
  have hleftEvalOne :
      (pathSpaceEvalAt 1 Z).comp leftPathMap =
        (pushout.inl (TopCat.ofHom i₂) (TopCat.ofHom g)).hom.comp f₁.right.hom := by
    -- The left leg at time `1` is the pushed-out image of the terminal endpoint `f₁`.
    ext x
    change
      (pushout.inl (TopCat.ofHom i₂) (TopCat.ofHom g)).hom (H.toHomotopy.toPathSpaceMap x 1) =
        (pushout.inl (TopCat.ofHom i₂) (TopCat.ofHom g)).hom (f₁.right.hom x)
    rw [H.toHomotopy.toPathSpaceMap_apply, H.toHomotopy.apply_one]
  have hrightEval (t : I) :
      (pathSpaceEvalAt t Z).comp rightPathMap =
        (pushout.inr (TopCat.ofHom i₂) (TopCat.ofHom g)).hom := by
    -- The right leg is the constant path at the canonical right pushout inclusion.
    ext b
    simp [rightPathMap]
  have hcompatEvalZero :
      ((pathSpaceEvalAt 0 Z).comp leftPathMap).comp i₁ =
        ((pathSpaceEvalAt 0 Z).comp rightPathMap).comp g := by
    simpa [ContinuousMap.comp_assoc] using
      congrArg (fun u : C(C, C(I, Z)) ↦ (pathSpaceEvalAt 0 Z).comp u) hcompatPath
  have hcompatEvalOne :
      ((pathSpaceEvalAt 1 Z).comp leftPathMap).comp i₁ =
        ((pathSpaceEvalAt 1 Z).comp rightPathMap).comp g := by
    simpa [ContinuousMap.comp_assoc] using
      congrArg (fun u : C(C, C(I, Z)) ↦ (pathSpaceEvalAt 1 Z).comp u) hcompatPath
  have hDzero :
      (pathSpaceEvalAt 0 Z).comp D = pushoutMapOfUnderHom g f₀ := by
    calc
      (pathSpaceEvalAt 0 Z).comp D =
          (pushout.desc
            (TopCat.ofHom ((pathSpaceEvalAt 0 Z).comp leftPathMap))
            (TopCat.ofHom ((pathSpaceEvalAt 0 Z).comp rightPathMap))
            (topCatOfHom_comp_of_continuousMapEq (g := i₁) (i := g) hcompatEvalZero)).hom := by
            simpa [D] using
              pathSpaceEvalAt_comp_pushoutDesc (i := i₁) (g := g)
                (l := leftPathMap) (r := rightPathMap) hcompatPath 0
      _ = pushoutMapOfUnderHom g f₀ := by
        have hleftZeroTop :
            TopCat.ofHom ((pathSpaceEvalAt 0 Z).comp leftPathMap) =
              f₀.right ≫ pushout.inl (TopCat.ofHom i₂) (TopCat.ofHom g) := by
          simpa [TopCat.ofHom_comp] using congrArg TopCat.ofHom hleftEvalZero
        have hrightZeroTop :
            TopCat.ofHom ((pathSpaceEvalAt 0 Z).comp rightPathMap) =
              pushout.inr (TopCat.ofHom i₂) (TopCat.ofHom g) := by
          simpa [TopCat.ofHom_comp] using congrArg TopCat.ofHom (hrightEval 0)
        have hpushInl :
            pushout.inl (TopCat.ofHom i₁) (TopCat.ofHom g) ≫
                TopCat.ofHom (pushoutMapOfUnderHom g f₀) =
              f₀.right ≫ pushout.inl (TopCat.ofHom i₂) (TopCat.ofHom g) := by
          simpa [TopCat.ofHom_comp] using
            congrArg TopCat.ofHom (pushoutMapOfUnderHom_comp_inl g f₀)
        have hpushInr :
            pushout.inr (TopCat.ofHom i₁) (TopCat.ofHom g) ≫
                TopCat.ofHom (pushoutMapOfUnderHom g f₀) =
              pushout.inr (TopCat.ofHom i₂) (TopCat.ofHom g) := by
          simpa [TopCat.ofHom_comp] using
            congrArg TopCat.ofHom (pushoutMapOfUnderHom_comp_inr g f₀)
        have hcat :
            TopCat.ofHom
                ((pushout.desc
                  (TopCat.ofHom ((pathSpaceEvalAt 0 Z).comp leftPathMap))
                  (TopCat.ofHom ((pathSpaceEvalAt 0 Z).comp rightPathMap))
                  (topCatOfHom_comp_of_continuousMapEq (g := i₁) (i := g)
                    hcompatEvalZero)).hom) =
              TopCat.ofHom (pushoutMapOfUnderHom g f₀) := by
          -- The time-`0` endpoint agrees with `pushoutMapOfUnderHom g f₀` on both pushout legs.
          apply pushout.hom_ext
          · have hfirst :
                pushout.inl (TopCat.ofHom i₁) (TopCat.ofHom g) ≫
                    TopCat.ofHom
                      ((pushout.desc
                        (TopCat.ofHom ((pathSpaceEvalAt 0 Z).comp leftPathMap))
                        (TopCat.ofHom ((pathSpaceEvalAt 0 Z).comp rightPathMap))
                        (topCatOfHom_comp_of_continuousMapEq (g := i₁) (i := g)
                          hcompatEvalZero)).hom) =
                  TopCat.ofHom ((pathSpaceEvalAt 0 Z).comp leftPathMap) := by
              simpa [TopCat.ofHom_comp] using
                pushout.inl_desc
                  (TopCat.ofHom ((pathSpaceEvalAt 0 Z).comp leftPathMap))
                  (TopCat.ofHom ((pathSpaceEvalAt 0 Z).comp rightPathMap))
                  (topCatOfHom_comp_of_continuousMapEq (g := i₁) (i := g)
                    hcompatEvalZero)
            exact hfirst.trans <| hleftZeroTop.trans <| by
              simpa [TopCat.ofHom_comp] using
                (congrArg TopCat.ofHom (pushoutMapOfUnderHom_comp_inl g f₀)).symm
          · calc
              pushout.inr (TopCat.ofHom i₁) (TopCat.ofHom g) ≫
                  TopCat.ofHom
                    ((pushout.desc
                      (TopCat.ofHom ((pathSpaceEvalAt 0 Z).comp leftPathMap))
                      (TopCat.ofHom ((pathSpaceEvalAt 0 Z).comp rightPathMap))
                      (topCatOfHom_comp_of_continuousMapEq (g := i₁) (i := g)
                        hcompatEvalZero)).hom) =
                TopCat.ofHom ((pathSpaceEvalAt 0 Z).comp rightPathMap) := by
                  simpa [TopCat.ofHom_comp] using
                    pushout.inr_desc
                      (TopCat.ofHom ((pathSpaceEvalAt 0 Z).comp leftPathMap))
                      (TopCat.ofHom ((pathSpaceEvalAt 0 Z).comp rightPathMap))
                      (topCatOfHom_comp_of_continuousMapEq (g := i₁) (i := g)
                        hcompatEvalZero)
            _ = pushout.inr (TopCat.ofHom i₂) (TopCat.ofHom g) := hrightZeroTop
            _ =
                pushout.inr (TopCat.ofHom i₁) (TopCat.ofHom g) ≫
                  TopCat.ofHom (pushoutMapOfUnderHom g f₀) := by
                    simpa [TopCat.ofHom_comp] using
                      (congrArg TopCat.ofHom (pushoutMapOfUnderHom_comp_inr g f₀)).symm
        simpa using congrArg TopCat.Hom.hom hcat
  have hDone :
      (pathSpaceEvalAt 1 Z).comp D = pushoutMapOfUnderHom g f₁ := by
    calc
      (pathSpaceEvalAt 1 Z).comp D =
          (pushout.desc
            (TopCat.ofHom ((pathSpaceEvalAt 1 Z).comp leftPathMap))
            (TopCat.ofHom ((pathSpaceEvalAt 1 Z).comp rightPathMap))
            (topCatOfHom_comp_of_continuousMapEq (g := i₁) (i := g) hcompatEvalOne)).hom := by
            simpa [D] using
              pathSpaceEvalAt_comp_pushoutDesc (i := i₁) (g := g)
                (l := leftPathMap) (r := rightPathMap) hcompatPath 1
      _ = pushoutMapOfUnderHom g f₁ := by
        have hleftOneTop :
            TopCat.ofHom ((pathSpaceEvalAt 1 Z).comp leftPathMap) =
              f₁.right ≫ pushout.inl (TopCat.ofHom i₂) (TopCat.ofHom g) := by
          simpa [TopCat.ofHom_comp] using congrArg TopCat.ofHom hleftEvalOne
        have hrightOneTop :
            TopCat.ofHom ((pathSpaceEvalAt 1 Z).comp rightPathMap) =
              pushout.inr (TopCat.ofHom i₂) (TopCat.ofHom g) := by
          simpa [TopCat.ofHom_comp] using congrArg TopCat.ofHom (hrightEval 1)
        have hpushInl :
            pushout.inl (TopCat.ofHom i₁) (TopCat.ofHom g) ≫
                TopCat.ofHom (pushoutMapOfUnderHom g f₁) =
              f₁.right ≫ pushout.inl (TopCat.ofHom i₂) (TopCat.ofHom g) := by
          simpa [TopCat.ofHom_comp] using
            congrArg TopCat.ofHom (pushoutMapOfUnderHom_comp_inl g f₁)
        have hpushInr :
            pushout.inr (TopCat.ofHom i₁) (TopCat.ofHom g) ≫
                TopCat.ofHom (pushoutMapOfUnderHom g f₁) =
              pushout.inr (TopCat.ofHom i₂) (TopCat.ofHom g) := by
          simpa [TopCat.ofHom_comp] using
            congrArg TopCat.ofHom (pushoutMapOfUnderHom_comp_inr g f₁)
        have hcat :
            TopCat.ofHom
                ((pushout.desc
                  (TopCat.ofHom ((pathSpaceEvalAt 1 Z).comp leftPathMap))
                  (TopCat.ofHom ((pathSpaceEvalAt 1 Z).comp rightPathMap))
                  (topCatOfHom_comp_of_continuousMapEq (g := i₁) (i := g)
                    hcompatEvalOne)).hom) =
              TopCat.ofHom (pushoutMapOfUnderHom g f₁) := by
          -- The time-`1` endpoint agrees with `pushoutMapOfUnderHom g f₁` on both pushout legs.
          apply pushout.hom_ext
          · have hfirst :
                pushout.inl (TopCat.ofHom i₁) (TopCat.ofHom g) ≫
                    TopCat.ofHom
                      ((pushout.desc
                        (TopCat.ofHom ((pathSpaceEvalAt 1 Z).comp leftPathMap))
                        (TopCat.ofHom ((pathSpaceEvalAt 1 Z).comp rightPathMap))
                        (topCatOfHom_comp_of_continuousMapEq (g := i₁) (i := g)
                          hcompatEvalOne)).hom) =
                  TopCat.ofHom ((pathSpaceEvalAt 1 Z).comp leftPathMap) := by
              simpa [TopCat.ofHom_comp] using
                pushout.inl_desc
                  (TopCat.ofHom ((pathSpaceEvalAt 1 Z).comp leftPathMap))
                  (TopCat.ofHom ((pathSpaceEvalAt 1 Z).comp rightPathMap))
                  (topCatOfHom_comp_of_continuousMapEq (g := i₁) (i := g)
                    hcompatEvalOne)
            exact hfirst.trans <| hleftOneTop.trans <| by
              simpa [TopCat.ofHom_comp] using
                (congrArg TopCat.ofHom (pushoutMapOfUnderHom_comp_inl g f₁)).symm
          · calc
              pushout.inr (TopCat.ofHom i₁) (TopCat.ofHom g) ≫
                  TopCat.ofHom
                    ((pushout.desc
                      (TopCat.ofHom ((pathSpaceEvalAt 1 Z).comp leftPathMap))
                      (TopCat.ofHom ((pathSpaceEvalAt 1 Z).comp rightPathMap))
                      (topCatOfHom_comp_of_continuousMapEq (g := i₁) (i := g)
                        hcompatEvalOne)).hom) =
                TopCat.ofHom ((pathSpaceEvalAt 1 Z).comp rightPathMap) := by
                  simpa [TopCat.ofHom_comp] using
                    pushout.inr_desc
                      (TopCat.ofHom ((pathSpaceEvalAt 1 Z).comp leftPathMap))
                      (TopCat.ofHom ((pathSpaceEvalAt 1 Z).comp rightPathMap))
                      (topCatOfHom_comp_of_continuousMapEq (g := i₁) (i := g)
                        hcompatEvalOne)
            _ = pushout.inr (TopCat.ofHom i₂) (TopCat.ofHom g) := hrightOneTop
            _ =
                pushout.inr (TopCat.ofHom i₁) (TopCat.ofHom g) ≫
                  TopCat.ofHom (pushoutMapOfUnderHom g f₁) := by
                    simpa [TopCat.ofHom_comp] using
                      (congrArg TopCat.ofHom (pushoutMapOfUnderHom_comp_inr g f₁)).symm
        simpa using congrArg TopCat.Hom.hom hcat
  -- Package the descended path family with its two endpoint computations.
  exact ⟨ContinuousMap.Homotopy.ofPathSpaceMap D hDzero hDone⟩

/-- Helper for Lemma 10.7.8: the top edge of the mapping-cylinder cylinder gives the boundary path
from `mappingCylinderTargetInclusion i ∘ i` to `mappingCylinderFactorizationIn i`. -/
private def mappingCylinderFactorizationBoundaryPathMap {i : C(C, A)} :
    C(C, C(I, i.mappingCylinder)) :=
  (mappingCylinderCylinderInclusion i).curry

/-- Helper for Lemma 10.7.8: evaluating the boundary path at time `0` recovers the target copy of
`i : C(C, A)` inside the mapping cylinder. -/
private theorem mappingCylinderFactorizationBoundaryPathMap_evalZero {i : C(C, A)} :
    (pathSpaceEvalAt 0 i.mappingCylinder).comp (mappingCylinderFactorizationBoundaryPathMap
      (i := i)) =
      (mappingCylinderTargetInclusion i).comp i := by
  -- Read the time-`0` endpoint of the cylinder path through the pushout gluing relation.
  ext c
  simpa [mappingCylinderFactorizationBoundaryPathMap, pathSpaceEvalAt, ContinuousMap.comp_apply]
    using congrArg (fun f : C(C, i.mappingCylinder) ↦ f c)
      (mappingCylinderIn_eq_targetInclusion_comp i)

/-- Helper for Lemma 10.7.8: evaluating the boundary path at time `1` recovers the source-faithful
factorization leg `mappingCylinderFactorizationIn i`. -/
private theorem mappingCylinderFactorizationBoundaryPathMap_evalOne {i : C(C, A)} :
    (pathSpaceEvalAt 1 i.mappingCylinder).comp (mappingCylinderFactorizationBoundaryPathMap
      (i := i)) =
      mappingCylinderFactorizationIn i := by
  -- The time-`1` endpoint is definitionally the top-slice inclusion.
  ext c
  rfl

/-- Helper for Lemma 10.7.8: the cylinder path yields the boundary homotopy used to correct the
ordinary mapping-cylinder inverse into a map under `C`. -/
private def mappingCylinderFactorizationBoundaryHomotopy {i : C(C, A)} :
    ((mappingCylinderTargetInclusion i).comp i).Homotopy (mappingCylinderFactorizationIn i) :=
  ContinuousMap.Homotopy.ofPathSpaceMap
    (mappingCylinderFactorizationBoundaryPathMap (i := i))
    (mappingCylinderFactorizationBoundaryPathMap_evalZero (i := i))
    (mappingCylinderFactorizationBoundaryPathMap_evalOne (i := i))

/-- Helper for Lemma 10.7.8: the HEP-corrected inverse endpoint extends
`mappingCylinderFactorizationIn i` from `C` to all of `A`. -/
private theorem mappingCylinderProjectionFactorizationUnderInverse_comp {i : C(C, A)}
    (hi : IsCofibration.{u, u, u} i) :
    (Classical.choose
      (hi.exists_homotopy_extension
        (mappingCylinderTargetInclusion i)
        (mappingCylinderFactorizationIn i)
        (mappingCylinderFactorizationBoundaryHomotopy (i := i)))).comp i =
      mappingCylinderFactorizationIn i := by
  -- Read the time-`1` endpoint of the chosen extension on the cofibration source.
  ext c
  simpa using
    (Classical.choose_spec
      (Classical.choose_spec
        (hi.exists_homotopy_extension
          (mappingCylinderTargetInclusion i)
          (mappingCylinderFactorizationIn i)
          (mappingCylinderFactorizationBoundaryHomotopy (i := i))))) (1, c)

/-- Helper for Lemma 10.7.8: the chosen HEP correction of `mappingCylinderTargetInclusion i`
defines a morphism under `C` from `i` to `mappingCylinderFactorizationIn i`. -/
private def mappingCylinderProjectionFactorizationUnderInverse {i : C(C, A)}
    (hi : IsCofibration.{u, u, u} i) :
    (Under.mk (TopCat.ofHom i) : Under (TopCat.of C)) ⟶
      (Under.mk (TopCat.ofHom (mappingCylinderFactorizationIn i)) : Under (TopCat.of C)) :=
  Under.homMk
    (TopCat.ofHom <|
      Classical.choose
        (hi.exists_homotopy_extension
          (mappingCylinderTargetInclusion i)
          (mappingCylinderFactorizationIn i)
          (mappingCylinderFactorizationBoundaryHomotopy (i := i))))
    (congrArg TopCat.ofHom <|
      mappingCylinderProjectionFactorizationUnderInverse_comp (i := i) hi)

/-- Helper for Lemma 10.7.8: the HEP correction is homotopic to the ordinary target inclusion
`A ⟶ M_i`. -/
private def mappingCylinderProjectionFactorizationUnderInverseHomotopy {i : C(C, A)}
    (hi : IsCofibration.{u, u, u} i) :
    (mappingCylinderTargetInclusion i).Homotopy
      (mappingCylinderProjectionFactorizationUnderInverse (i := i) hi).right.hom :=
  Classical.choose <|
    Classical.choose_spec
      (hi.exists_homotopy_extension
        (mappingCylinderTargetInclusion i)
        (mappingCylinderFactorizationIn i)
        (mappingCylinderFactorizationBoundaryHomotopy (i := i)))

/-- Helper for Lemma 10.7.8: after composing the corrected inverse with the canonical projection,
the result is homotopic under `C` to the identity on `A`. -/
private theorem mappingCylinderProjectionFactorizationUnderInverse_comp_projection_homotopic_id
    {i : C(C, A)} (hi : IsCofibration.{u, u, u} i) :
    HomotopicUnder
      (mappingCylinderProjectionFactorizationUnderInverse (i := i) hi ≫
        mappingCylinderProjectionFactorizationUnder (i := i))
      (𝟙 (Under.mk (TopCat.ofHom i) : Under (TopCat.of C))) := by
  -- Postcompose the corrected inverse homotopy with the projection and use that the boundary
  -- path projects to the constant map `i`.
  refine ⟨{
    toHomotopy :=
      ((ContinuousMap.Homotopy.refl (mappingCylinderProjection i)).comp
          (mappingCylinderProjectionFactorizationUnderInverseHomotopy (i := i) hi).symm).cast
          (by
            simp [mappingCylinderProjectionFactorizationUnderInverse,
              mappingCylinderProjectionFactorizationUnder, TopCat.ofHom_comp])
          (by
            simpa [mappingCylinderProjection_comp_targetInclusion])
    prop' := ?_
  }⟩
  intro t
  ext c
  change
    (mappingCylinderProjection i)
        ((mappingCylinderProjectionFactorizationUnderInverseHomotopy (i := i) hi)
          (σ t, i c)) =
      i c
  have hboundary :=
    (Classical.choose_spec
      (Classical.choose_spec
        (hi.exists_homotopy_extension
          (mappingCylinderTargetInclusion i)
          (mappingCylinderFactorizationIn i)
          (mappingCylinderFactorizationBoundaryHomotopy (i := i))))) (σ t, c)
  calc
    (mappingCylinderProjection i)
        ((mappingCylinderProjectionFactorizationUnderInverseHomotopy (i := i) hi)
          (σ t, i c)) =
    (mappingCylinderProjection i)
        ((mappingCylinderFactorizationBoundaryHomotopy (i := i)) (σ t, c)) := by
          simpa [mappingCylinderProjectionFactorizationUnderInverseHomotopy] using
            congrArg (mappingCylinderProjection i) hboundary
    _ = i c := by
      have hproj :=
        congrArg (fun g : C(C × I, A) ↦ g (c, σ t))
          (mappingCylinderProjection_comp_cylinderInclusion i)
      simpa [mappingCylinderFactorizationBoundaryHomotopy,
        mappingCylinderFactorizationBoundaryPathMap, ContinuousMap.comp_apply] using hproj

/-- Helper for Lemma 10.7.8: maps out of a mapping cylinder agree once they agree on the target
and cylinder legs. -/
private theorem mappingCylinderHom_ext {X Y Z : Type u} [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace Z] {f : C(X, Y)} {u v : C(f.mappingCylinder, Z)}
    (htarget :
      u.comp (mappingCylinderTargetInclusion f) = v.comp (mappingCylinderTargetInclusion f))
    (hcylinder :
      u.comp (mappingCylinderCylinderInclusion f) = v.comp (mappingCylinderCylinderInclusion f)) :
    u = v := by
  -- Compare the two maps on the pushout legs defining the mapping cylinder.
  have hcat : TopCat.ofHom u = TopCat.ofHom v := by
    apply pushout.hom_ext
    · simpa [TopCat.ofHom_comp] using congrArg TopCat.ofHom htarget
    · simpa [TopCat.ofHom_comp] using congrArg TopCat.ofHom hcylinder
  simpa using congrArg TopCat.Hom.hom hcat

/-- Helper for Lemma 10.7.8: the time-`0` point of the cylinder summand is glued to the target
copy of `i c`. -/
private theorem mappingCylinderCylinderInclusion_apply_zero {i : C(C, A)} (c : C) :
    (mappingCylinderCylinderInclusion i) (c, 0) = mappingCylinderTargetInclusion i (i c) := by
  -- Evaluate the defining pushout relation of the mapping cylinder at the chosen source point.
  have hc :=
    congrArg (fun g : C(C, i.mappingCylinder) ↦ g c) (mappingCylinderTargetInclusion_comp i)
  simpa [ContinuousMap.mappingCylinderTimeZeroInclusion, ContinuousMap.comp_apply] using hc.symm

/-- Helper for Lemma 10.7.8: the constant target-path family used in the explicit deformation of
`i.mappingCylinder`. -/
private def mappingCylinderConstantPathMap {i : C(C, A)} : C(A, C(I, i.mappingCylinder)) :=
  ((mappingCylinderTargetInclusion i).comp ContinuousMap.fst).curry

/-- Helper for Lemma 10.7.8: the cylinder side of the explicit deformation scales the interval
coordinate by the homotopy parameter. -/
private def scaledCylinderCoordinateMap (X : Type u) [TopologicalSpace X] :
    C((X × I) × I, X × I) :=
  { toFun := fun z ↦ (z.1.1, z.2 * z.1.2)
    continuous_toFun := by
      refine Continuous.prodMk continuous_fst.fst ?_
      exact Continuous.subtype_mk
        ((continuous_subtype_val.comp continuous_snd).mul
          (continuous_subtype_val.comp continuous_fst.snd))
        (fun z ↦ unitInterval.mul_mem z.2.property z.1.2.property) }

/-- Helper for Lemma 10.7.8: the scaled cylinder paths contract each cylinder line to its
time-`0` endpoint. -/
private def mappingCylinderScaledCylinderPathMap {i : C(C, A)} :
    C(C × I, C(I, i.mappingCylinder)) :=
  ((mappingCylinderCylinderInclusion i).comp (scaledCylinderCoordinateMap C)).curry

/-- Helper for Lemma 10.7.8: at `s = 0`, the scaled cylinder path is the constant path at the
target copy of `i c`. -/
private theorem mappingCylinderScaledCylinderPathMap_apply_zero {i : C(C, A)} (c : C) :
    mappingCylinderScaledCylinderPathMap (i := i) (c, 0) =
      mappingCylinderConstantPathMap (i := i) (i c) := by
  -- At time `0`, the cylinder point is glued to the target inclusion of `i c`.
  ext t
  simp [mappingCylinderScaledCylinderPathMap, scaledCylinderCoordinateMap,
    mappingCylinderConstantPathMap, mappingCylinderCylinderInclusion_apply_zero]

/-- Helper for Lemma 10.7.8: at `s = 1`, the scaled cylinder path is the full cylinder path. -/
private theorem mappingCylinderScaledCylinderPathMap_apply_one {i : C(C, A)} (c : C) :
    mappingCylinderScaledCylinderPathMap (i := i) (c, 1) =
      (mappingCylinderCylinderInclusion i).curry c := by
  -- Scaling by `1` leaves the cylinder parameter unchanged.
  ext t
  simp [mappingCylinderScaledCylinderPathMap, scaledCylinderCoordinateMap]

/-- Helper for Lemma 10.7.8: the explicit cylinder-side homotopy needed to normalize the
left-composite inverse law. -/
private def mappingCylinderProjectionPathHomotopy {i : C(C, A)} :
    ((mappingCylinderConstantPathMap (i := i)).comp i).Homotopy
      ((mappingCylinderCylinderInclusion i).curry) :=
  -- Use the same explicit interval-scaling deformation as in Lemma 6.3.2.
  ContinuousMap.Homotopy.ofProdSwap
    (mappingCylinderScaledCylinderPathMap (i := i))
    (mappingCylinderScaledCylinderPathMap_apply_zero (i := i))
    (mappingCylinderScaledCylinderPathMap_apply_one (i := i))

/-- Helper for Lemma 10.7.8: descending the constant target paths and the cylinder-side
deformation gives a path-space map on `i.mappingCylinder`. -/
private def mappingCylinderProjectionDeformationPathMap {i : C(C, A)} :
    C(i.mappingCylinder, C(I, i.mappingCylinder)) :=
  mappingCylinderDesc (mappingCylinderConstantPathMap (i := i))
    (mappingCylinderProjectionPathHomotopy (i := i))

/-- Helper for Lemma 10.7.8: evaluating the descended deformation at time `0` gives
`mappingCylinderTargetInclusion i ∘ mappingCylinderProjection i`. -/
private theorem mappingCylinderProjectionDeformationPathMap_evalZero {i : C(C, A)} :
    (pathSpaceEvalAt 0 i.mappingCylinder).comp
        (mappingCylinderProjectionDeformationPathMap (i := i)) =
      (mappingCylinderTargetInclusion i).comp (mappingCylinderProjection i) := by
  -- Compare the two maps on the two pushout legs of the mapping cylinder.
  apply mappingCylinderHom_ext
  · ext a
    have hdesc :
        (mappingCylinderProjectionDeformationPathMap (i := i))
            (mappingCylinderTargetInclusion i a) =
          mappingCylinderConstantPathMap (i := i) a := by
      simpa [mappingCylinderProjectionDeformationPathMap] using
        congrArg (fun g : C(A, C(I, i.mappingCylinder)) ↦ g a)
          (mappingCylinderDesc_comp_targetInclusion
            (mappingCylinderConstantPathMap (i := i))
            (mappingCylinderProjectionPathHomotopy (i := i)))
    have hproj : (mappingCylinderProjection i) (mappingCylinderTargetInclusion i a) = a := by
      simpa [ContinuousMap.comp_apply] using
        congrArg (fun g : C(A, A) ↦ g a) (mappingCylinderProjection_comp_targetInclusion i)
    calc
      ((pathSpaceEvalAt 0 i.mappingCylinder).comp
          (mappingCylinderProjectionDeformationPathMap (i := i)) |>.comp
          (mappingCylinderTargetInclusion i)) a =
        (pathSpaceEvalAt 0 i.mappingCylinder) (mappingCylinderConstantPathMap (i := i) a) := by
          simp [ContinuousMap.comp_apply, hdesc]
      _ = mappingCylinderTargetInclusion i a := by
        simp [pathSpaceEvalAt, mappingCylinderConstantPathMap]
      _ = ((mappingCylinderTargetInclusion i).comp (mappingCylinderProjection i) |>.comp
            (mappingCylinderTargetInclusion i)) a := by
        simp [ContinuousMap.comp_apply, hproj]
  · ext z
    rcases z with ⟨c, s⟩
    have hdesc :
        (mappingCylinderProjectionDeformationPathMap (i := i))
            (mappingCylinderCylinderInclusion i (c, s)) =
          mappingCylinderScaledCylinderPathMap (i := i) (c, s) := by
      simpa [mappingCylinderProjectionDeformationPathMap] using
        congrArg (fun g : C(C × I, C(I, i.mappingCylinder)) ↦ g (c, s))
          (mappingCylinderDesc_comp_cylinderInclusion
            (mappingCylinderConstantPathMap (i := i))
            (mappingCylinderProjectionPathHomotopy (i := i)))
    have hproj :
        (mappingCylinderProjection i) (mappingCylinderCylinderInclusion i (c, s)) = i c := by
      simpa [ContinuousMap.comp_apply] using
        congrArg (fun g : C(C × I, A) ↦ g (c, s))
          (mappingCylinderProjection_comp_cylinderInclusion i)
    calc
      ((pathSpaceEvalAt 0 i.mappingCylinder).comp
          (mappingCylinderProjectionDeformationPathMap (i := i)) |>.comp
          (mappingCylinderCylinderInclusion i)) (c, s) =
        (pathSpaceEvalAt 0 i.mappingCylinder)
          (mappingCylinderScaledCylinderPathMap (i := i) (c, s)) := by
          simp [ContinuousMap.comp_apply, hdesc]
      _ = mappingCylinderTargetInclusion i (i c) := by
        simp [mappingCylinderScaledCylinderPathMap, scaledCylinderCoordinateMap, pathSpaceEvalAt,
          mappingCylinderCylinderInclusion_apply_zero]
      _ = ((mappingCylinderTargetInclusion i).comp (mappingCylinderProjection i) |>.comp
            (mappingCylinderCylinderInclusion i)) (c, s) := by
        simp [ContinuousMap.comp_apply, hproj]

/-- Helper for Lemma 10.7.8: evaluating the descended deformation at time `1` gives the identity
on `i.mappingCylinder`. -/
private theorem mappingCylinderProjectionDeformationPathMap_evalOne {i : C(C, A)} :
    (pathSpaceEvalAt 1 i.mappingCylinder).comp
        (mappingCylinderProjectionDeformationPathMap (i := i)) =
      ContinuousMap.id i.mappingCylinder := by
  -- The descended path is constant on `A` and reaches the cylinder point at time `1`.
  apply mappingCylinderHom_ext
  · ext a
    have hdesc :
        (mappingCylinderProjectionDeformationPathMap (i := i))
            (mappingCylinderTargetInclusion i a) =
          mappingCylinderConstantPathMap (i := i) a := by
      simpa [mappingCylinderProjectionDeformationPathMap] using
        congrArg (fun g : C(A, C(I, i.mappingCylinder)) ↦ g a)
          (mappingCylinderDesc_comp_targetInclusion
            (mappingCylinderConstantPathMap (i := i))
            (mappingCylinderProjectionPathHomotopy (i := i)))
    calc
      ((pathSpaceEvalAt 1 i.mappingCylinder).comp
          (mappingCylinderProjectionDeformationPathMap (i := i)) |>.comp
          (mappingCylinderTargetInclusion i)) a =
        (pathSpaceEvalAt 1 i.mappingCylinder) (mappingCylinderConstantPathMap (i := i) a) := by
          simp [ContinuousMap.comp_apply, hdesc]
      _ = (ContinuousMap.id i.mappingCylinder).comp (mappingCylinderTargetInclusion i) a := by
        simp [pathSpaceEvalAt, mappingCylinderConstantPathMap]
  · ext z
    rcases z with ⟨c, s⟩
    have hdesc :
        (mappingCylinderProjectionDeformationPathMap (i := i))
            (mappingCylinderCylinderInclusion i (c, s)) =
          mappingCylinderScaledCylinderPathMap (i := i) (c, s) := by
      simpa [mappingCylinderProjectionDeformationPathMap] using
        congrArg (fun g : C(C × I, C(I, i.mappingCylinder)) ↦ g (c, s))
          (mappingCylinderDesc_comp_cylinderInclusion
            (mappingCylinderConstantPathMap (i := i))
            (mappingCylinderProjectionPathHomotopy (i := i)))
    calc
      ((pathSpaceEvalAt 1 i.mappingCylinder).comp
          (mappingCylinderProjectionDeformationPathMap (i := i)) |>.comp
          (mappingCylinderCylinderInclusion i)) (c, s) =
        (pathSpaceEvalAt 1 i.mappingCylinder)
          (mappingCylinderScaledCylinderPathMap (i := i) (c, s)) := by
          simp [ContinuousMap.comp_apply, hdesc]
      _ = (ContinuousMap.id i.mappingCylinder).comp (mappingCylinderCylinderInclusion i) (c, s) := by
        simp [mappingCylinderScaledCylinderPathMap, scaledCylinderCoordinateMap, pathSpaceEvalAt,
          ContinuousMap.comp_apply]

/-- Helper for Lemma 10.7.8: the descended deformation gives the standard homotopy from
`mappingCylinderTargetInclusion i ∘ mappingCylinderProjection i` to `id`. -/
private def mappingCylinderProjectionDeformationHomotopy {i : C(C, A)} :
    ((mappingCylinderTargetInclusion i).comp (mappingCylinderProjection i)).Homotopy
      (ContinuousMap.id i.mappingCylinder) :=
  ContinuousMap.Homotopy.ofPathSpaceMap
    (mappingCylinderProjectionDeformationPathMap (i := i))
    (mappingCylinderProjectionDeformationPathMap_evalZero (i := i))
    (mappingCylinderProjectionDeformationPathMap_evalOne (i := i))

/-- Helper for Lemma 10.7.8: restricting the descended deformation to the top slice
`mappingCylinderFactorizationIn i` recovers the boundary path of the mapping cylinder. -/
private theorem mappingCylinderProjectionDeformationPathMap_comp_factorizationIn
    {i : C(C, A)} :
    (mappingCylinderProjectionDeformationPathMap (i := i)).comp (mappingCylinderFactorizationIn i) =
      mappingCylinderFactorizationBoundaryPathMap (i := i) := by
  -- The top inclusion factors through the cylinder side at `s = 1`, so the descended path map is
  -- read off from the `s = 1` slice of the scaled cylinder deformation.
  ext c t
  have hdesc :
      (mappingCylinderProjectionDeformationPathMap (i := i))
          ((mappingCylinderFactorizationIn i) c) =
        mappingCylinderFactorizationBoundaryPathMap (i := i) c := by
    simpa [mappingCylinderFactorizationIn, mappingCylinderProjectionDeformationPathMap,
      mappingCylinderFactorizationBoundaryPathMap, ContinuousMap.comp_apply] using
      congrArg
        (fun g : C(C × I, C(I, i.mappingCylinder)) ↦ g (c, 1))
        (mappingCylinderDesc_comp_cylinderInclusion
          (mappingCylinderConstantPathMap (i := i))
          (mappingCylinderProjectionPathHomotopy (i := i)))
  calc
    ((mappingCylinderProjectionDeformationPathMap (i := i)).comp
        (mappingCylinderFactorizationIn i)) c t =
      mappingCylinderFactorizationBoundaryPathMap (i := i) c t := by
        simpa [ContinuousMap.comp_apply] using congrArg
          (fun γ : C(I, i.mappingCylinder) ↦ γ t) hdesc

/-- Helper for Lemma 10.7.8: restricting the descended deformation homotopy to
`mappingCylinderFactorizationIn i` gives the boundary homotopy. -/
private theorem mappingCylinderProjectionDeformationHomotopy_comp_factorizationIn
    {i : C(C, A)} :
    (mappingCylinderProjectionDeformationHomotopy (i := i)).toContinuousMap.comp
        ((ContinuousMap.id I).prodMap (mappingCylinderFactorizationIn i)) =
      (mappingCylinderFactorizationBoundaryHomotopy (i := i)).toContinuousMap := by
  -- Repackage the path-space restriction by evaluating both reconstructed homotopies pointwise.
  ext z
  rcases z with ⟨t, c⟩
  simpa [mappingCylinderProjectionDeformationHomotopy, mappingCylinderFactorizationBoundaryHomotopy,
    ContinuousMap.comp_apply] using
    congrArg (fun γ : C(I, i.mappingCylinder) ↦ γ t)
      (ContinuousMap.congr_fun
        (mappingCylinderProjectionDeformationPathMap_comp_factorizationIn (i := i)) c)

/-- Helper for Lemma 10.7.8: the loop `H.symm.trans H` contracts relative to the boundary
`({0, 1} : Set I) ×ˢ Set.univ`. -/
private theorem homotopySymmTransHomotopicRelRefl
    {T Z : Type u} [TopologicalSpace T] [TopologicalSpace Z]
    {r₀ r₁ : C(T, Z)}
    (H : r₀.Homotopy r₁) :
    (H.symm.trans H).toContinuousMap.HomotopicRel
      ((ContinuousMap.Homotopy.refl r₁).toContinuousMap)
      (({0, 1} : Set I) ×ˢ (Set.univ : Set T)) := by
  let loopParam : I × I → I := fun st ↦
    ⟨1 - Path.Homotopy.reflTransSymmAux (σ st.1, st.2), by
      have hmem := Path.Homotopy.reflTransSymmAux_mem_I (σ st.1, st.2)
      constructor
      · linarith [hmem.2]
      · linarith [hmem.1]⟩
  refine ⟨{
      toHomotopy :=
        { toFun := fun sx ↦ H (loopParam (sx.1, sx.2.1), sx.2.2)
          continuous_toFun := by
            fun_prop
          map_zero_left := by
            intro tx
            rcases tx with ⟨t, x⟩
            change H (loopParam (0, t), x) = (H.symm.trans H) (t, x)
            rw [ContinuousMap.Homotopy.trans_apply]
            split_ifs with ht
            · have hParam :
                loopParam (0, t) =
                  σ ⟨2 * t, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨t.2.1, ht⟩⟩ := by
                apply Subtype.ext
                have ht' : (t : ℝ) ≤ 1 / 2 := by
                  simpa using ht
                change (↑(loopParam (0, t)) : ℝ) = 1 - 2 * (t : ℝ)
                have hAux :
                    Path.Homotopy.reflTransSymmAux (σ 0, t) =
                      (if (t : ℝ) ≤ 1 / 2 then 2 * (t : ℝ) else 2 - 2 * (t : ℝ)) := by
                  simp [Path.Homotopy.reflTransSymmAux]
                rw [show (↑(loopParam (0, t)) : ℝ) =
                    1 - Path.Homotopy.reflTransSymmAux (σ 0, t) by
                  simp [loopParam]]
                rw [hAux, if_pos ht']
              exact congrArg (fun u : I ↦ H (u, x)) hParam
            · have hParam :
                loopParam (0, t) = ⟨2 * t - 1,
                  unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 ht).le, t.2.2⟩⟩ := by
                apply Subtype.ext
                have ht' : ¬ (t : ℝ) ≤ 1 / 2 := by
                  simpa using ht
                change (↑(loopParam (0, t)) : ℝ) = 2 * (t : ℝ) - 1
                have hAux :
                    Path.Homotopy.reflTransSymmAux (σ 0, t) =
                      (if (t : ℝ) ≤ 1 / 2 then 2 * (t : ℝ) else 2 - 2 * (t : ℝ)) := by
                  simp [Path.Homotopy.reflTransSymmAux]
                rw [show (↑(loopParam (0, t)) : ℝ) =
                    1 - Path.Homotopy.reflTransSymmAux (σ 0, t) by
                  simp [loopParam]]
                rw [hAux, if_neg ht']
                ring
              exact congrArg (fun u : I ↦ H (u, x)) hParam
          map_one_left := by
            intro tx
            rcases tx with ⟨t, x⟩
            simp [loopParam, Path.Homotopy.reflTransSymmAux] }
      prop' := ?_ }⟩
  intro s tx htx
  rcases tx with ⟨t, x⟩
  rcases Set.mem_insert_iff.mp htx.1 with ht | ht
  · subst ht
    norm_num [loopParam, Path.Homotopy.reflTransSymmAux]
  · have ht' : t = 1 := Set.mem_singleton_iff.mp ht
    subst ht'
    norm_num [loopParam, Path.Homotopy.reflTransSymmAux]

/-- Helper for Lemma 10.7.8: if an ordinary homotopy between endomorphisms of `Y` contracts after
restricting along `j`, then it upgrades to a homotopy under `C`. -/
private theorem homotopicUnder_of_restrictedContraction
    {Y : Type u} [TopologicalSpace Y] {j : C(C, Y)} (hj : IsCofibration.{u, u, u} j)
    {u₀ u₁ :
      (Under.mk (TopCat.ofHom j) : Under (TopCat.of C)) ⟶
        (Under.mk (TopCat.ofHom j) : Under (TopCat.of C))}
    (F : u₀.right.hom.Homotopy u₁.right.hom)
    (hFrel :
      (F.toContinuousMap.comp ((ContinuousMap.id I).prodMap j)).HomotopicRel
        ((ContinuousMap.Homotopy.refl j).toContinuousMap)
        (({0, 1} : Set I) ×ˢ (Set.univ : Set C))) :
    HomotopicUnder u₀ u₁ := by
  -- Rebracket the restricted contraction into a path-space homotopy, then extend it across `j`.
  have hu₀ : u₀.right.hom.comp j = j := by
    simpa using congrArg TopCat.Hom.hom (Under.w u₀)
  have hu₁ : u₁.right.hom.comp j = j := by
    simpa using congrArg TopCat.Hom.hom (Under.w u₁)
  rcases hFrel with ⟨hFrel⟩
  let rawK : C((I × C) × I, Y) :=
    { toFun := fun sat ↦ hFrel.toHomotopy (sat.1.1, (sat.2, sat.1.2))
      continuous_toFun := by
        have hcoord : Continuous fun sat : (I × C) × I ↦ (sat.1.1, (sat.2, sat.1.2)) := by
          fun_prop
        simpa using hFrel.toHomotopy.continuous.comp hcoord }
  let K :
      (F.toPathSpaceMap.comp j).Homotopy ((ContinuousMap.Homotopy.refl j).toPathSpaceMap) :=
    { toContinuousMap := rawK.curry
      map_zero_left := by
        intro c
        ext t
        calc
          rawK.curry (0, c) t = hFrel.toHomotopy (0, (t, c)) := rfl
          _ = (F.toContinuousMap.comp ((ContinuousMap.id I).prodMap j)) (t, c) := by
            exact hFrel.toHomotopy.apply_zero (t, c)
          _ = (F.toPathSpaceMap.comp j) c t := rfl
      map_one_left := by
        intro c
        ext t
        calc
          rawK.curry (1, c) t = ((ContinuousMap.Homotopy.refl j).toContinuousMap) (t, c) := by
            change hFrel.toHomotopy (1, (t, c)) = ((ContinuousMap.Homotopy.refl j).toContinuousMap) (t, c)
            exact hFrel.toHomotopy.apply_one (t, c)
          _ = ((ContinuousMap.Homotopy.refl j).toPathSpaceMap) c t := rfl }
  obtain ⟨G, L, hL⟩ := hj.exists_homotopy_extension
    (f₀ := F.toPathSpaceMap) (g := (ContinuousMap.Homotopy.refl j).toPathSpaceMap) K
  have hGj : G.comp j = (ContinuousMap.Homotopy.refl j).toPathSpaceMap := by
    ext c t
    calc
      G (j c) t = L (1, j c) t := by
        simpa using congrArg (fun γ : C(I, Y) ↦ γ t) (L.apply_one (j c)).symm
      _ = K (1, c) t := by
        simpa using ContinuousMap.congr_fun (hL (1, c)) t
      _ = ((ContinuousMap.Homotopy.refl j).toPathSpaceMap) c t := by
        simpa using ContinuousMap.congr_fun (K.apply_one c) t
  let v₀ :
      (Under.mk (TopCat.ofHom j) : Under (TopCat.of C)) ⟶
        (Under.mk (TopCat.ofHom j) : Under (TopCat.of C)) :=
    Under.homMk (TopCat.ofHom ((pathSpaceEvalAt 0 Y).comp G)) (by
      simpa using congrArg TopCat.ofHom (by
        ext c
        exact ContinuousMap.congr_fun (ContinuousMap.congr_fun hGj c) 0))
  let v₁ :
      (Under.mk (TopCat.ofHom j) : Under (TopCat.of C)) ⟶
        (Under.mk (TopCat.ofHom j) : Under (TopCat.of C)) :=
    Under.homMk (TopCat.ofHom ((pathSpaceEvalAt 1 Y).comp G)) (by
      simpa using congrArg TopCat.ofHom (by
        ext c
        exact ContinuousMap.congr_fun (ContinuousMap.congr_fun hGj c) 1))
  let sourceFaceRaw :
      ((pathSpaceEvalAt 0 Y).comp F.toPathSpaceMap).Homotopy ((pathSpaceEvalAt 0 Y).comp G) :=
    ContinuousMap.Homotopy.comp (ContinuousMap.Homotopy.refl (pathSpaceEvalAt 0 Y)) L
  let sourceFace : u₀.right.hom.Homotopy v₀.right.hom :=
    sourceFaceRaw.cast F.pathSpaceEvalAtZero_comp_toPathSpaceMap rfl
  have hSourceFace : HomotopicUnder u₀ v₀ := by
    refine ⟨{ toHomotopy := sourceFace, prop' := ?_ }⟩
    intro s
    ext c
    change (((pathSpaceEvalAt 0 Y).comp (L.curry s)).comp j) c = j c
    have hBoundary0 :
        (F.toContinuousMap.comp ((ContinuousMap.id I).prodMap j)) (0, c) = j c := by
      calc
        (F.toContinuousMap.comp ((ContinuousMap.id I).prodMap j)) (0, c) = F (0, j c) := rfl
        _ = u₀.right.hom (j c) := by
          simpa using F.apply_zero (j c)
        _ = j c := by
          simpa using ContinuousMap.congr_fun hu₀ c
    have hRestricted0 : hFrel.toHomotopy (s, (0, c)) = j c := by
      exact (hFrel.eq_fst s ⟨by simp, by simp⟩).trans hBoundary0
    have hFace0 :
        (((pathSpaceEvalAt 0 Y).comp (L.curry s)).comp j) c = hFrel.toHomotopy (s, (0, c)) := by
      calc
        (((pathSpaceEvalAt 0 Y).comp (L.curry s)).comp j) c =
            ((pathSpaceEvalAt 0 Y).comp (L.curry s)) (j c) := rfl
        _ = L (s, j c) 0 := rfl
        _ = K (s, c) 0 := by
            simpa using ContinuousMap.congr_fun (hL (s, c)) 0
        _ = hFrel.toHomotopy (s, (0, c)) := rfl
    exact hFace0.trans hRestricted0
  let middleFace : v₀.right.hom.Homotopy v₁.right.hom :=
    ContinuousMap.Homotopy.ofPathSpaceMap G rfl rfl
  have hMiddleFace : HomotopicUnder v₀ v₁ := by
    refine ⟨{ toHomotopy := middleFace, prop' := ?_ }⟩
    intro s
    ext c
    calc
      ((middleFace.curry s).comp j) c = G (j c) s := rfl
      _ = ((ContinuousMap.Homotopy.refl j).toPathSpaceMap) c s := by
        exact ContinuousMap.congr_fun (ContinuousMap.congr_fun hGj c) s
      _ = j c := rfl
  let targetFaceRaw :
      ((pathSpaceEvalAt 1 Y).comp F.toPathSpaceMap).Homotopy ((pathSpaceEvalAt 1 Y).comp G) :=
    ContinuousMap.Homotopy.comp (ContinuousMap.Homotopy.refl (pathSpaceEvalAt 1 Y)) L
  let targetFace : u₁.right.hom.Homotopy v₁.right.hom :=
    targetFaceRaw.cast ((F.pathSpaceEvalAt_comp_toPathSpaceMap 1).trans F.curry_one) rfl
  have hTargetFace : HomotopicUnder u₁ v₁ := by
    refine ⟨{ toHomotopy := targetFace, prop' := ?_ }⟩
    intro s
    ext c
    change (((pathSpaceEvalAt 1 Y).comp (L.curry s)).comp j) c = j c
    have hBoundary1 :
        (F.toContinuousMap.comp ((ContinuousMap.id I).prodMap j)) (1, c) = j c := by
      calc
        (F.toContinuousMap.comp ((ContinuousMap.id I).prodMap j)) (1, c) = F (1, j c) := rfl
        _ = u₁.right.hom (j c) := by
          simpa using F.apply_one (j c)
        _ = j c := by
          simpa using ContinuousMap.congr_fun hu₁ c
    have hRestricted1 : hFrel.toHomotopy (s, (1, c)) = j c := by
      exact (hFrel.eq_fst s ⟨by simp, by simp⟩).trans hBoundary1
    have hFace1 :
        (((pathSpaceEvalAt 1 Y).comp (L.curry s)).comp j) c = hFrel.toHomotopy (s, (1, c)) := by
      calc
        (((pathSpaceEvalAt 1 Y).comp (L.curry s)).comp j) c =
            ((pathSpaceEvalAt 1 Y).comp (L.curry s)) (j c) := rfl
        _ = L (s, j c) 1 := rfl
        _ = K (s, c) 1 := by
            simpa using ContinuousMap.congr_fun (hL (s, c)) 1
        _ = hFrel.toHomotopy (s, (1, c)) := rfl
    exact hFace1.trans hRestricted1
  exact HomotopicUnder.trans hSourceFace <|
    HomotopicUnder.trans hMiddleFace (HomotopicUnder.symm hTargetFace)

/-- Helper for Lemma 10.7.8: on `C`, the left-composite ordinary homotopy built from the
corrected inverse is the self-canceling loop
`mappingCylinderFactorizationBoundaryHomotopy.symm.trans mappingCylinderFactorizationBoundaryHomotopy`. -/
private theorem mappingCylinderProjectionFactorizationLeftCompositeRestrictionEq
    {i : C(C, A)} (hi : IsCofibration.{u, u, u} i) :
    let FfgRaw :
        ((mappingCylinderTargetInclusion i).comp (mappingCylinderProjection i)).Homotopy
          ((mappingCylinderProjectionFactorizationUnderInverse (i := i) hi).right.hom.comp
            (mappingCylinderProjection i)) :=
      ContinuousMap.Homotopy.comp
        (mappingCylinderProjectionFactorizationUnderInverseHomotopy (i := i) hi)
        (ContinuousMap.Homotopy.refl (mappingCylinderProjection i))
    let Ffg :
        ((mappingCylinderTargetInclusion i).comp (mappingCylinderProjection i)).Homotopy
          (mappingCylinderProjectionFactorizationUnder (i := i) ≫
            mappingCylinderProjectionFactorizationUnderInverse (i := i) hi).right.hom :=
      FfgRaw.cast rfl rfl
    ((Ffg.symm.trans (mappingCylinderProjectionDeformationHomotopy (i := i))).toContinuousMap).comp
      ((ContinuousMap.id I).prodMap (mappingCylinderFactorizationIn i)) =
      ((mappingCylinderFactorizationBoundaryHomotopy (i := i)).symm.trans
        (mappingCylinderFactorizationBoundaryHomotopy (i := i))).toContinuousMap := by
  let FfgRaw :
      ((mappingCylinderTargetInclusion i).comp (mappingCylinderProjection i)).Homotopy
        ((mappingCylinderProjectionFactorizationUnderInverse (i := i) hi).right.hom.comp
          (mappingCylinderProjection i)) :=
    ContinuousMap.Homotopy.comp
      (mappingCylinderProjectionFactorizationUnderInverseHomotopy (i := i) hi)
      (ContinuousMap.Homotopy.refl (mappingCylinderProjection i))
  let Ffg :
      ((mappingCylinderTargetInclusion i).comp (mappingCylinderProjection i)).Homotopy
        (mappingCylinderProjectionFactorizationUnder (i := i) ≫
          mappingCylinderProjectionFactorizationUnderInverse (i := i) hi).right.hom :=
    FfgRaw.cast rfl rfl
  have hcomp :
      (mappingCylinderProjection i).comp (mappingCylinderFactorizationIn i) = i :=
    mappingCylinderProjection_comp_factorizationIn i
  have hFfg :
      Ffg.toContinuousMap.comp ((ContinuousMap.id I).prodMap (mappingCylinderFactorizationIn i)) =
        (mappingCylinderFactorizationBoundaryHomotopy (i := i)).toContinuousMap := by
    -- Restricting the corrected inverse homotopy to `C` recovers the chosen boundary homotopy.
    ext z
    rcases z with ⟨t, c⟩
    have hboundary :=
      (Classical.choose_spec
        (Classical.choose_spec
          (hi.exists_homotopy_extension
            (mappingCylinderTargetInclusion i)
            (mappingCylinderFactorizationIn i)
            (mappingCylinderFactorizationBoundaryHomotopy (i := i))))) (t, c)
    calc
      Ffg (t, (mappingCylinderFactorizationIn i) c) =
          (mappingCylinderProjectionFactorizationUnderInverseHomotopy (i := i) hi)
            (t, (mappingCylinderProjection i) ((mappingCylinderFactorizationIn i) c)) := by
            rfl
      _ = (mappingCylinderProjectionFactorizationUnderInverseHomotopy (i := i) hi) (t, i c) := by
            rw [show (mappingCylinderProjection i) ((mappingCylinderFactorizationIn i) c) = i c by
              simpa using ContinuousMap.congr_fun hcomp c]
      _ = (mappingCylinderFactorizationBoundaryHomotopy (i := i)) (t, c) := by
            simpa [mappingCylinderProjectionFactorizationUnderInverseHomotopy] using hboundary
  have hLeftInvOnC_apply :
      ∀ z : I × C,
        (mappingCylinderProjectionDeformationHomotopy (i := i)) (z.1,
            (mappingCylinderFactorizationIn i) z.2) =
          (mappingCylinderFactorizationBoundaryHomotopy (i := i)) z := by
    intro z
    exact ContinuousMap.congr_fun
      (mappingCylinderProjectionDeformationHomotopy_comp_factorizationIn (i := i)) z
  -- Compare the restricted left composite pointwise with the normalized self-canceling loop.
  ext z
  rcases z with ⟨t, c⟩
  change
    (Ffg.symm.trans (mappingCylinderProjectionDeformationHomotopy (i := i)))
        (t, (mappingCylinderFactorizationIn i) c) =
      ((mappingCylinderFactorizationBoundaryHomotopy (i := i)).symm.trans
        (mappingCylinderFactorizationBoundaryHomotopy (i := i))) (t, c)
  rw [ContinuousMap.Homotopy.trans_apply, ContinuousMap.Homotopy.trans_apply]
  split_ifs with ht
  · simpa [ContinuousMap.Homotopy.symm] using
      ContinuousMap.congr_fun hFfg
        (σ ⟨2 * t, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨t.2.1, ht⟩⟩, c)
  · simpa using
      hLeftInvOnC_apply
        (⟨2 * t - 1, unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 ht).le, t.2.2⟩⟩, c)

/-- Helper for Lemma 10.7.8: the restricted left composite contracts relative to the boundary of
`I × C`. -/
private theorem mappingCylinderProjectionFactorizationLeftCompositeRestriction_homotopicRelRefl
    {i : C(C, A)} (hi : IsCofibration.{u, u, u} i) :
    let FfgRaw :
        ((mappingCylinderTargetInclusion i).comp (mappingCylinderProjection i)).Homotopy
          ((mappingCylinderProjectionFactorizationUnderInverse (i := i) hi).right.hom.comp
            (mappingCylinderProjection i)) :=
      ContinuousMap.Homotopy.comp
        (mappingCylinderProjectionFactorizationUnderInverseHomotopy (i := i) hi)
        (ContinuousMap.Homotopy.refl (mappingCylinderProjection i))
    let Ffg :
        ((mappingCylinderTargetInclusion i).comp (mappingCylinderProjection i)).Homotopy
          (mappingCylinderProjectionFactorizationUnder (i := i) ≫
            mappingCylinderProjectionFactorizationUnderInverse (i := i) hi).right.hom :=
      FfgRaw.cast rfl rfl
    ((((Ffg.symm.trans (mappingCylinderProjectionDeformationHomotopy (i := i))).toContinuousMap).comp
        ((ContinuousMap.id I).prodMap (mappingCylinderFactorizationIn i)))).HomotopicRel
      ((ContinuousMap.Homotopy.refl (mappingCylinderFactorizationIn i)).toContinuousMap)
        (({0, 1} : Set I) ×ˢ (Set.univ : Set C)) := by
  let FfgRaw :
      ((mappingCylinderTargetInclusion i).comp (mappingCylinderProjection i)).Homotopy
        ((mappingCylinderProjectionFactorizationUnderInverse (i := i) hi).right.hom.comp
          (mappingCylinderProjection i)) :=
    ContinuousMap.Homotopy.comp
      (mappingCylinderProjectionFactorizationUnderInverseHomotopy (i := i) hi)
      (ContinuousMap.Homotopy.refl (mappingCylinderProjection i))
  let Ffg :
      ((mappingCylinderTargetInclusion i).comp (mappingCylinderProjection i)).Homotopy
        (mappingCylinderProjectionFactorizationUnder (i := i) ≫
          mappingCylinderProjectionFactorizationUnderInverse (i := i) hi).right.hom :=
    FfgRaw.cast rfl rfl
  have hRestriction :
      ((Ffg.symm.trans (mappingCylinderProjectionDeformationHomotopy (i := i))).toContinuousMap).comp
          ((ContinuousMap.id I).prodMap (mappingCylinderFactorizationIn i)) =
        ((mappingCylinderFactorizationBoundaryHomotopy (i := i)).symm.trans
          (mappingCylinderFactorizationBoundaryHomotopy (i := i))).toContinuousMap := by
    -- Normalize the restricted composite once, so the remaining step is the standard loop
    -- contraction.
    simpa [FfgRaw, Ffg] using
      mappingCylinderProjectionFactorizationLeftCompositeRestrictionEq (i := i) hi
  -- After normalization, contract the self-canceling loop relative to the boundary.
  rcases homotopySymmTransHomotopicRelRefl (mappingCylinderFactorizationBoundaryHomotopy (i := i))
      with ⟨hrel⟩
  exact ⟨hrel.cast hRestriction.symm rfl⟩

/-- Helper for Lemma 10.7.8: the missing restricted-contraction bridge from an ordinary homotopy
to a homotopy under `mappingCylinderFactorizationIn i`. -/
private theorem mappingCylinderProjectionFactorizationUnder_comp_inverse_homotopic_id
    {i : C(C, A)} (hi : IsCofibration.{u, u, u} i) :
    HomotopicUnder
      (mappingCylinderProjectionFactorizationUnder (i := i) ≫
        mappingCylinderProjectionFactorizationUnderInverse (i := i) hi)
      (𝟙 (Under.mk (TopCat.ofHom (mappingCylinderFactorizationIn i)) : Under (TopCat.of C))) := by
  let FfgRaw :
      ((mappingCylinderTargetInclusion i).comp (mappingCylinderProjection i)).Homotopy
        ((mappingCylinderProjectionFactorizationUnderInverse (i := i) hi).right.hom.comp
          (mappingCylinderProjection i)) :=
    ContinuousMap.Homotopy.comp
      (mappingCylinderProjectionFactorizationUnderInverseHomotopy (i := i) hi)
      (ContinuousMap.Homotopy.refl (mappingCylinderProjection i))
  let Ffg :
      ((mappingCylinderTargetInclusion i).comp (mappingCylinderProjection i)).Homotopy
        (mappingCylinderProjectionFactorizationUnder (i := i) ≫
          mappingCylinderProjectionFactorizationUnderInverse (i := i) hi).right.hom :=
    FfgRaw.cast rfl rfl
  have hRestricted :
      (((Ffg.symm.trans (mappingCylinderProjectionDeformationHomotopy (i := i))).toContinuousMap).comp
          ((ContinuousMap.id I).prodMap (mappingCylinderFactorizationIn i))).HomotopicRel
        ((ContinuousMap.Homotopy.refl (mappingCylinderFactorizationIn i)).toContinuousMap)
        (({0, 1} : Set I) ×ˢ (Set.univ : Set C)) := by
    -- Route correction: promote the already-normalized restricted loop contraction, rather than
    -- redoing the transport inside the under-category theorem.
    simpa [FfgRaw, Ffg] using
      mappingCylinderProjectionFactorizationLeftCompositeRestriction_homotopicRelRefl
        (i := i) hi
  exact homotopicUnder_of_restrictedContraction
    (mappingCylinderFactorizationIn_isCofibration i)
    (Ffg.symm.trans (mappingCylinderProjectionDeformationHomotopy (i := i)))
    hRestricted

/-- Helper for Lemma 10.7.8: after pushing out along `j`, the factorization projection remains an
ordinary homotopy equivalence. -/
private theorem mappingCylinderProjectionFactorizationPushout_isHomotopyEquivalence
    {i : C(C, A)} {j : C(C, B)} (hi : IsCofibration.{u, u, u} i) :
    IsHomotopyEquivalence topCatHomotopyRel
      (TopCat.ofHom (pushoutMapOfUnderHom j (mappingCylinderProjectionFactorizationUnder (i := i)))) := by
  -- Push the chosen under-inverse and its two homotopies forward along `j`.
  refine (CategoryTheory.HomRel.IsHomotopyEquivalence.iff_exists_inverse
    (r := topCatHomotopyRel)).2 ?_
  refine ⟨TopCat.ofHom
    (pushoutMapOfUnderHom j (mappingCylinderProjectionFactorizationUnderInverse (i := i) hi)),
    ?_, ?_⟩
  · simpa [topCatHomotopyRel, TopCat.ofHom_comp, pushoutMapOfUnderHom_comp,
      pushoutMapOfUnderHom_id] using
        pushoutMapOfUnderHom_homotopic (g := j)
          (mappingCylinderProjectionFactorizationUnderInverse_comp_projection_homotopic_id
            (i := i) hi)
  · simpa [topCatHomotopyRel, TopCat.ofHom_comp, pushoutMapOfUnderHom_comp,
      pushoutMapOfUnderHom_id] using
        pushoutMapOfUnderHom_homotopic (g := j)
          (mappingCylinderProjectionFactorizationUnder_comp_inverse_homotopic_id
            (i := i) hi)

/-- Helper for Lemma 10.7.8: on the factorization-pushout side, the `A ⊕ B` summands map by the
target inclusion into `M_i` and the canonical right pushout leg for `B`. -/
private def doubleMappingCylinderFactorizationPushoutCoprodMap
    {i : C(C, A)} {j : C(C, B)} :
    C(A ⊕ B, (pushout (TopCat.ofHom (mappingCylinderFactorizationIn i)) (TopCat.ofHom j) : TopCat)) :=
  { toFun :=
      Sum.elim
        ((pushout.inl (TopCat.ofHom (mappingCylinderFactorizationIn i)) (TopCat.ofHom j)).hom.comp
          (mappingCylinderTargetInclusion i))
        (pushout.inr (TopCat.ofHom (mappingCylinderFactorizationIn i)) (TopCat.ofHom j)).hom
    continuous_toFun :=
      Continuous.sumElim
        (((pushout.inl (TopCat.ofHom (mappingCylinderFactorizationIn i))
          (TopCat.ofHom j)).hom).continuous.comp (mappingCylinderTargetInclusion i).continuous)
        ((pushout.inr (TopCat.ofHom (mappingCylinderFactorizationIn i))
          (TopCat.ofHom j)).hom).continuous }

/-- Helper for Lemma 10.7.8: on the factorization-pushout side, the cylinder summand maps through
the cylinder inclusion of the mapping cylinder. -/
private def doubleMappingCylinderFactorizationPushoutCylinderMap
    {i : C(C, A)} {j : C(C, B)} :
    C(C × I, (pushout (TopCat.ofHom (mappingCylinderFactorizationIn i)) (TopCat.ofHom j) : TopCat)) :=
  ((pushout.inl (TopCat.ofHom (mappingCylinderFactorizationIn i)) (TopCat.ofHom j)).hom).comp
    (mappingCylinderCylinderInclusion i)

/-- Helper for Lemma 10.7.8: the factorization-pushout comparison data satisfies the double
mapping cylinder gluing relation. -/
private theorem doubleMappingCylinderFactorizationPushout_condition
    {i : C(C, A)} {j : C(C, B)} :
    TopCat.ofHom (doubleMappingCylinderAttachMap i j) ≫
        TopCat.ofHom (doubleMappingCylinderFactorizationPushoutCoprodMap (i := i) (j := j)) =
      TopCat.ofHom (doubleMappingCylinderBoundaryMap C) ≫
        TopCat.ofHom (doubleMappingCylinderFactorizationPushoutCylinderMap (i := i) (j := j)) := by
  -- Verify the two boundary generators separately.
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  cases x with
  | inl c =>
      simp [doubleMappingCylinderFactorizationPushoutCoprodMap,
        doubleMappingCylinderFactorizationPushoutCylinderMap, ContinuousMap.comp_apply,
        mappingCylinderCylinderInclusion_apply_zero]
  | inr c =>
      simpa [doubleMappingCylinderFactorizationPushoutCoprodMap,
        doubleMappingCylinderFactorizationPushoutCylinderMap, mappingCylinderFactorizationIn,
        ContinuousMap.comp_apply] using
        congrArg
          (fun f :
            C(C, (pushout (TopCat.ofHom (mappingCylinderFactorizationIn i))
              (TopCat.ofHom j) : TopCat)) ↦ f c)
          (congrArg TopCat.Hom.hom
            (show TopCat.ofHom (mappingCylinderFactorizationIn i) ≫
                pushout.inl (TopCat.ofHom (mappingCylinderFactorizationIn i)) (TopCat.ofHom j) =
              TopCat.ofHom j ≫
                pushout.inr (TopCat.ofHom (mappingCylinderFactorizationIn i)) (TopCat.ofHom j) from
              pushout.condition)).symm

/-- Helper for Lemma 10.7.8: the double mapping cylinder maps to the factorization pushout by the
universal property of its defining pushout. -/
private def doubleMappingCylinderToFactorizationPushout
    {i : C(C, A)} {j : C(C, B)} :
    C(M(i, j), (pushout (TopCat.ofHom (mappingCylinderFactorizationIn i)) (TopCat.ofHom j) : TopCat)) :=
  (pushout.desc
    (TopCat.ofHom (doubleMappingCylinderFactorizationPushoutCoprodMap (i := i) (j := j)))
    (TopCat.ofHom (doubleMappingCylinderFactorizationPushoutCylinderMap (i := i) (j := j)))
    (doubleMappingCylinderFactorizationPushout_condition (i := i) (j := j))).hom

/-- Helper for Lemma 10.7.8: the forward comparison map restricts on `A ⊕ B` to the expected
sum-side map into the factorization pushout. -/
private theorem doubleMappingCylinderToFactorizationPushout_comp_coprodInclusion
    {i : C(C, A)} {j : C(C, B)} :
    (doubleMappingCylinderToFactorizationPushout (i := i) (j := j)).comp
        (doubleMappingCylinderCoprodInclusion i j) =
      doubleMappingCylinderFactorizationPushoutCoprodMap (i := i) (j := j) := by
  -- Read the forward comparison map on the coproduct leg using `pushout.inl_desc`.
  simpa [doubleMappingCylinderToFactorizationPushout] using
    congrArg TopCat.Hom.hom
      (pushout.inl_desc
        (TopCat.ofHom (doubleMappingCylinderFactorizationPushoutCoprodMap (i := i) (j := j)))
        (TopCat.ofHom (doubleMappingCylinderFactorizationPushoutCylinderMap (i := i) (j := j)))
        (doubleMappingCylinderFactorizationPushout_condition (i := i) (j := j)))

/-- Helper for Lemma 10.7.8: the forward comparison map restricts on the cylinder leg to the
expected cylinder-side map into the factorization pushout. -/
private theorem doubleMappingCylinderToFactorizationPushout_comp_cylinderInclusion
    {i : C(C, A)} {j : C(C, B)} :
    (doubleMappingCylinderToFactorizationPushout (i := i) (j := j)).comp
        (doubleMappingCylinderCylinderInclusion i j) =
      doubleMappingCylinderFactorizationPushoutCylinderMap (i := i) (j := j) := by
  -- Read the forward comparison map on the cylinder leg using `pushout.inr_desc`.
  simpa [doubleMappingCylinderToFactorizationPushout] using
    congrArg TopCat.Hom.hom
      (pushout.inr_desc
        (TopCat.ofHom (doubleMappingCylinderFactorizationPushoutCoprodMap (i := i) (j := j)))
        (TopCat.ofHom (doubleMappingCylinderFactorizationPushoutCylinderMap (i := i) (j := j)))
        (doubleMappingCylinderFactorizationPushout_condition (i := i) (j := j)))

/-- Helper for Lemma 10.7.8: evaluating the double mapping cylinder cylinder leg at `t = 0`
recovers the `A`-summand inclusion. -/
private theorem doubleMappingCylinderCylinderInclusion_curry_evalZero
    {i : C(C, A)} {j : C(C, B)} :
    (pathSpaceEvalAt 0 M(i, j)).comp ((doubleMappingCylinderCylinderInclusion i j).curry) =
      (((doubleMappingCylinderCoprodInclusion i j).comp sumLeftInclusion).comp i) := by
  -- Evaluate the pushout compatibility of the two inclusions on the left boundary point.
  ext c
  simpa [pathSpaceEvalAt, sumLeftInclusion, ContinuousMap.comp_apply,
    doubleMappingCylinderBoundaryMap] using
    (ContinuousMap.congr_fun (doubleMappingCylinderCoprodInclusion_comp i j) (Sum.inl c)).symm

/-- Helper for Lemma 10.7.8: evaluating the double mapping cylinder cylinder leg at `t = 1`
recovers the `B`-summand inclusion. -/
private theorem doubleMappingCylinderCylinderInclusion_curry_evalOne
    {i : C(C, A)} {j : C(C, B)} :
    (pathSpaceEvalAt 1 M(i, j)).comp ((doubleMappingCylinderCylinderInclusion i j).curry) =
      (((doubleMappingCylinderCoprodInclusion i j).comp sumRightInclusion).comp j) := by
  -- Evaluate the same pushout compatibility on the right boundary point.
  ext c
  simpa [pathSpaceEvalAt, sumRightInclusion, ContinuousMap.comp_apply,
    doubleMappingCylinderBoundaryMap] using
    (ContinuousMap.congr_fun (doubleMappingCylinderCoprodInclusion_comp i j) (Sum.inr c)).symm

/-- Helper for Lemma 10.7.8: the cylinder leg of `M(i, j)` is the boundary homotopy between the
`A`- and `B`-summand inclusions needed to descend a map out of `M_i`. -/
private def factorizationPushoutToDoubleMappingCylinderBoundaryHomotopy
    {i : C(C, A)} {j : C(C, B)} :
    (((doubleMappingCylinderCoprodInclusion i j).comp sumLeftInclusion).comp i).Homotopy
      (((doubleMappingCylinderCoprodInclusion i j).comp sumRightInclusion).comp j) :=
  ContinuousMap.Homotopy.ofPathSpaceMap
    ((doubleMappingCylinderCylinderInclusion i j).curry)
    (doubleMappingCylinderCylinderInclusion_curry_evalZero (i := i) (j := j))
    (doubleMappingCylinderCylinderInclusion_curry_evalOne (i := i) (j := j))

/-- Helper for Lemma 10.7.8: the left leg of the inverse comparison map is the descended map from
`M_i` to `M(i, j)` determined by the boundary cylinder homotopy. -/
private def factorizationPushoutToDoubleMappingCylinderLeftMap
    {i : C(C, A)} {j : C(C, B)} :
    C(i.mappingCylinder, M(i, j)) :=
  mappingCylinderDesc
    ((doubleMappingCylinderCoprodInclusion i j).comp sumLeftInclusion)
    (factorizationPushoutToDoubleMappingCylinderBoundaryHomotopy (i := i) (j := j))

/-- Helper for Lemma 10.7.8: the descended left comparison map restricts on the top slice
`mappingCylinderFactorizationIn i` to the `B`-summand inclusion. -/
private theorem factorizationPushoutToDoubleMappingCylinderLeftMap_comp_factorizationIn
    {i : C(C, A)} {j : C(C, B)} :
    (factorizationPushoutToDoubleMappingCylinderLeftMap (i := i) (j := j)).comp
        (mappingCylinderFactorizationIn i) =
      ((doubleMappingCylinderCoprodInclusion i j).comp sumRightInclusion).comp j := by
  -- Read the descended map on the top slice through the `t = 1` endpoint of the boundary
  -- homotopy into `M(i, j)`.
  ext c
  have hdesc :
      (factorizationPushoutToDoubleMappingCylinderLeftMap (i := i) (j := j))
          ((mappingCylinderFactorizationIn i) c) =
        (factorizationPushoutToDoubleMappingCylinderBoundaryHomotopy (i := i) (j := j)) (1, c) := by
    simpa [factorizationPushoutToDoubleMappingCylinderLeftMap, mappingCylinderFactorizationIn,
      ContinuousMap.comp_apply] using
      congrArg
        (fun g : C(C × I, M(i, j)) ↦ g (c, 1))
        (mappingCylinderDesc_comp_cylinderInclusion
          ((doubleMappingCylinderCoprodInclusion i j).comp sumLeftInclusion)
          (factorizationPushoutToDoubleMappingCylinderBoundaryHomotopy (i := i) (j := j)))
  calc
    ((factorizationPushoutToDoubleMappingCylinderLeftMap (i := i) (j := j)).comp
        (mappingCylinderFactorizationIn i)) c =
      (factorizationPushoutToDoubleMappingCylinderBoundaryHomotopy (i := i) (j := j)) (1, c) := by
        simpa [ContinuousMap.comp_apply] using hdesc
    _ = ((doubleMappingCylinderCoprodInclusion i j).comp sumRightInclusion).comp j c := by
      simpa [factorizationPushoutToDoubleMappingCylinderBoundaryHomotopy, pathSpaceEvalAt,
        ContinuousMap.comp_apply] using
        ContinuousMap.congr_fun (doubleMappingCylinderCylinderInclusion_curry_evalOne
          (i := i) (j := j)) c

/-- Helper for Lemma 10.7.8: the right leg of the inverse comparison map is the `B`-summand
inclusion into the double mapping cylinder. -/
private def factorizationPushoutToDoubleMappingCylinderRightMap
    {i : C(C, A)} {j : C(C, B)} :
    C(B, M(i, j)) :=
  (doubleMappingCylinderCoprodInclusion i j).comp sumRightInclusion

/-- Helper for Lemma 10.7.8: the inverse comparison data satisfies the factorization-pushout
gluing relation. -/
private theorem factorizationPushoutToDoubleMappingCylinder_condition
    {i : C(C, A)} {j : C(C, B)} :
    TopCat.ofHom (mappingCylinderFactorizationIn i) ≫
        TopCat.ofHom (factorizationPushoutToDoubleMappingCylinderLeftMap (i := i) (j := j)) =
      TopCat.ofHom j ≫
        TopCat.ofHom (factorizationPushoutToDoubleMappingCylinderRightMap (i := i) (j := j)) := by
  -- The left map hits the `B`-summand on the top slice, exactly matching the right pushout leg.
  simpa [TopCat.ofHom_comp] using
    congrArg TopCat.ofHom
      (factorizationPushoutToDoubleMappingCylinderLeftMap_comp_factorizationIn
        (i := i) (j := j))

/-- Helper for Lemma 10.7.8: the factorization pushout maps back to `M(i, j)` by the universal
property of the factorization pushout. -/
private def factorizationPushoutToDoubleMappingCylinder
    {i : C(C, A)} {j : C(C, B)} :
    C((pushout (TopCat.ofHom (mappingCylinderFactorizationIn i)) (TopCat.ofHom j) : TopCat), M(i, j)) :=
  (pushout.desc
    (TopCat.ofHom (factorizationPushoutToDoubleMappingCylinderLeftMap (i := i) (j := j)))
    (TopCat.ofHom (factorizationPushoutToDoubleMappingCylinderRightMap (i := i) (j := j)))
    (factorizationPushoutToDoubleMappingCylinder_condition (i := i) (j := j))).hom

/-- Helper for Lemma 10.7.8: the inverse comparison map restricts on the left factorization
pushout leg to the descended map from `M_i`. -/
private theorem factorizationPushoutToDoubleMappingCylinder_comp_inl
    {i : C(C, A)} {j : C(C, B)} :
    (factorizationPushoutToDoubleMappingCylinder (i := i) (j := j)).comp
        (pushout.inl (TopCat.ofHom (mappingCylinderFactorizationIn i)) (TopCat.ofHom j)).hom =
      factorizationPushoutToDoubleMappingCylinderLeftMap (i := i) (j := j) := by
  -- Read the inverse comparison map on the left pushout leg using `pushout.inl_desc`.
  simpa [factorizationPushoutToDoubleMappingCylinder] using
    congrArg TopCat.Hom.hom
      (pushout.inl_desc
        (TopCat.ofHom (factorizationPushoutToDoubleMappingCylinderLeftMap (i := i) (j := j)))
        (TopCat.ofHom (factorizationPushoutToDoubleMappingCylinderRightMap (i := i) (j := j)))
        (factorizationPushoutToDoubleMappingCylinder_condition (i := i) (j := j)))

/-- Helper for Lemma 10.7.8: the inverse comparison map restricts on the right factorization
pushout leg to the `B`-summand inclusion. -/
private theorem factorizationPushoutToDoubleMappingCylinder_comp_inr
    {i : C(C, A)} {j : C(C, B)} :
    (factorizationPushoutToDoubleMappingCylinder (i := i) (j := j)).comp
        (pushout.inr (TopCat.ofHom (mappingCylinderFactorizationIn i)) (TopCat.ofHom j)).hom =
      factorizationPushoutToDoubleMappingCylinderRightMap (i := i) (j := j) := by
  -- Read the inverse comparison map on the right pushout leg using `pushout.inr_desc`.
  simpa [factorizationPushoutToDoubleMappingCylinder] using
    congrArg TopCat.Hom.hom
      (pushout.inr_desc
        (TopCat.ofHom (factorizationPushoutToDoubleMappingCylinderLeftMap (i := i) (j := j)))
        (TopCat.ofHom (factorizationPushoutToDoubleMappingCylinderRightMap (i := i) (j := j)))
        (factorizationPushoutToDoubleMappingCylinder_condition (i := i) (j := j)))

/-- Helper for Lemma 10.7.8: the comparison maps compose to the identity on the double mapping
cylinder. -/
private theorem doubleMappingCylinderFactorizationPushout_hom_inv_id
    {i : C(C, A)} {j : C(C, B)} :
    TopCat.ofHom (doubleMappingCylinderToFactorizationPushout (i := i) (j := j)) ≫
        TopCat.ofHom (factorizationPushoutToDoubleMappingCylinder (i := i) (j := j)) =
      𝟙 (TopCat.of (M(i, j))) := by
  have hcoprodInv :
      (factorizationPushoutToDoubleMappingCylinder (i := i) (j := j)).comp
          (doubleMappingCylinderFactorizationPushoutCoprodMap (i := i) (j := j)) =
        doubleMappingCylinderCoprodInclusion i j := by
    have hleft :
        (factorizationPushoutToDoubleMappingCylinderLeftMap (i := i) (j := j)).comp
            (mappingCylinderTargetInclusion i) =
          (doubleMappingCylinderCoprodInclusion i j).comp sumLeftInclusion := by
      -- Read the descended inverse comparison map on the target side of `M_i`.
      simpa [factorizationPushoutToDoubleMappingCylinderLeftMap] using
        mappingCylinderDesc_comp_targetInclusion
          ((doubleMappingCylinderCoprodInclusion i j).comp sumLeftInclusion)
          (factorizationPushoutToDoubleMappingCylinderBoundaryHomotopy (i := i) (j := j))
    ext x
    cases x with
    | inl a =>
        calc
          ((factorizationPushoutToDoubleMappingCylinder (i := i) (j := j)).comp
              (doubleMappingCylinderFactorizationPushoutCoprodMap (i := i) (j := j))) (Sum.inl a) =
            (factorizationPushoutToDoubleMappingCylinderLeftMap (i := i) (j := j))
              (mappingCylinderTargetInclusion i a) := by
                simpa [doubleMappingCylinderFactorizationPushoutCoprodMap, ContinuousMap.comp_apply]
                  using
                    congrArg
                      (fun g : C(i.mappingCylinder, M(i, j)) ↦ g (mappingCylinderTargetInclusion i a))
                      (factorizationPushoutToDoubleMappingCylinder_comp_inl (i := i) (j := j))
          _ = ((doubleMappingCylinderCoprodInclusion i j).comp sumLeftInclusion) a := by
                simpa [ContinuousMap.comp_apply] using
                  congrArg (fun g : C(A, M(i, j)) ↦ g a) hleft
          _ = doubleMappingCylinderCoprodInclusion i j (Sum.inl a) := rfl
    | inr b =>
        calc
          ((factorizationPushoutToDoubleMappingCylinder (i := i) (j := j)).comp
              (doubleMappingCylinderFactorizationPushoutCoprodMap (i := i) (j := j))) (Sum.inr b) =
            (factorizationPushoutToDoubleMappingCylinderRightMap (i := i) (j := j)) b := by
                simpa [doubleMappingCylinderFactorizationPushoutCoprodMap, ContinuousMap.comp_apply]
                  using
                    congrArg (fun g : C(B, M(i, j)) ↦ g b)
                      (factorizationPushoutToDoubleMappingCylinder_comp_inr (i := i) (j := j))
          _ = doubleMappingCylinderCoprodInclusion i j (Sum.inr b) := rfl
  have hcylinderInv :
      (factorizationPushoutToDoubleMappingCylinder (i := i) (j := j)).comp
          (doubleMappingCylinderFactorizationPushoutCylinderMap (i := i) (j := j)) =
        doubleMappingCylinderCylinderInclusion i j := by
    have hleft :
        (factorizationPushoutToDoubleMappingCylinderLeftMap (i := i) (j := j)).comp
            (mappingCylinderCylinderInclusion i) =
          doubleMappingCylinderCylinderInclusion i j := by
      -- Read the descended inverse comparison map on the cylinder side of `M_i`.
      simpa [factorizationPushoutToDoubleMappingCylinderLeftMap,
        factorizationPushoutToDoubleMappingCylinderBoundaryHomotopy] using
        mappingCylinderDesc_comp_cylinderInclusion
          ((doubleMappingCylinderCoprodInclusion i j).comp sumLeftInclusion)
          (factorizationPushoutToDoubleMappingCylinderBoundaryHomotopy (i := i) (j := j))
    ext z
    rcases z with ⟨c, t⟩
    calc
      ((factorizationPushoutToDoubleMappingCylinder (i := i) (j := j)).comp
          (doubleMappingCylinderFactorizationPushoutCylinderMap (i := i) (j := j))) (c, t) =
        ((factorizationPushoutToDoubleMappingCylinderLeftMap (i := i) (j := j)).comp
          (mappingCylinderCylinderInclusion i)) (c, t) := by
            simpa [doubleMappingCylinderFactorizationPushoutCylinderMap, ContinuousMap.comp_apply]
              using
                congrArg
                  (fun g : C(i.mappingCylinder, M(i, j)) ↦ g (mappingCylinderCylinderInclusion i (c, t)))
                  (factorizationPushoutToDoubleMappingCylinder_comp_inl (i := i) (j := j))
      _ = doubleMappingCylinderCylinderInclusion i j (c, t) := by
            simpa [ContinuousMap.comp_apply] using
              congrArg (fun g : C(C × I, M(i, j)) ↦ g (c, t)) hleft
  have hcoprod :
      ((factorizationPushoutToDoubleMappingCylinder (i := i) (j := j)).comp
          (doubleMappingCylinderToFactorizationPushout (i := i) (j := j))).comp
        (doubleMappingCylinderCoprodInclusion i j) =
      doubleMappingCylinderCoprodInclusion i j := by
    rw [ContinuousMap.comp_assoc, doubleMappingCylinderToFactorizationPushout_comp_coprodInclusion]
    exact hcoprodInv
  have hcylinder :
      ((factorizationPushoutToDoubleMappingCylinder (i := i) (j := j)).comp
          (doubleMappingCylinderToFactorizationPushout (i := i) (j := j))).comp
        (doubleMappingCylinderCylinderInclusion i j) =
      doubleMappingCylinderCylinderInclusion i j := by
    rw [ContinuousMap.comp_assoc, doubleMappingCylinderToFactorizationPushout_comp_cylinderInclusion]
    exact hcylinderInv
  apply pushout.hom_ext
  · simpa [TopCat.ofHom_comp] using congrArg TopCat.ofHom hcoprod
  · simpa [TopCat.ofHom_comp] using congrArg TopCat.ofHom hcylinder

/-- Helper for Lemma 10.7.8: the comparison maps compose to the identity on the factorization
pushout. -/
private theorem doubleMappingCylinderFactorizationPushout_inv_hom_id
    {i : C(C, A)} {j : C(C, B)} :
    TopCat.ofHom (factorizationPushoutToDoubleMappingCylinder (i := i) (j := j)) ≫
        TopCat.ofHom (doubleMappingCylinderToFactorizationPushout (i := i) (j := j)) =
      𝟙
        (pushout (TopCat.ofHom (mappingCylinderFactorizationIn i)) (TopCat.ofHom j) : TopCat) := by
  have hleftTarget :
      ((doubleMappingCylinderToFactorizationPushout (i := i) (j := j)).comp
          (factorizationPushoutToDoubleMappingCylinderLeftMap (i := i) (j := j))).comp
        (mappingCylinderTargetInclusion i) =
      (pushout.inl (TopCat.ofHom (mappingCylinderFactorizationIn i)) (TopCat.ofHom j)).hom.comp
        (mappingCylinderTargetInclusion i) := by
    have hleft :
        (factorizationPushoutToDoubleMappingCylinderLeftMap (i := i) (j := j)).comp
            (mappingCylinderTargetInclusion i) =
          (doubleMappingCylinderCoprodInclusion i j).comp sumLeftInclusion := by
      -- The descended inverse comparison map restricts to the left end of `M(i, j)`.
      simpa [factorizationPushoutToDoubleMappingCylinderLeftMap] using
        mappingCylinderDesc_comp_targetInclusion
          ((doubleMappingCylinderCoprodInclusion i j).comp sumLeftInclusion)
          (factorizationPushoutToDoubleMappingCylinderBoundaryHomotopy (i := i) (j := j))
    calc
      ((doubleMappingCylinderToFactorizationPushout (i := i) (j := j)).comp
          (factorizationPushoutToDoubleMappingCylinderLeftMap (i := i) (j := j))).comp
          (mappingCylinderTargetInclusion i) =
        (doubleMappingCylinderToFactorizationPushout (i := i) (j := j)).comp
          ((factorizationPushoutToDoubleMappingCylinderLeftMap (i := i) (j := j)).comp
            (mappingCylinderTargetInclusion i)) := by
              rw [ContinuousMap.comp_assoc]
      _ = (doubleMappingCylinderToFactorizationPushout (i := i) (j := j)).comp
            ((doubleMappingCylinderCoprodInclusion i j).comp sumLeftInclusion) := by
              rw [hleft]
      _ = ((doubleMappingCylinderToFactorizationPushout (i := i) (j := j)).comp
            (doubleMappingCylinderCoprodInclusion i j)).comp sumLeftInclusion := by
              rw [ContinuousMap.comp_assoc]
      _ = (pushout.inl (TopCat.ofHom (mappingCylinderFactorizationIn i)) (TopCat.ofHom j)).hom.comp
            (mappingCylinderTargetInclusion i) := by
              rw [doubleMappingCylinderToFactorizationPushout_comp_coprodInclusion]
              rfl
  have hleftCylinder :
      ((doubleMappingCylinderToFactorizationPushout (i := i) (j := j)).comp
          (factorizationPushoutToDoubleMappingCylinderLeftMap (i := i) (j := j))).comp
        (mappingCylinderCylinderInclusion i) =
      (pushout.inl (TopCat.ofHom (mappingCylinderFactorizationIn i)) (TopCat.ofHom j)).hom.comp
        (mappingCylinderCylinderInclusion i) := by
    have hleft :
        (factorizationPushoutToDoubleMappingCylinderLeftMap (i := i) (j := j)).comp
            (mappingCylinderCylinderInclusion i) =
          doubleMappingCylinderCylinderInclusion i j := by
      -- The cylinder side of the descended inverse comparison map is the cylinder side of `M(i,j)`.
      simpa [factorizationPushoutToDoubleMappingCylinderLeftMap,
        factorizationPushoutToDoubleMappingCylinderBoundaryHomotopy] using
        mappingCylinderDesc_comp_cylinderInclusion
          ((doubleMappingCylinderCoprodInclusion i j).comp sumLeftInclusion)
          (factorizationPushoutToDoubleMappingCylinderBoundaryHomotopy (i := i) (j := j))
    calc
      ((doubleMappingCylinderToFactorizationPushout (i := i) (j := j)).comp
          (factorizationPushoutToDoubleMappingCylinderLeftMap (i := i) (j := j))).comp
          (mappingCylinderCylinderInclusion i) =
        (doubleMappingCylinderToFactorizationPushout (i := i) (j := j)).comp
          ((factorizationPushoutToDoubleMappingCylinderLeftMap (i := i) (j := j)).comp
            (mappingCylinderCylinderInclusion i)) := by
              rw [ContinuousMap.comp_assoc]
      _ = (doubleMappingCylinderToFactorizationPushout (i := i) (j := j)).comp
            (doubleMappingCylinderCylinderInclusion i j) := by
              rw [hleft]
      _ = (pushout.inl (TopCat.ofHom (mappingCylinderFactorizationIn i)) (TopCat.ofHom j)).hom.comp
            (mappingCylinderCylinderInclusion i) := by
              rw [doubleMappingCylinderToFactorizationPushout_comp_cylinderInclusion]
              rfl
  have hleft :
      (doubleMappingCylinderToFactorizationPushout (i := i) (j := j)).comp
          (factorizationPushoutToDoubleMappingCylinderLeftMap (i := i) (j := j)) =
        (pushout.inl (TopCat.ofHom (mappingCylinderFactorizationIn i)) (TopCat.ofHom j)).hom := by
    -- Compare the two maps from `M_i` on the target and cylinder generators.
    apply mappingCylinderHom_ext
    · exact hleftTarget
    · exact hleftCylinder
  have hinl :
      ((doubleMappingCylinderToFactorizationPushout (i := i) (j := j)).comp
          (factorizationPushoutToDoubleMappingCylinder (i := i) (j := j))).comp
        (pushout.inl (TopCat.ofHom (mappingCylinderFactorizationIn i)) (TopCat.ofHom j)).hom =
      (pushout.inl (TopCat.ofHom (mappingCylinderFactorizationIn i)) (TopCat.ofHom j)).hom := by
    rw [ContinuousMap.comp_assoc, factorizationPushoutToDoubleMappingCylinder_comp_inl]
    exact hleft
  have hinr :
      ((doubleMappingCylinderToFactorizationPushout (i := i) (j := j)).comp
          (factorizationPushoutToDoubleMappingCylinder (i := i) (j := j))).comp
        (pushout.inr (TopCat.ofHom (mappingCylinderFactorizationIn i)) (TopCat.ofHom j)).hom =
      (pushout.inr (TopCat.ofHom (mappingCylinderFactorizationIn i)) (TopCat.ofHom j)).hom := by
    calc
      ((doubleMappingCylinderToFactorizationPushout (i := i) (j := j)).comp
          (factorizationPushoutToDoubleMappingCylinder (i := i) (j := j))).comp
          (pushout.inr (TopCat.ofHom (mappingCylinderFactorizationIn i)) (TopCat.ofHom j)).hom =
        (doubleMappingCylinderToFactorizationPushout (i := i) (j := j)).comp
          (factorizationPushoutToDoubleMappingCylinderRightMap (i := i) (j := j)) := by
            rw [ContinuousMap.comp_assoc,
              factorizationPushoutToDoubleMappingCylinder_comp_inr]
      _ = (doubleMappingCylinderToFactorizationPushout (i := i) (j := j)).comp
            ((doubleMappingCylinderCoprodInclusion i j).comp sumRightInclusion) := by
              rfl
      _ = ((doubleMappingCylinderToFactorizationPushout (i := i) (j := j)).comp
            (doubleMappingCylinderCoprodInclusion i j)).comp sumRightInclusion := by
              rw [ContinuousMap.comp_assoc]
      _ = (pushout.inr (TopCat.ofHom (mappingCylinderFactorizationIn i)) (TopCat.ofHom j)).hom := by
              rw [doubleMappingCylinderToFactorizationPushout_comp_coprodInclusion]
              rfl
  apply pushout.hom_ext
  · simpa [TopCat.ofHom_comp] using congrArg TopCat.ofHom hinl
  · simpa [TopCat.ofHom_comp] using congrArg TopCat.ofHom hinr

/-- Helper for Lemma 10.7.8: the double mapping cylinder is canonically isomorphic to the pushout
obtained by gluing `B` to the source-faithful mapping-cylinder factorization of `i`. -/
private def doubleMappingCylinderFactorizationPushoutIso
    {i : C(C, A)} {j : C(C, B)} :
    M(i, j) ≅ (pushout (TopCat.ofHom (mappingCylinderFactorizationIn i)) (TopCat.ofHom j) : TopCat) :=
  { hom := TopCat.ofHom (doubleMappingCylinderToFactorizationPushout (i := i) (j := j))
    inv := TopCat.ofHom (factorizationPushoutToDoubleMappingCylinder (i := i) (j := j))
    hom_inv_id := doubleMappingCylinderFactorizationPushout_hom_inv_id (i := i) (j := j)
    inv_hom_id := doubleMappingCylinderFactorizationPushout_inv_hom_id (i := i) (j := j) }

/-- Helper for Lemma 10.7.8: after identifying the double mapping cylinder with the factorization
pushout, the quotient map is exactly the pushed-out factorization projection. -/
private theorem doubleMappingCylinderQuotientMap_viaFactorizationPushout
    {i : C(C, A)} {j : C(C, B)} :
    (doubleMappingCylinderFactorizationPushoutIso (i := i) (j := j)).hom ≫
        TopCat.ofHom (pushoutMapOfUnderHom j (mappingCylinderProjectionFactorizationUnder (i := i))) =
      doubleMappingCylinderQuotientMap i j := by
  have hcoprod :
      ((pushoutMapOfUnderHom j (mappingCylinderProjectionFactorizationUnder (i := i))).comp
          (doubleMappingCylinderFactorizationPushoutCoprodMap (i := i) (j := j))) =
        doubleMappingCylinderPushoutCoprodMap i j := by
    ext x
    cases x with
    | inl a =>
        have hproj : (mappingCylinderProjection i) (mappingCylinderTargetInclusion i a) = a := by
          simpa [ContinuousMap.comp_apply] using
            congrArg (fun g : C(A, A) ↦ g a) (mappingCylinderProjection_comp_targetInclusion i)
        have hInl :
            (pushoutMapOfUnderHom j (mappingCylinderProjectionFactorizationUnder (i := i))).comp
              (pushout.inl (TopCat.ofHom (mappingCylinderFactorizationIn i)) (TopCat.ofHom j)).hom =
            (pushout.inl (TopCat.ofHom i) (TopCat.ofHom j)).hom.comp (mappingCylinderProjection i) := by
          simpa [ContinuousMap.comp_assoc] using
            pushoutMapOfUnderHom_comp_inl j (mappingCylinderProjectionFactorizationUnder (i := i))
        calc
          ((pushoutMapOfUnderHom j (mappingCylinderProjectionFactorizationUnder (i := i))).comp
              (doubleMappingCylinderFactorizationPushoutCoprodMap (i := i) (j := j))) (Sum.inl a) =
            ((pushout.inl (TopCat.ofHom i) (TopCat.ofHom j)).hom.comp
              (mappingCylinderProjection i)) (mappingCylinderTargetInclusion i a) := by
                simpa [doubleMappingCylinderFactorizationPushoutCoprodMap, ContinuousMap.comp_apply]
                  using congrArg (fun g : C(i.mappingCylinder, _ ) ↦ g (mappingCylinderTargetInclusion i a))
                    hInl
          _ = doubleMappingCylinderPushoutCoprodMap i j (Sum.inl a) := by
                simp [doubleMappingCylinderPushoutCoprodMap, ContinuousMap.comp_apply, hproj]
    | inr b =>
        calc
          ((pushoutMapOfUnderHom j (mappingCylinderProjectionFactorizationUnder (i := i))).comp
              (doubleMappingCylinderFactorizationPushoutCoprodMap (i := i) (j := j))) (Sum.inr b) =
            (pushout.inr (TopCat.ofHom i) (TopCat.ofHom j)).hom b := by
              simpa [doubleMappingCylinderFactorizationPushoutCoprodMap, ContinuousMap.comp_apply]
                using congrArg (fun g : C(B, _ ) ↦ g b)
                  (pushoutMapOfUnderHom_comp_inr j (mappingCylinderProjectionFactorizationUnder (i := i)))
          _ = doubleMappingCylinderPushoutCoprodMap i j (Sum.inr b) := rfl
  have hcylinder :
      ((pushoutMapOfUnderHom j (mappingCylinderProjectionFactorizationUnder (i := i))).comp
          (doubleMappingCylinderFactorizationPushoutCylinderMap (i := i) (j := j))) =
        doubleMappingCylinderPushoutCylinderMap i j := by
    ext z
    rcases z with ⟨c, t⟩
    have hInl :
        (pushoutMapOfUnderHom j (mappingCylinderProjectionFactorizationUnder (i := i))).comp
          (pushout.inl (TopCat.ofHom (mappingCylinderFactorizationIn i)) (TopCat.ofHom j)).hom =
        (pushout.inl (TopCat.ofHom i) (TopCat.ofHom j)).hom.comp (mappingCylinderProjection i) := by
      simpa [ContinuousMap.comp_assoc] using
        pushoutMapOfUnderHom_comp_inl j (mappingCylinderProjectionFactorizationUnder (i := i))
    calc
      ((pushoutMapOfUnderHom j (mappingCylinderProjectionFactorizationUnder (i := i))).comp
          (doubleMappingCylinderFactorizationPushoutCylinderMap (i := i) (j := j))) (c, t) =
        ((pushout.inl (TopCat.ofHom i) (TopCat.ofHom j)).hom.comp
          (mappingCylinderProjection i) |>.comp (mappingCylinderCylinderInclusion i)) (c, t) := by
            simpa [doubleMappingCylinderFactorizationPushoutCylinderMap, ContinuousMap.comp_apply]
              using congrArg (fun g : C(i.mappingCylinder, _ ) ↦ g (mappingCylinderCylinderInclusion i (c, t)))
                hInl
      _ = doubleMappingCylinderPushoutCylinderMap i j (c, t) := by
            simp [doubleMappingCylinderPushoutCylinderMap, ContinuousMap.comp_apply,
              mappingCylinderProjection_comp_cylinderInclusion]
  apply pushout.hom_ext
  · simpa [TopCat.ofHom_comp] using
      congrArg TopCat.ofHom <|
        calc
          ((pushoutMapOfUnderHom j (mappingCylinderProjectionFactorizationUnder (i := i))).comp
              (doubleMappingCylinderToFactorizationPushout (i := i) (j := j))).comp
              (doubleMappingCylinderCoprodInclusion i j) =
            doubleMappingCylinderPushoutCoprodMap i j := by
              rw [ContinuousMap.comp_assoc,
                doubleMappingCylinderToFactorizationPushout_comp_coprodInclusion]
              exact hcoprod
          _ = (doubleMappingCylinderQuotientMap i j).hom.comp
                (doubleMappingCylinderCoprodInclusion i j) := by
              simpa [ContinuousMap.comp_assoc] using
                congrArg TopCat.Hom.hom
                  (doubleMappingCylinderCoprodInclusion_comp_quotientMap i j).symm
  · simpa [TopCat.ofHom_comp] using
      congrArg TopCat.ofHom <|
        calc
          ((pushoutMapOfUnderHom j (mappingCylinderProjectionFactorizationUnder (i := i))).comp
              (doubleMappingCylinderToFactorizationPushout (i := i) (j := j))).comp
              (doubleMappingCylinderCylinderInclusion i j) =
            doubleMappingCylinderPushoutCylinderMap i j := by
              rw [ContinuousMap.comp_assoc,
                doubleMappingCylinderToFactorizationPushout_comp_cylinderInclusion]
              exact hcylinder
          _ = (doubleMappingCylinderQuotientMap i j).hom.comp
                (doubleMappingCylinderCylinderInclusion i j) := by
              simpa [ContinuousMap.comp_assoc] using
                congrArg TopCat.Hom.hom
                  (doubleMappingCylinderCylinderInclusion_comp_quotientMap i j).symm

/-- Lemma 10.7.8. If `i : C(C, A)` is a cofibration and `j : C(C, B)` is any map, then the
quotient map `q : M(i, j) ⟶ A ∪_C B`, implemented as `doubleMappingCylinderQuotientMap i j`, is a
homotopy equivalence. On the proposition-level quotient-category side, this says that the
corresponding morphism in `TopCat` is a `CategoryTheory.HomRel.IsHomotopyEquivalence` for the
repository's canonical ordinary-homotopy relation `topCatHomotopyRel`. -/
instance doubleMappingCylinderQuotientMap.instIsHomotopyEquivalence
    {i : C(C, A)} {j : C(C, B)} (hi : IsCofibration.{u, u, u} i) :
    IsHomotopyEquivalence topCatHomotopyRel
      (doubleMappingCylinderQuotientMap i j) := by
  let _ :
      IsHomotopyEquivalence topCatHomotopyRel
        (TopCat.ofHom (pushoutMapOfUnderHom j (mappingCylinderProjectionFactorizationUnder (i := i)))) :=
    mappingCylinderProjectionFactorizationPushout_isHomotopyEquivalence (i := i) (j := j) hi
  -- Transport the pushed-out factorization equivalence across the comparison isomorphism.
  rw [← doubleMappingCylinderQuotientMap_viaFactorizationPushout (i := i) (j := j)]
  have hIsoPushout :
      IsIso ((CategoryTheory.Quotient.functor topCatHomotopyRel).map
        (TopCat.ofHom (pushoutMapOfUnderHom j (mappingCylinderProjectionFactorizationUnder (i := i))))) := by
    let _ :
        IsHomotopyEquivalence topCatHomotopyRel
          (TopCat.ofHom (pushoutMapOfUnderHom j (mappingCylinderProjectionFactorizationUnder (i := i)))) :=
      mappingCylinderProjectionFactorizationPushout_isHomotopyEquivalence (i := i) (j := j) hi
    infer_instance
  have hIsoComparison :
      IsIso ((CategoryTheory.Quotient.functor topCatHomotopyRel).map
        (doubleMappingCylinderFactorizationPushoutIso (i := i) (j := j)).hom) := by
    infer_instance
  have hIsoComp :
      IsIso (((CategoryTheory.Quotient.functor topCatHomotopyRel).map
          (doubleMappingCylinderFactorizationPushoutIso (i := i) (j := j)).hom) ≫
        ((CategoryTheory.Quotient.functor topCatHomotopyRel).map
          (TopCat.ofHom (pushoutMapOfUnderHom j (mappingCylinderProjectionFactorizationUnder (i := i)))))) := by
    exact IsIso.comp_isIso' hIsoComparison hIsoPushout
  let _ :
      IsIso ((CategoryTheory.Quotient.functor topCatHomotopyRel).map
        ((doubleMappingCylinderFactorizationPushoutIso (i := i) (j := j)).hom ≫
          TopCat.ofHom (pushoutMapOfUnderHom j (mappingCylinderProjectionFactorizationUnder (i := i))))) := by
    simpa [Functor.map_comp] using
      hIsoComp
  exact CategoryTheory.HomRel.IsHomotopyEquivalence.of_isIso_map (r := topCatHomotopyRel)

/-- Lemma 10.7.8. If `i : C(C, A)` is a cofibration and `j : C(C, B)` is any map, then the
quotient map `q : M(i, j) ⟶ A ∪_C B`, implemented as `doubleMappingCylinderQuotientMap i j`, is a
homotopy equivalence. In the repository's quotient-by-homotopy owner, this says that the
corresponding morphism in `TopCat` is an `IsHomotopyEquivalence` for `topCatHomotopyRel`. -/
theorem doubleMappingCylinderQuotientMap_isHomotopyEquivalence
    {i : C(C, A)} {j : C(C, B)} (hi : IsCofibration.{u, u, u} i) :
    IsHomotopyEquivalence topCatHomotopyRel
      (doubleMappingCylinderQuotientMap i j) := by
  exact doubleMappingCylinderQuotientMap.instIsHomotopyEquivalence hi

/-- Companion witness form of Lemma 10.7.8: the quotient map `doubleMappingCylinderQuotientMap i
j` is the forward map of a `ContinuousMap.HomotopyEquiv`. -/
theorem exists_homotopyEquiv_doubleMappingCylinderQuotientMap
    {i : C(C, A)} {j : C(C, B)} (hi : IsCofibration.{u, u, u} i) :
    ∃ e : M(i, j) ≃ₕ (pushout (TopCat.ofHom i) (TopCat.ofHom j) : TopCat),
      e.toFun = (doubleMappingCylinderQuotientMap i j).hom := by
  let _ : IsHomotopyEquivalence topCatHomotopyRel (doubleMappingCylinderQuotientMap i j) :=
    doubleMappingCylinderQuotientMap.instIsHomotopyEquivalence (i := i) (j := j) hi
  rcases
      (inferInstance : IsHomotopyEquivalence topCatHomotopyRel
        (doubleMappingCylinderQuotientMap i j)).exists_inverse with
    ⟨g, hgT, hgS⟩
  refine ⟨{
      toFun := (doubleMappingCylinderQuotientMap i j).hom
      invFun := g.hom
      left_inv := ?_
      right_inv := ?_
    }, rfl⟩
  · simpa [topCatHomotopyRel] using hgS
  · simpa [topCatHomotopyRel] using hgT

end ContinuousMap
