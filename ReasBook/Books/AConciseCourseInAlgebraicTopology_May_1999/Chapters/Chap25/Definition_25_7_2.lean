import Mathlib.CategoryTheory.CommSq
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap22.Definition_22_1_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap25.Definition_25_3_1

open CategoryTheory

universe u w

-- Semantic recall: the reduced suspension owner now exports the canonical bridge
-- `PointedCompactlyGenerated.reducedSuspensionFunctor`, so this file stays focused on the
-- source-facing morphism notion for prespectra.

namespace Prespectrum

/-- Definition 25.7.2: a map of prespectra is a sequence of based maps compatible with the
structure maps. -/
structure Hom (T U : Prespectrum.{u, w}) where
  /-- The degree-`n` component of the map of prespectra. -/
  app (n : ℕ) : T n ⟶ U n
  /-- The degree-`n` suspension square commutes. -/
  comm (n : ℕ) :
    CommSq
      (PointedCompactlyGenerated.reducedSuspensionFunctor.map (app n))
      (T.sigma n)
      (U.sigma n)
      (app (n + 1))

/-- A map of prespectra can be evaluated degreewise to recover its component based maps. -/
instance {T U : Prespectrum.{u, w}} :
    CoeFun (Hom T U) (fun _ ↦ ∀ n : ℕ, T n ⟶ U n) where
  coe f := f.app

/-- Evaluating a map of prespectra as a function returns its degreewise component map. -/
@[simp] theorem hom_coe_apply {T U : Prespectrum.{u, w}} (f : Hom T U) (n : ℕ) :
    f n = f.app n := rfl

/-- The defining compatibility of a prespectrum map is the source-facing suspension square. -/
@[simp] theorem comm_reducedSuspensionMap
    {T U : Prespectrum.{u, w}} (f : Hom T U) (n : ℕ) :
    PointedCompactlyGenerated.reducedSuspensionMap (f n) ≫ U.sigma n =
      T.sigma n ≫ f (n + 1) :=
  by
    simpa using (f.comm n).w

/-- Two maps of prespectra are equal when their degreewise component maps agree. -/
@[ext] theorem ext {T U : Prespectrum.{u, w}} {f g : Hom T U}
    (h : ∀ n : ℕ, f n = g n) : f = g := by
  cases f
  cases g
  simp only [Hom.mk.injEq]
  exact funext h

/-- Prespectra form a category with the source-facing morphisms of Definition 25.7.2. -/
instance : Category (Prespectrum.{u, w}) where
  Hom T U := Hom T U
  id T :=
    { app := fun n ↦ 𝟙 (T n)
      comm := by
        intro n
        refine ⟨?_⟩
        simp }
  comp := fun {T U V} f g ↦
    { app := fun n ↦ f.app n ≫ g.app n
      comm := by
        intro n
        refine ⟨?_⟩
        calc
          PointedCompactlyGenerated.reducedSuspensionFunctor.map (f.app n ≫ g.app n) ≫ V.sigma n =
              PointedCompactlyGenerated.reducedSuspensionFunctor.map (f.app n) ≫
                (PointedCompactlyGenerated.reducedSuspensionFunctor.map (g.app n) ≫ V.sigma n) := by
                  simp [Functor.map_comp, Category.assoc]
          _ = PointedCompactlyGenerated.reducedSuspensionFunctor.map (f.app n) ≫
                (U.sigma n ≫ g.app (n + 1)) := by
                  rw [(g.comm n).w]
          _ = (PointedCompactlyGenerated.reducedSuspensionFunctor.map (f.app n) ≫ U.sigma n) ≫
                g.app (n + 1) := by
                  rw [Category.assoc]
          _ = (T.sigma n ≫ f.app (n + 1)) ≫ g.app (n + 1) := by
                  simpa using
                    congrArg (fun k ↦ k ≫ g.app (n + 1)) (f.comm n).w
          _ = T.sigma n ≫ (f.app (n + 1) ≫ g.app (n + 1)) := by
                  rw [Category.assoc] }
  id_comp := by
    intro T U f
    ext n
    rfl
  comp_id := by
    intro T U f
    ext n
    rfl
  assoc := by
    intro T U V W f g h
    ext n
    rfl

/-- The map on the `k`th cofinal-tail stage of stable homotopy induced by a map of
prespectra. -/
noncomputable def stableHomotopyGroupTailMap
    {T U : Prespectrum.{u, w}} (f : T ⟶ U) (n : ℤ) (k : ℕ) :
    stableHomotopyGroupTailStage T n k ⟶ stableHomotopyGroupTailStage U n k :=
  let g := CategoryTheory.ConcreteCategory.hom
    (PointedCompactlyGenerated.Hom.hom
      (iteratedLoopMap k (f.app (stableHomotopyGroupTailStart n + k))))
  GrpCat.ofHom <|
    homotopyGroupMonoidHom
      g
      (show g (iteratedLoopPointedSpace k
            (T (stableHomotopyGroupTailStart n + k))).point =
          (iteratedLoopPointedSpace k
            (U (stableHomotopyGroupTailStart n + k))).point from
        PointedCompactlyGenerated.Hom.map_point
          (iteratedLoopMap k (f.app (stableHomotopyGroupTailStart n + k))))
      (stableHomotopyGroupTailOffset n)

/-- Degreewise maps induced by a map of prespectra commute with the stabilization maps. -/
theorem stableHomotopyGroupTailMap_naturality
    {T U : Prespectrum.{u, w}} (f : T ⟶ U) (n : ℤ) (k : ℕ) :
    stableHomotopyGroupTailStepMap T n k ≫ stableHomotopyGroupTailMap f n (k + 1) =
      stableHomotopyGroupTailMap f n k ≫ stableHomotopyGroupTailStepMap U n k := by
  sorry

/-- A map of prespectra induces a natural transformation between the cofinal-tail diagrams
defining stable homotopy groups. -/
noncomputable def stableHomotopyGroupTailNatTrans
    {T U : Prespectrum.{u, w}} (f : T ⟶ U) (n : ℤ) :
    stableHomotopyGroupTailDiagram T n ⟶ stableHomotopyGroupTailDiagram U n where
  app k := stableHomotopyGroupTailMap f n k
  naturality := by
    intro i j h
    sorry

/-- The map `π_n(T) ⟶ π_n(U)` induced by a map of prespectra `f : T ⟶ U`.  It is
obtained by descending the degreewise maps along the filtered colimits that define stable
homotopy groups. -/
noncomputable def stableHomotopyGroupMap
    {T U : Prespectrum.{u, w}} (f : T ⟶ U) (n : ℤ) :
    stableHomotopyGroup T n ⟶ stableHomotopyGroup U n :=
  (GrpCat.FilteredColimits.colimitCoconeIsColimit
      (stableHomotopyGroupTailDiagram T n)).desc
    { pt := stableHomotopyGroup U n
      ι :=
        { app := fun k ↦
            (stableHomotopyGroupTailNatTrans f n).app k ≫
              (GrpCat.FilteredColimits.colimitCocone
                (stableHomotopyGroupTailDiagram U n)).ι.app k
          naturality := by
            intro i j h
            sorry } }

/-- A map of prespectra is a stable equivalence when its induced map on every integer-graded
stable homotopy group is an isomorphism.  This is the weak-equivalence notion used in May's
construction of the stable category. -/
def IsStableEquivalence {T U : Prespectrum.{u, w}} (f : T ⟶ U) : Prop :=
  ∀ n : ℤ, IsIso (stableHomotopyGroupMap f n)

/-- The identity map of a prespectrum is the degreewise identity map. -/
@[simp] theorem id_app (T : Prespectrum.{u, w}) (n : ℕ) :
    (𝟙 T : T ⟶ T).app n = 𝟙 (T n) :=
  rfl

/-- Composition of prespectrum maps is computed degreewise. -/
@[simp] theorem comp_app
    {T U V : Prespectrum.{u, w}} (f : T ⟶ U) (g : U ⟶ V) (n : ℕ) :
    (f ≫ g).app n = f.app n ≫ g.app n :=
  rfl

end Prespectrum
