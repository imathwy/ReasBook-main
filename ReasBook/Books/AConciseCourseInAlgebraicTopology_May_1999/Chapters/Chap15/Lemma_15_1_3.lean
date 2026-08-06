import Mathlib.Algebra.Group.TypeTags.Hom
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.BasedHomotopyClassesPostcompose
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap02.Lemma_2_4_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Definition_9_6_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap14.Construction_14_1_3
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap14.Corollary_14_3_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap15.Definition_15_1_1

open CategoryTheory
open HomotopicalAlgebra
open scoped Topology Topology.Homotopy

noncomputable section

local notation "BasedSpace" => Under (⊤_ TopCat)
local notation "NBasedSpace" =>
  CategoryTheory.ObjectProperty.FullSubcategory
    (HomotopicalAlgebra.IsCofibrant : CategoryTheory.ObjectProperty BasedSpace)

-- Semantic recall via `lean_leansearch` surfaced only the canonical `π_ n` owner, while local
-- Chapter 11 precedent exposes suspension on homotopy groups only for its own sphere/suspension
-- owners. Definition 15.1.1 now exposes the canonical Hurewicz homomorphism
-- `hurewiczHomomorphism : π_ n(X) → H̃_n(X)` relative to the named Chapter 14.3.3 comparison
-- owner, so this file states Lemma 15.1.3 on that owner and keeps the explicit
-- comparison-compatible suspension helpers on the `basedSphere` surface.

/-- The additive homomorphism on positive-degree homotopy groups induced by a based map. -/
noncomputable def basedHomotopyGroupHom
    (n : ℕ) [Nonempty (Fin n)] {X Y : BasedSpace} (f : X ⟶ Y) :
    Additive (π_ n X.right (underTopBasepoint X)) →+
      Additive (π_ n Y.right (underTopBasepoint Y)) where
  toFun := fun a ↦
    Additive.ofMul
      ((fundamentalGroupFunctorMap_basepoint f) ▸
        homotopyGroupMap f.right.hom n (underTopBasepoint X) a.toMul)
  map_zero' := sorry
  map_add' := sorry

/-- The underlying multiplicative map of `basedHomotopyGroupHom` is the induced map on `π_ n`
with the canonical target-basepoint transport for the based map `f`. -/
theorem basedHomotopyGroupHom_apply
    (n : ℕ) [Nonempty (Fin n)] {X Y : BasedSpace} (f : X ⟶ Y)
    (a : Additive (π_ n X.right (underTopBasepoint X))) :
    (basedHomotopyGroupHom n f a).toMul =
      ((fundamentalGroupFunctorMap_basepoint f) ▸
        homotopyGroupMap f.right.hom n (underTopBasepoint X) a.toMul) := rfl

/-- The chosen Chapter 14.3.3 comparisons for `X` and `Y` are natural with respect to `f` when
they identify postcomposition on sphere classes with the induced map on `π_ n`. -/
def hurewiczComparisonNaturality
    (n : ℕ) [Nonempty (Fin n)] {X Y : BasedSpace}
    (comparisonX : HurewiczComparison n X)
    (comparisonY : HurewiczComparison n Y) (f : X ⟶ Y) : Prop :=
  ∀ a : Additive (π_ n X.right (underTopBasepoint X)),
    comparisonY.ofSphereClass
        (basedHomotopyClassesPostcomposeFun (basedSphere n) f
          (comparisonX.toSphereClass a.toMul)) =
      (basedHomotopyGroupHom n f a).toMul

/-- The reduced-homology suspension map on `Xn` coming from the chosen natural isomorphism of
Theorem 14.3.1. -/
noncomputable abbrev reducedHomologySuspensionMap
    [CategoryWithCofibrations BasedSpace]
    {π : Type} [AddCommGroup π] (H : PairHomologyTheory π)
    (S : ReducedSuspensionModel) (n : ℕ)
    (η : nBasedReducedHomologyFunctor H (n : ℤ) ≅
      S.suspension ⋙ nBasedReducedHomologyFunctor H ((n + 1 : ℤ)))
    (Xn : NBasedSpace) :
    basedReducedHomology H (n : ℤ) Xn.obj →+
      basedReducedHomology H ((n + 1 : ℤ)) (S.suspension.obj Xn).obj :=
  (((η.hom.app Xn).hom).toAddMonoidHom)

/-- Transport the actual sphere-case reduced-homology suspension map for the chosen model `S`
across explicit identifications of `basedSphere n` and `basedSphere (n + 1)` with a suspension
tower in `NBasedSpace`. -/
noncomputable abbrev basedSphereReducedHomologySuspensionMap
    [CategoryWithCofibrations BasedSpace]
    {π : Type} [AddCommGroup π] (H : PairHomologyTheory π)
    (S : ReducedSuspensionModel) (n : ℕ)
    (η : nBasedReducedHomologyFunctor H (n : ℤ) ≅
      S.suspension ⋙ nBasedReducedHomologyFunctor H ((n + 1 : ℤ)))
    (sphereModel : NBasedSpace)
    (sphereToBasedSphere : sphereModel.obj ≅ basedSphere n)
    (suspensionSphereToBasedSphere :
      (S.suspension.obj sphereModel).obj ≅ basedSphere (n + 1)) :
    basedReducedHomology H (n : ℤ) (basedSphere n) →+
      basedReducedHomology H ((n + 1 : ℤ)) (basedSphere (n + 1)) :=
  (basedHomologyReducedMap H ((n + 1 : ℤ)) suspensionSphereToBasedSphere.hom).comp
    ((reducedHomologySuspensionMap H S n η sphereModel).comp
      (basedHomologyReducedMap H (n : ℤ) sphereToBasedSphere.inv))

/-- Suspending the representative `f : basedSphere n ⟶ Xn.obj` along the chosen Chapter 14
comparison gives a representative `basedSphere (n + 1) ⟶ (S.suspension.obj Xn).obj`. -/
noncomputable abbrev basedSphereSuspensionRepresentative
    [CategoryWithCofibrations BasedSpace]
    (S : ReducedSuspensionModel) (n : ℕ) (Xn : NBasedSpace)
    (sphereModel : NBasedSpace)
    (sphereToBasedSphere : sphereModel.obj ≅ basedSphere n)
    (suspensionSphereToBasedSphere :
      (S.suspension.obj sphereModel).obj ≅ basedSphere (n + 1))
    (f : basedSphere n ⟶ Xn.obj) :
    basedSphere (n + 1) ⟶ (S.suspension.obj Xn).obj :=
  suspensionSphereToBasedSphere.inv ≫
    (S.suspension.map
      (CategoryTheory.ObjectProperty.homMk
        (sphereToBasedSphere.hom ≫ f) : sphereModel ⟶ Xn)).hom

/-- The explicit suspension formula on sphere representatives respects based homotopy. -/
theorem basedSphereSuspensionRepresentative_respects
    [CategoryWithCofibrations BasedSpace]
    (S : ReducedSuspensionModel) (n : ℕ) (Xn : NBasedSpace)
    (sphereModel : NBasedSpace)
    (sphereToBasedSphere : sphereModel.obj ≅ basedSphere n)
    (suspensionSphereToBasedSphere :
      (S.suspension.obj sphereModel).obj ≅ basedSphere (n + 1))
    {f g : basedSphere n ⟶ Xn.obj}
    (hfg : (basedHomotopySetoid (basedSphere n) Xn.obj).r f g) :
    (basedHomotopySetoid (basedSphere (n + 1)) (S.suspension.obj Xn).obj).r
      (basedSphereSuspensionRepresentative S n Xn sphereModel
        sphereToBasedSphere suspensionSphereToBasedSphere f)
      (basedSphereSuspensionRepresentative S n Xn sphereModel
        sphereToBasedSphere suspensionSphereToBasedSphere g) := sorry

/-- The sphere-class suspension map determined by explicit identifications of `basedSphere n` and
`basedSphere (n + 1)` with the chosen suspension tower of `S`. -/
noncomputable def basedSphereClassSuspensionMap
    [CategoryWithCofibrations BasedSpace]
    (S : ReducedSuspensionModel) (n : ℕ) (Xn : NBasedSpace)
    (sphereModel : NBasedSpace)
    (sphereToBasedSphere : sphereModel.obj ≅ basedSphere n)
    (suspensionSphereToBasedSphere :
      (S.suspension.obj sphereModel).obj ≅ basedSphere (n + 1)) :
    basedHomotopyClasses (basedSphere n) Xn.obj →
      basedHomotopyClasses (basedSphere (n + 1)) (S.suspension.obj Xn).obj :=
  Quotient.map
    (basedSphereSuspensionRepresentative S n Xn sphereModel
      sphereToBasedSphere suspensionSphereToBasedSphere)
    (fun _ _ hfg ↦
      basedSphereSuspensionRepresentative_respects S n Xn sphereModel
        sphereToBasedSphere suspensionSphereToBasedSphere hfg)

/-- A chosen suspension homomorphism on `π_ n(X)` is comparison-compatible when it matches the
explicit sphere-class suspension map determined by `S`. -/
structure HurewiczComparisonSuspensionMap
    [CategoryWithCofibrations BasedSpace]
    (n : ℕ) [Nonempty (Fin n)] (Xn : NBasedSpace)
    (S : ReducedSuspensionModel)
    (comparisonX : HurewiczComparison n Xn.obj)
    (comparisonSusp : HurewiczComparison (n + 1) (S.suspension.obj Xn).obj)
    (sphereModel : NBasedSpace)
    (sphereToBasedSphere : sphereModel.obj ≅ basedSphere n)
    (suspensionSphereToBasedSphere :
      (S.suspension.obj sphereModel).obj ≅ basedSphere (n + 1)) where
  /-- The chosen suspension homomorphism on `π_ n(X)`. -/
  hom :
    Additive (π_ n Xn.obj.right (underTopBasepoint Xn.obj)) →+
      Additive
        (π_ (n + 1) (S.suspension.obj Xn).obj.right
          (underTopBasepoint (S.suspension.obj Xn).obj))
  /-- The chosen homotopy-group suspension agrees with the explicit sphere-class suspension map
  under the fixed Chapter 14.3.3 comparisons. -/
  comparison_comm :
    ∀ a : Additive (π_ n Xn.obj.right (underTopBasepoint Xn.obj)),
      comparisonSusp.ofSphereClass
          (basedSphereClassSuspensionMap S n Xn sphereModel
            sphereToBasedSphere suspensionSphereToBasedSphere
            (comparisonX.toSphereClass a.toMul)) =
        (hom a).toMul

/-- Lemma 15.1.3 (1): for a chosen degree-`n` generator `i_n`, chosen Chapter 14.3.3
comparisons for `X` and `Y`, and an explicit compatibility hypothesis saying those comparisons
identify postcomposition on sphere classes with the induced map on `π_ n`, the Hurewicz
homomorphism is natural with respect to `f`. -/
theorem hurewiczHomomorphism_natural
    {π : Type} [AddCommGroup π] (H : PairHomologyTheory π)
    (n : ℕ) [Nonempty (Fin n)]
    {X Y : BasedSpace} (f : X ⟶ Y)
    [HasHurewiczComparison n X] [HasHurewiczComparison n Y]
    (hcomparison :
      hurewiczComparisonNaturality n (hurewiczComparison n X) (hurewiczComparison n Y) f)
    (i_n : SphereHomologyGenerator H n) :
    (basedHomologyReducedMap H (n : ℤ) f).comp
        (hurewiczHomomorphism H n X i_n) =
      (hurewiczHomomorphism H n Y i_n).comp
        (basedHomotopyGroupHom n f) := sorry

/-- Lemma 15.1.3 (2): for a chosen Chapter 14 suspension model `S`, chosen Chapter 14.3.3
comparisons in degrees `n` and `n + 1`, explicit sphere-model identifications of `basedSphere n`
and `basedSphere (n + 1)` with the suspension tower determined by `S`, a chosen
comparison-compatible suspension homomorphism on `π_ n`, an explicit suspension isomorphism `η`
from Theorem 14.3.1, and sphere generators related by the induced reduced-homology suspension
map, the Chapter 15 Hurewicz homomorphism commutes with suspension. -/
theorem hurewiczHomomorphism_suspension
    [CategoryWithCofibrations BasedSpace]
    {π : Type} [AddCommGroup π] (H : PairHomologyTheory π)
    (S : ReducedSuspensionModel) (n : ℕ) [Nonempty (Fin n)]
    (η : nBasedReducedHomologyFunctor H (n : ℤ) ≅
      S.suspension ⋙ nBasedReducedHomologyFunctor H ((n + 1 : ℤ)))
    (i_n : SphereHomologyGenerator H n)
    (i_succ : SphereHomologyGenerator H (n + 1))
    (Xn : NBasedSpace)
    [HasHurewiczComparison n Xn.obj]
    [HasHurewiczComparison (n + 1) (S.suspension.obj Xn).obj]
    (sphereModel : NBasedSpace)
    (sphereToBasedSphere : sphereModel.obj ≅ basedSphere n)
    (suspensionSphereToBasedSphere :
      (S.suspension.obj sphereModel).obj ≅ basedSphere (n + 1))
    (suspensionMap :
      HurewiczComparisonSuspensionMap n Xn S
        (hurewiczComparison n Xn.obj)
        (hurewiczComparison (n + 1) (S.suspension.obj Xn).obj)
        sphereModel sphereToBasedSphere suspensionSphereToBasedSphere)
    (hgeneratorSuspension :
      basedSphereReducedHomologySuspensionMap H S n η sphereModel
          sphereToBasedSphere suspensionSphereToBasedSphere i_n.toReducedHomology =
        i_succ.toReducedHomology) :
    (reducedHomologySuspensionMap H S n η Xn).comp
        (hurewiczHomomorphism H n Xn.obj i_n) =
      (hurewiczHomomorphism H (n + 1) (S.suspension.obj Xn).obj i_succ).comp
        suspensionMap.hom := sorry
