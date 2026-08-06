import Mathlib.Algebra.Group.TypeTags.Hom
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap05.Lemma_5_1_15
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap06.Definition_6_5_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.BasedHomotopyClassesPostcompose
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Definition_8_6_5
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Lemma_8_6_10
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap19.Definition_19_2_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap19.Definition_19_2_3
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap19.Theorem_19_2_5
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap22.Definition_22_2_5
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap22.OmegaPrespectrumReducedCohomology
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap22.Theorem_22_2_1.Representation

open CategoryTheory
open BasedHomotopyClasses
open HomotopicalAlgebra
open scoped HomotopyClasses Topology.Homotopy

noncomputable section

-- Semantic recall: `OmegaPrespectrumReducedCohomology` owns the source-facing represented
-- functor `q ↦ [X, R_q(T)]`. This file keeps that source-facing owner and packages its additive
-- enhancement through the Ω-prespectrum comparison with a double-loop bridge.

/- Theorem 22.2.6. Degreewise, the reduced cohomology functor attached to a prespectrum `T` is
represented by based homotopy classes into `omegaPrespectrumRepresentingBasedSpace T q`. -/
#check omegaPrespectrumReducedCohomology_obj

/-- In every nonnegative degree `q`, a prespectrum `T` represents the source-facing reduced
cohomology functor by the based homotopy classes `[X, T q]`. -/
theorem omegaPrespectrumReducedCohomology_nonnegative
    (T : Prespectrum) (q : ℕ) (X : BasedCWComplex) :
    (omegaPrespectrumReducedCohomology T (q : ℤ)).obj (Opposite.op X) =
      Ho*[X.obj, PointedCompactlyGenerated.toBasedSpace (T q)] := by
  rw [omegaPrespectrumReducedCohomology_obj]
  simp [omegaPrespectrumRepresentingBasedSpace]

/-- In degree `-(n + 1)`, a prespectrum `T` represents the source-facing reduced cohomology
functor by the based homotopy classes `[X, Ω^(n + 1) (T 0)]`. -/
theorem omegaPrespectrumReducedCohomology_negative
    (T : Prespectrum) (n : ℕ) (X : BasedCWComplex) :
    (omegaPrespectrumReducedCohomology T (-((n : ℤ) + 1))).obj (Opposite.op X) =
      Ho*[X.obj,
        iteratedLoopBasedSpace (n + 1)
          (PointedCompactlyGenerated.toBasedSpace (T 0))] := by
  rw [omegaPrespectrumReducedCohomology_obj]
  have hq : ¬ ((n : ℤ) ≤ -1) := by
    omega
  have hnatAbs : (-1 + - (n : ℤ)).natAbs = n + 1 := by
    omega
  simp [omegaPrespectrumRepresentingBasedSpace, hq, hnatAbs]

namespace BasedHomotopyClasses

/-- Precomposition with a based map acts multiplicatively on Chapter 8 double-loop homotopy
classes. -/
private noncomputable def doubleLoopHomotopyClassesPrecomposeHom
    (R : BasedSpace) {X Y : BasedSpace} (f : X ⟶ Y) :
    Ho*[Y, Ωᵇ (Ωᵇ R)] →* Ho*[X, Ωᵇ (Ωᵇ R)] where
  toFun := precomposeFun f
  map_one' := by
    simpa using precomposeFun_point f
  map_mul' := by
    intro a b
    refine Quotient.inductionOn₂ a b ?_
    intro g h
    rfl

private theorem doubleLoopHomotopyClassesPrecomposeHom_id
    (R X : BasedSpace) :
    doubleLoopHomotopyClassesPrecomposeHom R (𝟙 X) =
      MonoidHom.id (Ho*[X, Ωᵇ (Ωᵇ R)]) := by
  ext a
  exact congrArg (fun g ↦ g a) precompose_id

private theorem doubleLoopHomotopyClassesPrecomposeHom_comp
    (R : BasedSpace) {X Y Z : BasedSpace} (f : X ⟶ Y) (g : Y ⟶ Z) :
    doubleLoopHomotopyClassesPrecomposeHom R (f ≫ g) =
      (doubleLoopHomotopyClassesPrecomposeHom R f).comp
        (doubleLoopHomotopyClassesPrecomposeHom R g) := by
  ext a
  exact congrArg (fun h ↦ h a) (precompose_comp f g)

private theorem doubleLoopHomotopyClassesPrecomposeHom_toAdditive_comp
    (R : BasedSpace) {X Y Z : BasedSpace} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (doubleLoopHomotopyClassesPrecomposeHom R (f ≫ g)).toAdditive =
      ((doubleLoopHomotopyClassesPrecomposeHom R f).comp
        (doubleLoopHomotopyClassesPrecomposeHom R g)).toAdditive :=
  congrArg MonoidHom.toAdditive
    (doubleLoopHomotopyClassesPrecomposeHom_comp R f g)

/-- The contravariant `AddCommGrpCat`-valued double-loop homotopy-classes functor
`X ↦ Additive (Ho*[X, Ωᵇ (Ωᵇ R)])` on based spaces. -/
noncomputable def doubleLoopHomotopyClassesAdditiveFunctor
    (R : BasedSpace) : BasedSpaceᵒᵖ ⥤ AddCommGrpCat.{0} where
  obj X := AddCommGrpCat.of (Additive (Ho*[X.unop, Ωᵇ (Ωᵇ R)]))
  map f := AddCommGrpCat.ofHom <|
    (doubleLoopHomotopyClassesPrecomposeHom R f.unop).toAdditive
  map_id X := by
    simp [doubleLoopHomotopyClassesPrecomposeHom_id]
  map_comp f g := by
    simp [doubleLoopHomotopyClassesPrecomposeHom_toAdditive_comp]
    rfl

/-- Evaluating `doubleLoopHomotopyClassesAdditiveFunctor R` at `X` gives the additive group
`Additive (Ho*[X, Ωᵇ (Ωᵇ R)])`. -/
@[simp] theorem doubleLoopHomotopyClassesAdditiveFunctor_obj
    (R : BasedSpace) (X : BasedSpace) :
    (doubleLoopHomotopyClassesAdditiveFunctor R).obj (Opposite.op X) =
      AddCommGrpCat.of (Additive (Ho*[X, Ωᵇ (Ωᵇ R)])) :=
  rfl

/-- The double-loop homotopy-classes functor restricted to based CW complexes. -/
noncomputable abbrev doubleLoopHomotopyClassesAdditiveOnBasedCWComplexes
    (R : BasedSpace) : BasedCWComplexᵒᵖ ⥤ AddCommGrpCat.{0} :=
  basedCWComplexInclusion.op ⋙ doubleLoopHomotopyClassesAdditiveFunctor R

/-- Evaluating the based-CW restriction of `doubleLoopHomotopyClassesAdditiveFunctor R` at `X`
gives `Additive (Ho*[X, Ωᵇ (Ωᵇ R)])`. -/
@[simp] theorem doubleLoopHomotopyClassesAdditiveOnBasedCWComplexes_obj
    (R : BasedSpace) (X : BasedCWComplex) :
    (doubleLoopHomotopyClassesAdditiveOnBasedCWComplexes R).obj (Opposite.op X) =
      AddCommGrpCat.of (Additive (Ho*[X.obj, Ωᵇ (Ωᵇ R)])) :=
  rfl

end BasedHomotopyClasses

/-- The `AddCommGrpCat`-valued form of the represented reduced cohomology functor of a
prespectrum, obtained from the double-loop group structure on the representing space in degree
`q + 2`. For an Ω-prespectrum this is naturally identified with the source-facing represented
functor `X ↦ Ho*[X, omegaPrespectrumRepresentingBasedSpace T q]`. -/
noncomputable abbrev omegaPrespectrumReducedCohomologyAdditive
    (T : Prespectrum) :
    ℤ → BasedCWComplexᵒᵖ ⥤ AddCommGrpCat.{0} :=
  fun q ↦ doubleLoopHomotopyClassesAdditiveOnBasedCWComplexes
    (omegaPrespectrumRepresentingBasedSpace T (q + 2))

/-- Evaluating the additive reduced cohomology functor at `X` gives the double-loop homotopy-class
group into the representing space in degree `q + 2`. -/
@[simp] theorem omegaPrespectrumReducedCohomologyAdditive_obj
    (T : Prespectrum) (q : ℤ) (X : BasedCWComplex) :
    (omegaPrespectrumReducedCohomologyAdditive T q).obj (Opposite.op X) =
      AddCommGrpCat.of
        (Additive
          (Ho*[X.obj, Ωᵇ (Ωᵇ (omegaPrespectrumRepresentingBasedSpace T (q + 2)))])) :=
  rfl

private theorem int_toNat_add_one (q : ℤ) (hq : 0 ≤ q) :
    Int.toNat (q + 1) = Int.toNat q + 1 := by
  omega

private theorem int_toNat_add_two (q : ℤ) (hq : 0 ≤ q) :
    Int.toNat (q + 2) = Int.toNat q + 2 := by
  omega

/-- Helper for Theorem 22.2.6: forgetting the pointed compactly generated loop owner recovers the
ordinary based loop-space owner by the canonical forgetful based map. This keeps the later
Ω-prespectrum comparison maps in the source-facing `BasedSpace` spelling without forcing a false
owner equality. -/
private theorem PointedCompactlyGenerated.toBasedSpaceLoopComparison_w
    (X : PointedCompactlyGenerated) :
    (PointedCompactlyGenerated.toBasedSpace (Ω X)).hom ≫
        TopCat.ofHom
          { toFun := fun χ : (Ω X).toCompactlyGenerated ↦
              (show Path X.point X.point from χ)
            continuous_toFun := by
              -- Forgetting the compactly generated loop topology to the raw path topology is the
              -- identity map `k(Path x x) → Path x x`.
              exact continuous_id_compactlyGenerated
                (X := Path X.point X.point) (t := inferInstance) } =
      (Ωᵇ (PointedCompactlyGenerated.toBasedSpace X)).hom := by
  -- Both based maps from the terminal object select the constant loop at `X.point`.
  ext x
  rfl

/-- Helper for Theorem 22.2.6: the compactly generated loop owner maps canonically to the raw
based-space loop owner by the identity function on loops. -/
private noncomputable def PointedCompactlyGenerated.toBasedSpaceLoopComparison
    (X : PointedCompactlyGenerated) :
    PointedCompactlyGenerated.toBasedSpace (Ω X) ⟶
      Ωᵇ (PointedCompactlyGenerated.toBasedSpace X) :=
  Under.homMk
    (TopCat.ofHom
      { toFun := fun χ : (Ω X).toCompactlyGenerated ↦
          (show Path X.point X.point from χ)
        continuous_toFun := by
          -- The comparison only forgets the compactly generated replacement on the loop carrier.
          exact continuous_id_compactlyGenerated
            (X := Path X.point X.point) (t := inferInstance) })
    (PointedCompactlyGenerated.toBasedSpaceLoopComparison_w X)

/-- Helper for Theorem 22.2.6: the loop-owner comparison is pointwise the identity on loops. -/
@[simp] private theorem PointedCompactlyGenerated.toBasedSpaceLoopComparison_hom_apply
    (X : PointedCompactlyGenerated) (χ : (Ω X).toCompactlyGenerated) :
    (PointedCompactlyGenerated.toBasedSpaceLoopComparison X).right.hom χ =
      (show Path X.point X.point from χ) :=
  rfl

/-- Helper for Theorem 22.2.6: shifting the iterated loop count by one pulls out a single loop
functor. -/
private theorem iteratedLoopBasedSpace_add_one (n : ℕ) (X : BasedSpace) :
    iteratedLoopBasedSpace (n + 1) X =
      Ωᵇ (iteratedLoopBasedSpace n X) := by
  -- Split off the first loop from the iterate so the target is the literal successor normal
  -- form of `Nat.iterate`.
  simp [iteratedLoopBasedSpace, Function.iterate_succ_apply']

private theorem iteratedLoopBasedSpace_comm_one (n : ℕ) (X : BasedSpace) :
    iteratedLoopBasedSpace n (Ωᵇ X) =
      Ωᵇ (iteratedLoopBasedSpace n X) := by
  induction n with
  | zero =>
      -- Zero iterates leave the single outer loop untouched.
      rfl
  | succ n ih =>
      -- Peel off one loop, commute the remaining iterate inductively, and then repackage the
      -- result as the shifted iterate on `X`.
      calc
        iteratedLoopBasedSpace (n + 1) (Ωᵇ X) =
            Ωᵇ (iteratedLoopBasedSpace n (Ωᵇ X)) :=
          iteratedLoopBasedSpace_add_one n (Ωᵇ X)
        _ = Ωᵇ (Ωᵇ (iteratedLoopBasedSpace n X)) := by
          rw [ih]
        _ = Ωᵇ (iteratedLoopBasedSpace (n + 1) X) := by
          rw [iteratedLoopBasedSpace_add_one]

private theorem iteratedLoopBasedSpace_comm_two (n : ℕ) (X : BasedSpace) :
    iteratedLoopBasedSpace n (Ωᵇ (Ωᵇ X)) =
      Ωᵇ (Ωᵇ (iteratedLoopBasedSpace n X)) := by
  -- Commute the outer loop once past the iterate, then commute the inner loop past the iterate.
  calc
    iteratedLoopBasedSpace n (Ωᵇ (Ωᵇ X)) = Ωᵇ (iteratedLoopBasedSpace n (Ωᵇ X)) :=
      iteratedLoopBasedSpace_comm_one n (Ωᵇ X)
    _ = Ωᵇ (Ωᵇ (iteratedLoopBasedSpace n X)) := by
      rw [iteratedLoopBasedSpace_comm_one n X]

private theorem iteratedLoopBasedSpace_add_two (n : ℕ) (X : BasedSpace) :
    iteratedLoopBasedSpace (n + 2) X =
      Ωᵇ (Ωᵇ (iteratedLoopBasedSpace n X)) := by
  calc
    iteratedLoopBasedSpace (n + 2) X = iteratedLoopBasedSpace n (Ωᵇ (Ωᵇ X)) := by
      simp [iteratedLoopBasedSpace, Function.iterate_add_apply]
    _ = Ωᵇ (Ωᵇ (iteratedLoopBasedSpace n X)) :=
      iteratedLoopBasedSpace_comm_two n X

/-- Helper for Theorem 22.2.6: the two-step loop reindexing is the composite of the two one-step
reindexings. -/
private theorem iteratedLoopBasedSpace_add_two_via_add_one (n : ℕ) (X : BasedSpace) :
    iteratedLoopBasedSpace_add_two n X =
      (iteratedLoopBasedSpace_add_one (n + 1) X).trans
        (congrArg (fun Y ↦ Ωᵇ Y) (iteratedLoopBasedSpace_add_one n X)) := by
  -- Both sides are the canonical equality obtained by splitting off two loop functors.
  simp [iteratedLoopBasedSpace_add_one, iteratedLoopBasedSpace,
    Function.iterate_add_apply]

/-- The one-step Ω-prespectrum comparison from the degree-`q` representing space to the loop of
the degree-`q + 1` representing space. This packages the case split once so later proofs can
work with a stable shift interface instead of repeatedly unfolding
`omegaPrespectrumRepresentingBasedSpace`. -/
noncomputable def omegaPrespectrumShiftComparisonMap
    (T : Prespectrum) (q : ℤ) :
    omegaPrespectrumRepresentingBasedSpace T q ⟶
      Ωᵇ (omegaPrespectrumRepresentingBasedSpace T (q + 1)) := by
  by_cases hq : 0 ≤ q
  · have hq1 : 0 ≤ q + 1 := by
      omega
    have hdom :
        omegaPrespectrumRepresentingBasedSpace T q =
          PointedCompactlyGenerated.toBasedSpace (T (Int.toNat q)) := by
      simp [omegaPrespectrumRepresentingBasedSpace, hq]
    have hcod :
        Ωᵇ (PointedCompactlyGenerated.toBasedSpace (T (Int.toNat q + 1))) =
          Ωᵇ (omegaPrespectrumRepresentingBasedSpace T (q + 1)) := by
      simp [omegaPrespectrumRepresentingBasedSpace, hq1, int_toNat_add_one q hq]
    -- Route correction: the nonnegative shift is the adjoint structure map followed by the
    -- loop-owner comparison, not an owner equality.
    -- Normalize the codomain spelling once by an explicit equality transport.
    exact
      (eqToHom hdom ≫
        (PointedCompactlyGenerated.toBasedSpaceMap
          (adjointStructureMap T (Int.toNat q))) ≫
        PointedCompactlyGenerated.toBasedSpaceLoopComparison (T (Int.toNat q + 1))) ≫
          eqToHom hcod
  · by_cases hq1 : q = -1
    · -- At `q = -1`, both representing spaces are already one loop of `T 0`.
      simpa [omegaPrespectrumRepresentingBasedSpace, hq, hq1, iteratedLoopBasedSpace] using
        (𝟙 (Ωᵇ (PointedCompactlyGenerated.toBasedSpace (T 0))))
    · have hq0 : ¬ 0 ≤ q + 1 := by
        omega
      have hnatAbs : q.natAbs = (q + 1).natAbs + 1 := by
        omega
      have hloops :
          iteratedLoopBasedSpace q.natAbs
              (PointedCompactlyGenerated.toBasedSpace (T 0)) =
            Ωᵇ
              (iteratedLoopBasedSpace (q + 1).natAbs
                (PointedCompactlyGenerated.toBasedSpace (T 0))) := by
        -- In the remaining negative degrees, the shift is the tautological loop reindexing.
        simpa [hnatAbs] using
          iteratedLoopBasedSpace_add_one
            (q + 1).natAbs (PointedCompactlyGenerated.toBasedSpace (T 0))
      simpa [omegaPrespectrumRepresentingBasedSpace, hq, hq0] using
        (eqToHom hloops)

/-- Helper for Theorem 22.2.6: looping the identity based map is again the identity. -/
private theorem loopBasedMap_id (X : BasedSpace) :
    loopBasedMap (𝟙 X) = 𝟙 (Ωᵇ X) := by
  -- Compare both based maps pointwise on loops.
  ext χ t
  rfl

/-- Helper for Theorem 22.2.6: looping an equality transport gives the corresponding equality
transport on loop spaces. -/
private theorem loopBasedMap_eqToHom {X Y : BasedSpace} (h : X = Y) :
    loopBasedMap (eqToHom h) = eqToHom (congrArg (fun Z ↦ Ωᵇ Z) h) := by
  -- Reduce to the reflexive case so both sides are literally the identity.
  subst h
  simp [loopBasedMap_id]

/-- The Ω-prespectrum comparison map from the degree-`q` representing space to the double loop of
the degree-`q + 2` representing space. In nonnegative degrees this is the double iterate of the
adjoint structure maps, while in sufficiently negative degrees it is the tautological loop-space
identification. -/
noncomputable def omegaPrespectrumReducedCohomologyAdditiveComparisonMap
    (T : Prespectrum) (q : ℤ) :
    omegaPrespectrumRepresentingBasedSpace T q ⟶
      Ωᵇ (Ωᵇ (omegaPrespectrumRepresentingBasedSpace T (q + 2))) :=
  -- Route correction: use the normalized composite of successive one-step shifts once, rather
  -- than re-entering the degree-by-degree case split at every downstream use.
  (omegaPrespectrumShiftComparisonMap T q ≫
      loopBasedMap (omegaPrespectrumShiftComparisonMap T (q + 1))) ≫
    eqToHom
      (congrArg
        (fun n : ℤ ↦ Ωᵇ (Ωᵇ (omegaPrespectrumRepresentingBasedSpace T n)))
        (by omega : q + 1 + 1 = q + 2))

/-- Helper for Theorem 22.2.6: the successive one-step shifts land in degree `q + 1 + 1`, so the
normalized composite rewrites that codomain once to the target's degree-`q + 2` spelling. -/
noncomputable def omegaPrespectrumReducedCohomologyAdditiveComparisonNormalized
    (T : Prespectrum) (q : ℤ) :
    omegaPrespectrumRepresentingBasedSpace T q ⟶
      Ωᵇ (Ωᵇ (omegaPrespectrumRepresentingBasedSpace T (q + 2))) :=
  (omegaPrespectrumShiftComparisonMap T q ≫
      loopBasedMap (omegaPrespectrumShiftComparisonMap T (q + 1))) ≫
    eqToHom
      (congrArg
        (fun n : ℤ ↦ Ωᵇ (Ωᵇ (omegaPrespectrumRepresentingBasedSpace T n)))
        (by omega : q + 1 + 1 = q + 2))

/-- Helper for Theorem 22.2.6: in nonnegative degrees, the two-step additive comparison is
already the composite of the successive one-step shifts. -/
private theorem
    omegaPrespectrumReducedCohomologyAdditiveComparisonMap_factor_nonnegative
    (T : Prespectrum) (q : ℤ) (hq : 0 ≤ q) :
    omegaPrespectrumReducedCohomologyAdditiveComparisonMap T q =
      omegaPrespectrumReducedCohomologyAdditiveComparisonNormalized T q := by
  -- The comparison map is now defined by this normalized composite in every degree.
  rfl

/-- Helper for Theorem 22.2.6: at degree `-1`, the two-step additive comparison is the loop of
the degree-`0` shift map because the first shift is the identity. -/
private theorem omegaPrespectrumReducedCohomologyAdditiveComparisonMap_factor_negOne
    (T : Prespectrum) :
    omegaPrespectrumReducedCohomologyAdditiveComparisonMap T (-1) =
      omegaPrespectrumReducedCohomologyAdditiveComparisonNormalized T (-1) := by
  -- The normalized composite is the definition, so the degree `-1` specialization is reflexive.
  rfl

/-- Helper for Theorem 22.2.6: at degree `-2`, the two-step additive comparison is the first
negative shift followed by the loop of the identity shift at degree `-1`. -/
private theorem omegaPrespectrumReducedCohomologyAdditiveComparisonMap_factor_negTwo
    (T : Prespectrum) :
    omegaPrespectrumReducedCohomologyAdditiveComparisonMap T (-2) =
      omegaPrespectrumReducedCohomologyAdditiveComparisonNormalized T (-2) := by
  -- The normalized composite is the definition, so the degree `-2` specialization is reflexive.
  rfl

/-- Helper for Theorem 22.2.6: in degrees `q ≤ -3`, the two-step additive comparison is the
composite of the successive one-step shifts. -/
private theorem omegaPrespectrumReducedCohomologyAdditiveComparisonMap_factor_negTail
    (T : Prespectrum) {q : ℤ} (hq : q ≤ -3) :
    omegaPrespectrumReducedCohomologyAdditiveComparisonMap T q =
      omegaPrespectrumReducedCohomologyAdditiveComparisonNormalized T q := by
  -- The normalized composite is the definition, so the negative-tail specialization is reflexive.
  rfl

/-- Helper for Theorem 22.2.6: postcomposition by a composite factors as the composite of the
successive postcomposition maps on based homotopy classes. -/
private theorem basedHomotopyClassesPostcomposeFun_comp
    (X : BasedSpace) {A B C : BasedSpace} (u : A ⟶ B) (v : B ⟶ C) :
    basedHomotopyClassesPostcomposeFun X (u ≫ v) =
      basedHomotopyClassesPostcomposeFun X v ∘ basedHomotopyClassesPostcomposeFun X u := by
  -- Compare both functions on representatives: both sides send `[f]` to `[f ≫ u ≫ v]`.
  funext a
  refine Quotient.inductionOn a ?_
  intro f
  rfl

/-- Helper for Theorem 22.2.6: postcomposition by the identity based map is the identity on
based homotopy classes. -/
private theorem basedHomotopyClassesPostcomposeFun_id
    (X A : BasedSpace) :
    basedHomotopyClassesPostcomposeFun X (𝟙 A) = id := by
  -- Compare both functions on representatives: both sides keep the class of `f` unchanged.
  funext a
  refine Quotient.inductionOn a ?_
  intro f
  rfl

/-- Helper for Theorem 22.2.6: postcomposition by an equality transport is bijective on based
homotopy classes. -/
private theorem basedHomotopyClassesPostcomposeFun_bijective_of_eqToHom
    (X A B : BasedSpace) (h : A = B) :
    Function.Bijective (basedHomotopyClassesPostcomposeFun X (eqToHom h)) := by
  -- Equality transports are invertible; after substituting the equality, this is just the
  -- identity action on based homotopy classes.
  subst h
  simpa [basedHomotopyClassesPostcomposeFun_id] using
    (Function.bijective_id : Function.Bijective (id : Ho*[X, A] → Ho*[X, A]))

/-- Helper for Theorem 22.2.6: the quotient relation generated by based homotopies already
collapses to a single based homotopy. -/
private theorem basedHomotopyRel_of_setoid
    {A B : BasedSpace} {u v : A ⟶ B}
    (h : (basedHomotopySetoid A B).r u v) :
    basedHomotopyRel u v := by
  -- Re-run the equivalence-closure induction because based homotopy is already an equivalence
  -- relation on based maps.
  rw [basedHomotopySetoid_iff] at h
  induction h with
  | rel _ _ huv =>
      exact huv
  | refl u =>
      exact ContinuousMap.HomotopicRel.refl u.right.hom
  | symm _ _ _ huv =>
      exact ContinuousMap.HomotopicRel.symm huv
  | trans _ _ _ _ _ huv hvw =>
      exact ContinuousMap.HomotopicRel.trans huv hvw

/-- Helper for Theorem 22.2.6: homotopic maps under the basepoint induce the same
postcomposition map on based homotopy classes. This isolates the representative-level
homotopy-under transport needed by the source-facing `Ho*` owner. -/
private theorem postcomposeEq_ofHomotopicUnder
    (X : BasedSpace) {Y Z : BasedSpace} {u v : Y ⟶ Z} (h : HomotopicUnder u v) :
    basedHomotopyClassesPostcompose X u = basedHomotopyClassesPostcompose X v := by
  -- Compare the two induced maps on a representative `k : X ⟶ Y`, then descend the
  -- precomposed homotopy-under witness to the quotient defining `Ho*[X, Z]`.
  ext a
  refine Quotient.inductionOn a ?_
  intro k
  apply Quotient.sound
  change (basedHomotopySetoid X Z).r (k ≫ u) (k ≫ v)
  rw [basedHomotopySetoid_iff]
  obtain ⟨H⟩ := h
  refine Relation.EqvGen.rel _ _ ?_
  refine ⟨{ toHomotopy := H.toHomotopy.compContinuousMap k.right.hom, prop' := ?_ }⟩
  intro t x hx
  rcases Set.mem_singleton_iff.mp hx with rfl
  have hstage :
      H.toHomotopy.curry t (underTopBasepoint Y) = underTopBasepoint Z := by
    have hw :=
      ContinuousMap.congr_fun (UnderHomotopy.w H t)
        (TopCat.terminalIsoPUnit.inv PUnit.unit)
    simpa [underTopBasepoint] using hw
  calc
    (H.toHomotopy.compContinuousMap k.right.hom) (t, underTopBasepoint X) =
        H.toHomotopy.curry t (k.right.hom (underTopBasepoint X)) := rfl
    _ = H.toHomotopy.curry t (underTopBasepoint Y) := by
      rw [fundamentalGroupFunctorMap_basepoint k]
    _ = underTopBasepoint Z := hstage
    _ = (k ≫ u).right.hom (underTopBasepoint X) := by
      simp [fundamentalGroupFunctorMap_basepoint]

/-- Helper for Theorem 22.2.6: a homotopy through maps under the basepoint is exactly a based
homotopy relative to the chosen singleton basepoint. This normalizes the local source-facing
`Ho*` quotient to the Chapter 6 `HomotopicUnder` owner before comparing with model-category
homotopy owners. -/
private theorem basedHomotopyRel_iff_homotopicUnder
    {X Y : BasedSpace} {f g : X ⟶ Y} :
    basedHomotopyRel f g ↔ HomotopicUnder f g := by
  constructor
  · -- Reuse the established Chapter 8 bridge from relative based homotopies to under-homotopies.
    rintro ⟨H⟩
    refine ⟨{ toHomotopy := H.toHomotopy, prop' := ?_ }⟩
    intro t
    ext x
    have hx : TopCat.terminalIsoPUnit.hom x = PUnit.unit := by
      cases TopCat.terminalIsoPUnit.hom x
      rfl
    have hstage :
        H (t, underTopBasepoint X) = underTopBasepoint Y := by
      calc
        H (t, underTopBasepoint X) = f.right.hom (underTopBasepoint X) := by
          exact H.eq_fst t (by simp [basedBasepointSet])
        _ = underTopBasepoint Y := by
          simpa using fundamentalGroupFunctorMap_basepoint f
    calc
      (H.toHomotopy.curry t).comp X.hom.hom x = H (t, X.hom x) := rfl
      _ = H (t, underTopBasepoint X) := by
        rw [show X.hom x = underTopBasepoint X by
          change X.hom x = X.hom (TopCat.terminalIsoPUnit.inv PUnit.unit)
          rw [← hx]
          simp]
      _ = underTopBasepoint Y := hstage
      _ = Y.hom x := by
        change Y.hom (TopCat.terminalIsoPUnit.inv PUnit.unit) = Y.hom x
        rw [← hx]
        simp
  · intro h
    rcases h with ⟨H⟩
    refine ⟨{ toHomotopy := H.toHomotopy, prop' := ?_ }⟩
    intro t x hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    -- Each stage of an under-homotopy still sends the chosen basepoint of `X` to that of `Y`.
    have hstage :
        H.toHomotopy.curry t (underTopBasepoint X) = underTopBasepoint Y := by
      have hw :=
        ContinuousMap.congr_fun (UnderHomotopy.w H t)
          (TopCat.terminalIsoPUnit.inv PUnit.unit)
      simpa [underTopBasepoint] using hw
    simpa using hstage

/-- Helper for Theorem 22.2.6: a based homotopy equivalence induces a bijection on
`Ho*[X, -]` by postcomposition. This records the source-facing transport route independently of
the later weak-equivalence-to-homotopy-equivalence bridge. -/
private theorem basedHomotopyClassesPostcomposeFun_bijective_of_homotopyEquivalence
    (X : BasedSpace) {Y Z : BasedSpace} (g : Y ⟶ Z) [hg : IsCofiberHomotopyEquivalence g] :
    Function.Bijective (basedHomotopyClassesPostcomposeFun X g) := by
  -- Route correction: first solve the source-facing postcomposition algebra for genuine based
  -- homotopy equivalences. The later weak-equivalence lemmas only need to supply this input.
  rw [isCofiberHomotopyEquivalence_iff] at hg
  rcases hg with ⟨h, hgh, hhg⟩
  have hLeft :
      Function.LeftInverse
        (basedHomotopyClassesPostcomposeFun X h)
        (basedHomotopyClassesPostcomposeFun X g) := by
    intro a
    have hcomp :
        basedHomotopyClassesPostcomposeFun X h (basedHomotopyClassesPostcomposeFun X g a) =
          basedHomotopyClassesPostcomposeFun X (g ≫ h) a := by
      -- Normalize the composite on the chosen class `a` to postcomposition by `g ≫ h`.
      simpa [Function.comp] using
        congrArg (fun k : Ho*[X, Y] → Ho*[X, Y] ↦ k a)
          (basedHomotopyClassesPostcomposeFun_comp X g h).symm
    have hId :
        basedHomotopyClassesPostcomposeFun X (g ≫ h) = id := by
      -- Collapse the normalized composite to the identity using the chosen homotopy-under
      -- inverse relation.
      exact congrArg Pointed.Hom.toFun <| calc
        basedHomotopyClassesPostcompose X (g ≫ h) =
            basedHomotopyClassesPostcompose X (𝟙 Y) :=
          postcomposeEq_ofHomotopicUnder X hhg
        _ = 𝟙 (Ho*[X, Y]) :=
          Pointed.Hom.ext (basedHomotopyClassesPostcomposeFun_id X Y)
    calc
      basedHomotopyClassesPostcomposeFun X h (basedHomotopyClassesPostcomposeFun X g a) =
          basedHomotopyClassesPostcomposeFun X (g ≫ h) a := hcomp
      _ = a := congrArg (fun k : Ho*[X, Y] → Ho*[X, Y] ↦ k a) hId
  have hRight :
      Function.RightInverse
        (basedHomotopyClassesPostcomposeFun X h)
        (basedHomotopyClassesPostcomposeFun X g) := by
    intro a
    have hcomp :
        basedHomotopyClassesPostcomposeFun X g (basedHomotopyClassesPostcomposeFun X h a) =
          basedHomotopyClassesPostcomposeFun X (h ≫ g) a := by
      -- Normalize the opposite composite on the chosen class `a` to postcomposition by `h ≫ g`.
      simpa [Function.comp] using
        congrArg (fun k : Ho*[X, Z] → Ho*[X, Z] ↦ k a)
          (basedHomotopyClassesPostcomposeFun_comp X h g).symm
    have hId :
        basedHomotopyClassesPostcomposeFun X (h ≫ g) = id := by
      -- The second homotopy-under inverse relation collapses the normalized opposite composite.
      exact congrArg Pointed.Hom.toFun <| calc
        basedHomotopyClassesPostcompose X (h ≫ g) =
            basedHomotopyClassesPostcompose X (𝟙 Z) :=
          postcomposeEq_ofHomotopicUnder X hgh
        _ = 𝟙 (Ho*[X, Z]) :=
          Pointed.Hom.ext (basedHomotopyClassesPostcomposeFun_id X Z)
    calc
      basedHomotopyClassesPostcomposeFun X g (basedHomotopyClassesPostcomposeFun X h a) =
          basedHomotopyClassesPostcomposeFun X (h ≫ g) a := hcomp
      _ = a := congrArg (fun k : Ho*[X, Z] → Ho*[X, Z] ↦ k a) hId
  exact ⟨hLeft.injective, hRight.surjective⟩

/-- Helper for Theorem 22.2.6: homotopic maps under the basepoint induce the same
precomposition map on based homotopy classes. -/
private theorem basedHomotopyClassesPrecompose_eq_of_homotopicUnder
    (Z : BasedSpace) {A B : BasedSpace} {u v : A ⟶ B} (h : HomotopicUnder u v) :
    (BasedHomotopyClasses.precompose u : Ho*[B, Z] ⟶ Ho*[A, Z]) =
      BasedHomotopyClasses.precompose v := by
  -- Fix the target and source of the pointed maps explicitly so the quotient induction below
  -- works in the expected homotopy-class object.
  change (BasedHomotopyClasses.precompose u : Ho*[B, Z] ⟶ Ho*[A, Z]) =
      (show Ho*[B, Z] ⟶ Ho*[A, Z] from BasedHomotopyClasses.precompose v)
  ext a
  refine Quotient.inductionOn a ?_
  intro k
  -- Compare representatives by postcomposing the chosen under-homotopy with `k`.
  apply Quotient.sound
  change (basedHomotopySetoid A Z).r (u ≫ k) (v ≫ k)
  rw [basedHomotopySetoid_iff]
  obtain ⟨H⟩ := h
  refine Relation.EqvGen.rel _ _ ?_
  refine ⟨{ toHomotopy :=
      (ContinuousMap.Homotopy.refl k.right.hom).comp H.toHomotopy, prop' := ?_ }⟩
  intro t z hz
  rcases Set.mem_singleton_iff.mp hz with rfl
  have hstage : H.toHomotopy.curry t (underTopBasepoint A) = underTopBasepoint B := by
    have hw :=
      ContinuousMap.congr_fun (UnderHomotopy.w H t) (TopCat.terminalIsoPUnit.inv PUnit.unit)
    simpa [underTopBasepoint] using hw
  -- Each stage of the postcomposed homotopy still fixes the chosen basepoint of `A`.
  calc
    ((ContinuousMap.Homotopy.refl k.right.hom).comp H.toHomotopy) (t, underTopBasepoint A) =
        k.right.hom (H.toHomotopy.curry t (underTopBasepoint A)) := rfl
    _ = k.right.hom (underTopBasepoint B) := by
      rw [hstage]
    _ = k.right.hom (u.right.hom (underTopBasepoint A)) := by
      rw [fundamentalGroupFunctorMap_basepoint u]
    _ = (u ≫ k).right.hom (underTopBasepoint A) := rfl

/-- Helper for Theorem 22.2.6: precomposition by a based homotopy equivalence is bijective on
based homotopy classes. -/
private theorem basedHomotopyClassesPrecomposeFun_bijective_of_homotopyEquivalence
    {X Y Z : BasedSpace} (f : X ⟶ Y) [hf : IsCofiberHomotopyEquivalence f] :
    Function.Bijective (BasedHomotopyClasses.precomposeFun f : Ho*[Y, Z] → Ho*[X, Z]) := by
  rw [isCofiberHomotopyEquivalence_iff] at hf
  rcases hf with ⟨g, hgf, hfg⟩
  have hLeft :
      Function.LeftInverse
        (BasedHomotopyClasses.precomposeFun g : Ho*[X, Z] → Ho*[Y, Z])
        (BasedHomotopyClasses.precomposeFun f : Ho*[Y, Z] → Ho*[X, Z]) := by
    intro a
    -- Normalize the composite precomposition map to `g ≫ f`, then collapse it to the identity
    -- using the chosen homotopy inverse relation.
    have hcomp :
        BasedHomotopyClasses.precomposeFun g (BasedHomotopyClasses.precomposeFun f a) =
          BasedHomotopyClasses.precomposeFun (g ≫ f) a := by
      simpa using congrArg (fun h : Ho*[Y, Z] → Ho*[Y, Z] ↦ h a)
        (BasedHomotopyClasses.precompose_comp g f).symm
    have hId :
        (BasedHomotopyClasses.precompose (g ≫ f) : Ho*[Y, Z] ⟶ Ho*[Y, Z]) =
          𝟙 (Ho*[Y, Z]) := by
      calc
        (BasedHomotopyClasses.precompose (g ≫ f) : Ho*[Y, Z] ⟶ Ho*[Y, Z]) =
            BasedHomotopyClasses.precompose (𝟙 Y) :=
          basedHomotopyClassesPrecompose_eq_of_homotopicUnder Z hgf
        _ = 𝟙 (Ho*[Y, Z]) := Pointed.Hom.ext BasedHomotopyClasses.precompose_id
    calc
      BasedHomotopyClasses.precomposeFun g (BasedHomotopyClasses.precomposeFun f a) =
          BasedHomotopyClasses.precomposeFun (g ≫ f) a := hcomp
      _ = a := congrArg (fun h : Ho*[Y, Z] ⟶ Ho*[Y, Z] ↦ h a) hId
  have hRight :
      Function.RightInverse
        (BasedHomotopyClasses.precomposeFun g : Ho*[X, Z] → Ho*[Y, Z])
        (BasedHomotopyClasses.precomposeFun f : Ho*[Y, Z] → Ho*[X, Z]) := by
    intro a
    -- The other composite reduces to `f ≫ g`, which is homotopic under the basepoint to the
    -- identity on `X`.
    have hcomp :
        BasedHomotopyClasses.precomposeFun f (BasedHomotopyClasses.precomposeFun g a) =
          BasedHomotopyClasses.precomposeFun (f ≫ g) a := by
      simpa using congrArg (fun h : Ho*[X, Z] → Ho*[X, Z] ↦ h a)
        (BasedHomotopyClasses.precompose_comp f g).symm
    have hId :
        (BasedHomotopyClasses.precompose (f ≫ g) : Ho*[X, Z] ⟶ Ho*[X, Z]) =
          𝟙 (Ho*[X, Z]) := by
      calc
        (BasedHomotopyClasses.precompose (f ≫ g) : Ho*[X, Z] ⟶ Ho*[X, Z]) =
            BasedHomotopyClasses.precompose (𝟙 X) :=
          basedHomotopyClassesPrecompose_eq_of_homotopicUnder Z hfg
        _ = 𝟙 (Ho*[X, Z]) := Pointed.Hom.ext BasedHomotopyClasses.precompose_id
    calc
      BasedHomotopyClasses.precomposeFun f (BasedHomotopyClasses.precomposeFun g a) =
          BasedHomotopyClasses.precomposeFun (f ≫ g) a := hcomp
      _ = a := congrArg (fun h : Ho*[X, Z] ⟶ Ho*[X, Z] ↦ h a) hId
  exact ⟨hLeft.injective, hRight.surjective⟩

/-- Helper for Theorem 22.2.6: the loop-owner comparison has an explicit inverse on classes of
maps out of a based CW complex. -/
private theorem PointedCompactlyGenerated.toBasedSpaceLoopComparison_postcomposeBijective
    (A : BasedCWComplex) (X : PointedCompactlyGenerated) :
    Function.Bijective
      (basedHomotopyClassesPostcomposeFun A.obj
        (PointedCompactlyGenerated.toBasedSpaceLoopComparison X)) := by
  -- The missing library bridge is that an abstract `TopCat.CWComplex` has the compactly
  -- generated weak topology.  With that bridge, the inverse keeps the same loop-valued function
  -- and upgrades its continuity to the compactly generated loop topology.
  sorry

/-- Helper for Theorem 22.2.6: postcomposition by a weak equivalence is bijective on based
homotopy classes with cofibrant source and fibrant target. -/
private theorem basedHomotopyClassesPostcomposeFun_bijective_of_weakEquivalence
    [CategoryWithCofibrations BasedSpace]
    [CategoryWithFibrations BasedSpace]
    (X Y Z : BasedSpace) [IsCofibrant X] [IsFibrant Y] [IsFibrant Z]
    (g : Y ⟶ Z) (hg : IsWeakEquivalence g.right.hom) :
    Function.Bijective (basedHomotopyClassesPostcomposeFun X g) :=
  -- Route correction: the source-facing postcomposition algebra is now isolated in
  -- `basedHomotopyClassesPostcomposeFun_bijective_of_homotopyEquivalence`. The only remaining
  -- gap is the executable bridge from a model-category weak equivalence `g` to either a local
  -- `Ho*`-to-`LeftHomotopyClass` conjugation or a source-facing based homotopy-equivalence
  -- witness for `g`.
  sorry

/-- Helper for Theorem 22.2.6: postcomposition by the loop of a weak equivalence is bijective on
based homotopy classes after conjugating through the suspension-loop adjunction. -/
private theorem basedHomotopyClassesPostcomposeLoopBasedMap_bijective_of_weakEquivalence
    [CategoryWithCofibrations BasedSpace]
    [CategoryWithFibrations BasedSpace]
    (X Y Z : BasedSpace) [IsCofibrant X] [IsFibrant Y] [IsFibrant Z]
    (g : Y ⟶ Z) (hg : IsWeakEquivalence g.right.hom) :
    Function.Bijective (basedHomotopyClassesPostcomposeFun X (loopBasedMap g)) :=
  -- TODO: conjugate postcomposition by `loopBasedMap g` on `Ho*[X, Ω(-)]` to ordinary
  -- postcomposition by `g` on `Ho*[ΣX, -]` via `basedHomotopyClassesEquivPi0BasedMappingSpace`
  -- and `suspensionLoopAdjunctionZerothHomotopyEquiv`, then reuse the ordinary weak-equivalence
  -- bijectivity theorem on the suspended source.
  sorry

/-- Helper for Theorem 22.2.6: precomposition by a weak equivalence is bijective on based
homotopy classes with fibrant target. -/
private theorem basedHomotopyClassesPrecomposeFun_bijective_of_weakEquivalence
    [CategoryWithCofibrations BasedSpace]
    [CategoryWithFibrations BasedSpace]
    (X Y Z : BasedSpace) [IsCofibrant X] [IsCofibrant Y] [IsFibrant Z]
    (f : X ⟶ Y) (hf : IsWeakEquivalence f.right.hom) :
    Function.Bijective (BasedHomotopyClasses.precomposeFun f : Ho*[Y, Z] → Ho*[X, Z]) :=
  -- TODO: transport `Ho*[ -, Z]` to the owner-level right homotopy quotient and apply
  -- `RightHomotopyClass.precomp_bijective_of_weakEquivalence`.
  sorry

private theorem omegaPrespectrumReducedCohomologyAdditiveComparisonFun_bijective
    (T : Prespectrum) [OmegaPrespectrum T] (q : ℤ) (X : BasedCWComplex) :
    Function.Bijective
      (basedHomotopyClassesPostcomposeFun X.obj
        (omegaPrespectrumReducedCohomologyAdditiveComparisonMap T q)) := by
  -- This is the remaining owner-level weak-equivalence bridge for the comparison map.  The
  -- negative-degree equality transports and the nonnegative Ω-prespectrum structure maps are
  -- handled uniformly once the local `Ho*` quotient is identified with the model-category owner.
  sorry

/-- Helper for Theorem 22.2.6: precomposition on the source and postcomposition on the target
commute on based homotopy classes. This is the naturality square for the represented functors,
spelled directly on Chapter 8 representatives so the later comparison transformation can reuse it
without reopening the quotient relation. -/
private theorem basedHomotopyClassesPrecomposeFun_postcomposeFun
    {X Y A B : BasedSpace} (f : X ⟶ Y) (g : A ⟶ B) :
    basedHomotopyClassesPostcomposeFun X g ∘ BasedHomotopyClasses.precomposeFun f =
      BasedHomotopyClasses.precomposeFun f ∘ basedHomotopyClassesPostcomposeFun Y g := by
  -- Compare both composites on a representative `h : Y ⟶ A`; each side returns the class of
  -- `f ≫ h ≫ g`.
  funext a
  refine Quotient.inductionOn a ?_
  intro h
  rfl

private noncomputable def omegaPrespectrumReducedCohomologyAdditiveComparisonApp
    (T : Prespectrum) (q : ℤ) (X : BasedCWComplexᵒᵖ) :
    (omegaPrespectrumReducedCohomology T q).obj X ⟶
      ((omegaPrespectrumReducedCohomologyAdditive T q) ⋙ addCommGrpCatToPointed).obj X where
  toFun a :=
    show Additive
        (Ho*[X.unop.obj, Ωᵇ (Ωᵇ (omegaPrespectrumRepresentingBasedSpace T (q + 2)))]) from
      basedHomotopyClassesPostcomposeFun X.unop.obj
        (omegaPrespectrumReducedCohomologyAdditiveComparisonMap T q) a
  map_point := by
    simpa using
      basedHomotopyClassesPostcomposeFun_point X.unop.obj
        (omegaPrespectrumReducedCohomologyAdditiveComparisonMap T q)

/-- The additive bridge `omegaPrespectrumReducedCohomologyAdditive T q` carries a canonical
degreewise pointed comparison from the source-facing represented functor
`omegaPrespectrumReducedCohomology T q`. -/
noncomputable def omegaPrespectrumReducedCohomologyAdditiveComparison
    (T : Prespectrum) (q : ℤ) :
    omegaPrespectrumReducedCohomology T q ⟶
      (omegaPrespectrumReducedCohomologyAdditive T q) ⋙ addCommGrpCatToPointed :=
  { app := omegaPrespectrumReducedCohomologyAdditiveComparisonApp T q
    naturality := by
      intro X Y f
      -- The comparison is represented by postcomposition with a fixed based map, so naturality
      -- is exactly the commuting precompose/postcompose square on based homotopy classes.
      ext a
      simpa [omegaPrespectrumReducedCohomologyAdditiveComparisonApp,
        addCommGrpCatToPointed, BasedHomotopyClasses.doubleLoopHomotopyClassesAdditiveFunctor,
        BasedHomotopyClasses.doubleLoopHomotopyClassesAdditiveOnBasedCWComplexes,
        BasedHomotopyClasses.doubleLoopHomotopyClassesPrecomposeHom] using
        congrArg (fun h ↦ h a)
          (basedHomotopyClassesPrecomposeFun_postcomposeFun
            (basedCWComplexInclusion.map f.unop)
            (omegaPrespectrumReducedCohomologyAdditiveComparisonMap T q)) }

/-- For an Ω-prespectrum, the degreewise pointed comparison into the additive bridge is bijective
on each based-CW complex. -/
theorem omegaPrespectrumReducedCohomologyAdditiveComparison_bijective
    (T : Prespectrum) [OmegaPrespectrum T] (q : ℤ) (X : BasedCWComplex) :
    Function.Bijective
      ((omegaPrespectrumReducedCohomologyAdditiveComparison T q).app (Opposite.op X)) := by
  -- The restored natural transformation is pointwise the postcomposition map used to define its
  -- components, so the previously isolated pointwise bijectivity theorem applies verbatim.
  simpa [omegaPrespectrumReducedCohomologyAdditiveComparison,
    omegaPrespectrumReducedCohomologyAdditiveComparisonApp] using
    omegaPrespectrumReducedCohomologyAdditiveComparisonFun_bijective T q X

private theorem omegaPrespectrumReducedCohomologyAdditiveTheory
    [CategoryWithCofibrations BasedSpace]
    [CategoryWithCofibrations BasedCWComplex]
    [CategoryWithWeakEquivalences BasedCWComplex]
    (setup : BasedCWReducedSuspensionCofiberSetup)
    (T : Prespectrum) [OmegaPrespectrum T] :
    ReducedCohomologyTheoryOnBasedCWComplexes
      setup (omegaPrespectrumReducedCohomologyAdditive T) := by
  -- TODO: assemble the reduced-theory fields from Lemma 22.2.2 on the double-loop target, the
  -- normalized comparison bijection above, the source-side weak-equivalence action on `Ho*[ -, -]`,
  -- and the suspension-loop adjunction package.
  -- The remaining blocker is now explicit: the owner-level weak-equivalence transfer lemmas on
  -- based homotopy classes and the suspension natural isomorphism still need executable proofs.
  sorry

/-- The chosen additive bridge attached to an Ω-prespectrum `T` carries the reduced-cohomology
theory structure on based CW complexes. -/
instance omegaPrespectrumReducedCohomologyAdditive_isReducedCohomologyTheory
    [CategoryWithCofibrations BasedSpace]
    [CategoryWithCofibrations BasedCWComplex]
    [CategoryWithWeakEquivalences BasedCWComplex]
    (setup : BasedCWReducedSuspensionCofiberSetup)
    (T : Prespectrum) [OmegaPrespectrum T] :
    ReducedCohomologyTheoryOnBasedCWComplexes
      setup (omegaPrespectrumReducedCohomologyAdditive T) :=
  omegaPrespectrumReducedCohomologyAdditiveTheory setup T

/-- Theorem 22.2.6: an Ω-prespectrum `T` determines a reduced cohomology theory on based CW
complexes. The degreewise pointed comparison with the source-facing represented functors
`omegaPrespectrumReducedCohomology T q` is recorded by the companion theorem
`omegaPrespectrumRepresentsReducedCohomologyTheory_comparison`. -/
noncomputable def omegaPrespectrumRepresentsReducedCohomologyTheory
    [CategoryWithCofibrations BasedSpace]
    [CategoryWithCofibrations BasedCWComplex]
    [CategoryWithWeakEquivalences BasedCWComplex]
    (setup : BasedCWReducedSuspensionCofiberSetup)
    (T : Prespectrum) [OmegaPrespectrum T] :
    BundledReducedCohomologyTheory setup :=
  ⟨omegaPrespectrumReducedCohomologyAdditive T, inferInstance⟩

/-- The bundled reduced theory carried by an Ω-prespectrum has underlying graded functor
`omegaPrespectrumReducedCohomologyAdditive T`. -/
@[simp] theorem omegaPrespectrumRepresentsReducedCohomologyTheory_cohomology
    [CategoryWithCofibrations BasedSpace]
    [CategoryWithCofibrations BasedCWComplex]
    [CategoryWithWeakEquivalences BasedCWComplex]
    (setup : BasedCWReducedSuspensionCofiberSetup)
    (T : Prespectrum) [OmegaPrespectrum T] :
    (omegaPrespectrumRepresentsReducedCohomologyTheory setup T).cohomology =
      omegaPrespectrumReducedCohomologyAdditive T :=
  rfl

/-- In each degree, the bundled reduced theory carried by an Ω-prespectrum comes with the canonical
degreewise pointed comparison from the source-facing represented functor. -/
abbrev omegaPrespectrumRepresentsReducedCohomologyTheory_comparison
    [CategoryWithCofibrations BasedSpace]
    [CategoryWithCofibrations BasedCWComplex]
    [CategoryWithWeakEquivalences BasedCWComplex]
    (setup : BasedCWReducedSuspensionCofiberSetup)
    (T : Prespectrum) [OmegaPrespectrum T] (q : ℤ) :
    omegaPrespectrumReducedCohomology T q ⟶
      ((omegaPrespectrumRepresentsReducedCohomologyTheory setup T).cohomology q) ⋙
        addCommGrpCatToPointed := by
  simpa using omegaPrespectrumReducedCohomologyAdditiveComparison T q

/-- Each component of
`omegaPrespectrumRepresentsReducedCohomologyTheory_comparison setup T q` is bijective. -/
theorem omegaPrespectrumRepresentsReducedCohomologyTheory_comparison_bijective
    [CategoryWithCofibrations BasedSpace]
    [CategoryWithCofibrations BasedCWComplex]
    [CategoryWithWeakEquivalences BasedCWComplex]
    (setup : BasedCWReducedSuspensionCofiberSetup)
    (T : Prespectrum) [OmegaPrespectrum T] (q : ℤ) (X : BasedCWComplex) :
    Function.Bijective
      ((omegaPrespectrumRepresentsReducedCohomologyTheory_comparison setup T q).app
        (Opposite.op X)) := by
  simpa using omegaPrespectrumReducedCohomologyAdditiveComparison_bijective T q X
