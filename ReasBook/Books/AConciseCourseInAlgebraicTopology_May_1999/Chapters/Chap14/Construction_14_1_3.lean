import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap02.Lemma_2_4_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap13.PairHomologyTheory
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap14.Definition_14_1_2

open CategoryTheory Limits

universe u

-- Semantic recall via `lean_leansearch` surfaced only abstract splitting lemmas. The genuine
-- chapter-level owner in this repo is `PairHomologyTheory`, so this file states Construction
-- 14.1.3 directly on absolute and singleton-basepoint pairs.

/-- The pair-homology group `H_q(X, A)` attached to a Chapter 13 homology theory. -/
abbrev pairHomologyGroup
    {π : Type u} [AddCommGroup π] (H : PairHomologyTheory π)
    (q : ℤ) (X : TopCat.{u}) (A : Set X) : Type u :=
  (H.homology q).obj
    { space := X
      subspace := A }

/-- Pair-homology groups inherit their additive-group structure from the ambient `ModuleCat`
object. -/
instance pairHomologyGroupAddCommGroup
    {π : Type u} [AddCommGroup π] (H : PairHomologyTheory π)
    (q : ℤ) (X : TopCat.{u}) (A : Set X) :
    AddCommGroup (pairHomologyGroup H q X A) :=
  inferInstance

/-- The absolute homology group `H_q(X)` of the underlying space of a based space `X`. -/
abbrev absoluteHomology
    {π : Type u} [AddCommGroup π] (H : PairHomologyTheory π)
    (q : ℤ) (X : BasedSpace) : Type u :=
  pairHomologyGroup H q X.right (∅ : Set X.right)

/-- The reduced homology group `H̃_q(X)`, using Definition 14.1.2 for the singleton basepoint
pair. -/
abbrev basedReducedHomology
    {π : Type u} [AddCommGroup π] (H : PairHomologyTheory π)
    (q : ℤ) (X : BasedSpace) : Type u :=
  reducedHomology (pairHomologyGroup H) q X

/-- The point summand `H_q(*)`. -/
abbrev pointHomology
    {π : Type u} [AddCommGroup π] (H : PairHomologyTheory π)
    (q : ℤ) : Type u :=
  pairHomologyGroup H q (TopCat.of PUnit) (∅ : Set (TopCat.of PUnit))

/-- Reduced homology inherits its additive-group structure from the corresponding singleton-point
pair-homology group. -/
instance basedReducedHomologyAddCommGroup
    {π : Type u} [AddCommGroup π] (H : PairHomologyTheory π)
    (q : ℤ) (X : BasedSpace) :
    AddCommGroup (basedReducedHomology H q X) :=
  show AddCommGroup
      (pairHomologyGroup H q X.right ({underTopBasepoint X} : Set X.right)) from inferInstance

/-- The singleton-basepoint pair `(X, {x₀})` attached to a based space `X`. -/
def basedReducedPair (X : BasedSpace) : SpacePair where
  space := X.right
  subspace := ({underTopBasepoint X} : Set X.right)

/-- The constant map `X ⟶ *`, regarded as a map of pairs `(X, ∅) ⟶ (*, ∅)`. -/
def basedPointRetraction (X : BasedSpace) : SpacePair.absolute X.right ⟶ SpacePair.point where
  hom := TopCat.ofHom (ContinuousMap.const X.right PUnit.unit)
  map_subspace' := by
    intro x hx
    cases hx

/-- A based map induces a map of absolute pairs `(X, ∅) ⟶ (Y, ∅)`. -/
def basedMapAbsolutePairHom {X Y : BasedSpace} (f : X ⟶ Y) :
    SpacePair.absolute X.right ⟶ SpacePair.absolute Y.right where
  hom := f.right
  map_subspace' := by
    intro x hx
    cases hx

/-- A based map induces a map of singleton-basepoint pairs `(X, {x₀}) ⟶ (Y, {y₀})`. -/
def basedMapReducedPairHom {X Y : BasedSpace} (f : X ⟶ Y) :
    basedReducedPair X ⟶ basedReducedPair Y where
  hom := f.right
  map_subspace' := by
    intro x hx
    change f.right.hom x = underTopBasepoint Y
    change x = underTopBasepoint X at hx
    rw [hx]
    exact fundamentalGroupFunctorMap_basepoint f

/-- The canonical projection `H_q(X) ⟶ H̃_q(X)` is induced by the absolute-to-relative map of the
singleton-basepoint pair. -/
abbrev basedHomologyReducedProjection
    {π : Type u} [AddCommGroup π] (H : PairHomologyTheory π)
    (q : ℤ) (X : BasedSpace) :
    absoluteHomology H q X →+ basedReducedHomology H q X :=
  ((H.homology q).map (SpacePair.absoluteToRelative (basedReducedPair X))).hom.toAddMonoidHom

/-- The canonical projection `H_q(X) ⟶ H_q(*)` is induced by the basepoint retraction. -/
abbrev basedHomologyPointProjection
    {π : Type u} [AddCommGroup π] (H : PairHomologyTheory π)
    (q : ℤ) (X : BasedSpace) :
    absoluteHomology H q X →+ pointHomology H q :=
  ((H.homology q).map (basedPointRetraction X)).hom.toAddMonoidHom

/-- The absolute-homology map induced by a based map. -/
abbrev basedHomologyAbsoluteMap
    {π : Type u} [AddCommGroup π] (H : PairHomologyTheory π)
    (q : ℤ) {X Y : BasedSpace} (f : X ⟶ Y) :
    absoluteHomology H q X →+ absoluteHomology H q Y :=
  ((H.homology q).map (basedMapAbsolutePairHom f)).hom.toAddMonoidHom

/-- The reduced-homology map induced by a based map. -/
abbrev basedHomologyReducedMap
    {π : Type u} [AddCommGroup π] (H : PairHomologyTheory π)
    (q : ℤ) {X Y : BasedSpace} (f : X ⟶ Y) :
    basedReducedHomology H q X →+ basedReducedHomology H q Y :=
  ((H.homology q).map (basedMapReducedPairHom f)).hom.toAddMonoidHom

/-- The canonical split homomorphism `H_q(X) ⟶ H̃_q(X) × H_q(*)` is induced by the
absolute-to-relative map for `(X, {underTopBasepoint X})` together with the basepoint retraction
`X ⟶ *`. -/
def basedHomologySplitHom
    {π : Type u} [AddCommGroup π] (H : PairHomologyTheory π)
    (q : ℤ) (X : BasedSpace) :
    absoluteHomology H q X →+ basedReducedHomology H q X × pointHomology H q :=
  (basedHomologyReducedProjection H q X).prod (basedHomologyPointProjection H q X)

/-- Construction 14.1.3 (1). For a based space `X`, the canonical split homomorphism
`H_q(X) ⟶ H̃_q(X) × H_q(*)` induced by the absolute-to-relative map and the basepoint retraction
is bijective, so it exhibits the product decomposition of absolute homology. -/
theorem basedHomologySplit
    {π : Type u} [AddCommGroup π] (H : PairHomologyTheory π)
    (q : ℤ) (X : BasedSpace) :
    Function.Bijective (basedHomologySplitHom H q X) := sorry

/-- Construction 14.1.3 (2). For a based map `f : X ⟶ Y`, the canonical split homomorphism of
Construction 14.1.3 is natural with respect to the induced maps on absolute and reduced
homology, and the point summand is carried by the identity on `H_q(*)`. -/
theorem basedHomologySplit_natural
    {π : Type u} [AddCommGroup π] (H : PairHomologyTheory π)
    (q : ℤ) {X Y : BasedSpace} (f : X ⟶ Y) :
    CommSq
      (AddCommGrpCat.ofHom (basedHomologyAbsoluteMap H q f))
      (AddCommGrpCat.ofHom (basedHomologySplitHom H q X))
      (AddCommGrpCat.ofHom (basedHomologySplitHom H q Y))
      (AddCommGrpCat.ofHom
        ((basedHomologyReducedMap H q f).prodMap (AddMonoidHom.id (pointHomology H q)))) := by
  sorry

/-- The naturality square of Construction 14.1.3 as an equality of composites. -/
theorem basedHomologySplit_natural_w
    {π : Type u} [AddCommGroup π] (H : PairHomologyTheory π)
    (q : ℤ) {X Y : BasedSpace} (f : X ⟶ Y) :
    (basedHomologySplitHom H q Y).comp (basedHomologyAbsoluteMap H q f) =
      ((basedHomologyReducedMap H q f).prodMap (AddMonoidHom.id (pointHomology H q))).comp
        (basedHomologySplitHom H q X) :=
  by
    simpa using congrArg AddCommGrpCat.Hom.hom (basedHomologySplit_natural H q f).w
