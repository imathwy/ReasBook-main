import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap19.Theorem_19_2_5

open CategoryTheory
open HomotopicalAlgebra

universe u

-- Semantic recall via `lean_leansearch` did not surface a canonical mathlib owner for this
-- comparison, while local project precedent already formalizes the all-spaces axioms by
-- `PairCohomologyTheory π` and the CW-pair axioms by `IsCohomologyTheoryOnCWPairs π E`.

namespace PairCohomologyTheory

/-- An isomorphism of pair cohomology theories is a graded natural isomorphism compatible with the
connecting morphisms. -/
structure Iso {π : Type u} [AddCommGroup π] (H K : PairCohomologyTheory π) where
  /-- The degreewise natural isomorphism on the underlying graded contravariant functors. -/
  app : ∀ q : ℤ, H.cohomology q ≅ K.cohomology q
  /-- The degreewise natural isomorphism intertwines the connecting morphisms. -/
  boundary_comm :
    ∀ q : ℤ,
      Functor.whiskerLeft SpacePair.subspaceFunctor.op (app q).hom ≫ K.boundary q =
        H.boundary q ≫ (app (q + 1)).hom

/-- An isomorphism of pair cohomology theories respects two CW-pair comparison isomorphisms when,
after restriction to `CWPair`, it identifies them degreewise. -/
def Iso.RespectsCWPairComparison
    {π : Type u} [AddCommGroup π] {H K : PairCohomologyTheory π}
    (i : PairCohomologyTheory.Iso H K)
    {E : ℤ → CWPairᵒᵖ ⥤ AddCommGrpCat.{u}}
    (eH : ∀ q : ℤ, restrictPairCohomologyTheoryToCWPairs H q ≅ E q)
    (eK : ∀ q : ℤ, restrictPairCohomologyTheoryToCWPairs K q ≅ E q) : Prop :=
  ∀ q : ℤ,
    Functor.isoWhiskerLeft (CategoryTheory.ObjectProperty.ι IsCWPair).op (i.app q) ≪≫ eK q =
      eH q

end PairCohomologyTheory

/-- A degreewise natural isomorphism from the restriction of `H` to a source-facing CW-pair
cohomology theory `E` is comparison-compatible when it intertwines the pair-theory boundary with
the canonical CW-pair boundary on `(A, ∅)`. -/
def HasCWPairCohomologyTheoryComparison
    {π : Type u} [AddCommGroup π] (H : PairCohomologyTheory π)
    {E : ℤ → CWPairᵒᵖ ⥤ AddCommGrpCat.{u}} (hE : IsCohomologyTheoryOnCWPairs π E)
    (e : ∀ q : ℤ, restrictPairCohomologyTheoryToCWPairs H q ≅ E q) : Prop :=
  ∀ (q : ℤ) (P : CWPair),
    CommSq
      ((e q).hom.app (Opposite.op (IsCWPair.subspacePair P)))
      ((H.boundary q).app (Opposite.op (IsCWPair.toSpacePair P)))
      ((hE.boundary q).app (Opposite.op P))
      ((e (q + 1)).hom.app (Opposite.op P))

/-- A comparison `e` between the restriction of `H` and `E` is boundary-compatible exactly when,
for every degree `q` and CW pair `P`, the corresponding boundary square commutes on the canonical
CW-pair operator `(X, A) ↦ (A, ∅)`. -/
theorem hasCWPairCohomologyTheoryComparison_boundary_comm
    {π : Type u} [AddCommGroup π] {H : PairCohomologyTheory π}
    {E : ℤ → CWPairᵒᵖ ⥤ AddCommGrpCat.{u}} {hE : IsCohomologyTheoryOnCWPairs π E}
    {e : ∀ q : ℤ, restrictPairCohomologyTheoryToCWPairs H q ≅ E q}
    (he : HasCWPairCohomologyTheoryComparison H hE e) (q : ℤ) (P : CWPair) :
    ((e q).hom.app (Opposite.op (IsCWPair.subspacePair P))) ≫
        ((hE.boundary q).app (Opposite.op P)) =
      ((H.boundary q).app (Opposite.op (IsCWPair.toSpacePair P))) ≫
        ((e (q + 1)).hom.app (Opposite.op P)) :=
  (he q P).w

/-- Theorem 18.1.5 (1): the restriction of a Chapter 18 cohomology theory on all pairs of spaces
to the full subcategory of CW pairs satisfies the CW-pair cohomology axioms. -/
instance restrictPairCohomologyTheoryToCWPairs_isCohomologyTheoryOnCWPairs
    {π : Type u} [AddCommGroup π] (H : PairCohomologyTheory π) :
    IsCohomologyTheoryOnCWPairs π (restrictPairCohomologyTheoryToCWPairs H) where
  boundary q :=
    Functor.whiskerLeft (CategoryTheory.ObjectProperty.ι IsCWPair).op (H.boundary q)
  dimensionZero pt hpt := by
    sorry
  dimensionHigher pt hpt q hq := by
    sorry
  exact₁ q P := by
    simpa [restrictPairCohomologyTheoryToCWPairs, IsCWPair.absoluteToRelative,
      IsCWPair.subspaceInclusion] using H.exact₁ q (IsCWPair.toSpacePair P)
  exact₂ q P := by
    simpa [restrictPairCohomologyTheoryToCWPairs, IsCWPair.subspaceInclusion] using
      H.exact₂ q (IsCWPair.toSpacePair P)
  exact₃ q P := by
    simpa [restrictPairCohomologyTheoryToCWPairs, IsCWPair.absoluteToRelative] using
      H.exact₃ q (IsCWPair.toSpacePair P)
  excision q P U hU := by
    simpa [restrictPairCohomologyTheoryToCWPairs, IsCWPair.removeSubsetInclusion] using
      H.excision q (IsCWPair.toSpacePair P) U hU
  additivity q := by
    sorry
  weakEquivalenceInvariant q {P} {Q} f := by
    sorry

namespace PairCohomologyTheory

/-- The bundled CW-pair cohomology theory obtained by restricting `H` to the full subcategory of
CW pairs. -/
abbrev restrictToCWPairCohomologyTheory
    {π : Type u} [AddCommGroup π] (H : PairCohomologyTheory π) : CWPairCohomologyTheory π :=
  ⟨restrictPairCohomologyTheoryToCWPairs H, inferInstance⟩

end PairCohomologyTheory

namespace IsCohomologyTheoryOnCWPairs

/-- A source-facing CW-pair cohomology theory extends to some Chapter 18 pair cohomology theory
together with degreewise comparison isomorphisms compatible with its boundary maps, and that
extension is unique up to comparison-respecting isomorphism. -/
def HasPairCohomologyTheoryExtension
    {π : Type u} [AddCommGroup π] {E : ℤ → CWPairᵒᵖ ⥤ AddCommGrpCat.{u}}
    (hE : IsCohomologyTheoryOnCWPairs π E) : Prop :=
  ∃ H : PairCohomologyTheory π,
    ∃ e : ∀ q : ℤ, restrictPairCohomologyTheoryToCWPairs H q ≅ E q,
      HasCWPairCohomologyTheoryComparison H hE e ∧
      ∀ K : PairCohomologyTheory π,
        ∀ eK : ∀ q : ℤ, restrictPairCohomologyTheoryToCWPairs K q ≅ E q,
          HasCWPairCohomologyTheoryComparison K hE eK →
            ∃ i : PairCohomologyTheory.Iso H K,
              PairCohomologyTheory.Iso.RespectsCWPairComparison i e eK

end IsCohomologyTheoryOnCWPairs

namespace CWPairCohomologyTheory

/-- A bundled CW-pair cohomology theory extends to some Chapter 18 pair cohomology theory
together with degreewise comparison isomorphisms compatible with its boundary maps, and that
extension is unique up to comparison-respecting isomorphism. -/
def HasPairCohomologyTheoryExtension
    {π : Type u} [AddCommGroup π] (E : CWPairCohomologyTheory π) : Prop :=
  IsCohomologyTheoryOnCWPairs.HasPairCohomologyTheoryExtension E.2

end CWPairCohomologyTheory

/-- Theorem 18.1.5 (2): conversely, any graded cohomology theory on CW pairs extends to a
Chapter 18 cohomology theory on all pairs through CW approximation, and any two such extensions
equipped with boundary-compatible comparison isomorphisms are isomorphic in a way that
intertwines the supplied CW-pair comparison data after restriction. -/
theorem exists_pairCohomologyTheory_of_isCohomologyTheoryOnCWPairs
    {π : Type u} [AddCommGroup π] (E : ℤ → CWPairᵒᵖ ⥤ AddCommGrpCat.{u})
    (hE : IsCohomologyTheoryOnCWPairs π E) :
    hE.HasPairCohomologyTheoryExtension := sorry

/-- A bundled CW-pair cohomology theory extends to a Chapter 18 pair cohomology theory on all
pairs, with restriction back to CW pairs equipped with a graded natural isomorphism that is
compatible with the boundary maps, and any other such extension carries a comparison-respecting
isomorphism from the chosen one. -/
theorem exists_pairCohomologyTheory_of_cwPairCohomologyTheory
    {π : Type u} [AddCommGroup π] (E : CWPairCohomologyTheory π) :
    E.HasPairCohomologyTheoryExtension :=
  exists_pairCohomologyTheory_of_isCohomologyTheoryOnCWPairs E.1 E.2
