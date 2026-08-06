import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap13.CWPair
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap13.PairHomologyTheory

open CategoryTheory
open CategoryTheory.Limits
open HomotopicalAlgebra

noncomputable section

universe u

-- `Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap13.CWPair` already provides the canonical repository owner `IsCWPair`
-- and its full subcategory `CWPair`. This file builds the CW-pair homology-theory API on top of
-- that source-facing pair notion.

/-- Restrict a Chapter 13 homology theory on all pairs to the full subcategory of CW pairs. -/
abbrev restrictPairHomologyTheoryToCWPairs
    {π : Type u} [AddCommGroup π] (H : PairHomologyTheory π) :
    ℤ → CWPair ⥤ ModuleCat.{u} ℤ :=
  fun q ↦ CategoryTheory.ObjectProperty.ι IsCWPair ⋙ H.homology q

/-- A homology theory on CW pairs with underlying graded functor `E` records the canonical
CW-pair operators `(A, ∅)`, `(X, ∅)`, and excision on the repository owner `CWPair`, together
with the boundary natural transformations and the dimension, exactness, excision, additivity,
and weak-equivalence axioms directly on `E`. This is the canonical source-facing owner in the
file. -/
class IsHomologyTheoryOnCWPairs
    (π : Type u) [AddCommGroup π] (E : ℤ → CWPair ⥤ ModuleCat.{u} ℤ) where
  /-- The connecting morphisms `H_q(X, A; π) ⟶ H_(q - 1)(A; π)` on `CWPair`, natural in the
  canonical subspace functor `(X, A) ↦ (A, ∅)`. -/
  boundary (q : ℤ) : E q ⟶ IsCWPair.subspaceFunctor ⋙ E (q - 1)
  /-- Degree-zero homology of any CW-pair representative of the one-point pair is `π`. -/
  dimensionZero (pt : CWPair) (hpt : Nonempty (pt ≅ IsCWPair.point)) :
    Nonempty ((E 0).obj pt ≅ ModuleCat.of ℤ π)
  /-- Homology of a CW-pair representative of the one-point pair vanishes away from degree `0`. -/
  dimensionHigher (pt : CWPair) (hpt : Nonempty (pt ≅ IsCWPair.point))
      (q : ℤ) (hq : q ≠ 0) :
    IsZero ((E q).obj pt)
  /-- The sequence `H_q(A; π) ⟶ H_q(X; π) ⟶ H_q(X, A; π)` is exact for the canonical CW-pair
  operators. -/
  exact₁_zero (q : ℤ) (P : CWPair) :
    ((E q).map (IsCWPair.subspaceInclusion P)) ≫ ((E q).map (IsCWPair.absoluteToRelative P)) = 0
  /-- The first exactness window for the canonical CW-pair operators. -/
  exact₁ (q : ℤ) (P : CWPair) :
    (CategoryTheory.ShortComplex.mk
      ((E q).map (IsCWPair.subspaceInclusion P))
      ((E q).map (IsCWPair.absoluteToRelative P))
      (exact₁_zero q P)).Exact
  /-- The sequence `H_q(X; π) ⟶ H_q(X, A; π) ⟶ H_(q - 1)(A; π)` is exact for the canonical
  CW-pair operators. -/
  exact₂_zero (q : ℤ) (P : CWPair) :
    ((E q).map (IsCWPair.absoluteToRelative P)) ≫ (boundary q).app P = 0
  /-- The second exactness window for the canonical CW-pair operators. -/
  exact₂ (q : ℤ) (P : CWPair) :
    (CategoryTheory.ShortComplex.mk
      ((E q).map (IsCWPair.absoluteToRelative P))
      ((boundary q).app P)
      (exact₂_zero q P)).Exact
  /-- The sequence `H_q(X, A; π) ⟶ H_(q - 1)(A; π) ⟶ H_(q - 1)(X; π)` is exact for the canonical
  CW-pair operators. -/
  exact₃_zero (q : ℤ) (P : CWPair) :
    ((boundary q).app P) ≫ ((E (q - 1)).map (IsCWPair.subspaceInclusion P)) = 0
  /-- The third exactness window for the canonical CW-pair operators. -/
  exact₃ (q : ℤ) (P : CWPair) :
    (CategoryTheory.ShortComplex.mk
      ((boundary q).app P)
      ((E (q - 1)).map (IsCWPair.subspaceInclusion P))
      (exact₃_zero q P)).Exact
  /-- Excision identifies `H_q(X, A; π)` with the homology of the canonical excision pair. -/
  excision (q : ℤ) (P : CWPair) (U : Set (IsCWPair.space P))
      (hU : closure U ⊆ interior (IsCWPair.subspace P)) :
    IsIso ((E q).map (IsCWPair.removeSubsetInclusion P U hU))
  /-- Additivity for a coproduct `∐ i, (Xᵢ, Aᵢ)` of CW pairs. -/
  additivity {ι : Type u} (q : ℤ) (P : ι → CWPair) :
    Nonempty (((E q).obj (IsCWPair.sigmaPair P)) ≅ ∐ fun i : ι ↦ (E q).obj (P i))
  /-- Weakly equivalent CW pairs induce isomorphisms in each homological degree. -/
  weakEquivalenceInvariant (q : ℤ) {P Q : CWPair} (f : P ⟶ Q)
      [WeakEquivalence f] :
    IsIso ((E q).map f)

/-- A bundled CW-pair homology theory is a graded functor on `CWPair` equipped with the canonical
source-facing owner `IsHomologyTheoryOnCWPairs`. -/
abbrev CWPairHomologyTheory (π : Type u) [AddCommGroup π] :=
  Σ E : ℤ → CWPair ⥤ ModuleCat.{u} ℤ, IsHomologyTheoryOnCWPairs π E

/-- A bundled CW-pair homology theory can be used as its underlying graded covariant functor. -/
instance {π : Type u} [AddCommGroup π] :
    CoeFun (CWPairHomologyTheory π) (fun _ ↦ ℤ → CWPair ⥤ ModuleCat.{u} ℤ) where
  coe H := H.1

/-- A bundled `CWPairHomologyTheory` carries its chosen CW-pair homology-theory structure on the
underlying graded functor. -/
instance {π : Type u} [AddCommGroup π] (H : CWPairHomologyTheory π) :
    IsHomologyTheoryOnCWPairs π H.1 :=
  H.2

namespace IsHomologyTheoryOnCWPairs

/-- A source-facing CW-pair homology theory exposes the dimension, exactness, excision,
additivity, and weak-equivalence axioms stated using the canonical `CWPair` operators. -/
theorem spec
    {π : Type u} [AddCommGroup π] {E : ℤ → CWPair ⥤ ModuleCat.{u} ℤ}
    (hE : IsHomologyTheoryOnCWPairs π E) :
    (∀ pt : CWPair, Nonempty (pt ≅ IsCWPair.point) →
      Nonempty ((E 0).obj pt ≅ ModuleCat.of ℤ π)) ∧
      (∀ pt : CWPair, Nonempty (pt ≅ IsCWPair.point) →
        ∀ q : ℤ, q ≠ 0 → IsZero ((E q).obj pt)) ∧
      (∀ q : ℤ, ∀ P : CWPair,
        (CategoryTheory.ShortComplex.mk
          ((E q).map (IsCWPair.subspaceInclusion P))
          ((E q).map (IsCWPair.absoluteToRelative P))
          (hE.exact₁_zero q P)).Exact) ∧
      (∀ q : ℤ, ∀ P : CWPair,
        (CategoryTheory.ShortComplex.mk
          ((E q).map (IsCWPair.absoluteToRelative P))
          ((hE.boundary q).app P)
          (hE.exact₂_zero q P)).Exact) ∧
      (∀ q : ℤ, ∀ P : CWPair,
        (CategoryTheory.ShortComplex.mk
          ((hE.boundary q).app P)
          ((E (q - 1)).map (IsCWPair.subspaceInclusion P))
          (hE.exact₃_zero q P)).Exact) ∧
      (∀ q : ℤ, ∀ P : CWPair, ∀ U : Set (IsCWPair.space P),
        ∀ hU : closure U ⊆ interior (IsCWPair.subspace P),
          IsIso ((E q).map (IsCWPair.removeSubsetInclusion P U hU))) ∧
      (∀ {ι : Type u}, ∀ q : ℤ, ∀ P : ι → CWPair,
        Nonempty (((E q).obj (IsCWPair.sigmaPair P)) ≅ ∐ fun i : ι ↦ (E q).obj (P i))) ∧
      (∀ q : ℤ, ∀ {P Q : CWPair} (f : P ⟶ Q),
        [WeakEquivalence f] → IsIso ((E q).map f)) := by
  refine ⟨hE.dimensionZero, hE.dimensionHigher, hE.exact₁, hE.exact₂, hE.exact₃, ?_, ?_,
    hE.weakEquivalenceInvariant⟩
  · intro q P U hU
    exact hE.excision q P U hU
  · intro ι q P
    exact hE.additivity q P

/-- The first exactness window of a CW-pair homology theory is the source-facing sequence
`H_q(A; π) ⟶ H_q(X; π) ⟶ H_q(X, A; π)` on the canonical CW-pair operators. -/
theorem exact_subspace_absoluteToRelative
    {π : Type u} [AddCommGroup π] {E : ℤ → CWPair ⥤ ModuleCat.{u} ℤ}
    (hE : IsHomologyTheoryOnCWPairs π E) (q : ℤ) (P : CWPair) :
    (CategoryTheory.ShortComplex.mk
      ((E q).map (IsCWPair.subspaceInclusion P))
      ((E q).map (IsCWPair.absoluteToRelative P))
      (hE.exact₁_zero q P)).Exact :=
  hE.exact₁ q P

/-- The second exactness window of a CW-pair homology theory is the source-facing sequence
`H_q(X; π) ⟶ H_q(X, A; π) ⟶ H_(q - 1)(A; π)` on the canonical CW-pair operators. -/
theorem exact_absoluteToRelative_boundary
    {π : Type u} [AddCommGroup π] {E : ℤ → CWPair ⥤ ModuleCat.{u} ℤ}
    (hE : IsHomologyTheoryOnCWPairs π E) (q : ℤ) (P : CWPair) :
    (CategoryTheory.ShortComplex.mk
      ((E q).map (IsCWPair.absoluteToRelative P))
      ((hE.boundary q).app P)
      (hE.exact₂_zero q P)).Exact :=
  hE.exact₂ q P

/-- The third exactness window of a CW-pair homology theory is the source-facing sequence
`H_q(X, A; π) ⟶ H_(q - 1)(A; π) ⟶ H_(q - 1)(X; π)` on the canonical CW-pair operators. -/
theorem exact_boundary_subspace
    {π : Type u} [AddCommGroup π] {E : ℤ → CWPair ⥤ ModuleCat.{u} ℤ}
    (hE : IsHomologyTheoryOnCWPairs π E) (q : ℤ) (P : CWPair) :
    (CategoryTheory.ShortComplex.mk
      ((hE.boundary q).app P)
      ((E (q - 1)).map (IsCWPair.subspaceInclusion P))
      (hE.exact₃_zero q P)).Exact :=
  hE.exact₃ q P

/-- The connecting morphism of a CW-pair homology theory is natural with respect to maps of
CW pairs. -/
theorem boundary_naturality
    {π : Type u} [AddCommGroup π] {E : ℤ → CWPair ⥤ ModuleCat.{u} ℤ}
    (hE : IsHomologyTheoryOnCWPairs π E) (q : ℤ) {P Q : CWPair} (f : P ⟶ Q) :
    CommSq
      ((E q).map f)
      ((hE.boundary q).app P)
      ((hE.boundary q).app Q)
      ((E (q - 1)).map (IsCWPair.subspaceFunctor.map f)) := by
  exact ⟨by simpa using (hE.boundary q).naturality f⟩

/-- The naturality square for the connecting morphism commutes as an equality of composites. -/
theorem boundary_naturality_w
    {π : Type u} [AddCommGroup π] {E : ℤ → CWPair ⥤ ModuleCat.{u} ℤ}
    (hE : IsHomologyTheoryOnCWPairs π E) (q : ℤ) {P Q : CWPair} (f : P ⟶ Q) :
    ((E q).map f) ≫ (hE.boundary q).app Q =
      (hE.boundary q).app P ≫ ((E (q - 1)).map (IsCWPair.subspaceFunctor.map f)) :=
  (hE.boundary_naturality q f).w

/-- Weakly equivalent CW pairs induce isomorphisms on the homology groups of a source-facing
CW-pair homology theory. -/
theorem map_isIso_of_weakEquivalence
    {π : Type u} [AddCommGroup π] {E : ℤ → CWPair ⥤ ModuleCat.{u} ℤ}
    (hE : IsHomologyTheoryOnCWPairs π E) (q : ℤ) {P Q : CWPair} (f : P ⟶ Q)
    [WeakEquivalence f] :
    IsIso ((E q).map f) :=
  hE.weakEquivalenceInvariant q f

end IsHomologyTheoryOnCWPairs

namespace CWPairHomologyTheory

/-- A bundled `CWPairHomologyTheory` exposes the dimension, exactness, excision, additivity, and
weak-equivalence axioms stated using the canonical `CWPair` operators. -/
theorem spec
    {π : Type u} [AddCommGroup π] (H : CWPairHomologyTheory π) :
    (∀ pt : CWPair, Nonempty (pt ≅ IsCWPair.point) →
      Nonempty ((H 0).obj pt ≅ ModuleCat.of ℤ π)) ∧
      (∀ pt : CWPair, Nonempty (pt ≅ IsCWPair.point) →
        ∀ q : ℤ, q ≠ 0 → IsZero ((H q).obj pt)) ∧
      (∀ q : ℤ, ∀ P : CWPair,
        (CategoryTheory.ShortComplex.mk
          ((H q).map (IsCWPair.subspaceInclusion P))
          ((H q).map (IsCWPair.absoluteToRelative P))
          (H.2.exact₁_zero q P)).Exact) ∧
      (∀ q : ℤ, ∀ P : CWPair,
        (CategoryTheory.ShortComplex.mk
          ((H q).map (IsCWPair.absoluteToRelative P))
          ((H.2.boundary q).app P)
          (H.2.exact₂_zero q P)).Exact) ∧
      (∀ q : ℤ, ∀ P : CWPair,
        (CategoryTheory.ShortComplex.mk
          ((H.2.boundary q).app P)
          ((H (q - 1)).map (IsCWPair.subspaceInclusion P))
          (H.2.exact₃_zero q P)).Exact) ∧
      (∀ q : ℤ, ∀ P : CWPair, ∀ U : Set (IsCWPair.space P),
        ∀ hU : closure U ⊆ interior (IsCWPair.subspace P),
          IsIso ((H q).map (IsCWPair.removeSubsetInclusion P U hU))) ∧
      (∀ {ι : Type u}, ∀ q : ℤ, ∀ P : ι → CWPair,
        Nonempty (((H q).obj (IsCWPair.sigmaPair P)) ≅ ∐ fun i : ι ↦ (H q).obj (P i))) ∧
      (∀ q : ℤ, ∀ {P Q : CWPair} (f : P ⟶ Q),
        [WeakEquivalence f] → IsIso ((H q).map f)) :=
  H.2.spec

/-- Weakly equivalent CW pairs induce isomorphisms on the homology groups of a bundled
`CWPairHomologyTheory`. -/
instance map_isIso_of_weakEquivalence
    {π : Type u} [AddCommGroup π] (H : CWPairHomologyTheory π)
    (q : ℤ) {P Q : CWPair} (f : P ⟶ Q) [WeakEquivalence f] :
    IsIso ((H q).map f) :=
  H.2.weakEquivalenceInvariant q f

end CWPairHomologyTheory

/-- Theorem 13.1.7 (1): the restriction of a Chapter 13 homology theory on all pairs of spaces
to the full subcategory of CW pairs satisfies the source-facing CW-pair homology-theory axioms. -/
instance restrictPairHomologyTheoryToCWPairs_isHomologyTheoryOnCWPairs
    {π : Type u} [AddCommGroup π] (H : PairHomologyTheory π) :
    IsHomologyTheoryOnCWPairs π (restrictPairHomologyTheoryToCWPairs H) where
  boundary q :=
    { app := fun P ↦ (H.boundary q).app (IsCWPair.toSpacePair P)
      naturality := by
        intro P Q f
        simpa [restrictPairHomologyTheoryToCWPairs, IsCWPair.subspaceFunctor] using
          (H.boundary q).naturality f.hom }
  dimensionZero pt hpt := by
    rcases hpt with ⟨e⟩
    let h0 : (restrictPairHomologyTheoryToCWPairs H 0).obj IsCWPair.point ≅ ModuleCat.of ℤ π :=
      Classical.choice H.dimensionZero
    exact ⟨(restrictPairHomologyTheoryToCWPairs H 0).mapIso e ≪≫ h0⟩
  dimensionHigher pt hpt q hq := by
    rcases hpt with ⟨e⟩
    let h0 : IsZero ((restrictPairHomologyTheoryToCWPairs H q).obj IsCWPair.point) :=
      H.dimensionHigher q hq
    exact IsZero.of_iso h0 ((restrictPairHomologyTheoryToCWPairs H q).mapIso e)
  exact₁_zero q P := by
    simpa [restrictPairHomologyTheoryToCWPairs, IsCWPair.subspaceInclusion,
      IsCWPair.absoluteToRelative] using H.exact₁_zero q (IsCWPair.toSpacePair P)
  exact₁ q P := by
    simpa [restrictPairHomologyTheoryToCWPairs, IsCWPair.subspaceInclusion,
      IsCWPair.absoluteToRelative] using H.exact₁ q (IsCWPair.toSpacePair P)
  exact₂_zero q P := by
    simpa [restrictPairHomologyTheoryToCWPairs, IsCWPair.absoluteToRelative] using
      H.exact₂_zero q (IsCWPair.toSpacePair P)
  exact₂ q P := by
    simpa [restrictPairHomologyTheoryToCWPairs, IsCWPair.absoluteToRelative] using
      H.exact₂ q (IsCWPair.toSpacePair P)
  exact₃_zero q P := by
    simpa [restrictPairHomologyTheoryToCWPairs, IsCWPair.subspaceInclusion] using
      H.exact₃_zero q (IsCWPair.toSpacePair P)
  exact₃ q P := by
    simpa [restrictPairHomologyTheoryToCWPairs, IsCWPair.subspaceInclusion] using
      H.exact₃ q (IsCWPair.toSpacePair P)
  excision q P U hU := by
    simpa [restrictPairHomologyTheoryToCWPairs, IsCWPair.removeSubsetInclusion] using
      H.excision q (IsCWPair.toSpacePair P) U hU
  additivity q P := by
    simpa [restrictPairHomologyTheoryToCWPairs, IsCWPair.sigmaPair] using
      H.additivity q fun i ↦ IsCWPair.toSpacePair (P i)
  weakEquivalenceInvariant q {P} {Q} f := by
    intro
    let _ : WeakEquivalence f.hom := inferInstance
    simpa [restrictPairHomologyTheoryToCWPairs] using H.weakEquivalenceInvariant q f.hom

namespace PairHomologyTheory

/-- The bundled CW-pair homology theory obtained by restricting `H` to the full subcategory of
CW pairs. -/
abbrev restrictToCWPairHomologyTheory
    {π : Type u} [AddCommGroup π] (H : PairHomologyTheory π) : CWPairHomologyTheory π :=
  ⟨restrictPairHomologyTheoryToCWPairs H, inferInstance⟩

end PairHomologyTheory

/-- A degreewise natural isomorphism from the restriction of `H` to a source-facing CW-pair
homology theory `E` is comparison-compatible when it identifies the pair-theory boundary square
with the canonical CW-pair boundary on `(A, ∅)`. -/
def HasCWPairTheoryComparison
    {π : Type u} [AddCommGroup π] (H : PairHomologyTheory π)
    {E : ℤ → CWPair ⥤ ModuleCat.{u} ℤ} (hE : IsHomologyTheoryOnCWPairs π E)
    (e : ∀ q : ℤ, restrictPairHomologyTheoryToCWPairs H q ≅ E q) : Prop :=
  ∀ (q : ℤ) (P : CWPair),
    CommSq
      ((e q).hom.app P)
      ((H.boundary q).app (IsCWPair.toSpacePair P))
      ((hE.boundary q).app P)
      ((e (q - 1)).hom.app (IsCWPair.subspacePair P))

/-- A comparison `e` between the restriction of `H` and `E` is boundary-compatible exactly when,
for every degree `q` and CW pair `P`, the corresponding boundary square commutes on the canonical
CW-pair operator `(X, A) ↦ (A, ∅)`. -/
theorem hasCWPairTheoryComparison_boundary_comm
    {π : Type u} [AddCommGroup π] {H : PairHomologyTheory π}
    {E : ℤ → CWPair ⥤ ModuleCat.{u} ℤ} {hE : IsHomologyTheoryOnCWPairs π E}
    {e : ∀ q : ℤ, restrictPairHomologyTheoryToCWPairs H q ≅ E q}
    (he : HasCWPairTheoryComparison H hE e) (q : ℤ) (P : CWPair) :
    ((e q).hom.app P) ≫ (hE.boundary q).app P =
      ((H.boundary q).app (IsCWPair.toSpacePair P)) ≫
        ((e (q - 1)).hom.app (IsCWPair.subspacePair P)) :=
  (he q P).w

/-- A comparison between the restriction of `H` and a source-facing CW-pair homology theory `E`
is boundary-compatible when `E` carries the source-facing CW-pair axioms and the comparison
satisfies `HasCWPairTheoryComparison`. -/
def HasRestrictedCWPairTheoryComparison
    {π : Type u} [AddCommGroup π] (H : PairHomologyTheory π)
    {E : ℤ → CWPair ⥤ ModuleCat.{u} ℤ}
    (e : ∀ q : ℤ, restrictPairHomologyTheoryToCWPairs H q ≅ E q) : Prop :=
  ∃ hE : IsHomologyTheoryOnCWPairs π E, HasCWPairTheoryComparison H hE e

namespace PairHomologyTheory.Iso

/-- An isomorphism of pair homology theories respects two CW-pair comparison isomorphisms when,
after restricting to `CWPair`, it identifies them degreewise. -/
def RespectsCWPairComparison
    {π : Type u} [AddCommGroup π] {H K : PairHomologyTheory π}
    (i : PairHomologyTheory.Iso H K)
    {E : ℤ → CWPair ⥤ ModuleCat.{u} ℤ}
    (eH : ∀ q : ℤ, restrictPairHomologyTheoryToCWPairs H q ≅ E q)
    (eK : ∀ q : ℤ, restrictPairHomologyTheoryToCWPairs K q ≅ E q) : Prop :=
  ∀ q : ℤ,
    Functor.isoWhiskerLeft (CategoryTheory.ObjectProperty.ι IsCWPair) (i.app q) ≪≫ eK q = eH q

end PairHomologyTheory.Iso

namespace IsHomologyTheoryOnCWPairs

/-- A source-facing CW-pair homology theory extends to some Chapter 13 pair homology theory
together with degreewise comparison isomorphisms compatible with its boundary maps, and
that extension is unique up to comparison-respecting isomorphism. -/
def HasPairHomologyTheoryExtension
    {π : Type u} [AddCommGroup π] {E : ℤ → CWPair ⥤ ModuleCat.{u} ℤ}
    (hE : IsHomologyTheoryOnCWPairs π E) : Prop :=
  ∃ H : PairHomologyTheory π,
    ∃ e : ∀ q : ℤ, restrictPairHomologyTheoryToCWPairs H q ≅ E q,
      HasCWPairTheoryComparison H hE e ∧
      ∀ K : PairHomologyTheory π,
        ∀ eK : ∀ q : ℤ, restrictPairHomologyTheoryToCWPairs K q ≅ E q,
          HasCWPairTheoryComparison K hE eK →
            ∃ i : PairHomologyTheory.Iso H K,
              PairHomologyTheory.Iso.RespectsCWPairComparison i e eK

end IsHomologyTheoryOnCWPairs

namespace CWPairHomologyTheory

/-- A bundled CW-pair homology theory extends to some Chapter 13 pair homology theory together
with degreewise comparison isomorphisms compatible with its boundary maps, and that
extension is unique up to comparison-respecting isomorphism. -/
def HasPairHomologyTheoryExtension
    {π : Type u} [AddCommGroup π] (E : CWPairHomologyTheory π) : Prop :=
  IsHomologyTheoryOnCWPairs.HasPairHomologyTheoryExtension E.2

end CWPairHomologyTheory

/-- Theorem 13.1.7 (2): conversely, any graded homology theory on CW pairs extends to a Chapter
13 homology theory on all pairs through CW approximation, and any two such extensions equipped
with boundary-compatible comparison isomorphisms are isomorphic in a way that intertwines the
supplied CW-pair comparison data after restriction. -/
theorem exists_pairHomologyTheory_of_isHomologyTheoryOnCWPairs
    {π : Type u} [AddCommGroup π] (E : ℤ → CWPair ⥤ ModuleCat.{u} ℤ)
    (hE : IsHomologyTheoryOnCWPairs π E) :
    hE.HasPairHomologyTheoryExtension := sorry

/-- A bundled CW-pair homology theory extends to a Chapter 13 homology theory on all pairs, with
restriction back to CW pairs equipped with a graded natural isomorphism that is compatible with
the boundary maps, and any other such extension carries a comparison-respecting
isomorphism from the chosen one. -/
theorem exists_pairHomologyTheory_of_cwPairHomologyTheory
    {π : Type u} [AddCommGroup π] (E : CWPairHomologyTheory π) :
    E.HasPairHomologyTheoryExtension :=
  exists_pairHomologyTheory_of_isHomologyTheoryOnCWPairs E.1 E.2
