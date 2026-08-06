import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap06.Definition_6_1_4
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap13.CollapseSubsetPair
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap14.Construction_14_1_3
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap14.SubsetPair

open CategoryTheory
open SpacePair

noncomputable section

universe u

-- Semantic recall via `lean_leansearch` did not surface a source-exact quotient-homology owner.
-- Local Chapter 6/13/14 precedent already fixes `IsCofibration`, `PairHomologyTheory`, and
-- `basedReducedHomology`, so the main statement is stated on the canonical collapse quotient
-- `collapseSubsetType X A` with its collapsed point, and arbitrary quotient models `XA` are kept
-- only as transport companions.

/-- The canonical based quotient `(X/A, *)`, where the basepoint is the image of the collapsed
subspace `A`. -/
def collapseSubsetBasedSpace (X : TopCat.{u}) (A : Set X) (hA : A.Nonempty) :
    BasedSpace :=
  Under.mk
    (TopCat.terminalIsoPUnit.hom ≫
      TopCat.ofHom (ContinuousMap.const PUnit (collapseSubsetPoint A hA)))

/-- The chosen basepoint of `collapseSubsetBasedSpace X A hA` is the collapsed point of `A`. -/
@[simp] theorem collapseSubsetBasedSpace_basepoint
    (X : TopCat.{u}) (A : Set X) (hA : A.Nonempty) :
    underTopBasepoint (collapseSubsetBasedSpace X A hA) = collapseSubsetPoint A hA := sorry

/-- The canonical pair `(X / A, *)` is isomorphic to the reduced pair of
`collapseSubsetBasedSpace X A hA`. -/
def collapseSubsetPairIsoBasedReducedPair
    (X : TopCat.{u}) (A : Set X) (hA : A.Nonempty) :
    collapseSubsetPair A hA ≅ basedReducedPair (collapseSubsetBasedSpace X A hA) where
  hom :=
    { hom := 𝟙 (TopCat.of (collapseSubsetType X A))
      map_subspace' := by
        intro q hq
        change q = underTopBasepoint (collapseSubsetBasedSpace X A hA)
        change q = collapseSubsetPoint A hA at hq
        simpa using hq }
  inv :=
    { hom := 𝟙 (TopCat.of (collapseSubsetType X A))
      map_subspace' := by
        intro q hq
        change q = collapseSubsetPoint A hA
        change q = underTopBasepoint (collapseSubsetBasedSpace X A hA) at hq
        simpa using hq }
  hom_inv_id := by
    apply SpacePair.hom_ext
    rfl
  inv_hom_id := by
    apply SpacePair.hom_ext
    rfl

/-- The canonical quotient pair map, followed by the based-space bridge to
`collapseSubsetBasedSpace X A hA`. -/
def collapseSubsetBasedPairMap
    (X : TopCat.{u}) (A : Set X) (hA : A.Nonempty) :
    subsetPair X A ⟶ basedReducedPair (collapseSubsetBasedSpace X A hA) :=
  collapseSubsetPairMap A hA ≫ (collapseSubsetPairIsoBasedReducedPair X A hA).hom

/-- A chosen quotient map from `X` to a based quotient model `XA` collapsing `A ⊆ X`
to the basepoint, together with the minimal comparison data identifying `XA` with the canonical
quotient `X/A`. The basepoint-collapse and subspace facts are derived companion theorems.
-/
structure ReducedQuotientMap (X : TopCat.{u}) (A : Set X) (XA : BasedSpace) where
  /-- The collapse map `X ⟶ XA.right`. -/
  quotientMap : X ⟶ XA.right
  /-- The collapsed subset is nonempty, so `X/A` carries the distinguished basepoint coming from
  the image of `A`. -/
  subspace_nonempty : A.Nonempty
  /-- A chosen homeomorphism from the quotient model `XA` to the canonical collapse quotient
  `collapseSubsetType X A`. -/
  quotientHomeomorph : XA.right ≃ₜ collapseSubsetType X A
  /-- The chosen quotient model map is identified with the canonical collapse quotient map. -/
  quotientMap_eq (x : X) :
    quotientHomeomorph (quotientMap.hom x) = collapseSubsetQuotientMap A x
  /-- The chosen basepoint of `XA` corresponds to the collapsed point of `A` in `X/A`. -/
  basepoint_eq :
    quotientHomeomorph (underTopBasepoint XA) = collapseSubsetPoint A subspace_nonempty

/-- Every point of `A` is sent to the basepoint of `XA`. -/
@[simp] theorem ReducedQuotientMap.quotientMap_eq_basepoint
    {X : TopCat.{u}} {A : Set X} {XA : BasedSpace} (Q : ReducedQuotientMap X A XA)
    {x : X} (hx : x ∈ A) :
    Q.quotientMap.hom x = underTopBasepoint XA :=
  Q.quotientHomeomorph.injective <| by
    rw [Q.quotientMap_eq x, Q.basepoint_eq]
    simpa using collapseSubsetQuotientMap_eq_point A Q.subspace_nonempty ⟨x, hx⟩

/-- The quotient map of `ReducedQuotientMap` sends the chosen subspace into the singleton
basepoint subspace. -/
@[simp] theorem ReducedQuotientMap.mapsSubspace
    {X : TopCat.{u}} {A : Set X} {XA : BasedSpace} (Q : ReducedQuotientMap X A XA)
    {x : X} (hx : x ∈ A) :
    Q.quotientMap.hom x ∈ ({underTopBasepoint XA} : Set XA.right) := by
  change Q.quotientMap.hom x = underTopBasepoint XA
  exact Q.quotientMap_eq_basepoint hx

/-- A `ReducedQuotientMap` identifies the chosen quotient model `XA` with the canonical based
quotient `collapseSubsetBasedSpace X A Q.subspace_nonempty`. -/
def ReducedQuotientMap.collapseSubsetBasedSpaceIso
    {X : TopCat.{u}} {A : Set X} {XA : BasedSpace} (Q : ReducedQuotientMap X A XA) :
    XA ≅ collapseSubsetBasedSpace X A Q.subspace_nonempty :=
  Under.isoMk (TopCat.isoOfHomeo Q.quotientHomeomorph) <| by
    ext x
    have hx : x = TopCat.terminalIsoPUnit.inv PUnit.unit := by
      have hx' : x = TopCat.terminalIsoPUnit.inv (TopCat.terminalIsoPUnit.hom x) := by
        exact (congrArg (fun f ↦ f x) TopCat.terminalIsoPUnit.hom_inv_id).symm
      calc
        x = TopCat.terminalIsoPUnit.inv (TopCat.terminalIsoPUnit.hom x) := hx'
        _ = TopCat.terminalIsoPUnit.inv PUnit.unit := by
          exact congrArg TopCat.terminalIsoPUnit.inv <| by
            cases TopCat.terminalIsoPUnit.hom x
            rfl
    rw [hx]
    simpa [collapseSubsetBasedSpace, underTopBasepoint] using Q.basepoint_eq

/-- The quotient map `X ⟶ XA.right` induces a map of pairs `(X, A) ⟶ (XA.right, {underTopBasepoint
XA})`. -/
def ReducedQuotientMap.pairMap
    {X : TopCat.{u}} {A : Set X} {XA : BasedSpace} (Q : ReducedQuotientMap X A XA) :
    subsetPair X A ⟶ basedReducedPair XA where
  hom := Q.quotientMap
  map_subspace' := by
    intro x hx
    exact Q.mapsSubspace hx

section

variable {π : Type u} [AddCommGroup π]

/-- The homology morphism induced by the canonical quotient map of pairs
`(X, A) ⟶ (X/A, *)`. -/
abbrev cofibrationQuotientHomologyMap
    (H : PairHomologyTheory π) (q : ℤ)
    {X : TopCat.{u}} {A : Set X} (hA : A.Nonempty) :
    pairHomologyGroup H q X A →+ basedReducedHomology H q (collapseSubsetBasedSpace X A hA) :=
  ((H.homology q).map (collapseSubsetBasedPairMap X A hA)).hom.toAddMonoidHom

/-- Theorem 14.2.1: if `i : A ↪ X` is a cofibration and `A` is nonempty so that the collapse
quotient carries its canonical basepoint `*`, then the quotient map of pairs
`(X, A) ⟶ (collapseSubsetType X A, {collapseSubsetPoint A hA})` induces a bijection
`E_q(X, A) ⟶ Ẽ_q(collapseSubsetBasedSpace X A hA)` in every degree `q`. -/
theorem cofibrationQuotientHomologyMap_bijective
    (H : PairHomologyTheory π) (q : ℤ)
    {X : TopCat.{u}} {A : Set X}
    (hA : A.Nonempty)
    (hi : IsCofibration (subsetInclusion A)) :
    Function.Bijective (cofibrationQuotientHomologyMap H q hA) := sorry

/-- The quotient map of a cofibration induces an isomorphism on the corresponding homology
objects. -/
instance cofibrationQuotientHomologyMap_isIso
    (H : PairHomologyTheory π) (q : ℤ)
    {X : TopCat.{u}} {A : Set X}
    (hA : A.Nonempty)
    (hi : IsCofibration (subsetInclusion A)) :
    IsIso ((H.homology q).map (collapseSubsetBasedPairMap X A hA)) := sorry

/-- The homology morphism induced by a chosen quotient model `XA` equipped with a
`ReducedQuotientMap X A XA`. -/
abbrev reducedQuotientMapHomologyMap
    (H : PairHomologyTheory π) (q : ℤ)
    {X : TopCat.{u}} {A : Set X} {XA : BasedSpace} (Q : ReducedQuotientMap X A XA) :
    pairHomologyGroup H q X A →+ basedReducedHomology H q XA :=
  ((H.homology q).map Q.pairMap).hom.toAddMonoidHom

/-- A `ReducedQuotientMap X A XA` transports Theorem 14.2.1 from the canonical quotient
`collapseSubsetBasedSpace X A Q.subspace_nonempty` to the chosen based quotient model `XA`. -/
theorem reducedQuotientMapHomologyMap_bijective
    (H : PairHomologyTheory π) (q : ℤ)
    {X : TopCat.{u}} {A : Set X} {XA : BasedSpace}
    (Q : ReducedQuotientMap X A XA)
    (hi : IsCofibration (subsetInclusion A)) :
    Function.Bijective (reducedQuotientMapHomologyMap H q Q) := sorry

/-- A `ReducedQuotientMap X A XA` also yields an isomorphism on the corresponding homology
objects for the chosen based quotient model `XA`. -/
instance reducedQuotientMapHomologyMap_isIso
    (H : PairHomologyTheory π) (q : ℤ)
    {X : TopCat.{u}} {A : Set X} {XA : BasedSpace}
    (Q : ReducedQuotientMap X A XA)
    (hi : IsCofibration (subsetInclusion A)) :
    IsIso ((H.homology q).map Q.pairMap) := sorry

end
