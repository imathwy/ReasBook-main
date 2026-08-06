import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap19.Definition_19_1_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap19.Problem_19_6_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap14.Theorem_14_2_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits AddCommGrpCat
open scoped TensorProduct

noncomputable section

universe u v

-- Semantic recall via `lean_leansearch` only surfaced unrelated sheaf-theoretic
-- Mayer-Vietoris APIs, so this item is stated abstractly from the local owners
-- `RelativeCupProductMap`, `reducedCohomology`, and explicit quotient-model identifications.

/-- An isomorphism in `AddCommGrpCat` gives the corresponding `ℤ`-linear equivalence of the
underlying groups. -/
private abbrev intLinearMapOfHom {A B : AddCommGrpCat} (f : A ⟶ B) : A →ₗ[ℤ] B :=
  f.hom.toIntLinearMap

/-- An isomorphism in `AddCommGrpCat` gives the corresponding `ℤ`-linear equivalence of the
underlying groups. -/
private noncomputable def addCommGrpCatIsoToLinearEquiv
    {A B : AddCommGrpCat} (e : A ≅ B) : A ≃ₗ[ℤ] B where
  toLinearMap := intLinearMapOfHom e.hom
  invFun := e.inv.hom
  left_inv x := by
    exact congrArg (fun f ↦ f x) e.hom_inv_id
  right_inv x := by
    exact congrArg (fun f ↦ f x) e.inv_hom_id

/-- A chosen quotient model `XS` for collapsing `S ⊆ X` to the basepoint, built on the canonical
Chapter 14 quotient owner `ReducedQuotientMap X S XS`, together with the cohomological content
that makes the quotient-induced map on a chosen Chapter 18 pair cohomology theory an isomorphism.
For any concrete relative theory `E` equipped with a comparison to `pairTheory`, the actual
identification `E q X S ≃ₗ[ℤ] Ẽ^q(XS)` is derived from this owner. -/
structure ReducedQuotientIdentification
    {π : Type u} [AddCommGroup π] (pairTheory : PairCohomologyTheory π)
    (X : TopCat.{u}) (S : Set X)
    (XS : BasedSpace) where
  /-- The chosen based quotient model, expressed through the canonical Chapter 14 owner. -/
  quotientModel : ReducedQuotientMap X S XS
  /-- The quotient-induced cohomology map
  `H̃^q(XS; π) ⟶ H^q(X, S; π)` is an isomorphism in every degree. -/
  cohomologyMap_isIso : ∀ q : ℤ, IsIso ((pairTheory q).map quotientModel.pairMap.op)

namespace ReducedQuotientIdentification

/-- The quotient map of pairs induced by the chosen reduced quotient model. -/
abbrev pairMap
    {π : Type u} [AddCommGroup π] {pairTheory : PairCohomologyTheory π}
    {X : TopCat.{u}} {S : Set X} {XS : BasedSpace}
    (Q : ReducedQuotientIdentification pairTheory X S XS) :
    subsetPair X S ⟶ basedReducedPair XS :=
  Q.quotientModel.pairMap

instance instCohomologyMapIsIso
    {π : Type u} [AddCommGroup π] {pairTheory : PairCohomologyTheory π}
    {X : TopCat.{u}} {S : Set X} {XS : BasedSpace}
    (Q : ReducedQuotientIdentification pairTheory X S XS) (q : ℤ) :
    IsIso ((pairTheory q).map Q.pairMap.op) :=
  Q.cohomologyMap_isIso q

/-- The quotient map from `X` to the chosen based quotient model `XS`. -/
abbrev quotientMap
    {π : Type u} [AddCommGroup π] {pairTheory : PairCohomologyTheory π}
    {X : TopCat.{u}} {S : Set X} {XS : BasedSpace}
    (Q : ReducedQuotientIdentification pairTheory X S XS) :
    X ⟶ XS.right :=
  Q.quotientModel.quotientMap

/-- Every point of `S` is sent to the basepoint of `XS`. -/
@[simp] theorem quotientMap_eq_basepoint
    {π : Type u} [AddCommGroup π] {pairTheory : PairCohomologyTheory π}
    {X : TopCat.{u}} {S : Set X} {XS : BasedSpace}
    (Q : ReducedQuotientIdentification pairTheory X S XS)
    {x : X} (hx : x ∈ S) :
    Q.quotientMap.hom x = underTopBasepoint XS :=
  ReducedQuotientMap.quotientMap_eq_basepoint Q.quotientModel hx

/-- The collapsed subset for a quotient identification is nonempty, as recorded by the underlying
Chapter 14 quotient owner. -/
abbrev subspaceNonempty
    {π : Type u} [AddCommGroup π] {pairTheory : PairCohomologyTheory π}
    {X : TopCat.{u}} {S : Set X} {XS : BasedSpace}
    (Q : ReducedQuotientIdentification pairTheory X S XS) :
    S.Nonempty :=
  Q.quotientModel.subspace_nonempty

/-- The chosen quotient model is canonically identified with the Chapter 14 collapse quotient
`collapseSubsetBasedSpace X S Q.subspaceNonempty`. -/
def collapseSubsetBasedSpaceIso
    {π : Type u} [AddCommGroup π] {pairTheory : PairCohomologyTheory π}
    {X : TopCat.{u}} {S : Set X} {XS : BasedSpace}
    (Q : ReducedQuotientIdentification pairTheory X S XS) :
    XS ≅ collapseSubsetBasedSpace X S Q.subspaceNonempty :=
  Q.quotientModel.collapseSubsetBasedSpaceIso

/-- The quotient-induced cohomology isomorphism for the underlying pair cohomology theory. -/
noncomputable abbrev pairTheoryComparison
    {π : Type u} [AddCommGroup π] {pairTheory : PairCohomologyTheory π}
    {X : TopCat.{u}} {S : Set X} {XS : BasedSpace}
    (Q : ReducedQuotientIdentification pairTheory X S XS) (q : ℤ) :
    pairTheory.relativeCohomology q X S ≃ₗ[ℤ]
      reducedCohomology pairTheory.relativeCohomology q XS :=
  addCommGrpCatIsoToLinearEquiv
    (asIso ((pairTheory q).map Q.pairMap.op)).symm

/-- Any chosen comparison from `E` to the pair theory `pairTheory` turns the quotient-induced
pair-theory isomorphism into the corresponding reduced-cohomology comparison for `E`. -/
noncomputable def comparison
    {π : Type u} [AddCommGroup π] {pairTheory : PairCohomologyTheory π}
    {E : ℤ → (Y : TopCat) → Set Y → Type v}
    [∀ q (Y : TopCat) (S : Set Y), AddCommGroup (E q Y S)]
    [∀ q (Y : TopCat) (S : Set Y), Module ℤ (E q Y S)]
    {X : TopCat.{u}} {S : Set X} {XS : BasedSpace}
    (Q : ReducedQuotientIdentification pairTheory X S XS)
    (theoryIso :
      ∀ q : ℤ, ∀ Y : TopCat.{u}, ∀ T : Set Y,
        E q Y T ≃ₗ[ℤ] pairTheory.relativeCohomology q Y T)
    (q : ℤ) :
    E q X S ≃ₗ[ℤ] reducedCohomology E q XS :=
  (theoryIso q X S).trans <|
    (Q.pairTheoryComparison q).trans <|
      (theoryIso q XS.right ({underTopBasepoint XS} : Set XS.right)).symm

/-- The tensor-product comparison induced by the quotient-identification comparisons for `A` and
`B`. -/
noncomputable def tensorComparison
    {π : Type u} [AddCommGroup π] {pairTheory : PairCohomologyTheory π}
    {E : ℤ → (Y : TopCat) → Set Y → Type v}
    [∀ q (Y : TopCat) (S : Set Y), AddCommGroup (E q Y S)]
    [∀ q (Y : TopCat) (S : Set Y), Module ℤ (E q Y S)]
    {X : TopCat.{u}} {A B : Set X}
    {XA XB : BasedSpace}
    (idA : ReducedQuotientIdentification pairTheory X A XA)
    (theoryIso :
      ∀ q : ℤ, ∀ Y : TopCat.{u}, ∀ T : Set Y,
        E q Y T ≃ₗ[ℤ] pairTheory.relativeCohomology q Y T)
    (idB : ReducedQuotientIdentification pairTheory X B XB)
    (p q : ℤ) :
    E p X A ⊗[ℤ] E q X B ≃ₗ[ℤ]
      reducedCohomology E p XA ⊗[ℤ] reducedCohomology E q XB where
  toLinearMap :=
    TensorProduct.map
      (idA.comparison theoryIso p).toLinearMap
      (idB.comparison theoryIso q).toLinearMap
  invFun :=
    TensorProduct.map
      (idA.comparison theoryIso p).symm.toLinearMap
      (idB.comparison theoryIso q).symm.toLinearMap
  left_inv z := by
    refine TensorProduct.induction_on z ?_ ?_ ?_
    · simp
    · intro x y
      simp [comparison]
    · intro z z' hz hz'
      simpa using congrArg₂ (· + ·) hz hz'
  right_inv z := by
    refine TensorProduct.induction_on z ?_ ?_ ?_
    · simp
    · intro x y
      simp [comparison]
    · intro z z' hz hz'
      simpa using congrArg₂ (· + ·) hz hz'

@[simp] theorem symm_tensorComparison_apply
    {π : Type u} [AddCommGroup π] {pairTheory : PairCohomologyTheory π}
    {E : ℤ → (Y : TopCat) → Set Y → Type v}
    [∀ q (Y : TopCat) (S : Set Y), AddCommGroup (E q Y S)]
    [∀ q (Y : TopCat) (S : Set Y), Module ℤ (E q Y S)]
    {X : TopCat.{u}} {A B : Set X}
    {XA XB : BasedSpace}
    (idA : ReducedQuotientIdentification pairTheory X A XA)
    (theoryIso :
      ∀ q : ℤ, ∀ Y : TopCat.{u}, ∀ T : Set Y,
        E q Y T ≃ₗ[ℤ] pairTheory.relativeCohomology q Y T)
    (idB : ReducedQuotientIdentification pairTheory X B XB)
    (p q : ℤ)
    (z : E p X A ⊗[ℤ] E q X B) :
    (idA.tensorComparison theoryIso idB p q).symm
        ((idA.tensorComparison theoryIso idB p q) z) = z := by
  exact LinearEquiv.symm_apply_apply (idA.tensorComparison theoryIso idB p q) z

@[simp] theorem tensorComparison_symm_apply
    {π : Type u} [AddCommGroup π] {pairTheory : PairCohomologyTheory π}
    {E : ℤ → (Y : TopCat) → Set Y → Type v}
    [∀ q (Y : TopCat) (S : Set Y), AddCommGroup (E q Y S)]
    [∀ q (Y : TopCat) (S : Set Y), Module ℤ (E q Y S)]
    {X : TopCat.{u}} {A B : Set X}
    {XA XB : BasedSpace}
    (idA : ReducedQuotientIdentification pairTheory X A XA)
    (theoryIso :
      ∀ q : ℤ, ∀ Y : TopCat.{u}, ∀ T : Set Y,
        E q Y T ≃ₗ[ℤ] pairTheory.relativeCohomology q Y T)
    (idB : ReducedQuotientIdentification pairTheory X B XB)
    (p q : ℤ)
    (z : reducedCohomology E p XA ⊗[ℤ] reducedCohomology E q XB) :
    (idA.tensorComparison theoryIso idB p q)
        ((idA.tensorComparison theoryIso idB p q).symm z) = z := by
  exact LinearEquiv.apply_symm_apply (idA.tensorComparison theoryIso idB p q) z

@[simp] theorem symm_tensorComparison_comp
    {π : Type u} [AddCommGroup π] {pairTheory : PairCohomologyTheory π}
    {E : ℤ → (Y : TopCat) → Set Y → Type v}
    [∀ q (Y : TopCat) (S : Set Y), AddCommGroup (E q Y S)]
    [∀ q (Y : TopCat) (S : Set Y), Module ℤ (E q Y S)]
    {X : TopCat.{u}} {A B : Set X}
    {XA XB : BasedSpace}
    (idA : ReducedQuotientIdentification pairTheory X A XA)
    (theoryIso :
      ∀ q : ℤ, ∀ Y : TopCat.{u}, ∀ T : Set Y,
        E q Y T ≃ₗ[ℤ] pairTheory.relativeCohomology q Y T)
    (idB : ReducedQuotientIdentification pairTheory X B XB)
    (p q : ℤ) :
    ((idA.tensorComparison theoryIso idB p q).symm.toLinearMap).comp
        ((idA.tensorComparison theoryIso idB p q).toLinearMap) = LinearMap.id := by
  exact (idA.tensorComparison theoryIso idB p q).symm_comp

@[simp] theorem tensorComparison_comp_symm
    {π : Type u} [AddCommGroup π] {pairTheory : PairCohomologyTheory π}
    {E : ℤ → (Y : TopCat) → Set Y → Type v}
    [∀ q (Y : TopCat) (S : Set Y), AddCommGroup (E q Y S)]
    [∀ q (Y : TopCat) (S : Set Y), Module ℤ (E q Y S)]
    {X : TopCat.{u}} {A B : Set X}
    {XA XB : BasedSpace}
    (idA : ReducedQuotientIdentification pairTheory X A XA)
    (theoryIso :
      ∀ q : ℤ, ∀ Y : TopCat.{u}, ∀ T : Set Y,
        E q Y T ≃ₗ[ℤ] pairTheory.relativeCohomology q Y T)
    (idB : ReducedQuotientIdentification pairTheory X B XB)
    (p q : ℤ) :
    ((idA.tensorComparison theoryIso idB p q).toLinearMap).comp
        ((idA.tensorComparison theoryIso idB p q).symm.toLinearMap) = LinearMap.id := by
  exact (idA.tensorComparison theoryIso idB p q).comp_symm

end ReducedQuotientIdentification

/-- The reduced cup product induced from the relative cup product by the chosen quotient-model
identifications for `A`, `B`, and `A ∪ B`, derived from the quotient-induced cohomology
isomorphisms in `pairTheory` and the chosen comparison from `E` to `pairTheory`. -/
noncomputable def reducedCupProduct
    {π : Type u} [AddCommGroup π]
    (pairTheory : PairCohomologyTheory π)
    (E : ℤ → (Y : TopCat) → Set Y → Type v)
    [∀ q (Y : TopCat) (S : Set Y), AddCommGroup (E q Y S)]
    [∀ q (Y : TopCat) (S : Set Y), Module ℤ (E q Y S)]
    (theoryIso :
      ∀ q : ℤ, ∀ Y : TopCat.{u}, ∀ S : Set Y,
        E q Y S ≃ₗ[ℤ] pairTheory.relativeCohomology q Y S)
    (cupProduct : RelativeCupProductMap E)
    (X : TopCat.{u}) (A B : Set X)
    {XA XB XAuB : BasedSpace}
    (idA : ReducedQuotientIdentification pairTheory X A XA)
    (idB : ReducedQuotientIdentification pairTheory X B XB)
    (idAuB : ReducedQuotientIdentification pairTheory X (A ∪ B) XAuB)
    (p q : ℤ) :
    reducedCohomology E p XA ⊗[ℤ] reducedCohomology E q XB →ₗ[ℤ]
      reducedCohomology E (p + q) XAuB :=
  (idAuB.comparison theoryIso (p + q)).toLinearMap.comp <|
    (cupProduct A B p q).comp <|
      (idA.tensorComparison theoryIso idB p q).symm.toLinearMap

/-- Problem 19.6.3. The relative cup product for `(X, A)` and `(X, B)` induces the corresponding
reduced-cohomology diagram after identifying the relative groups with reduced cohomology of
quotient models for `X/A`, `X/B`, and `X/(A ∪ B)` via the quotient-induced cohomology
isomorphisms in a chosen pair theory, so the induced square commutes. -/
theorem reducedCupProductDiagram
    {π : Type u} [AddCommGroup π]
    (pairTheory : PairCohomologyTheory π)
    (E : ℤ → (Y : TopCat) → Set Y → Type v)
    [∀ q (Y : TopCat) (S : Set Y), AddCommGroup (E q Y S)]
    [∀ q (Y : TopCat) (S : Set Y), Module ℤ (E q Y S)]
    (theoryIso :
      ∀ q : ℤ, ∀ Y : TopCat.{u}, ∀ S : Set Y,
        E q Y S ≃ₗ[ℤ] pairTheory.relativeCohomology q Y S)
    (cupProduct : RelativeCupProductMap E)
    (X : TopCat.{u}) (A B : Set X)
    {XA XB XAuB : BasedSpace}
    (idA : ReducedQuotientIdentification pairTheory X A XA)
    (idB : ReducedQuotientIdentification pairTheory X B XB)
    (idAuB : ReducedQuotientIdentification pairTheory X (A ∪ B) XAuB)
    (p q : ℤ) :
    (reducedCupProduct pairTheory E theoryIso cupProduct X A B idA idB idAuB p q).comp
        (idA.tensorComparison theoryIso idB p q).toLinearMap =
      (idAuB.comparison theoryIso (p + q)).toLinearMap.comp (cupProduct A B p q) := by
  simp only [reducedCupProduct, LinearMap.comp_assoc,
    ReducedQuotientIdentification.symm_tensorComparison_comp, LinearMap.comp_id]

/-- The induced square from `reducedCupProductDiagram` commutes on every tensor-product element. -/
theorem reducedCupProductDiagram_apply
    {π : Type u} [AddCommGroup π]
    (pairTheory : PairCohomologyTheory π)
    (E : ℤ → (Y : TopCat) → Set Y → Type v)
    [∀ q (Y : TopCat) (S : Set Y), AddCommGroup (E q Y S)]
    [∀ q (Y : TopCat) (S : Set Y), Module ℤ (E q Y S)]
    (theoryIso :
      ∀ q : ℤ, ∀ Y : TopCat.{u}, ∀ S : Set Y,
        E q Y S ≃ₗ[ℤ] pairTheory.relativeCohomology q Y S)
    (cupProduct : RelativeCupProductMap E)
    (X : TopCat.{u}) (A B : Set X)
    {XA XB XAuB : BasedSpace}
    (idA : ReducedQuotientIdentification pairTheory X A XA)
    (idB : ReducedQuotientIdentification pairTheory X B XB)
    (idAuB : ReducedQuotientIdentification pairTheory X (A ∪ B) XAuB)
    (p q : ℤ) (z : E p X A ⊗[ℤ] E q X B) :
    reducedCupProduct pairTheory E theoryIso cupProduct X A B idA idB idAuB p q
        ((idA.tensorComparison theoryIso idB p q).toLinearMap z) =
      (idAuB.comparison theoryIso (p + q)) ((cupProduct A B p q) z) := by
  simpa using
    LinearMap.congr_fun
      (reducedCupProductDiagram pairTheory E theoryIso cupProduct X A B idA idB idAuB p q) z
