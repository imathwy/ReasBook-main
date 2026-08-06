import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap22.Theorem_22_2_1.Representation
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap19.Definition_19_1_2

open CategoryTheory Limits
open HomotopicalAlgebra
open scoped TensorProduct

noncomputable section

local notation "BasedCWComplex" =>
  CategoryTheory.ObjectProperty.FullSubcategory IsBasedCWComplex

-- Semantic recall via `lean_leansearch` surfaced only generic `HSpace` and product-level homotopy
-- infrastructure. Local Chapter 22 precedent now fixes explicit representation data
-- `ReducedCohomologyEilenbergMacLaneRepresentation`, so this file records the represented
-- coefficient pairings directly on those chosen `K(π, n)` models.

/-- The reduced cohomology group `H̃^n(X; π)` on based CW complexes carried by an explicit Chapter
22 representation datum `R`. -/
noncomputable abbrev representedReducedCohomologyGroup
    [CategoryWithCofibrations BasedSpace]
    [CategoryWithCofibrations BasedCWComplex]
    [CategoryWithWeakEquivalences BasedCWComplex]
    {π : Type} [AddCommGroup π] {n : ℕ}
    (R : ReducedCohomologyEilenbergMacLaneRepresentation π n) (X : BasedCWComplex) :
    AddCommGrpCat :=
  ((R.theory.cohomology (n : ℤ)).obj (Opposite.op X))

variable
    [CategoryWithCofibrations BasedSpace]
    [CategoryWithCofibrations BasedCWComplex]
    [CategoryWithWeakEquivalences BasedCWComplex]
    {π ρ σ : Type} [AddCommGroup π] [AddCommGroup ρ] [AddCommGroup σ]
    {p q : ℕ}
    (P : ReducedCohomologyEilenbergMacLaneRepresentation π p)
    (Q : ReducedCohomologyEilenbergMacLaneRepresentation ρ q)
    (S : ReducedCohomologyEilenbergMacLaneRepresentation σ (p + q))

/-- The raw formula on points induced by a represented pairing and two based maps into the chosen
`K(π, p)` and `K(ρ, q)` models. -/
def representedPairingMapFun
    (pairing :
      C((P.space).right ×
          (Q.space).right,
        (S.space).right))
    {X : BasedSpace}
    (f : X ⟶ P.space)
    (g : X ⟶ Q.space) :
    X.right → (S.space).right :=
  fun x ↦ pairing (f.right.hom x, g.right.hom x)

/-- The raw pointwise formula induced by a represented pairing is continuous. -/
theorem representedPairingMapFun_continuous
    (pairing :
      C((P.space).right ×
          (Q.space).right,
        (S.space).right))
    {X : BasedSpace}
    (f : X ⟶ P.space)
    (g : X ⟶ Q.space) :
    Continuous (representedPairingMapFun P Q S pairing f g) := sorry

/-- The continuous map on underlying spaces induced by a represented pairing and two based maps
into the chosen representing spaces. -/
def representedPairingContinuousMap
    (pairing :
      C((P.space).right ×
          (Q.space).right,
        (S.space).right))
    {X : BasedSpace}
    (f : X ⟶ P.space)
    (g : X ⟶ Q.space) :
    C(X.right, (S.space).right) :=
  ⟨representedPairingMapFun P Q S pairing f g,
    representedPairingMapFun_continuous P Q S pairing f g⟩

/-- The continuous map induced by a represented pairing preserves the chosen basepoint. -/
theorem representedPairingContinuousMap_w
    (pairing :
      C((P.space).right ×
          (Q.space).right,
        (S.space).right))
    (map_basepoint :
      pairing
          (underTopBasepoint (P.space),
            underTopBasepoint (Q.space)) =
        underTopBasepoint (S.space))
    {X : BasedSpace}
    (f : X ⟶ P.space)
    (g : X ⟶ Q.space) :
    X.hom ≫ TopCat.ofHom (representedPairingContinuousMap P Q S pairing f g) =
      (S.space).hom := sorry

/-- A represented pairing turns a pair of based maps
`X ⟶ K(π, p)` and `X ⟶ K(ρ, q)` into a based map `X ⟶ K(σ, p + q)`. -/
def representedPairingMap
    (pairing :
      C((P.space).right ×
          (Q.space).right,
        (S.space).right))
    (map_basepoint :
      pairing
          (underTopBasepoint (P.space),
            underTopBasepoint (Q.space)) =
        underTopBasepoint (S.space))
    {X : BasedSpace}
    (f : X ⟶ P.space)
    (g : X ⟶ Q.space) :
    X ⟶ S.space :=
  Under.homMk
    (TopCat.ofHom (representedPairingContinuousMap P Q S pairing f g))
    (representedPairingContinuousMap_w P Q S pairing map_basepoint f g)

/-- The pairing induced by a represented pairing respects based homotopies in both variables. -/
theorem representedPairingMap_wellDefined
    (pairing :
      C((P.space).right ×
          (Q.space).right,
        (S.space).right))
    (map_basepoint :
      pairing
          (underTopBasepoint (P.space),
            underTopBasepoint (Q.space)) =
        underTopBasepoint (S.space))
    {X : BasedSpace}
    {f₀ f₁ : X ⟶ P.space}
    {g₀ g₁ : X ⟶ Q.space}
    (hf : (basedHomotopySetoid X (P.space)).r f₀ f₁)
    (hg : (basedHomotopySetoid X (Q.space)).r g₀ g₁) :
    (basedHomotopySetoid X (S.space)).r
      (representedPairingMap P Q S pairing map_basepoint f₀ g₀)
      (representedPairingMap P Q S pairing map_basepoint f₁ g₁) := sorry

/-- A represented pairing descends to a degreewise operation on based homotopy classes with values
in the chosen `K(σ, p + q)` model. -/
def representedPairingOnBasedHomotopyClasses
    (pairing :
      C((P.space).right ×
          (Q.space).right,
        (S.space).right))
    (map_basepoint :
      pairing
          (underTopBasepoint (P.space),
            underTopBasepoint (Q.space)) =
        underTopBasepoint (S.space))
    (X : BasedSpace) :
    basedHomotopyClasses X (P.space) →
      basedHomotopyClasses X (Q.space) →
        basedHomotopyClasses X (S.space) :=
  Quotient.map₂
    (fun f g ↦ representedPairingMap P Q S pairing map_basepoint f g)
    (fun _ _ hf _ _ hg ↦ representedPairingMap_wellDefined P Q S pairing map_basepoint hf hg)

/-- The raw formula on points induced by a represented cap-side pairing and two based maps into
the chosen `K(π, p)` and `K(σ, p + q)` models. -/
def representedCapPairingMapFun
    (pairing :
      C((P.space).right ×
          (S.space).right,
        (Q.space).right))
    {X : BasedSpace}
    (f : X ⟶ P.space)
    (g : X ⟶ S.space) :
    X.right → (Q.space).right :=
  fun x ↦ pairing (f.right.hom x, g.right.hom x)

/-- The raw pointwise formula induced by a represented cap-side pairing is continuous. -/
theorem representedCapPairingMapFun_continuous
    (pairing :
      C((P.space).right ×
          (S.space).right,
        (Q.space).right))
    {X : BasedSpace}
    (f : X ⟶ P.space)
    (g : X ⟶ S.space) :
    Continuous (representedCapPairingMapFun P Q S pairing f g) := sorry

/-- The continuous map on underlying spaces induced by a represented cap-side pairing and two
based maps into the chosen representing spaces. -/
def representedCapPairingContinuousMap
    (pairing :
      C((P.space).right ×
          (S.space).right,
        (Q.space).right))
    {X : BasedSpace}
    (f : X ⟶ P.space)
    (g : X ⟶ S.space) :
    C(X.right, (Q.space).right) :=
  ⟨representedCapPairingMapFun P Q S pairing f g,
    representedCapPairingMapFun_continuous P Q S pairing f g⟩

/-- The continuous map induced by a represented cap-side pairing preserves the chosen basepoint. -/
theorem representedCapPairingContinuousMap_w
    (pairing :
      C((P.space).right ×
          (S.space).right,
        (Q.space).right))
    (map_basepoint :
      pairing
          (underTopBasepoint (P.space),
            underTopBasepoint (S.space)) =
        underTopBasepoint (Q.space))
    {X : BasedSpace}
    (f : X ⟶ P.space)
    (g : X ⟶ S.space) :
    X.hom ≫ TopCat.ofHom (representedCapPairingContinuousMap P Q S pairing f g) =
      (Q.space).hom := sorry

/-- A represented cap-side pairing turns a pair of based maps
`X ⟶ K(π, p)` and `X ⟶ K(σ, p + q)` into a based map `X ⟶ K(ρ, q)`. -/
def representedCapPairingMap
    (pairing :
      C((P.space).right ×
          (S.space).right,
        (Q.space).right))
    (map_basepoint :
      pairing
          (underTopBasepoint (P.space),
            underTopBasepoint (S.space)) =
        underTopBasepoint (Q.space))
    {X : BasedSpace}
    (f : X ⟶ P.space)
    (g : X ⟶ S.space) :
    X ⟶ Q.space :=
  Under.homMk
    (TopCat.ofHom (representedCapPairingContinuousMap P Q S pairing f g))
    (representedCapPairingContinuousMap_w P Q S pairing map_basepoint f g)

/-- The pairing induced by a represented cap-side pairing respects based homotopies in both
variables. -/
theorem representedCapPairingMap_wellDefined
    (pairing :
      C((P.space).right ×
          (S.space).right,
        (Q.space).right))
    (map_basepoint :
      pairing
          (underTopBasepoint (P.space),
            underTopBasepoint (S.space)) =
        underTopBasepoint (Q.space))
    {X : BasedSpace}
    {f₀ f₁ : X ⟶ P.space}
    {g₀ g₁ : X ⟶ S.space}
    (hf : (basedHomotopySetoid X (P.space)).r f₀ f₁)
    (hg : (basedHomotopySetoid X (S.space)).r g₀ g₁) :
    (basedHomotopySetoid X (Q.space)).r
      (representedCapPairingMap P Q S pairing map_basepoint f₀ g₀)
      (representedCapPairingMap P Q S pairing map_basepoint f₁ g₁) := sorry

/-- A represented cap-side pairing descends to a degreewise operation on based homotopy classes
with values in the chosen `K(ρ, q)` model. -/
def representedCapPairingOnBasedHomotopyClasses
    (pairing :
      C((P.space).right ×
          (S.space).right,
        (Q.space).right))
    (map_basepoint :
      pairing
          (underTopBasepoint (P.space),
            underTopBasepoint (S.space)) =
        underTopBasepoint (Q.space))
    (X : BasedSpace) :
    basedHomotopyClasses X (P.space) →
      basedHomotopyClasses X (S.space) →
        basedHomotopyClasses X (Q.space) :=
  Quotient.map₂
    (fun f g ↦ representedCapPairingMap P Q S pairing map_basepoint f g)
    (fun _ _ hf _ _ hg ↦ representedCapPairingMap_wellDefined P Q S pairing map_basepoint hf hg)

/-- Construction 22.3.1 (1). Coefficient multiplication `μ : π →+ ρ →+ σ` determines a
represented cup product, namely a bilinear family on represented reduced cohomology together with
a concrete based pairing among the chosen `K(π, p)`, `K(ρ, q)`, and `K(σ, p + q)` models that
represents this operation under Theorem 22.2.1. -/
structure RepresentedCupProduct
    (P : ReducedCohomologyEilenbergMacLaneRepresentation π p)
    (Q : ReducedCohomologyEilenbergMacLaneRepresentation ρ q)
    (S : ReducedCohomologyEilenbergMacLaneRepresentation σ (p + q))
    (μ : π →+ ρ →+ σ) where
  /-- The coefficient multiplication whose represented cup product is being packaged. -/
  coefficientMultiplication : π →+ ρ →+ σ
  /-- This represented cup product is attached to the ambient coefficient multiplication `μ`. -/
  coefficientMultiplication_eq : coefficientMultiplication = μ
  /-- The bilinear family on represented reduced cohomology corresponding to coefficient
  multiplication `μ`. -/
  cupProduct :
    ∀ X : BasedCWComplex,
      representedReducedCohomologyGroup P X ⊗[ℤ]
        representedReducedCohomologyGroup Q X →ₗ[ℤ]
          representedReducedCohomologyGroup S X
  /-- The concrete represented pairing among the chosen `K(π, p)`, `K(ρ, q)`, and
  `K(σ, p + q)` models. -/
  pairing :
    C((P.space).right ×
        (Q.space).right,
      (S.space).right)
  /-- The represented pairing sends the pair of chosen basepoints to the chosen basepoint. -/
  map_basepoint :
    pairing
        (underTopBasepoint (P.space),
          underTopBasepoint (Q.space)) =
      underTopBasepoint (S.space)
  /-- Under Theorem 22.2.1, the induced operation on based homotopy classes recovers the
  represented cup product attached to `μ`. -/
  cupProduct_spec :
    ∀ (X : BasedCWComplex)
      (α : representedReducedCohomologyGroup P X)
      (β : representedReducedCohomologyGroup Q X),
      representedPairingOnBasedHomotopyClasses P Q S pairing map_basepoint X.1
          (((P.comparison).app
              (Opposite.op X)).hom.toFun α)
          (((Q.comparison).app
              (Opposite.op X)).hom.toFun β) =
        (((S.comparison).app
            (Opposite.op X)).hom.toFun
          (cupProduct X (TensorProduct.tmul ℤ α β)))

/-- Construction 22.3.1 (2). Coefficient multiplication `μ : π →+ ρ →+ σ` determines a
represented cap product, namely a cap-side bilinear family on represented reduced cohomology
together with a concrete basepoint-preserving pairing among the chosen `K(π, p)`,
`K(σ, p + q)`, and `K(ρ, q)` models that represents this operation under Theorem 22.2.1. -/
structure RepresentedCapProduct
    (P : ReducedCohomologyEilenbergMacLaneRepresentation π p)
    (Q : ReducedCohomologyEilenbergMacLaneRepresentation ρ q)
    (S : ReducedCohomologyEilenbergMacLaneRepresentation σ (p + q))
    (μ : π →+ ρ →+ σ) where
  /-- The coefficient multiplication whose represented cap product is being packaged. -/
  coefficientMultiplication : π →+ ρ →+ σ
  /-- This represented cap product is attached to the ambient coefficient multiplication `μ`. -/
  coefficientMultiplication_eq : coefficientMultiplication = μ
  /-- The cap-side pairing on the chosen representing spaces
  `K(π, p) × K(σ, p + q) → K(ρ, q)`. -/
  pairing :
    C((P.space).right ×
        (S.space).right,
      (Q.space).right)
  /-- The represented cap-side pairing sends the pair of chosen basepoints to the chosen
  basepoint. -/
  map_basepoint :
    pairing
        (underTopBasepoint (P.space),
          underTopBasepoint (S.space)) =
          underTopBasepoint (Q.space)
  /-- The bilinear family on represented reduced cohomology corresponding on the cap side to
  `μ`. -/
  capProduct :
    ∀ X : BasedCWComplex,
      representedReducedCohomologyGroup P X ⊗[ℤ]
        representedReducedCohomologyGroup S X →ₗ[ℤ]
          representedReducedCohomologyGroup Q X
  /-- Under Theorem 22.2.1, the induced cap-side operation on based homotopy classes recovers the
  represented cap product attached to `μ`. -/
  capProduct_spec :
    ∀ (X : BasedCWComplex)
      (α : representedReducedCohomologyGroup P X)
      (γ : representedReducedCohomologyGroup S X),
      representedCapPairingOnBasedHomotopyClasses P Q S pairing map_basepoint X.1
          (((P.comparison).app
              (Opposite.op X)).hom.toFun α)
          (((S.comparison).app
              (Opposite.op X)).hom.toFun γ) =
        (((Q.comparison).app
            (Opposite.op X)).hom.toFun
          (capProduct X (TensorProduct.tmul ℤ α γ)))

/-- A represented cup product coerces to its underlying pointwise pairing. -/
instance
    :
    CoeFun (RepresentedCupProduct P Q S μ)
      (fun _ ↦
        (P.space).right ×
          (Q.space).right →
            (S.space).right) where
  coe cup := cup.pairing

/-- Evaluating a represented cup product as a function recovers its underlying pointwise
pairing. -/
@[simp] theorem RepresentedCupProduct.coe_apply
    (cup : RepresentedCupProduct P Q S μ)
    (x :
      (P.space).right ×
        (Q.space).right) :
    cup x = cup.pairing x := sorry

/-- A represented cup product turns a pair of based maps into the chosen `K(π, p)` and
`K(ρ, q)` models into a based map to `K(σ, p + q)`. -/
def RepresentedCupProduct.pairingMap
    (cup : RepresentedCupProduct P Q S μ)
    {X : BasedSpace}
    (f : X ⟶ P.space)
    (g : X ⟶ Q.space) :
    X ⟶ S.space :=
  representedPairingMap P Q S cup.pairing cup.map_basepoint f g

/-- A represented cup product induces the corresponding operation on based homotopy classes. -/
def RepresentedCupProduct.onBasedHomotopyClasses
    (cup : RepresentedCupProduct P Q S μ)
    (X : BasedSpace) :
    basedHomotopyClasses X (P.space) →
      basedHomotopyClasses X (Q.space) →
        basedHomotopyClasses X (S.space) :=
  representedPairingOnBasedHomotopyClasses P Q S cup.pairing cup.map_basepoint X

/-- A represented cap product coerces to its underlying pointwise pairing on
`K(π, p) × K(σ, p + q)`. -/
instance
    :
    CoeFun (RepresentedCapProduct P Q S μ)
      (fun _ ↦
        (P.space).right ×
          (S.space).right →
            (Q.space).right) where
  coe cap := cap.pairing

/-- Evaluating a represented cap product as a function recovers its underlying pointwise
pairing. -/
@[simp] theorem RepresentedCapProduct.coe_apply
    (cap : RepresentedCapProduct P Q S μ)
    (x :
      (P.space).right ×
        (S.space).right) :
    cap x = cap.pairing x := sorry

/-- A represented cap product turns a pair of based maps into the chosen `K(π, p)` and
`K(σ, p + q)` models into a based map to `K(ρ, q)`. -/
def RepresentedCapProduct.pairingMap
    (cap : RepresentedCapProduct P Q S μ)
    {X : BasedSpace}
    (f : X ⟶ P.space)
    (g : X ⟶ S.space) :
    X ⟶ Q.space :=
  representedCapPairingMap P Q S cap.pairing cap.map_basepoint f g

/-- A represented cap product induces the corresponding cap-side operation on based homotopy
classes. -/
def RepresentedCapProduct.onBasedHomotopyClasses
    (cap : RepresentedCapProduct P Q S μ)
    (X : BasedSpace) :
    basedHomotopyClasses X (P.space) →
      basedHomotopyClasses X (S.space) →
        basedHomotopyClasses X (Q.space) :=
  representedCapPairingOnBasedHomotopyClasses P Q S cap.pairing cap.map_basepoint X
