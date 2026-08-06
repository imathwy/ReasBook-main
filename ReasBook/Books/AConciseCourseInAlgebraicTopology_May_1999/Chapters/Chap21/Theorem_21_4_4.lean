import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap18.Definition_18_3_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap14.SubsetPair
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap21.Proposition_21_4_3

open CategoryTheory SpacePair
open scoped Manifold Topology

noncomputable section

section

variable (n : ℕ)
variable [NeZero n]
variable (M : Type) [TopologicalSpace M]
variable [ChartedSpace (EuclideanHalfSpace n) M]

/-- The `SpacePair` owner for the pair `(M, ∂M)`, realized by the canonical boundary subset
`M \ interior(M) = ((𝓡∂ n).interior M)ᶜ`. -/
abbrev manifoldBoundaryPair : SpacePair :=
  subsetPair (TopCat.of M) (((𝓡∂ n).interior M)ᶜ)

end

/-- The degree-`q` cohomology group of the canonical pair `(M, ∂M)` in the chosen pair
cohomology theory. -/
abbrev boundaryRelativeCohomology
    {R : Type} [CommRing R] (Hcoh : PairCohomologyTheory R) (q : ℤ) (n : ℕ)
    [NeZero n] (M : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace n) M] : AddCommGrpCat :=
  (Hcoh.cohomology q).obj (Opposite.op (manifoldBoundaryPair n M))

/- The source-facing cohomology notation depends in Lean on the chosen pair cohomology theory
`Hcoh : PairCohomologyTheory R`. The relative notation is only available for the canonical pair
`(M, ∂M)`: the macro accepts `H^q(M, ∂M; Hcoh, n)` and rejects a mismatched displayed boundary
term instead of silently discarding it. -/
notation3 "H^" q "(" M "; " H ")" =>
  (PairCohomologyTheory.absoluteCohomology H q).obj (Opposite.op (TopCat.of M))

syntax "H^" term "(" term ", " "∂" term "; " term ", " term ")" : term

macro_rules
  | `(H^$q($M, ∂$N; $H, $n)) =>
      if M.raw == N.raw then
        `(boundaryRelativeCohomology $H $q $n $M)
      else
        Lean.Macro.throwUnsupported

/-- The target `H_(n - p)(M; R)` for the second relative-duality morphism, viewed in
`AddCommGrpCat` so it can be compared directly with the pair-cohomology source. -/
abbrev singularHomologyGroup (R : Type) [CommRing R] (n : ℕ)
    (M : Type) [TopologicalSpace M] (p : ℕ) : AddCommGrpCat :=
  AddCommGrpCat.of (rSingularHomology R (n - p) (TopCat.of M))

/-- The target `H_(n - p)(M, ∂M; R)` for the first relative-duality morphism, viewed in
`AddCommGrpCat` so it can be compared directly with the pair-cohomology source. -/
abbrev boundaryRelativeSingularHomologyGroup (R : Type) [CommRing R]
    (n : ℕ) [NeZero n] (M : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace n) M] (p : ℕ) : AddCommGrpCat :=
  AddCommGrpCat.of (relativeTopHomologyGroup R (n - p) M ((𝓡∂ n).interior M))

/-- The codomain of the absolute-relative cap-product pairing in degree `p`, viewed as the
additive group of homomorphisms `H_n(M, ∂M; R) → H_(n - p)(M, ∂M; R)`. -/
abbrev absoluteToRelativeCapTarget (R : Type) [CommRing R]
    (n : ℕ) [NeZero n] (M : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace n) M] (p : ℕ) : AddCommGrpCat :=
  AddCommGrpCat.of
    (H[n](M, ∂M; R) →+ boundaryRelativeSingularHomologyGroup R n M p)

/-- The codomain of the relative-absolute cap-product pairing in degree `p`, viewed as the
additive group of homomorphisms `H_n(M, ∂M; R) → H_(n - p)(M; R)`. -/
abbrev relativeToAbsoluteCapTarget (R : Type) [CommRing R]
    (n : ℕ) [NeZero n] (M : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace n) M] (p : ℕ) : AddCommGrpCat :=
  AddCommGrpCat.of (H[n](M, ∂M; R) →+ singularHomologyGroup R n M p)

/-- Evaluation at `z ∈ H_n(M, ∂M; R)` turns a curried cap-product pairing into the corresponding
degree-`p` duality morphism. -/
abbrev evalAtBoundaryRelativeClass
    {R : Type} [CommRing R] {n : ℕ} [NeZero n] {M : Type} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace n) M] (z : H[n](M, ∂M; R)) (A : AddCommGrpCat) :
    AddCommGrpCat.of (H[n](M, ∂M; R) →+ A) ⟶ A :=
  AddCommGrpCat.ofHom
    { toFun := fun f ↦ f z
      map_zero' := rfl
      map_add' := by
        intro f g
        rfl }

/-- A chosen source-facing realization of the two cap-product pairings used in
Theorem 21.4.4. Evaluation at a boundary-relative class `z ∈ H_n(M, ∂M; R)` is imposed only when
forming the induced duality morphisms. -/
structure BoundaryRelativeCapProduct
    {R : Type} [CommRing R] (Hcoh : PairCohomologyTheory R)
    (n : ℕ) [NeZero n] (M : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace n) M] where
  /-- The absolute-relative cap-product pairing
  `H^p(M; R) ⟶ Hom(H_n(M, ∂M; R), H_(n - p)(M, ∂M; R))`. -/
  absolutePairing (p : ℕ) :
    H^(p : ℤ)(M; Hcoh) ⟶ absoluteToRelativeCapTarget R n M p
  /-- The relative-absolute cap-product pairing
  `H^p(M, ∂M; R) ⟶ Hom(H_n(M, ∂M; R), H_(n - p)(M; R))`. -/
  relativePairing (p : ℕ) :
    H^(p : ℤ)(M, ∂M; Hcoh, n) ⟶ relativeToAbsoluteCapTarget R n M p

/-- The degree-`p` morphism `H^p(M; R) ⟶ H_(n - p)(M, ∂M; R)` obtained by evaluating the
absolute-relative cap-product pairing at `z ∈ H_n(M, ∂M; R)`. -/
abbrev boundaryRelativeAbsoluteToRelativeMap
    {R : Type} [CommRing R] {Hcoh : PairCohomologyTheory R}
    {n : ℕ} [NeZero n] {M : Type} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace n) M] (z : H[n](M, ∂M; R))
    (capProduct : BoundaryRelativeCapProduct Hcoh n M)
    (p : ℕ) :
    H^(p : ℤ)(M; Hcoh) ⟶ boundaryRelativeSingularHomologyGroup R n M p :=
  capProduct.absolutePairing p ≫
    evalAtBoundaryRelativeClass z (boundaryRelativeSingularHomologyGroup R n M p)

/-- The degree-`p` morphism `H^p(M, ∂M; R) ⟶ H_(n - p)(M; R)` obtained by evaluating the
relative-absolute cap-product pairing at `z ∈ H_n(M, ∂M; R)`. -/
abbrev boundaryRelativeRelativeToAbsoluteMap
    {R : Type} [CommRing R] {Hcoh : PairCohomologyTheory R}
    {n : ℕ} [NeZero n] {M : Type} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace n) M] (z : H[n](M, ∂M; R))
    (capProduct : BoundaryRelativeCapProduct Hcoh n M)
    (p : ℕ) :
    H^(p : ℤ)(M, ∂M; Hcoh, n) ⟶ singularHomologyGroup R n M p :=
  capProduct.relativePairing p ≫
    evalAtBoundaryRelativeClass z (singularHomologyGroup R n M p)

/-- Unfolding `boundaryRelativeAbsoluteToRelativeMap z capProduct p` gives the degree-`p`
absolute-relative cap-product pairing from `capProduct` composed with evaluation at `z`. -/
theorem boundaryRelativeAbsoluteToRelativeMap_def
    {R : Type} [CommRing R] {Hcoh : PairCohomologyTheory R}
    {n : ℕ} [NeZero n] {M : Type} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace n) M] (z : H[n](M, ∂M; R))
    (capProduct : BoundaryRelativeCapProduct Hcoh n M)
    (p : ℕ) :
    boundaryRelativeAbsoluteToRelativeMap z capProduct p =
      capProduct.absolutePairing p ≫
        evalAtBoundaryRelativeClass z (boundaryRelativeSingularHomologyGroup R n M p) :=
  rfl

/-- Unfolding `boundaryRelativeRelativeToAbsoluteMap z capProduct p` gives the degree-`p`
relative-absolute cap-product pairing from `capProduct` composed with evaluation at `z`. -/
theorem boundaryRelativeRelativeToAbsoluteMap_def
    {R : Type} [CommRing R] {Hcoh : PairCohomologyTheory R}
    {n : ℕ} [NeZero n] {M : Type} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace n) M] (z : H[n](M, ∂M; R))
    (capProduct : BoundaryRelativeCapProduct Hcoh n M)
    (p : ℕ) :
    boundaryRelativeRelativeToAbsoluteMap z capProduct p =
      capProduct.relativePairing p ≫
        evalAtBoundaryRelativeClass z (singularHomologyGroup R n M p) :=
  rfl

/-- A source-facing pair of cap-product pairings realizes boundary-relative Poincare duality for
`z` when `z` is boundary-relative fundamental and the induced canonical degreewise maps are
isomorphisms. -/
class IsBoundaryRelativePoincareDualityMap
    {R : Type} [CommRing R] {Hcoh : PairCohomologyTheory R}
    {n : ℕ} [NeZero n] {M : Type} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace n) M] (z : H[n](M, ∂M; R))
    (capProduct : BoundaryRelativeCapProduct Hcoh n M) : Prop where
  /-- A boundary-relative duality family is only defined from a boundary-relative fundamental
  class. -/
  isBoundaryRelativeFundamentalClassFor : IsBoundaryRelativeFundamentalClassFor z
  /-- The absolute-relative cap-product maps induced by evaluating at `z` are degreewise
  isomorphisms. -/
  absoluteToRelative_isIso (p : ℕ) :
    IsIso (boundaryRelativeAbsoluteToRelativeMap z capProduct p)
  /-- The relative-absolute cap-product maps induced by evaluating at `z` are degreewise
  isomorphisms. -/
  relativeToAbsolute_isIso (p : ℕ) :
    IsIso (boundaryRelativeRelativeToAbsoluteMap z capProduct p)

section

variable {R : Type} [CommRing R]
variable {Hcoh : PairCohomologyTheory R}
variable {n : ℕ}
variable [NeZero n]
variable {M : Type} [TopologicalSpace M]
variable [ChartedSpace (EuclideanHalfSpace n) M]
variable {z : H[n](M, ∂M; R)}
variable (capProduct : BoundaryRelativeCapProduct Hcoh n M)

/-- The absolute-to-relative cap-with-`z` morphism is an isomorphism in each degree. This is the
automation-facing first clause of Theorem 21.4.4. -/
instance boundaryRelativeAbsoluteToRelativeMap_isIso
    (hD : IsBoundaryRelativePoincareDualityMap z capProduct)
    (p : ℕ) :
    IsIso (boundaryRelativeAbsoluteToRelativeMap z capProduct p) :=
  hD.absoluteToRelative_isIso p

/-- The relative-to-absolute cap-with-`z` morphism is an isomorphism in each degree. This is the
automation-facing second clause of Theorem 21.4.4. -/
instance boundaryRelativeRelativeToAbsoluteMap_isIso
    (hD : IsBoundaryRelativePoincareDualityMap z capProduct)
    (p : ℕ) :
    IsIso (boundaryRelativeRelativeToAbsoluteMap z capProduct p) :=
  hD.relativeToAbsolute_isIso p

end

section

variable {R : Type} [CommRing R]
variable {Hcoh : PairCohomologyTheory R}
variable {n : ℕ}
variable [NeZero n]
variable {M : Type} [TopologicalSpace M]
variable [ChartedSpace (EuclideanHalfSpace n) M]

/-- Theorem 21.4.4. If a chosen source-facing realization of the boundary-relative cap-product
pairings for `z ∈ H_n(M, ∂M; R)` realizes boundary-relative Poincare duality, then the canonical
degree-`p` maps obtained by evaluating those pairings at `z` are isomorphisms. -/
theorem relativePoincareDuality
    (z : H[n](M, ∂M; R))
    (capProduct : BoundaryRelativeCapProduct Hcoh n M)
    (hD : IsBoundaryRelativePoincareDualityMap z capProduct)
    (p : ℕ) :
    IsIso (boundaryRelativeAbsoluteToRelativeMap z capProduct p) ∧
      IsIso (boundaryRelativeRelativeToAbsoluteMap z capProduct p) := by
  constructor
  · exact
      boundaryRelativeAbsoluteToRelativeMap_isIso
        capProduct hD p
  · exact
      boundaryRelativeRelativeToAbsoluteMap_isIso
        capProduct hD p

end
