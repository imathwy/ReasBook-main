import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap22.ModTwoSingularCohomology

open CategoryTheory
open scoped BigOperators

noncomputable section

/-- The chosen ambient ordinary mod-`2` cohomology theory on `TopCat`, together with its degree-zero
unit class, cup product, and explicit compatibility data with Chapter 22 mod-`2` singular
cohomology. -/
structure ModTwoCohomologyTheory where
  /-- The degreewise mod-`2` cohomology functor. -/
  cohomology : ℕ → TopCatᵒᵖ ⥤ AddCommGrpCat
  /-- The degree-zero unit class. -/
  oneClass : ∀ B : TopCat, (cohomology 0).obj (Opposite.op B)
  /-- The cup product on mod-`2` cohomology classes. -/
  cup :
    ∀ {p q : ℕ} {B : TopCat},
      (cohomology p).obj (Opposite.op B) →
        (cohomology q).obj (Opposite.op B) →
        (cohomology (p + q)).obj (Opposite.op B)
  /-- The pullback map on Chapter 22 mod-`2` singular cohomology induced by a map of spaces. -/
  singularMap :
    ∀ {B B' : TopCat} (_ : B' ⟶ B) (n : ℕ),
      modTwoSingularCohomology B n ⟶ modTwoSingularCohomology B' n
  /-- The degree-zero unit class on Chapter 22 mod-`2` singular cohomology. -/
  singularOneClass : ∀ B : TopCat, modTwoSingularCohomology B 0
  /-- The cup product on Chapter 22 mod-`2` singular cohomology. -/
  singularCup :
    ∀ {p q : ℕ} {B : TopCat},
      modTwoSingularCohomology B p →
        modTwoSingularCohomology B q →
        modTwoSingularCohomology B (p + q)
  /-- The chosen ambient theory is identified degreewise with Chapter 22 mod-`2` singular
  cohomology. -/
  comparison :
    ∀ (n : ℕ) (B : TopCat),
      (cohomology n).obj (Opposite.op B) ≅
        (forget₂ (ModuleCat ℤ) AddCommGrpCat).obj (modTwoSingularCohomology B n)
  /-- The chosen comparisons are natural in the base space. -/
  comparison_natural :
    ∀ {B B' : TopCat} (f : B' ⟶ B) (n : ℕ),
      ((cohomology n).map f.op) ≫ (comparison n B').hom =
        (comparison n B).hom ≫
          (forget₂ (ModuleCat ℤ) AddCommGrpCat).map (singularMap f n)
  /-- The chosen comparisons carry the ambient unit class to the Chapter 22 unit class. -/
  comparison_oneClass :
    ∀ B : TopCat,
      (comparison 0 B).hom (oneClass B) = singularOneClass B
  /-- The chosen comparisons carry the ambient cup product to the Chapter 22 cup product. -/
  comparison_cup :
    ∀ {p q : ℕ} {B : TopCat}
      (x : (cohomology p).obj (Opposite.op B))
      (y : (cohomology q).obj (Opposite.op B)),
      (comparison (p + q) B).hom (cup x y) =
        singularCup ((comparison p B).hom x) ((comparison q B).hom y)

/-- The degree-`n` mod-`2` cohomology group of `X` in the chosen ambient theory `H2`. -/
abbrev modTwoCohomologyGroup (H2 : ModTwoCohomologyTheory) (n : ℕ) (X : TopCat) :=
  (H2.cohomology n).obj (Opposite.op X)

/-- Pullback in degree `n` on the chosen ambient mod-`2` cohomology theory `H2`. -/
abbrev modTwoCohomologyPullback (H2 : ModTwoCohomologyTheory) {X Y : TopCat} (f : X ⟶ Y) (n : ℕ) :
    modTwoCohomologyGroup H2 n Y ⟶ modTwoCohomologyGroup H2 n X :=
  (H2.cohomology n).map f.op

/-- The target degree in the Cartan expansion agrees with the target degree of `Sq^n` on
`H^(p + q)(X; ZMod 2)`. -/
theorem steenrodCartanDegree (p q n : ℕ) (i : Fin (n + 1)) :
    (p + i) + (q + (n - i)) = (p + q) + n := sorry

/-- The target degree in the Adem expansion agrees with the target degree of `Sq^i ∘ Sq^j`. -/
theorem steenrodAdemDegree (i j q : ℕ) (k : Fin (i / 2 + 1)) :
    (q + k) + (i + j - k) = (q + j) + i := sorry

/-- The target degree of `Sq^n` after one suspension agrees with the suspension of the target
degree. -/
theorem steenrodSuspensionDegree (q n : ℕ) :
    (q + 1) + n = (q + n) + 1 := sorry

/-- A family of Steenrod square operations on the chosen ambient mod-`2` cohomology theory `H2`.
The current ordinary-cohomology owner records the source-side stability relative to fixed
suspension data and the corresponding compatibility law for the degreewise operations
`sq n q : H^q(X; ZMod 2) → H^(q + n)(X; ZMod 2)`. -/
structure SteenrodSquareFamily
    (H2 : ModTwoCohomologyTheory)
    (suspension : TopCat ⥤ TopCat)
    (suspensionIso : ∀ q : ℕ, suspension.op ⋙ H2.cohomology (q + 1) ≅ H2.cohomology q) where
  /-- The operation `Sq^n : H^q(X; ZMod 2) → H^(q + n)(X; ZMod 2)`. -/
  sq :
    ∀ (n q : ℕ) (X : TopCat),
      modTwoCohomologyGroup H2 q X ⟶ modTwoCohomologyGroup H2 (q + n) X
  /-- Each `Sq^n` is stable with respect to the chosen suspension isomorphisms. -/
  stable :
    ∀ (n q : ℕ) (X : TopCat),
      (suspensionIso q).hom.app (Opposite.op X) ≫ sq n q X =
        sq n (q + 1) (suspension.obj X) ≫
          eqToHom
            (congrArg
              (fun m ↦ modTwoCohomologyGroup H2 m (suspension.obj X))
              (steenrodSuspensionDegree q n)) ≫
            (suspensionIso (q + n)).hom.app (Opposite.op X)
  /-- The Steenrod squares commute with pullback along maps of spaces. -/
  naturality :
    ∀ {X Y : TopCat} (f : X ⟶ Y) (n q : ℕ),
      modTwoCohomologyPullback H2 f q ≫ sq n q X =
        sq n q Y ≫ modTwoCohomologyPullback H2 f (q + n)
  /-- `Sq^0` is the identity in every degree. -/
  sq_zero :
    ∀ (q : ℕ) (X : TopCat), sq 0 q X = 𝟙 (modTwoCohomologyGroup H2 q X)
  /-- The top square of a degree-`q` class is its cup square. -/
  top_square :
    ∀ (q : ℕ) (X : TopCat) (x : modTwoCohomologyGroup H2 q X),
      sq q q X x = H2.cup x x
  /-- `Sq^n` vanishes on `H^q(X; ZMod 2)` when `q < n`. -/
  vanishing :
    ∀ (n q : ℕ) (X : TopCat), q < n → sq n q X = 0
  /-- The Cartan formula holds for cup products. -/
  cartan :
    ∀ (n p q : ℕ) (X : TopCat)
      (x : modTwoCohomologyGroup H2 p X)
      (y : modTwoCohomologyGroup H2 q X),
      sq n (p + q) X (H2.cup x y) =
        ∑ i : Fin (n + 1),
          cast
            (by
              simpa using
                congrArg
                  (fun m ↦ ((modTwoCohomologyGroup H2 m X) : Type))
                  (steenrodCartanDegree p q n i))
            (H2.cup (sq i p X x) (sq (n - i) q X y))
  /-- The Adem relations hold in the standard mod-`2` parity form. -/
  adem :
    ∀ (i j q : ℕ) (X : TopCat) (_ : i < 2 * j)
      (x : modTwoCohomologyGroup H2 q X),
      sq i (q + j) X (sq j q X x) =
        ∑ k : Fin (i / 2 + 1),
          if Nat.choose (j - k - 1) (i - 2 * k) % 2 = 1 then
            cast
              (by
                simpa using
                  congrArg
                    (fun m ↦ ((modTwoCohomologyGroup H2 m X) : Type))
                    (steenrodAdemDegree i j q k))
              (sq (i + j - k) (q + k) X (sq k q X x))
          else 0

namespace SteenrodSquareFamily

/-- The stability clause says that each `Sq^n` commutes with the chosen suspension isomorphisms of
the ambient mod-`2` cohomology theory. -/
theorem stability_spec
    {H2 : ModTwoCohomologyTheory}
    {suspension : TopCat ⥤ TopCat}
    {suspensionIso : ∀ q : ℕ, suspension.op ⋙ H2.cohomology (q + 1) ≅ H2.cohomology q}
    (Sq : SteenrodSquareFamily H2 suspension suspensionIso) :
    ∀ (n q : ℕ) (X : TopCat),
      (suspensionIso q).hom.app (Opposite.op X) ≫ Sq.sq n q X =
        Sq.sq n (q + 1) (suspension.obj X) ≫
          eqToHom
            (congrArg
              (fun m ↦ modTwoCohomologyGroup H2 m (suspension.obj X))
              (steenrodSuspensionDegree q n)) ≫
            (suspensionIso (q + n)).hom.app (Opposite.op X) := sorry

/-- The normalization clauses for a Steenrod-square family consist of the identity operation in
degree `0`, the top-square formula, and vanishing above the cohomological degree. -/
theorem normalization_spec
    {H2 : ModTwoCohomologyTheory}
    {suspension : TopCat ⥤ TopCat}
    {suspensionIso : ∀ q : ℕ, suspension.op ⋙ H2.cohomology (q + 1) ≅ H2.cohomology q}
    (Sq : SteenrodSquareFamily H2 suspension suspensionIso) :
    (∀ (q : ℕ) (X : TopCat), Sq.sq 0 q X = 𝟙 (modTwoCohomologyGroup H2 q X)) ∧
      (∀ (q : ℕ) (X : TopCat) (x : modTwoCohomologyGroup H2 q X),
        Sq.sq q q X x = H2.cup x x) ∧
      (∀ (n q : ℕ) (X : TopCat), q < n → Sq.sq n q X = 0) := sorry

/-- The multiplicative axioms for a Steenrod-square family are the Cartan formula and the Adem
relations. -/
theorem product_spec
    {H2 : ModTwoCohomologyTheory}
    {suspension : TopCat ⥤ TopCat}
    {suspensionIso : ∀ q : ℕ, suspension.op ⋙ H2.cohomology (q + 1) ≅ H2.cohomology q}
    (Sq : SteenrodSquareFamily H2 suspension suspensionIso) :
    (∀ (n p q : ℕ) (X : TopCat)
      (x : modTwoCohomologyGroup H2 p X)
      (y : modTwoCohomologyGroup H2 q X),
      Sq.sq n (p + q) X (H2.cup x y) =
        ∑ i : Fin (n + 1),
          cast
            (by
              simpa using
                congrArg
                  (fun m ↦ ((modTwoCohomologyGroup H2 m X) : Type))
                  (steenrodCartanDegree p q n i))
            (H2.cup (Sq.sq i p X x) (Sq.sq (n - i) q X y))) ∧
      (∀ (i j q : ℕ) (X : TopCat) (_ : i < 2 * j)
        (x : modTwoCohomologyGroup H2 q X),
        Sq.sq i (q + j) X (Sq.sq j q X x) =
          ∑ k : Fin (i / 2 + 1),
            if Nat.choose (j - k - 1) (i - 2 * k) % 2 = 1 then
              cast
                (by
                  simpa using
                    congrArg
                      (fun m ↦ ((modTwoCohomologyGroup H2 m X) : Type))
                      (steenrodAdemDegree i j q k))
                (Sq.sq (i + j - k) (q + k) X (Sq.sq k q X x))
            else 0) := sorry

/-- A Steenrod-square family on a chosen ambient mod-`2` cohomology theory induces a singular
operation after transporting along the theory's comparison isomorphisms with Chapter 22
mod-`2` singular cohomology. -/
abbrev singularSq
    {H2 : ModTwoCohomologyTheory}
    {suspension : TopCat ⥤ TopCat}
    {suspensionIso : ∀ q : ℕ, suspension.op ⋙ H2.cohomology (q + 1) ≅ H2.cohomology q}
    (Sq : SteenrodSquareFamily H2 suspension suspensionIso)
    (i n : ℕ) (X : TopCat) :
    (forget₂ (ModuleCat ℤ) AddCommGrpCat).obj (modTwoSingularCohomology X n) ⟶
      (forget₂ (ModuleCat ℤ) AddCommGrpCat).obj (modTwoSingularCohomology X (n + i)) :=
  (H2.comparison n X).inv ≫ Sq.sq i n X ≫ (H2.comparison (n + i) X).hom

end SteenrodSquareFamily
