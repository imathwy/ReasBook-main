import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.AlgebraicTopology.TopologicalSimplex
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap16.Definition_16_1_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap16.Definition_16_1_3
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap18.Construction_18_2_2

open CategoryTheory Limits AlgebraicTopology Simplicial
open scoped TensorProduct

noncomputable section

universe u

-- Construction 18.2.2 already fixes `singularCochainComplex R X` as the canonical Chapter 18
-- owner for singular cochains. This file keeps the source-facing simplexwise surface by exposing
-- the degreewise identification with functions on singular simplices.

/-- Source-facing simplexwise model for degree-`n` singular cochains on `X`. It is identified
below with the degree-`n` term of the canonical `linearYonedaObj` cochain complex from
Construction 18.2.2. -/
abbrev singularCochains (R : Type u) [CommRing R] (X : TopCat.{u}) (n : ℕ) : ModuleCat.{u} R :=
  ModuleCat.of.{u} R (singularSimplex n X → R)

/-- The degree-`n` term of the singular chain complex of `X` with coefficients in the constant
`R`-module `R`. -/
abbrev singularChainDegree (R : Type u) [CommRing R] (X : TopCat.{u}) (n : ℕ) :
    ModuleCat.{u} R :=
  ((((singularChainComplexFunctor (ModuleCat.{u} R)).obj (ModuleCat.of.{u} R R)).obj X).X n)

/-- The `n`-simplices of the singular simplicial set of `X`. -/
abbrev singularSSetSimplex (X : TopCat.{u}) (n : ℕ) : Type u :=
  (TopCat.toSSet.obj X) _⦋n⦌

/-- The degree-`n` singular chains are canonically the coproduct of one copy of `R` for each
`n`-simplex in the singular simplicial set of `X`. -/
noncomputable def singularChainDegreeIsoSSetCoproduct
    (R : Type u) [CommRing R] (X : TopCat.{u}) (n : ℕ) :
    singularChainDegree R X n ≅
      ∐ fun _ : singularSSetSimplex X n ↦ ModuleCat.of.{u} R R :=
  eqToIso rfl

/-- The degree-`n` singular chains are canonically the coproduct of one copy of `R` for each
singular `n`-simplex of `X`. -/
noncomputable def singularChainDegreeIsoCoproduct
    (R : Type u) [CommRing R] (X : TopCat.{u}) (n : ℕ) :
    singularChainDegree R X n ≅
      ∐ fun _ : singularSimplex n X ↦ ModuleCat.of.{u} R R :=
  singularChainDegreeIsoSSetCoproduct R X n ≪≫
    show (∐ fun _ : singularSSetSimplex X n ↦ ModuleCat.of.{u} R R) ≅
        ∐ fun _ : singularSimplex n X ↦ ModuleCat.of.{u} R R from
      Limits.Sigma.whiskerEquiv (singularSimplexEquiv n X)
        (fun _ ↦ Iso.refl (ModuleCat.of.{u} R R))

private noncomputable def singularCoproductHomEquiv
    (R : Type u) [CommRing R] (A : Type u) :
    ((∐ fun _ : A ↦ ModuleCat.of.{u} R R) ⟶ ModuleCat.of.{u} R R) ≃ₗ[R] (A → R) where
  toFun φ a := φ ((Limits.Sigma.ι (fun _ : A ↦ ModuleCat.of.{u} R R) a) 1)
  map_add' := by
    intro φ ψ
    sorry
  map_smul' := by
    intro r φ
    sorry
  invFun f :=
    Limits.Sigma.desc (fun a ↦ ModuleCat.ofHom (LinearMap.mulRight R (f a)))
  left_inv := by
    intro φ
    sorry
  right_inv := by
    intro f
    sorry

/-- The canonical degree `n` singular cochains are identified with the source-facing simplexwise
function model `singularCochains R X n`. -/
noncomputable def singularCochainComplexDegreeEquiv
    (R : Type u) [CommRing R] (X : TopCat.{u}) (n : ℕ) :
    (singularCochainComplex R X).X n ≃ₗ[R] singularCochains R X n where
  toFun φ :=
    singularCoproductHomEquiv R (singularSimplex n X)
      ((singularChainDegreeIsoCoproduct R X n).inv ≫ φ)
  map_add' := by
    intro φ ψ
    sorry
  map_smul' := by
    intro r φ
    sorry
  invFun f :=
    (singularChainDegreeIsoCoproduct R X n).hom ≫
      (singularCoproductHomEquiv R (singularSimplex n X)).symm f
  left_inv := by
    intro φ
    sorry
  right_inv := by
    intro f
    sorry

@[simp] theorem singularCochainComplexDegreeEquiv_symm_apply
    (R : Type u) [CommRing R] (X : TopCat.{u}) (n : ℕ)
    (f : singularCochains R X n) (σ : singularSimplex n X) :
    singularCochainComplexDegreeEquiv R X n
        ((singularCochainComplexDegreeEquiv R X n).symm f) σ =
      f σ := by
  simpa using congrFun
    ((singularCochainComplexDegreeEquiv R X n).apply_symm_apply f) σ

/-- Restriction of a singular `(p + q)`-simplex to its front `p`-face. -/
def singularFrontFace (X : TopCat.{u}) (p q : ℕ) :
    singularSimplex (p + q) X → singularSimplex p X :=
  fun σ ↦
    σ.comp ⟨_, stdSimplex.continuous_map (SimplexCategory.subinterval 0 p (by simp)).toOrderHom⟩

@[simp] theorem singularFrontFace_apply (X : TopCat.{u}) (p q : ℕ)
    (σ : singularSimplex (p + q) X) (x : stdSimplex ℝ (Fin (p + 1))) :
    singularFrontFace X p q σ x =
      σ (stdSimplex.map (SimplexCategory.subinterval 0 p (by simp)).toOrderHom x) :=
  rfl

/-- Restriction of a singular `(p + q)`-simplex to its back `q`-face. -/
def singularBackFace (X : TopCat.{u}) (p q : ℕ) :
    singularSimplex (p + q) X → singularSimplex q X :=
  fun σ ↦
    σ.comp ⟨_, stdSimplex.continuous_map (SimplexCategory.subinterval p q le_rfl).toOrderHom⟩

@[simp] theorem singularBackFace_apply (X : TopCat.{u}) (p q : ℕ)
    (σ : singularSimplex (p + q) X) (x : stdSimplex ℝ (Fin (q + 1))) :
    singularBackFace X p q σ x =
      σ (stdSimplex.map (SimplexCategory.subinterval p q le_rfl).toOrderHom x) :=
  rfl

/-- Construction 18.3.2. The singular-cochain cup product
`C^p(X; R) ⊗ C^q(X; R) → C^(p + q)(X; R)` is the bilinear pairing obtained by evaluating the
left cochain on the front `p`-face of a singular simplex, evaluating the right cochain on the
back `q`-face, and multiplying the two values in `R`. -/
def singularCochainCup (R : Type u) [CommRing R] (X : TopCat.{u}) (p q : ℕ) :
    singularCochains R X p ⊗[R] singularCochains R X q →ₗ[R]
      singularCochains R X (p + q) :=
  TensorProduct.lift <|
    LinearMap.mk₂ R
      (fun φ ψ σ ↦ φ (singularFrontFace X p q σ) * ψ (singularBackFace X p q σ))
      (by
        intro φ₁ φ₂ ψ
        sorry)
      (by
        intro a φ ψ
        sorry)
      (by
        intro φ ψ₁ ψ₂
        sorry)
      (by
        intro a φ ψ
        sorry)

namespace singularCochains

variable {R : Type u} [CommRing R] {X : TopCat.{u}} {p q : ℕ}

/-- The ordinary binary cup product of singular cochains underlying
`singularCochainCup R X p q`. -/
abbrev cup (φ : singularCochains R X p) (ψ : singularCochains R X q) :
    singularCochains R X (p + q) :=
  singularCochainCup R X p q (TensorProduct.tmul R φ ψ)

scoped[singularCochains] infixr:70 " ⌣ " => singularCochains.cup

@[simp] theorem cup_apply (φ : singularCochains R X p) (ψ : singularCochains R X q)
    (σ : singularSimplex (p + q) X) :
    (φ ⌣ ψ) σ = φ (singularFrontFace X p q σ) * ψ (singularBackFace X p q σ) := by
  simp [cup, singularCochainCup]

end singularCochains

open scoped singularCochains

/-- On pure tensors, `singularCochainCup` is the ordinary singular cup product `φ ⌣ ψ`. -/
@[simp] theorem singularCochainCup_tmul (R : Type u) [CommRing R] (X : TopCat.{u}) (p q : ℕ)
    (φ : singularCochains R X p) (ψ : singularCochains R X q) :
    singularCochainCup R X p q (TensorProduct.tmul R φ ψ) = φ ⌣ ψ :=
  rfl

/-- Evaluating `singularCochainCup` on a pure tensor and a singular simplex multiplies the
front-face and back-face evaluations. -/
@[simp] theorem singularCochainCup_tmul_apply (R : Type u) [CommRing R] (X : TopCat.{u})
    (p q : ℕ) (φ : singularCochains R X p) (ψ : singularCochains R X q)
    (σ : singularSimplex (p + q) X) :
    singularCochainCup R X p q (TensorProduct.tmul R φ ψ) σ =
      φ (singularFrontFace X p q σ) * ψ (singularBackFace X p q σ) := by
  rw [singularCochainCup_tmul R X p q φ ψ]
  exact singularCochains.cup_apply φ ψ σ
