import Mathlib
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import stacks_project.Chap18.Lemma_18_43_3

open CategoryTheory

noncomputable section

universe u v w

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory.Sheaf

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {Λ : Type w} [Ring Λ] [IsNoetherianRing Λ]
variable [HasWeakSheafify J (ModuleCat.{w} Λ)]
variable [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat.{w} Λ)]
variable [∀ U : C, ∀ V : Over U, HasWeakSheafify ((J.over U).over V) (ModuleCat.{w} Λ)]
variable [Abelian (Sheaf J (ModuleCat.{w} Λ))]
variable [∀ U : C, Abelian (Sheaf (J.over U) (ModuleCat.{w} Λ))]
variable [CategoryWithHomology (Sheaf J (ModuleCat.{w} Λ))]
variable [∀ U : C, CategoryWithHomology (Sheaf (J.over U) (ModuleCat.{w} Λ))]

/-- Restriction of sheaves of `\Lambda`-modules from `(C, J)` to the localized site
`(C/U, J.over U)`. -/
abbrev localizedModuleRestriction (U : C) :
    Sheaf J (ModuleCat.{w} Λ) ⥤ Sheaf (J.over U) (ModuleCat.{w} Λ) :=
  J.overPullback (ModuleCat.{w} Λ) U

/-- A complex of sheaves of `\Lambda`-modules is bounded finite-type locally constant if it is
bounded and each term is a locally constant sheaf of finite type. -/
def CochainComplex.IsBoundedFiniteTypeLocallyConstant
    (L : CochainComplex (Sheaf J (ModuleCat.{w} Λ)) ℤ) : Prop :=
  (∃ a b : ℤ, L.IsStrictlyGE a ∧ L.IsStrictlyLE b) ∧
    ∀ n : ℤ, IsFiniteTypeLocallyConstantModule (L.X n)

/-- A derived object has bounded finite-type locally constant cohomology if it is bounded and
each cohomology sheaf is locally constant of finite type. -/
def DerivedCategory.HasBoundedFiniteTypeLocallyConstantCohomology
    (K : DerivedCategory (Sheaf J (ModuleCat.{w} Λ))) : Prop :=
  (∃ a b : ℤ, K.IsGE a ∧ K.IsLE b) ∧
    ∀ n : ℤ,
      IsFiniteTypeLocallyConstantModule
        ((DerivedCategory.homologyFunctor (Sheaf J (ModuleCat.{w} Λ)) n).obj K)

-- Proof sketch: argue by induction on the cohomological amplitude of `K`. After refining to a
-- cover of the terminal object, make the top nonzero cohomology sheaf constant of finite type,
-- choose a surjection from a finite free constant sheaf, and form the cone to reduce the
-- amplitude. The weak-Serre closure of locally constant finite-type sheaves keeps the cone in the
-- same class, so on each member of the cover one obtains a bounded complex of locally constant
-- finite-type sheaves whose cohomology identifies with the restricted cohomology sheaves of `K`.
/-- Lemma 21.53.1: if `K ∈ D^b(\mathcal C, \Lambda)` has cohomology sheaves locally constant of
finite type and `X` is a final object of the site, then there exists a covering of `X` such that
on each slice site `(C/U_i, J.over U_i)` there is a bounded complex of locally constant sheaves of
finite type `\Lambda`-modules whose cohomology sheaves identify with the restrictions of the
cohomology sheaves of `K`. This is the statement-stage encoding of the textbook claim that each
`K|_{U_i}` is represented by such a complex. -/
theorem exists_cover_restriction_represented_by_bounded_finite_type_locally_constant_complex
    (X : C) (_hX : Limits.IsTerminal X)
    (K : DerivedCategory (Sheaf J (ModuleCat.{w} Λ)))
    (hK : DerivedCategory.HasBoundedFiniteTypeLocallyConstantCohomology K) :
    ∃ T : J.Cover X, ∀ I : T.Arrow,
      ∃ L : CochainComplex (Sheaf (J.over I.Y) (ModuleCat.{w} Λ)) ℤ,
        CochainComplex.IsBoundedFiniteTypeLocallyConstant L ∧
          ∀ n : ℤ,
            IsIsomorphic
              (L.homology n)
              ((localizedModuleRestriction I.Y).obj
                ((DerivedCategory.homologyFunctor (Sheaf J (ModuleCat.{w} Λ)) n).obj K)) := sorry

end

end CategoryTheory.Sheaf
