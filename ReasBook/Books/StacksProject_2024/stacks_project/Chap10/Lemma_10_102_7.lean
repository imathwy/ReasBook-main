import StacksProject_2024.stacks_project.Chap10.Situation_10_102_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open CategoryTheory HomologicalComplex

namespace ModuleCat

variable {R : Type u} [CommRing R]

/-- Bridge/view: the endofunctor on `ModuleCat R` induced by the canonical module quotient map
`QuotSMulTop.map x`. Its only role here is to apply `mapHomologicalComplex` to quotient a complex
termwise modulo `x`; the owner-level module data remain `QuotSMulTop` and `QuotSMulTop.map`. -/
def quotSMulTopFunctor (x : R) : ModuleCat R ⥤ ModuleCat R where
  obj M := ModuleCat.of R (QuotSMulTop x M)
  map f := ModuleCat.ofHom (QuotSMulTop.map x f.hom)
  map_id M := by
    change ModuleCat.ofHom (QuotSMulTop.map x (LinearMap.id : M →ₗ[R] M)) =
      ModuleCat.ofHom (LinearMap.id : QuotSMulTop x M →ₗ[R] QuotSMulTop x M)
    exact congrArg ModuleCat.ofHom (QuotSMulTop.map_id x M)
  map_comp f g := by
    change ModuleCat.ofHom (QuotSMulTop.map x (g.hom ∘ₗ f.hom)) =
      ModuleCat.ofHom (QuotSMulTop.map x g.hom ∘ₗ QuotSMulTop.map x f.hom)
    exact congrArg ModuleCat.ofHom (QuotSMulTop.map_comp x g.hom f.hom)

instance (x : R) : (quotSMulTopFunctor x).PreservesZeroMorphisms where
  map_zero X Y := by
    change ModuleCat.ofHom (QuotSMulTop.map x (0 : X →ₗ[R] Y)) =
      ModuleCat.ofHom (0 : QuotSMulTop x X →ₗ[R] QuotSMulTop x Y)
    apply congrArg ModuleCat.ofHom
    ext y
    rfl

end ModuleCat

section

variable {R : Type u} [CommRing R]
variable {e : ℕ}

-- Domain sampling pass:
-- * Primary domain: bounded chain complexes of modules, organized by the chapter owner
--   `FiniteFreeComplex` and the canonical exactness predicate `HomologicalComplex.ExactAt`.
-- * Relevant declarations sampled in this domain: `FiniteFreeComplex.toChainComplex`,
--   `HomologicalComplex.ExactAt`, `ModuleCat.smulShortComplex`, and
--   `QuotSMulTop.map_first_exact_on_four_term_exact_of_isSMulRegular_last`.
-- * Best owner abstraction: exactness lives on `HomologicalComplex.ExactAt`; the primitive
--   quotient data are `QuotSMulTop` and `QuotSMulTop.map`, while
--   `ModuleCat.quotSMulTopFunctor` is only the bridge needed to apply `mapHomologicalComplex`.
-- * Primitive data are the finite free complex `C` and the nonzerodivisor `x`; the displayed
--   quotient complex and its exactness are derived API from `C.toChainComplex` via
--   `ModuleCat.quotSMulTopFunctor`.
--
-- Proof sketch: apply `QuotSMulTop.map_first_exact_on_four_term_exact_of_isSMulRegular_last`
-- successively to the four-term windows of `C.toChainComplex`. Since each term of a
-- `FiniteFreeComplex` is free, a ring nonzerodivisor `x` is regular on every term, and the
-- exactness assumptions in degrees `e, …, 1` propagate to the quotient complex in degrees
-- `e, …, 2`.
/-- Lemma 10.102.7: in Situation 10.102.1, if the finite free complex is exact in degrees
`e, …, 1` and `x` is a nonzerodivisor, then the quotient complex modulo `x` is
exact in degrees `e, …, 2`. -/
theorem exact_mod_nonzerodivisor_of_exact
    (C : FiniteFreeComplex R e) {x : R} (hreg : IsRegular x)
    (hexact : ∀ j : ℕ, 1 ≤ j → j ≤ e → C.toChainComplex.ExactAt j) :
    ∀ j : ℕ, 2 ≤ j → j ≤ e →
      (((ModuleCat.quotSMulTopFunctor x).mapHomologicalComplex
          (ComplexShape.down ℕ)).obj C.toChainComplex).ExactAt j := sorry

end
