import stacks_proof.stacks_project.Chap10.Situation_10_102_1
import Mathlib.Tactic.StacksAttribute

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

/-- Helper for Lemma 10.102.7: in a chain complex of `R`-modules, exactness at a positive degree
is equivalent to exactness of the consecutive differentials as linear maps. -/
private lemma exactAt_iff_function_exact
    (K : ChainComplex (ModuleCat R) ℕ) {j : ℕ} (hj : 1 ≤ j) :
    K.ExactAt j ↔ Function.Exact (K.d (j + 1) j).hom (K.d j (j - 1)).hom := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hj
  have hmid : 1 + k = k + 1 := by omega
  have hsucc : k + 1 + 1 = k + 2 := by omega
  have hpred : k + 1 - 1 = k := by omega
  -- Re-index `ExactAt` through the explicit three-term window around a successor degree.
  rw [hmid, hsucc, hpred]
  rw [HomologicalComplex.exactAt_iff' K (k + 2) (k + 1) k (by simp) (by simp)]
  -- For modules, short-complex exactness is exactly `Function.Exact` on the underlying maps.
  simpa [HomologicalComplex.sc'] using
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact (K.sc' (k + 2) (k + 1) k))

/-- Helper for Lemma 10.102.7: if two adjacent degrees of a chain complex are exact and the last
term of the resulting four-term window is `x`-torsion-free, then quotienting termwise by `x`
preserves exactness at the middle degree. -/
private lemma exactAt_map_quotSMulTop_of_adjacent_exactAt
    (K : ChainComplex (ModuleCat R) ℕ) {x : R} {j : ℕ} (hj : 2 ≤ j)
    (h_exact_j : K.ExactAt j) (h_exact_prev : K.ExactAt (j - 1))
    (hreg : IsSMulRegular (K.X (j - 2)) x) :
    (((ModuleCat.quotSMulTopFunctor x).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj K).ExactAt j := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hj
  -- Translate the target exactness of the quotient complex into exactness of mapped differentials.
  have h_target :
      (((ModuleCat.quotSMulTopFunctor x).mapHomologicalComplex
          (ComplexShape.down ℕ)).obj K).ExactAt (2 + k) ↔
        Function.Exact
          (QuotSMulTop.map x (K.d (k + 3) (k + 2)).hom)
          (QuotSMulTop.map x (K.d (k + 2) (k + 1)).hom) := by
    simpa [ModuleCat.quotSMulTopFunctor, CategoryTheory.Functor.mapHomologicalComplex_obj_d,
      Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      (exactAt_iff_function_exact
        ((((ModuleCat.quotSMulTopFunctor x).mapHomologicalComplex
          (ComplexShape.down ℕ)).obj K)) (show 1 ≤ k + 2 by omega))
  rw [h_target]
  -- The source exactness assumptions provide the two adjacent exact pairs needed by the
  -- four-term quotient exactness lemma.
  have h_exact_j' : K.ExactAt (k + 2) := by
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h_exact_j
  have h_exact_prev' : K.ExactAt (k + 1) := by
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h_exact_prev
  have hreg' : IsSMulRegular (K.X k) x := by
    have hdeg : 2 + k - 2 = k := by omega
    rw [hdeg] at hreg
    exact hreg
  have h12 : Function.Exact (K.d (k + 3) (k + 2)).hom (K.d (k + 2) (k + 1)).hom := by
    exact (exactAt_iff_function_exact K (show 1 ≤ k + 2 by omega)).mp h_exact_j'
  have h23 : Function.Exact (K.d (k + 2) (k + 1)).hom (K.d (k + 1) k).hom := by
    exact (exactAt_iff_function_exact K (show 1 ≤ k + 1 by omega)).mp h_exact_prev'
  -- Apply the module-level exactness lemma for termwise quotients modulo a regular element.
  exact QuotSMulTop.map_first_exact_on_four_term_exact_of_isSMulRegular_last h12 h23 hreg'

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
@[stacks 00MZ]
theorem exact_mod_nonzerodivisor_of_exact
    (C : FiniteFreeComplex R e) {x : R} (hreg : IsRegular x)
    (hexact : ∀ j : ℕ, 1 ≤ j → j ≤ e → C.toChainComplex.ExactAt j) :
    ∀ j : ℕ, 2 ≤ j → j ≤ e →
      (((ModuleCat.quotSMulTopFunctor x).mapHomologicalComplex
          (ComplexShape.down ℕ)).obj C.toChainComplex).ExactAt j := by
  intro j hj hje
  -- The source proof uses the four-term window around `j`, together with regularity of `x` on the
  -- free term in degree `j - 2`, to deduce quotient exactness at degree `j`.
  have h_exact_j : C.toChainComplex.ExactAt j :=
    hexact j (show 1 ≤ j by omega) hje
  have h_exact_prev : C.toChainComplex.ExactAt (j - 1) :=
    hexact (j - 1) (show 1 ≤ j - 1 by omega) (show j - 1 ≤ e by omega)
  have hsmul : IsSMulRegular (C.toChainComplex.X (j - 2)) x :=
    Module.Flat.isSMulRegular_of_isRegular hreg
  exact exactAt_map_quotSMulTop_of_adjacent_exactAt C.toChainComplex hj h_exact_j h_exact_prev hsmul

end
