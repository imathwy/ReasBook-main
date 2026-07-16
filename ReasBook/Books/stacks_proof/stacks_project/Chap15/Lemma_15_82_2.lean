import Mathlib
import stacks_proof.stacks_project.Chap15.Definition_15_65_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open Polynomial

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]

private abbrev DModR := DerivedCategory.{u + 1, u, u + 1} (ModuleCat R)
local notation "ev0" => Polynomial.evalRingHom (0 : R)

/- Domain-style sampling for Lemma 15.82.2:
- primary domain: pseudo-coherence in derived categories under restriction of scalars along the
  polynomial evaluation map;
- sampled owner declarations:
  `DerivedCategory.IsMPseudoCoherent`,
  `ModuleCat.restrictScalars`,
  `Functor.mapDerivedCategory`,
  `Polynomial.evalRingHom`;
- best owner abstraction: the source-facing theorem compares the chapter owner
  `IsMPseudoCoherent` on `K` with the same owner on the restricted derived object;
- primitive data: the evaluation map `ev0 : R[X] →+* R` and the restricted derived object
  `((ModuleCat.restrictScalars ev0).mapDerivedCategory.obj K)`;
- bridge/view: restriction of scalars along `ev0`.

Source/core/bridge triage:
- `source-facing`: the equivalence below for evaluation at zero;
- `core/canonical`: `DerivedCategory.IsMPseudoCoherent` and
  `(ModuleCat.restrictScalars ev0).mapDerivedCategory`;
- `bridge/view`: the direct two-direction proof sketched by the Stacks Project text. -/

/-- Helper for Lemma 15.82.2: multiplication by `X` on `R[X]` is injective. -/
private theorem polynomial_eq_zero_of_mul_X_eq_zero {p : R[X]}
    (h : p * X = 0) :
    p = 0 := by
  -- Compare the coefficient of `X^(n + 1)` to recover every coefficient of `p`.
  ext n
  simpa [h] using (Polynomial.coeff_mul_X p n).symm

/-- Helper for Lemma 15.82.2: the restricted regular `R`-module should be pseudo-coherent over
`R[X]`. -/
private theorem regularModule_isPseudoCoherent_evalAtZero :
    ((ModuleCat.restrictScalars ev0).obj (ModuleCat.of R R)).IsPseudoCoherent := by
  -- Route correction: the source proof uses the short exact row
  -- `0 → R[X] --(·X)→ R[X] → R → 0`. The current workspace still needs a dependency-light bridge
  -- from that explicit row to the chapter owner `ModuleCat.IsPseudoCoherent`.
  -- TODO for Lemma 15.82.2: package the polynomial short exact sequence into the finite
  -- projective/pseudo-coherent owner needed for the restricted regular module.
  sorry

/-- Helper for Lemma 15.82.2: if `K` is `m`-pseudo-coherent over `R`, then its restriction along
`R[X] → R` should be `m`-pseudo-coherent over `R[X]`. -/
private theorem isMPseudoCoherent_restrictScalars_evalAtZero_of_base
    (K : DModR) (m : ℤ) :
    K.IsMPseudoCoherent m →
      ((ModuleCat.restrictScalars ev0).mapDerivedCategory.obj K).IsMPseudoCoherent m := by
  intro hK
  -- Route correction: avoid the broken `Lemma_15_65_11` import chain and follow the source proof
  -- directly from a bounded finite-free approximation of `K`.
  let _ := hK
  -- TODO for Lemma 15.82.2: restrict a chosen finite-free approximation termwise, prove the
  -- restricted finite free terms are pseudo-coherent over `R[X]`, transport the homology window
  -- through restriction of scalars, and finish with the bounded-above termwise criterion.
  sorry

/-- Helper for Lemma 15.82.2: if the restricted complex is `m`-pseudo-coherent over `R[X]`, then
the original complex should be `m`-pseudo-coherent over `R`. -/
private theorem isMPseudoCoherent_of_restrictScalars_evalAtZero
    (K : DModR) (m : ℤ) :
    ((ModuleCat.restrictScalars ev0).mapDerivedCategory.obj K).IsMPseudoCoherent m →
      K.IsMPseudoCoherent m := by
  intro hK
  -- Route correction: the source proof tensors back with `R`, rewrites via Lemma `15.82.1` as
  -- `K ⊞ K[1]`, and then descends to the left summand.
  let _ := hK
  -- TODO for Lemma 15.82.2: apply the derived tensor pseudo-coherence theorem to the restricted
  -- complex, use Lemma `15.82.1` to identify the result with `K ⊞ K⟦1⟧`, and then apply the
  -- direct-summand descent lemma from Lemma `15.65.8`.
  sorry

/-- Lemma 15.82.2: for the polynomial evaluation map `R[X] → R` sending `X` to `0`, a derived
`R`-complex is `m`-pseudo-coherent exactly when the same object viewed by restriction of scalars
as a derived `R[X]`-complex is `m`-pseudo-coherent. -/
@[stacks 065G]
theorem isMPseudoCoherent_iff_restrictScalars_evalAtZero
    (K : DModR) (m : ℤ) :
    K.IsMPseudoCoherent m ↔
      ((ModuleCat.restrictScalars ev0).mapDerivedCategory.obj K).IsMPseudoCoherent m := by
  constructor
  · exact isMPseudoCoherent_restrictScalars_evalAtZero_of_base (R := R) K m
  · exact isMPseudoCoherent_of_restrictScalars_evalAtZero (R := R) K m

end

end CategoryTheory
