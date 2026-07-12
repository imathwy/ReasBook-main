import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Module.Projective
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Monoidal.Rigid.Braided
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.TensorProduct.Finiteness

-- Declarations for this item will be appended below by the statement pipeline.

/-
Domain-style sampling:
- primary domain: duality in `ModuleCat R`, comparing an abstract exact pairing with the canonical
  module-dual owner of `M`;
- sampled owner declarations:
  `Definition 4.43.5` (`ExactPairing Y X` for a left dual `Y` of `X`),
  `MonoidalClosed.curry`,
  `Module.Dual`,
  `ModuleCat.homLinearEquiv`,
  `CategoryTheory.rightDualIso`,
  `BraidedCategory.exactPairing_swap`;
- best owner abstraction: the comparison from a chosen left dual is canonically the curried
  evaluation morphism into the internal Hom to the tensor unit; the module-theoretic codomain
  `Module.Dual R M = Hom_R(M, R)` is the canonical owner view of that internal-Hom object in
  `ModuleCat R`;
- primitive data: the ambient commutative ring, the two `R`-modules, and the exact pairing
  instance `[ExactPairing (ModuleCat.of R N) (ModuleCat.of R M)]`;
- derived API: the internal Hom object `(ihom (ModuleCat.of R M)).obj (𝟙_ (ModuleCat R))`, the
  currying map from the evaluation pairing, and the resulting comparison morphism to the canonical
  dual owner.

Source/core/bridge triage:
- `source-facing`: the textbook map from a left dual of `M` to `Hom_R(M, R)`;
- `core/canonical`: `MonoidalClosed.curry (ε_ (ModuleCat.of R N) (ModuleCat.of R M))`;
- `bridge/view`: `ExactPairing.toModuleDual`, the thin codomain-change bridge from the canonical
  curried evaluation morphism to the module-dual owner `Module.Dual R M`.
-/

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open ModuleCat
open scoped TensorProduct

noncomputable section

universe u

section

variable {R : Type u} [CommRing R]
variable {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
variable [ExactPairing (ModuleCat.of R N) (ModuleCat.of R M)]

namespace ExactPairing

/-- The canonical morphism from a left dual `N` of `M` to the canonical module dual
`Module.Dual R M = Hom_R(M, R)`, obtained by currying the evaluation pairing and then identifying
the internal Hom to the tensor unit with `Module.Dual R M`. This is the inverse of the textbook
map `e`. -/
abbrev toModuleDual : ModuleCat.of R N ⟶ ModuleCat.of R (Module.Dual R M) :=
  curry (ε_ (ModuleCat.of R N) (ModuleCat.of R M)) ≫
    ((homLinearEquiv :
        (ModuleCat.of R M ⟶ 𝟙_ (ModuleCat R)) ≃ₗ[R] Module.Dual R M).toModuleIso.hom)

/-- Helper for Lemma 15.73.1: if `N` is a chosen left dual of `M`, then the coevaluation element
produces a split map from a finite free module onto `M`. -/
theorem split_finite_free_of_left_dual
    {N : Type u} [AddCommGroup N] [Module R N]
    [ExactPairing (ModuleCat.of R N) (ModuleCat.of R M)] :
    ∃ k : ℕ, ∃ i : M →ₗ[R] (Fin k → R), ∃ s : (Fin k → R) →ₗ[R] M,
      s.comp i = LinearMap.id := by
  -- Expand the controlling coevaluation element `η(1)` as a finite sum of pure tensors.
  let z : N ⊗[R] M := (η_ (ModuleCat.of R N) (ModuleCat.of R M)) 1
  obtain ⟨k, n, m, hz⟩ := TensorProduct.exists_sum_tmul_eq z
  have hz' : (η_ (ModuleCat.of R N) (ModuleCat.of R M)) 1 = ∑ j, n j ⊗ₜ[R] m j := by
    simpa [z] using hz
  -- The coefficient map records the evaluations against the chosen finitely many dual vectors.
  let i : M →ₗ[R] (Fin k → R) :=
    { toFun := fun x j => (ε_ (ModuleCat.of R N) (ModuleCat.of R M)) (x ⊗ₜ[R] n j)
      map_add' := by
        intro x y
        ext j
        simp [TensorProduct.add_tmul]
      map_smul' := by
        intro a x
        ext j
        rw [← TensorProduct.smul_tmul', map_smul]
        rfl }
  -- The synthesis map rebuilds an element of `M` from the chosen finitely many generators `m j`.
  let s : (Fin k → R) →ₗ[R] M :=
    { toFun := fun a => ∑ j, a j • m j
      map_add' := by
        intro a b
        simp [Finset.sum_add_distrib, add_smul]
      map_smul' := by
        intro a b
        simp [Finset.smul_sum, mul_smul] }
  refine ⟨k, i, s, ?_⟩
  -- Evaluate the triangle identity on `x ⊗ 1`; after rewriting by `hz`, it is exactly `s (i x) = x`.
  ext x
  have htriangle :
      (ρ_ (ModuleCat.of R M)).inv ≫
          (ModuleCat.of R M ◁ η_ (ModuleCat.of R N) (ModuleCat.of R M) ≫
            (α_ (ModuleCat.of R M) (ModuleCat.of R N) (ModuleCat.of R M)).inv ≫
              ε_ (ModuleCat.of R N) (ModuleCat.of R M) ▷ ModuleCat.of R M) ≫
        (λ_ (ModuleCat.of R M)).hom =
      𝟙 (ModuleCat.of R M) := by
    calc
      (ρ_ (ModuleCat.of R M)).inv ≫
          (ModuleCat.of R M ◁ η_ (ModuleCat.of R N) (ModuleCat.of R M) ≫
            (α_ (ModuleCat.of R M) (ModuleCat.of R N) (ModuleCat.of R M)).inv ≫
              ε_ (ModuleCat.of R N) (ModuleCat.of R M) ▷ ModuleCat.of R M) ≫
          (λ_ (ModuleCat.of R M)).hom =
        (ρ_ (ModuleCat.of R M)).inv ≫
            ((ρ_ (ModuleCat.of R M)).hom ≫ (λ_ (ModuleCat.of R M)).inv) ≫
              (λ_ (ModuleCat.of R M)).hom := by
          rw [ExactPairing.coevaluation_evaluation]
      _ = 𝟙 (ModuleCat.of R M) := by
        simp [Category.assoc]
  have htriangle_apply := congrArg (fun f => f x) htriangle
  change
    ((λ_ (ModuleCat.of R M)).hom)
        (((ε_ (ModuleCat.of R N) (ModuleCat.of R M) ▷ ModuleCat.of R M)
          (((α_ (ModuleCat.of R M) (ModuleCat.of R N) (ModuleCat.of R M)).inv)
            (((ModuleCat.of R M ◁ η_ (ModuleCat.of R N) (ModuleCat.of R M))
              (((ρ_ (ModuleCat.of R M)).inv) x)))))) =
      x at htriangle_apply
  have hcomposite :
      ((λ_ (ModuleCat.of R M)).hom)
          (((ε_ (ModuleCat.of R N) (ModuleCat.of R M) ▷ ModuleCat.of R M)
            (((α_ (ModuleCat.of R M) (ModuleCat.of R N) (ModuleCat.of R M)).inv)
              (((ModuleCat.of R M ◁ η_ (ModuleCat.of R N) (ModuleCat.of R M))
                (((ρ_ (ModuleCat.of R M)).inv) x)))))) =
        ∑ j, (ε_ (ModuleCat.of R N) (ModuleCat.of R M)) (x ⊗ₜ[R] n j) • m j := by
    have hsum :
        (Finset.univ.sum fun j : Fin k =>
          (TensorProduct.lid R M)
            ((LinearMap.rTensor M (ε_ (ModuleCat.of R N) (ModuleCat.of R M)).hom)
              ((TensorProduct.assoc R M N M).symm (x ⊗ₜ[R] (n j ⊗ₜ[R] m j))))) =
          (Finset.univ.sum fun j : Fin k =>
            (ε_ (ModuleCat.of R N) (ModuleCat.of R M)) (x ⊗ₜ[R] n j) • m j) :=
      Finset.sum_congr rfl (fun j _ => by simp)
    have hsumExpr :
        (TensorProduct.lid R M)
          ((LinearMap.rTensor M (ε_ (ModuleCat.of R N) (ModuleCat.of R M)).hom)
            ((TensorProduct.assoc R M N M).symm (x ⊗ₜ[R] ∑ j : Fin k, n j ⊗ₜ[R] m j))) =
          (∑ j : Fin k,
            (TensorProduct.lid R M)
              ((LinearMap.rTensor M (ε_ (ModuleCat.of R N) (ModuleCat.of R M)).hom)
                ((TensorProduct.assoc R M N M).symm (x ⊗ₜ[R] (n j ⊗ₜ[R] m j))))) := by
      simp only [TensorProduct.tmul_sum, map_sum]
    have h0 :
        ((λ_ (ModuleCat.of R M)).hom)
            (((ε_ (ModuleCat.of R N) (ModuleCat.of R M) ▷ ModuleCat.of R M)
              (((α_ (ModuleCat.of R M) (ModuleCat.of R N) (ModuleCat.of R M)).inv)
                (((ModuleCat.of R M ◁ η_ (ModuleCat.of R N) (ModuleCat.of R M))
                  (((ρ_ (ModuleCat.of R M)).inv) x)))))) =
          (TensorProduct.lid R M)
            ((LinearMap.rTensor M (ε_ (ModuleCat.of R N) (ModuleCat.of R M)).hom)
              ((TensorProduct.assoc R M N M).symm
                ((LinearMap.lTensor M (η_ (ModuleCat.of R N) (ModuleCat.of R M)).hom)
                  (x ⊗ₜ[R] 1)))) := by
      simp only [ModuleCat.hom_hom_leftUnitor, ModuleCat.hom_inv_rightUnitor,
        ModuleCat.hom_inv_associator, ModuleCat.hom_whiskerLeft, ModuleCat.hom_whiskerRight,
        LinearEquiv.coe_coe, TensorProduct.rid_symm_apply]
    have h1 :
        (TensorProduct.lid R M)
            ((LinearMap.rTensor M (ε_ (ModuleCat.of R N) (ModuleCat.of R M)).hom)
              ((TensorProduct.assoc R M N M).symm
                ((LinearMap.lTensor M (η_ (ModuleCat.of R N) (ModuleCat.of R M)).hom)
                  (x ⊗ₜ[R] 1)))) =
          (TensorProduct.lid R M)
            ((LinearMap.rTensor M (ε_ (ModuleCat.of R N) (ModuleCat.of R M)).hom)
              ((TensorProduct.assoc R M N M).symm (x ⊗ₜ[R] (η_ (ModuleCat.of R N) (ModuleCat.of R M)) 1))) := by
      simpa using
        congrArg
          (fun t =>
            (TensorProduct.lid R M)
              ((LinearMap.rTensor M (ε_ (ModuleCat.of R N) (ModuleCat.of R M)).hom)
                ((TensorProduct.assoc R M N M).symm t)))
          (LinearMap.lTensor_tmul
            (f := (η_ (ModuleCat.of R N) (ModuleCat.of R M)).hom) (M := M) x (1 : R))
    have h2 :
        (TensorProduct.lid R M)
            ((LinearMap.rTensor M (ε_ (ModuleCat.of R N) (ModuleCat.of R M)).hom)
              ((TensorProduct.assoc R M N M).symm (x ⊗ₜ[R] (η_ (ModuleCat.of R N) (ModuleCat.of R M)) 1))) =
          (TensorProduct.lid R M)
            ((LinearMap.rTensor M (ε_ (ModuleCat.of R N) (ModuleCat.of R M)).hom)
              ((TensorProduct.assoc R M N M).symm (x ⊗ₜ[R] ∑ j : Fin k, n j ⊗ₜ[R] m j))) := by
      rw [hz']
    exact h0.trans (h1.trans (h2.trans (hsumExpr.trans hsum)))
  simpa [i, s, LinearMap.comp_apply, LinearMap.id_apply] using hcomposite.symm.trans htriangle_apply

/-- Helper for Lemma 15.73.1: the internal-Hom right adjoint attached to `M` is canonically
identified with tensoring on the left by the chosen left dual `N`. -/
private noncomputable def leftDualIhomIso :
    tensorLeft (ModuleCat.of R N) ≅ ihom (ModuleCat.of R M) :=
  Adjunction.rightAdjointUniq
    (tensorLeftAdjunction (ModuleCat.of R N) (ModuleCat.of R M))
    (ihom.adjunction (ModuleCat.of R M))

/-- Helper for Lemma 15.73.1: currying the evaluation pairing agrees with the component at the
tensor unit of the right-adjoint uniqueness isomorphism. -/
private theorem curry_exactPairingEvaluation_eq_rightAdjointUniq_hom :
    curry (ε_ (ModuleCat.of R N) (ModuleCat.of R M)) =
      (ρ_ (ModuleCat.of R N)).inv ≫
        ((leftDualIhomIso (R := R) (M := M) (N := N)).app (𝟙_ (ModuleCat R))).hom := by
  -- Compare the two candidates after uncurrying; the Chapter 17 right-adjoint-uniqueness route
  -- applies verbatim in `ModuleCat R`.
  let e : tensorLeft (ModuleCat.of R N) ≅ ihom (ModuleCat.of R M) :=
    leftDualIhomIso (R := R) (M := M) (N := N)
  have hCounit :
      ModuleCat.of R M ◁ e.hom.app (𝟙_ (ModuleCat R)) ≫
          (ihom.ev (ModuleCat.of R M)).app (𝟙_ (ModuleCat R)) =
        (tensorLeftAdjunction (ModuleCat.of R N) (ModuleCat.of R M)).counit.app
          (𝟙_ (ModuleCat R)) := by
    simpa [leftDualIhomIso, e] using
      (Adjunction.rightAdjointUniq_hom_app_counit
        (tensorLeftAdjunction (ModuleCat.of R N) (ModuleCat.of R M))
        (ihom.adjunction (ModuleCat.of R M))
        (𝟙_ (ModuleCat R)))
  have hUncurry :
      uncurry ((ρ_ (ModuleCat.of R N)).inv ≫ e.hom.app (𝟙_ (ModuleCat R))) =
        ε_ (ModuleCat.of R N) (ModuleCat.of R M) := by
    rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_eq]
    calc
      ModuleCat.of R M ◁ (ρ_ (ModuleCat.of R N)).inv ≫
          ModuleCat.of R M ◁ e.hom.app (𝟙_ (ModuleCat R)) ≫
            (ihom.ev (ModuleCat.of R M)).app (𝟙_ (ModuleCat R)) =
        ModuleCat.of R M ◁ (ρ_ (ModuleCat.of R N)).inv ≫
          (tensorLeftAdjunction (ModuleCat.of R N) (ModuleCat.of R M)).counit.app
            (𝟙_ (ModuleCat R)) := by
          simpa [Category.assoc] using
            congrArg (fun k ↦ ModuleCat.of R M ◁ (ρ_ (ModuleCat.of R N)).inv ≫ k) hCounit
      _ = ε_ (ModuleCat.of R N) (ModuleCat.of R M) := by
        change
          ModuleCat.of R M ◁ (ρ_ (ModuleCat.of R N)).inv ≫
              (ModuleCat.of R M ◁ (𝟙 (ModuleCat.of R N ⊗ 𝟙_ (ModuleCat R))) ≫
                (α_ (ModuleCat.of R M) (ModuleCat.of R N) (𝟙_ (ModuleCat R))).inv ≫
                  ε_ (ModuleCat.of R N) (ModuleCat.of R M) ▷ 𝟙_ (ModuleCat R) ≫
                    (λ_ (𝟙_ (ModuleCat R))).hom) =
            ε_ (ModuleCat.of R N) (ModuleCat.of R M)
        simp only [whiskerLeft_rightUnitor_inv, whiskerLeft_id, whiskerRight_id, Category.assoc,
          Category.id_comp, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc]
        have hUnitors : (ρ_ (𝟙_ (ModuleCat R))).inv = (λ_ (𝟙_ (ModuleCat R))).inv := by
          simpa using
            (show (ρ_ (𝟙_ (ModuleCat R))).inv = (λ_ (𝟙_ (ModuleCat R))).inv from
              unitors_inv_equal.symm)
        rw [hUnitors]
        simp
  apply MonoidalClosed.uncurry_injective
  simpa using hUncurry.symm

/-- Helper for Lemma 15.73.1: the curried evaluation map is already an isomorphism before
identifying the internal Hom with the module dual. -/
private theorem isIso_curry_exactPairingEvaluation :
    IsIso (curry (ε_ (ModuleCat.of R N) (ModuleCat.of R M))) := by
  -- Once the comparison with the right-adjoint uniqueness map is established, both displayed
  -- factors are standard isomorphisms.
  rw [curry_exactPairingEvaluation_eq_rightAdjointUniq_hom]
  let _ :
      IsIso (((leftDualIhomIso (R := R) (M := M) (N := N)).hom.app (𝟙_ (ModuleCat R)))) := by
    infer_instance
  refine ⟨⟨inv (((leftDualIhomIso (R := R) (M := M) (N := N)).hom.app (𝟙_ (ModuleCat R)))) ≫
      (ρ_ (ModuleCat.of R N)).hom, ?_, ?_⟩⟩ <;> simp

-- Proof sketch: choose a finite free module surjecting onto `M`, lift the coevaluation through
-- it, and use the triangle identity to factor `𝟙_M` through that finite free module; this gives
-- finite projectivity of `M`.
include N

/-- Lemma 15.73.1 (1): if `N` is a left dual of `M` in the monoidal category of `R`-modules, then
`M` is a finite projective `R`-module. -/
theorem exactPairing_source_finite_projective :
    Module.Finite R M ∧ Module.Projective R M := by
  -- Route correction: the exact-pairing data is already carried by the section variables, so the
  -- source proof reduces directly to the split finite-free presentation extracted from `η(1)`.
  rcases split_finite_free_of_left_dual (R := R) (M := M) (N := N) with ⟨k, i, s, hs⟩
  have hs_surj : Function.Surjective s := by
    intro x
    refine ⟨i x, ?_⟩
    simpa [LinearMap.comp_apply] using congrArg (fun f => f x) hs
  letI : Module.Finite R (Fin k → R) := by infer_instance
  have hfinite : Module.Finite R M := Module.Finite.of_surjective s hs_surj
  letI : Module.Projective R (Fin k → R) := by infer_instance
  have hprojective : Module.Projective R M := Module.Projective.of_split i s hs
  exact ⟨hfinite, hprojective⟩

-- Proof sketch: apply the same argument as for `M` after swapping the exact pairing in the
-- symmetric monoidal category `ModuleCat R`.
include M

/-- Lemma 15.73.1 (2): if `N` is a left dual of `M` in the monoidal category of `R`-modules, then
`N` is a finite projective `R`-module. -/
theorem exactPairing_target_finite_projective :
    Module.Finite R N ∧ Module.Projective R N := by
  -- Swap the pairing in the braided monoidal category and reuse the source result with the roles
  -- of `M` and `N` interchanged.
  letI : ExactPairing (ModuleCat.of R M) (ModuleCat.of R N) :=
    BraidedCategory.exactPairing_swap (ModuleCat.of R N) (ModuleCat.of R M)
  exact (exactPairing_source_finite_projective (R := R) (M := N) (N := M))

-- Proof sketch: specialize the canonical hom-set equivalence of Lemma `4.43.6` to
-- `Z = 𝟙_(ModuleCat R)` and `Z' = 𝟙_(ModuleCat R)`, then identify maps out of and into the tensor
-- unit with `Module.Dual R M` and `N`.
/-- Lemma 15.73.1 (3): the canonical morphism `N ⟶ Module.Dual R M` obtained from the evaluation
pairing is an isomorphism; equivalently, the textbook map
`e : Hom_R(M, R) → N` given by `φ ↦ (φ ⊗ 1)(η)` is bijective. -/
theorem isIso_toModuleDual :
    IsIso (toModuleDual : ModuleCat.of R N ⟶ ModuleCat.of R (Module.Dual R M)) := by
  -- The comparison map is the curried evaluation followed by the canonical identification of the
  -- internal Hom to the tensor unit with the ordinary module dual.
  change IsIso
    (curry (ε_ (ModuleCat.of R N) (ModuleCat.of R M)) ≫
      ((homLinearEquiv :
          (ModuleCat.of R M ⟶ 𝟙_ (ModuleCat R)) ≃ₗ[R] Module.Dual R M).toModuleIso.hom))
  let _ : IsIso (curry (ε_ (ModuleCat.of R N) (ModuleCat.of R M))) :=
    isIso_curry_exactPairingEvaluation (R := R) (M := M) (N := N)
  infer_instance

attribute [instance] isIso_toModuleDual

-- Proof sketch: `toModuleDual` is obtained by currying the evaluation pairing and then
-- identifying the internal-Hom object to the tensor unit with `Module.Dual R M`, so evaluation
-- on `m` is literally the original pairing.
/-- Lemma 15.73.1 (4): for `n : N` and `m : M`, evaluating the functional
`toModuleDual n : Module.Dual R M` at `m` recovers the exact-pairing evaluation on
`m ⊗ n`; equivalently, this is the inverse of the textbook map `e` applied to `n` and then
evaluated at `m`. -/
theorem toModuleDual_apply (n : N) (m : M) :
    (ε_ (ModuleCat.of R N) (ModuleCat.of R M)) (m ⊗ₜ[R] n) =
      toModuleDual n m := by
  rfl

end ExactPairing

end
