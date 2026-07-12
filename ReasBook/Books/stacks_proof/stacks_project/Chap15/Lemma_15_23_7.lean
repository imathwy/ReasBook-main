import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.RingTheory.TensorProduct.Pi
import StacksProject_2024.Chap15.Lemma_15_22_4
import StacksProject_2024.Chap15.Lemma_15_23_5
import StacksProject_2024.Chap15.Lemma_15_23_6
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

open scoped TensorProduct
open Function Module TensorProduct
open TensorProduct.AlgebraTensorModule

/-
Domain-style sampling:
- primary domain: reflexive finite modules over Noetherian domains and their behavior under flat
  base change to a domain algebra;
- sampled owner declarations:
  `Module.IsReflexive`,
  `Module.Finite.base_change`,
  `TensorProduct.piScalarRight`,
  `Module.Flat.lTensor_exact`,
  `isReflexive_of_exact_of_isReflexive_of_isTorsionFree`,
  `Module.IsReflexive.of_finite_of_free`,
  `isReflexive_iff_exists_injective_to_fin_fun_with_torsionFree_cokernel`,
  `isTorsionFree_baseChange_of_flat`;
- best owner abstraction: the core/canonical owner is `Module.IsReflexive`; the chapter-level
  bridge/view API is the characterization of a finite reflexive module by an injective map into a
  finite free module with torsion-free canonical cokernel; after tensoring that exact
  presentation, `Module.Flat.lTensor_exact` and
  `isReflexive_of_exact_of_isReflexive_of_isTorsionFree` keep the proof at the exact-sequence
  owner level, while `TensorProduct.piScalarRight` and `Module.IsReflexive.of_finite_of_free`
  supply the reflexive finite-free middle term after base change;
- source/core/bridge triage:
  - `source-facing`: reflexivity of the base-changed module `R' ⊗[R] M`;
  - `core/canonical`: `Module.IsReflexive`;
  - `bridge/view`: Lemma `15.23.6` for the finite-free presentation and
    `isTorsionFree_baseChange_of_flat` for the cokernel after tensoring.

Primitive data are the flat algebra `R → R'` from a Noetherian domain into a domain algebra and
the finite reflexive `R`-module `M`. The finiteness of `R' ⊗[R] M` is derived API via
`Module.Finite.base_change`, and the finite-free embedding used in the proof is derived from the
reflexive owner theorem rather than packaged as a new local structure.
-/

section

variable {R : Type u} {R' : Type v} {M : Type w}
variable [CommRing R] [IsDomain R] [IsNoetherianRing R]
variable [CommRing R'] [IsDomain R'] [Algebra R R'] [Flat R R']
variable [AddCommGroup M] [Module R M] [Module.Finite R M] [IsReflexive R M]

namespace Module.IsReflexive

-- Proof sketch: apply Lemma `15.23.6` to choose an injective map `f : M → R^n` whose canonical
-- cokernel `(Fin n → R) ⧸ LinearMap.range f` is torsion free. Tensor the exact sequence
-- `0 → M → R^n → cokernel(f) → 0` with `R'`; flatness preserves exactness and injectivity, and
-- `isTorsionFree_baseChange_of_flat` preserves torsion-freeness of the tensorized cokernel.
-- The middle term remains finite free after base change via `TensorProduct.piScalarRight`, hence
-- reflexive. Lemma `15.23.5` then applies directly to the tensorized exact pair.
/-- Lemma 15.23.7: for a flat homomorphism `R → R'` from a Noetherian domain to a domain, the
base change of a finite reflexive `R`-module is reflexive over `R'`. The finiteness of
`R' ⊗[R] M` is supplied by the canonical owner theorem `Module.Finite.base_change`. -/
@[stacks 0EB9]
theorem baseChange_of_flat :
    IsReflexive R' (R' ⊗[R] M) := by
  letI : Module.Finite R' (R' ⊗[R] M) := inferInstance
  have hMReflexive : IsReflexive R M := inferInstance
  rcases
      isReflexive_iff_exists_injective_to_fin_fun_with_torsionFree_cokernel.mp hMReflexive with
    ⟨n, f, hf, hQ⟩
  let F := Fin n → R
  let freeBaseChange : R' ⊗[R] F ≃ₗ[R'] Fin n → R' :=
    TensorProduct.piScalarRight R R' R' (Fin n)
  let fTensor : R' ⊗[R] M →ₗ[R'] R' ⊗[R] F := (lTensor R' R') f
  let qTensor : R' ⊗[R] F →ₗ[R'] R' ⊗[R] (F ⧸ LinearMap.range f) :=
    (lTensor R' R') (Submodule.mkQ (LinearMap.range f))
  have hfTensor : Function.Injective fTensor := by
    simpa [fTensor] using Module.Flat.lTensor_preserves_injective_linearMap f hf
  have hExactTensor : Function.Exact fTensor qTensor := by
    simpa [fTensor, qTensor, coe_lTensor] using
      Module.Flat.lTensor_exact R' (LinearMap.exact_map_mkQ_range f)
  haveI : IsTorsionFree R (F ⧸ LinearMap.range f) := hQ
  haveI : IsTorsionFree R' (R' ⊗[R] (F ⧸ LinearMap.range f)) :=
    isTorsionFree_baseChange_of_flat
  letI : Module.Finite R' (R' ⊗[R] F) := inferInstance
  letI : Module.Free R' (R' ⊗[R] F) := Module.Free.of_equiv freeBaseChange.symm
  letI : IsReflexive R' (R' ⊗[R] F) := Module.IsReflexive.of_finite_of_free R' (R' ⊗[R] F)
  haveI : IsTorsionFree R' (LinearMap.range qTensor) :=
    (Submodule.subtype_injective (LinearMap.range qTensor)).moduleIsTorsionFree
      (LinearMap.range qTensor).subtype fun r x ↦ rfl
  exact isReflexive_of_exact_of_isReflexive_of_isTorsionFree hExactTensor hfTensor

end Module.IsReflexive

end
