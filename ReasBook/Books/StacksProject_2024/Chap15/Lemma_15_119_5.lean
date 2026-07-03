import Mathlib
import StacksProject_2024.Chap15.Lemma_15_119_3
import StacksProject_2024.Chap15.Lemma_15_119_6

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section
open CategoryTheory
open LinearEquiv
open LinearMap
open scoped TensorProduct
open scoped DeterminantLine

universe u v w

variable {R : Type u} [CommRing R]
variable {M' : Type v} [AddCommGroup M'] [Module R M'] [Module.Finite R M']
  [Module.Projective R M']
variable {M'' : Type w} [AddCommGroup M''] [Module R M''] [Module.Finite R M'']
  [Module.Projective R M'']

/-
Domain-style sampling for Lemma 15.119.5:
- primary domain: determinant lines of finite projective modules and the canonical comparison maps
  attached to short exact sequences, specialized to the split rows for a direct sum;
- sampled owner declarations:
  * `CategoryTheory.ShortComplex.ShortExact.determinantTensorIso`,
  * `determinantTensorIsoOfShortExact`,
  * `determinantTensorIsoOfShortExact_naturality`,
  * `determinantLineMap`,
  * `LinearMap.projectiveDet`;
- best owner abstraction:
  `core/canonical`: `CategoryTheory.ShortComplex.ShortExact.determinantTensorIso`, with the
    presented-row bridge `determinantTensorIsoOfShortExact`;
  `bridge/view`: the symmetry square for the split exact rows
    `0 → M' → M' × M'' → M'' → 0` and `0 → M'' → M'' × M' → M' → 0`;
- primitive data: the finite projective modules `M'` and `M''`;
- derived API: the determinant comparison maps for the two split rows, the determinant-line map of
  `LinearEquiv.prodComm`, the canonical determinant scalar
  `tensorSwitchSign R M' M'' = det(-id_{M' ⊗[R] M''})`, and the tensor symmetry twisted by that
  scalar action.

This file therefore stays at the bridge layer and reuses the determinant-line owners already
introduced in `15.119.2` and `15.119.3`, rather than introducing any parallel split-row wrapper.
-/

section TensorSwitchSign

variable (R) (M') (M'')

private theorem determinantMap_eq_determinantLineMap_toLinearMap
    (e : (M' ⊗[R] M'') ≃ₗ[R] M' ⊗[R] M'') :
    LinearMap.determinantMap (fun _ ↦ rfl) e.toLinearMap =
      (determinantLineMap e).toLinearMap := by
  ext x
  rfl

/-- The canonical sign scalar `ε = det(-id_{M' ⊗[R] M''}) ∈ R` from the determinant owner
`LinearMap.projectiveDet`. -/
noncomputable def tensorSwitchSign : R :=
  LinearMap.projectiveDet
    (-LinearMap.id : (M' ⊗[R] M'') →ₗ[R] M' ⊗[R] M'')

/-- The canonical sign scalar acts on `det(M' ⊗[R] M'')` by the determinant-line map induced by
`-id_{M' ⊗[R] M''}`. -/
theorem tensorSwitchSign_spec :
    Module.toModuleEnd R (det(M' ⊗[R] M'')) (tensorSwitchSign R M' M'') =
      (determinantLineMap (neg R : (M' ⊗[R] M'') ≃ₗ[R] M' ⊗[R] M'')).toLinearMap := by
  simpa [tensorSwitchSign, determinantMap_eq_determinantLineMap_toLinearMap] using
    LinearMap.projectiveDet_spec
      (-LinearMap.id : (M' ⊗[R] M'') →ₗ[R] M' ⊗[R] M'')

/-- On the determinant line of `M' ⊗[R] M''`, the map induced by `-id` is scalar multiplication
by the canonical sign scalar `tensorSwitchSign R M' M''`. -/
theorem determinantLineMap_neg_toLinearMap_eq_tensorSwitchSign :
    (determinantLineMap (neg R : (M' ⊗[R] M'') ≃ₗ[R] M' ⊗[R] M'')).toLinearMap =
      Module.toModuleEnd R (det(M' ⊗[R] M'')) (tensorSwitchSign R M' M'') := by
  simpa using (tensorSwitchSign_spec R M' M'').symm

end TensorSwitchSign

/-- Lemma 15.119.5: for the split short exact sequences
`0 → M' → M' × M'' → M'' → 0` and `0 → M'' → M'' × M' → M' → 0`, the determinant-line
comparison maps from Lemma `15.119.2` are intertwined by switching the summands, up to the sign
scalar `tensorSwitchSign R M' M'' = det(-id_{M' ⊗[R] M''})` by which `-1` acts on the determinant
line of `M' ⊗[R] M''`. -/
theorem determinant_tensor_iso_switch_summands_commutes
    : CommSq
        (ModuleCat.ofHom <|
          (determinantTensorIsoOfShortExact
            (inl R M' M'')
            (snd R M' M'')
            inl_injective
            snd_surjective
            Function.Exact.inl_snd).toLinearMap)
        (ModuleCat.ofHom <|
          (TensorProduct.comm R (det(M')) (det(M''))).toLinearMap.comp
            (Module.toModuleEnd R (det(M') ⊗[R] det(M'')) (tensorSwitchSign R M' M'')))
        (ModuleCat.ofHom <| (determinantLineMap (prodComm R M' M'')).toLinearMap)
        (ModuleCat.ofHom <|
          (determinantTensorIsoOfShortExact
            (inl R M'' M')
            (snd R M'' M')
            inl_injective
            snd_surjective
            Function.Exact.inl_snd).toLinearMap) := by
  refine CommSq.mk ?_
  sorry
