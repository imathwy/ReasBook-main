import Mathlib
import stacks_project.Chap15.Lemma_15_119_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section
open CategoryTheory
open scoped TensorProduct
open scoped DeterminantLine

universe u v

variable {R : Type u} [CommRing R]

/-
Domain-style sampling for determinant-line comparison maps:
- primary domain: determinant lines of finite projective modules and the canonical comparison map
  attached to a short exact sequence;
- sampled owner declarations:
  * `CategoryTheory.ShortComplex.ShortExact.determinantTensorIso`,
  * `determinantTensorIsoOfShortExact`,
  * `shortComplexOfShortExact`,
  * `determinantLineMap`,
  * `CategoryTheory.ShortComplex.π₁.mapIso`,
  * `CategoryTheory.ShortComplex.π₂.mapIso`,
  * `CategoryTheory.ShortComplex.π₃.mapIso`;
- best owner abstraction: the canonical comparison map is the owner-level
  `CategoryTheory.ShortComplex.ShortExact.determinantTensorIso` on a short exact `ShortComplex`;
  the presentation-to-`ShortComplex` bridge is `shortComplexOfShortExact`, and the linear-map
  naturality theorem below is therefore a `bridge/view`;
- primitive data: an isomorphism of short exact sequences;
- derived API: the determinant-line maps induced on the left, middle, and right terms and the
  resulting tensor-product comparison map.
-/

namespace CategoryTheory.ShortComplex

namespace ShortExact

section Naturality

variable {S T : ShortComplex (ModuleCat R)}
variable [Module.Finite R S.X₁] [Module.Projective R S.X₁]
variable [Module.Finite R S.X₂] [Module.Projective R S.X₂]
variable [Module.Finite R S.X₃] [Module.Projective R S.X₃]
variable [Module.Finite R T.X₁] [Module.Projective R T.X₁]
variable [Module.Finite R T.X₂] [Module.Projective R T.X₂]
variable [Module.Finite R T.X₃] [Module.Projective R T.X₃]

/-- Core/canonical: an isomorphism of short exact sequences of finite projective `R`-modules
intertwines the owner-level determinant-line comparison maps. -/
theorem determinantTensorIso_naturality
    (hS : S.ShortExact) (e : S ≅ T) :
    CommSq
      (ModuleCat.ofHom <| hS.determinantTensorIso.toLinearMap)
      (ModuleCat.ofHom <|
        (TensorProduct.congr
          (determinantLineMap ((π₁.mapIso e).toLinearEquiv))
          (determinantLineMap ((π₃.mapIso e).toLinearEquiv))).toLinearMap)
      (ModuleCat.ofHom <| (determinantLineMap ((π₂.mapIso e).toLinearEquiv)).toLinearMap)
      (ModuleCat.ofHom <| (shortExact_of_iso e hS).determinantTensorIso.toLinearMap) := by
  sorry

end Naturality
end ShortExact
end CategoryTheory.ShortComplex

section Naturality

variable {M' : Type v} [AddCommGroup M'] [Module R M']
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {M'' : Type v} [AddCommGroup M''] [Module R M'']
variable {K' : Type v} [AddCommGroup K'] [Module R K']
variable {K : Type v} [AddCommGroup K] [Module R K]
variable {K'' : Type v} [AddCommGroup K''] [Module R K'']

private theorem injective_of_commSq
    {f : M' →ₗ[R] M} {fK : K' →ₗ[R] K}
    (hf : Function.Injective f) (u : M' ≃ₗ[R] K') (v : M ≃ₗ[R] K)
    (huv : v.toLinearMap.comp f = fK.comp u.toLinearMap) :
    Function.Injective fK := by
  intro x y hxy
  have hx : v (f (u.symm x)) = fK x := by
    simpa using congrArg (fun φ : M' →ₗ[R] K ↦ φ (u.symm x)) huv
  have hy : v (f (u.symm y)) = fK y := by
    simpa using congrArg (fun φ : M' →ₗ[R] K ↦ φ (u.symm y)) huv
  have hxy' : u.symm x = u.symm y := hf <| v.injective <| hx.trans (hxy.trans hy.symm)
  exact u.symm.injective hxy'

private theorem surjective_of_commSq
    {g : M →ₗ[R] M''} {gK : K →ₗ[R] K''}
    (hg : Function.Surjective g) (v : M ≃ₗ[R] K) (w : M'' ≃ₗ[R] K'')
    (hvw : w.toLinearMap.comp g = gK.comp v.toLinearMap) :
    Function.Surjective gK := by
  intro z
  obtain ⟨y, hy⟩ := hg (w.symm z)
  refine ⟨v y, ?_⟩
  have hy' : w (g y) = gK (v y) := by
    simpa using congrArg (fun φ : M →ₗ[R] K'' ↦ φ y) hvw
  calc
    gK (v y) = w (g y) := by simpa using hy'.symm
    _ = z := by simpa [hy]

private theorem exact_of_commSq
    {f : M' →ₗ[R] M} {g : M →ₗ[R] M''}
    {fK : K' →ₗ[R] K} {gK : K →ₗ[R] K''}
    (hexact : Function.Exact f g)
    (u : M' ≃ₗ[R] K') (v : M ≃ₗ[R] K) (w : M'' ≃ₗ[R] K'')
    (huv : v.toLinearMap.comp f = fK.comp u.toLinearMap)
    (hvw : w.toLinearMap.comp g = gK.comp v.toLinearMap) :
    Function.Exact fK gK := by
  exact Function.Exact.of_ladder_linearEquiv_of_exact huv.symm hvw.symm hexact

variable [Module.Finite R M'] [Module.Projective R M']
variable [Module.Finite R M] [Module.Projective R M]
variable [Module.Finite R M''] [Module.Projective R M'']
variable [Module.Finite R K'] [Module.Projective R K']
variable [Module.Finite R K] [Module.Projective R K]
variable [Module.Finite R K''] [Module.Projective R K'']

/-- Bridge/view: an isomorphism of presented short exact sequences of finite projective
`R`-modules intertwines the determinant-line comparison maps from Lemma `15.119.2`. The target-row
injectivity, surjectivity, and exactness hypotheses are derived internally by transport along the
given linear equivalences, and the underlying owner-level comparison is still the short-complex
determinant isomorphism `determinantTensorIso`. -/
theorem determinantTensorIsoOfShortExact_naturality
    (f : M' →ₗ[R] M) (g : M →ₗ[R] M'') (hf : Function.Injective f)
    (hg : Function.Surjective g) (hexact : Function.Exact f g)
    (fK : K' →ₗ[R] K) (gK : K →ₗ[R] K'') (u : M' ≃ₗ[R] K') (v : M ≃ₗ[R] K)
    (w : M'' ≃ₗ[R] K'')
    (huv : v.toLinearMap.comp f = fK.comp u.toLinearMap)
    (hvw : w.toLinearMap.comp g = gK.comp v.toLinearMap) :
    let hfK : Function.Injective fK := injective_of_commSq hf u v huv
    let hgK : Function.Surjective gK := surjective_of_commSq hg v w hvw
    let hexactK : Function.Exact fK gK := exact_of_commSq hexact u v w huv hvw
    CommSq
      (ModuleCat.ofHom <| (determinantTensorIsoOfShortExact f g hf hg hexact).toLinearMap)
      (ModuleCat.ofHom <|
        (TensorProduct.congr (determinantLineMap u) (determinantLineMap w)).toLinearMap)
      (ModuleCat.ofHom <| (determinantLineMap v).toLinearMap)
      (ModuleCat.ofHom <| (determinantTensorIsoOfShortExact fK gK hfK hgK hexactK).toLinearMap) :=
  by
  sorry

end Naturality
