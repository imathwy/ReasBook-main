import Mathlib
import stacks_project.Chap15.Lemma_15_99_3
import stacks_project.Chap15.Lemma_15_100_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R R' : Type u} [CommRing R] [CommRing R'] [Algebra R R']

local notation "DModR" => DerivedCategory (ModuleCat R)
local notation "DModR'" => DerivedCategory (ModuleCat R')
local notation "RHomPkg" => MonoidalClosed DModR
local notation "single₀" => DerivedCategory.singleFunctor (ModuleCat R) (0 : ℤ)

open scoped DerivedInternalHom DerivedTensorWithAlgebra

/- Domain-style sampling for Lemma 15.100.2:
- primary domain: derived base change for internal Hom on derived module categories;
- sampled owner declarations:
  `derivedInternalHom_tensor_left_comparison`,
  `derivedInternalHomTensorLeftComparison_hom_isIso_of_isPerfect_or_of_pseudoCoherent_boundedBelow_torAmplitudeGE`,
  `derivedInternalHomTensorLeftComparison_hom_isIso_of_source_isPerfect`,
  `derivedInternalHomTensorLeftComparison_hom_isIso_of_tensor_isPerfect`,
  `derivedInternalHomTensorLeftComparison_hom_isIso_of_isPseudoCoherent_of_boundedBelow_of_hasTorAmplitudeGE`,
  `Adjunction.rightAdjointUniq`;
- best owner abstraction:
  `source-facing`: the base-change morphism
    `RHom_R(K, M) ⊗^L_R R' → RHom_{R'}(K ⊗^L_R R', M ⊗^L_R R')`;
  `core/canonical`: a chosen owner `H : MonoidalClosed DModR`, Lemma `15.74.5` specialized to the
    tensor factor `R'[0]`, and the isomorphism criterion of Lemma `15.99.3`;
  `bridge/view`: the pointwise component of
    `adj.rightAdjointUniq (H'.derivedTensorAdj (K ⊗[R]^L[R']))`, with
    `H' : MonoidalClosed DModR' := inferInstance`, which rewrites the codomain into the
    target-ring internal Hom;
- primitive data: `K.IsPerfect`, `((single₀).obj (ModuleCat.of R R')).IsPerfect`,
  `K.IsPseudoCoherent`, `∃ n : ℤ, M.IsGE n`, and
  `HasTorAmplitudeGE ((single₀).obj (ModuleCat.of R R')) a`;
- derived API: the finite-tor-dimension hypothesis on `ModuleCat.of R R'`, which is only used to
  produce some lower tor-amplitude bound for `R'[0]`.

This item therefore should not introduce a second owner for the comparison morphism: the public
statement is a direct specialization of the chapter’s canonical tensor-left comparison, and the
displayed target-ring internal-Hom form is the companion bridge supplied by the canonical
right-adjoint uniqueness component from `15.100.1`.
-/

/- Companion target rewrite: the canonical right-adjoint uniqueness component from `15.100.1`
identifies the codomain of the owner comparison with the displayed target-ring internal Hom. -/
set_option linter.hashCommand false in
#check fun [MonoidalClosed DModR'] (K : DModR) (G : DModR' ⥤ DModR')
    (adj : derivedTensorProduct (K ⊗[R]^L[R']) ⊣ G) (M : DModR') ↦
  let H' : MonoidalClosed DModR' := inferInstance
  ((adj.rightAdjointUniq (H'.derivedTensorAdj (K ⊗[R]^L[R']))).app M).hom

/-- Lemma 15.100.2, owner-level form: the canonical tensor-left comparison with tensor factor
`R'[0]`
`R'[0] \otimes_R^{\mathbf L} R\mathrm{Hom}_R(K, M) \to
R\mathrm{Hom}_R(K, R'[0] \otimes_R^{\mathbf L} M)`
is an isomorphism whenever either `K` is perfect, or `R'` is perfect as an `R`-module, or `R'`
has finite tor dimension as an `R`-module and `K` is pseudo-coherent with `M ∈ D^+(R)`. Via
Lemma `15.100.1`, this is exactly the displayed base-change isomorphism
`R\mathrm{Hom}_R(K, M) \otimes_R^{\mathbf L} R' \to
R\mathrm{Hom}_{R'}(K \otimes_R^{\mathbf L} R', M \otimes_R^{\mathbf L} R')`. -/
theorem derivedInternalHom_baseChange_comparison_isIso_of_isPerfect_or_of_pseudoCoherent_boundedBelow
    (H : RHomPkg)
    (K M : DModR)
    (hcases :
      K.IsPerfect ∨
        (ModuleCat.of R R').IsPerfect ∨
          (K.IsPseudoCoherent ∧
            (∃ n : ℤ, M.IsGE n) ∧
            ModuleHasFiniteTorDimension (ModuleCat.of R R'))) :
    IsIso
      (derivedInternalHom_tensor_left_comparison H
        ((single₀).obj (ModuleCat.of R R'))
        M K) := by
  rcases hcases with hK | hR' | hpc
  · simpa using
      (derivedInternalHomTensorLeftComparison_hom_isIso_of_source_isPerfect
        H
        ((single₀).obj (ModuleCat.of R R'))
        M K hK)
  · simpa using
      (derivedInternalHomTensorLeftComparison_hom_isIso_of_tensor_isPerfect
        H
        ((single₀).obj (ModuleCat.of R R'))
        M K hR')
  · rcases hpc with ⟨hKpc, hM, htor⟩
    rcases htor with ⟨a, _, htor⟩
    simpa using
      (derivedInternalHomTensorLeftComparison_hom_isIso_of_isPseudoCoherent_of_boundedBelow_of_hasTorAmplitudeGE
        H
        ((single₀).obj (ModuleCat.of R R'))
        M K a hKpc hM htor.hasTorAmplitudeGE)

end

end CategoryTheory
