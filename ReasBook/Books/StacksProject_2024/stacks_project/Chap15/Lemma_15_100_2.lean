import Mathlib
import StacksProject_2024.Chap15.«15_100_1_1»
import StacksProject_2024.Chap15.Definition_15_65_1
import StacksProject_2024.Chap15.Lemma_15_67_4
import StacksProject_2024.Chap15.Definition_15_75_1
import StacksProject_2024.Chap15.«15_74_0_2»
import StacksProject_2024.Chap15.Lemma_15_59_15

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

open scoped DerivedInternalHom DerivedTensorProduct DerivedTensorWithAlgebra

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

/-- The morphism on derived tensor functors induced by a morphism of right tensor factors, obtained
as the mate of the corresponding map on internal-Hom functors. -/
noncomputable def derivedTensorProductMap
    (H : RHomPkg)
    {L₁ L₂ : DModR} (f : L₁ ⟶ L₂) :
    derivedTensorProduct L₁ ⟶ derivedTensorProduct L₂ :=
  letI := H
  (conjugateEquiv (H.derivedTensorAdj L₂) (H.derivedTensorAdj L₁)).symm
    (MonoidalClosed.pre f)

/-- Lemma 15.74.5: in a monoidal closed structure on `D(R)`, there is a canonical morphism
`K \otimes_R^{\mathbf L} R\mathrm{Hom}_R(M, L) \to R\mathrm{Hom}_R(M, K \otimes_R^{\mathbf L} L)`
in `D(R)`. -/
noncomputable def derivedInternalHom_tensor_left_comparison
    (H : RHomPkg)
    (K L M : DModR) :
    (K ⊗[R]^L (RHom[H](M, L))) ⟶ RHom[H](M, K ⊗[R]^L L) :=
  (H.derivedTensorAdj M).homEquiv _ _
    ((derivedTensorProduct_associator K (RHom[H](M, L)) M).hom ≫
      (derivedTensorProductMap H ((H.derivedTensorAdj M).counit.app L)).app K)

/-- Helper for Lemma 15.100.2: finite tor dimension of an `R`-module yields some lower
tor-amplitude bound for its degree-zero derived object. -/
lemma module_hasFiniteTorDimension_hasTorAmplitudeGE
    (N : ModuleCat R)
    (hN : ModuleHasFiniteTorDimension N) :
    ∃ a : ℤ, HasTorAmplitudeGE ((single₀).obj N) a := by
  rcases hN with ⟨a, b, hAmp⟩
  -- A finite tor-amplitude interval immediately gives the lower bound needed later.
  exact ⟨a, hAmp.hasTorAmplitudeGE⟩

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
  sorry

end

end CategoryTheory
