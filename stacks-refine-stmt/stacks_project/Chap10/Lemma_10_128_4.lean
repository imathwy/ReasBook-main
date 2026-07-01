import stacks_project.Chap10.Definition_10_54_1
import stacks_project.Chap10.Lemma_10_99_1

open IsLocalRing
open scoped TensorProduct

universe u v w x

section

variable {R : Type u} {S : Type v} {M : Type w} {N : Type x}
variable [CommRing R] [CommRing S] [IsLocalRing R] [Algebra R S]
variable [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
variable [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]

/- Domain-style sampling for Lemma 10.128.4:
- primary domain: the local flatness criterion for finitely presented modules over a local
  homomorphism, with the closed-fiber injectivity hypothesis on the quotient map modulo the
  maximal ideal and a standard residue-field tensor reformulation;
- sampled owner declarations:
  `LinearMap.quotientMapByIdeal`,
  `TensorProduct.quotTensorEquivQuotSMul`,
  `injective_of_mod_maximalIdeal_injective`,
  `flat_quotient_of_mod_maximalIdeal_injective`;
- best owner abstraction: the source-facing closed-fiber map is the reduction map
  `LinearMap.quotientMapByIdeal (maximalIdeal R)`; the residue-field tensor formulation is only a
  bridge to this owner via `TensorProduct.quotTensorEquivQuotSMul`;
- primitive data: the local map `R → S`, the essentially finitely presented `R`-algebra structure
  on `S`, canonically exposed in Chapter 10 as
  `RingHom.EssFinitePresentation (algebraMap R S)`, the finitely presented `S`-modules `M` and
  `N`, the `R`-flatness of `N`, and the injectivity of the closed-fiber map of `u`;
- derived API: injectivity of `u` and `R`-flatness of the quotient by its image.

Source/core/bridge triage:
- `source-facing`: Lemma 10.128.4 itself, phrased with injectivity of
  `M / maximalIdeal R • M → N / maximalIdeal R • N`;
- `core/canonical`: `Function.Injective`, `Module.Flat`, and the Chapter 10 owner theorems
  `injective_of_mod_maximalIdeal_injective` and
  `flat_quotient_of_mod_maximalIdeal_injective`;
- `bridge/view`: the standard closed-fiber identification
  `(R ⧸ maximalIdeal R) ⊗[R] M ≃ M ⧸ maximalIdeal R • ⊤`, implemented by
  `TensorProduct.quotTensorEquivQuotSMul`, converts the source-facing hypothesis to the quotient
  criterion used by the core owner theorems.
-/

-- Proof sketch: use the canonical closed-fiber identification
-- `(R ⧸ maximalIdeal R) ⊗[R] M ≃ M / maximalIdeal R • M` to convert the source-facing residue-field
-- injectivity hypothesis into injectivity of the quotient reduction map
-- `M / maximalIdeal R • M → N / maximalIdeal R • N`. Then apply the owner theorems from Lemma
-- `10.99.1` to obtain injectivity of `u` and flatness of its quotient.
/-- Bridge theorem: injectivity after tensoring with the residue field implies injectivity of the
reduction map modulo `maximalIdeal R`, which is the canonical quotient criterion used by Lemma
`10.99.1`. -/
theorem injective_mod_maximalIdeal_of_lTensor_residueField_injective
    (u : M →ₗ[S] N)
    (hbar : Function.Injective ((u.restrictScalars R).lTensor (ResidueField R))) :
    Function.Injective ((u.restrictScalars R).quotientMapByIdeal (maximalIdeal R)) := by
  sorry

-- Proof sketch: apply the owner theorems from Lemma `10.99.1` directly to the closed-fiber map
-- modulo `maximalIdeal R`; the quotient by the `R`-linear range of `u.restrictScalars R` is
-- definitionally the same module as the quotient by the `S`-linear range of `u`, viewed by
-- restriction of scalars.
/-- Lemma 10.128.4: for a local homomorphism `R → S` with `S` essentially of finite presentation
over `R`, if `M` and `N` are finitely presented `S`-modules, `N` is flat over `R`, and the
induced map `M / maximalIdeal R • M → N / maximalIdeal R • N` is injective, then `u` is injective
and its quotient is flat over `R`. -/
theorem injective_and_flat_quotient_of_mod_maximalIdeal_injective
    [IsLocalRing S] [IsLocalHom (algebraMap R S)]
    [Module.FinitePresentation S M] [Module.FinitePresentation S N] [Module.Flat R N]
    (hess : RingHom.EssFinitePresentation (algebraMap R S)) (u : M →ₗ[S] N)
    (hmod : Function.Injective ((u.restrictScalars R).quotientMapByIdeal (maximalIdeal R))) :
    Function.Injective u ∧ Module.Flat R (N ⧸ LinearMap.range u) := by
  have hess' : Algebra.EssFinitePresentation R S :=
    RingHom.essFinitePresentation_algebraMap.mp hess
  letI := hess'
  have hu : Function.Injective (u.restrictScalars R) :=
    injective_of_mod_maximalIdeal_injective (u.restrictScalars R) hmod
  have hflat : Module.Flat R (N ⧸ LinearMap.range (u.restrictScalars R)) :=
    flat_quotient_of_mod_maximalIdeal_injective (u.restrictScalars R) hmod
  refine ⟨hu, ?_⟩
  simpa [LinearMap.range_restrictScalars] using hflat

-- Proof sketch: bridge the residue-field injectivity hypothesis to injectivity of the closed-fiber
-- quotient map, then apply Lemma `10.128.4` in its source-facing quotient form.
/-- Companion reformulation of Lemma 10.128.4: the residue-field tensor criterion implies the
source-facing closed-fiber injectivity hypothesis, hence the same injectivity and flat-quotient
conclusion. -/
theorem injective_and_flat_quotient_of_lTensor_residueField_injective
    [IsLocalRing S] [IsLocalHom (algebraMap R S)]
    [Module.FinitePresentation S M] [Module.FinitePresentation S N] [Module.Flat R N]
    (hess : RingHom.EssFinitePresentation (algebraMap R S)) (u : M →ₗ[S] N)
    (hbar : Function.Injective ((u.restrictScalars R).lTensor (ResidueField R))) :
    Function.Injective u ∧ Module.Flat R (N ⧸ LinearMap.range u) := by
  exact
    injective_and_flat_quotient_of_mod_maximalIdeal_injective hess u
      (injective_mod_maximalIdeal_of_lTensor_residueField_injective u hbar)

end
