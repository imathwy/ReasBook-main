import LinearRepresentations_Serre_1977.Chap18.Theorem_18_18_2_2

noncomputable section

open scoped Representation TensorProduct

universe u

namespace Representation

section Exercise181828ScalarExtensionSupport

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {K : Type u} [Field K]
variable {G : Type u} [Group G] [Finite G]

local notation "RK" => K ⊗[ℤ] R₀[k](G)
local notation "ClassFnK" => PRegularConjClass G p → K

/-- Helper for Exercise 18-18.2-8: the scalar-extended Brauer-character linear map on
`PRegularConjClass G p`, re-exported from the canonical Chapter `18` owner. -/
noncomputable def scalarExtensionBrauerCharacterOnPRegularConjClass
    (lift : PrimeToPRoot p k →* Kˣ) :
    RK →ₗ[K] ClassFnK :=
  scalarExtensionVirtualModularCharacterOnPRegularConjClass
    (p := p) (k := k) (K := K) (G := G) lift

/-- Helper for Exercise 18-18.2-8: the scalar-extended Brauer-character algebra homomorphism,
re-exported from the canonical Chapter `18` owner. -/
noncomputable def scalarExtensionBrauerCharacterOnPRegularConjClassAlgHom
    (lift : PrimeToPRoot p k →* Kˣ) :
    RK →ₐ[K] ClassFnK :=
  scalarExtensionVirtualModularCharacterOnPRegularConjClassAlgHom
    (p := p) (k := k) (K := K) (G := G) lift

/-- Helper for Exercise 18-18.2-8: the re-exported algebra hom evaluates by the same
scalar-extension Brauer-character linear map. -/
@[simp] theorem scalarExtensionBrauerCharacterOnPRegularConjClassAlgHom_apply
    (lift : PrimeToPRoot p k →* Kˣ) (x : RK) :
    scalarExtensionBrauerCharacterOnPRegularConjClassAlgHom
        (p := p) (k := k) (K := K) (G := G) lift x =
      scalarExtensionBrauerCharacterOnPRegularConjClass
        (p := p) (k := k) (K := K) (G := G) lift x :=
  rfl

section

variable [Fact p.Prime]

/-- Helper for Exercise 18-18.2-8: the scalar-extension Brauer-character algebra equivalence,
re-exported from the canonical Chapter `18` owner. -/
noncomputable def scalarExtensionBrauerCharacterOnPRegularConjClassAlgEquiv
    (lift : PrimeToPRoot p k →* Kˣ) (hlift : Function.Injective lift) :
    RK ≃ₐ[K] ClassFnK :=
  scalarExtensionVirtualModularCharacterOnPRegularConjClassAlgEquiv
    (p := p) (k := k) (K := K) (G := G) lift hlift

/-- Helper for Exercise 18-18.2-8: the re-exported algebra equivalence refines the same
scalar-extension Brauer-character algebra homomorphism. -/
@[simp] theorem scalarExtensionBrauerCharacterOnPRegularConjClassAlgEquiv_toAlgHom
    (lift : PrimeToPRoot p k →* Kˣ) (hlift : Function.Injective lift) :
    (scalarExtensionBrauerCharacterOnPRegularConjClassAlgEquiv
        (p := p) (k := k) (K := K) (G := G) lift hlift).toAlgHom =
      scalarExtensionBrauerCharacterOnPRegularConjClassAlgHom
        (p := p) (k := k) (K := K) (G := G) lift := by
  rfl

end

end Exercise181828ScalarExtensionSupport

end Representation
