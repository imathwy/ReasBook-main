import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap01.Theorem_1_1_4_2
import LinearRepresentations_Serre_1977.Serre.Chap07.Proposition_7_7_1_1
import LinearRepresentations_Serre_1977.Serre.Chap07.Proposition_7_7_1_3
import LinearRepresentations_Serre_1977.Serre.Chap07.Remark_7_7_1_4
import LinearRepresentations_Serre_1977.Serre.Chap07.Proposition_7_7_4_1.IdentityProjectionRepresentativeSeeds
import LinearRepresentations_Serre_1977.Serre.Chap08.Corollary_8_8_3_8
import LinearRepresentations_Serre_1977.Serre.Chap15.Exercise_15_15_5_3.ResidueFieldLift
import LinearRepresentations_Serre_1977.GroupTheory.PSolvable
import LinearRepresentations_Serre_1977.Serre.Chap17.Theorem_17_17_3_1.CyclicNormalByPGroupBasics
import LinearRepresentations_Serre_1977.Serre.Chap17.Theorem_17_17_3_1.CliffordIsotypicTransport
import LinearRepresentations_Serre_1977.Serre.Chap17.Theorem_17_17_3_1.ResidueFieldLiftTransport
import LinearRepresentations_Serre_1977.Serre.Chap17.Theorem_17_17_3_1.CyclicOrbitSpan

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w x

namespace Representation

open CategoryTheory Rep
open scoped Representation

section

variable {A : Type u} [CommRing A] [HenselianLocalRing A]
variable {G : Type v} [Group G] [Finite G]
variable {p : ℕ}

variable [CharP (IsLocalRing.ResidueField A) p]
variable {V : Type w} [AddCommGroup V] [Module (IsLocalRing.ResidueField A) V]
variable [FiniteDimensional (IsLocalRing.ResidueField A) V]
variable {C P : Subgroup G}

local notation "k" => IsLocalRing.ResidueField A
noncomputable local instance theorem1731ResidueFieldModule
    {W : Type*} [AddCommGroup W] [Module k W] : Module A W :=
  Module.compHom W (algebraMap A k)
local instance theorem1731ResidueFieldIsScalarTower
    {W : Type*} [AddCommGroup W] [Module k W] : IsScalarTower A k W :=
  IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl

/-- Helper for Theorem 17-17.3-1: the raw Chapter `14` residue-field reduction package attached
to a pair of source/target representations, without the extra free/finite hypotheses bundled into
`IsResidueFieldLift`. -/

private theorem scalarExtension_induced_source_coinvariants_backward_invariant_local
    {H : Subgroup G}
    {W0 : Type u} [AddCommGroup W0] [Module A W0]
    (ρA_HU : Representation A H W0)
    :
    let _ : Module A (G →₀ A) :=
      @Finsupp.module G A A inferInstance inferInstance (Semiring.toModule)
    let _ : Module A k := Algebra.toModule
    let _ : Module k k := Semiring.toModule
    let _ : Module k (TensorProduct A k (TensorProduct A (G →₀ A) W0)) :=
      TensorProduct.leftModule
    let _ : Module k (TensorProduct A k (Representation.IndV H.subtype ρA_HU)) :=
      TensorProduct.leftModule
    let ρrawA :=
      Representation.tprod ((Representation.leftRegular A G).comp H.subtype) ρA_HU
    let sourceScalarρ :
        Representation k H (TensorProduct A k (TensorProduct A (G →₀ A) W0)) :=
      Representation.scalarExtension ρrawA
    ∀ h : H,
      ((Representation.Coinvariants.mk ρrawA).baseChange k) ∘ₗ sourceScalarρ h =
        (Representation.Coinvariants.mk ρrawA).baseChange k := by
  letI : Module A (G →₀ A) :=
    @Finsupp.module G A A inferInstance inferInstance (Semiring.toModule)
  letI : Module A k := Algebra.toModule
  letI : Module k k := Semiring.toModule
  letI : Module k (TensorProduct A k (TensorProduct A (G →₀ A) W0)) :=
    TensorProduct.leftModule
  let ρrawA :=
    Representation.tprod ((Representation.leftRegular A G).comp H.subtype) ρA_HU
  let sourceScalarρ :
      Representation k H (TensorProduct A k (TensorProduct A (G →₀ A) W0)) :=
    Representation.scalarExtension ρrawA
  letI : Module k (TensorProduct A k (Representation.IndV H.subtype ρA_HU)) :=
    TensorProduct.leftModule
  letI : Module k (TensorProduct A k (Representation.Coinvariants ρrawA)) :=
    TensorProduct.leftModule
  dsimp
  intro h
  apply LinearMap.ext
  intro t
  refine TensorProduct.induction_on t ?_ ?_ ?_
  · simp [LinearMap.comp_apply]
  · intro z y
    -- Normalize the scalar-extended action to `z ⊗ ρrawA h y`, then apply the raw coinvariants
    -- relation before base change.
    rw [LinearMap.comp_apply]
    have hscalar :
        sourceScalarρ h (z ⊗ₜ[A] y) = z ⊗ₜ[A] (ρrawA h y) := by
      change (LinearMap.baseChange k (ρrawA h)) (z ⊗ₜ[A] y) = z ⊗ₜ[A] (ρrawA h y)
      rw [LinearMap.baseChange_tmul]
    rw [hscalar]
    rw [LinearMap.baseChange_tmul (f := Representation.Coinvariants.mk ρrawA) (A := k) z
      (ρrawA h y)]
    rw [LinearMap.baseChange_tmul (f := Representation.Coinvariants.mk ρrawA) (A := k) z y]
    exact congrArg (fun t ↦ z ⊗ₜ[A] t)
      (Representation.Coinvariants.mk_self_apply ρrawA h y)
  · intro t₁ t₂ ht₁ ht₂
    simp [LinearMap.comp_apply, map_add, ht₁, ht₂]

/- Helper for Theorem 17-17.3-1: the inverse quotient map descends the base-changed quotient map
`k ⊗ mk : k ⊗ X → k ⊗ X_G`, again using only the universal property of `Coinvariants`. -/
set_option maxHeartbeats 4000000 in
private noncomputable def scalarExtension_induced_source_coinvariants_backward_local
    {H : Subgroup G}
    {W0 : Type u} [AddCommGroup W0] [Module A W0]
    (ρA_HU : Representation A H W0)
    :
    let _ : Module A (G →₀ A) :=
      @Finsupp.module G A A inferInstance inferInstance (Semiring.toModule)
    let _ : Module A k := Algebra.toModule
    let _ : Module k k := Semiring.toModule
    let _ : Module k (TensorProduct A k (TensorProduct A (G →₀ A) W0)) :=
      TensorProduct.leftModule
    let _ : Module k (TensorProduct A k (Representation.IndV H.subtype ρA_HU)) :=
      TensorProduct.leftModule
    let ρrawA :=
      Representation.tprod ((Representation.leftRegular A G).comp H.subtype) ρA_HU
    let sourceScalarρ :
        Representation k H (TensorProduct A k (TensorProduct A (G →₀ A) W0)) :=
      Representation.scalarExtension ρrawA
    Representation.Coinvariants sourceScalarρ →ₗ[k]
      TensorProduct A k (Representation.IndV H.subtype ρA_HU) :=
  by
  letI : Module A (G →₀ A) :=
    @Finsupp.module G A A inferInstance inferInstance (Semiring.toModule)
  letI : Module A k := Algebra.toModule
  letI : Module k k := Semiring.toModule
  letI : Module k (TensorProduct A k (TensorProduct A (G →₀ A) W0)) :=
    TensorProduct.leftModule
  let ρrawA :=
    Representation.tprod ((Representation.leftRegular A G).comp H.subtype) ρA_HU
  let sourceScalarρ :
      Representation k H (TensorProduct A k (TensorProduct A (G →₀ A) W0)) :=
    Representation.scalarExtension ρrawA
  letI : Module k (TensorProduct A k (Representation.IndV H.subtype ρA_HU)) :=
    TensorProduct.leftModule
  letI : Module k (TensorProduct A k (Representation.Coinvariants ρrawA)) :=
    TensorProduct.leftModule
  -- Descend the base-changed quotient map once; the relation is exactly the pure-tensor
  -- compatibility proved above.
  exact
    Representation.Coinvariants.lift sourceScalarρ
      ((Representation.Coinvariants.mk ρrawA).baseChange k)
      (scalarExtension_induced_source_coinvariants_backward_invariant_local ρA_HU)

/-- Helper for Theorem 17-17.3-1: on raw tensor classes, the backward map is the obvious
base-changed quotient map `[(z ⊗ y)] ↦ z ⊗ [y]`. -/
