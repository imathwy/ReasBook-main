import Mathlib
import LinearRepresentations_Serre_1977.Chap01.Theorem_1_1_4_2
import LinearRepresentations_Serre_1977.Chap07.Proposition_7_7_1_1
import LinearRepresentations_Serre_1977.Chap07.Proposition_7_7_1_3
import LinearRepresentations_Serre_1977.Chap07.Remark_7_7_1_4
import LinearRepresentations_Serre_1977.Chap07.Proposition_7_7_4_1.IdentityProjectionRepresentativeSeeds
import LinearRepresentations_Serre_1977.Chap08.Corollary_8_8_3_8
import LinearRepresentations_Serre_1977.Chap15.Exercise_15_15_5_3.ResidueFieldLift
import LinearRepresentations_Serre_1977.GroupTheory.PSolvable
import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_3_1.CyclicNormalByPGroupBasics
import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_3_1.CliffordIsotypicTransport
import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_3_1.ResidueFieldLiftTransport
import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_3_1.CyclicOrbitSpan
import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_3_1.ProperOvergroupRecursion
import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_3_1.ResidueFieldLiftInductionTransport
import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_3_1.ULiftScalarExtensionPreparation
import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_3_1.InducedScalarExtensionTransport

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w x

namespace Representation

open CategoryTheory Rep
open scoped Representation

section ScalarExtensionCoinvariantsGeneric

-- NOTE: this generic section must stay above the `local notation "k"` declaration below, since
-- the named argument `(k := S)` would otherwise collide with that notation.

variable {R : Type*} [CommRing R] {S : Type*} [CommRing S] [Algebra R S]
variable {Γ : Type*} [Group Γ]
variable {X : Type*} [AddCommGroup X] [Module R X]

/-- Generic helper for Theorem 17-17.3-1: the coinvariants quotient map absorbs the group
action, stated at the composition level over an opaque module so the concrete
induced-representation carrier never has to be unfolded. -/
private theorem coinvariantsMk_comp_self_generic
    (ρ : Representation R Γ X) (γ : Γ) :
    Representation.Coinvariants.mk ρ ∘ₗ ρ γ = Representation.Coinvariants.mk ρ :=
  LinearMap.ext fun x => Representation.Coinvariants.mk_self_apply ρ γ x

/-- Generic helper for Theorem 17-17.3-1: the base-changed coinvariants quotient map is
invariant under the scalar-extended action. Proved over an opaque base module so that the
concrete instantiation below is a single cheap application instead of a tensor-induction on the
huge induced carrier. -/
private theorem baseChange_coinvariantsMk_comp_scalarExtension_generic
    (ρ : Representation R Γ X) (γ : Γ) :
    ((Representation.Coinvariants.mk ρ).baseChange S) ∘ₗ
        (Representation.scalarExtension (k := S) ρ) γ =
      (Representation.Coinvariants.mk ρ).baseChange S := by
  have hact : (Representation.scalarExtension (k := S) ρ) γ = (ρ γ).baseChange S := rfl
  rw [hact, ← LinearMap.baseChange_comp, coinvariantsMk_comp_self_generic ρ γ]

end ScalarExtensionCoinvariantsGeneric

section

variable {A : Type u} [CommRing A] [HenselianLocalRing A]
variable {G : Type v} [Group G] [Finite G]
variable {p : ℕ}

variable [CharP (IsLocalRing.ResidueField A) p]
variable {V : Type w} [AddCommGroup V] [Module (IsLocalRing.ResidueField A) V]
variable [FiniteDimensional (IsLocalRing.ResidueField A) V]
variable {C P : Subgroup G}

local notation "k" => IsLocalRing.ResidueField A
noncomputable local instance inducedCoinvariantsMapsResidueFieldModule
    {W : Type*} [AddCommGroup W] [Module k W] : Module A W :=
  Module.compHom W (algebraMap A k)
local instance inducedCoinvariantsMapsResidueFieldIsScalarTower
    {W : Type*} [AddCommGroup W] [Module k W] : IsScalarTower A k W :=
  IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl

/-- Helper for Theorem 17-17.3-1: Serre's quotient step is implemented directly by sending
`z ⊗ [x]` to `[z ⊗ x]`, avoiding the earlier transport-heavy `range = ker` detour. -/
theorem scalarExtension_induced_source_coinvariants_forward_apply_act_local
    {H : Subgroup G}
    {W0 : Type x} [AddCommGroup W0] [Module A W0]
    (ρA_HU : Representation A H W0)
    (z : k) (h : H) :
    let _ : Module A (G →₀ A) :=
      @Finsupp.module G A A inferInstance inferInstance (Semiring.toModule)
    let _ : Module A k := Algebra.toModule
    let _ : Module k k := Semiring.toModule
    let _ : Module k (TensorProduct A k (TensorProduct A (G →₀ A) W0)) :=
      TensorProduct.leftModule
    let ρrawA : Representation A H (TensorProduct A (G →₀ A) W0) :=
      Representation.tprod ((Representation.leftRegular A G).comp H.subtype) ρA_HU
    let sourceScalarρ :
        Representation k H (TensorProduct A k (TensorProduct A (G →₀ A) W0)) :=
      Representation.scalarExtension ρrawA
    ∀ y : TensorProduct A (G →₀ A) W0,
      Representation.Coinvariants.mk sourceScalarρ (z ⊗ₜ[A] (ρrawA h y)) =
        Representation.Coinvariants.mk sourceScalarρ (z ⊗ₜ[A] y) := by
  classical
  letI : Module A (G →₀ A) :=
    @Finsupp.module G A A inferInstance inferInstance (Semiring.toModule)
  letI : Module A k := Algebra.toModule
  letI : Module k k := Semiring.toModule
  letI : Module k (TensorProduct A k (TensorProduct A (G →₀ A) W0)) :=
    TensorProduct.leftModule
  letI : IsScalarTower A k (TensorProduct A k (TensorProduct A (G →₀ A) W0)) :=
    IsScalarTower.of_algebraMap_smul fun a x ↦ by
      refine TensorProduct.induction_on x ?_ ?_ ?_
      · simp
      · intro z y
        simp [IsLocalRing.ResidueField.algebraMap_eq, Algebra.smul_def, TensorProduct.smul_tmul']
      · intro x₁ x₂ hx₁ hx₂
        have hx₁' : (IsLocalRing.residue A a) • x₁ = a • x₁ := by
          simpa [IsLocalRing.ResidueField.algebraMap_eq] using hx₁
        have hx₂' : (IsLocalRing.residue A a) • x₂ = a • x₂ := by
          simpa [IsLocalRing.ResidueField.algebraMap_eq] using hx₂
        rw [smul_add, smul_add, hx₁, hx₂]
  let ρrawA : Representation A H (TensorProduct A (G →₀ A) W0) :=
    Representation.tprod ((Representation.leftRegular A G).comp H.subtype) ρA_HU
  let sourceScalarρ :
      Representation k H (TensorProduct A k (TensorProduct A (G →₀ A) W0)) :=
    Representation.scalarExtension ρrawA
  -- Route correction: normalize the scalar-extended action on `z ⊗ y` before applying the
  -- coinvariants quotient relation, rather than transporting through a `range = ker` equality.
  change ∀ y : TensorProduct A (G →₀ A) W0,
      Representation.Coinvariants.mk sourceScalarρ (z ⊗ₜ[A] (ρrawA h y)) =
        Representation.Coinvariants.mk sourceScalarρ (z ⊗ₜ[A] y)
  intro y
  -- The scalar extension action is the base-changed raw action, so `baseChange_tmul` rewrites the
  -- left side into the canonical orbit representative killed by `mk_self_apply`.
  rw [← LinearMap.baseChange_tmul (f := ρrawA h) (A := k) z y]
  exact Representation.Coinvariants.mk_self_apply sourceScalarρ h (z ⊗ₜ[A] y)

/-- Helper for Theorem 17-17.3-1: Serre's quotient step is implemented directly by sending
`z ⊗ [x]` to `[z ⊗ x]`, avoiding the earlier transport-heavy `range = ker` detour. -/
noncomputable def scalarExtension_induced_source_coinvariants_forward_fixed_z_linear_local
    {H : Subgroup G}
    {W0 : Type x} [AddCommGroup W0] [Module A W0]
    (ρA_HU : Representation A H W0)
    (z : k) :
    let _ : Module A (G →₀ A) :=
      @Finsupp.module G A A inferInstance inferInstance (Semiring.toModule)
    let _ : Module A k := Algebra.toModule
    let _ : Module k k := Semiring.toModule
    let _ : Module k (TensorProduct A k (TensorProduct A (G →₀ A) W0)) :=
      TensorProduct.leftModule
    let ρrawA : Representation A H (TensorProduct A (G →₀ A) W0) :=
      Representation.tprod ((Representation.leftRegular A G).comp H.subtype) ρA_HU
    let sourceScalarρ :
        Representation k H (TensorProduct A k (TensorProduct A (G →₀ A) W0)) :=
      Representation.scalarExtension ρrawA
    TensorProduct A (G →₀ A) W0 →ₗ[A] Representation.Coinvariants sourceScalarρ := by
  letI : Module A (G →₀ A) :=
    @Finsupp.module G A A inferInstance inferInstance (Semiring.toModule)
  letI : Module A k := Algebra.toModule
  letI : Module k k := Semiring.toModule
  letI : Module k (TensorProduct A k (TensorProduct A (G →₀ A) W0)) :=
    TensorProduct.leftModule
  let ρrawA : Representation A H (TensorProduct A (G →₀ A) W0) :=
    Representation.tprod ((Representation.leftRegular A G).comp H.subtype) ρA_HU
  let sourceScalarρ :
      Representation k H (TensorProduct A k (TensorProduct A (G →₀ A) W0)) :=
    Representation.scalarExtension ρrawA
  -- Package the raw map `y ↦ [z ⊗ y]` as an explicit composition so Lean never has to infer the
  -- inner `A`-linearity from an anonymous lambda.
  refine
    { toFun := fun y ↦ Representation.Coinvariants.mk sourceScalarρ (z ⊗ₜ[A] y)
      map_add' := by
        intro y₁ y₂
        simp [TensorProduct.tmul_add]
      map_smul' := by
        intro a y
        show
          Representation.Coinvariants.mk sourceScalarρ (z ⊗ₜ[A] (a • y)) =
            Representation.Coinvariants.mk sourceScalarρ (((a • z : k)) ⊗ₜ[A] y)
        exact congrArg (Representation.Coinvariants.mk sourceScalarρ)
          (TensorProduct.tmul_smul a z y) }

/-- Helper for Theorem 17-17.3-1: for fixed `z`, the raw map `y ↦ [z ⊗ y]` descends through the
induction coinvariants quotient because the scalar-extended action preserves those classes. -/
noncomputable def scalarExtension_induced_source_coinvariants_forward_fixed_z_local
    {H : Subgroup G}
    {W0 : Type x} [AddCommGroup W0] [Module A W0]
    (ρA_HU : Representation A H W0)
    (z : k) :
    let _ : Module A (G →₀ A) :=
      @Finsupp.module G A A inferInstance inferInstance (Semiring.toModule)
    let _ : Module A k := Algebra.toModule
    let _ : Module k k := Semiring.toModule
    let _ : Module k (TensorProduct A k (TensorProduct A (G →₀ A) W0)) :=
      TensorProduct.leftModule
    let ρrawA : Representation A H (TensorProduct A (G →₀ A) W0) :=
      Representation.tprod ((Representation.leftRegular A G).comp H.subtype) ρA_HU
    let sourceScalarρ :
        Representation k H (TensorProduct A k (TensorProduct A (G →₀ A) W0)) :=
      Representation.scalarExtension ρrawA
    ρrawA.Coinvariants →ₗ[A] sourceScalarρ.Coinvariants := by
  letI : Module A (G →₀ A) :=
    @Finsupp.module G A A inferInstance inferInstance (Semiring.toModule)
  letI : Module A k := Algebra.toModule
  letI : Module k k := Semiring.toModule
  letI : Module k (TensorProduct A k (TensorProduct A (G →₀ A) W0)) :=
    TensorProduct.leftModule
  let ρrawA : Representation A H (TensorProduct A (G →₀ A) W0) :=
    Representation.tprod ((Representation.leftRegular A G).comp H.subtype) ρA_HU
  let sourceScalarρ :
      Representation k H (TensorProduct A k (TensorProduct A (G →₀ A) W0)) :=
    Representation.scalarExtension ρrawA
  -- Descend the fixed-`z` raw map once; the needed relation is exactly the generator equality
  -- proved in `scalarExtension_induced_source_coinvariants_forward_apply_act_local`.
  exact
    Representation.Coinvariants.lift ρrawA
      (scalarExtension_induced_source_coinvariants_forward_fixed_z_linear_local
        (A := A) (G := G) (ρA_HU := ρA_HU) z)
      (fun h ↦ by
        apply TensorProduct.ext'
        intro f xU
        simpa [scalarExtension_induced_source_coinvariants_forward_fixed_z_linear_local,
          LinearMap.comp_apply] using
          scalarExtension_induced_source_coinvariants_forward_apply_act_local
            (A := A) (G := G) (ρA_HU := ρA_HU) z h ((f : G →₀ A) ⊗ₜ[A] xU))

/-- Helper for Theorem 17-17.3-1: on standard induced generators, the fixed-`z` descended map is
exactly Serre's class `[(z ⊗ single g ⊗ x)]`. -/
theorem scalarExtension_induced_source_coinvariants_forward_fixed_z_apply_mk_local
    {H : Subgroup G}
    {W0 : Type x} [AddCommGroup W0] [Module A W0]
    (ρA_HU : Representation A H W0)
    (z : k) (g : G) (xU : W0) :
    let _ : Module A (G →₀ A) :=
      @Finsupp.module G A A inferInstance inferInstance (Semiring.toModule)
    let _ : Module A k := Algebra.toModule
    let _ : Module k k := Semiring.toModule
    let _ : Module k (TensorProduct A k (TensorProduct A (G →₀ A) W0)) :=
      TensorProduct.leftModule
    let ρrawA :=
      Representation.tprod ((Representation.leftRegular A G).comp H.subtype) ρA_HU
    let sourceScalarρ :
        Representation k H (TensorProduct A k (TensorProduct A (G →₀ A) W0)) :=
      Representation.scalarExtension ρrawA
    scalarExtension_induced_source_coinvariants_forward_fixed_z_local ρA_HU z
        (Representation.IndV.mk H.subtype ρA_HU g xU) =
      Representation.Coinvariants.mk sourceScalarρ
        (z ⊗ₜ[A] ((Finsupp.single g (1 : A)) ⊗ₜ[A] xU)) := by
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
  -- Evaluate the quotient lift on the canonical induced generator and then unfold the fixed-`z`
  -- wrapper only once.
  simp [scalarExtension_induced_source_coinvariants_forward_fixed_z_local,
    scalarExtension_induced_source_coinvariants_forward_fixed_z_linear_local,
    Representation.IndV.mk, LinearMap.comp_apply]

/-- Helper for Theorem 17-17.3-1: Serre's quotient step is implemented directly by sending
`z ⊗ [x]` to `[z ⊗ x]`, with the outer scalar handled by base change of the fixed-`1` quotient
map. -/
noncomputable def scalarExtension_induced_source_coinvariants_forward_local
    {H : Subgroup G}
    {W0 : Type x} [AddCommGroup W0] [Module A W0]
    (ρA_HU : Representation A H W0) :
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
    TensorProduct A k (Representation.IndV H.subtype ρA_HU) →ₗ[k]
      Representation.Coinvariants sourceScalarρ := by
  letI : Module A (G →₀ A) :=
    @Finsupp.module G A A inferInstance inferInstance (Semiring.toModule)
  letI : Module A k := Algebra.toModule
  letI : Module k k := Semiring.toModule
  letI : Module k (TensorProduct A k (TensorProduct A (G →₀ A) W0)) :=
    TensorProduct.leftModule
  letI : Module k (TensorProduct A k (Representation.IndV H.subtype ρA_HU)) :=
    TensorProduct.leftModule
  let ρrawA :=
    Representation.tprod ((Representation.leftRegular A G).comp H.subtype) ρA_HU
  let sourceScalarρ :
      Representation k H (TensorProduct A k (TensorProduct A (G →₀ A) W0)) :=
    Representation.scalarExtension ρrawA
  -- Route correction: first descend the fixed-`1` raw map, then let `liftBaseChange` handle the
  -- outer scalar variable. This keeps the source proof's quotient map while avoiding the failed
  -- anonymous-lambda elaboration path.
  exact
    (scalarExtension_induced_source_coinvariants_forward_fixed_z_local ρA_HU (1 : k)).liftBaseChange k

/-- Helper for Theorem 17-17.3-1: on pure tensors, the forward map is Serre's formula
`z ⊗ [x] ↦ [z ⊗ x]`. -/
theorem scalarExtension_induced_source_coinvariants_forward_apply_tmul_mk_local
    {H : Subgroup G}
    {W0 : Type x} [AddCommGroup W0] [Module A W0]
    (ρA_HU : Representation A H W0)
    (z : k) (g : G) (xU : W0) :
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
    scalarExtension_induced_source_coinvariants_forward_local
        (A := A) (G := G) (ρA_HU := ρA_HU)
        (z ⊗ₜ[A] Representation.IndV.mk H.subtype ρA_HU g xU) =
      Representation.Coinvariants.mk sourceScalarρ
        (z ⊗ₜ[A] ((Finsupp.single g (1 : A)) ⊗ₜ[A] xU)) :=
by
  letI : Module A (G →₀ A) :=
    @Finsupp.module G A A inferInstance inferInstance (Semiring.toModule)
  letI : Module A k := Algebra.toModule
  letI : Module k k := Semiring.toModule
  letI : Module k (TensorProduct A k (TensorProduct A (G →₀ A) W0)) :=
    TensorProduct.leftModule
  letI : Module k (TensorProduct A k (Representation.IndV H.subtype ρA_HU)) :=
    TensorProduct.leftModule
  let ρrawA :=
    Representation.tprod ((Representation.leftRegular A G).comp H.subtype) ρA_HU
  let sourceScalarρ :
      Representation k H (TensorProduct A k (TensorProduct A (G →₀ A) W0)) :=
    Representation.scalarExtension ρrawA
  -- Evaluate the base-changed fixed-`1` quotient map on the pure tensor, then rewrite the outer
  -- scalar as a scalar on the raw tensor representative.
  calc
    scalarExtension_induced_source_coinvariants_forward_local
        (A := A) (G := G) (ρA_HU := ρA_HU)
        (z ⊗ₜ[A] Representation.IndV.mk H.subtype ρA_HU g xU)
        =
      z •
        scalarExtension_induced_source_coinvariants_forward_fixed_z_local
          (A := A) (G := G) (ρA_HU := ρA_HU) (1 : k)
          (Representation.IndV.mk H.subtype ρA_HU g xU) := by
            simp [scalarExtension_induced_source_coinvariants_forward_local,
              LinearMap.liftBaseChange_tmul]
    _ =
      z • Representation.Coinvariants.mk sourceScalarρ
        ((1 : k) ⊗ₜ[A] ((Finsupp.single g (1 : A)) ⊗ₜ[A] xU)) := by
          rw [scalarExtension_induced_source_coinvariants_forward_fixed_z_apply_mk_local
            (A := A) (G := G) (ρA_HU := ρA_HU)]
    _ =
      Representation.Coinvariants.mk sourceScalarρ
        (z • ((1 : k) ⊗ₜ[A] ((Finsupp.single g (1 : A)) ⊗ₜ[A] xU))) := by
          rw [← (Representation.Coinvariants.mk sourceScalarρ).map_smul]
    _ =
      Representation.Coinvariants.mk sourceScalarρ
        (z ⊗ₜ[A] ((Finsupp.single g (1 : A)) ⊗ₜ[A] xU)) := by
          congr 1
          simpa [one_mul] using
            (TensorProduct.smul_tmul' z (1 : k)
              (((Finsupp.single g (1 : A)) ⊗ₜ[A] xU) :
                TensorProduct A (G →₀ A) W0))

/-
The old duplicate induced-lift packaging block stays deleted here: the canonical proper-overgroup
branch now runs through the finished local owner theorems later in this file, and reintroducing the
large commented copy only recreates elaboration pressure without changing Serre's proof route. -/

-- This universal-property statement is instantiated from the generic opaque-module lemma above,
-- so it stays within the default heartbeat budget.
theorem scalarExtension_induced_source_coinvariants_backward_invariant_local
    {H : Subgroup G}
    {W0 : Type x} [AddCommGroup W0] [Module A W0]
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
  -- Introduce the statement's `let`-bound instances and representations as local definitions, so
  -- the goal stays small, then apply the generic opaque-module invariance lemma.
  intro _ _ _ _ _ ρrawA sourceScalarρ h
  exact baseChange_coinvariantsMk_comp_scalarExtension_generic ρrawA h

/- Helper for Theorem 17-17.3-1: the inverse quotient map descends the base-changed quotient map
`k ⊗ mk : k ⊗ X → k ⊗ X_G`, again using only the universal property of `Coinvariants`. -/
noncomputable def scalarExtension_induced_source_coinvariants_backward_local
    {H : Subgroup G}
    {W0 : Type x} [AddCommGroup W0] [Module A W0]
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
  -- Introduce the statement's `let`-bound instances and representations as local definitions, so
  -- the goal stays small, then descend the base-changed quotient map once; the invariance
  -- relation is the generic opaque-module lemma proved above.
  intro _ _ _ _ _ ρrawA sourceScalarρ
  exact
    Representation.Coinvariants.lift sourceScalarρ
      ((Representation.Coinvariants.mk ρrawA).baseChange k)
      (fun h => baseChange_coinvariantsMk_comp_scalarExtension_generic ρrawA h)

/-- Helper for Theorem 17-17.3-1: on raw tensor classes, the backward map is the obvious
base-changed quotient map `[(z ⊗ y)] ↦ z ⊗ [y]`. -/
theorem scalarExtension_induced_source_coinvariants_backward_apply_mk_local
    {H : Subgroup G}
    {W0 : Type x} [AddCommGroup W0] [Module A W0]
    (ρA_HU : Representation A H W0) :
    let _ : Module A (G →₀ A) :=
      @Finsupp.module G A A inferInstance inferInstance (Semiring.toModule)
    let _ : Module A k := Algebra.toModule
    let _ : Module k k := Semiring.toModule
    let _ : Module k (TensorProduct A k (Representation.IndV H.subtype ρA_HU)) :=
      TensorProduct.leftModule
    let ρrawA :=
      Representation.tprod ((Representation.leftRegular A G).comp H.subtype) ρA_HU
    let sourceScalarρ :
        Representation k H (TensorProduct A k (TensorProduct A (G →₀ A) W0)) :=
      Representation.scalarExtension ρrawA
    ∀ z : k, ∀ y : TensorProduct A (G →₀ A) W0,
      scalarExtension_induced_source_coinvariants_backward_local ρA_HU
          (Representation.Coinvariants.mk sourceScalarρ (z ⊗ₜ[A] y)) =
        z ⊗ₜ[A] Representation.Coinvariants.mk ρrawA y :=
by
  letI : Module A (G →₀ A) :=
    @Finsupp.module G A A inferInstance inferInstance (Semiring.toModule)
  letI : Module A k := Algebra.toModule
  letI : Module k k := Semiring.toModule
  letI : Module k (TensorProduct A k (Representation.IndV H.subtype ρA_HU)) :=
    TensorProduct.leftModule
  let ρrawA :=
    Representation.tprod ((Representation.leftRegular A G).comp H.subtype) ρA_HU
  let sourceScalarρ :
      Representation k H (TensorProduct A k (TensorProduct A (G →₀ A) W0)) :=
    Representation.scalarExtension ρrawA
  intro z y
  -- Evaluate the descended quotient lift on the raw tensor representative and unfold the
  -- base-changed quotient map once.
  simp [scalarExtension_induced_source_coinvariants_backward_local, LinearMap.baseChange_tmul]

/-- Helper for Theorem 17-17.3-1: scalar extension commutes with the induction coinvariants
quotient, expressed directly as a linear equivalence rather than through a submodule equality. -/
theorem scalarExtension_induced_source_coinvariants_backward_forward_apply_tmul_mk_local
    {H : Subgroup G}
    {W0 : Type x} [AddCommGroup W0] [Module A W0]
    (ρA_HU : Representation A H W0)
    (z : k) (g : G) (xU : W0) :
    let _ : Module A (G →₀ A) :=
      @Finsupp.module G A A inferInstance inferInstance (Semiring.toModule)
    let _ : Module A k := Algebra.toModule
    let _ : Module k k := Semiring.toModule
    let _ : Module k (TensorProduct A k (Representation.IndV H.subtype ρA_HU)) :=
      TensorProduct.leftModule
    let ρrawA :=
      Representation.tprod ((Representation.leftRegular A G).comp H.subtype) ρA_HU
    let sourceScalarρ :
        Representation k H (TensorProduct A k (TensorProduct A (G →₀ A) W0)) :=
      Representation.scalarExtension ρrawA
    scalarExtension_induced_source_coinvariants_backward_local
        ρA_HU
        (scalarExtension_induced_source_coinvariants_forward_local
          (A := A) (G := G) (ρA_HU := ρA_HU)
          (z ⊗ₜ[A] Representation.IndV.mk H.subtype ρA_HU g xU)) =
      z ⊗ₜ[A] Representation.IndV.mk H.subtype ρA_HU g xU := by
  letI : Module A (G →₀ A) :=
    @Finsupp.module G A A inferInstance inferInstance (Semiring.toModule)
  letI : Module A k := Algebra.toModule
  letI : Module k k := Semiring.toModule
  letI : Module k (TensorProduct A k (Representation.IndV H.subtype ρA_HU)) :=
    TensorProduct.leftModule
  let ρrawA :=
    Representation.tprod ((Representation.leftRegular A G).comp H.subtype) ρA_HU
  let sourceScalarρ :
      Representation k H (TensorProduct A k (TensorProduct A (G →₀ A) W0)) :=
    Representation.scalarExtension ρrawA
  -- On the standard pure tensors, Serre's forward map and the base-changed quotient map are
  -- visibly inverse after both are rewritten on the canonical raw representative.
  calc
    scalarExtension_induced_source_coinvariants_backward_local
        ρA_HU
        (scalarExtension_induced_source_coinvariants_forward_local
          (A := A) (G := G) (ρA_HU := ρA_HU)
          (z ⊗ₜ[A] Representation.IndV.mk H.subtype ρA_HU g xU)) =
      scalarExtension_induced_source_coinvariants_backward_local
        ρA_HU
        (Representation.Coinvariants.mk sourceScalarρ
          (z ⊗ₜ[A] ((Finsupp.single g (1 : A)) ⊗ₜ[A] xU))) := by
            rw [scalarExtension_induced_source_coinvariants_forward_apply_tmul_mk_local
              (A := A) (G := G) (ρA_HU := ρA_HU)]
    _ = z ⊗ₜ[A] Representation.Coinvariants.mk ρrawA
          ((Finsupp.single g (1 : A)) ⊗ₜ[A] xU) := by
            rw [scalarExtension_induced_source_coinvariants_backward_apply_mk_local
              (A := A) (G := G) (ρA_HU := ρA_HU)]
    _ = z ⊗ₜ[A] Representation.IndV.mk H.subtype ρA_HU g xU := by
          rfl



end

end Representation
