import Mathlib
import LinearRepresentations_Serre_1977.Chap14.Corollary_14_14_3_3
import LinearRepresentations_Serre_1977.Chap14.Exercise_14_14_4_5
import LinearRepresentations_Serre_1977.Chap14.Infra_14_4_ProjectiveLift
import LinearRepresentations_Serre_1977.Chap14.Lemma_14_14_4_1
import LinearRepresentations_Serre_1977.Chap15.Definition_15_15_1_1
import LinearRepresentations_Serre_1977.Chap15.Definition_15_15_2_1
import LinearRepresentations_Serre_1977.Chap15.Definition_15_15_3_1
import LinearRepresentations_Serre_1977.Chap15.Exercise_15_15_2_5
import LinearRepresentations_Serre_1977.Chap15.Exercise_15_15_2_6.Foundations
import LinearRepresentations_Serre_1977.Chap15.Exercise_15_15_5_3.LocalProjectiveBridges
import LinearRepresentations_Serre_1977.Chap15.Proposition_15_15_5_1.ReductionMkQ
import LinearRepresentations_Serre_1977.Chap15.Proposition_15_15_5_1.StableLatticeExactOwner
import LinearRepresentations_Serre_1977.Chap15.Proposition_15_15_5_1.ReductionIsoReflection
import LinearRepresentations_Serre_1977.Chap15.Theorem_15_15_2_2

noncomputable section

open CategoryTheory
open Representation
open scoped MonoidAlgebra Representation TensorProduct

universe u v

section DecompositionHom

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [HenselianLocalRing A]
variable [CharP (IsLocalRing.ResidueField A) p]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]

local notation "k" => IsLocalRing.ResidueField A
local notation:max "R_K(" G ")" => finiteRepGrothendieckGroup K G
local notation:max "R_k(" G ")" => finiteRepGrothendieckGroup k G

/-- Helper for Proposition 15-15.5-1: a representation equivalence induces the corresponding
group-algebra-linear equivalence on owner modules. -/
private noncomputable def representationEquiv_asModuleLinearEquiv_local
    {F : Type u} [Field F]
    {H : Type u} [Group H]
    {W W' : Type v} [AddCommGroup W] [Module F W]
    [AddCommGroup W'] [Module F W']
    {ρ : Representation F H W} {σ : Representation F H W'}
    (e : ρ.Equiv σ) :
    ρ.asModule ≃ₗ[F[H]] σ.asModule := by
  refine
    { toFun := (Representation.IntertwiningMap.equivLinearMapAsModule ρ σ) e.toIntertwiningMap
      invFun := (Representation.IntertwiningMap.equivLinearMapAsModule σ ρ) e.symm.toIntertwiningMap
      left_inv := by
        intro x
        -- The inverse owner map is the inverse representation equivalence.
        change e.symm (e x) = x
        simp
      right_inv := by
        intro x
        -- The same simplification closes the inverse direction.
        change e (e.symm x) = x
        simp
      map_add' := by
        intro x y
        simp
      map_smul' := by
        intro r x
        simp }

/-- Helper for Proposition 15-15.5-1: complementary reduced subrepresentations split the reduced
owner module as a `k[G]`-linear product. -/
theorem subrepresentation_prod_nonempty_asModuleLinearEquiv_of_isCompl_local
    {F : Type u} [Field F]
    {W : Type v} [AddCommGroup W] [Module F W]
    {ρ : Representation F G W}
    (U V : Subrepresentation ρ)
    (hUV : IsCompl U.toSubmodule V.toSubmodule) :
    Nonempty (asModule (U.toRepresentation.prod V.toRepresentation) ≃ₗ[F[G]] asModule ρ) := by
  let eRep : (U.toRepresentation.prod V.toRepresentation).Equiv ρ :=
    .mk (U.toSubmodule.prodEquivOfIsCompl V.toSubmodule hUV) <| by
      intro g
      -- The direct-sum equivalence respects the `G`-action coordinatewise on the two summands.
      ext z
      · simpa [Submodule.coe_prodEquivOfIsCompl, LinearMap.comp_apply, LinearMap.coe_inl,
          LinearMap.coprod_apply, LinearMap.prodMap_apply, Submodule.coe_subtype,
          Representation.prod] using
          (show ↑((U.toRepresentation g) z) = (ρ g) ↑z from rfl)
      · simpa [Submodule.coe_prodEquivOfIsCompl, LinearMap.comp_apply, LinearMap.coe_inr,
          LinearMap.coprod_apply, LinearMap.prodMap_apply, Submodule.coe_subtype,
          Representation.prod] using
          (show ↑((V.toRepresentation g) z) = (ρ g) ↑z from rfl)
  -- Repackage the representation equivalence as a `F[G]`-linear equivalence of owner modules.
  exact ⟨representationEquiv_asModuleLinearEquiv_local eRep⟩

/-- Helper for Proposition 15-15.5-1: the product subrepresentation action agrees on each group
generator with the factorwise `Representation.ofModule'` action on the same carrier. -/
private theorem subrepresentation_prod_group_apply_eq_ofModule'_local
    {F : Type u} [Field F]
    {W : Type v} [AddCommGroup W] [Module F W]
    {ρ : Representation F G W}
    (U V : Subrepresentation ρ)
    (g : G) (x : U.toSubmodule × V.toSubmodule) :
    letI : Module F[G] U.toSubmodule :=
      Module.compHom U.toSubmodule U.toRepresentation.asAlgebraHom.toRingHom
    letI : Module F[G] V.toSubmodule :=
      Module.compHom V.toSubmodule V.toRepresentation.asAlgebraHom.toRingHom
    letI : IsScalarTower F F[G] U.toSubmodule :=
      IsScalarTower.of_algebraMap_smul fun d y ↦ by
        change U.toRepresentation.asAlgebraHom (algebraMap F F[G] d) y = d • y
        simp [Algebra.smul_def]
    letI : IsScalarTower F F[G] V.toSubmodule :=
      IsScalarTower.of_algebraMap_smul fun d y ↦ by
        change V.toRepresentation.asAlgebraHom (algebraMap F F[G] d) y = d • y
        simp [Algebra.smul_def]
    let Dom := U.toSubmodule × V.toSubmodule
    letI : IsScalarTower F F[G] Dom := inferInstance
    ((U.toRepresentation.prod V.toRepresentation) g) x =
      ((Representation.ofModule' Dom : Representation F G Dom) g) x := by
  letI : Module F[G] U.toSubmodule :=
    Module.compHom U.toSubmodule U.toRepresentation.asAlgebraHom.toRingHom
  letI : Module F[G] V.toSubmodule :=
    Module.compHom V.toSubmodule V.toRepresentation.asAlgebraHom.toRingHom
  letI : IsScalarTower F F[G] U.toSubmodule :=
    IsScalarTower.of_algebraMap_smul fun d y ↦ by
      change U.toRepresentation.asAlgebraHom (algebraMap F F[G] d) y = d • y
      simp [Algebra.smul_def]
  letI : IsScalarTower F F[G] V.toSubmodule :=
    IsScalarTower.of_algebraMap_smul fun d y ↦ by
      change V.toRepresentation.asAlgebraHom (algebraMap F F[G] d) y = d • y
      simp [Algebra.smul_def]
  let Dom := U.toSubmodule × V.toSubmodule
  letI : IsScalarTower F F[G] Dom := inferInstance
  -- Route correction: compare the two bundled `G`-actions directly on generators instead of
  -- re-opening the unstable same-carrier `a • x` transport problem.
  ext <;> simp [Representation.ofModule', Representation.prod]
  · simpa [Representation.asAlgebraHom_of] using
      (show (U.toRepresentation.asAlgebraHom (MonoidAlgebra.of F G g)) x.1 =
          (MonoidAlgebra.of F G g • x.1 : U.toSubmodule) by
        rfl)
  · simpa [Representation.asAlgebraHom_of] using
      (show (V.toRepresentation.asAlgebraHom (MonoidAlgebra.of F G g)) x.2 =
          (MonoidAlgebra.of F G g • x.2 : V.toSubmodule) by
        rfl)

/-- Helper for Proposition 15-15.5-1: the identity map on the product carrier is an equivalence
between the product subrepresentation and the factorwise `Representation.ofModule'` owner. -/
private theorem subrepresentation_prod_to_factorwise_ofModule'_equiv_local
    {F : Type u} [Field F]
    {W : Type v} [AddCommGroup W] [Module F W]
    {ρ : Representation F G W}
    (U V : Subrepresentation ρ) :
    letI : Module F[G] U.toSubmodule :=
      Module.compHom U.toSubmodule U.toRepresentation.asAlgebraHom.toRingHom
    letI : Module F[G] V.toSubmodule :=
      Module.compHom V.toSubmodule V.toRepresentation.asAlgebraHom.toRingHom
    letI : IsScalarTower F F[G] U.toSubmodule :=
      IsScalarTower.of_algebraMap_smul fun d y ↦ by
        change U.toRepresentation.asAlgebraHom (algebraMap F F[G] d) y = d • y
        simp [Algebra.smul_def]
    letI : IsScalarTower F F[G] V.toSubmodule :=
      IsScalarTower.of_algebraMap_smul fun d y ↦ by
        change V.toRepresentation.asAlgebraHom (algebraMap F F[G] d) y = d • y
        simp [Algebra.smul_def]
    let Dom := U.toSubmodule × V.toSubmodule
    letI : IsScalarTower F F[G] Dom := inferInstance
    Nonempty ((U.toRepresentation.prod V.toRepresentation).Equiv
      (Representation.ofModule' Dom)) := by
  letI : Module F[G] U.toSubmodule :=
    Module.compHom U.toSubmodule U.toRepresentation.asAlgebraHom.toRingHom
  letI : Module F[G] V.toSubmodule :=
    Module.compHom V.toSubmodule V.toRepresentation.asAlgebraHom.toRingHom
  letI : IsScalarTower F F[G] U.toSubmodule :=
    IsScalarTower.of_algebraMap_smul fun d y ↦ by
      change U.toRepresentation.asAlgebraHom (algebraMap F F[G] d) y = d • y
      simp [Algebra.smul_def]
  letI : IsScalarTower F F[G] V.toSubmodule :=
    IsScalarTower.of_algebraMap_smul fun d y ↦ by
      change V.toRepresentation.asAlgebraHom (algebraMap F F[G] d) y = d • y
      simp [Algebra.smul_def]
  let Dom := U.toSubmodule × V.toSubmodule
  letI : IsScalarTower F F[G] Dom := inferInstance
  -- The carrier does not change; the previous lemma supplies the intertwining condition.
  refine ⟨Representation.Equiv.mk (LinearEquiv.refl F Dom) ?_⟩
  intro g
  refine LinearMap.ext ?_
  intro y
  exact subrepresentation_prod_group_apply_eq_ofModule'_local (G := G) U V g y

/-- Helper for Proposition 15-15.5-1: the `asModule` owner of a product subrepresentation agrees
with the canonical coordinatewise product of the two factor owners. -/
private theorem subrepresentation_factorwise_product_to_asModule_product_linearEquiv_local
    {F : Type u} [Field F]
    {W : Type v} [AddCommGroup W] [Module F W]
    {ρ : Representation F G W}
    (U V : Subrepresentation ρ) :
    letI : Module F[G] U.toSubmodule :=
      Module.compHom U.toSubmodule U.toRepresentation.asAlgebraHom.toRingHom
    letI : Module F[G] V.toSubmodule :=
      Module.compHom V.toSubmodule V.toRepresentation.asAlgebraHom.toRingHom
    Nonempty ((U.toSubmodule × V.toSubmodule) ≃ₗ[F[G]]
      (asModule U.toRepresentation × asModule V.toRepresentation)) := by
  letI : Module F[G] U.toSubmodule :=
    Module.compHom U.toSubmodule U.toRepresentation.asAlgebraHom.toRingHom
  letI : Module F[G] V.toSubmodule :=
    Module.compHom V.toSubmodule V.toRepresentation.asAlgebraHom.toRingHom
  rcases
      nonempty_asModuleLinearEquiv_target_field_local
        (G := G) (ρ := U.toRepresentation) with
    ⟨eU⟩
  rcases
      nonempty_asModuleLinearEquiv_target_field_local
        (G := G) (ρ := V.toRepresentation) with
    ⟨eV⟩
  -- The factorwise owner is the direct product of the two exact owners, so the product of the
  -- two carrier identifications gives the desired `F[G]`-linear equivalence.
  exact ⟨LinearEquiv.prodCongr eU.symm eV.symm⟩

/-- Helper for Proposition 15-15.5-1: the `asModule` owner of a product subrepresentation agrees
with the canonical coordinatewise product of the two factor owners. -/
theorem subrepresentation_prod_asModule_to_factorwise_product_linearEquiv_local
    {F : Type u} [Field F]
    {W : Type v} [AddCommGroup W] [Module F W]
    {ρ : Representation F G W}
    (U V : Subrepresentation ρ) :
    Nonempty (asModule (U.toRepresentation.prod V.toRepresentation) ≃ₗ[F[G]]
      (asModule U.toRepresentation × asModule V.toRepresentation)) := by
  letI : Module F[G] U.toSubmodule :=
    Module.compHom U.toSubmodule U.toRepresentation.asAlgebraHom.toRingHom
  letI : Module F[G] V.toSubmodule :=
    Module.compHom V.toSubmodule V.toRepresentation.asAlgebraHom.toRingHom
  letI : IsScalarTower F F[G] U.toSubmodule :=
    IsScalarTower.of_algebraMap_smul fun d y ↦ by
      change U.toRepresentation.asAlgebraHom (algebraMap F F[G] d) y = d • y
      simp [Algebra.smul_def]
  letI : IsScalarTower F F[G] V.toSubmodule :=
    IsScalarTower.of_algebraMap_smul fun d y ↦ by
      change V.toRepresentation.asAlgebraHom (algebraMap F F[G] d) y = d • y
      simp [Algebra.smul_def]
  let Dom := U.toSubmodule × V.toSubmodule
  letI : IsScalarTower F F[G] Dom := inferInstance
  rcases subrepresentation_prod_to_factorwise_ofModule'_equiv_local (G := G) U V with ⟨eRep⟩
  rcases nonempty_ofModule'_asModuleLinearEquiv (G := G) F Dom with ⟨eDom⟩
  rcases
      subrepresentation_factorwise_product_to_asModule_product_linearEquiv_local
        (G := G) U V with
    ⟨eProd⟩
  -- Compose the bundled representation comparison with the canonical `ofModule'` owner
  -- identification and the already proved factorwise bridge.
  exact ⟨(representationEquiv_asModuleLinearEquiv_local eRep).trans (eDom.trans eProd)⟩

/-- Helper for Proposition 15-15.5-1: residue-field reduction commutes with binary products of
`A[G]`-modules. -/
private theorem reduction_prod_tmul_eq_smul_unit_tmul_local
    {P Q : Type v} [AddCommGroup P] [Module A P] [Module A[G] P] [IsScalarTower A A[G] P]
    [AddCommGroup Q] [Module A Q] [Module A[G] Q] [IsScalarTower A A[G] Q]
    (c : k) (p : P) (q : Q) :
    (c ⊗ₜ[A] (p, q) : k ⊗[A] (P × Q)) = c • ((1 : k) ⊗ₜ[A] (p, q)) := by
  -- Normalize to a tensor whose left factor is `1`.
  calc
    (c ⊗ₜ[A] (p, q) : k ⊗[A] (P × Q))
        = ((c • (1 : k)) ⊗ₜ[A] (p, q) : k ⊗[A] (P × Q)) := by simp
    _ = c • ((1 : k) ⊗ₜ[A] (p, q)) := by
          rw [TensorProduct.smul_tmul']

/-- Helper for Proposition 15-15.5-1: `TensorProduct.prodRight` respects the reduced group-algebra
action on pure tensors. -/
private theorem reduction_prodRight_map_monoidAlgebra_of_local
    {P Q : Type v} [AddCommGroup P] [Module A P] [Module A[G] P] [IsScalarTower A A[G] P]
    [AddCommGroup Q] [Module A Q] [Module A[G] Q] [IsScalarTower A A[G] Q]
    (g : G) (c : k) (p : P) (q : Q) :
    TensorProduct.prodRight A k k P Q
        (MonoidAlgebra.of k G g • (c ⊗ₜ[A] (p, q) : k ⊗[A] (P × Q))) =
      MonoidAlgebra.of k G g •
        TensorProduct.prodRight A k k P Q (c ⊗ₜ[A] (p, q) : k ⊗[A] (P × Q)) := by
  have hp :
      MonoidAlgebra.of k G g • (((1 : k) ⊗ₜ[A] p) : k ⊗[A] P) =
        (((1 : k) ⊗ₜ[A] (MonoidAlgebra.of A G g • p)) : k ⊗[A] P) := by
    simpa using
      (MonoidAlgebra.tensorProduct_mk_map_monoidAlgebra_of
        (Λ := A) (G := G) (P := P) g p).symm
  have hq :
      MonoidAlgebra.of k G g • (((1 : k) ⊗ₜ[A] q) : k ⊗[A] Q) =
        (((1 : k) ⊗ₜ[A] (MonoidAlgebra.of A G g • q)) : k ⊗[A] Q) := by
    simpa using
      (MonoidAlgebra.tensorProduct_mk_map_monoidAlgebra_of
        (Λ := A) (G := G) (P := Q) g q).symm
  have hpair :
      MonoidAlgebra.of k G g •
          ((((1 : k) ⊗ₜ[A] p) : k ⊗[A] P), (((1 : k) ⊗ₜ[A] q) : k ⊗[A] Q)) =
        ((((1 : k) ⊗ₜ[A] (MonoidAlgebra.of A G g • p)) : k ⊗[A] P),
          (((1 : k) ⊗ₜ[A] (MonoidAlgebra.of A G g • q)) : k ⊗[A] Q)) := by
    ext <;> assumption
  -- Transport the normalized pure-tensor computation through `TensorProduct.prodRight`.
  calc
    TensorProduct.prodRight A k k P Q
        (MonoidAlgebra.of k G g • (c ⊗ₜ[A] (p, q) : k ⊗[A] (P × Q))) =
      TensorProduct.prodRight A k k P Q
        (c • (MonoidAlgebra.of k G g • ((1 : k) ⊗ₜ[A] (p, q) : k ⊗[A] (P × Q)))) := by
          rw [reduction_prod_tmul_eq_smul_unit_tmul_local
            (A := A) (G := G) (P := P) (Q := Q) c p q]
          rw [smul_comm]
    _ = c • TensorProduct.prodRight A k k P Q
        (MonoidAlgebra.of k G g • ((1 : k) ⊗ₜ[A] (p, q) : k ⊗[A] (P × Q))) := by
          rw [map_smul]
    _ = c • TensorProduct.prodRight A k k P Q
        (((1 : k) ⊗ₜ[A] (MonoidAlgebra.of A G g • (p, q)) : k ⊗[A] (P × Q))) := by
          refine congrArg (fun t ↦ c • TensorProduct.prodRight A k k P Q t) ?_
          simpa using
            (MonoidAlgebra.tensorProduct_mk_map_monoidAlgebra_of
              (Λ := A) (G := G) (P := P × Q) g (p, q)).symm
    _ = c •
        ((((1 : k) ⊗ₜ[A] (MonoidAlgebra.of A G g • p)) : k ⊗[A] P),
          (((1 : k) ⊗ₜ[A] (MonoidAlgebra.of A G g • q)) : k ⊗[A] Q)) := by
          simp [TensorProduct.prodRight_tmul]
    _ = c •
        (MonoidAlgebra.of k G g •
          ((((1 : k) ⊗ₜ[A] p) : k ⊗[A] P), (((1 : k) ⊗ₜ[A] q) : k ⊗[A] Q))) := by
          rw [hpair]
    _ = MonoidAlgebra.of k G g •
        (c • ((((1 : k) ⊗ₜ[A] p) : k ⊗[A] P), (((1 : k) ⊗ₜ[A] q) : k ⊗[A] Q))) := by
          rw [smul_comm]
    _ = MonoidAlgebra.of k G g •
        TensorProduct.prodRight A k k P Q (c ⊗ₜ[A] (p, q) : k ⊗[A] (P × Q)) := by
          rw [show c • ((((1 : k) ⊗ₜ[A] p) : k ⊗[A] P), (((1 : k) ⊗ₜ[A] q) : k ⊗[A] Q)) =
            TensorProduct.prodRight A k k P Q (c ⊗ₜ[A] (p, q) : k ⊗[A] (P × Q)) by
              rw [reduction_prod_tmul_eq_smul_unit_tmul_local
                (A := A) (G := G) (P := P) (Q := Q) c p q]
              simp [TensorProduct.prodRight_tmul]]

/-- Helper for Proposition 15-15.5-1: a pure tensor in the scalar-extended product is a scalar
multiple of one with left tensor factor `1`. -/
private theorem scalarExtension_prod_tmul_eq_smul_unit_tmul_local
    {P Q : Type v} [AddCommGroup P] [Module A P] [Module A[G] P] [IsScalarTower A A[G] P]
    [AddCommGroup Q] [Module A Q] [Module A[G] Q] [IsScalarTower A A[G] Q]
    (c : K) (p : P) (q : Q) :
    (c ⊗ₜ[A] (p, q) : K ⊗[A] (P × Q)) = c • ((1 : K) ⊗ₜ[A] (p, q)) := by
  -- Normalize to a pure tensor of the form `1 ⊗ x`.
  calc
    (c ⊗ₜ[A] (p, q) : K ⊗[A] (P × Q))
        = ((c • (1 : K)) ⊗ₜ[A] (p, q) : K ⊗[A] (P × Q)) := by simp
    _ = c • ((1 : K) ⊗ₜ[A] (p, q)) := by
          rw [TensorProduct.smul_tmul']

/-- Helper for Proposition 15-15.5-1: `TensorProduct.prodRight` respects the scalar-extended
group-algebra action on pure tensors. -/
private theorem scalarExtension_prodRight_map_monoidAlgebra_of_local
    {P Q : Type v} [AddCommGroup P] [Module A P] [Module A[G] P] [IsScalarTower A A[G] P]
    [AddCommGroup Q] [Module A Q] [Module A[G] Q] [IsScalarTower A A[G] Q]
    (g : G) (c : K) (p : P) (q : Q) :
    TensorProduct.prodRight A K K P Q
        (MonoidAlgebra.of K G g • (c ⊗ₜ[A] (p, q) : K ⊗[A] (P × Q))) =
      MonoidAlgebra.of K G g •
        TensorProduct.prodRight A K K P Q (c ⊗ₜ[A] (p, q) : K ⊗[A] (P × Q)) := by
  have hp :
      MonoidAlgebra.of K G g • (((1 : K) ⊗ₜ[A] p) : K ⊗[A] P) =
        (((1 : K) ⊗ₜ[A] (MonoidAlgebra.of A G g • p)) : K ⊗[A] P) := by
    simpa using monoidAlgebra_of_smul_tmul (Λ := A) (κ := K) (G := G) (P := P) g 1 p
  have hq :
      MonoidAlgebra.of K G g • (((1 : K) ⊗ₜ[A] q) : K ⊗[A] Q) =
        (((1 : K) ⊗ₜ[A] (MonoidAlgebra.of A G g • q)) : K ⊗[A] Q) := by
    simpa using monoidAlgebra_of_smul_tmul (Λ := A) (κ := K) (G := G) (P := Q) g 1 q
  have hpair :
      MonoidAlgebra.of K G g •
          ((((1 : K) ⊗ₜ[A] p) : K ⊗[A] P), (((1 : K) ⊗ₜ[A] q) : K ⊗[A] Q)) =
        ((((1 : K) ⊗ₜ[A] (MonoidAlgebra.of A G g • p)) : K ⊗[A] P),
          (((1 : K) ⊗ₜ[A] (MonoidAlgebra.of A G g • q)) : K ⊗[A] Q)) := by
    ext <;> assumption
  -- Transport the normalized pure-tensor computation through `TensorProduct.prodRight`.
  calc
    TensorProduct.prodRight A K K P Q
        (MonoidAlgebra.of K G g • (c ⊗ₜ[A] (p, q) : K ⊗[A] (P × Q))) =
      TensorProduct.prodRight A K K P Q
        (c • (MonoidAlgebra.of K G g • ((1 : K) ⊗ₜ[A] (p, q) : K ⊗[A] (P × Q)))) := by
          rw [scalarExtension_prod_tmul_eq_smul_unit_tmul_local
            (A := A) (K := K) (G := G) (P := P) (Q := Q) c p q]
          rw [smul_comm]
    _ = c • TensorProduct.prodRight A K K P Q
        (MonoidAlgebra.of K G g • ((1 : K) ⊗ₜ[A] (p, q) : K ⊗[A] (P × Q))) := by
          rw [map_smul]
    _ = c • TensorProduct.prodRight A K K P Q
        (((1 : K) ⊗ₜ[A] (MonoidAlgebra.of A G g • (p, q)) : K ⊗[A] (P × Q))) := by
          refine congrArg (fun t ↦ c • TensorProduct.prodRight A K K P Q t) ?_
          simpa using
            monoidAlgebra_of_smul_tmul (Λ := A) (κ := K) (G := G) (P := P × Q) g 1 (p, q)
    _ = c •
        ((((1 : K) ⊗ₜ[A] (MonoidAlgebra.of A G g • p)) : K ⊗[A] P),
          (((1 : K) ⊗ₜ[A] (MonoidAlgebra.of A G g • q)) : K ⊗[A] Q)) := by
          simp [TensorProduct.prodRight_tmul]
    _ = c •
        (MonoidAlgebra.of K G g •
          ((((1 : K) ⊗ₜ[A] p) : K ⊗[A] P), (((1 : K) ⊗ₜ[A] q) : K ⊗[A] Q))) := by
          rw [hpair]
    _ = MonoidAlgebra.of K G g •
        (c • ((((1 : K) ⊗ₜ[A] p) : K ⊗[A] P), (((1 : K) ⊗ₜ[A] q) : K ⊗[A] Q))) := by
          rw [smul_comm]
    _ = MonoidAlgebra.of K G g •
        TensorProduct.prodRight A K K P Q (c ⊗ₜ[A] (p, q) : K ⊗[A] (P × Q)) := by
          rw [show c • ((((1 : K) ⊗ₜ[A] p) : K ⊗[A] P), (((1 : K) ⊗ₜ[A] q) : K ⊗[A] Q)) =
            TensorProduct.prodRight A K K P Q (c ⊗ₜ[A] (p, q) : K ⊗[A] (P × Q)) by
              rw [scalarExtension_prod_tmul_eq_smul_unit_tmul_local
                (A := A) (K := K) (G := G) (P := P) (Q := Q) c p q]
              simp [TensorProduct.prodRight_tmul]]

/-- Helper for Proposition 15-15.5-1: residue-field reduction commutes with binary products of
`A[G]`-modules. -/
theorem reduction_prod_nonempty_linearEquiv_local
    {P Q : Type v} [AddCommGroup P] [Module A P] [Module A[G] P] [IsScalarTower A A[G] P]
    [AddCommGroup Q] [Module A Q] [Module A[G] Q] [IsScalarTower A A[G] Q] :
    Nonempty (((k ⊗[A] (P × Q)) ≃ₗ[k[G]] (k ⊗[A] P) × (k ⊗[A] Q))) := by
  let e₀ : (k ⊗[A] (P × Q)) ≃ₗ[k] (k ⊗[A] P) × (k ⊗[A] Q) :=
    TensorProduct.prodRight A k k P Q
  refine ⟨
    { toFun := e₀
      invFun := e₀.symm
      left_inv := e₀.left_inv
      right_inv := e₀.right_inv
      map_add' := e₀.map_add
      map_smul' := ?_ }⟩
  intro a x
  -- Check equivariance on the `MonoidAlgebra.of` generators and then extend linearly.
  refine MonoidAlgebra.induction_on
    (p := fun b : k[G] => e₀ (b • x) = b • e₀ x) a ?_ ?_ ?_
  · intro g
    induction x using TensorProduct.induction_on with
    | zero =>
        simp [e₀]
    | tmul c y =>
        rcases y with ⟨p, q⟩
        simpa [e₀] using
          reduction_prodRight_map_monoidAlgebra_of_local
            (A := A) (G := G) (P := P) (Q := Q) g c p q
    | add y z hy hz =>
        simpa [MonoidAlgebra.of_apply, map_add, smul_add, e₀] using
          calc
            e₀ (MonoidAlgebra.of k G g • (y + z))
                = e₀ (MonoidAlgebra.of k G g • y) + e₀ (MonoidAlgebra.of k G g • z) := by
                    simp [map_add, smul_add, e₀]
            _ = MonoidAlgebra.of k G g • e₀ y + MonoidAlgebra.of k G g • e₀ z := by
                  rw [hy, hz]
            _ = MonoidAlgebra.of k G g • e₀ (y + z) := by
                  simp [smul_add, e₀]
  · intro b c hb hc
    simp [add_smul, map_add, hb, hc]
  · intro c b hb
    calc
      e₀ ((c • b) • x) = e₀ (c • (b • x)) := by rw [smul_assoc]
      _ = c • e₀ (b • x) := by exact e₀.toLinearMap.map_smul c (b • x)
      _ = c • (b • e₀ x) := by rw [hb]
      _ = (c • b) • e₀ x := by rw [smul_assoc]

/-- Helper for Proposition 15-15.5-1: scalar extension commutes with binary products of
`A[G]`-modules. -/
theorem scalarExtension_prod_nonempty_linearEquiv_local
    {P Q : Type v} [AddCommGroup P] [Module A P] [Module A[G] P] [IsScalarTower A A[G] P]
    [AddCommGroup Q] [Module A Q] [Module A[G] Q] [IsScalarTower A A[G] Q] :
    Nonempty (((K ⊗[A] (P × Q)) ≃ₗ[K[G]] (K ⊗[A] P) × (K ⊗[A] Q))) := by
  let e₀ : (K ⊗[A] (P × Q)) ≃ₗ[K] (K ⊗[A] P) × (K ⊗[A] Q) :=
    TensorProduct.prodRight A K K P Q
  refine ⟨
    { toFun := e₀
      invFun := e₀.symm
      left_inv := e₀.left_inv
      right_inv := e₀.right_inv
      map_add' := e₀.map_add
      map_smul' := ?_ }⟩
  intro a x
  -- As on the reduction side, it is enough to check equivariance on the group generators.
  refine MonoidAlgebra.induction_on
    (p := fun b : K[G] => e₀ (b • x) = b • e₀ x) a ?_ ?_ ?_
  · intro g
    induction x using TensorProduct.induction_on with
    | zero =>
        simp [e₀]
    | tmul c y =>
        rcases y with ⟨p, q⟩
        simpa [e₀] using
          scalarExtension_prodRight_map_monoidAlgebra_of_local
            (A := A) (K := K) (G := G) (P := P) (Q := Q) g c p q
    | add y z hy hz =>
        simpa [MonoidAlgebra.of_apply, map_add, smul_add, e₀] using
          calc
            e₀ (MonoidAlgebra.of K G g • (y + z))
                = e₀ (MonoidAlgebra.of K G g • y) + e₀ (MonoidAlgebra.of K G g • z) := by
                    simp [map_add, smul_add, e₀]
            _ = MonoidAlgebra.of K G g • e₀ y + MonoidAlgebra.of K G g • e₀ z := by
                  rw [hy, hz]
            _ = MonoidAlgebra.of K G g • e₀ (y + z) := by
                  simp [smul_add, e₀]
  · intro b c hb hc
    simp [add_smul, map_add, hb, hc]
  · intro c b hb
    calc
      e₀ ((c • b) • x) = e₀ (c • (b • x)) := by rw [smul_assoc]
      _ = c • e₀ (b • x) := by exact e₀.toLinearMap.map_smul c (b • x)
      _ = c • (b • e₀ x) := by rw [hb]
      _ = (c • b) • e₀ x := by rw [smul_assoc]

/-- Helper for Proposition 15-15.5-1: the product of two nonzero representations cannot be
irreducible. -/
theorem prod_representation_not_isIrreducible_of_nontrivial_local
    {F : Type u} [Field F]
    {P Q : Type v} [AddCommGroup P] [Module F P] [AddCommGroup Q] [Module F Q]
    {ρ : Representation F G P} {σ : Representation F G Q}
    [Nontrivial P] [Nontrivial Q] :
    ¬ (Representation.prod ρ σ).IsIrreducible := by
  intro hprod
  letI : (Representation.prod ρ σ).IsIrreducible := hprod
  let U : Subrepresentation (Representation.prod ρ σ) :=
    { toSubmodule := (⊤ : Submodule F P).prod (⊥ : Submodule F Q)
      apply_mem_toSubmodule := by
        intro g x hx
        have hx0 : x.2 = 0 := by simpa using hx.2
        exact ⟨Submodule.mem_top, by simpa [hx0] using LinearMap.map_zero (σ g)⟩ }
  have hU_ne_bot : U ≠ ⊥ := by
    intro hU
    obtain ⟨p, hp⟩ := exists_ne (0 : P)
    have hp_mem : (p, (0 : Q)) ∈ U.toSubmodule := by
      exact ⟨Submodule.mem_top, by simp⟩
    have hU_sub_eq : U.toSubmodule = (⊥ : Submodule F (P × Q)) := by
      simpa using congrArg Subrepresentation.toSubmodule hU
    have hpair_mem_bot : (p, (0 : Q)) ∈ (⊥ : Submodule F (P × Q)) := by
      simpa [hU_sub_eq] using hp_mem
    have hpair_eq : (p, (0 : Q)) = ((0 : P), (0 : Q)) := by
      simpa using hpair_mem_bot
    have hp0 : p = 0 := by
      simpa using congrArg Prod.fst hpair_eq
    exact hp hp0
  have hU_ne_top : U ≠ ⊤ := by
    intro hU
    obtain ⟨q, hq⟩ := exists_ne (0 : Q)
    have hq_mem_top : ((0 : P), q) ∈ (⊤ : Subrepresentation (Representation.prod ρ σ)).toSubmodule :=
      Submodule.mem_top
    have hq_mem : ((0 : P), q) ∈ U.toSubmodule := by
      simpa [hU] using hq_mem_top
    exact hq <| by simpa using hq_mem.2
  -- The first factor is a nonzero proper subrepresentation of the product representation.
  have hU_split : U = ⊥ ∨ U = ⊤ := IsSimpleOrder.eq_bot_or_eq_top U
  rcases hU_split with hUbot | hUtop
  · exact hU_ne_bot hUbot
  · exact hU_ne_top hUtop

/-- Helper for Proposition 15-15.5-1: complementary subrepresentations remain complementary on
their exact owner submodules. -/
theorem subrepresentation_isCompl_toSubmodule_local
    {F : Type u} [Field F]
    {W : Type v} [AddCommGroup W] [Module F W]
    {ρ : Representation F G W}
    {U V : Subrepresentation ρ}
    (hUV : IsCompl U V) :
    IsCompl U.toSubmodule V.toSubmodule := by
  refine ⟨?_, ?_⟩
  · rw [disjoint_iff]
    simpa using
      congrArg Subrepresentation.toSubmodule
        (show U ⊓ V = ⊥ from disjoint_iff.mp hUV.disjoint)
  · rw [codisjoint_iff]
    simpa using
      congrArg Subrepresentation.toSubmodule
        (show U ⊔ V = ⊤ from codisjoint_iff.mp hUV.codisjoint)

/-- Helper for Proposition 15-15.5-1: a nonzero free exact owner remains nonzero after scalar
extension to the fraction field. -/
theorem tensorProduct_nontrivial_of_free_local
    {P : Type v} [AddCommGroup P] [Module A P] [Module.Free A P] [Nontrivial P] :
    Nontrivial (K ⊗[A] P) := by
  let b : Module.Basis (Module.Free.ChooseBasisIndex A P) A P :=
    Module.Free.chooseBasis A P
  obtain ⟨x, hx⟩ := exists_ne (0 : P)
  have hmk_injective :
      Function.Injective (TensorProduct.mk A K P 1 : P →ₗ[A] K ⊗[A] P) := by
    intro y z hyz
    apply b.repr.injective
    ext i
    have hcoord := congrArg (fun t ↦ ((Algebra.TensorProduct.basis K b).repr t) i) hyz
    apply (IsFractionRing.injective A K)
    simpa using hcoord
  have htx : (TensorProduct.mk A K P 1) x ≠ 0 := by
    intro hzero
    apply hx
    apply hmk_injective
    simpa using hzero
  -- The pure tensor `1 ⊗ x` witnesses nontriviality after scalar extension.
  exact ⟨TensorProduct.mk A K P 1 x, 0, htx⟩

end DecompositionHom
