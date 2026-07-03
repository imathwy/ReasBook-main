import Mathlib
import LinearRepresentations_Serre_1977.Chap14.Corollary_14_14_3_3
import LinearRepresentations_Serre_1977.Chap14.Exercise_14_14_4_5
import LinearRepresentations_Serre_1977.Chap14.Infra_14_4_ProjectiveLift
import LinearRepresentations_Serre_1977.Chap14.Lemma_14_14_4_1
import LinearRepresentations_Serre_1977.Chap15.Definition_15_15_1_1
import LinearRepresentations_Serre_1977.Chap15.Definition_15_15_2_1
import LinearRepresentations_Serre_1977.Chap15.Definition_15_15_3_1
import LinearRepresentations_Serre_1977.Chap15.Exercise_15_15_2_5
import LinearRepresentations_Serre_1977.Chap15.Proposition_15_15_5_1.ReductionMkQ
import LinearRepresentations_Serre_1977.Chap15.Proposition_15_15_5_1.StableLatticeExactOwner
import LinearRepresentations_Serre_1977.Chap15.Theorem_15_15_2_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open Representation
open scoped MonoidAlgebra Representation TensorProduct

universe u v

section ProjectiveModules

variable {p : ℕ}
variable {k : Type u} [Field k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]

/-
Domain-style sampling for this item:
* `projective_groupAlgebra_iff_projective_and_exists_averaging_endomorphism` is the canonical
  projectivity owner for `A[G]`-modules; its primitive input is invertibility of `Nat.card G` in
  the coefficient ring, not the source-facing divisibility condition `¬ p ∣ Nat.card G`.
* `group_algebra_isSemisimpleRing_of_char_not_dvd_group_order` is the Chapter `6` source-facing
  bridge from `¬ p ∣ Nat.card G` to the Maschke owner over a field.
* `decompositionHom` is the owner of the reduction map `R_K(G) → R_k(G)`, so decomposition-matrix
  statements should be organized around that owner rather than a basis-dependent `Basis.constr`
  surrogate.
-/

/-- Proposition 15-15.5-1 (1): part (i). If the order of `G` is prime to `p`, then every
`k[G]`-module is projective. This is the source-facing projectivity consequence of the canonical
Maschke semisimplicity owner instance on `k[G]`. -/
-- Proof sketch: use Maschke semisimplicity for `k[G]` under `¬ p ∣ |G|`, then apply the standard
-- fact that modules over a semisimple ring are projective.
theorem groupAlgebra_module_projective_of_order_prime_to_p
    (hG : ¬ p ∣ Nat.card G) {M : Type v} [AddCommGroup M] [Module k[G] M] :
    Module.Projective k[G] M := by
  let _ : Fintype G := Fintype.ofFinite G
  -- Maschke's theorem turns the prime-to-`p` hypothesis into semisimplicity of `k[G]`.
  let _ : NeZero (Nat.card G : k) := NeZero.of_not_dvd k hG
  let _ : IsSemisimpleRing k[G] := by
    infer_instance
  -- Over a semisimple ring, every module is projective.
  exact Module.projective_of_isSemisimpleRing k[G] M

end ProjectiveModules

section ProjectiveModulesOfCardUnit

variable {A : Type u} [CommRing A]
variable {G : Type u} [Group G] [Finite G]
variable {P : Type v} [AddCommGroup P] [Module A[G] P]

-- Proof sketch: apply the averaging-endomorphism owner
-- `projective_groupAlgebra_iff_projective_and_exists_averaging_endomorphism` with the averaged
-- scalar multiple of `LinearMap.id`.
/-- Companion bridge: if `|G|` is invertible in `A`, then every `A[G]`-module whose underlying
`A`-module is projective is projective over `A[G]`. This is the primitive invertible-order input
to the local-ring source-facing form of Proposition `15-15.5-1 (2)`. -/
-- Proof sketch: apply the averaging-endomorphism criterion with the inverse of `|G|` times the
-- identity endomorphism.
theorem groupAlgebra_module_projective_of_card_unit_of_projective
    (hcard : IsUnit (Nat.card G : A))
    (hP : Module.Projective A (RestrictScalars A A[G] P)) :
    Module.Projective A[G] P := by
  let _ : Fintype G := Fintype.ofFinite G
  let _ : Module A P := Module.compHom P (algebraMap A A[G])
  let _ : IsScalarTower A A[G] P := IsScalarTower.of_compHom A A[G] P
  let u : Module.End A P :=
    Ring.inverse (Nat.card G : A) • LinearMap.id
  refine
    (projective_groupAlgebra_iff_projective_and_exists_averaging_endomorphism
      (Λ := A) (G := G) (P := P)).mpr ?_
  refine ⟨by simpa using hP, u, ?_⟩
  -- The inverse scalar multiple of the identity has average equal to the identity.
  ext x
  rw [LinearMap.sumOfConjugates_apply]
  calc
    ∑ g : G, u.conjugate g x = ∑ g : G, Ring.inverse (Nat.card G : A) • x := by
      refine Finset.sum_congr rfl fun g _ ↦ ?_
      calc
        u.conjugate g x
            = MonoidAlgebra.single g⁻¹ (1 : A) •
                (Ring.inverse (Nat.card G : A) • (MonoidAlgebra.single g (1 : A) • x)) := by
                  simp [u, LinearMap.conjugate_apply]
        _ = Ring.inverse (Nat.card G : A) •
              (MonoidAlgebra.single g⁻¹ (1 : A) • (MonoidAlgebra.single g (1 : A) • x)) := by
                rw [action_right_smul (Λ := A) (G := G) (P := P)]
        _ = Ring.inverse (Nat.card G : A) • ((1 : A[G]) • x) := by
              rw [← mul_smul, MonoidAlgebra.single_mul_single, inv_mul_cancel, mul_one,
                MonoidAlgebra.one_def]
        _ = Ring.inverse (Nat.card G : A) • x := by
              rw [one_smul]
    _ = (Fintype.card G : A) • (Ring.inverse (Nat.card G : A) • x) := by
          rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul A]
    _ = x := by
          rw [smul_smul, Fintype.card_eq_nat_card, mul_comm,
            Ring.inverse_mul_cancel _ hcard, one_smul]

end ProjectiveModulesOfCardUnit

section LocalProjectiveModules

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A]
variable [CharP (IsLocalRing.ResidueField A) p]
variable {G : Type u} [Group G] [Finite G]
variable {P : Type v} [AddCommGroup P] [Module A[G] P]

local notation "k" => IsLocalRing.ResidueField A

/-- Helper for Proposition 15-15.5-1: if `p` does not divide `|G|`, then the image of `|G|` in the
local ring `A` is a unit. -/
-- Proof sketch: the image of `|G|` in the residue field is nonzero because the residue field has
-- characteristic `p` and `p ∤ |G|`; local-ring theory then upgrades this to invertibility in `A`.
lemma card_unit_of_order_prime_to_p (hG : ¬ p ∣ Nat.card G) :
    IsUnit (Nat.card G : A) := by
  let _ : NeZero (Nat.card G : k) := NeZero.of_not_dvd k hG
  -- The residue of `|G|` is nonzero in characteristic `p`, so local-ring theory upgrades it to a
  -- unit already over `A`.
  have hresidue_ne_zero : IsLocalRing.residue A (Nat.card G : A) ≠ 0 := by
    rw [← IsLocalRing.ResidueField.algebraMap_eq]
    exact NeZero.ne (Nat.card G : k)
  exact (IsLocalRing.residue_ne_zero_iff_isUnit (Nat.card G : A)).mp hresidue_ne_zero

-- Proof sketch: part `(1)` applies over the residue field because `¬ p ∣ Nat.card G`, so the
-- image of `Nat.card G` in `A ⧸ 𝔪_A` is nonzero. In a local ring this implies that
-- `(Nat.card G : A)` is a unit, and the companion invertible-order bridge above then yields the
-- projectivity statement over `A[G]`.
/-- Proposition 15-15.5-1 (2): if the order of `G` is prime to `p`, then every `A[G]`-module
whose underlying `A`-module is projective is projective over `A[G]`. -/
theorem groupAlgebra_module_projective_of_order_prime_to_p_of_projective
    (hG : ¬ p ∣ Nat.card G)
    (hP : Module.Projective A (RestrictScalars A A[G] P)) :
    Module.Projective A[G] P := by
  -- First convert the prime-to-`p` hypothesis into invertibility of `|G|` inside the local ring.
  exact
    groupAlgebra_module_projective_of_card_unit_of_projective
      (A := A) (G := G) (P := P)
      (card_unit_of_order_prime_to_p (A := A) (G := G) (p := p) hG)
      hP

/-- Source-facing corollary of the preceding bridge theorem: if the order of `G` is prime to `p`,
then every `A[G]`-module that is free over `A` is projective. -/
-- Proof sketch: a free `A`-module is projective, so the preceding theorem applies immediately.
theorem free_groupAlgebra_module_projective_of_order_prime_to_p
    (hG : ¬ p ∣ Nat.card G) [Module.Free A (RestrictScalars A A[G] P)] :
    Module.Projective A[G] P := by
  -- Free modules are projective over the base ring, so the local projectivity bridge applies.
  let _ : Module.Projective A (RestrictScalars A A[G] P) := inferInstance
  exact
    groupAlgebra_module_projective_of_order_prime_to_p_of_projective
      (A := A) (G := G) (P := P) hG inferInstance

end LocalProjectiveModules

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

section ProjectiveLiteralReductionLocal

variable {E : Type u} [AddCommGroup E] [Module A E] [Module K E] [IsScalarTower A K E]

/-- Helper for Proposition 15-15.5-1: the underlying `A`-submodule of a stable lattice carries
the induced `A[G]`-module structure. -/
private instance stableLattice_toSubmodule_module_local_support
    {ρ : Representation K G E} (L : StableLattice A ρ) :
    Module A[G] L.toSubmodule := by
  change Module A[G] L.toRepresentation.asModule
  infer_instance

/-- Helper for Proposition 15-15.5-1: the induced `A[G]`-module structure on a stable lattice is
compatible with restriction of scalars from `A`. -/
private instance stableLattice_toSubmodule_isScalarTower_local_support
    {ρ : Representation K G E} (L : StableLattice A ρ) :
    IsScalarTower A A[G] L.toSubmodule := by
  change IsScalarTower A A[G] L.toRepresentation.asModule
  infer_instance

end ProjectiveLiteralReductionLocal

/-- Helper for Proposition 15-15.5-1: the literal scalar-extension map sends `x` to the pure
tensor `1 ⊗ x` inside `Q.scalarExtension K`. -/
private abbrev projective_scalarExtension_literal_map_local_support
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    Q.V →ₗ[A] K ⊗[A] Q.V :=
  TensorProduct.mk A K Q.V 1

/-- Helper for Proposition 15-15.5-1: over the fraction field, the literal map `x ↦ 1 ⊗ x` is
injective. -/
private theorem projective_scalarExtension_literal_map_injective_local_support
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    Function.Injective
      (projective_scalarExtension_literal_map_local_support
        (A := A) (K := K) (G := G) Q) := by
  let _ : Module.Free A Q.V := Q.free
  let b : Module.Basis (Module.Free.ChooseBasisIndex A Q.V) A Q.V :=
    Module.Free.chooseBasis A Q.V
  intro x y hxy
  -- Compare coordinates in the tensor-product basis to recover equality upstairs.
  apply b.repr.injective
  ext i
  have hcoord :=
    congrArg (fun z ↦ ((Algebra.TensorProduct.basis K b).repr z) i) hxy
  apply (IsFractionRing.injective A K)
  simpa using hcoord

/-- Helper for Proposition 15-15.5-1: the image of the literal map is stable under the
scalar-extended `G`-action. -/
private theorem projective_scalarExtension_literal_map_apply_mem_range_local_support
    (Q : FiniteProjectiveGroupAlgebraModule A G)
    (g : G) {x : K ⊗[A] Q.V}
    (hx :
      x ∈
        (projective_scalarExtension_literal_map_local_support
          (A := A) (K := K) (G := G) Q).range) :
    (Q.scalarExtension K).ρ g x ∈
      (projective_scalarExtension_literal_map_local_support
        (A := A) (K := K) (G := G) Q).range := by
  rcases hx with ⟨y, rfl⟩
  -- Rewrite the scalar-extended action on a pure tensor and keep the source vector upstairs.
  refine ⟨MonoidAlgebra.of A G g • y, ?_⟩
  let ρK : Representation K G (K ⊗[A] Q.V) :=
    Representation.scalarExtension (Representation.ofModule' Q.V)
  have hsingle :=
    Representation.single_smul (ρ := ρK) (t := (1 : K)) (g := g)
      (v := TensorProduct.mk A K Q.V 1 y)
  have haction :
      MonoidAlgebra.of K G g • (TensorProduct.mk A K Q.V 1 y) =
        ρK g (TensorProduct.mk A K Q.V 1 y) := by
    simpa [ρK, MonoidAlgebra.of_apply] using hsingle
  exact
    (monoidAlgebra_of_smul_tmul (Λ := A) (P := Q.V) (κ := K) g (1 : K) y).symm.trans
      haction

/-- Helper for Proposition 15-15.5-1: the literal image of `Q.V` spans the scalar extension over
`K` and is finite over `A`, so it forms a lattice. -/
private theorem projective_scalarExtension_literal_map_range_isLattice_local_support
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    Submodule.IsLattice K
      ((projective_scalarExtension_literal_map_local_support
        (A := A) (K := K) (G := G) Q).range) := by
  refine
    { fg := ?_
      span_eq_top := ?_ }
  · -- Finite generation is inherited from the finite `A`-module `Q.V`.
    have hfg_top : (⊤ : Submodule A Q.V).FG := by
      exact (Module.Finite.iff_fg (N := (⊤ : Submodule A Q.V))).1 inferInstance
    rw [LinearMap.range_eq_map]
    exact Submodule.FG.map
      (projective_scalarExtension_literal_map_local_support
        (A := A) (K := K) (G := G) Q) hfg_top
  · let _ : Module.Free A Q.V := Q.free
    let b := Module.Free.chooseBasis A Q.V
    -- The tensor-product basis vectors are literal pure tensors, hence already in the image.
    apply eq_top_iff.2
    intro x hx
    have hxrepr :
        x = ∑ i, ((Algebra.TensorProduct.basis K b).repr x) i •
          (Algebra.TensorProduct.basis K b) i := by
      simpa using ((Algebra.TensorProduct.basis K b).sum_repr x).symm
    rw [hxrepr]
    refine Submodule.sum_mem _ ?_
    intro i hi
    have hi' :
        (Algebra.TensorProduct.basis K b) i ∈
          Submodule.span K
            (((projective_scalarExtension_literal_map_local_support
                (A := A) (K := K) (G := G) Q).range :
                Submodule A (K ⊗[A] Q.V)) :
              Set (K ⊗[A] Q.V)) := by
      apply Submodule.subset_span
      refine ⟨b i, ?_⟩
      simpa [projective_scalarExtension_literal_map_local_support] using
        (Algebra.TensorProduct.basis_apply (A := K) (b := b) i)
    exact Submodule.smul_mem _ _ hi'

/-- Helper for Proposition 15-15.5-1: the literal range inside `Q.scalarExtension K` is the fixed
stable lattice used in LinearRepresentations_Serre_1977's projective comparison. -/
private noncomputable def projective_scalarExtension_literal_range_stableLattice_local_support
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    StableLattice A (Q.scalarExtension K).ρ :=
  { toSubmodule :=
      (projective_scalarExtension_literal_map_local_support
        (A := A) (K := K) (G := G) Q).range
    apply_mem_toSubmodule :=
      projective_scalarExtension_literal_map_apply_mem_range_local_support
        (A := A) (K := K) (G := G) Q
    isLattice :=
      projective_scalarExtension_literal_map_range_isLattice_local_support
        (A := A) (K := K) (G := G) Q }

/-- Helper for Proposition 15-15.5-1: restricting the literal map to its image keeps the exact
owner needed later for the decomposition-map computation. -/
private noncomputable def
    projective_scalarExtension_literal_rangeRestrictLinearMap_local_support
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    Q.V →ₗ[A]
      (projective_scalarExtension_literal_range_stableLattice_local_support
        (A := A) (K := K) (G := G) Q).toSubmodule :=
  (projective_scalarExtension_literal_map_local_support
    (A := A) (K := K) (G := G) Q).rangeRestrict

/-- Helper for Proposition 15-15.5-1: the range-restricted literal map is bijective. -/
private theorem
    projective_scalarExtension_literal_rangeRestrictLinearMap_bijective_local_support
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    Function.Bijective
      (projective_scalarExtension_literal_rangeRestrictLinearMap_local_support
        (A := A) (K := K) (G := G) Q) := by
  constructor
  · exact
      (LinearMap.injective_rangeRestrict_iff
        (f := projective_scalarExtension_literal_map_local_support
          (A := A) (K := K) (G := G) Q)).2
        (projective_scalarExtension_literal_map_injective_local_support
          (A := A) (K := K) (G := G) Q)
  · exact LinearMap.surjective_rangeRestrict
      (projective_scalarExtension_literal_map_local_support
        (A := A) (K := K) (G := G) Q)

/-- Helper for Proposition 15-15.5-1: the literal source module identifies `A`-linearly with its
range inside `Q.scalarExtension K`. -/
private noncomputable def projective_scalarExtension_literal_rangeLinearEquiv_local_support
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    Q.V ≃ₗ[A]
      (projective_scalarExtension_literal_range_stableLattice_local_support
        (A := A) (K := K) (G := G) Q).toSubmodule :=
  LinearEquiv.ofBijective
    (projective_scalarExtension_literal_rangeRestrictLinearMap_local_support
      (A := A) (K := K) (G := G) Q)
    (projective_scalarExtension_literal_rangeRestrictLinearMap_bijective_local_support
      (A := A) (K := K) (G := G) Q)

/-- Helper for Proposition 15-15.5-1: inside the literal-range lattice, the generator `[g]`
acts through the restricted ambient representation. -/
private theorem
    projective_scalarExtension_literal_range_toRepresentation_monoidAlgebra_of_smul_local_support
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    ∀ g : G, ∀ x :
      (projective_scalarExtension_literal_range_stableLattice_local_support
        (A := A) (K := K) (G := G) Q).toSubmodule,
      MonoidAlgebra.of A G g • x =
        (projective_scalarExtension_literal_range_stableLattice_local_support
          (A := A) (K := K) (G := G) Q).toRepresentation g x := by
  intro g x
  rw [← Representation.asAlgebraHom_single_one
    (ρ :=
      (projective_scalarExtension_literal_range_stableLattice_local_support
        (A := A) (K := K) (G := G) Q).toRepresentation) g]
  rfl

/-- Helper for Proposition 15-15.5-1: on group generators, the range-restricted literal map
already intertwines the exact subtype owner with the ambient scalar-extension action. -/
private theorem projective_scalarExtension_literal_rangeRestrict_map_of_local_support
    (Q : FiniteProjectiveGroupAlgebraModule A G)
    (g : G) (x : Q.V) :
    projective_scalarExtension_literal_rangeRestrictLinearMap_local_support
        (A := A) (K := K) (G := G) Q ((MonoidAlgebra.of A G g) • x) =
      (MonoidAlgebra.of A G g) •
        projective_scalarExtension_literal_rangeRestrictLinearMap_local_support
          (A := A) (K := K) (G := G) Q x := by
  -- Compare the two subtype points after forgetting back to the ambient tensor-product owner.
  apply Subtype.ext
  rw [projective_scalarExtension_literal_range_toRepresentation_monoidAlgebra_of_smul_local_support
    (A := A) (K := K) (G := G) Q g
    (projective_scalarExtension_literal_rangeRestrictLinearMap_local_support
      (A := A) (K := K) (G := G) Q x)]
  have hrestrict :
      ↑(projective_scalarExtension_literal_rangeRestrictLinearMap_local_support
          (A := A) (K := K) (G := G) Q x) =
        TensorProduct.mk A K Q.V 1 x := by
    rfl
  calc
    ↑((projective_scalarExtension_literal_rangeRestrictLinearMap_local_support
          (A := A) (K := K) (G := G) Q) ((MonoidAlgebra.of A G g) • x)) =
        TensorProduct.mk A K Q.V 1 ((MonoidAlgebra.of A G g) • x) := by
          rfl
    _ =
        (MonoidAlgebra.mapRingHom G (algebraMap A K) (MonoidAlgebra.of A G g)) •
          TensorProduct.mk A K Q.V 1 x := by
            simpa [MonoidAlgebra.of_apply] using
              (monoidAlgebra_of_smul_tmul
                (Λ := A) (P := Q.V) (κ := K) g (1 : K) x).symm
    _ =
        ((Q.scalarExtension K).ρ g)
          (TensorProduct.mk A K Q.V 1 x) := by
            simpa [MonoidAlgebra.of_apply] using
              (Representation.single_smul
                (ρ := (Q.scalarExtension K).ρ)
                (t := (1 : K)) (g := g) (v := TensorProduct.mk A K Q.V 1 x))
    _ =
        ((Q.scalarExtension K).ρ g)
          ↑(projective_scalarExtension_literal_rangeRestrictLinearMap_local_support
            (A := A) (K := K) (G := G) Q x) := by
              rw [hrestrict]
    _ =
        ↑((projective_scalarExtension_literal_range_stableLattice_local_support
            (A := A) (K := K) (G := G) Q).toRepresentation g
          (projective_scalarExtension_literal_rangeRestrictLinearMap_local_support
            (A := A) (K := K) (G := G) Q x)) := by
              simp [projective_scalarExtension_literal_rangeRestrictLinearMap_local_support,
                projective_scalarExtension_literal_map_local_support]

/-- Helper for Proposition 15-15.5-1: the range-restricted literal map already intertwines the
`A[G]`-action on `Q.V` with the induced action on the literal-range subtype. -/
private theorem projective_scalarExtension_literal_rangeRestrict_map_groupAlgebra_local_support
    (Q : FiniteProjectiveGroupAlgebraModule A G)
    (r : A[G]) (x : Q.V) :
    projective_scalarExtension_literal_rangeRestrictLinearMap_local_support
        (A := A) (K := K) (G := G) Q (r • x) =
      r • projective_scalarExtension_literal_rangeRestrictLinearMap_local_support
        (A := A) (K := K) (G := G) Q x := by
  -- Check equivariance on `MonoidAlgebra.of`, then extend linearly while keeping the subtype
  -- owner fixed.
  refine MonoidAlgebra.induction_on
    (p := fun a : A[G] =>
      projective_scalarExtension_literal_rangeRestrictLinearMap_local_support
          (A := A) (K := K) (G := G) Q (a • x) =
        a • projective_scalarExtension_literal_rangeRestrictLinearMap_local_support
          (A := A) (K := K) (G := G) Q x) r ?_ ?_ ?_
  · intro g
    simpa using
      projective_scalarExtension_literal_rangeRestrict_map_of_local_support
        (A := A) (K := K) (G := G) Q g x
  · intro a b ha hb
    simp [add_smul, ha, hb]
  · intro c a ha
    calc
      projective_scalarExtension_literal_rangeRestrictLinearMap_local_support
          (A := A) (K := K) (G := G) Q ((c • a) • x) =
        projective_scalarExtension_literal_rangeRestrictLinearMap_local_support
          (A := A) (K := K) (G := G) Q (c • (a • x)) := by
            simpa [smul_smul]
      _ =
        c • projective_scalarExtension_literal_rangeRestrictLinearMap_local_support
          (A := A) (K := K) (G := G) Q (a • x) := by
            simp
      _ =
        c • (a • projective_scalarExtension_literal_rangeRestrictLinearMap_local_support
          (A := A) (K := K) (G := G) Q x) := by
            rw [ha]
      _ =
        (c • a) • projective_scalarExtension_literal_rangeRestrictLinearMap_local_support
          (A := A) (K := K) (G := G) Q x := by
            simpa using
              (smul_assoc c a
                (projective_scalarExtension_literal_rangeRestrictLinearMap_local_support
                  (A := A) (K := K) (G := G) Q x)).symm

/-- Helper for Proposition 15-15.5-1: the literal range identification is compatible with the
`A[G]`-action. -/
private theorem projective_scalarExtension_literal_rangeLinearEquiv_map_groupAlgebra_local_support
    (Q : FiniteProjectiveGroupAlgebraModule A G)
    (r : A[G]) (x : Q.V) :
    projective_scalarExtension_literal_rangeLinearEquiv_local_support
        (A := A) (K := K) (G := G) Q (r • x) =
      r • projective_scalarExtension_literal_rangeLinearEquiv_local_support
        (A := A) (K := K) (G := G) Q x := by
  -- The `A`-linear equivalence is defined by the same range-restricted literal map.
  simpa [projective_scalarExtension_literal_rangeLinearEquiv_local_support] using
    projective_scalarExtension_literal_rangeRestrict_map_groupAlgebra_local_support
      (A := A) (K := K) (G := G) Q r x

/-- Helper for Proposition 15-15.5-1: the source module `Q.V` identifies with the literal range
as an `A[G]`-module. -/
private noncomputable def projective_scalarExtension_literal_rangeLinearEquiv_groupAlgebra_local_support
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    Q.V ≃ₗ[A[G]]
      (projective_scalarExtension_literal_range_stableLattice_local_support
        (A := A) (K := K) (G := G) Q).toSubmodule :=
  { toFun :=
      projective_scalarExtension_literal_rangeLinearEquiv_local_support
        (A := A) (K := K) (G := G) Q
    map_add' := by
      intro x y
      exact
        (projective_scalarExtension_literal_rangeLinearEquiv_local_support
          (A := A) (K := K) (G := G) Q).map_add x y
    map_smul' :=
      projective_scalarExtension_literal_rangeLinearEquiv_map_groupAlgebra_local_support
        (A := A) (K := K) (G := G) Q
    invFun :=
      (projective_scalarExtension_literal_rangeLinearEquiv_local_support
        (A := A) (K := K) (G := G) Q).symm
    left_inv :=
      (projective_scalarExtension_literal_rangeLinearEquiv_local_support
        (A := A) (K := K) (G := G) Q).left_inv
    right_inv :=
      (projective_scalarExtension_literal_rangeLinearEquiv_local_support
        (A := A) (K := K) (G := G) Q).right_inv }

/-- Helper for Proposition 15-15.5-1: the fixed literal range is `A[G]`-linearly equivalent to
`Q.V`. -/
theorem projective_scalarExtension_literal_range_nonempty_linearEquiv_local_support
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    Nonempty
      (Q.V ≃ₗ[A[G]]
        (projective_scalarExtension_literal_range_stableLattice_local_support
          (A := A) (K := K) (G := G) Q).toSubmodule) := by
  -- The owner-stable lattice is defined as the literal range, so the range-restricted map gives
  -- the needed `A[G]`-linear equivalence directly.
  exact
    ⟨projective_scalarExtension_literal_rangeLinearEquiv_groupAlgebra_local_support
      (A := A) (K := K) (G := G) Q⟩

/-- Helper for Proposition 15-15.5-1: the literal range is projective over `A[G]` because it is
`A[G]`-linearly equivalent to `Q.V`. -/
private theorem projective_scalarExtension_literal_range_projective_local_support
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    Module.Projective A[G]
      (projective_scalarExtension_literal_range_stableLattice_local_support
        (A := A) (K := K) (G := G) Q).toSubmodule := by
  let e :=
    projective_scalarExtension_literal_rangeLinearEquiv_groupAlgebra_local_support
      (A := A) (K := K) (G := G) Q
  -- Transport projectivity across the explicit `A[G]`-linear equivalence.
  exact Module.Projective.of_equiv' e

/-- Helper for Proposition 15-15.5-1: after freezing the literal-range lattice on the exact
owner, its reduction is `k[G]`-linearly equivalent to the canonical tensor-product reduction of
`Q.V`. -/
theorem projective_scalarExtension_literal_range_reduction_linearEquiv_local_support
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    let L :=
      projective_scalarExtension_literal_range_stableLattice_local_support
        (A := A) (K := K) (G := G) Q
    letI : Module k[G] L.reduction := by
      change Module k[G] L.reductionRepresentation.asModule
      infer_instance
    Nonempty (L.reduction ≃ₗ[k[G]] (k ⊗[A] Q.V)) := by
  let L :=
    projective_scalarExtension_literal_range_stableLattice_local_support
      (A := A) (K := K) (G := G) Q
  letI : Module A L.reduction := Module.compHom L.reduction (algebraMap A k)
  letI : IsScalarTower A k L.reduction :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  letI : Module k[G] L.reduction := by
    change Module k[G] L.reductionRepresentation.asModule
    infer_instance
  letI : IsScalarTower k k[G] L.reduction := by
    change IsScalarTower k k[G] L.reductionRepresentation.asModule
    infer_instance
  let eAQ :=
    projective_scalarExtension_literal_rangeLinearEquiv_groupAlgebra_local_support
      (A := A) (K := K) (G := G) Q
  have hprojQ : Module.Projective A[G] Q.V := by
    infer_instance
  have hprojL : Module.Projective A[G] L.toSubmodule :=
    projective_scalarExtension_literal_range_projective_local_support
      (A := A) (K := K) (G := G) Q
  have hAQ : Nonempty (Q.V ≃ₗ[A[G]] L.toSubmodule) := ⟨eAQ⟩
  -- Compare the tensor-product reduction of `Q.V` with the quotient reduction of the fixed
  -- literal lattice `L`.
  rcases
      (projective_monoidAlgebra_nonempty_linearEquiv_iff_of_isResidueFieldReduction
        (Λ := A) (G := G)
        (P := Q.V)
        (Pbar := k ⊗[A] Q.V)
        (f := TensorProduct.mk A k Q.V 1)
        (hf := MonoidAlgebra.tensorProduct_mk_isResidueFieldReduction
          (Λ := A) (G := G) (P := Q.V))
        (P' := L.toSubmodule)
        (Pbar' := L.reduction)
        (f' := (Submodule.mkQ L.maximalIdealSubmodule : L.toSubmodule →ₗ[A] L.reduction))
        (hf' := StableLattice.reduction_mkQ_isResidueFieldReduction_local
          (A := A) (K := K) (G := G) L)
        hprojQ hprojL).mp hAQ with
    ⟨ered⟩
  exact ⟨ered.symm⟩

/-- Helper for Proposition 15-15.5-1: the tautological owner module of a representation is
canonically `k[G]`-linearly equivalent to its underlying carrier. -/
private theorem nonempty_asModuleLinearEquiv_target_local_support
    {V : Type u} [AddCommGroup V] [Module k V] (ρ : Representation k G V) :
    letI : Module k[G] V := Module.compHom V ρ.asAlgebraHom.toRingHom
    letI : IsScalarTower k k[G] V :=
      IsScalarTower.of_algebraMap_smul fun a x ↦ by
        change ρ.asAlgebraHom (algebraMap k k[G] a) x = a • x
        simp [Algebra.smul_def]
    Nonempty (ρ.asModule ≃ₗ[k[G]] V) := by
  letI : Module k[G] V := Module.compHom V ρ.asAlgebraHom.toRingHom
  letI : IsScalarTower k k[G] V :=
    IsScalarTower.of_algebraMap_smul fun a x ↦ by
      change ρ.asAlgebraHom (algebraMap k k[G] a) x = a • x
      simp [Algebra.smul_def]
  refine ⟨
    { toFun := fun x ↦ ρ.asModuleEquiv x
      invFun := fun x ↦ ρ.asModuleEquiv.symm x
      left_inv := fun x ↦ ρ.asModuleEquiv.symm_apply_apply x
      right_inv := fun x ↦ ρ.asModuleEquiv.apply_symm_apply x
      map_add' := fun x y ↦ ρ.asModuleEquiv.map_add x y
      map_smul' := ?_ }⟩
  intro a x
  -- Transport the `k[G]`-action through `asModuleEquiv`, then read it as the original action.
  calc
    ρ.asModuleEquiv (a • x) = ρ.asAlgebraHom a (ρ.asModuleEquiv x) := by
      simpa using Representation.asModuleEquiv_map_smul (ρ := ρ) a x
    _ = a • ρ.asModuleEquiv x := rfl

/-- Helper for Proposition 15-15.5-1: a `k[G]`-linear equivalence between the owner modules of two
finite-dimensional representations upgrades to an isomorphism in `FDRep k G`. -/
private theorem fdRep_nonempty_iso_of_nonempty_asModuleLinearEquiv_local_support
    {σ τ : FDRep k G}
    (hστ : Nonempty (asModule σ.ρ ≃ₗ[k[G]] asModule τ.ρ)) :
    Nonempty (σ ≅ τ) := by
  rcases hστ with ⟨e⟩
  -- Repackage the recovered `k[G]`-linear equivalence as an isomorphism in `Rep k G`.
  let eRep : ((forget₂ (FDRep k G) (Rep k G)).obj σ) ≅
      ((forget₂ (FDRep k G) (Rep k G)).obj τ) :=
    Rep.unitIso ((forget₂ (FDRep k G) (Rep k G)).obj σ) ≪≫
      Rep.ofModuleMonoidAlgebra.mapIso e.toModuleIso ≪≫
      (Rep.unitIso ((forget₂ (FDRep k G) (Rep k G)).obj τ)).symm
  -- Faithfulness of `FDRep ⥤ Rep` transports that isomorphism back to `FDRep`.
  refine ⟨⟨(FDRep.forget₂HomLinearEquiv σ τ) eRep.hom,
    (FDRep.forget₂HomLinearEquiv τ σ) eRep.inv, ?_, ?_⟩⟩
  · apply (forget₂ (FDRep k G) (Rep k G)).map_injective
    change eRep.hom ≫ eRep.inv = 𝟙 _
    exact eRep.hom_inv_id
  · apply (forget₂ (FDRep k G) (Rep k G)).map_injective
    change eRep.inv ≫ eRep.hom = 𝟙 _
    exact eRep.inv_hom_id

/-- Helper for Proposition 15-15.5-1: the reduction of the fixed literal range lattice is
isomorphic to the intrinsic residue-field reduction of `Q`. -/
theorem projective_scalarExtension_literal_range_reduction_iso_local_support
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    Nonempty
      (FDRep.of
          (projective_scalarExtension_literal_range_stableLattice_local_support
            (A := A) (K := K) (G := G) Q).reductionRepresentation ≅
        Q.residueFieldReduction.toFiniteRep) := by
  let L :=
    projective_scalarExtension_literal_range_stableLattice_local_support
      (A := A) (K := K) (G := G) Q
  letI : Module k[G] L.reduction := by
    change Module k[G] L.reductionRepresentation.asModule
    infer_instance
  have hL :
      Nonempty
        (asModule (FDRep.of L.reductionRepresentation).ρ ≃ₗ[k[G]] L.reduction) := by
    simpa using
      (nonempty_asModuleLinearEquiv_target_local_support
        (G := G) (ρ := (FDRep.of L.reductionRepresentation).ρ))
  rcases hL with ⟨eL⟩
  rcases _root_.projective_scalarExtension_literal_range_reduction_linearEquiv_local_support
      (A := A) (K := K) (G := G) Q with
    ⟨ered⟩
  letI : Module k Q.residueFieldReduction.V :=
    Module.compHom Q.residueFieldReduction.V (algebraMap k k[G])
  letI : IsScalarTower k k[G] Q.residueFieldReduction.V :=
    IsScalarTower.of_compHom k k[G] Q.residueFieldReduction.V
  have hQas :
      Nonempty
        (asModule Q.residueFieldReduction.toFiniteRep.ρ ≃ₗ[k[G]] Q.residueFieldReduction.V) := by
    change Nonempty
      ((Representation.ofModule (ModuleCat.of k[G] Q.residueFieldReduction.V)).asModule ≃ₗ[k[G]]
        Q.residueFieldReduction.V)
    let Mmod : ModuleCat k[G] := ModuleCat.of k[G] Q.residueFieldReduction.V
    let toFun : (Representation.ofModule Mmod).asModule → Q.residueFieldReduction.V := fun x ↦
      (RestrictScalars.addEquiv k k[G] Q.residueFieldReduction.V)
        ((Representation.ofModule Mmod).asModuleEquiv x)
    let invFun : Q.residueFieldReduction.V → (Representation.ofModule Mmod).asModule := fun x ↦
      (Representation.ofModule Mmod).asModuleEquiv.symm
        ((RestrictScalars.addEquiv k k[G] Q.residueFieldReduction.V).symm x)
    refine ⟨
      { toFun := toFun
        invFun := invFun
        left_inv := by
          intro x
          simp [toFun, invFun, Mmod]
        right_inv := by
          intro x
          simp [toFun, invFun, Mmod]
        map_add' := by
          intro x y
          simp [toFun, Mmod]
        map_smul' := by
          intro r x
          exact Representation.smul_ofModule_asModule (M := Mmod) r x }⟩
  have hQowner :
      Nonempty (Q.residueFieldReduction.V ≃ₗ[k[G]] (k ⊗[A] Q.V)) := by
    simpa [FiniteProjectiveGroupAlgebraModule.residueFieldReduction,
      FiniteProjectiveGroupAlgebraModule.V] using
        (show Nonempty ((k ⊗[A] Q.V) ≃ₗ[k[G]] (k ⊗[A] Q.V)) from
          ⟨LinearEquiv.refl k[G] (k ⊗[A] Q.V)⟩)
  rcases hQas with ⟨eQas⟩
  rcases hQowner with ⟨eQowner⟩
  let eQ : asModule Q.residueFieldReduction.toFiniteRep.ρ ≃ₗ[k[G]] (k ⊗[A] Q.V) :=
    eQas.trans eQowner
  -- Route correction: compare the two `FDRep` owners through explicit `asModule` bridges, so the
  -- exact tensor-product carrier is only exposed once.
  refine
    fdRep_nonempty_iso_of_nonempty_asModuleLinearEquiv_local_support
      (G := G) ?_
  refine ⟨eL.trans (ered.trans eQ.symm)⟩

/-- Helper for Proposition 15-15.5-1: an honest projective scalar extension carries the literal
stable lattice whose reduction is exactly the intrinsic residue-field reduction of the original
projective module. -/
theorem projective_scalarExtension_literal_reduction_class_support
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    ∃ L : StableLattice A (Q.scalarExtension K).ρ,
      [FDRep.of L.reductionRepresentation]₀ = [Q.residueFieldReduction.toFiniteRep]₀ := by
  let L :=
    projective_scalarExtension_literal_range_stableLattice_local_support
      (A := A) (K := K) (G := G) Q
  refine ⟨L, ?_⟩
  -- Package the fixed literal lattice with the already proved reduction isomorphism.
  exact
    finiteRepGrothendieckClass_eq_of_nonempty_iso
      (L := k) (G := G)
      (_root_.projective_scalarExtension_literal_range_reduction_iso_local_support
        (A := A) (K := K) (G := G) Q)

/-- Helper for Proposition 15-15.5-1: `Q.scalarExtension K` should carry the literal stable
lattice coming from the image of `x ↦ 1 ⊗ x`, and that lattice should reduce to
`Q.residueFieldReduction.toFiniteRep`. -/
private theorem projective_scalarExtension_literal_reduction_class_local
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    ∃ L : StableLattice A (Q.scalarExtension K).ρ,
      [FDRep.of L.reductionRepresentation]₀ = [Q.residueFieldReduction.toFiniteRep]₀ := by
  -- Reuse the literal-range reduction theorem proved in this file instead of delegating through
  -- the theorem-local support import.
  exact
    projective_scalarExtension_literal_reduction_class_support
      (A := A) (K := K) (G := G) Q

/-- Helper for Proposition 15-15.5-1: the `k[G]`-module underlying a finite-dimensional
representation. -/
private noncomputable abbrev fdRepAsModule (τ : FDRep k G) : ModuleCat k[G] :=
  Rep.toModuleMonoidAlgebra.obj ((forget₂ (FDRep k G) (Rep k G)).obj τ)

/-- Helper for Proposition 15-15.5-1: choose LinearRepresentations_Serre_1977's literal scalar-extension lattice on the
ambient scalar-extension owner once and for all. -/
private noncomputable def projective_scalarExtension_literal_stableLattice_source_local
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    StableLattice A (Q.scalarExtension K).ρ :=
  Classical.choose <|
    projective_scalarExtension_literal_reduction_class_local
      (A := A) (K := K) (G := G) Q

/-- Helper for Proposition 15-15.5-1: the chosen literal scalar-extension lattice on the ambient
owner reduces to the intrinsic residue-field reduction of `Q`. -/
private theorem projective_scalarExtension_literal_stableLattice_source_reduction_class_local
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    let L :=
      projective_scalarExtension_literal_stableLattice_source_local
        (A := A) (K := K) (G := G) Q
    [FDRep.of L.reductionRepresentation]₀ = [Q.residueFieldReduction.toFiniteRep]₀ := by
  simpa [projective_scalarExtension_literal_stableLattice_source_local] using
    Classical.choose_spec <|
      projective_scalarExtension_literal_reduction_class_local
        (A := A) (K := K) (G := G) Q

/-- Helper for Proposition 15-15.5-1: restate the chosen literal scalar-extension lattice on the
default `FDRep.of` owner so later applications use the canonical restrict-scalars instance. -/
private noncomputable def projective_scalarExtension_literal_stableLattice_fdrep_default_local
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    let V : FDRep K G := FDRep.of (Q.scalarExtension K).ρ
    StableLattice A V.ρ := by
  let V : FDRep K G := FDRep.of (Q.scalarExtension K).ρ
  let L :=
    projective_scalarExtension_literal_stableLattice_source_local
      (A := A) (K := K) (G := G) Q
  refine
    { toSubmodule :=
        { carrier := (L.toSubmodule : Set V.V)
          zero_mem' := L.toSubmodule.zero_mem
          add_mem' := fun hx hy ↦ L.toSubmodule.add_mem hx hy
          smul_mem' := fun a x hx ↦ by
            -- The canonical restrict-scalars action on the rebundled owner is still multiplication
            -- by the image of `a` in `K`.
            simpa [Algebra.smul_def] using L.toSubmodule.smul_mem a hx }
      apply_mem_toSubmodule := ?_
      isLattice := ?_ }
  · intro g x hx
    exact L.apply_mem_toSubmodule g hx
  · simpa using L.isLattice

/-- Helper for Proposition 15-15.5-1: the default-owner rebundling of the chosen literal
scalar-extension lattice keeps the same residue-field reduction class. -/
private theorem
    projective_scalarExtension_literal_stableLattice_fdrep_default_reduction_class_local
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    let V : FDRep K G := FDRep.of (Q.scalarExtension K).ρ
    let L :=
      projective_scalarExtension_literal_stableLattice_fdrep_default_local
        (A := A) (K := K) (G := G) Q
    [FDRep.of L.reductionRepresentation]₀ = [Q.residueFieldReduction.toFiniteRep]₀ := by
  -- Rebundling changes only the owner packaging, not the underlying literal lattice or its
  -- reduction class.
  simpa [projective_scalarExtension_literal_stableLattice_fdrep_default_local,
    projective_scalarExtension_literal_stableLattice_source_local] using
    projective_scalarExtension_literal_stableLattice_source_reduction_class_local
      (A := A) (K := K) (G := G) Q

/-- Helper for Proposition 15-15.5-1: package the rebundled literal lattice on the explicit
`FDRep.of (Q.scalarExtension K).ρ` owner so later theorems can use it without `let`-bound
transport noise. -/
private noncomputable def projective_scalarExtension_literal_stableLattice_fdrep_owner_local
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    StableLattice A (FDRep.of (Q.scalarExtension K).ρ).ρ :=
  projective_scalarExtension_literal_stableLattice_fdrep_default_local
    (A := A) (K := K) (G := G) Q

/-- Helper for Proposition 15-15.5-1: the explicit-owner rebundling of the literal lattice keeps
the same residue-field reduction class. -/
private theorem projective_scalarExtension_literal_stableLattice_fdrep_owner_reduction_class_local
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    [FDRep.of
      (projective_scalarExtension_literal_stableLattice_fdrep_owner_local
        (A := A) (K := K) (G := G) Q).reductionRepresentation]₀ =
      [Q.residueFieldReduction.toFiniteRep]₀ := by
  -- The explicit-owner version is definitionally the previously proved default-owner rebundling.
  simpa [projective_scalarExtension_literal_stableLattice_fdrep_owner_local] using
    projective_scalarExtension_literal_stableLattice_fdrep_default_reduction_class_local
      (A := A) (K := K) (G := G) Q

/-- Helper for Proposition 15-15.5-1: the source of a projective envelope of a simple `k[G]`
module is finitely generated over `k[G]`. -/
private theorem moduleFinite_of_projectiveEnvelope_simple_local
    {P M : Type u} [AddCommGroup P] [Module k[G] P]
    [AddCommGroup M] [Module k[G] M] [IsSimpleModule k[G] M]
    {f : P →ₗ[k[G]] M} (hf : f.IsProjectiveEnvelope) :
    Module.Finite k[G] P := by
  letI : Nontrivial M := IsSimpleModule.nontrivial (R := k[G]) (M := M)
  obtain ⟨m, hm⟩ := exists_ne (0 : M)
  obtain ⟨x, hx⟩ := hf.surjective m
  let N : Submodule k[G] P := Submodule.span k[G] {x}
  have hmap_ne_bot : N.map f ≠ ⊥ := by
    -- The chosen cyclic generator maps to a nonzero element of the simple target.
    intro hbot
    have hxmem : f x ∈ N.map f := by
      exact ⟨x, Submodule.mem_span_singleton_self x, rfl⟩
    have hfx : f x = 0 := by
      rw [hbot] at hxmem
      simpa using hxmem
    exact hm <| by simpa [hx] using hfx
  have hmap_top : N.map f = ⊤ :=
    (IsSimpleOrder.eq_bot_or_eq_top (N.map f)).resolve_left hmap_ne_bot
  have hN_top : N = ⊤ := hf.toIsEssential.eq_top_of_map_eq_top N hmap_top
  have hsurj : Function.Surjective (LinearMap.toSpanSingleton k[G] P x) := by
    -- Once the cyclic span is all of `P`, the canonical map from `k[G]` is onto.
    simpa [LinearMap.toSpanSingleton_apply] using
      (Submodule.span_singleton_eq_top_iff (R := k[G]) (x := x)).1 (by simpa [N] using hN_top)
  exact Module.Finite.of_surjective (LinearMap.toSpanSingleton k[G] P x) hsurj

/-- Helper for Proposition 15-15.5-1: every simple finite-dimensional `k[G]`-representation
admits a finite projective envelope in the canonical owner category. -/
private theorem exists_finite_projective_envelope_of_simple_local
    (S : FDRep k G) [Simple S] :
    ∃ P : FiniteProjectiveGroupAlgebraModule k G,
      ∃ f : P.V →ₗ[k[G]] asModule S.ρ, f.IsProjectiveEnvelope := by
  let ρ : Representation k G S := S.ρ
  letI : Module k[G] S := by
    -- Expose the ambient `k[G]`-module structure carried by the owner `S`.
    simpa [ρ] using (inferInstance : Module k[G] ρ.asModule)
  letI : Representation.IsIrreducible ρ := by
    -- Categorical simplicity of `S` implies irreducibility of its bundled representation.
    simpa [ρ] using (FDRep.isIrreducible_of_simple S)
  letI : IsSimpleModule k[G] S := by
    -- The projective-envelope owner theorem is stated for `k[G]`-modules.
    simpa [ρ] using
      (Representation.irreducible_iff_isSimpleModule_asModule ρ).mp inferInstance
  let M : ModuleCat k[G] := ModuleCat.of k[G] S
  let _ : Module.Finite k k[G] := MonoidAlgebra.moduleFinite
  let _ : IsArtinianRing k[G] := IsArtinianRing.of_finite k k[G]
  obtain ⟨P', f', hf'⟩ := exists_isProjectiveEnvelope M
  have hfinite : Module.Finite k[G] P' :=
    moduleFinite_of_projectiveEnvelope_simple_local (G := G) (f := f'.hom) hf'
  let Pfg : FGModuleCat k[G] := by
    -- Repackage the envelope source as a finite projective owner.
    refine ⟨P', ?_⟩
    change Module.Finite k[G] P'
    exact hfinite
  have hproj : Module.Projective k[G] Pfg := by
    -- Projectivity is already part of the envelope source structure.
    change Module.Projective k[G] P'
    infer_instance
  let P : FiniteProjectiveGroupAlgebraModule k G := ⟨Pfg, hproj⟩
  refine ⟨P, ?_⟩
  refine ⟨?_, ?_⟩
  · simpa [ρ] using f'.hom
  · simpa [P, ρ] using hf'

/-- Helper for Proposition 15-15.5-1: under the prime-to-`p` hypothesis, a projective envelope
over `k[G]` is already isomorphic to its target because Maschke makes the target projective. -/
private theorem finite_projective_envelope_toFiniteRep_iso_target_of_order_prime_to_p
    (hG : ¬ p ∣ Nat.card G)
    {π : FDRep k G}
    {P : FiniteProjectiveGroupAlgebraModule k G}
    {f : P.V →ₗ[k[G]] asModule π.ρ}
    (hf : f.IsProjectiveEnvelope) :
    Nonempty (P.toFiniteRep ≅ π) := by
  let M := fdRepAsModule π
  let _ : Module.Projective k[G] M :=
    groupAlgebra_module_projective_of_order_prime_to_p
      (G := G) (M := M) hG
  let f' : P.V →ₗ[k[G]] M := by
    -- Re-express the envelope in the canonical `ModuleCat` owner of the target `FDRep`.
    simpa [fdRepAsModule] using f
  have hf' : f'.IsProjectiveEnvelope := by
    -- The projective-envelope structure is unchanged by that definitional rebundling.
    simpa [f', fdRepAsModule] using hf
  obtain ⟨e⟩ := hf'.nonempty_linearEquiv_target
  let eRep' : P.toRep ≅ ((forget₂ (FDRep k G) (Rep k G)).obj π) :=
    Rep.ofModuleMonoidAlgebra.mapIso e.toModuleIso ≪≫
      (Rep.unitIso ((forget₂ (FDRep k G) (Rep k G)).obj π)).symm
  let eRep : ((forget₂ (FDRep k G) (Rep k G)).obj P.toFiniteRep) ≅
      ((forget₂ (FDRep k G) (Rep k G)).obj π) := by
    -- `P.toFiniteRep` forgets to the same `Rep` owner as `P.toRep`.
    simpa [FiniteProjectiveGroupAlgebraModule.toFiniteRep,
      FiniteProjectiveGroupAlgebraModule.toRep] using eRep'
  -- Transport the recovered `Rep` isomorphism back to `FDRep`.
  refine ⟨⟨(FDRep.forget₂HomLinearEquiv P.toFiniteRep π) eRep.hom,
    (FDRep.forget₂HomLinearEquiv π P.toFiniteRep) eRep.inv, ?_, ?_⟩⟩
  · apply (forget₂ (FDRep k G) (Rep k G)).map_injective
    change eRep.hom ≫ eRep.inv = 𝟙 _
    exact eRep.hom_inv_id
  · apply (forget₂ (FDRep k G) (Rep k G)).map_injective
    change eRep.inv ≫ eRep.hom = 𝟙 _
    exact eRep.inv_hom_id

/-- Helper for Proposition 15-15.5-1: every simple `k[G]`-representation lifts to a finite
projective `A[G]`-module whose residue-field reduction is isomorphic to it. -/
private theorem exists_projective_lift_reducing_to_simple_of_order_prime_to_p
    (hG : ¬ p ∣ Nat.card G)
    (S : FDRep k G) [Simple S] :
    ∃ Q : FiniteProjectiveGroupAlgebraModule A G,
      Nonempty (Q.residueFieldReduction.toFiniteRep ≅ S) := by
  -- First package the simple target as an actual finite projective `k[G]`-module by taking a
  -- projective envelope and then using Maschke to identify the source with the target.
  obtain ⟨P, f, hf⟩ :=
    exists_finite_projective_envelope_of_simple_local (A := A) (G := G) S
  have hPS : Nonempty (P.toFiniteRep ≅ S) :=
    finite_projective_envelope_toFiniteRep_iso_target_of_order_prime_to_p
      (A := A) (p := p) (G := G) (π := S) (P := P) (f := f) hG hf
  -- Then lift that honest projective `k[G]`-module through the Chapter `14` owner theorem.
  obtain ⟨Q, hQP⟩ :=
    Representation.exists_projective_lift_of_residueField_projective
      (A := A) (G := G) P
  refine ⟨Q, ?_⟩
  have hQredP :
      Nonempty (Q.residueFieldReduction.toFiniteRep ≅ P.toFiniteRep) := by
    rcases
        (finiteProjectiveGroupAlgebraModule_nonempty_iso_iff_nonempty_linearEquiv
          (A := k) (G := G) Q.residueFieldReduction P).1 hQP with
      ⟨e⟩
    let eRep :
        ((forget₂ (FDRep k G) (Rep k G)).obj Q.residueFieldReduction.toFiniteRep) ≅
          ((forget₂ (FDRep k G) (Rep k G)).obj P.toFiniteRep) :=
      Rep.ofModuleMonoidAlgebra.mapIso e.toModuleIso
    -- Transport the recovered `Rep` isomorphism back to `FDRep`.
    refine ⟨⟨(FDRep.forget₂HomLinearEquiv _ _) eRep.hom,
      (FDRep.forget₂HomLinearEquiv _ _) eRep.inv, ?_, ?_⟩⟩
    · apply (forget₂ (FDRep k G) (Rep k G)).map_injective
      change eRep.hom ≫ eRep.inv = 𝟙 _
      exact eRep.hom_inv_id
    · apply (forget₂ (FDRep k G) (Rep k G)).map_injective
      change eRep.inv ≫ eRep.hom = 𝟙 _
      exact eRep.inv_hom_id
  rcases hQredP with ⟨eQredP⟩
  rcases hPS with ⟨ePS⟩
  -- Compose the lifted reduction identification with the envelope-source identification.
  exact ⟨eQredP.trans ePS⟩

/-- Helper for Proposition 15-15.5-1: the restricted `A`-action on a rebundled `FDRep` carrier
forms the expected scalar tower over `K`. -/
private theorem fdRep_compHom_isScalarTower_local
    (V : FDRep K G) :
    letI : Module A V.V := Module.compHom V.V (algebraMap A K)
    IsScalarTower A K V.V := by
  letI : Module A V.V := Module.compHom V.V (algebraMap A K)
  -- The `A`-action is obtained by restricting scalars through `A → K`, so the tower relation is
  -- exactly the `compHom` scalar action.
  refine IsScalarTower.of_algebraMap_smul ?_
  intro a x
  show ((algebraMap A K a) • x : V.V) =
    @SMul.smul A V.V (Module.compHom V.V (algebraMap A K)).toSMul a x
  rfl

/-- Helper for Proposition 15-15.5-1: the literal tensor-product `A`-action on
`Q.scalarExtension K` forms the ambient scalar tower over `K`. -/
private theorem projective_scalarExtension_tensor_left_isScalarTower_local
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    let V : FDRep K G := Q.scalarExtension K
    IsScalarTower A K V.V := by
  let V : FDRep K G := Q.scalarExtension K
  -- The source-faithful literal lattice lives on the tensor-product owner, so verify the scalar
  -- tower directly on pure tensors for that owner.
  refine IsScalarTower.of_algebraMap_smul fun a x ↦ ?_
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simp
  · intro z y
    simp [Algebra.smul_def, TensorProduct.smul_tmul']
  · intro x₁ x₂ hx₁ hx₂
    rw [smul_add, smul_add, hx₁, hx₂]

/-- Helper for Proposition 15-15.5-1: rebundling an `FDRep` from its underlying representation
does not change its isomorphism class. -/
private noncomputable def fdRepIsoOfRho_local
    (τ : FDRep K G) : τ ≅ FDRep.of τ.ρ :=
  Action.mkIso (Iso.refl _) fun g ↦ by
    -- Rebundling preserves the carrier and the action pointwise.
    ext x
    rfl

/-- Helper for Proposition 15-15.5-1: rebundling `Q.scalarExtension K` as `FDRep.of` does not
change its generic Grothendieck class. -/
private theorem finiteRepClass_projective_scalarExtension_eq_fdrepOfRho_local
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    [Q.scalarExtension K]₀ = [FDRep.of (Q.scalarExtension K).ρ]₀ := by
  -- The scalar-extended representation and its `FDRep.of` rebundling are canonically isomorphic.
  rw [finiteRepGrothendieckClass_eq_of_nonempty_iso
    (L := K) (G := G) ⟨fdRepIsoOfRho_local (τ := Q.scalarExtension K)⟩]

/-- Helper for Proposition 15-15.5-1: the decomposition class of `Q.scalarExtension K` is
unchanged after rebundling through `FDRep.of`. -/
private theorem decompositionHom_projective_scalarExtension_class_eq_fdrepOfRho_local
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    decompositionHom A K G [Q.scalarExtension K]₀ =
      decompositionHom A K G [FDRep.of (Q.scalarExtension K).ρ]₀ := by
  -- `decompositionHom` sees only the Grothendieck class, and the rebundled class is equal.
  rw [finiteRepClass_projective_scalarExtension_eq_fdrepOfRho_local
    (A := A) (K := K) (G := G) Q]

/-- Helper for Proposition 15-15.5-1: rebuild LinearRepresentations_Serre_1977's literal range lattice on the explicit
`FDRep.of (Q.scalarExtension K).ρ` owner used by `decompositionHom`. -/
private noncomputable def projective_scalarExtension_literal_range_stableLattice_fdrep_owner_local
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    StableLattice A (FDRep.of (Q.scalarExtension K).ρ).ρ := by
  let V : FDRep K G := FDRep.of (Q.scalarExtension K).ρ
  let L :=
    projective_scalarExtension_literal_range_stableLattice_local_support
      (A := A) (K := K) (G := G) Q
  refine
    { toSubmodule :=
        { carrier := (L.toSubmodule : Set V.V)
          zero_mem' := L.toSubmodule.zero_mem
          add_mem' := fun hx hy ↦ L.toSubmodule.add_mem hx hy
          smul_mem' := fun a x hx ↦ by
            -- The restrict-scalars `A`-action on the explicit `FDRep.of` owner is still the
            -- ambient tensor-product action defining LinearRepresentations_Serre_1977's literal lattice.
            simpa [Algebra.smul_def] using L.toSubmodule.smul_mem a hx }
      apply_mem_toSubmodule := ?_
      isLattice := ?_ }
  · intro g x hx
    exact L.apply_mem_toSubmodule g hx
  · simpa using L.isLattice

/-- Helper for Proposition 15-15.5-1: the explicit-owner literal range lattice still reduces to
the intrinsic residue-field reduction of `Q`. -/
private theorem projective_scalarExtension_literal_range_reduction_class_fdrep_owner_local
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    let L :=
      projective_scalarExtension_literal_range_stableLattice_fdrep_owner_local
        (A := A) (K := K) (G := G) Q
    [FDRep.of L.reductionRepresentation]₀ = [Q.residueFieldReduction.toFiniteRep]₀ := by
  -- The exact-owner rebundling does not change the literal range lattice or its reduced class.
  simpa [projective_scalarExtension_literal_range_stableLattice_fdrep_owner_local] using
    finiteRepGrothendieckClass_eq_of_nonempty_iso
      (L := k) (G := G)
      (projective_scalarExtension_literal_range_reduction_iso_local_support
        (A := A) (K := K) (G := G) Q)

/-- Helper for Proposition 15-15.5-1: LinearRepresentations_Serre_1977's literal scalar-extension lattice can be chosen on
the exact `FDRep.of` owner used by the decomposition-map computation. -/
private theorem projective_scalarExtension_literal_reduction_class_fdrep_owner_local
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    ∃ L : StableLattice A (FDRep.of (Q.scalarExtension K).ρ).ρ,
      [FDRep.of L.reductionRepresentation]₀ = [Q.residueFieldReduction.toFiniteRep]₀ := by
  let L :=
    projective_scalarExtension_literal_range_stableLattice_fdrep_owner_local
      (A := A) (K := K) (G := G) Q
  -- Package the fixed literal lattice with the already proved reduction-class computation.
  refine ⟨L, ?_⟩
  simpa [L] using
    projective_scalarExtension_literal_range_reduction_class_fdrep_owner_local
      (A := A) (K := K) (G := G) Q

/-- Helper for Proposition 15-15.5-1: computing `decompositionHom` on the rebundled
scalar-extension owner recovers the literal residue-field reduction class of `Q`. -/
private theorem decompositionHom_fdrepOf_scalarExtension_eq_literal_reduction_class_local
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    decompositionHom A K G [FDRep.of (Q.scalarExtension K).ρ]₀ =
      [Q.residueFieldReduction.toFiniteRep]₀ := by
  -- TODO: transport LinearRepresentations_Serre_1977's literal tensor-product lattice to the default `FDRep`
  -- restrict-scalars owner used by `decompositionHom_finiteRepClass_eq`; the blocker is the
  -- non-definitional mismatch between the tensor-product `A`-action and `FDRep.instModuleRestrictScalars`.
  sorry

private theorem decompositionHom_projective_scalarExtension_class_eq_residueFieldReduction_class
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    decompositionHom A K G [Q.scalarExtension K]₀ =
      cartanHom k G [Q.residueFieldReduction]ₚ₀ := by
  -- Route correction: pass once through the explicit `FDRep.of` owner of the literal lattice,
  -- then identify the resulting reduction class with the Cartan class of `Q mod 𝔪`.
  calc
    decompositionHom A K G [Q.scalarExtension K]₀ =
        decompositionHom A K G [FDRep.of (Q.scalarExtension K).ρ]₀ := by
          exact
            decompositionHom_projective_scalarExtension_class_eq_fdrepOfRho_local
              (A := A) (K := K) (G := G) Q
    _ = [Q.residueFieldReduction.toFiniteRep]₀ := by
          exact
            decompositionHom_fdrepOf_scalarExtension_eq_literal_reduction_class_local
              (A := A) (K := K) (G := G) Q
    _ = cartanHom k G [Q.residueFieldReduction]ₚ₀ := by
          simpa using
            (cartanHom_projectiveClass_eq k G Q.residueFieldReduction).symm

/-- Helper for Proposition 15-15.5-1: the Cartan class of the residue-field reduction of a
projective `A[G]`-module is its finite-representation class. -/
private theorem residueFieldReduction_cartan_class_eq_finiteRepClass_local
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    cartanHom k G [Q.residueFieldReduction]ₚ₀ = [Q.residueFieldReduction.toFiniteRep]₀ := by
  -- The residue-field reduction is already projective over `k[G]`, so its Cartan class is the
  -- corresponding finite-representation class.
  exact cartanHom_projectiveClass_eq k G Q.residueFieldReduction

/-- Helper for Proposition 15-15.5-1: LinearRepresentations_Serre_1977's projective generator identity immediately rewrites
the scalar-extension class of `Q` to the finite-representation class of its residue reduction. -/
private theorem decompositionHom_projective_scalarExtension_class_eq_finiteRepClass_local
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    decompositionHom A K G [Q.scalarExtension K]₀ =
      [Q.residueFieldReduction.toFiniteRep]₀ := by
  -- First compute `d([Q_K])` by LinearRepresentations_Serre_1977's projective formula, then collapse the Cartan class of the
  -- projective residue reduction to its ordinary finite-representation class.
  calc
    decompositionHom A K G [Q.scalarExtension K]₀ =
        cartanHom k G [Q.residueFieldReduction]ₚ₀ := by
          exact
            decompositionHom_projective_scalarExtension_class_eq_residueFieldReduction_class
              (A := A) (K := K) (G := G) Q
    _ = [Q.residueFieldReduction.toFiniteRep]₀ := by
          exact residueFieldReduction_cartan_class_eq_finiteRepClass_local Q

/-- Helper for Proposition 15-15.5-1: if a projective lift reduces to `τ`, then LinearRepresentations_Serre_1977's
decomposition map sends its generic class to `[τ]₀`. -/
private theorem decompositionHom_projective_scalarExtension_class_eq_iso_target_local
    (Q : FiniteProjectiveGroupAlgebraModule A G) {τ : FDRep k G}
    (hQτ : Nonempty (Q.residueFieldReduction.toFiniteRep ≅ τ)) :
    decompositionHom A K G [Q.scalarExtension K]₀ = [τ]₀ := by
  -- Compute `d([Q_K])` by the reduction of `Q`, then transport along the chosen reduction
  -- isomorphism to the target simple class.
  calc
    decompositionHom A K G [Q.scalarExtension K]₀ =
        [Q.residueFieldReduction.toFiniteRep]₀ := by
          exact
            decompositionHom_projective_scalarExtension_class_eq_finiteRepClass_local
              (A := A) (K := K) (G := G) Q
    _ = [τ]₀ := by
          simpa using
            finiteRepGrothendieckClass_eq_of_nonempty_iso (L := k) (G := G) hQτ

/-- Helper for Proposition 15-15.5-1: if a lifted projective module reduces to a simple
`k[G]`-representation, then its generic fiber is simple. -/
private theorem projective_lift_scalarExtension_simple_of_order_prime_to_p
    (hG : ¬ p ∣ Nat.card G)
    (S : FDRep k G) [Simple S]
    (Q : FiniteProjectiveGroupAlgebraModule A G)
    (hQS : Nonempty (Q.residueFieldReduction.toFiniteRep ≅ S)) :
    Simple (Q.scalarExtension K) := by
  let _ : NeZero (Nat.card G : k) := NeZero.of_not_dvd k hG
  obtain ⟨L, hL⟩ :=
    projective_scalarExtension_literal_reduction_class_local
      (A := A) (K := K) (G := G) Q
  have hsemiL : IsSemisimpleRepresentation (FDRep.of L.reductionRepresentation).ρ := by
    infer_instance
  have hsemiS : IsSemisimpleRepresentation S.ρ := by
    infer_instance
  have hclass :
      [FDRep.of L.reductionRepresentation]₀ = [S]₀ := by
    -- First rewrite the reduction of the literal lattice to the intrinsic residue reduction of
    -- `Q`, and then use the chosen isomorphism with the simple target `S`.
    calc
      [FDRep.of L.reductionRepresentation]₀ = [Q.residueFieldReduction.toFiniteRep]₀ := hL
      _ = [S]₀ := by
            simpa using finiteRepGrothendieckClass_eq_of_nonempty_iso
              (L := k) (G := G) hQS
  rcases
      (finiteRepGrothendieckClass_eq_iff_nonempty_iso_of_isSemisimple hsemiL hsemiS).mp hclass
    with ⟨eLS⟩
  let _ : Simple (FDRep.of L.reductionRepresentation) := CategoryTheory.Simple.of_iso eLS
  have hLirr : L.reductionRepresentation.IsIrreducible := by
    -- The reduction representation is simple because it is isomorphic to `S`.
    simpa using FDRep.isIrreducible_of_simple (FDRep.of L.reductionRepresentation)
  have hQirr : Representation.IsIrreducible (Q.scalarExtension K).ρ := by
    -- LinearRepresentations_Serre_1977's route now applies the simple-reduction criterion to the literal stable lattice.
    simpa using simple_reduction_implies_isIrreducible
      (A := A) (K := K) (G := G) ((Q.scalarExtension K).ρ) L hLirr
  exact FDRep.simple_of_isIrreducible (Q.scalarExtension K)

/-- Helper for Proposition 15-15.5-1: once an isomorphism of reductions reflects to an
isomorphism of the generic fibers, pairwise nonisomorphism of the reduced family follows
immediately. -/
private theorem stableLattice_reductionFamily_pairwise_of_iso_reflection
    {S : Type v}
    (πK : S → FDRep K G)
    (hπK_pairwise : PairwiseNonisomorphic πK)
    (L : ∀ i, StableLattice A (πK i).ρ)
    (hreflect :
      ∀ {i j : S},
        Nonempty (FDRep.of (L i).reductionRepresentation ≅
          FDRep.of (L j).reductionRepresentation) →
        Nonempty (πK i ≅ πK j)) :
    let πk : S → FDRep k G := fun i ↦ FDRep.of (L i).reductionRepresentation
    PairwiseNonisomorphic πk := by
  dsimp
  intro i j hij hijred
  -- Any isomorphism between the chosen reductions would lift back upstairs, contradicting the
  -- pairwise nonisomorphism of the simple generic family.
  exact hπK_pairwise hij (hreflect hijred)

/-- Helper for Proposition 15-15.5-1: the tautological `F[G]`-module attached to a
representation is canonically linear-equivalent to its carrier. -/
private theorem nonempty_asModuleLinearEquiv_target_field_local
    {F : Type u} [Field F]
    {V : Type v} [AddCommGroup V] [Module F V]
    (ρ : Representation F G V) :
    letI : Module F[G] V := Module.compHom V ρ.asAlgebraHom.toRingHom
    letI : IsScalarTower F F[G] V :=
      IsScalarTower.of_algebraMap_smul fun a x ↦ by
        change ρ.asAlgebraHom (algebraMap F F[G] a) x = a • x
        simp [Algebra.smul_def]
    Nonempty (ρ.asModule ≃ₗ[F[G]] V) := by
  letI : Module F[G] V := Module.compHom V ρ.asAlgebraHom.toRingHom
  letI : IsScalarTower F F[G] V :=
    IsScalarTower.of_algebraMap_smul fun a x ↦ by
      change ρ.asAlgebraHom (algebraMap F F[G] a) x = a • x
      simp [Algebra.smul_def]
  refine ⟨
    { toFun := fun x ↦ ρ.asModuleEquiv x
      invFun := fun x ↦ ρ.asModuleEquiv.symm x
      left_inv := fun x ↦ ρ.asModuleEquiv.symm_apply_apply x
      right_inv := fun x ↦ ρ.asModuleEquiv.apply_symm_apply x
      map_add' := fun x y ↦ ρ.asModuleEquiv.map_add x y
      map_smul' := ?_ }⟩
  intro a x
  calc
    ρ.asModuleEquiv (a • x) = ρ.asAlgebraHom a (ρ.asModuleEquiv x) := by
      simpa using Representation.asModuleEquiv_map_smul (ρ := ρ) a x
    _ = a • ρ.asModuleEquiv x := by
          rfl

/-- Helper for Proposition 15-15.5-1: a `K[G]`-linear equivalence of owner modules upgrades to an
isomorphism in `FDRep K G`. -/
private theorem fdRep_nonempty_iso_of_nonempty_asModuleLinearEquiv_field_local
    {σ τ : FDRep K G}
    (hστ : Nonempty (asModule σ.ρ ≃ₗ[K[G]] asModule τ.ρ)) :
    Nonempty (σ ≅ τ) := by
  exact
    Representation.fdRep_nonempty_iso_of_nonempty_asModuleLinearEquiv_field_local_support
      (K := K) (G := G) hστ

/-- Helper for Proposition 15-15.5-1: scalar extension transports an exact-owner
`A[G]`-linear equivalence to the corresponding `K[G]`-linear equivalence on the generic fibers. -/
private theorem scalarExtension_nonempty_linearEquiv_of_nonempty_linearEquiv_local
    {P Q : Type v} [AddCommGroup P] [Module A P] [Module A[G] P] [IsScalarTower A A[G] P]
    [AddCommGroup Q] [Module A Q] [Module A[G] Q] [IsScalarTower A A[G] Q]
    (hPQ : Nonempty (P ≃ₗ[A[G]] Q)) :
    Nonempty ((K ⊗[A] P) ≃ₗ[K[G]] (K ⊗[A] Q)) := by
  rcases hPQ with ⟨e⟩
  let e₀ : (K ⊗[A] P) ≃ₗ[K] (K ⊗[A] Q) :=
    LinearEquiv.baseChange A K P Q (LinearEquiv.restrictScalars A e)
  refine ⟨
    { toFun := e₀
      invFun := e₀.symm
      left_inv := e₀.left_inv
      right_inv := e₀.right_inv
      map_add' := e₀.map_add
      map_smul' := ?_ }⟩
  intro a x
  -- Extend the `MonoidAlgebra.of` computation from pure tensors to all scalars in `K[G]`.
  refine MonoidAlgebra.induction_on
    (p := fun b : K[G] => e₀ (b • x) = b • e₀ x) a ?_ ?_ ?_
  · intro g
    induction x using TensorProduct.induction_on with
    | zero =>
        simp [e₀]
    | tmul c p =>
        have hq :
            MonoidAlgebra.of K G g • (c ⊗ₜ[A] e p : K ⊗[A] Q) =
              (c ⊗ₜ[A] (MonoidAlgebra.of A G g • e p) : K ⊗[A] Q) := by
          simpa using
            monoidAlgebra_of_smul_tmul (Λ := A) (κ := K) (G := G) (P := Q) g c (e p)
        have hp :
            MonoidAlgebra.of K G g • (c ⊗ₜ[A] p : K ⊗[A] P) =
              (c ⊗ₜ[A] (MonoidAlgebra.of A G g • p) : K ⊗[A] P) := by
          simpa using
            monoidAlgebra_of_smul_tmul (Λ := A) (κ := K) (G := G) (P := P) g c p
        calc
          e₀ (MonoidAlgebra.of K G g • (c ⊗ₜ[A] p : K ⊗[A] P))
              = e₀ (c ⊗ₜ[A] (MonoidAlgebra.of A G g • p) : K ⊗[A] P) := by
                  rw [hp]
          _ = (c ⊗ₜ[A] e (MonoidAlgebra.of A G g • p) : K ⊗[A] Q) := by
                simp [e₀, LinearEquiv.baseChange_tmul]
          _ = (c ⊗ₜ[A] (MonoidAlgebra.of A G g • e p) : K ⊗[A] Q) := by
                rw [e.map_smul]
          _ = MonoidAlgebra.of K G g • e₀ (c ⊗ₜ[A] p : K ⊗[A] P) := by
                rw [← hq]
                simp [e₀, LinearEquiv.baseChange_tmul]
    | add y z hy hz =>
        calc
          e₀ (MonoidAlgebra.of K G g • (y + z))
              = e₀ (MonoidAlgebra.of K G g • y) + e₀ (MonoidAlgebra.of K G g • z) := by
                  rw [smul_add, map_add]
          _ = MonoidAlgebra.of K G g • e₀ y + MonoidAlgebra.of K G g • e₀ z := by
                rw [hy, hz]
          _ = MonoidAlgebra.of K G g • e₀ (y + z) := by
                simp [smul_add, e₀.map_add]
  · intro a b ha hb
    simp [ha, hb, add_smul]
  · intro c b hb
    calc
      e₀ ((c • b) • x) = e₀ (c • (b • x)) := by simp [smul_smul]
      _ = c • e₀ (b • x) := by simp
      _ = c • (b • e₀ x) := by rw [hb]
      _ = (c • b) • e₀ x := by simp [smul_smul]

/-- Helper for Proposition 15-15.5-1: an isomorphism between the chosen reductions should
reflect to an isomorphism between the generic fibers when `p ∤ |G|`. -/
-- Route correction: LinearRepresentations_Serre_1977's injectivity step should stay on the exact owners `L.toSubmodule`;
-- once the reduction isomorphism reflects there, scalar extension and the support-file exact-owner
-- identifications transport it back to the original generic fibers.
private theorem stableLattice_reduction_iso_implies_generic_iso_of_order_prime_to_p
    {S : Type v}
    (hG : ¬ p ∣ Nat.card G)
    (πK : S → FDRep K G)
    (L : ∀ i, StableLattice A (πK i).ρ)
    {i j : S}
    (hij :
      Nonempty (FDRep.of (L i).reductionRepresentation ≅
        FDRep.of (L j).reductionRepresentation)) :
    Nonempty (πK i ≅ πK j) := by
  have hOwner :
      Nonempty ((L i).toSubmodule ≃ₗ[A[G]] (L j).toSubmodule) :=
    StableLattice.reduction_iso_reflects_exact_owner_linearEquiv_of_order_prime_to_p
      (A := A) (K := K) (G := G) (p := p) hG (L i) (L j) hij
  have hOwnerK :
      Nonempty ((K ⊗[A] (L i).toSubmodule) ≃ₗ[K[G]] (K ⊗[A] (L j).toSubmodule)) :=
    scalarExtension_nonempty_linearEquiv_of_nonempty_linearEquiv_local
      (A := A) (K := K) (G := G) hOwner
  have hi_owner :
      Nonempty
        (asModule
            (show Representation K G (K ⊗[A] (L i).toSubmodule) from
              Representation.scalarExtension (L i).toRepresentation) ≃ₗ[K[G]]
          (K ⊗[A] (L i).toSubmodule)) :=
    StableLattice.scalarExtension_exact_owner_asModule_linearEquiv_local_support
      (A := A) (K := K) (G := G) (L i)
  have hj_owner :
      Nonempty
        (asModule
            (show Representation K G (K ⊗[A] (L j).toSubmodule) from
              Representation.scalarExtension (L j).toRepresentation) ≃ₗ[K[G]]
          (K ⊗[A] (L j).toSubmodule)) :=
    StableLattice.scalarExtension_exact_owner_asModule_linearEquiv_local_support
      (A := A) (K := K) (G := G) (L j)
  have hExact :
      Nonempty
        (FDRep.of
            (show Representation K G (K ⊗[A] (L i).toSubmodule) from
              Representation.scalarExtension (L i).toRepresentation) ≅
          FDRep.of
            (show Representation K G (K ⊗[A] (L j).toSubmodule) from
              Representation.scalarExtension (L j).toRepresentation)) := by
    rcases hi_owner with ⟨ei⟩
    rcases hOwnerK with ⟨eij⟩
    rcases hj_owner with ⟨ej⟩
    -- Compare the two exact-owner scalar extensions through the transported tensor-owner
    -- equivalence.
    exact
      fdRep_nonempty_iso_of_nonempty_asModuleLinearEquiv_field_local
        (σ := FDRep.of
          (show Representation K G (K ⊗[A] (L i).toSubmodule) from
            Representation.scalarExtension (L i).toRepresentation))
        (τ := FDRep.of
          (show Representation K G (K ⊗[A] (L j).toSubmodule) from
            Representation.scalarExtension (L j).toRepresentation))
        (G := G)
        ⟨by simpa using ei.trans (eij.trans ej.symm)⟩
  rcases StableLattice.scalarExtension_exact_owner_fdrep_iso_local_support
      (A := A) (K := K) (G := G) (X := πK i) (L := L i) with
    ⟨ei⟩
  rcases hExact with ⟨eExact⟩
  rcases StableLattice.scalarExtension_exact_owner_fdrep_iso_local_support
      (A := A) (K := K) (G := G) (X := πK j) (L := L j) with
    ⟨ej⟩
  -- Reflect the reduced isomorphism to the exact owners, scalar-extend, and then identify those
  -- exact-owner scalar extensions with the original generic fibers.
  exact ⟨ei.symm.trans (eExact.trans ej)⟩

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
private theorem subrepresentation_prod_nonempty_asModuleLinearEquiv_of_isCompl_local
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
private theorem subrepresentation_prod_asModule_to_factorwise_product_linearEquiv_local
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
private theorem reduction_prod_nonempty_linearEquiv_local
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
private theorem scalarExtension_prod_nonempty_linearEquiv_local
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
private theorem prod_representation_not_isIrreducible_of_nontrivial_local
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
private theorem subrepresentation_isCompl_toSubmodule_local
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
private theorem tensorProduct_nontrivial_of_free_local
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

/-- Helper for Proposition 15-15.5-1: irreducibility transports across a representation
equivalence. -/
private noncomputable def subrepresentationOrderIso_local
    {F : Type u} [Field F]
    {W W' : Type v} [AddCommGroup W] [Module F W]
    [AddCommGroup W'] [Module F W']
    {ρ : Representation F G W} {σ : Representation F G W'}
    (e : ρ.Equiv σ) :
    Subrepresentation ρ ≃o Subrepresentation σ where
  toFun U :=
    { toSubmodule := U.toSubmodule.map e.toLinearMap
      apply_mem_toSubmodule := by
        intro g x hx
        rcases hx with ⟨y, hy, rfl⟩
        refine ⟨ρ g y, U.apply_mem_toSubmodule g hy, ?_⟩
        simp [e.isIntertwining] }
  invFun U :=
    { toSubmodule := U.toSubmodule.map e.symm.toLinearMap
      apply_mem_toSubmodule := by
        intro g x hx
        rcases hx with ⟨y, hy, rfl⟩
        refine ⟨σ g y, U.apply_mem_toSubmodule g hy, ?_⟩
        simp [e.symm.isIntertwining] }
  left_inv := by
    intro U
    apply Subrepresentation.toSubmodule_injective
    ext x
    constructor
    · intro hx
      rcases hx with ⟨y, hy, hxy⟩
      have : y = e x := by
        simpa using congrArg e hxy
      subst this
      simp at hy
      exact hy
    · intro hx
      change x ∈
        Submodule.map e.symm.toLinearMap (Submodule.map e.toLinearMap U.toSubmodule)
      exact ⟨e x, ⟨x, hx, rfl⟩, by simp⟩
  right_inv := by
    intro U
    apply Subrepresentation.toSubmodule_injective
    ext x
    constructor
    · intro hx
      rcases hx with ⟨y, hy, hxy⟩
      have : y = e.symm x := by
        simpa using congrArg e.symm hxy
      subst this
      simp at hy
      exact hy
    · intro hx
      change x ∈
        Submodule.map e.toLinearMap (Submodule.map e.symm.toLinearMap U.toSubmodule)
      exact ⟨e.symm x, ⟨x, hx, rfl⟩, by simp⟩
  map_rel_iff' := by
    intro U V
    constructor
    · intro h x hx
      have hx' : e x ∈ U.toSubmodule.map e.toLinearMap := ⟨x, hx, rfl⟩
      rcases h hx' with ⟨y, hy, hxy⟩
      have : y = x := by
        apply e.toLinearEquiv.injective
        simpa using hxy
      simpa [this] using hy
    · intro h x hx
      rcases hx with ⟨y, hy, rfl⟩
      exact ⟨y, h hy, rfl⟩

/-- Helper for Proposition 15-15.5-1: irreducibility transports across a representation
equivalence. -/
private theorem isIrreducible_of_equiv_local
    {F : Type u} [Field F]
    {W W' : Type v} [AddCommGroup W] [Module F W]
    [AddCommGroup W'] [Module F W']
    {ρ : Representation F G W} {σ : Representation F G W'}
    [ρ.IsIrreducible] (e : ρ.Equiv σ) : σ.IsIrreducible := by
  -- Irreducibility is the simple-order owner on subrepresentations, so transport it through the
  -- mapped-carrier order isomorphism.
  exact OrderIso.isSimpleOrder_iff (subrepresentationOrderIso_local (G := G) e) |>.mp inferInstance

/-- Helper for Proposition 15-15.5-1: under Maschke's hypothesis, a reduced subrepresentation can
be packaged on its exact `asModule` owner as a finite projective `k[G]`-module. -/
private theorem subrepresentation_asModule_finiteProjective_owner_of_order_prime_to_p
    (τ : FDRep k G)
    (U : Subrepresentation τ.ρ)
    (hG : ¬ p ∣ Nat.card G) :
    ∃ P : FiniteProjectiveGroupAlgebraModule k G,
      Nonempty (P.V ≃ₗ[k[G]] asModule U.toRepresentation) := by
  letI : Module k[G] U.toSubmodule :=
    Module.compHom U.toSubmodule U.toRepresentation.asAlgebraHom.toRingHom
  letI : IsScalarTower k k[G] U.toSubmodule :=
    IsScalarTower.of_algebraMap_smul fun a x ↦ by
      change U.toRepresentation.asAlgebraHom (algebraMap k k[G] a) x = a • x
      simp [Algebra.smul_def]
  let M : ModuleCat k[G] := ModuleCat.of k[G] U.toSubmodule
  have hfinite : Module.Finite k[G] M := by
    -- The reduced summand is finite-dimensional over `k`, hence finite over the group algebra.
    change Module.Finite k[G] U.toSubmodule
    exact Module.Finite.of_restrictScalars_finite k k[G] U.toSubmodule
  let Pfg : FGModuleCat k[G] := ⟨M, hfinite⟩
  have hproj_sub : Module.Projective k[G] U.toSubmodule :=
    groupAlgebra_module_projective_of_order_prime_to_p
      (G := G) (M := U.toSubmodule) hG
  have hproj : Module.Projective k[G] Pfg := by
    -- Route correction: package the summand on the exact `asModule` carrier itself, so the
    -- Maschke projectivity owner applies without any subtype-owner transport.
    simpa [Pfg, M] using hproj_sub
  let P : FiniteProjectiveGroupAlgebraModule k G := ⟨Pfg, hproj⟩
  rcases
      nonempty_asModuleLinearEquiv_target_field_local
        (G := G) (ρ := U.toRepresentation) with
    ⟨eU⟩
  refine ⟨P, ?_⟩
  -- The chosen owner is definitionally the exact `asModule` carrier of `U`.
  exact ⟨by
    simpa [P, Pfg, M, FiniteProjectiveGroupAlgebraModule.V] using
      eU.symm⟩

/-- Helper for Proposition 15-15.5-1: each reduced summand lifts to a finite projective
`A[G]`-module whose residue-field reduction is the exact `asModule` owner of that summand. -/
private theorem subrepresentation_exists_projective_lift_of_order_prime_to_p
    (τ : FDRep k G)
    (U : Subrepresentation τ.ρ)
    (hG : ¬ p ∣ Nat.card G) :
    ∃ Q : FiniteProjectiveGroupAlgebraModule A G,
      Nonempty ((k ⊗[A] Q.V) ≃ₗ[k[G]] asModule U.toRepresentation) := by
  obtain ⟨P, hP⟩ :=
    subrepresentation_asModule_finiteProjective_owner_of_order_prime_to_p
      (G := G) (p := p) τ U hG
  obtain ⟨Q, hQP⟩ :=
    Representation.exists_projective_lift_of_residueField_projective
      (A := A) (G := G) P
  rcases hP with ⟨eP⟩
  rcases
      (finiteProjectiveGroupAlgebraModule_nonempty_iso_iff_nonempty_linearEquiv
        (A := k) (G := G) Q.residueFieldReduction P).1 hQP with
    ⟨eQP⟩
  refine ⟨Q, ?_⟩
  -- The Chapter `14` lift theorem already identifies the residue-field reduction of `Q` with the
  -- canonical summand owner `P`; now forget the owner and read the carrier as `asModule U`.
  exact ⟨by
    simpa [FiniteProjectiveGroupAlgebraModule.residueFieldReduction,
      FiniteProjectiveGroupAlgebraModule.V] using
      eQP.trans eP⟩

/-- Helper for Proposition 15-15.5-1: a complemented split of the reduction rewrites as the
reduction of a product of projective lifts of the two factors. -/
private theorem reduction_split_to_lifted_product_linearEquiv_local
    (X : FDRep K G)
    (hG : ¬ p ∣ Nat.card G)
    (L : StableLattice A X.ρ)
    (U V : Subrepresentation L.reductionRepresentation)
    (hUV : IsCompl U V) :
    ∃ QU QV : FiniteProjectiveGroupAlgebraModule A G,
      Nonempty ((k ⊗[A] QU.V) ≃ₗ[k[G]] asModule U.toRepresentation) ∧
      Nonempty ((k ⊗[A] QV.V) ≃ₗ[k[G]] asModule V.toRepresentation) ∧
      Nonempty (L.reduction ≃ₗ[k[G]] k ⊗[A] (QU.V × QV.V)) := by
  obtain ⟨QU, hQU⟩ :=
    subrepresentation_exists_projective_lift_of_order_prime_to_p
      (A := A) (G := G) (p := p) (τ := FDRep.of L.reductionRepresentation) U hG
  obtain ⟨QV, hQV⟩ :=
    subrepresentation_exists_projective_lift_of_order_prime_to_p
      (A := A) (G := G) (p := p) (τ := FDRep.of L.reductionRepresentation) V hG
  rcases hQU with ⟨eQU⟩
  rcases hQV with ⟨eQV⟩
  rcases
      subrepresentation_prod_nonempty_asModuleLinearEquiv_of_isCompl_local
        (G := G) U V
        (subrepresentation_isCompl_toSubmodule_local (G := G) hUV) with
    ⟨eSplit⟩
  rcases
      subrepresentation_prod_asModule_to_factorwise_product_linearEquiv_local
        (G := G) U V with
    ⟨eProd⟩
  rcases
      reduction_prod_nonempty_linearEquiv_local
        (A := A) (G := G) (P := QU.V) (Q := QV.V) with
    ⟨ered⟩
  refine ⟨QU, QV, ?_, ?_, ?_⟩
  · exact ⟨eQU⟩
  · exact ⟨eQV⟩
  · -- Follow LinearRepresentations_Serre_1977's source route: split the reduced module, identify the product owner
    -- factorwise, then rewrite the factorwise summands as reductions of lifted projectives.
    exact ⟨by
      simpa using
        eSplit.symm.trans
          (eProd.trans
            ((LinearEquiv.prodCongr eQU.symm eQV.symm).trans ered.symm))⟩
/-- Helper for Proposition 15-15.5-1: scalar extension of the product exact owner identifies
directly with the `asModule` owner of the product representation upstairs. -/
private theorem scalarExtension_prod_exact_owner_asModule_linearEquiv_local
    (QU QV : FiniteProjectiveGroupAlgebraModule A G) :
    Nonempty ((K ⊗[A] (QU.V × QV.V)) ≃ₗ[K[G]]
      asModule (Representation.prod (QU.scalarExtension K).ρ (QV.scalarExtension K).ρ)) := by
  let Dom := (K ⊗[A] QU.V) × (K ⊗[A] QV.V)
  let ρprod : Representation K G Dom :=
    Representation.prod (QU.scalarExtension K).ρ (QV.scalarExtension K).ρ
  rcases
      scalarExtension_prod_nonempty_linearEquiv_local
        (A := A) (K := K) (G := G) (P := QU.V) (Q := QV.V) with
    ⟨eprod⟩
  let eρprod : asModule ρprod ≃ₗ[K[G]] Dom :=
    { toFun := fun x ↦ ρprod.asModuleEquiv x
      invFun := fun x ↦ ρprod.asModuleEquiv.symm x
      left_inv := fun x ↦ ρprod.asModuleEquiv.left_inv x
      right_inv := fun x ↦ ρprod.asModuleEquiv.right_inv x
      map_add' := fun x y ↦ ρprod.asModuleEquiv.map_add x y
      map_smul' := by
        intro r x
        calc
          ρprod.asModuleEquiv (r • x) = ρprod.asAlgebraHom r (ρprod.asModuleEquiv x) := by
            exact Representation.asModuleEquiv_map_smul (ρ := ρprod) r x
          _ = r • ρprod.asModuleEquiv x := by
            rcases ρprod.asModuleEquiv x with ⟨x₁, x₂⟩
            refine MonoidAlgebra.induction_on
              (p := fun s : K[G] => ρprod.asAlgebraHom s (x₁, x₂) = s • (x₁, x₂)) r ?_ ?_ ?_
            · intro g
              have hQU :
                  ((QU.scalarExtension K).ρ g) x₁ =
                    MonoidAlgebra.of K G g • x₁ := by
                exact Representation.asModuleEquiv_symm_map_rho
                  (ρ := (QU.scalarExtension K).ρ) g x₁
              have hQV :
                  ((QV.scalarExtension K).ρ g) x₂ =
                    MonoidAlgebra.of K G g • x₂ := by
                exact Representation.asModuleEquiv_symm_map_rho
                  (ρ := (QV.scalarExtension K).ρ) g x₂
              ext
              · simpa [ρprod, Representation.prod, Representation.asAlgebraHom_of] using hQU
              · simpa [ρprod, Representation.prod, Representation.asAlgebraHom_of] using hQV
            · intro a b ha hb
              calc
                ρprod.asAlgebraHom (a + b) (x₁, x₂)
                    = ρprod.asAlgebraHom a (x₁, x₂) + ρprod.asAlgebraHom b (x₁, x₂) := by
                        simp [map_add]
                _ = a • (x₁, x₂) + b • (x₁, x₂) := by rw [ha, hb]
                _ = (a + b) • (x₁, x₂) := by simp [add_smul]
            · intro c a ha
              calc
                ρprod.asAlgebraHom (c • a) (x₁, x₂)
                    = c • ρprod.asAlgebraHom a (x₁, x₂) := by simp
                _ = c • (a • (x₁, x₂)) := by rw [ha]
                _ = (c • a) • (x₁, x₂) := by simp }
  -- Keep the product side unbundled until the end: first split the tensor product, then identify
  -- the resulting carrier with the canonical `asModule` owner of the product representation.
  exact ⟨by
    simpa [Dom, ρprod] using eprod.trans eρprod.symm⟩

/-- Helper for Proposition 15-15.5-1: the scalar extension of the exact lattice owner is already
the raw tensor-product `K[G]`-module on `K ⊗[A] L.toSubmodule`. -/
private theorem scalarExtension_exact_owner_asModule_linearEquiv_local
    (X : FDRep K G)
    (L : StableLattice A X.ρ) :
    Nonempty
      (asModule
          (show Representation K G (K ⊗[A] L.toSubmodule) from
            Representation.scalarExtension L.toRepresentation) ≃ₗ[K[G]]
        (K ⊗[A] L.toSubmodule)) := by
  exact
    StableLattice.scalarExtension_exact_owner_asModule_linearEquiv_local_support
      (A := A) (K := K) (G := G) L

/-- Helper for Proposition 15-15.5-1: after reflecting the reduced split to the exact owner
upstairs, scalar extension lands directly in the product representation owner. -/
private theorem reflected_exact_owner_scalarExtension_to_prod_asModule_linearEquiv_local
    (X : FDRep K G)
    (L : StableLattice A X.ρ)
    (QU QV : FiniteProjectiveGroupAlgebraModule A G)
    (hA : Nonempty (L.toSubmodule ≃ₗ[A[G]] (QU.V × QV.V))) :
    Nonempty ((K ⊗[A] L.toSubmodule) ≃ₗ[K[G]]
      asModule (Representation.prod (QU.scalarExtension K).ρ (QV.scalarExtension K).ρ)) := by
  rcases
      scalarExtension_nonempty_linearEquiv_of_nonempty_linearEquiv_local
        (A := A) (K := K) (G := G) (P := L.toSubmodule) (Q := QU.V × QV.V) hA with
    ⟨eK⟩
  rcases
      scalarExtension_prod_exact_owner_asModule_linearEquiv_local
        (A := A) (K := K) (G := G) QU QV with
    ⟨eprod⟩
  -- Base-change LinearRepresentations_Serre_1977's exact-owner equivalence once, then compose with the raw product-owner
  -- adapter instead of bundling a separate product projective owner.
  exact ⟨eK.trans eprod⟩

/-- Helper for Proposition 15-15.5-1: the scalar extension of the exact lattice owner is
isomorphic to the product of the lifted summands upstairs. -/
private theorem stableLattice_exact_owner_scalarExtension_to_product_iso_local
    (X : FDRep K G)
    (L : StableLattice A X.ρ)
    (QU QV : FiniteProjectiveGroupAlgebraModule A G)
    (hA : Nonempty (L.toSubmodule ≃ₗ[A[G]] (QU.V × QV.V))) :
    Nonempty (FDRep.of (Representation.scalarExtension L.toRepresentation) ≅
      FDRep.of (Representation.prod (QU.scalarExtension K).ρ (QV.scalarExtension K).ρ)) := by
  let ρL : Representation K G (K ⊗[A] L.toSubmodule) :=
    Representation.scalarExtension L.toRepresentation
  let ρprod : Representation K G ((K ⊗[A] QU.V) × (K ⊗[A] QV.V)) :=
    Representation.prod (QU.scalarExtension K).ρ (QV.scalarExtension K).ρ
  rcases
      scalarExtension_exact_owner_asModule_linearEquiv_local
        (A := A) (K := K) (G := G) X L with
    ⟨eOwnerL⟩
  rcases
      reflected_exact_owner_scalarExtension_to_prod_asModule_linearEquiv_local
        (A := A) (K := K) (G := G) X L QU QV hA with
    ⟨hKprod⟩
  -- Compare the explicit scalar-extension owner of `L` with the product owner obtained from the
  -- reflected split, then package that owner comparison as an `FDRep` isomorphism.
  exact
    fdRep_nonempty_iso_of_nonempty_asModuleLinearEquiv_field_local
      (σ := FDRep.of (Representation.scalarExtension L.toRepresentation))
      (τ := FDRep.of
        (Representation.prod (QU.scalarExtension K).ρ (QV.scalarExtension K).ρ))
      (G := G) ⟨eOwnerL.trans hKprod⟩

/-- Helper for Proposition 15-15.5-1: a reduced product split reflects directly to an exact-owner
`A[G]`-linear equivalence when `p ∤ |G|`. -/
-- Route correction: apply Chapter `14`'s projective reflection theorem to the actual product owner
-- `QU.V × QV.V`, rather than trying to rebundle that owner as a second stable lattice.
private theorem StableLattice.reduction_split_reflects_exact_owner_product_linearEquiv_of_order_prime_to_p_local
    (hG : ¬ p ∣ Nat.card G)
    {X : FDRep K G}
    (L : StableLattice A X.ρ)
    (QU QV : FiniteProjectiveGroupAlgebraModule A G)
    (hred : Nonempty (L.reduction ≃ₗ[k[G]] k ⊗[A] (QU.V × QV.V))) :
    Nonempty (L.toSubmodule ≃ₗ[A[G]] (QU.V × QV.V)) := by
  let _ : Module.Free A L.toSubmodule := by
    infer_instance
  have hprojL : Module.Projective A[G] L.toSubmodule := by
    -- LinearRepresentations_Serre_1977's averaging argument packages the exact lattice owner as projective over `A[G]`.
    exact
      free_groupAlgebra_module_projective_of_order_prime_to_p
        (A := A) (G := G) (p := p) (P := L.toSubmodule) hG
  have hprojProd : Module.Projective A[G] (QU.V × QV.V) := by
    -- The product owner remains projective because both lifted summands already are.
    infer_instance
  -- Reflect the reduced product equivalence through the canonical residue-field reductions on the
  -- two exact owners.
  exact
    (projective_monoidAlgebra_nonempty_linearEquiv_iff_of_isResidueFieldReduction
      (Λ := A) (G := G)
      (P := L.toSubmodule)
      (Pbar := L.reduction)
      (f := (Submodule.mkQ L.maximalIdealSubmodule : L.toSubmodule →ₗ[A] L.reduction))
      (hf := StableLattice.reduction_mkQ_isResidueFieldReduction_local
        (A := A) (K := K) (G := G) L)
      (P' := QU.V × QV.V)
      (Pbar' := k ⊗[A] (QU.V × QV.V))
      (f' := (TensorProduct.mk A k (QU.V × QV.V) 1 :
        (QU.V × QV.V) →ₗ[A] k ⊗[A] (QU.V × QV.V)))
      (hf' := MonoidAlgebra.tensorProduct_mk_isResidueFieldReduction
        (Λ := A) (G := G) (P := QU.V × QV.V))
      hprojL hprojProd).2 hred

/-- Helper for Proposition 15-15.5-1: nontriviality of a residue-field tensor factor already
forces nontriviality after scalar extension to the fraction field. -/
private theorem nontrivial_scalar_extension_of_nontrivial_reduction_factor_local
    {P : Type v} [AddCommGroup P] [Module A P] [Module.Free A P]
    (hred : Nontrivial (k ⊗[A] P)) :
    Nontrivial (K ⊗[A] P) := by
  have hP : Nontrivial P := by
    by_contra hP
    let _ : Subsingleton P := not_nontrivial_iff_subsingleton.mp hP
    -- If the exact owner collapsed to a singleton, so would its reduction tensor.
    exact
      (not_nontrivial_iff_subsingleton.mpr
        (inferInstance : Subsingleton (k ⊗[A] P))) hred
  let _ : Nontrivial P := hP
  -- Once the exact owner is nontrivial, the fraction-field tensor stays nontrivial by
  -- injectivity of `x ↦ 1 ⊗ x` on free modules.
  exact tensorProduct_nontrivial_of_free_local (A := A) (K := K) (P := P)

-- Helper for Proposition 15-15.5-1: the reduction of a stable lattice in a simple
-- `K[G]`-representation should again be simple when `p ∤ |G|`.
-- Route correction: the source proof reflects a nontrivial reduced splitting back to the generic
-- fiber via the exact-owner projective package on `L.toSubmodule`; that reflection step is the
-- only remaining blocker here.
/-- Helper for Proposition 15-15.5-1: core split-reflection package for the exact-owner route. -/
private theorem stableLattice_reduction_split_reflects_generic_nonsimple_of_order_prime_to_p_core
    (hG : ¬ p ∣ Nat.card G)
    (X : FDRep K G) [Simple X]
    (L : StableLattice A X.ρ)
    (U V : Subrepresentation L.reductionRepresentation)
    (hUV : IsCompl U V) (hU : U ≠ ⊥) (hV : V ≠ ⊥) :
    False := by
  obtain ⟨QU, QV, hQU, hQV, hred⟩ :=
    reduction_split_to_lifted_product_linearEquiv_local
      (A := A) (K := K) (G := G) (p := p) X hG L U V hUV
  rcases hQU with ⟨eQU⟩
  rcases hQV with ⟨eQV⟩
  have hA :
      Nonempty (L.toSubmodule ≃ₗ[A[G]] (QU.V × QV.V)) :=
    StableLattice.reduction_split_reflects_exact_owner_product_linearEquiv_of_order_prime_to_p_local
      (A := A) (K := K) (G := G) (p := p) hG L QU QV hred
  let ρprod : Representation K G ((K ⊗[A] QU.V) × (K ⊗[A] QV.V)) :=
    Representation.prod (QU.scalarExtension K).ρ (QV.scalarExtension K).ρ
  rcases
      StableLattice.scalarExtension_exact_owner_fdrep_iso_local_support
        (A := A) (K := K) (G := G) (X := X) (L := L) with
    ⟨eLX⟩
  rcases
      stableLattice_exact_owner_scalarExtension_to_product_iso_local
        (A := A) (K := K) (G := G) X L QU QV hA with
    ⟨eProd⟩
  let eXProd : X ≅ FDRep.of ρprod := eLX.symm.trans eProd
  let eRep : Representation.Equiv X.ρ ρprod :=
    Representation.equivOfIso ((forget₂ (FDRep K G) (Rep K G)).mapIso eXProd)
  let _ : Representation.IsIrreducible X.ρ := FDRep.isIrreducible_of_simple X
  let _ : Representation.IsIrreducible ρprod :=
    isIrreducible_of_equiv_local (G := G) (ρ := X.ρ) (σ := ρprod) eRep
  have hU_sub : U.toSubmodule ≠ ⊥ := by
    intro hU_sub
    apply hU
    apply Subrepresentation.toSubmodule_injective
    simpa using hU_sub
  have hV_sub : V.toSubmodule ≠ ⊥ := by
    intro hV_sub
    apply hV
    apply Subrepresentation.toSubmodule_injective
    simpa using hV_sub
  let _ : Nontrivial (asModule U.toRepresentation) := by
    change Nontrivial U.toSubmodule
    exact Submodule.nontrivial_iff_ne_bot.mpr hU_sub
  let _ : Nontrivial (asModule V.toRepresentation) := by
    change Nontrivial V.toSubmodule
    exact Submodule.nontrivial_iff_ne_bot.mpr hV_sub
  have hQUred_nontrivial : Nontrivial (k ⊗[A] QU.V) := by
    -- The nonzero reduced factor transfers across the chosen exact-owner identification.
    obtain ⟨x, hx⟩ := exists_ne (0 : asModule U.toRepresentation)
    refine ⟨eQU.symm x, 0, ?_⟩
    intro hzero
    apply hx
    simpa using congrArg eQU hzero
  have hQVred_nontrivial : Nontrivial (k ⊗[A] QV.V) := by
    -- The same transfer works for the complementary reduced factor.
    obtain ⟨x, hx⟩ := exists_ne (0 : asModule V.toRepresentation)
    refine ⟨eQV.symm x, 0, ?_⟩
    intro hzero
    apply hx
    simpa using congrArg eQV hzero
  let _ : Module.Free A QU.V := FiniteProjectiveGroupAlgebraModule.free (A := A) (G := G) QU
  let _ : Module.Free A QV.V := FiniteProjectiveGroupAlgebraModule.free (A := A) (G := G) QV
  let _ : Nontrivial (K ⊗[A] QU.V) :=
    nontrivial_scalar_extension_of_nontrivial_reduction_factor_local
      (A := A) (K := K) (P := QU.V) hQUred_nontrivial
  let _ : Nontrivial (K ⊗[A] QV.V) :=
    nontrivial_scalar_extension_of_nontrivial_reduction_factor_local
      (A := A) (K := K) (P := QV.V) hQVred_nontrivial
  have hprod_not_irreducible : ¬ ρprod.IsIrreducible := by
    -- A genuine product of two nonzero factors cannot stay irreducible upstairs.
    simpa [ρprod] using
      (prod_representation_not_isIrreducible_of_nontrivial_local
        (G := G) (F := K) (ρ := (QU.scalarExtension K).ρ) (σ := (QV.scalarExtension K).ρ))
  exact hprod_not_irreducible inferInstance

/-- Helper for Proposition 15-15.5-1: a nontrivial complemented split of the reduction of a stable
lattice should contradict simplicity of the generic fiber. -/
private theorem stableLattice_reduction_split_reflects_generic_nonsimple_of_order_prime_to_p
    (hG : ¬ p ∣ Nat.card G)
    (X : FDRep K G) [Simple X]
    (L : StableLattice A X.ρ)
    (U V : Subrepresentation L.reductionRepresentation)
    (hUV : IsCompl U V) (hU : U ≠ ⊥) (hV : V ≠ ⊥) :
    False := by
  exact
    stableLattice_reduction_split_reflects_generic_nonsimple_of_order_prime_to_p_core
      (A := A) (K := K) (G := G) (p := p) hG X L U V hUV hU hV

/-- Helper for Proposition 15-15.5-1: under Maschke's prime-to-`p` hypothesis, every reduced
subrepresentation has a complementary reduced subrepresentation. -/
private theorem stableLattice_reduction_exists_isCompl_of_order_prime_to_p
    (hG : ¬ p ∣ Nat.card G)
    (X : FDRep K G)
    (L : StableLattice A X.ρ)
    (U : Subrepresentation L.reductionRepresentation) :
    ∃ V : Subrepresentation L.reductionRepresentation, IsCompl U V := by
  let _ : NeZero (Nat.card G : k) := NeZero.of_not_dvd k hG
  let _ : IsSemisimpleRepresentation L.reductionRepresentation := by
    infer_instance
  -- Maschke makes the reduced representation semisimple, so complements already exist downstairs.
  simpa using exists_isCompl U

/-- Helper for Proposition 15-15.5-1: if a complement of a reduced subrepresentation is zero, then
the original subrepresentation is all of the reduction. -/
private theorem subrepresentation_eq_top_of_isCompl_right_eq_bot
    {F : Type u} [Field F]
    {V : Type v} [AddCommGroup V] [Module F V]
    {ρ : Representation F G V}
    {U V' : Subrepresentation ρ}
    (hUV : IsCompl U V') (hV : V' = ⊥) :
    U = ⊤ := by
  rw [hV] at hUV
  -- Once the complementary summand vanishes, codisjointness forces the remaining summand to be
  -- the whole representation.
  simpa [codisjoint_iff] using hUV.codisjoint

/-- Helper for Proposition 15-15.5-1: the reduction of a stable lattice in a simple generic
representation is irreducible under the prime-to-`p` hypothesis. -/
private theorem stableLattice_reduction_isIrreducible_of_order_prime_to_p
    (hG : ¬ p ∣ Nat.card G)
    (X : FDRep K G) [Simple X]
    (L : StableLattice A X.ρ) :
    L.reductionRepresentation.IsIrreducible := by
  let _ : Representation.IsIrreducible X.ρ := FDRep.isIrreducible_of_simple X
  let _ : Nontrivial X.V := by
    by_contra hXV
    let _ : Subsingleton X.V := not_nontrivial_iff_subsingleton.mp hXV
    exact (show (⊥ : Subrepresentation X.ρ) ≠ ⊤ from IsSimpleOrder.bot_ne_top) <| by
      apply Subrepresentation.toSubmodule_injective
      ext x
      constructor
      · intro _
        trivial
      · intro _
        simpa using (show x = 0 from Subsingleton.elim x 0)
  let _ : Nontrivial L.reduction :=
    StableLattice.reduction_nontrivial_monoid (A := A) (K := K) L
  let _ : Nontrivial (Subrepresentation L.reductionRepresentation) :=
    ⟨⊥, ⊤, fun h ↦
      bot_ne_top <| by simpa using congrArg Subrepresentation.toSubmodule h⟩
  refine IsSimpleOrder.of_forall_eq_top fun U hU ↦ ?_
  obtain ⟨V, hUV⟩ :=
    stableLattice_reduction_exists_isCompl_of_order_prime_to_p
      (A := A) (K := K) (G := G) (p := p) hG X L U
  by_cases hV : V = ⊥
  · -- If the complement vanishes, the original subrepresentation is the whole reduction.
    exact subrepresentation_eq_top_of_isCompl_right_eq_bot hUV hV
  · -- Otherwise the nontrivial split contradicts the simplicity of the generic fiber.
    exact False.elim <|
      stableLattice_reduction_split_reflects_generic_nonsimple_of_order_prime_to_p
        (A := A) (K := K) (G := G) (p := p) hG X L U V hUV hU hV

private theorem stableLattice_reduction_simple_of_order_prime_to_p
    (hG : ¬ p ∣ Nat.card G)
    (X : FDRep K G) [Simple X]
    (L : StableLattice A X.ρ) :
    Simple (FDRep.of L.reductionRepresentation) := by
  letI : L.reductionRepresentation.IsIrreducible :=
    stableLattice_reduction_isIrreducible_of_order_prime_to_p
      (A := A) (K := K) (G := G) (p := p) hG X L
  letI : Representation.IsIrreducible (FDRep.of L.reductionRepresentation).ρ := by
    simpa using (inferInstance : L.reductionRepresentation.IsIrreducible)
  -- Once irreducibility of the reduced representation is isolated, the bundled `FDRep` simplicity
  -- statement is the standard Chapter `2` wrapper.
  exact FDRep.simple_of_isIrreducible (FDRep.of L.reductionRepresentation)

/-- Helper for Proposition 15-15.5-1: in a complete simple generic family, LinearRepresentations_Serre_1977's reduction
argument makes every chosen reduction simple. -/
private theorem stableLattice_reductionFamily_isSimple_of_order_prime_to_p
    {S : Type v}
    (hG : ¬ p ∣ Nat.card G)
    (πK : S → FDRep K G)
    (hπK_complete : IsCompleteIrreducibleFamily πK)
    (L : ∀ i, StableLattice A (πK i).ρ) :
    ∀ i, Simple (FDRep.of (L i).reductionRepresentation) := by
  intro i
  -- Each generic family member is simple by completeness, so the pointwise reduction lemma applies
  -- directly to LinearRepresentations_Serre_1977's chosen stable lattice in that member.
  letI : Simple (πK i) := hπK_complete.isSimple i
  exact
    stableLattice_reduction_simple_of_order_prime_to_p
      (A := A) (K := K) (G := G) (p := p) hG (πK i) (L i)

-- Proof sketch: when `p ∤ |G|`, both `K[G]` and `k[G]` are semisimple. Therefore a stable lattice
-- in a simple `K[G]`-module has simple reduction, nonisomorphic simples stay nonisomorphic after
-- reduction, and every simple `k[G]`-module occurs as the reduction of one of the chosen simple
-- `K[G]`-modules.
/-- Proposition 15-15.5-1 (3), pairwise-nonisomorphic component for the canonical reduced family. -/
-- TODO: deduce pairwise nonisomorphism by showing equal reduction classes force equal simple
-- `K[G]`-classes through the semisimple prime-to-`p` decomposition picture.
theorem stableLattice_reductionFamily_pairwiseNonisomorphic_of_order_prime_to_p
    {S : Type v}
    (hG : ¬ p ∣ Nat.card G)
    (πK : S → FDRep K G)
    (hπK_pairwise : PairwiseNonisomorphic πK)
    (hπK_complete : IsCompleteIrreducibleFamily πK)
    (L : ∀ i, StableLattice A (πK i).ρ) :
    let πk : S → FDRep k G := fun i ↦ FDRep.of (L i).reductionRepresentation
    PairwiseNonisomorphic πk := by
  -- Reflect any isomorphism between reductions back upstairs, then use the pairwise hypothesis
  -- on the original simple `K[G]`-family.
  exact
    stableLattice_reductionFamily_pairwise_of_iso_reflection
      (A := A) (K := K) (G := G) (S := S) πK hπK_pairwise L
      (fun {i j} hij ↦
        stableLattice_reduction_iso_implies_generic_iso_of_order_prime_to_p
          (A := A) (K := K) (G := G) (p := p) (S := S) hG πK L hij)

/-- Helper for Proposition 15-15.5-1: LinearRepresentations_Serre_1977's projective-envelope inverse map already proves the
existence clause for the reduced family attached to a complete simple `K[G]`-family. -/
-- Proof sketch: lift the simple `k[G]`-representation through a projective envelope over `A[G]`,
-- show the scalar extension of that lift is simple, then use completeness of `πK` and compare
-- Grothendieck classes via `decompositionHom`.
private theorem stableLattice_reductionFamily_exists_iso_of_order_prime_to_p
    {S : Type v}
    (hG : ¬ p ∣ Nat.card G)
    (πK : S → FDRep K G)
    (hπK_complete : IsCompleteIrreducibleFamily πK)
    (L : ∀ i, StableLattice A (πK i).ρ)
    {τ : FDRep k G} [Simple τ] :
    ∃ i, Nonempty (τ ≅ FDRep.of (L i).reductionRepresentation) := by
  classical
  let πk : S → FDRep k G := fun i ↦ FDRep.of (L i).reductionRepresentation
  letI : Representation.IsIrreducible τ.ρ := FDRep.isIrreducible_of_simple τ
  obtain ⟨Q, hQτ⟩ :=
    exists_projective_lift_reducing_to_simple_of_order_prime_to_p
      (A := A) (G := G) (p := p) hG τ
  have hQsimple : Simple (Q.scalarExtension K) :=
    projective_lift_scalarExtension_simple_of_order_prime_to_p
      (A := A) (K := K) (G := G) (p := p) hG τ Q hQτ
  letI : Simple (Q.scalarExtension K) := hQsimple
  letI : Representation.IsIrreducible (Q.scalarExtension K).ρ := by
    simpa using FDRep.isIrreducible_of_simple (Q.scalarExtension K)
  obtain ⟨i, hi⟩ :=
    IsCompleteIrreducibleFamily.exists_iso_of_representation
      (π := πK) hπK_complete (τ := (Q.scalarExtension K).ρ) inferInstance
  refine ⟨i, ?_⟩
  have hQiso : Nonempty (Q.scalarExtension K ≅ πK i) := by
    simpa using hi
  have hclassτ :
      [τ]₀ = decompositionHom A K G [Q.scalarExtension K]₀ := by
    -- LinearRepresentations_Serre_1977's projective-lift identity computes the reduction class of `Q` directly as `[τ]₀`.
    simpa using
      (decompositionHom_projective_scalarExtension_class_eq_iso_target_local
        (A := A) (K := K) (G := G) Q hQτ).symm
  have hclassi :
      decompositionHom A K G [Q.scalarExtension K]₀ = [πk i]₀ := by
    -- Completeness picks out one member of `πK`; its chosen lattice computes the same
    -- decomposition class as the lifted projective envelope.
    calc
      decompositionHom A K G [Q.scalarExtension K]₀ =
          decompositionHom A K G [πK i]₀ := by
            rw [finiteRepGrothendieckClass_eq_of_nonempty_iso (L := K) (G := G) hQiso]
      _ = [πk i]₀ := by
            simpa [πk] using
              decompositionHom_finiteRepClass_eq (A := A) (K := K) (G := G) (πK i) (L i)
  have hclass : [τ]₀ = [πk i]₀ := hclassτ.trans hclassi
  let _ : NeZero (Nat.card G : k) := NeZero.of_not_dvd k hG
  have hsemiτ : IsSemisimpleRepresentation τ.ρ := by
    infer_instance
  have hsemii : IsSemisimpleRepresentation (πk i).ρ := by
    infer_instance
  exact
    (finiteRepGrothendieckClass_eq_iff_nonempty_iso_of_isSemisimple hsemiτ hsemii).mp hclass

/-- Helper for Proposition 15-15.5-1: once the reductions `FDRep.of (L i).reductionRepresentation`
are known to be simple, LinearRepresentations_Serre_1977's projective-envelope inverse map already supplies the completeness
of the reduced family. -/
private theorem stableLattice_reductionFamily_complete_of_isSimple_of_order_prime_to_p
    {S : Type v}
    (hG : ¬ p ∣ Nat.card G)
    (πK : S → FDRep K G)
    (hπK_complete : IsCompleteIrreducibleFamily πK)
    (L : ∀ i, StableLattice A (πK i).ρ)
    (hsimple : ∀ i, Simple (FDRep.of (L i).reductionRepresentation)) :
    let πk : S → FDRep k G := fun i ↦ FDRep.of (L i).reductionRepresentation
    IsCompleteIrreducibleFamily πk := by
  classical
  let πk : S → FDRep k G := fun i ↦ FDRep.of (L i).reductionRepresentation
  refine
    { isSimple := ?_
      exists_iso := ?_ }
  · intro i
    simpa [πk] using hsimple i
  · intro τ hτ
    letI : Simple τ := hτ
    -- LinearRepresentations_Serre_1977's lifted-projective-envelope argument already provides the completeness clause.
    exact
      stableLattice_reductionFamily_exists_iso_of_order_prime_to_p
        (A := A) (K := K) (G := G) (p := p) hG πK hπK_complete L

/-- Proposition 15-15.5-1 (3), completeness component for the canonical reduced family. -/
-- TODO: start from a simple `k[G]`-representation, lift a projective envelope through `A[G]`,
-- scalar-extend to `K`, and identify its decomposition class with one of the chosen `πK i`.
theorem stableLattice_reductionFamily_isCompleteIrreducible_of_order_prime_to_p
    {S : Type v}
    (hG : ¬ p ∣ Nat.card G)
    (πK : S → FDRep K G)
    (hπK_complete : IsCompleteIrreducibleFamily πK)
    (L : ∀ i, StableLattice A (πK i).ρ) :
    let πk : S → FDRep k G := fun i ↦ FDRep.of (L i).reductionRepresentation
    IsCompleteIrreducibleFamily πk := by
  refine
    stableLattice_reductionFamily_complete_of_isSimple_of_order_prime_to_p
      (A := A) (K := K) (G := G) (p := p) hG πK hπK_complete L ?_
  -- Apply the new family-level simplicity package instead of rebuilding the pointwise reduction
  -- argument inside the completeness proof.
  exact
    stableLattice_reductionFamily_isSimple_of_order_prime_to_p
      (A := A) (K := K) (G := G) (p := p) hG πK hπK_complete L

/-- Proposition 15-15.5-1 (3): source-facing form of part (ii). If `p ∤ |G|` and `πK` is a
complete family of pairwise nonisomorphic simple `K[G]`-representations, then the reductions of
stable lattices in the `πK i` again form a complete family of pairwise nonisomorphic simple
`k[G]`-representations. In the project API this is recorded by the reduced `FDRep` family
`fun i ↦ FDRep.of (L i).reductionRepresentation` together with the owner predicates
`PairwiseNonisomorphic` and `IsCompleteIrreducibleFamily`. -/
theorem stableLattice_reductions_form_complete_simple_family_of_order_prime_to_p
    {S : Type v}
    (hG : ¬ p ∣ Nat.card G)
    (πK : S → FDRep K G)
    (hπK_pairwise : PairwiseNonisomorphic πK)
    (hπK_complete : IsCompleteIrreducibleFamily πK)
    (L : ∀ i, StableLattice A (πK i).ρ) :
    let πk : S → FDRep k G := fun i ↦ FDRep.of (L i).reductionRepresentation
    PairwiseNonisomorphic πk ∧ IsCompleteIrreducibleFamily πk := by
  refine ⟨?_, ?_⟩
  · exact
      stableLattice_reductionFamily_pairwiseNonisomorphic_of_order_prime_to_p
        (A := A) (K := K) (G := G) (p := p) (S := S)
        hG πK hπK_pairwise hπK_complete L
  · exact
      stableLattice_reductionFamily_isCompleteIrreducible_of_order_prime_to_p
        (A := A) (K := K) (G := G) (p := p) (S := S)
        hG πK hπK_complete L

end DecompositionHom

section CartanMatrix

variable {p : ℕ}
variable {k : Type u} [Field k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]

/-- Helper for Proposition 15-15.5-1: once `p ∤ |G|`, the source of a projective envelope of a
finite-dimensional `k[G]`-representation has the same Grothendieck class as its target, because
Maschke makes the target itself projective. -/
theorem projectiveEnvelope_finiteRepClass_eq_target_of_order_prime_to_p
    (hG : ¬ p ∣ Nat.card G)
    {π : FDRep k G}
    {P : FiniteProjectiveGroupAlgebraModule k G}
    {f : P.V →ₗ[k[G]] asModule π.ρ}
    (hf : f.IsProjectiveEnvelope) :
    [P.toFiniteRep]₀ = [π]₀ := by
  let M : ModuleCat k[G] :=
    Rep.toModuleMonoidAlgebra.obj ((forget₂ (FDRep k G) (Rep k G)).obj π)
  let _ : Module.Projective k[G] M :=
    groupAlgebra_module_projective_of_order_prime_to_p (k := k) (G := G) (M := M) hG
  let f' : P.V →ₗ[k[G]] M := by
    -- Repackage the target representation in its canonical `ModuleCat` owner.
    simpa using f
  have hf' : f'.IsProjectiveEnvelope := by
    -- The envelope structure survives that definitional rebundling unchanged.
    simpa [f'] using hf
  obtain ⟨eLin⟩ := hf'.nonempty_linearEquiv_target
  let eRep' : P.toRep ≅ ((forget₂ (FDRep k G) (Rep k G)).obj π) :=
    Rep.ofModuleMonoidAlgebra.mapIso eLin.toModuleIso ≪≫
      (Rep.unitIso ((forget₂ (FDRep k G) (Rep k G)).obj π)).symm
  let eRep : ((forget₂ (FDRep k G) (Rep k G)).obj P.toFiniteRep) ≅
      ((forget₂ (FDRep k G) (Rep k G)).obj π) := by
    -- Forgetting `P.toFiniteRep` returns the same `Rep` owner as `P.toRep`.
    simpa [FiniteProjectiveGroupAlgebraModule.toFiniteRep,
      FiniteProjectiveGroupAlgebraModule.toRep] using eRep'
  let e : P.toFiniteRep ≅ π :=
    ⟨(FDRep.forget₂HomLinearEquiv P.toFiniteRep π) eRep.hom,
      (FDRep.forget₂HomLinearEquiv π P.toFiniteRep) eRep.inv,
      by
        apply (forget₂ (FDRep k G) (Rep k G)).map_injective
        change eRep.hom ≫ eRep.inv = 𝟙 _
        exact eRep.hom_inv_id,
      by
        apply (forget₂ (FDRep k G) (Rep k G)).map_injective
        change eRep.inv ≫ eRep.hom = 𝟙 _
        exact eRep.inv_hom_id⟩
  -- Grothendieck classes agree across the recovered `FDRep` isomorphism.
  exact finiteRepGrothendieckClass_eq_of_nonempty_iso (L := k) (G := G) ⟨e⟩

-- Proof sketch: under the bijection of part `(ii)`, the simple classes and the projective-envelope
-- classes define the same distinguished basis. The projective-envelope basis is derived from the
-- canonical projective-envelope construction, so it should
-- not be primitive input data.
/-- Proposition 15-15.5-1 (4): if `p ∤ |G|`, then the canonical projective-envelope basis of
`P_k(G)` attached to a complete simple family has identity Cartan matrix against the corresponding
canonical simple-class basis of `R_k(G)`. -/
-- TODO: evaluate the Cartan matrix on basis vectors, use `cartanHom_projectiveClass_eq`, and then
-- identify each projective envelope source with its simple target via projectivity from part `(i)`.
theorem cartanMatrix_eq_one_of_order_prime_to_p
    {S : Type v} [Fintype S]
    (hG : ¬ p ∣ Nat.card G)
    (π : S → FDRep k G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (P : S → FiniteProjectiveGroupAlgebraModule k G)
    (hP_envelope :
      ∀ i, ∃ f : (P i).V →ₗ[k[G]] asModule (π i).ρ, f.IsProjectiveEnvelope) :
    let bP :=
      projectiveEnvelope_classes_basis_of_complete_family
        π hπ_pairwise hπ_complete P hP_envelope
    let b :=
      simple_finiteRep_classes_basis_of_complete_family
        π hπ_pairwise hπ_complete
    cartanMatrix k G bP b = b.toMatrix b := by
  classical
  have himages :
      (fun i ↦
        cartanHom k G
          (projectiveEnvelope_classes_basis_of_complete_family
            π hπ_pairwise hπ_complete P hP_envelope i)) =
        simple_finiteRep_classes_basis_of_complete_family π hπ_pairwise hπ_complete := by
    funext i
    -- On each projective-envelope basis vector, the Cartan map lands on the matching simple
    -- class.
    rcases hP_envelope i with ⟨f, hf⟩
    rw [projectiveEnvelope_classes_basis_of_complete_family_apply]
    rw [simple_finiteRep_classes_basis_of_complete_family_apply]
    simp [cartanHom_projectiveClass_eq,
      projectiveEnvelope_finiteRepClass_eq_target_of_order_prime_to_p hG hf]
  ext i j
  rw [cartanMatrix, LinearMap.toMatrix_apply, Module.Basis.toMatrix_apply]
  exact
    congrArg
      (fun x ↦
        ((simple_finiteRep_classes_basis_of_complete_family
          π hπ_pairwise hπ_complete).repr x) i)
      (congrFun himages j)

end CartanMatrix

section MatrixIdentities

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [HenselianLocalRing A]
variable [CharP (IsLocalRing.ResidueField A) p]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]

local notation "k" => IsLocalRing.ResidueField A
local notation:max "P_k(" G ")" => finiteProjectiveGroupAlgebraGrothendieckGroup k G
local notation:max "P_A(" G ")" => finiteProjectiveGroupAlgebraGrothendieckGroup A G
local notation:max "R_K(" G ")" => finiteRepGrothendieckGroup K G
local notation:max "R_k(" G ")" => finiteRepGrothendieckGroup k G

/-- Helper for Proposition 15-15.5-1: the reduced simple family attached to the chosen lattices. -/
private noncomputable abbrev reduction_family_of_order_prime_to_p_local
    {S : Type v}
    (πK : S → FDRep K G)
    (L : ∀ i : S, StableLattice A (πK i).ρ) :
    S → FDRep k G :=
  fun i ↦ FDRep.of (L i).reductionRepresentation

/-- Helper for Proposition 15-15.5-1: Maschke's hypothesis makes the reduced lattice family
pairwise nonisomorphic. -/
private abbrev reduction_family_pairwise_nonisomorphic_of_order_prime_to_p_local
    {S : Type v}
    (hG : ¬ p ∣ Nat.card G)
    (πK : S → FDRep K G)
    (hπK_pairwise : PairwiseNonisomorphic πK)
    (hπK_complete : IsCompleteIrreducibleFamily πK)
    (L : ∀ i, StableLattice A (πK i).ρ) :
    PairwiseNonisomorphic
      (reduction_family_of_order_prime_to_p_local
        (A := A) (K := K) (G := G) πK L) :=
  stableLattice_reductionFamily_pairwiseNonisomorphic_of_order_prime_to_p
    (A := A) (K := K) (G := G) (p := p)
    hG πK hπK_pairwise hπK_complete L

/-- Helper for Proposition 15-15.5-1: Maschke's hypothesis makes the reduced lattice family a
complete irreducible family. -/
private abbrev reduction_family_complete_irreducible_of_order_prime_to_p_local
    {S : Type v}
    (hG : ¬ p ∣ Nat.card G)
    (πK : S → FDRep K G)
    (hπK_complete : IsCompleteIrreducibleFamily πK)
    (L : ∀ i, StableLattice A (πK i).ρ) :
    IsCompleteIrreducibleFamily
      (reduction_family_of_order_prime_to_p_local
        (A := A) (K := K) (G := G) πK L) :=
  stableLattice_reductionFamily_isCompleteIrreducible_of_order_prime_to_p
    (A := A) (K := K) (G := G) (p := p)
    hG πK hπK_complete L

/-- Helper for Proposition 15-15.5-1: the canonical simple-class basis over `K` for the chosen
generic simple family. -/
private noncomputable abbrev generic_simple_basis_of_order_prime_to_p_local
    {S : Type v}
    (πK : S → FDRep K G)
    (hπK_pairwise : PairwiseNonisomorphic πK)
    (hπK_complete : IsCompleteIrreducibleFamily πK) :
    Module.Basis S ℤ (R_K(G)) :=
  simple_finiteRep_classes_basis_of_complete_family
    πK hπK_pairwise hπK_complete

/-- Helper for Proposition 15-15.5-1: the canonical simple-class basis over `k` for the reduced
lattice family. -/
private noncomputable abbrev reduced_simple_basis_of_order_prime_to_p_local
    {S : Type v}
    (hG : ¬ p ∣ Nat.card G)
    (πK : S → FDRep K G)
    (hπK_pairwise : PairwiseNonisomorphic πK)
    (hπK_complete : IsCompleteIrreducibleFamily πK)
    (L : ∀ i, StableLattice A (πK i).ρ) :
    Module.Basis S ℤ (R_k(G)) :=
  simple_finiteRep_classes_basis_of_complete_family
    (reduction_family_of_order_prime_to_p_local (A := A) (K := K) (G := G) πK L)
    (reduction_family_pairwise_nonisomorphic_of_order_prime_to_p_local
      (A := A) (K := K) (G := G) (p := p)
      hG πK hπK_pairwise hπK_complete L)
    (reduction_family_complete_irreducible_of_order_prime_to_p_local
      (A := A) (K := K) (G := G) (p := p)
      hG πK hπK_complete L)

/-- Helper for Proposition 15-15.5-1: the canonical projective-envelope basis over `k` attached to
the reduced lattice family. -/
private noncomputable abbrev projective_envelope_basis_of_order_prime_to_p_local
    {S : Type v}
    (hG : ¬ p ∣ Nat.card G)
    (πK : S → FDRep K G)
    (hπK_pairwise : PairwiseNonisomorphic πK)
    (hπK_complete : IsCompleteIrreducibleFamily πK)
    (L : ∀ i, StableLattice A (πK i).ρ)
    (P : S → FiniteProjectiveGroupAlgebraModule k G)
    (hP_envelope :
      ∀ i,
        ∃ f : (P i).V →ₗ[k[G]]
          asModule (L i).reductionRepresentation,
          f.IsProjectiveEnvelope) :
    Module.Basis S ℤ (P_k(G)) :=
  projectiveEnvelope_classes_basis_of_complete_family
    (reduction_family_of_order_prime_to_p_local (A := A) (K := K) (G := G) πK L)
    (reduction_family_pairwise_nonisomorphic_of_order_prime_to_p_local
      (A := A) (K := K) (G := G) (p := p)
      hG πK hπK_pairwise hπK_complete L)
    (reduction_family_complete_irreducible_of_order_prime_to_p_local
      (A := A) (K := K) (G := G) (p := p)
      hG πK hπK_complete L)
    P hP_envelope

/-- Helper for Proposition 15-15.5-1: once the reduced family is complete and pairwise
nonisomorphic, the basis-built map `bk.constr ℤ bK` is a left inverse to `decompositionHom`. -/
private theorem decomposition_basis_leftInverse_of_order_prime_to_p_local
    {S : Type v}
    (hG : ¬ p ∣ Nat.card G)
    (πK : S → FDRep K G)
    (hπK_pairwise : PairwiseNonisomorphic πK)
    (hπK_complete : IsCompleteIrreducibleFamily πK)
    (L : ∀ i, StableLattice A (πK i).ρ) :
    ((reduced_simple_basis_of_order_prime_to_p_local
        (A := A) (K := K) (G := G) (p := p)
        hG πK hπK_pairwise hπK_complete L).constr ℤ
      (generic_simple_basis_of_order_prime_to_p_local
        (G := G) πK hπK_pairwise hπK_complete)).comp
      (decompositionHom A K G).toIntLinearMap = LinearMap.id := by
  let bK : Module.Basis S ℤ (R_K(G)) :=
    generic_simple_basis_of_order_prime_to_p_local
      (G := G) πK hπK_pairwise hπK_complete
  let bk : Module.Basis S ℤ (R_k(G)) :=
    reduced_simple_basis_of_order_prime_to_p_local
      (A := A) (K := K) (G := G) (p := p)
      hG πK hπK_pairwise hπK_complete L
  -- Evaluate `decompositionHom` on the `K`-simple basis and package the resulting basis images.
  apply bK.ext
  intro i
  have hi :
      (decompositionHom A K G).toIntLinearMap (bK i) = bk i := by
    rw [simple_finiteRep_classes_basis_of_complete_family_apply,
      simple_finiteRep_classes_basis_of_complete_family_apply]
    simpa [reduction_family_of_order_prime_to_p_local] using
      decompositionHom_finiteRepClass_eq (A := A) (K := K) (G := G) (πK i) (L i)
  calc
    ((bk.constr ℤ bK).comp (decompositionHom A K G).toIntLinearMap) (bK i) =
        (bk.constr ℤ bK) ((decompositionHom A K G).toIntLinearMap (bK i)) := by
          simp [LinearMap.comp_apply]
    _ = (bk.constr ℤ bK) (bk i) := by
          rw [hi]
    _ = bK i := by
          simp

-- Proof sketch: part `(3)` shows that the reductions of the chosen lattices form a complete
-- simple family over `k`, so Proposition `14-14.1-1` already supplies the canonical basis owner
-- on `R_k(G)`. The owner `decompositionHom A K G` sends the basis vector `i` in `R_K(G)` to the
-- same
-- indexed reduced simple class, so its matrix in the two canonical simple-class bases is the
-- identity.
/-- Proposition 15-15.5-1 (5): source-facing decomposition-matrix form. If `p ∤ |G|`, then for a
complete family of simple `K[G]`-modules with chosen stable lattices, the canonical simple-class
basis on the reduced family identifies `decompositionHom A K G : R_K(G) → R_k(G)` with the identity
matrix. -/
-- TODO: once the reduced family is proved complete and pairwise nonisomorphic, evaluate each
-- simple-class basis vector under `decompositionHom` and simplify with
-- `decompositionHom_finiteRepClass_eq`.
theorem decompositionHom_toMatrix_eq_one_of_order_prime_to_p
    {S : Type v}
    (hG : ¬ p ∣ Nat.card G)
    (πK : S → FDRep K G)
    (hπK_pairwise : PairwiseNonisomorphic πK)
    (hπK_complete : IsCompleteIrreducibleFamily πK)
    (L : ∀ i, StableLattice A (πK i).ρ) :
    let πk : S → FDRep k G := fun i ↦ FDRep.of (L i).reductionRepresentation
    let hπk_pairwise :=
      stableLattice_reductionFamily_pairwiseNonisomorphic_of_order_prime_to_p
        hG πK hπK_pairwise hπK_complete L
    let hπk_complete :=
      stableLattice_reductionFamily_isCompleteIrreducible_of_order_prime_to_p
        hG πK hπK_complete L
    let bK :=
      simple_finiteRep_classes_basis_of_complete_family
        πK hπK_pairwise hπK_complete
    let bk :=
      simple_finiteRep_classes_basis_of_complete_family
        πk hπk_pairwise hπk_complete
    bk.toMatrix (fun i ↦ (decompositionHom A K G).toIntLinearMap (bK i)) =
      bk.toMatrix bk := by
  let hπk_pairwise :
      PairwiseNonisomorphic (fun i : S ↦ FDRep.of (L i).reductionRepresentation) :=
    stableLattice_reductionFamily_pairwiseNonisomorphic_of_order_prime_to_p
      (A := A) (K := K) (G := G) (p := p)
      hG πK hπK_pairwise hπK_complete L
  let hπk_complete :
      IsCompleteIrreducibleFamily (fun i : S ↦ FDRep.of (L i).reductionRepresentation) :=
    stableLattice_reductionFamily_isCompleteIrreducible_of_order_prime_to_p
      (A := A) (K := K) (G := G) (p := p)
      hG πK hπK_complete L
  let bK : Module.Basis S ℤ (R_K(G)) :=
    simple_finiteRep_classes_basis_of_complete_family
      πK hπK_pairwise hπK_complete
  let bk : Module.Basis S ℤ (R_k(G)) :=
    simple_finiteRep_classes_basis_of_complete_family
      (fun i : S ↦ FDRep.of (L i).reductionRepresentation) hπk_pairwise hπk_complete
  have himages :
      (fun i ↦ (decompositionHom A K G).toIntLinearMap (bK i)) = bk := by
    funext i
    rw [simple_finiteRep_classes_basis_of_complete_family_apply,
      simple_finiteRep_classes_basis_of_complete_family_apply]
    -- The chosen lattice `L i` is exactly the reduction datum used to define the `i`-th basis
    -- vector on the residue-field side.
    simpa using
      decompositionHom_finiteRepClass_eq
        (A := A) (K := K) (G := G) (πK i) (L i)
  exact congrArg (fun g ↦ bk.toMatrix g) himages

-- Proof sketch: in the `cde` triangle, once both `c` and `decompositionHom A K G` are identity
-- matrices in the simple bases from part `(ii)`, the matrix of
-- `projectiveGrothendieckScalarExtensionHom A K` is also the identity.
-- Proposition 15-15.5-1 (6): if `p ∤ |G|`, then LinearRepresentations_Serre_1977's scalar-extension homomorphism is
-- represented by the identity matrix between the canonical projective-envelope basis of `P_k(G)`
-- attached to the canonical reduced family and the corresponding complete simple-class basis of
-- `R_K(G)`. Concretely, this is the canonical owner
-- `projectiveGrothendieckScalarExtensionHom A K`.
-- TODO: combine the Cartan identity with the decomposition identity, using the
-- `projectiveGrothendieckReductionEquiv` transport and the projective-class bridge
-- `projectiveGrothendieckScalarExtensionHom_apply`.
/-- Helper for Proposition 15-15.5-1: LinearRepresentations_Serre_1977's scalar-extension homomorphism satisfies
`d (e x) = c x` on projective Grothendieck classes over the residue field. -/
private theorem decompositionHom_projectiveGrothendieckBaseChange_eq_cartan_reduction_local
    (x : P_A(G)) :
    decompositionHom A K G ((projectiveGrothendieckBaseChangeHom K) x) =
      cartanHom k G ((projectiveGrothendieckReductionEquiv (A := A) (G := G)) x) := by
  refine QuotientAddGroup.induction_on x ?_
  intro a
  refine FreeAbelianGroup.induction_on a ?_ ?_ ?_ ?_
  · simp
  · intro Q
    have hred :
        projectiveGrothendieckReductionEquiv (A := A) (G := G) [Q]ₚ₀ =
          [Q.residueFieldReduction]ₚ₀ := by
      change
        projectiveGrothendieckReductionHom (A := A) (G := G) [Q]ₚ₀ =
          [Q.residueFieldReduction]ₚ₀
      simpa using
        projectiveGrothendieckReductionHom_projectiveClass_eq (A := A) (G := G) Q
    calc
      decompositionHom A K G ((projectiveGrothendieckBaseChangeHom K) [Q]ₚ₀) =
          decompositionHom A K G [Q.scalarExtension K]₀ := by
            rw [projectiveGrothendieckBaseChangeHom_projectiveClass_eq]
      _ = cartanHom k G [Q.residueFieldReduction]ₚ₀ := by
            exact
              decompositionHom_projective_scalarExtension_class_eq_residueFieldReduction_class
                (A := A) (K := K) (G := G) Q
      _ = cartanHom k G ((projectiveGrothendieckReductionEquiv (A := A) (G := G)) [Q]ₚ₀) := by
            rw [hred]
  · intro a ha
    simpa using congrArg Neg.neg ha
  · intro a b ha hb
    simpa [map_add] using congrArg₂ (fun x y ↦ x + y) ha hb

/-- Helper for Proposition 15-15.5-1: LinearRepresentations_Serre_1977's scalar-extension homomorphism satisfies
`d (e x) = c x` on projective Grothendieck classes over the residue field. -/
private theorem decompositionHom_comp_projectiveGrothendieckScalarExtensionHom_eq_cartanHom
    (x : P_k(G)) :
    decompositionHom A K G
      ((projectiveGrothendieckScalarExtensionHom (A := A) (K := K) (G := G)) x) =
      cartanHom k G x := by
  let y : P_A(G) := (projectiveGrothendieckReductionEquiv (A := A) (G := G)).symm x
  -- Transport to `P_A(G)`, evaluate the triangle on that projective class, and then rewrite back.
  calc
    decompositionHom A K G
        ((projectiveGrothendieckScalarExtensionHom (A := A) (K := K) (G := G)) x) =
      decompositionHom A K G ((projectiveGrothendieckBaseChangeHom K) y) := by
        simp [projectiveGrothendieckScalarExtensionHom_apply, y]
    _ =
        cartanHom k G ((projectiveGrothendieckReductionEquiv (A := A) (G := G)) y) := by
          exact
            decompositionHom_projectiveGrothendieckBaseChange_eq_cartan_reduction_local
              (A := A) (K := K) (G := G) y
    _ = cartanHom k G x := by
          simp [y]

/-- Helper for Proposition 15-15.5-1: the Cartan map sends each projective-envelope basis vector
to the matching reduced simple-class basis vector. -/
private theorem cartanHom_projective_envelope_class_eq_reduction_target_local
    {S : Type v}
    (hG : ¬ p ∣ Nat.card G)
    (πK : S → FDRep K G)
    (L : ∀ i, StableLattice A (πK i).ρ)
    (P : S → FiniteProjectiveGroupAlgebraModule k G)
    (hP_envelope :
      ∀ i,
        ∃ f : (P i).V →ₗ[k[G]]
          asModule (L i).reductionRepresentation,
          f.IsProjectiveEnvelope)
    (i : S) :
    cartanHom k G [P i]ₚ₀ = [FDRep.of (L i).reductionRepresentation]₀ := by
  rcases hP_envelope i with ⟨f, hf⟩
  -- Compute the Cartan class of the projective envelope source and then identify that source with
  -- the reduced simple target by Maschke's theorem.
  calc
    cartanHom k G [P i]ₚ₀ = [(P i).toFiniteRep]₀ := by
      simpa using (cartanHom_projectiveClass_eq k G (P i))
    _ = [FDRep.of (L i).reductionRepresentation]₀ := by
      simpa using
        (projectiveEnvelope_finiteRepClass_eq_target_of_order_prime_to_p hG hf)

/-- Helper for Proposition 15-15.5-1: the Cartan map sends each projective-envelope basis vector
to the matching reduced simple-class basis vector. -/
private theorem cartanHom_projectiveEnvelope_basis_eq_reduced_simple_basis_local
    {S : Type v}
    (hG : ¬ p ∣ Nat.card G)
    (πK : S → FDRep K G)
    (hπK_pairwise : PairwiseNonisomorphic πK)
    (hπK_complete : IsCompleteIrreducibleFamily πK)
    (L : ∀ i, StableLattice A (πK i).ρ)
    (P : S → FiniteProjectiveGroupAlgebraModule k G)
    (hP_envelope :
      ∀ i,
        ∃ f : (P i).V →ₗ[k[G]]
          asModule (L i).reductionRepresentation,
          f.IsProjectiveEnvelope) :
    ∀ i,
      cartanHom k G
          ((projective_envelope_basis_of_order_prime_to_p_local
              (A := A) (K := K) (G := G) (p := p)
              hG πK hπK_pairwise hπK_complete L P hP_envelope) i) =
        (reduced_simple_basis_of_order_prime_to_p_local
          (A := A) (K := K) (G := G) (p := p)
          hG πK hπK_pairwise hπK_complete L) i := by
  let bP : Module.Basis S ℤ (P_k(G)) :=
    projective_envelope_basis_of_order_prime_to_p_local
      (A := A) (K := K) (G := G) (p := p)
      hG πK hπK_pairwise hπK_complete L P hP_envelope
  let bk : Module.Basis S ℤ (R_k(G)) :=
    reduced_simple_basis_of_order_prime_to_p_local
      (A := A) (K := K) (G := G) (p := p)
      hG πK hπK_pairwise hπK_complete L
  intro i
  -- Rewrite both basis vectors to their defining classes and then invoke the class-level Cartan
  -- computation for the chosen projective envelope.
  calc
    cartanHom k G (bP i) = cartanHom k G [P i]ₚ₀ := by
      rw [projectiveEnvelope_classes_basis_of_complete_family_apply]
    _ = [FDRep.of (L i).reductionRepresentation]₀ := by
      exact
        cartanHom_projective_envelope_class_eq_reduction_target_local
          (A := A) (K := K) (G := G) (p := p) hG πK L P hP_envelope i
    _ = bk i := by
      rw [simple_finiteRep_classes_basis_of_complete_family_apply]

/-- Helper for Proposition 15-15.5-1: evaluating LinearRepresentations_Serre_1977's `d ∘ e = c` triangle on the chosen
projective-envelope basis yields the reduced simple basis. -/
private theorem projectiveScalarExtension_triangle_on_projectiveEnvelope_basis_local
    {S : Type v}
    (bP : Module.Basis S ℤ (P_k(G)))
    (bk : Module.Basis S ℤ (R_k(G)))
    (hcartan_basis : ∀ i, cartanHom k G (bP i) = bk i) :
    ∀ i,
      (decompositionHom A K G).toIntLinearMap
          ((projectiveGrothendieckScalarExtensionHom (A := A) (K := K) (G := G)).toIntLinearMap
            (bP i)) =
        bk i := by
  intro i
  -- Compute `d (e (bP i))` through LinearRepresentations_Serre_1977's triangle, then rewrite the Cartan image on the basis.
  calc
    (decompositionHom A K G).toIntLinearMap
        ((projectiveGrothendieckScalarExtensionHom (A := A) (K := K) (G := G)).toIntLinearMap
          (bP i))
        = cartanHom k G (bP i) := by
            simpa using
              decompositionHom_comp_projectiveGrothendieckScalarExtensionHom_eq_cartanHom
                (A := A) (K := K) (G := G) (bP i)
    _ = bk i := by
          exact hcartan_basis i

/-- Helper for Proposition 15-15.5-1: evaluating a left inverse at a point recovers that point. -/
private theorem linearMap_eq_of_comp_eq_id_apply_local_support
    {M : Type u} [AddCommGroup M] [Module ℤ M]
    {N : Type u} [AddCommGroup N] [Module ℤ N]
    (s : N →ₗ[ℤ] M)
    (f : M →ₗ[ℤ] N)
    (h : s.comp f = (LinearMap.id : M →ₗ[ℤ] M))
    (x : M) :
    s (f x) = x := by
  -- Evaluate the equality `s.comp f = id` at `x`.
  exact congrArg (fun g : M →ₗ[ℤ] M ↦ g x) h

/-- Helper for Proposition 15-15.5-1: a left inverse identifies any element mapping to the `i`-th
reduced basis vector with the corresponding `K`-basis vector. -/
private theorem basis_image_of_left_inverse_and_basis_value_local_support
    {S : Type v}
    (bK : Module.Basis S ℤ (R_K(G)))
    (bk : Module.Basis S ℤ (R_k(G)))
    (d : R_K(G) →ₗ[ℤ] R_k(G))
    (x : R_K(G))
    (i : S)
    (hleftInv : (bk.constr ℤ bK).comp d = (LinearMap.id : R_K(G) →ₗ[ℤ] R_K(G)))
    (hx : d x = bk i) :
    x = bK i := by
  let s : R_k(G) →ₗ[ℤ] R_K(G) := bk.constr ℤ bK
  calc
    x = s (d x) := by
      symm
      exact linearMap_eq_of_comp_eq_id_apply_local_support s d hleftInv x
    _ = s (bk i) := by
      rw [hx]
    _ = bK i := by
      simp [s]

/-- Helper for Proposition 15-15.5-1: scalar extension sends each projective-envelope basis vector
to the matching `K`-simple basis vector. -/
private theorem projectiveScalarExtension_basis_image_of_order_prime_to_p_local
    {S : Type v}
    (hG : ¬ p ∣ Nat.card G)
    (πK : S → FDRep K G)
    (hπK_pairwise : PairwiseNonisomorphic πK)
    (hπK_complete : IsCompleteIrreducibleFamily πK)
    (L : ∀ i, StableLattice A (πK i).ρ)
    (P : S → FiniteProjectiveGroupAlgebraModule k G)
    (hP_envelope :
      ∀ i,
        ∃ f : (P i).V →ₗ[k[G]]
          asModule (L i).reductionRepresentation,
          f.IsProjectiveEnvelope) :
    ∀ i,
      (projectiveGrothendieckScalarExtensionHom (A := A) (K := K) (G := G)).toIntLinearMap
          ((projective_envelope_basis_of_order_prime_to_p_local
              (A := A) (K := K) (G := G) (p := p)
              hG πK hπK_pairwise hπK_complete L P hP_envelope) i) =
        (generic_simple_basis_of_order_prime_to_p_local
          (G := G) πK hπK_pairwise hπK_complete) i := by
  -- Route correction: keep LinearRepresentations_Serre_1977's `d ∘ e = c` proof, but split the old hotspot into separate
  -- triangle and left-inverse helpers so Lean no longer elaborates one large declaration.
  let bP : Module.Basis S ℤ (P_k(G)) :=
    projective_envelope_basis_of_order_prime_to_p_local
      (A := A) (K := K) (G := G) (p := p)
      hG πK hπK_pairwise hπK_complete L P hP_envelope
  let bK : Module.Basis S ℤ (R_K(G)) :=
    generic_simple_basis_of_order_prime_to_p_local
      (G := G) πK hπK_pairwise hπK_complete
  let bk : Module.Basis S ℤ (R_k(G)) :=
    reduced_simple_basis_of_order_prime_to_p_local
      (A := A) (K := K) (G := G) (p := p)
      hG πK hπK_pairwise hπK_complete L
  have hleftInv :
      (bk.constr ℤ bK).comp (decompositionHom A K G).toIntLinearMap = LinearMap.id := by
    -- The reduced simple basis already gives a left inverse to the decomposition map.
    simpa [bK, bk] using
      decomposition_basis_leftInverse_of_order_prime_to_p_local
        (A := A) (K := K) (G := G) (p := p)
        hG πK hπK_pairwise hπK_complete L
  have hcartan_basis : ∀ i, cartanHom k G (bP i) = bk i := by
    -- Reuse the basis-level Cartan computation instead of re-expanding the same basis rewrites
    -- inside the scalar-extension triangle argument.
    simpa [bP, bk] using
      cartanHom_projectiveEnvelope_basis_eq_reduced_simple_basis_local
        (A := A) (K := K) (G := G) (p := p)
        hG πK hπK_pairwise hπK_complete L P hP_envelope
  have htriangle_basis :
      ∀ i,
        (decompositionHom A K G).toIntLinearMap
            ((projectiveGrothendieckScalarExtensionHom (A := A) (K := K) (G := G)).toIntLinearMap
              (bP i)) =
          bk i := by
    -- Evaluate LinearRepresentations_Serre_1977's `d ∘ e = c` triangle on the chosen projective-envelope basis.
    exact
      projectiveScalarExtension_triangle_on_projectiveEnvelope_basis_local
        (A := A) (K := K) (G := G) bP bk hcartan_basis
  intro i
  -- The decomposition left inverse identifies the unique preimage of `bk i` with `bK i`.
  exact
    basis_image_of_left_inverse_and_basis_value_local_support
      bK bk
      (decompositionHom A K G).toIntLinearMap
      ((projectiveGrothendieckScalarExtensionHom (A := A) (K := K) (G := G)).toIntLinearMap
        (bP i))
      i hleftInv (htriangle_basis i)

theorem projectiveScalarExtension_toMatrix_eq_one_of_order_prime_to_p
    {S : Type v}
    (hG : ¬ p ∣ Nat.card G)
    (πK : S → FDRep K G)
    (hπK_pairwise : PairwiseNonisomorphic πK)
    (hπK_complete : IsCompleteIrreducibleFamily πK)
    (L : ∀ i, StableLattice A (πK i).ρ)
    (P : S → FiniteProjectiveGroupAlgebraModule k G)
    (hP_envelope :
      ∀ i,
        ∃ f : (P i).V →ₗ[k[G]]
          asModule (L i).reductionRepresentation,
          f.IsProjectiveEnvelope) :
    let πk : S → FDRep k G := fun i ↦ FDRep.of (L i).reductionRepresentation
    let hπk_pairwise :=
      stableLattice_reductionFamily_pairwiseNonisomorphic_of_order_prime_to_p
        hG πK hπK_pairwise hπK_complete L
    let hπk_complete :=
      stableLattice_reductionFamily_isCompleteIrreducible_of_order_prime_to_p
        hG πK hπK_complete L
    let bP :=
      projectiveEnvelope_classes_basis_of_complete_family
        πk hπk_pairwise hπk_complete
        P hP_envelope
    let bK :=
      simple_finiteRep_classes_basis_of_complete_family
        πK hπK_pairwise hπK_complete
    bK.toMatrix
      (fun i ↦
        (projectiveGrothendieckScalarExtensionHom (A := A) (K := K) (G := G)).toIntLinearMap
          (bP i)) =
      bK.toMatrix bK := by
  let πk : S → FDRep k G := fun i ↦ FDRep.of (L i).reductionRepresentation
  let hπk_pairwise : PairwiseNonisomorphic πk :=
    stableLattice_reductionFamily_pairwiseNonisomorphic_of_order_prime_to_p
      (A := A) (K := K) (G := G) (p := p)
      hG πK hπK_pairwise hπK_complete L
  let hπk_complete : IsCompleteIrreducibleFamily πk :=
    stableLattice_reductionFamily_isCompleteIrreducible_of_order_prime_to_p
      (A := A) (K := K) (G := G) (p := p)
      hG πK hπK_complete L
  let bP' : Module.Basis S ℤ (P_k(G)) :=
    projective_envelope_basis_of_order_prime_to_p_local
      (A := A) (K := K) (G := G) (p := p)
      hG πK hπK_pairwise hπK_complete L P hP_envelope
  let bK' : Module.Basis S ℤ (R_K(G)) :=
    generic_simple_basis_of_order_prime_to_p_local
      (G := G) πK hπK_pairwise hπK_complete
  have himages' :
      ∀ i,
        (projectiveGrothendieckScalarExtensionHom (A := A) (K := K) (G := G)).toIntLinearMap
          (bP' i) = bK' i := by
    -- Reuse the pointwise scalar-extension basis-image theorem on the named matrix-tail bases
    -- before translating back to the theorem's boundary `let`-bindings.
    intro i
    simpa [bP', bK'] using
      projectiveScalarExtension_basis_image_of_order_prime_to_p_local
        (A := A) (K := K) (G := G) (p := p)
        hG πK hπK_pairwise hπK_complete L P hP_envelope i
  have hmatrix :
      bK'.toMatrix
        (fun i ↦
          (projectiveGrothendieckScalarExtensionHom (A := A) (K := K) (G := G)).toIntLinearMap
            (bP' i)) =
        bK'.toMatrix bK' := by
    -- Once the basis images are known pointwise, the basis matrix is the identity.
    have hfun :
        (fun i ↦
          (projectiveGrothendieckScalarExtensionHom (A := A) (K := K) (G := G)).toIntLinearMap
            (bP' i)) = bK' := by
      funext i
      exact himages' i
    exact congrArg (fun g ↦ bK'.toMatrix g) hfun
  -- Translate the named basis packages back to the theorem's boundary `let`-bindings.
  simpa [πk, hπk_pairwise, hπk_complete, bP', bK',
    reduction_family_of_order_prime_to_p_local,
    reduction_family_pairwise_nonisomorphic_of_order_prime_to_p_local,
    reduction_family_complete_irreducible_of_order_prime_to_p_local,
    projective_envelope_basis_of_order_prime_to_p_local,
    generic_simple_basis_of_order_prime_to_p_local] using hmatrix

end MatrixIdentities
