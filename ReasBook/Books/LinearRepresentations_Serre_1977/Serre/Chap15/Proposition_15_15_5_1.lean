import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap14.Corollary_14_14_3_3
import LinearRepresentations_Serre_1977.Serre.Chap14.Exercise_14_14_4_5
import LinearRepresentations_Serre_1977.Serre.Chap14.Infra_14_4_ProjectiveLift
import LinearRepresentations_Serre_1977.Serre.Chap14.Lemma_14_14_4_1
import LinearRepresentations_Serre_1977.Serre.Chap15.Definition_15_15_1_1
import LinearRepresentations_Serre_1977.Serre.Chap15.Definition_15_15_2_1
import LinearRepresentations_Serre_1977.Serre.Chap15.Definition_15_15_3_1
import LinearRepresentations_Serre_1977.Serre.Chap15.Exercise_15_15_2_5
import LinearRepresentations_Serre_1977.Serre.Chap15.Proposition_15_15_5_1.Index
import LinearRepresentations_Serre_1977.Serre.Chap15.Theorem_15_15_2_2

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

/-- Part (i) of Proposition 15-15.5-1: if the order of `G` is prime to `p`, then every
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

local notation "k" => IsLocalRing.ResidueField A

/-- Helper for Proposition 15-15.5-1: if `p` does not divide `|G|`, then the image of `|G|` in the
local ring `A` is a unit. -/
-- Proof sketch: the image of `|G|` in the residue field is nonzero because the residue field has
-- characteristic `p` and `p ∤ |G|`; local-ring theory then upgrades this to invertibility in `A`.
lemma card_unit_of_order_prime_to_p {G : Type u} [Finite G] (hG : ¬ p ∣ Nat.card G) :
    IsUnit (Nat.card G : A) := by
  let _ : NeZero (Nat.card G : k) := NeZero.of_not_dvd k hG
  -- The residue of `|G|` is nonzero in characteristic `p`, so local-ring theory upgrades it to a
  -- unit already over `A`.
  have hresidue_ne_zero : IsLocalRing.residue A (Nat.card G : A) ≠ 0 := by
    rw [← IsLocalRing.ResidueField.algebraMap_eq]
    exact NeZero.ne (Nat.card G : k)
  exact (IsLocalRing.residue_ne_zero_iff_isUnit (Nat.card G : A)).mp hresidue_ne_zero

variable {G : Type u} [Group G] [Finite G]
variable {P : Type v} [AddCommGroup P] [Module A[G] P]

-- Proof sketch: part `(1)` applies over the residue field because `¬ p ∣ Nat.card G`, so the
-- image of `Nat.card G` in `A ⧸ 𝔪_A` is nonzero. In a local ring this implies that
-- `(Nat.card G : A)` is a unit, and the companion invertible-order bridge above then yields the
-- projectivity statement over `A[G]`.
/-- Part (i) of Proposition 15-15.5-1 over a local base ring: if the order of `G` is prime to
`p`, then every `A[G]`-module
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
-- Proof sketch: when `p ∤ |G|`, both `K[G]` and `k[G]` are semisimple. Therefore a stable lattice
-- in a simple `K[G]`-module has simple reduction, nonisomorphic simples stay nonisomorphic after
-- reduction, and every simple `k[G]`-module occurs as the reduction of one of the chosen simple
-- `K[G]`-modules.
/-- Helper for Proposition 15-15.5-1: the canonical reduced family remains pairwise
nonisomorphic under the prime-to-`p` hypothesis. -/
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
  let _ := hπK_complete
  -- Reflect any isomorphism between reductions back upstairs, then use the pairwise hypothesis
  -- on the original simple `K[G]`-family.
  exact
    stableLattice_reductionFamily_pairwise_of_iso_reflection
      (A := A) (K := K) (G := G) (S := S) πK hπK_pairwise L
      (fun {i j} hij ↦
        stableLattice_reduction_iso_implies_generic_iso_of_order_prime_to_p
          (A := A) (K := K) (G := G) (p := p) (S := S) hG πK L hij)


/-- Helper for Proposition 15-15.5-1: the canonical reduced family is complete and irreducible
under the prime-to-`p` hypothesis. -/
-- TODO: start from a simple `k[G]`-representation, lift a projective envelope through `A[G]`,
-- scalar-extend to `K`, and identify its decomposition class with one of the chosen `πK i`.
theorem stableLattice_reductionFamily_isCompleteIrreducible_of_order_prime_to_p
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
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

/-- Part (ii) of Proposition 15-15.5-1: if `p ∤ |G|` and `πK` is a
complete family of pairwise nonisomorphic simple `K[G]`-representations, then the reductions of
stable lattices in the `πK i` again form a complete family of pairwise nonisomorphic simple
`k[G]`-representations. In the project API this is recorded by the reduced `FDRep` family
`fun i ↦ FDRep.of (L i).reductionRepresentation` together with the owner predicates
`PairwiseNonisomorphic` and `IsCompleteIrreducibleFamily`. -/
theorem stableLattice_reductions_form_complete_simple_family_of_order_prime_to_p
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
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
/-- Intermediate matrix identity for Proposition 15-15.5-1: if `p ∤ |G|`, then the canonical
projective-envelope basis of
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


-- Proof sketch: part `(3)` shows that the reductions of the chosen lattices form a complete
-- simple family over `k`, so Proposition `14-14.1-1` already supplies the canonical basis owner
-- on `R_k(G)`. The owner `decompositionHom A K G` sends the basis vector `i` in `R_K(G)` to the
-- same
-- indexed reduced simple class, so its matrix in the two canonical simple-class bases is the
-- identity.
/-- Intermediate matrix identity for Proposition 15-15.5-1: source-facing decomposition-matrix
form. If `p ∤ |G|`, then for a
complete family of simple `K[G]`-modules with chosen stable lattices, the canonical simple-class
basis on the reduced family identifies `decompositionHom A K G : R_K(G) → R_k(G)` with the identity
matrix. -/
-- TODO: once the reduced family is proved complete and pairwise nonisomorphic, evaluate each
-- simple-class basis vector under `decompositionHom` and simplify with
-- `decompositionHom_finiteRepClass_eq`.
theorem decompositionHom_toMatrix_eq_one_of_order_prime_to_p
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
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
/-- Proposition 15-15.5-1: source-facing matrix form of part (iii). If `p ∤ |G|`, then Serre's
scalar-extension homomorphism is represented by the identity matrix between the canonical
projective-envelope basis of `P_k(G)` attached to the canonical reduced family and the
corresponding complete simple-class basis of `R_K(G)`. Concretely, this is the canonical owner
`projectiveGrothendieckScalarExtensionHom A K`. -/
-- TODO: combine the Cartan identity with the decomposition identity, using the
-- `projectiveGrothendieckReductionEquiv` transport and the projective-class bridge
-- `projectiveGrothendieckScalarExtensionHom_apply`.
theorem projectiveScalarExtension_toMatrix_eq_one_of_order_prime_to_p
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
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
