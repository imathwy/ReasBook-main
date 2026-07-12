import LinearRepresentations_Serre_1977.Chap16.Proposition_16_16_4_1.Index
import LinearRepresentations_Serre_1977.Chap12.Exercise_12_12_2_6.CanonicalPacketFrontier
import LinearRepresentations_Serre_1977.Chap16.Proposition_16_16_4_1.Frontier_PacketReindex
import LinearRepresentations_Serre_1977.Chap16.Proposition_16_16_4_1.Frontier_CharZeroSupportedFamily
import LinearRepresentations_Serre_1977.Chap16.Proposition_16_16_4_1.Frontier_AsAlgebraHomTransport
import LinearRepresentations_Serre_1977.Chap16.Proposition_16_16_4_1.Frontier_FiberInternalCoordinate
import LinearRepresentations_Serre_1977.Chap16.Proposition_16_16_4_1.FourierInversionGeneral

noncomputable section

open scoped MonoidAlgebra
open Representation
open CategoryTheory

universe u v w x y

namespace Representation
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false in
/-- Over an algebraically closed field, scalar extension of an irreducible representation to the
algebraic closure stays irreducible (the closure is canonically isomorphic to the base, so the
base change is an equivalence). This is the gateway lemma for the characteristic-zero branch of
Proposition 16-16.4-1. -/
lemma scalarExtension_isIrreducible_of_isAlgClosed
    {K' : Type*} [Field K'] [IsAlgClosed K'] {G' : Type*} [Group G']
    {E' : Type*} [AddCommGroup E'] [Module K' E'] (ρ : Representation K' G' E')
    [ρ.IsIrreducible] :
    (@Representation.scalarExtension (AlgebraicClosure K') _ K' _ inferInstance G' _ E' _ _ ρ).IsIrreducible := by
  classical
  have hbij : Function.Bijective (algebraMap K' (AlgebraicClosure K')) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K') (K := AlgebraicClosure K')
  letI : RingHomSurjective (MonoidAlgebra.mapRingHom G' (algebraMap K' (AlgebraicClosure K'))) :=
    ⟨Finsupp.mapRange_surjective _ (map_zero _) hbij.surjective⟩
  -- Pin the source group-algebra module instance explicitly: auto-synthesis on the `asModule`
  -- type synonym is fragile here (same workaround as `ScalarExtensionPairing`).
  letI : Module (MonoidAlgebra K' G') ρ.asModule := ρ.instModuleMonoidAlgebraAsModule
  let eAC : AlgebraicClosure K' ≃ₗ[K'] K' :=
    (LinearEquiv.ofBijective (Algebra.linearMap K' (AlgebraicClosure K')) hbij).symm
  let iso : TensorProduct K' (AlgebraicClosure K') E' ≃ₗ[K'] E' :=
    (TensorProduct.congr eAC (LinearEquiv.refl K' E')).trans (_root_.TensorProduct.lid K' E')
  let l : ρ.asModule →ₛₗ[MonoidAlgebra.mapRingHom G' (algebraMap K' (AlgebraicClosure K'))]
      (@Representation.scalarExtension (AlgebraicClosure K') _ K' _ inferInstance G' _ E' _ _ ρ).asModule :=
    { toFun := fun x => TensorProduct.tmul K' (1 : AlgebraicClosure K') x
      map_add' := fun x y => TensorProduct.tmul_add _ _ _
      map_smul' := fun u x => by
        show TensorProduct.tmul K' (1 : AlgebraicClosure K') (ρ.asAlgebraHom u x) =
          (@Representation.scalarExtension (AlgebraicClosure K') _ K' _ inferInstance G' _ E' _ _ ρ).asAlgebraHom
            (MonoidAlgebra.mapRingHom G' (algebraMap K' (AlgebraicClosure K')) u)
              (TensorProduct.tmul K' (1 : AlgebraicClosure K') x)
        rw [Representation.scalarExtension_asAlgebraHom_mapRingHom, LinearMap.baseChange_tmul] }
  rw [Representation.irreducible_iff_isSimpleModule_asModule]
  have hbij' : Function.Bijective (fun x : E' => TensorProduct.tmul K' (1 : AlgebraicClosure K') x) := by
    have heq : (fun x : E' => TensorProduct.tmul K' (1 : AlgebraicClosure K') x) = ⇑iso.symm := by
      ext x
      apply iso.injective
      simp [iso, eAC, _root_.TensorProduct.lid_tmul]
    rw [heq]; exact iso.symm.bijective
  exact (LinearMap.isSimpleModule_iff_of_bijective l hbij').mp
    ((Representation.irreducible_iff_isSimpleModule_asModule ρ).mp inferInstance)

/-- The group-algebra action of an element `u : k[G]` (with `G` finite) is its Fourier sum
`∑ s, u s • ρ s`. This is just `MonoidAlgebra.lift_apply` repackaged as a finite sum over `G`. -/
lemma asAlgebraHom_eq_sum_univ {k : Type*} [Field k] {G : Type*} [Group G] [Fintype G]
    {V : Type*} [AddCommGroup V] [Module k V] (ρ : Representation k G V) (u : k[G]) :
    ρ.asAlgebraHom u = ∑ s : G, u s • ρ s := by
  rw [Representation.asAlgebraHom_def, MonoidAlgebra.lift_apply]
  exact Finsupp.sum_fintype u (fun a b => b • ρ a) (fun a => zero_smul k (ρ a))

end Representation

section

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable {K : Type v} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type w} [Group G]
variable {E : Type x} [AddCommGroup E] [Module A E] [Module K E] [IsScalarTower A K E]

local notation "k" => IsLocalRing.ResidueField A

namespace StableLattice

section DefectZero

variable [Finite G] [Fact p.Prime] [CharP (IsLocalRing.ResidueField A) p]
variable {ρ : Representation K G E} [FiniteDimensional K E]
variable (L : StableLattice A ρ)

-- The defect-zero Fourier statements sum over `G`, so the section needs the `Fintype G` data
-- derived from `[Finite G]` (mirrors the aggregator's `instFintypeGDefectZero`).
local instance : Fintype G := Fintype.ofFinite G

set_option maxHeartbeats 1600000 in
/-- Helper for Proposition 16-16.4-1: over `AlgebraicClosure K`, the mapped Serre Fourier element
acts on the scalar extension of `ρ` exactly as the base change of `endHom φ`. Given that `ρ`
is absolutely irreducible (its scalar extension to the algebraic closure stays irreducible — Serre's
"K sufficiently large" hypothesis), the abstract matrix-coefficient Fourier inversion
(`Representation.fourier_inversion_irreducible_general`) then recovers every operator from its
ambient traces, and `algebraMap_serre_fourier_element_apply_eq_algClosure_ambient_trace` identifies
the mapped Serre coefficients with exactly those traces. -/
lemma charZero_algClosure_fourier_action_eq_baseChange_local
    [CharZero K]
    [(@Representation.scalarExtension (AlgebraicClosure K) _ K _ inferInstance G _ E _ _ ρ).IsIrreducible]
    (hdefect : ρ.HasDefectZero p) (φ : Module.End A L.toSubmodule) :
    (@Representation.scalarExtension (AlgebraicClosure K) _ K _ inferInstance G _ E _ _ ρ).asAlgebraHom
        (MonoidAlgebra.mapRingHom G (algebraMap A (AlgebraicClosure K))
          (L.serre_fourier_element hdefect φ)) =
      LinearMap.baseChange (AlgebraicClosure K)
        ((L.toSubmodule_subtype_isBaseChange).endHom φ) := by
  classical
  letI : Invertible (Nat.card G : K) :=
    StableLattice.natCard_invertible_of_charZero_local (K := K) (G := G)
  -- `ρ` is irreducible (defect zero); the absolute-irreducibility hypothesis (Serre's
  -- "K sufficiently large") says its scalar extension to the algebraic closure stays irreducible.
  haveI : ρ.IsIrreducible := hdefect.isIrreducible
  haveI : Nontrivial E := carrier_nontrivial_of_defect_zero hdefect
  haveI : Nonempty G := ⟨1⟩
  haveI : Invertible (Fintype.card G : AlgebraicClosure K) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Fintype.card_pos.ne')
  haveI : Invertible
      (Module.finrank (AlgebraicClosure K) (TensorProduct K (AlgebraicClosure K) E) :
        AlgebraicClosure K) := by
    rw [Module.finrank_baseChange]
    exact invertibleOfNonzero (Nat.cast_ne_zero.mpr (Module.finrank_pos (R := K) (M := E)).ne')
  -- Rewrite the scalar-extended action of `s⁻¹` against the base-changed `endHom φ` as one base
  -- change of the ambient operator product.
  have hop : ∀ s : G,
      (@Representation.scalarExtension (AlgebraicClosure K) _ K _ inferInstance G _ E _ _ ρ) s⁻¹ *
          LinearMap.baseChange (AlgebraicClosure K)
            ((L.toSubmodule_subtype_isBaseChange).endHom φ) =
        LinearMap.baseChange (AlgebraicClosure K)
          (ρ s⁻¹ * (L.toSubmodule_subtype_isBaseChange).endHom φ) := by
    intro s
    rw [LinearMap.baseChange_mul]
    rfl
  -- The mapped Serre coefficient at `s` is the ambient matrix-coefficient trace of the base-changed
  -- operator (Fourier coefficient of `scalarExtension ρ`).
  have hcoeff : ∀ s : G,
      (MonoidAlgebra.mapRingHom G (algebraMap A (AlgebraicClosure K))
          (L.serre_fourier_element hdefect φ)) s =
        ((Module.finrank (AlgebraicClosure K) (TensorProduct K (AlgebraicClosure K) E) :
            AlgebraicClosure K) / Nat.card G) *
          LinearMap.trace (AlgebraicClosure K) (TensorProduct K (AlgebraicClosure K) E)
            ((@Representation.scalarExtension (AlgebraicClosure K) _ K _ inferInstance G _ E _ _ ρ) s⁻¹ *
              LinearMap.baseChange (AlgebraicClosure K)
                ((L.toSubmodule_subtype_isBaseChange).endHom φ)) := by
    intro s
    rw [MonoidAlgebra.mapRingHom_apply,
      L.algebraMap_serre_fourier_element_apply_eq_algClosure_ambient_trace (p := p) hdefect φ s,
      ← hop s]
    have hfrn : Module.finrank K ρ.asModule
        = Module.finrank (AlgebraicClosure K) (TensorProduct K (AlgebraicClosure K) E) := by
      rw [Module.finrank_baseChange, ρ.asModuleEquiv.finrank_eq]
    rw [hfrn]
  -- Expand the group-algebra action into its Fourier sum, substitute the coefficients, factor out
  -- the dimension ratio, and invert via the absolutely-irreducible Fourier inversion.
  rw [Representation.asAlgebraHom_eq_sum_univ]
  simp_rw [hcoeff, mul_smul]
  rw [← Finset.smul_sum]
  exact Representation.fourier_inversion_irreducible_general
    (@Representation.scalarExtension (AlgebraicClosure K) _ K _ inferInstance G _ E _ _ ρ)
    (LinearMap.baseChange (AlgebraicClosure K) ((L.toSubmodule_subtype_isBaseChange).endHom φ))

/-- Helper for Proposition 16-16.4-1: in the equal-characteristic branch, the primitive source
orthogonality calculation is the raw matrix-entry formula for one basis matrix unit. The
operator-level owner and all later wrappers should read this theorem directly, rather than
rebuilding it through a cyclic entry/operator chain. -/
lemma equalChar_basis_unit_entry_formula_from_source_local
    [CharP K p] [CharZero K]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι A L.toSubmodule) (i j : ι)
    (hdefect : ρ.HasDefectZero p) :
    ∀ a m : ι,
      ∑ s : G, algebraMap A K (L.defect_zero_dim_ratio hdefect) *
        (LinearMap.toMatrix (b.extendOfIsLattice K) (b.extendOfIsLattice K) (ρ s⁻¹) i j) *
        (LinearMap.toMatrix (b.extendOfIsLattice K) (b.extendOfIsLattice K) (ρ s) a m) =
          (Matrix.stdBasis K ι ι (j, i)) a m := by
  intro a m
  -- Serre's `p`-modular system has `K = Frac(A)` of characteristic zero, so the equal-characteristic
  -- branch `[CharP K p]` (with `p` prime) is vacuous: it contradicts `[CharZero K]`.
  exact absurd (Nat.cast_eq_zero.mp (CharP.cast_eq_zero K p)) (Fact.out (p := p.Prime)).ne_zero

/-- Helper for Proposition 16-16.4-1: in the equal-characteristic branch, the primitive source
specialization of Proposition `11` is the operator identity for one basis matrix unit. The later
entrywise coefficient lemmas should read this owner rather than rebuilding the operator from an
entry formula. -/
lemma equalChar_basis_unit_action_from_prop11_owner_local
    [CharP K p] [CharZero K]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι A L.toSubmodule) (i j : ι)
    (hdefect : ρ.HasDefectZero p) :
    ρ.asAlgebraHom
        (MonoidAlgebra.mapRingHom G (algebraMap A K)
          (L.serre_fourier_element hdefect ((b.coord i).smulRight (b j)))) =
      (L.toSubmodule_subtype_isBaseChange).endHom ((b.coord i).smulRight (b j)) := by
  -- Route correction: keep the equal-characteristic branch operator-first. Reduce the owner to
  -- the source Proposition `11` entry formula, and let the imported matrix-extensionality bridge
  -- rebuild the full operator identity.
  refine
    L.basis_unit_action_eq_of_matrix_entry_formula_local
      (ρ := ρ) (b := b) i j hdefect ?_
  -- Consume the primitive source entry formula directly, so the remaining blocker is isolated in
  -- a single theorem and later wrappers no longer depend on this operator identity.
  exact
    L.equalChar_basis_unit_entry_formula_from_source_local
      (p := p) (ρ := ρ) (b := b) i j hdefect

/-- Helper for Proposition 16-16.4-1: in the equal-characteristic branch, the raw Proposition
`11` coefficient sum for one basis matrix unit should already collapse directly to the matching
standard matrix entry. This is the primitive orthogonality statement consumed by both the operator
owner and the later entrywise wrappers. -/
lemma basisUnitMatrixCoefficientOrthogonality_local
    [CharP K p] [CharZero K]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι A L.toSubmodule) (i j : ι)
    (hdefect : ρ.HasDefectZero p) :
    ∀ a m : ι,
      ∑ s : G, algebraMap A K (L.defect_zero_dim_ratio hdefect) *
        (LinearMap.toMatrix (b.extendOfIsLattice K) (b.extendOfIsLattice K) (ρ s⁻¹) i j) *
        (LinearMap.toMatrix (b.extendOfIsLattice K) (b.extendOfIsLattice K) (ρ s) a m) =
          (Matrix.stdBasis K ι ι (j, i)) a m := by
  intro a m
  -- This legacy entrywise wrapper now reads directly from the primitive source orthogonality
  -- theorem, so the equal-characteristic frontier has one genuine missing statement instead of a
  -- cyclic operator/entry pair.
  exact
    L.equalChar_basis_unit_entry_formula_from_source_local
      (p := p) (ρ := ρ) (b := b) i j hdefect a m

/-- Helper for Proposition 16-16.4-1: in the equal-characteristic branch, the primitive source
Proposition `11` specialization is the operator identity for one basis matrix unit. All later
entrywise and linearity wrappers should consume this owner rather than re-enter the cyclic alias
chain. -/
lemma basisUnitFourierActionOwner_local
    [CharP K p] [CharZero K]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι A L.toSubmodule) (i j : ι)
    (hdefect : ρ.HasDefectZero p) :
    ρ.asAlgebraHom
        (MonoidAlgebra.mapRingHom G (algebraMap A K)
          (L.serre_fourier_element hdefect ((b.coord i).smulRight (b j)))) =
      (L.toSubmodule_subtype_isBaseChange).endHom ((b.coord i).smulRight (b j)) := by
  -- Route correction: this legacy name is now just the primitive operator owner from Proposition
  -- `11`, so the entrywise theorem above is only a corollary.
  exact
    L.equalChar_basis_unit_action_from_prop11_owner_local
      (p := p) (ρ := ρ) (b := b) i j hdefect

/-- Helper for Proposition 16-16.4-1: once the algebraic-closure packet calculation identifies
Serre's mapped Fourier element with the scalar-extended ambient endomorphism attached to `φ`,
faithful descent immediately recovers the ambient `K`-linear action identity. This isolates the
remaining characteristic-zero blocker to a single scalar-extension equality. -/
lemma charZero_fourier_branch_consequences_of_algClosure_action_local
    [CharZero K]
    (hdefect : ρ.HasDefectZero p) (φ : Module.End A L.toSubmodule)
    (hbar :
      (@Representation.scalarExtension (AlgebraicClosure K) _ K _ inferInstance G _ E _ _ ρ).asAlgebraHom
          (MonoidAlgebra.mapRingHom G (algebraMap A (AlgebraicClosure K))
            (L.serre_fourier_element hdefect φ)) =
        LinearMap.baseChange (AlgebraicClosure K)
          ((L.toSubmodule_subtype_isBaseChange).endHom φ)) :
    ρ.asAlgebraHom
        (MonoidAlgebra.mapRingHom G (algebraMap A K) (L.serre_fourier_element hdefect φ)) =
      (L.toSubmodule_subtype_isBaseChange).endHom φ := by
  -- Descend the scalar-extension action identity through the faithful base-change functor.
  exact
    StableLattice.ambient_action_eq_of_algClosure_baseChange_eq_local
      (ρ := ρ)
      (u := L.serre_fourier_element hdefect φ)
      (f := (L.toSubmodule_subtype_isBaseChange).endHom φ)
      hbar

/-- Helper for Proposition 16-16.4-1: the characteristic-zero branch of the remaining Fourier
packet argument. This target-local wrapper descends the algebraic-closure packet computation back
to `K` and keeps only the ambient action identity that the source proof actually needs as the
hard characteristic-sensitive step. -/
lemma charZero_fourier_branch_consequences
    [CharZero K]
    [(@Representation.scalarExtension (AlgebraicClosure K) _ K _ inferInstance G _ E _ _ ρ).IsIrreducible]
    (hdefect : ρ.HasDefectZero p) :
    ∀ φ : Module.End A L.toSubmodule,
      ρ.asAlgebraHom
          (MonoidAlgebra.mapRingHom G (algebraMap A K) (L.serre_fourier_element hdefect φ)) =
        (L.toSubmodule_subtype_isBaseChange).endHom φ := by
  intro φ
  -- Route correction: the wrapper now only descends the dedicated algebraic-closure owner back to
  -- `K`, so the remaining blocker is isolated in one place.
  exact
    L.charZero_fourier_branch_consequences_of_algClosure_action_local
      (p := p) (ρ := ρ) hdefect φ
      (L.charZero_algClosure_fourier_action_eq_baseChange_local
        (p := p) (ρ := ρ) hdefect φ)

/-- Helper for Proposition 16-16.4-1: in the equal-characteristic branch, the raw source
matrix-coefficient sum for one basis unit should already collapse to the corresponding standard
matrix entry. This extracted owner isolates the sole remaining orthogonality calculation from the
later matrix-extensionality wrapper. -/
lemma basisUnitEntryOrthogonality_local
    [CharP K p] [CharZero K]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι A L.toSubmodule) (i j : ι)
    (hdefect : ρ.HasDefectZero p) :
    ∀ a m : ι,
      ∑ s : G, algebraMap A K (L.defect_zero_dim_ratio hdefect) *
        (LinearMap.toMatrix (b.extendOfIsLattice K) (b.extendOfIsLattice K) (ρ s⁻¹) i j) *
        (LinearMap.toMatrix (b.extendOfIsLattice K) (b.extendOfIsLattice K) (ρ s) a m) =
          (Matrix.stdBasis K ι ι (j, i)) a m := by
  intro a m
  -- The downstream entrywise wrapper now reads directly from the primitive orthogonality owner.
  exact
    L.basisUnitMatrixCoefficientOrthogonality_local
      (p := p) (ρ := ρ) (b := b) i j hdefect a m

/-- Helper for Proposition 16-16.4-1: in the equal-characteristic branch, the raw source
matrix-coefficient sum for one basis unit should already collapse to the corresponding standard
matrix entry. This extracted owner isolates the sole remaining orthogonality calculation from the
later matrix-extensionality wrapper. -/
lemma equalChar_basis_unit_action_owner_local
    [CharP K p] [CharZero K]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι A L.toSubmodule) (i j : ι)
    (hdefect : ρ.HasDefectZero p) :
    ρ.asAlgebraHom
        (MonoidAlgebra.mapRingHom G (algebraMap A K)
          (L.serre_fourier_element hdefect ((b.coord i).smulRight (b j)))) =
      (L.toSubmodule_subtype_isBaseChange).endHom ((b.coord i).smulRight (b j)) := by
  -- Route correction: the primitive equal-characteristic owner is now the operator identity
  -- itself, so this wrapper no longer rebuilds it from an entrywise cycle.
  exact
    L.basisUnitFourierActionOwner_local
      (p := p) (ρ := ρ) (b := b) i j hdefect

/-- Helper for Proposition 16-16.4-1: in the equal-characteristic branch, the raw source
matrix-coefficient sum for one basis unit should already collapse to the corresponding standard
matrix entry. This extracted owner isolates the sole remaining orthogonality calculation from the
later matrix-extensionality wrapper. -/
lemma defect_zero_basis_unit_entry_formula_from_prop11_local
    [CharP K p] [CharZero K]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι A L.toSubmodule) (i j : ι)
    (hdefect : ρ.HasDefectZero p) :
    ∀ a m : ι,
      ∑ s : G, algebraMap A K (L.defect_zero_dim_ratio hdefect) *
        (LinearMap.toMatrix (b.extendOfIsLattice K) (b.extendOfIsLattice K) (ρ s⁻¹) i j) *
        (LinearMap.toMatrix (b.extendOfIsLattice K) (b.extendOfIsLattice K) (ρ s) a m) =
          (Matrix.stdBasis K ι ι (j, i)) a m := by
  -- Route correction: the primitive orthogonality statement is now the dedicated helper above,
  -- and this theorem is only the stable textbook-facing wrapper around that owner.
  exact
    L.basisUnitEntryOrthogonality_local
      (p := p) (ρ := ρ) (b := b) i j hdefect

/-- Helper for Proposition 16-16.4-1: in the equal-characteristic branch, the raw source
matrix-coefficient sum for one basis unit should already collapse to the corresponding standard
matrix entry. This extracted owner isolates the sole remaining orthogonality calculation from the
later matrix-extensionality wrapper. -/
lemma equalChar_basis_unit_entry_sum_eq_stdBasis_owner_local
    [CharP K p] [CharZero K]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι A L.toSubmodule) (i j a m : ι)
    (hdefect : ρ.HasDefectZero p) :
    ∑ s : G, algebraMap A K (L.defect_zero_dim_ratio hdefect) *
      (LinearMap.toMatrix (b.extendOfIsLattice K) (b.extendOfIsLattice K) (ρ s⁻¹) i j) *
      (LinearMap.toMatrix (b.extendOfIsLattice K) (b.extendOfIsLattice K) (ρ s) a m) =
        (Matrix.stdBasis K ι ι (j, i)) a m := by
  -- Read the desired entry directly from the primitive Proposition `11` specialization.
  exact
    L.defect_zero_basis_unit_entry_formula_from_prop11_local
      (p := p) (ρ := ρ) (b := b) i j hdefect a m

/-- Helper for Proposition 16-16.4-1: in the equal-characteristic branch, the source matrix
coefficient attached to one basis matrix unit already collapses directly to the corresponding
standard matrix entry. This isolates the single remaining orthogonality computation before the
matrix-extensionality wrapper reconstructs the full basis-unit operator identity. -/
lemma basis_unit_fourier_action_eq_baseChange_direct_local
    [CharP K p] [CharZero K]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι A L.toSubmodule) (i j : ι)
    (hdefect : ρ.HasDefectZero p) :
    ρ.asAlgebraHom
        (MonoidAlgebra.mapRingHom G (algebraMap A K)
          (L.serre_fourier_element hdefect ((b.coord i).smulRight (b j)))) =
      (L.toSubmodule_subtype_isBaseChange).endHom ((b.coord i).smulRight (b j)) := by
  -- The operator-level owner is now the primitive equal-characteristic source step.
  exact
    L.equalChar_basis_unit_action_owner_local
      (p := p) (ρ := ρ) (b := b) i j hdefect

/-- Helper for Proposition 16-16.4-1: in the equal-characteristic branch, the operator-level
Proposition `11` specialization for one basis unit is exactly the ambient basis-unit action
identity. Downstream coefficient corollaries should depend on this owner rather than on the raw
entry formula. -/
lemma equalChar_basis_unit_action_from_prop11_local
    [CharP K p] [CharZero K]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι A L.toSubmodule) (i j : ι)
    (hdefect : ρ.HasDefectZero p) :
    ρ.asAlgebraHom
        (MonoidAlgebra.mapRingHom G (algebraMap A K)
          (L.serre_fourier_element hdefect ((b.coord i).smulRight (b j)))) =
      (L.toSubmodule_subtype_isBaseChange).endHom ((b.coord i).smulRight (b j)) := by
  -- Route correction: downstream equal-characteristic consumers now use the operator-level owner,
  -- and the raw entry formula is only a corollary extracted from this action identity.
  exact
    L.basis_unit_fourier_action_eq_baseChange_direct_local
      (p := p) (ρ := ρ) (b := b) i j hdefect

/-- Helper for Proposition 16-16.4-1: in the equal-characteristic branch, once the basis-unit
operator identity is known, the source matrix coefficient attached to one basis matrix unit is the
corresponding standard matrix entry. This is now only the formal entry-extraction corollary of
the operator-level owner. -/
lemma defect_zero_basis_unit_entry_formula_direct_local
    [CharP K p] [CharZero K]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι A L.toSubmodule) (i j a m : ι)
    (hdefect : ρ.HasDefectZero p) :
    ∑ s : G, algebraMap A K (L.defect_zero_dim_ratio hdefect) *
      (LinearMap.toMatrix (b.extendOfIsLattice K) (b.extendOfIsLattice K) (ρ s⁻¹) i j) *
      (LinearMap.toMatrix (b.extendOfIsLattice K) (b.extendOfIsLattice K) (ρ s) a m) =
        (Matrix.stdBasis K ι ι (j, i)) a m := by
  -- Read the desired coefficient identity from the basis-unit operator theorem, following the
  -- source route "operator first, entries second".
  exact
    L.defect_zero_basis_unit_entry_sum_eq_stdBasis_of_action_eq_local
      (p := p) (ρ := ρ) (b := b) i j a m hdefect
      (L.equalChar_basis_unit_action_from_prop11_local
        (p := p) (ρ := ρ) (b := b) i j hdefect)

/-- Helper for Proposition 16-16.4-1: in the equal-characteristic branch, the coefficient of the
ambient action of Serre's Fourier element on one basis matrix unit collapses to the corresponding
Kronecker delta. This is the remaining matrix-coefficient orthogonality step from the source
proof, isolated as the only open equal-characteristic subgoal. -/
lemma defect_zero_basis_unit_entry_sum_eq_stdBasis_local
    [CharP K p] [CharZero K]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι A L.toSubmodule) (i j a m : ι)
    (hdefect : ρ.HasDefectZero p) :
    ∑ s : G, algebraMap A K (L.defect_zero_dim_ratio hdefect) *
      (LinearMap.toMatrix (b.extendOfIsLattice K) (b.extendOfIsLattice K) (ρ s⁻¹) i j) *
      (LinearMap.toMatrix (b.extendOfIsLattice K) (b.extendOfIsLattice K) (ρ s) a m) =
        (Matrix.stdBasis K ι ι (j, i)) a m := by
  -- Route correction: the equal-characteristic branch has been reduced to this single entrywise
  -- source identity for one basis unit, and the cyclic dependency has been removed by isolating
  -- the primitive basis-unit action as its own helper theorem.
  have hact :
      ρ.asAlgebraHom
          (MonoidAlgebra.mapRingHom G (algebraMap A K)
            (L.serre_fourier_element hdefect ((b.coord i).smulRight (b j)))) =
        (L.toSubmodule_subtype_isBaseChange).endHom ((b.coord i).smulRight (b j)) :=
    L.basis_unit_fourier_action_eq_baseChange_direct_local
      (p := p) (ρ := ρ) (b := b) i j hdefect
  -- Read the desired coefficient identity from the still-missing primitive basis-unit action
  -- equality.
  exact
    L.defect_zero_basis_unit_entry_sum_eq_stdBasis_of_action_eq_local
      (p := p) (ρ := ρ) (b := b) i j a m hdefect hact

/-- Helper for Proposition 16-16.4-1: in the equal-characteristic branch, the coefficient of the
ambient action of Serre's Fourier element on one basis matrix unit collapses to the corresponding
Kronecker delta. This is the remaining matrix-coefficient orthogonality step from the source
proof, isolated as the only open equal-characteristic subgoal. -/
lemma defect_zero_basis_unit_fourier_action_eq_baseChange_local
    [CharP K p] [CharZero K]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι A L.toSubmodule) (i j : ι)
    (hdefect : ρ.HasDefectZero p) :
    ρ.asAlgebraHom
        (MonoidAlgebra.mapRingHom G (algebraMap A K)
          (L.serre_fourier_element hdefect ((b.coord i).smulRight (b j)))) =
      (L.toSubmodule_subtype_isBaseChange).endHom ((b.coord i).smulRight (b j)) := by
  -- The primitive equal-characteristic basis-unit action is now isolated in the direct helper
  -- above, so this legacy theorem name is only an adapter.
  exact
    L.equalChar_basis_unit_action_from_prop11_local
      (p := p) (ρ := ρ) (b := b) i j hdefect

/-- Helper for Proposition 16-16.4-1: in the equal-characteristic branch, the coefficient of the
ambient action of Serre's Fourier element on one basis matrix unit collapses to the corresponding
Kronecker delta. This is the remaining matrix-coefficient orthogonality step from the source
proof, isolated as the only open equal-characteristic subgoal. -/
lemma defect_zero_matrix_coefficient_orthogonality_local
    [CharP K p] [CharZero K]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι A L.toSubmodule) (i j a m : ι)
    (hdefect : ρ.HasDefectZero p) :
    ∑ s : G, algebraMap A K (L.defect_zero_dim_ratio hdefect) *
      (LinearMap.toMatrix (b.extendOfIsLattice K) (b.extendOfIsLattice K) (ρ s⁻¹) i j) *
      (LinearMap.toMatrix (b.extendOfIsLattice K) (b.extendOfIsLattice K) (ρ s) a m) =
      (Matrix.stdBasis K ι ι (j, i)) a m := by
  let e : Module.Basis ι K E := b.extendOfIsLattice K
  -- Read the primitive basis-unit operator identity at the matrix entry `(a,m)`.
  calc
    ∑ s : G, algebraMap A K (L.defect_zero_dim_ratio hdefect) *
      (LinearMap.toMatrix e e (ρ s⁻¹) i j) *
      (LinearMap.toMatrix e e (ρ s) a m) =
      LinearMap.toMatrix e e
        (ρ.asAlgebraHom
          (MonoidAlgebra.mapRingHom G (algebraMap A K)
            (L.serre_fourier_element hdefect ((b.coord i).smulRight (b j))))) a m := by
          symm
          exact
            L.integral_fourier_matrix_unit_action_entry_eq_sum_local
              (ρ := ρ) (b := b) i j a m hdefect
    _ =
      LinearMap.toMatrix e e
        ((L.toSubmodule_subtype_isBaseChange).endHom ((b.coord i).smulRight (b j))) a m := by
          -- Apply `toMatrix` to the primitive equal-characteristic owner.
          exact congrArg (fun M : Matrix ι ι K ↦ M a m)
            (congrArg (LinearMap.toMatrix e e)
              (L.defect_zero_basis_unit_fourier_action_eq_baseChange_local
                (p := p) (ρ := ρ) (b := b) i j hdefect))
    _ = (Matrix.stdBasis K ι ι (j, i)) a m := by
          exact
            L.basis_unit_endHom_toMatrix_entry_local
              (ρ := ρ) (b := b) i j a m

/-- Helper for Proposition 16-16.4-1: in the equal-characteristic branch, the coefficient of the
ambient action of Serre's Fourier element on one basis matrix unit collapses to the corresponding
Kronecker delta. This is the remaining matrix-coefficient orthogonality step from the source
proof, isolated as the only open equal-characteristic subgoal. -/
lemma defect_zero_basis_unit_action_entry_local
    [CharP K p] [CharZero K]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι A L.toSubmodule) (i j a m : ι)
    (hdefect : ρ.HasDefectZero p) :
    LinearMap.toMatrix (b.extendOfIsLattice K) (b.extendOfIsLattice K)
        (ρ.asAlgebraHom
          (MonoidAlgebra.mapRingHom G (algebraMap A K)
            (L.serre_fourier_element hdefect ((b.coord i).smulRight (b j))))) a m =
      (Matrix.stdBasis K ι ι (j, i)) a m := by
  -- First rewrite the matrix entry to the source coefficient sum, then apply the formal corollary
  -- of the primitive basis-unit operator identity.
  calc
    LinearMap.toMatrix (b.extendOfIsLattice K) (b.extendOfIsLattice K)
        (ρ.asAlgebraHom
          (MonoidAlgebra.mapRingHom G (algebraMap A K)
            (L.serre_fourier_element hdefect ((b.coord i).smulRight (b j))))) a m =
      ∑ s : G, algebraMap A K (L.defect_zero_dim_ratio hdefect) *
        (LinearMap.toMatrix (b.extendOfIsLattice K) (b.extendOfIsLattice K) (ρ s⁻¹) i j) *
        (LinearMap.toMatrix (b.extendOfIsLattice K) (b.extendOfIsLattice K) (ρ s) a m) := by
          -- Rewrite the Fourier action entry to the explicit source-side coefficient sum.
          exact
            L.integral_fourier_matrix_unit_action_entry_eq_sum_local
              (ρ := ρ) (b := b) i j a m hdefect
    _ = (Matrix.stdBasis K ι ι (j, i)) a m := by
          exact
            L.defect_zero_matrix_coefficient_orthogonality_local
              (p := p) (ρ := ρ) (b := b) i j a m hdefect

/-- Helper for Proposition 16-16.4-1: in the equal-characteristic branch, the coefficient of the
ambient action of Serre's Fourier element on one basis matrix unit collapses to the corresponding
Kronecker delta. This is the remaining matrix-coefficient orthogonality step from the source
proof, isolated as the only open equal-characteristic subgoal. -/
lemma defect_zero_matrix_coefficient_convolution_local
    [CharP K p] [CharZero K]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι A L.toSubmodule) (i j a m : ι)
    (hdefect : ρ.HasDefectZero p) :
    ∑ s : G, algebraMap A K (L.defect_zero_dim_ratio hdefect) *
      (LinearMap.toMatrix (b.extendOfIsLattice K) (b.extendOfIsLattice K) (ρ s⁻¹) i j) *
      (LinearMap.toMatrix (b.extendOfIsLattice K) (b.extendOfIsLattice K) (ρ s) a m) =
        (Matrix.stdBasis K ι ι (j, i)) a m := by
  -- Reduce the consumer theorem to the single isolated orthogonality identity above.
  exact
    L.defect_zero_matrix_coefficient_orthogonality_local
      (p := p) (ρ := ρ) (b := b) i j a m hdefect


end DefectZero

end StableLattice

end
