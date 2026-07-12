import Mathlib
import LinearRepresentations_Serre_1977.Chap10.Definition_10_10_1_1
import LinearRepresentations_Serre_1977.Chap12.Proposition_12_12_1_3
-- `Serre.Chap12.Proposition_12_12_6_5` is intentionally not imported: it declares the *abbrev*
-- `Representation.IsQuasisplitGroupAlgebra K G := R[K](G) = R̄[K](G)`, whose name now clashes with
-- the homonymous *class* `Representation.IsQuasisplitGroupAlgebra` from
-- `Serre.Chap12.Corollary_12_12_2_2` (pulled in transitively via `Theorem_16_16_1_2`/
-- `Theorem_16_16_2_1`), giving an "environment already contains
-- 'Representation.IsQuasisplitGroupAlgebra'" collision.  This file only used the abbrev as the
-- `Fact`-wrapped quasisplitness hypothesis, so we spell that hypothesis out directly as
-- `Fact (R[K](G) = R̄[K](G))` (definitionally the abbrev) and drop the import.
import LinearRepresentations_Serre_1977.Chap15.Definition_15_15_3_1
import LinearRepresentations_Serre_1977.Chap15.Definition_15_15_3_1.FiniteRepScalarExtension
import LinearRepresentations_Serre_1977.Chap16.Exercise_16_16_1_11
import LinearRepresentations_Serre_1977.Chap16.Corollary_16_16_1_3.CharacterDescent
import LinearRepresentations_Serre_1977.Chap16.Corollary_16_16_1_3.GrothendieckCharacter
import LinearRepresentations_Serre_1977.Chap15.Proposition_15_15_5_1.MatrixPrimeToP
import LinearRepresentations_Serre_1977.Chap16.Theorem_16_16_1_2
import LinearRepresentations_Serre_1977.Chap16.Theorem_16_16_2_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

namespace Representation

open scoped Representation

section

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {K' : Type u} [Field K'] [Algebra K K'] [FiniteDimensional K K']
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime] [CharP (IsLocalRing.ResidueField A) p]

local notation "k" => IsLocalRing.ResidueField A
local notation:max "P_k(" G ")" => finiteProjectiveGroupAlgebraGrothendieckGroup k G

variable [IsDomain A] [IsDiscreteValuationRing A] [CharZero K]
variable [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [Fact (R[K](G) = R̄[K](G))]

omit [IsLocalRing A] [HenselianLocalRing A] [Field K'] [Algebra K K']
    [FiniteDimensional K K'] [Group G] [Finite G] [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField A) p] in
/-- Helper for Theorem 16-16.2-2: a coefficient ring embedded in a fraction field is a domain. -/
private theorem isDomain_of_isFractionRing_field_current
    (A : Type u) [CommRing A] (K : Type u) [Field K] [Algebra A K] [IsFractionRing A K] :
    IsDomain A := by
  exact (IsFractionRing.injective A K).isDomain

omit [FiniteDimensional K K'] [CharZero K] [Fact (R[K](G) = R̄[K](G))] in
/-- Helper for Theorem 16-16.2-2: ordinary Grothendieck characters commute pointwise with
finite scalar extension of coefficients. -/
private theorem finiteRepGrothendieckCharacter_scalarExtensionHom_apply
    (y : R₀[K](G)) (g : G) :
    (finiteRepGrothendieckCharacter K' G
        ((finiteRepGrothendieckScalarExtensionHom K K' G) y) : G → K') g =
      algebraMap K K' ((finiteRepGrothendieckCharacter K G y : G → K) g) := by
  -- Prove the computation on generators of the Grothendieck group, then extend additively.
  refine QuotientAddGroup.induction_on y ?_
  intro a
  refine FreeAbelianGroup.induction_on a ?_ ?_ ?_ ?_
  · simp
  · intro V
    -- On a genuine representation this is exactly trace compatibility with base change.
    change
      (finiteRepGrothendieckCharacter K' G
        ((finiteRepGrothendieckScalarExtensionHom K K' G) [V]₀) : G → K') g =
        algebraMap K K' ((finiteRepGrothendieckCharacter K G [V]₀ : G → K) g)
    rw [finiteRepGrothendieckScalarExtensionHom_class_eq,
      finiteRepGrothendieckCharacter_class, finiteRepGrothendieckCharacter_class]
    simpa [FDRep.scalarExtension] using
      (congrFun
        (ProjectiveScalarExtensionSplitInjective.scalarExtension_character_eq_map_local
          (G := G) (F := K) (E := K') (τ := V.ρ))
        g)
  · intro V hV
    -- Negatives are transported by additivity of both character maps.
    simpa using congrArg Neg.neg hV
  · intro a b ha hb
    -- Sums are transported by additivity of scalar extension and of characters.
    simpa [map_add] using congrArg₂ HAdd.hAdd ha hb

omit [FiniteDimensional K K'] [CharZero K] [Fact (R[K](G) = R̄[K](G))] in
/-- Helper for Theorem 16-16.2-2: a scalar-extended Grothendieck character is valued in the base
field. -/
private theorem isValuedInBaseField_finiteRepGrothendieckCharacter_scalarExtensionHom
    (y : R₀[K](G)) :
    IsValuedInBaseField K
      (finiteRepGrothendieckCharacter K' G
        ((finiteRepGrothendieckScalarExtensionHom K K' G) y) : G → K') := by
  -- The base-field preimage is the original `K`-valued Grothendieck character.
  rw [isValuedInBaseField_iff_mem_pointwiseAlgebraMap_range]
  refine ⟨(finiteRepGrothendieckCharacter K G y : G → K), ?_⟩
  ext g
  exact (finiteRepGrothendieckCharacter_scalarExtensionHom_apply (K := K) (K' := K') y g).symm

omit [FiniteDimensional K K'] [Fact p.Prime] [CharP (IsLocalRing.ResidueField A) p]
    [IsLocalRing A] [HenselianLocalRing A] [Algebra A K] [IsFractionRing A K]
    [Finite G] in
/-- Helper for Theorem 16-16.2-2: the source-facing Grothendieck-character map agrees with the
Corollary 16-16.1-3 character owner. -/
private theorem finiteRepGrothendieckCharacter_eq_local_current
    {F : Type u} [Field F] {H : Type u} [Group H] [Finite H]
    (x : R₀[F](H)) :
    finiteRepGrothendieckCharacter F H x =
      ProjectiveScalarExtensionSplitInjective.finiteRepGrothendieckCharacter_local
        (F := F) (G := H) x := by
  -- It is enough to compare both character maps on free generators of the Grothendieck group.
  refine QuotientAddGroup.induction_on x ?_
  intro a
  refine FreeAbelianGroup.induction_on a ?_ ?_ ?_ ?_
  · simp
  · intro V
    -- On an honest representation class both maps evaluate to the usual representation
    -- character.
    apply Subtype.ext
    funext h
    change finiteRepGrothendieckCharacter F H [V]₀ h =
      ProjectiveScalarExtensionSplitInjective.finiteRepGrothendieckCharacter_local
        (F := F) (G := H) [V]₀ h
    rw [finiteRepGrothendieckCharacter_class]
    exact
      (ProjectiveScalarExtensionSplitInjective.finiteRepGrothendieckCharacter_local_class
        (F := F) (G := H) V h).symm
  · intro V hV
    -- Additivity carries the generator comparison across negatives.
    simpa [map_neg] using congrArg Neg.neg hV
  · intro a b ha hb
    -- Additivity carries the generator comparison across sums.
    simp [map_add, ha, hb]

omit [FiniteDimensional K K'] [Fact p.Prime] [CharP (IsLocalRing.ResidueField A) p]
    [IsLocalRing A] [HenselianLocalRing A] [Algebra A K] [IsFractionRing A K]
    [Finite G] in
/-- Helper for Theorem 16-16.2-2: in characteristic zero, equality of source-facing
Grothendieck characters detects equality of virtual representation classes. -/
private theorem finiteRepGrothendieckCharacter_eq_iff_charZero_current
    {F : Type u} [Field F] [CharZero F] {H : Type u} [Group H] [Finite H]
    {x y : R₀[F](H)} :
    finiteRepGrothendieckCharacter F H x =
      finiteRepGrothendieckCharacter F H y ↔ x = y := by
  -- Convert to the Corollary 16-16.1-3 owner, where the existing basis inverse applies.
  letI : NeZero (Nat.card H : F) := ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
  rw [finiteRepGrothendieckCharacter_eq_local_current (F := F) (H := H) x,
    finiteRepGrothendieckCharacter_eq_local_current (F := F) (H := H) y]
  exact
    ProjectiveScalarExtensionSplitInjective.finiteRepGrothendieckCharacter_eq_iff_general_local
      (F := F) (G := H)

omit [FiniteDimensional K K'] [Finite G] [Fact p.Prime] [CharP (IsLocalRing.ResidueField A) p]
    [IsLocalRing A] [HenselianLocalRing A] [Algebra A K] [IsFractionRing A K]
    [CharZero K] [Fact (R[K](G) = R̄[K](G))] in
/-- Helper for Theorem 16-16.2-2: if scalar extension transports a complete simple family to a
complete simple family with the same index set, then ordinary scalar extension has a basiswise
retract. -/
private theorem finiteRepGrothendieckScalarExtension_retract_data_of_complete_simple_family_current
    {ι : Type*}
    (π : ι → FDRep K G)
    (hπ_pairwise : CategoryTheory.PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (hπ'_pairwise :
      CategoryTheory.PairwiseNonisomorphic
        (fun i ↦ ((FDRep.scalarExtension (π i) : FDRep K' G))))
    (hπ'_complete :
      IsCompleteIrreducibleFamily (fun i ↦ ((FDRep.scalarExtension (π i) : FDRep K' G)))) :
    ∃ r : R₀[K'](G) →+ R₀[K](G),
      (finiteRepGrothendieckScalarExtensionHom K K' G).comp r = AddMonoidHom.id _ ∧
        Function.Injective (finiteRepGrothendieckScalarExtensionHom K K' G) := by
  classical
  -- Build the two simple-class bases and define the inverse by sending the transported basis
  -- vector back to its source basis vector.
  let b : Module.Basis ι ℤ (R₀[K](G)) :=
    simple_finiteRep_classes_basis_of_complete_family π hπ_pairwise hπ_complete
  let b' : Module.Basis ι ℤ (R₀[K'](G)) :=
    simple_finiteRep_classes_basis_of_complete_family
      (fun i ↦ ((FDRep.scalarExtension (π i) : FDRep K' G))) hπ'_pairwise hπ'_complete
  let fL : R₀[K](G) →ₗ[ℤ] R₀[K'](G) :=
    (finiteRepGrothendieckScalarExtensionHom K K' G).toIntLinearMap
  let rL : R₀[K'](G) →ₗ[ℤ] R₀[K](G) := b'.constr ℤ b
  have hbasis_add : ∀ i,
      finiteRepGrothendieckScalarExtensionHom K K' G (b i) = b' i := by
    intro i
    -- On basis generators, scalar extension sends `[π i]₀` to the corresponding transported
    -- simple class over `K'`.
    rw [show b i = [π i]₀ by
      simp [b, simple_finiteRep_classes_basis_of_complete_family_apply]]
    rw [show b' i = [((FDRep.scalarExtension (π i) : FDRep K' G))]₀ by
      simp [b', simple_finiteRep_classes_basis_of_complete_family_apply]]
    rw [finiteRepGrothendieckScalarExtensionHom_class_eq]
  have hbasis : ∀ i, fL (b i) = b' i := by
    intro i
    simpa [fL] using hbasis_add i
  have hrightL : fL.comp rL = LinearMap.id := by
    -- The basis-defined inverse is a right inverse on every transported basis vector.
    apply b'.ext
    intro i
    simp [rL, hbasis i]
  have hleftL : rL.comp fL = LinearMap.id := by
    -- The same basis comparison also recovers source basis vectors, giving injectivity.
    apply b.ext
    intro i
    simp [rL, hbasis i]
  let r : R₀[K'](G) →+ R₀[K](G) := rL.toAddMonoidHom
  refine ⟨r, ?_, ?_⟩
  · -- Repackage the linear right-inverse identity as an additive-hom identity.
    apply AddMonoidHom.ext
    intro x
    have hright_apply :=
      congrArg (fun t : R₀[K'](G) →ₗ[ℤ] R₀[K'](G) ↦ t x) hrightL
    simpa [fL, r, LinearMap.comp_apply] using hright_apply
  · -- Injectivity follows by applying the linear left inverse to an equality after scalar
    -- extension.
    intro x y hxy
    have hleft_apply_x :=
      congrArg (fun t : R₀[K](G) →ₗ[ℤ] R₀[K](G) ↦ t x) hleftL
    have hleft_apply_y :=
      congrArg (fun t : R₀[K](G) →ₗ[ℤ] R₀[K](G) ↦ t y) hleftL
    calc
      x = rL (fL x) := by simpa [LinearMap.comp_apply] using hleft_apply_x.symm
      _ = rL (fL y) := by simpa [fL] using congrArg rL hxy
      _ = y := by simpa [LinearMap.comp_apply] using hleft_apply_y

omit [FiniteDimensional K K'] [Finite G] [Fact p.Prime] [CharP (IsLocalRing.ResidueField A) p]
    [IsLocalRing A] [HenselianLocalRing A] [Algebra A K] [IsFractionRing A K]
    [CharZero K] [Fact (R[K](G) = R̄[K](G))] in
/-- Helper for Theorem 16-16.2-2: basiswise transport of a complete simple family gives
surjectivity of ordinary scalar extension on Grothendieck groups. -/
private theorem finiteRepGrothendieckScalarExtension_surjective_of_complete_simple_family_current
    {ι : Type*}
    (π : ι → FDRep K G)
    (hπ_pairwise : CategoryTheory.PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (hπ'_pairwise :
      CategoryTheory.PairwiseNonisomorphic
        (fun i ↦ ((FDRep.scalarExtension (π i) : FDRep K' G))))
    (hπ'_complete :
      IsCompleteIrreducibleFamily (fun i ↦ ((FDRep.scalarExtension (π i) : FDRep K' G)))) :
    Function.Surjective
      (finiteRepGrothendieckScalarExtensionHom K K' G : R₀[K](G) →+ R₀[K'](G)) := by
  -- Consume the basiswise right inverse by evaluating it at the requested target class.
  rcases
    finiteRepGrothendieckScalarExtension_retract_data_of_complete_simple_family_current
      (K := K) (K' := K') (G := G)
      π hπ_pairwise hπ_complete hπ'_pairwise hπ'_complete with
    ⟨r, hr, _hr_injective⟩
  intro x
  refine ⟨r x, ?_⟩
  have hx :=
    congrArg (fun f : R₀[K'](G) →+ R₀[K'](G) ↦ f x) hr
  simpa [AddMonoidHom.comp_apply] using hx

omit [FiniteDimensional K K'] [Fact p.Prime] [CharP (IsLocalRing.ResidueField A) p]
    [IsLocalRing A] [HenselianLocalRing A] [Algebra A K] [IsFractionRing A K]
    [Finite G] in
/-- Helper for Theorem 16-16.2-2: choose representatives for simple finite-dimensional
representations over an arbitrary field. -/
private theorem exists_complete_pairwise_nonisomorphic_simple_family_over_field_current
    {F : Type u} [Field F] {H : Type u} [Group H] :
    ∃ (ι : Type (u + 1)) (π : ι → FDRep F H),
      CategoryTheory.PairwiseNonisomorphic π ∧ IsCompleteIrreducibleFamily π := by
  classical
  let SimpleRep : Type (u + 1) := { τ : FDRep F H // CategoryTheory.Simple τ }
  let r : Setoid SimpleRep :=
    { r := fun a b ↦ Nonempty (a.1 ≅ b.1)
      iseqv :=
        ⟨fun a ↦ ⟨CategoryTheory.Iso.refl _⟩,
          fun {a b} hab ↦ by
            rcases hab with ⟨e⟩
            exact ⟨e.symm⟩,
          fun {a b c} hab hbc ↦ by
            rcases hab with ⟨eab⟩
            rcases hbc with ⟨ebc⟩
            exact ⟨eab.trans ebc⟩⟩ }
  let ι : Type (u + 1) := Quotient r
  let π : ι → FDRep F H := fun q ↦ (Quotient.out q).1
  have hπ_pairwise : CategoryTheory.PairwiseNonisomorphic π := by
    intro q q' hqq' hIso
    rcases hIso with ⟨e⟩
    have hclasses : (⟦Quotient.out q⟧ : ι) = (⟦Quotient.out q'⟧ : ι) := by
      apply Quotient.sound
      exact ⟨e⟩
    apply hqq'
    calc
      q = (⟦Quotient.out q⟧ : ι) := (Quotient.out_eq q).symm
      _ = (⟦Quotient.out q'⟧ : ι) := hclasses
      _ = q' := Quotient.out_eq q'
  have hπ_complete : IsCompleteIrreducibleFamily π := by
    refine ⟨?_, ?_⟩
    · intro q
      exact (Quotient.out q).2
    · intro τ hτ
      let q : ι := ⟦⟨τ, hτ⟩⟧
      refine ⟨q, ?_⟩
      have hq : Nonempty (((Quotient.out q).1) ≅ τ) := by
        exact Quotient.exact (Quotient.out_eq q)
      rcases hq with ⟨e⟩
      exact ⟨e.symm⟩
  exact ⟨ι, π, hπ_pairwise, hπ_complete⟩

/-- Helper for Theorem 16-16.2-2: a `K`-valued virtual character over `K'` should descend to a
virtual representation over `K`. -/
private theorem finiteRepGrothendieckScalarExtensionHom_mem_range_of_isValuedInBaseField_character
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    (x : R₀[K'](G))
    (hx : IsValuedInBaseField K (finiteRepGrothendieckCharacter K' G x : G → K')) :
    x ∈ (finiteRepGrothendieckScalarExtensionHom K K' G : R₀[K](G) →+ R₀[K'](G)).range := by
  -- The `K`-valued character gives a coefficientwise preimage.  Since enough roots make `K[G]`
  -- quasisplit, that preimage is an honest virtual character, and character injectivity recovers
  -- the original Grothendieck class.
  classical
  have hquasi : R[K](G) = R̄[K](G) := by
    -- The quasisplit owner is exactly the character-ring equality needed for descent.
    exact Fact.out
  rw [isValuedInBaseField_iff_mem_pointwiseAlgebraMap_range] at hx
  rcases hx with ⟨χK, hχK_map⟩
  have hχK_overline : χK ∈ R̄[K](G) := by
    let ι : K' →ₐ[K] AlgebraicClosure K := IsAlgClosed.lift (R := K)
    letI : Algebra K' (AlgebraicClosure K) := ι.toAlgebra
    letI : IsScalarTower K K' (AlgebraicClosure K) :=
      IsScalarTower.of_algebraMap_eq fun a ↦ (ι.commutes a).symm
    let ιZ : K' →ₐ[ℤ] AlgebraicClosure K := ι.restrictScalars ℤ
    have hχ'_alg :
        (ιZ.compLeft G) (finiteRepGrothendieckCharacter K' G x : G → K') ∈
          R[AlgebraicClosure K](G) :=
      ProjectiveScalarExtensionSplitInjective.map_mem_characterRingOverField_local
        (G := G) (f := ιZ)
        (finiteRepGrothendieckCharacter K' G x : G → K')
        (finiteRepGrothendieckCharacter K' G x).2
    rw [mem_overlineCharacterRingInExtension_iff K (AlgebraicClosure K) χK]
    convert hχ'_alg using 1
    ext g
    have hg :
        algebraMap K K' (χK g) =
          (finiteRepGrothendieckCharacter K' G x : G → K') g :=
      congrFun hχK_map g
    calc
      algebraMap K (AlgebraicClosure K) (χK g) =
          algebraMap K' (AlgebraicClosure K) (algebraMap K K' (χK g)) := by
            exact IsScalarTower.algebraMap_apply K K' (AlgebraicClosure K) (χK g)
      _ = algebraMap K' (AlgebraicClosure K)
          ((finiteRepGrothendieckCharacter K' G x : G → K') g) := by rw [hg]
  have hχK_mem : χK ∈ R[K](G) := by
    simpa [hquasi] using hχK_overline
  let χ : R[K](G) := ⟨χK, hχK_mem⟩
  letI : CharZero K' := (RingHom.charZero_iff (algebraMap K K').injective).1 inferInstance
  obtain ⟨sK, hsK_comp, _hsK_left⟩ :=
    ProjectiveScalarExtensionSplitInjective.finiteRepGrothendieckCharacter_local_has_inverse
      (F := K) (G := G)
  let y : R₀[K](G) := sK χ
  refine ⟨y, ?_⟩
  apply (finiteRepGrothendieckCharacter_eq_iff_charZero_current (F := K') (H := G)).1
  have hychar_local :
      ProjectiveScalarExtensionSplitInjective.finiteRepGrothendieckCharacter_local
          (F := K) (G := G) y = χ := by
    -- The chosen section sends the base-field character back to a Grothendieck class with that
    -- same character.
    have hychar :=
      congrArg (fun f : R[K](G) →+ R[K](G) ↦ f χ) hsK_comp
    simpa [y, AddMonoidHom.comp_apply] using hychar
  have hychar : finiteRepGrothendieckCharacter K G y = χ := by
    rw [finiteRepGrothendieckCharacter_eq_local_current (F := K) (H := G) y]
    exact hychar_local
  ext g
  calc
    (finiteRepGrothendieckCharacter K' G
        ((finiteRepGrothendieckScalarExtensionHom K K' G) y) : G → K') g =
      algebraMap K K' ((finiteRepGrothendieckCharacter K G y : G → K) g) := by
        exact finiteRepGrothendieckCharacter_scalarExtensionHom_apply
          (K := K) (K' := K') y g
    _ = algebraMap K K' ((χ : G → K) g) := by
        exact congrArg (fun η : R[K](G) ↦ algebraMap K K' ((η : G → K) g)) hychar
    _ = (finiteRepGrothendieckCharacter K' G x : G → K') g := by
        simpa [χ] using congrFun hχK_map g

omit [FiniteDimensional K K'] [Fact p.Prime] [CharP (IsLocalRing.ResidueField A) p]
    [IsLocalRing A] [HenselianLocalRing A] [Algebra A K] [IsFractionRing A K]
    [Finite G] [CharZero K] [Fact (R[K](G) = R̄[K](G))] in
/-- Helper for Theorem 16-16.2-2: the ordinary Grothendieck group over a splitting field has no
nonzero natural torsion. -/
private theorem finiteRepGrothendieckClass_eq_zero_of_nsmul_eq_zero_current
    {N : ℕ} (hN : N ≠ 0) {x : R₀[K](G)} (hx : N • x = 0) : x = 0 := by
  classical
  -- Choose the simple-class basis and read the torsion equation in each integral coordinate.
  obtain ⟨ι, π, hπ_pairwise, hπ_complete⟩ :=
    exists_complete_pairwise_nonisomorphic_simple_family_over_field_current
      (F := K) (H := G)
  let b : Module.Basis ι ℤ (R₀[K](G)) :=
    simple_finiteRep_classes_basis_of_complete_family π hπ_pairwise hπ_complete
  -- The basis coordinates live in `ℤ`; multiplication by a nonzero natural is injective there.
  apply b.repr.injective
  ext i
  have hcoeff := congrArg (fun y : R₀[K](G) => b.repr y i) hx
  have hcoeff' : N • (b.repr x) i = 0 := by
    calc
      N • (b.repr x) i = (N • b.repr x) i := by
        simp
      _ = (b.repr (N • x)) i := by
        rw [map_nsmul]
      _ = 0 := by
        simpa using hcoeff
  simpa using (nsmul_eq_zero_iff_right hN).1 hcoeff'

omit [Fact p.Prime] in
/-- Helper for Theorem 16-16.2-2: the fraction field has either characteristic zero or the same
prime characteristic as the residue field. -/
private theorem charZero_or_charP_fraction_field_current
    (A : Type u) [CommRing A] [IsLocalRing A] [Algebra A K] [IsFractionRing A K]
    [CharP (IsLocalRing.ResidueField A) p] :
    CharZero K ∨ CharP K p := by
  -- In the theorem-local context the fraction field is characteristic zero.
  left
  infer_instance

omit [Fact p.Prime] [Fact (R[K](G) = R̄[K](G))] in
/-- Helper for Theorem 16-16.2-2: enough roots force either characteristic zero or group order
prime to the residue characteristic. -/
private theorem charZero_or_order_prime_to_p_of_hasEnoughRoots_fractionField_current
    (A : Type u) [CommRing A] [IsLocalRing A] [Algebra A K] [IsFractionRing A K]
    [CharP (IsLocalRing.ResidueField A) p]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)] :
    CharZero K ∨ ¬ p ∣ Nat.card G := by
  -- In equal characteristic `p`, divisibility of `|G|` by `p` would make `|G|` vanish in `K`,
  -- contradicting the enough-roots nonvanishing lemma.
  rcases charZero_or_charP_fraction_field_current
      (A := A) (K := K) (p := p) with hchar0 | hcharp
  · exact Or.inl hchar0
  · right
    intro hpdiv
    letI : CharP K p := hcharp
    have hcard_zero : (Nat.card G : K) = 0 :=
      (CharP.cast_eq_zero_iff K p (Nat.card G)).2 hpdiv
    exact
      ProjectiveScalarExtensionSplitInjective.nat_card_ne_zero_of_hasEnoughRoots_local
        (K := K) (L := K) (G := G) hcard_zero

/-- Helper for Theorem 16-16.2-2: if `p` does not divide the group order, every group element is
`p`-regular. -/
private theorem isPRegular_of_not_dvd_natCard_current
    (hG : ¬ p ∣ Nat.card G) (g : G) :
    IsPRegular p g := by
  -- The order of an element divides the order of the finite group, so `p` cannot divide it.
  rw [isPRegular_iff_not_dvd_orderOf (p := p) g]
  intro hporder
  letI : Fintype G := Fintype.ofFinite G
  have horder_card : orderOf g ∣ Nat.card G := by
    simpa [Nat.card_eq_fintype_card] using (orderOf_dvd_card (x := g))
  exact hG (dvd_trans hporder horder_card)

/-- Helper for Theorem 16-16.2-2: under the prime-to-`p` group-order hypothesis, a claimed
`p`-singular element gives a contradiction. -/
private theorem not_isPRegular_false_of_not_dvd_natCard_current
    (hG : ¬ p ∣ Nat.card G) {g : G} (hg : ¬ IsPRegular p g) : False := by
  -- Convert the global prime-to-`p` hypothesis into pointwise `p`-regularity and contradict
  -- the supplied singularity witness.
  exact hg (isPRegular_of_not_dvd_natCard_current (G := G) (p := p) hG g)

omit [IsDiscreteValuationRing A] [Fact (R[K](G) = R̄[K](G))] in
/-- Helper for Theorem 16-16.2-2: base-field projective scalar-extension criterion under the
target hypotheses. -/
private theorem baseFieldProjectiveScalarExtensionCriterion_current
    [hDVR : IsDiscreteValuationRing A]
    [IsNoetherianRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    (y : R₀[K](G)) :
    y ∈ (projectiveGrothendieckScalarExtensionHom A K : P_k(G) →+ R₀[K](G)).range ↔
      ∀ g : G, ¬ IsPRegular p g →
        (finiteRepGrothendieckCharacter K G y : G → K) g = 0 := by
  -- The imported Chapter `16` criterion supplies this base-field case; the current context
  -- already has the required modular-system instances available by typeclass search.
  letI : IsDomain A := isDomain_of_isFractionRing_field_current A K
  exact
    mem_projectiveGrothendieckScalarExtension_range_iff_character_eq_zero_on_pSingular
      (A := A) (K := K) (G := G) (p := p) y

omit [FiniteDimensional K K'] [Fact p.Prime] [CharZero K]
    [Fact (R[K](G) = R̄[K](G))] in
/-- Helper for Theorem 16-16.2-2: vanishing of the scalar-extended character pulls back through
the injective coefficient map. -/
private theorem zeroOnPSingular_of_scalarExtensionHom_eq
    {y : R₀[K](G)} {x : R₀[K'](G)}
    (hxy : finiteRepGrothendieckScalarExtensionHom K K' G y = x)
    (hxzero :
      ∀ g : G, ¬ IsPRegular p g →
        (finiteRepGrothendieckCharacter K' G x : G → K') g = 0) :
    ∀ g : G, ¬ IsPRegular p g →
      (finiteRepGrothendieckCharacter K G y : G → K) g = 0 := by
  intro g hg
  -- Map the desired equality to `K'`, use character compatibility, then descend by injectivity.
  apply (algebraMap K K').injective
  calc
    algebraMap K K' ((finiteRepGrothendieckCharacter K G y : G → K) g)
        =
      (finiteRepGrothendieckCharacter K' G
        ((finiteRepGrothendieckScalarExtensionHom K K' G) y) : G → K') g := by
        exact (finiteRepGrothendieckCharacter_scalarExtensionHom_apply
          (K := K) (K' := K') y g).symm
    _ = (finiteRepGrothendieckCharacter K' G x : G → K') g := by
        rw [hxy]
    _ = algebraMap K K' 0 := by rw [hxzero g hg, map_zero]

omit [IsDiscreteValuationRing A] [Fact (R[K](G) = R̄[K](G))] in
/-- Helper for Theorem 16-16.2-2: the forward direction of the projective scalar-extension
criterion over the base field, stated with the hypotheses available in this item. -/
private theorem character_eq_zero_on_pSingular_of_mem_projectiveScalarExtension_range_current
    [hDVR : IsDiscreteValuationRing A]
    [IsNoetherianRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    {y : R₀[K](G)}
    (hy :
      y ∈ (projectiveGrothendieckScalarExtensionHom A K : P_k(G) →+ R₀[K](G)).range) :
    ∀ g : G, ¬ IsPRegular p g →
      (finiteRepGrothendieckCharacter K G y : G → K) g = 0 := by
  -- The local trace/Swan expansion is now delegated to the theorem-local base-field criterion.
  exact (baseFieldProjectiveScalarExtensionCriterion_current y).1 hy

omit [IsDiscreteValuationRing A] [Fact (R[K](G) = R̄[K](G))] in
/-- Helper for Theorem 16-16.2-2: when `p` is prime to the group order, every ordinary
Grothendieck class is represented by scalar extension of a residue-field projective class. -/
private theorem projectiveGrothendieckScalarExtensionHom_surjective_of_not_dvd_natCard_current
    [hDVR : IsDiscreteValuationRing A]
    [IsNoetherianRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    (hG : ¬ p ∣ Nat.card G) :
    Function.Surjective
      (projectiveGrothendieckScalarExtensionHom A K : P_k(G) →+ R₀[K](G)) := by
  -- If `p` does not divide `|G|`, there are no `p`-singular elements, so the base-field
  -- criterion makes the projective scalar-extension map onto.
  intro y
  refine
    (baseFieldProjectiveScalarExtensionCriterion_current y).2 ?_
  intro g hg
  exact (not_isPRegular_false_of_not_dvd_natCard_current (G := G) (p := p) hG hg).elim

omit [IsDiscreteValuationRing A] [CharZero K] [Fact (R[K](G) = R̄[K](G))] in
/-- Helper for Theorem 16-16.2-2: the base-field criterion turns vanishing on `p`-singular
elements into membership in the projective scalar-extension range. -/
private theorem
    mem_projectiveScalarExtension_range_of_character_eq_zero_on_pSingular_baseCriterion_current
    [hDVR : IsDiscreteValuationRing A]
    [IsNoetherianRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [hCharZero : CharZero K]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    {y : R₀[K](G)}
    (hyzero :
      ∀ g : G, ¬ IsPRegular p g →
        (finiteRepGrothendieckCharacter K G y : G → K) g = 0) :
    y ∈ (projectiveGrothendieckScalarExtensionHom A K : P_k(G) →+ R₀[K](G)).range := by
  -- The Cartan/decomposition argument is exactly the reverse direction of the theorem-local
  -- base-field criterion.
  exact
    (baseFieldProjectiveScalarExtensionCriterion_current y).2 hyzero

omit [Fact (R[K](G) = R̄[K](G))] in
/-- Helper for Theorem 16-16.2-2: the reverse direction of the projective scalar-extension
criterion over the base field, stated with the hypotheses available in this item. -/
private theorem mem_projectiveScalarExtension_range_of_character_eq_zero_on_pSingular_current
    [IsNoetherianRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    {y : R₀[K](G)}
    (hyzero :
      ∀ g : G, ¬ IsPRegular p g →
        (finiteRepGrothendieckCharacter K G y : G → K) g = 0) :
    y ∈ (projectiveGrothendieckScalarExtensionHom A K : P_k(G) →+ R₀[K](G)).range := by
  -- Split off the equal-characteristic prime-to-`p` branch and the characteristic-zero branch,
  -- matching the target-local forward proof above.
  rcases
      charZero_or_order_prime_to_p_of_hasEnoughRoots_fractionField_current
        (A := A) (K := K) (G := G) (p := p) with
    hchar0 | hprimeToP
  · letI : CharZero K := hchar0
    exact
      mem_projectiveScalarExtension_range_of_character_eq_zero_on_pSingular_baseCriterion_current
        hyzero
  · exact
      projectiveGrothendieckScalarExtensionHom_surjective_of_not_dvd_natCard_current
        hprimeToP y

omit [Fact (R[K](G) = R̄[K](G))] in
/-- Helper for Theorem 16-16.2-2: the base-field projective scalar-extension criterion, stated
with the hypotheses available in this item. -/
private theorem
    mem_projectiveGrothendieckScalarExtension_range_iff_character_eq_zero_on_pSingular_current
    [IsNoetherianRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    (y : R₀[K](G)) :
    y ∈ (projectiveGrothendieckScalarExtensionHom A K : P_k(G) →+ R₀[K](G)).range ↔
      ∀ g : G, ¬ IsPRegular p g →
        (finiteRepGrothendieckCharacter K G y : G → K) g = 0 := by
  exact baseFieldProjectiveScalarExtensionCriterion_current y

omit [FiniteDimensional K K'] [Fact (R[K](G) = R̄[K](G))] in
/-- Helper for Theorem 16-16.2-2: membership in the composite projective scalar-extension image
forces the finite-extension character to be base-valued and zero on `p`-singular elements. -/
private theorem characterCriterion_of_mem_projectiveScalarExtensionOverExtension_range_current
    [IsNoetherianRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    {x : R₀[K'](G)}
    (hx :
      x ∈ ((finiteRepGrothendieckScalarExtensionHom K K' G).comp
        (projectiveGrothendieckScalarExtensionHom A K) : P_k(G) →+ R₀[K'](G)).range) :
    IsValuedInBaseField K (finiteRepGrothendieckCharacter K' G x) ∧
      ∀ g : G, ¬ IsPRegular p g → finiteRepGrothendieckCharacter K' G x g = 0 := by
  rcases hx with ⟨z, hz⟩
  let y : R₀[K](G) := projectiveGrothendieckScalarExtensionHom A K z
  have hxy : finiteRepGrothendieckScalarExtensionHom K K' G y = x := by
    simpa [y, AddMonoidHom.comp_apply] using hz
  constructor
  · -- Scalar-extension compatibility makes the character visibly `K`-valued.
    simpa [hxy] using
      isValuedInBaseField_finiteRepGrothendieckCharacter_scalarExtensionHom
        (K := K) (K' := K') (G := G) y
  · intro g hg
    have hy_range :
        y ∈ (projectiveGrothendieckScalarExtensionHom A K : P_k(G) →+ R₀[K](G)).range :=
      ⟨z, rfl⟩
    have hyzero :
        ∀ g : G, ¬ IsPRegular p g →
          (finiteRepGrothendieckCharacter K G y : G → K) g = 0 :=
      character_eq_zero_on_pSingular_of_mem_projectiveScalarExtension_range_current hy_range
    -- The base theorem gives vanishing over `K`; map that zero through `K → K'`.
    calc
      (finiteRepGrothendieckCharacter K' G x : G → K') g =
          (finiteRepGrothendieckCharacter K' G
            ((finiteRepGrothendieckScalarExtensionHom K K' G) y) : G → K') g := by
            rw [hxy]
      _ = algebraMap K K' ((finiteRepGrothendieckCharacter K G y : G → K) g) := by
            exact finiteRepGrothendieckCharacter_scalarExtensionHom_apply
              (K := K) (K' := K') y g
      _ = 0 := by rw [hyzero g hg, map_zero]

/- Domain-style sampling for Theorem 16-16.2-2:
* primary domain: modular representation theory on Grothendieck groups, combining Serre's
  projective scalar-extension map over a finite extension field with ordinary characters;
* relevant owner declarations inspected in this domain:
  `projectiveGrothendieckScalarExtensionHom`,
  `finiteRepGrothendieckScalarExtensionHom`,
  `finiteRepGrothendieckCharacter`,
  `IsValuedInBaseField`;
* best owner abstraction: the existing Chapter `15` and `16` scalar-extension owners on
  Grothendieck groups, namely
  `(finiteRepGrothendieckScalarExtensionHom K K' G).comp
    (projectiveGrothendieckScalarExtensionHom A K)`,
  together with the Chapter `16` character bridge and the Chapter `12` `K`-valuedness predicate
  on class functions;
* source/core/bridge triage:
  source-facing: the image criterion over the finite extension `K' / K`;
  core/canonical: `projectiveGrothendieckScalarExtensionHom A K`,
    `finiteRepGrothendieckScalarExtensionHom K K' G`,
    `finiteRepGrothendieckCharacter K' G`, and `IsValuedInBaseField K`;
  bridge/view: this theorem, which characterizes the range of the canonical composite of those
    scalar-extension owners by a base-field-valuedness condition plus vanishing on `p`-singular
    elements.

Primitive data vs derived API:
* primitive data: the canonical composite
  `(finiteRepGrothendieckScalarExtensionHom K K' G).comp
    (projectiveGrothendieckScalarExtensionHom A K)`;
* derived API: the character-theoretic criterion for membership in its range.
This file should therefore reuse those upstream owners directly and avoid introducing a parallel
public map declaration for their composite.
-/

-- Proof sketch: if `x` lies in the image of the finite-extension scalar-extension map
-- `P_k(G) → R_K'(G)`, then it comes by extension of scalars from a projective class over `K`, so
-- its ordinary character is the scalar extension of a `K`-valued character, so it is
-- `Representation.IsValuedInBaseField K`; Theorem `16-16.2-1` gives vanishing on `p`-singular
-- elements. Conversely, if the character of `x` is `K`-valued and vanishes on `p`-singular
-- elements, descend `x` to a class in `R_K(G)` and apply Theorem `16-16.2-1`, then re-extend
-- scalars to recover `x`.
/-- Theorem 16-16.2-2: for a finite extension `K' / K`, an element of `R_K'(G)` lies in the image
of the projective scalar-extension homomorphism `e : P_k(G) → R_K'(G)` exactly when its ordinary
character is `K`-valued and vanishes on every `p`-singular element of `G`. Here
`k = IsLocalRing.ResidueField A`. -/
theorem mem_projectiveScalarExtensionOverExtension_range_iff_valuedInBaseField_zero_on_pSingular
    [IsNoetherianRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    (x : R₀[K'](G)) :
    x ∈ ((finiteRepGrothendieckScalarExtensionHom K K' G).comp
      (projectiveGrothendieckScalarExtensionHom A K) : P_k(G) →+ R₀[K'](G)).range ↔
      IsValuedInBaseField K (finiteRepGrothendieckCharacter K' G x) ∧
      ∀ g : G, ¬ IsPRegular p g → finiteRepGrothendieckCharacter K' G x g = 0 := by
  constructor
  · intro hx
    -- The forward helper packages descent to the base projective criterion and scalar-extension
    -- character compatibility.
    exact
      characterCriterion_of_mem_projectiveScalarExtensionOverExtension_range_current
        (A := A) (K := K) (K' := K') (G := G) (p := p) hx
  · rintro ⟨hxvalued, hxzero⟩
    obtain ⟨y, hxy⟩ :=
      finiteRepGrothendieckScalarExtensionHom_mem_range_of_isValuedInBaseField_character
        (K := K) (K' := K') (G := G) x hxvalued
    have hyzero :
        ∀ g : G, ¬ IsPRegular p g →
          (finiteRepGrothendieckCharacter K G y : G → K) g = 0 :=
      zeroOnPSingular_of_scalarExtensionHom_eq
        (K := K) (K' := K') (G := G) (p := p) hxy hxzero
    have hy_range :
        y ∈ (projectiveGrothendieckScalarExtensionHom A K : P_k(G) →+ R₀[K](G)).range :=
      mem_projectiveScalarExtension_range_of_character_eq_zero_on_pSingular_current
        (A := A) (K := K) (G := G) (p := p) hyzero
    rcases hy_range with ⟨z, hz⟩
    refine ⟨z, ?_⟩
    -- Reassemble the two scalar-extension steps into the composite range witness.
    change
      finiteRepGrothendieckScalarExtensionHom K K' G
        ((projectiveGrothendieckScalarExtensionHom A K) z) = x
    rw [hz]
    exact hxy

end

end Representation
