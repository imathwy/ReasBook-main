import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap02.Proposition_2_2_1_1
import LinearRepresentations_Serre_1977.Serre.Chap03.Theorem_3_3_2_1
import LinearRepresentations_Serre_1977.Serre.Chap12.Proposition_12_12_1_1
import LinearRepresentations_Serre_1977.Serre.Chap12.Proposition_12_12_1_3
import LinearRepresentations_Serre_1977.Serre.Chap12.Proposition_12_12_2_1.ScaledCharacterCore
import LinearRepresentations_Serre_1977.Serre.Chap12.Exercise_12_12_2_6.CharacterBasisCoefficients
import LinearRepresentations_Serre_1977.Serre.Chap14.Remark_14_14_1_2
import LinearRepresentations_Serre_1977.Serre.Chap15.Definition_15_15_3_1
import LinearRepresentations_Serre_1977.Serre.Chap15.Definition_15_15_3_1.FiniteRepScalarExtension
import LinearRepresentations_Serre_1977.Serre.Chap16.Theorem_16_16_1_2
import LinearRepresentations_Serre_1977.Serre.Chap16.Corollary_16_16_1_3.CharacterDescent
import LinearRepresentations_Serre_1977.Serre.Chap16.Corollary_16_16_1_3.GrothendieckCharacter

noncomputable section

open CategoryTheory
open scoped Representation TensorProduct

universe u

namespace Representation
open ProjectiveScalarExtensionSplitInjective

section

variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {K' : Type u} [Field K'] [Algebra K K'] [FiniteDimensional K K']
variable {G : Type u} [Group G] [Finite G]

local notation "k" => IsLocalRing.ResidueField A
local notation:max "P_k(" G ")" => finiteProjectiveGroupAlgebraGrothendieckGroup k G

private instance fdRep_restrictScalars_module_local (τ : FDRep K' G) : Module K τ.V :=
  Module.compHom τ.V (algebraMap K K')

private instance fdRep_restrictScalars_isScalarTower_local (τ : FDRep K' G) :
    IsScalarTower K K' τ.V :=
  IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl

omit [Finite G] in
/-- Helper for Corollary 16-16.1-3: over any field, one can choose one representative of each
isomorphism class of simple finite-dimensional `G`-representations. -/
private theorem exists_complete_pairwise_nonisomorphic_simple_family_over_field_local
    {F : Type u} [Field F] :
    ∃ (ι : Type (u + 1)) (π : ι → FDRep F G),
      PairwiseNonisomorphic π ∧ IsCompleteIrreducibleFamily π := by
  classical
  let SimpleRep : Type (u + 1) := { τ : FDRep F G // CategoryTheory.Simple τ }
  let r : Setoid SimpleRep :=
    { r := fun a b ↦ Nonempty (a.1 ≅ b.1)
      iseqv :=
        ⟨fun a ↦ ⟨Iso.refl _⟩,
          fun {a b} hab ↦ by
            rcases hab with ⟨e⟩
            exact ⟨e.symm⟩,
          fun {a b c} hab hbc ↦ by
            rcases hab with ⟨eab⟩
            rcases hbc with ⟨ebc⟩
            exact ⟨eab.trans ebc⟩⟩ }
  let ι : Type (u + 1) := Quotient r
  let π : ι → FDRep F G := fun q ↦ (Quotient.out q).1
  have hπ_pairwise : PairwiseNonisomorphic π := by
    -- Isomorphic representatives define the same quotient class, so distinct classes stay
    -- pairwise nonisomorphic.
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

omit [Finite G] in
/-- Helper for Corollary 16-16.1-3: the live file already provides a complete pairwise
nonisomorphic simple family over the specific base field `K`. -/
private theorem existsCompleteSimpleFamilyOverBaseField_local :
    ∃ (ι : Type (u + 1)) (π : ι → FDRep K G),
      PairwiseNonisomorphic π ∧ IsCompleteIrreducibleFamily π := by
  -- This is the current-base-field specialization of the generic family-existence owner above.
  exact exists_complete_pairwise_nonisomorphic_simple_family_over_field_local

/-
Avoid carrying unused section variables into theorem signatures that only package linear-algebraic
retract data.
-/
omit [FiniteDimensional K K'] [Finite G] in
/-- Helper for Corollary 16-16.1-3: if one already has a complete simple `K[G]`-family whose
scalar extension to `K'` stays pairwise nonisomorphic and complete, the `R₀` scalar-extension map
inherits the required retract data immediately. -/
private theorem finiteRepGrothendieckScalarExtension_retract_data_of_exists_complete_family_local
    (h :
      ∃ (ι : Type (u + 1)) (π : ι → FDRep K G),
        PairwiseNonisomorphic π ∧
          IsCompleteIrreducibleFamily π ∧
            PairwiseNonisomorphic
              (fun i ↦ ((FDRep.scalarExtension (π i) : FDRep K' G))) ∧
              IsCompleteIrreducibleFamily
                (fun i ↦ ((FDRep.scalarExtension (π i) : FDRep K' G)))) :
    ∃ r : R₀[K'](G) →+ R₀[K](G),
      (finiteRepGrothendieckScalarExtensionHom K K' G).comp r = AddMonoidHom.id _ ∧
        Function.Injective (finiteRepGrothendieckScalarExtensionHom K K' G) := by
  rcases h with ⟨ι, π, hπ_pairwise, hπ_complete, hπ'_pairwise, hπ'_complete⟩
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
    -- Scalar extension transports the simple basis class `[π i]₀` to the matching simple class.
    rw [show b i = [π i]₀ by
      simp [b, simple_finiteRep_classes_basis_of_complete_family_apply]]
    rw [show b' i = [((FDRep.scalarExtension (π i) : FDRep K' G))]₀ by
      simp [b', simple_finiteRep_classes_basis_of_complete_family_apply]]
    rw [finiteRepGrothendieckScalarExtensionHom_class_eq]
  have hbasis : ∀ i, fL (b i) = b' i := by
    intro i
    simpa [fL] using hbasis_add i
  have hrightL : fL.comp rL = LinearMap.id := by
    -- On the target simple basis, the basis reconstruction map is a right inverse to extension.
    apply b'.ext
    intro i
    simp [rL, hbasis i]
  have hleftL : rL.comp fL = LinearMap.id := by
    -- The same basis comparison gives a left inverse on the source simple basis.
    apply b.ext
    intro i
    simp [rL, hbasis i]
  let r : R₀[K'](G) →+ R₀[K](G) := rL.toAddMonoidHom
  refine ⟨r, ?_, ?_⟩
  · apply AddMonoidHom.ext
    intro x
    have hright_apply :=
      congrArg (fun t : R₀[K'](G) →ₗ[ℤ] R₀[K'](G) ↦ t x) hrightL
    simpa [fL, r, LinearMap.comp_apply] using hright_apply
  · intro x y hxy
    have hleft_apply_x :=
      congrArg (fun t : R₀[K](G) →ₗ[ℤ] R₀[K](G) ↦ t x) hleftL
    have hleft_apply_y :=
      congrArg (fun t : R₀[K](G) →ₗ[ℤ] R₀[K](G) ↦ t y) hleftL
    calc
      x = rL (fL x) := by simpa [LinearMap.comp_apply] using hleft_apply_x.symm
      _ = rL (fL y) := by simpa [fL] using congrArg rL hxy
      _ = y := by simpa [LinearMap.comp_apply] using hleft_apply_y

omit [FiniteDimensional K K'] in
/-- Helper for Corollary 16-16.1-3: the remaining source-faithful Chapter `12/16` owner is the
retract data for ordinary scalar extension `R₀[K](G) → R₀[K'](G)`. -/
private theorem scalarExtension_character_eq_of_iso_local
    {ι : Type (u + 1)}
    (π : ι → FDRep K G)
    {i j : ι}
    (hIso :
      Nonempty (((FDRep.scalarExtension (π i) : FDRep K' G)) ≅
        ((FDRep.scalarExtension (π j) : FDRep K' G)))) :
    (π i).character = (π j).character := by
  rcases hIso with ⟨e⟩
  have hchar_i :
      (Representation.scalarExtension (π i).ρ).character =
        fun g ↦ algebraMap K K' ((π i).character g) :=
    scalarExtension_character_eq_map_local (π i).ρ
  have hchar_j :
      (Representation.scalarExtension (π j).ρ).character =
        fun g ↦ algebraMap K K' ((π j).character g) :=
    scalarExtension_character_eq_map_local (π j).ρ
  -- Compare the scalar-extension characters with the coefficientwise image of the source
  -- characters and then descend through injectivity of `K → K'`.
  ext g
  apply (algebraMap K K').injective
  calc
    algebraMap K K' ((π i).character g) =
        ((FDRep.scalarExtension (π i) : FDRep K' G)).character g := by
          simpa [FDRep.scalarExtension] using (congrFun hchar_i g).symm
    _ = ((FDRep.scalarExtension (π j) : FDRep K' G)).character g := by
          simpa using congrFun (FDRep.char_iso e) g
    _ = algebraMap K K' ((π j).character g) := by
          simpa [FDRep.scalarExtension] using congrFun hchar_j g

omit [FiniteDimensional K K'] in
/-- Helper for Corollary 16-16.1-3: under enough roots of unity, scalar extension preserves the
pairwise nonisomorphism of a complete simple `K[G]`-family. -/
private theorem scalarExtension_pairwise_nonisomorphic_of_hasEnoughRoots_local
    {ι : Type (u + 1)}
    (π : ι → FDRep K G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    [CharZero K]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)] :
    PairwiseNonisomorphic
      (fun i ↦ ((FDRep.scalarExtension (π i) : FDRep K' G))) := by
  intro i j hij hIso
  letI : NeZero (Nat.card G : K) :=
    @ProjectiveScalarExtensionSplitInjective.nat_card_neZero_of_hasEnoughRoots_local
      K _ G _ _ K _ (by infer_instance) (by infer_instance)
  have hcard_ne : (Nat.card G : K) ≠ 0 := NeZero.ne _
  letI : Invertible (Nat.card G : K) := invertibleOfNonzero hcard_ne
  letI : Simple (π i) := hπ_complete.isSimple i
  letI : Simple (π j) := hπ_complete.isSimple j
  have hchar :
      (π i).character = (π j).character :=
    scalarExtension_character_eq_of_iso_local
      (K := K) (K' := K') (G := G) (π := π) (i := i) (j := j) hIso
  have horth :
      Pairwise fun i j ↦ ⟪(π i).character, (π j).character⟫ = (0 : K) :=
    irreducible_characters_pairwise_orthogonal_of_pairwise_nonisomorphic
      K π hπ_complete.isSimple hπ_pairwise
  have hself_ne :
      ⟪(π i).character, (π i).character⟫ ≠ (0 : K) :=
    groupFunctionPairingOverField_character_self_ne_zero (π i)
  have hself_zero :
      ⟪(π i).character, (π i).character⟫ = (0 : K) := by
    simpa [hchar] using horth hij
  exact (hself_ne hself_zero).elim

omit [Finite G] in
/-- Helper for Corollary 16-16.1-3: scalar extension acts on pure tensors by applying the
source representation to the module factor. -/
private theorem scalarExtension_apply_tmul_of_field_extension_local
    {F : Type u} [Field F]
    {E : Type u} [Field E] [Algebra F E]
    {V : Type u} [AddCommGroup V] [Module F V]
    (ρ : Representation F G V) (g : G) (a : E) (x : V) :
    (Representation.scalarExtension ρ : Representation E G (E ⊗[F] V)) g (a ⊗ₜ[F] x) =
      a ⊗ₜ[F] (ρ g x) := by
  change ((Module.End.baseChangeHom F E V) (ρ g)) (a ⊗ₜ[F] x) =
    a ⊗ₜ[F] (ρ g x)
  exact LinearMap.baseChange_tmul (ρ g) a x

omit [FiniteDimensional K K'] [Finite G] in
/-- Helper for Corollary 16-16.1-3: a representation equivalence survives scalar extension. -/
private theorem scalarExtension_equiv_of_equiv_local
    {V : Type u} [AddCommGroup V] [Module K V]
    {W : Type u} [AddCommGroup W] [Module K W]
    {ρ : Representation K G V} {σ : Representation K G W}
    (e : Representation.Equiv ρ σ) :
    Nonempty
      ((Representation.scalarExtension ρ : Representation K' G (K' ⊗[K] V)).Equiv
        (Representation.scalarExtension σ : Representation K' G (K' ⊗[K] W))) := by
  let eK : K' ⊗[K] V ≃ₗ[K'] K' ⊗[K] W :=
    e.toLinearEquiv.baseChange K K' V W
  refine ⟨Representation.Equiv.mk eK ?_⟩
  intro g
  apply TensorProduct.AlgebraTensorModule.ext
  intro a x
  have hgx := LinearMap.congr_fun (e.isIntertwining' g) x
  simpa [Representation.scalarExtension] using congrArg (fun y ↦ a ⊗ₜ[K] y) hgx

omit [FiniteDimensional K K'] [Finite G] in
/-- Helper for Corollary 16-16.1-3: an `FDRep` isomorphism survives scalar extension. -/
private theorem scalarExtension_nonempty_iso_of_nonempty_iso_local
    {X Y : FDRep K G} (h : Nonempty (X ≅ Y)) :
    Nonempty ((FDRep.scalarExtension X : FDRep K' G) ≅
      (FDRep.scalarExtension Y : FDRep K' G)) := by
  rcases h with ⟨e⟩
  let eRep : Representation.Equiv X.ρ Y.ρ :=
    Representation.equivOfIso ((forget₂ (FDRep K G) (Rep K G)).mapIso e)
  have hExt :
      Nonempty
        ((Representation.scalarExtension X.ρ : Representation K' G (K' ⊗[K] X.V)).Equiv
          (Representation.scalarExtension Y.ρ : Representation K' G (K' ⊗[K] Y.V))) :=
    scalarExtension_equiv_of_equiv_local eRep
  rcases hExt with ⟨eExt⟩
  exact ⟨by simpa [FDRep.scalarExtension] using eExt.toFDRepIso⟩

/-- Helper for Corollary 16-16.1-3: the scalar extension of a restricted subrepresentation maps
canonically and equivariantly into the original `K'`-representation. -/
private noncomputable def scalarExtensionSubrepresentationHom_local
    (τ : FDRep K' G)
    (S : Subrepresentation (Representation.restrictScalars K τ.ρ))
    [Module.Finite K S.toSubmodule] :
    (FDRep.scalarExtension (FDRep.of S.toRepresentation) : FDRep K' G) ⟶ τ := by
  let l : S.toSubmodule →ₗ[K] τ := S.toSubmodule.subtype
  let f : K' ⊗[K] S.toSubmodule →ₗ[K'] τ := l.liftBaseChange K'
  let source : FDRep K' G :=
    (FDRep.scalarExtension (FDRep.of S.toRepresentation) : FDRep K' G)
  let fRep : ((forget₂ (FDRep K' G) (Rep K' G)).obj source ⟶
      (forget₂ (FDRep K' G) (Rep K' G)).obj τ) :=
    Rep.ofHom ⟨f, ?_⟩
  · exact (FDRep.forget₂HomLinearEquiv source τ) fRep
  · intro g
    ext z
    change f ((Representation.scalarExtension S.toRepresentation : Representation K' G
        (K' ⊗[K] S.toSubmodule)) g z) =
      τ.ρ g (f z)
    refine TensorProduct.induction_on z ?_ ?_ ?_
    · simp
    · intro a x
      rw [scalarExtension_apply_tmul_of_field_extension_local]
      rw [LinearMap.liftBaseChange_tmul, LinearMap.liftBaseChange_tmul]
      change a • (((S.toRepresentation) g x : S.toSubmodule) : τ) =
        τ.ρ g (a • (x : τ))
      have hxact :
          (((S.toRepresentation) g x : S.toSubmodule) : τ) = τ.ρ g (x : τ) := by
        rfl
      rw [hxact]
      exact ((τ.ρ g).map_smul a (x : τ)).symm
    · intro z₁ z₂ hz₁ hz₂
      simp [map_add, hz₁, hz₂]

omit [FiniteDimensional K K'] [Finite G] in
/-- Helper for Corollary 16-16.1-3: the canonical map from a nonzero restricted
subrepresentation remains nonzero after scalar extension. -/
private theorem scalarExtensionSubrepresentationHom_ne_zero_local
    (τ : FDRep K' G)
    (S : Subrepresentation (Representation.restrictScalars K τ.ρ))
    [Module.Finite K S.toSubmodule]
    (hS : S.toSubmodule ≠ ⊥) :
    scalarExtensionSubrepresentationHom_local τ S ≠ 0 := by
  classical
  letI : Nontrivial S.toSubmodule := (Submodule.nontrivial_iff_ne_bot).2 hS
  obtain ⟨x, hx⟩ := exists_ne (0 : S.toSubmodule)
  intro hzero
  have hxzero : ((x : S.toSubmodule) : τ) = 0 := by
    have hcongr :=
      congrArg
        (fun f :
          (FDRep.scalarExtension (FDRep.of S.toRepresentation) : FDRep K' G) ⟶ τ =>
            f.hom.hom (1 ⊗ₜ[K] x))
        hzero
    change (LinearMap.liftBaseChange K' S.toSubmodule.subtype) (1 ⊗ₜ[K] x) = 0 at hcongr
    simpa [LinearMap.liftBaseChange_tmul] using hcongr
  exact hx (Subtype.ext hxzero)

omit [FiniteDimensional K K'] in
/-- Helper for Corollary 16-16.1-3: coefficientwise scalar extension on ordinary character
rings. -/
private noncomputable def characterRingScalarExtensionHom_local :
    R[K](G) →+ R[K'](G) where
  toFun χ :=
    ⟨((IsScalarTower.toAlgHom ℤ K K').compLeft G) (χ : G → K),
      map_mem_characterRingOverField_local
        (IsScalarTower.toAlgHom ℤ K K') (χ : G → K) χ.2⟩
  map_zero' := by
    ext g
    simp
  map_add' χ ψ := by
    ext g
    simp

omit [FiniteDimensional K K'] in
/-- Helper for Corollary 16-16.1-3: coefficientwise scalar extension on ordinary character
rings is injective. -/
private theorem characterRingScalarExtensionHom_injective_local :
    Function.Injective (characterRingScalarExtensionHom_local : R[K](G) →+ R[K'](G)) := by
  intro χ ψ hχψ
  ext g
  apply (algebraMap K K').injective
  have hfun := congrArg (fun η : R[K'](G) ↦ (η : G → K')) hχψ
  exact congrFun hfun g

omit [FiniteDimensional K K'] in
/-- Helper for Corollary 16-16.1-3: the Grothendieck character map commutes with scalar
extension. -/
private theorem finiteRepGrothendieckCharacter_scalarExtensionHom_local
    (x : R₀[K](G)) :
    (finiteRepGrothendieckCharacter_local : R₀[K'](G) →+ R[K'](G))
        ((finiteRepGrothendieckScalarExtensionHom K K' G) x) =
      characterRingScalarExtensionHom_local
        ((finiteRepGrothendieckCharacter_local : R₀[K](G) →+ R[K](G)) x) := by
  refine QuotientAddGroup.induction_on x ?_
  intro a
  refine FreeAbelianGroup.induction_on a ?_ ?_ ?_ ?_
  · simp
  · intro V
    ext g
    change
      (finiteRepGrothendieckCharacter_local : R₀[K'](G) →+ R[K'](G))
          ((finiteRepGrothendieckScalarExtensionHom K K' G)
            (finiteRepGrothendieckClass K G V)) g =
        algebraMap K K'
          (((finiteRepGrothendieckCharacter_local : R₀[K](G) →+ R[K](G))
            (finiteRepGrothendieckClass K G V)) g)
    rw [finiteRepGrothendieckScalarExtensionHom_class_eq]
    rw [finiteRepGrothendieckCharacter_local_class]
    rw [finiteRepGrothendieckCharacter_local_class]
    exact congrFun (scalarExtension_character_eq_map_local V.ρ) g
  · intro V hV
    simpa using congrArg Neg.neg hV
  · intro a b ha hb
    simpa [map_add] using congrArg₂ HAdd.hAdd ha hb

/-- Helper for Corollary 16-16.1-3: under enough roots and the Chapter 12 quasisplit owner,
every `K'`-virtual character is the coefficientwise scalar extension of a `K`-virtual
character. -/
private theorem characterRingScalarExtensionHom_surjective_of_hasEnoughRoots_local
    [CharZero K]
    (hquasi : R[K](G) = R̄[K](G))
    [HasEnoughRootsOfUnity K (Monoid.exponent G)] :
    Function.Surjective (characterRingScalarExtensionHom_local : R[K](G) →+ R[K'](G)) := by
  intro χ'
  have hχ'_valued :
      IsValuedInBaseField K (χ' : G → K') :=
    character_isValuedInBaseField_of_mem_characterRing_of_hasEnoughRoots_compiled
      χ'.2
  rw [Representation.isValuedInBaseField_iff_mem_pointwiseAlgebraMap_range] at hχ'_valued
  rcases hχ'_valued with ⟨χK, hχK_map⟩
  have hχK_overline : χK ∈ R̄[K](G) := by
    let ι : K' →ₐ[K] AlgebraicClosure K := IsAlgClosed.lift
    letI : Algebra K' (AlgebraicClosure K) := ι.toAlgebra
    letI : IsScalarTower K K' (AlgebraicClosure K) :=
      IsScalarTower.of_algebraMap_eq fun x ↦ (ι.commutes x).symm
    let ιZ : K' →ₐ[ℤ] AlgebraicClosure K := ι.restrictScalars ℤ
    have hχ'_alg :
        (ιZ.compLeft G) (χ' : G → K') ∈ R[AlgebraicClosure K](G) :=
      map_mem_characterRingOverField_local
        ιZ (χ' : G → K') χ'.2
    rw [mem_overlineCharacterRingInExtension_iff K (AlgebraicClosure K) χK]
    convert hχ'_alg using 1
    ext g
    have hg : algebraMap K K' (χK g) = (χ' : G → K') g := congrFun hχK_map g
    change algebraMap K (AlgebraicClosure K) (χK g) = ι (χ' g)
    calc
      algebraMap K (AlgebraicClosure K) (χK g)
          = algebraMap K' (AlgebraicClosure K) (algebraMap K K' (χK g)) :=
              IsScalarTower.algebraMap_apply K K' (AlgebraicClosure K) (χK g)
      _ = ι (algebraMap K K' (χK g)) := by
            rw [RingHom.algebraMap_toAlgebra]; rfl
      _ = ι (χ' g) := by rw [hg]
  have hχK_mem : χK ∈ R[K](G) := by
    simpa [hquasi] using hχK_overline
  refine ⟨⟨χK, hχK_mem⟩, ?_⟩
  ext g
  exact congrFun hχK_map g

/-- Helper for Corollary 16-16.1-3: the remaining source-faithful Chapter `12/16` owner is the
retract data for ordinary scalar extension `R₀[K](G) → R₀[K'](G)`. -/
theorem finiteRepGrothendieckScalarExtension_retract_data_of_hasEnoughRoots_local
    [CharZero K]
    (hquasi : R[K](G) = R̄[K](G))
    [HasEnoughRootsOfUnity K (Monoid.exponent G)] :
    ∃ r : R₀[K'](G) →+ R₀[K](G),
      (finiteRepGrothendieckScalarExtensionHom K K' G).comp r = AddMonoidHom.id _ ∧
        Function.Injective (finiteRepGrothendieckScalarExtensionHom K K' G) :=
  by
  classical
  letI : CharZero K' := (RingHom.charZero_iff (algebraMap K K').injective).1 inferInstance
  letI : NeZero (Nat.card G : K) :=
    @ProjectiveScalarExtensionSplitInjective.nat_card_neZero_of_hasEnoughRoots_local
      K _ G _ _ K _ (by infer_instance) (by infer_instance)
  letI : NeZero (Nat.card G : K') :=
    @ProjectiveScalarExtensionSplitInjective.nat_card_neZero_of_hasEnoughRoots_local
      K _ G _ _ K' _ (by infer_instance) (by infer_instance)
  obtain ⟨sK, hsK_comp, _hsK_left⟩ :=
    (finiteRepGrothendieckCharacter_local_has_inverse :
      ∃ sF : R[K](G) →+ R₀[K](G),
        ((finiteRepGrothendieckCharacter_local : R₀[K](G) →+ R[K](G))).comp sF =
            AddMonoidHom.id _ ∧
          Function.LeftInverse sF
            (finiteRepGrothendieckCharacter_local : R₀[K](G) →+ R[K](G)))
  have hsK_apply :
      ∀ χ : R[K](G),
        (finiteRepGrothendieckCharacter_local : R₀[K](G) →+ R[K](G)) (sK χ) = χ := by
    intro χ
    have h :=
      congrArg (fun f : R[K](G) →+ R[K](G) ↦ f χ) hsK_comp
    simpa [AddMonoidHom.comp_apply] using h
  obtain ⟨ι, π', hπ'_pairwise, hπ'_complete⟩ :=
    (exists_complete_pairwise_nonisomorphic_simple_family_over_field_local :
      ∃ (ι : Type (u + 1)) (π : ι → FDRep K' G),
        PairwiseNonisomorphic π ∧ IsCompleteIrreducibleFamily π)
  let b' : Module.Basis ι ℤ (R₀[K'](G)) :=
    simple_finiteRep_classes_basis_of_complete_family π' hπ'_pairwise hπ'_complete
  have hpre :
      ∀ i : ι,
        ∃ χK : R[K](G),
          characterRingScalarExtensionHom_local χK =
            (finiteRepGrothendieckCharacter_local : R₀[K'](G) →+ R[K'](G)) [π' i]₀ := by
    intro i
    exact
      characterRingScalarExtensionHom_surjective_of_hasEnoughRoots_local hquasi
        ((finiteRepGrothendieckCharacter_local : R₀[K'](G) →+ R[K'](G)) [π' i]₀)
  choose χK hχK using hpre
  let rL : R₀[K'](G) →ₗ[ℤ] R₀[K](G) := b'.constr ℤ (fun i ↦ sK (χK i))
  have hbasis : ∀ i,
      (finiteRepGrothendieckScalarExtensionHom K K' G) (rL (b' i)) = b' i := by
    intro i
    apply (finiteRepGrothendieckCharacter_eq_iff_general_local).1
    calc
      (finiteRepGrothendieckCharacter_local : R₀[K'](G) →+ R[K'](G))
          ((finiteRepGrothendieckScalarExtensionHom K K' G) (rL (b' i)))
          =
        characterRingScalarExtensionHom_local
          ((finiteRepGrothendieckCharacter_local : R₀[K](G) →+ R[K](G)) (rL (b' i))) := by
            rw [finiteRepGrothendieckCharacter_scalarExtensionHom_local]
      _ =
        characterRingScalarExtensionHom_local (χK i) := by
            simp [rL, hsK_apply]
      _ = (finiteRepGrothendieckCharacter_local : R₀[K'](G) →+ R[K'](G)) [π' i]₀ := hχK i
      _ = (finiteRepGrothendieckCharacter_local : R₀[K'](G) →+ R[K'](G)) (b' i) := by
            simp [b', simple_finiteRep_classes_basis_of_complete_family_apply]
  have hrightL :
      (finiteRepGrothendieckScalarExtensionHom K K' G).toIntLinearMap.comp rL =
        LinearMap.id := by
    apply b'.ext
    intro i
    simpa [LinearMap.comp_apply] using hbasis i
  let r : R₀[K'](G) →+ R₀[K](G) := rL.toAddMonoidHom
  refine ⟨r, ?_, ?_⟩
  · apply AddMonoidHom.ext
    intro x
    have hx :=
      congrArg (fun f : R₀[K'](G) →ₗ[ℤ] R₀[K'](G) ↦ f x) hrightL
    simpa [r, LinearMap.comp_apply] using hx
  · intro x y hxy
    apply (finiteRepGrothendieckCharacter_eq_iff_general_local).1
    apply
      (characterRingScalarExtensionHom_injective_local :
        Function.Injective (characterRingScalarExtensionHom_local : R[K](G) →+ R[K'](G)))
    calc
      characterRingScalarExtensionHom_local
          ((finiteRepGrothendieckCharacter_local : R₀[K](G) →+ R[K](G)) x)
          =
        (finiteRepGrothendieckCharacter_local : R₀[K'](G) →+ R[K'](G))
          ((finiteRepGrothendieckScalarExtensionHom K K' G) x) := by
            rw [finiteRepGrothendieckCharacter_scalarExtensionHom_local]
      _ =
        (finiteRepGrothendieckCharacter_local : R₀[K'](G) →+ R[K'](G))
          ((finiteRepGrothendieckScalarExtensionHom K K' G) y) := by rw [hxy]
      _ =
        characterRingScalarExtensionHom_local
          ((finiteRepGrothendieckCharacter_local : R₀[K](G) →+ R[K](G)) y) := by
            rw [finiteRepGrothendieckCharacter_scalarExtensionHom_local]

/-
This packaging step only uses the retract witness itself, so the ambient finiteness hypotheses
should stay out of the theorem statement.
-/
omit [FiniteDimensional K K'] [Finite G] in
/-- Helper for Corollary 16-16.1-3: once the ordinary scalar-extension retract data is available,
it packages immediately into the left inverse consumed by the main corollary. -/
private theorem finiteRepGrothendieckScalarExtension_left_inverse_of_retract_data_local
    (h :
      ∃ r : R₀[K'](G) →+ R₀[K](G),
        (finiteRepGrothendieckScalarExtensionHom K K' G).comp r = AddMonoidHom.id _ ∧
          Function.Injective (finiteRepGrothendieckScalarExtensionHom K K' G)) :
    ∃ t : R₀[K'](G) →+ R₀[K](G),
      Function.LeftInverse t (finiteRepGrothendieckScalarExtensionHom K K' G) := by
  rcases h with ⟨r, hr, hinj⟩
  refine ⟨r, ?_⟩
  intro x
  -- Apply the right-inverse identity at `f x` and reflect back along injectivity.
  apply hinj
  have hr_apply :=
    congrArg (fun f : R₀[K'](G) →+ R₀[K'](G) =>
      f ((finiteRepGrothendieckScalarExtensionHom K K' G) x)) hr
  simpa [AddMonoidHom.comp_apply] using hr_apply

/-- Helper for Corollary 16-16.1-3: the remaining Chapter `12` descent owner is a left inverse for
ordinary scalar extension `R₀[K](G) → R₀[K'](G)`. -/
private theorem finiteRepGrothendieckScalarExtension_left_inverse_of_hasEnoughRoots_local
    [CharZero K]
    (hquasi : R[K](G) = R̄[K](G))
    [HasEnoughRootsOfUnity K (Monoid.exponent G)] :
    ∃ t : R₀[K'](G) →+ R₀[K](G),
      Function.LeftInverse t (finiteRepGrothendieckScalarExtensionHom K K' G) := by
  -- The only open mathematical input is now the retract data isolated in the previous theorem.
  exact
    finiteRepGrothendieckScalarExtension_left_inverse_of_retract_data_local
      (finiteRepGrothendieckScalarExtension_retract_data_of_hasEnoughRoots_local hquasi)

-- Semantic recall note: `lean_leansearch` did not surface a directly relevant library theorem for
-- this exact split-injectivity composite, so the public statement stays on the verified canonical
-- owners `projectiveGrothendieckScalarExtensionHom` and
-- `finiteRepGrothendieckScalarExtensionHom`.
/-- Corollary 16-16.1-3: for each finite extension `K' / K`, the composite of Serre's
homomorphism `e : P_k(G) → R₀[K](G)` with ordinary scalar extension
`R₀[K](G) → R₀[K'](G)` is a split injection. Here `k = IsLocalRing.ResidueField A`. -/
theorem projectiveScalarExtensionOverExtension_split_injective
    [IsDomain A] [IsDiscreteValuationRing A]
    [IsNoetherianRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [CharZero K] [PerfectField (IsLocalRing.ResidueField A)]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    (hquasi : R[K](G) = R̄[K](G)) :
    ∃ s : R₀[K'](G) →+ P_k(G),
      Function.LeftInverse s
        ((finiteRepGrothendieckScalarExtensionHom K K' G).comp
          (projectiveGrothendieckScalarExtensionHom A K)) := by
  -- Serre's route is to compose the existing section of `e : P_k(G) → R₀[K](G)` with the local
  -- section of ordinary scalar extension `R₀[K](G) → R₀[K'](G)`.
  obtain ⟨sP, hsP⟩ :=
    projectiveGrothendieckScalarExtensionHom_split_injective
      (A := A) (K := K) (G := G)
  obtain ⟨t, ht⟩ :=
    finiteRepGrothendieckScalarExtension_left_inverse_of_hasEnoughRoots_local
      (K := K) (K' := K') (G := G) hquasi
  refine ⟨sP.comp t, ?_⟩
  -- Evaluating on `x` lets the two previously constructed left inverses fire in sequence.
  intro x
  calc
    (sP.comp t)
        (((finiteRepGrothendieckScalarExtensionHom K K' G).comp
          (projectiveGrothendieckScalarExtensionHom A K)) x)
        =
          sP
            (t
              ((finiteRepGrothendieckScalarExtensionHom K K' G)
                ((projectiveGrothendieckScalarExtensionHom A K) x))) := by
                  simp [AddMonoidHom.comp_apply]
    _ = sP ((projectiveGrothendieckScalarExtensionHom A K) x) := by
          rw [ht]
    _ = x := hsP x

end

end Representation
