import Mathlib
import LinearRepresentations_Serre_1977.GroupTheory.ConjClassesPower
import LinearRepresentations_Serre_1977.Chap10.Definition_10_10_1_1
import LinearRepresentations_Serre_1977.Chap11.Proposition_11_11_4_1.OwnersAndPrimeFibers
import LinearRepresentations_Serre_1977.Chap12.Proposition_12_12_1_1
import LinearRepresentations_Serre_1977.Chap12.Corollary_12_12_4_2
import LinearRepresentations_Serre_1977.Chap12.Theorem_12_12_4_1
import LinearRepresentations_Serre_1977.Chap12.GaloisPowerClasses

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open scoped Representation

universe u v w x

namespace Representation

section GaloisPowerClasses

variable {G : Type u} [Group G] [Finite G]

/- The galois-power-class cluster (`GaloisPowerClass`, `galoisPowerClassMk`,
`IsConstantOnGaloisPowerClasses`, `galoisPowerClassFunctionSubmodule` with its `equivFun`, the
`p`-regular variants, and the basic instances) is defined canonically in
`Serre.Chap12.GaloisPowerClasses` and imported above. Only the additional reformulations used by
this corollary are recorded here. -/

section GaloisPowerClassReformulations

variable {R : Type v}

@[simp] theorem IsConstantOnGaloisPowerClasses.lift_comp_mk
    {ΓK : Subgroup (ZMod (Monoid.exponent G))ˣ} {f : G → R}
    (hf : IsConstantOnGaloisPowerClasses ΓK f) :
    hf.lift ∘ galoisPowerClassMk ΓK = f := by
  ext g
  rfl

/-- A `Γ_K`-class-constant function is exactly a class function that factors through the quotient
map `G → GaloisPowerClass ΓK`; the class-function field is derived rather than primitive. -/
theorem isConstantOnGaloisPowerClasses_iff_isClassFunction_and_factorsThrough
    {ΓK : Subgroup (ZMod (Monoid.exponent G))ˣ} {f : G → R} :
    IsConstantOnGaloisPowerClasses ΓK f ↔
      _root_.IsClassFunction f ∧ f.FactorsThrough (galoisPowerClassMk ΓK) := by
  constructor
  · intro hf
    exact ⟨hf.isClassFunction, hf.factorsThrough⟩
  · rintro ⟨_, hfactor⟩
    exact ⟨hfactor⟩

/-- A function on `G` is constant on Serre's `Γ_K`-classes exactly when it is pulled back from
`GaloisPowerClass ΓK`. -/
theorem isConstantOnGaloisPowerClasses_iff_exists
    {ΓK : Subgroup (ZMod (Monoid.exponent G))ˣ} {f : G → R} :
    IsConstantOnGaloisPowerClasses ΓK f ↔
      ∃ φ : GaloisPowerClass ΓK → R, f = φ ∘ galoisPowerClassMk ΓK := by
  constructor
  · intro hf
    exact ⟨hf.lift, hf.lift_comp_mk.symm⟩
  · rintro ⟨φ, rfl⟩
    infer_instance

end GaloisPowerClassReformulations

end GaloisPowerClasses

section RankOfRepresentationRing

variable {G : Type u} [Group G] [Finite G]
variable {A : Type v} [CommRing A]
variable {L : Type u} [Field L] [NumberField L]
variable [IsCyclotomicExtension {Monoid.exponent G} ℚ L]
variable {ι : Type x}

variable (K : IntermediateField ℚ L)
variable [Algebra A K]

/-
Corollary `12-12.4-2`, rewritten through the canonical quotient owner
`GaloisPowerClass (Γ[K](G))`: a `K`-valued function in `A ⊗ R_K(G)` is automatically a class
function, since this scalar extension is spanned by ordinary characters.
-/
omit [IsCyclotomicExtension {Monoid.exponent G} ℚ L] in
theorem isClassFunction_of_mem_characterRingOverFieldScalarExtension
    {f : G → K} (hf : f ∈ A ⊗R[K](G)) :
    _root_.IsClassFunction f := by
  induction hf using Submodule.span_induction with
  | mem ψ hψ =>
      exact Representation.isClassFunction_of_mem_characterRingOverField ψ hψ
  | zero =>
      simpa using (inferInstance : _root_.IsClassFunction (fun _ : G ↦ (0 : K)))
  | add f g _ _ hf hg =>
      letI : _root_.IsClassFunction f := hf
      letI : _root_.IsClassFunction g := hg
      simpa using (inferInstance : _root_.IsClassFunction (f + g))
  | smul a f _ hf =>
      letI : _root_.IsClassFunction f := hf
      simpa using (inferInstance : _root_.IsClassFunction (a • f))

/-- Corollary `12-12.4-2`, rewritten through the canonical quotient owner
`GaloisPowerClass (Γ[K](G))`: a `K`-valued function belongs to `K ⊗ R_K(G)` exactly when
it is constant on Serre's `Γ_K`-classes. -/
theorem classFunction_mem_characterRingOverFieldScalarExtension_iff_isConstantOnGaloisPowerClasses
    (f : G → K) :
    f ∈ K⊗R[K](G) ↔ IsConstantOnGaloisPowerClasses (Γ[K](G)) f := by
  constructor
  · intro hf
    let hfClass : _root_.IsClassFunction f :=
      isClassFunction_of_mem_characterRingOverFieldScalarExtension K hf
    let φ : classFunctionSubmodule K G :=
      ⟨f, (mem_classFunctionSubmodule_iff K f).2 hfClass⟩
    exact
      (isConstantOnGaloisPowerClasses_iff_forall_pow_eq hfClass).2 <|
        (classFunction_mem_characterRingOverFieldScalarExtension_iff_gammaSubgroup_invariant
          G K φ).1 hf
  · intro hf
    let φ : classFunctionSubmodule K G :=
      ⟨f, (mem_classFunctionSubmodule_iff K f).2 hf.isClassFunction⟩
    exact
      (classFunction_mem_characterRingOverFieldScalarExtension_iff_gammaSubgroup_invariant
        G K φ).2 <|
        (isConstantOnGaloisPowerClasses_iff_forall_pow_eq hf.isClassFunction).1 hf

/-- Helper for Corollary 12-12.4-3: this is the canonical owner submodule of `Γ[K](G)`-constant
`K`-valued functions, written with the explicit pointwise `K`-module structure on `G → K`. -/
abbrev galoisPowerClassFunctionSubmoduleOverField :
    @Submodule K (G → K) _ _ (Pi.module G (fun _ : G ↦ K) K) :=
  galoisPowerClassFunctionSubmodule (R := K) (Γ[K](G))

/-- Serre's scalar extension `K ⊗ R_K(G)` is exactly the owner submodule of `K`-valued
functions on `G` that are constant on `Γ[K](G)`-power classes. This is Corollary 12.4.2 in
Serre's notation; the earlier rationalized owner `ℚ ⊗ R_K(G)` is too small for this statement. -/
theorem characterRingOverFieldScalarExtension_eq_galoisPowerClassFunctionSubmodule :
    (K⊗R[K](G) : Submodule K (G → K)) =
      galoisPowerClassFunctionSubmoduleOverField (G := G) (L := L) K := by
  ext f
  rw [mem_galoisPowerClassFunctionSubmodule_iff]
  exact
    classFunction_mem_characterRingOverFieldScalarExtension_iff_isConstantOnGaloisPowerClasses
      K f

/-- Corollary 12-12.4-3 bridge: Serre's scalar extension `K ⊗ R_K(G)` is canonically the full
function space on the quotient `GaloisPowerClass (Γ[K](G))`. -/
def characterRingOverFieldScalarExtensionEquivGaloisPowerClassFunctions
    :
    K⊗R[K](G) ≃ₗ[K] GaloisPowerClass (Γ[K](G)) → K :=
  (LinearEquiv.ofEq _ _
      (characterRingOverFieldScalarExtension_eq_galoisPowerClassFunctionSubmodule K)).trans
    (galoisPowerClassFunctionSubmodule.equivFun (R := K) (Γ[K](G)))

/-- Helper for Corollary 12-12.4-3: pulling back the quotient-function equivalence along
`galoisPowerClassMk` recovers the original function in `K ⊗ R_K(G)`. -/
@[simp] theorem
    characterRingOverFieldScalarExtensionEquivGaloisPowerClassFunctions_comp_galoisPowerClassMk
    (f : K ⊗R[K](G)) :
    characterRingOverFieldScalarExtensionEquivGaloisPowerClassFunctions K f ∘
        galoisPowerClassMk (Γ[K](G)) =
      f := by
  ext g
  let φ :
      galoisPowerClassFunctionSubmoduleOverField K :=
    (LinearEquiv.ofEq _ _
      (characterRingOverFieldScalarExtension_eq_galoisPowerClassFunctionSubmodule K)) f
  let φK : galoisPowerClassFunctionSubmodule (R := K) (Γ[K](G)) := φ
  let hφ : IsConstantOnGaloisPowerClasses (Γ[K](G)) ((φK : G → K)) := φK.2
  -- Unfold the transport across the restricted owner equality and then evaluate the quotient lift.
  have hdef :
      (characterRingOverFieldScalarExtensionEquivGaloisPowerClassFunctions K) f =
        galoisPowerClassFunctionSubmodule.equivFun (R := K) (Γ[K](G)) φ := by
    rfl
  have hφ_eq : (φK : G → K) = (f : G → K) := by
    dsimp [φ, φK]
  have hpull :
      ((galoisPowerClassFunctionSubmodule.equivFun (R := K) (Γ[K](G)) φ) ∘
        galoisPowerClassMk (Γ[K](G))) = (φK : G → K) := by
    exact congrArg
      (fun ψ : galoisPowerClassFunctionSubmodule (R := K) (Γ[K](G)) ↦ (ψ : G → K))
      ((galoisPowerClassFunctionSubmodule.equivFun (R := K) (Γ[K](G))).left_inv φ)
  rw [hdef]
  have hleft :
      ↑(((galoisPowerClassFunctionSubmodule.equivFun (R := K) (Γ[K](G)) φ) ∘
          galoisPowerClassMk (Γ[K](G))) g) = ↑(φK g) := by
    simpa [Function.comp] using congrArg ((↑) : K → L) (congrFun hpull g)
  have hright : ↑(φK g) = ↑((f : G → K) g) := by
    simpa using congrArg ((↑) : K → L) (congrFun hφ_eq g)
  simpa using hleft.trans hright

/-- Over the coefficient field itself, the algebra-level scalar-extension owner
`K ⊗ R_K(G)` consists exactly of the functions that are constant on Serre's
`Γ[K](G)`-power classes. -/
theorem mem_characterRingOverFieldAlgebraScalarExtension_over_field_iff_isConstantOnGaloisPowerClasses
    {f : G → K} :
    f ∈ characterRingOverFieldAlgebraScalarExtensionSubalgebra K K G ↔
      IsConstantOnGaloisPowerClasses (Γ[K](G)) f := by
  simpa [mem_characterRingOverFieldAlgebraScalarExtensionSubalgebra_iff] using
    (classFunction_mem_characterRingOverFieldScalarExtension_iff_isConstantOnGaloisPowerClasses
      (G := G) (L := L) K f)

/-- Over the coefficient field itself, Serre's algebra-level scalar-extension owner
`K ⊗ R_K(G)` is canonically the full function algebra on the quotient of conjugacy classes by
`Γ[K](G)`. -/
noncomputable def
    characterRingOverFieldAlgebraScalarExtensionSubalgebra_over_field_algEquiv_galoisPowerClass_functions :
    characterRingOverFieldAlgebraScalarExtensionSubalgebra K K G ≃ₐ[K]
      (GaloisPowerClass (Γ[K](G)) → K) := by
  let e :
      characterRingOverFieldAlgebraScalarExtensionSubalgebra K K G ≃ₗ[K]
        (GaloisPowerClass (Γ[K](G)) → K) :=
    { toFun := fun φ ↦
        let hφ : IsConstantOnGaloisPowerClasses (Γ[K](G))
            ((φ : characterRingOverFieldAlgebraScalarExtensionSubalgebra K K G) : G → K) :=
          (mem_characterRingOverFieldAlgebraScalarExtension_over_field_iff_isConstantOnGaloisPowerClasses
            (G := G) (L := L) (K := K)).1 φ.2
        hφ.lift
      invFun := fun φ ↦
        ⟨φ ∘ galoisPowerClassMk (Γ[K](G)),
          (mem_characterRingOverFieldAlgebraScalarExtension_over_field_iff_isConstantOnGaloisPowerClasses
            (G := G) (L := L) (K := K)).2 inferInstance⟩
      left_inv := by
        intro φ
        ext g
        let hφ : IsConstantOnGaloisPowerClasses (Γ[K](G))
            ((φ : characterRingOverFieldAlgebraScalarExtensionSubalgebra K K G) : G → K) :=
          (mem_characterRingOverFieldAlgebraScalarExtension_over_field_iff_isConstantOnGaloisPowerClasses
            (G := G) (L := L) (K := K)).1 φ.2
        simpa using hφ.lift_mk g
      right_inv := by
        intro φ
        ext c
        obtain ⟨g, rfl⟩ := galoisPowerClassMk_surjective (G := G) (Γ[K](G)) c
        let hφ : IsConstantOnGaloisPowerClasses (Γ[K](G))
            (φ ∘ galoisPowerClassMk (Γ[K](G))) :=
          inferInstance
        simpa using hφ.lift_mk g
      map_add' := by
        intro φ ψ
        ext c
        obtain ⟨g, rfl⟩ := galoisPowerClassMk_surjective (G := G) (Γ[K](G)) c
        rfl
      map_smul' := by
        intro a φ
        ext c
        obtain ⟨g, rfl⟩ := galoisPowerClassMk_surjective (G := G) (Γ[K](G)) c
        rfl }
  refine AlgEquiv.ofLinearEquiv e ?_ ?_
  · ext c
    obtain ⟨g, rfl⟩ := galoisPowerClassMk_surjective (G := G) (Γ[K](G)) c
    let h1 :
        IsConstantOnGaloisPowerClasses (Γ[K](G))
          ((1 : characterRingOverFieldAlgebraScalarExtensionSubalgebra K K G) : G → K) :=
      (mem_characterRingOverFieldAlgebraScalarExtension_over_field_iff_isConstantOnGaloisPowerClasses
        (G := G) (L := L) (K := K)).1 (by
          exact (1 : characterRingOverFieldAlgebraScalarExtensionSubalgebra K K G).2)
    have he1 : e 1 = h1.lift := rfl
    rw [he1]
    simpa using h1.lift_mk g
  · intro φ ψ
    ext c
    obtain ⟨g, rfl⟩ := galoisPowerClassMk_surjective (G := G) (Γ[K](G)) c
    let hφ : IsConstantOnGaloisPowerClasses (Γ[K](G))
        ((φ : characterRingOverFieldAlgebraScalarExtensionSubalgebra K K G) : G → K) :=
      (mem_characterRingOverFieldAlgebraScalarExtension_over_field_iff_isConstantOnGaloisPowerClasses
        (G := G) (L := L) (K := K)).1 φ.2
    let hψ : IsConstantOnGaloisPowerClasses (Γ[K](G))
        ((ψ : characterRingOverFieldAlgebraScalarExtensionSubalgebra K K G) : G → K) :=
      (mem_characterRingOverFieldAlgebraScalarExtension_over_field_iff_isConstantOnGaloisPowerClasses
        (G := G) (L := L) (K := K)).1 ψ.2
    let hφψ :
        IsConstantOnGaloisPowerClasses (Γ[K](G))
          (((φ * ψ : characterRingOverFieldAlgebraScalarExtensionSubalgebra K K G) : G → K)) :=
      (mem_characterRingOverFieldAlgebraScalarExtension_over_field_iff_isConstantOnGaloisPowerClasses
        (G := G) (L := L) (K := K)).1 (φ * ψ).2
    have hK :
        hφψ.lift (galoisPowerClassMk (Γ[K](G)) g) =
          hφ.lift (galoisPowerClassMk (Γ[K](G)) g) *
            hψ.lift (galoisPowerClassMk (Γ[K](G)) g) := by
      rw [hφψ.lift_mk, hφ.lift_mk, hψ.lift_mk]
      rfl
    have hφe : e φ = hφ.lift := rfl
    have hψe : e ψ = hψ.lift := rfl
    have hφψe : e (φ * ψ) = hφψ.lift := rfl
    rw [hφψe, hφe, hψe]
    rw [Pi.mul_apply]
    exact congrArg Subtype.val hK

/-- Evaluating the quotient-function realization of the `K`-coefficient owner on the
`Γ[K](G)`-class of `g` recovers the original value at `g`. -/
@[simp] theorem
    characterRingOverFieldAlgebraScalarExtensionSubalgebra_over_field_algEquiv_galoisPowerClass_functions_apply_mk
    (φ : characterRingOverFieldAlgebraScalarExtensionSubalgebra K K G) (g : G) :
    characterRingOverFieldAlgebraScalarExtensionSubalgebra_over_field_algEquiv_galoisPowerClass_functions
        (G := G) (L := L) (K := K) φ
        (galoisPowerClassMk (Γ[K](G)) g) =
      (φ : G → K) g := by
  let hφ : IsConstantOnGaloisPowerClasses (Γ[K](G))
      ((φ : characterRingOverFieldAlgebraScalarExtensionSubalgebra K K G) : G → K) :=
    (mem_characterRingOverFieldAlgebraScalarExtension_over_field_iff_isConstantOnGaloisPowerClasses
      (G := G) (L := L) (K := K)).1 φ.2
  have hφe :
      characterRingOverFieldAlgebraScalarExtensionSubalgebra_over_field_algEquiv_galoisPowerClass_functions
          (G := G) (L := L) (K := K) φ =
        hφ.lift := rfl
  rw [hφe]
  exact hφ.lift_mk g

/-- A `K`-valued character in `R_K(G)` is constant on Serre's `Γ_K`-classes. -/
theorem isConstantOnGaloisPowerClasses_of_mem_characterRingOverField
    {f : G → K} (hf : f ∈ R[K](G)) :
    IsConstantOnGaloisPowerClasses (Γ[K](G)) f := by
  exact
      (classFunction_mem_characterRingOverFieldScalarExtension_iff_isConstantOnGaloisPowerClasses
      K f).1
      (mem_characterRingOverFieldAlgebraScalarExtension_of_mem_characterRingOverField (A := K) hf)

/-- Membership in Serre's scalar extension `A ⊗ R_K(G)` implies constancy on the genuine
arithmetic `Γ_K`-classes. This is the owner-level Chapter `12` upgrade of the `R_K(G)` statement
above, and the canonical source for later reductions modulo prime ideals. -/
theorem isConstantOnGaloisPowerClasses_of_mem_characterRingOverFieldAlgebraScalarExtension
    {f : G → K} (hf : f ∈ A ⊗R[K](G)) :
    IsConstantOnGaloisPowerClasses (Γ[K](G)) f := by
  induction hf using Submodule.span_induction with
  | mem ψ hψ =>
      exact isConstantOnGaloisPowerClasses_of_mem_characterRingOverField K (by simpa using hψ)
  | zero =>
      simpa using
        (inferInstance : IsConstantOnGaloisPowerClasses (Γ[K](G)) (fun _ : G ↦ (0 : K)))
  | add f g _ _ hf hg =>
      letI : IsConstantOnGaloisPowerClasses (Γ[K](G)) f := hf
      letI : IsConstantOnGaloisPowerClasses (Γ[K](G)) g := hg
      simpa using
        (inferInstance : IsConstantOnGaloisPowerClasses (Γ[K](G)) (f + g))
  | smul a f _ hf =>
      letI : IsConstantOnGaloisPowerClasses (Γ[K](G)) f := hf
      simpa using
        (inferInstance : IsConstantOnGaloisPowerClasses (Γ[K](G)) (a • f))

-- Proof sketch: Corollary `12-12.4-2` identifies the image of `K ⊗ R_K(G)` with the
-- bundled owner `galoisPowerClassFunctionSubmodule K (Γ[K](G))`, hence with the full function
-- space `GaloisPowerClass (Γ[K](G)) → K` via
-- `characterRingOverFieldScalarExtensionEquivGaloisPowerClassFunctions`. Transport each
-- irreducible character through that quotient equivalence, then package the resulting family as
-- the basis promised by Serre's corollary.
/-- The quotient function on `GaloisPowerClass (Γ[K](G))` corresponding to the irreducible
character of `π i`. -/
def irreducibleCharacterOnGaloisPowerClasses
    (π : ι → FDRep K G)
    (hπ_complete : IsCompleteIrreducibleFamily π) (i : ι) :
    GaloisPowerClass (Γ[K](G)) → K :=
  letI : Simple (π i) := hπ_complete.isSimple i
  characterRingOverFieldScalarExtensionEquivGaloisPowerClassFunctions K
    ⟨(π i).character,
      mem_characterRingOverFieldAlgebraScalarExtension_of_mem_characterRingOverField
        (A := K) (FDRep.character_mem_characterRingOverField K (π i))⟩

@[simp] theorem irreducibleCharacterOnGaloisPowerClasses_comp_galoisPowerClassMk
    (π : ι → FDRep K G)
    (hπ_complete : IsCompleteIrreducibleFamily π) (i : ι) :
    irreducibleCharacterOnGaloisPowerClasses K π hπ_complete i ∘
        galoisPowerClassMk (Γ[K](G)) =
      (π i).character := by
  letI := hπ_complete.isSimple i
  -- Route correction: the quotient character is obtained through a scalar-restricted transport, so
  -- the pullback identity is proved by unfolding that transport rather than by definitional `rfl`.
  simpa [irreducibleCharacterOnGaloisPowerClasses] using
    characterRingOverFieldScalarExtensionEquivGaloisPowerClassFunctions_comp_galoisPowerClassMk
      K
      ⟨(π i).character,
        mem_characterRingOverFieldAlgebraScalarExtension_of_mem_characterRingOverField
          (A := K) (FDRep.character_mem_characterRingOverField K (π i))⟩

/- Helper for Corollary 12-12.4-3: every element of `R[K](G)` already lies in the ambient
`K`-span of the ordinary irreducible characters of a complete pairwise nonisomorphic family. -/
omit [IsCyclotomicExtension {Monoid.exponent G} ℚ L] in
lemma mem_span_irreducible_characters_of_mem_characterRingOverField
    (π : ι → FDRep K G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    {χ : G → K} (hχ : χ ∈ R[K](G)) :
    χ ∈ Submodule.span K (Set.range fun i ↦ (π i).character) := by
  classical
  let b := irreducible_characters_basis_of_complete_family K π hπ_pairwise hπ_complete
  let c := b.repr ⟨χ, hχ⟩
  -- Rewrite the basis expansion in `R[K](G)` inside the ambient function space `G → K`.
  have hχ_eq :
      Finset.sum c.support (fun i ↦ c i • (π i).character) = χ := by
    have hrepr :
        (Finsupp.linearCombination ℤ (fun i ↦ b i)) c = ⟨χ, hχ⟩ := by
      rw [show c = b.repr ⟨χ, hχ⟩ by rfl]
      exact b.linearCombination_repr ⟨χ, hχ⟩
    simpa [Finsupp.linearCombination_apply, Finsupp.sum, b,
      irreducible_characters_basis_of_complete_family_apply,
      FDRep.irreducibleCharacter_apply] using
      congrArg ((↑) : R[K](G) → G → K) hrepr
  -- A finite linear combination of the generators lies in their span.
  rw [← hχ_eq]
  exact
    Submodule.sum_mem (Submodule.span K (Set.range fun i ↦ (π i).character)) fun i _ ↦
      by
        simpa [zsmul_eq_mul] using
          (Submodule.smul_mem (Submodule.span K (Set.range fun j ↦ (π j).character))
            (c i : K)
            (Submodule.subset_span ⟨i, rfl⟩))

/-- Helper for Corollary 12-12.4-3: every function in the ambient span of the ordinary
irreducible characters is the pullback of a quotient function in the corresponding quotient span.
-/
lemma exists_mem_span_irreducibleCharacterOnGaloisPowerClasses_of_mem_span
    (π : ι → FDRep K G)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    {f : G → K}
    (hf : f ∈ Submodule.span K (Set.range fun i ↦ (π i).character)) :
    ∃ φ ∈ Submodule.span K
        (Set.range (irreducibleCharacterOnGaloisPowerClasses K π hπ_complete)),
      φ ∘ galoisPowerClassMk (Γ[K](G)) = f := by
  induction hf using Submodule.span_induction with
  | mem ψ hψ =>
      rcases hψ with ⟨i, rfl⟩
      -- Each ordinary irreducible character is the pullback of its quotient avatar.
      refine ⟨irreducibleCharacterOnGaloisPowerClasses K π hπ_complete i,
        Submodule.subset_span ⟨i, rfl⟩, ?_⟩
      exact irreducibleCharacterOnGaloisPowerClasses_comp_galoisPowerClassMk K π hπ_complete i
  | zero =>
      -- The zero function descends trivially.
      exact ⟨0, Submodule.zero_mem _, by ext g; rfl⟩
  | add f g _ _ hf hg =>
      rcases hf with ⟨φf, hφf, rfl⟩
      rcases hg with ⟨φg, hφg, rfl⟩
      -- Descent is stable under addition.
      refine ⟨φf + φg, Submodule.add_mem _ hφf hφg, ?_⟩
      ext g
      rfl
  | smul a f _ hf =>
      rcases hf with ⟨φ, hφ, rfl⟩
      -- Descent is stable under scalar multiplication.
      refine ⟨a • φ, Submodule.smul_mem _ a hφ, ?_⟩
      ext g
      rfl

section PairingHelpers

variable {G : Type u} [Group G] [Finite G]
variable {L : Type u} [Field L] [NumberField L]
variable {ι : Type x}
variable (K : IntermediateField ℚ L)

/-- Helper for Corollary 12-12.4-3: the normalized pairing is additive on finite `K`-linear
combinations in its left argument. -/
private theorem groupFunctionPairing_sum_smul_left
    [Invertible (Nat.card G : K)]
    (s : Finset ι) (g : ι → K) (χ : ι → G → K) (ψ : G → K) :
    ⟪∑ j ∈ s, g j • χ j, ψ⟫ = ∑ j ∈ s, g j * ⟪χ j, ψ⟫ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [groupFunctionPairingOverField]
  | insert a s ha ih =>
      -- Expand the inserted term, then use additivity and homogeneity of the pairing.
      simp [Finset.sum_insert, ha, ih, groupFunctionPairing_add_left,
        groupFunctionPairing_smul_left]

/-- Helper for Corollary 12-12.4-3: the self-pairing of the character of a simple
finite-dimensional representation is nonzero, because the identity intertwiner survives in its
endomorphism space. -/
private theorem groupFunctionPairingOverField_character_self_ne_zero
    (V : FDRep K G) [Simple V] :
    ⟪V.character, V.character⟫ ≠ (0 : K) := by
  letI : Fintype G := Fintype.ofFinite G
  have hcard_ne : (Nat.card G : K) ≠ 0 := by
    rw [← Fintype.card_eq_nat_card]
    exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  letI : Invertible (Nat.card G : K) := invertibleOfNonzero hcard_ne
  let X : Rep K G := (forget₂ (FDRep K G) (Rep K G)).obj V
  let e₁ : (V ⟶ V) ≃ₗ[K] (X ⟶ X) := (FDRep.forget₂HomLinearEquiv V V).symm
  let e₂ : (X ⟶ X) ≃ₗ[K] (Representation.IntertwiningMap V.ρ V.ρ) := by
    simpa [X, FDRep.forget₂_ρ] using (Rep.homLinearEquiv X X)
  let e : (V ⟶ V) ≃ₗ[K] (Representation.IntertwiningMap V.ρ V.ρ) := e₁.trans e₂
  letI : FiniteDimensional K (Representation.IntertwiningMap V.ρ V.ρ) :=
    FiniteDimensional.of_injective e.symm.toLinearMap e.symm.injective
  have hnontriv : Nontrivial (Representation.IntertwiningMap V.ρ V.ρ) := by
    refine ⟨0, e (𝟙 V), ?_⟩
    intro h
    apply CategoryTheory.id_nonzero V
    exact e.injective h.symm
  letI : Nontrivial (Representation.IntertwiningMap V.ρ V.ρ) := hnontriv
  have hpair :
      ⟪V.character, V.character⟫ =
        Module.finrank K (Representation.IntertwiningMap V.ρ V.ρ) :=
    Representation.groupFunctionPairingOverField_character_eq_finrank_intertwiningMap K V.ρ V.ρ
  rw [hpair]
  exact_mod_cast Module.finrank_pos.ne'

end PairingHelpers

/-- Helper for Corollary 12-12.4-3: the quotient irreducible characters remain linearly
independent after passing to functions on `GaloisPowerClass (Γ[K](G))`. -/
lemma linearIndependent_irreducibleCharacterOnGaloisPowerClasses
    (π : ι → FDRep K G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π) :
    LinearIndependent K (irreducibleCharacterOnGaloisPowerClasses K π hπ_complete) := by
  classical
  let pullback :
      (GaloisPowerClass (Γ[K](G)) → K) →ₗ[K] G → K :=
    { toFun := fun φ ↦ φ ∘ galoisPowerClassMk (Γ[K](G))
      map_add' := by intro φ ψ; rfl
      map_smul' := by intro a φ; rfl }
  have hchars : LinearIndependent K (fun i ↦ (π i).character) := by
    letI : Fintype G := Fintype.ofFinite G
    have hcard_ne : (Nat.card G : K) ≠ 0 := by
      rw [← Fintype.card_eq_nat_card]
      exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    letI : Invertible (Nat.card G : K) := invertibleOfNonzero hcard_ne
    have horth :
        Pairwise fun i j ↦
          ⟪(π i).character, (π j).character⟫ = (0 : K) :=
      Representation.irreducible_characters_pairwise_orthogonal_of_pairwise_nonisomorphic
        K π hπ_complete.isSimple hπ_pairwise
    rw [linearIndependent_iff']
    intro s g hg i hi
    -- Pair the relation with the `i`-th character to isolate its coefficient.
    have hpair0 :=
      congrArg (fun ψ : G → K ↦ groupFunctionPairingOverField K ψ (π i).character) hg
    have hpair :
        ⟪∑ j ∈ s, g j • (π j).character, (π i).character⟫ = (0 : K) := by
      simpa [Representation.groupFunctionPairingOverField] using hpair0
    rw [Representation.groupFunctionPairing_sum_smul_left
        K s g (fun j ↦ (π j).character) ((π i).character)]
      at hpair
    -- Route correction: the diagonal term is handled via the simple-object endomorphism-space
    -- computation, avoiding the previous timeout-prone explicit self-intertwining witness.
    rw [Finset.sum_eq_single i] at hpair
    · exact (mul_eq_zero.mp hpair).resolve_right <|
        Representation.groupFunctionPairingOverField_character_self_ne_zero K (π i)
    · intro j hj hji
      rw [horth hji, mul_zero]
    · intro hnot_mem
      exact (hnot_mem hi).elim
  -- Pulling back along the surjective quotient map identifies the quotient characters with the
  -- ordinary irreducible characters.
  have hpullback :
      LinearIndependent K
        (pullback ∘ irreducibleCharacterOnGaloisPowerClasses K π hπ_complete) := by
    have hfamily :
        (pullback ∘ irreducibleCharacterOnGaloisPowerClasses K π hπ_complete) =
          fun i ↦ (π i).character := by
      funext i
      ext g
      -- Evaluate the pullback on each quotient character and rewrite with the explicit descent law.
      simpa [pullback] using
        congrFun
          (irreducibleCharacterOnGaloisPowerClasses_comp_galoisPowerClassMk K π hπ_complete i) g
    rw [hfamily]
    exact hchars
  exact LinearIndependent.of_comp pullback hpullback

/-- Helper for Corollary 12-12.4-3: the transported irreducible characters span all functions on
`GaloisPowerClass (Γ[K](G))`. -/
lemma span_irreducibleCharacterOnGaloisPowerClasses_eq_top
    (π : ι → FDRep K G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π) :
    Submodule.span K
        (Set.range (irreducibleCharacterOnGaloisPowerClasses K π hπ_complete)) =
      ⊤ := by
  apply le_antisymm
  · exact le_top
  · intro φ hφ
    let f : G → K := φ ∘ galoisPowerClassMk (Γ[K](G))
    have hf_scalar : f ∈ K⊗R[K](G) := by
      -- Pulling back a quotient function produces a `Γ[K](G)`-constant function, so Corollary
      -- `12-12.4-2` places it in `K ⊗ R[K](G)`.
      exact
        (classFunction_mem_characterRingOverFieldScalarExtension_iff_isConstantOnGaloisPowerClasses
          K f).2 inferInstance
    have hscalar_to_span :
        ∀ h : G → K, h ∈ K⊗R[K](G) →
          h ∈ Submodule.span K (Set.range fun i ↦ (π i).character) := by
      intro h hh
      -- First span in the ambient function space `G → K`; the generator case is the previous
      -- `R[K](G)` spanning lemma, and the scalar extension is now the source-correct `K`-span.
      induction hh using Submodule.span_induction with
      | mem χ hχ =>
          exact
            mem_span_irreducible_characters_of_mem_characterRingOverField
              K π hπ_pairwise hπ_complete (by simpa using hχ)
      | zero =>
          exact Submodule.zero_mem _
      | add f g _ _ hf hg =>
          exact Submodule.add_mem _ hf hg
      | smul a h _ hh =>
          exact Submodule.smul_mem _ a hh
    have hf_span :
        f ∈ Submodule.span K (Set.range fun i ↦ (π i).character) :=
      hscalar_to_span f hf_scalar
    rcases
        exists_mem_span_irreducibleCharacterOnGaloisPowerClasses_of_mem_span
          K π hπ_complete hf_span with
      ⟨ψ, hψ, hψ_eq⟩
    have hpullback_eq : ψ ∘ galoisPowerClassMk (Γ[K](G)) = φ ∘ galoisPowerClassMk (Γ[K](G)) := by
      simpa [f] using hψ_eq
    have hψφ : ψ = φ := by
      ext q
      obtain ⟨g, rfl⟩ := galoisPowerClassMk_surjective (Γ[K](G)) q
      simpa using congrFun hpullback_eq g
    simpa [hψφ] using hψ

/-- Corollary 12-12.4-3: the characters of the distinct irreducible `K`-representations of `G`
form a basis of the `K`-valued functions that are constant on Serre's `Γ_K`-classes of `G`. In
the canonical quotient-owner presentation used in this file, this is realized as a basis of the
function space on `GaloisPowerClass (Γ[K](G))`. -/
def irreducible_characters_basis_of_galoisPowerClassFunctions
    (π : ι → FDRep K G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π) :
    Module.Basis ι K (GaloisPowerClass (Γ[K](G)) → K) :=
  Module.Basis.mk
    (linearIndependent_irreducibleCharacterOnGaloisPowerClasses
      K π hπ_pairwise hπ_complete)
    ((span_irreducibleCharacterOnGaloisPowerClasses_eq_top
      K π hπ_pairwise hπ_complete).ge)

@[simp] theorem irreducible_characters_basis_of_galoisPowerClassFunctions_apply
    (π : ι → FDRep K G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (i : ι) :
    irreducible_characters_basis_of_galoisPowerClassFunctions K π hπ_pairwise hπ_complete i =
      irreducibleCharacterOnGaloisPowerClasses K π hπ_complete i := by
  exact Module.Basis.mk_apply _ _ _

@[simp] theorem irreducible_characters_basis_of_galoisPowerClassFunctions_comp_galoisPowerClassMk
    (π : ι → FDRep K G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (i : ι) :
    irreducible_characters_basis_of_galoisPowerClassFunctions K π hπ_pairwise hπ_complete i ∘
        galoisPowerClassMk (Γ[K](G)) =
      (π i).character := by
  rw [irreducible_characters_basis_of_galoisPowerClassFunctions_apply]
  exact
    irreducibleCharacterOnGaloisPowerClasses_comp_galoisPowerClassMk
      K π hπ_complete i

/-- The index set of a complete pairwise nonisomorphic irreducible family has the same
cardinality as the quotient `GaloisPowerClass (Γ[K](G))`. -/
theorem nat_card_irreducible_family_eq_nat_card_galoisPowerClass
    (π : ι → FDRep K G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π) :
    Nat.card ι = Nat.card (GaloisPowerClass (Γ[K](G))) := by
  letI : Finite (GaloisPowerClass (Γ[K](G))) :=
    Finite.of_surjective
      (galoisPowerClassMk (Γ[K](G)))
      (galoisPowerClassMk_surjective (Γ[K](G)))
  letI : Fintype (GaloisPowerClass (Γ[K](G))) := Fintype.ofFinite _
  let b : Module.Basis ι K (GaloisPowerClass (Γ[K](G)) → K) :=
    irreducible_characters_basis_of_galoisPowerClassFunctions K π hπ_pairwise hπ_complete
  letI : Finite ι := Module.Finite.finite_basis b
  letI : Fintype ι := Fintype.ofFinite ι
  calc
    Nat.card ι = Fintype.card ι := Nat.card_eq_fintype_card
    _ = Module.finrank K (GaloisPowerClass (Γ[K](G)) → K) :=
      (Module.finrank_eq_card_basis b).symm
    _ = Fintype.card (GaloisPowerClass (Γ[K](G))) := Module.finrank_fintype_fun_eq_card K
    _ = Nat.card (GaloisPowerClass (Γ[K](G))) := Nat.card_eq_fintype_card.symm

end RankOfRepresentationRing

end Representation
