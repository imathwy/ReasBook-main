import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap01.Definition_1_1_2_1
import LinearRepresentations_Serre_1977.Serre.Chap02.Remark_2_2_1_2
import LinearRepresentations_Serre_1977.Serre.Chap02.Theorem_2_2_5_2
import LinearRepresentations_Serre_1977.Serre.Chap07.Exercise_7_7_2_5
import LinearRepresentations_Serre_1977.Serre.Chap10.Definition_10_10_1_3
import LinearRepresentations_Serre_1977.Serre.Chap12.CharacterRingOverFieldScalarExtension
import LinearRepresentations_Serre_1977.Serre.Chap12.Proposition_12_12_1_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v w

namespace Representation

section CharacterRing

variable {G : Type u} [Group G]

scoped[Representation] notation:max "R(" G ")" => R[ℂ](G)

open scoped Representation

end CharacterRing

section FiniteRepCharacterRing

variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
/-- Helper for Theorem 11-11.2-1: conjugating a representation by a linear equivalence preserves
the identity element of the representation law. -/
theorem conj_representation_map_one
    {V : Type w} {W : Type v} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (e : V ≃ₗ[ℂ] W) (ρ : Representation ℂ G V) :
    e.conj (ρ 1) = 1 := by
  -- Replace `ρ 1` by the identity map, then use the standard conjugation identity.
  calc
    e.conj (ρ 1) = e.conj 1 := by rw [map_one]
    _ = 1 := LinearEquiv.conj_id e

omit [Finite G] in
/-- Helper for Theorem 11-11.2-1: conjugating a representation by a linear equivalence preserves
the multiplication law. -/
theorem conj_representation_map_mul
    {V : Type w} {W : Type v} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (e : V ≃ₗ[ℂ] W) (ρ : Representation ℂ G V) (g h : G) :
    e.conj (ρ (g * h)) = e.conj (ρ g) * e.conj (ρ h) := by
  -- Conjugation turns composition into composition, so the representation law is transported
  -- unchanged.
  rw [map_mul]
  ext x
  simp [LinearEquiv.conj_apply_apply]

omit [Finite G] in
/-- Helper for Theorem 11-11.2-1: move a finite-dimensional complex representation to the ambient
universe via a chosen finite basis. -/
def finBasis_representation
    {V : Type w} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) : Representation ℂ G (Fin (Module.finrank ℂ V) → ℂ) :=
  let e := (Module.finBasis ℂ V).equivFun
  { toFun := fun g ↦ e.conj (ρ g)
    map_one' := conj_representation_map_one (G := G) e ρ
    map_mul' := fun g h ↦ conj_representation_map_mul (G := G) e ρ g h }

omit [Finite G] in
/-- Helper for Theorem 11-11.2-1: transporting a representation to a finite-basis model does not
change its character. -/
theorem character_finBasis_representation_eq
    {V : Type w} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (g : G) :
    (finBasis_representation ρ).character g = ρ.character g := by
  -- Trace is invariant under conjugation, so the coordinate-model representation has the same
  -- character values.
  simpa [finBasis_representation, Representation.character] using
    (LinearMap.trace_conj' (ρ g) ((Module.finBasis ℂ V).equivFun))

omit [Finite G] in
/-- Helper for Theorem 11-11.2-1: a representation may be moved to the target carrier universe by
`ULift` without changing its action. -/
def ulift_representation
    {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) : Representation ℂ G (ULift.{u} V) where
  toFun g :=
    { toFun := fun x ↦ ⟨ρ g x.down⟩
      map_add' := by
        intro x y
        ext
        simp
      map_smul' := by
        intro a x
        ext
        simp }
  map_one' := by
    ext x
    simp
  map_mul' g h := by
    ext x
    simp [map_mul]

omit [Finite G] in
/-- Helper for Theorem 11-11.2-1: `ULift` preserves character values. -/
theorem character_ulift_representation_eq
    {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (g : G) :
    (ulift_representation (G := G) ρ).character g = ρ.character g := by
  -- The canonical linear equivalence `V ≃ ULift V` conjugates the lifted action back to the
  -- original operator.
  change
    LinearMap.trace ℂ (ULift.{u} V)
        ((ULift.moduleEquiv.symm : V ≃ₗ[ℂ] ULift.{u} V).conj (ρ g)) =
      LinearMap.trace ℂ V (ρ g)
  exact LinearMap.trace_conj' (ρ g) (ULift.moduleEquiv.symm : V ≃ₗ[ℂ] ULift.{u} V)

omit [Finite G] in
/-- The ordinary character of a finite-dimensional complex representation defines an element of
Serre's character ring `R(G)`. -/
theorem rep_character_mem_characterRing (ρ : Rep.{w} ℂ G) [FiniteDimensional ℂ ρ] :
    ρ.ρ.character ∈ R(G) := by
  let ρfin : Representation ℂ G (Fin (Module.finrank ℂ ρ) → ℂ) :=
    finBasis_representation ρ.ρ
  let τρ : Representation ℂ G (ULift.{u} (Fin (Module.finrank ℂ ρ) → ℂ)) :=
    ulift_representation (G := G) ρfin
  let τ : Rep.{u} ℂ G := Rep.of τρ
  -- Transport the character to the coordinate model, where the Chapter 12 owner theorem applies.
  have hchar : ρ.ρ.character = τ.ρ.character := by
    ext g
    calc
      ρ.ρ.character g = ρfin.character g := by
        symm
        simpa [ρfin] using character_finBasis_representation_eq (G := G) ρ.ρ g
      _ = τ.ρ.character g := by
        symm
        simpa [τ, τρ] using character_ulift_representation_eq (G := G) ρfin g
  exact hchar ▸ Representation.rep_character_mem_characterRingOverField (K := ℂ) (G := G) τ

end FiniteRepCharacterRing

end Representation

section FiniteRepCharacterRing

open scoped Representation

variable {G : Type u} [Group G] [Finite G]

namespace MonoidHom

/-- A degree-`1` complex character of a finite group, viewed in Serre's character ring `R(G)`. -/
abbrev toCharacterRing (ρ : G →* ℂˣ) : R(G) :=
  ⟨ρ.toRepresentation.character,
    Representation.rep_character_mem_characterRing (Rep.of ρ.toRepresentation)⟩

@[simp] theorem toCharacterRing_apply (ρ : G →* ℂˣ) (g : G) :
    (ρ.toCharacterRing : G → ℂ) g = (ρ g : ℂ) :=
  MonoidHom.toRepresentation_character_apply ρ g

end MonoidHom

end FiniteRepCharacterRing

namespace Representation

section AdamsOperator

variable {G : Type u} [Group G]
variable {A : Type v}

/-- Serre's Adams operator `Ψ^n` on `A`-valued class functions, defined by precomposition with the
`n`th-power map on `G`. -/
def adamsOperator (n : ℕ+) (f : G → A) : G → A :=
  fun g ↦ f (g ^ (n : ℕ))

scoped[Representation] notation:max "Ψ^" n "(" χ ")" => adamsOperator n χ

open scoped Representation

-- Proof sketch: if `u` and `v` are conjugate, then so are `u ^ n` and `v ^ n`; applying the
-- class-function property of `f` to those powers gives the result.
/-- Adams operators preserve the class-function condition. -/
theorem isClassFunction_adamsOperator (n : ℕ+) {f : G → A} (hf : _root_.IsClassFunction f) :
    _root_.IsClassFunction (Ψ^n(f)) := by
  -- Conjugacy is preserved by taking powers, so the class-function relation survives
  -- precomposition with the `n`th-power map.
  refine ⟨fun {x y} hxy ↦ ?_⟩
  have hxy_conj : IsConj x y := (ConjClasses.mk_eq_mk_iff_isConj).1 hxy
  simpa [adamsOperator] using _root_.IsClassFunction.eq_of_isConj hf (hxy_conj.pow (n : ℕ))

end AdamsOperator

section FrobeniusTheorem

open scoped Representation TensorProduct BigOperators SubgroupInduction

variable {G : Type u} [Group G]
variable {A : Type v} [CommRing A] [Algebra A ℂ]


/-- Helper for Theorem 11-11.2-1: a finite group has finitely many conjugacy classes. -/
local instance tensorCharacterBridge_conjClasses_fintype
    (H : Type w) [Group H] [Finite H] : Fintype (ConjClasses H) :=
  Fintype.ofFinite (ConjClasses H)

/-- Helper for Theorem 11-11.2-1: finite subgroups inherit their canonical `Fintype` structure. -/
local instance tensorCharacterBridge_subgroup_fintype [Finite G] (H : Subgroup G) : Fintype H :=
  Fintype.ofFinite H

-- Source/core/bridge triage:
-- * source-facing: Serre's tensor character ring `A ⊗ R(G)`.
-- * core/canonical: the tensor product owner `TensorProduct ℤ A (R(G))`.
-- * bridge/view: `characterRingScalarExtension A G`, the realized `A`-span in `G → ℂ`.
--
-- Primitive data: the tensor product owner and the integral character ring `R(G)`.
-- Derived API: the realized span in functions, the realization map into that span, and the
-- coercion from the owner to `G → ℂ`.
scoped[Representation] notation:max A " ⊗R(" G ")" => TensorProduct ℤ A (R(G))

/-- The ambient complex-function realization of Serre's tensor character ring. This is a
bridge/view of the owner `A ⊗R(G)`. -/
def characterRingScalarExtension (A : Type v) [CommRing A] [Algebra A ℂ]
    (G : Type u) [Group G] : Submodule A (G → ℂ) :=
  Submodule.span A (R(G) : Set (G → ℂ))

instance : CoeFun (A ⊗R(G)) (fun _ ↦ G → ℂ) where
  coe := (characterRingScalarExtension A G).subtype.comp (((R(G)).toSubmodule).tensorToSpan A)

@[simp] theorem coe_tmul (a : A) (χ : R(G)) :
    ((a ⊗ₜ[ℤ] χ : A ⊗R(G)) : G → ℂ) = a • (χ : G → ℂ) :=
  rfl

/-- Every realized tensor character belongs to the ambient span view
`characterRingScalarExtension A G`. -/
theorem tensorCharacterRing_mem_characterRingScalarExtension (χ : A ⊗R(G)) :
    (χ : G → ℂ) ∈ characterRingScalarExtension A G :=
  (((R(G)).toSubmodule).tensorToSpan A χ).property

-- Proof sketch: `χ` is one of the generators of the `A`-span defining
-- `characterRingScalarExtension A G`.
/-- Every element of Serre's integral character ring belongs to the complex-function realization of
its scalar extension to `A`. -/
theorem mem_characterRingScalarExtension_of_mem_characterRing
    (χ : G → ℂ) (hχ : χ ∈ R(G)) :
    χ ∈ characterRingScalarExtension A G :=
  Submodule.subset_span hχ

-- Proof sketch: the constant function with value `a` is `a` times the trivial character, so it
-- lies in the `A`-span of `R(G)`.
/-- Every scalar-valued constant function belongs to the complex-function realization of
`A ⊗ R(G)`. -/
theorem algebraMap_mem_characterRingScalarExtension (a : A) :
    algebraMap A (G → ℂ) a ∈ characterRingScalarExtension A G := by
  -- The constant function is the scalar multiple of the trivial character.
  have hone : (1 : G → ℂ) ∈ characterRingScalarExtension A G := by
    exact Submodule.subset_span ((R(G)).one_mem : (1 : G → ℂ) ∈ R(G))
  simpa [Pi.smul_apply, Algebra.smul_def] using
    (characterRingScalarExtension A G).smul_mem a hone

-- Proof sketch: every irreducible character is constant on conjugacy classes, and the defining
-- `A`-span preserves that property under addition and scalar multiplication.
/-- Every element of Serre's scalar extension `A ⊗ R(G)` is a class function. -/
theorem isClassFunction_of_mem_characterRingScalarExtension {f : G → ℂ}
    (hf : f ∈ characterRingScalarExtension A G) : _root_.IsClassFunction f := by
  induction hf using Submodule.span_induction with
  | mem ψ hψ =>
      have hψ' : ψ ∈ Representation.characterRingOverField ℂ G := hψ
      exact Representation.isClassFunction_of_mem_characterRingOverField (K := ℂ) ψ hψ'
  | zero =>
      refine ⟨fun {_ _} _ ↦ rfl⟩
  | add f g _ _ hf hg =>
      letI : _root_.IsClassFunction f := hf
      letI : _root_.IsClassFunction g := hg
      infer_instance
  | smul a f _ hf =>
      letI : _root_.IsClassFunction f := hf
      infer_instance

-- Proof sketch: the product of two ordinary characters is the character of a tensor product
-- representation, and bilinearity extends this closure to the whole scalar extension.
/-- Serre's scalar extension `A ⊗ R(G)` is closed under pointwise multiplication. -/
theorem mul_mem_characterRingScalarExtension {f g : G → ℂ}
    (hf : f ∈ characterRingScalarExtension A G) (hg : g ∈ characterRingScalarExtension A G) :
    f * g ∈ characterRingScalarExtension A G := by
  -- Expand both factors from the span definition and reduce to the product of two generators.
  revert g hg
  induction hf using Submodule.span_induction with
  | mem ψ hψ =>
      intro g hg
      induction hg using Submodule.span_induction with
      | mem φ hφ =>
          exact Submodule.subset_span ((R(G)).mul_mem hψ hφ)
      | zero =>
          simpa using (zero_mem (characterRingScalarExtension A G) : (0 : G → ℂ) ∈
            characterRingScalarExtension A G)
      | add g₁ g₂ _ _ ih₁ ih₂ =>
          simpa [Pi.mul_apply, mul_add] using
            (characterRingScalarExtension A G).add_mem ih₁ ih₂
      | smul a g _ ih =>
          simpa [Pi.mul_apply, Pi.smul_apply, Algebra.smul_def, mul_assoc, mul_left_comm,
            mul_comm] using
              (characterRingScalarExtension A G).smul_mem a ih
  | zero =>
      intro g hg
      simpa using (zero_mem (characterRingScalarExtension A G) : (0 : G → ℂ) ∈
        characterRingScalarExtension A G)
  | add f₁ f₂ _ _ ih₁ ih₂ =>
      intro g hg
      simpa [Pi.mul_apply, add_mul] using
        (characterRingScalarExtension A G).add_mem (ih₁ hg) (ih₂ hg)
  | smul a f _ ih =>
      intro g hg
      simpa [Pi.mul_apply, Pi.smul_apply, Algebra.smul_def, mul_assoc, mul_left_comm, mul_comm]
        using (characterRingScalarExtension A G).smul_mem a (ih hg)

/-- The pointwise `A`-subalgebra of complex-valued functions on `G` whose carrier is
`Representation.characterRingScalarExtension A G`. This is the canonical algebra-level bridge/view
of Serre's scalar extension `A ⊗ R(G)`. -/
def characterRingScalarExtensionSubalgebra
    (A : Type v) [CommRing A] [Algebra A ℂ] (G : Type u) [Group G] :
    Subalgebra A (G → ℂ) :=
  (characterRingScalarExtension A G).toSubalgebra
    (by
      simpa using algebraMap_mem_characterRingScalarExtension (1 : A))
    (fun f g ↦ mul_mem_characterRingScalarExtension)

/-- The canonical `A`-algebra hom from Serre's tensor character ring to its algebra-level
realization inside complex-valued functions on `G`. -/
noncomputable def tensorCharacterRingToSubalgebra
    (A : Type v) [CommRing A] [Algebra A ℂ] (G : Type u) [Group G] :
    A ⊗R(G) →ₐ[A] characterRingScalarExtensionSubalgebra A G :=
  (AlgHom.liftEquiv ℤ A (R(G)) (characterRingScalarExtensionSubalgebra A G))
    { toFun := fun χ ↦
        ⟨(χ : G → ℂ),
          mem_characterRingScalarExtension_of_mem_characterRing
            (χ : G → ℂ) χ.property⟩
      map_one' := by
        ext g
        rfl
      map_mul' := fun χ ψ ↦ by
        ext g
        rfl
      map_zero' := by
        ext g
        rfl
      map_add' := fun χ ψ ↦ by
        ext g
        rfl
      commutes' := fun n ↦ by
        ext g
        simp }

omit [Algebra A ℂ] in
/-- Helper for Theorem 11-11.2-1: restricting an `A`-valued bundled class function to a subgroup
preserves the class-function condition. -/
theorem subgroup_classFunctionRestriction_mem
    (H : Subgroup G) (f : classFunctionSubmodule A G) :
    (fun h : H ↦ f h) ∈ classFunctionSubmodule A H := by
  -- Restriction only changes the ambient carrier; conjugacy inside `H` is conjugacy inside `G`.
  let hf : _root_.IsClassFunction (f : G → A) := (mem_classFunctionSubmodule_iff A _).1 f.2
  refine (mem_classFunctionSubmodule_iff A _).2 ?_
  refine ⟨fun {x y} hxy ↦ ?_⟩
  have hxyH : IsConj x y := (ConjClasses.mk_eq_mk_iff_isConj).1 hxy
  have hxyG : IsConj (x : G) (y : G) := by
    rw [isConj_iff] at hxyH ⊢
    rcases hxyH with ⟨c, hc⟩
    exact ⟨(c : G), by simpa using congrArg Subtype.val hc⟩
  exact _root_.IsClassFunction.eq_of_isConj hf hxyG

omit [Algebra A ℂ] in
/-- Helper for Theorem 11-11.2-1: subgroup restriction of an `A`-valued bundled class function. -/
def subgroupClassFunctionRestriction
    (H : Subgroup G) (f : classFunctionSubmodule A G) : classFunctionSubmodule A H :=
  ⟨fun h ↦ f h, subgroup_classFunctionRestriction_mem (A := A) H f⟩

/-- Helper for Theorem 11-11.2-1: multiplying an induced class function by the ambient class
function equals inducing the product with the canonical subgroup restriction. -/
theorem induced_mul_eq_induced_mul_classFunctionRestriction
    [Finite G] (H : Subgroup G) (ψ : H → ℂ) (φ : classFunctionSubmodule ℂ G) :
    Ind[H](ψ) * (φ : G → ℂ) =
      Ind[H](fun h : H ↦ ψ h * (H.classFunctionRestriction φ : H → ℂ) h) := by
  classical
  -- Compare both sides pointwise and replace the ambient value of `φ` by its conjugacy-invariant
  -- subgroup value on each induction summand.
  ext x
  simp only [Pi.mul_apply, Subgroup.inducedClassFunction]
  rw [mul_assoc, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro s hs_univ
  by_cases hs : s⁻¹ * x * s ∈ H
  · have hs' : s⁻¹ * (x * s) ∈ H := by
      simpa [mul_assoc] using hs
    have hφ :
        (φ : G → ℂ) (s⁻¹ * x * s) = (φ : G → ℂ) x := by
      exact _root_.IsClassFunction.eq_of_isConj ((mem_classFunctionSubmodule_iff ℂ _).1 φ.2) <|
        isConj_iff.2 ⟨s, by group⟩
    have hφ' :
        (φ : G → ℂ) (s⁻¹ * (x * s)) = (φ : G → ℂ) x := by
      simpa [mul_assoc] using hφ
    simp [hs', hφ', mul_comm, mul_assoc]
  · simp [hs]

/-- Helper for Theorem 11-11.2-1: every realized element of the scalar extension comes from an
actual tensor character. -/
theorem tensorCharacter_exists_of_mem_characterRingScalarExtension
    {f : G → ℂ} (hf : f ∈ characterRingScalarExtension A G) :
    ∃ χ : A ⊗R(G), (χ : G → ℂ) = f := by
  let fχ : characterRingScalarExtension A G := ⟨f, hf⟩
  obtain ⟨χ, hχ⟩ := (R(G)).toSubmodule.surjective_tensorToSpan A fχ
  change A ⊗R(G) at χ
  change (R(G)).toSubmodule.tensorToSpan A χ = fχ at hχ
  -- Forget the subtype after surjectivity of the realization map.
  refine ⟨χ, ?_⟩
  simpa [fχ] using congrArg ((↑) : characterRingScalarExtension A G → G → ℂ) hχ

/-- Helper for Theorem 11-11.2-1: subgroup induction sends the realized scalar extension
`A ⊗ R(H)` into `A ⊗ R(G)`. -/
theorem induced_mem_characterRingScalarExtension_of_mem
    [Finite G] (H : Subgroup G) {f : H → ℂ}
    (hf : f ∈ characterRingScalarExtension A H) :
    Ind[H](f) ∈ characterRingScalarExtension A G := by
  -- Induct over the defining `A`-span on `H`, reducing to honest induced characters.
  induction hf using Submodule.span_induction with
  | mem χ hχ =>
      exact mem_characterRingScalarExtension_of_mem_characterRing (A := A) (Ind[H](χ)) <|
        _root_.Subgroup.inducedClassFunction_mem_characterRingOverField (K := ℂ) H ⟨χ, hχ⟩
  | zero =>
      have hzero : Ind[H]((0 : H → ℂ)) = (0 : G → ℂ) := by
        ext g
        simp [Subgroup.inducedClassFunction]
      rw [hzero]
      exact
        (zero_mem (characterRingScalarExtension A G) :
          (0 : G → ℂ) ∈ characterRingScalarExtension A G)
  | add f g _ _ hf hg =>
      simpa [Subgroup.inducedClassFunction_map_add] using
        (characterRingScalarExtension A G).add_mem hf hg
  | smul a f _ hf =>
      simpa [Subgroup.inducedClassFunction_map_smul] using
        (characterRingScalarExtension A G).smul_mem a hf

/-- Helper for Theorem 11-11.2-1: inducing an integral virtual character on a subgroup gives an
integral virtual character on the ambient group. -/
theorem Subgroup.inducedClassFunction_mem_characterRing_local
    [Finite G] (H : Subgroup G) (χ : R(H)) :
    Ind[H]((χ : H → ℂ)) ∈ R(G) := by
  -- This is the complex specialization of the subgroup-induction character theorem.
  simpa using _root_.Subgroup.inducedClassFunction_mem_characterRingOverField (K := ℂ) H χ

/-- Helper for Theorem 11-11.2-1: the canonical subgroup-induction map on Serre's integral
character rings. -/
def Subgroup.characterRingInduction_local
    [Finite G] (H : Subgroup G) :
    R(H) →ₗ[ℤ] R(G) where
  toFun χ := ⟨Ind[H]((χ : H → ℂ)),
    Subgroup.inducedClassFunction_mem_characterRing_local (G := G) H χ⟩
  map_add' χ ψ := by
    have h_add :=
      (((classFunctionSubmodule ℂ G).subtype.comp H.classFunctionInduction).restrictScalars ℤ).map_add
        (χ : H → ℂ) (ψ : H → ℂ)
    ext g
    exact congrFun h_add g
  map_smul' n χ := by
    have h_smul :=
      (((classFunctionSubmodule ℂ G).subtype.comp H.classFunctionInduction).restrictScalars ℤ).map_smul
        n (χ : H → ℂ)
    ext g
    exact congrFun h_smul g

/-- Helper for Theorem 11-11.2-1: evaluating the local subgroup-induction map recovers the
induced complex-valued class function. -/
@[simp] theorem Subgroup.characterRingInduction_local_apply
    [Finite G] (H : Subgroup G) (χ : R(H)) :
    ((Subgroup.characterRingInduction_local (G := G) H χ : R(G)) : G → ℂ) =
      Ind[H]((χ : H → ℂ)) :=
  rfl

/-- Helper for Theorem 11-11.2-1: the owner submodule generated by the induction maps from a
finite family of subgroups. -/
def artinInducedCharacterSubmodule_local
    [Finite G] (X : Finset (Subgroup G)) : Submodule ℤ (R(G)) :=
  ⨆ H : X, LinearMap.range (Subgroup.characterRingInduction_local (G := G) H.1)

/-- Helper for Theorem 11-11.2-1: an induction generator from a subgroup in `X` already lies in
the theorem-local Artin-induction owner generated by `X`. -/
theorem characterRingInduction_mem_artinInducedCharacterSubmodule_local
    [Finite G] {X : Finset (Subgroup G)} {H : Subgroup G} (hH : H ∈ X) (χ : R(H)) :
    Subgroup.characterRingInduction_local (G := G) H χ ∈
      artinInducedCharacterSubmodule_local (G := G) X := by
  -- Insert the subgroup-induced character into the corresponding range summand of the local
  -- supremum.
  exact
    (show LinearMap.range (Subgroup.characterRingInduction_local (G := G) H) ≤
        artinInducedCharacterSubmodule_local (G := G) X from
      le_iSup
        (fun K : X ↦ LinearMap.range (Subgroup.characterRingInduction_local (G := G) K.1))
        ⟨H, hH⟩) ⟨χ, rfl⟩

/-- Helper for Theorem 11-11.2-1: Brauer's subgroup `V_p` realized locally from the induction
ranges attached to the `p`-elementary subgroups. -/
abbrev pElementaryInducedCharacterSpan_local
    [Finite G] (p : ℕ) : Submodule ℤ (R(G)) :=
  let _ : DecidablePred fun H : Subgroup G ↦ IsPElementary p H := Classical.decPred _
  artinInducedCharacterSubmodule_local
    (Finset.univ.filter fun H : Subgroup G ↦ IsPElementary p H)

/-- Helper for Theorem 11-11.2-1: the unit character acts trivially on class functions by
pointwise multiplication. -/
theorem one_character_mul_classFunction [Finite G] (φ : classFunctionSubmodule ℂ G) :
    ((1 : R(G)) : G → ℂ) * (φ : G → ℂ) = (φ : G → ℂ) := by
  -- Evaluate pointwise: the unit character has constant value `1`.
  ext x
  simp

/-- Helper for Theorem 11-11.2-1: restricting a realized scalar-extension class function to a
subgroup preserves realized scalar-extension membership. -/
theorem classFunctionRestriction_mem_characterRingScalarExtension_local
    [Finite G] (H : Subgroup G) {η : G → ℂ}
    (hη : η ∈ characterRingScalarExtension A G) :
    (fun h : H ↦ η h) ∈ characterRingScalarExtension A H := by
  -- Restrict the defining span generator-by-generator along the subgroup inclusion.
  rw [characterRingScalarExtension] at hη ⊢
  refine
    Submodule.span_induction
      (s := (R(G) : Set (G → ℂ)))
      (p := fun ψ _ ↦
        (fun h : H ↦ ψ h) ∈ Submodule.span A (R(H) : Set (H → ℂ)))
      ?_ ?_ ?_ ?_ hη
  · intro ψ hψ
    have hres : (fun h : H ↦ ψ h) ∈ R(H) := by
      -- Honest characters stay honest after subgroup restriction, and `R(H)` is generated by
      -- those honest characters.
      refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ hψ
      · intro χ hχ
        rcases hχ with ⟨σ, hσfd, _hσirr, rfl⟩
        letI : FiniteDimensional ℂ σ := hσfd
        simpa using
          (Representation.rep_character_mem_characterRing
            (Rep.res H.subtype (Rep.of σ.ρ)))
      · intro n
        exact (R(H)).algebraMap_mem n
      · intro f g _ _ hf hg
        simpa using (R(H)).add_mem hf hg
      · intro f g _ _ hf hg
        simpa using (R(H)).mul_mem hf hg
    exact Submodule.subset_span hres
  · exact Submodule.zero_mem (Submodule.span A (R(H) : Set (H → ℂ)))
  · intro ψ ξ _ _ hψ hξ
    simpa using (Submodule.add_mem (Submodule.span A (R(H) : Set (H → ℂ))) hψ hξ)
  · intro a ψ _ hψ
    simpa using (Submodule.smul_mem (Submodule.span A (R(H) : Set (H → ℂ))) a hψ)

/-- Helper for Theorem 11-11.2-1: Brauer's elementary-subgroup detection lifts a class function
from realized elementary restrictions to the global tensor character ring. -/
theorem pElementaryInducedCharacterSpan_mul_classFunction_mem_characterRingScalarExtension_local
    [Finite G] (φ : classFunctionSubmodule ℂ G)
    (hres : ∀ H : Subgroup G, IsElementary H →
      (fun h : H ↦ (φ : G → ℂ) h) ∈ characterRingScalarExtension A H)
    (p : Nat.Primes) {χ : R(G)}
    (hχ : χ ∈ pElementaryInducedCharacterSpan_local (G := G) (p : ℕ)) :
    ((χ : G → ℂ) * (φ : G → ℂ)) ∈ characterRingScalarExtension A G := by
  classical
  let _ : DecidablePred (fun H : Subgroup G ↦ IsPElementary (p : ℕ) H) := Classical.decPred _
  -- Rewrite `V[p](G)` as the supremum of induction ranges from `p`-elementary subgroups.
  change χ ∈
      artinInducedCharacterSubmodule_local (G := G)
        (Finset.univ.filter fun H : Subgroup G ↦ IsPElementary (p : ℕ) H) at hχ
  rw [artinInducedCharacterSubmodule_local] at hχ
  refine Submodule.iSup_induction
      (p := fun H :
        { H : Subgroup G |
          H ∈ Finset.filter (fun H : Subgroup G ↦ IsPElementary (p : ℕ) H) Finset.univ } ↦
        LinearMap.range (Subgroup.characterRingInduction_local (G := G) H.1))
      (motive := fun ξ : R(G) ↦
        ((ξ : G → ℂ) * (φ : G → ℂ)) ∈ characterRingScalarExtension A G)
      hχ ?_ ?_ ?_
  · intro H ξ hξ
    rcases H with ⟨H, hHmem⟩
    rcases hξ with ⟨η, rfl⟩
    have hH : IsPElementary (p : ℕ) H := by
      simpa using (Finset.mem_filter.mp hHmem).2
    have hη :
        ((η : R(H)) : H → ℂ) ∈ characterRingScalarExtension A H :=
      mem_characterRingScalarExtension_of_mem_characterRing (A := A) _ η.property
    have hφH :
        (H.classFunctionRestriction φ : H → ℂ) ∈ characterRingScalarExtension A H := by
      simpa using hres H ⟨p, hH⟩
    have hmul :
        ((η : R(H)) : H → ℂ) * (H.classFunctionRestriction φ : H → ℂ) ∈
          characterRingScalarExtension A H :=
      mul_mem_characterRingScalarExtension hη hφH
    have hind :
        Ind[H]((((η : R(H)) : H → ℂ) * (H.classFunctionRestriction φ : H → ℂ))) ∈
          characterRingScalarExtension A G :=
      induced_mem_characterRingScalarExtension_of_mem (A := A) H hmul
    -- Turn the subgroup-induced generator into the corresponding global product.
    rw [Subgroup.characterRingInduction_local_apply (G := G),
      induced_mul_eq_induced_mul_classFunctionRestriction]
    exact hind
  · simpa using zero_mem (characterRingScalarExtension A G)
  · intro ξ η hξ hη
    simpa [add_mul] using (characterRingScalarExtension A G).add_mem hξ hη

/-- Helper for Theorem 11-11.2-1: Brauer's elementary-subgroup detection lifts a class function
from realized elementary restrictions to the global tensor character ring once the Chapter 10
Brauer span identity is available. -/
theorem classFunction_lifts_to_tensorCharacterRing_of_restrict_mem_on_elementarySubgroups_of_brauer_span
    [Finite G]
    (hbrauer :
      (⨆ p : Nat.Primes, pElementaryInducedCharacterSpan_local (G := G) (p : ℕ)) = ⊤)
    (φ : classFunctionSubmodule ℂ G)
    (hres : ∀ H : Subgroup G, IsElementary H →
      (fun h : H ↦ (φ : G → ℂ) h) ∈ characterRingScalarExtension A H) :
    ∃ ψ : A ⊗R(G), (ψ : G → ℂ) = (φ : G → ℂ) := by
  have hone :
      ((1 : R(G)) : G → ℂ) * (φ : G → ℂ) ∈ characterRingScalarExtension A G := by
    have hone' :
        (1 : R(G)) ∈
          (⨆ p : Nat.Primes, pElementaryInducedCharacterSpan_local (G := G) (p : ℕ)) := by
      have hone_top : (1 : R(G)) ∈ (⊤ : Submodule ℤ (R(G))) := by
        simp
      simpa [hbrauer] using hone_top
    -- Once the unit character lies in Brauer's supremum, `iSup`-induction reduces the claim to
    -- the local `V[p]` multiplication theorem proved above.
    refine Submodule.iSup_induction
        (p := fun p : Nat.Primes ↦ pElementaryInducedCharacterSpan_local (G := G) (p : ℕ))
        (motive := fun χ : R(G) ↦
          ((χ : G → ℂ) * (φ : G → ℂ)) ∈ characterRingScalarExtension A G)
        hone' ?_ ?_ ?_
    · intro p χ hχ
      exact
        pElementaryInducedCharacterSpan_mul_classFunction_mem_characterRingScalarExtension_local
          (A := A) φ hres p hχ
    · simpa using zero_mem (characterRingScalarExtension A G)
    · intro χ ψ hχ hψ
      simpa [add_mul] using (characterRingScalarExtension A G).add_mem hχ hψ
  have hφ : (φ : G → ℂ) ∈ characterRingScalarExtension A G := by
    -- The unit character acts trivially, so the `V[p]`-induction output is exactly `φ`.
    rw [← one_character_mul_classFunction φ]
    exact hone
  -- Convert the realized-span membership back to an owner element of `A ⊗ R(G)`.
  exact tensorCharacter_exists_of_mem_characterRingScalarExtension (A := A) hφ

end FrobeniusTheorem

end Representation
