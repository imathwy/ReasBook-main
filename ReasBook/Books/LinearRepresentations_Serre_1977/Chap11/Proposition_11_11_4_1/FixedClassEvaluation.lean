import LinearRepresentations_Serre_1977.Chap06.Proposition_6_6_5_1
import LinearRepresentations_Serre_1977.Chap11.Proposition_11_11_4_1.ConjClassFunctionRealization

-- Stable fixed-class evaluation helpers extracted from Proposition 11-11.4-1.

universe u v

noncomputable section

open Representation
open scoped Representation SubgroupInduction TensorProduct

namespace Proposition_11_11_4_1

section

variable {G : Type} [Group G]
variable {A : Type v} [CommRing A]
variable [Finite G] [Algebra A ℂ]

local instance fixedClassEvaluationFintypeGroup : Fintype G := Fintype.ofFinite G
local instance fixedClassEvaluationFintypeSubgroup (H : Subgroup G) : Fintype H :=
  Fintype.ofFinite H

local notation "P0" => tensorCharacterRingZeroPrimeIdeal

/-- Helper for Proposition 11-11.4-1: choose a representative of a conjugacy class. This keeps
the source-side fixed-class evaluation route concrete without unfolding quotient recursion in the
main proofs. -/
def conjClassRepresentative
    (c : ConjClasses G) : G :=
  Classical.choose (ConjClasses.mk_surjective c)

/-- Helper for Proposition 11-11.4-1: the chosen representative maps back to the original
conjugacy class. -/
theorem conjClassRepresentative_mk
    (c : ConjClasses G) :
    ConjClasses.mk (conjClassRepresentative (G := G) c) = c :=
  Classical.choose_spec (ConjClasses.mk_surjective c)

/-- Helper for Proposition 11-11.4-1: evaluating a realized tensor character at the chosen
representative gives a concrete complex-valued ring hom on `A ⊗ R(G)`. This is the fixed-class
evaluation map used by the source proof. -/
def tensorCharacterRingValueAtConjClassComplex
    (c : ConjClasses G) :
    A ⊗R(G) →+* ℂ where
  toFun χ :=
    ((tensorCharacterRingToSubalgebra A G χ :
        characterRingScalarExtensionSubalgebra A G) : G → ℂ)
      (conjClassRepresentative (G := G) c)
  map_one' := by
    simp [conjClassRepresentative]
  map_mul' χ ψ := by
    simp [conjClassRepresentative]
  map_zero' := by
    simp [conjClassRepresentative]
  map_add' χ ψ := by
    simp [conjClassRepresentative]

/-- Helper for Proposition 11-11.4-1: the fixed-class complex evaluation can be computed at any
representative of the same conjugacy class. -/
theorem tensorCharacterRingValueAtConjClassComplex_eq_of_mk_eq
    (c : ConjClasses G) (χ : A ⊗R(G)) {x : G} (hx : ConjClasses.mk x = c) :
    tensorCharacterRingValueAtConjClassComplex (A := A) (G := G) c χ =
      ((tensorCharacterRingToSubalgebra A G χ :
          characterRingScalarExtensionSubalgebra A G) : G → ℂ) x := by
  let f : G → ℂ :=
    ((tensorCharacterRingToSubalgebra A G χ :
        characterRingScalarExtensionSubalgebra A G) : G → ℂ)
  have hf : _root_.IsClassFunction f := by
    exact
      isClassFunction_of_mem_characterRingScalarExtension
        (show f ∈ characterRingScalarExtension A G from
          (tensorCharacterRingToSubalgebra A G χ).2)
  have hrepr :
      ConjClasses.mk (conjClassRepresentative (G := G) c) = ConjClasses.mk x := by
    rw [conjClassRepresentative_mk (G := G) c, hx]
  exact hf.eq_of_isConj (ConjClasses.mk_eq_mk_iff_isConj.mp hrepr)

/-- Helper for Proposition 11-11.4-1: scalar tensors evaluate to the same scalar under the
fixed-class complex evaluation. -/
theorem tensorCharacterRingValueAtConjClassComplex_algebraMap
    (c : ConjClasses G) (a : A) :
    tensorCharacterRingValueAtConjClassComplex (A := A) (G := G) c
      ((algebraMap A (A ⊗R(G))) a) = algebraMap A ℂ a := by
  simpa [tensorCharacterRingValueAtConjClassComplex, conjClassRepresentative] using
    congrArg
      (fun f : characterRingScalarExtensionSubalgebra A G ↦
        ((f : G → ℂ) (conjClassRepresentative (G := G) c)))
      ((tensorCharacterRingToSubalgebra A G).commutes a)

/-- Helper for Proposition 11-11.4-1: every value of a virtual character of `G` is an algebraic
integer. This is the light dependency-closed integrality input needed to build the fixed-class
evaluation bridge without importing later Chapter `11` files. -/
theorem characterRing_value_isIntegral_local
    (χ : R(G)) (x : G) :
    IsIntegral ℤ (χ x) := by
  refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ χ.property
  · rintro ψ ⟨ρ, hρfd, _hρirr, rfl⟩
    letI : FiniteDimensional ℂ ρ := hρfd
    simpa using Representation.char_isIntegral ρ.ρ x
  · intro n
    simpa using (isIntegral_algebraMap : IsIntegral ℤ (algebraMap ℤ ℂ n))
  · intro f g hf hg hf_int hg_int
    exact hf_int.add hg_int
  · intro f g hf hg hf_int hg_int
    exact hf_int.mul hg_int

section IntegralClosureFixedClassEvaluation

variable [IsIntegralClosure A ℤ ℂ]

/-- Helper for Proposition 11-11.4-1: evaluating an integral character at a representative of `c`
already lands in the arithmetic coefficient ring `A`. This is the coefficient-side source bridge
for the fixed-class evaluation map. -/
theorem characterRingValueAtConjClass_mem_range
    (c : ConjClasses G) (χ : R(G)) :
    (χ (conjClassRepresentative (G := G) c) : ℂ) ∈ Set.range (algebraMap A ℂ) := by
  exact
    (IsIntegralClosure.isIntegral_iff (A := A) (R := ℤ) (B := ℂ)).mp
      (characterRing_value_isIntegral_local (G := G) χ
        (conjClassRepresentative (G := G) c))

/-- Helper for Proposition 11-11.4-1: evaluation on the chosen representative lifts from the
ordinary character ring `R(G)` to an `A`-valued algebra map. -/
def characterRingValueAtConjClass
    (c : ConjClasses G) :
    R(G) →ₐ[ℤ] A where
  toFun χ := Classical.choose (characterRingValueAtConjClass_mem_range (A := A) (G := G) c χ)
  map_zero' := by
    apply IsIntegralClosure.algebraMap_injective A ℤ ℂ
    simpa using
      (Classical.choose_spec
        (characterRingValueAtConjClass_mem_range (A := A) (G := G) c 0))
  map_one' := by
    apply IsIntegralClosure.algebraMap_injective A ℤ ℂ
    simpa using
      (Classical.choose_spec
        (characterRingValueAtConjClass_mem_range (A := A) (G := G) c 1))
  map_add' χ ψ := by
    apply IsIntegralClosure.algebraMap_injective A ℤ ℂ
    have hχ :=
      Classical.choose_spec
        (characterRingValueAtConjClass_mem_range (A := A) (G := G) c χ)
    have hψ :=
      Classical.choose_spec
        (characterRingValueAtConjClass_mem_range (A := A) (G := G) c ψ)
    have hχψ :=
      Classical.choose_spec
        (characterRingValueAtConjClass_mem_range (A := A) (G := G) c (χ + ψ))
    calc
      algebraMap A ℂ
          (Classical.choose
            (characterRingValueAtConjClass_mem_range (A := A) (G := G) c (χ + ψ))) =
          (χ + ψ) (conjClassRepresentative (G := G) c) := hχψ
      _ = χ (conjClassRepresentative (G := G) c) +
            ψ (conjClassRepresentative (G := G) c) := by
            simp
      _ = algebraMap A ℂ
            (Classical.choose
              (characterRingValueAtConjClass_mem_range (A := A) (G := G) c χ)) +
          algebraMap A ℂ
            (Classical.choose
              (characterRingValueAtConjClass_mem_range (A := A) (G := G) c ψ)) := by
            rw [hχ, hψ]
      _ = algebraMap A ℂ
            (Classical.choose
                (characterRingValueAtConjClass_mem_range (A := A) (G := G) c χ) +
              Classical.choose
                (characterRingValueAtConjClass_mem_range (A := A) (G := G) c ψ)) := by
            rw [map_add]
  map_mul' χ ψ := by
    apply IsIntegralClosure.algebraMap_injective A ℤ ℂ
    have hχ :=
      Classical.choose_spec
        (characterRingValueAtConjClass_mem_range (A := A) (G := G) c χ)
    have hψ :=
      Classical.choose_spec
        (characterRingValueAtConjClass_mem_range (A := A) (G := G) c ψ)
    have hχψ :=
      Classical.choose_spec
        (characterRingValueAtConjClass_mem_range (A := A) (G := G) c (χ * ψ))
    calc
      algebraMap A ℂ
          (Classical.choose
            (characterRingValueAtConjClass_mem_range (A := A) (G := G) c (χ * ψ))) =
          (χ * ψ) (conjClassRepresentative (G := G) c) := hχψ
      _ = χ (conjClassRepresentative (G := G) c) *
            ψ (conjClassRepresentative (G := G) c) := by
            simp
      _ = algebraMap A ℂ
            (Classical.choose
              (characterRingValueAtConjClass_mem_range (A := A) (G := G) c χ)) *
          algebraMap A ℂ
            (Classical.choose
              (characterRingValueAtConjClass_mem_range (A := A) (G := G) c ψ)) := by
            rw [hχ, hψ]
      _ = algebraMap A ℂ
            (Classical.choose
                (characterRingValueAtConjClass_mem_range (A := A) (G := G) c χ) *
              Classical.choose
                (characterRingValueAtConjClass_mem_range (A := A) (G := G) c ψ)) := by
            rw [map_mul]
  commutes' n := by
    apply IsIntegralClosure.algebraMap_injective A ℤ ℂ
    simpa using
      (Classical.choose_spec
        (characterRingValueAtConjClass_mem_range (A := A) (G := G) c
          (algebraMap ℤ (R(G)) n)))

/-- Helper for Proposition 11-11.4-1: after scalar extension to `ℂ`, the `A`-valued evaluation on
`R(G)` agrees with ordinary character evaluation at the chosen representative of `c`. -/
theorem characterRingValueAtConjClass_algebraMap
    (c : ConjClasses G) (χ : R(G)) :
    algebraMap A ℂ (characterRingValueAtConjClass (A := A) (G := G) c χ) =
      (χ (conjClassRepresentative (G := G) c) : ℂ) :=
  Classical.choose_spec (characterRingValueAtConjClass_mem_range (A := A) (G := G) c χ)

/-- Helper for Proposition 11-11.4-1: tensoring the identity on `A` with fixed-class evaluation on
`R(G)` gives an `A`-valued evaluation map on `A ⊗ R(G)`. -/
def tensorCharacterRingValueAtConjClass
    (c : ConjClasses G) :
    A ⊗R(G) →ₐ[ℤ] A :=
  Algebra.TensorProduct.productMap
    (AlgHom.id ℤ A)
    (characterRingValueAtConjClass (A := A) (G := G) c)

/-- Helper for Proposition 11-11.4-1: the tensor-product evaluation sends a scalar tensor to the
same scalar in `A`. -/
theorem tensorCharacterRingValueAtConjClass_algebraMap
    (c : ConjClasses G) (a : A) :
    tensorCharacterRingValueAtConjClass (A := A) (G := G) c
      ((algebraMap A (A ⊗R(G))) a) = a := by
  simp [tensorCharacterRingValueAtConjClass]

/-- Helper for Proposition 11-11.4-1: after applying `A → ℂ`, the `A`-valued tensor-product
evaluation becomes the corresponding complex evaluation at the chosen representative. -/
theorem tensorCharacterRingValueAtConjClass_complex_eq
    (c : ConjClasses G) (χ : A ⊗R(G)) :
    algebraMap A ℂ (tensorCharacterRingValueAtConjClass (A := A) (G := G) c χ) =
      tensorCharacterRingValueAtConjClassComplex (A := A) (G := G) c χ := by
  let f : A ⊗R(G) →ₐ[A] ℂ :=
    { toRingHom := (algebraMap A ℂ).comp
        (tensorCharacterRingValueAtConjClass (A := A) (G := G) c).toRingHom
      commutes' := by
        intro a
        exact congrArg (algebraMap A ℂ)
          (tensorCharacterRingValueAtConjClass_algebraMap (A := A) (G := G) c a) }
  let g : A ⊗R(G) →ₐ[A] ℂ :=
    { toRingHom := tensorCharacterRingValueAtConjClassComplex (A := A) (G := G) c
      commutes' := tensorCharacterRingValueAtConjClassComplex_algebraMap (A := A) (G := G) c }
  have hright :
      (AlgHom.restrictScalars ℤ f).comp
          (Algebra.TensorProduct.includeRight (R := ℤ) (A := A) (B := R(G))) =
        (AlgHom.restrictScalars ℤ g).comp
          (Algebra.TensorProduct.includeRight (R := ℤ) (A := A) (B := R(G))) := by
    ext ψ
    simp [f, g, tensorCharacterRingValueAtConjClass,
      characterRingValueAtConjClass_algebraMap]
    simpa [tensorCharacterRingToSubalgebra] using
      (tensorCharacterRingValueAtConjClassComplex_eq_of_mk_eq
        (A := A) (G := G) c
        ((Algebra.TensorProduct.includeRight (R := ℤ) (A := A) (B := R(G))) ψ)
        (conjClassRepresentative_mk (G := G) c)).symm
  have hfg : f = g := Algebra.TensorProduct.ext_ring hright
  exact congrArg (fun h : A ⊗R(G) →ₐ[A] ℂ ↦ h χ) hfg

end IntegralClosureFixedClassEvaluation

/-- Helper for Proposition 11-11.4-1: LinearRepresentations_Serre_1977's zero prime `P₀,c` is the kernel of the concrete
fixed-class evaluation map at any representative of `c`. This is the source-facing identification
used when reducing the zero branch to coordinate kernels. -/
theorem tensorCharacterRingZeroPrimeIdealEval_eq_valueAtConjClassComplex
    (c : ConjClasses G) :
    tensorCharacterRingZeroPrimeIdealEval A c =
      tensorCharacterRingValueAtConjClassComplex (A := A) (G := G) c := by
  apply RingHom.ext
  intro z
  obtain ⟨x, hx⟩ := ConjClasses.mk_surjective c
  calc
    tensorCharacterRingZeroPrimeIdealEval A c z =
        ((tensorCharacterRingToSubalgebra A G z :
            characterRingScalarExtensionSubalgebra A G) : G → ℂ) x := by
              rw [show c = ConjClasses.mk x by symm; exact hx]
              rfl
    _ = tensorCharacterRingValueAtConjClassComplex (A := A) (G := G) c z := by
          symm
          exact
            tensorCharacterRingValueAtConjClassComplex_eq_of_mk_eq
              (A := A) (G := G) c z hx

/-- Helper for Proposition 11-11.4-1: every complex-valued function on `ConjClasses G` is the
conjugacy-class evaluation profile of some complex tensor character. This closes the easy complex
side of the zero-branch realization route; only the missing coefficient-descent step from complex
values back to the bottom residue field remains. -/
theorem surjective_tensorCharacterRing_to_conjClasses_complex :
    Function.Surjective
      ((classFunctionSubalgebraEvalConjClasses_complex (G := G)).comp
        (tensorCharacterRingToSubalgebra ℂ G)) := by
  intro F
  let f : characterRingScalarExtensionSubalgebra ℂ G :=
    ⟨fun g ↦ F (ConjClasses.mk g),
      classFunction_mem_characterRingScalarExtension_complex
        (G := G) (fun g ↦ F (ConjClasses.mk g))
        ⟨by
          intro x y hxy
          exact congrArg F hxy⟩⟩
  obtain ⟨χ, hχ⟩ := surjective_tensorCharacterRingToSubalgebra (A := ℂ) (G := G) f
  refine ⟨χ, ?_⟩
  ext c
  obtain ⟨g, rfl⟩ := ConjClasses.mk_surjective c
  have hχfun :
      ((tensorCharacterRingToSubalgebra ℂ G χ :
          characterRingScalarExtensionSubalgebra ℂ G) : G → ℂ) g =
        (f : G → ℂ) g := by
    have hχ' := congrArg
      (fun z : characterRingScalarExtensionSubalgebra ℂ G ↦ (z : G → ℂ)) hχ
    simpa using congrFun hχ' g
  simpa [f, classFunctionSubalgebraEvalConjClasses_complex] using hχfun

/-- Helper for Proposition 11-11.4-1: a subgroup-induction generator lies in the zero-residual
prime indexed by the class of `x` exactly when the induced character vanishes at `x`. This is the
source-level zero-line membership test used in Proposition `30'`. -/
lemma induction_generator_mem_zero_prime_iff
    (H : Subgroup G) (x : G) (χ : R(H)) :
    (Algebra.TensorProduct.includeRight (R := ℤ) (A := A) (B := R(G))
      (H.characterRingInduction χ)) ∈ (P0 A (ConjClasses.mk x)).asIdeal ↔
      ((H.characterRingInduction χ : R(G)) : G → ℂ) x = 0 := by
  change (((tensorCharacterRingToSubalgebra A G)
      ((Algebra.TensorProduct.includeRight (R := ℤ) (A := A) (B := R(G)))
        (H.characterRingInduction χ)) :
        characterRingScalarExtensionSubalgebra A G) : G → ℂ) x = 0 ↔ _
  simp [tensorCharacterRingToSubalgebra, Subgroup.characterRingInduction_apply]

/-- Helper for Proposition 11-11.4-1: if a subgroup misses the conjugacy class of `x`, then every
character induced from that subgroup vanishes at `x`. This is the source zero-line separator
behind Proposition `30'`(i). -/
lemma induced_character_value_eq_zero_of_disjoint_carrier
    (H : Subgroup G) (x : G)
    (hdisj : ((H : Set G) ∩ (ConjClasses.mk x).carrier) = ∅) (χ : R(H)) :
    ((H.characterRingInduction χ : R(G)) : G → ℂ) x = 0 := by
  classical
  let _ : Fintype G := Fintype.ofFinite G
  let _ : Fintype H := Fintype.ofFinite H
  rw [Subgroup.characterRingInduction_apply]
  change ((Nat.card H : ℂ)⁻¹) *
      (∑ s : G,
        if hsg : s⁻¹ * x * s ∈ H then
          χ ⟨s⁻¹ * x * s, hsg⟩
        else 0) = 0
  have hsum :
      (∑ s : G,
        if hsg : s⁻¹ * x * s ∈ H then
          χ ⟨s⁻¹ * x * s, hsg⟩
        else 0) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro s _
    by_cases hs : s⁻¹ * x * s ∈ H
    · have hsconj : s * (s⁻¹ * x * s) * s⁻¹ = x := by
        group
      have hcarrier : s⁻¹ * x * s ∈ (ConjClasses.mk x).carrier := by
        refine ConjClasses.mem_carrier_iff_mk_eq.mpr ?_
        exact ConjClasses.mk_eq_mk_iff_isConj.mpr (isConj_iff.2 ⟨s, hsconj⟩)
      have hempty : False := by
        have hmem : s⁻¹ * x * s ∈ ((H : Set G) ∩ (ConjClasses.mk x).carrier) := ⟨hs, hcarrier⟩
        simpa [hdisj] using hmem
      exact False.elim hempty
    · simp [hs]
  rw [hsum, mul_zero]

/-- Helper for Proposition 11-11.4-1: a subgroup-induction ideal coming from a subgroup disjoint
from `c` is contained in the zero-residual prime `P₀,c`. This packages the source proof of
Proposition `30'`(i) in the tensor-character-ring language. -/
theorem tensorCharacterRingInductionIdeal_le_zero_line_prime_of_disjoint_carrier
    (H : Subgroup G) (c : ConjClasses G)
    (hdisj : ((H : Set G) ∩ c.carrier) = ∅) :
    tensorCharacterRingInductionIdeal (A := A) (G := G) H ≤ (P0 A c).asIdeal := by
  rw [tensorCharacterRingInductionIdeal, Ideal.span_le]
  intro ξ hξ
  rcases hξ with ⟨χ, rfl⟩
  obtain ⟨x, hmk⟩ := ConjClasses.mk_surjective c
  have hdisj_x : ((H : Set G) ∩ (ConjClasses.mk x).carrier) = ∅ := by
    simpa [hmk] using hdisj
  have hmem_x :
      (Algebra.TensorProduct.includeRight (R := ℤ) (A := A) (B := R(G))
        (H.characterRingInduction χ)) ∈ (P0 A (ConjClasses.mk x)).asIdeal :=
    (induction_generator_mem_zero_prime_iff (A := A) (G := G) H x χ).2
      (induced_character_value_eq_zero_of_disjoint_carrier (G := G) H x hdisj_x χ)
  simpa [hmk] using hmem_x

end

end Proposition_11_11_4_1
