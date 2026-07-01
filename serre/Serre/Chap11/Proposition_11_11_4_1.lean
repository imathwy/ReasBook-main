import Serre.Chap11.Proposition_11_11_4_1.RegularOwnerIncidence
import Serre.Chap10.Lemma_10_10_2_3
import Serre.Chap10.Lemma_10_10_3_3
import Serre.Chap10.Theorem_10_10_5_2.BrauerInductionInfrastructure
import Serre.Chap11.Remark_11_11_1_3.TensorCharacterRingRestriction
import Serre.Chap11.Theorem_11_11_2_1.TensorCharacterBridge
import Serre.Chap11.Theorem_11_11_3_2

-- Declarations for this item are assembled here from the extracted Proposition 11-11.4-1 API.

universe u v

noncomputable section

open Representation
open Proposition_11_11_4_1
open scoped Pointwise Representation SubgroupInduction TensorProduct

namespace Proposition_11_11_4_1

section

variable {G : Type} [Group G] [Finite G]
variable {A : Type v} [CommRing A] [Algebra A ℂ]

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
  · intro f g _ _ hf_int hg_int
    exact hf_int.add hg_int
  · intro f g _ _ hf_int hg_int
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

/-- Helper for Proposition 11-11.4-1: Serre's zero prime `P₀,c` is the kernel of the concrete
fixed-class evaluation map at any representative of `c`. This is the source-facing identification
used when reducing the zero branch to coordinate kernels. -/
theorem tensorCharacterRingZeroPrimeIdealEval_eq_valueAtConjClassComplex
    (c : ConjClasses G) :
    tensorCharacterRingZeroPrimeIdealEval (A := A) (G := G) c =
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

section SourceValueProfile

variable [IsDomain A] [Ring.HasFiniteQuotients A] [IsIntegralClosure A ℤ ℂ]

/-- Helper for Proposition 11-11.4-1: when fixed-class evaluation already lands in the integral
closure ring `A`, the zero point of `Spec A` pulls back exactly to the public zero owner `P₀,c`.
This is the source-faithful normalization step behind the discarded stronger zero-branch route. -/
theorem zero_line_point_eq_comap_tensorCharacterRingValueAtConjClass
    (c : ConjClasses G) :
    PrimeSpectrum.comap (tensorCharacterRingValueAtConjClass (A := A) (G := G) c)
      ⟨(⊥ : Ideal A), inferInstance⟩ =
        tensorCharacterRingZeroPrimeIdeal (A := A) (G := G) c := by
  apply PrimeSpectrum.ext
  ext χ
  change tensorCharacterRingValueAtConjClass (A := A) (G := G) c χ = 0 ↔
    tensorCharacterRingZeroPrimeIdealEval A c χ = 0
  constructor
  · intro hχ
    rw [tensorCharacterRingZeroPrimeIdealEval_eq_valueAtConjClassComplex (A := A) (G := G) c,
      ← tensorCharacterRingValueAtConjClass_complex_eq (A := A) (G := G) c]
    simpa [hχ]
  · intro hχ
    apply IsIntegralClosure.algebraMap_injective A ℤ ℂ
    rw [tensorCharacterRingZeroPrimeIdealEval_eq_valueAtConjClassComplex (A := A) (G := G) c,
      ← tensorCharacterRingValueAtConjClass_complex_eq (A := A) (G := G) c] at hχ
    simpa using hχ

/-- Helper for Proposition 11-11.4-1: every fixed-class evaluation pullback contracts to the
source prime used on the coefficient ring. This is the scalar normalization needed before the
zero and nonzero branches can both read off the coefficient prime from the same source
presentation. -/
theorem value_comap_eq_source_prime
    (c : ConjClasses G) (q : PrimeSpectrum A) :
    Ideal.comap (algebraMap A (A ⊗R(G)))
        (PrimeSpectrum.comap (tensorCharacterRingValueAtConjClass (A := A) (G := G) c) q).asIdeal =
      q.asIdeal := by
  ext a
  change
    tensorCharacterRingValueAtConjClass (A := A) (G := G) c
        ((algebraMap A (A ⊗R(G))) a) ∈ q.asIdeal ↔
      a ∈ q.asIdeal
  rw [tensorCharacterRingValueAtConjClass_algebraMap (A := A) (G := G) c a]

/-- Helper for Proposition 11-11.4-1: bundle the fixed-class evaluations into Serre's source
map `A ⊗ R(G) → A^{Cl(G)}`. This is the governing source object for Proposition `30`, and it
keeps the later prime-classification step on the source route instead of returning to fiber
transport packages. -/
noncomputable def tensorCharacterRingValueProfile :
    A ⊗R(G) →ₐ[A] (ConjClasses G → A) where
  toFun χ c := tensorCharacterRingValueAtConjClass (A := A) (G := G) c χ
  map_one' := by
    ext c
    simp [tensorCharacterRingValueAtConjClass]
  map_mul' χ ψ := by
    ext c
    simp [tensorCharacterRingValueAtConjClass]
  map_zero' := by
    ext c
    simp [tensorCharacterRingValueAtConjClass]
  map_add' χ ψ := by
    ext c
    simp [tensorCharacterRingValueAtConjClass]
  commutes' a := by
    ext c
    simpa using
      tensorCharacterRingValueAtConjClass_algebraMap (A := A) (G := G) c a

/-- Helper for Proposition 11-11.4-1: the source map evaluates pointwise to the chosen fixed-class
evaluation. This keeps later `rw` steps on the explicit source presentation. -/
@[simp] theorem tensorCharacterRingValueProfile_apply
    (χ : A ⊗R(G)) (c : ConjClasses G) :
    tensorCharacterRingValueProfile (A := A) (G := G) χ c =
      tensorCharacterRingValueAtConjClass (A := A) (G := G) c χ :=
  rfl

/-- Helper for Proposition 11-11.4-1: the point-mass function at a conjugacy class in Serre's
source ring `A^{Cl(G)}`. This is the idempotent source generator used in the lying-over pivot. -/
noncomputable def conjClassDelta
    (c : ConjClasses G) : ConjClasses G → A :=
  fun d ↦
    let _ : DecidableEq (ConjClasses G) := Classical.decEq _
    if d = c then 1 else 0

/-- Helper for Proposition 11-11.4-1: each source point mass is an idempotent in
`A^{Cl(G)}`. This is the key source-side integrality input for the intended lying-over proof. -/
theorem conjClassDelta_mul_self
    (c : ConjClasses G) :
    conjClassDelta (A := A) (G := G) c * conjClassDelta (A := A) (G := G) c =
      conjClassDelta (A := A) (G := G) c := by
  ext d
  classical
  by_cases hd : d = c
  · simp [conjClassDelta, hd]
  · simp [conjClassDelta, hd]

/-- Helper for Proposition 11-11.4-1: the source point masses span the full function ring on
conjugacy classes. This makes the intended source-spectrum proof reduce to adjoining finitely many
idempotents to the image of the source map. -/
theorem sum_smul_conjClassDelta_eq
    (F : ConjClasses G → A) :
    (∑ c : ConjClasses G, F c • conjClassDelta (A := A) (G := G) c) = F := by
  funext d
  classical
  simp [conjClassDelta]

/-- Helper for Proposition 11-11.4-1: each source point mass is integral over the image of
Serre's source profile map. This is the idempotent input for the lying-over step on
`A^{Cl(G)}`. -/
theorem conjClassDelta_isIntegral_over_valueProfile
    (c : ConjClasses G) :
    ((tensorCharacterRingValueProfile (A := A) (G := G)).toRingHom).IsIntegralElem
      (conjClassDelta (A := A) (G := G) c) := by
  refine ⟨Polynomial.X * (Polynomial.X - Polynomial.C (1 : A ⊗R(G))), ?_, ?_⟩
  · simpa using
      (Polynomial.monic_X.mul
        (Polynomial.monic_X_sub_C (1 : A ⊗R(G))))
  · simp [conjClassDelta_mul_self, sub_eq_add_neg, mul_add]

/-- Helper for Proposition 11-11.4-1: Serre's source profile map
`A ⊗ R(G) → A^{Cl(G)}` is injective. This is the exact missing hypothesis needed to apply
lying-over to the source inclusion and keep the proof on Serre's source spectrum
`Spec(A^{Cl(G)}) → Spec(A ⊗ R(G))`. -/
theorem tensorCharacterRingValueProfile_injective :
    Function.Injective (tensorCharacterRingValueProfile (A := A) (G := G)) := by
  intro χ ψ hχψ
  apply tensorCharacterRingToFunction_injective (A := A) (G := G)
  ext g
  have hclass :
      tensorCharacterRingValueProfile (A := A) (G := G) χ (ConjClasses.mk g) =
        tensorCharacterRingValueProfile (A := A) (G := G) ψ (ConjClasses.mk g) :=
    congrFun hχψ (ConjClasses.mk g)
  have hclass_complex := congrArg (algebraMap A ℂ) hclass
  rw [tensorCharacterRingValueProfile_apply (A := A) (G := G) χ (ConjClasses.mk g),
    tensorCharacterRingValueProfile_apply (A := A) (G := G) ψ (ConjClasses.mk g)] at hclass_complex
  rw [tensorCharacterRingValueAtConjClass_complex_eq (A := A) (G := G) (ConjClasses.mk g) χ,
    tensorCharacterRingValueAtConjClass_complex_eq (A := A) (G := G) (ConjClasses.mk g) ψ] at hclass_complex
  rw [tensorCharacterRingValueAtConjClassComplex_eq_of_mk_eq (A := A) (G := G)
      (ConjClasses.mk g) χ rfl,
    tensorCharacterRingValueAtConjClassComplex_eq_of_mk_eq (A := A) (G := G)
      (ConjClasses.mk g) ψ rfl] at hclass_complex
  simpa using hclass_complex

/-- Helper for Proposition 11-11.4-1: Serre's source profile map
`A ⊗ R(G) → A^{Cl(G)}` is integral. This is the source-faithful bridge from the tensor character
ring to the function ring on conjugacy classes. -/
theorem tensorCharacterRingValueProfile_isIntegral :
    RingHom.IsIntegral (tensorCharacterRingValueProfile (A := A) (G := G)).toRingHom := by
  let f : A ⊗R(G) →+* (ConjClasses G → A) :=
    (tensorCharacterRingValueProfile (A := A) (G := G)).toRingHom
  intro F
  let s : Finset (ConjClasses G) := Finset.univ
  have hsum :
      f.IsIntegralElem
        (s.sum fun c =>
          f ((algebraMap A (A ⊗R(G))) (F c)) *
            conjClassDelta (A := A) (G := G) c) := by
    classical
    refine Finset.induction_on (s := s) ?_ ?_
    · simpa using RingHom.isIntegralElem_zero f
    · intro c s hc hs
      rw [Finset.sum_insert hc]
      have hscalar :
          f.IsIntegralElem (f ((algebraMap A (A ⊗R(G))) (F c))) :=
        RingHom.isIntegralElem_map f
      have hterm :
          f.IsIntegralElem
            (f ((algebraMap A (A ⊗R(G))) (F c)) *
              conjClassDelta (A := A) (G := G) c) :=
        hscalar.mul f (conjClassDelta_isIntegral_over_valueProfile (A := A) (G := G) c)
      exact hterm.add f hs
  have hrewrite :
      (s.sum fun c =>
        f ((algebraMap A (A ⊗R(G))) (F c)) *
          conjClassDelta (A := A) (G := G) c) = F := by
    calc
      (s.sum fun c =>
        f ((algebraMap A (A ⊗R(G))) (F c)) *
          conjClassDelta (A := A) (G := G) c)
          =
        (s.sum fun c =>
          F c • conjClassDelta (A := A) (G := G) c) := by
            refine Finset.sum_congr rfl ?_
            intro c hc
            ext d
            have hconst :
                f ((algebraMap A (A ⊗R(G))) (F c)) d = F c := by
              simpa [f, tensorCharacterRingValueProfile] using
                tensorCharacterRingValueAtConjClass_algebraMap
                  (A := A) (G := G) d (F c)
            calc
              (f ((algebraMap A (A ⊗R(G))) (F c)) *
                  conjClassDelta (A := A) (G := G) c) d
                  =
                f ((algebraMap A (A ⊗R(G))) (F c)) d *
                  conjClassDelta (A := A) (G := G) c d := by
                    rfl
              _ = F c * conjClassDelta (A := A) (G := G) c d := by rw [hconst]
              _ = (F c • conjClassDelta (A := A) (G := G) c) d := by
                    simp [Algebra.smul_def]
      _ = F := by
            simpa [s] using sum_smul_conjClassDelta_eq (A := A) (G := G) F
  exact hrewrite ▸ hsum

/-- Helper for Proposition 11-11.4-1: evaluating Serre's source profile at a fixed conjugacy
class recovers the corresponding fixed-class evaluation map. This keeps the source-spectrum proof
as a direct comap computation instead of a transport argument. -/
theorem evalRingHom_comp_tensorCharacterRingValueProfile
    (d : ConjClasses G) :
    (Pi.evalRingHom (fun _ : ConjClasses G ↦ A) d).comp
        (tensorCharacterRingValueProfile (A := A) (G := G)).toRingHom =
      (tensorCharacterRingValueAtConjClass (A := A) (G := G) d).toRingHom := by
  rfl

/-- Helper for Proposition 11-11.4-1: every ambient prime should be presented directly as the
pullback of a coefficient prime along fixed-class evaluation. This is Serre's actual source map
`Spec(A^{Cl(G)}) → Spec(A ⊗ R(G))`, and replacing the old fiber packages by this theorem is the
main structural pivot for Proposition `30`. -/
theorem source_prime_eq_value_comap_of_class
    (𝔭 : PrimeSpectrum (A ⊗R(G))) :
    ∃ (d : ConjClasses G) (q : PrimeSpectrum A),
      PrimeSpectrum.comap (tensorCharacterRingValueAtConjClass (A := A) (G := G) d) q = 𝔭 := by
  let f : A ⊗R(G) →+* (ConjClasses G → A) :=
    (tensorCharacterRingValueProfile (A := A) (G := G)).toRingHom
  obtain ⟨Q, hQ⟩ :=
    RingHom.IsIntegral.comap_surjective
      (f := f)
      (tensorCharacterRingValueProfile_isIntegral (A := A) (G := G))
      (tensorCharacterRingValueProfile_injective (A := A) (G := G))
      𝔭
  obtain ⟨d, q, hdq⟩ :=
    PrimeSpectrum.exists_comap_evalRingHom_eq (R := fun _ : ConjClasses G ↦ A) Q
  refine ⟨d, q, ?_⟩
  have hcomp :
      PrimeSpectrum.comap
          (((Pi.evalRingHom (fun _ : ConjClasses G ↦ A) d)).comp f) q = 𝔭 := by
    simpa [hdq] using hQ
  simpa [f, evalRingHom_comp_tensorCharacterRingValueProfile (A := A) (G := G) d] using hcomp

/-- Helper for Proposition 11-11.4-1: once an ambient prime is known to contract to the fixed
maximal ideal `M`, Serre's source-spectrum presentation can be normalized so that the coefficient
prime in the fixed-class evaluation pullback is exactly `M`. This is the source-faithful wrapper
needed before attaching the `p`-regular owner class to the presentation. -/
theorem source_prime_eq_value_comap_of_class_over_fixed_maximal
    (p : Nat.Primes) (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    {𝔭 : PrimeSpectrum (A ⊗R(G))}
    (h𝔭 : Ideal.comap (algebraMap A (A ⊗R(G))) 𝔭.asIdeal = M.1.asIdeal) :
    ∃ d : ConjClasses G,
      PrimeSpectrum.comap (tensorCharacterRingValueAtConjClass (A := A) (G := G) d)
        (⟨M.1.asIdeal, inferInstance⟩ : PrimeSpectrum A) = 𝔭 := by
  obtain ⟨d, q, hq⟩ :=
    source_prime_eq_value_comap_of_class (A := A) (G := G) 𝔭
  have hqIdeal : q.asIdeal = M.1.asIdeal := by
    calc
      q.asIdeal =
          Ideal.comap (algebraMap A (A ⊗R(G)))
            (PrimeSpectrum.comap
              (tensorCharacterRingValueAtConjClass (A := A) (G := G) d) q).asIdeal := by
                symm
                exact value_comap_eq_source_prime (A := A) (G := G) d q
      _ =
          Ideal.comap (algebraMap A (A ⊗R(G))) 𝔭.asIdeal := by
            simpa [hq]
      _ = M.1.asIdeal := h𝔭
  have hqEq : q = (⟨M.1.asIdeal, inferInstance⟩ : PrimeSpectrum A) := by
    apply PrimeSpectrum.ext
    simpa using hqIdeal
  refine ⟨d, ?_⟩
  simpa [hqEq] using hq

/-- Helper for Proposition 11-11.4-1: under the integral-closure hypothesis, the zero branch is
already a formal corollary of the source-spectrum presentation. This records the exact reduction
proved by the source route, even though the public zero-branch theorem below still needs a
coefficient-descent-free bridge to avoid adding `[IsIntegralClosure A ℤ ℂ]` to its statement. -/
theorem zero_fiber_prime_classification_over_bot_of_source_presentation
    {𝔭 : PrimeSpectrum (A ⊗R(G))}
    (h𝔭 : Ideal.comap (algebraMap A (A ⊗R(G))) 𝔭.asIdeal = ⊥) :
    ∃ c : ConjClasses G, P0 A c = 𝔭 := by
  obtain ⟨c, q, hq⟩ :=
    source_prime_eq_value_comap_of_class (A := A) (G := G) 𝔭
  have hqbotIdeal : q.asIdeal = ⊥ := by
    calc
      q.asIdeal =
          Ideal.comap (algebraMap A (A ⊗R(G)))
            (PrimeSpectrum.comap (tensorCharacterRingValueAtConjClass (A := A) (G := G) c) q).asIdeal := by
              symm
              exact value_comap_eq_source_prime (A := A) (G := G) c q
      _ =
          Ideal.comap (algebraMap A (A ⊗R(G))) 𝔭.asIdeal := by
            simpa [hq]
      _ = ⊥ := h𝔭
  have hqbot : q = ⟨(⊥ : Ideal A), inferInstance⟩ := by
    apply PrimeSpectrum.ext
    simpa using hqbotIdeal
  refine ⟨c, ?_⟩
  calc
    P0 A c =
        PrimeSpectrum.comap (tensorCharacterRingValueAtConjClass (A := A) (G := G) c)
          ⟨(⊥ : Ideal A), inferInstance⟩ := by
            symm
            exact zero_line_point_eq_comap_tensorCharacterRingValueAtConjClass
              (A := A) (G := G) c
    _ =
        PrimeSpectrum.comap (tensorCharacterRingValueAtConjClass (A := A) (G := G) c) q := by
          simpa [hqbot]
    _ = 𝔭 := hq

end SourceValueProfile

end

end Proposition_11_11_4_1

section

variable {G : Type} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]

/-- Helper for Proposition 11-11.4-1: a sufficiently large power of `p` kills the `p`-unipotent
part, so `x` and its `p'`-component have the same `p^k`th power. -/
theorem exists_p_power_eq_pRegularComponent_pow (x : G) :
    ∃ k : ℕ, x ^ (p ^ k) = (pRegularComponent p x) ^ (p ^ k) := by
  let hdecomp :=
    p_component_decomposition_exists (p := p) x (isOfFinOrder_of_finite x)
  rcases hdecomp.isPElement with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  have hpowu : (pUnipotentComponent p x) ^ (p ^ k) = 1 := by
    simpa [hk] using pow_orderOf_eq_one (pUnipotentComponent p x)
  calc
    x ^ (p ^ k) = ((pUnipotentComponent p x) * (pRegularComponent p x)) ^ (p ^ k) := by
      exact congrArg (fun g : G ↦ g ^ (p ^ k)) hdecomp.eq_mul
    _ = (pUnipotentComponent p x) ^ (p ^ k) * (pRegularComponent p x) ^ (p ^ k) := by
      rw [hdecomp.commute.mul_pow]
    _ = (pRegularComponent p x) ^ (p ^ k) := by
      rw [hpowu, one_mul]

end

section

variable {G : Type u} [Group G] [Finite G]
variable {A : Type v} [CommRing A] [Algebra A ℂ] [IsIntegralClosure A ℤ ℂ]
variable {p : ℕ} [Fact p.Prime]

/-- Helper for Proposition 11-11.4-1: the quotient by the principal ideal `(p)` has
characteristic `p`. -/
private theorem quotient_span_prime_charP :
    CharP (A ⧸ Ideal.span ({(p : A)} : Set A)) p := by
  have hp_nonunit : ¬ IsUnit (p : A) := by
    intro hp_unit
    rcases hp_unit with ⟨u, hu⟩
    let a : A := ↑u⁻¹
    have ha_mul : a * (p : A) = 1 := by
      calc
        a * (p : A) = (↑u⁻¹ : A) * ↑u := by rw [hu]
        _ = 1 := by simp
    have hmap : algebraMap A ℂ a * p = 1 := by
      simpa [map_mul] using congrArg (algebraMap A ℂ) ha_mul
    have hEq : algebraMap ℚ ℂ (((1 : ℤ) : ℚ) / p) = algebraMap A ℂ a := by
      have hpC : (p : ℂ) ≠ 0 := by
        exact_mod_cast (Fact.out : Nat.Prime p).ne_zero
      calc
        algebraMap ℚ ℂ (((1 : ℤ) : ℚ) / p) = (1 : ℂ) / p := by
          norm_num [Rat.cast_def]
        _ = algebraMap A ℂ a := by
          exact (div_eq_iff hpC).2 hmap.symm
    have hintC : IsIntegral ℤ (algebraMap A ℂ a) := by
      exact (IsIntegralClosure.isIntegral_iff (A := A) (R := ℤ) (B := ℂ)).2 ⟨a, rfl⟩
    have hintQ : IsIntegral ℤ ((((1 : ℤ) : ℚ) / p)) := by
      exact (isIntegral_algebraMap_iff (algebraMap ℚ ℂ).injective).mp <| by
        rw [hEq]
        exact hintC
    rcases (show ∃ z : ℤ, algebraMap ℤ ℚ z = (((1 : ℤ) : ℚ) / p) by
        simpa [IsLocalization.IsInteger] using UniqueFactorizationMonoid.integer_of_integral hintQ)
      with ⟨z, hz⟩
    have hpq : (p : ℚ) ≠ 0 := by
      exact_mod_cast (Fact.out : Nat.Prime p).ne_zero
    have hzmul := congrArg (fun x : ℚ ↦ x * p) hz
    field_simp [hpq] at hzmul
    have hz' : (1 : ℚ) = p * z := by
      simpa [mul_comm] using hzmul.symm
    have hdiv : (p : ℤ) ∣ 1 := by
      refine ⟨z, ?_⟩
      exact_mod_cast hz'
    have hdivNat : p ∣ 1 := by
      exact_mod_cast hdiv
    exact (Fact.out : Nat.Prime p).not_dvd_one hdivNat
  exact CharP.quotient A p (by simpa using hp_nonunit)

/-- Helper for Proposition 11-11.4-1: an irreducible character of a finite cyclic group comes
from a degree-one character. -/
private theorem exists_linear_character_of_irreducible_rep
    {H : Type u} [Group H] [Finite H] [IsCyclic H]
    (ρ : Rep ℂ H) [FiniteDimensional ℂ ρ] [ρ.ρ.IsIrreducible] :
    ∃ α : H →* ℂˣ, ρ.ρ.character = α.toRepresentation.character := by
  letI : CommGroup H := IsCyclic.commGroup
  have hdim : Module.finrank ℂ ρ = 1 := by
    simpa using Representation.IsIrreducible.finrank_eq_one_of_isMulCommutative ρ.ρ
  let scalarEquiv : ℂ ≃ₗ[ℂ] (ρ →ₗ[ℂ] ρ) :=
    LinearEquiv.smul_id_of_finrank_eq_one hdim
  have hscalar (c : ℂ) : scalarEquiv c = c • LinearMap.id :=
    LinearEquiv.smul_id_of_finrank_eq_one_apply hdim c
  let α₀ : H → ℂ := fun h ↦ scalarEquiv.symm (ρ.ρ h)
  have hα₀_eq (h : H) : ρ.ρ h = α₀ h • LinearMap.id := by
    calc
      ρ.ρ h = scalarEquiv (α₀ h) := by simp [α₀]
      _ = α₀ h • LinearMap.id := hscalar _
  have hα₀_one : α₀ 1 = 1 := by
    apply scalarEquiv.injective
    calc
      scalarEquiv (α₀ 1) = ρ.ρ 1 := by simp [α₀]
      _ = (1 : ρ →ₗ[ℂ] ρ) := by simp
      _ = scalarEquiv 1 := by simpa using (hscalar (1 : ℂ)).symm
  have hα₀_mul (h₁ h₂ : H) : α₀ (h₁ * h₂) = α₀ h₁ * α₀ h₂ := by
    apply scalarEquiv.injective
    calc
      scalarEquiv (α₀ (h₁ * h₂)) = ρ.ρ (h₁ * h₂) := by simp [α₀]
      _ = ρ.ρ h₁ * ρ.ρ h₂ := by simp
      _ = (α₀ h₁ * α₀ h₂) • LinearMap.id := by
        rw [hα₀_eq, hα₀_eq]
        ext x
        simp [smul_smul, mul_comm]
      _ = scalarEquiv (α₀ h₁ * α₀ h₂) := (hscalar _).symm
  have hα₀_ne_zero (h : H) : α₀ h ≠ 0 := by
    have hpos : 0 < Module.finrank ℂ ρ := by simpa [hdim]
    letI : Nontrivial ρ := Module.nontrivial_of_finrank_pos hpos
    intro hzero
    have hzeroMap : ρ.ρ h = 0 := by simp [hα₀_eq, hzero]
    have hone : (1 : ρ →ₗ[ℂ] ρ) ≠ 0 := one_ne_zero
    have hidzero : (1 : ρ →ₗ[ℂ] ρ) = 0 := by
      calc
        (1 : ρ →ₗ[ℂ] ρ) = ρ.ρ h * ρ.ρ h⁻¹ := by
          simpa using ρ.ρ.map_mul h h⁻¹
        _ = 0 := by rw [hzeroMap]; simp
    exact hone hidzero
  let α : H →* ℂˣ :=
    { toFun := fun h ↦ Units.mk0 (α₀ h) (hα₀_ne_zero h)
      map_one' := by ext; simpa using hα₀_one
      map_mul' h₁ h₂ := by ext; simpa using hα₀_mul h₁ h₂ }
  refine ⟨α, ?_⟩
  ext h
  rw [MonoidHom.toRepresentation_character_apply, Representation.character, hα₀_eq]
  simp [hdim, α]

/-- Helper for Proposition 11-11.4-1: linear-character values admit lifts in `A` whose
`p^k`th powers agree when the underlying group elements do. -/
private theorem exists_lifts_of_linear_character_values_with_pow_eq
    {H : Type u} [Group H] [Finite H]
    (ρ : H →* ℂˣ) {y z : H} {k : ℕ}
    (hpow : y ^ (p ^ k) = z ^ (p ^ k)) :
    ∃ ay az : A,
      algebraMap A ℂ ay = (ρ y : ℂ) ∧
      algebraMap A ℂ az = (ρ z : ℂ) ∧
      ay ^ (p ^ k) = az ^ (p ^ k) := by
  have hyInt : IsIntegral ℤ ((ρ y : ℂ)) := by
    apply IsIntegral.of_pow (n := orderOf y)
    · exact orderOf_pos y
    · rw [show ((ρ y : ℂ) ^ orderOf y) = 1 by
        have hpowUnits : (ρ y) ^ orderOf y = 1 := by
          rw [← map_pow]
          simp [pow_orderOf_eq_one y]
        exact congrArg (fun w : ℂˣ ↦ (w : ℂ)) hpowUnits]
      exact isIntegral_one
  have hzInt : IsIntegral ℤ ((ρ z : ℂ)) := by
    apply IsIntegral.of_pow (n := orderOf z)
    · exact orderOf_pos z
    · rw [show ((ρ z : ℂ) ^ orderOf z) = 1 by
        have hpowUnits : (ρ z) ^ orderOf z = 1 := by
          rw [← map_pow]
          simp [pow_orderOf_eq_one z]
        exact congrArg (fun w : ℂˣ ↦ (w : ℂ)) hpowUnits]
      exact isIntegral_one
  obtain ⟨ay, hay⟩ :=
    (IsIntegralClosure.isIntegral_iff (A := A) (R := ℤ) (B := ℂ)).1 hyInt
  obtain ⟨az, haz⟩ :=
    (IsIntegralClosure.isIntegral_iff (A := A) (R := ℤ) (B := ℂ)).1 hzInt
  refine ⟨ay, az, hay, haz, ?_⟩
  let h_inj : Function.Injective (algebraMap A ℂ) :=
    IsIntegralClosure.algebraMap_injective A ℤ ℂ
  apply h_inj
  calc
    algebraMap A ℂ (ay ^ (p ^ k)) = (ρ y : ℂ) ^ (p ^ k) := by rw [map_pow, hay]
    _ = (ρ (y ^ (p ^ k)) : ℂ) := by simp
    _ = (ρ (z ^ (p ^ k)) : ℂ) := by simp [hpow]
    _ = (ρ z : ℂ) ^ (p ^ k) := by simp
    _ = algebraMap A ℂ (az ^ (p ^ k)) := by rw [map_pow, haz]

/-- Helper for Proposition 11-11.4-1: on a cyclic group, character values at two elements with
the same `p^k`th power have lifts with equal `p^k`th powers modulo `(p)`. -/
private theorem cyclic_character_qpow_quotient_eq
    {H : Type u} [Group H] [Finite H] [IsCyclic H]
    {ψ : H → ℂ} (hψ : ψ ∈ R(H)) {y z : H} {k : ℕ}
    (hpow : y ^ (p ^ k) = z ^ (p ^ k)) :
    ∃ ay az : A,
      algebraMap A ℂ ay = ψ y ∧
      algebraMap A ℂ az = ψ z ∧
      (Ideal.Quotient.mk (Ideal.span ({(p : A)} : Set A)) ay) ^ (p ^ k) =
        (Ideal.Quotient.mk (Ideal.span ({(p : A)} : Set A)) az) ^ (p ^ k) := by
  let I : Ideal A := Ideal.span ({(p : A)} : Set A)
  let mk : A →+* A ⧸ I := Ideal.Quotient.mk I
  letI : CommGroup H := IsCyclic.commGroup
  letI : CharP (A ⧸ I) p := quotient_span_prime_charP (A := A) (p := p)
  let P : (g : H → ℂ) → g ∈ R(H) → Prop := fun g _ ↦
    ∃ ay az : A,
      algebraMap A ℂ ay = g y ∧
      algebraMap A ℂ az = g z ∧
      (mk ay) ^ (p ^ k) = (mk az) ^ (p ^ k)
  refine Algebra.adjoin_induction (p := P) ?_ ?_ ?_ ?_ hψ
  · intro χ hχ
    rcases hχ with ⟨ρ, -, hρirr, rfl⟩
    obtain ⟨α, hα⟩ := exists_linear_character_of_irreducible_rep (ρ := ρ)
    obtain ⟨ay, az, hay, haz, hpowA⟩ :=
      exists_lifts_of_linear_character_values_with_pow_eq (A := A) (p := p) α hpow
    refine ⟨ay, az, ?_, ?_, ?_⟩
    · simpa [hα]
    · simpa [hα]
    · simpa [mk] using congrArg mk hpowA
  · intro n
    refine ⟨n, n, ?_, ?_, ?_⟩
    · simp
    · simp
    · rfl
  · intro f g _ _ hf hg
    rcases hf with ⟨ay, az, hay, haz, hq⟩
    rcases hg with ⟨uy, uz, huy, huz, hr⟩
    refine ⟨ay + uy, az + uz, ?_, ?_, ?_⟩
    · simp [hay, huy]
    · simp [haz, huz]
    · calc
        mk ((ay + uy) ^ (p ^ k)) = (mk (ay + uy)) ^ (p ^ k) := by simp [mk]
        _ = (mk ay + mk uy) ^ (p ^ k) := by simp [mk]
        _ = (mk ay) ^ (p ^ k) + (mk uy) ^ (p ^ k) := by
          simpa using add_pow_char_pow (mk ay) (mk uy) p k
        _ = (mk az) ^ (p ^ k) + (mk uz) ^ (p ^ k) := by rw [hq, hr]
        _ = (mk (az + uz)) ^ (p ^ k) := by
          symm
          calc
            (mk (az + uz)) ^ (p ^ k) = (mk az + mk uz) ^ (p ^ k) := by simp [mk]
            _ = (mk az) ^ (p ^ k) + (mk uz) ^ (p ^ k) := by
              simpa using add_pow_char_pow (mk az) (mk uz) p k
        _ = mk ((az + uz) ^ (p ^ k)) := by simp [mk]
  · intro f g _ _ hf hg
    rcases hf with ⟨ay, az, hay, haz, hq⟩
    rcases hg with ⟨uy, uz, huy, huz, hr⟩
    refine ⟨ay * uy, az * uz, ?_, ?_, ?_⟩
    · simp [hay, huy, map_mul]
    · simp [haz, huz, map_mul]
    · calc
        mk ((ay * uy) ^ (p ^ k)) = (mk (ay * uy)) ^ (p ^ k) := by simp [mk]
        _ = (mk ay * mk uy) ^ (p ^ k) := by simp [mk]
        _ = (mk ay) ^ (p ^ k) * (mk uy) ^ (p ^ k) := by
          simpa using mul_pow (mk ay) (mk uy) (p ^ k)
        _ = (mk az) ^ (p ^ k) * (mk uz) ^ (p ^ k) := by rw [hq, hr]
        _ = (mk (az * uz)) ^ (p ^ k) := by
          symm
          calc
            (mk (az * uz)) ^ (p ^ k) = (mk az * mk uz) ^ (p ^ k) := by simp [mk]
            _ = (mk az) ^ (p ^ k) * (mk uz) ^ (p ^ k) := by
              simpa using mul_pow (mk az) (mk uz) (p ^ k)
        _ = mk ((az * uz) ^ (p ^ k)) := by simp [mk]

/-- Helper for Proposition 11-11.4-1: the cyclic Frobenius congruence extends to the realized
scalar extension `A ⊗ R(H)`. -/
private theorem tensor_character_qpow_quotient_eq_of_mem_characterRingScalarExtension
    {H : Type u} [Group H] [Finite H] [IsCyclic H]
    {f : H → ℂ} (hf : f ∈ characterRingScalarExtension A H)
    {y z : H} {k : ℕ} (hpow : y ^ (p ^ k) = z ^ (p ^ k)) :
    ∃ ay az : A,
      algebraMap A ℂ ay = f y ∧
      algebraMap A ℂ az = f z ∧
      (Ideal.Quotient.mk (Ideal.span ({(p : A)} : Set A)) ay) ^ (p ^ k) =
        (Ideal.Quotient.mk (Ideal.span ({(p : A)} : Set A)) az) ^ (p ^ k) := by
  let I : Ideal A := Ideal.span ({(p : A)} : Set A)
  let mk : A →+* A ⧸ I := Ideal.Quotient.mk I
  letI : CharP (A ⧸ I) p := quotient_span_prime_charP (A := A) (p := p)
  let P : (H → ℂ) → Prop := fun g ↦
    ∃ ay az : A,
      algebraMap A ℂ ay = g y ∧
      algebraMap A ℂ az = g z ∧
      (mk ay) ^ (p ^ k) = (mk az) ^ (p ^ k)
  refine Submodule.span_induction
    (s := (R(H) : Set (H → ℂ)))
    (p := fun g _ ↦ P g)
    ?_ ?_ ?_ ?_ hf
  · intro ψ hψ
    exact cyclic_character_qpow_quotient_eq (A := A) (p := p) hψ hpow
  · refine ⟨0, 0, ?_, ?_, rfl⟩ <;> simp
  · intro f g _ _ hf hg
    rcases hf with ⟨ay, az, hay, haz, hq⟩
    rcases hg with ⟨uy, uz, huy, huz, hr⟩
    refine ⟨ay + uy, az + uz, ?_, ?_, ?_⟩
    · simp [hay, huy]
    · simp [haz, huz]
    · calc
        mk ((ay + uy) ^ (p ^ k)) = (mk (ay + uy)) ^ (p ^ k) := by simp [mk]
        _ = (mk ay + mk uy) ^ (p ^ k) := by simp [mk]
        _ = (mk ay) ^ (p ^ k) + (mk uy) ^ (p ^ k) := by
          simpa using add_pow_char_pow (mk ay) (mk uy) p k
        _ = (mk az) ^ (p ^ k) + (mk uz) ^ (p ^ k) := by rw [hq, hr]
        _ = (mk (az + uz)) ^ (p ^ k) := by
          symm
          calc
            (mk (az + uz)) ^ (p ^ k) = (mk az + mk uz) ^ (p ^ k) := by simp [mk]
            _ = (mk az) ^ (p ^ k) + (mk uz) ^ (p ^ k) := by
              simpa using add_pow_char_pow (mk az) (mk uz) p k
        _ = mk ((az + uz) ^ (p ^ k)) := by simp [mk]
  · intro a g _ hg
    rcases hg with ⟨ay, az, hay, haz, hq⟩
    refine ⟨a * ay, a * az, ?_, ?_, ?_⟩
    · calc
        algebraMap A ℂ (a * ay) = algebraMap A ℂ a * algebraMap A ℂ ay := by simp [map_mul]
        _ = algebraMap A ℂ a * g y := by rw [hay]
        _ = (a • g) y := by simp [Pi.smul_apply, Algebra.smul_def]
    · calc
        algebraMap A ℂ (a * az) = algebraMap A ℂ a * algebraMap A ℂ az := by simp [map_mul]
        _ = algebraMap A ℂ a * g z := by rw [haz]
        _ = (a • g) z := by simp [Pi.smul_apply, Algebra.smul_def]
    · calc
        mk ((a * ay) ^ (p ^ k)) = (mk (a * ay)) ^ (p ^ k) := by simp [mk]
        _ = (mk a * mk ay) ^ (p ^ k) := by simp [mk]
        _ = (mk a) ^ (p ^ k) * (mk ay) ^ (p ^ k) := by
          simpa using mul_pow (mk a) (mk ay) (p ^ k)
        _ = (mk a) ^ (p ^ k) * (mk az) ^ (p ^ k) := by rw [hq]
        _ = (mk (a * az)) ^ (p ^ k) := by
          symm
          calc
            (mk (a * az)) ^ (p ^ k) = (mk a * mk az) ^ (p ^ k) := by simp [mk]
            _ = (mk a) ^ (p ^ k) * (mk az) ^ (p ^ k) := by
              simpa using mul_pow (mk a) (mk az) (p ^ k)
        _ = mk ((a * az) ^ (p ^ k)) := by simp [mk]

/-- Helper for Proposition 11-11.4-1: quotient equality of `p^k`th powers modulo `(p)` forces
congruence modulo `p` of the original integers. -/
private theorem int_modEq_of_qpow_quotient_eq_mod_p
    (m n : ℤ) (k : ℕ)
    (h : Ideal.Quotient.mk (Ideal.span ({(p : A)} : Set A)) ((m : A) ^ (p ^ k)) =
      Ideal.Quotient.mk (Ideal.span ({(p : A)} : Set A)) ((n : A) ^ (p ^ k))) :
    m ≡ n [ZMOD p] := by
  let q : ℕ := p ^ k
  let d : ℤ := m ^ q - n ^ q
  have hmem : ((m : A) ^ q - (n : A) ^ q) ∈ Ideal.span ({(p : A)} : Set A) := by
    simpa [q] using (Ideal.Quotient.eq.mp h)
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hmem
  have haC : (d : ℂ) = p * algebraMap A ℂ a := by
    have haA : ((d : ℤ) : A) = a * (p : A) := by
      calc
        (((d : ℤ) : A)) = (m : A) ^ q - (n : A) ^ q := by simp [d]
        _ = a * (p : A) := by simpa using ha.symm
    have haC' := congrArg (algebraMap A ℂ) haA
    simpa [d, map_mul, mul_comm] using haC'
  have hintC : IsIntegral ℤ (algebraMap A ℂ a) := by
    exact (IsIntegralClosure.isIntegral_iff (A := A) (R := ℤ) (B := ℂ)).2 ⟨a, rfl⟩
  have hintQ : IsIntegral ℤ (((d : ℤ) : ℚ) / p) := by
    have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast (Fact.out : Nat.Prime p).ne_zero
    have hqC : algebraMap ℚ ℂ (((d : ℤ) : ℚ) / p) = algebraMap A ℂ a := by
      calc
        algebraMap ℚ ℂ (((d : ℤ) : ℚ) / p) = ((d : ℂ) / p) := by norm_num [Rat.cast_def]
        _ = algebraMap A ℂ a := by
          exact (div_eq_iff hpC).2 (by simpa [mul_comm] using haC)
    exact (isIntegral_algebraMap_iff (algebraMap ℚ ℂ).injective).mp <| by
      rw [hqC]
      exact hintC
  have hdiv : (p : ℤ) ∣ d := by
    rcases (show ∃ z : ℤ, algebraMap ℤ ℚ z = (((d : ℤ) : ℚ) / p) by
        simpa [IsLocalization.IsInteger] using UniqueFactorizationMonoid.integer_of_integral hintQ)
      with ⟨z, hz⟩
    refine ⟨z, ?_⟩
    have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : Nat.Prime p).ne_zero
    have hzmul := congrArg (fun x : ℚ ↦ x * p) hz
    field_simp [hpq] at hzmul
    have hz' : (d : ℚ) = p * z := by simpa [mul_comm] using hzmul.symm
    exact_mod_cast hz'
  have hpow : ((m : ZMod p) ^ q) = ((n : ZMod p) ^ q) := by
    have hdiv' : (p : ℤ) ∣ -d := Int.dvd_neg.mpr hdiv
    have hdiv'' : (p : ℤ) ∣ (n ^ q - m ^ q : ℤ) := by
      simpa [d, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hdiv'
    simpa using (ZMod.intCast_eq_intCast_iff_dvd_sub (m ^ q) (n ^ q) p).2 hdiv''
  have hm : (m : ZMod p) ^ q = (m : ZMod p) := by simp [q, ZMod.pow_card_pow]
  have hn : (n : ZMod p) ^ q = (n : ZMod p) := by simp [q, ZMod.pow_card_pow]
  rw [hm, hn] at hpow
  exact (ZMod.intCast_eq_intCast_iff m n p).mp hpow

end

section

variable {G : Type} [Group G] [Finite G]
variable {A : Type v} [CommRing A] [IsDomain A] [Ring.HasFiniteQuotients A]
variable [Algebra A ℂ] [IsIntegralClosure A ℤ ℂ]

local notation "SpecARG" => PrimeSpectrum (A ⊗R(G))

/-- Helper for Proposition 11-11.4-1: every nonzero prime of the arithmetic coefficient ring is
one of the residual-characteristic maximal ideals indexing Serre's regular branch. -/
theorem nonzero_primeSpectrum_eq_residual_maximal
    (q : PrimeSpectrum A) (hq : q.asIdeal ≠ ⊥) :
    ∃ p : Nat.Primes, ∃ M : NonzeroResidualCharacteristicMaximalIdeal A p,
      M.1.asIdeal = q.asIdeal := by
  -- A nonzero prime becomes maximal because every nonzero quotient of `A` is finite.
  letI : q.asIdeal.IsMaximal :=
    Ring.HasFiniteQuotients.maximalOfPrime hq
  have hfiniteQuot : Finite (A ⧸ q.asIdeal) :=
    Ring.HasFiniteQuotients.finiteQuotient hq
  letI : Finite (A ⧸ q.asIdeal) := hfiniteQuot
  -- The residue field is finite, so its characteristic is a genuine prime number.
  have hfiniteResidue : Finite q.asIdeal.ResidueField := by
    exact Finite.of_surjective
      (algebraMap (A ⧸ q.asIdeal) q.asIdeal.ResidueField)
      (Ideal.bijective_algebraMap_quotient_residueField q.asIdeal).surjective
  letI : Finite q.asIdeal.ResidueField := hfiniteResidue
  let p : Nat.Primes :=
    ⟨ringChar q.asIdeal.ResidueField, CharP.prime_ringChar q.asIdeal.ResidueField⟩
  let M : NonzeroResidualCharacteristicMaximalIdeal A p :=
    ⟨⟨q.asIdeal, inferInstance⟩, hq, by
      simpa [p] using
        (inferInstance : CharP q.asIdeal.ResidueField (ringChar q.asIdeal.ResidueField))⟩
  -- The packaged maximal ideal is definitionally the original prime ideal.
  exact ⟨p, M, rfl⟩

/-- Helper for Proposition 11-11.4-1: the source-spectrum route already classifies every prime of
`A ⊗ R(G)` into the zero branch or into a fixed-class evaluation pullback over a residual
maximal ideal. This is the verified prefix of Serre's proof before the remaining regular-branch
owner identification is applied. -/
theorem tensor_character_ring_prime_ideal_source_presentation
    (𝔭 : SpecARG) :
    (∃ c : ConjClasses G, tensorCharacterRingZeroPrimeIdeal A c = 𝔭) ∨
      ∃ p : Nat.Primes, ∃ M : NonzeroResidualCharacteristicMaximalIdeal A p,
        ∃ d : ConjClasses G,
          PrimeSpectrum.comap (tensorCharacterRingValueAtConjClass (A := A) (G := G) d)
            (⟨M.1.asIdeal, inferInstance⟩ : PrimeSpectrum A) = 𝔭 := by
  by_cases h𝔭 :
      Ideal.comap (algebraMap A (A ⊗R(G))) 𝔭.asIdeal = ⊥
  · left
    -- The zero-contraction branch is already handled by the extracted source-presentation theorem.
    exact
      zero_fiber_prime_classification_over_bot_of_source_presentation
        (A := A) (G := G) h𝔭
  · right
    let q : PrimeSpectrum A :=
      PrimeSpectrum.comap (algebraMap A (A ⊗R(G))) 𝔭
    have hq : q.asIdeal ≠ ⊥ := by
      -- The negated zero branch says exactly that the contracted coefficient prime is nonzero.
      simpa [q] using h𝔭
    obtain ⟨p, M, hM⟩ :=
      nonzero_primeSpectrum_eq_residual_maximal (A := A) q hq
    have hcontract :
        Ideal.comap (algebraMap A (A ⊗R(G))) 𝔭.asIdeal = M.1.asIdeal := by
      -- Re-express the contracted prime using the packaged residual-characteristic maximal ideal.
      simpa [q] using hM.symm
    obtain ⟨d, q', hq'⟩ :=
      source_prime_eq_value_comap_of_class (A := A) (G := G) 𝔭
    have hqIdeal : q'.asIdeal = M.1.asIdeal := by
      calc
        q'.asIdeal =
            Ideal.comap (algebraMap A (A ⊗R(G)))
              (PrimeSpectrum.comap
                (tensorCharacterRingValueAtConjClass (A := A) (G := G) d) q').asIdeal := by
                  symm
                  exact value_comap_eq_source_prime (A := A) (G := G) d q'
        _ = Ideal.comap (algebraMap A (A ⊗R(G))) 𝔭.asIdeal := by
              simpa [hq']
        _ = M.1.asIdeal := hcontract
    have hqEq : q' = (⟨M.1.asIdeal, inferInstance⟩ : PrimeSpectrum A) := by
      apply PrimeSpectrum.ext
      simpa using hqIdeal
    -- This is the exact nonzero branch that remains to be identified with Serre's indexed
    -- regular owner `P_{M,c}`.
    exact ⟨p, M, d, by simpa [hqEq] using hq'⟩

/-- Helper for Proposition 11-11.4-1: evaluating at a fixed conjugacy class and then contracting
back to `A` recovers the chosen residual-characteristic maximal ideal. This is the easy scalar
half of the nonzero source branch. -/
theorem value_comap_eq_fixed_maximal
    (p : Nat.Primes) (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (d : ConjClasses G) :
    Ideal.comap (algebraMap A (A ⊗R(G)))
        (PrimeSpectrum.comap (tensorCharacterRingValueAtConjClass (A := A) (G := G) d)
          (⟨M.1.asIdeal, inferInstance⟩ : PrimeSpectrum A)).asIdeal =
      M.1.asIdeal := by
  -- The fixed-class evaluation fixes scalar tensors, so the source prime contracts back to `M`.
  simpa using
    value_comap_eq_source_prime (A := A) (G := G) d
      (⟨M.1.asIdeal, inferInstance⟩ : PrimeSpectrum A)

/-- Helper for Proposition 11-11.4-1: a pure induction generator belongs to the evaluation
pullback prime over `M` exactly when its fixed-class value lies in `M`. This is the stable
rewrite needed before the regular-owner criterion can be applied. -/
theorem induction_generator_mem_value_comap_iff
    (M : MaximalSpectrum A) (d : ConjClasses G) (H : Subgroup G) (χ : R(H)) :
    (Algebra.TensorProduct.includeRight (R := ℤ) (A := A) (B := R(G))
      (H.characterRingInduction_local χ)) ∈
      (PrimeSpectrum.comap (tensorCharacterRingValueAtConjClass (A := A) (G := G) d)
        (⟨M.asIdeal, inferInstance⟩ : PrimeSpectrum A)).asIdeal ↔
        characterRingValueAtConjClass (A := A) d
          (H.characterRingInduction_local χ) ∈ M.asIdeal := by
  -- Membership in a prime comap is definitionally membership of the evaluated image.
  change
    tensorCharacterRingValueAtConjClass (A := A) (G := G) d
        (Algebra.TensorProduct.includeRight (R := ℤ) (A := A) (B := R(G))
          (H.characterRingInduction_local χ)) ∈ M.asIdeal ↔
      _
  -- On pure tensors from the character-ring factor, the tensor evaluator is the fixed-class value.
  simp [tensorCharacterRingValueAtConjClass]

/-- Helper for Proposition 11-11.4-1: if the owner class of `d` has no associated
`p`-elementary subgroup inside `H`, then no conjugate of any associated subgroup built from a
representative of that owner can lie inside `H`. This is the exact hypothesis shape required by
Theorem `11-11.3-2`. -/
theorem no_conjugate_associated_subgroup_of_not_hasAssociated_owner
    (p : Nat.Primes) (H : Subgroup G) (d : ConjClasses G) {x : G}
    (hx :
      x ∈
        ((Proposition_11_11_4_1.pregular_conj_class_of_conj_class (G := G) p d :
          PRegularConjClass G p) : ConjClasses G).carrier)
    (P : Sylow (p : ℕ) (Subgroup.centralizer ({x} : Set G)))
    (hNotAssoc :
      ¬ HasAssociatedPElementarySubgroupInClass
          (Proposition_11_11_4_1.pregular_conj_class_of_conj_class (G := G) p d) H) :
    ∀ g : G, ¬ MulAut.conj g • associatedPElementarySubgroup (p : ℕ) x P ≤ H := by
  intro g hg
  letI : Fact ((p : ℕ).Prime) := ⟨p.2⟩
  let owner : PRegularConjClass G p :=
    Proposition_11_11_4_1.pregular_conj_class_of_conj_class (G := G) p d
  let P' :
      Sylow (p : ℕ) (Subgroup.centralizer ({MulAut.conj g x} : Set G)) :=
    P.mapSurjective
      (show Function.Surjective
          (Proposition_11_11_4_1.centralizer_conj_equiv (G := G) g x).toMonoidHom from
        (Proposition_11_11_4_1.centralizer_conj_equiv (G := G) g x).surjective)
  have hxg :
      MulAut.conj g x ∈ ((owner : PRegularConjClass G p) : ConjClasses G).carrier := by
    -- Conjugating a representative stays inside the same owner conjugacy class.
    apply ConjClasses.mem_carrier_iff_mk_eq.mpr
    calc
      ConjClasses.mk (MulAut.conj g x) = ConjClasses.mk x := by
        exact ConjClasses.mk_eq_mk_iff_isConj.mpr
          (isConj_iff.mpr ⟨g⁻¹, by simp [MulAut.conj_apply, mul_assoc]⟩)
      _ = ((owner : PRegularConjClass G p) : ConjClasses G) :=
        ConjClasses.mem_carrier_iff_mk_eq.mp hx
  have hmap :
      Subgroup.map (MulAut.conj g).toMonoidHom
          (associatedPElementarySubgroup (p : ℕ) x P) ≤ H := by
    simpa using hg
  have htransport :
      associatedPElementarySubgroup (p : ℕ) (MulAut.conj g x) P' ≤ H := by
    -- The stable conjugation-transport lemma rewrites the given subgroup inclusion into the
    -- canonical owner-facing subgroup at the conjugated representative.
    let htransport_eq :=
      Proposition_11_11_4_1.associatedPElementarySubgroup_conj_transport_stable
        (G := G) p (x := x) (g := g) P
    simpa [P'] using htransport_eq ▸ hmap
  exact hNotAssoc
    (hasAssociatedPElementarySubgroupInClass_of_le
      (c := owner) (H := H) hxg P' htransport)

/-- Helper for Proposition 11-11.4-1: if an `A`-valued quantity becomes a `p`-multiple of an
algebraic integer in `ℂ`, then it lies in every maximal ideal of residual characteristic `p`.
This separates the coefficient-ring descent from the group-theoretic part of the regular-branch
criterion. -/
theorem mem_residual_maximal_of_complex_prime_multiple
    (p : Nat.Primes) (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    {a : A} {z : integralClosure ℤ ℂ}
    (ha : algebraMap A ℂ a = (z : ℂ) * (p : ℂ)) :
    a ∈ M.1.asIdeal := by
  obtain ⟨b, hb⟩ :
      (z : ℂ) ∈ Set.range (algebraMap A ℂ) := by
    -- Every algebraic integer of `ℂ` already comes from `A`, because `A` is an integral closure
    -- of `ℤ` inside `ℂ`.
    exact
      (IsIntegralClosure.isIntegral_iff (A := A) (R := ℤ) (B := ℂ)).mp <|
        (IsIntegralClosure.isIntegral_iff
          (A := integralClosure ℤ ℂ) (R := ℤ) (B := ℂ)).2
          ⟨z, rfl⟩
  have haA : a = b * (p : A) := by
    -- Compare the complex realizations and then use injectivity of `A → ℂ`.
    apply IsIntegralClosure.algebraMap_injective A ℤ ℂ
    calc
      algebraMap A ℂ a = (z : ℂ) * (p : ℂ) := ha
      _ = algebraMap A ℂ b * (p : ℂ) := by rw [hb]
      _ = algebraMap A ℂ (b * (p : A)) := by
        rw [map_mul, map_natCast]
  have hp0 :
      (p : A ⧸ M.1.asIdeal) = 0 := by
    -- The quotient by `M` has characteristic `p`, so the scalar `p` vanishes there.
    letI : CharP M.1.asIdeal.ResidueField p := M.2.2
    letI : CharP (A ⧸ M.1.asIdeal) p :=
      RingHom.charP
        (algebraMap (A ⧸ M.1.asIdeal) M.1.asIdeal.ResidueField)
        M.1.asIdeal.injective_algebraMap_quotient_residueField p
    exact CharP.cast_eq_zero (R := A ⧸ M.1.asIdeal) p
  have hp_mem : (p : A) ∈ M.1.asIdeal := by
    exact Ideal.Quotient.eq_zero_iff_mem.mp (by simpa using hp0)
  rw [haA]
  -- Once the value is written as `b * p`, the ideal membership is just closure under
  -- multiplication by arbitrary coefficients.
  simpa [smul_eq_mul] using (M.1.asIdeal.smul_mem b hp_mem)

/-- Helper for Proposition 11-11.4-1: an `A`-valued quantity whose complex realization is an
integer divisible by the residual characteristic already lies in the maximal ideal `M`. This is
the integer-valued counterpart to the algebraic-integer descent used on induction values. -/
theorem mem_residual_maximal_of_integer_value_dvd
    (p : Nat.Primes) (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    {a : A} {n : ℤ}
    (ha : algebraMap A ℂ a = (n : ℂ))
    (hn : (p : ℤ) ∣ n) :
    a ∈ M.1.asIdeal := by
  rcases hn with ⟨m, rfl⟩
  -- Rewrite the integer value as an explicit `p`-multiple and apply the algebraic-integer
  -- descent already proved above.
  refine mem_residual_maximal_of_complex_prime_multiple (A := A) (p := p) (M := M)
    (a := a) (z := algebraMap ℤ (integralClosure ℤ ℂ) m) ?_
  calc
    algebraMap A ℂ a = ((m : ℤ) * (p : ℤ) : ℂ) := by
      simpa [Int.cast_mul, mul_comm] using ha
    _ = ((algebraMap ℤ (integralClosure ℤ ℂ) m : integralClosure ℤ ℂ) : ℂ) * (p : ℂ) := by
      simp [Int.cast_mul]

/-- Helper for Proposition 11-11.4-1: an `A`-valued quantity whose complex realization is an
integer not divisible by the residual characteristic cannot lie in the maximal ideal `M`. This is
the arithmetic endpoint needed for the future Brauer witness on the regular branch. -/
theorem not_mem_residual_maximal_of_integer_value_not_dvd
    (p : Nat.Primes) (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    {a : A} {n : ℤ}
    (ha : algebraMap A ℂ a = (n : ℂ))
    (hn : ¬ (p : ℤ) ∣ n) :
    a ∉ M.1.asIdeal := by
  intro haM
  have haA : a = (n : A) := by
    -- Compare the complex realizations and use injectivity of `A → ℂ` to identify `a` with the
    -- integer element `n` inside `A`.
    apply IsIntegralClosure.algebraMap_injective A ℤ ℂ
    calc
      algebraMap A ℂ a = (n : ℂ) := ha
      _ = algebraMap A ℂ (n : A) := by simp
  have hn_mem : (n : A) ∈ M.1.asIdeal := by
    simpa [haA] using haM
  have hp0 :
      (p : A ⧸ M.1.asIdeal) = 0 := by
    -- The quotient by `M` has characteristic `p`, so the scalar `p` vanishes there.
    letI : CharP M.1.asIdeal.ResidueField p := M.2.2
    letI : CharP (A ⧸ M.1.asIdeal) p :=
      RingHom.charP
        (algebraMap (A ⧸ M.1.asIdeal) M.1.asIdeal.ResidueField)
        M.1.asIdeal.injective_algebraMap_quotient_residueField p
    exact CharP.cast_eq_zero (R := A ⧸ M.1.asIdeal) p
  have hp_mem : ((p : ℤ) : A) ∈ M.1.asIdeal := by
    exact Ideal.Quotient.eq_zero_iff_mem.mp (by simpa using hp0)
  have hnat_not_dvd : ¬ (p : ℕ) ∣ n.natAbs := by
    intro hdiv
    exact hn <|
      (Int.dvd_natAbs).mp <|
        Int.natCast_dvd_natCast.mpr hdiv
  have hcop : Nat.Coprime n.natAbs (p : ℕ) := by
    exact ((Nat.Prime.coprime_iff_not_dvd p.2).2 hnat_not_dvd).symm
  have hgcd : Int.gcd n (p : ℤ) = 1 := by
    -- Convert the prime-to-`p` hypothesis into the integer gcd form needed for Bézout.
    simpa [Int.gcd_def, Nat.gcd_comm] using hcop.gcd_eq_one
  have hbezout :
      n * Int.gcdA n (p : ℤ) + (p : ℤ) * Int.gcdB n (p : ℤ) = 1 := by
    -- Rewrite the integer gcd identity into a Bézout relation for `n` and `p`.
    simpa [hgcd] using (Int.gcd_eq_gcd_ab n (p : ℤ)).symm
  have hbezoutA :
      ((n * Int.gcdA n (p : ℤ) + (p : ℤ) * Int.gcdB n (p : ℤ) : ℤ) : A) = 1 := by
    -- Move the Bézout relation from integers into the coefficient ring `A`.
    simpa using congrArg (fun z : ℤ ↦ (z : A)) hbezout
  have h1_mem : (1 : A) ∈ M.1.asIdeal := by
    have hleft :
        ((n : A) * (Int.gcdA n (p : ℤ) : A)) ∈ M.1.asIdeal := by
      exact M.1.asIdeal.mul_mem_right (Int.cast (R := A) (Int.gcdA n (p : ℤ))) hn_mem
    have hright :
        (((p : ℤ) : A) * (Int.gcdB n (p : ℤ) : A)) ∈ M.1.asIdeal := by
      simpa [mul_comm] using
        M.1.asIdeal.mul_mem_left (Int.cast (R := A) (Int.gcdB n (p : ℤ))) hp_mem
    have hsum :
        ((n : A) * (Int.gcdA n (p : ℤ) : A) +
          (((p : ℤ) : A) * (Int.gcdB n (p : ℤ) : A))) ∈ M.1.asIdeal :=
      M.1.asIdeal.add_mem hleft hright
    rw [← hbezoutA]
    simpa [Int.cast_add, Int.cast_mul] using hsum
  have htop : M.1.asIdeal = ⊤ :=
    Ideal.eq_top_of_isUnit_mem M.1.asIdeal h1_mem (by simp)
  exact M.1.2.ne_top htop

/-- Helper for Proposition 11-11.4-1: every induced class function coming from the realized scalar
extension on a subgroup is represented by an element of Serre's induction ideal `I_H`. This
separates the tensor-realization step from the later Brauer arithmetic on the induced values. -/
theorem induced_realization_mem_tensorCharacterRingInductionIdeal
    (H : Subgroup G) {f : H → ℂ}
    (hf : f ∈ characterRingScalarExtension A H) :
    ∃ ξ : A ⊗R(G), ξ ∈ tensorCharacterRingInductionIdeal (A := A) (G := G) H ∧
      (ξ : G → ℂ) = Ind[H](f) := by
  -- Induct over the defining `A`-span of the scalar extension on `H`, so the base case is
  -- exactly one generator of Serre's induction ideal `I_H`.
  induction hf using Submodule.span_induction with
  | mem χ hχ =>
      refine ⟨Algebra.TensorProduct.includeRight (R := ℤ) (A := A) (B := R(G))
          (Subgroup.characterRingInduction_local (G := G) H ⟨χ, hχ⟩), ?_, ?_⟩
      · -- By definition, the local induction generator is one of the spanning generators of `I_H`.
        exact Ideal.subset_span ⟨⟨χ, hχ⟩, rfl⟩
      · -- The chosen generator realizes the induced class function pointwise on `G`.
        ext g
        simp [Algebra.TensorProduct.includeRight, Subgroup.characterRingInduction_local_apply]
  | zero =>
      refine ⟨0, Ideal.zero_mem _, ?_⟩
      -- Induction sends the zero class function to the zero class function.
      ext g
      simp [Subgroup.inducedClassFunction]
  | add f₁ f₂ _ _ hf₁ hf₂ =>
      rcases hf₁ with ⟨ξ₁, hξ₁_mem, hξ₁_eval⟩
      rcases hf₂ with ⟨ξ₂, hξ₂_mem, hξ₂_eval⟩
      refine ⟨ξ₁ + ξ₂,
        (tensorCharacterRingInductionIdeal (A := A) (G := G) H).add_mem hξ₁_mem hξ₂_mem,
        ?_⟩
      -- The tensor realization is additive, and subgroup induction is additive as well.
      ext g
      calc
        ((ξ₁ + ξ₂ : A ⊗R(G)) : G → ℂ) g = (ξ₁ : G → ℂ) g + (ξ₂ : G → ℂ) g := by
          simp
        _ = Ind[H](f₁) g + Ind[H](f₂) g := by rw [hξ₁_eval, hξ₂_eval]
        _ = Ind[H](f₁ + f₂) g := by
          simpa [Subgroup.inducedClassFunction_map_add]
  | smul a f _ hf' =>
      rcases hf' with ⟨ξ, hξ_mem, hξ_eval⟩
      have hsmul_mem : a • ξ ∈ tensorCharacterRingInductionIdeal (A := A) (G := G) H := by
        have hsmul_eq :
            a • ξ = (algebraMap A (A ⊗R(G)) a) * ξ := by
          simpa using (Algebra.smul_def a ξ)
        have hmul :
            (algebraMap A (A ⊗R(G)) a) * ξ ∈
              tensorCharacterRingInductionIdeal (A := A) (G := G) H :=
          (tensorCharacterRingInductionIdeal (A := A) (G := G) H).mul_mem_left
            (algebraMap A (A ⊗R(G)) a) hξ_mem
        rw [hsmul_eq]
        exact hmul
      refine ⟨a • ξ, hsmul_mem, ?_⟩
      -- Scalar multiplication commutes with both the tensor realization and subgroup induction.
      ext g
      calc
        ((a • ξ : A ⊗R(G)) : G → ℂ) g = algebraMap A ℂ a * (ξ : G → ℂ) g := by
          change
            (((characterRingScalarExtension A G).subtype ∘ₗ
                Submodule.tensorToSpan A (Subalgebra.toSubmodule R[ℂ](G))) (a • ξ)) g =
              algebraMap A ℂ a * (ξ : G → ℂ) g
          rw [LinearMap.map_smul]
          simp [Pi.smul_apply, Algebra.smul_def]
        _ = algebraMap A ℂ a * Ind[H](f) g := by rw [hξ_eval]
        _ = Ind[H](a • f) g := by
          simpa [Pi.smul_apply, Algebra.smul_def, mul_comm] using
            congrFun
              (Subgroup.inducedClassFunction_map_smul (S := A) H a f).symm g

/-- Helper for Proposition 11-11.4-1: the forward half of Serre's regular-prime criterion is
already available once the canonical `p`-regular owner of `d` is represented by a concrete
element `x`. This isolates the Chapter `11.3` divisibility step before transporting the result
back from `ConjClasses.mk x` to the original class `d` modulo `M`. -/
theorem tensorCharacterRingInductionIdeal_le_value_comap_of_not_hasAssociated_owner_representative
    (p : Nat.Primes) (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (d : ConjClasses G) (H : Subgroup G) {x : G}
    (hx :
      x ∈
        ((Proposition_11_11_4_1.pregular_conj_class_of_conj_class (G := G) p d :
          PRegularConjClass G p) : ConjClasses G).carrier)
    (hNotAssoc :
      ¬ HasAssociatedPElementarySubgroupInClass
          (Proposition_11_11_4_1.pregular_conj_class_of_conj_class (G := G) p d) H) :
    tensorCharacterRingInductionIdeal (A := A) (G := G) H ≤
      (PrimeSpectrum.comap
        (tensorCharacterRingValueAtConjClass (A := A) (G := G) (ConjClasses.mk x))
        (⟨M.1.asIdeal, inferInstance⟩ : PrimeSpectrum A)).asIdeal := by
  classical
  let owner : PRegularConjClass G p :=
    Proposition_11_11_4_1.pregular_conj_class_of_conj_class (G := G) p d
  letI : Fact ((p : ℕ).Prime) := ⟨p.2⟩
  let P : Sylow (p : ℕ) (Subgroup.centralizer ({x} : Set G)) :=
    Classical.choice
      (show Nonempty (Sylow (p : ℕ) (Subgroup.centralizer ({x} : Set G))) from Sylow.nonempty)
  -- Reduce ideal containment to checking the source generators coming from subgroup induction.
  refine Ideal.span_le.mpr ?_
  rintro _ ⟨χ, rfl⟩
  refine
    (induction_generator_mem_value_comap_iff
      (A := A) (G := G) M.1 (ConjClasses.mk x) H χ).2 ?_
  have hxreg : IsPRegular (p : ℕ) x := owner.2 x hx
  have hnoConj :
      ∀ g : G, ¬ MulAut.conj g • associatedPElementarySubgroup (p : ℕ) x P ≤ H :=
    no_conjugate_associated_subgroup_of_not_hasAssociated_owner
      (G := G) p H d hx P hNotAssoc
  obtain ⟨z, hz⟩ :=
    induced_characterRing_value_eq_prime_multiple_of_algebraicInteger
      (p := (p : ℕ)) (H := H) (x := x) hxreg P hnoConj χ
  have hclass :
      ((H.characterRingInduction_local χ : R(G)) : G → ℂ)
          (Proposition_11_11_4_1.conjClassRepresentative (G := G) (ConjClasses.mk x)) =
        ((H.characterRingInduction_local χ : R(G)) : G → ℂ) x := by
    have hf :
        _root_.IsClassFunction
          (((H.characterRingInduction_local χ : R(G)) : G → ℂ)) := by
      exact
        Representation.isClassFunction_of_mem_characterRingOverField
          (K := ℂ) (H.characterRingInduction_local χ)
          (H.characterRingInduction_local χ).property
    -- The chosen representative of `ConjClasses.mk x` is conjugate to `x`, so class functions
    -- take the same value at both points.
    exact hf.eq_of_isConj <|
      ConjClasses.mk_eq_mk_iff_isConj.mp <|
        by simpa using
          Proposition_11_11_4_1.conjClassRepresentative_mk (G := G) (ConjClasses.mk x)
  -- Chapter `11.3` gives the required value as a `p`-multiple in `ℂ`, and the residual
  -- characteristic of `M` descends that multiple back to membership in `M`.
  refine mem_residual_maximal_of_complex_prime_multiple (A := A) (p := p) (M := M)
    (a := characterRingValueAtConjClass (A := A) (G := G) (ConjClasses.mk x)
      (H.characterRingInduction_local χ))
    (z := z) ?_
  calc
    algebraMap A ℂ
        (characterRingValueAtConjClass (A := A) (G := G) (ConjClasses.mk x)
          (H.characterRingInduction_local χ)) =
        ((H.characterRingInduction_local χ : R(G)) : G → ℂ)
          (Proposition_11_11_4_1.conjClassRepresentative (G := G) (ConjClasses.mk x)) := by
            simpa using
              characterRingValueAtConjClass_algebraMap (A := A) (G := G) (ConjClasses.mk x)
                (H.characterRingInduction_local χ)
    _ = ((H.characterRingInduction_local χ : R(G)) : G → ℂ) x := hclass
    _ = (z : ℂ) * (p : ℂ) := by
          simpa [Subgroup.characterRingInduction_local,
            Representation.Subgroup.characterRingInduction] using hz.symm

/-- Helper for Proposition 11-11.4-1: the forward half of Serre's regular-prime criterion can be
applied at the canonical owner representative obtained by taking the `p'`-part of the fixed
representative of `d`. This packages the arbitrary-representative lemma above in the exact
source-chosen form used by the remaining transport step back to `d`. -/
theorem tensorCharacterRingInductionIdeal_le_value_comap_of_not_hasAssociated_owner_canonical_representative
    (p : Nat.Primes) (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (d : ConjClasses G) (H : Subgroup G)
    (hNotAssoc :
      ¬ HasAssociatedPElementarySubgroupInClass
          (Proposition_11_11_4_1.pregular_conj_class_of_conj_class (G := G) p d) H) :
    tensorCharacterRingInductionIdeal (A := A) (G := G) H ≤
      (PrimeSpectrum.comap
        (tensorCharacterRingValueAtConjClass (A := A) (G := G)
          (ConjClasses.mk
            (pRegularComponent p
              (Proposition_11_11_4_1.conjClassRepresentative (G := G) d))))
        (⟨M.1.asIdeal, inferInstance⟩ : PrimeSpectrum A)).asIdeal := by
  let x : G := pRegularComponent p
    (Proposition_11_11_4_1.conjClassRepresentative (G := G) d)
  have hx :
      x ∈
        ((Proposition_11_11_4_1.pregular_conj_class_of_conj_class (G := G) p d :
          PRegularConjClass G p) : ConjClasses G).carrier := by
    -- Rewrite the owner of `d` to the owner of its chosen representative, then note that a
    -- conjugacy class contains the representative used to define it.
    rw [← Proposition_11_11_4_1.conjClassRepresentative_mk (G := G) d]
    simpa [x, Proposition_11_11_4_1.pregular_conj_class_of_element] using
      (ConjClasses.mem_carrier_iff_mk_eq.mpr rfl :
        pRegularComponent p (Proposition_11_11_4_1.conjClassRepresentative (G := G) d) ∈
          (ConjClasses.mk
            (pRegularComponent p
              (Proposition_11_11_4_1.conjClassRepresentative (G := G) d))).carrier)
  -- Apply the representative-level forward implication to the canonical source representative.
  simpa [x] using
    tensorCharacterRingInductionIdeal_le_value_comap_of_not_hasAssociated_owner_representative
      (A := A) (G := G) p M d H hx hNotAssoc

/-- Helper for Proposition 11-11.4-1: transporting a tensor character from the standard integral
closure `integralClosure ℤ ℂ` to the chosen coefficient ring `A` preserves its complex-valued
realization. -/
theorem transport_integralClosure_tensorCharacter_realization
    {H : Subgroup G}
    (ψ : (↥(integralClosure ℤ ℂ)) ⊗R(H)) :
    let e : (↥(integralClosure ℤ ℂ)) ≃ₐ[ℤ] A :=
      IsIntegralClosure.equiv ℤ (↥(integralClosure ℤ ℂ)) ℂ A
    (((Algebra.TensorProduct.map e.toAlgHom (AlgHom.id ℤ (R(H))) ψ :
        A ⊗R(H)) : H → ℂ)) = (ψ : H → ℂ) := by
  let e : (↥(integralClosure ℤ ℂ)) ≃ₐ[ℤ] A :=
    IsIntegralClosure.equiv ℤ (↥(integralClosure ℤ ℂ)) ℂ A
  induction ψ using TensorProduct.induction_on with
  | zero =>
      -- The transported zero tensor still realizes the zero class function.
      ext h
      simp
  | tmul a χ =>
      -- On pure tensors, the transport only changes the coefficient representative, and
      -- `IsIntegralClosure.equiv` preserves the scalar embedding into `ℂ`.
      ext h
      simp [TensorProduct.map_tmul, Submodule.tensorToSpan_apply_tmul, Algebra.smul_def,
        IsIntegralClosure.algebraMap_equiv
          (R := ℤ) (A := ↥(integralClosure ℤ ℂ)) (B := ℂ) (A' := A) a]
  | add ψ₁ ψ₂ hψ₁ hψ₂ =>
      -- The realization map and the coefficient transport are both additive.
      ext h
      calc
        ((characterRingScalarExtension A H).subtype ∘ₗ
            Submodule.tensorToSpan A (Subalgebra.toSubmodule R[ℂ](H)))
            ((Algebra.TensorProduct.map e.toAlgHom (AlgHom.id ℤ (R(H))) (ψ₁ + ψ₂))) h =
          ((characterRingScalarExtension A H).subtype ∘ₗ
              Submodule.tensorToSpan A (Subalgebra.toSubmodule R[ℂ](H)))
              ((Algebra.TensorProduct.map e.toAlgHom (AlgHom.id ℤ (R(H))) ψ₁)) h +
            ((characterRingScalarExtension A H).subtype ∘ₗ
              Submodule.tensorToSpan A (Subalgebra.toSubmodule R[ℂ](H)))
              ((Algebra.TensorProduct.map e.toAlgHom (AlgHom.id ℤ (R(H))) ψ₂)) h := by
                simp
        _ =
          ((characterRingScalarExtension ↥(integralClosure ℤ ℂ) H).subtype ∘ₗ
              Submodule.tensorToSpan (↥(integralClosure ℤ ℂ))
                (Subalgebra.toSubmodule R[ℂ](H))) ψ₁ h +
            ((characterRingScalarExtension ↥(integralClosure ℤ ℂ) H).subtype ∘ₗ
              Submodule.tensorToSpan (↥(integralClosure ℤ ℂ))
                (Subalgebra.toSubmodule R[ℂ](H))) ψ₂ h := by
                  rw [hψ₁, hψ₂]
                  rfl
        _ =
          ((characterRingScalarExtension ↥(integralClosure ℤ ℂ) H).subtype ∘ₗ
              Submodule.tensorToSpan (↥(integralClosure ℤ ℂ))
                (Subalgebra.toSubmodule R[ℂ](H))) (ψ₁ + ψ₂) h := by
                  simp

/-- Helper for Proposition 11-11.4-1: restricting a realized scalar-extension class function from
`L` to the subgroup-of-`H` copy `L.subgroupOf H` preserves scalar-extension membership. This is
the thin interface bridge needed before induction in stages can move the auxiliary witness from
its associated subgroup into `I_H`. -/
theorem subgroupOf_restriction_mem_characterRingScalarExtension
    (L H : Subgroup G) (hL : L ≤ H) {f : L → ℂ}
    (hf : f ∈ characterRingScalarExtension A L) :
    (fun z : L.subgroupOf H ↦ f ((Subgroup.subgroupOfEquivOfLe hL) z)) ∈
      characterRingScalarExtension A (L.subgroupOf H) := by
  -- Transport the defining span across the canonical subgroup equivalence `L.subgroupOf H ≃* L`.
  rw [characterRingScalarExtension] at hf ⊢
  induction hf using Submodule.span_induction with
  | mem ψ hψ =>
    let e : L.subgroupOf H ≃* L := Subgroup.subgroupOfEquivOfLe hL
    let χ : R(L.subgroupOf H) := Subgroup.characterRingTransport e ⟨ψ, hψ⟩
    have hχ :
        ((χ : R(L.subgroupOf H)) : L.subgroupOf H → ℂ) =
          fun z : L.subgroupOf H ↦ ψ (e z) := by
      ext z
      simp [χ, e, Subgroup.characterRingTransport_apply]
    exact hχ ▸ Submodule.subset_span χ.property
  | zero =>
    exact Submodule.zero_mem _
  | add f₁ f₂ _ _ hf₁ hf₂ =>
    exact Submodule.add_mem _ hf₁ hf₂
  | smul a g _ hg =>
    exact Submodule.smul_mem _ a hg

/-- Helper for Proposition 11-11.4-1: if `L ≤ H` and a class function on `L` lies in the realized
scalar extension, then its direct induction from `L` to `G` is realized by an element of Serre's
induction ideal `I_H`. This packages the restriction-to-`L.subgroupOf H` and induction-in-stages
route into a single reusable witness theorem. -/
theorem induced_realization_mem_tensorCharacterRingInductionIdeal_of_le
    (L H : Subgroup G) (hL : L ≤ H) {f : L → ℂ}
    (hf : f ∈ characterRingScalarExtension A L) :
    ∃ ξ : A ⊗R(G), ξ ∈ tensorCharacterRingInductionIdeal (A := A) (G := G) H ∧
      (ξ : G → ℂ) = Ind[L](f) := by
  let fH : H → ℂ :=
    Ind[L.subgroupOf H](
      fun z : L.subgroupOf H ↦ f ((Subgroup.subgroupOfEquivOfLe hL) z))
  have hf_restr :
      (fun z : L.subgroupOf H ↦ f ((Subgroup.subgroupOfEquivOfLe hL) z)) ∈
        characterRingScalarExtension A (L.subgroupOf H) :=
    subgroupOf_restriction_mem_characterRingScalarExtension
      (A := A) (G := G) L H hL hf
  have hfH : fH ∈ characterRingScalarExtension A H := by
    -- First realize the restricted auxiliary function on `H`, then induce inside `H`.
    simpa [fH] using
      induced_mem_characterRingScalarExtension_of_mem
        (A := A) (G := H) (H := L.subgroupOf H) hf_restr
  rcases induced_realization_mem_tensorCharacterRingInductionIdeal
      (A := A) (G := G) H hfH with ⟨ξ, hξ_mem, hξ_eval⟩
  refine ⟨ξ, hξ_mem, ?_⟩
  -- Induction in stages identifies the realization of the `I_H` witness with direct induction
  -- from the original subgroup `L`.
  calc
    (ξ : G → ℂ) = Ind[H](fH) := hξ_eval
    _ = Ind[L](f) := by
      simpa [fH] using
        (Subgroup.inducedClassFunction_subgroupOf_induction_in_stages
          (H := H) (L := L) hL f)

/-- Helper for Proposition 11-11.4-1: an associated owner subgroup should supply an explicit
element of Serre's induction ideal `I_H` whose fixed-class value is an integer prime to `p`, so
it cannot lie in the evaluation pullback prime over `M`. -/
theorem associated_owner_induction_witness_not_mem_owner_value_comap
    (p : Nat.Primes) (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (d : ConjClasses G) (H : Subgroup G) {x : G}
    (hx :
      x ∈
        ((Proposition_11_11_4_1.pregular_conj_class_of_conj_class (G := G) p d :
          PRegularConjClass G p) : ConjClasses G).carrier)
    (P : Sylow (p : ℕ) (Subgroup.centralizer ({x} : Set G)))
    (hP : associatedPElementarySubgroup (p : ℕ) x P ≤ H) :
    ∃ ξ : A ⊗R(G), ξ ∈ tensorCharacterRingInductionIdeal (A := A) (G := G) H ∧
      ξ ∉ (PrimeSpectrum.comap
        (tensorCharacterRingValueAtConjClass (A := A) (G := G) (ConjClasses.mk x))
        (⟨M.1.asIdeal, inferInstance⟩ : PrimeSpectrum A)).asIdeal := by
  let owner : PRegularConjClass G p :=
    Proposition_11_11_4_1.pregular_conj_class_of_conj_class (G := G) p d
  let L : Subgroup G := associatedPElementarySubgroup (p : ℕ) x P
  have hxreg : IsPRegular (p : ℕ) x := owner.2 x hx
  letI : Fact ((p : ℕ).Prime) := ⟨p.2⟩
  obtain ⟨ψ, hψ_int, ⟨n, hnval, hndiv⟩, _hψ_zero⟩ :=
    exists_associated_auxiliary_character_with_brauer_induction_support
      (p := (p : ℕ)) (x := x) P hxreg
  let e : (↥(integralClosure ℤ ℂ)) ≃ₐ[ℤ] A :=
    IsIntegralClosure.equiv ℤ (↥(integralClosure ℤ ℂ)) ℂ A
  let ψA : A ⊗R(L) :=
    Algebra.TensorProduct.map e.toAlgHom (AlgHom.id ℤ (R(L))) ψ
  have hψA_realization : (ψA : L → ℂ) = (ψ : L → ℂ) := by
    -- Transporting the coefficient ring from `integralClosure ℤ ℂ` to `A` does not change the
    -- realized class function on the associated subgroup.
    simpa [ψA, e] using
      (transport_integralClosure_tensorCharacter_realization
        (A := A) (G := G) (H := L) ψ)
  have hψA_mem : (ψA : L → ℂ) ∈ characterRingScalarExtension A L := by
    -- Every tensor character realizes to a class function in the scalar-extension owner.
    exact (tensorCharacterRingToSubalgebra A L ψA).2
  rcases induced_realization_mem_tensorCharacterRingInductionIdeal_of_le
      (A := A) (G := G) L H hP hψA_mem with ⟨ξ, hξ_mem, hξ_eval⟩
  have hvalue_complex :
      algebraMap A ℂ
          (tensorCharacterRingValueAtConjClass (A := A) (G := G) (ConjClasses.mk x) ξ) =
        (n : ℂ) := by
    -- Evaluate the induced witness at the owner representative `x`, then replace the transported
    -- auxiliary tensor by the original Chapter 10 witness.
    calc
      algebraMap A ℂ
          (tensorCharacterRingValueAtConjClass (A := A) (G := G) (ConjClasses.mk x) ξ) =
          tensorCharacterRingValueAtConjClassComplex (A := A) (G := G) (ConjClasses.mk x) ξ := by
            simpa using
              tensorCharacterRingValueAtConjClass_complex_eq
                (A := A) (G := G) (ConjClasses.mk x) ξ
      _ = (ξ : G → ℂ) x := by
            simpa [tensorCharacterRingToSubalgebra] using
              (tensorCharacterRingValueAtConjClassComplex_eq_of_mk_eq
                (A := A) (G := G) (ConjClasses.mk x) ξ
                (rfl : ConjClasses.mk x = ConjClasses.mk x))
      _ = Ind[L]((ψA : L → ℂ)) x := by
            simpa using congrFun hξ_eval x
      _ = Ind[L]((ψ : L → ℂ)) x := by
            simpa [hψA_realization]
      _ = (n : ℂ) := hnval
  refine ⟨ξ, hξ_mem, ?_⟩
  -- The Chapter 10 auxiliary value at `x` is an integer prime to `p`, so the pullback prime over
  -- `M` cannot contain the induced witness.
  change
    tensorCharacterRingValueAtConjClass (A := A) (G := G) (ConjClasses.mk x) ξ ∉ M.1.asIdeal
  exact
    not_mem_residual_maximal_of_integer_value_not_dvd
      (A := A) (p := p) (M := M) hvalue_complex hndiv

/-- Helper for Proposition 11-11.4-1: any owner representative `x` of the canonical `p`-regular
class of `d` gives the same fixed-class evaluation as the source-chosen representative
`pRegularComponent p (conjClassRepresentative d)`. This isolates the exact class-equality part of
the remaining transport. -/
theorem owner_representative_value_eq_canonical_pregular_component_value
    (p : Nat.Primes) (d : ConjClasses G) {x : G}
    (hx :
      x ∈
        ((Proposition_11_11_4_1.pregular_conj_class_of_conj_class (G := G) p d :
          PRegularConjClass G p) : ConjClasses G).carrier)
    (ξ : A ⊗R(G)) :
    tensorCharacterRingValueAtConjClass (A := A) (G := G) (ConjClasses.mk x) ξ =
      tensorCharacterRingValueAtConjClass (A := A) (G := G)
        (ConjClasses.mk
          (pRegularComponent p
            (Proposition_11_11_4_1.conjClassRepresentative (G := G) d))) ξ := by
  have hmk :
      ConjClasses.mk x =
        ConjClasses.mk
          (pRegularComponent p
            (Proposition_11_11_4_1.conjClassRepresentative (G := G) d)) := by
    -- Both representatives lie in the same canonical owner class of `d`.
    calc
      ConjClasses.mk x =
          (Proposition_11_11_4_1.pregular_conj_class_of_conj_class (G := G) p d :
            ConjClasses G) :=
        ConjClasses.mem_carrier_iff_mk_eq.mp hx
      _ =
          (Proposition_11_11_4_1.pregular_conj_class_of_conj_class (G := G) p
            (ConjClasses.mk
              (Proposition_11_11_4_1.conjClassRepresentative (G := G) d)) :
            ConjClasses G) := by
            rw [Proposition_11_11_4_1.conjClassRepresentative_mk (G := G) d]
      _ =
          ConjClasses.mk
            (pRegularComponent p
              (Proposition_11_11_4_1.conjClassRepresentative (G := G) d)) := by
            rfl
  -- Compare the two `A`-valued evaluations after embedding them into `ℂ`, where the class-equality
  -- rewrite can be applied directly to the realized tensor character.
  apply IsIntegralClosure.algebraMap_injective A ℤ ℂ
  rw [tensorCharacterRingValueAtConjClass_complex_eq (A := A) (G := G) (ConjClasses.mk x) ξ]
  rw [tensorCharacterRingValueAtConjClass_complex_eq (A := A) (G := G)
    (ConjClasses.mk
      (pRegularComponent p
        (Proposition_11_11_4_1.conjClassRepresentative (G := G) d))) ξ]
  rw [tensorCharacterRingValueAtConjClassComplex_eq_of_mk_eq (A := A) (G := G)
    (ConjClasses.mk x) ξ rfl]
  rw [tensorCharacterRingValueAtConjClassComplex_eq_of_mk_eq (A := A) (G := G)
    (ConjClasses.mk
      (pRegularComponent p
        (Proposition_11_11_4_1.conjClassRepresentative (G := G) d))) ξ hmk]

/-- Helper for Proposition 11-11.4-1: modulo the residual ideal `M`, membership of the fixed-class
value at the canonical `p`-regular component is equivalent to membership of the value at any owner
representative `x` of that component. This isolates the owner-side transport from the still-missing
Chapter `10` comparison between `d` and its canonical `p`-regular component. -/
theorem canonical_pregular_component_value_mem_residual_iff_owner_representative
    (p : Nat.Primes) (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (d : ConjClasses G) {x : G}
    (hx :
      x ∈
        ((Proposition_11_11_4_1.pregular_conj_class_of_conj_class (G := G) p d :
          PRegularConjClass G p) : ConjClasses G).carrier)
    (ξ : A ⊗R(G)) :
    tensorCharacterRingValueAtConjClass (A := A) (G := G)
        (ConjClasses.mk
          (pRegularComponent p
            (Proposition_11_11_4_1.conjClassRepresentative (G := G) d))) ξ ∈
      M.1.asIdeal ↔
        tensorCharacterRingValueAtConjClass (A := A) (G := G) (ConjClasses.mk x) ξ ∈
          M.1.asIdeal := by
  -- The two fixed-class evaluations already agree in `A`, so ideal membership is identical.
  rw [← owner_representative_value_eq_canonical_pregular_component_value
    (A := A) (G := G) p d hx ξ]

-- The remaining cyclic quotient comparison lemmas elaborate large transport terms through
-- `tensorCharacterRingValueAtConjClass`; raise heartbeats locally for this final block.
set_option maxHeartbeats 800000

/-- Helper for Proposition 11-11.4-1: if a tensor character has chosen integer values at `x` and
at `pRegularComponent p x`, then the corresponding fixed-class evaluations are equal modulo the
residual ideal `M`. This isolates exactly the Chapter `10.10.3.2` cyclic-descent input that is
already available without the broken recall shim. -/
theorem residual_valueAtConjClass_eq_pregular_component_of_integer_endpoint_values
    (p : Nat.Primes) (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (ξ : A ⊗R(G)) (x : G) {m n : ℤ}
    (hm : (ξ : G → ℂ) x = (m : ℂ))
    (hn : (ξ : G → ℂ) (pRegularComponent p x) = (n : ℂ)) :
    Ideal.Quotient.mk M.1.asIdeal
        (tensorCharacterRingValueAtConjClass (A := A) (G := G) (ConjClasses.mk x) ξ) =
    Ideal.Quotient.mk M.1.asIdeal
        (tensorCharacterRingValueAtConjClass (A := A) (G := G)
          (ConjClasses.mk (pRegularComponent p x)) ξ) := by
  letI : Fact ((p : ℕ).Prime) := ⟨p.2⟩
  obtain ⟨k, hkpow⟩ := exists_p_power_eq_pRegularComponent_pow (p := (p : ℕ)) x
  have hmod :
      m ≡ n [ZMOD (p : ℕ)] := by
    -- The cyclic-subgroup Frobenius step already compares the two chosen endpoint values modulo
    -- the principal ideal `(p)`, and the arithmetic descent turns that quotient equality into a
    -- congruence modulo `p`.
    have hqpow :
        Ideal.Quotient.mk (Ideal.span ({((p : ℕ) : A)} : Set A)) ((m : A) ^ ((p : ℕ) ^ k)) =
          Ideal.Quotient.mk (Ideal.span ({((p : ℕ) : A)} : Set A)) ((n : A) ^ ((p : ℕ) ^ k)) := by
      let H : Subgroup G := Subgroup.zpowers x
      let xH : H := ⟨x, Subgroup.mem_zpowers x⟩
      let xrH : H :=
        ⟨pRegularComponent p x,
          (p_component_decomposition_exists (p := (p : ℕ)) x
            (isOfFinOrder_of_finite x)).right_mem_zpowers⟩
      have hxpowH : xH ^ ((p : ℕ) ^ k) = xrH ^ ((p : ℕ) ^ k) := by
        apply Subtype.ext
        simpa [xH, xrH] using hkpow
      let f : H → ℂ := ((H.tensorCharacterRingRestriction ξ : A ⊗R(H)) : H → ℂ)
      have hf : f ∈ characterRingScalarExtension A H := by
        exact tensorCharacterRing_mem_characterRingScalarExtension
          (H.tensorCharacterRingRestriction ξ)
      have hfx : f xH = (m : ℂ) := by
        calc
          f xH = (ξ : G → ℂ) x := by
            change ((H.tensorCharacterRingRestriction ξ : A ⊗R(H)) : H → ℂ) xH =
              (ξ : G → ℂ) x
            rw [Subgroup.tensorCharacterRingRestriction_apply (A := A)]
          _ = (m : ℂ) := hm
      have hfxr : f xrH = (n : ℂ) := by
        calc
          f xrH = (ξ : G → ℂ) (pRegularComponent p x) := by
            change ((H.tensorCharacterRingRestriction ξ : A ⊗R(H)) : H → ℂ) xrH =
              (ξ : G → ℂ) (pRegularComponent p x)
            rw [Subgroup.tensorCharacterRingRestriction_apply (A := A)]
          _ = (n : ℂ) := hn
      obtain ⟨ay, az, hay, haz, hq⟩ :=
        tensor_character_qpow_quotient_eq_of_mem_characterRingScalarExtension
          (A := A) (p := (p : ℕ)) (f := f) hf (y := xH) (z := xrH) (k := k) hxpowH
      have haym : ay = (m : A) := by
        apply IsIntegralClosure.algebraMap_injective A ℤ ℂ
        calc
          algebraMap A ℂ ay = f xH := hay
          _ = (m : ℂ) := hfx
          _ = algebraMap A ℂ (m : A) := by simp
      have hazn : az = (n : A) := by
        apply IsIntegralClosure.algebraMap_injective A ℤ ℂ
        calc
          algebraMap A ℂ az = f xrH := haz
          _ = (n : ℂ) := hfxr
          _ = algebraMap A ℂ (n : A) := by simp
      simpa [haym, hazn] using hq
    simpa using
      int_modEq_of_qpow_quotient_eq_mod_p
        (A := A) (p := (p : ℕ)) m n k hqpow
  have hdiv : ((p : ℕ) : ℤ) ∣ (m - n) := by
    have hdiv' : ((p : ℕ) : ℤ) ∣ (n - m) :=
      (Int.modEq_iff_dvd).mp hmod
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using Int.dvd_neg.mpr hdiv'
  have hvalue_x :
      algebraMap A ℂ
          (tensorCharacterRingValueAtConjClass (A := A) (G := G) (ConjClasses.mk x) ξ) =
        (m : ℂ) := by
    calc
      algebraMap A ℂ
          (tensorCharacterRingValueAtConjClass (A := A) (G := G) (ConjClasses.mk x) ξ) =
        tensorCharacterRingValueAtConjClassComplex (A := A) (G := G) (ConjClasses.mk x) ξ := by
          exact
            tensorCharacterRingValueAtConjClass_complex_eq
              (A := A) (G := G) (ConjClasses.mk x) ξ
      _ = (ξ : G → ℂ) x := by
          simpa using
            (tensorCharacterRingValueAtConjClassComplex_eq_of_mk_eq
              (A := A) (G := G) (ConjClasses.mk x) ξ rfl)
      _ = (m : ℂ) := hm
  have hvalue_xr :
      algebraMap A ℂ
          (tensorCharacterRingValueAtConjClass (A := A) (G := G)
            (ConjClasses.mk (pRegularComponent p x)) ξ) =
        (n : ℂ) := by
    calc
      algebraMap A ℂ
          (tensorCharacterRingValueAtConjClass (A := A) (G := G)
            (ConjClasses.mk (pRegularComponent p x)) ξ) =
        tensorCharacterRingValueAtConjClassComplex (A := A) (G := G)
          (ConjClasses.mk (pRegularComponent p x)) ξ := by
          exact
            tensorCharacterRingValueAtConjClass_complex_eq
              (A := A) (G := G) (ConjClasses.mk (pRegularComponent p x)) ξ
      _ = (ξ : G → ℂ) (pRegularComponent p x) := by
          simpa using
            (tensorCharacterRingValueAtConjClassComplex_eq_of_mk_eq
              (A := A) (G := G) (ConjClasses.mk (pRegularComponent p x)) ξ rfl)
      _ = (n : ℂ) := hn
  refine Ideal.Quotient.eq.mpr ?_
  -- Compare the two fixed-class evaluations through their complex realizations, then package the
  -- resulting integer difference as an element of the residual maximal ideal.
  refine mem_residual_maximal_of_integer_value_dvd (A := A) (p := p) (M := M)
    (a := tensorCharacterRingValueAtConjClass (A := A) (G := G) (ConjClasses.mk x) ξ -
      tensorCharacterRingValueAtConjClass (A := A) (G := G)
        (ConjClasses.mk (pRegularComponent p x)) ξ)
    (n := m - n) ?_ hdiv
  calc
    algebraMap A ℂ
        (tensorCharacterRingValueAtConjClass (A := A) (G := G) (ConjClasses.mk x) ξ -
          tensorCharacterRingValueAtConjClass (A := A) (G := G)
            (ConjClasses.mk (pRegularComponent p x)) ξ) =
      algebraMap A ℂ
          (tensorCharacterRingValueAtConjClass (A := A) (G := G) (ConjClasses.mk x) ξ) -
        algebraMap A ℂ
          (tensorCharacterRingValueAtConjClass (A := A) (G := G)
            (ConjClasses.mk (pRegularComponent p x)) ξ) := by
          simp
    _ = (m : ℂ) - (n : ℂ) := by
          rw [hvalue_x, hvalue_xr]
    _ = ((m - n : ℤ) : ℂ) := by
          simp

/-- Helper for Proposition 11-11.4-1: the previous congruence can be read directly as an ideal
membership statement for the difference of the two fixed-class evaluations. -/
theorem valueAtConjClass_sub_mem_residual_of_integer_endpoint_values
    (p : Nat.Primes) (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (ξ : A ⊗R(G)) (x : G) {m n : ℤ}
    (hm : (ξ : G → ℂ) x = (m : ℂ))
    (hn : (ξ : G → ℂ) (pRegularComponent p x) = (n : ℂ)) :
    tensorCharacterRingValueAtConjClass (A := A) (G := G) (ConjClasses.mk x) ξ -
        tensorCharacterRingValueAtConjClass (A := A) (G := G)
          (ConjClasses.mk (pRegularComponent p x)) ξ ∈
      M.1.asIdeal := by
  -- Re-express the quotient equality as membership of the difference in the defining ideal.
  exact Ideal.Quotient.eq.mp <|
    residual_valueAtConjClass_eq_pregular_component_of_integer_endpoint_values
      (A := A) (G := G) p M ξ x hm hn

/-- Helper for Proposition 11-11.4-1: for any tensor character, the fixed-class evaluations at an
element `x` and at its canonical `p`-regular component become equal in the residue field of `M`.
This is the source-faithful Chapter `10` congruence specialized to the only quotient used in the
regular branch. -/
theorem residual_valueAtConjClass_eq_pregular_component
    (p : Nat.Primes) (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (x : G) (ξ : A ⊗R(G)) :
    Ideal.Quotient.mk M.1.asIdeal
        (tensorCharacterRingValueAtConjClass (A := A) (G := G) (ConjClasses.mk x) ξ) =
      Ideal.Quotient.mk M.1.asIdeal
        (tensorCharacterRingValueAtConjClass (A := A) (G := G)
          (ConjClasses.mk (pRegularComponent p x)) ξ) := by
  letI : Fact ((p : ℕ).Prime) := ⟨p.2⟩
  let a :=
    tensorCharacterRingValueAtConjClass (A := A) (G := G) (ConjClasses.mk x) ξ
  let b :=
    tensorCharacterRingValueAtConjClass (A := A) (G := G)
      (ConjClasses.mk (pRegularComponent p x)) ξ
  let H : Subgroup G := Subgroup.zpowers x
  let xH : H := ⟨x, Subgroup.mem_zpowers x⟩
  let xrH : H :=
    ⟨pRegularComponent p x,
      (p_component_decomposition_exists (p := (p : ℕ)) x
        (isOfFinOrder_of_finite x)).right_mem_zpowers⟩
  obtain ⟨k, hkpow⟩ := exists_p_power_eq_pRegularComponent_pow (p := (p : ℕ)) x
  have hxpowH : xH ^ ((p : ℕ) ^ k) = xrH ^ ((p : ℕ) ^ k) := by
    -- The same `p^k`-power coincidence holds inside the cyclic subgroup `⟨x⟩`.
    apply Subtype.ext
    simpa [xH, xrH] using hkpow
  let f : H → ℂ := ((H.tensorCharacterRingRestriction ξ : A ⊗R(H)) : H → ℂ)
  have hf : f ∈ characterRingScalarExtension A H := by
    -- Restricting a tensor character to `⟨x⟩` stays inside the scalar-extended character ring.
    exact
      tensorCharacterRing_mem_characterRingScalarExtension
        (H.tensorCharacterRingRestriction ξ)
  obtain ⟨ay, az, hay, haz, hqpow⟩ :=
    tensor_character_qpow_quotient_eq_of_mem_characterRingScalarExtension
      (A := A) (p := (p : ℕ)) (f := f) hf (y := xH) (z := xrH) (k := k) hxpowH
  have hfx :
      f xH = (ξ : G → ℂ) x := by
    -- Restriction to `⟨x⟩` does not change the value at the chosen generator.
    change ((H.tensorCharacterRingRestriction ξ : A ⊗R(H)) : H → ℂ) xH = (ξ : G → ℂ) x
    rw [Subgroup.tensorCharacterRingRestriction_apply (A := A)]
  have hfxr :
      f xrH = (ξ : G → ℂ) (pRegularComponent p x) := by
    -- The same restriction identity holds at the canonical `p`-regular component.
    change ((H.tensorCharacterRingRestriction ξ : A ⊗R(H)) : H → ℂ) xrH =
      (ξ : G → ℂ) (pRegularComponent p x)
    rw [Subgroup.tensorCharacterRingRestriction_apply (A := A)]
  have ha :
      algebraMap A ℂ a = (ξ : G → ℂ) x := by
    -- Rewrite the fixed-class evaluator back to the underlying realized tensor character.
    calc
      algebraMap A ℂ a =
          tensorCharacterRingValueAtConjClassComplex (A := A) (G := G)
            (ConjClasses.mk x) ξ := by
              exact
                tensorCharacterRingValueAtConjClass_complex_eq (A := A) (G := G)
                  (ConjClasses.mk x) ξ
      _ = (ξ : G → ℂ) x := by
            simpa using
              (tensorCharacterRingValueAtConjClassComplex_eq_of_mk_eq
                (A := A) (G := G) (ConjClasses.mk x) ξ rfl)
  have hb :
      algebraMap A ℂ b = (ξ : G → ℂ) (pRegularComponent p x) := by
    -- The second fixed-class evaluator is handled by the same representative computation.
    calc
      algebraMap A ℂ b =
          tensorCharacterRingValueAtConjClassComplex (A := A) (G := G)
            (ConjClasses.mk (pRegularComponent p x)) ξ := by
              exact
                tensorCharacterRingValueAtConjClass_complex_eq (A := A) (G := G)
                  (ConjClasses.mk (pRegularComponent p x)) ξ
      _ = (ξ : G → ℂ) (pRegularComponent p x) := by
            simpa using
              (tensorCharacterRingValueAtConjClassComplex_eq_of_mk_eq
                (A := A) (G := G) (ConjClasses.mk (pRegularComponent p x)) ξ rfl)
  have hay_eq : ay = a := by
    -- The cyclic-step lift at `x` coincides with the canonical `A`-valued fixed-class evaluation.
    apply IsIntegralClosure.algebraMap_injective A ℤ ℂ
    calc
      algebraMap A ℂ ay = f xH := hay
      _ = (ξ : G → ℂ) x := hfx
      _ = algebraMap A ℂ a := ha.symm
  have haz_eq : az = b := by
    -- The same comparison identifies the lift at `pRegularComponent p x`.
    apply IsIntegralClosure.algebraMap_injective A ℤ ℂ
    calc
      algebraMap A ℂ az = f xrH := haz
      _ = (ξ : G → ℂ) (pRegularComponent p x) := hfxr
      _ = algebraMap A ℂ b := hb.symm
  have hp0 :
      (p : A ⧸ M.1.asIdeal) = 0 := by
    -- The quotient by `M` has characteristic `p`.
    letI : CharP M.1.asIdeal.ResidueField p := M.2.2
    letI : CharP (A ⧸ M.1.asIdeal) p :=
      RingHom.charP
        (algebraMap (A ⧸ M.1.asIdeal) M.1.asIdeal.ResidueField)
        M.1.asIdeal.injective_algebraMap_quotient_residueField p
    exact CharP.cast_eq_zero (R := A ⧸ M.1.asIdeal) p
  have hp_mem : ((p : ℕ) : A) ∈ M.1.asIdeal := by
    -- Thus the principal ideal `(p)` maps into the residual maximal ideal `M`.
    exact Ideal.Quotient.eq_zero_iff_mem.mp (by simpa using hp0)
  have hspan_le :
      Ideal.span ({((p : ℕ) : A)} : Set A) ≤ M.1.asIdeal := by
    -- This is the exact quotient-factorization needed to descend the cyclic congruence to `A / M`.
    rw [Ideal.span_singleton_le_iff_mem]
    simpa using hp_mem
  have hqpowM :
      (Ideal.Quotient.mk M.1.asIdeal a) ^ ((p : ℕ) ^ k) =
        (Ideal.Quotient.mk M.1.asIdeal b) ^ ((p : ℕ) ^ k) := by
    -- Factor the Chapter `10` equality from `A / (p)` down to `A / M`.
    simpa [a, b, hay_eq, haz_eq] using
      congrArg (Ideal.Quotient.factor hspan_le) hqpow
  letI : CharP M.1.asIdeal.ResidueField p := M.2.2
  letI : CharP (A ⧸ M.1.asIdeal) p :=
    RingHom.charP
      (algebraMap (A ⧸ M.1.asIdeal) M.1.asIdeal.ResidueField)
      M.1.asIdeal.injective_algebraMap_quotient_residueField p
  -- Route correction: instead of importing the stale Chapter `10` recall shim, descend the cyclic
  -- `p^k`-power congruence to `A / M` and cancel Frobenius there by injectivity.
  exact ((frobenius_inj (A ⧸ M.1.asIdeal) p).iterate k) <| by
    simpa [iterate_frobenius] using hqpowM

/-- Helper for Proposition 11-11.4-1: the fixed-class evaluation at `d` differs from the
evaluation at the canonical `p`-regular component of `conjClassRepresentative d` by an element of
the residual ideal `M`. This is the exact Chapter `10` congruence step missing from the current
dependency-closed imports. -/
theorem residual_valueAtConjClass_eq_canonical_pregular_component
    (p : Nat.Primes) (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (d : ConjClasses G) (ξ : A ⊗R(G)) :
    Ideal.Quotient.mk M.1.asIdeal
        (tensorCharacterRingValueAtConjClass (A := A) (G := G) d ξ) =
    Ideal.Quotient.mk M.1.asIdeal
        (tensorCharacterRingValueAtConjClass (A := A) (G := G)
          (ConjClasses.mk
            (pRegularComponent p
              (Proposition_11_11_4_1.conjClassRepresentative (G := G) d))) ξ) := by
  -- Apply the representative-level residue congruence to the source-chosen representative of `d`.
  simpa [Proposition_11_11_4_1.conjClassRepresentative_mk (G := G) d] using
    residual_valueAtConjClass_eq_pregular_component
      (A := A) (G := G) p M
      (Proposition_11_11_4_1.conjClassRepresentative (G := G) d) ξ

/-- Helper for Proposition 11-11.4-1: the fixed-class evaluation at `d` differs from the
evaluation at the canonical `p`-regular component of `conjClassRepresentative d` by an element of
the residual ideal `M`. This is now a direct corollary of the quotient-level source congruence. -/
theorem value_at_conj_class_sub_mem_residual_of_canonical_pregular_component
    (p : Nat.Primes) (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (d : ConjClasses G) (ξ : A ⊗R(G)) :
    tensorCharacterRingValueAtConjClass (A := A) (G := G) d ξ -
        tensorCharacterRingValueAtConjClass (A := A) (G := G)
          (ConjClasses.mk
            (pRegularComponent p
              (Proposition_11_11_4_1.conjClassRepresentative (G := G) d))) ξ ∈
      M.1.asIdeal := by
  -- Pass to the quotient `A / M`, where the missing Chapter `10` step is exactly an equality.
  refine Ideal.Quotient.eq_zero_iff_mem.mp ?_
  calc
    Ideal.Quotient.mk M.1.asIdeal
        (tensorCharacterRingValueAtConjClass (A := A) (G := G) d ξ -
          tensorCharacterRingValueAtConjClass (A := A) (G := G)
            (ConjClasses.mk
              (pRegularComponent p
                (Proposition_11_11_4_1.conjClassRepresentative (G := G) d))) ξ) =
      Ideal.Quotient.mk M.1.asIdeal
        (tensorCharacterRingValueAtConjClass (A := A) (G := G) d ξ) -
        Ideal.Quotient.mk M.1.asIdeal
          (tensorCharacterRingValueAtConjClass (A := A) (G := G)
            (ConjClasses.mk
              (pRegularComponent p
                (Proposition_11_11_4_1.conjClassRepresentative (G := G) d))) ξ) := by
          simp
    _ = 0 := by
          rw [residual_valueAtConjClass_eq_canonical_pregular_component
            (A := A) (G := G) p M d ξ]
          simp

/-- Helper for Proposition 11-11.4-1: if `x` lies in the owner carrier of `d`, then the fixed
class evaluations at `d` and at `ConjClasses.mk x` differ by an element of the residual ideal
`M`. This is the exact bridge needed in the final contradiction argument. -/
theorem value_at_conj_class_sub_mem_residual_of_mem_owner_carrier
    (p : Nat.Primes) (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (d : ConjClasses G) {x : G}
    (hx :
      x ∈
        ((Proposition_11_11_4_1.pregular_conj_class_of_conj_class (G := G) p d :
          PRegularConjClass G p) : ConjClasses G).carrier)
    (ξ : A ⊗R(G)) :
    tensorCharacterRingValueAtConjClass (A := A) (G := G) d ξ -
        tensorCharacterRingValueAtConjClass (A := A) (G := G) (ConjClasses.mk x) ξ ∈
      M.1.asIdeal := by
  -- Rewrite the owner representative to the canonical `p`-regular representative, so only the
  -- Chapter `10` congruence for `d` remains.
  rw [owner_representative_value_eq_canonical_pregular_component_value
    (A := A) (G := G) p d hx ξ]
  exact
    value_at_conj_class_sub_mem_residual_of_canonical_pregular_component
      (A := A) (G := G) p M d ξ

-- TODO: start from the Chapter `10.10.3.3` auxiliary tensor on the associated subgroup
-- `associatedPElementarySubgroup p x P`, transport it from `integralClosure ℤ ℂ` to `A` using
-- `transport_integralClosure_tensorCharacter_realization`, and then use induction in stages to
-- place the resulting ambient tensor inside `I_H`.
-- Route correction: the subgroup-of-`H` transport is now isolated in
-- `induced_realization_mem_tensorCharacterRingInductionIdeal_of_le`, and the owner-side witness is
-- now packaged by `associated_owner_induction_witness_not_mem_owner_value_comap`. The remaining
-- blocker is the Chapter `10` congruence from the ordinary class `d` to its canonical `p`-regular
-- component modulo `M`.
theorem associated_owner_induction_witness_not_mem_value_comap
    (p : Nat.Primes) (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (d : ConjClasses G) (H : Subgroup G)
    (hAssoc :
      HasAssociatedPElementarySubgroupInClass
        (Proposition_11_11_4_1.pregular_conj_class_of_conj_class p d) H) :
    ∃ ξ : A ⊗R(G), ξ ∈ tensorCharacterRingInductionIdeal (A := A) H ∧
      ξ ∉ (PrimeSpectrum.comap (tensorCharacterRingValueAtConjClass (A := A) (G := G) d)
        (⟨M.1.asIdeal, inferInstance⟩ : PrimeSpectrum A)).asIdeal := by
  rcases hAssoc with ⟨x, hx, P, hP⟩
  rcases associated_owner_induction_witness_not_mem_owner_value_comap
      (A := A) (G := G) (p := p) (M := M) (d := d) (H := H) hx P hP with
    ⟨ξ, hξ_mem, hξ_notmem⟩
  refine ⟨ξ, hξ_mem, ?_⟩
  change tensorCharacterRingValueAtConjClass (A := A) (G := G) d ξ ∉ M.1.asIdeal
  change tensorCharacterRingValueAtConjClass (A := A) (G := G) (ConjClasses.mk x) ξ ∉
      M.1.asIdeal at hξ_notmem
  intro hξd
  have hquot_d :
      Ideal.Quotient.mk M.1.asIdeal
          (tensorCharacterRingValueAtConjClass (A := A) (G := G) d ξ) = 0 := by
    -- The assumed membership at `d` is exactly quotient-zero in `A / M`.
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hξd
  have hcanon :
      tensorCharacterRingValueAtConjClass (A := A) (G := G)
          (ConjClasses.mk
            (pRegularComponent p
              (Proposition_11_11_4_1.conjClassRepresentative (G := G) d))) ξ ∈
        M.1.asIdeal := by
    -- The missing Chapter `10` congruence identifies the quotient values at `d` and at the
    -- canonical `p`-regular component.
    have hquot_canonical :
        Ideal.Quotient.mk M.1.asIdeal
            (tensorCharacterRingValueAtConjClass (A := A) (G := G)
              (ConjClasses.mk
                (pRegularComponent p
                  (Proposition_11_11_4_1.conjClassRepresentative (G := G) d))) ξ) = 0 := by
      calc
        Ideal.Quotient.mk M.1.asIdeal
            (tensorCharacterRingValueAtConjClass (A := A) (G := G)
              (ConjClasses.mk
                (pRegularComponent p
                  (Proposition_11_11_4_1.conjClassRepresentative (G := G) d))) ξ) =
          Ideal.Quotient.mk M.1.asIdeal
            (tensorCharacterRingValueAtConjClass (A := A) (G := G) d ξ) := by
              symm
              exact residual_valueAtConjClass_eq_canonical_pregular_component
                (A := A) (G := G) p M d ξ
        _ = 0 := hquot_d
    exact Ideal.Quotient.eq_zero_iff_mem.mp hquot_canonical
  have hξx :
      tensorCharacterRingValueAtConjClass (A := A) (G := G) (ConjClasses.mk x) ξ ∈ M.1.asIdeal := by
    -- The owner representative lies in the same canonical `p`-regular class, so the already
    -- settled owner-side transport converts canonical membership into owner membership.
    exact
      (canonical_pregular_component_value_mem_residual_iff_owner_representative
        (A := A) (G := G) p M d hx ξ).mp hcanon
  exact hξ_notmem hξx

/-- Helper for Proposition 11-11.4-1: the fixed-class evaluation pullback over `M` already
satisfies Serre's intrinsic regular-prime criterion for the canonical `p`-regular owner of `d`. -/
theorem value_comap_isTensorCharacterRingRegularPrime
    (p : Nat.Primes) (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (d : ConjClasses G) :
    IsTensorCharacterRingRegularPrime (A := A) (G := G) p M
      (Proposition_11_11_4_1.pregular_conj_class_of_conj_class p d)
      (PrimeSpectrum.comap (tensorCharacterRingValueAtConjClass (A := A) (G := G) d)
        (⟨M.1.asIdeal, inferInstance⟩ : PrimeSpectrum A)) := by
  constructor
  · -- The evaluation pullback contracts to the chosen maximal ideal because fixed-class
    -- evaluation fixes scalar tensors.
    exact value_comap_eq_fixed_maximal (A := A) (G := G) p M d
  · intro H
    constructor
    · intro hcontain hAssoc
      -- An associated owner subgroup forces an explicit element of `I_H` to survive modulo `M`,
      -- so `I_H` cannot be contained in the pullback prime.
      rcases associated_owner_induction_witness_not_mem_value_comap
          (A := A) (G := G) p M d H hAssoc with ⟨ξ, hξ_mem, hξ_notmem⟩
      exact hξ_notmem (hcontain hξ_mem)
    · intro hNotAssoc
      -- The forward containment direction is exactly the Chapter `11.3` divisibility argument
      -- already packaged at the canonical owner representative.
      let ccanon : ConjClasses G :=
        ConjClasses.mk
          (pRegularComponent p
            (Proposition_11_11_4_1.conjClassRepresentative (G := G) d))
      have hcanonical :
          tensorCharacterRingInductionIdeal (A := A) (G := G) H ≤
            (PrimeSpectrum.comap
              (tensorCharacterRingValueAtConjClass (A := A) (G := G) ccanon)
              (⟨M.1.asIdeal, inferInstance⟩ : PrimeSpectrum A)).asIdeal :=
        tensorCharacterRingInductionIdeal_le_value_comap_of_not_hasAssociated_owner_canonical_representative
          (A := A) (G := G) p M d H hNotAssoc
      intro ξ hξ
      change tensorCharacterRingValueAtConjClass (A := A) (G := G) d ξ ∈ M.1.asIdeal
      have hcanonical_mem :
          tensorCharacterRingValueAtConjClass (A := A) (G := G) ccanon ξ ∈ M.1.asIdeal :=
        by
          change tensorCharacterRingValueAtConjClass (A := A) (G := G) ccanon ξ ∈ M.1.asIdeal
          exact hcanonical hξ
      have hdiff :
          tensorCharacterRingValueAtConjClass (A := A) (G := G) d ξ -
              tensorCharacterRingValueAtConjClass (A := A) (G := G) ccanon ξ ∈
            M.1.asIdeal :=
        value_at_conj_class_sub_mem_residual_of_canonical_pregular_component
          (A := A) (G := G) p M d ξ
      rw [show tensorCharacterRingValueAtConjClass (A := A) (G := G) d ξ =
          (tensorCharacterRingValueAtConjClass (A := A) (G := G) d ξ -
              tensorCharacterRingValueAtConjClass (A := A) (G := G) ccanon ξ) +
            tensorCharacterRingValueAtConjClass (A := A) (G := G) ccanon ξ by
            exact (sub_add_cancel _ _).symm]
      exact M.1.asIdeal.add_mem hdiff hcanonical_mem

/-- Helper for Proposition 11-11.4-1: the regular-branch prime indexed by a `p`-regular owner
class `c` and a residual-characteristic maximal ideal `M` is the pullback of `M` along fixed-class
evaluation on the underlying ordinary conjugacy class of `c`. -/
def tensorCharacterRingRegularPrime
    (p : Nat.Primes) (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (c : PRegularConjClass G p) : SpecARG :=
  PrimeSpectrum.comap
    (tensorCharacterRingValueAtConjClass (A := A) (G := G) (c : ConjClasses G))
    (⟨M.1.asIdeal, inferInstance⟩ : PrimeSpectrum A)

/-- Helper for Proposition 11-11.4-1: the remaining nonzero source branch should identify the
fixed-class evaluation pullback over `M` with Serre's canonical regular prime indexed by the
owner `p`-regular class of `d`. -/
theorem value_comap_eq_tensorCharacterRingRegularPrime
    (p : Nat.Primes) (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (d : ConjClasses G) :
    PrimeSpectrum.comap (tensorCharacterRingValueAtConjClass (A := A) (G := G) d)
      (⟨M.1.asIdeal, inferInstance⟩ : PrimeSpectrum A) =
        tensorCharacterRingRegularPrime (A := A) (G := G) p M
          (Proposition_11_11_4_1.pregular_conj_class_of_conj_class p d) := by
  let c : PRegularConjClass G p :=
    Proposition_11_11_4_1.pregular_conj_class_of_conj_class p d
  let x : G := Proposition_11_11_4_1.conjClassRepresentative (G := G) (c : ConjClasses G)
  have hx : x ∈ (c : ConjClasses G).carrier := by
    exact ConjClasses.mem_carrier_iff_mk_eq.mpr
      (Proposition_11_11_4_1.conjClassRepresentative_mk (G := G) (c : ConjClasses G))
  apply PrimeSpectrum.ext
  ext ξ
  change tensorCharacterRingValueAtConjClass (A := A) (G := G) d ξ ∈ M.1.asIdeal ↔
    tensorCharacterRingValueAtConjClass (A := A) (G := G) (c : ConjClasses G) ξ ∈ M.1.asIdeal
  have hsub :
      tensorCharacterRingValueAtConjClass (A := A) (G := G) d ξ -
          tensorCharacterRingValueAtConjClass (A := A) (G := G) (ConjClasses.mk x) ξ ∈
        M.1.asIdeal :=
    value_at_conj_class_sub_mem_residual_of_mem_owner_carrier
      (A := A) (G := G) p M d
      (by simpa [c, x] using hx) ξ
  have hquot :
      Ideal.Quotient.mk M.1.asIdeal
          (tensorCharacterRingValueAtConjClass (A := A) (G := G) d ξ) =
        Ideal.Quotient.mk M.1.asIdeal
          (tensorCharacterRingValueAtConjClass (A := A) (G := G) (ConjClasses.mk x) ξ) :=
    Ideal.Quotient.eq.mpr hsub
  rw [Proposition_11_11_4_1.conjClassRepresentative_mk (G := G) (c : ConjClasses G)] at hquot
  constructor
  · intro hmem
    have hzero :
        Ideal.Quotient.mk M.1.asIdeal
            (tensorCharacterRingValueAtConjClass (A := A) (G := G) d ξ) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hmem
    have hzero' :
        Ideal.Quotient.mk M.1.asIdeal
            (tensorCharacterRingValueAtConjClass (A := A) (G := G) (c : ConjClasses G) ξ) = 0 := by
      rw [← hquot]
      exact hzero
    exact Ideal.Quotient.eq_zero_iff_mem.mp hzero'
  · intro hmem
    have hzero :
        Ideal.Quotient.mk M.1.asIdeal
            (tensorCharacterRingValueAtConjClass (A := A) (G := G) (c : ConjClasses G) ξ) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hmem
    have hzero' :
        Ideal.Quotient.mk M.1.asIdeal
            (tensorCharacterRingValueAtConjClass (A := A) (G := G) d ξ) = 0 := by
      rw [hquot]
      exact hzero
    exact Ideal.Quotient.eq_zero_iff_mem.mp hzero'

/-- Proposition 11-11.4-1: if with each ordinary conjugacy class `c` we associate `P₀,c`, and
with each `p`-regular class `c` and residual-characteristic maximal ideal `M` we associate
`P_{M,c}`, then every prime ideal of `A ⊗ R(G)` occurs exactly once in one of these two
families. -/
theorem tensor_character_ring_prime_ideal_classification
    (𝔭 : SpecARG) :
    (∃ c : ConjClasses G, tensorCharacterRingZeroPrimeIdeal A c = 𝔭) ∨
      ∃ p : Nat.Primes, ∃ M : NonzeroResidualCharacteristicMaximalIdeal A p,
        ∃ c : PRegularConjClass G p,
          tensorCharacterRingRegularPrime (A := A) (G := G) p M c = 𝔭 := by
  -- Start from the verified source-spectrum presentation and only rewrite the nonzero branch
  -- through the canonical regular-owner parameter.
  rcases tensor_character_ring_prime_ideal_source_presentation (A := A) (G := G) 𝔭 with h𝔭 | h𝔭
  · exact Or.inl h𝔭
  · rcases h𝔭 with ⟨p, M, d, hd⟩
    refine Or.inr ⟨p, M,
      Proposition_11_11_4_1.pregular_conj_class_of_conj_class p d, ?_⟩
    -- The remaining rewrite is exactly the regular-branch owner identification above.
    calc
      tensorCharacterRingRegularPrime (A := A) (G := G) p M
          (Proposition_11_11_4_1.pregular_conj_class_of_conj_class p d) =
          PrimeSpectrum.comap (tensorCharacterRingValueAtConjClass (A := A) (G := G) d)
            (⟨M.1.asIdeal, inferInstance⟩ : PrimeSpectrum A) := by
              symm
              exact value_comap_eq_tensorCharacterRingRegularPrime (A := A) (G := G) p M d
      _ = 𝔭 := hd

/-- Helper for Proposition 11-11.4-1: any prime of `A ⊗ R(G)` whose contraction to `A` is `(0)` is
canonically recovered from the corresponding point of the bottom fiber. This remains a thin
compatibility wrapper around the extracted owner API while the full Proposition 30 classification
is reconstructed on top of it. -/
theorem tensor_character_ring_prime_over_bot_to_fiber_symm
    {𝔭 : SpecARG}
    (h𝔭 : Ideal.comap (algebraMap A (A ⊗R(G))) 𝔭.asIdeal = ⊥) :
    ((PrimeSpectrum.primesOverOrderIsoFiber A (A ⊗R(G)) (⊥ : Ideal A)).symm
      (prime_over_bot_to_fiber (A := A) 𝔭 h𝔭)).1 =
        𝔭.asIdeal := by
  -- This is the standard bottom-fiber normalization already verified in the extracted owner API.
  simpa using prime_over_bot_to_fiber_symm (A := A) (G := G) 𝔭 h𝔭

end
