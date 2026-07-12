import LinearRepresentations_Serre_1977.Chap11.Proposition_11_11_4_1.OwnersAndPrimeFibers
import LinearRepresentations_Serre_1977.Chap09.Theorem_9_9_2_1
import LinearRepresentations_Serre_1977.Chap11.Theorem_11_11_2_2

-- Stable conjugacy-class function-ring realization helpers extracted from Proposition 11-11.4-1.

universe u v

noncomputable section

open Representation
open scoped Representation SubgroupInduction TensorProduct

section

variable {G : Type} [Group G]
variable {A : Type v} [CommRing A]
variable [Finite G] [Algebra A ℂ]

local instance conjClassFunctionRealizationFintypeGroup : Fintype G := Fintype.ofFinite G
local instance conjClassFunctionRealizationFintypeSubgroup (H : Subgroup G) : Fintype H :=
  Fintype.ofFinite H

local notation "SpecARG" =>
  PrimeSpectrum (A ⊗R(G))

local notation "P0" => tensorCharacterRingZeroPrimeIdeal
local notation "ℐ" => tensorCharacterRingInductionIdeal

section RegularPrime

variable [IsDomain A] [Ring.HasFiniteQuotients A]
/-- Helper for Proposition 11-11.4-1: every prime ideal of the finite function ring on ordinary
conjugacy classes is an evaluation prime. This is the final classification step once the zero
fiber has been transported to `ConjClasses G → K`. -/
theorem exists_eq_comap_evalRingHom_bot_of_primeSpectrum_conjClasses
    {K : Type*} [Field K] (P : PrimeSpectrum (ConjClasses G → K)) :
    ∃ c : ConjClasses G,
      PrimeSpectrum.comap (Pi.evalRingHom (fun _ : ConjClasses G ↦ K) c)
        ⟨(⊥ : Ideal K), inferInstance⟩ = P := by
  -- First classify the prime by a coordinate and an arbitrary prime of the field factor.
  obtain ⟨c, q, hq⟩ :=
    PrimeSpectrum.exists_comap_evalRingHom_eq (R := fun _ : ConjClasses G ↦ K) P
  refine ⟨c, ?_⟩
  -- A field has only the zero prime, so the residual prime factor is forced to be `⊥`.
  have hqbotIdeal : q.asIdeal = ⊥ := by
    exact Ideal.eq_bot_of_prime q.asIdeal
  have hqbot : q = ⟨(⊥ : Ideal K), inferInstance⟩ := by
    apply PrimeSpectrum.ext
    simpa using hqbotIdeal
  simpa [hqbot] using hq

/-- Helper for Proposition 11-11.4-1: every prime ideal of the finite function ring on
`p`-regular conjugacy classes is an evaluation prime. This is the final classification step once
the regular fiber has been transported to `PRegularConjClass G p → K`. -/
theorem exists_eq_comap_evalRingHom_bot_of_primeSpectrum_pRegularConjClass
    {K : Type*} [Field K] (p : Nat.Primes)
    (P : PrimeSpectrum (PRegularConjClass G p → K)) :
    ∃ c : PRegularConjClass G p,
      PrimeSpectrum.comap (Pi.evalRingHom (fun _ : PRegularConjClass G p ↦ K) c)
        ⟨(⊥ : Ideal K), inferInstance⟩ = P := by
  -- First classify the prime by a coordinate and an arbitrary prime of the field factor.
  obtain ⟨c, q, hq⟩ :=
    PrimeSpectrum.exists_comap_evalRingHom_eq (R := fun _ : PRegularConjClass G p ↦ K) P
  refine ⟨c, ?_⟩
  -- A field has only the zero prime, so the residual prime factor is again forced to be `⊥`.
  have hqbotIdeal : q.asIdeal = ⊥ := by
    exact Ideal.eq_bot_of_prime q.asIdeal
  have hqbot : q = ⟨(⊥ : Ideal K), inferInstance⟩ := by
    apply PrimeSpectrum.ext
    simpa using hqbotIdeal
  simpa [hqbot] using hq

/-- Helper for Proposition 11-11.4-1: each conjugacy-class indicator already belongs to the
realized scalar extension over any characteristic-zero coefficient field mapping to `ℂ`. This
isolates the basis vector needed for the zero-fiber comparison before the remaining fiber
transport is addressed. -/
lemma conjClassIndicator_mem_characterRingScalarExtension_field
    {K : Type*} [Field K] [CharZero K] [Algebra K ℂ]
    (c : ConjClasses G) :
    (ConjClasses.indicator c : G → ℂ) ∈ characterRingScalarExtension K G := by
  obtain ⟨x, rfl⟩ := ConjClasses.mk_surjective c
  let w : G → ℂ := fun g ↦ (orderOf g : ℂ) * ((ConjClasses.mk x).indicator g : ℚ)
  have hwQ : w ∈ characterRingScalarExtension ℚ G := by
    -- Chapter `9.9.2.1` already realizes the order-weighted class indicator over `ℚ`.
    simpa [w] using
      Representation.weighted_conjClassIndicator_mem_characterRingScalarExtension
        (G := G) (c := ConjClasses.mk x)
  have hle :
      Representation.characterRingScalarExtension ℚ G ≤
        (Representation.characterRingScalarExtension K G).restrictScalars ℚ := by
    refine Submodule.span_le.2 ?_
    intro χ hχ
    exact Submodule.subset_span hχ
  have hwK : w ∈ characterRingScalarExtension K G := hle hwQ
  have hxK : (orderOf x : K) ≠ 0 := by
    exact_mod_cast (orderOf_pos x).ne'
  have hscale :
      ((orderOf x : K)⁻¹) • w =
        (ConjClasses.indicator (ConjClasses.mk x) : G → ℂ) := by
    funext g
    by_cases hg : g ∈ (ConjClasses.mk x).carrier
    · have horder : orderOf g = orderOf x := by
        have hgmk : ConjClasses.mk g = ConjClasses.mk x :=
          ConjClasses.mem_carrier_iff_mk_eq.mp hg
        rcases ConjClasses.mk_eq_mk_iff_isConj.mp hgmk with ⟨a, ha⟩
        simpa using SemiconjBy.orderOf_eq (a := (a : G)) ha
      calc
        (((orderOf x : K)⁻¹) • w) g
            = algebraMap K ℂ ((orderOf x : K)⁻¹) * ((orderOf x : ℂ) * 1) := by
                simp [w, Pi.smul_apply, Algebra.smul_def, ConjClasses.indicator, hg, horder]
        _ = algebraMap K ℂ ((orderOf x : K)⁻¹) * algebraMap K ℂ (orderOf x : K) := by
              simp
        _ = algebraMap K ℂ (((orderOf x : K)⁻¹) * (orderOf x : K)) := by
              rw [← map_mul]
        _ = 1 := by
              simp [hxK]
        _ = (ConjClasses.indicator (ConjClasses.mk x) : G → ℂ) g := by
              simp [ConjClasses.indicator, hg]
    · simp [w, Pi.smul_apply, Algebra.smul_def, ConjClasses.indicator, hg]
  simpa [hscale] using
    (characterRingScalarExtension K G).smul_mem ((orderOf x : K)⁻¹) hwK

/-- Helper for Proposition 11-11.4-1: each conjugacy-class indicator already belongs to the
complex realization of Serre's tensor character ring. This is the basis vector used to identify
the zero fiber with functions on `ConjClasses G`. -/
lemma conjClassIndicator_mem_characterRingScalarExtension_complex
    (c : ConjClasses G) :
    (ConjClasses.indicator c : G → ℂ) ∈ characterRingScalarExtension ℂ G := by
  -- The field-valued indicator lemma already gives the complex specialization.
  simpa using
    conjClassIndicator_mem_characterRingScalarExtension_field
      (G := G) (K := ℂ) c

/-- Helper for Proposition 11-11.4-1: every complex-valued class function on `G` belongs to the
complex realization of Serre's tensor character ring. This turns the zero branch into a function
ring on conjugacy classes once the bottom fiber is transported to the complex realization. -/
lemma classFunction_mem_characterRingScalarExtension_complex
    (f : G → ℂ) (hf : _root_.IsClassFunction f) :
    f ∈ characterRingScalarExtension ℂ G := by
  classical
  letI : Fintype (ConjClasses G) := Fintype.ofFinite (ConjClasses G)
  let F : ConjClasses G → ℂ := hf.lift
  have hsum : (fun x : G ↦ ∑ c : ConjClasses G, F c * ConjClasses.indicator c x) = f := by
    -- Expand a class function in the indicator basis of conjugacy classes.
    funext x
    calc
      ∑ c : ConjClasses G, F c * ConjClasses.indicator c x = F (ConjClasses.mk x) := by
        classical
        rw [Finset.sum_eq_single (ConjClasses.mk x)]
        · simp [ConjClasses.indicator, ConjClasses.mem_carrier_iff_mk_eq]
        · intro c hc hcx
          have hxnot : x ∉ c.carrier := by
            intro hxmem
            exact hcx ((ConjClasses.mem_carrier_iff_mk_eq).mp hxmem).symm
          simp [ConjClasses.indicator, hxnot]
        · intro hmem
          simp at hmem
      _ = f x := by
        simp [F]
  rw [← hsum]
  -- Each indicator basis vector lies in the tensor character ring, so the finite sum does too.
  have hsum_mem :
      (∑ c : ConjClasses G, F c • ConjClasses.indicator c) ∈ characterRingScalarExtension ℂ G := by
    simpa using
      (Submodule.sum_mem (characterRingScalarExtension ℂ G)
        (fun c hc ↦
          (characterRingScalarExtension ℂ G).smul_mem _
            (conjClassIndicator_mem_characterRingScalarExtension_complex (G := G) c)))
  have hsum_eq :
      (∑ c : ConjClasses G, F c • ConjClasses.indicator c : G → ℂ) =
        fun x : G ↦ ∑ c : ConjClasses G, F c * ConjClasses.indicator c x := by
    funext x
    simp [Pi.smul_apply]
  exact hsum_eq ▸ hsum_mem

/-- Helper for Proposition 11-11.4-1: a `K`-valued class function becomes an element of the
scalar extension `K ⊗ R(G)` after applying `algebraMap K ℂ` pointwise. This is the correct
coefficient-field bridge for the zero-fiber route; the earlier attempt to realize arbitrary
complex-valued class functions over `K` was false. -/
lemma classFunction_mem_characterRingScalarExtension_field_mapped
    {K : Type*} [Field K] [CharZero K] [Algebra K ℂ]
    (f : G → K) (hf : _root_.IsClassFunction f) :
    (fun g ↦ algebraMap K ℂ (f g)) ∈ characterRingScalarExtension K G := by
  classical
  letI : Fintype (ConjClasses G) := Fintype.ofFinite (ConjClasses G)
  let F : ConjClasses G → K := hf.lift
  have hsum :
      (fun x : G ↦ ∑ c : ConjClasses G,
        algebraMap K ℂ (F c) * ConjClasses.indicator c x) =
        fun g ↦ algebraMap K ℂ (f g) := by
    -- Expand a class function in the indicator basis of conjugacy classes.
    funext x
    calc
      ∑ c : ConjClasses G, algebraMap K ℂ (F c) * ConjClasses.indicator c x =
          algebraMap K ℂ (F (ConjClasses.mk x)) := by
        classical
        rw [Finset.sum_eq_single (ConjClasses.mk x)]
        · simp [ConjClasses.indicator, ConjClasses.mem_carrier_iff_mk_eq]
        · intro c hc hcx
          have hxnot : x ∉ c.carrier := by
            intro hxmem
            exact hcx ((ConjClasses.mem_carrier_iff_mk_eq).mp hxmem).symm
          simp [ConjClasses.indicator, hxnot]
        · intro hmem
          simp at hmem
      _ = algebraMap K ℂ (f x) := by
        simp [F]
  rw [← hsum]
  -- Each indicator basis vector already lies in the scalar extension over `K`, so the finite sum
  -- does as well.
  have hsum_mem :
      (∑ c : ConjClasses G, F c • ConjClasses.indicator c) ∈ characterRingScalarExtension K G := by
    simpa using
      (Submodule.sum_mem (characterRingScalarExtension K G)
        (fun c hc ↦
          (characterRingScalarExtension K G).smul_mem _
            (conjClassIndicator_mem_characterRingScalarExtension_field
              (G := G) (K := K) c)))
  have hsum_eq :
      (∑ c : ConjClasses G, F c • ConjClasses.indicator c : G → ℂ) =
        fun x : G ↦ ∑ c : ConjClasses G,
          algebraMap K ℂ (F c) * ConjClasses.indicator c x := by
    funext x
    simp [Pi.smul_apply, Algebra.smul_def]
  exact hsum_eq ▸ hsum_mem

/-- Helper for Proposition 11-11.4-1: evaluating realized tensor characters on conjugacy classes
over a characteristic-zero coefficient field still gives the full complex-valued function ring on
`ConjClasses G`. -/
noncomputable def classFunctionSubalgebraEvalConjClasses_field
    {K : Type*} [Field K] [CharZero K] [Algebra K ℂ] :
    characterRingScalarExtensionSubalgebra K G →ₐ[K] (ConjClasses G → ℂ) where
  toFun f :=
    (isClassFunction_of_mem_characterRingScalarExtension
      (show (f : G → ℂ) ∈ characterRingScalarExtension K G from f.2)).lift
  map_one' := by
    -- Evaluating the constant class function `1` on a representative gives `1`.
    ext c
    obtain ⟨g, rfl⟩ := ConjClasses.mk_surjective c
    simp
  map_mul' f g := by
    -- The descended lift preserves pointwise multiplication on class functions.
    ext c
    obtain ⟨x, rfl⟩ := ConjClasses.mk_surjective c
    simp
  map_zero' := by
    ext c
    obtain ⟨g, rfl⟩ := ConjClasses.mk_surjective c
    simp
  map_add' f g := by
    -- The descended lift is pointwise additive on class functions.
    ext c
    obtain ⟨x, rfl⟩ := ConjClasses.mk_surjective c
    simp
  commutes' z := by
    ext c
    obtain ⟨g, rfl⟩ := ConjClasses.mk_surjective c
    simp

/-- Helper for Proposition 11-11.4-1: evaluating a realized complex tensor character on
conjugacy classes packages it as a function on `ConjClasses G`. This is the function-ring side of
the zero-fiber classification route. -/
noncomputable def classFunctionSubalgebraEvalConjClasses_complex :
    characterRingScalarExtensionSubalgebra ℂ G →ₐ[ℂ] (ConjClasses G → ℂ) where
  toFun f :=
    (isClassFunction_of_mem_characterRingScalarExtension
      (show (f : G → ℂ) ∈ characterRingScalarExtension ℂ G from f.2)).lift
  map_one' := by
    -- Evaluating the constant class function `1` on a representative gives `1`.
    ext c
    obtain ⟨g, rfl⟩ := ConjClasses.mk_surjective c
    simp
  map_mul' f g := by
    -- The descended lift preserves pointwise multiplication on class functions.
    ext c
    obtain ⟨x, rfl⟩ := ConjClasses.mk_surjective c
    simp
  map_zero' := by
    ext c
    obtain ⟨g, rfl⟩ := ConjClasses.mk_surjective c
    simp
  map_add' f g := by
    -- The descended lift is pointwise additive on class functions.
    ext c
    obtain ⟨x, rfl⟩ := ConjClasses.mk_surjective c
    simp
  commutes' z := by
    ext c
    obtain ⟨g, rfl⟩ := ConjClasses.mk_surjective c
    simp

/-- Helper for Proposition 11-11.4-1: evaluating realized complex tensor characters on
conjugacy classes is bijective. This closes the function-ring part of the zero branch; the only
remaining zero-branch blocker is the transport from the bottom fiber to this complex realization.
-/
lemma bijective_classFunctionSubalgebraEvalConjClasses_complex :
    Function.Bijective (classFunctionSubalgebraEvalConjClasses_complex (G := G)) := by
  constructor
  · intro f g hfg
    -- Equality on every conjugacy class forces equality of the underlying class functions.
    ext x
    have h := congrFun hfg (ConjClasses.mk x)
    simpa [classFunctionSubalgebraEvalConjClasses_complex] using h
  · intro F
    refine ⟨⟨fun g ↦ F (ConjClasses.mk g), ?_⟩, ?_⟩
    · -- Pulling back a function on conjugacy classes gives a class function, hence a realized
      -- complex tensor character by the previous basis expansion lemma.
      exact classFunction_mem_characterRingScalarExtension_complex
        (G := G) (fun g ↦ F (ConjClasses.mk g))
        ⟨by
          intro x y hxy
          exact congrArg F hxy⟩
    · -- Evaluating the pulled-back class function on conjugacy classes recovers `F`.
      ext c
      obtain ⟨g, rfl⟩ := ConjClasses.mk_surjective c
      simp [classFunctionSubalgebraEvalConjClasses_complex]

/-- Helper for Proposition 11-11.4-1: the complex realization of Serre's tensor character ring is
canonically the full function ring on conjugacy classes. The zero branch is therefore reduced to
transporting the bottom fiber into this already-identified complex realization. -/
noncomputable def classFunctionSubalgebraAlgEquivConjClasses_complex :
    characterRingScalarExtensionSubalgebra ℂ G ≃ₐ[ℂ] (ConjClasses G → ℂ) :=
  AlgEquiv.ofBijective (classFunctionSubalgebraEvalConjClasses_complex (G := G))
    (bijective_classFunctionSubalgebraEvalConjClasses_complex (G := G))

omit [Finite G] [IsDomain A] [Ring.HasFiniteQuotients A] in
/-- Helper for Proposition 11-11.4-1: the realized complex-valued subalgebra model is still
surjective on the nose. This keeps the tensor-to-span bridge available in the zero branch even
before the characteristic-zero fiber transport is upgraded to an equivalence. -/
theorem surjective_tensorCharacterRingToSubalgebra :
    Function.Surjective (tensorCharacterRingToSubalgebra A G) := by
  intro f
  -- The span model is onto by `Submodule.tensorToSpan`, so every realized element comes from an
  -- actual tensor character.
  rcases (R(G)).toSubmodule.surjective_tensorToSpan A ⟨(f : G → ℂ), f.2⟩ with ⟨χ, hχ⟩
  refine ⟨χ, ?_⟩
  ext g
  have h := congrArg
    (fun z : Representation.characterRingScalarExtension A G ↦ (z : G → ℂ) g) hχ
  simpa [tensorCharacterRingToSubalgebra] using h

/-- Helper for Proposition 11-11.4-1: once the coefficient field is an epi/flat `ℤ`-algebra,
the tensor character ring injects into the realized scalar-extension subalgebra inside `G → ℂ`.
Route correction: this is the precise structural fact available without forcing a false
identification with the full coefficient-field-valued function ring on conjugacy classes. -/
theorem injective_tensorCharacterRingToSubalgebra_field
    {K : Type*} [Field K] [CharZero K] [Algebra K ℂ]
    [Algebra.IsEpi ℤ K] [Module.Flat ℤ K] :
    Function.Injective (tensorCharacterRingToSubalgebra K G) := by
  intro χ ψ hχψ
  have hfun :
      ((tensorCharacterRingToSubalgebra K G χ :
          characterRingScalarExtensionSubalgebra K G) : G → ℂ) =
        ((tensorCharacterRingToSubalgebra K G ψ :
          characterRingScalarExtensionSubalgebra K G) : G → ℂ) := by
    exact
      congrArg
        (fun f : characterRingScalarExtensionSubalgebra K G ↦ (f : G → ℂ))
        hχψ
  have hspan :
      (((R(G)).toSubmodule).tensorToSpan K χ :
          Representation.characterRingScalarExtension K G) =
        (((R(G)).toSubmodule).tensorToSpan K ψ :
          Representation.characterRingScalarExtension K G) := by
    -- Equality in the realized subalgebra is equality in the span model after evaluating points.
    ext g
    simpa [tensorCharacterRingToSubalgebra] using congrArg (fun f : G → ℂ ↦ f g) hfun
  exact ((R(G)).toSubmodule.injective_tensorToSpan K) hspan

/-- Helper for Proposition 11-11.4-1: equality on all conjugacy classes already detects equality
in the realized scalar-extension subalgebra over any characteristic-zero coefficient field. This
keeps later zero-fiber comparisons at the function-ring level instead of returning to pointwise
arguments on `G`. -/
theorem injective_classFunctionSubalgebraEvalConjClasses_field
    {K : Type*} [Field K] [CharZero K] [Algebra K ℂ] :
    Function.Injective (classFunctionSubalgebraEvalConjClasses_field (G := G) (K := K)) := by
  intro f g hfg
  -- Equality on every conjugacy class forces equality of the underlying class functions.
  ext x
  have h := congrFun hfg (ConjClasses.mk x)
  simpa [classFunctionSubalgebraEvalConjClasses_field] using h

/-- Helper for Proposition 11-11.4-1: any `K`-valued function on conjugacy classes is realized,
after applying `algebraMap K ℂ` pointwise, by an element of the realized scalar-extension
subalgebra. This is the mapped-function version of the zero-fiber surjectivity step. -/
theorem exists_classFunctionSubalgebra_preimage_of_conjClassFunction_mapped
    {K : Type*} [Field K] [CharZero K] [Algebra K ℂ]
    (F : ConjClasses G → K) :
    ∃ f : characterRingScalarExtensionSubalgebra K G,
      classFunctionSubalgebraEvalConjClasses_field (G := G) (K := K) f =
        fun c ↦ algebraMap K ℂ (F c) := by
  refine ⟨⟨fun g ↦ algebraMap K ℂ (F (ConjClasses.mk g)), ?_⟩, ?_⟩
  · -- Pull back the target function to a class function on `G`, then use the mapped realization
    -- lemma proved above.
    exact classFunction_mem_characterRingScalarExtension_field_mapped
      (G := G) (K := K) (fun g ↦ F (ConjClasses.mk g))
      ⟨by
        intro x y hxy
        exact congrArg F hxy⟩
  · -- Descending the pulled-back class function simply evaluates `F` on the chosen class.
    ext c
    obtain ⟨g, rfl⟩ := ConjClasses.mk_surjective c
    simp [classFunctionSubalgebraEvalConjClasses_field]

/-- Helper for Proposition 11-11.4-1: any mapped `K`-valued function on conjugacy classes is
already realized by an actual tensor character. This packages the previous subalgebra surjectivity
with the tensor-to-subalgebra realization map, isolating the remaining zero-fiber blocker to the
coefficient-side descent. -/
theorem exists_tensorCharacter_preimage_of_conjClassFunction_mapped
    {K : Type*} [Field K] [CharZero K] [Algebra K ℂ]
    (F : ConjClasses G → K) :
    ∃ χ : TensorProduct ℤ K (R(G)),
      classFunctionSubalgebraEvalConjClasses_field (G := G) (K := K)
          (tensorCharacterRingToSubalgebra K G χ) =
        fun c ↦ algebraMap K ℂ (F c) := by
  obtain ⟨f, hf⟩ :=
    exists_classFunctionSubalgebra_preimage_of_conjClassFunction_mapped
      (G := G) (K := K) F
  obtain ⟨χ, hχ⟩ := surjective_tensorCharacterRingToSubalgebra (A := K) (G := G) f
  refine ⟨χ, ?_⟩
  -- Replace the chosen subalgebra witness by its tensor-character preimage.
  calc
    classFunctionSubalgebraEvalConjClasses_field (G := G) (K := K)
        (tensorCharacterRingToSubalgebra K G χ) =
      classFunctionSubalgebraEvalConjClasses_field (G := G) (K := K) f := by
        simpa using
          congrArg (classFunctionSubalgebraEvalConjClasses_field (G := G) (K := K)) hχ
    _ = fun c ↦ algebraMap K ℂ (F c) := hf

/-- Helper for Proposition 11-11.4-1: the point-mass function on `ConjClasses G` at the chosen
class `c`. This keeps the zero-branch mapped-surjectivity witness readable without threading a
global `DecidableEq` instance through the section. -/
noncomputable def conjClass_deltaFunction
    {K : Type*} [Zero K] [One K] (c : ConjClasses G) :
    ConjClasses G → K :=
  fun d ↦
    let _ : DecidableEq (ConjClasses G) := Classical.decEq _
    if d = c then 1 else 0

/-- Helper for Proposition 11-11.4-1: each conjugacy-class point mass over a characteristic-zero
field already comes from a tensor character after applying `algebraMap K ℂ` pointwise. This is
the exact mapped surjectivity input needed for the zero-fiber coefficient-descent step. -/
theorem exists_tensorCharacter_preimage_of_conjClass_delta_mapped
    {K : Type*} [Field K] [CharZero K] [Algebra K ℂ]
    (c : ConjClasses G) :
    ∃ χ : TensorProduct ℤ K (R(G)),
      classFunctionSubalgebraEvalConjClasses_field (G := G) (K := K)
          (tensorCharacterRingToSubalgebra K G χ) =
        fun d ↦ algebraMap K ℂ (conjClass_deltaFunction (G := G) (K := K) c d) := by
  -- Specialize the mapped-function surjectivity theorem to the point mass at `c`.
  -- Specialize the mapped-function surjectivity theorem to the point mass at `c`.
  simpa using
    exists_tensorCharacter_preimage_of_conjClassFunction_mapped
      (G := G) (K := K)
      (conjClass_deltaFunction (G := G) (K := K) c)

/-- Helper for Proposition 11-11.4-1: once a characteristic-zero tensor character is evaluated on
conjugacy classes, those values already determine the tensor element. This packages the injective
half of the zero-branch comparison and shows that the remaining obstruction is coefficient
descent, not class-function separation. -/
theorem tensorCharacter_eq_of_conjClass_eval_eq
    {K : Type*} [Field K] [CharZero K] [Algebra K ℂ]
    [Algebra.IsEpi ℤ K] [Module.Flat ℤ K]
    {χ ψ : TensorProduct ℤ K (R(G))}
    (hχψ : ∀ c : ConjClasses G,
      classFunctionSubalgebraEvalConjClasses_field (G := G) (K := K)
          (tensorCharacterRingToSubalgebra K G χ) c =
        classFunctionSubalgebraEvalConjClasses_field (G := G) (K := K)
          (tensorCharacterRingToSubalgebra K G ψ) c) :
    χ = ψ := by
  -- Equality on every conjugacy class already identifies the realized class functions.
  have hclass :
      classFunctionSubalgebraEvalConjClasses_field (G := G) (K := K)
          (tensorCharacterRingToSubalgebra K G χ) =
        classFunctionSubalgebraEvalConjClasses_field (G := G) (K := K)
          (tensorCharacterRingToSubalgebra K G ψ) := by
    ext c
    exact hχψ c
  -- Injectivity of evaluation and of the tensor-to-subalgebra realization recovers the tensor.
  apply injective_tensorCharacterRingToSubalgebra_field (G := G) (K := K)
  exact
    (injective_classFunctionSubalgebraEvalConjClasses_field (G := G) (K := K)) hclass

/-- Helper for Proposition 11-11.4-1: each conjugacy-class indicator over a characteristic-zero
field is realized by an actual tensor character. This packages the weighted-Adams indicator route
as a concrete tensor element, so the remaining zero-fiber blocker is only the algebra-equivalence
packaging. -/
theorem exists_tensorCharacter_preimage_of_conjClassIndicator
    {K : Type*} [Field K] [CharZero K] [Algebra K ℂ] (c : ConjClasses G) :
    ∃ χ : TensorProduct ℤ K (R(G)),
      (((tensorCharacterRingToSubalgebra K G χ :
          characterRingScalarExtensionSubalgebra K G) : G → ℂ) =
        ConjClasses.indicator c) := by
  let f : characterRingScalarExtensionSubalgebra K G :=
    ⟨ConjClasses.indicator c,
      conjClassIndicator_mem_characterRingScalarExtension_field
        (G := G) (K := K) c⟩
  obtain ⟨χ, hχ⟩ := surjective_tensorCharacterRingToSubalgebra (A := K) (G := G) f
  refine ⟨χ, ?_⟩
  -- Forgetting the subtype records the required pointwise equality of functions.
  simpa [f] using congrArg
    (fun z : characterRingScalarExtensionSubalgebra K G ↦ (z : G → ℂ)) hχ

/-- Helper for Proposition 11-11.4-1: the point-mass function at a `p`-regular conjugacy class.
This keeps the later delta-witness statements readable without threading a global decidable
equality instance through the section. -/
noncomputable def pregular_deltaFunction
    (p : Nat.Primes) {K : Type*} [Zero K] [One K]
    (c : PRegularConjClass G p) :
    PRegularConjClass G p → K :=
  fun d ↦
    let _ : DecidableEq (PRegularConjClass G p) := Classical.decEq _
    if d = c then 1 else 0

/-- Helper for Proposition 11-11.4-1: descend a tensor character to Serre's owner
`PRegularConjClass G p` by first viewing it as a class function on `G`. -/
def tensorCharacterRingPRegularLift
    {K : Type*} [Field K] [CharZero K] [Algebra K ℂ]
    (p : ℕ) (χ : TensorProduct ℤ K (R(G))) :
    PRegularConjClass G p → ℂ :=
  let f : G → ℂ :=
    ((tensorCharacterRingToSubalgebra K G χ :
      characterRingScalarExtensionSubalgebra K G) : G → ℂ)
  (isClassFunction_of_mem_characterRingScalarExtension
    (show f ∈ characterRingScalarExtension K G by
      simpa [f] using
        (tensorCharacterRingToSubalgebra K G χ :
          characterRingScalarExtensionSubalgebra K G).2)).pRegularLift p

/-- Helper for Proposition 11-11.4-1: the indicator of a `p`-regular class lifts to an actual
tensor character whose descended regular-class function is the corresponding point mass after
applying `algebraMap K ℂ`. This isolates the executable delta witness already available before the
remaining residue-field algebra-equivalence packaging. -/
theorem exists_tensorCharacter_preimage_of_pregular_delta
    {K : Type*} [Field K] [CharZero K] [Algebra K ℂ]
    (p : Nat.Primes) (c : PRegularConjClass G p) :
    ∃ χ : TensorProduct ℤ K (R(G)),
      tensorCharacterRingPRegularLift (G := G) (K := K) (p : ℕ) χ =
        fun d ↦ algebraMap K ℂ (pregular_deltaFunction (G := G) p c d) := by
  classical
  obtain ⟨χ, hχ⟩ :=
    exists_tensorCharacter_preimage_of_conjClassIndicator
      (G := G) (K := K) c.1
  refine ⟨χ, ?_⟩
  ext d
  obtain ⟨x, hx⟩ := ConjClasses.mk_surjective (d : ConjClasses G)
  let f : G → ℂ :=
    ((tensorCharacterRingToSubalgebra K G χ :
      characterRingScalarExtensionSubalgebra K G) : G → ℂ)
  have hf : _root_.IsClassFunction f :=
    isClassFunction_of_mem_characterRingScalarExtension
      (show f ∈ characterRingScalarExtension K G by
        simpa [f] using
          (tensorCharacterRingToSubalgebra K G χ :
            characterRingScalarExtensionSubalgebra K G).2)
  have hfx : f x = ConjClasses.indicator c.1 x := by
    -- Evaluate the chosen tensor-character representative at a representative of `d`.
    simpa [f] using congrArg (fun g : G → ℂ ↦ g x) hχ
  -- Evaluating the descended class function at a representative of `d` reduces to the underlying
  -- conjugacy-class indicator.
  change hf.pRegularLift (p : ℕ) d =
      algebraMap K ℂ (pregular_deltaFunction (G := G) p c d)
  rw [IsClassFunction.pRegularLift]
  rw [show d.1 = ConjClasses.mk x by simpa [hx], _root_.IsClassFunction.lift_mk, hfx]
  by_cases hdc : d = c
  · subst hdc
    have hxmem : x ∈ d.1.carrier := ConjClasses.mem_carrier_iff_mk_eq.mpr hx
    simp [ConjClasses.indicator, pregular_deltaFunction, hxmem]
  · have hxnot : x ∉ c.1.carrier := by
      intro hxmem
      apply hdc
      apply Subtype.ext
      exact hx.symm.trans (ConjClasses.mem_carrier_iff_mk_eq.mp hxmem)
    simp [ConjClasses.indicator, pregular_deltaFunction, hxnot, hdc]

/-- Helper for Proposition 11-11.4-1: base change along any field extension `A → K` identifies
the fiber-side tensor product `K ⊗[A] (A ⊗ R(G))` with the scalar-extended tensor character ring
`K ⊗ R(G)`. This removes the tensor-associativity bookkeeping from both the zero and regular
fiber branches, so the remaining work is purely the class-function quotient step. -/
noncomputable def fiber_algEquiv_tensorCharacterRing_baseChange
    (K : Type*) [Field K] [Algebra A K] :
    TensorProduct A K (A ⊗R(G)) ≃ₐ[K] TensorProduct ℤ K (R(G)) := by
  let g : ↥R[ℂ](G) ≃ₐ[ℤ] ↥R[ℂ](G) :=
    AlgEquiv.refl (R := ℤ) (A₁ := ↥R[ℂ](G))
  -- First reassociate the iterated tensor product, then contract the middle factor `K ⊗[A] A`
  -- using the standard right-unit algebra equivalence.
  exact
    (Algebra.TensorProduct.assoc ℤ A K K A (R(G))).symm.trans
      (Algebra.TensorProduct.congr (Algebra.TensorProduct.rid A K K) g)

/-- Helper for Proposition 11-11.4-1: choose a tensor-character lift of the conjugacy-class point
mass at `c`. This is the algebraic idempotent family that should generate the bottom fiber once
the remaining surjectivity step is proved. -/
noncomputable def conjClass_deltaTensor
    {K : Type*} [Field K] [CharZero K] [Algebra K ℂ]
    (c : ConjClasses G) :
    TensorProduct ℤ K (R(G)) :=
  Classical.choose
    (exists_tensorCharacter_preimage_of_conjClass_delta_mapped (G := G) (K := K) c)

/-- Helper for Proposition 11-11.4-1: the chosen tensor `conjClass_deltaTensor c` evaluates to
the mapped point mass at `c` on `ConjClasses G`. This is the concrete coordinate formula used in
the bottom-fiber orthogonal-idempotent calculations. -/
theorem conjClass_deltaTensor_spec
    {K : Type*} [Field K] [CharZero K] [Algebra K ℂ]
    (c : ConjClasses G) :
    classFunctionSubalgebraEvalConjClasses_field (G := G) (K := K)
        (tensorCharacterRingToSubalgebra K G (conjClass_deltaTensor (G := G) (K := K) c)) =
      fun d ↦ algebraMap K ℂ (conjClass_deltaFunction (G := G) (K := K) c d) :=
  Classical.choose_spec
    (exists_tensorCharacter_preimage_of_conjClass_delta_mapped (G := G) (K := K) c)

/-- Helper for Proposition 11-11.4-1: the chosen delta tensors multiply like ordinary point
masses on `ConjClasses G`. This isolates the algebra structure needed for the bottom-fiber
function-ring model from the still-missing surjectivity step. -/
theorem conjClass_deltaTensor_mul
    {K : Type*} [Field K] [CharZero K] [Algebra K ℂ]
    [Algebra.IsEpi ℤ K] [Module.Flat ℤ K] [DecidableEq (ConjClasses G)]
    (c d : ConjClasses G) :
    conjClass_deltaTensor (G := G) (K := K) c *
        conjClass_deltaTensor (G := G) (K := K) d =
      if c = d then conjClass_deltaTensor (G := G) (K := K) c else 0 := by
  classical
  -- Compare the two tensors on every conjugacy class and then use the already-proved injectivity
  -- of class-function evaluation on tensor characters.
  apply tensorCharacter_eq_of_conjClass_eval_eq (G := G) (K := K)
  intro e
  by_cases hcd : c = d
  · subst hcd
    simp [conjClass_deltaTensor_spec, conjClass_deltaFunction]
  · have hdc : d ≠ c := fun h ↦ hcd h.symm
    by_cases hed : e = d
    · subst hed
      have hce : c ≠ e := fun h ↦ hdc h.symm
      simp [conjClass_deltaTensor_spec, conjClass_deltaFunction, hce]
      exact hdc
    · simp [hed, hcd, conjClass_deltaTensor_spec, conjClass_deltaFunction]

/-- Helper for Proposition 11-11.4-1: summing the chosen delta tensors over all conjugacy classes
gives the tensor-character unit. This packages the partition-of-unity identity needed to build the
bottom-fiber function-ring algebra map. -/
theorem sum_conjClass_deltaTensor_eq_one
    {K : Type*} [Field K] [CharZero K] [Algebra K ℂ]
    [Algebra.IsEpi ℤ K] [Module.Flat ℤ K] :
    ∑ c : ConjClasses G, conjClass_deltaTensor (G := G) (K := K) c = 1 := by
  -- Evaluate the finite sum at an arbitrary conjugacy class; exactly one point mass contributes.
  apply tensorCharacter_eq_of_conjClass_eval_eq (G := G) (K := K)
  intro d
  simp [conjClass_deltaTensor_spec, conjClass_deltaFunction]

/-- Helper for Proposition 11-11.4-1: the orthogonal delta tensors define the obvious algebra map
from `K`-valued functions on `ConjClasses G` into the tensor character ring over `K`. The only
remaining bottom-fiber structural gap is to prove that this algebra map is surjective. -/
noncomputable def conjClassFunction_to_tensorCharacterRing
    {K : Type*} [Field K] [CharZero K] [Algebra K ℂ]
    [Algebra.IsEpi ℤ K] [Module.Flat ℤ K] :
    (ConjClasses G → K) →ₐ[K] TensorProduct ℤ K (R(G)) where
  toFun F :=
    ∑ c : ConjClasses G, F c • conjClass_deltaTensor (G := G) (K := K) c
  map_zero' := by
    simp
  map_one' := by
    -- The constant function `1` maps to the partition of unity of the delta tensors.
    simpa using sum_conjClass_deltaTensor_eq_one (G := G) (K := K)
  map_add' F H := by
    -- Addition is coefficientwise on the finite delta basis.
    simp [add_smul, Finset.sum_add_distrib]
  map_mul' F H := by
    -- The orthogonal-idempotent relations reduce multiplication to the diagonal coefficients.
    apply tensorCharacter_eq_of_conjClass_eval_eq (G := G) (K := K)
    intro d
    simpa [conjClass_deltaTensor_spec, conjClass_deltaFunction, smul_smul, mul_comm]
  commutes' a := by
    -- Scalars act as constant functions, so they again collapse against the partition of unity.
    calc
      (∑ x : ConjClasses G, a • conjClass_deltaTensor (G := G) (K := K) x)
          = a • ∑ x : ConjClasses G, conjClass_deltaTensor (G := G) (K := K) x := by
              simp [Finset.smul_sum]
      _ = a • (1 : TensorProduct ℤ K (R(G))) := by
            rw [sum_conjClass_deltaTensor_eq_one (G := G) (K := K)]
      _ = algebraMap K (TensorProduct ℤ K (R(G))) a := by
            rw [Algebra.algebraMap_eq_smul_one]

/-- Helper for Proposition 11-11.4-1: evaluating the delta-basis algebra map on a conjugacy
class recovers the original coefficient of that class after applying `algebraMap K ℂ`. This is
the explicit basis computation that isolates the remaining zero-fiber obstruction to coefficient
descent. -/
theorem conjClassFunction_to_tensorCharacterRing_spec
    {K : Type*} [Field K] [CharZero K] [Algebra K ℂ]
    [Algebra.IsEpi ℤ K] [Module.Flat ℤ K]
    (F : ConjClasses G → K) (c : ConjClasses G) :
    classFunctionSubalgebraEvalConjClasses_field (G := G) (K := K)
        (tensorCharacterRingToSubalgebra K G
          (conjClassFunction_to_tensorCharacterRing (G := G) (K := K) F)) c =
      algebraMap K ℂ (F c) := by
  -- Evaluate the delta-basis expansion at `c`; every summand vanishes except the one supported
  -- on `c`, and that remaining summand is the scalar image of `F c`.
  have hpure :
      classFunctionSubalgebraEvalConjClasses_field (G := G) (K := K)
          ((tensorCharacterRingToSubalgebra K G) (F c ⊗ₜ[ℤ] 1)) c =
        algebraMap K ℂ (F c) := by
    simpa [classFunctionSubalgebraEvalConjClasses_field] using
      congrArg
        (fun f : characterRingScalarExtensionSubalgebra K G ↦
          classFunctionSubalgebraEvalConjClasses_field (G := G) (K := K) f c)
        ((tensorCharacterRingToSubalgebra K G).commutes (F c))
  simpa [conjClassFunction_to_tensorCharacterRing, conjClass_deltaTensor_spec,
    conjClass_deltaFunction, Algebra.smul_def] using hpure

/-- Helper for Proposition 11-11.4-1: the delta-tensor algebra map from the function ring on
`ConjClasses G` is injective. This reduces the bottom-fiber algebra-equivalence hole to the
surjectivity of `conjClassFunction_to_tensorCharacterRing`. -/
theorem injective_conjClassFunction_to_tensorCharacterRing
    {K : Type*} [Field K] [CharZero K] [Algebra K ℂ]
    [Algebra.IsEpi ℤ K] [Module.Flat ℤ K] :
    Function.Injective (conjClassFunction_to_tensorCharacterRing (G := G) (K := K)) := by
  intro F H hFH
  ext c
  have hEval := congrArg
    (fun χ : TensorProduct ℤ K (R(G)) ↦
      classFunctionSubalgebraEvalConjClasses_field (G := G) (K := K)
        (tensorCharacterRingToSubalgebra K G χ) c)
    hFH
  exact (algebraMap K ℂ).injective <| by
    simpa [conjClassFunction_to_tensorCharacterRing_spec] using hEval

/-- Helper for Proposition 11-11.4-1: pairing a finite linear combination of group functions with
another function distributes coefficientwise. This is the finite-dimensional bookkeeping needed in
the bottom-fiber dimension count. -/
theorem groupFunctionPairing_sum_smul_left
    {ι : Type*} (s : Finset ι) (a : ι → ℂ) (φ : ι → G → ℂ) (ψ : G → ℂ) :
    Representation.groupFunctionPairingOverField ℂ (∑ i ∈ s, a i • φ i) ψ =
      ∑ i ∈ s, a i * Representation.groupFunctionPairingOverField ℂ (φ i) ψ := by
  classical
  -- Expand the finite sum one term at a time and use additivity and homogeneity of the pairing.
  induction s using Finset.induction_on with
  | empty =>
      simp [Representation.groupFunctionPairingOverField]
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Representation.groupFunctionPairing_add_left,
        Representation.groupFunctionPairing_smul_left, ih, Finset.sum_insert hi]


end RegularPrime

end
