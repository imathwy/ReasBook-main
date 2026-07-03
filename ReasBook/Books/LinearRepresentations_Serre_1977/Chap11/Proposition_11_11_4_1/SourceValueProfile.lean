import LinearRepresentations_Serre_1977.Chap10.Lemma_10_10_2_3
import LinearRepresentations_Serre_1977.Chap11.Proposition_11_11_4_1.FixedClassEvaluation

-- Stable source value-profile helpers extracted from Proposition 11-11.4-1.

universe u v

noncomputable section

open Representation
open scoped Representation SubgroupInduction TensorProduct

namespace Proposition_11_11_4_1

section

variable {G : Type} [Group G]
variable {A : Type v} [CommRing A]
variable [Finite G] [Algebra A ℂ]

local instance sourceValueProfileFintypeGroup : Fintype G := Fintype.ofFinite G
local instance sourceValueProfileFintypeSubgroup (H : Subgroup G) : Fintype H :=
  Fintype.ofFinite H

local notation "P0" => tensorCharacterRingZeroPrimeIdeal

section ZeroFiberIntegralClosureBridge

variable [IsDomain A] [Ring.HasFiniteQuotients A] [IsIntegralClosure A ℤ ℂ]

/-- Helper for Proposition 11-11.4-1: when fixed-class evaluation already lands in the integral
closure ring `A`, the zero point of `Spec A` pulls back exactly to the public zero owner `P₀,c`.
This is the source-faithful normalization step behind the discarded stronger zero-branch route. -/
theorem zero_line_point_eq_comap_tensorCharacterRingValueAtConjClass
    (c : ConjClasses G) :
    PrimeSpectrum.comap (tensorCharacterRingValueAtConjClass (A := A) (G := G) c)
      ⟨(⊥ : Ideal A), inferInstance⟩ = P0 A c := by
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

/-- Helper for Proposition 11-11.4-1: bundle the fixed-class evaluations into LinearRepresentations_Serre_1977's source
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

/-- Helper for Proposition 11-11.4-1: LinearRepresentations_Serre_1977's source profile map
`A ⊗ R(G) → A^{Cl(G)}` is injective. This is the exact missing hypothesis needed to apply
lying-over to the source inclusion and keep the proof on LinearRepresentations_Serre_1977's source spectrum
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

/-- Helper for Proposition 11-11.4-1: the point-mass function at a conjugacy class in LinearRepresentations_Serre_1977's
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
LinearRepresentations_Serre_1977's source profile map. This is the idempotent input for the lying-over step on
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

/-- Helper for Proposition 11-11.4-1: LinearRepresentations_Serre_1977's source profile map
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

/-- Helper for Proposition 11-11.4-1: evaluating LinearRepresentations_Serre_1977's source profile at a fixed conjugacy
class recovers the corresponding fixed-class evaluation map. This keeps the source-spectrum proof
as a direct comap computation instead of a transport argument. -/
theorem evalRingHom_comp_tensorCharacterRingValueProfile
    (d : ConjClasses G) :
    (Pi.evalRingHom (fun _ : ConjClasses G ↦ A) d).comp
        (tensorCharacterRingValueProfile (A := A) (G := G)).toRingHom =
      (tensorCharacterRingValueAtConjClass (A := A) (G := G) d).toRingHom := by
  rfl

/-- Helper for Proposition 11-11.4-1: every ambient prime should be presented directly as the
pullback of a coefficient prime along fixed-class evaluation. This is LinearRepresentations_Serre_1977's actual source map
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
maximal ideal `M`, LinearRepresentations_Serre_1977's source-spectrum presentation can be normalized so that the coefficient
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

end ZeroFiberIntegralClosureBridge

end

end Proposition_11_11_4_1
