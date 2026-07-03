import Serre.Chap11.Proposition_11_11_4_1.ConjClassFunctionRealization

-- Stable zero-fiber transport helpers extracted from Proposition 11-11.4-1.

universe u v

noncomputable section

open Representation
open scoped Representation SubgroupInduction TensorProduct

section

variable {G : Type} [Group G]
variable {A : Type v} [CommRing A]
variable [Finite G] [Algebra A ℂ]

local instance zeroFiberTransportFintypeGroup : Fintype G := Fintype.ofFinite G
local instance zeroFiberTransportFintypeSubgroup (H : Subgroup G) : Fintype H :=
  Fintype.ofFinite H

local notation "SpecARG" =>
  PrimeSpectrum (A ⊗R(G))

local notation "P0" => tensorCharacterRingZeroPrimeIdeal
local notation "ℐ" => tensorCharacterRingInductionIdeal

variable [IsDomain A] [Ring.HasFiniteQuotients A]
/-- Helper for Proposition 11-11.4-1: evaluating `P₀,c` on a scalar tensor recovers the original
scalar under `A → ℂ`. -/
lemma tensorCharacterRingZeroPrimeIdealEval_algebraMap
    (A : Type v) [CommRing A] [Algebra A ℂ] (G : Type) [Group G] [Finite G]
    (c : ConjClasses G) (a : A) :
    tensorCharacterRingZeroPrimeIdealEval A c ((algebraMap A (A ⊗R(G))) a) =
      algebraMap A ℂ a := by
  -- The scalar map into the tensor character ring is transported by the algebra realization
  -- `A ⊗ R(G) → characterRingScalarExtensionSubalgebra A G`, and evaluation then reads off the
  -- same scalar as a constant class function.
  obtain ⟨g, rfl⟩ := ConjClasses.mk_surjective c
  change ((tensorCharacterRingToSubalgebra A G)
      (algebraMap A (A ⊗R(G)) a) : G → ℂ) g = algebraMap A ℂ a
  -- The tensor-character realization is an `A`-algebra map, so it commutes with the scalar map.
  simpa using
    congrArg (fun f : characterRingScalarExtensionSubalgebra A G ↦ (f : G → ℂ) g)
      ((tensorCharacterRingToSubalgebra A G).commutes a)

/-- Helper for Proposition 11-11.4-1: the zero-residual prime `P₀,c` contracts to the kernel of
`A → ℂ`. -/
lemma tensorCharacterRingZeroPrimeIdeal_comap_algebraMap
    (c : ConjClasses G) :
    Ideal.comap (algebraMap A (A ⊗R(G))) (P0 A c).asIdeal =
      RingHom.ker (algebraMap A ℂ) := by
  -- A scalar lies in the contracted ideal exactly when its evaluation on the chosen conjugacy
  -- class vanishes, and the previous lemma computes that evaluation explicitly.
  ext a
  -- Reduce the membership test to the scalar-evaluation computation.
  change tensorCharacterRingZeroPrimeIdealEval A c ((algebraMap A (A ⊗R(G))) a) = 0 ↔
      algebraMap A ℂ a = 0
  rw [tensorCharacterRingZeroPrimeIdealEval_algebraMap (A := A) (G := G) c a]

variable [IsDomain A] [Ring.HasFiniteQuotients A]

/-- Helper for Proposition 11-11.4-1: in the arithmetic setting, the zero-residual prime
`P₀,c` lies over the zero ideal of `A`. -/
theorem tensorCharacterRingZeroPrimeIdeal_comap_algebraMap_eq_bot
    (c : ConjClasses G) :
    Ideal.comap (algebraMap A (A ⊗R(G))) (P0 A c).asIdeal = ⊥ := by
  -- The explicit contraction formula from the previous lemma collapses because `A → ℂ` is
  -- injective in the arithmetic setting.
  rw [tensorCharacterRingZeroPrimeIdeal_comap_algebraMap, ker_algebraMap_complex_eq_bot]

/-- Helper for Proposition 11-11.4-1: the indexed zero owner `P₀,c` is recovered by the standard
round-trip through the bottom fiber over `(0)`. This packages the already-verified ambient
transport normalization for the specific zero-branch owner primes. -/
theorem zeroPrimeIdeal_prime_over_bot_to_fiber_symm
    (c : ConjClasses G) :
    ((PrimeSpectrum.primesOverOrderIsoFiber A (A ⊗R(G)) (⊥ : Ideal A)).symm
      (prime_over_bot_to_fiber (A := A) (G := G) (P0 A c)
        (tensorCharacterRingZeroPrimeIdeal_comap_algebraMap_eq_bot (A := A) (G := G) c))).1 =
        (P0 A c).asIdeal := by
  -- The zero owner already lies over `(0)`, so the general fiber/primes-over normalization
  -- theorem applies to it directly.
  simpa using
    prime_over_bot_to_fiber_symm (A := A) (G := G) (P0 A c)
      (tensorCharacterRingZeroPrimeIdeal_comap_algebraMap_eq_bot (A := A) (G := G) c)

/-- Helper for Proposition 11-11.4-1: the evaluation prime at a conjugacy class in the function
ring on `ConjClasses G` over the bottom residue field. -/
noncomputable def zeroFiberEvalPrime
    (c : ConjClasses G) :
    PrimeSpectrum (ConjClasses G → ((⊥ : Ideal A).ResidueField)) :=
  PrimeSpectrum.comap
    (Pi.evalRingHom (fun _ : ConjClasses G ↦ ((⊥ : Ideal A).ResidueField)) c)
    ⟨(⊥ : Ideal ((⊥ : Ideal A).ResidueField)), inferInstance⟩

/-- Helper for Proposition 11-11.4-1: distinct conjugacy classes already define distinct
coordinate-evaluation primes on the function ring `ConjClasses G → ((0).ResidueField)`. This is
the zero-fiber analogue of the regular-side coordinate uniqueness lemma. -/
theorem zeroFiberEvalPrime_eq_iff
    (c₁ c₂ : ConjClasses G) :
    zeroFiberEvalPrime (A := A) (G := G) c₁ =
        zeroFiberEvalPrime (A := A) (G := G) c₂ ↔
      c₁ = c₂ := by
  constructor
  · intro hP
    -- The point-mass function at `c₁` separates the two coordinate kernels unless the classes
    -- are equal.
    by_contra hc
    classical
    let f : ConjClasses G → ((⊥ : Ideal A).ResidueField) := fun d ↦ if d = c₁ then 1 else 0
    have hc' : c₂ ≠ c₁ := fun h ↦ hc h.symm
    have hf₂ : f ∈ (zeroFiberEvalPrime (A := A) (G := G) c₂).asIdeal := by
      change Pi.evalRingHom (fun _ : ConjClasses G ↦ ((⊥ : Ideal A).ResidueField)) c₂ f = 0
      simp [f, hc']
    have hf₁ : f ∉ (zeroFiberEvalPrime (A := A) (G := G) c₁).asIdeal := by
      change
        Pi.evalRingHom (fun _ : ConjClasses G ↦ ((⊥ : Ideal A).ResidueField)) c₁ f ≠ 0
      simp [f]
    exact hf₁ (by simpa [hP] using hf₂)
  · intro hc
    -- Equal class parameters make the coordinate kernels definitionally equal.
    subst hc
    rfl

/-- Helper for Proposition 11-11.4-1: an algebra equivalence from the bottom fiber to the
function ring on `ConjClasses G` transports coordinate-evaluation primes back to the fiber. -/
noncomputable def zero_fiber_lift
    (e : ((⊥ : Ideal A).Fiber (A ⊗R(G))) ≃ₐ[((⊥ : Ideal A).ResidueField)]
      (ConjClasses G → ((⊥ : Ideal A).ResidueField)))
    (c : ConjClasses G) :
    PrimeSpectrum (((⊥ : Ideal A).Fiber (A ⊗R(G)))) :=
  (PrimeSpectrum.comapEquiv e.toRingEquiv).symm
    (zeroFiberEvalPrime (A := A) (G := G) c)

/-- Helper for Proposition 11-11.4-1: after transporting the bottom fiber to the function ring on
`ConjClasses G`, equality of two lifted coordinate primes is already equivalent to equality of the
underlying conjugacy classes. This removes any remaining uniqueness ambiguity once the zero-fiber
algebra equivalence is in hand. -/
theorem zero_fiber_lift_eq_iff
    (e : ((⊥ : Ideal A).Fiber (A ⊗R(G))) ≃ₐ[((⊥ : Ideal A).ResidueField)]
      (ConjClasses G → ((⊥ : Ideal A).ResidueField)))
    (c₁ c₂ : ConjClasses G) :
    zero_fiber_lift (A := A) (G := G) e c₁ =
        zero_fiber_lift (A := A) (G := G) e c₂ ↔
      c₁ = c₂ := by
  let E :
      PrimeSpectrum (ConjClasses G → ((⊥ : Ideal A).ResidueField)) ≃o
        PrimeSpectrum (((⊥ : Ideal A).Fiber (A ⊗R(G)))) :=
    (PrimeSpectrum.comapEquiv
      (R := ((⊥ : Ideal A).Fiber (A ⊗R(G))))
      (S := ConjClasses G → ((⊥ : Ideal A).ResidueField))
      e.toRingEquiv).symm
  constructor
  · intro hlift
    -- Injectivity of the transport reduces equality in the bottom fiber to equality of the
    -- underlying coordinate primes in the function ring.
    have heval :
        zeroFiberEvalPrime (A := A) (G := G) c₁ =
          zeroFiberEvalPrime (A := A) (G := G) c₂ := by
      exact E.injective <| by simpa [zero_fiber_lift, E] using hlift
    exact (zeroFiberEvalPrime_eq_iff (A := A) (G := G) c₁ c₂).mp heval
  · intro hc
    -- Equal class parameters yield equal transported coordinate primes by substitution.
    subst hc
    rfl

/-- Helper for Proposition 11-11.4-1: once the bottom fiber is identified with the function ring
on `ConjClasses G`, every bottom-fiber prime is the lift of a coordinate-evaluation prime. -/
theorem zero_fiber_lift_surjective
    (e : ((⊥ : Ideal A).Fiber (A ⊗R(G))) ≃ₐ[((⊥ : Ideal A).ResidueField)]
      (ConjClasses G → ((⊥ : Ideal A).ResidueField))) :
    Function.Surjective (zero_fiber_lift (A := A) (G := G) e) := by
  intro q
  let E :
      PrimeSpectrum (ConjClasses G → ((⊥ : Ideal A).ResidueField)) ≃o
        PrimeSpectrum (((⊥ : Ideal A).Fiber (A ⊗R(G)))) :=
    (PrimeSpectrum.comapEquiv
      (R := ((⊥ : Ideal A).Fiber (A ⊗R(G))))
      (S := ConjClasses G → ((⊥ : Ideal A).ResidueField))
      e.toRingEquiv).symm
  -- Classify the pushed-forward bottom-fiber prime by a coordinate of the function ring.
  obtain ⟨c, hc⟩ :=
    exists_eq_comap_evalRingHom_bot_of_primeSpectrum_conjClasses (G := G) (E.symm q)
  refine ⟨c, ?_⟩
  calc
    zero_fiber_lift (A := A) (G := G) e c = E (zeroFiberEvalPrime (A := A) (G := G) c) := by
      rfl
    _ = E (E.symm q) := by
          simpa [E, zeroFiberEvalPrime] using congrArg E hc
    _ = q := by
          simpa [E] using E.apply_symm_apply q

/-- Helper for Proposition 11-11.4-1: the complex-valued coordinate-evaluation prime at a
conjugacy class in the function ring on `ConjClasses G`. This is the zero-branch prime model that
matches the defining complex evaluation used in `P₀,c`. -/
noncomputable def zeroFiberEvalPrimeComplex
    (c : ConjClasses G) :
    PrimeSpectrum (ConjClasses G → ℂ) :=
  PrimeSpectrum.comap
    (Pi.evalRingHom (fun _ : ConjClasses G ↦ ℂ) c)
    ⟨(⊥ : Ideal ℂ), inferInstance⟩

/-- Helper for Proposition 11-11.4-1: after identifying the bottom fiber with the complex-valued
function ring on `ConjClasses G`, transport the coordinate-evaluation prime at `c` back to the
fiber. This is the source-faithful zero-branch lift matching the ambient owner `P₀,c`. -/
noncomputable def zero_fiber_lift_complex
    (e : ((⊥ : Ideal A).Fiber (A ⊗R(G))) ≃ₐ[((⊥ : Ideal A).ResidueField)]
      (ConjClasses G → ℂ))
    (c : ConjClasses G) :
    PrimeSpectrum (((⊥ : Ideal A).Fiber (A ⊗R(G)))) :=
  (PrimeSpectrum.comapEquiv e.toRingEquiv).symm
    (zeroFiberEvalPrimeComplex (G := G) c)

/-- Helper for Proposition 11-11.4-1: once the bottom fiber is identified with the complex-valued
function ring on `ConjClasses G`, every bottom-fiber prime is the lift of a complex
coordinate-evaluation prime. This is the surjectivity input used to close the zero-contraction
branch without changing the owner `P₀,c`, which is defined via complex evaluation. -/
theorem zero_fiber_lift_complex_surjective
    (e : ((⊥ : Ideal A).Fiber (A ⊗R(G))) ≃ₐ[((⊥ : Ideal A).ResidueField)]
      (ConjClasses G → ℂ)) :
    Function.Surjective (zero_fiber_lift_complex (A := A) (G := G) e) := by
  intro q
  let E :
      PrimeSpectrum (ConjClasses G → ℂ) ≃o
        PrimeSpectrum (((⊥ : Ideal A).Fiber (A ⊗R(G)))) :=
    (PrimeSpectrum.comapEquiv
      (R := ((⊥ : Ideal A).Fiber (A ⊗R(G))))
      (S := ConjClasses G → ℂ)
      e.toRingEquiv).symm
  -- Classify the pushed-forward bottom-fiber prime by a coordinate of the complex function ring.
  obtain ⟨c, hc⟩ :=
    exists_eq_comap_evalRingHom_bot_of_primeSpectrum_conjClasses
      (G := G) (K := ℂ) (E.symm q)
  refine ⟨c, ?_⟩
  calc
    zero_fiber_lift_complex (A := A) (G := G) e c =
        E (zeroFiberEvalPrimeComplex (G := G) c) := by
          rfl
    _ = E (E.symm q) := by
          simpa [E, zeroFiberEvalPrimeComplex] using congrArg E hc
    _ = q := by
          simpa [E] using E.apply_symm_apply q

/-- Helper for Proposition 11-11.4-1: evaluation at a conjugacy class in the bottom-fiber
function ring, followed by the canonical coefficient map to `ℂ`, is an algebra map over
`((0).ResidueField)`. This isolates the scalar-compatibility check for the final zero-fiber
transport. -/
theorem zero_fiber_evalAlgHomToComplex_commutes
    (c : ConjClasses G) (x : ((⊥ : Ideal A).ResidueField)) :
    ((algebraMap ((⊥ : Ideal A).ResidueField) ℂ).comp
      (Pi.evalRingHom (fun _ : ConjClasses G ↦ ((⊥ : Ideal A).ResidueField)) c))
      (algebraMap ((⊥ : Ideal A).ResidueField)
        (ConjClasses G → ((⊥ : Ideal A).ResidueField)) x) =
      algebraMap ((⊥ : Ideal A).ResidueField) ℂ x := by
  -- Evaluating a constant residue-field-valued function returns the chosen scalar.
  rfl

/-- Helper for Proposition 11-11.4-1: evaluation at a fixed conjugacy class in the residue-field
function ring, followed by the canonical map `((0).ResidueField) → ℂ`, is an algebra map over the
bottom residue field. This is the codomain-side map used in the zero-fiber transport. -/
noncomputable def zero_fiber_evalAlgHomToComplex
    (c : ConjClasses G) :
    (ConjClasses G → ((⊥ : Ideal A).ResidueField)) →ₐ[((⊥ : Ideal A).ResidueField)] ℂ :=
  { toRingHom := (algebraMap ((⊥ : Ideal A).ResidueField) ℂ).comp
      (Pi.evalRingHom (fun _ : ConjClasses G ↦ ((⊥ : Ideal A).ResidueField)) c)
    commutes' := zero_fiber_evalAlgHomToComplex_commutes (A := A) (G := G) c
  }

/-- Helper for Proposition 11-11.4-1: after choosing a bottom-fiber equivalence `e`, evaluating
at a conjugacy class and then mapping the residue field into `ℂ` gives the exact transported
`A`-algebra map whose kernel defines the ambient zero-fiber prime. -/
noncomputable def transported_zero_fiber_evalAlgHom
    (e : ((⊥ : Ideal A).Fiber (A ⊗R(G))) ≃ₐ[((⊥ : Ideal A).ResidueField)]
      (ConjClasses G → ((⊥ : Ideal A).ResidueField)))
    (c : ConjClasses G) :
    A ⊗R(G) →ₐ[A] ℂ :=
  (AlgHom.restrictScalars A
      ((zero_fiber_evalAlgHomToComplex (A := A) (G := G) c).comp e.toAlgHom)).comp
    (Algebra.TensorProduct.includeRight
      (R := A) (A := ((⊥ : Ideal A).ResidueField))
      (B := A ⊗R(G)))

/-- Helper for Proposition 11-11.4-1: after identifying the bottom fiber with the function ring
on conjugacy classes, transport the coordinate-evaluation prime back to an ideal of
`A ⊗ R(G)`. -/
noncomputable def transportedZeroFiberEvalPrimeAsIdeal
    (e : ((⊥ : Ideal A).Fiber (A ⊗R(G))) ≃ₐ[((⊥ : Ideal A).ResidueField)]
      (ConjClasses G → ((⊥ : Ideal A).ResidueField)))
    (c : ConjClasses G) : Ideal (A ⊗R(G)) :=
  ((PrimeSpectrum.primesOverOrderIsoFiber A (A ⊗R(G)) (⊥ : Ideal A)).symm
    ((PrimeSpectrum.comapEquiv e.toRingEquiv).symm
      (zeroFiberEvalPrime (A := A) (G := G) c))).1

/-- Helper for Proposition 11-11.4-1: the residue-field-valued transported evaluation map before
postcomposing with the canonical coefficient embedding `((0).ResidueField) → ℂ`. This isolates
the pure bottom-fiber coordinate evaluation from the later comparison with Serre's complex owner
map. -/
noncomputable def transported_zero_fiber_residue_evalRingHom
    (e : ((⊥ : Ideal A).Fiber (A ⊗R(G))) ≃ₐ[((⊥ : Ideal A).ResidueField)]
      (ConjClasses G → ((⊥ : Ideal A).ResidueField)))
    (c : ConjClasses G) :
    A ⊗R(G) →+* ((⊥ : Ideal A).ResidueField) :=
    (((Pi.evalRingHom (fun _ : ConjClasses G ↦ ((⊥ : Ideal A).ResidueField)) c).comp
      e.toRingHom).comp
      (Algebra.TensorProduct.includeRight
        (R := A) (A := ((⊥ : Ideal A).ResidueField))
        (B := A ⊗R(G))).toRingHom)

/-- Helper for Proposition 11-11.4-1: postcomposing the residue-field-valued transported
evaluation map with the canonical embedding `((0).ResidueField) → ℂ` does not change its kernel.
This isolates the easy injectivity step from the still-missing bottom-fiber prime normalization. -/
theorem transported_zero_fiber_evalAlgHom_ker_eq_residue_eval_ker
    (e : ((⊥ : Ideal A).Fiber (A ⊗R(G))) ≃ₐ[((⊥ : Ideal A).ResidueField)]
      (ConjClasses G → ((⊥ : Ideal A).ResidueField)))
    (c : ConjClasses G) :
    RingHom.ker (transported_zero_fiber_evalAlgHom (A := A) (G := G) e c).toRingHom =
      RingHom.ker (transported_zero_fiber_residue_evalRingHom (A := A) (G := G) e c) := by
  -- The only extra map is the injective scalar extension from the residue field into `ℂ`.
  change RingHom.ker
      ((algebraMap ((⊥ : Ideal A).ResidueField) ℂ).comp
        (transported_zero_fiber_residue_evalRingHom (A := A) (G := G) e c)) =
      RingHom.ker (transported_zero_fiber_residue_evalRingHom (A := A) (G := G) e c)
  exact RingHom.ker_comp_of_injective
      (transported_zero_fiber_residue_evalRingHom (A := A) (G := G) e c)
      (algebraMap ((⊥ : Ideal A).ResidueField) ℂ).injective

/-- Helper for Proposition 11-11.4-1: transporting the residue-field coordinate-evaluation prime
back through the bottom-fiber identifications produces the kernel of the corresponding
residue-field-valued evaluation map on `A ⊗ R(G)`. This is the exact structural normalization
needed before comparing with Serre's complex owner map for `P₀,c`. -/
theorem transportedZeroFiberEvalPrimeAsIdeal_eq_ker_residue_evalRingHom
    (e : ((⊥ : Ideal A).Fiber (A ⊗R(G))) ≃ₐ[((⊥ : Ideal A).ResidueField)]
      (ConjClasses G → ((⊥ : Ideal A).ResidueField)))
    (c : ConjClasses G) :
    transportedZeroFiberEvalPrimeAsIdeal (A := A) (G := G) e c =
      RingHom.ker (transported_zero_fiber_residue_evalRingHom (A := A) (G := G) e c) := by
  -- Unfold both transports: `PrimeSpectrum.comapEquiv` turns the coordinate prime into the kernel
  -- of the evaluation map on the fiber, and `PrimeSpectrum.primesOverOrderIsoFiber` then pulls
  -- that kernel back along `includeRight`.
  simp [transportedZeroFiberEvalPrimeAsIdeal, zeroFiberEvalPrime,
    transported_zero_fiber_residue_evalRingHom, PrimeSpectrum.primesOverOrderIsoFiber,
    PrimeSpectrum.preimageOrderIsoFiber, PrimeSpectrum.preimageEquivFiber]
  -- Route correction: proving the kernel/comap identity pointwise avoids the typeclass search
  -- timeout triggered by the generic `RingHom.comap_ker` wrapper here.
  ext x
  simp [RingHom.mem_ker, RingHom.comp_apply]

/-- Helper for Proposition 11-11.4-1: once the transported bottom-fiber evaluation map agrees
with Serre's defining complex evaluation map for `P₀,c`, the corresponding transported
coordinate-evaluation prime is already exactly `P₀,c`. This reduces the remaining zero-fiber
transport blocker to a pointwise equality of `A`-algebra maps. -/
theorem transported_zero_fiber_eval_prime_eq_zero_prime_of_evalAlgHom_eq
    (e : ((⊥ : Ideal A).Fiber (A ⊗R(G))) ≃ₐ[((⊥ : Ideal A).ResidueField)]
      (ConjClasses G → ((⊥ : Ideal A).ResidueField)))
    (c : ConjClasses G)
    (hfg :
      transported_zero_fiber_evalAlgHom (A := A) (G := G) e c =
        { toRingHom := tensorCharacterRingZeroPrimeIdealEval A c
          commutes' := tensorCharacterRingZeroPrimeIdealEval_algebraMap
            (A := A) (G := G) c }) :
    ((PrimeSpectrum.primesOverOrderIsoFiber A (A ⊗R(G)) (⊥ : Ideal A)).symm
      (zero_fiber_lift (A := A) (G := G) e c)).1 =
        (P0 A c).asIdeal := by
  -- Matching the transported evaluation map with Serre's owner map identifies their kernels.
  have hker :
      RingHom.ker (transported_zero_fiber_evalAlgHom (A := A) (G := G) e c).toRingHom =
        RingHom.ker (tensorCharacterRingZeroPrimeIdealEval A c) := by
    rw [show
        (transported_zero_fiber_evalAlgHom (A := A) (G := G) e c).toRingHom =
          tensorCharacterRingZeroPrimeIdealEval A c by
            exact congrArg AlgHom.toRingHom hfg]
  have hresidueKer :
      RingHom.ker (transported_zero_fiber_evalAlgHom (A := A) (G := G) e c).toRingHom =
        RingHom.ker (transported_zero_fiber_residue_evalRingHom (A := A) (G := G) e c) :=
    transported_zero_fiber_evalAlgHom_ker_eq_residue_eval_ker (A := A) (G := G) e c
  have htransported :
      ((PrimeSpectrum.primesOverOrderIsoFiber A (A ⊗R(G)) (⊥ : Ideal A)).symm
        (zero_fiber_lift (A := A) (G := G) e c)).1 =
          RingHom.ker (transported_zero_fiber_residue_evalRingHom (A := A) (G := G) e c) := by
    -- The transported coordinate prime is exactly the structural kernel identified above.
    simpa [zero_fiber_lift] using
      transportedZeroFiberEvalPrimeAsIdeal_eq_ker_residue_evalRingHom
        (A := A) (G := G) e c
  -- With the structural kernel now normalized, the map-equality hypothesis identifies it with the
  -- defining kernel of `P₀,c`.
  calc
    ((PrimeSpectrum.primesOverOrderIsoFiber A (A ⊗R(G)) (⊥ : Ideal A)).symm
      (zero_fiber_lift (A := A) (G := G) e c)).1
        = RingHom.ker (transported_zero_fiber_residue_evalRingHom (A := A) (G := G) e c) :=
          htransported
    _ = RingHom.ker (tensorCharacterRingZeroPrimeIdealEval A c) := by
          exact hresidueKer.symm.trans hker
    _ = (P0 A c).asIdeal := by
          rfl

/-- Helper for Proposition 11-11.4-1: an `A`-algebra map out of `A ⊗ R(G)` is already determined
by its values on the canonical `R(G)`-side generators `1 ⊗ χ`. This isolates the only genuinely
missing zero-branch descent step from the routine tensor-product extensionality. -/
theorem tensorCharacterRing_algHom_ext_of_eq_on_includeRight
    {B : Type*} [CommRing B] [Algebra A B]
    {f g : A ⊗R(G) →ₐ[A] B}
    (hχ : ∀ χ : R(G),
      f ((Algebra.TensorProduct.includeRight (R := ℤ) (A := A) (B := R(G))) χ) =
        g ((Algebra.TensorProduct.includeRight (R := ℤ) (A := A) (B := R(G))) χ)) :
    f = g := by
  -- `A`-algebra maps out of the tensor product are determined by the right-factor generators.
  apply Algebra.TensorProduct.ext_ring
  ext χ
  exact hχ χ

/-- Helper for Proposition 11-11.4-1: to identify the transported zero-fiber evaluation map with
Serre's defining owner map, it suffices to compare them on the `R(G)` generators. This packages
the extensionality reduction so the remaining blocker is a single coefficient-descent statement on
tensor generators. -/
theorem zero_fiber_transport_evalAlgHom_eq_zeroPrimeIdealEval_of_includeRight
    (e : ((⊥ : Ideal A).Fiber (A ⊗R(G))) ≃ₐ[((⊥ : Ideal A).ResidueField)]
      (ConjClasses G → ((⊥ : Ideal A).ResidueField)))
    (c : ConjClasses G)
    (hχ : ∀ χ : R(G),
      transported_zero_fiber_evalAlgHom (A := A) (G := G) e c
          ((Algebra.TensorProduct.includeRight (R := ℤ) (A := A) (B := R(G))) χ) =
        tensorCharacterRingZeroPrimeIdealEval A c
          ((Algebra.TensorProduct.includeRight (R := ℤ) (A := A) (B := R(G))) χ)) :
    transported_zero_fiber_evalAlgHom (A := A) (G := G) e c =
      { toRingHom := tensorCharacterRingZeroPrimeIdealEval A c
        commutes' := tensorCharacterRingZeroPrimeIdealEval_algebraMap
          (A := A) (G := G) c } := by
  -- Both sides are `A`-algebra maps, so tensor-product extensionality reduces the comparison to
  -- the right-factor generators.
  apply tensorCharacterRing_algHom_ext_of_eq_on_includeRight (A := A) (G := G)
  intro χ
  simpa using hχ χ
end
