import Mathlib
import StacksProject_2024.Chap10.Lemma_10_57_8
import StacksProject_2024.Chap10.Definition_10_59_6
import StacksProject_2024.Chap10.Definition_10_59_8
import StacksProject_2024.Chap10.Proposition_10_60_9
import StacksProject_2024.Chap05.Lemma_5_10_2
import StacksProject_2024.Chap10.Lemma_10_114_6

open Filter Ideal HomogeneousIdeal IsLocalRing TopologicalSpace

universe u

noncomputable section

section

variable {k : Type u} [Field k]
variable {S : Type u} [CommRing S] [Algebra k S]
variable (𝒜 : ℕ → Submodule k S) [GradedAlgebra 𝒜]

local notation "S₊" => HomogeneousIdeal.irrelevant 𝒜

/-
Domain-style sampling:
* primary domain: standard graded algebras over a field, their irrelevant maximal ideal, and the
  local Hilbert function and Hilbert-Samuel polynomial of the corresponding local ring;
* sampled owner declarations:
  `minimalPrimes`,
  `Algebra.adjoin`,
  `finiteType_iff_irrelevant_fg`,
  `isHomogeneous_of_mem_minimalPrimes`,
  `Ideal.hilbertSamuelPhi`,
  `hilbertSamuelPolynomialDegree`,
  `topologicalKrullDimAt_closedPoint_eq_ringKrullDim_localizationAtMaximal`;
* best owner abstraction: the source-facing graded-ring input for this lemma is the primitive
  ring-level data `Algebra.adjoin (𝒜 0) (𝒜 1 : Set S) = ⊤`, `Algebra.FiniteType (𝒜 0) S`, and the
  degree-zero identification `k ≃ₐ[k] 𝒜 0`; minimal primes are organized by the owner
  `minimalPrimes S`, and the local Hilbert-function and dimension statements are organized by the
  existing owners `Ideal.hilbertSamuelPhi`, `hilbertSamuelPolynomialDegree`, `MaximalSpectrum`,
  `PrimeSpectrum`, and `Localization.AtPrime`;
* primitive data: generation in degree `1`, finite type over `𝒜 0`, and the canonical degree-zero
  identification `zeroIso : k ≃ₐ[k] 𝒜 0`;
* derived API: finite type over `k`, maximality of the irrelevant ideal, containment of minimal
  primes in that ideal, and the local/global dimension and Hilbert-function comparisons at the
  corresponding canonical point of `MaximalSpectrum S`.

Source/core/bridge triage:
* `source-facing`: the textbook assertions of Lemma `10.117.1`;
* `core/canonical`: `Algebra.adjoin`, `Algebra.FiniteType`, `Ideal.hilbertSamuelPhi`,
  `hilbertSamuelPolynomialDegree`, `topologicalKrullDimAt`, `MaximalSpectrum`, and
  `Localization.AtPrime`;
* `bridge/view`: the finite-type transfer from `𝒜 0` to `k` through `zeroIso`, the canonical
  maximal-spectrum point with underlying ideal `S₊.toIdeal`, and the comparison from the local
  Hilbert function of its localization to the function `d ↦ dimₖ(S_d)`.
-/

/-- Helper for Chap10 Lemma 10 117 1: the irrelevant ideal is the kernel of the projection to the
degree-zero homogeneous summand. -/
private theorem irrelevant_toIdeal_eq_ker_projZero :
    S₊.toIdeal = RingHom.ker (GradedRing.projZeroRingHom' 𝒜) := by
  -- Compare membership in the irrelevant ideal with vanishing of the degree-zero projection.
  ext x
  constructor
  · intro hx
    ext
    simpa [HomogeneousIdeal.mem_irrelevant_iff] using hx
  · intro hx
    rw [HomogeneousIdeal.toIdeal_irrelevant]
    change GradedRing.projZeroRingHom 𝒜 x = 0
    exact congrArg Subtype.val hx

/-- Helper for Chap10 Lemma 10 117 1: an element outside the irrelevant ideal has nonzero
degree-zero projection. -/
private theorem projZero_ne_zero_of_notMem_irrelevant {x : S}
    (hx : x ∉ S₊.toIdeal) :
    GradedRing.projZeroRingHom' 𝒜 x ≠ 0 := by
  -- Use the kernel description to turn nonmembership into a nonzero projection.
  intro hzero
  exact hx (by simpa [irrelevant_toIdeal_eq_ker_projZero (𝒜 := 𝒜)] using hzero)

/-- Derived bridge: finite type over `𝒜 0`, together with the degree-zero identification
`k ≃ₐ[k] 𝒜 0`, canonically yields the finite-type instance `Algebra.FiniteType k S`. -/
theorem finiteType_of_degreeZeroIso
    (hfiniteType : Algebra.FiniteType (𝒜 0) S)
    (zeroIso : k ≃ₐ[k] 𝒜 0) :
    Algebra.FiniteType k S := by
  rw [← RingHom.finiteType_algebraMap]
  have h0S : (algebraMap (𝒜 0) S).FiniteType := by
    rw [RingHom.finiteType_algebraMap]
    exact hfiniteType
  have hk0 : (algebraMap k (𝒜 0)).FiniteType := by
    convert RingHom.FiniteType.of_surjective zeroIso.toAlgHom.toRingHom zeroIso.surjective using 1
    ext r
    simpa using (congrArg (fun x : 𝒜 0 ↦ (x : S)) (zeroIso.commutes r)).symm
  exact RingHom.FiniteType.comp h0S hk0

/-- If the degree-zero piece is identified with the field `k`, then the irrelevant ideal is
maximal. -/
theorem irrelevant_isMaximal
    (zeroIso : k ≃ₐ[k] 𝒜 0) :
    S₊.toIdeal.IsMaximal := by
  -- Identify the irrelevant ideal with the kernel of the projection onto degree zero.
  let f : S →+* 𝒜 0 := GradedRing.projZeroRingHom' 𝒜
  have htarget : IsField (𝒜 0) :=
    zeroIso.symm.toRingEquiv.toMulEquiv.isField (Field.toIsField k)
  have hquot : IsField (S ⧸ RingHom.ker f) :=
    (RingHom.quotientKerEquivOfSurjective (f := f)
      (GradedRing.projZeroRingHom'_surjective 𝒜)).toMulEquiv.isField htarget
  have hker : (RingHom.ker f).IsMaximal :=
    Ideal.Quotient.maximal_of_isField _ hquot
  -- Maximality transports across that kernel identification.
  rw [irrelevant_toIdeal_eq_ker_projZero]
  exact hker

/-- The canonical closed point of `Spec(S)` defined by the irrelevant ideal. -/
abbrev irrelevantClosedPoint
    (zeroIso : k ≃ₐ[k] 𝒜 0) : MaximalSpectrum S :=
  ⟨S₊.toIdeal, irrelevant_isMaximal 𝒜 zeroIso⟩

/-- Every minimal prime of a graded ring is homogeneous. This is the canonical subtype-facing
companion to `isHomogeneous_of_mem_minimalPrimes`. -/
theorem minimalPrime_isHomogeneous
    (p : minimalPrimes S) :
    p.1.IsHomogeneous 𝒜 := by
  simpa using isHomogeneous_of_mem_minimalPrimes 𝒜 p.2

/-- Helper for Chap10 Lemma 10 117 1: a proper homogeneous ideal has zero degree-zero image when
the degree-zero piece is identified with the base field. -/
theorem homogeneousProperIdeal_le_irrelevant_of_degreeZeroIso
    (zeroIso : k ≃ₐ[k] 𝒜 0) {P : Ideal S}
    (hP : P.IsHomogeneous 𝒜) (hPne : P ≠ ⊤) :
    P ≤ S₊.toIdeal := by
  intro x hx
  rw [HomogeneousIdeal.toIdeal_irrelevant]
  change GradedRing.projZeroRingHom 𝒜 x = 0
  let a : 𝒜 0 := GradedRing.projZeroRingHom' 𝒜 x
  -- Homogeneity keeps the degree-zero component of `x` inside `P`.
  have haP : (a : S) ∈ P := by
    exact (hP.mem_iff.mp hx) 0
  have htarget : IsField (𝒜 0) :=
    zeroIso.symm.toRingEquiv.toMulEquiv.isField (Field.toIsField k)
  -- A nonzero degree-zero component would be a unit modulo the field structure, forcing `P = ⊤`.
  by_contra hnonzero
  have ha_ne : a ≠ 0 := by
    intro ha
    exact hnonzero (congrArg Subtype.val ha)
  rcases htarget.mul_inv_cancel ha_ne with ⟨b, hb⟩
  have hmulS : (a : S) * (b : S) = 1 := by
    exact congrArg Subtype.val hb
  have hOneP : (1 : S) ∈ P := by
    rw [← hmulS]
    exact P.mul_mem_right (b : S) haP
  exact hPne ((Ideal.eq_top_iff_one P).mpr hOneP)

/-- If the degree-zero piece is identified with the field `k`, then every minimal prime of `S` is
contained in the irrelevant ideal. Together with `minimalPrime_isHomogeneous`, this is clause `(2)`
of Lemma `10.117.1`. -/
theorem minimalPrime_le_irrelevant
    (zeroIso : k ≃ₐ[k] 𝒜 0)
    (p : minimalPrimes S) :
    p.1 ≤ S₊.toIdeal := by
  -- Minimal primes are homogeneous and proper, so the general homogeneous-ideal helper applies.
  exact homogeneousProperIdeal_le_irrelevant_of_degreeZeroIso (𝒜 := 𝒜) zeroIso
    (minimalPrime_isHomogeneous 𝒜 p) (Ideal.minimalPrimes_isPrime p.2).ne_top

/-- Helper for Chap10 Lemma 10 117 1: if every minimal component contains a closed point, then
the global affine Krull dimension is the local topological dimension at that point. -/
theorem ringKrullDim_eq_topologicalKrullDimAt_of_minimalPrimes_le
    [Algebra.FiniteType k S] (m : MaximalSpectrum S)
    (hmin : ∀ p : minimalPrimes S, p.1 ≤ m.asIdeal) :
    ringKrullDim S = topologicalKrullDimAt m.toPrimeSpectrum := by
  rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim S]
  rw [topologicalKrullDim_eq_iSup_topologicalKrullDimAt]
  refine le_antisymm ?_ ?_
  · refine iSup_le fun x ↦ ?_
    -- Compare local dimensions by the irreducible components through each point.
    rw [topologicalKrullDimAt_eq_iSup_topologicalKrullDim_irreducibleComponents_through
      (S := S) x]
    rw [topologicalKrullDimAt_eq_iSup_topologicalKrullDim_irreducibleComponents_through
      (S := S) m.toPrimeSpectrum]
    refine iSup_le fun Z ↦ ?_
    have hZclosed : IsClosed (Z.1 : Set (PrimeSpectrum S)) :=
      isClosed_of_mem_irreducibleComponents (Z.1 : Set (PrimeSpectrum S)) Z.1.2
    have hZmin : PrimeSpectrum.vanishingIdeal (Z.1 : Set (PrimeSpectrum S)) ∈ minimalPrimes S := by
      rw [PrimeSpectrum.vanishingIdeal_mem_minimalPrimes]
      simpa [hZclosed.closure_eq] using Z.1.2
    -- The minimal-prime containment places the chosen closed point on this component.
    have hmZero : m.toPrimeSpectrum ∈
        PrimeSpectrum.zeroLocus
          (PrimeSpectrum.vanishingIdeal (Z.1 : Set (PrimeSpectrum S)) : Set S) := by
      exact (PrimeSpectrum.mem_zeroLocus m.toPrimeSpectrum
        (PrimeSpectrum.vanishingIdeal (Z.1 : Set (PrimeSpectrum S)) : Set S)).mpr
        (hmin ⟨PrimeSpectrum.vanishingIdeal (Z.1 : Set (PrimeSpectrum S)), hZmin⟩)
    have hmZ : m.toPrimeSpectrum ∈ (Z.1 : Set (PrimeSpectrum S)) := by
      have hzero_eq :
          PrimeSpectrum.zeroLocus
              (PrimeSpectrum.vanishingIdeal (Z.1 : Set (PrimeSpectrum S)) : Set S) =
            (Z.1 : Set (PrimeSpectrum S)) := by
        rw [PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure]
        exact hZclosed.closure_eq
      simpa [hzero_eq] using hmZero
    exact le_iSup_of_le ⟨Z.1, hmZ⟩ le_rfl
  · -- The point `m` itself is one of the local dimensions in the global supremum.
    exact le_iSup (fun x : PrimeSpectrum S ↦ topologicalKrullDimAt x) m.toPrimeSpectrum

/-- If `S` is finite type over `𝒜 0` and `𝒜 0 ≃ k`, then at the closed point of `Spec(S)`
corresponding to the irrelevant ideal, the local dimension equals the global dimension of `S`. -/
theorem ringKrullDim_eq_topologicalKrullDimAt_irrelevant_closedPoint
    (hfiniteType : Algebra.FiniteType (𝒜 0) S)
    (zeroIso : k ≃ₐ[k] 𝒜 0) :
    ringKrullDim S =
      topologicalKrullDimAt (irrelevantClosedPoint 𝒜 zeroIso).toPrimeSpectrum := by
  letI : Algebra.FiniteType k S :=
    finiteType_of_degreeZeroIso 𝒜 hfiniteType zeroIso
  -- All minimal primes lie under the irrelevant closed point by the previous clause.
  exact ringKrullDim_eq_topologicalKrullDimAt_of_minimalPrimes_le
    (k := k) (S := S) (irrelevantClosedPoint 𝒜 zeroIso)
    (fun p ↦ minimalPrime_le_irrelevant 𝒜 zeroIso p)

/-- If `S` is finite type over `𝒜 0` and `𝒜 0 ≃ k`, then the localization of `S` at the
irrelevant ideal `S₊.toIdeal` has the same Krull dimension as `S`. -/
theorem ringKrullDim_eq_ringKrullDim_irrelevant_localization
    (hfiniteType : Algebra.FiniteType (𝒜 0) S)
    (zeroIso : k ≃ₐ[k] 𝒜 0) :
    ringKrullDim S =
      ringKrullDim
        (Localization.AtPrime (irrelevantClosedPoint 𝒜 zeroIso).toPrimeSpectrum.asIdeal) := by
  letI : Algebra.FiniteType k S :=
    finiteType_of_degreeZeroIso 𝒜 hfiniteType zeroIso
  -- First compare global and local topological dimensions, then use the closed-point formula.
  calc
    ringKrullDim S =
        topologicalKrullDimAt (irrelevantClosedPoint 𝒜 zeroIso).toPrimeSpectrum := by
      exact ringKrullDim_eq_topologicalKrullDimAt_irrelevant_closedPoint 𝒜 hfiniteType zeroIso
    _ = ringKrullDim
          (Localization.AtPrime (irrelevantClosedPoint 𝒜 zeroIso).toPrimeSpectrum.asIdeal) := by
      exact topologicalKrullDimAt_closedPoint_eq_ringKrullDim_localizationAtMaximal
        (S := S) (m := irrelevantClosedPoint 𝒜 zeroIso)

/-- Helper for Chap10 Lemma 10 117 1: viewing an ideal multiple of a submodule inside the
ambient module agrees with the intrinsic ideal multiple in the submodule. -/
private theorem smulSubmodule_submoduleOf_eq_smulTop
    (R : Type u) [CommRing R] {M : Type u} [AddCommGroup M] [Module R M]
    (J : Ideal R) (N : Submodule R M) :
    (J • N).submoduleOf N = (J • (⊤ : Submodule R N)) := by
  -- Pull the ambient scalar multiple back along the subtype map of `N`.
  have hrange : N ≤ LinearMap.range N.subtype := by
    simpa [Submodule.range_subtype]
  simpa [Submodule.range_subtype] using
    (Submodule.comap_smul'' (f := N.subtype) N.subtype_injective
      (p := N) (I := J) hrange)

/-- Helper for Chap10 Lemma 10 117 1: the Hilbert-Samuel `φ`-value of a module is the length of
the successive quotient `I^d M / I^(d+1) M`. -/
private theorem hilbertSamuelPhi_eq_length_powSuccQuotient
    (R : Type u) [CommRing R] {M : Type u} [AddCommGroup M] [Module R M]
    (I : Ideal R) (N : Submodule R M) (d : ℕ) :
    φ_ I N d =
      Module.length R
        ((I ^ d • N : Submodule R M) ⧸
          (I ^ (d + 1) • N : Submodule R M).submoduleOf (I ^ d • N)) := by
  let A : Submodule R M := I ^ d • N
  let B : Submodule R M := I ^ (d + 1) • N
  let A₀ : Submodule R N := I ^ d • (⊤ : Submodule R N)
  let D₀ : Submodule R A₀ := I • (⊤ : Submodule R A₀)
  let D₁ : Submodule R (A.submoduleOf N) := I • (⊤ : Submodule R (A.submoduleOf N))
  have hA : A ≤ N := by
    -- Ideal multiples of `N` remain submodules of `N`.
    dsimp [A]
    exact Submodule.smul_le.mpr fun r hr x hx ↦ N.smul_mem r hx
  have hB : B = I • A := by
    -- Passing from `d` to `d + 1` is one further multiplication by `I`.
    dsimp [A, B]
    simp [pow_succ', mul_smul]
  have hnum : A.submoduleOf N = A₀ := by
    -- Reinterpret the ambient submodule `I^d N` intrinsically inside `N`.
    dsimp [A, A₀]
    exact smulSubmodule_submoduleOf_eq_smulTop R (I ^ d) N
  let e₀ : A₀ ≃ₗ[R] A.submoduleOf N := LinearEquiv.ofEq _ _ hnum.symm
  have hmap₀ : D₀.map (e₀ : A₀ →ₗ[R] A.submoduleOf N) = D₁ := by
    -- The equality transport preserves the intrinsic `I`-multiple.
    ext x
    simp [D₀, D₁, e₀]
  let e₁ : A.submoduleOf N ≃ₗ[R] A := Submodule.submoduleOfEquivOfLe hA
  have hmap₁ : D₁.map (e₁ : A.submoduleOf N →ₗ[R] A) = B.submoduleOf A := by
    -- The subtype equivalence sends the intrinsic denominator to the ambient next power.
    calc
      D₁.map (e₁ : A.submoduleOf N →ₗ[R] A) = I • (⊤ : Submodule R A) := by
        dsimp [D₁]
        rw [Submodule.map_smul'', Submodule.map_top,
          LinearMap.range_eq_top.mpr e₁.surjective]
      _ = (I • A).submoduleOf A := by
        exact (smulSubmodule_submoduleOf_eq_smulTop R I A).symm
      _ = B.submoduleOf A := by
        rw [hB]
  -- Transport quotient lengths across the two canonical linear equivalences.
  calc
    φ_ I N d = Module.length R (A₀ ⧸ D₀) := by
      rfl
    _ = Module.length R ((A.submoduleOf N) ⧸ D₁) := by
      simpa [A₀, D₀, D₁] using (Submodule.Quotient.equiv D₀ D₁ e₀ hmap₀).length_eq
    _ = Module.length R (A ⧸ B.submoduleOf A) := by
      simpa [D₁] using (Submodule.Quotient.equiv D₁ (B.submoduleOf A) e₁ hmap₁).length_eq
    _ = Module.length R
          ((I ^ d • N : Submodule R M) ⧸
            (I ^ (d + 1) • N : Submodule R M).submoduleOf (I ^ d • N)) := by
      rfl

/-- Helper for Chap10 Lemma 10 117 1: for the regular module `R`, the Hilbert-Samuel
`φ`-value is the length of the successive quotient `I^d/I^(d+1)`. -/
private theorem hilbertSamuelPhi_eq_length_powSuccQuotient_top
    (R : Type u) [CommRing R] (I : Ideal R) (d : ℕ) :
    φ_ I R d =
      Module.length R
        ((I ^ d • (⊤ : Submodule R R) : Submodule R R) ⧸
          (I ^ (d + 1) • (⊤ : Submodule R R) : Submodule R R).submoduleOf
            (I ^ d • (⊤ : Submodule R R))) := by
  let A : Submodule R R := I ^ d • (⊤ : Submodule R R)
  let B : Submodule R R := I ^ (d + 1) • (⊤ : Submodule R R)
  have hden :
      I • (⊤ : Submodule R A) = B.submoduleOf A := by
    -- The denominator in the owner definition is exactly the next ideal power inside `I^d`.
    simpa [A, B, pow_succ', mul_smul] using
      (smulSubmodule_submoduleOf_eq_smulTop R I A).symm
  -- Unfold `φ` only after the quotient denominator has a stable named normal form.
  rw [Ideal.hilbertSamuelPhi]
  dsimp [A]
  rw [hden]
  rfl

/-- Helper for Chap10 Lemma 10 117 1: generation in degree one identifies the span of the
degree-one piece with the irrelevant ideal. -/
private theorem span_degreeOne_eq_irrelevant_of_adjoin_eq_top
    (hgenerated : Algebra.adjoin (𝒜 0) (𝒜 1 : Set S) = ⊤) :
    Ideal.span (𝒜 1 : Set S) = S₊.toIdeal := by
  -- The project lemma converts degree-one algebra generation into the irrelevant-ideal span.
  have hdegree :
      ∀ ⦃x : S⦄, x ∈ (𝒜 1 : Set S) → ∃ n > 0, x ∈ 𝒜 n := by
    intro x hx
    exact ⟨1, by decide, hx⟩
  exact (homogeneous_adjoin_eq_top_iff_span_eq_irrelevant
    𝒜 (𝒜 1 : Set S) hdegree).1 hgenerated

/-- Helper for Chap10 Lemma 10 117 1: every power of a homogeneous ideal is homogeneous. -/
private theorem homogeneousIdeal_pow_isHomogeneous
    (I : HomogeneousIdeal 𝒜) (n : ℕ) :
    (I.toIdeal ^ n).IsHomogeneous 𝒜 := by
  induction n with
  | zero =>
      -- The zeroth power is `⊤`, which is homogeneous for any grading.
      simpa using (Ideal.IsHomogeneous.top (𝒜 := 𝒜))
  | succ n ih =>
      -- Multiplying the previous homogeneous power by the homogeneous ideal preserves
      -- homogeneity.
      simpa [pow_succ] using Ideal.IsHomogeneous.mul (𝒜 := 𝒜) ih I.isHomogeneous

/-- Helper for Chap10 Lemma 10 117 1: an element of a power of a homogeneous ideal contained in
the irrelevant ideal has no components below that power. -/
private theorem decompose_pow_mem_eq_zero_of_lt
    (I : HomogeneousIdeal 𝒜)
    (hI : I ≤ S₊)
    {n j : ℕ} {r : S}
    (hr : r ∈ I.toIdeal ^ n)
    (hj : j < n) :
    ((DirectSum.decompose 𝒜 r j : 𝒜 j) : S) = 0 := by
  classical
  have hvanish :
      ∀ {m : ℕ} {x : S}, x ∈ I.toIdeal ^ m →
        ∀ t < m, ((DirectSum.decompose 𝒜 x t : 𝒜 t) : S) = 0 := by
    intro m x hx
    refine Submodule.pow_induction_on_left'
        (M := I.toIdeal)
        (C := fun m x _ =>
          ∀ t < m, ((DirectSum.decompose 𝒜 x t : 𝒜 t) : S) = 0) ?_ ?_ ?_ hx
    · intro a t ht
      exact (Nat.not_lt_zero _ ht).elim
    · intro x y m hx hy hx_zero hy_zero t ht
      -- Components are additive, so vanishing is stable under addition in the power.
      simpa [DirectSum.decompose_add, hx_zero t ht, hy_zero t ht]
    · intro a ha m x hx hx_zero t ht
      have ha_zero :
          ((DirectSum.decompose 𝒜 a 0 : 𝒜 0) : S) = 0 := by
        -- Containment in the irrelevant ideal says precisely that the degree-zero component
        -- vanishes.
        have ha_irrelevant : a ∈ S₊ := hI ha
        have hproj0 : GradedRing.proj 𝒜 0 a = 0 := by
          simpa [HomogeneousIdeal.mem_irrelevant_iff] using ha_irrelevant
        simpa [GradedRing.proj_apply] using hproj0
      -- Expand the left factor into homogeneous components. Degree zero vanishes by
      -- irrelevance, while positive components shift the right factor below its induction
      -- cutoff.
      rw [← DirectSum.sum_support_decompose 𝒜 a, Finset.sum_mul, DirectSum.decompose_sum]
      have hsum_zero :
          (∑ i ∈ (DirectSum.decompose 𝒜 a).support,
              (DirectSum.decompose 𝒜
                ((((DirectSum.decompose 𝒜 a) i : 𝒜 i) : S) * x) t : 𝒜 t)) = 0 := by
        refine Finset.sum_eq_zero ?_
        intro i hi
        by_cases hi0 : i = 0
        · subst hi0
          apply Subtype.ext
          simpa [ha_zero]
        · by_cases hit : i ≤ t
          · have hlt : t - i < m := by
              omega
            apply Subtype.ext
            rw [DirectSum.coe_decompose_mul_of_left_mem_of_le (𝒜 := 𝒜)
              (a := (((DirectSum.decompose 𝒜 a i : 𝒜 i) : S))) (b := x)
              (i := i) (n := t) (a_mem := SetLike.coe_mem _) hit]
            simp [hx_zero (t - i) hlt]
          · apply Subtype.ext
            simpa using
              (DirectSum.coe_decompose_mul_of_left_mem_of_not_le (𝒜 := 𝒜)
                (a := (((DirectSum.decompose 𝒜 a i : 𝒜 i) : S))) (b := x)
                (i := i) (n := t) (a_mem := SetLike.coe_mem _) hit)
      simpa using congrArg (fun z : 𝒜 t ↦ (z : S)) hsum_zero
  exact hvanish hr j hj

/-- Helper for Chap10 Lemma 10 117 1: powers of the irrelevant ideal have zero low-degree
components. -/
private theorem mem_irrelevantPow_lowDegreeComponents_eq_zero
    {n : ℕ} {x : S}
    (hx : x ∈ S₊.toIdeal ^ n) :
    ∀ j < n, ((DirectSum.decompose 𝒜 x j : 𝒜 j) : S) = 0 := by
  -- Apply the homogeneous-power vanishing lemma to the irrelevant ideal itself.
  intro j hj
  exact decompose_pow_mem_eq_zero_of_lt (𝒜 := 𝒜) S₊ (fun _ h ↦ h) hx hj

/-- Helper for Chap10 Lemma 10 117 1: under degree-one generation, a homogeneous element of
degree at least `n` lies in the `n`th power of the irrelevant ideal. -/
private theorem homogeneous_mem_irrelevantPow_of_le_degree
    (hspan : Ideal.span (𝒜 1 : Set S) = S₊.toIdeal)
    {n m : ℕ} {x : S}
    (hnm : n ≤ m) (hx : x ∈ 𝒜 m) :
    x ∈ S₊.toIdeal ^ n := by
  classical
  -- Induct on the required power. The successor step writes a homogeneous element as a sum of
  -- degree-one generators times lower-degree coefficients and applies the induction hypothesis to
  -- the homogeneous coefficient of degree one less.
  induction n generalizing m x with
  | zero =>
      simpa using (show x ∈ (⊤ : Ideal S) from trivial)
  | succ n ih =>
      cases m with
      | zero =>
          omega
      | succ m =>
          have hnm' : n ≤ m := Nat.succ_le_succ_iff.mp hnm
          have hx_span : x ∈ Ideal.span (𝒜 1 : Set S) := by
            rw [hspan]
            exact mem_irrelevant_of_mem 𝒜 (Nat.succ_pos m) hx
          rw [Ideal.span, Finsupp.span_eq_range_linearCombination] at hx_span
          rw [LinearMap.mem_range] at hx_span
          obtain ⟨l, rfl⟩ := hx_span
          have hproj :
              GradedRing.proj 𝒜 (m + 1)
                  (Finsupp.linearCombination S (fun z : (𝒜 1 : Set S) ↦ (z : S)) l) =
                Finsupp.linearCombination S (fun z : (𝒜 1 : Set S) ↦ (z : S)) l := by
            -- The original element is homogeneous of degree `m + 1`, so projection to that degree
            -- fixes the chosen span expression.
            rw [GradedRing.proj_apply, DirectSum.decompose_of_mem_same 𝒜 hx]
          rw [← hproj, Finsupp.linearCombination_apply, Finsupp.sum, map_sum]
          refine Ideal.sum_mem _ fun z _ ↦ ?_
          have hz_irrelevant : (z : S) ∈ S₊.toIdeal := by
            rw [← hspan]
            exact Ideal.subset_span z.2
          have hz_degree : (z : S) ∈ 𝒜 1 := z.2
          rw [smul_eq_mul, GradedRing.proj_apply,
            DirectSum.coe_decompose_mul_of_right_mem_of_le (𝒜 := 𝒜)
              (a := l z) (b := (z : S)) (i := 1) (n := m + 1)
              (b_mem := hz_degree) (by omega)]
          have hcoeff :
              ((DirectSum.decompose 𝒜 (l z) m : 𝒜 m) : S) ∈ S₊.toIdeal ^ n := by
            exact ih hnm' (SetLike.coe_mem _)
          have hmul :
              (z : S) * ((DirectSum.decompose 𝒜 (l z) m : 𝒜 m) : S) ∈
                S₊.toIdeal * S₊.toIdeal ^ n :=
            Ideal.mul_mem_mul hz_irrelevant hcoeff
          simpa [pow_succ, mul_comm] using hmul

/-- Helper for Chap10 Lemma 10 117 1: under degree-one generation, the degree-`d` piece maps
into the `d`th irrelevant-power filtration step. -/
private theorem degreePiece_mem_irrelevantPow_of_span_degreeOne
    (hspan : Ideal.span (𝒜 1 : Set S) = S₊.toIdeal)
    (d : ℕ) (x : 𝒜 d) :
    (x : S) ∈ S₊.toIdeal ^ d := by
  -- Specialize the high-degree membership helper to equal degrees.
  exact homogeneous_mem_irrelevantPow_of_le_degree (𝒜 := 𝒜) hspan le_rfl x.2

/-- Helper for Chap10 Lemma 10 117 1: modulo the next irrelevant-power step, an element in
`S₊^d` is represented by its degree-`d` component. -/
private theorem degreeComponent_congr_mod_irrelevantPow_succ
    (hspan : Ideal.span (𝒜 1 : Set S) = S₊.toIdeal)
    {d : ℕ} {x : S} (hx : x ∈ S₊.toIdeal ^ d) :
    x - ((DirectSum.decompose 𝒜 x d : 𝒜 d) : S) ∈ S₊.toIdeal ^ (d + 1) := by
  classical
  let x_d : S := ((DirectSum.decompose 𝒜 x d : 𝒜 d) : S)
  have htargetHomogeneous :
      (S₊.toIdeal ^ (d + 1)).IsHomogeneous 𝒜 :=
    homogeneousIdeal_pow_isHomogeneous (𝒜 := 𝒜) S₊ (d + 1)
  -- Since the target ideal is homogeneous, it is enough to check each component separately.
  refine htargetHomogeneous.mem_iff.mpr ?_
  intro j
  by_cases hjlt : j < d
  · have hxj :
        ((DirectSum.decompose 𝒜 x j : 𝒜 j) : S) = 0 :=
      mem_irrelevantPow_lowDegreeComponents_eq_zero (𝒜 := 𝒜) hx j hjlt
    have hxdj :
        ((DirectSum.decompose 𝒜 x_d j : 𝒜 j) : S) = 0 := by
      exact DirectSum.decompose_of_mem_ne 𝒜
        (SetLike.coe_mem (DirectSum.decompose 𝒜 x d : 𝒜 d)) (Nat.ne_of_gt hjlt)
    have hyj :
        ((DirectSum.decompose 𝒜 (x - x_d) j : 𝒜 j) : S) = 0 := by
      simpa [DirectSum.decompose_sub, hxj, hxdj]
    -- Low components vanish, hence lie in every ideal.
    rw [hyj]
    exact Ideal.zero_mem _
  · by_cases hj : j = d
    · subst j
      have hxdj :
          ((DirectSum.decompose 𝒜 x_d d : 𝒜 d) : S) =
            ((DirectSum.decompose 𝒜 x d : 𝒜 d) : S) := by
        exact DirectSum.decompose_of_mem_same 𝒜
          (SetLike.coe_mem (DirectSum.decompose 𝒜 x d : 𝒜 d))
      have hyj :
          ((DirectSum.decompose 𝒜 (x - x_d) d : 𝒜 d) : S) = 0 := by
        simpa [DirectSum.decompose_sub, x_d, hxdj]
      -- The degree-`d` component cancels by construction.
      rw [hyj]
      exact Ideal.zero_mem _
    · have hd_ne_j : d ≠ j := fun h ↦ hj h.symm
      have hdj : d < j := lt_of_le_of_ne (le_of_not_gt hjlt) hd_ne_j
      have hxdj :
          ((DirectSum.decompose 𝒜 x_d j : 𝒜 j) : S) = 0 := by
        exact DirectSum.decompose_of_mem_ne 𝒜
          (SetLike.coe_mem (DirectSum.decompose 𝒜 x d : 𝒜 d)) hd_ne_j
      have hyj :
          ((DirectSum.decompose 𝒜 (x - x_d) j : 𝒜 j) : S) =
            ((DirectSum.decompose 𝒜 x j : 𝒜 j) : S) := by
        simpa [DirectSum.decompose_sub, hxdj]
      -- Components of degree strictly above `d` lie in `S₊^(d+1)` by generation in degree one.
      rw [hyj]
      exact homogeneous_mem_irrelevantPow_of_le_degree (𝒜 := 𝒜) hspan
        (Nat.succ_le_of_lt hdj) (SetLike.coe_mem (DirectSum.decompose 𝒜 x j : 𝒜 j))

/-- Helper for Chap10 Lemma 10 117 1: powers of the maximal ideal in the localization at the
irrelevant closed point are the localizations of the corresponding irrelevant-ideal powers. -/
private theorem localPow_eq_localized_irrelevantPow
    (zeroIso : k ≃ₐ[k] 𝒜 0) (n : ℕ) :
    let P := (irrelevantClosedPoint 𝒜 zeroIso).toPrimeSpectrum.asIdeal
    let I : Ideal (Localization.AtPrime P) := maximalIdeal (Localization.AtPrime P)
    (S₊.toIdeal ^ n • (⊤ : Submodule S S)).localized P.primeCompl =
      I ^ n • (⊤ : Submodule (Localization.AtPrime P) (Localization.AtPrime P)) := by
  let P := (irrelevantClosedPoint 𝒜 zeroIso).toPrimeSpectrum.asIdeal
  letI : P.IsPrime := by
    dsimp [P]
    exact (irrelevantClosedPoint 𝒜 zeroIso).toPrimeSpectrum.isPrime
  let I : Ideal (Localization.AtPrime P) := maximalIdeal (Localization.AtPrime P)
  have hP : S₊.toIdeal = P := rfl
  -- Push localization through the ideal multiple and rewrite the localized ideal as the maximal
  -- ideal of `S₊`'s local ring.
  dsimp only
  rw [Submodule.localized, Submodule.localized'_smul, Ideal.localized'_eq_map, Ideal.map_pow, hP,
    Localization.AtPrime.map_eq_maximalIdeal, Submodule.localized'_top]

/-- Helper for Chap10 Lemma 10 117 1: a degree-`d` element dies in the next irrelevant-power
filtration step only when it is zero. -/
private theorem degreePiece_mem_irrelevantPow_succ_iff_eq_zero
    (d : ℕ) (x : 𝒜 d) :
    (x : S) ∈ S₊.toIdeal ^ (d + 1) ↔ x = 0 := by
  constructor
  · intro hx
    -- Low-degree vanishing at degree `d` forces the homogeneous representative itself to vanish.
    have hzero :=
      mem_irrelevantPow_lowDegreeComponents_eq_zero (𝒜 := 𝒜) hx d (Nat.lt_succ_self d)
    apply Subtype.ext
    simpa [DirectSum.decompose_of_mem_same 𝒜 x.2] using hzero
  · intro hx
    -- The zero element belongs to every ideal power.
    rw [hx]
    exact Ideal.zero_mem _

/-- Helper for Chap10 Lemma 10 117 1: multiplying a degree-`d` element by `a` is congruent
modulo the next irrelevant-power step to multiplying by the degree-zero part of `a`. -/
private theorem degreePiece_mul_congr_projZero
    (hspan : Ideal.span (𝒜 1 : Set S) = S₊.toIdeal)
    {d : ℕ} (a : S) (x : 𝒜 d) :
    a * (x : S) - ((GradedRing.projZeroRingHom' 𝒜 a : 𝒜 0) : S) * (x : S) ∈
      S₊.toIdeal ^ (d + 1) := by
  let a₀ : S := ((GradedRing.projZeroRingHom' 𝒜 a : 𝒜 0) : S)
  -- Removing the degree-zero part puts the multiplier in the irrelevant ideal.
  have ha₀ : a - a₀ ∈ S₊.toIdeal := by
    rw [irrelevant_toIdeal_eq_ker_projZero (𝒜 := 𝒜)]
    apply Subtype.ext
    simp [a₀]
  have hxpow : (x : S) ∈ S₊.toIdeal ^ d :=
    degreePiece_mem_irrelevantPow_of_span_degreeOne (𝒜 := 𝒜) hspan d x
  -- The irrelevant multiplier times a degree-`d` element lands in `S₊ * S₊^d`.
  have hmul :
      (a - a₀) * (x : S) ∈ S₊.toIdeal * S₊.toIdeal ^ d :=
    Ideal.mul_mem_mul ha₀ hxpow
  have hpow : (a - a₀) * (x : S) ∈ S₊.toIdeal ^ (d + 1) := by
    simpa [pow_succ'] using hmul
  simpa [a₀, sub_mul] using hpow

/-- Helper for Chap10 Lemma 10 117 1: the residue ring of the localization at the irrelevant
closed point is equivalent to the base field through the degree-zero projection. -/
private theorem irrelevantLocalization_residueRingEquiv_nonempty
    (zeroIso : k ≃ₐ[k] 𝒜 0) :
    Nonempty
      ((Localization.AtPrime (irrelevantClosedPoint 𝒜 zeroIso).toPrimeSpectrum.asIdeal ⧸
          maximalIdeal
            (Localization.AtPrime (irrelevantClosedPoint 𝒜 zeroIso).toPrimeSpectrum.asIdeal)) ≃+*
        k) := by
  let P := (irrelevantClosedPoint 𝒜 zeroIso).toPrimeSpectrum.asIdeal
  letI : P.IsPrime := by
    dsimp [P]
    exact (irrelevantClosedPoint 𝒜 zeroIso).toPrimeSpectrum.isPrime
  letI : P.IsMaximal := by
    dsimp [P]
    simpa using (irrelevantClosedPoint 𝒜 zeroIso).isMaximal
  have hPker : P = RingHom.ker (GradedRing.projZeroRingHom' 𝒜) := by
    -- The closed point is defined by `S₊`, and `S₊` is the kernel of projection to degree zero.
    dsimp [P]
    exact irrelevant_toIdeal_eq_ker_projZero (𝒜 := 𝒜)
  let eLoc : S ⧸ P ≃+*
      Localization.AtPrime P ⧸ maximalIdeal (Localization.AtPrime P) :=
    IsLocalization.AtPrime.equivQuotMaximalIdeal P (Localization.AtPrime P)
  let eDegZero : S ⧸ P ≃+* 𝒜 0 :=
    (Ideal.quotEquivOfEq hPker).trans
      (RingHom.quotientKerEquivOfSurjective
        (f := GradedRing.projZeroRingHom' 𝒜)
        (GradedRing.projZeroRingHom'_surjective 𝒜))
  -- Compose the localization quotient comparison with the degree-zero quotient and `zeroIso`.
  exact ⟨eLoc.symm.trans (eDegZero.trans zeroIso.symm.toRingEquiv)⟩

/-- Helper for Chap10 Lemma 10 117 1: the residue equivalence from the irrelevant localization
computes on localization fractions by projecting numerator and denominator to degree zero. -/
private theorem exists_irrelevantLocalization_residueRingEquiv_apply_mk'
    (zeroIso : k ≃ₐ[k] 𝒜 0) :
    let P := (irrelevantClosedPoint 𝒜 zeroIso).toPrimeSpectrum.asIdeal
    let Rloc := Localization.AtPrime P
    let I : Ideal Rloc := maximalIdeal Rloc
    ∃ eRes : (Rloc ⧸ I) ≃+* k,
      ∀ (a : S) (s : P.primeCompl),
        eRes (Ideal.Quotient.mk I (IsLocalization.mk' Rloc a s)) =
          zeroIso.symm (GradedRing.projZeroRingHom' 𝒜 a) /
            zeroIso.symm (GradedRing.projZeroRingHom' 𝒜 (s : S)) := by
  let P := (irrelevantClosedPoint 𝒜 zeroIso).toPrimeSpectrum.asIdeal
  letI : P.IsPrime := by
    dsimp [P]
    exact (irrelevantClosedPoint 𝒜 zeroIso).toPrimeSpectrum.isPrime
  letI : P.IsMaximal := by
    dsimp [P]
    simpa using (irrelevantClosedPoint 𝒜 zeroIso).isMaximal
  let Rloc := Localization.AtPrime P
  let I : Ideal Rloc := maximalIdeal Rloc
  have hPker : P = RingHom.ker (GradedRing.projZeroRingHom' 𝒜) := by
    -- The closed point is defined by `S₊`, and `S₊` is the kernel of projection to degree zero.
    dsimp [P]
    exact irrelevant_toIdeal_eq_ker_projZero (𝒜 := 𝒜)
  letI : Field (S ⧸ P) := Ideal.Quotient.field P
  have hkerMax : (RingHom.ker (GradedRing.projZeroRingHom' 𝒜)).IsMaximal := by
    rw [← hPker]
    infer_instance
  letI : (RingHom.ker (GradedRing.projZeroRingHom' 𝒜)).IsMaximal := hkerMax
  letI : Field (S ⧸ RingHom.ker (GradedRing.projZeroRingHom' 𝒜)) :=
    Ideal.Quotient.field _
  have htarget : IsField (𝒜 0) :=
    zeroIso.symm.toRingEquiv.toMulEquiv.isField (Field.toIsField k)
  letI : Field (𝒜 0) := htarget.toField
  let eLoc : S ⧸ P ≃+* Rloc ⧸ I :=
    IsLocalization.AtPrime.equivQuotMaximalIdeal P Rloc
  let eDegZero : S ⧸ P ≃+* 𝒜 0 :=
    (Ideal.quotEquivOfEq hPker).trans
      (RingHom.quotientKerEquivOfSurjective
        (f := GradedRing.projZeroRingHom' 𝒜)
        (GradedRing.projZeroRingHom'_surjective 𝒜))
  let eRes : Rloc ⧸ I ≃+* k :=
    eLoc.symm.trans (eDegZero.trans zeroIso.symm.toRingEquiv)
  refine ⟨eRes, ?_⟩
  intro a s
  -- First move the localized fraction back to `S ⧸ P`, then use the projection-kernel quotient.
  dsimp [eRes, eLoc, eDegZero]
  rw [IsLocalization.AtPrime.equivQuotMaximalIdeal_symm_apply_mk]
  rw [map_mul, map_inv₀, map_mul, map_inv₀]
  rw [Ideal.quotEquivOfEq_mk, Ideal.quotEquivOfEq_mk]
  simp [div_eq_mul_inv]
  rfl

/-- Helper for Chap10 Lemma 10 117 1: the quotient `I^d/I^(d+1)` is killed by `I`. -/
private theorem ideal_smul_successiveQuotient_eq_bot
    (R : Type u) [CommRing R] (I : Ideal R) (d : ℕ) :
    I • (⊤ : Submodule R
      ((I ^ d • (⊤ : Submodule R R) : Submodule R R) ⧸
        (I ^ (d + 1) • (⊤ : Submodule R R) : Submodule R R).submoduleOf
          (I ^ d • (⊤ : Submodule R R) : Submodule R R))) = ⊥ := by
  -- It suffices to show that every scalar in `I` annihilates every quotient class.
  rw [← Submodule.le_annihilator_iff, Submodule.annihilator_top]
  intro r hr
  rw [Module.mem_annihilator]
  intro q
  refine Submodule.Quotient.induction_on _ q ?_
  intro a
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  change (r • (a : R)) ∈ I ^ (d + 1) • (⊤ : Submodule R R)
  -- Multiplying a representative from `I^d` by an element of `I` lands in `I^(d+1)`.
  have hmem : r • (a : R) ∈ I • (I ^ d • (⊤ : Submodule R R)) :=
    Submodule.smul_mem_smul hr a.2
  simpa [pow_succ', mul_smul] using hmem

/-- Helper for Chap10 Lemma 10 117 1: if all denominators act invertibly, then the identity map
already satisfies the localized-module universal property. -/
private theorem isLocalizedModule_id_of_invertibleScalars
    (R : Type u) [CommRing R] (T : Submonoid R)
    {M : Type u} [AddCommGroup M] [Module R M]
    (hM : ∀ t : T, IsUnit (algebraMap R (Module.End R M) t)) :
    IsLocalizedModule T (LinearMap.id : M →ₗ[R] M) where
  map_units := hM
  surj m := by
    -- Every element is represented with denominator `1` because the map is the identity.
    exact ⟨(m, 1), by simp⟩
  exists_of_eq h := by
    -- Equality before localization is witnessed by the unit denominator `1`.
    exact ⟨1, by simpa using h⟩

/-- Helper for Chap10 Lemma 10 117 1: on a module killed by a maximal ideal, every element outside
that ideal acts invertibly. -/
private theorem isUnit_scalar_of_isMaximal_smul_top_eq_bot
    (R : Type u) [CommRing R] {m : Ideal R} (hm : m.IsMaximal)
    {M : Type u} [AddCommGroup M] [Module R M]
    (hkill : m • (⊤ : Submodule R M) = ⊥) (s : m.primeCompl) :
    IsUnit (algebraMap R (Module.End R M) (s : R)) := by
  rcases hm.exists_inv s.2 with ⟨a, i, hi, hai⟩
  have hi_smul : ∀ x : M, i • x = 0 := by
    intro x
    have hxmem : i • x ∈ m • (⊤ : Submodule R M) :=
      Submodule.smul_mem_smul hi trivial
    have hxbot : i • x ∈ (⊥ : Submodule R M) := by
      simpa [hkill] using hxmem
    simpa using hxbot
  have hleft : ∀ x : M, (a * (s : R)) • x = x := by
    intro x
    have h := congrArg (fun r : R ↦ r • x) hai
    simpa [add_smul, hi_smul x] using h
  -- The Bezout inverse supplied by maximality gives an inverse to scalar multiplication by `s`.
  refine (Module.End.isUnit_iff _).mpr ⟨?_, ?_⟩
  · intro x y hxy
    have h := congrArg (fun z : M ↦ a • z) hxy
    simpa [Module.algebraMap_end_apply, smul_smul, mul_comm, hleft] using h
  · intro x
    refine ⟨a • x, ?_⟩
    simpa [Module.algebraMap_end_apply, smul_smul, mul_comm, hleft] using hleft x

/-- Helper for Chap10 Lemma 10 117 1: the global quotient `S₊^d/S₊^(d+1)` is unchanged by
localization at the irrelevant maximal ideal, as an `S`-localized module. -/
private theorem globalIrrelevantPowQuotient_isLocalizedModule_id
    (zeroIso : k ≃ₐ[k] 𝒜 0) (d : ℕ) :
    let P := (irrelevantClosedPoint 𝒜 zeroIso).toPrimeSpectrum.asIdeal
    IsLocalizedModule P.primeCompl
      (LinearMap.id :
        ((S₊.toIdeal ^ d • (⊤ : Submodule S S) : Submodule S S) ⧸
          (S₊.toIdeal ^ (d + 1) • (⊤ : Submodule S S) : Submodule S S).submoduleOf
            (S₊.toIdeal ^ d • (⊤ : Submodule S S) : Submodule S S)) →ₗ[S]
        ((S₊.toIdeal ^ d • (⊤ : Submodule S S) : Submodule S S) ⧸
          (S₊.toIdeal ^ (d + 1) • (⊤ : Submodule S S) : Submodule S S).submoduleOf
            (S₊.toIdeal ^ d • (⊤ : Submodule S S) : Submodule S S))) := by
  let P := (irrelevantClosedPoint 𝒜 zeroIso).toPrimeSpectrum.asIdeal
  let G : Type u :=
    (S₊.toIdeal ^ d • (⊤ : Submodule S S) : Submodule S S) ⧸
      (S₊.toIdeal ^ (d + 1) • (⊤ : Submodule S S) : Submodule S S).submoduleOf
        (S₊.toIdeal ^ d • (⊤ : Submodule S S) : Submodule S S)
  have hPmax : P.IsMaximal := by
    dsimp [P]
    simpa using (irrelevantClosedPoint 𝒜 zeroIso).isMaximal
  have hkill : P • (⊤ : Submodule S G) = ⊥ := by
    -- The global associated-graded quotient is killed by one multiplication by the irrelevant
    -- ideal.
    simpa [P, G] using ideal_smul_successiveQuotient_eq_bot S S₊.toIdeal d
  -- Elements outside the maximal ideal act invertibly, so the identity is the localization map.
  exact isLocalizedModule_id_of_invertibleScalars S P.primeCompl
    (isUnit_scalar_of_isMaximal_smul_top_eq_bot S hPmax hkill)

/-- Helper for Chap10 Lemma 10 117 1: before localization, the quotient
`S₊^d/S₊^(d+1)` is the same `k`-vector space as the degree-`d` summand. -/
private theorem globalIrrelevantPowQuotient_linearEquiv_degreePiece
    (hspan : Ideal.span (𝒜 1 : Set S) = S₊.toIdeal) (d : ℕ) :
    Nonempty
      (((S₊.toIdeal ^ d • (⊤ : Submodule S S) : Submodule S S) ⧸
          (S₊.toIdeal ^ (d + 1) • (⊤ : Submodule S S) : Submodule S S).submoduleOf
            (S₊.toIdeal ^ d • (⊤ : Submodule S S) : Submodule S S)) ≃ₗ[k]
        𝒜 d) := by
  let Gnum : Submodule S S := S₊.toIdeal ^ d • (⊤ : Submodule S S)
  let Gden : Submodule S Gnum :=
    (S₊.toIdeal ^ (d + 1) • (⊤ : Submodule S S) : Submodule S S).submoduleOf Gnum
  let toQuot : 𝒜 d →ₗ[k] Gnum ⧸ Gden :=
    { toFun := fun x ↦
        Submodule.Quotient.mk
          (⟨(x : S), by
            -- Degree-`d` homogeneous elements lie in the `d`th irrelevant-power step.
            simpa [Gnum, Ideal.smul_eq_mul, Ideal.mul_top] using
              degreePiece_mem_irrelevantPow_of_span_degreeOne (𝒜 := 𝒜) hspan d x⟩ : Gnum)
      map_add' := by
        intro x y
        rfl
      map_smul' := by
        intro c x
        rfl }
  have hker : Function.Injective toQuot := by
    intro x y hxy
    have hdiff_mem :
        ((x - y : 𝒜 d) : S) ∈ S₊.toIdeal ^ (d + 1) := by
      have hquot :
          (Submodule.Quotient.mk
            (⟨((x - y : 𝒜 d) : S), by
              -- The source is a submodule, so differences of degree-`d` elements remain in
              -- the numerator filtration step.
              simpa [Gnum, Ideal.smul_eq_mul, Ideal.mul_top] using
                degreePiece_mem_irrelevantPow_of_span_degreeOne
                  (𝒜 := 𝒜) hspan d (x - y)⟩ : Gnum) :
              Gnum ⧸ Gden) = 0 := by
        -- Injectivity of the quotient map reduces to membership in the denominator.
        change toQuot (x - y) = 0
        rw [map_sub, hxy, sub_self]
      have hden :
          (⟨((x - y : 𝒜 d) : S), by
            simpa [Gnum, Ideal.smul_eq_mul, Ideal.mul_top] using
              degreePiece_mem_irrelevantPow_of_span_degreeOne
                (𝒜 := 𝒜) hspan d (x - y)⟩ : Gnum) ∈ Gden :=
        (Submodule.Quotient.mk_eq_zero Gden).mp hquot
      simpa [Gden, Ideal.smul_eq_mul, Ideal.mul_top] using hden
    have hzero :
        x - y = 0 :=
      (degreePiece_mem_irrelevantPow_succ_iff_eq_zero (𝒜 := 𝒜) d (x - y)).mp hdiff_mem
    exact sub_eq_zero.mp hzero
  have hsurj : Function.Surjective toQuot := by
    intro q
    refine Submodule.Quotient.induction_on (p := Gden) (x := q) ?_
    intro y
    let yd : 𝒜 d := DirectSum.decompose 𝒜 (y : S) d
    refine ⟨yd, ?_⟩
    have hy : (y : S) ∈ S₊.toIdeal ^ d := by
      -- A quotient representative carries exactly the numerator-membership proof.
      simpa [Gnum, Ideal.smul_eq_mul, Ideal.mul_top] using y.2
    have hcongr :
        (y : S) - (yd : S) ∈ S₊.toIdeal ^ (d + 1) :=
      degreeComponent_congr_mod_irrelevantPow_succ (𝒜 := 𝒜) hspan hy
    have hden :
        y - (⟨(yd : S), by
          simpa [Gnum, Ideal.smul_eq_mul, Ideal.mul_top] using
            degreePiece_mem_irrelevantPow_of_span_degreeOne (𝒜 := 𝒜) hspan d yd⟩ : Gnum) ∈
          Gden := by
      -- The component congruence is precisely the quotient denominator relation.
      simpa [Gden, Ideal.smul_eq_mul, Ideal.mul_top] using hcongr
    exact ((Submodule.Quotient.eq Gden).mpr hden).symm
  -- The component map is bijective, so it packages as the desired global comparison.
  exact ⟨(LinearEquiv.ofBijective toQuot ⟨hker, hsurj⟩).symm⟩

/-- Helper for Chap10 Lemma 10 117 1: on the global quotient `S₊^d/S₊^(d+1)`,
an `S`-scalar acts through its degree-zero residue in `k`. -/
private theorem globalIrrelevantPowQuotient_residueScalar_eq
    (hspan : Ideal.span (𝒜 1 : Set S) = S₊.toIdeal)
    (zeroIso : k ≃ₐ[k] 𝒜 0) {d : ℕ} (a : S)
    (q :
      (S₊.toIdeal ^ d • (⊤ : Submodule S S) : Submodule S S) ⧸
        (S₊.toIdeal ^ (d + 1) • (⊤ : Submodule S S) : Submodule S S).submoduleOf
          (S₊.toIdeal ^ d • (⊤ : Submodule S S) : Submodule S S)) :
    a • q = (zeroIso.symm (GradedRing.projZeroRingHom' 𝒜 a) : k) • q := by
  let Gnum : Submodule S S := S₊.toIdeal ^ d • (⊤ : Submodule S S)
  let Gden : Submodule S Gnum :=
    (S₊.toIdeal ^ (d + 1) • (⊤ : Submodule S S) : Submodule S S).submoduleOf Gnum
  let a₀ : S := ((GradedRing.projZeroRingHom' 𝒜 a : 𝒜 0) : S)
  have hscalar :
      algebraMap k S (zeroIso.symm (GradedRing.projZeroRingHom' 𝒜 a)) = a₀ := by
    -- The chosen degree-zero equivalence identifies the base-field scalar with the projected
    -- degree-zero component inside `S`.
    have hcomm :=
      congrArg (fun x : 𝒜 0 ↦ (x : S))
        (zeroIso.commutes (zeroIso.symm (GradedRing.projZeroRingHom' 𝒜 a)))
    simpa [a₀] using hcomm.symm
  -- It is enough to compare quotient representatives in the global numerator.
  refine Submodule.Quotient.induction_on (p := Gden) (x := q) ?_
  intro y
  rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul]
  apply (Submodule.Quotient.eq Gden).mpr
  let yd : 𝒜 d := DirectSum.decompose 𝒜 (y : S) d
  have hy : (y : S) ∈ S₊.toIdeal ^ d := by
    simpa [Gnum, Ideal.smul_eq_mul, Ideal.mul_top] using y.2
  have hycongr :
      (y : S) - (yd : S) ∈ S₊.toIdeal ^ (d + 1) :=
    degreeComponent_congr_mod_irrelevantPow_succ (𝒜 := 𝒜) hspan hy
  have hleft :
      a * ((y : S) - (yd : S)) ∈ S₊.toIdeal ^ (d + 1) :=
    Ideal.mul_mem_left _ a hycongr
  have hmid :
      a * (yd : S) - a₀ * (yd : S) ∈ S₊.toIdeal ^ (d + 1) :=
    degreePiece_mul_congr_projZero (𝒜 := 𝒜) hspan a yd
  have hright :
      a₀ * ((yd : S) - (y : S)) ∈ S₊.toIdeal ^ (d + 1) := by
    have hneg : (yd : S) - (y : S) ∈ S₊.toIdeal ^ (d + 1) := by
      simpa [sub_eq_add_neg, add_comm] using (neg_mem hycongr)
    exact Ideal.mul_mem_left _ a₀ hneg
  have hsum :
      a * ((y : S) - (yd : S)) +
          (a * (yd : S) - a₀ * (yd : S)) +
          a₀ * ((yd : S) - (y : S)) ∈
        S₊.toIdeal ^ (d + 1) :=
    Ideal.add_mem _ (Ideal.add_mem _ hleft hmid) hright
  -- The three denominator terms telescope to the scalar-action difference.
  have hdiff :
      a * (y : S) - a₀ * (y : S) ∈ S₊.toIdeal ^ (d + 1) := by
    convert hsum using 1
    ring
  have hcoe :
      ((a • y - (zeroIso.symm (GradedRing.projZeroRingHom' 𝒜 a) : k) • y : Gnum) : S) =
        a * (y : S) - a₀ * (y : S) := by
    simp [Algebra.smul_def, hscalar]
  change ((a • y - (zeroIso.symm (GradedRing.projZeroRingHom' 𝒜 a) : k) • y : Gnum) : S) ∈
    (S₊.toIdeal ^ (d + 1) • (⊤ : Submodule S S) : Submodule S S)
  rw [hcoe]
  simpa [Ideal.smul_eq_mul, Ideal.mul_top] using hdiff

/-- Helper for Chap10 Lemma 10 117 1: after localizing the global quotient, a local scalar acts
through its residue in `k`. -/
private theorem localizedGlobalIrrelevantPowQuotient_residueScalar_eq
    (hspan : Ideal.span (𝒜 1 : Set S) = S₊.toIdeal)
    (zeroIso : k ≃ₐ[k] 𝒜 0) {d : ℕ}
    (eRes :
      let P := (irrelevantClosedPoint 𝒜 zeroIso).toPrimeSpectrum.asIdeal
      let I : Ideal (Localization.AtPrime P) := maximalIdeal (Localization.AtPrime P)
      (Localization.AtPrime P ⧸ I) ≃+* k)
    (hresidueMk' :
      let P := (irrelevantClosedPoint 𝒜 zeroIso).toPrimeSpectrum.asIdeal
      let Rloc := Localization.AtPrime P
      let I : Ideal Rloc := maximalIdeal Rloc
      ∀ (a : S) (s : P.primeCompl),
        eRes (Ideal.Quotient.mk I (IsLocalization.mk' Rloc a s)) =
          zeroIso.symm (GradedRing.projZeroRingHom' 𝒜 a) /
            zeroIso.symm (GradedRing.projZeroRingHom' 𝒜 (s : S))) :
    let P := (irrelevantClosedPoint 𝒜 zeroIso).toPrimeSpectrum.asIdeal
    let I : Ideal (Localization.AtPrime P) := maximalIdeal (Localization.AtPrime P)
    let G : Type u :=
      (S₊.toIdeal ^ d • (⊤ : Submodule S S) : Submodule S S) ⧸
        (S₊.toIdeal ^ (d + 1) • (⊤ : Submodule S S) : Submodule S S).submoduleOf
          (S₊.toIdeal ^ d • (⊤ : Submodule S S) : Submodule S S)
    letI : IsLocalizedModule P.primeCompl (LinearMap.id : G →ₗ[S] G) :=
      globalIrrelevantPowQuotient_isLocalizedModule_id (𝒜 := 𝒜) zeroIso d
    letI : Module (Localization.AtPrime P) G :=
      IsLocalizedModule.module P.primeCompl (LinearMap.id : G →ₗ[S] G)
    ∀ (r : Localization.AtPrime P) (q : G),
      r • q = eRes (Ideal.Quotient.mk I r) • q := by
  dsimp only
  let P := (irrelevantClosedPoint 𝒜 zeroIso).toPrimeSpectrum.asIdeal
  letI : P.IsPrime := by
    dsimp [P]
    exact (irrelevantClosedPoint 𝒜 zeroIso).toPrimeSpectrum.isPrime
  let I : Ideal (Localization.AtPrime P) := maximalIdeal (Localization.AtPrime P)
  let G : Type u :=
    (S₊.toIdeal ^ d • (⊤ : Submodule S S) : Submodule S S) ⧸
      (S₊.toIdeal ^ (d + 1) • (⊤ : Submodule S S) : Submodule S S).submoduleOf
        (S₊.toIdeal ^ d • (⊤ : Submodule S S) : Submodule S S)
  letI : IsLocalizedModule P.primeCompl (LinearMap.id : G →ₗ[S] G) :=
    globalIrrelevantPowQuotient_isLocalizedModule_id (𝒜 := 𝒜) zeroIso d
  letI : Module (Localization.AtPrime P) G :=
    IsLocalizedModule.module P.primeCompl (LinearMap.id : G →ₗ[S] G)
  letI : IsScalarTower S (Localization.AtPrime P) G :=
    IsLocalizedModule.isScalarTower_module P.primeCompl (LinearMap.id : G →ₗ[S] G)
  intro r q
  rcases (IsLocalization.mk'_surjective (M := P.primeCompl) (S := Localization.AtPrime P) r)
    with ⟨⟨a, s⟩, rfl⟩
  let ca : k := zeroIso.symm (GradedRing.projZeroRingHom' 𝒜 a)
  let cs : k := zeroIso.symm (GradedRing.projZeroRingHom' 𝒜 (s : S))
  have hcs_ne : cs ≠ 0 := by
    -- Denominators avoid `P = S₊`, hence have nonzero degree-zero residue.
    have hs_not : (s : S) ∉ S₊.toIdeal := by
      have hP : P = S₊.toIdeal := rfl
      rw [← hP]
      exact s.2
    have hproj_ne :
        GradedRing.projZeroRingHom' 𝒜 (s : S) ≠ 0 :=
      projZero_ne_zero_of_notMem_irrelevant (𝒜 := 𝒜) hs_not
    intro hcs
    apply hproj_ne
    change zeroIso.symm (GradedRing.projZeroRingHom' 𝒜 (s : S)) = 0 at hcs
    have hcs0 :
        zeroIso.symm (GradedRing.projZeroRingHom' 𝒜 (s : S)) = zeroIso.symm 0 := by
      rw [map_zero]
      exact hcs
    exact zeroIso.symm.injective hcs0
  have hmk :
      IsLocalization.mk' (Localization.AtPrime P) a s • q =
        IsLocalizedModule.mk' (LinearMap.id : G →ₗ[S] G) (a • q) s := by
    -- Move the denominator from the local-ring scalar into the localized-module representative.
    have h :=
      IsLocalizedModule.mk'_smul_mk' (Localization.AtPrime P)
        (LinearMap.id : G →ₗ[S] G) a q s (1 : P.primeCompl)
    simpa using h
  have hlocalized :
      IsLocalizedModule.mk' (LinearMap.id : G →ₗ[S] G) (a • q) s =
        (ca / cs) • q := by
    rw [IsLocalizedModule.mk'_eq_iff]
    -- Clearing the denominator reduces the claim to the already proved global residue-scalar
    -- formula and a field identity in `k`.
    calc
      a • q = ca • q := by
        simpa [G, ca] using
          globalIrrelevantPowQuotient_residueScalar_eq
            (𝒜 := 𝒜) hspan zeroIso a q
      _ = cs • ((ca / cs) • q) := by
        have hcoeff : cs * (ca / cs) = ca := by
          field_simp [hcs_ne]
        rw [smul_smul, hcoeff]
      _ = (s : S) • ((ca / cs) • q) := by
        simpa [G, cs] using
          (globalIrrelevantPowQuotient_residueScalar_eq
            (𝒜 := 𝒜) hspan zeroIso (s : S) ((ca / cs) • q)).symm
  calc
    IsLocalization.mk' (Localization.AtPrime P) a s • q =
        IsLocalizedModule.mk' (LinearMap.id : G →ₗ[S] G) (a • q) s := hmk
    _ = (ca / cs) • q := hlocalized
    _ = eRes (Ideal.Quotient.mk I (IsLocalization.mk' (Localization.AtPrime P) a s)) • q := by
      rw [hresidueMk' a s]

/-- Helper for Chap10 Lemma 10 117 1: finite generation descends from an `R`-module structure
to a field structure when all `R`-scalars act through that field. -/
private theorem moduleFinite_of_finite_of_scalar_eq
    {K : Type u} [Field K] {R : Type u} [CommRing R]
    {M : Type u} [AddCommGroup M] [Module R M] [Module K M]
    (φ : R → K) [Module.Finite R M]
    (hscalar : ∀ (r : R) (m : M), r • m = φ r • m) :
    Module.Finite K M := by
  classical
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := R) (M := M)
  refine Module.Finite.of_fg_top ?_
  rw [Submodule.fg_iff_exists_fin_generating_family]
  refine ⟨n, s, ?_⟩
  apply top_unique
  intro m hm
  have hmS : m ∈ Submodule.span R (Set.range s) := by
    simpa [hs]
  -- Rewrite each `R`-scalar in a finite `R`-linear expression as its controlling field scalar.
  refine Submodule.span_induction (s := Set.range s)
    (p := fun z _ ↦ z ∈ Submodule.span K (Set.range s)) ?_ ?_ ?_ ?_ hmS
  · rintro x ⟨i, rfl⟩
    exact Submodule.subset_span ⟨i, rfl⟩
  · exact Submodule.zero_mem _
  · intro x y hx hy hxK hyK
    exact Submodule.add_mem _ hxK hyK
  · intro r x hx hxK
    rw [hscalar r x]
    exact Submodule.smul_mem _ (φ r) hxK

/-- Helper for Chap10 Lemma 10 117 1: the global quotient `S₊^d/S₊^(d+1)` is finite-dimensional
over `k`. -/
private theorem globalIrrelevantPowQuotient_finiteDimensional
    (hgenerated : Algebra.adjoin (𝒜 0) (𝒜 1 : Set S) = ⊤)
    (hfiniteType : Algebra.FiniteType (𝒜 0) S)
    (zeroIso : k ≃ₐ[k] 𝒜 0) (d : ℕ) :
    Module.Finite k
      ((S₊.toIdeal ^ d • (⊤ : Submodule S S) : Submodule S S) ⧸
        (S₊.toIdeal ^ (d + 1) • (⊤ : Submodule S S) : Submodule S S).submoduleOf
          (S₊.toIdeal ^ d • (⊤ : Submodule S S) : Submodule S S)) := by
  letI : Algebra.FiniteType k S :=
    finiteType_of_degreeZeroIso 𝒜 hfiniteType zeroIso
  letI : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing k S
  let Gnum : Submodule S S := S₊.toIdeal ^ d • (⊤ : Submodule S S)
  let Gden : Submodule S Gnum :=
    (S₊.toIdeal ^ (d + 1) • (⊤ : Submodule S S) : Submodule S S).submoduleOf Gnum
  let G : Type u := Gnum ⧸ Gden
  have hspan : Ideal.span (𝒜 1 : Set S) = S₊.toIdeal :=
    span_degreeOne_eq_irrelevant_of_adjoin_eq_top (𝒜 := 𝒜) hgenerated
  letI : Module.Finite S G := inferInstance
  -- Noetherianity makes the quotient finite over `S`, and the preceding scalar-normalization
  -- helper turns the same finite generator set into a `k`-generator set.
  exact moduleFinite_of_finite_of_scalar_eq
    (K := k) (R := S) (M := G)
    (fun a ↦ zeroIso.symm (GradedRing.projZeroRingHom' 𝒜 a))
    (globalIrrelevantPowQuotient_residueScalar_eq (𝒜 := 𝒜) hspan zeroIso)

/-- Helper for Chap10 Lemma 10 117 1: once the degree piece is finite-dimensional, the global
quotient has the same rank as the degree-piece finrank. -/
private theorem globalIrrelevantPowQuotient_rank_eq_degreePieceFinrank_of_finite
    (hspan : Ideal.span (𝒜 1 : Set S) = S₊.toIdeal) (d : ℕ)
    [FiniteDimensional k (𝒜 d)] :
    Cardinal.toENat
        (Module.rank k
          ((S₊.toIdeal ^ d • (⊤ : Submodule S S) : Submodule S S) ⧸
            (S₊.toIdeal ^ (d + 1) • (⊤ : Submodule S S) : Submodule S S).submoduleOf
              (S₊.toIdeal ^ d • (⊤ : Submodule S S) : Submodule S S))) =
      (Module.finrank k (𝒜 d) : ℕ∞) := by
  obtain ⟨eGlobalDegree⟩ :=
    globalIrrelevantPowQuotient_linearEquiv_degreePiece (𝒜 := 𝒜) hspan d
  -- Transport rank across the global degree-piece equivalence, then convert finite rank to
  -- finrank.
  calc
    Cardinal.toENat
        (Module.rank k
          ((S₊.toIdeal ^ d • (⊤ : Submodule S S) : Submodule S S) ⧸
            (S₊.toIdeal ^ (d + 1) • (⊤ : Submodule S S) : Submodule S S).submoduleOf
              (S₊.toIdeal ^ d • (⊤ : Submodule S S) : Submodule S S))) =
        Cardinal.toENat (Module.rank k (𝒜 d)) := by
      rw [eGlobalDegree.rank_eq]
    _ = (Module.finrank k (𝒜 d) : ℕ∞) := by
      rw [← Module.finrank_eq_rank' k (𝒜 d)]
      simp

/-- Helper for Chap10 Lemma 10 117 1: a semilinear additive equivalence transports module rank
across a bijective scalar map. -/
private theorem rank_toENat_eq_of_semilinearAddEquiv
    {R R' : Type u} {M M' : Type u}
    [Semiring R] [Semiring R'] [AddCommMonoid M] [AddCommMonoid M']
    [Module R M] [Module R' M']
    (i : R → R') (j : M ≃+ M') (hi : Function.Bijective i)
    (hc : ∀ (r : R) (m : M), j (r • m) = i r • j m) :
    Cardinal.toENat (Module.rank R M) = Cardinal.toENat (Module.rank R' M') := by
  -- The mathlib rank transport theorem works at the cardinal level; this helper records the
  -- exact `toENat` normal form needed by the local length comparison.
  rw [rank_eq_of_equiv_equiv i j hi hc]

/-- Helper for Chap10 Lemma 10 117 1: a linear equivalence from a module killed by an ideal
transports residue-field rank when the target scalar action factors through the residue field. -/
private theorem rank_toENat_eq_of_quotient_torsion_linearEquiv
    {R K : Type u} {M N : Type u}
    [CommRing R] [Field K] [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] [Module K N]
    {I : Ideal R} [I.IsTwoSided]
    (hTorsion : Module.IsTorsionBySet R M I)
    (eRes : R ⧸ I ≃+* K)
    (eLinear : M ≃ₗ[R] N)
    (hscalar : ∀ (a : R) (n : N), a • n = eRes (Ideal.Quotient.mk I a) • n) :
    letI : Module (R ⧸ I) M := hTorsion.module
    Cardinal.toENat (Module.rank (R ⧸ I) M) = Cardinal.toENat (Module.rank K N) := by
  let instResidueModule : Module (R ⧸ I) M := hTorsion.module
  letI : Module (R ⧸ I) M := instResidueModule
  let j : M ≃+ N := eLinear.toAddEquiv
  have hj : ∀ (r : R ⧸ I) (x : M),
      j (@SMul.smul (R ⧸ I) M hTorsion.hasSMul r x) = eRes r • j x := by
    intro r x
    -- Quotient induction reduces the source scalar to the original `R`-scalar.
    refine Quotient.inductionOn' r ?_
    intro a
    calc
      j (@SMul.smul (R ⧸ I) M hTorsion.hasSMul (Ideal.Quotient.mk I a) x) =
          j (a • x) := by
        rfl
      _ = a • j x := by
        exact eLinear.map_smul a x
      _ = eRes (Ideal.Quotient.mk I a) • j x := by
        exact hscalar a (j x)
  -- The abstract semilinear rank transport applies to the residue-field scalar map.
  have hrank :=
    @rank_toENat_eq_of_semilinearAddEquiv (R ⧸ I) K M N
      inferInstance inferInstance inferInstance inferInstance instResidueModule inferInstance
      eRes j eRes.bijective hj
  simpa [instResidueModule] using hrank

/-- Helper for Chap10 Lemma 10 117 1: under the canonical equivalence between a localized
submodule and the localization of the submodule, localized nested submodules are carried to each
other. -/
private theorem map_localizedEquiv_submoduleOf_eq
    {R : Type u} [CommRing R] {M : Type u} [AddCommGroup M] [Module R M]
    (p : Submonoid R) {L N : Submodule R M} (hLN : L ≤ N) :
    Submodule.map
        (Submodule.localizedEquiv p N : N.localized p →ₗ[Localization p] LocalizedModule p N)
        ((L.localized p).submoduleOf (N.localized p)) =
      (L.submoduleOf N).localized p := by
  -- Compare both localized submodules by writing their elements as fractions and using the
  -- defining universal equivalence between the two localized models of `N`.
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rcases
      (Submodule.mem_localized' (Localization p) p (LocalizedModule.mkLinearMap p M) L y).mp hy
      with ⟨l, hl, s, hls⟩
    rw [Submodule.mem_localized']
    refine ⟨⟨l, hLN hl⟩, hl, s, ?_⟩
    rw [IsLocalizedModule.mk'_eq_iff]
    have hy_eq : (Submodule.toLocalized p N) ⟨l, hLN hl⟩ = (s : R) • y := by
      ext
      change (LocalizedModule.mkLinearMap p M) l = (s : R) • (y : LocalizedModule p M)
      exact IsLocalizedModule.mk'_eq_iff.mp hls
    calc
      (LocalizedModule.mkLinearMap p N) ⟨l, hLN hl⟩ =
          (Submodule.localizedEquiv p N) ((Submodule.toLocalized p N) ⟨l, hLN hl⟩) := by
        simpa [Submodule.localizedEquiv] using
          (IsLocalizedModule.linearEquiv_apply p (Submodule.toLocalized p N)
            (LocalizedModule.mkLinearMap p N) ⟨l, hLN hl⟩).symm
      _ = (s : R) • (Submodule.localizedEquiv p N) y := by
        rw [hy_eq]
        simpa [Submonoid.smul_def, algebraMap_smul] using
          map_smul (Submodule.localizedEquiv p N)
            (algebraMap R (Localization p) (s : R)) y
  · intro hx
    rw [Submodule.mem_localized'] at hx
    rcases hx with ⟨l, hl, s, hls⟩
    let y : N.localized p := IsLocalizedModule.mk' (Submodule.toLocalized p N) l s
    refine ⟨y, ?_, ?_⟩
    · change (y : LocalizedModule p M) ∈ L.localized p
      rw [Submodule.mem_localized']
      refine ⟨(l : M), hl, s, ?_⟩
      rw [IsLocalizedModule.mk'_eq_iff]
      have hy_eq : (Submodule.toLocalized p N) l = (s : R) • y := by
        dsimp [y]
        exact IsLocalizedModule.mk'_eq_iff.mp rfl
      simpa [Submodule.toLocalized, Submodule.toLocalized', Submodule.toLocalized₀,
        LocalizedModule.mkLinearMap_apply] using congrArg Subtype.val hy_eq
    · rw [← hls]
      rw [eq_comm, IsLocalizedModule.mk'_eq_iff]
      have hy_eq : (Submodule.toLocalized p N) l = (s : R) • y := by
        dsimp [y]
        exact IsLocalizedModule.mk'_eq_iff.mp rfl
      calc
        (LocalizedModule.mkLinearMap p N) l =
            (Submodule.localizedEquiv p N) ((Submodule.toLocalized p N) l) := by
          simpa [Submodule.localizedEquiv] using
            (IsLocalizedModule.linearEquiv_apply p (Submodule.toLocalized p N)
              (LocalizedModule.mkLinearMap p N) l).symm
        _ = (s : R) • (Submodule.localizedEquiv p N) y := by
          rw [hy_eq]
          simpa [Submonoid.smul_def, algebraMap_smul] using
            map_smul (Submodule.localizedEquiv p N)
              (algebraMap R (Localization p) (s : R)) y

/-- Helper for Chap10 Lemma 10 117 1: the quotient of localized nested submodules is the
localization of the original quotient. -/
private noncomputable def localizedSubmoduleQuotientEquiv
    {R : Type u} [CommRing R] {M : Type u} [AddCommGroup M] [Module R M]
    (p : Submonoid R) {L N : Submodule R M} (hLN : L ≤ N) :
    (N.localized p ⧸ (L.localized p).submoduleOf (N.localized p)) ≃ₗ[Localization p]
      LocalizedModule p (N ⧸ L.submoduleOf N) :=
  -- First move the numerator model from a localized submodule to the localization of the
  -- numerator, then apply the owner quotient-localization equivalence.
  (Submodule.Quotient.equiv ((L.localized p).submoduleOf (N.localized p))
    ((L.submoduleOf N).localized p) (Submodule.localizedEquiv p N)
    (map_localizedEquiv_submoduleOf_eq p hLN)).trans
    (localizedQuotientEquiv p (L.submoduleOf N))

/-- Helper for Chap10 Lemma 10 117 1: equality transports numerator and denominator submodules
to the corresponding quotient. -/
private theorem map_submoduleOf_of_eq
    {R : Type u} [Ring R] {M : Type u} [AddCommGroup M] [Module R M]
    {A B C D : Submodule R M} (hA : A = C) (hB : B = D) :
    Submodule.map (LinearEquiv.ofEq A C hA : A →ₗ[R] C) (B.submoduleOf A) =
      D.submoduleOf C := by
  -- After replacing the equal submodules, the equality equivalence is the identity on carriers.
  subst C
  subst D
  ext x
  constructor
  · rintro ⟨y, hy, hxy⟩
    subst x
    simpa [LinearEquiv.ofEq] using hy
  · intro hx
    refine ⟨x, hx, ?_⟩
    exact Subtype.ext rfl

/-- Helper for Chap10 Lemma 10 117 1: the canonical local successive quotient is the localization
of the global irrelevant-power quotient. -/
private theorem irrelevantLocalSuccessiveQuotient_linearEquiv_localizedGlobal
    (zeroIso : k ≃ₐ[k] 𝒜 0) {d : ℕ} :
    let P := (irrelevantClosedPoint 𝒜 zeroIso).toPrimeSpectrum.asIdeal
    let I : Ideal (Localization.AtPrime P) := maximalIdeal (Localization.AtPrime P)
    let A : Submodule (Localization.AtPrime P) (Localization.AtPrime P) :=
      I ^ d • (⊤ : Submodule (Localization.AtPrime P) (Localization.AtPrime P))
    let B : Submodule (Localization.AtPrime P) (Localization.AtPrime P) :=
      I ^ (d + 1) • (⊤ : Submodule (Localization.AtPrime P) (Localization.AtPrime P))
    let G : Type u :=
      (S₊.toIdeal ^ d • (⊤ : Submodule S S) : Submodule S S) ⧸
        (S₊.toIdeal ^ (d + 1) • (⊤ : Submodule S S) : Submodule S S).submoduleOf
          (S₊.toIdeal ^ d • (⊤ : Submodule S S) : Submodule S S)
    Nonempty ((A ⧸ B.submoduleOf A) ≃ₗ[Localization.AtPrime P] LocalizedModule P.primeCompl G) := by
  dsimp only
  let P := (irrelevantClosedPoint 𝒜 zeroIso).toPrimeSpectrum.asIdeal
  letI : P.IsPrime := by
    dsimp [P]
    exact (irrelevantClosedPoint 𝒜 zeroIso).toPrimeSpectrum.isPrime
  let I : Ideal (Localization.AtPrime P) := maximalIdeal (Localization.AtPrime P)
  let N : Submodule S S := S₊.toIdeal ^ d • (⊤ : Submodule S S)
  let L : Submodule S S := S₊.toIdeal ^ (d + 1) • (⊤ : Submodule S S)
  let A : Submodule (Localization.AtPrime P) (Localization.AtPrime P) :=
    I ^ d • (⊤ : Submodule (Localization.AtPrime P) (Localization.AtPrime P))
  let B : Submodule (Localization.AtPrime P) (Localization.AtPrime P) :=
    I ^ (d + 1) • (⊤ : Submodule (Localization.AtPrime P) (Localization.AtPrime P))
  have hLN : L ≤ N := by
    -- The denominator power is contained in the numerator power before localization.
    exact Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_succ d))
  have hNloc : N.localized P.primeCompl = A := by
    -- Normalize the localized numerator to the corresponding local power.
    simpa [P, I, N, A] using localPow_eq_localized_irrelevantPow (𝒜 := 𝒜) zeroIso d
  have hLloc : L.localized P.primeCompl = B := by
    -- Normalize the localized denominator to the next local power.
    simpa [P, I, L, B] using localPow_eq_localized_irrelevantPow (𝒜 := 𝒜) zeroIso (d + 1)
  let eNum : A ≃ₗ[Localization.AtPrime P] N.localized P.primeCompl :=
    LinearEquiv.ofEq A (N.localized P.primeCompl) hNloc.symm
  have hden :
      Submodule.map (eNum : A →ₗ[Localization.AtPrime P] N.localized P.primeCompl)
          (B.submoduleOf A) =
        (L.localized P.primeCompl).submoduleOf (N.localized P.primeCompl) := by
    -- The equality equivalence carries the local denominator to the localized global denominator.
    simpa [eNum] using
      map_submoduleOf_of_eq (R := Localization.AtPrime P)
        (hA := hNloc.symm) (hB := hLloc.symm)
  let eQuot :
      (A ⧸ B.submoduleOf A) ≃ₗ[Localization.AtPrime P]
        (N.localized P.primeCompl ⧸
          (L.localized P.primeCompl).submoduleOf (N.localized P.primeCompl)) :=
    Submodule.Quotient.equiv (B.submoduleOf A)
      ((L.localized P.primeCompl).submoduleOf (N.localized P.primeCompl)) eNum hden
  -- Quotient-localization then identifies the localized quotient with the localization of the
  -- global quotient.
  exact ⟨eQuot.trans (localizedSubmoduleQuotientEquiv P.primeCompl hLN)⟩

/-- Helper for Chap10 Lemma 10 117 1: the localized global quotient is linearly equivalent to
the global quotient itself after localization at the irrelevant closed point. -/
private theorem localizedGlobalIrrelevantPowQuotient_linearEquiv_self
    (zeroIso : k ≃ₐ[k] 𝒜 0) {d : ℕ} :
    let P := (irrelevantClosedPoint 𝒜 zeroIso).toPrimeSpectrum.asIdeal
    let G : Type u :=
      (S₊.toIdeal ^ d • (⊤ : Submodule S S) : Submodule S S) ⧸
        (S₊.toIdeal ^ (d + 1) • (⊤ : Submodule S S) : Submodule S S).submoduleOf
          (S₊.toIdeal ^ d • (⊤ : Submodule S S) : Submodule S S)
    letI : IsLocalizedModule P.primeCompl (LinearMap.id : G →ₗ[S] G) :=
      globalIrrelevantPowQuotient_isLocalizedModule_id (𝒜 := 𝒜) zeroIso d
    letI : Module (Localization.AtPrime P) G :=
      IsLocalizedModule.module P.primeCompl (LinearMap.id : G →ₗ[S] G)
    Nonempty (LocalizedModule P.primeCompl G ≃ₗ[Localization.AtPrime P] G) := by
  dsimp only
  let P := (irrelevantClosedPoint 𝒜 zeroIso).toPrimeSpectrum.asIdeal
  letI : P.IsPrime := by
    dsimp [P]
    exact (irrelevantClosedPoint 𝒜 zeroIso).toPrimeSpectrum.isPrime
  let G : Type u :=
    (S₊.toIdeal ^ d • (⊤ : Submodule S S) : Submodule S S) ⧸
      (S₊.toIdeal ^ (d + 1) • (⊤ : Submodule S S) : Submodule S S).submoduleOf
        (S₊.toIdeal ^ d • (⊤ : Submodule S S) : Submodule S S)
  letI : IsLocalizedModule P.primeCompl (LinearMap.id : G →ₗ[S] G) :=
    globalIrrelevantPowQuotient_isLocalizedModule_id (𝒜 := 𝒜) zeroIso d
  letI : Module (Localization.AtPrime P) G :=
    IsLocalizedModule.module P.primeCompl (LinearMap.id : G →ₗ[S] G)
  letI : IsScalarTower S (Localization.AtPrime P) G :=
    IsLocalizedModule.isScalarTower_module P.primeCompl (LinearMap.id : G →ₗ[S] G)
  -- The identity is already a localization map, so its localization comparison extends scalars to
  -- the local ring.
  exact ⟨LinearEquiv.extendScalarsOfIsLocalization P.primeCompl (Localization.AtPrime P)
    (IsLocalizedModule.iso P.primeCompl (LinearMap.id : G →ₗ[S] G))⟩

/-- Helper for Chap10 Lemma 10 117 1: composing the local quotient localization with the
identity-localization of the global quotient gives the direct local-to-global equivalence. -/
private theorem irrelevantLocalSuccessiveQuotient_linearEquiv_global
    (zeroIso : k ≃ₐ[k] 𝒜 0) {d : ℕ} :
    let P := (irrelevantClosedPoint 𝒜 zeroIso).toPrimeSpectrum.asIdeal
    let I : Ideal (Localization.AtPrime P) := maximalIdeal (Localization.AtPrime P)
    let A : Submodule (Localization.AtPrime P) (Localization.AtPrime P) :=
      I ^ d • (⊤ : Submodule (Localization.AtPrime P) (Localization.AtPrime P))
    let B : Submodule (Localization.AtPrime P) (Localization.AtPrime P) :=
      I ^ (d + 1) • (⊤ : Submodule (Localization.AtPrime P) (Localization.AtPrime P))
    let G : Type u :=
      (S₊.toIdeal ^ d • (⊤ : Submodule S S) : Submodule S S) ⧸
        (S₊.toIdeal ^ (d + 1) • (⊤ : Submodule S S) : Submodule S S).submoduleOf
          (S₊.toIdeal ^ d • (⊤ : Submodule S S) : Submodule S S)
    letI : IsLocalizedModule P.primeCompl (LinearMap.id : G →ₗ[S] G) :=
      globalIrrelevantPowQuotient_isLocalizedModule_id (𝒜 := 𝒜) zeroIso d
    letI : Module (Localization.AtPrime P) G :=
      IsLocalizedModule.module P.primeCompl (LinearMap.id : G →ₗ[S] G)
    Nonempty ((A ⧸ B.submoduleOf A) ≃ₗ[Localization.AtPrime P] G) := by
  dsimp only
  let P := (irrelevantClosedPoint 𝒜 zeroIso).toPrimeSpectrum.asIdeal
  letI : P.IsPrime := by
    dsimp [P]
    exact (irrelevantClosedPoint 𝒜 zeroIso).toPrimeSpectrum.isPrime
  let I : Ideal (Localization.AtPrime P) := maximalIdeal (Localization.AtPrime P)
  let A : Submodule (Localization.AtPrime P) (Localization.AtPrime P) :=
    I ^ d • (⊤ : Submodule (Localization.AtPrime P) (Localization.AtPrime P))
  let B : Submodule (Localization.AtPrime P) (Localization.AtPrime P) :=
    I ^ (d + 1) • (⊤ : Submodule (Localization.AtPrime P) (Localization.AtPrime P))
  let G : Type u :=
    (S₊.toIdeal ^ d • (⊤ : Submodule S S) : Submodule S S) ⧸
      (S₊.toIdeal ^ (d + 1) • (⊤ : Submodule S S) : Submodule S S).submoduleOf
        (S₊.toIdeal ^ d • (⊤ : Submodule S S) : Submodule S S)
  letI : IsLocalizedModule P.primeCompl (LinearMap.id : G →ₗ[S] G) :=
    globalIrrelevantPowQuotient_isLocalizedModule_id (𝒜 := 𝒜) zeroIso d
  letI : Module (Localization.AtPrime P) G :=
    IsLocalizedModule.module P.primeCompl (LinearMap.id : G →ₗ[S] G)
  obtain ⟨eLocal⟩ :=
    irrelevantLocalSuccessiveQuotient_linearEquiv_localizedGlobal (𝒜 := 𝒜) zeroIso (d := d)
  obtain ⟨eSelf⟩ :=
    localizedGlobalIrrelevantPowQuotient_linearEquiv_self (𝒜 := 𝒜) zeroIso (d := d)
  -- Compose the two linear equivalences before the longer rank proof unfolds any quotient data.
  exact ⟨eLocal.trans eSelf⟩

/-- Helper for Chap10 Lemma 10 117 1: the identity-localization structure on the global quotient
is stable under replacing the canonical prime by an equal local alias. -/
private theorem globalIrrelevantPowQuotient_isLocalizedModule_id_of_eq
    (zeroIso : k ≃ₐ[k] 𝒜 0) {d : ℕ}
    (P : Ideal S) [P.IsPrime]
    (hP : P = (irrelevantClosedPoint 𝒜 zeroIso).toPrimeSpectrum.asIdeal) :
    let G : Type u :=
      (S₊.toIdeal ^ d • (⊤ : Submodule S S) : Submodule S S) ⧸
        (S₊.toIdeal ^ (d + 1) • (⊤ : Submodule S S) : Submodule S S).submoduleOf
          (S₊.toIdeal ^ d • (⊤ : Submodule S S) : Submodule S S)
    IsLocalizedModule P.primeCompl (LinearMap.id : G →ₗ[S] G) := by
  -- Replace the alias for `P` before invoking the canonical identity-localization helper.
  subst P
  simpa using globalIrrelevantPowQuotient_isLocalizedModule_id (𝒜 := 𝒜) zeroIso d

/-- Helper for Chap10 Lemma 10 117 1: the direct local-to-global equivalence is stable under
the local aliases used in the final associated-graded comparison. -/
private theorem localSuccessiveQuotient_linearEquiv_global_of_eq
    (zeroIso : k ≃ₐ[k] 𝒜 0) {d : ℕ}
    (P : Ideal S) [P.IsPrime]
    (hP : P = (irrelevantClosedPoint 𝒜 zeroIso).toPrimeSpectrum.asIdeal)
    (I : Ideal (Localization.AtPrime P))
    (hI : I = maximalIdeal (Localization.AtPrime P))
    (A : Submodule (Localization.AtPrime P) (Localization.AtPrime P))
    (hA : A = I ^ d • (⊤ : Submodule (Localization.AtPrime P) (Localization.AtPrime P)))
    (B : Submodule (Localization.AtPrime P) (Localization.AtPrime P))
    (hB : B = I ^ (d + 1) • (⊤ : Submodule (Localization.AtPrime P) (Localization.AtPrime P))) :
    let G : Type u :=
      (S₊.toIdeal ^ d • (⊤ : Submodule S S) : Submodule S S) ⧸
        (S₊.toIdeal ^ (d + 1) • (⊤ : Submodule S S) : Submodule S S).submoduleOf
          (S₊.toIdeal ^ d • (⊤ : Submodule S S) : Submodule S S)
    letI : IsLocalizedModule P.primeCompl (LinearMap.id : G →ₗ[S] G) :=
      globalIrrelevantPowQuotient_isLocalizedModule_id_of_eq (𝒜 := 𝒜) zeroIso P hP
    letI : Module (Localization.AtPrime P) G :=
      IsLocalizedModule.module P.primeCompl (LinearMap.id : G →ₗ[S] G)
    Nonempty ((A ⧸ B.submoduleOf A) ≃ₗ[Localization.AtPrime P]
        ((S₊.toIdeal ^ d • (⊤ : Submodule S S) : Submodule S S) ⧸
          (S₊.toIdeal ^ (d + 1) • (⊤ : Submodule S S) : Submodule S S).submoduleOf
            (S₊.toIdeal ^ d • (⊤ : Submodule S S) : Submodule S S))) := by
  -- Replace the local aliases by their canonical definitions, then use the direct bridge.
  subst P
  subst I
  subst A
  subst B
  simpa using irrelevantLocalSuccessiveQuotient_linearEquiv_global (𝒜 := 𝒜) zeroIso (d := d)

/-- Chap10 Lemma 10 117 1: the local successive quotient has the same residue-field rank as the
global irrelevant-power quotient, in the alias form used by the length proof. -/
private theorem localSuccessiveQuotient_rank_eq_globalIrrelevantPowQuotient_rank
    (hspan : Ideal.span (𝒜 1 : Set S) = S₊.toIdeal)
    (zeroIso : k ≃ₐ[k] 𝒜 0) {d : ℕ}
    (P : Ideal S) [P.IsPrime]
    (hP : P = (irrelevantClosedPoint 𝒜 zeroIso).toPrimeSpectrum.asIdeal)
    (I : Ideal (Localization.AtPrime P))
    (hI : I = maximalIdeal (Localization.AtPrime P))
    (A : Submodule (Localization.AtPrime P) (Localization.AtPrime P))
    (hA : A = I ^ d • (⊤ : Submodule (Localization.AtPrime P) (Localization.AtPrime P)))
    (B : Submodule (Localization.AtPrime P) (Localization.AtPrime P))
    (hB : B = I ^ (d + 1) • (⊤ : Submodule (Localization.AtPrime P) (Localization.AtPrime P)))
    (eRes : (Localization.AtPrime P ⧸ I) ≃+* k)
    (hresidueMk' :
      ∀ (a : S) (s : P.primeCompl),
        eRes (Ideal.Quotient.mk I (IsLocalization.mk' (Localization.AtPrime P) a s)) =
          zeroIso.symm (GradedRing.projZeroRingHom' 𝒜 a) /
            zeroIso.symm (GradedRing.projZeroRingHom' 𝒜 (s : S)))
    (hTorsion : Module.IsTorsionBySet (Localization.AtPrime P) (A ⧸ B.submoduleOf A) I) :
    letI : Module ((Localization.AtPrime P) ⧸ I) (A ⧸ B.submoduleOf A) := hTorsion.module
    Cardinal.toENat (Module.rank ((Localization.AtPrime P) ⧸ I) (A ⧸ B.submoduleOf A)) =
      Cardinal.toENat
        (Module.rank k
          ((S₊.toIdeal ^ d • (⊤ : Submodule S S) : Submodule S S) ⧸
            (S₊.toIdeal ^ (d + 1) • (⊤ : Submodule S S) : Submodule S S).submoduleOf
              (S₊.toIdeal ^ d • (⊤ : Submodule S S) : Submodule S S))) := by
  -- Replace aliases before using the abstract quotient-rank transport.
  subst P
  subst I
  subst A
  subst B
  let G : Type u :=
    (S₊.toIdeal ^ d • (⊤ : Submodule S S) : Submodule S S) ⧸
      (S₊.toIdeal ^ (d + 1) • (⊤ : Submodule S S) : Submodule S S).submoduleOf
        (S₊.toIdeal ^ d • (⊤ : Submodule S S) : Submodule S S)
  letI : IsLocalizedModule
      (irrelevantClosedPoint 𝒜 zeroIso).toPrimeSpectrum.asIdeal.primeCompl
      (LinearMap.id : G →ₗ[S] G) :=
    globalIrrelevantPowQuotient_isLocalizedModule_id (𝒜 := 𝒜) zeroIso d
  letI : Module
      (Localization.AtPrime (irrelevantClosedPoint 𝒜 zeroIso).toPrimeSpectrum.asIdeal) G :=
    IsLocalizedModule.module
      (irrelevantClosedPoint 𝒜 zeroIso).toPrimeSpectrum.asIdeal.primeCompl
      (LinearMap.id : G →ₗ[S] G)
  obtain ⟨eLinear⟩ :=
    irrelevantLocalSuccessiveQuotient_linearEquiv_global (𝒜 := 𝒜) zeroIso (d := d)
  have hscalar :
      ∀ (a : Localization.AtPrime (irrelevantClosedPoint 𝒜 zeroIso).toPrimeSpectrum.asIdeal)
        (q : G), a • q = eRes (Ideal.Quotient.mk _ a) • q := by
    -- The scalar on the global quotient factors through the residue field.
    exact localizedGlobalIrrelevantPowQuotient_residueScalar_eq
      (𝒜 := 𝒜) hspan zeroIso eRes hresidueMk'
  simpa [G] using
    rank_toENat_eq_of_quotient_torsion_linearEquiv
      (R := Localization.AtPrime (irrelevantClosedPoint 𝒜 zeroIso).toPrimeSpectrum.asIdeal)
      (K := k) (N := G) hTorsion eRes eLinear hscalar

/-- Helper for Chap10 Lemma 10 117 1: after the local/global rank bridge, the local successive
quotient rank is the finrank of the degree piece. -/
private theorem localSuccessiveQuotient_rank_eq_degreePieceFinrank_of_eq
    (hgenerated : Algebra.adjoin (𝒜 0) (𝒜 1 : Set S) = ⊤)
    (hfiniteType : Algebra.FiniteType (𝒜 0) S)
    (zeroIso : k ≃ₐ[k] 𝒜 0) (d : ℕ)
    (P : Ideal S) [P.IsPrime]
    (hP : P = (irrelevantClosedPoint 𝒜 zeroIso).toPrimeSpectrum.asIdeal)
    (I : Ideal (Localization.AtPrime P))
    (hI : I = maximalIdeal (Localization.AtPrime P))
    (A : Submodule (Localization.AtPrime P) (Localization.AtPrime P))
    (hA : A = I ^ d • (⊤ : Submodule (Localization.AtPrime P) (Localization.AtPrime P)))
    (B : Submodule (Localization.AtPrime P) (Localization.AtPrime P))
    (hB : B = I ^ (d + 1) • (⊤ : Submodule (Localization.AtPrime P) (Localization.AtPrime P)))
    (hTorsion : Module.IsTorsionBySet (Localization.AtPrime P) (A ⧸ B.submoduleOf A) I) :
    letI : Module ((Localization.AtPrime P) ⧸ I) (A ⧸ B.submoduleOf A) := hTorsion.module
    Cardinal.toENat (Module.rank ((Localization.AtPrime P) ⧸ I) (A ⧸ B.submoduleOf A)) =
      (Module.finrank k (𝒜 d) : ℕ∞) := by
  -- Move the alias-facing statement to the canonical local point before doing rank comparisons.
  subst P
  subst I
  subst A
  subst B
  -- Compare first with the global quotient, then with the degree-`d` piece.
  have hspan : Ideal.span (𝒜 1 : Set S) = S₊.toIdeal :=
    span_degreeOne_eq_irrelevant_of_adjoin_eq_top (𝒜 := 𝒜) hgenerated
  obtain ⟨eRes, hresidueMk'⟩ :=
    exists_irrelevantLocalization_residueRingEquiv_apply_mk' (𝒜 := 𝒜) zeroIso
  letI : Nontrivial
      (Localization.AtPrime (irrelevantClosedPoint 𝒜 zeroIso).toPrimeSpectrum.asIdeal ⧸
        maximalIdeal (Localization.AtPrime (irrelevantClosedPoint 𝒜 zeroIso).toPrimeSpectrum.asIdeal)) :=
    eRes.toEquiv.nontrivial
  let G : Type u :=
    (S₊.toIdeal ^ d • (⊤ : Submodule S S) : Submodule S S) ⧸
      (S₊.toIdeal ^ (d + 1) • (⊤ : Submodule S S) : Submodule S S).submoduleOf
        (S₊.toIdeal ^ d • (⊤ : Submodule S S) : Submodule S S)
  have hlocalGlobalRank :=
    localSuccessiveQuotient_rank_eq_globalIrrelevantPowQuotient_rank
      (𝒜 := 𝒜) hspan zeroIso (d := d)
      (irrelevantClosedPoint 𝒜 zeroIso).toPrimeSpectrum.asIdeal rfl
      (maximalIdeal (Localization.AtPrime (irrelevantClosedPoint 𝒜 zeroIso).toPrimeSpectrum.asIdeal))
      rfl
      (maximalIdeal (Localization.AtPrime (irrelevantClosedPoint 𝒜 zeroIso).toPrimeSpectrum.asIdeal) ^ d •
        (⊤ : Submodule
          (Localization.AtPrime (irrelevantClosedPoint 𝒜 zeroIso).toPrimeSpectrum.asIdeal)
          (Localization.AtPrime (irrelevantClosedPoint 𝒜 zeroIso).toPrimeSpectrum.asIdeal)))
      rfl
      (maximalIdeal (Localization.AtPrime (irrelevantClosedPoint 𝒜 zeroIso).toPrimeSpectrum.asIdeal) ^ (d + 1) •
        (⊤ : Submodule
          (Localization.AtPrime (irrelevantClosedPoint 𝒜 zeroIso).toPrimeSpectrum.asIdeal)
          (Localization.AtPrime (irrelevantClosedPoint 𝒜 zeroIso).toPrimeSpectrum.asIdeal)))
      rfl eRes hresidueMk' hTorsion
  have hfiniteGlobal : Module.Finite k G := by
    -- The global quotient is finite over `S`, and its scalar action factors through `k`.
    simpa [G] using
      globalIrrelevantPowQuotient_finiteDimensional
        (𝒜 := 𝒜) hgenerated hfiniteType zeroIso d
  letI : Module.Finite k G := hfiniteGlobal
  obtain ⟨eGlobalDegree⟩ :=
    globalIrrelevantPowQuotient_linearEquiv_degreePiece (𝒜 := 𝒜) hspan d
  have hfiniteDegree : FiniteDimensional k (𝒜 d) := by
    -- The global degree-piece equivalence transports finite-dimensionality to `𝒜 d`.
    exact Module.Finite.equiv eGlobalDegree
  letI : FiniteDimensional k (𝒜 d) := hfiniteDegree
  have hglobalRank :
      Cardinal.toENat (Module.rank k G) = (Module.finrank k (𝒜 d) : ℕ∞) := by
    simpa [G] using
      globalIrrelevantPowQuotient_rank_eq_degreePieceFinrank_of_finite
        (𝒜 := 𝒜) hspan d
  exact hlocalGlobalRank.trans hglobalRank

/-- Helper for Chap10 Lemma 10 117 1: the remaining local associated-graded comparison identifies
the length of the local successive quotient with the dimension of the degree piece. -/
private theorem localSuccessiveQuotient_length_eq_degreePieceFinrank
    (hgenerated : Algebra.adjoin (𝒜 0) (𝒜 1 : Set S) = ⊤)
    (hfiniteType : Algebra.FiniteType (𝒜 0) S)
    (zeroIso : k ≃ₐ[k] 𝒜 0)
    (d : ℕ) :
    let P := (irrelevantClosedPoint 𝒜 zeroIso).toPrimeSpectrum.asIdeal
    let I : Ideal (Localization.AtPrime P) := maximalIdeal (Localization.AtPrime P)
    let A : Submodule (Localization.AtPrime P) (Localization.AtPrime P) :=
      I ^ d • (⊤ : Submodule (Localization.AtPrime P) (Localization.AtPrime P))
    let B : Submodule (Localization.AtPrime P) (Localization.AtPrime P) :=
      I ^ (d + 1) • (⊤ : Submodule (Localization.AtPrime P) (Localization.AtPrime P))
    Module.length (Localization.AtPrime P) (A ⧸ B.submoduleOf A) =
      (Module.finrank k (𝒜 d) : ℕ∞) := by
  -- Route correction: the earlier direct localized-denominator order-reflection route was too
  -- brittle. The rank comparison is now isolated in an alias-stable helper.
  let P := (irrelevantClosedPoint 𝒜 zeroIso).toPrimeSpectrum.asIdeal
  letI : P.IsPrime := by
    dsimp [P]
    exact (irrelevantClosedPoint 𝒜 zeroIso).toPrimeSpectrum.isPrime
  let I : Ideal (Localization.AtPrime P) := maximalIdeal (Localization.AtPrime P)
  let A : Submodule (Localization.AtPrime P) (Localization.AtPrime P) :=
    I ^ d • (⊤ : Submodule (Localization.AtPrime P) (Localization.AtPrime P))
  let B : Submodule (Localization.AtPrime P) (Localization.AtPrime P) :=
    I ^ (d + 1) • (⊤ : Submodule (Localization.AtPrime P) (Localization.AtPrime P))
  have hImax : I.IsMaximal := by
    dsimp [I]
    infer_instance
  letI : I.IsMaximal := hImax
  have hresidueNontrivial : Nontrivial ((Localization.AtPrime P) ⧸ I) :=
    Ideal.Quotient.nontrivial_iff.mpr hImax.ne_top
  letI : Nontrivial ((Localization.AtPrime P) ⧸ I) := hresidueNontrivial
  have hquotKilled :
      I • (⊤ : Submodule (Localization.AtPrime P) (A ⧸ B.submoduleOf A)) = ⊥ := by
    -- The successive quotient is annihilated by the maximal ideal, so its length is residue rank.
    simpa [A, B] using
      ideal_smul_successiveQuotient_eq_bot (Localization.AtPrime P) I d
  have hTorsion :
      Module.IsTorsionBySet (Localization.AtPrime P) (A ⧸ B.submoduleOf A) I := by
    -- Repackage annihilation by `I` into the canonical torsion-by-set hypothesis.
    rw [Module.isTorsionBySet_iff_subset_annihilator]
    rw [← Submodule.annihilator_top]
    change I ≤ (⊤ : Submodule (Localization.AtPrime P) (A ⧸ B.submoduleOf A)).annihilator
    exact Submodule.le_annihilator_iff.mpr hquotKilled
  letI : Module ((Localization.AtPrime P) ⧸ I) (A ⧸ B.submoduleOf A) := hTorsion.module
  have hlengthRank :
      Module.length (Localization.AtPrime P) (A ⧸ B.submoduleOf A) =
        (Module.rank ((Localization.AtPrime P) ⧸ I) (A ⧸ B.submoduleOf A)).toENat := by
    -- Apply the earlier length/rank theorem to the quotient killed by `I`.
    simpa using
      module_length_eq_rank_quotient_of_isTorsionBySet hTorsion
  have hrankDegree :
      (Module.rank ((Localization.AtPrime P) ⧸ I) (A ⧸ B.submoduleOf A)).toENat =
        (Module.finrank k (𝒜 d) : ℕ∞) := by
    -- The rank comparison helper handles the local/global bridge and the finite degree-piece step.
    simpa [P, I, A, B] using
      localSuccessiveQuotient_rank_eq_degreePieceFinrank_of_eq
        (𝒜 := 𝒜) hgenerated hfiniteType zeroIso d P rfl I rfl A rfl B rfl hTorsion
  -- The remaining local statement follows once the residue-rank comparison is available.
  simpa [P, I, A, B] using hlengthRank.trans hrankDegree

/-- If `S` is generated in degree `1`, finite type over `𝒜 0`, and `𝒜 0 ≃ k`, then the local ring
obtained by localizing at the irrelevant ideal `S₊.toIdeal` has the same Hilbert function as the
graded ring `S`: its Hilbert-Samuel `φ`-function is exactly `d ↦ dimₖ(S_d)`. -/
theorem hilbertSamuelPhi_eq_degreePieceFinrank_of_irrelevant_localization
    (hgenerated : Algebra.adjoin (𝒜 0) (𝒜 1 : Set S) = ⊤)
    (hfiniteType : Algebra.FiniteType (𝒜 0) S)
    (zeroIso : k ≃ₐ[k] 𝒜 0)
    (d : ℕ) :
    φ_
        (maximalIdeal
          (Localization.AtPrime (irrelevantClosedPoint 𝒜 zeroIso).toPrimeSpectrum.asIdeal))
        (Localization.AtPrime (irrelevantClosedPoint 𝒜 zeroIso).toPrimeSpectrum.asIdeal) d =
      (Module.finrank k (𝒜 d) : ℕ∞) := by
  let P := (irrelevantClosedPoint 𝒜 zeroIso).toPrimeSpectrum.asIdeal
  letI : P.IsPrime := by
    dsimp [P]
    exact (irrelevantClosedPoint 𝒜 zeroIso).toPrimeSpectrum.isPrime
  let I : Ideal (Localization.AtPrime P) := maximalIdeal (Localization.AtPrime P)
  let A : Submodule (Localization.AtPrime P) (Localization.AtPrime P) :=
    I ^ d • (⊤ : Submodule (Localization.AtPrime P) (Localization.AtPrime P))
  let B : Submodule (Localization.AtPrime P) (Localization.AtPrime P) :=
    I ^ (d + 1) • (⊤ : Submodule (Localization.AtPrime P) (Localization.AtPrime P))
  have hspan : Ideal.span (𝒜 1 : Set S) = S₊.toIdeal :=
    span_degreeOne_eq_irrelevant_of_adjoin_eq_top (𝒜 := 𝒜) hgenerated
  have hquotKilled :
      I • (⊤ : Submodule (Localization.AtPrime P) (A ⧸ B.submoduleOf A)) = ⊥ := by
    -- The local associated graded piece is a successive power quotient, so `I` annihilates it.
    simpa [A, B] using
      ideal_smul_successiveQuotient_eq_bot (Localization.AtPrime P) I d
  have hphiLength :
      φ_ I (Localization.AtPrime P) d =
        Module.length (Localization.AtPrime P) (A ⧸ B.submoduleOf A) := by
    -- Rewrite the Hilbert-Samuel `φ`-value as the length of the successive quotient.
    simpa [A, B] using
      hilbertSamuelPhi_eq_length_powSuccQuotient_top
        (Localization.AtPrime P) I d
  have hcalc :
      φ_ I (Localization.AtPrime P) d = (Module.finrank k (𝒜 d) : ℕ∞) := by
    calc
      φ_ I (Localization.AtPrime P) d =
          Module.length (Localization.AtPrime P) (A ⧸ B.submoduleOf A) := hphiLength
      _ = (Module.finrank k (𝒜 d) : ℕ∞) := by
        -- The remaining comparison is isolated in the closing helper; `hspan` and
        -- `hquotKilled` record the exact filtration and residue-field side conditions consumed
        -- by that helper.
        exact localSuccessiveQuotient_length_eq_degreePieceFinrank
          (𝒜 := 𝒜) hgenerated hfiniteType zeroIso d
  simpa [P, I] using hcalc

/-- Helper for Chap10 Lemma 10 117 1: a nontrivial local Noetherian ring has non-bottom
Hilbert-Samuel polynomial degree. -/
private theorem hilbertSamuelPolynomialDegree_ne_bot_of_nontrivial
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Nontrivial R] :
    hilbertSamuelPolynomialDegree R R ≠ (⊥ : WithBot ℕ) := by
  -- Compare the Hilbert-Samuel degree with Krull dimension, whose nontrivial local value is not
  -- bottom.
  have hle :
      ringKrullDim R ≤ Nat.castOrderEmbedding.withBotMap (hilbertSamuelPolynomialDegree R R) :=
    ringKrullDim_le_hilbertSamuelPolynomialDegree (R := R)
  have hdim_ne : ringKrullDim R ≠ (⊥ : WithBot ℕ∞) := ringKrullDim_ne_bot
  intro hbot
  have hlebot : ringKrullDim R ≤ (⊥ : WithBot ℕ∞) := by
    simpa [hbot] using hle
  exact hdim_ne (le_bot_iff.mp hlebot)

/-- Helper for Chap10 Lemma 10 117 1: the canonical `χ`-polynomial is nonzero over a nontrivial
local Noetherian ring. -/
private theorem hilbertSamuelChiPolynomial_ne_zero_of_nontrivial
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Nontrivial R] :
    hilbertSamuelChiPolynomial R R ≠ 0 := by
  -- If the polynomial were zero, its defining degree would be bottom, contradicting the previous
  -- local nontriviality consequence.
  intro hzero
  have hdeg_bot : hilbertSamuelPolynomialDegree R R = (⊥ : WithBot ℕ) := by
    simpa [hilbertSamuelPolynomialDegree, hzero]
  exact hilbertSamuelPolynomialDegree_ne_bot_of_nontrivial R hdeg_bot

/-- Helper for Chap10 Lemma 10 117 1: an eventual `χ`-polynomial gives the backward
finite-difference polynomial for the corresponding `φ`-function. -/
private theorem eventuallyEq_hilbertSamuelPhi_of_eventuallyEq_hilbertSamuelChi
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (I : Ideal R) (hI : I.IsIdealOfDefinition) {Q : Polynomial ℚ}
    (hQ : ∀ᶠ n : ℕ in atTop, Q.eval (n : ℚ) = ((χ_ I R n).toNat : ℚ)) :
    ∀ᶠ n : ℕ in atTop,
      (Q - Q.comp (Polynomial.X - Polynomial.C 1)).eval (n : ℚ) =
        ((φ_ I R n).toNat : ℚ) := by
  -- Work on a common tail where the eventual `χ`-formula holds at both `n` and `n - 1`.
  rcases eventually_atTop.mp hQ with ⟨N, hN⟩
  filter_upwards [eventually_ge_atTop (N + 1)] with n hn
  have hnpos : 0 < n := lt_of_lt_of_le (Nat.succ_pos N) hn
  have hQn : Q.eval (n : ℚ) = ((χ_ I R n).toNat : ℚ) := by
    exact hN n (le_trans (Nat.le_succ N) hn)
  have hQpred : Q.eval ((n - 1 : ℕ) : ℚ) = ((χ_ I R (n - 1)).toNat : ℚ) := by
    apply hN (n - 1)
    omega
  -- The public successor formula converts the difference of consecutive `χ`-values to `φ`.
  have hchiNat :
      (χ_ I R n).toNat = (χ_ I R (n - 1)).toNat + (φ_ I R n).toNat := by
    have hsucc :=
      hilbertSamuelChi_succ_toNat_eq_add_hilbertSamuelPhi_toNat_of_isIdealOfDefinition
        (R := R) (I := I) hI (n - 1)
    simpa [Nat.sub_add_cancel hnpos] using hsucc
  have hphi :
      ((φ_ I R n).toNat : ℚ) =
        ((χ_ I R n).toNat : ℚ) - ((χ_ I R (n - 1)).toNat : ℚ) := by
    have hchiRat :
        ((χ_ I R n).toNat : ℚ) =
          ((χ_ I R (n - 1)).toNat : ℚ) + ((φ_ I R n).toNat : ℚ) := by
      exact_mod_cast hchiNat
    linarith
  calc
    (Q - Q.comp (Polynomial.X - Polynomial.C 1)).eval (n : ℚ) =
        Q.eval (n : ℚ) - Q.eval ((n - 1 : ℕ) : ℚ) := by
      rw [Polynomial.eval_sub, Polynomial.eval_comp]
      simp [hnpos, sub_eq_add_neg]
    _ = ((φ_ I R n).toNat : ℚ) := by
      rw [hQn, hQpred, hphi]

/-- Helper for Chap10 Lemma 10 117 1: the first forward difference of a positive-degree
polynomial drops degree by one. -/
private theorem forwardDifference_degree_eq_sub_one_of_pos
    {Q : Polynomial ℚ} (hQdeg : 0 < Q.degree) :
    (Q.comp (Polynomial.X + Polynomial.C 1) - Q).degree = (Q.natDegree - 1 : ℕ) := by
  let D : Polynomial ℚ := Q.comp (Polynomial.X + Polynomial.C (1 : ℚ)) - Q
  have hQ0 : Q ≠ 0 := Polynomial.ne_zero_of_degree_gt hQdeg
  have hnatPos : 0 < Q.natDegree := by
    rw [Polynomial.degree_eq_natDegree hQ0, Nat.cast_pos] at hQdeg
    exact hQdeg
  -- Translation by `1` preserves degree and leading coefficient.
  have hlinearDegree : 0 < (Polynomial.X + Polynomial.C (1 : ℚ)).degree := by
    rw [Polynomial.degree_X_add_C (1 : ℚ)]
    decide
  have hdegComp :
      (Q.comp (Polynomial.X + Polynomial.C (1 : ℚ))).degree = Q.degree := by
    calc
      (Q.comp (Polynomial.X + Polynomial.C (1 : ℚ))).degree =
          Q.degree * (Polynomial.X + Polynomial.C (1 : ℚ)).degree := by
        exact Polynomial.degree_comp (p := Q) (q := Polynomial.X + Polynomial.C (1 : ℚ))
          hlinearDegree
      _ = Q.degree := by
        rw [Polynomial.degree_X_add_C (1 : ℚ)]
        simp
  have hlinearNatDegree : (Polynomial.X + Polynomial.C (1 : ℚ)).natDegree ≠ 0 := by
    rw [Polynomial.natDegree_X_add_C (1 : ℚ)]
    decide
  have hlcComp :
      (Q.comp (Polynomial.X + Polynomial.C (1 : ℚ))).leadingCoeff = Q.leadingCoeff := by
    rw [Polynomial.leadingCoeff_comp]
    · rw [Polynomial.leadingCoeff_X_add_C]
      simp
    · exact hlinearNatDegree
  have hUpperLt' : D.degree < (Q.comp (Polynomial.X + Polynomial.C (1 : ℚ))).degree := by
    -- The leading terms cancel in the translated difference.
    simpa [D] using
      (Polynomial.degree_sub_lt hdegComp
        ((Polynomial.comp_X_add_C_ne_zero_iff (p := Q) (t := (1 : ℚ))).2 hQ0)
        hlcComp)
  have hUpperLt : D.degree < Q.degree := by
    exact hdegComp ▸ hUpperLt'
  have hUpper : D.degree ≤ (Q.natDegree - 1 : ℕ) := by
    by_cases hD0 : D = 0
    · simp [hD0]
    · have hDnat : D.natDegree < Q.natDegree := by
        exact (Polynomial.natDegree_lt_iff_degree_lt hD0).2 <| by
          simpa [Polynomial.degree_eq_natDegree hQ0] using hUpperLt
      rw [Polynomial.degree_eq_natDegree hD0]
      exact WithBot.coe_le_coe.2 (Nat.le_pred_of_lt hDnat)
  have hLower : ((Q.natDegree - 1 : ℕ) : WithBot ℕ) ≤ D.degree := by
    -- A Hasse-derivative coefficient witnesses that degree `natDegree Q - 1` survives.
    let H : Polynomial ℚ := Polynomial.hasseDeriv (Q.natDegree - 1) Q
    have hcoeffComp :
        (Q.comp (Polynomial.X + Polynomial.C (1 : ℚ))).coeff (Q.natDegree - 1) =
          H.eval (1 : ℚ) := by
      simpa [H, Polynomial.taylor_apply] using
        (Polynomial.taylor_coeff (r := (1 : ℚ)) (f := Q) (n := Q.natDegree - 1))
    have hcoeffQ : Q.coeff (Q.natDegree - 1) = H.eval (0 : ℚ) := by
      simpa [H, Polynomial.taylor_apply] using
        (Polynomial.taylor_coeff (r := (0 : ℚ)) (f := Q) (n := Q.natDegree - 1))
    have hHnat : H.natDegree = 1 := by
      dsimp [H]
      rw [Polynomial.natDegree_hasseDeriv]
      omega
    have hHnatLe : H.natDegree ≤ 1 := by
      rw [hHnat]
    have hHdeg : H.degree ≤ 1 := by
      exact Polynomial.degree_le_of_natDegree_le hHnatLe
    have hHshape : H = Polynomial.C (H.coeff 1) * Polynomial.X + Polynomial.C (H.coeff 0) := by
      exact Polynomial.eq_X_add_C_of_degree_le_one hHdeg
    have hEvalDiff : H.eval (1 : ℚ) - H.eval (0 : ℚ) = H.coeff 1 := by
      rw [hHshape]
      simp
    have hcoeffH : H.coeff 1 = (Q.natDegree : ℚ) * Q.leadingCoeff := by
      dsimp [H]
      rw [Polynomial.hasseDeriv_coeff]
      have hpred : 1 + (Q.natDegree - 1) = Q.natDegree := by
        omega
      have hchoose : (1 + (Q.natDegree - 1)).choose (Q.natDegree - 1) = Q.natDegree := by
        have hchoose' :
            (1 + (Q.natDegree - 1)).choose (Q.natDegree - 1) = 1 + (Q.natDegree - 1) := by
          simpa [Nat.add_comm, Nat.succ_eq_add_one] using
            Nat.choose_succ_self_right (Q.natDegree - 1)
        rw [hchoose']
        omega
      rw [hchoose, hpred, Polynomial.leadingCoeff]
    have hcoeffNe : D.coeff (Q.natDegree - 1) ≠ 0 := by
      dsimp [D]
      rw [Polynomial.coeff_sub, hcoeffComp, hcoeffQ, hEvalDiff, hcoeffH]
      exact mul_ne_zero (by exact_mod_cast Nat.ne_of_gt hnatPos)
        (Polynomial.leadingCoeff_ne_zero.mpr hQ0)
    exact Polynomial.le_degree_of_ne_zero (n := Q.natDegree - 1) hcoeffNe
  change D.degree = (Q.natDegree - 1 : ℕ)
  exact le_antisymm hUpper hLower

/-- Helper for Chap10 Lemma 10 117 1: the first backward difference of a positive-degree
polynomial drops degree by one. -/
private theorem backwardDifference_degree_eq_sub_one_of_pos
    {Q : Polynomial ℚ} (hQdeg : 0 < Q.degree) :
    (Q - Q.comp (Polynomial.X - Polynomial.C 1)).degree = (Q.natDegree - 1 : ℕ) := by
  let Q₁ : Polynomial ℚ := Q.comp (Polynomial.X - Polynomial.C (1 : ℚ))
  -- Recast the backward difference as the forward difference of the translated polynomial.
  have hlinearDegree : 0 < (Polynomial.X - Polynomial.C (1 : ℚ)).degree := by
    rw [Polynomial.degree_X_sub_C (1 : ℚ)]
    decide
  have hQ₁deg : Q₁.degree = Q.degree := by
    calc
      Q₁.degree = (Q.comp (Polynomial.X - Polynomial.C (1 : ℚ))).degree := by
        rfl
      _ = Q.degree * (Polynomial.X - Polynomial.C (1 : ℚ)).degree := by
        exact Polynomial.degree_comp (p := Q) (q := Polynomial.X - Polynomial.C (1 : ℚ))
          hlinearDegree
      _ = Q.degree := by
        rw [Polynomial.degree_X_sub_C (1 : ℚ)]
        simp
  have hQ₁pos : 0 < Q₁.degree := by
    simpa [hQ₁deg] using hQdeg
  have hQ₁nat : Q₁.natDegree = Q.natDegree := by
    have hQ₁0 : Q₁ ≠ 0 := Polynomial.ne_zero_of_degree_gt hQ₁pos
    have hQ0 : Q ≠ 0 := Polynomial.ne_zero_of_degree_gt hQdeg
    exact WithBot.coe_eq_coe.mp <| by
      simpa [Polynomial.degree_eq_natDegree hQ₁0, Polynomial.degree_eq_natDegree hQ0] using hQ₁deg
  have hrewrite :
      Q₁.comp (Polynomial.X + Polynomial.C (1 : ℚ)) - Q₁ =
        Q - Q.comp (Polynomial.X - Polynomial.C (1 : ℚ)) := by
    simp [Q₁, Polynomial.comp_assoc, sub_eq_add_neg, add_left_comm, add_comm]
  rw [← hrewrite, forwardDifference_degree_eq_sub_one_of_pos hQ₁pos, hQ₁nat]

/-- Helper for Chap10 Lemma 10 117 1: a degree-at-most-zero polynomial has zero backward
difference. -/
private theorem backwardDifference_degree_eq_bot_of_degree_le_zero
    {Q : Polynomial ℚ} (hQdeg : Q.degree ≤ 0) :
    (Q - Q.comp (Polynomial.X - Polynomial.C 1)).degree = ⊥ := by
  -- Constants are unchanged by translation, so their backward difference is zero.
  rw [Polynomial.eq_C_of_degree_le_zero hQdeg]
  simp

/-- Helper for Chap10 Lemma 10 117 1: a nonzero polynomial's degree is the successor of the
backward-difference degree. -/
private theorem degree_eq_backwardDifference_degree_succ_of_ne_zero
    {Q : Polynomial ℚ} (hQne : Q ≠ 0) :
    Q.degree = (((Q - Q.comp (Polynomial.X - Polynomial.C 1)).degree.succ : ℕ) : WithBot ℕ) := by
  -- Positive degree uses the exact degree drop; the constant nonzero case is the bottom
  -- backward-difference edge case.
  by_cases hQpos : 0 < Q.degree
  · rw [backwardDifference_degree_eq_sub_one_of_pos hQpos]
    have hnatPos : 0 < Q.natDegree := by
      rw [Polynomial.degree_eq_natDegree hQne, Nat.cast_pos] at hQpos
      exact hQpos
    rw [Polynomial.degree_eq_natDegree hQne]
    have hsucc : Q.natDegree = (Q.natDegree - 1).succ := by
      omega
    exact_mod_cast hsucc
  · have hQle : Q.degree ≤ 0 := le_of_not_gt hQpos
    have hQdegree : Q.degree = (0 : WithBot ℕ) := by
      rw [Polynomial.degree_eq_natDegree hQne] at hQle ⊢
      exact le_antisymm hQle (by simp)
    rw [backwardDifference_degree_eq_bot_of_degree_le_zero hQle, hQdegree]
    rfl

/-- Helper for Chap10 Lemma 10 117 1: an eventual polynomial representative of the maximal-ideal
Hilbert-Samuel `φ`-function computes local Krull dimension by the successor of its degree. -/
theorem ringKrullDim_eq_phiPolynomial_degree_succ
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Nontrivial R]
    (P : Polynomial ℚ)
    (hP : ∀ᶠ d : ℕ in atTop,
      P.eval (d : ℚ) = ((φ_(maximalIdeal R) R d).toNat : ℚ)) :
    ringKrullDim R = P.degree.succ := by
  -- Turn the canonical `χ`-polynomial into an eventual representative for the local `φ`-function.
  let Q : Polynomial ℚ := hilbertSamuelChiPolynomial R R
  have hQevent :
      ∀ᶠ n : ℕ in atTop, Q.eval (n : ℚ) = ((χ_(maximalIdeal R) R n).toNat : ℚ) := by
    simpa [Q] using hilbertSamuelChiPolynomial_eventuallyEq R R
  have hQphi :
      ∀ᶠ n : ℕ in atTop,
        (Q - Q.comp (Polynomial.X - Polynomial.C 1)).eval (n : ℚ) =
          ((φ_(maximalIdeal R) R n).toNat : ℚ) :=
    eventuallyEq_hilbertSamuelPhi_of_eventuallyEq_hilbertSamuelChi
      R (maximalIdeal R) Ideal.maximalIdeal_isIdealOfDefinition hQevent
  -- Eventual representatives of the same Hilbert-Samuel `φ`-function have the same degree.
  have hPdeg : P.degree = (Q - Q.comp (Polynomial.X - Polynomial.C 1)).degree := by
    exact Ideal.hilbertSamuelPhi_degree_eq_of_isIdealOfDefinition
      (R := R) (M := R) (I := maximalIdeal R) (I' := maximalIdeal R)
      Ideal.maximalIdeal_isIdealOfDefinition Ideal.maximalIdeal_isIdealOfDefinition hP hQphi
  have hQne : Q ≠ 0 := by
    simpa [Q] using hilbertSamuelChiPolynomial_ne_zero_of_nontrivial R
  -- The backward finite difference shifts the nonzero `χ`-degree down by one, so its successor
  -- recovers the Hilbert-Samuel polynomial degree.
  have hdegree : hilbertSamuelPolynomialDegree R R = (P.degree.succ : WithBot ℕ) := by
    calc
      hilbertSamuelPolynomialDegree R R = Q.degree := by
        rfl
      _ = (((Q - Q.comp (Polynomial.X - Polynomial.C 1)).degree.succ : ℕ) : WithBot ℕ) := by
        exact degree_eq_backwardDifference_degree_succ_of_ne_zero hQne
      _ = (P.degree.succ : WithBot ℕ) := by
        rw [hPdeg]
  -- The local Hilbert-Samuel dimension theorem converts the degree statement to Krull dimension.
  exact ((local_noetherian_ring_dimension_tfae (R := R) P.degree.succ).out 0 1 rfl rfl).mpr
    hdegree

/-- Consequence of Chap10 Lemma 10 117 1: if `S` is generated in degree `1`, finite type over
`S₀`, and `S₀ ≃ k`, then any polynomial that eventually agrees with `d ↦ dimₖ(S_d)` computes the
dimension of `S` by the exact canonical degree formula `P.degree.succ`, which already gives `0`
for the zero polynomial. -/
@[stacks 00P6]
theorem ringKrullDim_eq_degree_succ_of_eventuallyEq_degreePieceFinrank
    (hgenerated : Algebra.adjoin (𝒜 0) (𝒜 1 : Set S) = ⊤)
    (hfiniteType : Algebra.FiniteType (𝒜 0) S)
    (zeroIso : k ≃ₐ[k] 𝒜 0)
    (P : Polynomial ℚ)
    (hP : ∀ᶠ d : ℕ in atTop,
      P.eval (d : ℚ) = (Module.finrank k (𝒜 d) : ℚ)) :
    ringKrullDim S = P.degree.succ := by
  letI : Algebra.FiniteType k S :=
    finiteType_of_degreeZeroIso 𝒜 hfiniteType zeroIso
  let Rloc := Localization.AtPrime (irrelevantClosedPoint 𝒜 zeroIso).toPrimeSpectrum.asIdeal
  haveI : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing k S
  haveI : IsNoetherianRing Rloc :=
    IsLocalization.isNoetherianRing
      (irrelevantClosedPoint 𝒜 zeroIso).toPrimeSpectrum.asIdeal.primeCompl Rloc inferInstance
  have hphiP :
      ∀ᶠ d : ℕ in atTop,
        P.eval (d : ℚ) =
          ((φ_(maximalIdeal Rloc) Rloc d).toNat : ℚ) := by
    -- Rewrite the given graded Hilbert function into the local Hilbert-Samuel `φ`-function.
    filter_upwards [hP] with d hd
    have hphi :
        φ_(maximalIdeal Rloc) Rloc d =
          (Module.finrank k (𝒜 d) : ℕ∞) := by
      simpa [Rloc] using
        hilbertSamuelPhi_eq_degreePieceFinrank_of_irrelevant_localization
          𝒜 hgenerated hfiniteType zeroIso d
    simpa [hphi] using hd
  -- Apply the local Hilbert-polynomial dimension formula, then transport back to `S`.
  calc
    ringKrullDim S = ringKrullDim Rloc := by
      simpa [Rloc] using
        ringKrullDim_eq_ringKrullDim_irrelevant_localization 𝒜 hfiniteType zeroIso
    _ = P.degree.succ := by
      exact ringKrullDim_eq_phiPolynomial_degree_succ Rloc P hphiP

end
