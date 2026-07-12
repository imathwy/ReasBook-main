import StacksProject_2024.Chap10.Lemma_10_70_3.ReesLocalization

open HomogeneousLocalization
open IsLocalization
open Polynomial
open scoped AffineBlowupChart DirectSum TensorProduct

universe u v w

section

variable {R : Type u} [CommRing R]

/-- Helper for Lemma 10.70.3: the extension of an ideal along a base-change ring map. -/
abbrev idealBaseChange {S : Type v} [CommRing S] [Algebra R S] (I : Ideal R) : Ideal S :=
  Ideal.map (algebraMap R S) I

/-- Helper for Lemma 10.70.3: the image of the distinguished element in the extended ideal. -/
abbrev idealBaseChangeElement {S : Type v} [CommRing S] [Algebra R S]
    (I : Ideal R) (a : I) : idealBaseChange (S := S) I :=
  mappedIdealElement I a

/-- Helper for Lemma 10.70.3: the raw target of the graded base-change map before transporting the
codomain to the standard target chart. -/
private abbrev affineBlowupChartBaseChangeRawTarget {S : Type v} [CommRing S] [Algebra R S]
    (I : Ideal R) (a : I) :=
  Away (reesAlgebraGrade (idealBaseChange (S := S) I))
    ((reesAlgebraBaseChangeGradedHom I) (reesAlgebraDegreeOne I a))

/-- Helper for Lemma 10.70.3: the standard affine blowup chart attached to the extended ideal. -/
abbrev affineBlowupChartBaseChangeTarget {S : Type v} [CommRing S] [Algebra R S]
    (I : Ideal R) (a : I) :=
  affineBlowupChart (idealBaseChange (S := S) I) (idealBaseChangeElement (S := S) I a)

/-- Helper for Chap10 Lemma 10 70 3: the base-change graded map sends the source chart
denominator to the standard target chart denominator. -/
private theorem affineBlowupChartBaseChange_denominator_eq
    {S : Type v} [CommRing S] [Algebra R S] (I : Ideal R) (a : I) :
    (reesAlgebraBaseChangeGradedHom (S := S) I) (reesAlgebraDegreeOne I a) =
      reesAlgebraDegreeOne (idealBaseChange (S := S) I)
        (idealBaseChangeElement (S := S) I a) := by
  simpa [idealBaseChange, idealBaseChangeElement] using
    reesAlgebraBaseChange_degreeOne (S := S) I a

/-- Helper for Lemma 10.70.3: the canonical degree-zero class in the raw target chart attached to
the scalar `r`. -/
private noncomputable abbrev affineBlowupChartBaseChangeRawScalar {S : Type v} [CommRing S]
    [Algebra R S]
    (I : Ideal R) (a : I) (r : R) : affineBlowupChartBaseChangeRawTarget (S := S) I a :=
  HomogeneousLocalization.fromZeroRingHom
    (reesAlgebraGrade (idealBaseChange (S := S) I))
    (Submonoid.powers ((reesAlgebraBaseChangeGradedHom I) (reesAlgebraDegreeOne I a)))
    (reesAlgebraBaseChangeZeroDegreeCoeff (S := S) I r)

/-- Helper for Lemma 10.70.3: the graded base-change map sends the distinguished source
degree-one parameter to the distinguished target degree-one parameter, so the raw `Away.map`
codomain is the standard target chart. -/
private theorem affineBlowupChartBaseChange_codomain_eq
    {S : Type v} [CommRing S] [Algebra R S] (I : Ideal R) (a : I) :
    Away (reesAlgebraGrade (Ideal.map (algebraMap R S) I))
        ((reesAlgebraBaseChangeGradedHom I) (reesAlgebraDegreeOne I a)) =
      affineBlowupChart (Ideal.map (algebraMap R S) I) (mappedIdealElement I a) := by
  simpa [affineBlowupChart] using
    congrArg (fun y ↦ Away (reesAlgebraGrade (Ideal.map (algebraMap R S) I)) y)
      (reesAlgebraBaseChange_degreeOne (S := S) I a)

/-- Helper for Chap10 Lemma 10 70 3: powers of the source denominator map into powers of the
standard target denominator. -/
private theorem reesAlgebraBaseChange_powers_le
    {S : Type v} [CommRing S] [Algebra R S] (I : Ideal R) (a : I) :
    Submonoid.powers (reesAlgebraDegreeOne I a) ≤
      (Submonoid.powers
        (reesAlgebraDegreeOne (idealBaseChange (S := S) I)
          (idealBaseChangeElement (S := S) I a))).comap
        (reesAlgebraBaseChangeGradedHom (S := S) I) := by
  intro x hx
  rcases hx with ⟨n, rfl⟩
  refine ⟨n, ?_⟩
  rw [map_pow, affineBlowupChartBaseChange_denominator_eq (S := S) I a]

/-- Helper for Lemma 10.70.3: the homogeneous-localization ring homomorphism underlying the
base-change chart map. -/
private noncomputable def affineBlowupChartBaseChangeMap_toRingHom {S : Type v} [CommRing S]
    [Algebra R S] (I : Ideal R) (a : I) :
    R[I / a] →+* affineBlowupChartBaseChangeTarget (S := S) I a :=
  HomogeneousLocalization.map (reesAlgebraBaseChangeGradedHom (S := S) I)
    (reesAlgebraBaseChange_powers_le (S := S) I a)

/-- Helper for Lemma 10.70.3: the target chart’s `R`-algebra map is the composite of the scalar
extension map `R → S` with the target chart’s canonical `S`-algebra map. -/
private theorem affineBlowupChartBaseChange_target_algebraMap_eq
    {S : Type v} [CommRing S] [Algebra R S] (I : Ideal R) (a : I) (r : R) :
    algebraMap R (affineBlowupChartBaseChangeTarget (S := S) I a) r =
      algebraMap S (affineBlowupChartBaseChangeTarget (S := S) I a) (algebraMap R S r) := by
  -- The auxiliary `R`-algebra structure on the target chart is defined by this composite.
  rfl

/-- Helper for Lemma 10.70.3: the target chart carries the expected scalar tower
`R → S → S[IS/b]`. -/
private instance affineBlowupChartBaseChangeTarget_isScalarTower
    {S : Type v} [CommRing S] [Algebra R S] {I : Ideal R} {a : I} :
    IsScalarTower R S (affineBlowupChartBaseChangeTarget (S := S) I a) := by
  constructor
  intro r s x
  rw [Algebra.smul_def]
  apply HomogeneousLocalization.val_injective
  rw [show r • (s • x) =
      algebraMap R (affineBlowupChartBaseChangeTarget (S := S) I a) r * (s • x) by
        exact Algebra.smul_def r (s • x)]
  rw [HomogeneousLocalization.val_mul]
  rw [HomogeneousLocalization.val_smul
    (x := Submonoid.powers
      (reesAlgebraDegreeOne (idealBaseChange (S := S) I)
        (idealBaseChangeElement (S := S) I a)))
    (n := s) x]
  rw [affineBlowupChartBaseChange_target_algebraMap_eq]
  rw [HomogeneousLocalization.val_smul
    (x := Submonoid.powers
      (reesAlgebraDegreeOne (idealBaseChange (S := S) I)
        (idealBaseChangeElement (S := S) I a)))
    (n := (algebraMap R S r * s)) x]
  have hval_algebraMap (t : S) :
      HomogeneousLocalization.val
          (algebraMap S (affineBlowupChartBaseChangeTarget (S := S) I a) t) =
        algebraMap S
          (Localization (Submonoid.powers
            (reesAlgebraDegreeOne (idealBaseChange (S := S) I)
              (idealBaseChangeElement (S := S) I a)))) t := by
    rw [affineBlowupChart_algebraMap_eq_fromZeroRingHom]
    simpa [reesAlgebraZeroDegreeCoeff_generic] using
      homogeneousLocalization_val_fromZeroRingHom
        (𝒜 := reesAlgebraGrade (idealBaseChange (S := S) I))
        (P := Submonoid.powers
          (reesAlgebraDegreeOne (idealBaseChange (S := S) I)
            (idealBaseChangeElement (S := S) I a)))
        (a := reesAlgebraZeroDegreeCoeff_generic (idealBaseChange (S := S) I) t)
  rw [hval_algebraMap]
  repeat rw [Algebra.smul_def]
  rw [map_mul, mul_assoc]

/-- Helper for Lemma 10.70.3: the canonical `S`-algebra map into the target chart, used as the
left leg of the tensor-product comparison morphism. -/
private noncomputable def affineBlowupChartBaseChange_targetAlgHom
    {S : Type v} [CommRing S] [Algebra R S] (I : Ideal R) (a : I) :
    S →ₐ[S] affineBlowupChartBaseChangeTarget (S := S) I a :=
  -- Freeze the target `S`-algebra structure before forming the tensor lift.
  Algebra.ofId S (affineBlowupChartBaseChangeTarget (S := S) I a)

set_option maxHeartbeats 1000000 in
/-- Helper for Lemma 10.70.3: the base-change chart map is compatible with the `R`-algebra
structures because the graded base-change map is the identity on degree zero after transporting
coefficients along `R → S`. -/
private theorem affineBlowupChartBaseChangeMap_commutes
    {S : Type v} [CommRing S] [Algebra R S] (I : Ideal R) (a : I) (r : R) :
    affineBlowupChartBaseChangeMap_toRingHom (S := S) I a
        (algebraMap R (R[I / a]) r) =
      algebraMap R (affineBlowupChartBaseChangeTarget (S := S) I a) r := by
  rw [affineBlowupChartBaseChange_target_algebraMap_eq]
  rw [affineBlowupChart_algebraMap_eq_fromZeroRingHom]
  rw [affineBlowupChart_algebraMap_eq_fromZeroRingHom]
  simpa [affineBlowupChartBaseChangeMap_toRingHom,
    reesAlgebraBaseChange_zeroDegree_algebraMap_generic (S := S) I r,
    reesAlgebraBaseChangeZeroDegreeCoeff_eq_generic (S := S) I r] using
    homogeneousLocalization_map_fromZeroRingHom (reesAlgebraGrade I)
      (reesAlgebraGrade (idealBaseChange (S := S) I))
      (reesAlgebraBaseChangeGradedHom (S := S) I)
      (reesAlgebraBaseChange_powers_le (S := S) I a)
      (reesAlgebraZeroDegreeCoeff_generic I r)

/-- Helper for Lemma 10.70.3: the graded base-change map sends a normalized monomial numerator in
the Rees algebra of `I` to the corresponding normalized monomial numerator in the Rees algebra of
`IS`. -/
private theorem reesAlgebraBaseChange_monomial
    {S : Type v} [CommRing S] [Algebra R S] (I : Ideal R) (n : ℕ) (x : ↥(I ^ n)) :
    reesAlgebraBaseChangeGradedHom (S := S) I
        (⟨Polynomial.monomial n x.1, (reesAlgebra.monomial_mem).2 x.2⟩ : reesAlgebra I) =
      (⟨Polynomial.monomial n (algebraMap R S x.1),
        (reesAlgebra.monomial_mem).2 (by
          simpa [Ideal.map_pow] using
            (Ideal.mem_map_of_mem (algebraMap R S) x.2 :
              algebraMap R S x.1 ∈ Ideal.map (algebraMap R S) (I ^ n)))⟩ :
        reesAlgebra (Ideal.map (algebraMap R S) I)) := by
  -- The graded base-change map only applies the coefficient map to the chosen monomial.
  apply Subtype.ext
  simp [reesAlgebraBaseChangeGradedHom, reesAlgebraMap]

/-- Helper for Lemma 10.70.3: the explicit `AlgHom` underlying the affine-blowup-chart
base-change map. -/
private noncomputable def affineBlowupChartBaseChangeMapAlgHom
    {S : Type v} [CommRing S] [Algebra R S] (I : Ideal R) (a : I) :
    R[I / a] →ₐ[R] affineBlowupChartBaseChangeTarget (S := S) I a :=
  { toRingHom :=
      by
        exact affineBlowupChartBaseChangeMap_toRingHom (S := S) I a
    commutes' := by
      intro r
      simpa [affineBlowupChartBaseChangeTarget] using
        affineBlowupChartBaseChangeMap_commutes (S := S) I a r }

/-- The canonical affine-blowup-chart map induced by a base change `R → S`. -/
noncomputable def affineBlowupChartBaseChangeMap {S : Type v} [CommRing S] [Algebra R S]
    (I : Ideal R) (a : I) :
    let J : Ideal S := Ideal.map (algebraMap R S) I
    let b : J := mappedIdealElement I a
    R[I / a] →ₐ[R] S[J / b] :=
  affineBlowupChartBaseChangeMapAlgHom (S := S) I a

/-- Helper for Chap10 Lemma 10 70 3: the target affine blowup chart is an algebra over the source chart via base change. -/
private noncomputable instance instAlgebraAffineBlowupChartBaseChange {S : Type v} [CommRing S]
    [Algebra R S]
    (I : Ideal R) (a : I) :
    Algebra R[I / a] (affineBlowupChart (Ideal.map (algebraMap R S) I) (mappedIdealElement I a)) :=
  let φ : R[I / a] →ₐ[R] affineBlowupChart (Ideal.map (algebraMap R S) I) (mappedIdealElement I a) :=
    affineBlowupChartBaseChangeMap (S := S) I a
  φ.toAlgebra

/-- Helper for Lemma 10.70.3: the tensor comparison map is the tensor-product lift of the left
scalar map `S → S[J/b]` and the right chart map `R[I/a] → S[J/b]`. -/
private theorem tensorToAffineBlowupAlgebra_spec
    (S : Type v) [CommRing S] [Algebra R S] (I : Ideal R) (a : I) :
    ∃ φ : S ⊗[R] R[I / a] →ₐ[S] affineBlowupChartBaseChangeTarget (S := S) I a,
      ∀ s : S, ∀ x : R[I / a],
        φ (s ⊗ₜ[R] x) =
          algebraMap S (affineBlowupChartBaseChangeTarget (S := S) I a) s *
            affineBlowupChartBaseChangeMap (S := S) I a x := by
  let leftR : S →ₐ[R] affineBlowupChartBaseChangeTarget (S := S) I a :=
    { toRingHom := algebraMap S (affineBlowupChartBaseChangeTarget (S := S) I a)
      commutes' := by
        intro r
        exact (affineBlowupChartBaseChange_target_algebraMap_eq (S := S) I a r).symm }
  let φR : S ⊗[R] R[I / a] →ₐ[R] affineBlowupChartBaseChangeTarget (S := S) I a :=
    Algebra.TensorProduct.lift
      leftR
      (affineBlowupChartBaseChangeMap (S := S) I a)
      (fun _ _ ↦ Commute.all _ _)
  let φ : S ⊗[R] R[I / a] →ₐ[S] affineBlowupChartBaseChangeTarget (S := S) I a :=
    { toRingHom := φR.toRingHom
      commutes' := by
        intro s
        change φR (s ⊗ₜ[R] (1 : R[I / a])) =
          algebraMap S (affineBlowupChartBaseChangeTarget (S := S) I a) s
        rw [Algebra.TensorProduct.lift_tmul]
        simp [leftR] }
  refine ⟨φ, ?_⟩
  intro s x
  -- Evaluate the tensor-product lift on a pure tensor and simplify the left factor.
  change
    Algebra.TensorProduct.lift
        leftR
        (affineBlowupChartBaseChangeMap (S := S) I a)
        (fun _ _ ↦ Commute.all _ _)
        (s ⊗ₜ[R] x) =
      algebraMap S (affineBlowupChartBaseChangeTarget (S := S) I a) s *
        affineBlowupChartBaseChangeMap (S := S) I a x
  rw [Algebra.TensorProduct.lift_tmul]
  simp [leftR]

/-- The canonical base-change map
`S ⊗[R] R[I/a] → S[J/b]`, where `J = Ideal.map (algebraMap R S) I` and `b ∈ J` is the image of
`a`. -/
noncomputable def tensorToAffineBlowupAlgebra
    (S : Type v) [CommRing S] [Algebra R S] (I : Ideal R) (a : I) :
    let J : Ideal S := Ideal.map (algebraMap R S) I
    let b : J := mappedIdealElement I a
    S ⊗[R] R[I / a] →ₐ[S] S[J / b] :=
  Classical.choose (tensorToAffineBlowupAlgebra_spec S I a)

/-- Helper for Lemma 10.70.3: on a pure tensor, the base-change comparison map is the product of
the scalar image from `S` and the chart image from `R[I/a]`. -/
theorem tensorToAffineBlowupAlgebra_tmul
    (S : Type v) [CommRing S] [Algebra R S] (I : Ideal R) (a : I)
    (s : S) (x : R[I / a]) :
    let J : Ideal S := Ideal.map (algebraMap R S) I
    let b : J := mappedIdealElement I a
    tensorToAffineBlowupAlgebra S I a (s ⊗ₜ[R] x) =
      algebraMap S S[J / b] s * affineBlowupChartBaseChangeMap (S := S) I a x := by
  -- Read off the computation rule from the tensor-lift specification.
  simpa [tensorToAffineBlowupAlgebra] using
    (Classical.choose_spec (tensorToAffineBlowupAlgebra_spec S I a) s x)

/-- Helper for Lemma 10.70.3: on the pure tensor `1 ⊗ x`, the tensor comparison map reduces to
the chart base-change map on the right factor. -/
theorem tensorToAffineBlowupAlgebra_one_tmul
    (S : Type v) [CommRing S] [Algebra R S] (I : Ideal R) (a : I) (x : R[I / a]) :
    tensorToAffineBlowupAlgebra S I a (1 ⊗ₜ[R] x) =
      affineBlowupChartBaseChangeMap (S := S) I a x := by
  -- Specialize the pure-tensor formula to the unit scalar and simplify the left factor.
  simpa using tensorToAffineBlowupAlgebra_tmul S I a 1 x

/-- Helper for Lemma 10.70.3: the base-change tensor map sends the distinguished source parameter
to the distinguished chart parameter in the target. -/
theorem tensorToAffineBlowupAlgebra_parameter_image
    (S : Type v) [CommRing S] [Algebra R S] (I : Ideal R) (a : I) :
    let J : Ideal S := Ideal.map (algebraMap R S) I
    let b : J := mappedIdealElement I a
    (tensorToAffineBlowupAlgebra S I a) (algebraMap R (S ⊗[R] R[I / a]) a.1) =
      algebraMap S S[J / b] b.1 := by
  -- Rewrite the source scalar in the tensor product as `(algebraMap R S a) ⊗ 1` and evaluate the
  -- tensor comparison map on that pure tensor.
  dsimp
  change
    tensorToAffineBlowupAlgebra S I a ((algebraMap R S a.1) ⊗ₜ[R] (1 : R[I / a])) =
      algebraMap S (affineBlowupChartBaseChangeTarget (S := S) I a) (algebraMap R S a.1)
  rw [tensorToAffineBlowupAlgebra_tmul]
  rw [map_one, mul_one]

/-- Helper for Lemma 10.70.3: the base-changed chart map sends a source basic fraction to the
corresponding target basic fraction. -/
theorem affineBlowupChartBaseChangeMap_basicFraction
    (S : Type v) [CommRing S] [Algebra R S] (I : Ideal R) (a x : I) :
    let J : Ideal S := Ideal.map (algebraMap R S) I
    let b : J := mappedIdealElement I a
    affineBlowupChartBaseChangeMap (S := S) I a (affineBlowupChartBasicFraction I a x) =
      affineBlowupChartBasicFraction J b (mappedIdealElement I x) := by
  -- Compute the raw `Away.map` on the degree-one fraction and then transport once to the
  -- standard target chart.
  dsimp [affineBlowupChartBaseChangeMap, affineBlowupChartBaseChangeMapAlgHom]
  change (affineBlowupChartBaseChangeMap_toRingHom (S := S) I a)
      (affineBlowupChartBasicFraction I a x) = _
  rw [affineBlowupChartBaseChangeMap_toRingHom, affineBlowupChartBasicFraction,
    HomogeneousLocalization.Away.mk]
  rw [HomogeneousLocalization.map_mk]
  simpa [affineBlowupChartBasicFraction, HomogeneousLocalization.Away.mk,
    reesAlgebraBaseChange_degreeOne (S := S) I x,
    reesAlgebraBaseChange_degreeOne (S := S) I a, affineBlowupChartBaseChangeTarget,
    idealBaseChange, idealBaseChangeElement, affineBlowupChart, mappedIdealElement]

/-- Helper for Lemma 10.70.3: the base-changed chart map preserves normalized degree-`n`
fractions. -/
theorem affineBlowupChartBaseChangeMap_powerFraction
    (S : Type v) [CommRing S] [Algebra R S] (I : Ideal R) (a : I) (n : ℕ)
    (x : ↥(I ^ n)) :
    let J : Ideal S := Ideal.map (algebraMap R S) I
    let b : J := mappedIdealElement I a
    let xJ : ↥(J ^ n) :=
      ⟨algebraMap R S x.1, by
        simpa [J, Ideal.map_pow] using
          (Ideal.mem_map_of_mem (algebraMap R S) x.2 :
            algebraMap R S x.1 ∈ Ideal.map (algebraMap R S) (I ^ n))⟩
    affineBlowupChartBaseChangeMap (S := S) I a
        (affineBlowupChartPowerFraction I a n x) =
      affineBlowupChartPowerFraction J b n xJ := by
  -- Compute the raw `Away.map` on the normalized monomial fraction and rewrite the mapped
  -- monomial numerator through the graded base-change map.
  dsimp [affineBlowupChartBaseChangeMap, affineBlowupChartBaseChangeMapAlgHom]
  change (affineBlowupChartBaseChangeMap_toRingHom (S := S) I a)
      (affineBlowupChartPowerFraction I a n x) = _
  rw [affineBlowupChartBaseChangeMap_toRingHom, affineBlowupChartPowerFraction,
    HomogeneousLocalization.Away.mk]
  rw [HomogeneousLocalization.map_mk]
  simpa [affineBlowupChartPowerFraction, HomogeneousLocalization.Away.mk,
    reesAlgebraBaseChange_monomial (S := S) I n x,
    reesAlgebraBaseChange_degreeOne (S := S) I a, affineBlowupChartBaseChangeTarget,
    idealBaseChange, idealBaseChangeElement, affineBlowupChart]

/-- Helper for Lemma 10.70.3: on a pure tensor `s ⊗ x/a`, the tensor comparison map multiplies
the target basic fraction by the scalar `s`. -/
theorem tensorToAffineBlowupAlgebra_tmul_basicFraction
    (S : Type v) [CommRing S] [Algebra R S] (I : Ideal R) (a x : I) (s : S) :
    let J : Ideal S := Ideal.map (algebraMap R S) I
    let b : J := mappedIdealElement I a
    tensorToAffineBlowupAlgebra S I a (s ⊗ₜ[R] affineBlowupChartBasicFraction I a x) =
      algebraMap S S[J / b] s * affineBlowupChartBasicFraction J b (mappedIdealElement I x) := by
  -- Evaluate the tensor-product lift on the pure tensor and rewrite the right factor with the
  -- chart base-change formula on basic fractions.
  rw [tensorToAffineBlowupAlgebra_tmul, affineBlowupChartBaseChangeMap_basicFraction]

/-- Helper for Lemma 10.70.3: on a pure tensor `s ⊗ x/a^n`, the tensor comparison map multiplies
the target normalized degree-`n` fraction by the scalar `s`. -/
theorem tensorToAffineBlowupAlgebra_tmul_powerFraction
    (S : Type v) [CommRing S] [Algebra R S] (I : Ideal R) (a : I) (n : ℕ)
    (x : ↥(I ^ n)) (s : S) :
    let J : Ideal S := Ideal.map (algebraMap R S) I
    let b : J := mappedIdealElement I a
    let xJ : ↥(J ^ n) :=
      ⟨algebraMap R S x.1, by
        simpa [J, Ideal.map_pow] using
          (Ideal.mem_map_of_mem (algebraMap R S) x.2 :
            algebraMap R S x.1 ∈ Ideal.map (algebraMap R S) (I ^ n))⟩
    tensorToAffineBlowupAlgebra S I a (s ⊗ₜ[R] affineBlowupChartPowerFraction I a n x) =
      algebraMap S S[J / b] s * affineBlowupChartPowerFraction J b n xJ := by
  -- Evaluate the tensor-product lift on the pure tensor and rewrite the right factor with the
  -- chart base-change formula on normalized power fractions.
  rw [tensorToAffineBlowupAlgebra_tmul, affineBlowupChartBaseChangeMap_powerFraction]

end
