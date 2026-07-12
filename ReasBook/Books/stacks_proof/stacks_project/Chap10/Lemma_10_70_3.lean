import StacksProject_2024.Chap10.Lemma_10_70_3.TargetSurjectivity

-- Declarations for this item will be appended below by the statement pipeline.

open HomogeneousLocalization
open IsLocalization
open Polynomial
open scoped AffineBlowupChart DirectSum TensorProduct

universe u v w

section

variable {R : Type u} [CommRing R]

/-
Domain-style sampling pass for Lemma 10.70.3.

Primary domain: commutative algebra of affine blowup charts under flat base change.

Sampled owner declarations:
* `affineBlowupChart` from `Definition_10_70_1.lean`;
* `affineBlowupChartScaledMap_surjective_and_ker_eq_f_power_torsion` from
  `Lemma_10_70_8.lean`;
* `Ideal.primaryComponent_mem` and `Submodule.mem_torsionBySet_iff` from mathlib's torsion API.

Owner abstraction: the affine blowup chart `R[I/a]`, with the canonical base-change map
`tensorToAffineBlowupAlgebra : S ⊗[R] R[I/a] → S[IS/b]`.
Primitive data here are the induced ideal `Ideal.map (algebraMap R S) I`, the distinguished image
`mappedIdealElement I a`, and the comparison map on blowup charts. The primary-component equality
is derived API; the source-facing statement is the torsion description of the kernel.

Source/core/bridge triage:
* source-facing: the surjective base-change map with kernel given by powers of the distinguished
  tensor image of `a`;
* core/canonical: the same kernel as a primary component;
* bridge/view: `tensorToAffineBlowupAlgebra`.
-/

/-- Helper for Chap10 Lemma 10 70 3: powers map into powers under base change. -/
private theorem powers_map_le_comap
    (S : Type v) [CommRing S] [Algebra R S] (r : R) :
    Submonoid.powers r ≤ (Submonoid.powers (algebraMap R S r)).comap (algebraMap R S) := by
  -- A power of `r` maps to the same power of the image of `r`.
  intro x hx
  rw [Submonoid.mem_comap]
  rcases (Submonoid.mem_powers_iff x r).mp hx with ⟨n, rfl⟩
  rw [map_pow]
  exact Submonoid.pow_mem _
    ((Submonoid.mem_powers_iff _ _).mpr ⟨1, by simp⟩) n

/-- Helper for Chap10 Lemma 10 70 3: base change induces an algebra map
`Localization.Away r → Localization.Away (algebraMap R S r)`. -/
private noncomputable instance localizationAwayBaseChangeAlgebra
    (S : Type v) [CommRing S] [Algebra R S] (r : R) :
    Algebra (Localization.Away r) (Localization.Away (algebraMap R S r)) :=
  (IsLocalization.map (Localization.Away (algebraMap R S r)) (algebraMap R S)
    (powers_map_le_comap S r)).toAlgebra

/-- Helper for Chap10 Lemma 10 70 3: the induced map
`R_r → S_{algebraMap R S r}` sends `x / r^n` to `algebraMap R S x / algebraMap R S r^n`. -/
private theorem localizationAwayBaseChangeAlgebra_mk
    (S : Type v) [CommRing S] [Algebra R S] (r x : R) (n : ℕ) :
    algebraMap (Localization.Away r) (Localization.Away (algebraMap R S r))
        (Localization.mk x ⟨r ^ n, by exact ⟨n, rfl⟩⟩) =
      Localization.mk (algebraMap R S x)
        ⟨(algebraMap R S r) ^ n, by exact ⟨n, rfl⟩⟩ := by
  -- Freeze the localization-map computation once, so later tensor formulas can rewrite by name.
  change (IsLocalization.map (Localization.Away (algebraMap R S r)) (algebraMap R S)
      (powers_map_le_comap S r)) (Localization.mk x ⟨r ^ n, by exact ⟨n, rfl⟩⟩) = _
  rw [Localization.mk_eq_mk'_apply]
  rw [IsLocalization.map_mk']
  rw [Localization.mk_eq_mk'_apply]
  congr 1
  ext
  simp [map_pow]

/-- Helper for Chap10 Lemma 10 70 3: the left-oriented tensor-away equivalence sends
`s ⊗ 1` to the scalar image of `s`. -/
private theorem tensorAwayEquiv_tmul_one
    (S : Type v) [CommRing S] [Algebra R S] (r : R) (s : S) :
    (IsLocalization.Away.tensorEquiv S r (Localization.Away r))
        (s ⊗ₜ[R] (1 : Localization.Away r)) =
      algebraMap S (Localization.Away (algebraMap R S r)) s := by
  -- This is the `S`-algebra map computation for the tensor-away equivalence.
  change (IsLocalization.Away.tensorEquiv S r (Localization.Away r))
      (algebraMap S (S ⊗[R] Localization.Away r) s) = _
  exact (IsLocalization.Away.tensorEquiv S r (Localization.Away r)).commutes s

/-- Helper for Chap10 Lemma 10 70 3: the left-oriented tensor-away equivalence sends
`1 ⊗ x` to the base-changed localization image of `x`. -/
private theorem tensorAwayEquiv_one_tmul
    (S : Type v) [CommRing S] [Algebra R S] (r : R) (x : Localization.Away r) :
    (IsLocalization.Away.tensorEquiv S r (Localization.Away r))
        ((1 : S) ⊗ₜ[R] x) =
      algebraMap (Localization.Away r) (Localization.Away (algebraMap R S r)) x := by
  -- Compare the two maps from `R_r` by their values on `R`.
  have hRightHom :
      ((IsLocalization.Away.tensorEquiv S r (Localization.Away r)).toRingHom.comp
          (Algebra.TensorProduct.includeRight :
            Localization.Away r →ₐ[R] S ⊗[R] Localization.Away r).toRingHom) =
        (algebraMap (Localization.Away r) (Localization.Away (algebraMap R S r))) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers r)
    ext t
    calc
      (IsLocalization.Away.tensorEquiv S r (Localization.Away r))
          ((Algebra.TensorProduct.includeRight :
            Localization.Away r →ₐ[R] S ⊗[R] Localization.Away r)
            (algebraMap R (Localization.Away r) t)) =
        (IsLocalization.Away.tensorEquiv S r (Localization.Away r))
          (algebraMap S (S ⊗[R] Localization.Away r) (algebraMap R S t)) := by
          simp
      _ = algebraMap S (Localization.Away (algebraMap R S r)) (algebraMap R S t) := by
          exact (IsLocalization.Away.tensorEquiv S r (Localization.Away r)).commutes
            (algebraMap R S t)
      _ = algebraMap (Localization.Away r) (Localization.Away (algebraMap R S r))
          (algebraMap R (Localization.Away r) t) := by
          change algebraMap S (Localization.Away (algebraMap R S r)) (algebraMap R S t) =
            (IsLocalization.map (Localization.Away (algebraMap R S r)) (algebraMap R S)
              (powers_map_le_comap S r)) (algebraMap R (Localization.Away r) t)
          rw [IsLocalization.map_eq]
  change ((IsLocalization.Away.tensorEquiv S r (Localization.Away r)).toRingHom.comp
      (Algebra.TensorProduct.includeRight :
        Localization.Away r →ₐ[R] S ⊗[R] Localization.Away r).toRingHom) x = _
  rw [hRightHom]

/-- Helper for Chap10 Lemma 10 70 3: the right-oriented tensor-away equivalence sends
`x ⊗ 1` to the base-changed localization image of `x`. -/
private theorem tensorRightAwayEquiv_tmul_one
    (S : Type v) [CommRing S] [Algebra R S] (r : R) (x : Localization.Away r) :
    (IsLocalization.Away.tensorRightEquiv S r (Localization.Away r))
        (x ⊗ₜ[R] (1 : S)) =
      algebraMap (Localization.Away r) (Localization.Away (algebraMap R S r)) x := by
  -- Compare the two right-oriented maps from `R_r` by their values on `R`.
  letI : Algebra S (Localization.Away r ⊗[R] S) := Algebra.TensorProduct.rightAlgebra
  have hLeftHom :
      ((IsLocalization.Away.tensorRightEquiv S r (Localization.Away r)).toRingHom.comp
          (Algebra.TensorProduct.includeLeft :
            Localization.Away r →ₐ[R] Localization.Away r ⊗[R] S).toRingHom) =
        (algebraMap (Localization.Away r) (Localization.Away (algebraMap R S r))) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers r)
    ext t
    calc
      (IsLocalization.Away.tensorRightEquiv S r (Localization.Away r))
          ((Algebra.TensorProduct.includeLeft :
            Localization.Away r →ₐ[R] Localization.Away r ⊗[R] S)
            (algebraMap R (Localization.Away r) t)) =
        algebraMap S (Localization.Away (algebraMap R S r)) (algebraMap R S t) := by
          have hsource :
              (Algebra.TensorProduct.includeLeft :
                Localization.Away r →ₐ[R] Localization.Away r ⊗[R] S)
                  (algebraMap R (Localization.Away r) t) =
                algebraMap S (Localization.Away r ⊗[R] S) (algebraMap R S t) := by
            simpa [Algebra.TensorProduct.algebraMap_eq_includeRight] using
              congrFun
                (congrArg DFunLike.coe
                  (Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap
                    (R := R) (A := Localization.Away r) (B := S))) t
          rw [hsource]
          exact (IsLocalization.Away.tensorRightEquiv S r (Localization.Away r)).commutes
            (algebraMap R S t)
      _ = algebraMap (Localization.Away r) (Localization.Away (algebraMap R S r))
          (algebraMap R (Localization.Away r) t) := by
          change algebraMap S (Localization.Away (algebraMap R S r)) (algebraMap R S t) =
            (IsLocalization.map (Localization.Away (algebraMap R S r)) (algebraMap R S)
              (powers_map_le_comap S r)) (algebraMap R (Localization.Away r) t)
          rw [IsLocalization.map_eq]
  change ((IsLocalization.Away.tensorRightEquiv S r (Localization.Away r)).toRingHom.comp
      (Algebra.TensorProduct.includeLeft :
        Localization.Away r →ₐ[R] Localization.Away r ⊗[R] S).toRingHom) x = _
  rw [hLeftHom]

/-- Helper for Chap10 Lemma 10 70 3: the right-oriented tensor-away equivalence sends
`1 ⊗ s` to the scalar image of `s`. -/
private theorem tensorRightAwayEquiv_one_tmul
    (S : Type v) [CommRing S] [Algebra R S] (r : R) (s : S) :
    (IsLocalization.Away.tensorRightEquiv S r (Localization.Away r))
        ((1 : Localization.Away r) ⊗ₜ[R] s) =
      algebraMap S (Localization.Away (algebraMap R S r)) s := by
  -- This is the `S`-algebra map computation for the right-oriented tensor-away equivalence.
  letI : Algebra S (Localization.Away r ⊗[R] S) := Algebra.TensorProduct.rightAlgebra
  change (IsLocalization.Away.tensorRightEquiv S r (Localization.Away r))
      (algebraMap S (Localization.Away r ⊗[R] S) s) = _
  exact (IsLocalization.Away.tensorRightEquiv S r (Localization.Away r)).commutes s

/-- Helper for Chap10 Lemma 10 70 3: tensoring the source chart-to-away map on the right gives the
explicit localization map from `S ⊗[R] R[I/a]` to `S ⊗[R] R_a`. -/
private noncomputable def tensorAffineBlowupSourceToLocalizationTensor
    (S : Type v) [CommRing S] [Algebra R S] (I : Ideal R) (a : I) :
    S ⊗[R] R[I / a] →+* S ⊗[R] Localization.Away a.1 :=
  (Algebra.TensorProduct.map (AlgHom.id R S)
      { toRingHom := affineBlowupChartToLocalizationAway I a
        commutes' := affineBlowupChartToLocalizationAway_algebraMap (I := I) a }).toRingHom

/-- Helper for Chap10 Lemma 10 70 3: on normalized pure tensors, the tensor-localization map acts
only on the chart factor. -/
private theorem tensorAffineBlowupSourceToLocalizationTensor_tmul_powerFraction
    (S : Type v) [CommRing S] [Algebra R S] (I : Ideal R) (a : I) (n : ℕ)
    (x : ↥(I ^ n)) (s : S) :
    tensorAffineBlowupSourceToLocalizationTensor S I a
        (s ⊗ₜ[R] affineBlowupChartPowerFraction I a n x) =
      s ⊗ₜ[R] Localization.mk x.1
        ⟨a.1 ^ n, affineBlowupChart_parameter_pow_mem I a n⟩ := by
  -- The tensor-localization map acts factorwise, and the right factor is the already-computed
  -- normalized chart fraction in `R_a`.
  change
    Algebra.TensorProduct.map
        (AlgHom.id R S)
        { toRingHom := affineBlowupChartToLocalizationAway I a
          commutes' := affineBlowupChartToLocalizationAway_algebraMap (I := I) a }
        (s ⊗ₜ[R] affineBlowupChartPowerFraction I a n x) =
      s ⊗ₜ[R] Localization.mk x.1
        ⟨a.1 ^ n, affineBlowupChart_parameter_pow_mem I a n⟩
  rw [Algebra.TensorProduct.map_tmul]
  simp [affineBlowupChartPowerFraction,
    affineBlowupChartToLocalizationAway_fraction_of_monomial]

/-- Helper for Chap10 Lemma 10 70 3: composing the tensor-localization map with the standard
tensor/localization equivalence gives the ordinary away-localization map from the source tensor
product to `S_b`. -/
private noncomputable def tensorAffineBlowupSourceToAway
    (S : Type v) [CommRing S] [Algebra R S] (I : Ideal R) (a : I) :
    S ⊗[R] R[I / a] →+* Localization.Away (algebraMap R S a.1) :=
  (IsLocalization.Away.tensorEquiv S a.1 (Localization.Away a.1)).toRingHom.comp
    (tensorAffineBlowupSourceToLocalizationTensor S I a)

/-- Helper for Chap10 Lemma 10 70 3: on normalized pure tensors, the ordinary away-localization map
from the source tensor product has the expected textbook formula `s ⊗ x/a^n ↦ s · x/b^n`. -/
private theorem tensorAffineBlowupSourceToAway_tmul_powerFraction
    (S : Type v) [CommRing S] [Algebra R S] (I : Ideal R) (a : I) (n : ℕ)
    (x : ↥(I ^ n)) (s : S) :
    tensorAffineBlowupSourceToAway S I a
        (s ⊗ₜ[R] affineBlowupChartPowerFraction I a n x) =
      algebraMap S (Localization.Away (algebraMap R S a.1)) s *
        Localization.mk (algebraMap R S x.1)
          ⟨(algebraMap R S a.1) ^ n, by exact ⟨n, rfl⟩⟩ := by
  -- Rewrite the left-oriented tensor map as the composite with `tensorEquiv`, then separate the
  -- pure tensor into its scalar and localization factors.
  dsimp [tensorAffineBlowupSourceToAway]
  rw [tensorAffineBlowupSourceToLocalizationTensor_tmul_powerFraction]
  calc
    (IsLocalization.Away.tensorEquiv S a.1 (Localization.Away a.1))
        (s ⊗ₜ[R] Localization.mk x.1
          ⟨a.1 ^ n, affineBlowupChart_parameter_pow_mem I a n⟩) =
      (IsLocalization.Away.tensorEquiv S a.1 (Localization.Away a.1))
        ((s ⊗ₜ[R] (1 : Localization.Away a.1)) *
          (1 ⊗ₜ[R] Localization.mk x.1
            ⟨a.1 ^ n, affineBlowupChart_parameter_pow_mem I a n⟩)) := by
          simp [Algebra.TensorProduct.tmul_mul_tmul]
    _ =
      (IsLocalization.Away.tensorEquiv S a.1 (Localization.Away a.1))
          (s ⊗ₜ[R] (1 : Localization.Away a.1)) *
        (IsLocalization.Away.tensorEquiv S a.1 (Localization.Away a.1))
          (1 ⊗ₜ[R] Localization.mk x.1
            ⟨a.1 ^ n, affineBlowupChart_parameter_pow_mem I a n⟩) := by
              rw [map_mul]
    _ =
      algebraMap S (Localization.Away (algebraMap R S a.1)) s *
        algebraMap (Localization.Away a.1) (Localization.Away (algebraMap R S a.1))
          (Localization.mk x.1 ⟨a.1 ^ n, affineBlowupChart_parameter_pow_mem I a n⟩) := by
            rw [tensorAwayEquiv_tmul_one, tensorAwayEquiv_one_tmul]
    _ =
      algebraMap S (Localization.Away (algebraMap R S a.1)) s *
        Localization.mk (algebraMap R S x.1)
          ⟨(algebraMap R S a.1) ^ n, by exact ⟨n, rfl⟩⟩ := by
            rw [localizationAwayBaseChangeAlgebra_mk]

/-- Helper for Chap10 Lemma 10 70 3: after commuting tensor factors, the right-oriented tensor-away
equivalence has the same normalized pure-tensor formula as the left-oriented map. -/
private theorem tensorRightAway_tmul_powerFraction
    (S : Type v) [CommRing S] [Algebra R S] (I : Ideal R) (a : I) (n : ℕ)
    (x : ↥(I ^ n)) (s : S) :
    (IsLocalization.Away.tensorRightEquiv S a.1 (Localization.Away a.1))
        (Localization.mk x.1 ⟨a.1 ^ n, affineBlowupChart_parameter_pow_mem I a n⟩ ⊗ₜ[R] s) =
      algebraMap S (Localization.Away (algebraMap R S a.1)) s *
        Localization.mk (algebraMap R S x.1)
          ⟨(algebraMap R S a.1) ^ n, by exact ⟨n, rfl⟩⟩ := by
  -- Split the right-oriented pure tensor into the localization factor and the scalar factor.
  calc
    (IsLocalization.Away.tensorRightEquiv S a.1 (Localization.Away a.1))
        (Localization.mk x.1 ⟨a.1 ^ n, affineBlowupChart_parameter_pow_mem I a n⟩ ⊗ₜ[R] s) =
      (IsLocalization.Away.tensorRightEquiv S a.1 (Localization.Away a.1))
        ((Localization.mk x.1 ⟨a.1 ^ n, affineBlowupChart_parameter_pow_mem I a n⟩ ⊗ₜ[R]
            (1 : S)) *
          (1 ⊗ₜ[R] s)) := by
            simp [Algebra.TensorProduct.tmul_mul_tmul]
    _ =
      (IsLocalization.Away.tensorRightEquiv S a.1 (Localization.Away a.1))
          (Localization.mk x.1 ⟨a.1 ^ n, affineBlowupChart_parameter_pow_mem I a n⟩ ⊗ₜ[R]
            (1 : S)) *
        (IsLocalization.Away.tensorRightEquiv S a.1 (Localization.Away a.1))
          (1 ⊗ₜ[R] s) := by
            rw [map_mul]
    _ =
      algebraMap (Localization.Away a.1) (Localization.Away (algebraMap R S a.1))
          (Localization.mk x.1 ⟨a.1 ^ n, affineBlowupChart_parameter_pow_mem I a n⟩) *
        algebraMap S (Localization.Away (algebraMap R S a.1)) s := by
          rw [tensorRightAwayEquiv_tmul_one, tensorRightAwayEquiv_one_tmul]
    _ =
      algebraMap S (Localization.Away (algebraMap R S a.1)) s *
        algebraMap (Localization.Away a.1) (Localization.Away (algebraMap R S a.1))
          (Localization.mk x.1 ⟨a.1 ^ n, affineBlowupChart_parameter_pow_mem I a n⟩) := by
            rw [mul_comm]
    _ =
      algebraMap S (Localization.Away (algebraMap R S a.1)) s *
        Localization.mk (algebraMap R S x.1)
          ⟨(algebraMap R S a.1) ^ n, by exact ⟨n, rfl⟩⟩ := by
            rw [localizationAwayBaseChangeAlgebra_mk]

/-- Helper for Chap10 Lemma 10 70 3: after composing with the ordinary away-localization of the
target chart, the base-change map agrees with the ordinary away-localization map on a normalized
pure tensor. -/
private theorem tensorToAffineBlowupAlgebra_comp_to_away_tmul_powerFraction
    (S : Type v) [CommRing S] [Algebra R S] (I : Ideal R) (a : I) (n : ℕ)
    (x : ↥(I ^ n)) (s : S) :
    let J : Ideal S := Ideal.map (algebraMap R S) I
    let b : J := mappedIdealElement I a
    affineBlowupChartToLocalizationAway J b
        (tensorToAffineBlowupAlgebra S I a (s ⊗ₜ[R] affineBlowupChartPowerFraction I a n x)) =
      tensorAffineBlowupSourceToAway S I a
        (s ⊗ₜ[R] affineBlowupChartPowerFraction I a n x) := by
  -- Compute both sides on the normalized pure tensor and identify them with the same ordinary
  -- localization fraction in `S_b`.
  let J : Ideal S := Ideal.map (algebraMap R S) I
  let b : J := mappedIdealElement I a
  rw [tensorToAffineBlowupAlgebra_tmul_powerFraction]
  dsimp
  rw [map_mul]
  let xJ : ↥(J ^ n) :=
    ⟨algebraMap R S x.1, by
      simpa [J, Ideal.map_pow] using
        (Ideal.mem_map_of_mem (algebraMap R S) x.2 :
          algebraMap R S x.1 ∈ Ideal.map (algebraMap R S) (I ^ n))⟩
  have hfrac :
      affineBlowupChartToLocalizationAway J b (affineBlowupChartPowerFraction J b n xJ) =
        Localization.mk (algebraMap R S x.1)
          ⟨(algebraMap R S a.1) ^ n, by exact ⟨n, rfl⟩⟩ := by
    simpa [J, b, xJ, mappedIdealElement] using
      affineBlowupChartToLocalizationAway_fraction_of_monomial J b n xJ
  rw [hfrac]
  simpa [map_mul] using (tensorAffineBlowupSourceToAway_tmul_powerFraction S I a n x s).symm

/-- Helper for Chap10 Lemma 10 70 3: after composing with ordinary away-localization, the target
chart map agrees with the source tensor-localization map on all source elements. -/
private theorem tensorToAffineBlowupAlgebra_comp_to_away
    (S : Type v) [CommRing S] [Algebra R S] (I : Ideal R) (a : I) :
    let J : Ideal S := Ideal.map (algebraMap R S) I
    let b : J := mappedIdealElement I a
    ∀ z : S ⊗[R] R[I / a],
      affineBlowupChartToLocalizationAway J b (tensorToAffineBlowupAlgebra S I a z) =
        tensorAffineBlowupSourceToAway S I a z := by
  intro J b z
  -- Reduce the map comparison to pure tensors, then normalize the chart factor to a power
  -- fraction.
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · simp [tensorAffineBlowupSourceToAway]
    rfl
  · intro s x
    obtain ⟨n, y, hy, rfl⟩ := HomogeneousLocalization.Away.mk_surjective (reesAlgebraGrade I)
      (reesAlgebraDegreeOne_mem I a) x
    have hy' : y ∈ reesAlgebraGrade I n := by
      simpa [nsmul_eq_mul] using hy
    change y ∈ LinearMap.range _ at hy'
    rcases hy' with ⟨r, rfl⟩
    simpa [affineBlowupChartPowerFraction] using
      tensorToAffineBlowupAlgebra_comp_to_away_tmul_powerFraction S I a n r s
  · intro x y hx hy
    simpa [map_add] using congrArg₂ (fun a b => a + b) hx hy

/-- Helper for Chap10 Lemma 10 70 3: the chart-to-away algebra map is compatible with the
base algebra map from `R`. -/
private theorem affineBlowupChartToLocalizationAway_algebraMap_comp
    (I : Ideal R) (a : I) :
    algebraMap R (Localization.Away a.1) =
      (algebraMap R[I / a] (Localization.Away a.1)).comp (algebraMap R R[I / a]) := by
  -- Evaluate the two ring maps on `R`; the chart comparison theorem gives exactly this identity.
  ext r
  exact (affineBlowupChartToLocalizationAway_algebraMap I a r).symm

/-- Helper for Chap10 Lemma 10 70 3: the ordinary localization `R_a` carries the scalar tower
`R → R[I/a] → R_a` induced by the chart-to-away map. -/
private theorem affineBlowupChartToLocalizationAway_isScalarTower
    (I : Ideal R) (a : I) :
    letI : SMul R R[I / a] := (instAlgebraAffineBlowupChart I a).toSMul
    IsScalarTower R R[I / a] (Localization.Away a.1) := by
  -- Turn the named algebra-map compatibility into the scalar-tower instance needed for tensoring.
  exact IsScalarTower.of_algebraMap_eq'
    (affineBlowupChartToLocalizationAway_algebraMap_comp I a)

/-- Helper for Chap10 Lemma 10 70 3: tensoring the chart localization on the right by `S`
again gives a localization at the image of the chart parameter. -/
private theorem tensorAffineBlowupSource_right_isLocalization
    (S : Type v) [CommRing S] [Algebra R S] (I : Ideal R) (a : I) :
    letI : SMul R R[I / a] := (instAlgebraAffineBlowupChart I a).toSMul
    letI : IsScalarTower R R[I / a] (Localization.Away a.1) :=
      affineBlowupChartToLocalizationAway_isScalarTower I a
    let rightQ : Algebra S (R[I / a] ⊗[R] S) := Algebra.TensorProduct.rightAlgebra
    let rightL : Algebra S (Localization.Away a.1 ⊗[R] S) :=
      Algebra.TensorProduct.rightAlgebra
    let leftQ : Algebra R[I / a] (R[I / a] ⊗[R] S) := Algebra.TensorProduct.leftAlgebra
    let leftL : Algebra R[I / a] (Localization.Away a.1 ⊗[R] S) :=
      Algebra.TensorProduct.leftAlgebra
    let tensorQL : Algebra (R[I / a] ⊗[R] S) (Localization.Away a.1 ⊗[R] S) :=
      (Algebra.tensor_right_map (R := R) (S := Localization.Away a.1) (Q := R[I / a])
        (T := S)).toAlgebra
    letI : Algebra (R[I / a] ⊗[R] S) (Localization.Away a.1 ⊗[R] S) := tensorQL
    letI : Algebra S (R[I / a] ⊗[R] S) := rightQ
    letI : Algebra S (Localization.Away a.1 ⊗[R] S) := rightL
    letI : Algebra R[I / a] (R[I / a] ⊗[R] S) := leftQ
    letI : Algebra R[I / a] (Localization.Away a.1 ⊗[R] S) := leftL
    IsLocalization
      (Algebra.algebraMapSubmonoid (R[I / a] ⊗[R] S)
        (Submonoid.powers (algebraMap R R[I / a] a.1)))
      (Localization.Away a.1 ⊗[R] S) := by
  -- Build the tensor-product localization witness from the compatibility square of
  -- `Algebra.tensor_right_map`.
  letI : SMul R R[I / a] := (instAlgebraAffineBlowupChart I a).toSMul
  letI : IsScalarTower R R[I / a] (Localization.Away a.1) :=
    affineBlowupChartToLocalizationAway_isScalarTower I a
  let rightQ : Algebra S (R[I / a] ⊗[R] S) := Algebra.TensorProduct.rightAlgebra
  let rightL : Algebra S (Localization.Away a.1 ⊗[R] S) := Algebra.TensorProduct.rightAlgebra
  let leftQ : Algebra R[I / a] (R[I / a] ⊗[R] S) := Algebra.TensorProduct.leftAlgebra
  let leftL : Algebra R[I / a] (Localization.Away a.1 ⊗[R] S) :=
    Algebra.TensorProduct.leftAlgebra
  let tensorQL : Algebra (R[I / a] ⊗[R] S) (Localization.Away a.1 ⊗[R] S) :=
    (Algebra.tensor_right_map (R := R) (S := Localization.Away a.1) (Q := R[I / a])
      (T := S)).toAlgebra
  letI : Algebra (R[I / a] ⊗[R] S) (Localization.Away a.1 ⊗[R] S) := tensorQL
  letI : Algebra S (R[I / a] ⊗[R] S) := rightQ
  letI : Algebra S (Localization.Away a.1 ⊗[R] S) := rightL
  letI : Algebra R[I / a] (R[I / a] ⊗[R] S) := leftQ
  letI : Algebra R[I / a] (Localization.Away a.1 ⊗[R] S) := leftL
  have hQtower :
      (algebraMap (R[I / a] ⊗[R] S) (Localization.Away a.1 ⊗[R] S)).comp
          (algebraMap R[I / a] (R[I / a] ⊗[R] S)) =
        algebraMap R[I / a] (Localization.Away a.1 ⊗[R] S) := by
    exact Algebra.tensor_right_map_q_tower
      (R := R) (S := Localization.Away a.1) (Q := R[I / a]) (T := S)
  have hQtowerInst :=
    @IsScalarTower.of_algebraMap_eq' (R[I / a]) (R[I / a] ⊗[R] S)
      (Localization.Away a.1 ⊗[R] S)
      inferInstance inferInstance inferInstance leftQ tensorQL leftL hQtower.symm
  have hcompat :
      (algebraMap (R[I / a] ⊗[R] S) (Localization.Away a.1 ⊗[R] S)).comp
          Algebra.TensorProduct.includeRight.toRingHom =
        Algebra.TensorProduct.includeRight.toRingHom := by
    exact Algebra.tensor_right_map_includeRight_comp
      (R := R) (S := Localization.Away a.1) (Q := R[I / a]) (T := S)
  exact
    @Algebra.isLocalization_tensor_right_of_isLocalization R (Localization.Away a.1)
      inferInstance inferInstance inferInstance (R[I / a]) inferInstance inferInstance
      inferInstance inferInstance (Submonoid.powers (algebraMap R R[I / a] a.1)) S
      inferInstance inferInstance rightQ rightL tensorQL hQtowerInst
      (affineBlowupChartToLocalizationAway_isLocalizationAway I a) hcompat

/-- Helper for Chap10 Lemma 10 70 3: the source tensor-away map is the right-tensor
localization map after commuting tensor factors. -/
private theorem tensorAffineBlowupSourceToAway_eq_rightTensorLocalization
    (S : Type v) [CommRing S] [Algebra R S] (I : Ideal R) (a : I)
    (x : S ⊗[R] R[I / a]) :
    letI : SMul R R[I / a] := (instAlgebraAffineBlowupChart I a).toSMul
    letI : IsScalarTower R R[I / a] (Localization.Away a.1) :=
      affineBlowupChartToLocalizationAway_isScalarTower I a
    tensorAffineBlowupSourceToAway S I a x =
      (IsLocalization.Away.tensorRightEquiv S a.1 (Localization.Away a.1))
        ((Algebra.tensor_right_map (R := R) (S := Localization.Away a.1) (Q := R[I / a])
            (T := S)) ((Algebra.TensorProduct.commRight R S R[I / a]) x)) := by
  -- Reduce the map comparison to pure tensors and identify each chart factor by its normalized
  -- power-fraction presentation.
  letI : SMul R R[I / a] := (instAlgebraAffineBlowupChart I a).toSMul
  letI : IsScalarTower R R[I / a] (Localization.Away a.1) :=
    affineBlowupChartToLocalizationAway_isScalarTower I a
  let eComm := Algebra.TensorProduct.commRight R S (R[I / a])
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simp [tensorAffineBlowupSourceToAway]
  · intro s y
    obtain ⟨n, z, hz, hy⟩ := HomogeneousLocalization.Away.mk_surjective (reesAlgebraGrade I)
      (reesAlgebraDegreeOne_mem I a) y
    have hz' : z ∈ reesAlgebraGrade I n := by
      simpa [nsmul_eq_mul] using hz
    change z ∈ LinearMap.range _ at hz'
    rcases hz' with ⟨r, hr⟩
    subst z
    have hy' : affineBlowupChartPowerFraction I a n r = y := by
      simpa [affineBlowupChartPowerFraction] using hy
    rw [← hy']
    simpa [eComm, affineBlowupChartPowerFraction, Algebra.tensor_right_map_tmul,
      RingHom.algebraMap_toAlgebra, affineBlowupChartToLocalizationAway_fraction_of_monomial,
      tensorAffineBlowupSourceToAway_tmul_powerFraction, tensorRightAway_tmul_powerFraction] using
      (tensorAffineBlowupSourceToAway_tmul_powerFraction S I a n r s).trans
        (tensorRightAway_tmul_powerFraction S I a n r s).symm
  · intro x y hx hy
    simpa [map_add] using congrArg₂ (fun a b => a + b) hx hy

/-- Chap10 Lemma 10 70 3 (Stacks tag `0BIP`): if the source tensor element vanishes in the ordinary
away localization, then some power of the tensor image of `a` already annihilates it. -/
private theorem exists_pow_mul_eq_zero_of_tensorAffineBlowupSourceToAway_eq_zero
    (S : Type v) [CommRing S] [Algebra R S] (I : Ideal R) (a : I)
    (x : S ⊗[R] R[I / a])
    (hχ : tensorAffineBlowupSourceToAway S I a x = 0) :
    ∃ n : ℕ, (algebraMap R (S ⊗[R] R[I / a]) a.1) ^ n * x = 0 := by
  -- Route correction: name the scalar tower first, then use the right-oriented tensor localization
  -- zero criterion and commute the resulting annihilator back to the source tensor product.
  letI : SMul R R[I / a] := (instAlgebraAffineBlowupChart I a).toSMul
  letI : IsScalarTower R R[I / a] (Localization.Away a.1) :=
    affineBlowupChartToLocalizationAway_isScalarTower I a
  let eComm := Algebra.TensorProduct.commRight R S (R[I / a])
  let rightQ : Algebra S (R[I / a] ⊗[R] S) := Algebra.TensorProduct.rightAlgebra
  let rightL : Algebra S (Localization.Away a.1 ⊗[R] S) := Algebra.TensorProduct.rightAlgebra
  let leftQ : Algebra R[I / a] (R[I / a] ⊗[R] S) := Algebra.TensorProduct.leftAlgebra
  let leftL : Algebra R[I / a] (Localization.Away a.1 ⊗[R] S) :=
    Algebra.TensorProduct.leftAlgebra
  let tensorQL : Algebra (R[I / a] ⊗[R] S) (Localization.Away a.1 ⊗[R] S) :=
    (Algebra.tensor_right_map (R := R) (S := Localization.Away a.1) (Q := R[I / a])
      (T := S)).toAlgebra
  letI : Algebra (R[I / a] ⊗[R] S) (Localization.Away a.1 ⊗[R] S) := tensorQL
  letI : Algebra S (R[I / a] ⊗[R] S) := rightQ
  letI : Algebra S (Localization.Away a.1 ⊗[R] S) := rightL
  letI : Algebra R[I / a] (R[I / a] ⊗[R] S) := leftQ
  letI : Algebra R[I / a] (Localization.Away a.1 ⊗[R] S) := leftL
  have hχ' :
      (Algebra.tensor_right_map (R := R) (S := Localization.Away a.1) (Q := R[I / a])
          (T := S)) (eComm x) = 0 := by
    -- Remove the tensor-away equivalence from the vanishing hypothesis.
    rw [tensorAffineBlowupSourceToAway_eq_rightTensorLocalization S I a x] at hχ
    exact (RingEquiv.map_eq_zero_iff
      (IsLocalization.Away.tensorRightEquiv S a.1 (Localization.Away a.1)).toRingEquiv).1 hχ
  letI :
      IsLocalization
        (Algebra.algebraMapSubmonoid (R[I / a] ⊗[R] S)
          (Submonoid.powers (algebraMap R R[I / a] a.1)))
        (Localization.Away a.1 ⊗[R] S) := tensorAffineBlowupSource_right_isLocalization S I a
  have hzero :
      ∃ m :
          Algebra.algebraMapSubmonoid (R[I / a] ⊗[R] S)
            (Submonoid.powers (algebraMap R R[I / a] a.1)),
        (m : R[I / a] ⊗[R] S) * eComm x = 0 := by
    -- The localization zero criterion supplies a denominator from the mapped power submonoid.
    exact
      (IsLocalization.map_eq_zero_iff
        (Algebra.algebraMapSubmonoid (R[I / a] ⊗[R] S)
          (Submonoid.powers (algebraMap R R[I / a] a.1)))
        (Localization.Away a.1 ⊗[R] S) (eComm x)).1 hχ'
  rcases hzero with ⟨m, hm⟩
  rcases m.2 with ⟨q, hq, hqm⟩
  rcases (Submonoid.mem_powers_iff q (algebraMap R R[I / a] a.1)).mp hq with ⟨n, hqpow⟩
  refine ⟨n, ?_⟩
  -- Commute the right-oriented annihilator equation back to `S ⊗[R] R[I/a]`.
  apply eComm.injective
  have hm' :
      algebraMap R[I / a] (R[I / a] ⊗[R] S)
          ((algebraMap R R[I / a] a.1) ^ n) * eComm x = 0 := by
    rw [hqpow, hqm]
    exact hm
  rw [map_pow] at hm'
  have hscalar :
      eComm (algebraMap R (S ⊗[R] R[I / a]) a.1) =
        algebraMap R[I / a] (R[I / a] ⊗[R] S) (algebraMap R R[I / a] a.1) := by
    simpa [eComm] using
      (Algebra.TensorProduct.tmul_one_eq_one_tmul (A := R[I / a]) (B := S) a.1).symm
  rw [map_mul, map_pow, map_zero, hscalar]
  exact hm'

-- Proof sketch: the canonical map `S ⊗[R] R[I/a] → S[IS/b]` sends `s ⊗ x / a^n` to the
-- corresponding fraction in `S[IS/b]`, which gives surjectivity by writing elements of `J^n` as
-- sums of tensors from `I^n`. Its kernel is exactly the `b`-power torsion, because localizing away
-- from `b` kills precisely the elements annihilated by some power of `b`.
/-- Membership in the kernel of the base-change map is exactly torsion by a power of the
distinguished tensor image of `a`. -/
theorem mem_ker_tensorToAffineBlowupAlgebra_iff_exists_pow_mul_eq_zero
    (S : Type v) [CommRing S] [Algebra R S] (I : Ideal R) (a : I)
    (x : S ⊗[R] R[I / a]) :
    x ∈ RingHom.ker (tensorToAffineBlowupAlgebra S I a).toRingHom ↔
      ∃ n : ℕ, (algebraMap R (S ⊗[R] R[I / a]) a.1) ^ n * x = 0 := by
  constructor
  · intro hx
    have hAway :
        tensorAffineBlowupSourceToAway S I a x = 0 := by
      -- Push the kernel equation through the ordinary away-localization comparison.
      rw [RingHom.mem_ker] at hx
      have hx' : tensorToAffineBlowupAlgebra S I a x = 0 := by
        simpa using hx
      rw [← tensorToAffineBlowupAlgebra_comp_to_away S I a x, hx', map_zero]
      rfl
    exact exists_pow_mul_eq_zero_of_tensorAffineBlowupSourceToAway_eq_zero S I a x hAway
  · intro hx
    exact exists_pow_mul_eq_zero_mem_ker_tensorToAffineBlowupAlgebra S I a x hx

/-- Helper for Chap10 Lemma 10 70 3: the canonical base-change map
`S ⊗[R] R[I/a] → S[IS/b]` is surjective, and its kernel consists exactly of the elements
annihilated by some power of the image of `a` in the tensor product. -/
@[stacks 0BIP]
theorem affineBlowupChart_baseChange_surjective_and_ker_eq_a_power_torsion
    (S : Type v) [CommRing S] [Algebra R S] (I : Ideal R) (a : I) :
    let A := S ⊗[R] R[I / a]
    let φ := tensorToAffineBlowupAlgebra S I a
    let aS : A := algebraMap R A a.1
    Function.Surjective φ ∧
      ∀ x : A, x ∈ RingHom.ker φ.toRingHom ↔ ∃ n : ℕ, aS ^ n * x = 0 := by
  refine ⟨?_, ?_⟩
  · intro y
    let J : Ideal S := Ideal.map (algebraMap R S) I
    let b : J := mappedIdealElement I a
    obtain ⟨n, s, hs, rfl⟩ := HomogeneousLocalization.Away.mk_surjective (reesAlgebraGrade J)
      (reesAlgebraDegreeOne_mem J b) y
    have hs' : s ∈ reesAlgebraGrade J n := by
      simpa [nsmul_eq_mul] using hs
    change s ∈ LinearMap.range _ at hs'
    rcases hs' with ⟨r, rfl⟩
    simpa [affineBlowupChartPowerFraction] using
      affineBlowupChart_target_powerFraction_surjective S I a n r
  · intro x
    simpa using mem_ker_tensorToAffineBlowupAlgebra_iff_exists_pow_mul_eq_zero S I a x

/-- Helper for Chap10 Lemma 10 70 3: membership in the primary component of `(y)` is equivalent
to annihilation by some power of `y`. -/
private theorem mem_primaryComponent_span_singleton_iff_pow_mul_eq_zero
    {A : Type*} [CommRing A] (y x : A) :
    x ∈ (Ideal.span ({y} : Set A)).primaryComponent A ↔ ∃ n : ℕ, y ^ n * x = 0 := by
  -- Unfold the primary component into torsion by powers of the principal ideal, then identify
  -- powers of `(y)` with `(y ^ n)`.
  rw [Ideal.primaryComponent_mem]
  constructor
  · rintro ⟨n, hx⟩
    rw [Submodule.mem_torsionBySet_iff] at hx
    refine ⟨n, ?_⟩
    simpa [smul_eq_mul, Ideal.span_singleton_pow] using
      hx ⟨y ^ n, by
        rw [Ideal.span_singleton_pow]
        exact Ideal.subset_span (by simp)⟩
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    rw [Submodule.mem_torsionBySet_iff]
    intro z
    rcases z with ⟨z, hz⟩
    rw [Ideal.span_singleton_pow] at hz
    change z ∈ Ideal.span ({y ^ n} : Set A) at hz
    rw [Ideal.mem_span_singleton'] at hz
    rcases hz with ⟨c, rfl⟩
    simp [smul_eq_mul, mul_assoc, hn]

/-- Canonical reformulation of Chap10 Lemma 10 70 3: the kernel of the base-change map is the
primary component of the principal ideal generated by the distinguished tensor image of `a`. -/
theorem affineBlowupChart_baseChange_surjective_and_ker_eq_primaryComponent
    (S : Type v) [CommRing S] [Algebra R S] (I : Ideal R) (a : I) :
    let A := S ⊗[R] R[I / a]
    let φ := tensorToAffineBlowupAlgebra S I a
    let aS : A := algebraMap R A a.1
    Function.Surjective φ ∧
      RingHom.ker φ.toRingHom = (Ideal.span ({aS} : Set A)).primaryComponent A := by
  refine ⟨(affineBlowupChart_baseChange_surjective_and_ker_eq_a_power_torsion S I a).1, ?_⟩
  -- Compare membership in the two ideals through the torsion characterization and the principal
  -- primary-component helper.
  ext x
  rw [mem_primaryComponent_span_singleton_iff_pow_mul_eq_zero]
  exact affineBlowupChart_baseChange_surjective_and_ker_eq_a_power_torsion S I a |>.2 x

end
