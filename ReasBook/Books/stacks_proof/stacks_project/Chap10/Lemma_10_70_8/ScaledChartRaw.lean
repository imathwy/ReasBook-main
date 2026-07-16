import stacks_proof.stacks_project.Chap10.Lemma_10_70_8.ScaledReesAlgebra
import stacks_proof.stacks_project.Chap10.Lemma_10_70_8.LocalizationTransport

universe u

noncomputable section

open HomogeneousLocalization
open IsLocalization
open Polynomial
open scoped DirectSum

section

variable {R : Type u} [CommRing R]

/-- Helper for Lemma 10.70.8: the raw codomain of the scaled chart map agrees with the standard
scaled affine blowup chart after rewriting the degree-one parameter. -/
theorem scaled_chart_codomain_eq
    (I : Ideal R) (a : I) (f : R) :
    Away (reesAlgebraGrade (scaledIdeal I f))
      ((scaledGradedHom I f) (reesAlgebraDegreeOne I a)) =
      affineBlowupChart (scaledIdeal I f) (scaledElement I a f) := by
  simpa [affineBlowupChart] using
    congrArg
      (fun y ↦ Away (reesAlgebraGrade (scaledIdeal I f)) y)
      (scaled_degreeOne I a f)

/-- Helper for Lemma 10.70.8: the raw codomain of the scaled chart map before transport. -/
abbrev scaledChartRaw
    (I : Ideal R) (a : I) (f : R) :=
  Away (reesAlgebraGrade (scaledIdeal I f))
    ((scaledGradedHom I f) (reesAlgebraDegreeOne I a))

/-- Helper for Lemma 10.70.8: the target scaled affine blowup chart. -/
abbrev scaledChartTarget
    (I : Ideal R) (a : I) (f : R) :=
  affineBlowupChart (scaledIdeal I f) (scaledElement I a f)

/-- Helper for Lemma 10.70.8: the raw degree-zero class in the scaled chart before transport. -/
noncomputable def scaledChartRawZeroDegreeClass
    (I : Ideal R) (a : I) (f r : R) :
    scaledChartRaw I a f :=
  HomogeneousLocalization.fromZeroRingHom
    (reesAlgebraGrade (scaledIdeal I f))
    (Submonoid.powers ((scaledGradedHom I f) (reesAlgebraDegreeOne I a)))
    (scaledReesAlgebraZeroDegreeCoeff I f r)

/-- Helper for Lemma 10.70.8: the raw scaled-chart codomain carries the canonical homogeneous
localization ring structure. -/
noncomputable instance scaledAffineBlowupChartRawCommRing
    (I : Ideal R) (a : I) (f : R) :
    CommRing (scaledChartRaw I a f) :=
  HomogeneousLocalization.homogeneousLocalizationCommRing

/-- Helper for Lemma 10.70.8: the raw scaled chart compares to the ordinary localization
`R_(fa)` by transporting the standard target-chart comparison map back along
`scaled_chart_codomain_eq`. -/
noncomputable def scaledChartRawToLocalizationAway
    (I : Ideal R) (a : I) (f : R) :
    scaledChartRaw I a f → Localization.Away (f * a.1) :=
  fun y ↦ affineBlowupChartToLocalizationAway (scaledIdeal I f) (scaledElement I a f)
    (cast (scaled_chart_codomain_eq I a f) y)

/-- Helper for Lemma 10.70.8: evaluating the transported raw comparison map is the same as first
transporting the raw chart element into the standard scaled chart. -/
theorem scaledChartRawToLocalizationAway_cast
    (I : Ideal R) (a : I) (f : R) (y : scaledChartRaw I a f) :
    scaledChartRawToLocalizationAway I a f y =
      affineBlowupChartToLocalizationAway (scaledIdeal I f) (scaledElement I a f)
        (cast (scaled_chart_codomain_eq I a f) y) := by
  rfl

/-- Helper for Lemma 10.70.8: the underlying ring homomorphism of the scaled chart map. -/
noncomputable def affineBlowupChartScaledMap_toRingHom
    (I : Ideal R) (a : I) (f : R) :
    affineBlowupChart I a →+*
      affineBlowupChart (Ideal.span ({f} : Set R) * I)
        ⟨f * a.1, Ideal.mul_mem_mul (Ideal.subset_span (by simp)) a.2⟩ :=
  Eq.mp
    (congrArg
      (fun x ↦ affineBlowupChart I a →+* Away (reesAlgebraGrade (scaledIdeal I f)) x)
      (scaled_degreeOne I a f))
    (HomogeneousLocalization.Away.map (scaledGradedHom I f) (reesAlgebraDegreeOne I a))

/-- Helper for Lemma 10.70.8: before transporting the codomain along `scaled_degreeOne`, the raw
homogeneous-localization map already commutes with the base-ring algebra map. -/
theorem affineBlowupChartScaledMap_raw_commutes
    (I : Ideal R) (a : I) (f r : R) :
    let Araw :=
      Away (reesAlgebraGrade (scaledIdeal I f))
        ((scaledGradedHom I f) (reesAlgebraDegreeOne I a))
    let ψ : affineBlowupChart I a →+* Araw :=
      HomogeneousLocalization.Away.map (scaledGradedHom I f) (reesAlgebraDegreeOne I a)
    ψ (algebraMap R (affineBlowupChart I a) r) =
      HomogeneousLocalization.fromZeroRingHom (reesAlgebraGrade (scaledIdeal I f))
        (Submonoid.powers ((scaledGradedHom I f) (reesAlgebraDegreeOne I a)))
        (scaledReesAlgebraZeroDegreeCoeff I f r) := by
  let Araw :=
    Away (reesAlgebraGrade (scaledIdeal I f))
      ((scaledGradedHom I f) (reesAlgebraDegreeOne I a))
  letI : CommRing Araw := HomogeneousLocalization.homogeneousLocalizationCommRing
  let ψ : affineBlowupChart I a →+* Araw :=
    HomogeneousLocalization.Away.map (scaledGradedHom I f) (reesAlgebraDegreeOne I a)
  -- Compute the raw `Away.map` on the degree-zero class `r / 1` before introducing any casts.
  simpa [Araw, ψ, RingHom.algebraMap_toAlgebra,
    scaledReesAlgebra_zeroDegree_algebraMap I f r] using
    (away_map_fromZeroRingHom (𝒜 := reesAlgebraGrade I)
      (ℬ := reesAlgebraGrade (scaledIdeal I f)) (scaledGradedHom I f)
      (reesAlgebraDegreeOne I a) (reesAlgebraZeroDegreeCoeff I r))

end
