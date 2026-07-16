import Mathlib
import StacksProject_2024.stacks_project.Chap10.Lemma_10_40_4
import StacksProject_2024.stacks_project.Chap10.Lemma_10_147_5
import StacksProject_2024.stacks_project.Chap15.Definition_15_41_1
import StacksProject_2024.stacks_project.Chap16.Definition_16_2_1
import StacksProject_2024.stacks_project.Chap16.Situation_16_8_1

-- Declarations for this item will be appended below by the statement pipeline.

namespace Algebra

open scoped SingularIdealNotation

universe u

section

variable {R : Type u} {Λ : Type u}
variable [CommRing R] [CommRing Λ] [Algebra R Λ]
variable [IsNoetherianRing R] [IsNoetherianRing Λ] [(algebraMap R Λ).IsRegularRingMap]

/- Domain-style sampling:
- primary domain: regular ring maps of Noetherian commutative rings and the PT property
  `RingHom.IsFilteredColimitOfSmooth`;
- sampled owner declarations:
  `RingHom.IsFilteredColimitOfSmooth`,
  `IsRegularRingMap`,
  `RingHom.IsFilteredColimitOfSmooth.isRegularRingMap_of_noetherianFibers`,
  `RingHom.IsFilteredColimitOfSmooth.prodMap`;
- best owner abstraction: PT is already owned by
  `(algebraMap R Λ).IsFilteredColimitOfSmooth`, while Situation `16.8.1` itself is owned by the
  ambient instance `[IsRegularRingMap R Λ]`;
- primitive vs. derived: the only primitive input of the reduction theorem is the field-case PT
  hypothesis phrased directly at that owner. Any chosen presentation of a filtered diagram of
  smooth algebras is derived API already packaged by `RingHom.IsFilteredColimitOfSmooth`.

Source/core/bridge triage:
- `source-facing`: the reduction from arbitrary regular maps to the case where the source is a
  field;
- `core/canonical`: `[IsRegularRingMap R Λ]` for the ambient situation and
  `(algebraMap R Λ).IsFilteredColimitOfSmooth` for PT;
- `bridge/view`: the auxiliary reductions through quotients, total quotient rings, and product
  decompositions used in the proof sketch.
-/

-- Proof sketch: for an arbitrary regular map `R → Λ`, consider the set of ideals `I ⊆ R` for
-- which the quotient map `R / I → Λ / IΛ` does not satisfy PT, and choose a maximal such ideal if
-- any exist. After replacing the situation by this quotient, every nonzero quotient satisfies PT,
-- so Proposition `16.5.3` shows `R` is reduced. Localizing at the nonzerodivisors reduces to the
-- total ring of fractions, which is a finite product of fields; apply Lemmas `16.8.2`, `16.8.3`,
-- `16.6.1`, and `16.7.2` to descend the field-case smooth factorization back to `Λ`.
/-- Helper for Lemma 16.8.4: lift PT across a nilpotent quotient. This local placeholder replaces
the broken import of Proposition `16.5.3` so the remaining proof frontier stays inside the current
item file. -/
theorem isFilteredColimitOfSmooth_of_nilpotent_quotient
    (I : Ideal R) (hI : IsNilpotent I)
    (hquot : (algebraMap (R ⧸ I) (Λ ⧸ I.map (algebraMap R Λ))).IsFilteredColimitOfSmooth) :
    (algebraMap R Λ).IsFilteredColimitOfSmooth := by
  -- Proof comment: this should be discharged by the square-zero/nilpotent induction package from
  -- Proposition `16.5.3` once that file compiles again.
  --
  -- TODO: restore the dependency-closed nilpotent-thickening proof from Proposition `16.5.3`,
  -- then delete this local placeholder and reuse the canonical theorem instead.
  sorry

/-- Helper for Lemma 16.8.4: a smooth finitely presented algebra has unit singular ideal. -/
lemma singularIdeal_eq_top_of_smooth
    {S : Type u} {T : Type u}
    [CommRing S] [CommRing T] [Algebra S T]
    [FinitePresentation S T] [Smooth S T] :
    H[T⁄S] = ⊤ := by
  -- Proof comment: smoothness makes the smooth locus all of `Spec(T)`, so the singular ideal has
  -- empty zero locus and is therefore the unit ideal.
  apply PrimeSpectrum.zeroLocus_empty_iff_eq_top.mp
  rw [Algebra.zeroLocus_singularIdeal_eq_compl_smoothLocus, Algebra.smoothLocus_eq_univ, Set.compl_univ]

/-- Helper for Lemma 16.8.4: if an ideal already contains the kernel of a quotient map and its
image in the quotient is the unit ideal, then the ideal itself is the unit ideal. -/
lemma ideal_eq_top_of_quotient_map_eq_top
    (I J : Ideal Λ) (hIJ : I ≤ J)
    (hmap : Ideal.map (Ideal.Quotient.mk I) J = ⊤) :
    J = ⊤ := by
  -- Proof comment: pull the quotient-level unit-ideal statement back along the surjective quotient
  -- map; the resulting supremum collapses because `I ≤ J`.
  have hComapTop :
      Ideal.comap (Ideal.Quotient.mk I) (Ideal.map (Ideal.Quotient.mk I) J) = ⊤ := by
    rw [hmap, Ideal.comap_top]
  have hSupTop : J ⊔ Ideal.comap (Ideal.Quotient.mk I) ⊥ = ⊤ := by
    simpa [Ideal.comap_map_of_surjective (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective] using hComapTop
  have hSupTop' : J ⊔ I = ⊤ := by
    simpa [← RingHom.ker_eq_comap_bot, Ideal.mk_ker] using hSupTop
  rwa [sup_eq_left.2 hIJ] at hSupTop'

/-- Helper for Lemma 16.8.4: a quotient-minimal counterexample has reduced source ring. -/
lemma isReduced_of_counterexample_minimal_under_nonzero_quotients
    (hbad : ¬ (algebraMap R Λ).IsFilteredColimitOfSmooth)
    (hquot :
      ∀ I : Ideal R, I ≠ ⊥ →
        (algebraMap (R ⧸ I) (Λ ⧸ I.map (algebraMap R Λ))).IsFilteredColimitOfSmooth) :
    IsReduced R := by
  -- Proof comment: if the nilradical were nonzero, the quotient hypothesis would make the
  -- nilradical quotient satisfy PT, and Proposition `16.5.3` would lift PT back to `R → Λ`,
  -- contradicting the assumed minimal counterexample.
  rw [← nilradical_eq_bot_iff]
  by_contra hnil
  exact hbad <|
    isFilteredColimitOfSmooth_of_nilpotent_quotient
      (R := R) (Λ := Λ) (I := nilradical R)
      (IsNoetherianRing.isNilpotent_nilradical R)
      (hquot (nilradical R) hnil)

/-- Helper for Lemma 16.8.4: the induced target ideal in the double-quotient step agrees with the
direct quotient ideal obtained from the larger source ideal. -/
lemma quotientStepTargetIdeal_eq
    {S : Type u} {T : Type u} [CommRing S] [CommRing T] [Algebra S T]
    (J K : Ideal S) :
    Ideal.map
        (algebraMap (S ⧸ J) (T ⧸ J.map (algebraMap S T)))
        (Ideal.map (Ideal.Quotient.mk J) K) =
      Ideal.map (Ideal.Quotient.mk (J.map (algebraMap S T))) (K.map (algebraMap S T)) := by
  -- Proof comment: rewrite the quotient algebra map as the composite of the original algebra map
  -- with the source quotient map, then the target ideal identity is exactly `Ideal.map_map`.
  have hcomp :
      (algebraMap (S ⧸ J) (T ⧸ J.map (algebraMap S T))).comp (Ideal.Quotient.mk J) =
        algebraMap S (T ⧸ J.map (algebraMap S T)) := by
    ext x
    rfl
  simpa [Ideal.map_map, hcomp]

/-- Helper for Lemma 16.8.4: the induction hypothesis on larger ideals of `R` descends to every
nonzero quotient of `R ⧸ I`. -/
lemma quotientPt_of_inductionStep
    (I : Ideal R)
    (hind :
      ∀ J : Ideal R, I < J →
        (algebraMap (R ⧸ J) (Λ ⧸ J.map (algebraMap R Λ))).IsFilteredColimitOfSmooth)
    (K : Ideal (R ⧸ I)) (hK : K ≠ ⊥) :
    (algebraMap
        ((R ⧸ I) ⧸ K)
        ((Λ ⧸ I.map (algebraMap R Λ)) ⧸
          Ideal.map (algebraMap (R ⧸ I) (Λ ⧸ I.map (algebraMap R Λ))) K)).IsFilteredColimitOfSmooth := by
  -- Proof comment: this is the standard double-quotient transport used in the quotient-induction
  -- step. The route is stable, but the current file still needs the cleaned owner-level transport
  -- lemma package before this proof can be restored without elaboration churn.
  --
  -- TODO: adapt the proven `quotientHypothesisOfQuotientStep` transport from Proposition `16.5.3`
  -- to the present `I < J` induction step and then compose with `Ideal.quotEquivOfEq hJmap.symm`.
  sorry

/-- Helper for Lemma 16.8.4: a positive power of a nonzerodivisor generates a nonzero principal
ideal. -/
lemma span_singleton_pow_ne_bot_of_mem_nonZeroDivisors
    {S : Type u} [CommRing S] [Nontrivial S] {π : S} {n : ℕ}
    (hπ : π ∈ nonZeroDivisors S) :
    Ideal.span ({π ^ n} : Set S) ≠ ⊥ := by
  -- Proof comment: a nonzerodivisor has nonzero positive powers, so the principal ideal generated
  -- by such a power cannot be the zero ideal.
  intro hspan
  have hpow : π ^ n ∈ nonZeroDivisors S := pow_mem hπ n
  have hpow_cancel : ∀ x : S, π ^ n * x = 0 → x = 0 := (mem_nonZeroDivisors_iff.mp hpow).1
  have hpow_ne : π ^ n ≠ 0 := by
    intro hzero
    have hone : (1 : S) = 0 := hpow_cancel 1 (by simpa [hzero])
    exact one_ne_zero hone
  apply hpow_ne
  have hmem : π ^ n ∈ Ideal.span ({π ^ n} : Set S) :=
    Ideal.mem_span_singleton_self (π ^ n)
  simpa [hspan, Ideal.mem_bot] using hmem

/-- Helper for Lemma 16.8.4: the induction-step quotient PT applies to the principal quotient by
`π⁸` as soon as `π` is a nonzerodivisor. -/
lemma quotientPt_at_piPowEight_of_nonZeroDivisor
    {S : Type u} {T : Type u}
    [CommRing S] [Nontrivial S] [CommRing T] [Algebra S T]
    (hquot :
      ∀ K : Ideal S, K ≠ ⊥ →
        (algebraMap (S ⧸ K) (T ⧸ K.map (algebraMap S T))).IsFilteredColimitOfSmooth)
    {π : S} (hπ : π ∈ nonZeroDivisors S) :
    (algebraMap
        (S ⧸ Ideal.span ({π ^ 8} : Set S))
        (T ⧸ Ideal.map (algebraMap S T) (Ideal.span ({π ^ 8} : Set S)))).IsFilteredColimitOfSmooth := by
  -- Proof comment: `π⁸` remains a nonzerodivisor, hence nonzero, so the principal ideal `(π⁸)`
  -- is a genuine nonzero quotient to which the induction-step PT hypothesis applies.
  apply hquot
  exact span_singleton_pow_ne_bot_of_mem_nonZeroDivisors hπ

/-- Helper for Lemma 16.8.4: a nonzerodivisor has trivial self-torsion ideal. -/
lemma torsionOf_eq_bot_of_mem_nonZeroDivisors
    {S : Type u} [CommRing S] {x : S}
    (hx : x ∈ nonZeroDivisors S) :
    Ideal.torsionOf S S x = ⊥ := by
  ext a
  constructor
  · intro ha
    -- Proof comment: membership in the torsion ideal means `a * x = 0`, and the right-regularity
    -- half of `hx` forces `a = 0`.
    rw [Ideal.mem_bot]
    exact (mem_nonZeroDivisors_iff.mp hx).2 a (by simpa [Ideal.mem_torsionOf_iff, smul_eq_mul] using ha)
  · intro ha
    -- Proof comment: once `a = 0`, the torsion equation is immediate.
    rw [Ideal.mem_bot] at ha
    simpa [Ideal.mem_torsionOf_iff, smul_eq_mul, ha]

/-- Helper for Lemma 16.8.4: a nonzerodivisor satisfies the square-step annihilator equality
`Ann(π) = Ann(π²)` in its own ring. -/
lemma torsionOf_squareStep_of_mem_nonZeroDivisors
    {S : Type u} [CommRing S] {π : S}
    (hπ : π ∈ nonZeroDivisors S) :
    Ideal.torsionOf S S π = Ideal.torsionOf S S (π ^ 2) := by
  -- Proof comment: both torsion ideals are already zero because `π` and `π²` are nonzerodivisors.
  rw [torsionOf_eq_bot_of_mem_nonZeroDivisors hπ,
    torsionOf_eq_bot_of_mem_nonZeroDivisors (pow_mem hπ 2)]

/-- Helper for Lemma 16.8.4: flat base change transports the square-step annihilator equality
`Ann(π) = Ann(π²)`. -/
lemma torsionOf_squareStep_of_flat_algebra
    {S : Type u} {T : Type u}
    [CommRing S] [CommRing T] [Algebra S T] [Module.Flat S T]
    {π : S}
    (hAnnS : Ideal.torsionOf S S π = Ideal.torsionOf S S (π ^ 2)) :
    Ideal.torsionOf T T (algebraMap S T π) =
      Ideal.torsionOf T T (algebraMap S T (π ^ 2)) := by
  let e := TensorProduct.AlgebraTensorModule.rid S T T
  have htransport :
      ∀ r : S,
        Ideal.torsionOf T (TensorProduct S T S) ((1 : T) ⊗ₜ[S] r) =
          Ideal.torsionOf T T (algebraMap S T r) := by
    intro r
    ext x
    rw [Ideal.mem_torsionOf_iff, Ideal.mem_torsionOf_iff]
    constructor
    · intro hx
      -- Proof comment: compare the tensor torsion equation with the scalar one through the
      -- right-unit tensor equivalence.
      have hx' := congrArg e hx
      simpa [e, TensorProduct.AlgebraTensorModule.rid_tmul, Algebra.smul_def, mul_comm,
        mul_left_comm, mul_assoc] using hx'
    · intro hx
      -- Proof comment: the same equivalence transports the scalar torsion equation back to the
      -- tensor-product model.
      apply e.injective
      simpa [e, TensorProduct.AlgebraTensorModule.rid_tmul, Algebra.smul_def, mul_comm,
        mul_left_comm, mul_assoc] using hx
  calc
    Ideal.torsionOf T T (algebraMap S T π) =
        Ideal.map (algebraMap S T) (Ideal.torsionOf S S π) := by
          symm
          calc
            Ideal.map (algebraMap S T) (Ideal.torsionOf S S π) =
                Ideal.torsionOf T (TensorProduct S T S) ((1 : T) ⊗ₜ[S] π) := by
                  simpa using
                    (Ideal.map_torsionOf_eq_torsionOf_baseChange_of_flat
                      (R := S) (S := T) (M := S) π)
            _ = Ideal.torsionOf T T (algebraMap S T π) := htransport π
    _ = Ideal.map (algebraMap S T) (Ideal.torsionOf S S (π ^ 2)) := by rw [hAnnS]
    _ = Ideal.torsionOf T T (algebraMap S T (π ^ 2)) := by
          calc
            Ideal.map (algebraMap S T) (Ideal.torsionOf S S (π ^ 2)) =
                Ideal.torsionOf T (TensorProduct S T S) ((1 : T) ⊗ₜ[S] (π ^ 2)) := by
                  simpa using
                    (Ideal.map_torsionOf_eq_torsionOf_baseChange_of_flat
                      (R := S) (S := T) (M := S) (π ^ 2))
            _ = Ideal.torsionOf T T (algebraMap S T (π ^ 2)) := htransport (π ^ 2)

/-- Lemma 16.8.4: if PT, namely `RingHom.IsFilteredColimitOfSmooth`, holds for every
Situation 16.8.1 whose source ring is a field, then PT holds for every Situation 16.8.1. -/
theorem isFilteredColimitOfSmooth_of_forall_field_cases
    (hfield :
      ∀ {K A : Type u} [Field K] [CommRing A] [Algebra K A]
        [IsNoetherianRing A] [(algebraMap K A).IsRegularRingMap],
        (algebraMap K A).IsFilteredColimitOfSmooth) :
    (algebraMap R Λ).IsFilteredColimitOfSmooth := by
  -- Proof comment: the intended route is fixed by the textbook proof: quotient induction,
  -- reduced total-quotient reduction, localization-to-finite-product-of-fields, then the `π⁸`
  -- desingularization endgame. The remaining blocker is the owner-level transport from the
  -- field-case hypothesis to the localized total-quotient map.
  --
  -- TODO: first restore `quotientPt_of_inductionStep`, then prove the finite-product-of-fields PT
  -- bridge and `localizedPt_of_reduced_totalQuotient`, and finally assemble the existing
  -- `16.8.3` descent with the `π⁸` closing helpers already present in this file.
  sorry

end

end Algebra
