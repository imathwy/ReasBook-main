import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.Ideal.Quotient.Operations
import StacksProject_2024.stacks_project.Chap10.Lemma_10_96_4
import StacksProject_2024.stacks_project.Chap15.PrincipalIdeal

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

open Module
open scoped nonZeroDivisors
open AdicCompletion

variable {R : Type u} [CommRing R]

/-
Domain-style sampling:
- primary domain: commutative algebra of the Beauville-Laszlo Cech sequence for the principal-adic
  completion map `R → principalAdicCompletion f`;
- sampled owner declarations:
  `principalAdicCompletion`,
  `IsBeauvilleLaszloGlueingPairAlong`,
  `principalAdicCompletion_isBeauvilleLaszloGlueingPairAlong_iff_bijective_fPowerTorsion`,
  `primaryComponent_principalIdeal_eq_fPowerTorsion`,
  `powerTorsionSubmodule_eq_bot_of_injective_awayLocalizationFamilyMap`,
  `Ideal.primaryComponent`;
- best owner abstraction: the chapter owner `IsBeauvilleLaszloGlueingPairAlong`, specialized to
  the completion owner `principalAdicCompletion`; the source-facing `f^∞`-torsion notation is a
  bridge to the canonical torsion owner `(principalIdeal f).primaryComponent`;
- primitive data: a commutative ring `R` and an element `f : R`;
- derived API: the completion-side nonzerodivisor statement and the source theorem that a
  nonzerodivisor yields this exact completion-localization glueing pair;
- triage: `core/canonical` = `principalAdicCompletion` together with
  `IsBeauvilleLaszloGlueingPairAlong` and `Ideal.primaryComponent`,
  `bridge/view` = the completion specialization below,
  `source-facing` =
  `principalAdicCompletion_isBeauvilleLaszloGlueingPairAlong_of_mem_nonZeroDivisors`,
  `bridge/view` also includes the torsion-vanishing and completion-side nonzerodivisor comparison
  theorems below.
-/

/-- Helper for Remark 15.91.7: the algebra map sends `f^∞`-torsion to `f^∞`-torsion. -/
private theorem map_mem_fPowerTorsion
    {S : Type u} [CommRing S] (φ : R →+* S) (f : R)
    (x : (Submodule.torsion' R R (Submonoid.powers f) : Submodule R R)) :
    let _ : Algebra R S := φ.toAlgebra
    Algebra.linearMap R S x ∈ (Submodule.torsion' R S (Submonoid.powers f) : Submodule R S) := by
  let _ : Algebra R S := φ.toAlgebra
  rcases (Submodule.mem_torsion'_iff (Submonoid.powers f) (x : R)).1 x.2 with ⟨a, hx⟩
  refine (Submodule.mem_torsion'_iff (Submonoid.powers f) ((Algebra.linearMap R S) x)).2 ?_
  refine ⟨a, ?_⟩
  have hx₀ : (a : R) * (x : R) = 0 := by
    simpa [smul_eq_mul] using hx
  have hx' : (Algebra.linearMap R S) ((a : R) * (x : R)) = 0 := by
    simpa using congrArg (Algebra.linearMap R S) hx₀
  simpa [Algebra.smul_def, map_mul] using hx'

/-- Helper for Remark 15.91.7: the map on `f^∞`-torsion induced by `φ`. -/
private abbrev f_power_torsion_to_extension
    {S : Type u} [CommRing S] (φ : R →+* S) (f : R) :
    let _ : Algebra R S := φ.toAlgebra
    (Submodule.torsion' R R (Submonoid.powers f) : Submodule R R) →ₗ[R]
      (Submodule.torsion' R S (Submonoid.powers f) : Submodule R S) :=
  let _ : Algebra R S := φ.toAlgebra
  show (Submodule.torsion' R R (Submonoid.powers f) : Submodule R R) →ₗ[R]
      (Submodule.torsion' R S (Submonoid.powers f) : Submodule R S) from
    ((Algebra.linearMap R S).domRestrict
        (Submodule.torsion' R R (Submonoid.powers f) : Submodule R R)).codRestrict
      (Submodule.torsion' R S (Submonoid.powers f) : Submodule R S)
      (map_mem_fPowerTorsion (R := R) φ f)

/-- Helper for Remark 15.91.7: the completion-side Beauville-Laszlo criterion is the conjunction
of bijectivity on `f^∞`-torsion. -/
private abbrev completion_glueing_pair_along
    {S : Type u} [CommRing S] (φ : R →+* S) (f : R) : Prop :=
  let _ : Algebra R S := φ.toAlgebra
  Function.Bijective (f_power_torsion_to_extension (R := R) φ f)

local notation "IsBeauvilleLaszloGlueingPairAlong" => completion_glueing_pair_along

/-- Helper for Remark 15.91.7: if the image of `f` is a nonzerodivisor, then the
`f^∞`-torsion submodule vanishes. -/
private theorem fPowerTorsion_eq_bot_of_algebraMap_mem_nonZeroDivisors
    {S : Type u} [CommRing S] [Algebra R S] (f : R)
    (hf : algebraMap R S f ∈ nonZeroDivisors S) :
    Submodule.torsion' R S (Submonoid.powers f) = ⊥ := by
  -- Any torsion element is killed by some power of the image of `f`; peel off one copy of `f`
  -- at a time using the nonzerodivisor hypothesis.
  rw [Submodule.eq_bot_iff]
  intro x hx
  rw [Submodule.mem_torsion'_iff] at hx
  rcases hx with ⟨a, ha⟩
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff a.1 f).mp a.2
  have hf_left : ∀ y : S, algebraMap R S f * y = 0 → y = 0 :=
    mem_nonZeroDivisors_iff_left.mp hf
  have hpow :
      algebraMap R S f ^ n * x = 0 := by
    have haR : (a : R) • x = 0 := by
      simpa using ha
    have ha' : algebraMap R S (a : R) * x = 0 := by
      simpa [Algebra.smul_def] using haR
    have hpowEq : algebraMap R S (a : R) = algebraMap R S f ^ n := by
      simpa [map_pow] using congrArg (algebraMap R S) hn.symm
    simpa [hpowEq] using ha'
  have hkill :
      ∀ n : ℕ, algebraMap R S f ^ n * x = 0 → x = 0 := by
    intro n
    induction n with
    | zero =>
        intro hn
        simpa using hn
    | succ n ih =>
        intro hn
        have hn' : algebraMap R S f ^ n * x = 0 := by
          apply hf_left
          simpa [pow_succ', mul_assoc] using hn
        exact ih hn'
  exact hkill n hpow

/-- Helper for Remark 15.91.7: the principal sequence
`R --(* f)--> R --> R / (f)` is exact in the middle. -/
private theorem mulRight_exact_quotient_principalIdeal
    (f : R) :
    Function.Exact
      (LinearMap.mulRight R f)
      ((Ideal.Quotient.mkₐ R (principalIdeal f)).toLinearMap) := by
  -- Rewrite exactness as `ker = range`, then identify kernel elements with multiples of `f`.
  rw [LinearMap.exact_iff]
  ext x
  constructor
  · intro hx
    change Ideal.Quotient.mk (principalIdeal f) x = 0 at hx
    rw [Ideal.Quotient.eq_zero_iff_mem, principalIdeal] at hx
    rw [LinearMap.mem_range]
    rcases Ideal.mem_span_singleton.mp hx with ⟨a, ha⟩
    exact ⟨a, by simpa [LinearMap.mulRight_apply, mul_comm] using ha.symm⟩
  · rintro ⟨a, rfl⟩
    change Ideal.Quotient.mk (principalIdeal f) ((LinearMap.mulRight R f) a) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem, principalIdeal]
    exact Ideal.mem_span_singleton.mpr ⟨a, by simpa [LinearMap.mulRight_apply, mul_comm]⟩

/-- Helper for Remark 15.91.7: the quotient `R / (f)` is annihilated by the ideal `(f)`. -/
private theorem principalIdeal_quotient_smul_top_eq_bot
    (f : R) :
    (principalIdeal f) ^ 1 • (⊤ : Submodule R (R ⧸ principalIdeal f)) = ⊥ := by
  -- Every element of the mapped principal ideal becomes zero in the quotient.
  rw [pow_one, Submodule.eq_bot_iff]
  intro x hx
  rw [Ideal.smul_top_eq_map] at hx
  rcases (Ideal.mem_map_iff_of_surjective
      (algebraMap R (R ⧸ principalIdeal f))
      Ideal.Quotient.mk_surjective).mp hx with ⟨y, hy, rfl⟩
  simpa using (Ideal.Quotient.eq_zero_iff_mem.2 hy :
    Ideal.Quotient.mk (principalIdeal f) y = 0)

/-- Helper for Remark 15.91.7: on the principal adic completion, the completed map induced by
`x ↦ x * f` is ordinary multiplication by the image of `f`. -/
private theorem principalAdicCompletion_map_mulRight_eq_mulRight
    (f : R) :
    (((AdicCompletion.map (principalIdeal f) (LinearMap.mulRight R f)).restrictScalars R) :
      principalAdicCompletion f →ₗ[R] principalAdicCompletion f) =
      LinearMap.mulRight R (algebraMap R (principalAdicCompletion f) f) := by
  -- Compare both maps on Cauchy sequences, where both sides reduce coordinatewise.
  apply AdicCompletion.map_ext''
  ext a n
  simp [LinearMap.mulRight_apply, AdicCompletion.algebraMap_apply]

-- Proof sketch: apply Algebra Lemma `10.96.4` to the exact sequence
-- `0 → R --f--> R → R / (f) → 0`. The induced completion map on the first arrow is
-- multiplication by the image of `f`, so its injectivity shows that image is a nonzerodivisor.
private theorem principalAdicCompletion_mem_nonZeroDivisors_of_mem_nonZeroDivisors
    (f : R) (hf : f ∈ nonZeroDivisors R) :
    algebraMap R (principalAdicCompletion f) f ∈
      nonZeroDivisors (principalAdicCompletion f) := by
  -- The principal quotient sequence stays short exact after completion, so the completed
  -- multiplication-by-`f` map is injective.
  have hmul_injective : Function.Injective (LinearMap.mulRight R f) := by
    have hf_right : ∀ x : R, x * f = 0 → x = 0 :=
      mem_nonZeroDivisors_iff_right.mp hf
    intro x y hxy
    apply sub_eq_zero.mp
    apply hf_right
    calc
      (x - y) * f = x * f - y * f := sub_mul x y f
      _ = 0 := by simpa [LinearMap.mulRight_apply] using sub_eq_zero.mpr hxy
  have hquot_surjective :
      Function.Surjective ((Ideal.Quotient.mkₐ R (principalIdeal f)).toLinearMap) := by
    simpa using
      (Ideal.Quotient.mkₐ_surjective R (principalIdeal f) :
        Function.Surjective (Ideal.Quotient.mkₐ R (principalIdeal f)))
  have hcompleted_injective :
      Function.Injective
        (((AdicCompletion.map (principalIdeal f) (LinearMap.mulRight R f)).restrictScalars R) :
          principalAdicCompletion f →ₗ[R] principalAdicCompletion f) := by
    let S :=
      completion_shortExact_of_pow_smul_top_eq_bot
        (I := principalIdeal f)
        (f := LinearMap.mulRight R f)
        (g := (Ideal.Quotient.mkₐ R (principalIdeal f)).toLinearMap)
        hmul_injective
        (mulRight_exact_quotient_principalIdeal f)
        hquot_surjective
        (c := 1)
        (principalIdeal_quotient_smul_top_eq_bot f)
    exact S.moduleCat_injective_f
  -- The concrete multiplication map agrees with the completed map from the short exact sequence.
  rw [mem_nonZeroDivisors_iff_right]
  intro x hx
  apply hcompleted_injective
  simpa [principalAdicCompletion_map_mulRight_eq_mulRight f] using hx

-- Proof sketch: after the previous theorem, both `R[f^∞]` and `R^∧[f^∞]` vanish, so Lemma
-- `15.91.6` gives the exact Beauville-Laszlo Cech condition for the completion pair.
/-- Remark 15.91.7: if `f` is a nonzerodivisor in `R`, then `(R, f)` is a Beauville-Laszlo
glueing pair for the completion map. -/
theorem principalAdicCompletion_isBeauvilleLaszloGlueingPairAlong_of_mem_nonZeroDivisors
    (f : R) (hf : f ∈ nonZeroDivisors R) :
    IsBeauvilleLaszloGlueingPairAlong (algebraMap R (principalAdicCompletion f)) f := by
  have hsource :
      Submodule.torsion' R R (Submonoid.powers f) = ⊥ := by
    simpa using
      fPowerTorsion_eq_bot_of_algebraMap_mem_nonZeroDivisors
        (R := R) (S := R) f (by simpa using hf)
  have htarget :
      Submodule.torsion' R (principalAdicCompletion f) (Submonoid.powers f) = ⊥ := by
    simpa using
      fPowerTorsion_eq_bot_of_algebraMap_mem_nonZeroDivisors
        (R := R) (S := principalAdicCompletion f) f
        (principalAdicCompletion_mem_nonZeroDivisors_of_mem_nonZeroDivisors f hf)
  constructor
  · intro x y _
    have hx : (x : R) = 0 := by
      have hx_mem : (x : R) ∈ Submodule.torsion' R R (Submonoid.powers f) := x.2
      have hx_bot : (x : R) ∈ (⊥ : Submodule R R) := by
        simpa [hsource] using hx_mem
      simpa using hx_bot
    have hy : (y : R) = 0 := by
      have hy_mem : (y : R) ∈ Submodule.torsion' R R (Submonoid.powers f) := y.2
      have hy_bot : (y : R) ∈ (⊥ : Submodule R R) := by
        simpa [hsource] using hy_mem
      simpa using hy_bot
    apply Subtype.ext
    simpa [hx, hy]
  · intro y
    refine ⟨0, ?_⟩
    have hy : (y : principalAdicCompletion f) = 0 := by
      have hy_mem :
          (y : principalAdicCompletion f) ∈
            Submodule.torsion' R (principalAdicCompletion f) (Submonoid.powers f) := y.2
      have hy_bot : (y : principalAdicCompletion f) ∈
          (⊥ : Submodule R (principalAdicCompletion f)) := by
        simpa [htarget] using hy_mem
      simpa using hy_bot
    apply Subtype.ext
    simpa [hy]

end
