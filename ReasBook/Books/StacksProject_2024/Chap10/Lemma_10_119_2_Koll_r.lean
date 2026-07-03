import Mathlib
import StacksProject_2024.Chap10.Definition_10_63_1
import StacksProject_2024.Chap10.Definition_10_72_1
import StacksProject_2024.Chap10.Lemma_10_72_5
import StacksProject_2024.Chap10.Lemma_10_72_6
import StacksProject_2024.Chap10.Lemma_10_157_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open IsLocalRing
open scoped Pointwise ENat

section

variable (R : Type u) [CommRing R] [IsLocalRing R]

/-- A finite `R`-algebra appearing in Kollár's fourth alternative: the canonical map `R → S` is
not an isomorphism, its kernel and cokernel are annihilated by a power of the maximal ideal of
`R`, the maximal ideal is not an associated prime of `S`, and `S` is nonzero. -/
def HasKollarExceptionalFiniteExtension : Prop :=
  ∃ (S : Type u) (_ : CommRing S) (_ : Algebra R S) (_ : Module.Finite R S) (_ : Nontrivial S),
    ¬ Function.Bijective (algebraMap R S) ∧
      (∃ n : ℕ,
        (maximalIdeal R) ^ n • (RingHom.ker (algebraMap R S) : Submodule R R) = ⊥ ∧
        (maximalIdeal R) ^ n • (⊤ : Submodule R S) ≤ (Algebra.linearMap R S).range) ∧
      maximalIdeal R ∉ associatedPrimes R S

-- Proof sketch: this is just the defining existential package for the fourth alternative; later
-- arguments can unfold it to access the finite `R`-algebra, the `𝔪`-power torsion conditions on
-- the kernel and cokernel, the non-associated-prime hypothesis, and the nontriviality of the
-- target ring.
/-- Unfolding `HasKollarExceptionalFiniteExtension R` into its finite `R`-algebra data and the
torsion conditions on the kernel and cokernel of the canonical map. -/
theorem hasKollarExceptionalFiniteExtension_iff :
    HasKollarExceptionalFiniteExtension R ↔
      ∃ (S : Type u) (_ : CommRing S) (_ : Algebra R S) (_ : Module.Finite R S)
        (_ : Nontrivial S),
        ¬ Function.Bijective (algebraMap R S) ∧
          (∃ n : ℕ,
            (maximalIdeal R) ^ n • (RingHom.ker (algebraMap R S) : Submodule R R) = ⊥ ∧
            (maximalIdeal R) ^ n • (⊤ : Submodule R S) ≤ (Algebra.linearMap R S).range) ∧
          maximalIdeal R ∉ associatedPrimes R S := by
  -- This theorem is only the owner-level unpacking of the defining existential package.
  rfl

namespace RingHom

variable {R}
variable {S : Type u} [CommRing S]

/-- A specific finite ring map `f : R →+* S` realizes Kollár's exceptional finite-extension
alternative when the canonical `R`-algebra structure induced by `f` makes `S` a nontrivial finite
`R`-algebra, the map is not bijective, its kernel and cokernel are annihilated by a power of the
maximal ideal, and that maximal ideal is not an associated prime of `S`. This is a
`bridge/view` proposition from an explicit map to the owner predicate
`HasKollarExceptionalFiniteExtension R`. -/
def IsKollarExceptionalFiniteExtension (f : R →+* S) : Prop :=
  let _ : Algebra R S := f.toAlgebra
  Nontrivial S ∧
    Module.Finite R S ∧
      ¬ Function.Bijective f ∧
        (∃ n : ℕ,
          (maximalIdeal R) ^ n • (RingHom.ker f : Submodule R R) = ⊥ ∧
            (maximalIdeal R) ^ n • (⊤ : Submodule R S) ≤ (Algebra.linearMap R S).range) ∧
          maximalIdeal R ∉ associatedPrimes R S

/-- A map-level witness of Kollár's exceptional finite-extension alternative yields the canonical
owner proposition `HasKollarExceptionalFiniteExtension R`. -/
theorem hasKollarExceptionalFiniteExtension (f : R →+* S)
    (hf : f.IsKollarExceptionalFiniteExtension) :
    HasKollarExceptionalFiniteExtension R := by
  let _ : Algebra R S := f.toAlgebra
  rcases hf with ⟨hS, hfinite, hbij, htorsion, hassoc⟩
  exact (hasKollarExceptionalFiniteExtension_iff (R := R)).2
    ⟨S, inferInstance, f.toAlgebra, hfinite, hS, hbij, htorsion, hassoc⟩

end RingHom

variable [IsNoetherianRing R]

/-- Helper for Lemma 10.119.2 (Kollár): an associated-prime witness for `R/xR`, expressed as
`QuotSMulTop x R`, lifts to an element `y : R` that is nonzero modulo `(x)` and whose product with
every element of the maximal ideal lies in `(x)`. -/
lemma exists_lift_outside_span_singleton_of_associated_quotSMulTop {x : R}
    (hassoc : maximalIdeal R ∈ associatedPrimes R (QuotSMulTop x R)) :
    ∃ y : R, y ∉ Ideal.span ({x} : Set R) ∧
      ∀ t ∈ maximalIdeal R, y * t ∈ Ideal.span ({x} : Set R) := by
  let e : QuotSMulTop x R ≃ₗ[R] R ⧸ Ideal.span ({x} : Set R) :=
    Submodule.quotEquivOfEq (x • (⊤ : Submodule R R)) (Ideal.span ({x} : Set R))
      (by simpa using (Submodule.ideal_span_singleton_smul x (⊤ : Submodule R R)).symm)
  have hassoc' : maximalIdeal R ∈ associatedPrimesOfModule R (QuotSMulTop x R) := by
    simpa [associatedPrimesOfModule_eq_associatedPrimes (R := R) (M := QuotSMulTop x R)] using
      hassoc
  have hassoc_quot :
      maximalIdeal R ∈ associatedPrimesOfModule R (R ⧸ Ideal.span ({x} : Set R)) := by
    rw [← LinearEquiv.associatedPrimesOfModule_eq (R := R) (M := QuotSMulTop x R)
      (M' := R ⧸ Ideal.span ({x} : Set R)) e]
    exact hassoc'
  rw [mem_associatedPrimesOfModule_iff, Ideal.isAssociatedToModule_iff_exists_torsionOf] at hassoc_quot
  rcases hassoc_quot with ⟨hmax, z, hz⟩
  have hz_ne : z ≠ 0 := by
    intro hz_zero
    have htop : Ideal.torsionOf R (R ⧸ Ideal.span ({x} : Set R)) z = ⊤ := by
      simpa [hz_zero] using (Ideal.torsionOf_eq_top_iff (R := R) z).2 hz_zero
    exact hmax.ne_top (hz.trans htop)
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
  refine ⟨y, ?_, ?_⟩
  · -- The quotient class must stay nonzero, so the chosen lift does not lie in `(x)`.
    intro hy
    exact hz_ne ((Ideal.Quotient.eq_zero_iff_mem).2 hy)
  · -- Membership in the annihilator ideal says exactly that every `t ∈ 𝔪` kills the quotient
    -- class of `y`, which rewrites to `y * t ∈ (x)`.
    intro t ht
    have ht_torsion :
        t ∈ Ideal.torsionOf R (R ⧸ Ideal.span ({x} : Set R))
          (Ideal.Quotient.mk (Ideal.span ({x} : Set R)) y) := by
      simpa [hz] using ht
    rw [Ideal.mem_torsionOf_iff] at ht_torsion
    change Ideal.Quotient.mk (Ideal.span ({x} : Set R)) (t * y) = 0 at ht_torsion
    simpa [mul_comm] using (Ideal.Quotient.eq_zero_iff_mem).1 ht_torsion

/-- Helper for Lemma 10.119.2 (Kollár): a finite upper bound on the Krull dimension of a
Noetherian ring forces the dimension to be represented by an actual natural number. -/
private lemma ringKrullDim_eq_nat_of_le {d : ℕ} (h : ringKrullDim R ≤ d) :
    ∃ n : ℕ, n ≤ d ∧ ringKrullDim R = n := by
  -- Convert the `WithBot ℕ∞`-valued dimension into a genuine natural number using finiteness.
  have hbot : ringKrullDim R ≠ ⊥ := ringKrullDim_ne_bot
  have htop : ringKrullDim R ≠ ⊤ := ringKrullDim_ne_top
  let n : ℕ := ((ringKrullDim R).unbot hbot).toNat
  have hneTop : (ringKrullDim R).unbot hbot ≠ ⊤ := by
    intro htop'
    exact htop <| by
      simpa [WithBot.coe_unbot] using
        congrArg (fun x : ℕ∞ ↦ (x : WithBot ℕ∞)) htop'
  have hdim : ringKrullDim R = n := by
    have hdim' : ((ringKrullDim R).unbot hbot : WithBot ℕ∞) = n := by
      simpa [n] using
        congrArg (fun x : ℕ∞ ↦ (x : WithBot ℕ∞)) (ENat.coe_toNat hneTop).symm
    calc
      ringKrullDim R = (ringKrullDim R).unbot hbot := by
        exact (WithBot.coe_unbot (ringKrullDim R) hbot).symm
      _ = n := hdim'
  refine ⟨n, ?_, hdim⟩
  -- The original upper bound transports directly to the recovered natural dimension.
  simpa [hdim] using h

/-- Helper for Lemma 10.119.2 (Kollár): if `y / x` in the localization away from a regular
element `x` came from `R`, then `y` would already lie in the principal ideal `(x)`. -/
lemma localized_ratio_not_mem_range_of_not_mem_span_singleton {x y : R}
    (hxreg : IsSMulRegular R x) (hy : y ∉ Ideal.span ({x} : Set R)) :
    let z : Localization.Away x :=
      algebraMap R (Localization.Away x) y * IsLocalization.Away.invSelf x
    z ∉ Set.range (algebraMap R (Localization.Away x)) := by
  dsimp
  rintro ⟨r, hr⟩
  have hinj : Function.Injective (algebraMap R (Localization.Away x)) := by
    -- Regularity of `x` propagates to every denominator in the localization away from `x`.
    rw [IsLocalization.injective_iff_isRegular (M := Submonoid.powers x) (S := Localization.Away x)]
    intro c
    rcases c with ⟨c, ⟨n, rfl⟩⟩
    have hx_regular : IsRegular x :=
      (Commute.isRegular_iff (a := x) (fun b ↦ mul_comm x b)).mpr hxreg.isLeftRegular
    simpa using hx_regular.pow n
  have hr' : algebraMap R (Localization.Away x) (r * x) =
      algebraMap R (Localization.Away x) y := by
    -- Multiplying the identity `y / x = r` by `x` clears the denominator inside the localization.
    calc
      algebraMap R (Localization.Away x) (r * x) =
          algebraMap R (Localization.Away x) r * algebraMap R (Localization.Away x) x := by
            simp [map_mul]
      _ = (algebraMap R (Localization.Away x) y * IsLocalization.Away.invSelf x) *
            algebraMap R (Localization.Away x) x := by
            rw [hr]
      _ = algebraMap R (Localization.Away x) y *
            (IsLocalization.Away.invSelf x * algebraMap R (Localization.Away x) x) := by
            rw [mul_assoc]
      _ = algebraMap R (Localization.Away x) y * 1 := by
            rw [mul_comm (IsLocalization.Away.invSelf x), IsLocalization.Away.mul_invSelf]
      _ = algebraMap R (Localization.Away x) y := by
            simp
  have hyr : r * x = y := hinj hr'
  -- Therefore `y` lies in `(x)`, contradicting the chosen lift.
  exact hy <| Ideal.mem_span_singleton'.2 ⟨r, hyr⟩

/-- Helper for Lemma 10.119.2 (Kollár): outside the Artinian case, a principal maximal ideal
forces the ring to be regular local of dimension `1`. -/
lemma regular_dim_one_of_principal_maximalIdeal_and_not_artinian
    (hprincipal : (maximalIdeal R).IsPrincipal) (hnotArtinian : ¬ IsArtinianRing R) :
    IsRegularLocalRing R ∧ ringKrullDim R = 1 := by
  have hnontrivial : Nontrivial R := by
    -- The zero ring is Artinian, so the non-Artinian hypothesis rules it out immediately.
    by_contra hsub
    letI : Subsingleton R := not_nontrivial_iff_subsingleton.mp hsub
    exact hnotArtinian inferInstance
  have hspan_le : (maximalIdeal R).spanFinrank ≤ 1 := by
    -- A principal maximal ideal is generated by one element, hence has span finrank at most `1`.
    obtain ⟨x, hx⟩ := Submodule.IsPrincipal.principal (maximalIdeal R)
    rw [hx]
    calc
      (Ideal.span ({x} : Set R)).spanFinrank ≤ ({x} : Set R).ncard := by
        exact Submodule.spanFinrank_span_le_ncard_of_finite (Set.toFinite {x})
      _ = 1 := by
        simp
  have hdim_le : ringKrullDim R ≤ 1 := by
    -- Krull's height theorem bounds the local dimension by the number of generators of `𝔪`.
    exact le_trans (ringKrullDim_le_spanFinrank_maximalIdeal (R := R)) (by exact_mod_cast hspan_le)
  obtain ⟨n, hn_le, hdim⟩ := ringKrullDim_eq_nat_of_le (R := R) hdim_le
  have hn_ne_zero : n ≠ 0 := by
    -- Dimension `0` would make the Noetherian local ring Artinian, contrary to hypothesis.
    intro hn_zero
    have hdim_zero : ringKrullDim R = 0 := by
      simpa [hn_zero] using hdim
    have hdim_le_zero : Ring.KrullDimLE 0 R :=
      ringKrullDimZero_iff_ringKrullDim_eq_zero.mpr hdim_zero
    exact hnotArtinian <|
      (isArtinianRing_iff_isNoetherianRing_krullDimLE_zero).2 ⟨inferInstance, hdim_le_zero⟩
  have hn_one : n = 1 := by
    omega
  have hregular : IsRegularLocalRing R := by
    -- With `dim R = 1`, the one-generator bound is exactly the regular-local criterion.
    refine IsRegularLocalRing.of_spanFinrank_maximalIdeal_le (R := R) ?_
    calc
      ↑(maximalIdeal R).spanFinrank ≤ (1 : WithBot ℕ∞) := by
        exact_mod_cast hspan_le
      _ = ringKrullDim R := by
        simpa [hn_one] using hdim.symm
  exact ⟨hregular, by simpa [hn_one] using hdim⟩

/-- Helper for Lemma 10.119.2 (Kollár): a nontrivial finite module annihilated by a power of the
maximal ideal has depth `0`. -/
lemma moduleDepth_eq_zero_of_pow_maximalIdeal_smul_top_eq_bot
    {M : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]
    {n : ℕ} (hn : (maximalIdeal R) ^ n • (⊤ : Submodule R M) = ⊥) :
    moduleDepth R M = 0 := by
  by_contra hdepth
  -- Positive depth gives a regular element in `𝔪`, exactly as in the source proof.
  obtain ⟨x, hx, hxreg⟩ :=
    exists_mem_maximalIdeal_isSMulRegular_of_moduleDepth_ne_zero (R := R) (M := M) hdepth
  have hpowreg : IsSMulRegular M (x ^ n) := hxreg.pow n
  have hpow_eq_zero : ((x ^ n) • · : M → M) = ((0 : R) • ·) := by
    funext m
    -- Since `x^n ∈ 𝔪^n`, the `𝔪^n`-torsion hypothesis forces `x^n • m = 0`.
    have hmem : x ^ n • m ∈ (maximalIdeal R) ^ n • (⊤ : Submodule R M) := by
      exact Submodule.smul_mem_smul (Ideal.pow_mem_pow hx n) (by simp)
    simpa [hn] using hmem
  have hzero_reg : IsSMulRegular M (0 : R) := by
    simpa [IsSMulRegular, hpow_eq_zero] using hpowreg
  exact (IsSMulRegular.not_zero (M := M)) hzero_reg

/-- Helper for Lemma 10.119.2 (Kollár): a submodule of `R` killed by a power of the maximal ideal
cannot have positive depth unless it is zero. -/
lemma submodule_eq_bot_of_pow_maximalIdeal_smul_eq_bot_of_moduleDepth_ne_zero
    (N : Submodule R R) {n : ℕ} (hn : (maximalIdeal R) ^ n • N = ⊥)
    (hdepth : moduleDepth R N ≠ 0) :
    N = ⊥ := by
  by_contra hN
  letI : Nontrivial N := Submodule.nontrivial_iff_ne_bot.mpr hN
  have hdepth_zero : moduleDepth R N = 0 := by
    -- Rewrite the ambient annihilation statement onto the top submodule of `N`.
    have hn' : (maximalIdeal R) ^ n • (⊤ : Submodule R N) = ⊥ := by
      apply le_antisymm ?_ bot_le
      intro x hx
      have hx' : (x : R) ∈ (maximalIdeal R) ^ n • N :=
        (Submodule.mem_smul_top_iff (I := (maximalIdeal R) ^ n) (N := N) (x := x)).1 hx
      have hx0' : (x : R) = 0 := by
        have hx0 : (x : R) ∈ (⊥ : Submodule R R) := by
          rw [← hn]
          exact hx'
        simpa [Submodule.mem_bot] using hx0
      exact Subtype.ext hx0'
    exact moduleDepth_eq_zero_of_pow_maximalIdeal_smul_top_eq_bot (R := R) (M := N) hn'
  exact hdepth hdepth_zero

/-- Helper for Lemma 10.119.2 (Kollár): a finite module killed by a power of the maximal ideal is
trivial as soon as its depth is nonzero. -/
lemma subsingleton_of_pow_maximalIdeal_smul_top_eq_bot_of_moduleDepth_ne_zero
    {M : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M]
    {n : ℕ} (hn : (maximalIdeal R) ^ n • (⊤ : Submodule R M) = ⊥)
    (hdepth : moduleDepth R M ≠ 0) :
    Subsingleton M := by
  by_contra hM
  letI : Nontrivial M := not_subsingleton_iff_nontrivial.mp hM
  exact hdepth (moduleDepth_eq_zero_of_pow_maximalIdeal_smul_top_eq_bot
    (R := R) (M := M) hn)

/-- Helper for Lemma 10.119.2 (Kollár): a linear equivalence preserves the regular-sequence
lengths cut out by a fixed ideal. -/
private theorem regularSequenceLengths_eq_of_linearEquiv {M N : Type u} [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module R N] (I : Ideal R) (e : M ≃ₗ[R] N) :
    Ideal.regularSequenceLengths I M = Ideal.regularSequenceLengths I N := by
  -- Transport each regular sequence across the equivalence and then reverse the argument.
  ext d
  constructor
  · rintro ⟨rs, hreg, hI, rfl⟩
    exact ⟨rs, (e.isRegular_congr rs).1 hreg, hI, rfl⟩
  · rintro ⟨rs, hreg, hI, rfl⟩
    exact ⟨rs, (e.isRegular_congr rs).2 hreg, hI, rfl⟩

/-- Helper for Lemma 10.119.2 (Kollár): finite modules related by a linear equivalence have the
same ideal depth. -/
private theorem idealDepth_eq_of_linearEquiv {M N : Type u} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Module.Finite R M] [Module.Finite R N] (I : Ideal R)
    (e : M ≃ₗ[R] N) :
    Ideal.depth I M = Ideal.depth I N := by
  -- Compare the `IM = M` branch on both sides, and otherwise use the same regular-sequence data.
  have htop : I • (⊤ : Submodule R M) = ⊤ ↔ I • (⊤ : Submodule R N) = ⊤ := by
    constructor
    · intro h
      have hmap := congrArg (Submodule.map e.toLinearMap) h
      simpa [Submodule.map_smul'', LinearMap.range_eq_top.2 e.surjective] using hmap
    · intro h
      have hmap := congrArg (Submodule.map e.symm.toLinearMap) h
      simpa [Submodule.map_smul'', LinearMap.range_eq_top.2 e.symm.surjective] using hmap
  by_cases hM : I • (⊤ : Submodule R M) = ⊤
  · rw [Ideal.depth_eq_top_of_smul_top I M hM, Ideal.depth_eq_top_of_smul_top I N (htop.mp hM)]
  · rw [Ideal.depth_eq_sSup_lengths_of_smul_top_ne_top I M hM,
      Ideal.depth_eq_sSup_lengths_of_smul_top_ne_top I N (mt htop.mpr hM),
      regularSequenceLengths_eq_of_linearEquiv (R := R) (M := M) (N := N) I e]

/-- Helper for Lemma 10.119.2 (Kollár): linear equivalences preserve module depth over the local
base ring. -/
private theorem moduleDepth_eq_of_linearEquiv {M N : Type u} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Module.Finite R M] [Module.Finite R N]
    (e : M ≃ₗ[R] N) :
    moduleDepth R M = moduleDepth R N := by
  -- Specialize ideal-depth invariance to the maximal ideal.
  simpa [moduleDepth] using
    idealDepth_eq_of_linearEquiv (R := R) (M := M) (N := N) (maximalIdeal R) e

/-- Helper for Lemma 10.119.2 (Kollár): the canonical row `0 → N → M → M / N → 0` as a short
complex of `R`-modules. -/
private abbrev submodule_quotient_shortComplex {M : Type u} [AddCommGroup M] [Module R M]
    (N : Submodule R M) :
    CategoryTheory.ShortComplex (ModuleCat R) :=
  CategoryTheory.ShortComplex.moduleCatMk N.subtype N.mkQ
    (LinearMap.exact_subtype_mkQ N).linearMap_comp_eq_zero

/-- Helper for Lemma 10.119.2 (Kollár): the canonical quotient row is short exact. -/
private theorem submodule_quotient_shortExact {M : Type u} [AddCommGroup M] [Module R M]
    (N : Submodule R M) :
    (submodule_quotient_shortComplex (R := R) N).ShortExact := by
  -- Exactness is the standard kernel-range computation for `N ↪ M → M / N`.
  refine CategoryTheory.ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
    simpa [submodule_quotient_shortComplex] using LinearMap.exact_subtype_mkQ N
  · exact (ModuleCat.mono_iff_injective _).2 N.subtype_injective
  · exact (ModuleCat.epi_iff_surjective _).2 N.mkQ_surjective

namespace Submodule

/-- Helper for Lemma 10.119.2 (Kollár): the quotient row `0 → N → M → M / N → 0` gives the
standard lower bound on the depth of `M / N`. -/
lemma moduleDepth_quotient_ge_min_of_submodule_row {M : Type u} [AddCommGroup M] [Module R M]
    [Module.Finite R M] (N : Submodule R M) :
    moduleDepth R (M ⧸ N) ≥ min (moduleDepth R M) (moduleDepth R N - 1) := by
  letI : Module.Finite R N :=
    Module.Finite.of_injective N.subtype N.injective_subtype
  letI : Module.Finite R (M ⧸ N) :=
    Module.Finite.of_surjective N.mkQ N.mkQ_surjective
  letI : Module.Finite R ((submodule_quotient_shortComplex (R := R) N).X₁) := by
    change Module.Finite R N
    infer_instance
  letI : Module.Finite R ((submodule_quotient_shortComplex (R := R) N).X₃) := by
    change Module.Finite R (M ⧸ N)
    infer_instance
  -- Apply the chapter's short-exact depth inequality to the canonical quotient row.
  simpa [submodule_quotient_shortComplex] using
    CategoryTheory.ShortComplex.ShortExact.moduleDepth_right_ge_min
      (R := R) (S := submodule_quotient_shortComplex (R := R) N)
      (submodule_quotient_shortExact (R := R) N)

end Submodule

/-- Helper for Lemma 10.119.2 (Kollár): if a power of the maximal ideal sends `N` into the range
of `f`, then the same power kills the quotient `N / range(f)`. -/
lemma pow_smul_top_eq_bot_of_pow_smul_top_le_range_mkQ
    {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {f : M →ₗ[R] N} {n : ℕ}
    (h : (maximalIdeal R) ^ n • (⊤ : Submodule R N) ≤ LinearMap.range f) :
    (maximalIdeal R) ^ n • (⊤ : Submodule R (N ⧸ LinearMap.range f)) = ⊥ := by
  apply le_antisymm ?_ bot_le
  -- Map the containment through `mkQ`; the image of the range is zero in the quotient.
  have hmap :
      Submodule.map (Submodule.mkQ (LinearMap.range f))
          ((maximalIdeal R) ^ n • (⊤ : Submodule R N)) ≤
        (⊥ : Submodule R (N ⧸ LinearMap.range f)) := by
    calc
      Submodule.map (Submodule.mkQ (LinearMap.range f))
          ((maximalIdeal R) ^ n • (⊤ : Submodule R N)) ≤
          Submodule.map (Submodule.mkQ (LinearMap.range f)) (LinearMap.range f) :=
        Submodule.map_mono h
      _ = ⊥ := by
        simpa using (Submodule.mkQ_map_self (p := LinearMap.range f))
  simpa [Submodule.map_smul''] using hmap

/-- Helper for Lemma 10.119.2 (Kollár): once the canonical map `R → S` is injective, depth at
least `2` on `R` forces positive depth on the quotient `S / range(R → S)`. -/
lemma moduleDepth_quotient_range_algebraLinearMap_ne_zero_of_depth_ge_two
    {S : Type u} [CommRing S] [Algebra R S] [Module.Finite R S]
    (hinj : Function.Injective (algebraMap R S))
    (hdepth : (2 : WithTop ℕ) ≤ moduleDepth R R)
    (hassoc : maximalIdeal R ∉ associatedPrimes R S) :
    moduleDepth R (S ⧸ LinearMap.range (Algebra.linearMap R S)) ≠ 0 := by
  let η : R →ₗ[R] S := Algebra.linearMap R S
  letI : Module.Finite R (LinearMap.range η) :=
    Module.Finite.of_injective (LinearMap.range η).subtype (LinearMap.range η).injective_subtype
  letI : Module.Finite R (S ⧸ LinearMap.range η) :=
    Module.Finite.of_surjective (LinearMap.range η).mkQ (Submodule.mkQ_surjective _)
  have hdepthS_ne_zero : moduleDepth R S ≠ 0 := by
    -- The exceptional witness already rules out `𝔪` as an associated prime of `S`.
    intro hzero
    exact hassoc <|
      Module.maximalIdeal_mem_associatedPrimes_of_moduleDepth_eq_zero
        (A := R) (N := S) hzero
  have hdepthRange :
      moduleDepth R (LinearMap.range η) = moduleDepth R R := by
    -- Replace `R` by the concrete image of `η` via the injective range equivalence.
    simpa [η] using
      (moduleDepth_eq_of_linearEquiv (R := R)
        (M := R) (N := LinearMap.range η)
        (LinearEquiv.ofInjective η (by simpa [η] using hinj))).symm
  have hdepthQ :
      min (moduleDepth R S) (moduleDepth R (LinearMap.range η) - 1) ≤
        moduleDepth R (S ⧸ LinearMap.range η) := by
    -- Use the canonical quotient row `0 → range(η) → S → S / range(η) → 0`.
    simpa [η] using
      (Submodule.moduleDepth_quotient_ge_min_of_submodule_row
        (R := R) (M := S) (N := LinearMap.range η))
  have honeS : (1 : ℕ∞) ≤ moduleDepth R S :=
    ENat.one_le_iff_ne_zero.2 hdepthS_ne_zero
  have htwoRange : (2 : ℕ∞) ≤ moduleDepth R (LinearMap.range η) := by
    simpa [hdepthRange] using hdepth
  have honeRangeSub :
      (1 : ℕ∞) ≤ moduleDepth R (LinearMap.range η) - 1 := by
    -- Depth at least `2` prevents the predecessor from vanishing.
    have hne :
        moduleDepth R (LinearMap.range η) - 1 ≠ 0 := by
      intro hzero
      have hle : moduleDepth R (LinearMap.range η) ≤ 1 :=
        (tsub_eq_zero_iff_le).1 hzero
      have : (2 : ℕ∞) ≤ (1 : ℕ∞) := le_trans htwoRange hle
      norm_num at this
    exact ENat.one_le_iff_ne_zero.2 hne
  have honeMin :
      (1 : ℕ∞) ≤ min (moduleDepth R S) (moduleDepth R (LinearMap.range η) - 1) := by
    exact le_min honeS honeRangeSub
  exact ENat.one_le_iff_ne_zero.1 (le_trans honeMin hdepthQ)

/-- Helper for Lemma 10.119.2 (Kollár): depth at least `2` excludes Kollár's exceptional finite
extension alternative. -/
lemma not_hasKollarExceptionalFiniteExtension_of_depth_ge_two
    (hdepth : (2 : WithTop ℕ) ≤ moduleDepth R R) :
    ¬ HasKollarExceptionalFiniteExtension R := by
  -- Route correction: work with the canonical quotient row
  -- `0 → range(R → S) → S → S / range(R → S) → 0`, so the cokernel torsion statement can be
  -- transported once through `mkQ` instead of being re-expanded through a raw custom exact row.
  intro hExceptional
  rcases (hasKollarExceptionalFiniteExtension_iff (R := R)).1 hExceptional with
    ⟨S, _, _, _, _, hnotbij, ⟨n, hker, htop⟩, hassoc⟩
  let η : R →ₗ[R] S := Algebra.linearMap R S
  let K : Submodule R R := (RingHom.ker (algebraMap R S) : Submodule R R)
  have hdepthR_ne_zero : moduleDepth R R ≠ 0 := by
    intro hzero
    have hbad : ¬ ((2 : WithTop ℕ) ≤ 0) := by
      norm_num
    have hzeroDepth : (2 : WithTop ℕ) ≤ 0 := by
      have hdepth' := hdepth
      rwa [hzero] at hdepth'
    exact hbad hzeroDepth
  obtain ⟨x, hx, hxreg⟩ :=
    exists_mem_maximalIdeal_isSMulRegular_of_moduleDepth_ne_zero
      (R := R) (M := R) hdepthR_ne_zero
  have hKbot : K = ⊥ := by
    by_cases hK : K = ⊥
    · exact hK
    · letI : Nontrivial K := Submodule.nontrivial_iff_ne_bot.mpr hK
      letI : Module.Finite R K := Module.Finite.of_injective K.subtype K.injective_subtype
      have hdepthK_ne_zero : moduleDepth R K ≠ 0 := by
        -- The same maximal-ideal regular element stays regular on the kernel submodule.
        intro hzero
        have hno :=
          (moduleDepth_eq_zero_iff_no_maximalIdeal_regular (R := R) (M := K)).1 hzero
        exact hno ⟨x, hx, IsSMulRegular.submodule K x hxreg⟩
      exact
        submodule_eq_bot_of_pow_maximalIdeal_smul_eq_bot_of_moduleDepth_ne_zero
          (R := R) K (by simpa [K] using hker) hdepthK_ne_zero
  have hker_bot : RingHom.ker (algebraMap R S) = ⊥ := by
    simpa [K] using hKbot
  have hinj : Function.Injective (algebraMap R S) := by
    exact (RingHom.injective_iff_ker_eq_bot (algebraMap R S)).2 hker_bot
  letI : Module.Finite R (S ⧸ LinearMap.range η) :=
    Module.Finite.of_surjective (LinearMap.range η).mkQ (Submodule.mkQ_surjective _)
  have hquot_depth_ne_zero :
      moduleDepth R (S ⧸ LinearMap.range η) ≠ 0 :=
    moduleDepth_quotient_range_algebraLinearMap_ne_zero_of_depth_ge_two
      (R := R) (S := S) hinj hdepth hassoc
  have hquot_torsion :
      (maximalIdeal R) ^ n • (⊤ : Submodule R (S ⧸ LinearMap.range η)) = ⊥ :=
    pow_smul_top_eq_bot_of_pow_smul_top_le_range_mkQ
      (R := R) (f := η) (n := n) (by simpa [η] using htop)
  have hquot_subsingleton : Subsingleton (S ⧸ LinearMap.range η) :=
    subsingleton_of_pow_maximalIdeal_smul_top_eq_bot_of_moduleDepth_ne_zero
      (R := R) (M := S ⧸ LinearMap.range η) hquot_torsion hquot_depth_ne_zero
  have hsurjη : Function.Surjective η := by
    -- Vanishing of the quotient means the image is all of `S`.
    exact LinearMap.range_eq_top.1 ((Submodule.Quotient.subsingleton_iff).1 hquot_subsingleton)
  have hsurj : Function.Surjective (algebraMap R S) := by
    simpa [η] using hsurjη
  exact hnotbij ⟨hinj, hsurj⟩

/-- Helper for Lemma 10.119.2 (Kollár): in an Artinian local ring, every prime ideal is the
maximal ideal. -/
lemma prime_eq_maximalIdeal_of_isArtinianRing {p : Ideal R}
    (hArt : IsArtinianRing R) (hp : p.IsPrime) :
    p = maximalIdeal R := by
  have hpmax : p.IsMaximal := (IsArtinianRing.isPrime_iff_isMaximal p).mp hp
  have hple : p ≤ maximalIdeal R := IsLocalRing.le_maximalIdeal hp.ne_top
  -- Localness collapses the unique maximal ideal of the Artinian ring onto any prime ideal.
  exact hpmax.eq_of_le (IsLocalRing.maximalIdeal.isMaximal R).ne_top hple

/-- Helper for Lemma 10.119.2 (Kollár): the Artinian alternative excludes Kollár's exceptional
finite-extension alternative because every associated prime of a nonzero finite module is then the
maximal ideal. -/
lemma not_hasKollarExceptionalFiniteExtension_of_isArtinianRing
    (hArt : IsArtinianRing R) :
    ¬ HasKollarExceptionalFiniteExtension R := by
  intro hExceptional
  rcases (hasKollarExceptionalFiniteExtension_iff (R := R)).1 hExceptional with
    ⟨S, hSComm, hSAlg, hSFinite, hSNontrivial, _, _, hassoc⟩
  letI : CommRing S := hSComm
  letI : Algebra R S := hSAlg
  letI : Module.Finite R S := hSFinite
  letI : Nontrivial S := hSNontrivial
  obtain ⟨p, hp_assoc⟩ := associatedPrimes.nonempty R S
  have hp_eq : p = maximalIdeal R :=
    prime_eq_maximalIdeal_of_isArtinianRing (R := R) hArt hp_assoc.1
  -- The witness module `S` must have an associated prime, and in the Artinian local case that
  -- associated prime can only be `𝔪`, contradicting the exceptional-extension hypothesis.
  exact hassoc (hp_eq ▸ hp_assoc)

-- Proof sketch: the textbook argument first proves that one of the four alternatives must occur
-- by killing the maximal `𝔪`-power-torsion ideal, finding a nonzerodivisor in `𝔪`, and then
-- splitting into the depth-at-least-two, regular-dimension-one, and exceptional-finite-extension
-- cases via the determinantal trick. It then shows these alternatives are pairwise incompatible,
-- with the nontrivial exclusions against the fourth case handled by the freeness result for
-- maximal Cohen-Macaulay modules over a one-dimensional regular local ring and by the depth
-- inequalities in short exact sequences.
/-- Lemma 10.119.2 (Kollár): for a local Noetherian ring `R`, exactly one of the following holds:
`R` is Artinian, `R` is a regular local ring of dimension `1`, the depth of `R` is at least `2`,
or there exists a finite ring map `R → S` which is not an isomorphism, whose kernel and cokernel
are annihilated by a power of the maximal ideal, such that the maximal ideal of `R` is not an
associated prime of `S` and `S` is nonzero. -/
theorem kollar_exactly_one_of_artinian_regular_dim_one_depth_ge_two_or_exceptional_finite_extension :
    Xor' (IsArtinianRing R)
      (Xor' (IsRegularLocalRing R ∧ ringKrullDim R = 1)
        (Xor' ((2 : WithTop ℕ) ≤ moduleDepth R R)
          (HasKollarExceptionalFiniteExtension R))) :=
  -- Route correction: the source-faithful `R/xR` witness extraction is now isolated in
  -- `exists_lift_outside_span_singleton_of_associated_quotSMulTop`. The remaining gap is the next
  -- source step: package the determinantal-trick branch into
  -- `HasKollarExceptionalFiniteExtension R`, then finish the final incompatibility checks.
  -- TODO: prove the simple-adjoin localization branch
  -- `hasKollarExceptionalFiniteExtension_of_determinantal_data`, then thread the resulting
  -- four-way case split through the final nested `Xor'`.
  sorry

end
