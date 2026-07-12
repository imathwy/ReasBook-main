import Mathlib
import StacksProject_2024.Chap10.Lemma_10_82_7
import StacksProject_2024.Chap10.Lemma_10_82_13
import StacksProject_2024.Chap10.Lemma_10_89_7
import StacksProject_2024.Chap10.Example_10_91_1
import StacksProject_2024.Chap10.Lemma_10_91_4
import StacksProject_2024.Chap10.Theorem_10_93_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

namespace LinearMap

open CategoryTheory
open CategoryTheory.ShortComplex

section

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/- Route map: work around the same-universe owner theorem by lifting source and target to one
`ModuleCat` universe, build the range-quotient short exact complex there, and then transport
flatness and the Mittag-Leffler property back to the original source. -/

/-- Helper for Chap10 Lemma 10 93 5: universal injectivity is unchanged after replacing source
and target by linearly equivalent modules, with the test modules taken in the new universe. -/
private theorem universallyInjective_equiv_comp
    {N : Type w} [AddCommGroup N] [Module R N]
    {M' N' : Type (max u (max v w))} [AddCommGroup M'] [Module R M']
    [AddCommGroup N'] [Module R N']
    (f : M →ₗ[R] N) (eM : M' ≃ₗ[R] M) (eN : N' ≃ₗ[R] N)
    (hf : UniversallyInjective.{u, v, w, max u (max v w)} f) :
    UniversallyInjective.{u, max u (max v w), max u (max v w), max u (max v w)}
      (eN.symm.toLinearMap.comp (f.comp eM.toLinearMap)) := by
  -- The tensorized lifted map becomes the original tensorized map after applying the two tensor
  -- equivalences, so injectivity descends from `hf`.
  intro Q _ _ x y hxy
  have hcomm :
      (eN.toLinearMap.rTensor Q).comp
          ((eN.symm.toLinearMap.comp (f.comp eM.toLinearMap)).rTensor Q) =
        (f.rTensor Q).comp (eM.toLinearMap.rTensor Q) := by
    rw [← LinearMap.rTensor_comp, ← LinearMap.rTensor_comp]
    ext z
    simp
  have hbase :
      (f.rTensor Q) ((eM.rTensor Q) x) =
        (f.rTensor Q) ((eM.rTensor Q) y) := by
    calc
      (f.rTensor Q) ((eM.rTensor Q) x)
          = (eN.rTensor Q)
              (((eN.symm.toLinearMap.comp (f.comp eM.toLinearMap)).rTensor Q) x) := by
              simpa using (LinearMap.congr_fun hcomm x).symm
      _ = (eN.rTensor Q)
              (((eN.symm.toLinearMap.comp (f.comp eM.toLinearMap)).rTensor Q) y) := by
              rw [hxy]
      _ = (f.rTensor Q) ((eM.rTensor Q) y) := by
              simpa using LinearMap.congr_fun hcomm y
  exact (eM.rTensor Q).injective (hf Q inferInstance inferInstance hbase)

/-- Helper for Chap10 Lemma 10 93 5: a universally injective map into a flat Mittag-Leffler module
from a direct sum of countably generated modules has projective source. -/
private theorem projective_of_universallyInjective_to_flatMittagLefflerTarget
    {N : Type w} [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (hf : UniversallyInjective.{u, v, w, max u (max v w)} f)
    [Module.Flat R N] [Module.MittagLeffler R N]
    (hM : Module.IsDirectSumOfCountablyGenerated R M) :
    Module.Projective R M := by
  let M' : Type (max u (max v w)) := ULift.{max u w} M
  let N' : Type (max u (max v w)) := ULift.{max u v} N
  let eM : M' ≃ₗ[R] M := ULift.moduleEquiv
  let eN : N' ≃ₗ[R] N := ULift.moduleEquiv
  let f' : M' →ₗ[R] N' := eN.symm.toLinearMap.comp (f.comp eM.toLinearMap)
  have hf' :
      UniversallyInjective.{u, max u (max v w), max u (max v w), max u (max v w)}
        f' := by
    -- Transport universal injectivity from `f` to the lifted same-universe map `f'`.
    simpa [f'] using universallyInjective_equiv_comp (R := R) (M := M) (N := N)
      f eM eN hf
  have hf'_inj : Function.Injective f' := by
    -- Specialize universal injectivity modulo the zero ideal, then identify the quotient by
    -- `0 • ⊤` with the original map.
    have hbotFG : (⊥ : Ideal R).FG := by
      simpa using (Submodule.fg_bot : (⊥ : Ideal R).FG)
    have hquot : Function.Injective (f'.quotientMapByIdeal (⊥ : Ideal R)) :=
      (universallyInjective_iff_injective_mod_finite_ideal f').1 hf' ⊥ hbotFG
    intro x y hxy
    have hxyQ :
        (((⊥ : Ideal R) • (⊤ : Submodule R M')).mkQ x) =
          (((⊥ : Ideal R) • (⊤ : Submodule R M')).mkQ y) := by
      apply hquot
      simp [LinearMap.quotientMapByIdeal, hxy]
    have hmem : x - y ∈ ((⊥ : Ideal R) • (⊤ : Submodule R M') : Submodule R M') :=
      (Submodule.Quotient.eq
        (((⊥ : Ideal R) • (⊤ : Submodule R M') : Submodule R M'))).mp hxyQ
    simpa [sub_eq_zero] using hmem
  have hzero :
      ModuleCat.ofHom f' ≫ ModuleCat.ofHom (LinearMap.range f').mkQ =
        (0 : ModuleCat.of R M' ⟶ ModuleCat.of R (N' ⧸ LinearMap.range f')) := by
    -- The quotient map kills the range of `f'`, giving the zero composite for `ShortComplex.mk`.
    ext x
    simp
  let S : ShortComplex (ModuleCat.{max u (max v w)} R) :=
    ShortComplex.mk (ModuleCat.ofHom f') (ModuleCat.ofHom (LinearMap.range f').mkQ) hzero
  have hExactRange : Function.Exact f' (LinearMap.range f').mkQ := by
    -- Exactness of the range-quotient pair is the standard `map_mkQ_range` exactness.
    simpa [S] using LinearMap.exact_map_mkQ_range f'
  have hSurjRange : Function.Surjective (LinearMap.range f').mkQ :=
    Submodule.mkQ_surjective _
  have hS : S.ShortExact :=
    ModuleCat.shortComplex_shortExact S hExactRange hf'_inj hSurjRange
  have hS_univ :
      UniversallyInjective.{u, max u (max v w), max u (max v w), max u (max v w)}
        S.f.hom := by
    -- The first morphism of `S` is exactly the lifted universally injective map.
    simpa [S] using hf'
  have hU : UniversallyExact.{u, max u (max v w)} S := ⟨hS, hS_univ⟩
  letI : Module.Flat R N' := Module.Flat.of_linearEquiv eN
  letI : Module.MittagLeffler R N' := Module.mittagLeffler_of_linearEquiv eN
  have hFlatLift : Module.Flat R M' := UniversallyExact.flat_X₁.{u, max v w} hU
  have hMLLift : Module.MittagLeffler R M' :=
    UniversallyExact.mittagLeffler_X₁.{u, max u (max v w)} hU
  letI : Module.Flat R M := Module.Flat.of_linearEquiv eM.symm
  letI : Module.MittagLeffler R M := Module.mittagLeffler_of_linearEquiv eM.symm
  -- With flatness and Mittag-Lefflerness transported back to `M`, Theorem `10.93.3` finishes.
  exact Module.projective_iff_flat_mittagLeffler_and_isDirectSumOfCountablyGenerated.2
    ⟨inferInstance, inferInstance, hM⟩

variable [IsNoetherianRing R]

/- Domain triage:
- `source-facing`: this Stacks lemma specializes the projectivity criterion to maps into
  `MvPowerSeries (Fin n) R`;
- `core/canonical`: the proof uses the range-quotient universally exact complex and Theorem
  `Module.projective_iff_flat_mittagLeffler_and_isDirectSumOfCountablyGenerated`, with
  `Module.Projective` as the ambient owner predicate;
- `bridge/view`: `Module.noetherian_mvPowerSeries_flat_and_mittagLeffler` provides the derived flat
  and Mittag-Leffler structure on the target module.
Primitive data are the universally injective map `f` and the direct-sum hypothesis on `M`; the
flat and Mittag-Leffler facts for the codomain are derived API and should not be repackaged
locally. -/

-- Proof sketch: install the canonical flat and Mittag-Leffler instances for
-- `MvPowerSeries (Fin n) R` from Lemma `10.91.4`, then apply the local lifted criterion above.
/-- Chap10 Lemma 10 93 5: if `M` is a direct sum of countably generated `R`-modules and admits a
universally injective `R`-linear map into the formal power series ring
`MvPowerSeries (Fin n) R`, then `M` is projective. -/
@[stacks 05A1]
theorem projective_of_universallyInjective_to_mvPowerSeries_of_isDirectSumOfCountablyGenerated
    (n : ℕ) (f : M →ₗ[R] MvPowerSeries (Fin n) R)
    (hf : UniversallyInjective.{u, v, u, max u v} f)
    (hM : Module.IsDirectSumOfCountablyGenerated R M) :
    Module.Projective R M := by
  have hTarget := Module.noetherian_mvPowerSeries_flat_and_mittagLeffler (R := R) n
  letI : Module.Flat R (MvPowerSeries (Fin n) R) := hTarget.1
  letI : Module.MittagLeffler R (MvPowerSeries (Fin n) R) := hTarget.2
  -- The general lifted criterion applies after installing the target-side flatness and
  -- Mittag-Leffler facts for multivariable power series.
  exact projective_of_universallyInjective_to_flatMittagLefflerTarget f hf hM

end

end LinearMap
