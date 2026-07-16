import Mathlib
import StacksProject_2024.stacks_project.Chap10.Lemma_10_82_7
import StacksProject_2024.stacks_project.Chap10.Lemma_10_82_13
import StacksProject_2024.stacks_project.Chap10.Lemma_10_89_7
import StacksProject_2024.stacks_project.Chap10.Theorem_10_93_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace LinearMap

open CategoryTheory
open CategoryTheory.ShortComplex

section

variable {R : Type u} [CommRing R]
variable {M N : Type v}
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N]

-- Proof sketch: attach to `f` the short exact sequence `0 → M → N → N ⧸ range f → 0`. Universal
-- injectivity makes this short complex universally exact, so Lemma `10.82.7` gives flatness of
-- `M` from flatness of `N`, and Lemma `10.89.7` gives the Mittag-Leffler property of `M` from that
-- of `N`. Then apply Theorem `10.93.3` using the assumed decomposition of `M` as a direct sum of
-- countably generated submodules.
/-- Lemma 10.93.4: if `f : M →ₗ[R] N` is universally injective, `M` is a direct sum of countably
generated `R`-modules, and `N` is flat and Mittag-Leffler, then `M` is projective. -/
theorem projective_of_universallyInjective_of_flat_of_mittagLeffler_of_isDirectSumOfCountablyGenerated
    (f : M →ₗ[R] N) (hf : UniversallyInjective.{u, v, v, v} f)
    [Module.Flat R N] [Module.MittagLeffler R N]
    (hM : Module.IsDirectSumOfCountablyGenerated R M) :
    Module.Projective R M := by
  have hf_inj : Function.Injective f := by
    have hquot : Function.Injective (f.quotientMapByIdeal (⊥ : Ideal R)) :=
      (universallyInjective_iff_injective_mod_finite_ideal f).1 hf ⊥
        (by simpa using (Submodule.fg_bot : (⊥ : Ideal R).FG))
    intro x y hxy
    have hxyQ :
        (((⊥ : Ideal R) • (⊤ : Submodule R M)).mkQ x) =
          (((⊥ : Ideal R) • (⊤ : Submodule R M)).mkQ y) := by
      apply hquot
      simp [LinearMap.quotientMapByIdeal, hxy]
    have hmem : x - y ∈ ((⊥ : Ideal R) • (⊤ : Submodule R M) : Submodule R M) :=
      (Submodule.Quotient.eq (((⊥ : Ideal R) • (⊤ : Submodule R M) : Submodule R M))).mp hxyQ
    simpa [sub_eq_zero] using hmem
  let S : ShortComplex (ModuleCat.{v} R) :=
    ShortComplex.mk (ModuleCat.ofHom f) (ModuleCat.ofHom (LinearMap.range f).mkQ)
      (by
        ext x
        simp)
  have hS : S.ShortExact := ModuleCat.shortComplex_shortExact S
    (by simpa [S] using LinearMap.exact_map_mkQ_range f)
    hf_inj (Submodule.mkQ_surjective _)
  have hU : UniversallyExact S := ⟨hS, by simpa [S] using hf⟩
  letI : Module.Flat R M := UniversallyExact.flat_X₁ hU
  letI : Module.MittagLeffler R M := UniversallyExact.mittagLeffler_X₁ hU
  exact
    Module.projective_iff_flat_mittagLeffler_and_isDirectSumOfCountablyGenerated.2
      ⟨inferInstance, inferInstance, hM⟩

end

end LinearMap
