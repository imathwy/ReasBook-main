import Mathlib
import StacksProject_2024.stacks_project.Chap10.Lemma_10_91_4
import StacksProject_2024.stacks_project.Chap10.Lemma_10_93_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace LinearMap

section

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/- Domain triage:
- `source-facing`: this Stacks lemma specializes the projectivity criterion to maps into
  `MvPowerSeries (Fin n) R`;
- `core/canonical`: `LinearMap
  .projective_of_universallyInjective_of_flat_of_mittagLeffler_of_isDirectSumOfCountablyGenerated`
  is the owner theorem, with `Module.Projective` as the ambient owner predicate;
- `bridge/view`: `Module.noetherian_mvPowerSeries_flat_and_mittagLeffler` provides the derived flat
  and Mittag-Leffler structure on the target module.
Primitive data are the universally injective map `f` and the direct-sum hypothesis on `M`; the
flat and Mittag-Leffler facts for the codomain are derived API and should not be repackaged
locally. -/

-- Proof sketch: install the canonical flat and Mittag-Leffler instances for
-- `MvPowerSeries (Fin n) R` from Lemma `10.91.4`, then apply the owner theorem `10.93.4`.
/-- Lemma 10.93.5: if `M` is a direct sum of countably generated `R`-modules and admits a
universally injective `R`-linear map into the formal power series ring
`MvPowerSeries (Fin n) R`, then `M` is projective. -/
theorem projective_of_universallyInjective_to_mvPowerSeries_of_isDirectSumOfCountablyGenerated
    (n : ℕ) (f : M →ₗ[R] MvPowerSeries (Fin n) R) (hf : UniversallyInjective f)
    (hM : Module.IsDirectSumOfCountablyGenerated R M) :
    Module.Projective R M := by
  sorry

end

end LinearMap
