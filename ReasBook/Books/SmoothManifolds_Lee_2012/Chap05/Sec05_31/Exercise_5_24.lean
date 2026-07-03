import SmoothManifolds_Lee_2012.Chap05.Sec05_31.Proposition_5_23
import Mathlib.Tactic.Recall

open TopologicalSpace
open Manifold
open scoped Manifold ContDiff

universe uE uH uM uS

section

variable {k : ℕ}
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners ℝ E H} [IsManifold I (⊤ : WithTop ℕ∞) M]
variable {S : Type uS} [TopologicalSpace S] [ChartedSpace (EuclideanSpace ℝ (Fin k)) S]
variable [IsManifold (𝓡 k) (⊤ : WithTop ℕ∞) S]
variable {ι : S → M}

/- Exercise 5.24: this file only recalls the owner-based local-parametrization API from
Proposition 5.23. The core owner is `ImmersedSubmanifold.IsSmoothLocalParametrization`, and the
bridge from an injective immersion `ι` to that owner is `IsImmersion.toImmersedSubmanifold`. -/
recall ImmersedSubmanifold.IsSmoothLocalParametrization
recall IsImmersion.toImmersedSubmanifold

/- Exercise 5.24 (1): a smooth coordinate chart with target `U` determines the corresponding local
parametrization by composing the inverse chart with the inclusion map. -/
#check IsImmersion.isSmoothLocalParametrization_of_mem_maximalAtlas

/- Exercise 5.24 (2): Proposition 5.23 (1) is the full equivalence between smooth local
parametrizations and inverse smooth coordinate charts with target `U`. -/
#check IsImmersion.isSmoothLocalParametrization_iff_exists_chart

/- Exercise 5.24 (3): this is exactly Proposition 5.23 (2). -/
#check IsImmersion.exists_isSmoothLocalParametrization_through

end
