import ConvexAnalysis_Rockafellar_1970.Chap06.Proposition_6_27_6
import ConvexAnalysis_Rockafellar_1970.Chap06.Lemma_31_0_6

noncomputable section

universe u v w

namespace Bifunction

open scoped Rockafellar

section

variable {𝕜 : Type v} {E : Type u} {U : Type w} {Y : Type (max u v)}
variable [Ring 𝕜] [TopologicalSpace 𝕜] [Preorder 𝕜]
variable [AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E]
variable [Zero Y] [HasPairing E Y 𝕜] [HasPairingZeroRight E Y 𝕜]
variable [AddCommMonoid U] [Module 𝕜 U]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Lemma 31.0.15 records the extremality condition in Theorem 31.2 for the primal
  Fenchel objective `x ↦ f x - g (A x)`.
- `core/canonical`: the chapter owners already present upstream are
  `(fenchelPerturbation A f g)₀`, `minimumSet`, and Proposition 6.27.6's minimizer
  criteria at three canonical layers:
  pairing (`∂[Y]h(x)`), canonical continuous dual (`∂ h at x`), and Euclidean bridge
  (`∂ᵥh(x)`).
- `bridge/view`: the source phrase “attains its minimum at `x`” is already
  `IsMinOn ((fenchelPerturbation A f g)₀) Set.univ x` by the owner `minimumSet`, so this file
  only records specializations of the existing minimizer criteria to the Chapter 31 primal
  objective.

Domain-style sampling used here:
- `Bifunction.fenchelPerturbation` and `Bifunction.objective_fenchelPerturbation_apply` from
  `Lemma_31_0_6`;
- `minimumSet` from `Definition_6_27_3`;
- `mem_minimumSet_iff_zero_mem_subdifferentialAt_pairing`,
- `mem_minimumSet_iff_zero_mem_subdifferentialAt` and
  `mem_minimumSet_iff_zero_mem_subdifferentialAt_vector` from `Proposition_6_27_6`.

Primitive data vs derived API:
- primitive source data: the linear map `A`, the functions `f` and `g`, and the point `x`;
- primitive owner object: `(fenchelPerturbation A f g)₀` together with the canonical
  minimizer owner `minimumSet`;
- derived source-facing view: `IsMinOn _ Set.univ _`, obtained from `minimumSet` by definition.

Layer target: `source-facing` reusable specializations on the canonical owners already present
upstream.
-/

variable (A : E →ₗ[𝕜] U) (f : E → WithBotTop 𝕜) (g : U → WithBotTop 𝕜)
variable (x : E)
local notation "F0" => (fenchelPerturbation A f g)₀

/- Lemma 31.0.15, pairing-owner form: Proposition 6.27.6 specialized to the primal Fenchel
objective, at the canonical owner layer `minimumSet`. -/
/-- Lemma 31.0.15, pairing-owner form: the primal Fenchel objective `F0` has `x` in its
minimum set exactly when `0` belongs to its pairing-valued subdifferential at `x`. -/
theorem mem_minimumSet_objective_fenchelPerturbation_iff_zero_mem_subdifferentialAt_pairing :
    x ∈ minimumSet F0 ↔ (0 : Y) ∈ (∂[Y]F0(x)) := by
  exact mem_minimumSet_iff_zero_mem_subdifferentialAt_pairing

/- Source wording bridge: “attains its minimum at `x`” is `IsMinOn _ Set.univ _`,
definitionally equivalent to minimum-set membership. -/
/-- Source-phrasing bridge for Lemma 31.0.15 at the pairing owner layer: saying that `F0`
attains its minimum at `x` is equivalent to zero-subgradient membership at `x`. -/
theorem isMinOn_objective_fenchelPerturbation_univ_iff_zero_mem_subdifferentialAt_pairing :
    IsMinOn F0 Set.univ x ↔ (0 : Y) ∈ (∂[Y]F0(x)) := by
  change x ∈ minimumSet F0 ↔ (0 : Y) ∈ (∂[Y]F0(x))
  exact mem_minimumSet_objective_fenchelPerturbation_iff_zero_mem_subdifferentialAt_pairing
    (A := A) (f := f) (g := g) (x := x)

end

section

variable {𝕜 : Type v} {E : Type u} {U : Type w}
variable [NormedField 𝕜] [Preorder 𝕜]
variable [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [AddCommMonoid U] [Module 𝕜 U]

variable (A : E →ₗ[𝕜] U) (f : E → WithBotTop 𝕜) (g : U → WithBotTop 𝕜)
variable (x : E)
local notation "F0" => (fenchelPerturbation A f g)₀

/- Lemma 31.0.15, canonical-dual form: the same minimizer criterion expressed with the canonical
continuous-dual owner `∂ ((fenchelPerturbation A f g)₀) at x`. -/
/-- Lemma 31.0.15, canonical-dual form: for the primal Fenchel objective `F0`, membership of `x`
in `minimumSet F0` is equivalent to zero membership in the canonical continuous-dual
subdifferential at `x`. -/
theorem mem_minimumSet_objective_fenchelPerturbation_iff_zero_mem_subdifferentialAt :
    x ∈ minimumSet F0 ↔ (0 : StrongDual 𝕜 E) ∈ (∂ F0 at x) := by
  exact mem_minimumSet_iff_zero_mem_subdifferentialAt

/- Source wording bridge for the canonical-dual specialization. -/
/-- Source-phrasing bridge for Lemma 31.0.15 at the canonical-dual owner layer. -/
theorem isMinOn_objective_fenchelPerturbation_univ_iff_zero_mem_subdifferentialAt :
    IsMinOn F0 Set.univ x ↔ (0 : StrongDual 𝕜 E) ∈ (∂ F0 at x) := by
  change x ∈ minimumSet F0 ↔ (0 : StrongDual 𝕜 E) ∈ (∂ F0 at x)
  exact mem_minimumSet_objective_fenchelPerturbation_iff_zero_mem_subdifferentialAt
    (A := A) (f := f) (g := g) (x := x)

end

section

variable {𝕜 : Type v} {E : Type u} {U : Type w}
variable [RCLike 𝕜] [Preorder 𝕜]
variable [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [AddCommMonoid U] [Module 𝕜 U]

variable (A : E →ₗ[𝕜] U) (f : E → WithBotTop 𝕜) (g : U → WithBotTop 𝕜)
variable (x : E)
local notation "F0" => (fenchelPerturbation A f g)₀

/- Euclidean bridge form of Lemma 31.0.15: the same source-facing specialization through the
vector notation `∂ᵥ((fenchelPerturbation A f g)₀)(x)`. -/
/-- Euclidean bridge form of Lemma 31.0.15: for the primal Fenchel objective `F0`, `x` is a
global minimizer exactly when `0` belongs to the vector-valued subdifferential at `x`. -/
theorem mem_minimumSet_objective_fenchelPerturbation_iff_zero_mem_subdifferentialAt_vector :
    x ∈ minimumSet F0 ↔ (0 : E) ∈ (∂ᵥF0(x)) := by
  exact mem_minimumSet_iff_zero_mem_subdifferentialAt_vector

/- Source wording bridge for the Euclidean specialization. -/
/-- Source-phrasing bridge for Lemma 31.0.15 at the Euclidean vector owner layer. -/
theorem isMinOn_objective_fenchelPerturbation_univ_iff_zero_mem_subdifferentialAt_vector :
    IsMinOn F0 Set.univ x ↔ (0 : E) ∈ (∂ᵥF0(x)) := by
  change x ∈ minimumSet F0 ↔ (0 : E) ∈ (∂ᵥF0(x))
  exact mem_minimumSet_objective_fenchelPerturbation_iff_zero_mem_subdifferentialAt_vector
    (A := A) (f := f) (g := g) (x := x)

end

end Bifunction
