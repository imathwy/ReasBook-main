import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap02.Definition_8_9_1
import ConvexAnalysis_Rockafellar_1970.Chap04.Text_19_0_8
import ConvexAnalysis_Rockafellar_1970.Chap04.Text_21_0_1
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_27_4
import ConvexAnalysis_Rockafellar_1970.Chap06.Theorem_6_27_3

open scoped Rockafellar

noncomputable section

universe u v

variable {𝕜 : Type*} {E : Type u}

variable [Field 𝕜]
variable [ConditionallyCompleteLinearOrder 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜]
variable [IsStrictOrderedRing 𝕜]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 6.27.5 concerns minimization of a closed proper convex objective
  `f₀` under an arbitrary family of weak convex inequalities `fᵢ(x) ≤ 0`, first under a
  no-common-recession hypothesis and then under the finite-polyhedral refinement where the
  remaining common recession directions are constant for the objective and the nonpolyhedral
  constraints.
- `core/canonical`: the owner abstractions already present in the project are the Chapter 21 weak
  feasible-set owner `weakConvexInequalitySolutionSet`, the source-facing function recession
  predicate `Function.RecedesInDirection`, the primitive convex/proper/lower-semicontinuous
  owners (`Function.IsConvex`, `Function.IsProper`, `LowerSemicontinuous`), the
  polyhedral-function owner
  `Function.HasPolyhedralEpigraph`, the canonical constant-translation-direction owner
  `Function.lineal`, and the minimizer owner `IsMinOn`.
- `bridge/view`: textbook consistency is recorded canonically as nonemptiness of the weak feasible
  set, while the conclusion is stated in owner form as existence of a minimizer of `f₀` on that
  feasible set. The second clause keeps the source's finite polyhedral subsystem explicitly as an
  intrinsic finite subset `I₀ : Set I` together with `I₀.Finite`, but phrases constant common
  recession directions through the intrinsic nonpolyhedral owner test
  `¬ (f i).HasPolyhedralEpigraph` and the existing lineality notation `lin(·)`, instead of a
  parallel local predicate.

Domain-style sampling used here:
- `weakConvexInequalitySolutionSet` from `Chap04/Text_21_0_1`;
- `Function.RecedesInDirection` from `Chap06/Definition_6_27_4`;
- `exists_mem_isMinOn_of_no_common_recession_direction` from `Chap06/Theorem_6_27_3`;
- `Function.HasPolyhedralEpigraph` from `Chap04/Text_19_0_8`;
- `Function.lineal` and
  `Function.mem_lineal_iff_forall_translate_profile_constant` from
  `Chap02/Definition_8_9_1`.

Primitive data vs derived API:
- primitive inputs: the objective `f₀`, the constraint family `f`, consistency of the weak
  feasible set, the source-facing common-recession hypotheses, and in the refined clause a finite
  polyhedral subfamily `I₀ : Set I` together with its finiteness witness `I₀.Finite` and the
  canonical lineality owner for constant-translation directions;
- derived API: existence of a minimizer in the canonical owner form
  `∃ x ∈ weakConvexInequalitySolutionSet f, IsMinOn f₀ ... x`.

Layer target: `source-facing`, but stated directly on the canonical feasible-set and minimizer
owners, with constant common recession directions expressed by the existing owner `lineal`
instead of a separate constrained-program wrapper or local constancy predicate.

Ambient-layer note:
- clause (1) is placed on the same finite-dimensional topological-vector-space layer over `𝕜` as the
  owner theorem `exists_mem_isMinOn_of_no_common_recession_direction`;
- clause (2) stays on that same faithful TVS layer, keeping the topological-vector-space
  compatibility and separation assumptions needed for Chapter 6 closed/proper/convex attainment
  statements, without reintroducing any stronger concrete model.
-/

variable [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E]
variable [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [T2Space E] [FiniteDimensional 𝕜 E]

section NoCommonRecessionDirection

variable {I : Sort v}
variable (f : I → E → WithBotTop 𝕜)

local notation "C" => weakConvexInequalitySolutionSet f

-- Proof sketch: let `C := weakConvexInequalitySolutionSet f`. Closedness and
-- convexity of `C` come from the Chapter 21 owner theorems applied to the closed proper convex
-- constraint family. Any common recession direction of all `f i` preserves all weak constraints,
-- hence is a recession direction of `C`; Theorem 6.27.3 then yields a minimizer of `f₀` on `C`.
/-- Corollary 6.27.5 (1): if the weak system `f i x ≤ 0` is consistent and no recession direction
is common to the objective `f₀` and to every constraint function `f i`, then `f₀` attains its
infimum on the weak feasible set cut out by those constraints. -/
theorem exists_mem_isMinOn_of_no_common_recession_direction_for_convex_inequalities
    (f₀ : E → WithBotTop 𝕜)
    (hf₀_convex : f₀.IsConvex 𝕜) (hf₀_proper : f₀.IsProper)
    (hf₀_closed : LowerSemicontinuous f₀)
    (hf_convex : ∀ i : I, (f i).IsConvex 𝕜)
    (hf_proper : ∀ i : I, (f i).IsProper)
    (hf_closed : ∀ i : I, LowerSemicontinuous (f i))
    (hconsistent : Set.Nonempty C)
    (hno_common :
      ¬ ∃ y : E, f₀.RecedesInDirection 𝕜 y ∧ ∀ i : I, (f i).RecedesInDirection 𝕜 y) :
    ∃ x ∈ C, IsMinOn f₀ C x := sorry

end NoCommonRecessionDirection

section FinitePolyhedralRefinement

variable {I : Type v}
variable (f : I → E → WithBotTop 𝕜)

local notation "C" => weakConvexInequalitySolutionSet f

-- Proof sketch: keep the finite polyhedral subsystem indexed by a finite subset `I₀ : Set I` as
-- the explicit feasible set, and absorb the remaining constraints into a modified objective by
-- adding the indicator of their common feasible region. The polyhedral hypotheses make the
-- retained subsystem fit the finite polyhedral attainment route, while the lineality assumption
-- turns every common recession direction of the reduced problem into a direction harmless for the
-- modified objective. The resulting minimizer is then feasible for the full family.
/-- Corollary 6.27.5 (2): more generally, if a finite subset `I₀` is polyhedral and every
recession direction common to `f₀` and all constraints lies in `lin(f₀)` and in `lin(f i)` for
every nonpolyhedral constraint `i` (i.e. `¬ (f i).HasPolyhedralEpigraph`), then `f₀` still
attains its infimum on the weak feasible set. -/
theorem exists_mem_isMinOn_of_finite_polyhedral_subfamily_and_constant_common_recession_directions
    (f₀ : E → WithBotTop 𝕜) (I₀ : Set I) (hI₀_finite : I₀.Finite)
    (hf₀_convex : f₀.IsConvex 𝕜) (hf₀_proper : f₀.IsProper)
    (hf₀_closed : LowerSemicontinuous f₀)
    (hf_convex : ∀ i : I, (f i).IsConvex 𝕜)
    (hf_proper : ∀ i : I, (f i).IsProper)
    (hf_closed : ∀ i : I, LowerSemicontinuous (f i))
    (hpoly : ∀ i : I, i ∈ I₀ → (f i).HasPolyhedralEpigraph)
    (hconsistent : Set.Nonempty C)
    (hlineal :
      ∀ ⦃y : E⦄, f₀.RecedesInDirection 𝕜 y → (∀ i : I, (f i).RecedesInDirection 𝕜 y) →
        y ∈ lin(f₀) ∧ ∀ i : I, ¬ (f i).HasPolyhedralEpigraph → y ∈ lin(f i)) :
    ∃ x ∈ C, IsMinOn f₀ C x := sorry

end FinitePolyhedralRefinement
