import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap02.Text_7_0_4
import ConvexAnalysis_Rockafellar_1970.Chap04.Text_19_0_8
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_27_3
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_29_10
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_29_19
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_30_11
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_30_14
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_30_16
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_30_17
import ConvexAnalysis_Rockafellar_1970.Chap07.Defn_34_2

noncomputable section

open scoped Rockafellar

universe u v w

namespace Bifunction

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 6.30.17 lists ten sufficient conditions guaranteeing normality of both
  the primal convex program `(P)` attached to a closed convex bifunction `F` and its adjoint dual
  program `(P*)`.
- `core/canonical`: the Chapter 6 owner layer is already
  `perturbationFunction`, `upperPerturbationFunction`, `(·)⋆`, `(·)₀`,
  `IsStronglyConsistent`, `IsConsistent`, `IsKuhnTuckerVector`,
  `IsDualKuhnTuckerVector`, `minimumSet`, `Function.HasPolyhedralEpigraph`, and
  `IsClosedConvex`.
- `bridge/view`: the source normality statements are kept directly as the two closure identities
  `p 0 = cl(p) 0` and `q 0 = (-cl(-q)) 0`, rather than via a larger wrapper around the ten source
  hypotheses. The dual objective surface is expressed canonically by the Chapter 6 owner
  `((adjoint XStar UStar F)₀)`.

Primary mathematical domain:
- convex duality for closed convex bifunctions on paired scalar-parametric spaces.

Domain-style sampling used here:
- `IsStronglyConsistent` from Definition 6.29.10;
- `IsKuhnTuckerVector` from Definition 6.29.19;
- `upperPerturbationFunction` from Definition 6.30.11;
- `adjoint` / notation `(·)⋆` from Definition 6.30.14;
- `((adjoint XStar UStar F)₀)` from Definition 6.30.16;

Best owner abstraction:
- theorem-level sufficient conditions stated directly on those Chapter 6 owners, not a separate
  public predicate packaging the ten alternatives, and with closed-convexity stated on the
  canonical owner `IsClosedConvex`.

Primitive data vs derived API:
- primitive input: a bifunction `F : U → X → WithBotTop 𝕜` together with the
  closed-convex owner `IsClosedConvex F` when the clause hypothesis itself does not already force
  it;
- primitive/source-side sufficient conditions: the ten textbook clauses, each stated directly on
  the canonical owners above;
- derived conclusion: primal and dual normality, expressed by the two closure equalities at `0`.

Layer target: `source-facing`, split into atomic theorem surfaces for the ten source clauses.
-/

section

variable {𝕜 : Type w} {U : Type u} {X : Type v} {UStar : Type u} {XStar : Type v}
variable [Ring 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜]
variable [AddCommGroup U] [Module 𝕜 U] [TopologicalSpace U]
variable [Neg UStar]
variable [AddCommGroup X] [Module 𝕜 X] [TopologicalSpace X]
variable [AddCommGroup XStar] [Module 𝕜 XStar] [TopologicalSpace XStar]
variable [HasPairing U UStar 𝕜] [HasPairing X XStar 𝕜]

variable {F : U → X → WithBotTop 𝕜}

local notation "F⋆" => ((adjoint XStar UStar F) : XStar → UStar → WithBotTop 𝕜)
local notation "f₀" => (F)₀
local notation "d₀" => (((F⋆)₀) : UStar → WithBotTop 𝕜)
local notation "p" => perturbationFunction F
local notation "q" => upperPerturbationFunction (F⋆)
local notation "primalSublevel(" ξ ")" => (f₀ ⁻¹' Set.Iic ξ)
local notation "dualSuperlevel(" ξ ")" => (d₀ ⁻¹' Set.Ici ξ)
local notation "dualMaximizerSet" =>
  ({uStar : UStar | IsMaxOn d₀ Set.univ uStar} : Set UStar)

/-- Theorem 6.30.17 (1): under source clause `(a)`, strong consistency of the primal program
forces normality of both the primal perturbation function and the dual upper perturbation
function at `0` for a closed convex bifunction `F`. -/
theorem primalNormal_and_dualNormal_of_isStronglyConsistent
    (hF_closedConvex : IsClosedConvex F)
    (hstrong : IsStronglyConsistent 𝕜 F) :
    p 0 = cl(p) 0 ∧ q 0 = (-cl(-q)) 0 :=
  sorry

/-- Theorem 6.30.17 (2): under source clause `(b)`, strong consistency of the adjoint dual
program forces normality of both the primal perturbation function and the dual upper perturbation
function at `0` for a closed convex bifunction `F`. -/
theorem primalNormal_and_dualNormal_of_isStronglyConsistent_adjointFunction
    (hF_closedConvex : IsClosedConvex F)
    (hstrong : IsStronglyConsistent 𝕜 (F⋆)) :
    p 0 = cl(p) 0 ∧ q 0 = (-cl(-q)) 0 :=
  sorry

/-- Theorem 6.30.17 (3): under source clause `(c)`, existence of a primal Kuhn--Tucker vector
forces normality of both the primal perturbation function and the dual upper perturbation
function at `0` for a closed convex bifunction `F`. -/
theorem primalNormal_and_dualNormal_of_exists_isKuhnTuckerVector
    (hF_closedConvex : IsClosedConvex F)
    (hKT : ∃ uStar : UStar, IsKuhnTuckerVector F uStar) :
    p 0 = cl(p) 0 ∧ q 0 = (-cl(-q)) 0 :=
  sorry

/-- Theorem 6.30.17 (4): under source clause `(d)`, existence of a dual Kuhn--Tucker vector
forces normality of both the primal perturbation function and the dual upper perturbation
function at `0`, rendered on the canonical Chapter 6 source-facing dual owner
`IsDualKuhnTuckerVector`. The ambient closed-convex hypothesis is stated on the canonical owner
`IsClosedConvex F`. -/
theorem primalNormal_and_dualNormal_of_exists_isDualKuhnTuckerVector
    (hF_closedConvex : IsClosedConvex F)
    (hdualKT : ∃ x : X, IsDualKuhnTuckerVector UStar XStar F x) :
    p 0 = cl(p) 0 ∧ q 0 = (-cl(-q)) 0 :=
  sorry

/-- Theorem 6.30.17 (5): under source clause `(e)`, a polyhedral epigraph for `uncurry F`
together with primal consistency forces normality of both the primal perturbation function and the
dual upper perturbation function at `0`. -/
theorem primalNormal_and_dualNormal_of_uncurry_hasPolyhedralEpigraph_and_isConsistent
    (hpoly : (Function.uncurry F).HasPolyhedralEpigraph)
    (hconsistent : IsConsistent F) :
    p 0 = cl(p) 0 ∧ q 0 = (-cl(-q)) 0 :=
  sorry

/-- Theorem 6.30.17 (6): under source clause `(f)`, a polyhedral epigraph for the
negative adjoint graph function together with dual consistency forces normality of both the
primal perturbation function and the dual upper perturbation function at `0`. -/
theorem
    primalNormal_and_dualNormal_of_adjoint_hasPolyhedralEpigraph_and_isConsistent
    [AddCommGroup UStar] [Module 𝕜 UStar]
    (hpoly : (-Function.uncurry (F⋆)).HasPolyhedralEpigraph)
    (hconsistent : IsConsistent (F⋆)) :
    p 0 = cl(p) 0 ∧ q 0 = (-cl(-q)) 0 :=
  sorry

variable [Bornology X] [Bornology UStar]

/-- Theorem 6.30.17 (7): under source clause `(g)`, a nonempty bounded primal sublevel set of the
zero-slice objective forces normality of both the primal perturbation function and the dual upper
perturbation function at `0` for a closed convex bifunction `F`. -/
theorem primalNormal_and_dualNormal_of_nonempty_bounded_primalSublevel
    (hF_closedConvex : IsClosedConvex F)
    (ξ : WithBotTop 𝕜)
    (hsublevel_nonempty : (primalSublevel(ξ)).Nonempty)
    (hsublevel_bounded : Bornology.IsBounded (primalSublevel(ξ))) :
    p 0 = cl(p) 0 ∧ q 0 = (-cl(-q)) 0 :=
  sorry

/-- Theorem 6.30.17 (8): under source clause `(h)`, a nonempty bounded dual superlevel set of
the dual zero-slice objective forces normality of both the primal perturbation function and the
dual upper perturbation function at `0` for a closed convex bifunction `F`. -/
theorem primalNormal_and_dualNormal_of_nonempty_bounded_dualSuperlevel
    (hF_closedConvex : IsClosedConvex F)
    (ξ : WithBotTop 𝕜)
    (hsuperlevel_nonempty : (dualSuperlevel(ξ)).Nonempty)
    (hsuperlevel_bounded : Bornology.IsBounded (dualSuperlevel(ξ))) :
    p 0 = cl(p) 0 ∧ q 0 = (-cl(-q)) 0 :=
  sorry

/-- Theorem 6.30.17 (9): under source clause `(i)`, a nonempty bounded minimum set of the primal
zero-slice objective forces normality of both the primal perturbation function and the dual upper
perturbation function at `0` for a closed convex bifunction `F`. -/
theorem primalNormal_and_dualNormal_of_nonempty_bounded_minimumSet_objective
    (hF_closedConvex : IsClosedConvex F)
    (hminimum_nonempty : Set.Nonempty (minimumSet f₀))
    (hminimum_bounded : Bornology.IsBounded (minimumSet f₀)) :
    p 0 = cl(p) 0 ∧ q 0 = (-cl(-q)) 0 :=
  sorry

/-- Theorem 6.30.17 (10): under source clause `(j)`, a nonempty bounded maximizer set of the
dual zero-slice objective forces normality of both the primal perturbation function and the dual
upper perturbation function at `0` for a closed convex bifunction `F`. -/
theorem primalNormal_and_dualNormal_of_nonempty_bounded_dualMaximizerSet
    (hF_closedConvex : IsClosedConvex F)
    (hmaximum_nonempty : Set.Nonempty dualMaximizerSet)
    (hmaximum_bounded : Bornology.IsBounded dualMaximizerSet) :
    p 0 = cl(p) 0 ∧ q 0 = (-cl(-q)) 0 :=
  sorry

/-- Any one of the ten sufficient clauses from Theorem 6.30.17 yields both primal and dual
normality at `0`. This aggregated bridge keeps the reusable disjunctive interface expected by
later Chapter 6 and Chapter 7 statements while the source-facing clauses remain split atomically
above. -/
theorem primalNormal_and_dualNormal_of_sufficientNormalityHypothesis
    [AddCommGroup UStar] [Module 𝕜 UStar]
    (hqual :
      (IsClosedConvex F ∧ IsStronglyConsistent 𝕜 F) ∨
        (IsClosedConvex F ∧ IsStronglyConsistent 𝕜 (F⋆)) ∨
        (IsClosedConvex F ∧ ∃ uStar : UStar, IsKuhnTuckerVector F uStar) ∨
        (IsClosedConvex F ∧ ∃ x : X, IsDualKuhnTuckerVector UStar XStar F x) ∨
        ((Function.uncurry F).HasPolyhedralEpigraph ∧ IsConsistent F) ∨
        ((-Function.uncurry (F⋆)).HasPolyhedralEpigraph ∧ IsConsistent (F⋆)) ∨
        (IsClosedConvex F ∧
          ∃ ξ : WithBotTop 𝕜,
            (primalSublevel(ξ)).Nonempty ∧
              Bornology.IsBounded (primalSublevel(ξ))) ∨
        (IsClosedConvex F ∧
          ∃ ξ : WithBotTop 𝕜,
            (dualSuperlevel(ξ)).Nonempty ∧
              Bornology.IsBounded (dualSuperlevel(ξ))) ∨
        (IsClosedConvex F ∧
          Set.Nonempty (minimumSet f₀) ∧
            Bornology.IsBounded (minimumSet f₀)) ∨
        (IsClosedConvex F ∧
          Set.Nonempty dualMaximizerSet ∧
            Bornology.IsBounded dualMaximizerSet)) :
    p 0 = cl(p) 0 ∧ q 0 = (-cl(-q)) 0 :=
  sorry

end

end Bifunction
