import Mathlib.Tactic.Recall
import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_5_7
import ConvexAnalysis_Rockafellar_1970.Chap03.Defn_12_2
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_30_1
import ConvexAnalysis_Rockafellar_1970.Chap06.Theorem_6_30_2
import ConvexAnalysis_Rockafellar_1970.Chap06.Theorem_6_30_3
import ConvexAnalysis_Rockafellar_1970.Chap06.Theorem_6_30_4

noncomputable section

universe u v w

open scoped Rockafellar

/-!
Source/core/bridge triage for this item.

- `source-facing`: Definition 33.0.27 recalls three notions used in the saddle-function chapter:
  Fenchel conjugate, concave conjugate, and the closed-concave fixed-point condition
  `ψ = ψ_{**}`.
- `core/canonical`: the first two owners already exist in the project as
  `convexConjugate` (with notation `f⋆`), `concaveConjugate`, and, on the Chapter 6 closedness
  layer, `concaveClosure`, `UpperSemicontinuous`, and the hypograph owner `hypo`.
- `bridge/view`: clause (3) is kept source-facing as the primitive biconjugate fixed-point
  predicate; it first bridges on the linear-pairing/module layer to the canonical owner
  `g.IsConcave 𝕜`, and on the stronger finite-dimensional scalar-parametric self-pairing layer it
  is then bridged, under the explicit owner hypothesis `g.IsConcave 𝕜`, to the Chapter 6 owners
  `concaveClosure g = g`, `UpperSemicontinuous g`, and `IsClosed (hypo g)`.

Primary mathematical domain:
- convex/concave conjugacy and closedness of extended-real-valued concave functions.

Domain-style sampling used here:
- `convexConjugate`;
- `convexConjugate_eq_iSup_pairing_sub`;
- `concaveConjugate`;
- `concaveConjugate_eq_iInf_pairing_sub`.
- `concaveConjugate_eq_neg_convexConjugate_neg`;
- `Function.isConvex_convexConjugate`;
- `Function.IsConcave.biconjugate_eq_concaveClosure`;
- `Function.IsConcave.convex_upperLevelSet`;
- `concaveClosure_eq_self_iff_upperSemicontinuous`.

Abstraction checks applied:
- no concrete Euclidean model is baked into the owner surfaces;
- no extra scalar structure is introduced (only the primitive pairing/infimum/subtraction data);
- no inner-product-specific owner is used where pairing data suffice;
- no extra notation/macro layer is introduced;
- no parallel `concaveBiconjugate` API is introduced when the canonical composition already exists;
- the source-facing owner for clause (3) is kept primitive, with a first bridge to
  `Function.IsConcave` on the linear-pairing layer and the stronger Chapter 6 closure owners
  exposed only as thin bridge theorems under their native assumptions.
-/

/- Source clause 1 (Fenchel conjugate) is already the canonical owner `convexConjugate`. -/
recall convexConjugate
recall convexConjugate_eq_iSup_pairing_sub

/- Source clause 2 (concave conjugate) is already the canonical owner `concaveConjugate`. -/
recall concaveConjugate
recall concaveConjugate_eq_iInf_pairing_sub

namespace Function

section ClosedConcave

variable {E : Type u} {EStar : Type v} {L : Type w}
variable [InfSet L] [Sub L]

/-- Definition33.0.27: a concave function is closed concave when it equals its concave
biconjugate `ψ = ψ_{**}`. On the stronger Chapter 6 closedness layer, the bridge theorems below
identify this, under explicit concavity, with `concaveClosure g = g`,
`UpperSemicontinuous g`, and closedness of the hypograph `hypo g`. -/
def IsClosedConcave [HasPairing E EStar L] [HasPairing EStar E L] (g : E → L) : Prop :=
  ((g∗ : EStar → L)∗ : E → L) = g

namespace IsClosedConcave

variable {g : E → L}
variable [HasPairing E EStar L] [HasPairing EStar E L]

-- Proof sketch: unfold `Function.IsClosedConcave`; the hypothesis is exactly the concave
-- biconjugate fixed-point equation.
/-- A closed-concave function agrees with its concave biconjugate. -/
theorem biconjugate_eq (hg : IsClosedConcave g) :
    ((g∗ : EStar → L)∗ : E → L) = g :=
  show ((g∗ : EStar → L)∗ : E → L) = g from hg

end IsClosedConcave

namespace IsClosedConcave

variable {𝕜 : Type*} [CommRing 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [IsOrderedAddMonoid 𝕜]
variable {E : Type u} {EStar : Type v}
variable [AddCommGroup E] [Module 𝕜 E]
variable [AddCommMonoid EStar] [Module 𝕜 EStar]
variable [HasLinearPairing E EStar 𝕜] [HasLinearPairing EStar E 𝕜]
variable {g : E → WithTopBot 𝕜}

-- Proof sketch: rewrite the concave biconjugate of `g` using the sign-dual owner theorem
-- `concaveConjugate_eq_neg_convexConjugate_neg_apply`. This identifies `-g` with the convex
-- conjugate of `-(g∗)` precomposed by the negation linear map, hence convexity follows from the
-- canonical owner theorem `Function.isConvex_convexConjugate`.
/-- A function fixed by its concave biconjugate is concave. This lives on the linear-pairing
module layer; the stronger topological Chapter 6 consequences are derived later only where needed.
-/
theorem concave (h : IsClosedConcave g) :
    g.IsConcave 𝕜 := by
  change (-g).IsConvex 𝕜
  let gStar : EStar → WithTopBot 𝕜 := g∗
  have hconv : ((-gStar)⋆ : E → WithTopBot 𝕜).IsConvex 𝕜 :=
    Function.isConvex_convexConjugate (-gStar)
  have hneg :
      -g = (-gStar)⋆ ∘ (-LinearMap.id : E →ₗ[𝕜] E) := by
    ext x
    have hx : (gStar∗ : E → WithTopBot 𝕜) x = g x := congrFun h x
    have hx' := congrArg Neg.neg hx
    rw [concaveConjugate_eq_neg_convexConjugate_neg_apply gStar x] at hx'
    simpa [Function.comp, gStar] using hx'.symm
  simpa [hneg, Function.comp] using hconv.comp_linearMap (-LinearMap.id : E →ₗ[𝕜] E)

end IsClosedConcave

end ClosedConcave

section ClosedConcaveWithTopBot

variable {𝕜 : Type*}
variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜] [TopologicalSpace (WithTopBot 𝕜)]
variable {E : Type u}
variable [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E]
variable [FiniteDimensional 𝕜 E] [HasLinearPairing E E 𝕜] [HasContinuousPairing E E 𝕜]

local instance : HasPairing E E 𝕜 := instHasPairingOfHasLinearPairing
local notation:max g "∗∗" => ((g∗ : E → WithTopBot 𝕜)∗ : E → WithTopBot 𝕜)

namespace IsConcave

variable {g : E → WithTopBot 𝕜}

-- Proof sketch: for a concave `WithTopBot 𝕜`-valued function on the Chapter 6 self-pairing layer,
-- Theorem 6.30.3 identifies the concave biconjugate with `concaveClosure g`.
/-- On the canonical Chapter 6 `WithTopBot 𝕜` layer, a concave function is closed concave exactly
when
its concave closure fixes it. -/
@[simp] theorem isClosedConcave_iff_concaveClosure_eq_self
    (hg : g.IsConcave 𝕜) :
    IsClosedConcave g ↔ concaveClosure g = g := by
  constructor
  · intro h
    calc
      concaveClosure g = g∗∗ :=
        hg.biconjugate_eq_concaveClosure.symm
      _ = g := IsClosedConcave.biconjugate_eq h
  · intro h
    calc
      g∗∗ = concaveClosure g :=
        hg.biconjugate_eq_concaveClosure
      _ = g := h

-- Proof sketch: combine the previous bridge with Theorem 6.30.2, which identifies the Chapter 6
-- fixed-point equation `concaveClosure g = g` with upper semicontinuity.
/-- On the canonical Chapter 6 `WithTopBot 𝕜` layer, a concave function is closed concave exactly
when
it is upper semicontinuous. -/
@[simp] theorem isClosedConcave_iff_upperSemicontinuous
    [OrderTopology 𝕜]
    [NoMinOrder 𝕜] [NoMaxOrder 𝕜] [NoBotOrder 𝕜] [DenselyOrdered 𝕜] [ContinuousAdd 𝕜]
    (hg : g.IsConcave 𝕜) :
    IsClosedConcave g ↔ UpperSemicontinuous g := by
  rw [hg.isClosedConcave_iff_concaveClosure_eq_self]
  exact concaveClosure_eq_self_iff_upperSemicontinuous g

-- Proof sketch: combine the upper-semicontinuity bridge above with mathlib's canonical
-- hypograph characterization of upper semicontinuity and rewrite the set as `hypo g`.
/-- On the canonical Chapter 6 `WithTopBot 𝕜` layer, a concave function is closed concave exactly
when
its hypograph is closed. -/
@[simp] theorem isClosedConcave_iff_isClosed_hypograph
    [OrderTopology 𝕜]
    [NoMinOrder 𝕜] [NoMaxOrder 𝕜] [NoBotOrder 𝕜] [DenselyOrdered 𝕜] [ContinuousAdd 𝕜]
    [ClosedIicTopology (WithTopBot 𝕜)]
    (hg : g.IsConcave 𝕜) :
    IsClosedConcave g ↔ IsClosed (hypo g) := by
  rw [hg.isClosedConcave_iff_upperSemicontinuous]
  simpa [hypo_univ_eq_setOf_le] using
    (upperSemicontinuous_iff_IsClosed_hypograph :
      UpperSemicontinuous g ↔ IsClosed {p : E × WithTopBot 𝕜 | p.2 ≤ g p.1})

end IsConcave

namespace IsClosedConcave

variable {g : E → WithTopBot 𝕜}

/-- A closed-concave `WithTopBot 𝕜`-valued function is fixed by the Chapter 6 concave closure. -/
theorem concaveClosure_eq_self (hclosed : IsClosedConcave g) :
    concaveClosure g = g :=
  hclosed.concave.isClosedConcave_iff_concaveClosure_eq_self.1 hclosed

/-- A closed-concave `WithTopBot 𝕜`-valued function is upper semicontinuous. -/
theorem upperSemicontinuous
    [OrderTopology 𝕜]
    [NoMinOrder 𝕜] [NoMaxOrder 𝕜] [NoBotOrder 𝕜] [DenselyOrdered 𝕜] [ContinuousAdd 𝕜]
    (hclosed : IsClosedConcave g) :
    UpperSemicontinuous g :=
  hclosed.concave.isClosedConcave_iff_upperSemicontinuous.1 hclosed

/-- The hypograph of a closed-concave `WithTopBot 𝕜`-valued function is closed. -/
theorem isClosed_hypograph
    [OrderTopology 𝕜]
    [NoMinOrder 𝕜] [NoMaxOrder 𝕜] [NoBotOrder 𝕜] [DenselyOrdered 𝕜] [ContinuousAdd 𝕜]
    [ClosedIicTopology (WithTopBot 𝕜)]
    (hclosed : IsClosedConcave g) :
    IsClosed (hypo g) :=
  hclosed.concave.isClosedConcave_iff_isClosed_hypograph.1 hclosed

end IsClosedConcave

end ClosedConcaveWithTopBot

end Function
