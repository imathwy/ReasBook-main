import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_4
import ConvexAnalysis_Rockafellar_1970.Chap01.Defintion_4_8_2
import ConvexAnalysis_Rockafellar_1970.Chap02.Text_7_0_4
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_30_2
import ConvexAnalysis_Rockafellar_1970.Chap07.Text_35_5_1
import ConvexAnalysis_Rockafellar_1970.Chap07.Text_35_5_3

noncomputable section

open Function
open scoped Rockafellar

universe u v

namespace Bifunction

section

variable {𝕜 : Type*}
variable [NormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [TopologicalSpace 𝕜] [TopologicalSpace (WithTopBot 𝕜)]
variable {U : Type u} {V : Type v}
variable [AddCommGroup U] [SMul 𝕜 U]

/-!
Source/core/bridge triage:

- `source-facing`: Text 35.6.6 fixes a first-variable slice `K · v` and studies the
  reflected first partial directional-derivative profile `u' ↦ -K'(u, v; -u', 0)`.
- `core/canonical`: the owner abstractions already present upstream are
  `Function.directionalDerivativeAt` for one-variable slices and `Bifunction.subdifferential1At`
  for the first partial subdifferential.
- `bridge/view`: the displayed source profile is exactly the reflected slice owner
  `u' ↦ -directionalDerivativeAt (fun u'' ↦ K u'' v) u (-u')`; the uncurried bridge
  `Function.directionalDerivativeAt_uncurry_first_eq` remains upstream and no second public owner
  is introduced here.

Domain-style sampling used here:
- `Function.IsConcave` from `Chap06.Definition_6_30_2` as the canonical whole-space owner for the
  fixed first slice `K · v`, definitionally replacing `ConcaveOn 𝕜 Set.univ`;
- `Function.directionalDerivativeAt` from `Chap05.Lemma_23_0_1`;
- `Function.isConvex_directionalDerivativeAt_of_finite_point` from `Chap05.Theorem_23_1`;
- `Function.directionalDerivativeAt_uncurry_first_eq` from `Chap07.Text_35_5_3`;
- `Bifunction.subdifferential1At` from `Chap07.Text_35_5_1`.

Primitive data vs derived API:
- primitive inputs: a fixed slice `K · v`, its canonical whole-space concavity owner,
  and finiteness of `K u v`;
- derived API: convexity of the reflected first-direction profile below.

Layer target: `source-facing`, stated directly on the canonical slice directional-derivative
owner.

Ambient-assumption minimization:
- the first-variable directional-derivative owner and its finite-point convexity theorem from
  Chapter 23 live on the scalar-action layer of `U`, while the reflected source direction `-u'`
  requires additive inverses on `U`;
- the second variable is a fixed parameter here, so no algebraic structure on `V` enters the
  public API.
-/

-- Proof sketch: apply the Chapter 23 convexity theorem to the convex function
-- `fun u'' ↦ -K u'' v` at the finite point `u`, then read the resulting direction profile in the
-- reflected source form `u' ↦ -K'(u, v; -u', 0)`.
/-- Text 35.6.6 (1): if the first-variable slice `K · v` is concave and `u` belongs to
its effective domain with finite value, then the reflected first partial directional-derivative
profile `u' ↦ -K'(u, v; -u', 0)`, rendered here as
`u' ↦ -directionalDerivativeAt (K · v) u (-u')`, is convex. -/
theorem isConvex_neg_directionalDerivativeAt_first
    {K : U → V → WithTopBot 𝕜} {u : U} {v : V}
    (hK_concave : (K · v).IsConcave 𝕜)
    (huv : u ∈ dom((K · v))) (huv_bot : K u v ≠ ⊥) :
    (fun u' : U ↦ -directionalDerivativeAt (K · v) u (-u')).IsConvex 𝕜 := sorry

end

section

variable {𝕜 : Type*}
variable [NormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [TopologicalSpace 𝕜] [TopologicalSpace (WithTopBot 𝕜)]
variable {U : Type u} {V : Type v}
variable [TopologicalSpace U] [AddCommGroup U] [SMul 𝕜 U]

/-!
Source/core/bridge triage:

- `source-facing`: Text 35.6.6 also identifies the lower-semicontinuous hull of the same
  reflected first partial directional-derivative profile with the support function of the first
  partial subdifferential.
- `core/canonical`: the owner abstractions are the lower-semicontinuous hull `cl(·)`, the support
  function `δᵛ(· | ·)`, the slice directional derivative `Function.directionalDerivativeAt`, and
  the canonical first-partial owner `Bifunction.subdifferential1At` on the pairing-level surface
  `∂₁[Y]K(u, v)`.
- `bridge/view`: the source notation `-K'(u, v; -u', 0)` is kept on the theorem surface only
  through the reflected slice owner, while the first partial subdifferential is surfaced on the
  intrinsic pairing owner layer as `∂₁[Y]K(u, v)`.

Domain-style sampling used here:
- `Bifunction.subdifferential1At` from `Chap07.Text_35_5_1`;
- `Function.IsConcave` from `Chap06.Definition_6_30_2` as the canonical whole-space owner for the
  fixed first slice `K · v`;
- `Function.directionalDerivativeAt` from `Chap05.Lemma_23_0_1`;
- the intrinsic dual-pairing owner `HasPairing U Y 𝕜`;
- the chapter support-function notation `δᵛ(· | ·)`;
- the chapter lower-semicontinuous-hull owner `cl(·)`.

Primitive data vs derived API:
- primitive inputs: the same fixed-slice whole-space concavity owner as in part (1), together
  with the pairing-level first partial owner `∂₁[Y]K(u, v)`;
- derived API: the lower-semicontinuous-hull/support-function identity below.

Layer target: `source-facing`.

Ambient-assumption minimization:
- this clause uses only the pairing-level first-partial owner `∂₁[Y]K(u, v)`, so it stays at the
  scalar-action/additive-group layer of `U` needed for reflected directions `-u'`;
- the second variable is again a fixed parameter, so no algebraic or topological structure on `V`
  enters the public API.
-/

-- Proof sketch: apply the Chapter 23 support-function description of the lower-semicontinuous
-- hull of directional derivatives to the convex function `fun u'' ↦ -K u'' v` at `u`, then
-- rewrite the resulting subdifferential through the first partial owner `∂₁[Y]K(u, v)`
-- and express the profile in the reflected source form.
/-- Text 35.6.6 (2): under the same concavity and finiteness hypotheses, the lower-semicontinuous
closure of the reflected first partial directional-derivative profile is the support function of
the first partial subdifferential `∂₁[Y]K(u, v)`. -/
theorem
    lowerSemicontinuousHull_neg_directionalDerivativeAt_first_eq_supportFunction_subdifferential1At
    {Y : Type*} [HasPairing U Y 𝕜]
    {K : U → V → WithTopBot 𝕜} {u : U} {v : V}
    (hK_concave : (K · v).IsConcave 𝕜)
    (huv : u ∈ dom((K · v))) (huv_bot : K u v ≠ ⊥) :
    cl(fun u' : U ↦ -directionalDerivativeAt (K · v) u (-u')) =
      (δᵛ(· | ∂₁[Y]K(u, v))) := sorry

end

section

variable {𝕜 : Type*}
variable [NormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [TopologicalSpace 𝕜] [TopologicalSpace (WithTopBot 𝕜)]
variable {U : Type u} {V : Type v}
variable [SeminormedAddCommGroup U] [NormedSpace 𝕜 U]

/-- Strong-dual specialization of Text 35.6.6 (2): on the canonical dual bridge, the same
lower-semicontinuous-hull identity is written with plain notation `∂₁ K(u, v)`. -/
theorem
    lscHull_neg_directionalDerivativeAt_first_eq_supportFunction_subdifferential1At_dual
    {K : U → V → WithTopBot 𝕜} {u : U} {v : V}
    (hK_concave : (K · v).IsConcave 𝕜)
    (huv : u ∈ dom((K · v))) (huv_bot : K u v ≠ ⊥) :
    cl(fun u' : U ↦ -directionalDerivativeAt (K · v) u (-u')) =
      (δᵛ(· | ∂₁ K(u, v))) := sorry

end

end Bifunction
