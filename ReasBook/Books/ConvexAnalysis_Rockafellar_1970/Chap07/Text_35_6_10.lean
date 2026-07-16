import ConvexAnalysis_Rockafellar_1970.Chap03.Text_13_0_2
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_4
import ConvexAnalysis_Rockafellar_1970.Chap05.Lemma_23_0_1
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_30_2
import ConvexAnalysis_Rockafellar_1970.Chap07.Defn_34_3
import ConvexAnalysis_Rockafellar_1970.Chap07.Text_35_5_1
import ConvexAnalysis_Rockafellar_1970.Chap07.Text_35_5_3

noncomputable section

universe u v

open Function
open scoped Rockafellar

namespace Bifunction

section

variable {𝕜 : Type*}
variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [TopologicalSpace 𝕜]
variable [TopologicalSpace (WithTopBot 𝕜)]
variable {U : Type u} {V : Type v}
variable [AddCommGroup U] [SMul 𝕜 U]
variable {Y : Type*} [HasPairing U Y 𝕜]

variable {K : U → V → WithTopBot 𝕜} {u : U} {v : V}

/-!
Source/core/bridge triage:

- `source-facing`: Text 35.6.10 identifies the first partial directional derivative with the
  infimum of pairings against the first partial subdifferential of the first-variable slice.
- `core/canonical`: the primary owner layer is the first-variable slice
  `Function.directionalDerivativeAt (fun u'' ↦ K u'' v) u u'`, together with the Chapter 35
  first-partial owner `Bifunction.subdifferential1At`, used here on the pairing-level surface
  `∂₁[Y]K(u, v)`.
- `bridge/view`: the uncurried source notation `K'(u, v; u', 0)` is retained below through
  `Function.directionalDerivativeAt_uncurry_first_eq`.

Primary mathematical domain:
- convex analysis of first-slice concavity and first partial subdifferentials.

Domain-style sampling used here:
- `Function.directionalDerivativeAt` and
  `Function.directionalDerivativeAt_eq_supportFunction_subdifferentialAt_of_mem_riDom` from
  Chapter 23;
- `Function.IsConcave` from `Chap06.Definition_6_30_2`, which is the chapter's canonical
  whole-space owner for the fixed first slice `fun u'' ↦ K u'' v`;
- `Bifunction.subdifferential1At` and the notation `∂₁[...]K(u, v)` from `Chap07.Text_35_5_1`;
- `Function.directionalDerivativeAt_uncurry_first_eq` from `Chap07.Text_35_5_3`;
- `neg_supportFunction_neg_eq_sInf_image_pairing` from `Chap03.Text_13_0_2`, which rewrites the
  Chapter 23 support-function identity into the textbook infimum formula.

Primitive data vs derived API:
- primitive source data: whole-space concavity of the fixed first-variable slice
  `(fun u'' ↦ K u'' v).IsConcave 𝕜`, a finite first-slice base point encoded by
  `u ∈ dom(fun u'' ↦ -K u'' v)` together with `K u v ≠ ⊤`, first-partial
  subdifferential nonemptiness, and a first-direction vector `u'`;
- primitive owner data already exist upstream as `Function.directionalDerivativeAt` and the
  first-partial owner `Bifunction.subdifferential1At` on the pairing-level surface
  `∂₁[Y]K(u, v)`;
- derived API here: the first-direction infimum formula on that owner notation, together with the
  uncurried-direction bridge corollary.

Layer target: `source-facing` on the intrinsic pairing-level owner.

Demotion note:
- Inner-product vector bridges (`subdifferential1AtVec`) are intentionally not surfaced in this
  source item; they belong to downstream bridge files.
-/

-- Proof sketch: transport first-partial nonemptiness through the Chapter 6 sign bridge to a
-- nonempty Chapter 23 subdifferential of the convex negated slice `fun u'' ↦ -K u'' v`. The
-- finite-point hypotheses `u ∈ dom(fun u'' ↦ -K u'' v)` and `K u v ≠ ⊤` give both side
-- finiteness conditions for `-K(·, v)` at `u`, which are needed to recover properness from that
-- nonempty subdifferential. Apply the one-variable
-- support-function formula to `-K(·, v)`, then rewrite the resulting support term by the Chapter
-- 13 pairing/infimum bridge and the first-partial owner `∂₁[Y]K(u, v)`.
/-- Text 35.6.10, owner form: if the first-variable slice `u'' ↦ K u'' v` is concave on the whole
space, `u` is a finite point of the negated slice `-K(·, v)` in the sense that
`u ∈ dom(fun u'' ↦ -K u'' v)` and `K u v ≠ ⊤`, and the first partial
subdifferential `∂₁[Y]K(u, v)` is nonempty, then the first directional derivative
equals the infimum of pairings against that first partial subdifferential. -/
theorem directionalDerivativeAt_firstSlice_eq_iInf_subdifferential1At
    (hK_concave : (K · v).IsConcave 𝕜)
    (hu : u ∈ dom(fun u'' ↦ -K u'' v))
    (hu_top : K u v ≠ ⊤)
    (hsub : (∂₁[Y]K(u, v)).Nonempty)
    (u' : U) :
    directionalDerivativeAt (K · v) u u' =
      ⨅ uStar : ∂₁[Y]K(u, v),
        ((⟪u', (uStar : Y)⟫ₚ : 𝕜) : WithTopBot 𝕜) := sorry

section

variable [AddCommMonoid V] [SMulZeroClass 𝕜 V]

-- Proof sketch: rewrite the source notation `K'(u, v; u', 0)` as the directional derivative of
-- the first slice by `Function.directionalDerivativeAt_uncurry_first_eq`, then apply the
-- canonical first-slice theorem above.
/-- Text 35.6.10, uncurried source-facing form: under the same whole-space first-slice concavity,
the finite-point hypotheses `u ∈ dom(fun u'' ↦ -K u'' v)` and `K u v ≠ ⊤`, and the
first-partial-subdifferential hypothesis, the first partial directional derivative
`K'(u, v; u', 0)` equals the infimum of pairings over `∂₁[Y]K(u, v)`. -/
theorem directionalDerivativeAt_uncurry_first_eq_iInf_subdifferential1At
    (hK_concave : (K · v).IsConcave 𝕜)
    (hu : u ∈ dom(fun u'' ↦ -K u'' v))
    (hu_top : K u v ≠ ⊤)
    (hsub : (∂₁[Y]K(u, v)).Nonempty)
    (u' : U) :
    directionalDerivativeAt (uncurry K) (u, v) (u', 0) =
      ⨅ uStar : ∂₁[Y]K(u, v),
        ((⟪u', (uStar : Y)⟫ₚ : 𝕜) : WithTopBot 𝕜) := by
  rw [directionalDerivativeAt_uncurry_first_eq K u v u']
  exact directionalDerivativeAt_firstSlice_eq_iInf_subdifferential1At
    hK_concave hu hu_top hsub u'

end

end

section

variable {𝕜 : Type*}
variable [NormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜] [OrderTopology 𝕜]
variable [TopologicalSpace (WithTopBot 𝕜)] [OrderTopology (WithTopBot 𝕜)]
variable {U : Type u} {V : Type v}
variable [NormedAddCommGroup U] [NormedSpace 𝕜 U]
variable {Y : Type*} [HasPairing U Y 𝕜]

variable {K : U → V → WithTopBot 𝕜} {u : U} {v : V}

-- Proof sketch: apply Theorem 23.4 directly to the proper convex negated slice `-K(·, v)` at the
-- `riDom` base point `u`; the additional guard `K u v ≠ ⊤` keeps the base value of `-K(·, v)`
-- away from `⊥`, so the slice is finite there. Then rewrite the support term through the
-- sign-change bridge and Chapter 13 pairing/infimum formula exactly as in the intrinsic owner
-- theorem above.
/-- `riDom` companion to Text 35.6.10 at the pairing owner layer: the Chapter 23
relative-interior qualification on `-K(·, v)`, together with the lower-side finiteness guard
`K u v ≠ ⊤`, yields the same first-slice infimum formula over `∂₁[Y]K(u, v)`. -/
theorem directionalDerivativeAt_firstSlice_eq_iInf_subdifferential1At_of_mem_riDom_neg
    (hK_concave : (K · v).IsConcave 𝕜)
    (hu : u ∈ riDom[𝕜](fun u'' ↦ -K u'' v))
    (hu_top : K u v ≠ ⊤)
    (u' : U) :
    directionalDerivativeAt (K · v) u u' =
      ⨅ uStar : ∂₁[Y]K(u, v),
        ((⟪u', (uStar : Y)⟫ₚ : 𝕜) : WithTopBot 𝕜) := sorry

end

end Bifunction
