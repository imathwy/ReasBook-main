import ConvexAnalysis_Rockafellar_1970.Chap05.Definition_26_2_1
import ConvexAnalysis_Rockafellar_1970.Chap05.Lemma_26_1
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_12_3_6

noncomputable section

open scoped Rockafellar SetRel

universe u v

section

variable {𝕜 : Type v} [Semiring 𝕜] [TopologicalSpace 𝕜] [PartialOrder 𝕜]
variable {E : Type u} [AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E]
variable [TopologicalSpace (WithTopBot 𝕜)]
variable {Y : Type (max u v)} [HasPairing E Y 𝕜]
local notation "IsClosedProperConvex" => Function.IsClosedProperConvex (𝕜 := 𝕜)
local notation "IsEssentiallyStrictlyConvex[" Y "]" =>
  Function.IsEssentiallyStrictlyConvex (Y := Y)

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 26.4 identifies essential strict convexity of a closed proper convex
  function with the inverse-single-valued clause for its subdifferential mapping.
- `core/canonical`: the owner abstractions already present in the chapter are
  `Function.IsEssentiallyStrictlyConvex`, the intrinsic graph owner
  `_root_.subdifferentialGraph (Y := Y) f : SetRel E Y`, the Chapter 26
  inverse-single-valued owner `(_root_.subdifferentialGraph (Y := Y) f).LeftUnique`, and the
  chapter's one-to-one owner `(_root_.subdifferentialGraph (Y := Y) f).BiUnique` from
  `Definition_26_0_3`.
- `bridge/view`: the Fréchet-Riesz transport `Function.subdifferentialGraph f` gives the
  vector-valued graph view of the same intrinsic owner on inner-product spaces.

Domain-style sampling used here:
- `Function.IsEssentiallyStrictlyConvex` from `Definition_26_2_1`;
- `_root_.subdifferentialGraph` from `Definition_5_24_3`;
- `SetRel.injOn_snd_iff` from `Lemma_26_1`, the chapter's canonical second-projection bridge for
  inverse single-valuedness;
- `(_root_.subdifferentialGraph f).dom` in `Definition_26_2_1`, which already makes the
  essential-strict-convexity owner intrinsic rather than Fréchet-Riesz-dependent;
- `Function.subdifferentialGraph` from `Definition_5_24_3`.

Primitive data vs derived API:
- primitive source data: a closed proper convex function `f` and its canonical graph relation
  `_root_.subdifferentialGraph f`;
- primitive owner theorem surface: inverse-single-valuedness of that intrinsic graph relation and
  the class `f.IsEssentiallyStrictlyConvex`;
- derived API: the vector-valued Fréchet-Riesz restatement.

Layer target:
- `leftUnique_subdifferentialGraph_iff_isEssentiallyStrictlyConvex`: `source-facing`, stated
  directly on the intrinsic pairing-codomain graph owner of the subdifferential;
- `rightUnique_inv_subdifferentialGraph_iff_isEssentiallyStrictlyConvex`: `bridge/view`,
  the source inverse-wording restated from the canonical `LeftUnique` owner;
- `injOn_snd_subdifferentialGraph_iff_isEssentiallyStrictlyConvex`: `bridge/view`, the graph
  projection reformulation of the source inverse-single-valuedness clause;
- the inner-product-space theorems below: `bridge/view`, because they transport the source
  sentence through Fréchet-Riesz identification.
-/

/-- Theorem 26.4, canonical graph-owner form: for a closed proper convex function, the intrinsic
subdifferential graph is left-unique exactly when the function is essentially strictly convex.
This is the Chapter 26 inverse-single-valued owner clause, stated directly on
`(_root_.subdifferentialGraph (Y := Y) f).LeftUnique`.

Abstraction note: this intrinsic owner theorem is stated on the chapter's validated source layer
(`WithTopBot 𝕜` codomain with explicit pairing codomain `Y`); the vector-valued inner-product
form appears below only as a Fréchet-Riesz bridge. -/
theorem leftUnique_subdifferentialGraph_iff_isEssentiallyStrictlyConvex
    {f : E → WithTopBot 𝕜} (hf : IsClosedProperConvex f) :
    (gph∂[Y](f)).LeftUnique ↔
      IsEssentiallyStrictlyConvex[Y] f := by
  sorry

/-- Inverse-wording bridge companion to Theorem 26.4: inverse right-uniqueness of the intrinsic
subdifferential graph is exactly the canonical `LeftUnique` owner. -/
theorem rightUnique_inv_subdifferentialGraph_iff_isEssentiallyStrictlyConvex
    {f : E → WithTopBot 𝕜} (hf : IsClosedProperConvex f) :
    (gph∂[Y](f))⁻¹.RightUnique ↔
      IsEssentiallyStrictlyConvex[Y] f := by
  change Relator.RightUnique (· ~[(gph∂[Y](f))⁻¹] ·) ↔ IsEssentiallyStrictlyConvex[Y] f
  exact (SetRel.rightUnique_inv_iff_leftUnique (ρ := gph∂[Y](f))).trans
    (leftUnique_subdifferentialGraph_iff_isEssentiallyStrictlyConvex hf)

/-- Projection-criterion companion to Theorem 26.4: inverse single-valuedness of the intrinsic
subdifferential graph is equivalently injectivity of `Prod.snd` on that graph. -/
theorem injOn_snd_subdifferentialGraph_iff_isEssentiallyStrictlyConvex
    {f : E → WithTopBot 𝕜} (hf : IsClosedProperConvex f) :
    Set.InjOn Prod.snd (gph∂[Y](f)) ↔
      IsEssentiallyStrictlyConvex[Y] f := by
  rw [← SetRel.leftUnique_iff_injOn_snd]
  exact leftUnique_subdifferentialGraph_iff_isEssentiallyStrictlyConvex hf

end

section

variable {𝕜 : Type v} [RCLike 𝕜]
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
local notation "IsClosedProperConvex[" 𝕜 "]" => Function.IsClosedProperConvex (𝕜 := 𝕜)
local notation "IsEssentiallyStrictlyConvex[" 𝕜 "]" =>
  Function.IsEssentiallyStrictlyConvex (𝕜 := 𝕜)

private theorem injOn_snd_functionSubdifferentialGraph_iff
    (f : E → WithTopBot 𝕜) :
    Set.InjOn Prod.snd (Function.subdifferentialGraph f) ↔
      Set.InjOn Prod.snd (_root_.subdifferentialGraph f) := by
  let e := InnerProductSpace.toDual 𝕜 E
  constructor
  · intro h p hp q hq hpq
    let p' : E × E := (p.1, e.symm p.2)
    let q' : E × E := (q.1, e.symm q.2)
    have hpDual : p.2 ∈ _root_.subdifferentialAt f p.1 :=
      _root_.mem_subdifferentialGraph.mp hp
    have hqDual : q.2 ∈ _root_.subdifferentialAt f q.1 :=
      _root_.mem_subdifferentialGraph.mp hq
    have hp' : p' ∈ Function.subdifferentialGraph f := by
      rw [Function.mem_subdifferentialGraph]
      change e (e.symm p.2) ∈ _root_.subdifferentialAt f p.1
      rwa [LinearIsometryEquiv.apply_symm_apply]
    have hq' : q' ∈ Function.subdifferentialGraph f := by
      rw [Function.mem_subdifferentialGraph]
      change e (e.symm q.2) ∈ _root_.subdifferentialAt f q.1
      rwa [LinearIsometryEquiv.apply_symm_apply]
    have hpq' : Prod.snd p' = Prod.snd q' := by
      simpa [p', q'] using congrArg e.symm hpq
    have hEq' : p' = q' := h hp' hq' hpq'
    apply Prod.ext
    · simpa [p', q'] using congrArg Prod.fst hEq'
    · have hsnd : e.symm p.2 = e.symm q.2 := by
        simpa [p', q'] using congrArg Prod.snd hEq'
      exact by simpa using congrArg e hsnd
  · intro h p hp q hq hpq
    have hpVec : p.2 ∈ Function.subdifferentialAt f p.1 :=
      Function.mem_subdifferentialGraph.mp hp
    have hqVec : q.2 ∈ Function.subdifferentialAt f q.1 :=
      Function.mem_subdifferentialGraph.mp hq
    have hp' : (p.1, e p.2) ∈ _root_.subdifferentialGraph f := by
      rw [_root_.mem_subdifferentialGraph]
      change p.2 ∈ Function.subdifferentialAt f p.1
      exact hpVec
    have hq' : (q.1, e q.2) ∈ _root_.subdifferentialGraph f := by
      rw [_root_.mem_subdifferentialGraph]
      change q.2 ∈ Function.subdifferentialAt f q.1
      exact hqVec
    have hEq : (p.1, e p.2) = (q.1, e q.2) := by
      exact h hp' hq' (by simpa using congrArg e hpq)
    apply Prod.ext
    · simpa using congrArg Prod.fst hEq
    · exact e.injective (by simpa using congrArg Prod.snd hEq)

private theorem leftUnique_functionSubdifferentialGraph_iff
    (f : E → WithTopBot 𝕜) :
    (Function.subdifferentialGraph f).LeftUnique ↔
      (_root_.subdifferentialGraph f).LeftUnique := by
  rw [SetRel.leftUnique_iff_injOn_snd, SetRel.leftUnique_iff_injOn_snd]
  exact injOn_snd_functionSubdifferentialGraph_iff f

namespace Function

/-- Theorem 26.4, vector-valued owner bridge form: on a complete inner-product space, the
Fréchet-Riesz realization of the subdifferential graph is left-unique exactly when the function is
essentially strictly convex. -/
theorem leftUnique_subdifferentialGraph_iff_isEssentiallyStrictlyConvex
    {f : E → WithTopBot 𝕜} (hf : IsClosedProperConvex[𝕜] f) :
    (subdifferentialGraph f).LeftUnique ↔ IsEssentiallyStrictlyConvex[𝕜] f := by
  rw [leftUnique_functionSubdifferentialGraph_iff f]
  exact _root_.leftUnique_subdifferentialGraph_iff_isEssentiallyStrictlyConvex hf

/-- Inverse-wording companion on the Fréchet-Riesz graph owner. -/
theorem rightUnique_inv_subdifferentialGraph_iff_isEssentiallyStrictlyConvex
    {f : E → WithTopBot 𝕜} (hf : IsClosedProperConvex[𝕜] f) :
    (subdifferentialGraph f)⁻¹.RightUnique ↔
      IsEssentiallyStrictlyConvex[𝕜] f := by
  change Relator.RightUnique (· ~[(subdifferentialGraph f)⁻¹] ·) ↔
      IsEssentiallyStrictlyConvex[𝕜] f
  exact (SetRel.rightUnique_inv_iff_leftUnique (ρ := subdifferentialGraph f)).trans
    (leftUnique_subdifferentialGraph_iff_isEssentiallyStrictlyConvex hf)

/-- Theorem 26.4, vector-valued projection companion: on a complete inner-product space, the
Fréchet-Riesz realization of the subdifferential has injective second projection exactly when the
function is essentially strictly convex. This is the inner-product graph-coordinate restatement
of the owner theorem above. -/
theorem injOn_snd_subdifferentialGraph_iff_isEssentiallyStrictlyConvex
    {f : E → WithTopBot 𝕜} (hf : IsClosedProperConvex[𝕜] f) :
    Set.InjOn Prod.snd (subdifferentialGraph f) ↔ IsEssentiallyStrictlyConvex[𝕜] f := by
  rw [← SetRel.leftUnique_iff_injOn_snd]
  exact leftUnique_subdifferentialGraph_iff_isEssentiallyStrictlyConvex hf
end Function

end
