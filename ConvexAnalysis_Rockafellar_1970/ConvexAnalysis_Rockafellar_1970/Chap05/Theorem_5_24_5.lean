import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_12_3_6
import ConvexAnalysis_Rockafellar_1970.Chap05.Definition_5_24_3
import ConvexAnalysis_Rockafellar_1970.Chap05.Definition_5_24_4
import ConvexAnalysis_Rockafellar_1970.Chap05.Remark_5_24_4
import ConvexAnalysis_Rockafellar_1970.Chap05.Theorem_5_24_4
import ConvexAnalysis_Rockafellar_1970.Chap05.Theorem_5_24_12

noncomputable section

open scoped SetRel

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 5.24.5 characterizes exactly which relations `Γ ⊆ ℝ × ℝ` occur as
  graphs of one-dimensional subdifferential mappings of closed proper convex functions, and it
  adds the uniqueness-up-to-constant clause for the realizing function.
- `core/canonical`: the project already owns the relevant notions as the relation predicate
  `SetRel.IsCompleteNondecreasingCurve Γ`, the graph owner
  `_root_.subdifferentialGraph (Y := ℝ) f`, and the admissibility owner
  `Function.IsClosedProperConvex`.
- `bridge/view`: Theorem 5.24.4 already provides the two source halves separately: the existence
  direction for complete nondecreasing curves and the uniqueness theorem for equal
  subdifferential graphs. The current item packages those canonical pieces into the source-facing
  characterization theorem.

Domain-style sampling used here:
- `SetRel.IsCompleteNondecreasingCurve` from
  `ConvexAnalysis_Rockafellar_1970/Chap05/Definition_5_24_4.lean`;
- `Function.subdifferentialGraph` from
  `ConvexAnalysis_Rockafellar_1970/Chap05/Definition_5_24_3.lean`;
- `SetRel.exists_isClosedProperConvex_subdifferentialGraph_eq_of_isCompleteNondecreasingCurve`
  from `ConvexAnalysis_Rockafellar_1970/Chap05/Theorem_5_24_4.lean`;
- `Function.eq_add_const_of_subdifferentialGraph_eq` from
  `ConvexAnalysis_Rockafellar_1970/Chap05/Theorem_5_24_4.lean`.

Primitive data vs derived API:
- primitive source-facing owner input: a relation `Γ : SetRel ℝ ℝ`;
- primitive witness in the existence clause: a function `f : ℝ → WithBotTop ℝ` with
  `f.IsClosedProperConvex`;
- derived clause: if two such functions have graph `Γ`, then they differ by an additive real
  constant.

Layer target: `source-facing`. The main labeled entry is the characterization of the admissible
graphs; the uniqueness statement is kept as a companion theorem rather than being folded into a
large conjunction.

Scalar/codomain canonicalization checkpoint:
- this item remains at the one-dimensional real scalar layer because its primitive reused owners
  (`_root_.subdifferentialGraph`, `SetRel.IsCompleteNondecreasingCurve`, and the Chapter 24
  maximality bridges) are all the `ℝ`-line theorem surfaces for this chapter, not a deferred
  specialization from a scalar-parametric upstream owner in this file;
- the codomain remains `WithBotTop ℝ` because the realizing-function owner
  `Function.IsClosedProperConvex` and the one-dimensional subdifferential graph owner already live
  there upstream; this file only repackages that owner layer.

Topology-language checkpoint:
- no new ambient `closure`/`interior` statement is introduced in this packaging theorem;
- the theorem surface is purely relation/graph classification, so there is no intrinsic-vs-ambient
  topology reformulation to perform in this file.
-/

namespace SetRel

local notation "IsClosedProperConvex[ℝ]" => Function.IsClosedProperConvex (𝕜 := ℝ)
local notation "subgradGraph" =>
  (fun f : ℝ → WithBotTop ℝ ↦
    @_root_.subdifferentialGraph ℝ _ _ _ ℝ _ _ _ f ℝ SetRel.instHasPairingRealLine)
local notation "subgradGraphScalarLine" =>
  (fun f : ℝ → WithBotTop ℝ ↦
    @_root_.subdifferentialGraph ℝ _ _ _ ℝ _ _ _ f ℝ Function.instHasPairingScalarLine)

/-- The scalar-line pairing owner used in Theorem 5.24.4 and the real-line pairing owner used in
Remark 5.24.4 induce the same intrinsic graph relation on `ℝ`. -/
private theorem subgradGraph_scalarLine_eq_subgradGraph (f : ℝ → WithBotTop ℝ) :
    subgradGraphScalarLine f = subgradGraph f := by
  exact _root_.subdifferentialGraph_eq_of_pairing_eq
    (f := f) (Y := ℝ)
    (pairing₁ := Function.instHasPairingScalarLine)
    (pairing₂ := SetRel.instHasPairingRealLine)
    (fun _ _ ↦ rfl)

/-- Bridge on the real line: the Euclidean graph owner `Function.subdifferentialGraph` agrees with
the intrinsic scalar-line subdifferential graph owner. -/
private theorem function_subdifferentialGraph_eq_subgradGraph (f : ℝ → WithBotTop ℝ) :
    Function.subdifferentialGraph f = subgradGraph f := by
  ext p
  rcases p with ⟨x, xStar⟩
  constructor
  · intro hx
    rw [@_root_.mem_subdifferentialGraph ℝ _ _ _ ℝ _ _ _ f ℝ SetRel.instHasPairingRealLine x
      xStar]
    rw [@_root_.mem_subdifferentialAt_pairing ℝ _ _ _ ℝ _ _ _ f x ℝ SetRel.instHasPairingRealLine
      xStar]
    rw [Function.mem_subdifferentialGraph, Function.mem_subdifferentialAt] at hx
    intro z
    have hinner : (inner ℝ xStar (z - x) : ℝ) = (z - x) * xStar := by
      calc
        inner ℝ xStar (z - x) = (starRingEnd ℝ) xStar * (z - x) := by
          simpa using (RCLike.inner_apply' (x := xStar) (y := (z - x)))
        _ = (z - x) * xStar := by simp [mul_comm]
    have hxz := hx z
    rw [hinner] at hxz
    exact hxz
  · intro hx
    rw [Function.mem_subdifferentialGraph, Function.mem_subdifferentialAt]
    rw [@_root_.mem_subdifferentialGraph ℝ _ _ _ ℝ _ _ _ f ℝ SetRel.instHasPairingRealLine x
      xStar] at hx
    rw [@_root_.mem_subdifferentialAt_pairing ℝ _ _ _ ℝ _ _ _ f x ℝ SetRel.instHasPairingRealLine
      xStar] at hx
    intro z
    have hinner : (inner ℝ xStar (z - x) : ℝ) = (z - x) * xStar := by
      calc
        inner ℝ xStar (z - x) = (starRingEnd ℝ) xStar * (z - x) := by
          simpa using (RCLike.inner_apply' (x := xStar) (y := (z - x)))
        _ = (z - x) * xStar := by simp [mul_comm]
    have hxz := hx z
    rw [hinner]
    exact hxz

-- Proof sketch: combine the forward direction from the one-dimensional intrinsic
-- `_root_.subdifferentialGraph` owner with the converse maximal-cyclic bridge.
/-- Theorem 5.24.5: a relation `Γ ⊆ ℝ × ℝ` is a complete non-decreasing curve exactly when it is
the graph of the subdifferential mapping of some closed proper convex function on `ℝ`. -/
theorem isCompleteNondecreasingCurve_iff_exists_isClosedProperConvex_subdifferentialGraph_eq
    (Γ : SetRel ℝ ℝ) :
    Γ.IsCompleteNondecreasingCurve ↔
      ∃ f : ℝ → WithBotTop ℝ,
        IsClosedProperConvex[ℝ] f ∧ subgradGraph f = Γ := by
  -- Theorem 5.24.12 now runs directly at the intrinsic pairing owner layer, so we instantiate it
  -- with the real-line multiplication pairing used by `subgradGraph`.
  let CycRealLine : SetRel ℝ ℝ → Prop := fun ρ =>
    CMonPair[SetRel.instHasPairingRealLine](ρ)
  let MonRealLine : SetRel ℝ ℝ → Prop := fun ρ =>
    Mon[SetRel.instHasPairingRealLine, ℝ](ρ)
  constructor
  · intro hΓ
    rcases
        exists_isClosedProperConvex_subdifferentialGraph_eq_of_isCompleteNondecreasingCurve hΓ
      with
      ⟨f, hf, hgraph⟩
    refine ⟨f, hf, ?_⟩
    calc
      subgradGraph f = subgradGraphScalarLine f := (subgradGraph_scalarLine_eq_subgradGraph f).symm
      _ = Γ := hgraph
  · rintro ⟨f, hf, hgraph⟩
    have hmaxCyclicRealLine :
        Maximal CycRealLine Γ := by
      letI : HasPairing ℝ ℝ ℝ := SetRel.instHasPairingRealLine
      have hmax : Maximal (fun σ : SetRel ℝ ℝ ↦ σ.CyclicallyMonotone ℝ) Γ := by
        simpa using
          (maximal_cyclicallyMonotone_iff_exists_isClosedProperConvex_subdifferentialGraph_eq
            (𝕜 := ℝ) (E := ℝ) (Y := ℝ) Γ).2 ⟨f, hf, hgraph⟩
      simpa [CycRealLine] using hmax
    have hmaxMonotoneRealLine :
        Maximal MonRealLine Γ := by
      rcases hmaxCyclicRealLine with ⟨hΓCyc, hmaxCyc⟩
      refine ⟨(by
        simpa [CycRealLine, MonRealLine] using (monotone_iff_cyclicallyMonotone Γ).2 hΓCyc), ?_⟩
      intro ρ hρMono hΓρ
      have hρCyc : CycRealLine ρ := by
        simpa [CycRealLine, MonRealLine] using (monotone_iff_cyclicallyMonotone ρ).1 hρMono
      exact hmaxCyc hρCyc hΓρ
    exact (maximal_monotone_iff_isCompleteNondecreasingCurve Γ).1
      (by simpa [MonRealLine] using hmaxMonotoneRealLine)

-- Owner-projection form of the existence direction in Theorem 5.24.5.
theorem IsCompleteNondecreasingCurve.exists_isClosedProperConvex_subdifferentialGraph_eq
    {Γ : SetRel ℝ ℝ} (hΓ : Γ.IsCompleteNondecreasingCurve) :
    ∃ f : ℝ → WithBotTop ℝ,
      IsClosedProperConvex[ℝ] f ∧ subgradGraph f = Γ :=
  (isCompleteNondecreasingCurve_iff_exists_isClosedProperConvex_subdifferentialGraph_eq Γ).1 hΓ

-- Owner-projection form of the converse direction in Theorem 5.24.5.
theorem isCompleteNondecreasingCurve_of_exists_isClosedProperConvex_subdifferentialGraph_eq
    {Γ : SetRel ℝ ℝ}
    (hΓ : ∃ f : ℝ → WithBotTop ℝ,
      IsClosedProperConvex[ℝ] f ∧ subgradGraph f = Γ) :
    Γ.IsCompleteNondecreasingCurve :=
  (isCompleteNondecreasingCurve_iff_exists_isClosedProperConvex_subdifferentialGraph_eq Γ).2 hΓ

-- Canonical uniqueness surface: equal subdifferential-graph owners imply equality up to a
-- real additive constant.
/-- Two closed proper convex functions on `ℝ` with equal subdifferential graph owners differ by an
additive real constant. -/
theorem eq_add_const_of_subdifferentialGraph_eq
    {f g : ℝ → WithBotTop ℝ}
    (hf : IsClosedProperConvex[ℝ] f) (hg : IsClosedProperConvex[ℝ] g)
    (hfg : subgradGraph f = subgradGraph g) :
    ∃ α : ℝ, g = fun x ↦ f x + α :=
  by
    have hfg_scalar : subgradGraphScalarLine f = subgradGraphScalarLine g := by
      calc
        subgradGraphScalarLine f = subgradGraph f :=
          subgradGraph_scalarLine_eq_subgradGraph f
        _ = subgradGraph g := hfg
        _ = subgradGraphScalarLine g :=
          (subgradGraph_scalarLine_eq_subgradGraph g).symm
    exact
      Function.eq_add_const_of_subdifferentialGraph_eq hf hg hfg_scalar

-- Proof sketch: convert the source-facing same-curve hypotheses to the canonical graph-equality
-- hypothesis and apply `eq_add_const_of_subdifferentialGraph_eq`.
/-- Two closed proper convex functions on `ℝ` with the same subdifferential graph `Γ` differ by
an additive real constant. -/
theorem eq_add_const_of_subdifferentialGraph_eq_same_curve
    {Γ : SetRel ℝ ℝ} {f g : ℝ → WithBotTop ℝ}
    (hf : IsClosedProperConvex[ℝ] f) (hg : IsClosedProperConvex[ℝ] g)
    (hfΓ : subgradGraph f = Γ)
    (hgΓ : subgradGraph g = Γ) :
    ∃ α : ℝ, g = fun x ↦ f x + α :=
  eq_add_const_of_subdifferentialGraph_eq hf hg (hfΓ.trans hgΓ.symm)

end SetRel
