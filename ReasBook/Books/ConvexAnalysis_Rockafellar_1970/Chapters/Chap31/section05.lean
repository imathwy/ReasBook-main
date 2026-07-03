import Mathlib
import Mathlib.Analysis.Calculus.Gradient.Basic

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_31_5_1 (from Chap06) -/
noncomputable section

universe u

section

open scoped Gradient RealInnerProductSpace Rockafellar SetRel

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "IsClosedProperConvex[ℝ]" => @Function.IsClosedProperConvex ℝ
local notation "w" => (fun z : E ↦ (((1 / 2 : ℝ) * ‖z‖ ^ 2 : ℝ) : WithBotTop ℝ))

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 31.5.1 says that for a closed proper convex function, the graph of
  the subdifferential is carried homeomorphically onto the ambient space by the coordinate-sum
  map `(x, x⋆) ↦ x + x⋆`.
- `core/canonical`: the project already owns the intrinsic subdifferential graph relation as
  `gph∂[E](f)`, and Proposition 5.24.1 already owns the generic relation-side coordinate-sum map
  `Γ.coordinateSumMap` together with the canonical topological target predicate `IsHomeomorph`.
- `bridge/view`: the proof uses Euclidean Moreau/proximal bridge lemmas on
  `Function.subdifferentialGraph` internally, then transports membership to the intrinsic owner
  `gph∂[E](f)` for the theorem surface.

Domain-style sampling used here:
- `gph∂[E](f)` and `Function.subdifferentialGraph` from `Chap05.Definition_5_24_3`;
- `(Γ : SetRel X Y).coordinateSumMap` from `Chap05.Proposition_5_24_1`;
- `moreau_identity` and `primal_and_dual_moreau_minimizers_iff_euclidean` from
  `Chap06.Theorem_31_5`;
- `Function.prox_add_dual_moreau_gradient_mem_subdifferential` and
  `Function.dual_moreau_gradient_eq_sub` from `Chap06.Remark_31_5_1`;
- `Function.prox_nonexpansive` from `Chap06.Example_31_5_2`.

Primitive data vs derived API:
- primitive input: a closed proper convex function `f`, represented by
  `hf : f.IsClosedProperConvex`;
- primitive source-facing map: the coordinate-sum map on the intrinsic graph owner
  `(gph∂[E](f)).coordinateSumMap`;
- derived conclusion: this map is a homeomorphism from the graph subtype onto the ambient space.

Ambient-assumption minimization:
- the source writes `R^n`, but the proof route uses only the Euclidean Moreau/proximal theory
  already established in complete real inner-product spaces;
- finite dimensionality is therefore not primitive for the canonical theorem surface here, and the
  textbook statement is recovered by specialization.
-/

namespace Function

-- Proof sketch: use Theorem 31.5 to show that every `z` admits a unique decomposition
-- `z = x + xStar` with `xStar ∈ ∂ᵥf(x)`, so the coordinate-sum map on `subdifferentialGraph f`
-- is bijective. Remark 31.5.1 gives the inverse explicitly as
-- `z ↦ (prox f hf z, z - prox f hf z)`, and Example 31.5.2 gives continuity of `prox`; the
-- residual map `z ↦ z - prox f hf z` is therefore continuous as well.
/-- Corollary 31.5.1: for a closed proper convex function on a complete real inner-product space,
the coordinate-sum map `(x, x⋆) ↦ x + x⋆` is a homeomorphism from the intrinsic self-pairing
subdifferential graph `gph∂[E](f)` onto the ambient space. The textbook `R^n` statement is
recovered by specialization. -/
theorem isHomeomorph_subdifferentialGraph_coordinateSumMap
    (f : E → WithBotTop ℝ) (hf : IsClosedProperConvex[ℝ] f) :
    IsHomeomorph (gph∂[E](f)).coordinateSumMap := by
  let Γ := gph∂[E](f)
  let prox := Function.prox f hf
  have hgraph_iff_vec {x xStar : E} :
      x ~[Γ] xStar ↔ x ~[Function.subdifferentialGraph f] xStar := by
    change x ~[gph∂[E](f)] xStar ↔ x ~[Function.subdifferentialGraph f] xStar
    constructor
    · intro hx
      rw [_root_.mem_subdifferentialGraph, _root_.mem_subdifferentialAt_pairing,
        Function.mem_subdifferentialGraph, Function.mem_subdifferentialAt] at *
      intro z
      have hz := hx z
      have hinner :
          (inner ℝ xStar (z - x) : ℝ) =
            (HasLinearPairing.pairingLinear z xStar - HasLinearPairing.pairingLinear x xStar) :=
        by
          calc
            (inner ℝ xStar (z - x) : ℝ) = inner ℝ xStar z - inner ℝ xStar x := by
              rw [inner_sub_right]
            _ = inner ℝ z xStar - inner ℝ x xStar := by
              simp [real_inner_comm]
            _ =
                (HasLinearPairing.pairingLinear z xStar -
                  HasLinearPairing.pairingLinear x xStar) := by
              rfl
      simpa [hinner] using hz
    · intro hx
      rw [_root_.mem_subdifferentialGraph, _root_.mem_subdifferentialAt_pairing,
        Function.mem_subdifferentialGraph, Function.mem_subdifferentialAt] at *
      intro z
      have hz := hx z
      have hinner :
          (inner ℝ xStar (z - x) : ℝ) =
            (HasLinearPairing.pairingLinear z xStar - HasLinearPairing.pairingLinear x xStar) :=
        by
          calc
            (inner ℝ xStar (z - x) : ℝ) = inner ℝ xStar z - inner ℝ xStar x := by
              rw [inner_sub_right]
            _ = inner ℝ z xStar - inner ℝ x xStar := by
              simp [real_inner_comm]
            _ =
                (HasLinearPairing.pairingLinear z xStar -
                  HasLinearPairing.pairingLinear x xStar) := by
              rfl
      simpa [hinner] using hz
  have hprox_mem_graph (z : E) : prox z ~[Γ] (z - prox z) := by
    refine (hgraph_iff_vec (x := prox z) (xStar := z - prox z)).2 ?_
    rw [Function.mem_subdifferentialGraph]
    change z - Function.prox f hf z ∈ ∂ᵥf(Function.prox f hf z)
    exact
      (Function.dual_moreau_gradient_eq_sub f hf z) ▸
        (Function.prox_add_dual_moreau_gradient_mem_subdifferential f hf z).2
  have hprox_lipschitz : LipschitzWith 1 prox := by
    simpa [prox] using Function.prox_lipschitz f hf
  have hprox_cont : Continuous prox :=
    hprox_lipschitz.continuous
  let inv : E → Γ := fun z ↦ ⟨(prox z, z - prox z), hprox_mem_graph z⟩
  have hleft_inv : Function.LeftInverse inv Γ.coordinateSumMap := by
    intro p
    rcases p with ⟨⟨x, xStar⟩, hxGraph⟩
    have hxGraphVec : x ~[Function.subdifferentialGraph f] xStar :=
      (hgraph_iff_vec (x := x) (xStar := xStar)).1 hxGraph
    have hmin :
        IsMinOn (fun y : E ↦ f y + w ((x + xStar) - y)) Set.univ x ∧
          IsMinOn (fun yStar : E ↦ (f⋆) yStar + w ((x + xStar) - yStar)) Set.univ xStar := by
      exact
        (primal_and_dual_moreau_minimizers_iff_euclidean hf (x + xStar) x xStar).2
          ⟨rfl, Function.mem_subdifferentialGraph.mp hxGraphVec⟩
    have hx : x = prox (x + xStar) :=
      Function.eq_prox_of_isMinOn f hf (x + xStar) x hmin.1
    apply Subtype.ext
    apply Prod.ext
    · exact hx.symm
    · change (x + xStar) - prox (x + xStar) = xStar
      rw [← hx]
      abel
  have hright_inv : Function.RightInverse inv Γ.coordinateSumMap := by
    intro z
    change prox z + (z - prox z) = z
    abel
  let e : Γ ≃ₜ E :=
    { toEquiv :=
        { toFun := Γ.coordinateSumMap
          invFun := inv
          left_inv := hleft_inv
          right_inv := hright_inv }
      continuous_toFun := by
        simpa [Γ, SetRel.coordinateSumMap] using
          (continuous_subtype_val.fst.add continuous_subtype_val.snd :
            Continuous (fun p : Γ ↦ (p : E × E).1 + (p : E × E).2))
      continuous_invFun := by
        simpa [inv] using
          (hprox_cont.prodMk (continuous_id.sub hprox_cont)).subtype_mk hprox_mem_graph }
  exact e.isHomeomorph

end Function

end

/-! ### Remark_31_5_1 (from Chap06) -/
noncomputable section

open scoped Gradient PolarCone RealInnerProductSpace Rockafellar

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "IsClosedProperConvex[ℝ]" => @Function.IsClosedProperConvex ℝ
local notation "w" => (fun z : E ↦ (((1 / 2 : ℝ) * ‖z‖ ^ 2 : ℝ) : WithBotTop ℝ))

/-!
Source/core/bridge triage for this item.

- `source-facing`: Remark 31.5.1 introduces the proximation operator of a closed proper convex
  function as the unique minimizer of the quadratic perturbation from Theorem 31.5, then records
  Moreau's decomposition through the canonical dual Moreau minimizer, together with the
  closed-convex-set / cone / subspace specializations.
- `core/canonical`: the relevant existing owners are `Function.IsClosedProperConvex`,
  `IsMinOn`, Fenchel conjugation `f⋆`, the subdifferential owner
  `∂ᵥ` / `Function.subdifferentialAt`, the indicator notation `δ[ℝ](· | C)`, and the polar
  notation `Kᵒ`, plus the Chapter 31 gradient/minimizer owners for the primal and dual Moreau
  envelopes.
- `bridge/view`: the new source-facing owner in this file is the proximal map itself; the cone and
  subspace remarks stay as companion theorems rather than as a new wrapper package.

Domain-style sampling used here:
- `existsUnique_primal_moreau_minimizer`;
- `primal_and_dual_moreau_minimizers_iff_euclidean`;
- `gradient_dual_moreau_envelope_is_primal_minimizer`;
- `gradient_primal_moreau_envelope_is_dual_minimizer`;
- `indicatorFunction_isClosedProperConvex_of_nonempty`;
- `convexConjugate_indicatorFunction_eq_indicatorFunction_polarCone`;
- `polarCone_eq_orthogonal`.

Primitive data vs derived API:
- primitive inputs: a closed proper convex function `f`, represented by
  `hf : f.IsClosedProperConvex`, and a point `z`;
- derived API: the canonical minimizer `Function.prox f hf z`, its variational specification, the
  Moreau decomposition through the canonical dual Moreau gradient, and the geometric
  specializations to projections onto a closed convex set, to cone/polar decompositions, and to
  orthogonal decompositions of subspaces.

Layer target: `source-facing`, with the public owner `Function.prox` built from the canonical
unique-minimizer owner already proved in Theorem 31.5.

Notation decision:
- no additional textbook notation is introduced here, because the canonical owner depends on the
  non-inferable hypothesis `hf : f.IsClosedProperConvex`; keeping `hf` explicit is part of the
  correct public API for this file.
-/

namespace Function

/-- Remark 31.5.1: for a closed proper convex function `f`, the proximation operator sends `z` to
the unique minimizer of `x ↦ f x + (1 / 2) ‖z - x‖^2`. This is Rockafellar's
`prox(z | f)`. -/
noncomputable def prox (f : E → WithBotTop ℝ) (hf : IsClosedProperConvex[ℝ] f) (z : E) : E :=
  Classical.choose (existsUnique_primal_moreau_minimizer hf z)

-- Proof sketch: `Function.prox f hf z` is the unique primal Moreau minimizer supplied by
-- `existsUnique_primal_moreau_minimizer hf z`.
/-- The proximation operator realizes the unique minimizer in Theorem 31.5. -/
theorem prox_isMinOn (f : E → WithBotTop ℝ) (hf : IsClosedProperConvex[ℝ] f) (z : E) :
    IsMinOn (fun x : E ↦ f x + w (z - x)) Set.univ (prox f hf z) := sorry

-- Proof sketch: uniqueness in `existsUnique_primal_moreau_minimizer hf z` identifies any other
-- minimizer of the same quadratic perturbation with the chosen point `prox f hf z`.
/-- Any minimizer of the primal Moreau objective is equal to the proximation point. -/
theorem eq_prox_of_isMinOn (f : E → WithBotTop ℝ) (hf : IsClosedProperConvex[ℝ] f) (z x : E)
    (hx : IsMinOn (fun y : E ↦ f y + w (z - y)) Set.univ x) :
    x = prox f hf z := sorry

-- Proof sketch: combine `prox_isMinOn` with
-- `gradient_primal_moreau_envelope_is_dual_minimizer hf z`, then apply
-- `primal_and_dual_moreau_minimizers_iff_euclidean`. The resulting identity is Moreau's
-- decomposition, with the gradient of the primal Moreau envelope realizing the dual proximation
-- point.
/-- Moreau's decomposition: `z` is the sum of the proximation point `prox(z | f)` and the
gradient of the primal Moreau envelope `((f □ w).realBranch)`, and that gradient lies in
`∂f (prox(z | f))`. -/
theorem prox_add_dual_moreau_gradient_mem_subdifferential
    (f : E → WithBotTop ℝ) (hf : IsClosedProperConvex[ℝ] f) (z : E) :
    z = prox f hf z + ∇ (Function.realBranch ((f □ w) : E → WithBotTop ℝ)) z ∧
      ∇ (Function.realBranch ((f □ w) : E → WithBotTop ℝ)) z ∈ ∂ᵥf(prox f hf z) := sorry

-- Proof sketch: take the decomposition identity from
-- `prox_add_dual_moreau_gradient_mem_subdifferential` and solve for the dual Moreau gradient.
/-- The dual Moreau gradient is the residual `z - prox(z | f)`. In Remark 31.5.1 this is the
dual proximation point corresponding to `f⋆`. -/
theorem dual_moreau_gradient_eq_sub
    (f : E → WithBotTop ℝ) (hf : IsClosedProperConvex[ℝ] f) (z : E) :
    ∇ (Function.realBranch ((f □ w) : E → WithBotTop ℝ)) z = z - prox f hf z := sorry

-- Proof sketch: for `f = δ[ℝ](· | C)`, the objective defining `prox f z` is finite exactly on
-- `C`, where it reduces to `(1 / 2) ‖z - x‖^2`. Thus the proximation point lies in `C` and is
-- the nearest point of `C` to `z`.
/-- For the indicator of a nonempty closed convex set, the proximation point is the closest point
of the set. -/
theorem prox_indicator_isClosestPoint
    {C : Set E} (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    (z : E) :
    prox (δ[ℝ](· | C) : E → WithBotTop ℝ)
        (indicatorFunction_isClosedProperConvex_of_nonempty hC_nonempty hC_closed hC_convex) z ∈
      C ∧
      IsMinOn (fun x : E ↦ ‖z - x‖) C
        (prox (δ[ℝ](· | C) : E → WithBotTop ℝ)
          (indicatorFunction_isClosedProperConvex_of_nonempty hC_nonempty hC_closed hC_convex)
          z) := sorry

end Function

-- Proof sketch: specialize the Moreau decomposition theorem to the indicator of `K`. Theorem 14.1
-- identifies the conjugate with the indicator of `Kᵒ`, so the two proximation points belong to
-- `K` and `Kᵒ`; the subgradient characterization of Theorem 31.5 yields the complementary
-- slackness condition `⟪x, xStar⟫ = 0`.
/-- For the indicator of a nonempty closed convex cone `K`, every `z` has a unique decomposition
`z = x + xStar` with `x ∈ K`, `xStar ∈ Kᵒ[ℝ]`, and `⟪x, xStar⟫ = 0`. -/
theorem existsUnique_cone_polar_decomposition
    {K : Set E} (hK_nonempty : K.Nonempty) (hK_closed : IsClosed K) (hK : Set.IsConvexCone ℝ K)
    (z : E) :
    ∃! p : E × E,
      z = p.1 + p.2 ∧
        p.1 ∈ K ∧
        p.2 ∈ Kᵒ[ℝ] ∧
        ⟪p.1, p.2⟫ = (0 : ℝ) := sorry

section FiniteDimensional

variable [FiniteDimensional ℝ E]

-- Proof sketch: apply the cone/polar decomposition theorem to the subspace `L`, then rewrite its
-- polar cone by `Submodule.polarCone_eq_orthogonal`. The resulting pair is exactly the orthogonal
-- decomposition of `z` with respect to `L`.
/-- For a subspace `L`, the cone/polar decomposition from Remark 31.5.1 becomes the orthogonal
decomposition of `z` into a component of `L` and a component of `Lᗮ`. -/
theorem existsUnique_submodule_orthogonal_decomposition
    (L : Submodule ℝ E) (z : E) :
    ∃! p : E × E,
      z = p.1 + p.2 ∧
        p.1 ∈ L ∧
        p.2 ∈ L.orthogonal := sorry

end FiniteDimensional

end

/-! ### Corollary_31_5_2 (from Chap06) -/
noncomputable section

universe u

section

open scoped Gradient RealInnerProductSpace Rockafellar SetRel

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {f : E → WithBotTop ℝ}

local notation "w" => (fun z : E ↦ (((1 / 2 : ℝ) * ‖z‖ ^ 2 : ℝ) : WithBotTop ℝ))
local notation "fStar" => (f⋆ : E → WithBotTop ℝ)
local notation "primalEnvelope" => (f □ w : E → WithBotTop ℝ)
local notation "dualEnvelope" => (fStar □ w : E → WithBotTop ℝ)
local notation "primalEnvelopeReal" => (Function.realBranch primalEnvelope : E → ℝ)
local notation "dualEnvelopeReal" => (Function.realBranch dualEnvelope : E → ℝ)
local notation "IsClosedProperConvex[ℝ]" => @Function.IsClosedProperConvex ℝ

/-!
Source/core/bridge triage:

- `source-facing`: Corollary 31.5.2 asserts that the subdifferential of a closed proper convex
  function on `R^n` is a maximal monotone mapping. This file states the same content on the more
  canonical ambient layer of complete real inner-product spaces, which specializes back to the
  finite-dimensional source setting.
- `core/canonical`: the project already organizes subdifferential mappings as the pairing-level
  relation `gph∂[Y](f)`, monotonicity as `SetRel.Monotone ρ ℝ`, and
  maximality as `Maximal` for the inclusion order on relations.
- `bridge/view`: this item uses Euclidean Moreau identities only as the proof bridge, while the
  theorem surface is stated on the intrinsic self-pairing owner `gph∂[E](f)`.

Domain-style sampling used here:

- `Function.IsClosedProperConvex` from `Chap03.Text_12_3_6`;
- `_root_.subdifferentialGraph` / notation `gph∂[Y](f)` from `Chap05.Definition_5_24_3`;
- `SetRel.CyclicallyMonotone.monotone` from `Chap05.Proposition_5_24_4`;
- `SetRel.Monotone` from `Chap05.Definition_5_24_7`;
- `gradient_dual_moreau_envelope_is_primal_minimizer`,
  `gradient_primal_moreau_envelope_is_dual_minimizer`, and
  `primal_and_dual_moreau_minimizers_iff_euclidean` from
  `Chap06.Theorem_31_5`;
- `Maximal` from mathlib's order API.

Ambient-assumption minimization:
- `subdifferentialGraph_cyclicallyMonotone` uses only properness;
- the Moreau gradient-minimizer theorems already have the canonical `[CompleteSpace E]` owner
  layer;
- `primal_and_dual_moreau_minimizers_iff_euclidean` is the Euclidean bridge theorem needed for the
  graph-level argument here;
- finite dimensionality is therefore derived rather than primitive here, so the public theorem is
  stated directly on complete real inner-product spaces.

Layer target: `source-facing`, stated directly on the canonical relation graph of the
subdifferential.
-/

/-- Corollary 31.5.2: if `f` is a closed proper convex function on a complete real inner-product
space, then its self-pairing subdifferential graph `gph∂[E](f)` is maximal among monotone
relations. The finite-dimensional `R^n` source statement is recovered by specialization. This is
the canonical relation-level form of saying that `∂f` is a maximal monotone mapping. -/
theorem maximal_monotone_subdifferentialGraph
    (hf : IsClosedProperConvex[ℝ] f) :
    Maximal (·.Monotone ℝ) (gph∂[E](f)) := by
  have hgraphMon : (gph∂[E](f)).Monotone ℝ := by
    exact SetRel.CyclicallyMonotone.monotone
      (subdifferentialGraph_cyclicallyMonotone (Y := E) hf.proper)
  refine ⟨hgraphMon, ?_⟩
  intro ρ hρ hgraph_le_ρ p hp
  rcases p with ⟨y, yStar⟩
  let z := y + yStar
  let x := ∇ dualEnvelopeReal z
  let xStar := ∇ primalEnvelopeReal z
  have hxMin : IsMinOn (fun x : E ↦ f x + w (z - x)) Set.univ x := by
    simpa [x] using gradient_dual_moreau_envelope_is_primal_minimizer hf z
  have hxStarMin :
      IsMinOn (fun xStar : E ↦ fStar xStar + w (z - xStar)) Set.univ xStar := by
    simpa [xStar] using gradient_primal_moreau_envelope_is_dual_minimizer hf z
  have hdecomp : z = x + xStar ∧ xStar ∈ ∂ᵥf(x) :=
    (primal_and_dual_moreau_minimizers_iff_euclidean hf z x xStar).mp ⟨hxMin, hxStarMin⟩
  rcases hdecomp with ⟨hz, hxStar_mem⟩
  have hxGraphVec : x ~[Function.subdifferentialGraph f] xStar :=
    Function.mem_subdifferentialGraph.mpr hxStar_mem
  have hxGraph : x ~[gph∂[E](f)] xStar := by
    rw [_root_.mem_subdifferentialGraph, _root_.mem_subdifferentialAt_pairing]
    intro z
    have hinner :
        (inner ℝ xStar (z - x) : ℝ) =
          (HasLinearPairing.pairingLinear z xStar - HasLinearPairing.pairingLinear x xStar) := by
      calc
        (inner ℝ xStar (z - x) : ℝ) = inner ℝ xStar z - inner ℝ xStar x := by
          rw [inner_sub_right]
        _ = inner ℝ z xStar - inner ℝ x xStar := by
          simp [real_inner_comm]
        _ = (HasLinearPairing.pairingLinear z xStar - HasLinearPairing.pairingLinear x xStar) := by
          rfl
    simpa [hinner] using
      Function.mem_subdifferentialAt.mp (Function.mem_subdifferentialGraph.mp hxGraphVec) z
  have hxρ : x ~[ρ] xStar :=
    hgraph_le_ρ hxGraph
  have hnonneg : 0 ≤ (⟪y - x, yStar - xStar⟫ₚ : ℝ) :=
    hρ.pairing_nonneg hxρ hp
  have hsum : (y - x) + (yStar - xStar) = 0 := by
    have hz' : y + yStar = x + xStar := by
      simpa [z] using hz
    calc
      (y - x) + (yStar - xStar) = (y + yStar) - (x + xStar) := by abel
      _ = 0 := by rw [hz']; simp
  have hsub : yStar - xStar = -(y - x) := by
    calc
      yStar - xStar = -(y - x) + ((y - x) + (yStar - xStar)) := by abel
      _ = -(y - x) := by rw [hsum, add_zero]
  have hpair :
      (⟪y - x, yStar - xStar⟫ₚ : ℝ) = -‖y - x‖ ^ 2 := by
    change inner ℝ (y - x) (yStar - xStar) = -‖y - x‖ ^ 2
    rw [hsub, inner_neg_right, real_inner_self_eq_norm_sq]
  have hnorm_sq_le_zero : ‖y - x‖ ^ 2 ≤ 0 := by
    nlinarith [hnonneg, hpair]
  have hnorm_sq_zero : ‖y - x‖ ^ 2 = 0 :=
    le_antisymm hnorm_sq_le_zero (sq_nonneg ‖y - x‖)
  have hyx : y = x := by
    apply sub_eq_zero.mp
    apply norm_eq_zero.mp
    exact sq_eq_zero_iff.mp hnorm_sq_zero
  have hyStarxStar : yStar = xStar := by
    have hz' : y + yStar = x + xStar := by
      simpa [z] using hz
    simpa [hyx] using hz'
  rw [hyx, hyStarxStar]
  exact hxGraph

end

/-! ### Example_31_5_2 (from Chap06) -/
noncomputable section

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

open scoped Rockafellar SetRel

local notation "IsClosedProperConvex[ℝ]" => @Function.IsClosedProperConvex ℝ

/-!
Source/core/bridge triage for this item.

- `source-facing`: Example 31.5.2 records the contraction property of the proximation operator of a
  closed proper convex function.
- `core/canonical`: the relevant owner abstractions are the Chapter 12 owner
  `Function.IsClosedProperConvex`, the proximation operator `Function.prox` from
  `Remark_31_5_1`, and the vector subdifferential owner `Function.subdifferentialAt`.
- `bridge/view`: the explicit minimizer formulation is derived API now owned upstream by
  `Function.prox_isMinOn` and `Function.eq_prox_of_isMinOn`; this file keeps the source-facing
  contraction theorem directly on the canonical proximation operator instead of reintroducing a
  parallel minimizer-level public statement.

Domain-style sampling used here:
- `Function.IsClosedProperConvex`;
- `Function.prox`;
- `Function.prox_isMinOn`;
- `Function.eq_prox_of_isMinOn`;
- `Function.subdifferentialAt`;
- `SetRel.Monotone`.

Primitive data vs derived API:
- primitive input: a closed proper convex function `f`, represented by
  `hf : f.IsClosedProperConvex`;
- primitive source data: two points `z₀` and `z₁`;
- derived output: the contraction estimate for the canonical proximation points
  `prox f hf z₀` and `prox f hf z₁`; any explicit minimizer statement is a companion view obtained
  by rewriting with `eq_prox_of_isMinOn`.

Layer target: `source-facing`, stated directly on the canonical owner `Function.prox`.

Ambient-assumption minimization:
- the proximation owner from Remark 31.5.1 already lives on complete real inner-product spaces;
- finite dimensionality is therefore not primitive for this example and is removed from the public
  statement.
-/

namespace Function

-- Proof sketch: apply Remark 31.5.1 to write the residual vectors
-- `zᵢ - prox f hf zᵢ` as subgradients of `f` at `prox f hf zᵢ`. Monotonicity of the
-- subdifferential then gives
-- `0 ≤ ⟪prox f hf z₁ - prox f hf z₀, (z₁ - prox f hf z₁) - (z₀ - prox f hf z₀)⟫`.
-- Expanding `‖z₁ - z₀‖²` as the norm square of the sum of these two differences yields the
-- contraction estimate.
/-- Example 31.5.2, canonical owner form: the proximation operator is `1`-Lipschitz. -/
theorem prox_lipschitz
    (f : E → WithBotTop ℝ) (hf : IsClosedProperConvex[ℝ] f) :
    LipschitzWith 1 (prox f hf) := by
  refine lipschitzWith_iff_norm_sub_le.mpr ?_
  intro z₁ z₀
  let x₀ : E := prox f hf z₀
  let x₁ : E := prox f hf z₁
  let g₀ : E := z₀ - x₀
  let g₁ : E := z₁ - x₁
  let Γ : SetRel E E := _root_.subdifferentialGraph (f := f) (Y := E)
  have hg₀_mem : g₀ ∈ Function.subdifferentialAt f x₀ := by
    dsimp [g₀, x₀]
    exact (Function.dual_moreau_gradient_eq_sub f hf z₀) ▸
      (Function.prox_add_dual_moreau_gradient_mem_subdifferential f hf z₀).2
  have hg₁_mem : g₁ ∈ Function.subdifferentialAt f x₁ := by
    dsimp [g₁, x₁]
    exact (Function.dual_moreau_gradient_eq_sub f hf z₁) ▸
      (Function.prox_add_dual_moreau_gradient_mem_subdifferential f hf z₁).2
  have hg₀_graph_vec : x₀ ~[Function.subdifferentialGraph f] g₀ :=
    Function.mem_subdifferentialGraph.mpr hg₀_mem
  have hg₁_graph_vec : x₁ ~[Function.subdifferentialGraph f] g₁ :=
    Function.mem_subdifferentialGraph.mpr hg₁_mem
  have hg₀_graph : x₀ ~[Γ] g₀ := by
    dsimp [Γ]
    rw [_root_.mem_subdifferentialAt_pairing]
    intro z
    have hinner :
        (inner ℝ g₀ (z - x₀) : ℝ) =
          (HasLinearPairing.pairingLinear z g₀ - HasLinearPairing.pairingLinear x₀ g₀) := by
      calc
        (inner ℝ g₀ (z - x₀) : ℝ) = inner ℝ g₀ z - inner ℝ g₀ x₀ := by
          rw [inner_sub_right]
        _ = inner ℝ z g₀ - inner ℝ x₀ g₀ := by
          simp [real_inner_comm]
        _ = (HasLinearPairing.pairingLinear z g₀ - HasLinearPairing.pairingLinear x₀ g₀) := by
          rfl
    simpa [hinner] using
      Function.mem_subdifferentialAt.mp
        (Function.mem_subdifferentialGraph.mp hg₀_graph_vec) z
  have hg₁_graph : x₁ ~[Γ] g₁ := by
    dsimp [Γ]
    rw [_root_.mem_subdifferentialAt_pairing]
    intro z
    have hinner :
        (inner ℝ g₁ (z - x₁) : ℝ) =
          (HasLinearPairing.pairingLinear z g₁ - HasLinearPairing.pairingLinear x₁ g₁) := by
      calc
        (inner ℝ g₁ (z - x₁) : ℝ) = inner ℝ g₁ z - inner ℝ g₁ x₁ := by
          rw [inner_sub_right]
        _ = inner ℝ z g₁ - inner ℝ x₁ g₁ := by
          simp [real_inner_comm]
        _ = (HasLinearPairing.pairingLinear z g₁ - HasLinearPairing.pairingLinear x₁ g₁) := by
          rfl
    simpa [hinner] using
      Function.mem_subdifferentialAt.mp
        (Function.mem_subdifferentialGraph.mp hg₁_graph_vec) z
  have hΓ_mon : Γ.Monotone ℝ := by
    dsimp [Γ]
    exact SetRel.CyclicallyMonotone.monotone
      (subdifferentialGraph_cyclicallyMonotone (Y := E) hf.proper)
  have hnonneg_pair : 0 ≤ (⟪x₁ - x₀, g₁ - g₀⟫ₚ : ℝ) :=
    hΓ_mon.pairing_nonneg hg₀_graph hg₁_graph
  have hnonneg :
      0 ≤ inner ℝ (x₁ - x₀) (g₁ - g₀) := by
    change 0 ≤ (⟪x₁ - x₀, g₁ - g₀⟫ₚ : ℝ)
    exact hnonneg_pair
  have hg_diff : g₁ - g₀ = (z₁ - z₀) - (x₁ - x₀) := by
    dsimp [g₀, g₁]
    abel
  have hmono :
      0 ≤ inner ℝ (x₁ - x₀) ((z₁ - z₀) - (x₁ - x₀)) := by
    simpa [hg_diff] using hnonneg
  have hsq_le_inner :
      ‖x₁ - x₀‖ ^ 2 ≤ inner ℝ (x₁ - x₀) (z₁ - z₀) := by
    have hmono' :
        0 ≤ inner ℝ (x₁ - x₀) (z₁ - z₀) - inner ℝ (x₁ - x₀) (x₁ - x₀) := by
      simpa [inner_sub_right] using hmono
    have hinner_le :
        inner ℝ (x₁ - x₀) (x₁ - x₀) ≤ inner ℝ (x₁ - x₀) (z₁ - z₀) := by
      linarith
    simpa [real_inner_self_eq_norm_sq] using hinner_le
  have hsq_le_mul :
      ‖x₁ - x₀‖ ^ 2 ≤ ‖x₁ - x₀‖ * ‖z₁ - z₀‖ := by
    exact hsq_le_inner.trans (real_inner_le_norm _ _)
  have hnorm_le : ‖x₁ - x₀‖ ≤ ‖z₁ - z₀‖ := by
    by_cases hzero : ‖x₁ - x₀‖ = 0
    · simp [hzero]
    · have hpos : 0 < ‖x₁ - x₀‖ :=
        lt_of_le_of_ne (norm_nonneg (x₁ - x₀)) (Ne.symm hzero)
      have hmul :
          ‖x₁ - x₀‖ * ‖x₁ - x₀‖ ≤ ‖x₁ - x₀‖ * ‖z₁ - z₀‖ := by
        simpa [pow_two] using hsq_le_mul
      exact le_of_mul_le_mul_left hmul hpos
  simpa [x₀, x₁, one_mul] using hnorm_le

/-- Example 31.5.2, pointwise view: the proximation operator is nonexpansive. -/
theorem prox_nonexpansive
    (f : E → WithBotTop ℝ) (hf : IsClosedProperConvex[ℝ] f) (z₀ z₁ : E) :
    ‖prox f hf z₁ - prox f hf z₀‖ ≤ ‖z₁ - z₀‖ := by
  have h :=
    (lipschitzWith_iff_norm_sub_le.mp (prox_lipschitz f hf)) z₁ z₀
  simpa [one_mul] using h

end Function

end

/-! ### Theorem_31_5 (from Chap06) -/
noncomputable section

open scoped Gradient RealInnerProductSpace Rockafellar

universe u

section

variable {E : Type u} {EStar : Type u}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup EStar] [NormedSpace ℝ EStar]
variable [HasPairing E EStar ℝ]
variable {f : E → WithBotTop ℝ}
variable (J : E →ₗ[ℝ] EStar)

local notation "IsClosedProperConvex[ℝ]" => @Function.IsClosedProperConvex ℝ
local notation "w" => (fun z : E ↦ (((1 / 2 : ℝ) * ‖z‖ ^ 2 : ℝ) : WithBotTop ℝ))
local notation "fStar" => (f⋆ : EStar → WithBotTop ℝ)
local notation "wStar" =>
  (fun zStar : EStar ↦ (((1 / 2 : ℝ) * ‖zStar‖ ^ 2 : ℝ) : WithBotTop ℝ))
local notation "primalEnvelope" => (f □ w : E → WithBotTop ℝ)
local notation "dualEnvelope" => (fStar □ wStar : EStar → WithBotTop ℝ)
local notation "dualEnvelopeOnPrimal" =>
  (fun z : E ↦ dualEnvelope (J z))

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 31.5 is Moreau's identity for a closed proper convex function together
  with finiteness/unique-attainment of the two quadratic infimal convolutions and the optimality
  characterization of the primal/dual minimizing pair.
- `core/canonical`: the source owner layer here is pairing-first, on a primal/dual ambient
  `(E, EStar)` with explicit bridge map `J : E →ₗ[ℝ] EStar`; the canonical owners are infimal
  convolution `□`, Fenchel conjugation `f⋆`, `Function.IsClosedProperConvex`, and intrinsic
  subdifferentials `∂[EStar]f(x)`.
- `bridge/view`: the self-dual Hilbert-space formulas (`toDualMap`, `∂ᵥ`, gradients) are stated
  below as Euclidean bridge theorems; they are not the root owner layer for this item.

Domain-style sampling used here:
- `convexConjugate` / `f⋆` from `Chap03.Defn_12_2`;
- `Function.IsClosedProperConvex` from `Chap03.Text_12_3_6`;
- `_root_.subdifferentialAt` and the notation `∂ f at x` from `Chap05.Definition_23_0_6`;
- `Function.subdifferentialAt` / `∂ᵥf(x)` from the same file, used only in the bridge section.

Primitive data vs derived API:
- primitive input: a closed proper convex function `f`, represented by
  `hf : f.IsClosedProperConvex`;
- primitive primal/dual kernels:
  `w(z) = (1 / 2) ‖z‖²` on `E` and `wStar(zStar) = (1 / 2) ‖zStar‖²` on `EStar`;
- primitive bridge data: the explicit map `J : E →ₗ[ℝ] EStar`, which is mathematically essential
  because `EStar` is not recoverable from `E` in the pairing-level owner;
- derived API: Moreau identity along `J`, finiteness of both envelope values, existence/uniqueness
  of primal and dual minimizers, and intrinsic-dual optimality characterization.

Layer targets in this file:
- `source-facing` / `core-canonical`: pairing-level declarations below, with explicit `EStar` and
  `J`;
- `bridge/view`: Euclidean self-dual/gradient declarations in the final section.

Scalar note:
- the quadratic kernels are norm-squared and therefore intrinsically `ℝ`-valued, so this item
  stays on the real scalar branch and keeps norm-compatible scalar structure (`NormedSpace`) even
  when the owner is lifted away from `InnerProductSpace`.
-/

-- Proof sketch: combine the Fenchel conjugacy identity for a sum with the self-conjugacy of the
-- quadratic kernels on the primal and dual spaces, then evaluate the dual envelope along the
-- explicit bridge `J`.
/-- Theorem 31.5, pairing-owner form: for a closed proper convex function `f` and an explicit
primal-to-dual bridge `J : E →ₗ[ℝ] EStar`, the primal quadratic Moreau envelope of `f` and the
dual quadratic Moreau envelope of `f⋆`, read along `J`, add up pointwise to `w`. -/
theorem moreau_identity (hf : IsClosedProperConvex[ℝ] f) :
    (primalEnvelope + dualEnvelopeOnPrimal : E → WithBotTop ℝ) = w := sorry

-- Proof sketch: once Moreau's identity identifies `primalEnvelope z + dualEnvelope (J z)`
-- with the finite real value `w z`, the primal term cannot be `⊥` or `⊤`.
/-- The primal quadratic infimal convolution `f □ w` is finite at every point. -/
theorem primal_moreau_envelope_finite
    (hf : IsClosedProperConvex[ℝ] f) (z : E) :
    ⊥ < primalEnvelope z ∧ primalEnvelope z < ⊤ := sorry

-- Proof sketch: apply the same finite-value argument to the conjugate side, evaluated at the
-- dual point `J z`.
/-- The intrinsic dual quadratic infimal convolution of `f⋆` is finite along `J`. -/
theorem dual_moreau_envelope_finite
    (hf : IsClosedProperConvex[ℝ] f) (z : E) :
    ⊥ < dualEnvelope (J z) ∧ dualEnvelope (J z) < ⊤ := sorry

section CompleteSpace

variable [CompleteSpace E] [CompleteSpace EStar]

-- Proof sketch: the quadratic perturbation by `w(z - x)` makes the primal objective strictly
-- convex and coercive on the finite branch, so the infimum defining `(f □ w) z` is attained at a
-- unique point.
/-- For each `z`, the primal infimum defining `(f □ w) z` is attained at a unique minimizer. -/
theorem existsUnique_primal_moreau_minimizer
    (hf : IsClosedProperConvex[ℝ] f) (z : E) :
    ∃! x : E, IsMinOn (fun x : E ↦ f x + w (z - x)) Set.univ x := sorry

-- Proof sketch: the dual Moreau objective lives on the complete dual owner `EStar`,
-- and the dual value is read at the embedded point `J z`.
/-- For each `z`, the dual infimum defining the intrinsic dual Moreau envelope of `f⋆` at
`J z` is attained at a unique minimizer. -/
theorem existsUnique_dual_moreau_minimizer
    (hf : IsClosedProperConvex[ℝ] f) (z : E) :
    ∃! xStar : EStar,
      IsMinOn
        (fun yStar : EStar ↦ fStar yStar + wStar (J z - yStar))
        Set.univ xStar := sorry

-- Proof sketch: the optimality conditions for the two quadratic perturbation problems are the
-- Fenchel-Young subgradient relations for `f` and `f⋆`, linked through the explicit bridge `J`.
-- Eliminating the conjugate-side condition yields the residual identity
-- `xStar = J (z - x)` and intrinsic subgradient membership `xStar ∈ ∂[EStar]f(x)`.
/-- A primal minimizer `x` and an intrinsic dual minimizer `xStar` for the two Moreau envelopes at
the same primal point `z` are characterized exactly by the residual-dual relation
`xStar = J (z - x)` and the intrinsic subgradient condition `xStar ∈ ∂[EStar]f(x)`. -/
theorem primal_and_dual_moreau_minimizers_iff
    (hf : IsClosedProperConvex[ℝ] f) (z x : E) (xStar : EStar) :
    (IsMinOn (fun y : E ↦ f y + w (z - y)) Set.univ x ∧
        IsMinOn
          (fun yStar : EStar ↦ fStar yStar + wStar (J z - yStar))
          Set.univ xStar) ↔
      xStar = J (z - x) ∧ xStar ∈ (∂[EStar]f(x)) := sorry

end CompleteSpace
end

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {f : E → WithBotTop ℝ}

local notation "IsClosedProperConvex[ℝ]" => @Function.IsClosedProperConvex ℝ
local notation "w" => (fun z : E ↦ (((1 / 2 : ℝ) * ‖z‖ ^ 2 : ℝ) : WithBotTop ℝ))
local notation "toDualMap" => (InnerProductSpace.toDualMap ℝ E)

local notation "fStarVec" => (f⋆ : E → WithBotTop ℝ)
local notation "primalEnvelope" => (f □ w : E → WithBotTop ℝ)
local notation "dualEnvelopeVec" => (fStarVec □ w : E → WithBotTop ℝ)
local notation "primalEnvelopeReal" => (Function.realBranch primalEnvelope : E → ℝ)
local notation "dualEnvelopeVecReal" => (Function.realBranch dualEnvelopeVec : E → ℝ)

section CompleteSpace

variable [CompleteSpace E]

-- Proof sketch: transport the intrinsic dual minimizer theorem through the Fréchet-Riesz
-- map `toDualMap` and rewrite the intrinsic subgradient condition using
-- the vector-valued bridge owner `∂ᵥ`.
/-- Euclidean bridge form of Theorem 31.5: a primal minimizer `x` and a dual vector minimizer
`xStar` for the two self-dual Hilbert-space Moreau envelopes at `z` are characterized by
`z = x + xStar` and `xStar ∈ ∂ᵥf(x)`. -/
theorem primal_and_dual_moreau_minimizers_iff_euclidean
    (hf : IsClosedProperConvex[ℝ] f) (z x xStar : E) :
    (IsMinOn (fun y : E ↦ f y + w (z - y)) Set.univ x ∧
        IsMinOn (fun yStar : E ↦ fStarVec yStar + w (z - yStar)) Set.univ xStar) ↔
      z = x + xStar ∧ xStar ∈ ∂ᵥf(x) := sorry

-- Proof sketch: the finite real branch `dualEnvelopeVec.realBranch` is differentiable at every
-- point of the ambient space, and the unique primal minimizer from Theorem 31.5 is the gradient
-- vector given by that differentiability statement.
/-- The finite real branch `((f⋆ □ w).realBranch)` has a gradient at every point. -/
theorem hasGradientAt_dual_moreau_envelope
    (hf : IsClosedProperConvex[ℝ] f) (z : E) :
    HasGradientAt dualEnvelopeVecReal (∇ dualEnvelopeVecReal z) z := sorry

-- Proof sketch: the same differentiability statement holds for the primal Moreau envelope
-- `primalEnvelope.realBranch`, with gradient linked to the intrinsic dual minimizer through
-- `toDualMap`.
/-- The finite real branch `((f □ w).realBranch)` has a gradient at every point. -/
theorem hasGradientAt_primal_moreau_envelope
    (hf : IsClosedProperConvex[ℝ] f) (z : E) :
    HasGradientAt primalEnvelopeReal (∇ primalEnvelopeReal z) z := sorry

-- Proof sketch: combine the previous `HasGradientAt` theorem for `dualEnvelopeVec.realBranch`
-- with the Moreau-Yosida differentiability description to identify its gradient vector with the
-- unique primal minimizer.
/-- The gradient of `((f⋆ □ w).realBranch)` is the unique primal minimizer in Moreau's theorem. -/
theorem gradient_dual_moreau_envelope_is_primal_minimizer
    (hf : IsClosedProperConvex[ℝ] f) (z : E) :
    IsMinOn (fun x : E ↦ f x + w (z - x)) Set.univ
      (∇ dualEnvelopeVecReal z) := sorry

-- Proof sketch: the gradient of the primal envelope branch `primalEnvelope.realBranch` is the
-- unique self-dual Hilbert-space dual minimizer, obtained from the intrinsic dual minimizer
-- through the Fréchet-Riesz bridge map.
/-- The gradient of `((f □ w).realBranch)` is the unique Euclidean dual minimizer in Moreau's
theorem. -/
theorem gradient_primal_moreau_envelope_is_dual_minimizer
    (hf : IsClosedProperConvex[ℝ] f) (z : E) :
    IsMinOn (fun xStar : E ↦ fStarVec xStar + w (z - xStar)) Set.univ
      (∇ primalEnvelopeReal z) := sorry

end CompleteSpace
end
