import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap05.Definition_5_24_3
import ConvexAnalysis_Rockafellar_1970.Chap05.Proposition_5_24_1
import ConvexAnalysis_Rockafellar_1970.Chap06.Example_31_5_2

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
