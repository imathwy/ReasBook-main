import BauschkeLean.Chap03.Definition_3_8
import BauschkeLean.Chap03.Theorem_3_16_1
import BauschkeLean.Chap04.Definition_4_1
import BauschkeLean.Chap04.Definition_4_26
import BauschkeLean.Chap04.Proposition_4_23
import BauschkeLean.Chap05.Proposition_5_13
import BauschkeLean.Chap29.Definition_29_24

-- Declarations for this item will be appended below by the statement pipeline.

open Filter Function
open scoped Topology

universe u v

noncomputable section

section

variable {H : Type u} {I : Type v}

/-- The common fixed-point set `⋂ i, Fix(Tᵢ)` of a family `T`. -/
def commonFixedPointSet (T : I → H → H) : Set H :=
  ⋂ i, fixedPoints (T i)

/-- `commonFixedPointSet T` is the intersection `⋂ i, Fix(Tᵢ)`. -/
@[simp] theorem commonFixedPointSet_eq_iInter_fixedPoints (T : I → H → H) :
    commonFixedPointSet T = ⋂ i, fixedPoints (T i) :=
  rfl

/-- Membership in `commonFixedPointSet T` means being fixed by every component of `T`. -/
@[simp] theorem mem_commonFixedPointSet_iff (T : I → H → H) {x : H} :
    x ∈ commonFixedPointSet T ↔ ∀ i, T i x = x := by
  simp [commonFixedPointSet, Function.mem_fixedPoints, Function.IsFixedPt]

/-- The source block-control condition: each block of `m` consecutive iterates contains every index
of the control set `I`. -/
def VisitsEveryIndexInEachBlock (control : ℕ → I) (m : ℕ) : Prop :=
  ∀ j : I, ∀ n : ℕ, ∃ k : Fin m, control (n + k) = j

/-- `VisitsEveryIndexInEachBlock control m` unfolds to the source block-coverage condition. -/
@[simp] theorem visitsEveryIndexInEachBlock_iff (control : ℕ → I) (m : ℕ) :
    VisitsEveryIndexInEachBlock control m ↔
      ∀ j : I, ∀ n : ℕ, ∃ k : Fin m, control (n + k) = j :=
  Iff.rfl

/-- The block-coverage condition already forces the block length to be positive. -/
theorem visitsEveryIndexInEachBlock_pos {control : ℕ → I} {m : ℕ}
    (hcontrol : VisitsEveryIndexInEachBlock control m) :
    0 < m := by
  rcases hcontrol (control 0) 0 with ⟨k, _⟩
  exact k.pos

end

section

variable {H : Type u} [NormedAddCommGroup H]
variable {I : Type v}

-- Semantic recall: `lean_leansearch` only surfaced generic quasiconvex and projection owners, so
-- this item uses the verified local API `specialPolyhedronQ`, `FirmlyQuasinonexpansive`,
-- `DemiclosedAt`, `residualMapOnUniv`, and the metric projection notation `P[C, hC]`. The
-- source's operator class is formalized through the Chapter 4 fixed-point owner
-- `FirmlyQuasinonexpansive`.

/- Source/core/bridge triage:
- `source-facing`: `haugazeauIteration` and Theorem 30.8 itself.
- `core/canonical`: the common fixed-point set is expressed by the ambient fixed-point owner
  `Function.fixedPoints`, and its geometric properties are derived through the Chapter 4/5
  quasinonexpansive fixed-point API together with `isChebyshev_of_nonempty_isClosed_convex`.
- `bridge/view`: `commonFixedPointSet`, `residualMapOnUniv`, and
  `VisitsEveryIndexInEachBlock` package the repeated source-facing surfaces reused by the direct
  Chapter 30 corollaries. -/

/-- The residual map `Id - T` of a self-map `T : H → H`, viewed on the canonical domain
`Set.univ`. -/
def residualMapOnUniv (T : H → H) : {x : H // x ∈ (Set.univ : Set H)} → H :=
  fun x ↦ (x : H) - T (x : H)

/-- `residualMapOnUniv T` acts by `x ↦ x - T x`. -/
@[simp] theorem residualMapOnUniv_apply (T : H → H) (x : {x : H // x ∈ (Set.univ : Set H)}) :
    residualMapOnUniv T x = (x : H) - T x :=
  rfl

variable [InnerProductSpace ℝ H]

/-- The Haugazeau iteration attached to a family of self-maps `T`, a control map
`control : ℕ → I`, and an initial point `x₀`, with recursion
`xₙ₊₁ = Q(x₀, xₙ, T_{control n}(xₙ))`. -/
noncomputable def haugazeauIteration (T : I → H → H) (control : ℕ → I) (x0 : H) : ℕ → H
  | 0 => x0
  | n + 1 =>
      let xn := haugazeauIteration T control x0 n
      specialPolyhedronQ x0 xn (T (control n) xn)

/-- The Haugazeau iteration starts at the prescribed initial point. -/
@[simp] theorem haugazeauIteration_zero (T : I → H → H) (control : ℕ → I) (x0 : H) :
    haugazeauIteration T control x0 0 = x0 := sorry

/-- The Haugazeau iteration satisfies the recursion
`xₙ₊₁ = Q(x₀, xₙ, T_{control n}(xₙ))`. -/
@[simp] theorem haugazeauIteration_succ (T : I → H → H) (control : ℕ → I) (x0 : H) (n : ℕ) :
    haugazeauIteration T control x0 (n + 1) =
      specialPolyhedronQ x0 (haugazeauIteration T control x0 n)
        (T (control n) (haugazeauIteration T control x0 n)) := sorry

/-- The common fixed-point set of a family of firmly quasinonexpansive self-maps is closed and
convex. -/
theorem isClosed_and_convex_commonFixedPointSet_of_firmlyQuasinonexpansive
    (T : I → H → H) (hT : ∀ i, FirmlyQuasinonexpansive (T i)) :
    IsClosed (commonFixedPointSet T) ∧ Convex ℝ (commonFixedPointSet T) := by
  have hfixed : ∀ i, IsClosed (fixedPoints (T i)) ∧ Convex ℝ (fixedPoints (T i)) := by
    intro i
    have hquasi : QuasinonexpansiveOn (Set.univ : Set H) (T i) :=
      quasinonexpansiveOn_univ_of_firmlyQuasinonexpansive (T i) (hT i)
    simpa [fixedPointSetOn_eq_inter_fixedPoints] using
      isClosed_and_convex_fixedPointSetOn_of_quasinonexpansive
        hquasi isClosed_univ convex_univ
  refine ⟨isClosed_iInter (fun i ↦ (hfixed i).1), convex_iInter fun i ↦ (hfixed i).2⟩

end

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {I : Type v}

/-- The common fixed-point set of a family of firmly quasinonexpansive self-maps is
Chebyshev whenever it is nonempty. -/
theorem iInter_fixedPoints_isChebyshev_of_firmlyQuasinonexpansive
    (T : I → H → H) (hT : ∀ i, FirmlyQuasinonexpansive (T i))
    (hC_nonempty : (commonFixedPointSet T).Nonempty) :
    IsChebyshev (commonFixedPointSet T) := by
  exact
    isChebyshev_of_nonempty_isClosed_convex hC_nonempty
      (isClosed_and_convex_commonFixedPointSet_of_firmlyQuasinonexpansive T hT).1
      (isClosed_and_convex_commonFixedPointSet_of_firmlyQuasinonexpansive T hT).2

/-- Theorem 30.8: for a family of firmly quasinonexpansive operators `T`, if every residual map
`Id - T_i` is demiclosed at `0`, if the common fixed-point set
`commonFixedPointSet T = ⋂ i, Fix T_i` is nonempty, and if the control map
`control : ℕ → I` satisfies `VisitsEveryIndexInEachBlock control m` for some block length `m`
(hence automatically `0 < m` by `visitsEveryIndexInEachBlock_pos`), then the Haugazeau
iteration `xₙ₊₁ = Q(x₀, xₙ, T_{control n}(xₙ))` converges strongly to the metric projection of
`x₀` onto `commonFixedPointSet T`. -/
theorem haugazeau_iteration_tendsto_projection_iInter_fixedPoints
    (T : I → H → H) (hT : ∀ i, FirmlyQuasinonexpansive (T i))
    (hDemiclosed : ∀ i, DemiclosedAt (Set.univ : Set H) (residualMapOnUniv (T i)) 0)
    (hC_nonempty : (commonFixedPointSet T).Nonempty)
    {m : ℕ} (control : ℕ → I) (hcontrol : VisitsEveryIndexInEachBlock control m)
    (x0 : H) :
    Tendsto (haugazeauIteration T control x0) atTop
      (𝓝 (P[commonFixedPointSet T,
        iInter_fixedPoints_isChebyshev_of_firmlyQuasinonexpansive T hT hC_nonempty] x0)) := sorry

end
