import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Topology.Covering.Basic
import SmoothManifoldsLee.Chap04.Sec04_22.Exercise_4_10
import SmoothManifoldsLee.Chap04.Sec04_25.Definition_4_25_extra_1
import SmoothManifoldsLee.Chap04.Sec04_25.Theorem_4_26
import SmoothManifoldsLee.Chap04.Sec04_26.Definition_4_26_extra_1

-- Declarations for this item will be appended below by the statement pipeline.

open Bundle
open scoped Manifold ContDiff

universe uK uVE uVM uHE uHM uE uM

section

variable {E : Type uE} [TopologicalSpace E]
variable {M : Type uM} [TopologicalSpace M]

namespace IsCoveringMap

/-- On a preconnected open subset `U` of the base of a covering map, two continuous local
sections that agree at one point agree everywhere on `U`. -/
theorem localSection_eq {pi : E → M} (hpi : IsCoveringMap pi) {U : TopologicalSpace.Opens M}
    (hU : IsPreconnected (U : Set M)) {q : U} {σ σ' : U → E}
    (hσ : Continuous σ) (hσ' : Continuous σ') (hsec : ∀ x : U, pi (σ x) = x)
    (hsec' : ∀ x : U, pi (σ' x) = x) (hqq : σ q = σ' q) :
    σ = σ' := by
  let _ : PreconnectedSpace U := Subtype.preconnectedSpace hU
  refine hpi.eq_of_comp_eq hσ hσ' ?_ q hqq
  funext x
  exact (hsec x).trans (hsec' x).symm

/-- Helper for Proposition 4.36: an evenly covered open subset carries a continuous local section
through any prescribed point of the chosen fiber. -/
theorem exists_localSectionOn {pi : E → M} (hpi : IsCoveringMap pi) {q : M}
    (t : Trivialization (pi ⁻¹' {q}) pi) (hq : q ∈ t.baseSet) {p : E}
    (hp : p ∈ pi ⁻¹' {q}) :
    let U : TopologicalSpace.Opens M := ⟨t.baseSet, t.open_baseSet⟩
    ∃ σ : C(U, E), (⟨pi, hpi.continuous⟩ : C(E, M)).IsLocalSection U σ ∧ σ ⟨q, hq⟩ = p := by
  let U : TopologicalSpace.Opens M := ⟨t.baseSet, t.open_baseSet⟩
  have hp_eq : pi p = q := by
    simpa [Set.mem_preimage, Set.mem_singleton_iff] using hp
  have hp_base : pi p ∈ t.baseSet := by
    simpa [hp_eq] using hq
  have hmain :
      ∃ σ : C(U, E), (⟨pi, hpi.continuous⟩ : C(E, M)).IsLocalSection U σ ∧ σ ⟨q, hq⟩ = p := by
    -- Fix the sheet of `p` inside the trivialization and lift each base point along that sheet.
    have hσ_cont : Continuous fun x : U => t.lift p x := by
      have hgraph : Continuous fun x : U => ((x : M), (t p).2) := by
        exact continuous_subtype_val.prodMk continuous_const
      have htarget : ∀ x : U, ((x : M), (t p).2) ∈ t.target := by
        intro x
        exact t.mem_target.2 x.2
      -- Continuity comes from composing the inverse trivialization with the fixed-sheet graph.
      simpa [Bundle.Trivialization.lift] using
        t.continuousOn_invFun.comp_continuous hgraph htarget
    let σ : C(U, E) := ⟨fun x => t.lift p x, hσ_cont⟩
    have hσ_sec : (⟨pi, hpi.continuous⟩ : C(E, M)).IsLocalSection U σ := by
      -- The fixed-sheet lift is a right inverse to `pi` on the evenly covered base set.
      intro x
      simpa [σ] using t.proj_lift (z := p) (b := (x : M)) x.2
    have hσq : σ ⟨q, hq⟩ = p := by
      -- Over the point `q = pi p`, lifting along the sheet of `p` returns `p` itself.
      simpa [σ, hp_eq] using t.lift_self (z := p) hp_base
    exact ⟨σ, hσ_sec, hσq⟩
  simpa [U] using hmain

end IsCoveringMap

end

section

variable {K : Type uK} [NontriviallyNormedField K]
variable {VE : Type uVE} [NormedAddCommGroup VE] [NormedSpace K VE]
variable {VM : Type uVM} [NormedAddCommGroup VM] [NormedSpace K VM]
variable {HE : Type uHE} [TopologicalSpace HE]
variable {HM : Type uHM} [TopologicalSpace HM]
variable (IE : ModelWithCorners K VE HE) (IM : ModelWithCorners K VM HM)
variable {E : Type uE} [TopologicalSpace E] [ChartedSpace HE E]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace HM M]

namespace Manifold.IsSmoothCoveringMap

/-- Proposition 4.36 (1): on an evenly covered open subset `U`, a smooth covering map has a smooth
local section through any chosen point `p` of the fiber over `q`. -/
-- Proof sketch: let `i` be the sheet coordinate of `p` in the chosen trivialization `t`, and
-- define a continuous local section on `t.baseSet` by `x ↦ t.invFun (x, i)`. Smoothness then
-- follows from `hπ.localSection_contMDiffOn`.
theorem exists_localSectionOn
    {pi : E → M} (hpi : Manifold.IsSmoothCoveringMap IE IM pi) {q : M}
    (t : Trivialization (pi ⁻¹' {q}) pi) (hq : q ∈ t.baseSet) {p : E}
    (hp : p ∈ pi ⁻¹' {q}) :
    let U : TopologicalSpace.Opens M := ⟨t.baseSet, t.open_baseSet⟩
    ∃ σ : U → E, Manifold.IsSmoothLocalSection IE IM pi U σ ∧ σ ⟨q, hq⟩ = p :=
  by
  let U : TopologicalSpace.Opens M := ⟨t.baseSet, t.open_baseSet⟩
  have htop :
      ∃ σ : C(U, E), (⟨pi, hpi.isCoveringMap.continuous⟩ : C(E, M)).IsLocalSection U σ ∧
        σ ⟨q, hq⟩ = p := by
    simpa [U] using hpi.isCoveringMap.exists_localSectionOn (q := q) t hq hp
  rcases htop with ⟨σ, hσ, hσq⟩
  have hsmooth : ContMDiff IM IE ∞ σ := by
    have hcomp : pi ∘ σ = Subtype.val := by
      funext x
      exact hσ x
    -- Smoothness is detected after composing with the smooth local diffeomorphism `pi`.
    refine (smooth_iff_comp_left_of_isLocalDiffeomorph hpi.isLocalDiffeomorph σ.continuous).mpr ?_
    simpa [hcomp] using
      (contMDiff_subtype_val : ContMDiff IM IM ∞ (Subtype.val : U → M))
  have hmain : ∃ σ : U → E, Manifold.IsSmoothLocalSection IE IM pi U σ ∧ σ ⟨q, hq⟩ = p := by
    -- Package the continuous section together with the smoothness upgrade.
    exact ⟨σ, ⟨hsmooth, hσ⟩, hσq⟩
  simpa [U] using hmain

/-- Proposition 4.36 (2): on a preconnected open subset `U` of the base of a smooth covering map,
any two smooth local sections that agree at one point agree on all of `U`. -/
-- Proof sketch: apply the topological covering-space uniqueness theorem
-- `IsCoveringMap.localSection_eq` to the underlying continuous local sections.
theorem localSection_eq
    {pi : E → M} (hpi : Manifold.IsSmoothCoveringMap IE IM pi) {U : TopologicalSpace.Opens M}
    (hU : IsPreconnected (U : Set M)) {q : U} {σ σ' : U → E}
    (hσ : Manifold.IsSmoothLocalSection IE IM pi U σ)
    (hσ' : Manifold.IsSmoothLocalSection IE IM pi U σ') (hqq : σ q = σ' q) :
    σ = σ' := by
  exact hpi.isCoveringMap.localSection_eq hU hσ.1.continuous hσ'.1.continuous
    hσ.apply_eq hσ'.apply_eq hqq

end Manifold.IsSmoothCoveringMap

end
