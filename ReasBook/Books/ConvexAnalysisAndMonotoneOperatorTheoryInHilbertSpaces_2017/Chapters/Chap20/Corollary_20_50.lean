import BauschkeLean.Chap01.Text_1_0_8
import BauschkeLean.Chap06.Definition_6_38
import BauschkeLean.Chap20.Proposition_20_49

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace Pointwise Set

universe u

namespace SetValuedOperator

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

local notation "OperatorMonotone" => Function.operatorMonotone

/- Source/core/bridge triage:
- `source-facing`: Corollary 20.50 studies an operator `A` that agrees on a closed convex set `C`
  with a continuous single-valued map on `C`; the source assumptions are monotonicity of `A` and
  continuity of the restriction `A|_C`, and the conclusion is maximal monotonicity for `A + N[C]`.
- `core/canonical`: the owner abstractions are the normal cone operator `N[C]`, maximality
  `Maximal`, and the singleton-valued restriction presentation of `A` on `C`.
- `bridge/view`: the present theorem records that restriction presentation through explicit
  singleton equalities `A x = {T ⟨x, hx⟩}` for `x ∈ C`. -/
-- Semantic recall note: `lean_leansearch` did not return a direct owner for this corollary; the
-- verified local canonical bridge is Proposition 20.49 for a continuous single-valued restriction.

-- Proof sketch: extend the continuous subtype map `T : C → H` to an ambient map `T' : H → H`.
-- The pointwise singleton agreement hypothesis on `C` then identifies `A + N[C]` with the
-- canonical singleton-valued restriction of an ambient extension of `T`, since the normal cone is
-- empty off `C`. The continuity of `T` yields hemicontinuity of that extension on `C`, while
-- monotonicity of `A` transfers to the singleton-valued restriction on `C`, so Proposition 20.49
-- applies.
/-- Helper for Corollary 20.50: extend a continuous map on the subtype `C` to an ambient map by
using `0` away from `C`. -/
def ambientExtension {C : Set H} [DecidablePred (· ∈ C)] (T : C → H) : H → H :=
  fun x ↦ if hx : x ∈ C then T ⟨x, hx⟩ else 0

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Corollary 20.50: the ambient extension is continuous on `C`. -/
private lemma ambient_extension_continuousOn {C : Set H} [DecidablePred (· ∈ C)]
    (T : C → H) (hT_cont : Continuous T) :
    ContinuousOn (ambientExtension T) C := by
  -- On the restricted domain `C`, the ambient extension agrees definitionally with `T`.
  rw [continuousOn_iff_continuous_restrict]
  convert hT_cont using 1
  ext x
  simp [ambientExtension]

omit [CompleteSpace H] in
/-- Helper for Corollary 20.50: the ambient extension is hemicontinuous on the convex set `C`. -/
private lemma ambient_extension_hemicontinuousOn {C : Set H} [DecidablePred (· ∈ C)]
    (hC_convex : Convex ℝ C) (T : C → H) (hT_cont : Continuous T) :
    (ambientExtension T).IsHemicontinuousOn C := by
  -- The Chapter 20 bridge turns continuity on a convex set into Rockafellar hemicontinuity.
  exact (ambient_extension_continuousOn T hT_cont).isHemicontinuousOn hC_convex

omit [CompleteSpace H] in
/-- Helper for Corollary 20.50: the singleton-valued restriction coming from the ambient extension
inherits monotonicity from `A`. -/
private lemma ambient_extension_monotone_on {C : Set H} [DecidablePred (· ∈ C)]
    (A : SetValuedOperator H H)
    (hA_mono : OperatorMonotone A) (T : C → H)
    (hA_eq : ∀ x, ∀ hx : x ∈ C, A x = ({T ⟨x, hx⟩} : Set H)) :
    Function.operatorMonotone ((ambientExtension T).toSetValuedOperatorOn C) := by
  intro x u y v hu hv
  -- Membership in the singleton-valued restriction forces both base points to lie in `C`.
  have hx : x ∈ C := by
    by_contra hx
    simp [Function.toSetValuedOperatorOn, hx] at hu
  have hy : y ∈ C := by
    by_contra hy
    simp [Function.toSetValuedOperatorOn, hy] at hv
  -- Rewrite both singleton fibers back through the original operator `A`.
  have huA : u ∈ A x := by
    rw [hA_eq x hx]
    simpa [Function.toSetValuedOperatorOn, ambientExtension, hx] using hu
  have hvA : v ∈ A y := by
    rw [hA_eq y hy]
    simpa [Function.toSetValuedOperatorOn, ambientExtension, hy] using hv
  exact hA_mono huA hvA

omit [CompleteSpace H] in
/-- Helper for Corollary 20.50: the original sum operator agrees with the ambient-extension model
used in Proposition 20.49. -/
private lemma add_normalCone_eq_ambient_extension_add_normalCone {C : Set H}
    [DecidablePred (· ∈ C)]
    (A : SetValuedOperator H H) (T : C → H)
    (hA_eq : ∀ x, ∀ hx : x ∈ C, A x = ({T ⟨x, hx⟩} : Set H)) :
    A + N[C] = (ambientExtension T).toSetValuedOperatorOn C + N[C] := by
  funext x
  by_cases hx : x ∈ C
  · -- On `C`, both operators have the same singleton fiber, so the sums coincide pointwise.
    simp [Function.toSetValuedOperatorOn, ambientExtension, hA_eq x hx, hx]
  · -- Off `C`, the normal cone vanishes, so both sums are empty.
    simp [Function.toSetValuedOperatorOn, Set.normalCone_of_not_mem hx, hx]

/-- Corollary 20.50: if `C` is a nonempty closed convex subset of a real Hilbert space, if `A` is
a monotone set-valued operator, and if on `C` the operator `A` is represented by a continuous
single-valued map `T : C → H`, then `A + N[C]` is maximally monotone. -/
theorem add_normalCone_isMaximallyMonotone_of_monotone_of_eq_singleton_continuous
    {C : Set H} (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    (A : SetValuedOperator H H) (hA_mono : OperatorMonotone A) (T : C → H)
    (hA_eq : ∀ x, ∀ hx : x ∈ C, A x = ({T ⟨x, hx⟩} : Set H)) (hT_cont : Continuous T) :
    Maximal OperatorMonotone (A + N[C]) := by
  classical
  let T_ext : H → H := ambientExtension T
  have hT_ext_mono : Function.operatorMonotone (T_ext.toSetValuedOperatorOn C) := by
    -- The singleton-valued restriction of the ambient extension inherits monotonicity from `A`.
    simpa [T_ext] using ambient_extension_monotone_on A hA_mono T hA_eq
  have hT_ext_hemi : T_ext.IsHemicontinuousOn C := by
    -- Continuity of the subtype map gives hemicontinuity on the convex set `C`.
    simpa [T_ext] using ambient_extension_hemicontinuousOn hC_convex T hT_cont
  have hsum_eq : A + N[C] = T_ext.toSetValuedOperatorOn C + N[C] := by
    -- The ambient-extension model matches `A + N[C]` because `N[C]` is empty off `C`.
    simpa [T_ext] using add_normalCone_eq_ambient_extension_add_normalCone A T hA_eq
  -- Rewrite the target to the Proposition 20.49 model and apply the maximality theorem there.
  change Maximal Function.operatorMonotone (A + N[C])
  rw [hsum_eq]
  exact Function.ofFunction_add_normalCone_isMaximallyMonotone_of_monotoneOn_hemicontinuousOn
    hC_nonempty hC_closed hC_convex T_ext hT_ext_mono hT_ext_hemi

end SetValuedOperator
