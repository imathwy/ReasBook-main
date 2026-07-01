import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

/-
`analyticFunctionSubring` is a `bridge/view` declaration: the owner notion in this chapter is
`AnalyticOnNhd`, and this subring packages its restrictions to `D`.
-/
/-- The ring of restrictions to `D` of functions analytic on a neighborhood of `D`. -/
def analyticFunctionSubring
    (𝕜 : Type u) [RCLike 𝕜] (D : Set 𝕜) : Subring (D → 𝕜) where
  carrier := { f | ∃ F : 𝕜 → 𝕜, AnalyticOnNhd 𝕜 F D ∧ D.restrict F = f }
  zero_mem' := by
    refine ⟨0, ?_, rfl⟩
    simpa using (analyticOnNhd_const : AnalyticOnNhd 𝕜 (0 : 𝕜 → 𝕜) D)
  one_mem' := by
    refine ⟨1, ?_, rfl⟩
    simpa using (analyticOnNhd_const : AnalyticOnNhd 𝕜 (1 : 𝕜 → 𝕜) D)
  add_mem' {f g} hf hg := by
    rcases hf with ⟨F, hF, rfl⟩
    rcases hg with ⟨G, hG, rfl⟩
    exact ⟨F + G, hF.add hG, rfl⟩
  mul_mem' {f g} hf hg := by
    rcases hf with ⟨F, hF, rfl⟩
    rcases hg with ⟨G, hG, rfl⟩
    exact ⟨F * G, hF.mul hG, rfl⟩
  neg_mem' {f} hf := by
    rcases hf with ⟨F, hF, rfl⟩
    exact ⟨-F, hF.neg, rfl⟩

instance {𝕜 : Type u} [RCLike 𝕜] {D : Set 𝕜} :
    FunLike ↥(analyticFunctionSubring 𝕜 D) D 𝕜 where
  coe f := f.1
  coe_injective' _ _ h := Subtype.ext h

instance {𝕜 : Type u} [RCLike 𝕜] {D : Set 𝕜} :
    ContinuousMapClass ↥(analyticFunctionSubring 𝕜 D) D 𝕜 where
  map_continuous f := by
    rcases f with ⟨f, hf⟩
    rcases hf with ⟨F, hF, hEq⟩
    simpa [← hEq] using (continuousOn_iff_continuous_restrict.mp hF.continuousOn)

namespace analyticFunctionSubring

@[simp] theorem coe_toContinuousMap
    {𝕜 : Type u} [RCLike 𝕜] {D : Set 𝕜} (f : analyticFunctionSubring 𝕜 D) :
    ⇑(f : C(D, 𝕜)) = (f : D → 𝕜) :=
  ContinuousMap.coe_coe f

@[simp] theorem toContinuousMap_apply
    {𝕜 : Type u} [RCLike 𝕜] {D : Set 𝕜} (f : analyticFunctionSubring 𝕜 D) (z : D) :
    (f : C(D, 𝕜)) z = f z :=
  ContinuousMap.coe_apply f z

/-- On a preconnected set, the ring of analytic restrictions has no zero divisors. -/
instance noZeroDivisors
    {𝕜 : Type u} [RCLike 𝕜] {D : Set 𝕜} (hD : IsPreconnected D)
    : NoZeroDivisors (analyticFunctionSubring 𝕜 D) where
  eq_zero_or_eq_zero_of_mul_eq_zero := by
    intro f g hfg
    rcases f with ⟨f, hf⟩
    rcases g with ⟨g, hg⟩
    have hfg' : f * g = 0 := by
      simpa using Subtype.ext_iff.mp hfg
    rcases hf with ⟨F, hF, rfl⟩
    rcases hg with ⟨G, hG, rfl⟩
    have hmul : ∀ w ∈ D, F w * G w = 0 := by
      intro w hw
      have hw' := congrArg (fun h : D → 𝕜 ↦ h ⟨w, hw⟩) hfg'
      simpa using hw'
    rcases hF.eq_zero_or_eq_zero_of_mul_eq_zero hG hmul hD with h | h
    · left
      ext w
      exact h w w.2
    · right
      ext w
      exact h w w.2

end analyticFunctionSubring

/-- Corollary 1: the ring of functions on a connected set `D` that admit analytic extensions on
`D` is an integral domain. -/
-- Proof sketch: represent two elements of `analyticFunctionSubring 𝕜 D` by ambient analytic
-- functions on `D`; if their product vanishes on `D`, apply
-- `AnalyticOnNhd.eq_zero_or_eq_zero_of_mul_eq_zero` on the connected set `D` to obtain the
-- canonical `NoZeroDivisors` structure on `analyticFunctionSubring 𝕜 D`, then conclude.
theorem analyticFunctionSubring_isDomain
    {𝕜 : Type u} [RCLike 𝕜] {D : Set 𝕜} (hD : IsConnected D) :
    IsDomain (analyticFunctionSubring 𝕜 D) := by
  rcases hD.nonempty with ⟨z, hz⟩
  letI : Nonempty D := ⟨⟨z, hz⟩⟩
  letI := analyticFunctionSubring.noZeroDivisors hD.isPreconnected
  exact NoZeroDivisors.to_isDomain _
