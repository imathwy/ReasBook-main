import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Manifold

universe u

section

variable (X : Type u) [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]

private noncomputable abbrev chartExpression (x : X) (f : X → ℂ) : ℂ → ℂ :=
  writtenInExtChartAt 𝓘(ℂ) 𝓘(ℂ) x f

private def IsMeromorphic (f : X → ℂ) : Prop :=
  ∀ x, MeromorphicAt (chartExpression X x f) (extChartAt 𝓘(ℂ) x x)

private def meromorphicSubalgebra : Subalgebra ℂ (X → ℂ) where
  carrier := {f | IsMeromorphic X f}
  zero_mem' := by
    intro x
    change MeromorphicAt (fun _ : ℂ ↦ (0 : ℂ)) ((chartAt ℂ x) x)
    exact MeromorphicAt.const (0 : ℂ) ((chartAt ℂ x) x)
  add_mem' := by
    intro f g hf hg x
    simpa [IsMeromorphic, writtenInExtChartAt, Function.comp] using (hf x).add (hg x)
  one_mem' := by
    intro x
    change MeromorphicAt (fun _ : ℂ ↦ (1 : ℂ)) ((chartAt ℂ x) x)
    exact MeromorphicAt.const (1 : ℂ) ((chartAt ℂ x) x)
  mul_mem' := by
    intro f g hf hg x
    simpa [IsMeromorphic, writtenInExtChartAt, Function.comp] using (hf x).mul (hg x)
  algebraMap_mem' := by
    intro c x
    change MeromorphicAt (fun _ : ℂ ↦ c) ((chartAt ℂ x) x)
    exact MeromorphicAt.const c ((chartAt ℂ x) x)

omit [IsManifold 𝓘(ℂ) 1 X] in
private theorem isMeromorphic_inv {f : X → ℂ} (hf : IsMeromorphic X f) :
    IsMeromorphic X f⁻¹ := by
  intro x
  change MeromorphicAt ((chartExpression X x f)⁻¹) ((chartAt ℂ x) x)
  simpa [IsMeromorphic, chartExpression] using (hf x).inv

private noncomputable instance : Inv ↥(meromorphicSubalgebra X) where
  inv f := ⟨(f : X → ℂ)⁻¹, isMeromorphic_inv X f.property⟩

private def meromorphicCon : RingCon ↥(meromorphicSubalgebra X) where
  r f g := (f : X → ℂ) =ᶠ[Filter.codiscrete X] (g : X → ℂ)
  iseqv := ⟨fun f ↦ Filter.EventuallyEq.rfl, fun h ↦ h.symm, fun h₁ h₂ ↦ h₁.trans h₂⟩
  add' := by
    intro a b c d hab hcd
    exact hab.add hcd
  mul' := by
    intro a b c d hab hcd
    exact hab.mul hcd

/-- The meromorphic function field `ℂ(X)`, realized as meromorphic representatives modulo
codiscrete equality, which forgets inessential point values at isolated poles. -/
abbrev MeromorphicFunctionField := RingCon.Quotient (meromorphicCon X)

end

notation:max "ℂ(" X ")" => MeromorphicFunctionField X

section

variable (X : Type u) [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
  [ConnectedSpace X]

private theorem meromorphicFunctionField_zero_ne_one :
    (0 : ℂ(X)) ≠ 1 := by
  sorry

noncomputable instance : Nontrivial (ℂ(X)) :=
  ⟨0, 1, meromorphicFunctionField_zero_ne_one X⟩

private theorem meromorphicFunctionField_isUnit_or_eq_zero (f : ℂ(X)) :
    IsUnit f ∨ f = 0 := by
  sorry

noncomputable instance : Field (ℂ(X)) :=
  Field.ofIsUnitOrEqZero fun f ↦ meromorphicFunctionField_isUnit_or_eq_zero X f

/- Example 9.3.6: the meromorphic function field `ℂ(X)` of a connected Riemann surface carries
its canonical field structure. -/
#check (inferInstance : Field (ℂ(X)))

end
