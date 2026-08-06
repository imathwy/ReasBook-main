import Mathlib.Algebra.Ring.Basic
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap23.Theorem_23_7_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap24.Proposition_24_1_8

open CategoryTheory

universe u

/-- The actual `K`-theory class `[L]` of a bundled complex line bundle `L`. -/
noncomputable abbrev lineBundleKTheoryClass
    {X : Type u} [TopologicalSpace X] (L : ComplexPlaneBundle 1 X) :
    complexKTheory X :=
  ComplexVectorBundle.toVirtualPresentation
    (ComplexVectorBundle.Presentation.ofFamily (Fin 1 → ℂ) L.fiber)

theorem lineBundleKTheoryClass_def
    {X : Type u} [TopologicalSpace X] (L : ComplexPlaneBundle 1 X) :
    lineBundleKTheoryClass L =
      ComplexVectorBundle.toVirtualPresentation
        (ComplexVectorBundle.Presentation.ofFamily (Fin 1 → ℂ) L.fiber) :=
  rfl

/-- The nonzero integers. -/
abbrev NonzeroInt := {k : ℤ // k ≠ 0}

namespace NonzeroInt

instance : One NonzeroInt := ⟨⟨1, by decide⟩⟩

instance : Mul NonzeroInt := ⟨fun k l ↦ ⟨(k : ℤ) * l, mul_ne_zero k.2 l.2⟩⟩

@[simp] theorem coe_one : ((1 : NonzeroInt) : ℤ) = 1 := rfl

@[simp] theorem coe_mul (k l : NonzeroInt) : ((k * l : NonzeroInt) : ℤ) = (k : ℤ) * l := rfl

end NonzeroInt

/-- A family of candidate Adams operations `ψ^k : K(X) → K(X)` on `complexKTheory`, indexed by
nonzero integers. -/
abbrev ComplexKTheoryAdamsFamily :=
  ∀ (X : Type u) [TopologicalSpace X] [CompactSpace X],
    NonzeroInt → complexKTheory X →+* complexKTheory X

namespace ComplexKTheoryAdamsFamily

variable (ψ : ComplexKTheoryAdamsFamily)
variable (X : Type u) [TopologicalSpace X] [CompactSpace X]

/-- For fixed `X`, `ComplexKTheoryAdamsFamily.op ψ X k` is the Adams operation
`ψ^k : K(X) → K(X)`. -/
abbrev op (k : NonzeroInt) : complexKTheory X →+* complexKTheory X :=
  ψ X k

@[simp] theorem op_apply (k : NonzeroInt) (ξ : complexKTheory X) :
    ComplexKTheoryAdamsFamily.op ψ X k ξ = ψ X k ξ :=
  rfl

end ComplexKTheoryAdamsFamily

namespace ComplexKTheoryAdams

/-- The Lean notation `ψ ^[k]` denotes the Adams operation `ψ^k` on the ambient `complexKTheory`
space. -/
scoped notation:max ψ " ^[" k:max "]" => ComplexKTheoryAdamsFamily.op ψ _ k

end ComplexKTheoryAdams

open scoped ComplexKTheoryAdams

/-- `unitZPow u k` is the image in `complexKTheory X` of the integral power `u ^ k`. -/
noncomputable abbrev unitZPow
    {X : Type u} [TopologicalSpace X]
    (u : Units (complexKTheory X)) (k : ℤ) : complexKTheory X :=
  ((u ^ k : Units (complexKTheory X)) : complexKTheory X)

/-- `unitPow u k` is the image in `complexKTheory X` of the nonzero-integer power `u ^ k`. -/
noncomputable abbrev unitPow
    {X : Type u} [TopologicalSpace X]
    (u : Units (complexKTheory X)) (k : NonzeroInt) : complexKTheory X :=
  unitZPow u (k : ℤ)

@[simp] theorem unitPow_def
    {X : Type u} [TopologicalSpace X]
    (u : Units (complexKTheory X)) (k : NonzeroInt) :
    unitPow u k = unitZPow u (k : ℤ) :=
  rfl

/-- `IsLineBundleKTheoryLift L u` means that `u` is a unit lift of the line-bundle class `[L]`. -/
def IsLineBundleKTheoryLift
    {X : Type u} [TopologicalSpace X]
    (L : ComplexPlaneBundle 1 X) (u : Units (complexKTheory X)) : Prop :=
  (u : complexKTheory X) = lineBundleKTheoryClass L

namespace IsLineBundleKTheoryLift

/-- Any two unit lifts of `[L]` agree. -/
theorem ext
    {X : Type u} [TopologicalSpace X]
    {L : ComplexPlaneBundle 1 X} {u v : Units (complexKTheory X)}
    (hu : IsLineBundleKTheoryLift L u) (hv : IsLineBundleKTheoryLift L v) :
    u = v := by
  apply Units.ext
  simpa [IsLineBundleKTheoryLift] using hu.trans hv.symm

end IsLineBundleKTheoryLift

/-- `IsLineBundleKTheoryPower L k ξ` means that `ξ` is the `k`th power of the line-bundle class
`[L]` in `complexKTheory X`. The witness is an internal unit lift of `[L]`, so the public API does
not choose one. -/
def IsLineBundleKTheoryPower
    {X : Type u} [TopologicalSpace X]
    (L : ComplexPlaneBundle 1 X) (k : NonzeroInt) (ξ : complexKTheory X) : Prop :=
  ∃ u : Units (complexKTheory X), IsLineBundleKTheoryLift L u ∧ ξ = unitPow u k

namespace IsLineBundleKTheoryPower

/-- It suffices to verify the `k`th-power formula for one unit lift of `[L]`. -/
theorem of_eq_pow
    {X : Type u} [TopologicalSpace X]
    {L : ComplexPlaneBundle 1 X} {k : NonzeroInt} {ξ : complexKTheory X}
    {u : Units (complexKTheory X)} (hu : IsLineBundleKTheoryLift L u)
    (hξ : ξ = unitPow u k) :
    IsLineBundleKTheoryPower L k ξ := by
  exact ⟨u, hu, hξ⟩

/-- If `ξ` is the `k`th power of `[L]`, then it equals the `k`th power of any unit lift of
`lineBundleKTheoryClass L`. -/
theorem eq_pow
    {X : Type u} [TopologicalSpace X]
    {L : ComplexPlaneBundle 1 X} {k : NonzeroInt} {ξ : complexKTheory X}
    (hξ : IsLineBundleKTheoryPower L k ξ)
    {u : Units (complexKTheory X)} (hu : IsLineBundleKTheoryLift L u) :
    ξ = unitPow u k := by
  rcases hξ with ⟨v, hv, rfl⟩
  have hvu : v = u := IsLineBundleKTheoryLift.ext hv hu
  simp [hvu]

/-- `IsLineBundleKTheoryPower` provides a unit lift witnessing the power formula. -/
theorem exists_eq_pow
    {X : Type u} [TopologicalSpace X]
    {L : ComplexPlaneBundle 1 X} {k : NonzeroInt} {ξ : complexKTheory X}
    (hξ : IsLineBundleKTheoryPower L k ξ) :
    ∃ u : Units (complexKTheory X), IsLineBundleKTheoryLift L u ∧ ξ = unitPow u k :=
  hξ

end IsLineBundleKTheoryPower

/-- The companion laws asserting that a chosen Adams-operation family satisfies the Adams
operation axioms. -/
structure IsComplexKTheoryAdams (ψ : ComplexKTheoryAdamsFamily.{u}) : Prop where
  /-- The Adams operations are natural with respect to pullback in `complexKTheory`. -/
  naturality
      {X Y : Type u} [TopologicalSpace X] [CompactSpace X]
      [TopologicalSpace Y] [CompactSpace Y]
      (f : TopCat.of Y ⟶ TopCat.of X)
      (fStar : complexKTheory X →+* complexKTheory Y)
      (hfStar : IsComplexKTheoryPresentationPullback f fStar) (k : NonzeroInt) :
      fStar.comp (ψ ^[k]) = (ψ ^[k]).comp fStar
  /-- The normalization `ψ^1 = id`. -/
  one
      (X : Type u) [TopologicalSpace X] [CompactSpace X] :
      ψ ^[(1 : NonzeroInt)] = RingHom.id (complexKTheory X)
  /-- The multiplicativity relation `ψ^k ∘ ψ^l = ψ^(k * l)`. -/
  mul
      (X : Type u) [TopologicalSpace X] [CompactSpace X]
      (k l : NonzeroInt) :
      (ψ X k).comp (ψ X l) = ψ X (k * l)
  /-- On line-bundle classes, `ψ^k` is the `k`th power of the line-bundle class. -/
  lineBundle
      (X : Type u) [TopologicalSpace X] [CompactSpace X]
      (L : ComplexPlaneBundle 1 X) (k : NonzeroInt) :
      IsLineBundleKTheoryPower L k ((ψ ^[k]) (lineBundleKTheoryClass L))

namespace IsComplexKTheoryAdams

/-- The Adams operation `ψ^1` is the identity on `K(X)`. -/
@[simp] theorem one_eq_id
    {ψ : ComplexKTheoryAdamsFamily} (hψ : IsComplexKTheoryAdams ψ)
    (X : Type u) [TopologicalSpace X] [CompactSpace X] :
    ψ ^[(1 : NonzeroInt)] = RingHom.id (complexKTheory X) :=
  hψ.one X

/-- On line-bundle classes, `ψ^k` agrees with the `k`th power for any chosen unit lift of
`lineBundleKTheoryClass L`. -/
theorem lineBundle_eq_pow
    {ψ : ComplexKTheoryAdamsFamily} (hψ : IsComplexKTheoryAdams ψ)
    (X : Type u) [TopologicalSpace X] [CompactSpace X]
    (L : ComplexPlaneBundle 1 X) (k : NonzeroInt)
    {u : Units (complexKTheory X)} (hu : IsLineBundleKTheoryLift L u) :
    (ψ ^[k]) (lineBundleKTheoryClass L) = unitPow u k :=
  IsLineBundleKTheoryPower.eq_pow (hψ.lineBundle X L k) hu

end IsComplexKTheoryAdams
