import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section14_part2

/-- The pointwise supremum of all lower semicontinuous minorants of an `EReal`-valued function. -/
noncomputable def erealLowerSemicontinuousHull
    {X : Type*} [TopologicalSpace X] (f : X → EReal) : X → EReal :=
  fun x =>
    ⨆ h : {h : X → EReal // LowerSemicontinuous h ∧ h ≤ f}, h.1 x

/-- The book-style closure of an `EReal`-valued function: the lower semicontinuous hull when the
function never takes the value `-∞`, and the constant function `-∞` otherwise. -/
noncomputable def erealFunctionClosure
    {X : Type*} [TopologicalSpace X] (f : X → EReal) : X → EReal :=
  letI : Decidable (∀ x, f x ≠ (⊥ : EReal)) := Classical.propDecidable _
  if (∀ x, f x ≠ (⊥ : EReal)) then
    erealLowerSemicontinuousHull f
  else
    fun _ => (⊥ : EReal)

/-- The book-style closure of a bifunction, defined as the closure of the associated function on
the product and then uncurrying back. -/
noncomputable def bifunctionClosure
    {U X : Type*} [TopologicalSpace U] [TopologicalSpace X] (F : U → X → EReal) : U → X → EReal :=
  fun u x => erealFunctionClosure (fun p : U × X => F p.1 p.2) (u, x)
