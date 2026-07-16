import StacksProject_2024.stacks_project.Chap28.Definition_28_26_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

/- Semantic recall: `lean_leansearch` did not expose a packaged tensor-power ampleness owner in the
current project. The Chapter 28 owner already records ampleness as `Scheme.Modules.IsAmple`, the
chosen positive tensor powers of an invertible module through the source-facing family `hL n`, and
their canonical invertibility in `Invertible.instInvertibleTensorPow`, so the statement is
expressed directly on that interface. -/

variable {X : Scheme.{u}}
variable [CategoryTheory.MonoidalCategory X.Modules]

/-- Lemma 28.26.2: for a scheme `X`, an invertible `\mathcal{O}_X`-module `L` is ample if and
only if its positive tensor power `L^{\otimes n}` is ample. In the current Chapter 28 owner
interface, the tensor power is the chosen module `hL n`, carrying its canonical invertible-module
instance from Definition 28.26.1. -/
@[stacks 01PT]
theorem isAmple_iff_tensorPow_isAmple
    (L : X.Modules) [hL : Invertible L] (n : ℕ) (hn : 0 < n)
    : IsAmple L ↔ IsAmple (hL n) := sorry

/-- If an invertible `\mathcal O_X`-module is ample, then every positive chosen tensor power is
ample. -/
theorem IsAmple.tensorPow
    {L : X.Modules} [hL : Invertible L] (hA : IsAmple L)
    {n : ℕ} (hn : 0 < n) :
    IsAmple (hL n) :=
  (isAmple_iff_tensorPow_isAmple L n hn).1 hA

/-- If a positive chosen tensor power of an invertible `\mathcal O_X`-module is ample, then the
module itself is ample. -/
theorem IsAmple.of_tensorPow
    {L : X.Modules} [hL : Invertible L]
    {n : ℕ} (hn : 0 < n)
    (hA : IsAmple (hL n)) :
    IsAmple L :=
  (isAmple_iff_tensorPow_isAmple L n hn).2 hA

end AlgebraicGeometry.Scheme.Modules
