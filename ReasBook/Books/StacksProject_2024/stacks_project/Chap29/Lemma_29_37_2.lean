import Mathlib
import StacksProject_2024.Chap28.Lemma_28_26_2
import StacksProject_2024.Chap29.Definition_29_37_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

/- Semantic recall / analogue check:
- `lean_leansearch` did not surface a pre-existing relative-ampleness tensor-power theorem in the
  current environment;
- the checked-in local owner for relative ampleness is `AlgebraicGeometry.RelativelyAmple`;
- the dependency `Lemma 28.26.2` already expresses the absolute tensor-power invariance of
  ampleness using the chosen tensor power `hL n` of an invertible module `L`.

The source statement is therefore formalized directly on `RelativelyAmple`, reusing the same
chosen tensor-power interface as Chapter 28. -/

/-- Lemma 29.37.2: for a morphism of schemes `f : X ⟶ S`, an invertible
`\mathcal{O}_X`-module `\mathcal L` is `f`-ample if and only if its positive tensor power
`\mathcal L^{\otimes n}` is `f`-ample. In the current owner interface, the tensor power is the
chosen module `hL n`, equipped with an invertible-module instance in the ambient context. -/
@[stacks 02NN]
theorem relativelyAmple_iff_tensorPow_relativelyAmple
    {X S : Scheme.{u}} {f : X ⟶ S}
    (L : X.Modules) [hL : Scheme.Modules.Invertible L] (n : ℕ) (hn : 0 < n) :
    RelativelyAmple f L ↔ RelativelyAmple f (hL n) := sorry

end AlgebraicGeometry
