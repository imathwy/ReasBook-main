import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory HomologicalComplex

universe v u

variable {V : Type u} [Category.{v} V] [Preadditive V]

/- Domain-style sampling:
- primary domain: homotopies of homological complexes in a preadditive category
- sampled canonical owner declarations:
  `Homotopy`,
  `Homotopy.compLeft`,
  `Homotopy.compRight`,
  `Homotopy.compLeft_hom`,
  `Homotopy.compRight_hom`
- best owner abstraction: `Homotopy` on `HomologicalComplex V c`
- primitive data: the fields `hom`, `zero`, and `comm` of a homotopy
- derived API: closure under precomposition and postcomposition, together with the degreewise
  component lemmas `Homotopy.compLeft_hom` and `Homotopy.compRight_hom`
- source/core/bridge triage:
  `core/canonical`: `Homotopy` and its composition operations on `HomologicalComplex`,
  `bridge/view`: the cochain-complex whiskering statement obtained by combining
  `Homotopy.compLeft` and `Homotopy.compRight`

Lemma 12.13.7 is not just a recall of the separate owner operations: it is the thin cochain-side
bridge that packages both whiskerings into the specific homotopy with components
`a.f i ≫ h.hom i (i - 1) ≫ c.f (i - 1)`.
-/

namespace Homotopy

variable {A B C D : CochainComplex V ℤ} {a : A ⟶ B} {f g : B ⟶ C} {c : C ⟶ D}

/-- Lemma 12.13.7: if `h : Homotopy f g`, then whiskering `h` on the left by `a` and on the right
by `c` gives a homotopy from `((a ≫ f) ≫ c)` to `((a ≫ g) ≫ c)`, corresponding to the source
notation `c ∘ f ∘ a` and `c ∘ g ∘ a`. -/
@[stacks 0112]
def cochainWhisker (a : A ⟶ B) (h : Homotopy f g) (c : C ⟶ D) :
    Homotopy ((a ≫ f) ≫ c) ((a ≫ g) ≫ c) :=
  (h.compLeft a).compRight c

/-- The degree-`i` component of `cochainWhisker h` corresponds to the source formula
`c^{i - 1} ∘ h^i ∘ a^i`; in Lean this is
`a.f i ≫ h.hom i (i - 1) ≫ c.f (i - 1)`. -/
theorem cochainWhisker_hom (h : Homotopy f g) (i : ℤ) :
    (cochainWhisker a h c).hom i (i - 1) =
      a.f i ≫ h.hom i (i - 1) ≫ c.f (i - 1) := by
  simp [cochainWhisker]

end Homotopy
