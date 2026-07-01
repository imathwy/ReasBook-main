import Mathlib
import stacks_project.Chap04.Example_4_22_6

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open SequentialProObjectMorphismRep
open scoped CategoryTheory ZeroObject

universe uC vC uD vD

namespace CategoryTheory

/-
Domain-style sampling for Lemma 13.42.4:
- primary domain: sequential inverse systems in a pretriangulated category, viewed through the
  Chapter 4 owner for sequential pro-object morphisms and the Hom-colimit functor
  `X ↦ colimₙ Hom(-, X)`.
- inspected owner-level declarations:
  `HasProObjectValue`,
  `SequentialProObjectMorphismRep`,
  `SequentialProObjectMorphismRep.IsProIsomorphism`,
  `SequentialProObjectMorphismRep.ofOrderDualNatTrans`,
  `SequentialProObjectMorphismRep.toProObjectHom`,
  `SequentialProObjectMorphismRep.isProIsomorphism_toProObjectHom_app_bijective`,
  `Functor.whiskerLeft`,
  `Triangle.π₁Toπ₂`.
- best owner abstraction: the sequential pro-object morphism represented by the first maps in the
  triangle system, obtained from `Functor.whiskerLeft T Triangle.π₁Toπ₂` via
  `SequentialProObjectMorphismRep.ofOrderDualNatTrans`; the source-facing owner statement is that
  this representative is a pro-isomorphism, and its evaluation on a test object is the canonical
  Hom-colimit map after passing to the standard `ℕᵒᵖ` presentation of the sequential system.
- primitive data: the triangle system `T`, the first-to-second natural transformation
  `Functor.whiskerLeft T Triangle.π₁Toπ₂`.
- derived API: the pro-isomorphism owner
  `(SequentialProObjectMorphismRep.ofOrderDualNatTrans ...).IsProIsomorphism`, its evaluated
  morphism `(SequentialProObjectMorphismRep.ofOrderDualNatTrans ...).toProObjectHom.app X`, and
  the source-facing pro-zero condition `HasProObjectValue (T ⋙ Triangle.π₃) (0 : D)`.

Source/core/bridge triage:
- `source-facing`: the theorem below, asserting that a pro-zero third term system forces the maps
  `Aₙ ⟶ Bₙ` to define a pro-isomorphism.
- `core/canonical`: `HasProObjectValue` and `SequentialProObjectMorphismRep`.
- `bridge/view`: `SequentialProObjectMorphismRep.ofOrderDualNatTrans` and
  `SequentialProObjectMorphismRep.toProObjectHom`. -/

section

variable {D : Type uD} [Category.{vD} D] [HasZeroObject D] [Preadditive D] [HasShift D ℤ]
  [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D]
variable {T : OrderDual ℕ ⥤ Triangle D}

-- Proof sketch: for each test object `X`, apply the homological functor `Hom(-, X)` to every
-- distinguished triangle in the system to obtain an exact sequence of filtered colimits. Lemma
-- 10.8.8 gives exactness after passing to colimits, and the pro-zero hypothesis on `(Cₙ)` forces
-- the first and last colimit terms to vanish. Hence the middle map
-- `colimₙ Hom(Bₙ, X) → colimₙ Hom(Aₙ, X)` is bijective for every `X`, which is the Hom-colimit
-- form of the claimed pro-isomorphism by Remark 4.22.7.
/-- Lemma 13.42.4: for a sequential inverse system of distinguished triangles
`Aₙ ⟶ Bₙ ⟶ Cₙ ⟶ Aₙ⟦1⟧`, if the system `(Cₙ)` is essentially constant as a pro-object with value
`0`, then the maps `Aₙ ⟶ Bₙ` determine a pro-isomorphism between the pro-objects `(Aₙ)` and
`(Bₙ)`. -/
theorem triangleFirstToSecond_isProIsomorphism_of_proZero_third
    (hT : ∀ n : ℕ, T.obj n ∈ distTriang D)
    (h₃ : HasProObjectValue (T ⋙ Triangle.π₃) (0 : D))
    :
    (ofOrderDualNatTrans (Functor.whiskerLeft T Triangle.π₁Toπ₂)).IsProIsomorphism := sorry

/-- Bridge/view companion to Lemma 13.42.4: under the same pro-zero hypothesis on `(Cₙ)`, the
induced map `colimₙ Hom(Bₙ, X) → colimₙ Hom(Aₙ, X)` is bijective for every test object `X`. -/
theorem triangleFirstToSecond_toProObjectHom_app_bijective_of_proZero_third
    (hT : ∀ n : ℕ, T.obj n ∈ distTriang D)
    (h₃ : HasProObjectValue (T ⋙ Triangle.π₃) (0 : D))
    (X : D) :
    Function.Bijective
      ((ofOrderDualNatTrans (Functor.whiskerLeft T Triangle.π₁Toπ₂)).toProObjectHom.app X) := by
  simpa using
    isProIsomorphism_toProObjectHom_app_bijective
      (triangleFirstToSecond_isProIsomorphism_of_proZero_third hT h₃) X

end

end CategoryTheory
