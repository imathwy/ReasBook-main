import Mathlib
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import StacksProject_2024.Chap15.«15_91_16_1»
import StacksProject_2024.Chap15.Lemma_15_91_10

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open scoped TensorProduct

noncomputable section

universe u

section

variable {R : Type u} [CommRing R]
variable {R' : Type u} [CommRing R'] [Algebra R R']
variable (f : R)

variable (R') in
/-- The full subcategory of `ModuleCat R` consisting of modules glueable for the
Beauville-Laszlo pair `(R → R', f)`. -/
abbrev beauvilleLaszloGlueableProperty (f : R) : ObjectProperty (ModuleCat R) :=
  fun M ↦ (beauvilleLaszloModuleCechSequence R' M f).ShortExact

-- Proof sketch: for a glueing datum `(M', M₁, α₁)`, define `H^0` as the kernel of the
-- Beauville-Laszlo differential from `15.91.16.1`. The surjectivity and exactness statements in
-- `15.91.16.1`-`15.91.16.3`, together with Lemmas `15.91.15`, `15.89.9`, and `15.90.11`, show
-- that this kernel is glueable, that `Can(H^0(-))` reconstructs the original glueing datum, and
-- that `H^0(Can(M)) = M` for every glueable module `M`.
/-- Theorem 15.91.16: if `(R → R', f)` is a Beauville-Laszlo glueing pair, then the canonical
functor `Can : Mod_R → Glue(R → R', f)` induces an equivalence from the category of glueable
`R`-modules for `(R → R', f)` to the category of Beauville-Laszlo glueing data. In this
library-facing formalization, the source is the full subcategory
`(beauvilleLaszloGlueableProperty R' f).FullSubcategory` of `ModuleCat R`, and the target is the
categorical pullback `Mod_{R'} ×_{Mod_{R'_f}} Mod_{R_f}`. -/
theorem beauvilleLaszloGlueableCan_isEquivalence
    (f : R) (hpair : IsBeauvilleLaszloGlueingPairAlong (algebraMap R R') f) :
    Functor.IsEquivalence
      ((beauvilleLaszloGlueableProperty R' f).ι ⋙ formalGlueingSingleFunctor R' f) := sorry

end
