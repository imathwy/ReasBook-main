import Mathlib
import StacksProject_2024.Chap29.Lemma_29_55_5

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry
namespace Scheme.Hom

noncomputable section

variable {X Y : Scheme.{u}} (f : Y ⟶ X)
variable [QuasiCompact f] [QuasiSeparated f] [IsDominant f]

/-
Definition 29.55.6: for a quasi-compact, quasi-separated, dominant morphism
`f : Y ⟶ X`, the initial object of `RelativeSeminormalizationFactorizations f` constructed in
Lemma 29.55.5 (2) is the seminormalization of `X` in `Y`, written
`Y ⟶ X^{Y/sn} ⟶ X`; the initial object of `RelativeWeakNormalizationFactorizations f`
constructed in Lemma 29.55.5 (1) is the weak normalization of `X` in `Y`, written
`Y ⟶ X^{Y/wn} ⟶ X`.

Semantic recall: `lean_leansearch` surfaced the canonical `CategoryTheory.Factorisation`
category and its initial-object API. Local Chapter 29 precedent records definition-by-naming of
constructed normalization morphisms as typed recalls rather than abbreviations, since local
abbreviations for the chosen initial objects would inherit `sorryAx` through the statement-stage
`HasInitial` instances. The Stacks tag evidence is consistent: item tag `0H3P` agrees with the
source URL ending in `/tag/0H3P`.
-/

#check ((⊥_ (RelativeSeminormalizationFactorizations f)).1 :
    CategoryTheory.Factorisation f)

#check ((⊥_ (RelativeSeminormalizationFactorizations f)).1.ι :
    Y ⟶ (⊥_ (RelativeSeminormalizationFactorizations f)).1.mid)

#check ((⊥_ (RelativeSeminormalizationFactorizations f)).1.π :
    (⊥_ (RelativeSeminormalizationFactorizations f)).1.mid ⟶ X)

#check ((⊥_ (RelativeWeakNormalizationFactorizations f)).1 :
    CategoryTheory.Factorisation f)

#check ((⊥_ (RelativeWeakNormalizationFactorizations f)).1.ι :
    Y ⟶ (⊥_ (RelativeWeakNormalizationFactorizations f)).1.mid)

#check ((⊥_ (RelativeWeakNormalizationFactorizations f)).1.π :
    (⊥_ (RelativeWeakNormalizationFactorizations f)).1.mid ⟶ X)

end

end Scheme.Hom
end AlgebraicGeometry
