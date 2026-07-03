import Mathlib
import StacksProject_2024.Chap12.Lemma_12_31_3
import StacksProject_2024.Chap12.Lemma_12_31_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe u v

namespace CategoryTheory

namespace ShortComplex.ShortExact

variable {A : Type u} [Category.{v} A] [Abelian A]
variable {S : ShortComplex (SequentialInverseSystem A)}

/- Domain-style sampling for Lemma 12.31.6 in the sequential inverse-system domain:
- owner abstractions: `ShortComplex.ShortExact`,
  `SequentialInverseSystem.IsMittagLeffler`, and `IsEssentiallyConstantCofilteredDiagram`
- sampled chapter-level declarations:
  * `SequentialInverseSystem.IsMittagLeffler` in `Definition_12_31_2`
  * `ShortComplex.ShortExact` in the ambient abelian-category owner API
  * `SequentialInverseSystem.essentiallyConstant_iff_hasLimitTailDecomposition` in
    `Lemma_12_31_5`

This item is therefore `bridge/view`: the source lemma compares the two owner predicates across a
short exact sequence whose right term is controlled by the chapter-level essential-constancy
criterion. The statement should stay at that bridge layer rather than introduce any new wrapper
around the short exact sequence data. -/

-- Proof sketch: use the structure theorem for essentially constant sequential inverse systems from
-- Lemma 12.31.5 to reduce to a quotient that is eventually zero modulo a constant summand, and
-- then compare the stabilized images in the short exact sequence stagewise. The eventually zero
-- case identifies the middle images with successive left images, while the constant case preserves
-- stabilization because the quotients of the middle images are all canonically `C`.
/-- Lemma 12.31.6: in a short exact sequence of sequential inverse systems in an abelian category,
if the quotient inverse system is essentially constant, then the left inverse system is
Mittag-Leffler if and only if the middle inverse system is Mittag-Leffler. -/
theorem isMittagLeffler_X₁_iff_X₂_of_essentiallyConstant_X₃
    (hS : S.ShortExact) (hC : IsEssentiallyConstantCofilteredDiagram S.X₃) :
    S.X₁.IsMittagLeffler ↔ S.X₂.IsMittagLeffler := sorry

end ShortComplex.ShortExact

end CategoryTheory
