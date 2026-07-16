import Mathlib
import StacksProject_2024.stacks_project.Chap29.Lemma_29_35_11

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry

/- Semantic recall / analogue check:
- `lean_leansearch` recalled the canonical scheme-side owners `AlgebraicGeometry.IsEtale`,
  `Scheme.Hom.fiber`, and the ring-level finite-separable field-extension criterion.
- Local Chapter 29 precedent in `Lemma_29_35_11` already owns the explicit over-`Spec k`
  coproduct data as `SchemeAsDisjointUnionOfSpecFiniteSeparable`; this item reuses that owner and
  replaces unramifiedness by étaleness in the two source-facing statements.
-/

/-- Lemma 29.36.7 (1): for a scheme over a field `k`, the structure morphism is étale if and only
if the scheme is a disjoint union of spectra of finite separable field extensions of `k`. -/
@[stacks 02GL]
theorem etale_iff_schemeAsDisjointUnionOfSpecFiniteSeparable
    {k : Type u} [Field k] (X : Over (Spec (CommRingCat.of k))) :
    Etale X.hom ↔
      Nonempty (SchemeAsDisjointUnionOfSpecFiniteSeparable k X) := sorry

/-- Lemma 29.36.7 (2): every fibre of an étale morphism is a disjoint union of spectra of finite
separable extensions of the corresponding residue field. -/
@[stacks 02GL]
theorem fiber_schemeAsDisjointUnionOfSpecFiniteSeparable_of_etale
    {X S : Scheme.{u}} (f : X ⟶ S) [Etale f] (s : S) :
    Nonempty
      (SchemeAsDisjointUnionOfSpecFiniteSeparable (S.residueField s)
        (Over.mk (f.fiberToSpecResidueField s))) := sorry

end AlgebraicGeometry
