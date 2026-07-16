import Mathlib
import StacksProject_2024.stacks_project.Chap29.Lemma_29_35_9

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory
open CategoryTheory Limits

noncomputable section

universe u

namespace AlgebraicGeometry

/- Semantic recall / analogue check:
- `lean_leansearch` recalled the canonical scheme-fiber owners `Scheme.Hom.fiber` and
  `Scheme.Hom.fiberOverSpecResidueField`.
- Local Chapter 29 precedent uses `Over (Spec (CommRingCat.of k))` for a scheme over a field
  (`Lemma_29_23_4`) and explicit over-`Spec κ(s)` coproduct data for finite separable fibres
  (`Lemma_29_35_12`).
- This item records the field-base decomposition once, then applies it to
  `f.fiberToSpecResidueField s` for the fibre clause.
-/

/-- Explicit data saying that an object over the spectrum of a field is a coproduct of spectra of
finite separable field extensions of that base field. -/
@[stacks 02G7]
structure SchemeAsDisjointUnionOfSpecFiniteSeparable (k : Type u) [Field k]
    (X : Over (Spec (CommRingCat.of k))) where
  /-- The indexing type for the components. -/
  ι : Type u
  /-- The field attached to each component. -/
  field : ι → Type u
  /-- Each component carrier is a field. -/
  instField : ∀ i, Field (field i)
  /-- Each component field is an extension of the base field. -/
  algebra : ∀ i, Algebra k (field i)
  /-- Each component extension is finite. -/
  finite : ∀ i, letI := instField i; letI := algebra i; FiniteDimensional k (field i)
  /-- Each component extension is separable. -/
  separable : ∀ i, letI := instField i; letI := algebra i; Algebra.IsSeparable k (field i)
  /-- The given scheme over the base is isomorphic to the coproduct of the component spectra over
  `Spec k`. -/
  iso :
    Over.mk X.hom ≅
      Over.mk
        (Limits.Sigma.desc fun i : ι ↦
          letI := instField i
          letI := algebra i
          Spec.map (CommRingCat.ofHom (algebraMap k (field i))))

/-- Each component in a finite-separable spectral coproduct decomposition is a field. -/
instance instFieldSchemeAsDisjointUnionOfSpecFiniteSeparable
    {k : Type u} [Field k] {X : Over (Spec (CommRingCat.of k))}
    (D : SchemeAsDisjointUnionOfSpecFiniteSeparable k X) (i : D.ι) :
    Field (D.field i) :=
  D.instField i

/-- Each component in a finite-separable spectral coproduct decomposition is an algebra over the
base field. -/
instance instAlgebraSchemeAsDisjointUnionOfSpecFiniteSeparable
    {k : Type u} [Field k] {X : Over (Spec (CommRingCat.of k))}
    (D : SchemeAsDisjointUnionOfSpecFiniteSeparable k X) (i : D.ι) :
    Algebra k (D.field i) :=
  D.algebra i

/-- The canonical map from the coproduct of the component spectra to the base spectrum. -/
def SchemeAsDisjointUnionOfSpecFiniteSeparable.toSpec
    {k : Type u} [Field k] {X : Over (Spec (CommRingCat.of k))}
    (D : SchemeAsDisjointUnionOfSpecFiniteSeparable k X) :
    (∐ fun i : D.ι ↦ Spec (CommRingCat.of (D.field i))) ⟶ Spec (CommRingCat.of k) :=
  Limits.Sigma.desc fun i : D.ι ↦
    letI := D.instField i
    letI := D.algebra i
    Spec.map (CommRingCat.ofHom (algebraMap k (D.field i)))

/-- The canonical coproduct-to-base map is the descent of the maps induced by the component field
extensions. -/
theorem SchemeAsDisjointUnionOfSpecFiniteSeparable.toSpec_eq
    {k : Type u} [Field k] {X : Over (Spec (CommRingCat.of k))}
    (D : SchemeAsDisjointUnionOfSpecFiniteSeparable k X) :
    D.toSpec =
      Limits.Sigma.desc fun i : D.ι ↦
        letI := D.instField i
        letI := D.algebra i
        Spec.map (CommRingCat.ofHom (algebraMap k (D.field i))) := sorry

/-- The data in a finite-separable spectral coproduct decomposition expose finite separable
component extensions and an over-base coproduct isomorphism. -/
theorem SchemeAsDisjointUnionOfSpecFiniteSeparable.spec
    {k : Type u} [Field k] {X : Over (Spec (CommRingCat.of k))}
    (D : SchemeAsDisjointUnionOfSpecFiniteSeparable k X) :
    (∀ i : D.ι, FiniteDimensional k (D.field i) ∧
      Algebra.IsSeparable k (D.field i)) ∧
      Nonempty (Over.mk X.hom ≅ Over.mk D.toSpec) := sorry

/-- Lemma 29.35.11 (1): for a scheme over a field `k`, the structure morphism is unramified if
and only if the scheme is a disjoint union of spectra of finite separable field extensions of
`k`. -/
@[stacks 02G7]
theorem unramified_iff_schemeAsDisjointUnionOfSpecFiniteSeparable
    {k : Type u} [Field k] (X : Over (Spec (CommRingCat.of k))) :
    Unramified X.hom ↔
      Nonempty (SchemeAsDisjointUnionOfSpecFiniteSeparable k X) := sorry

/-- Lemma 29.35.11 (2): every fibre of an unramified morphism is a disjoint union of spectra of
finite separable extensions of the corresponding residue field. -/
@[stacks 02G7]
theorem fiber_schemeAsDisjointUnionOfSpecFiniteSeparable_of_unramified
    {X S : Scheme.{u}} (f : X ⟶ S) [Unramified f] (s : S) :
    Nonempty
      (SchemeAsDisjointUnionOfSpecFiniteSeparable (S.residueField s)
        (Over.mk (f.fiberToSpecResidueField s))) := sorry

end AlgebraicGeometry
