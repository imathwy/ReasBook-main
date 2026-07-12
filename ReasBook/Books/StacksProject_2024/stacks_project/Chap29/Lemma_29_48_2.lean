import StacksProject_2024.Chap29.Definition_29_48_1
import StacksProject_2024.Chap29.Definition_29_14_2

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}} {f : X ⟶ S}

/-- The affine-open ring map condition underlying finite locally free morphisms in this file:
the induced ring map is finite and the target is free over the source via the induced algebra
structure. -/
abbrev ringHomFiniteFree
    {R T : Type u} [CommRing R] [CommRing T] (φ : R →+* T) : Prop :=
  let _ : Algebra R T := φ.toAlgebra
  RingHom.Finite φ ∧ Module.Free R T

/-- Unfold `ringHomFiniteFree` into finiteness and freeness over the induced algebra structure. -/
theorem ringHomFiniteFree_iff
    {R T : Type u} [CommRing R] [CommRing T] (φ : R →+* T) :
    ringHomFiniteFree φ ↔
      let _ : Algebra R T := φ.toAlgebra
      RingHom.Finite φ ∧ Module.Free R T :=
  Iff.rfl

-- Semantic recall note: `lean_leansearch` surfaced the scheme-level owners `IsFinite`, `Flat`,
-- `LocallyOfFinitePresentation`, and the chapter-local affine owner `LocallyOfType`; Chapter 29
-- already provides the canonical source-facing owner `IsFiniteLocallyFree` in
-- `Definition_29_48_1.lean`, so the present file keeps that owner and exposes only thin bridge
-- theorems.

/-- Lemma 29.48.2 (1): a morphism of schemes is finite locally free exactly when it is finite,
flat, and locally of finite presentation. -/
theorem finiteLocallyFree_iff_isFinite_and_flat_and_locallyOfFinitePresentation :
    IsFiniteLocallyFree f ↔ IsFinite f ∧ Flat f ∧ LocallyOfFinitePresentation f := sorry

/-- Build the source-facing owner `IsFiniteLocallyFree` from the canonical scheme-side conditions
finite, flat, and locally of finite presentation. -/
theorem isFiniteLocallyFree_of_isFinite_and_flat_and_locallyOfFinitePresentation
    (hfinite : IsFinite f) (hflat : Flat f) (hlfp : LocallyOfFinitePresentation f) :
    IsFiniteLocallyFree f :=
  finiteLocallyFree_iff_isFinite_and_flat_and_locallyOfFinitePresentation.2
    ⟨hfinite, hflat, hlfp⟩

/-- A finite locally free morphism is finite. -/
theorem IsFiniteLocallyFree.isFinite (h : IsFiniteLocallyFree f) : IsFinite f :=
  finiteLocallyFree_iff_isFinite_and_flat_and_locallyOfFinitePresentation.1 h |>.1

/-- A finite locally free morphism is flat. -/
theorem IsFiniteLocallyFree.flat (h : IsFiniteLocallyFree f) : Flat f :=
  finiteLocallyFree_iff_isFinite_and_flat_and_locallyOfFinitePresentation.1 h |>.2.1

/-- A finite locally free morphism is locally of finite presentation. -/
theorem IsFiniteLocallyFree.locallyOfFinitePresentation
    (h : IsFiniteLocallyFree f) : LocallyOfFinitePresentation f :=
  finiteLocallyFree_iff_isFinite_and_flat_and_locallyOfFinitePresentation.1 h |>.2.2

/-- A finite locally free morphism is finite. -/
instance instIsFiniteOfIsFiniteLocallyFree [IsFiniteLocallyFree f] : IsFinite f :=
  (inferInstance : IsFiniteLocallyFree f).isFinite

/-- A finite locally free morphism is flat. -/
instance instFlatOfIsFiniteLocallyFree [IsFiniteLocallyFree f] : Flat f :=
  (inferInstance : IsFiniteLocallyFree f).flat

/-- A finite locally free morphism is locally of finite presentation. -/
instance instLocallyOfFinitePresentationOfIsFiniteLocallyFree [IsFiniteLocallyFree f] :
    LocallyOfFinitePresentation f :=
  (inferInstance : IsFiniteLocallyFree f).locallyOfFinitePresentation

/-- Affine-local bridge for finite locally free morphisms: on affine opens, the induced ring map is
finite and free over the source via the induced algebra structure. -/
theorem finiteLocallyFree_iff_locallyOfType_ringHomFiniteFree :
    IsFiniteLocallyFree f ↔ LocallyOfType ringHomFiniteFree f := sorry

/-- A finite locally free morphism satisfies the affine-local finite-free ring-map condition. -/
theorem IsFiniteLocallyFree.locallyOfType_ringHomFiniteFree (h : IsFiniteLocallyFree f) :
    LocallyOfType ringHomFiniteFree f :=
  finiteLocallyFree_iff_locallyOfType_ringHomFiniteFree.1 h

/-- A finite locally free morphism satisfies the affine-local finite-free ring-map condition. -/
instance instLocallyOfTypeRingHomFiniteFreeOfIsFiniteLocallyFree [IsFiniteLocallyFree f] :
    LocallyOfType ringHomFiniteFree f :=
  (inferInstance : IsFiniteLocallyFree f).locallyOfType_ringHomFiniteFree

/-- Lemma 29.48.2 (2): over a locally Noetherian base scheme, a morphism is finite locally free
exactly when it is finite and flat. -/
theorem finiteLocallyFree_iff_isFinite_and_flat [IsLocallyNoetherian S] :
    IsFiniteLocallyFree f ↔ IsFinite f ∧ Flat f := sorry

end AlgebraicGeometry
