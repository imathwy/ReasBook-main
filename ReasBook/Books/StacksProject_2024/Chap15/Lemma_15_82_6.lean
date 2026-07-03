import StacksProject_2024.Chap15.Lemma_15_82_10

noncomputable section

open CategoryTheory ObjectProperty Pretriangulated

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} {A : Type v}
variable [CommRing R] [CommRing A] [Algebra R A] [Algebra.FiniteType R A]

local notation "DModA" => DerivedCategory (ModuleCat A)

/- Domain-style sampling for Lemma 15.82.6:
- primary domain: relative pseudo-coherent object properties in the derived category `D(A)` and
  their closure under distinguished triangles for a finite type ring map `R → A`;
- sampled owner declarations:
  `DerivedCategory.IsMPseudoCoherentRelativeTo`,
  `DerivedCategory.IsPseudoCoherentRelativeTo`,
  `ObjectProperty.IsTriangulatedClosed₂`,
  `ObjectProperty.IsTriangulated`;
- best owner abstraction: the fixed-`m` closure owner is the object property
  `fun K : DModA ↦ K.IsMPseudoCoherentRelativeTo R m`, while the pseudo-coherent owner is
  `fun K : DModA ↦ K.IsPseudoCoherentRelativeTo R`;
- primitive vs. derived:
  primitive data are the relative `m`-pseudo-coherent and pseudo-coherent predicates from
  Definition `15.82.4` and Lemma `15.82.10`;
  derived API is the distinguished-triangle closure, with parts `(1)`-`(3)` providing the
  degreewise `m`-pseudo-coherent input and parts `(4)`-`(6)` derived from the owner abstraction;
- source/core/bridge triage:
  `source-facing`: the six textbook closure statements for relative pseudo-coherence in a
    distinguished triangle;
  `core/canonical`: `ObjectProperty.IsTriangulatedClosed₂
    (fun K : DModA ↦ K.IsMPseudoCoherentRelativeTo R m)` for the fixed-`m` layer, and
    `ObjectProperty.IsTriangulated
    (fun K : DModA ↦ K.IsPseudoCoherentRelativeTo R)`;
  `bridge/view`: deriving the pseudo-coherent `obj₁`/`obj₂`/`obj₃` statements from that owner.
- layer: this file keeps the source-facing statements, but it targets the `core/canonical` layer
  first for fixed-`m` clause `(2)` and then for the pseudo-coherent part, so downstream files
  reuse the triangulated owner rather than a parallel family of standalone lemmas.
-/

-- Proof sketch: fix a surjective polynomial presentation `P → A`, restrict the distinguished
-- triangle from `D(A)` to `D(P)`, and apply the distinguished-triangle closure of
-- `m`-pseudo-coherence over the polynomial ring `P`.
/-- Lemma 15.82.6 (1): for a finite type ring map `R → A` and a distinguished triangle in
`D(A)`, if the first term is `(m + 1)`-pseudo-coherent relative to `R` and the second term is
`m`-pseudo-coherent relative to `R`, then the third term is `m`-pseudo-coherent relative to
`R`. -/
theorem isMPseudoCoherentRelativeTo_obj₃_of_distinguishedTriangle
    {m : ℤ} (T : Triangle DModA) (hT : T ∈ distTriang DModA)
    (h₁ : T.obj₁.IsMPseudoCoherentRelativeTo R (m + 1))
    (h₂ : T.obj₂.IsMPseudoCoherentRelativeTo R m) :
    T.obj₃.IsMPseudoCoherentRelativeTo R m := sorry

instance isMPseudoCoherentRelativeTo_isClosedUnderIsomorphisms (m : ℤ) :
    ObjectProperty.IsClosedUnderIsomorphisms
      (fun K : DModA ↦ K.IsMPseudoCoherentRelativeTo R m) where
  of_iso _ _ := by
    sorry

/-- For fixed `m`, relative `m`-pseudo-coherent objects of `D(A)` satisfy the canonical
`ObjectProperty.IsTriangulatedClosed₂` two-out-of-three axiom. -/
instance isMPseudoCoherentRelativeTo_isTriangulatedClosed₂ (m : ℤ) :
    ObjectProperty.IsTriangulatedClosed₂
      (fun K : DModA ↦ K.IsMPseudoCoherentRelativeTo R m) := by
  sorry

-- Proof sketch: fix a surjective polynomial presentation `P → A`, restrict the distinguished
-- triangle from `D(A)` to `D(P)`, and apply the second distinguished-triangle closure statement
-- for `m`-pseudo-coherence over `P`.
/-- Lemma 15.82.6 (2): for a finite type ring map `R → A` and a distinguished triangle in
`D(A)`, if the first and third terms are `m`-pseudo-coherent relative to `R`, then the second
term is `m`-pseudo-coherent relative to `R`. -/
theorem isMPseudoCoherentRelativeTo_obj₂_of_distinguishedTriangle
    {m : ℤ} (T : Triangle DModA) (hT : T ∈ distTriang DModA)
    (h₁ : T.obj₁.IsMPseudoCoherentRelativeTo R m)
    (h₃ : T.obj₃.IsMPseudoCoherentRelativeTo R m) :
    T.obj₂.IsMPseudoCoherentRelativeTo R m := by
  sorry

-- Proof sketch: fix a surjective polynomial presentation `P → A`, restrict the distinguished
-- triangle from `D(A)` to `D(P)`, and apply the third distinguished-triangle closure statement
-- for `m`-pseudo-coherence over `P`.
/-- Lemma 15.82.6 (3): for a finite type ring map `R → A` and a distinguished triangle in
`D(A)`, if the second term is `(m + 1)`-pseudo-coherent relative to `R` and the third term is
`m`-pseudo-coherent relative to `R`, then the first term is `(m + 1)`-pseudo-coherent relative
to `R`. -/
theorem isMPseudoCoherentRelativeTo_obj₁_of_distinguishedTriangle
    {m : ℤ} (T : Triangle DModA) (hT : T ∈ distTriang DModA)
    (h₂ : T.obj₂.IsMPseudoCoherentRelativeTo R (m + 1))
    (h₃ : T.obj₃.IsMPseudoCoherentRelativeTo R m) :
    T.obj₁.IsMPseudoCoherentRelativeTo R (m + 1) := sorry

instance isPseudoCoherentRelativeTo_isClosedUnderIsomorphisms :
    ObjectProperty.IsClosedUnderIsomorphisms
      (fun K : DModA ↦ K.IsPseudoCoherentRelativeTo R) where
  of_iso _ _ := by
    sorry

-- Proof sketch: combine the degreewise distinguished-triangle closure from parts `(1)`-`(3)` with
-- the defining universal quantification of `IsPseudoCoherentRelativeTo`, exactly as in the
-- absolute analogue `Lemma 15.65.6`. The previous instance supplies the needed closure under
-- isomorphisms for the owner object property.
/-- Canonical owner form of Lemma 15.82.6 (4)-(6): pseudo-coherent objects of `D(A)` relative to
`R` form a triangulated object property. -/
instance isPseudoCoherentRelativeTo_isTriangulated :
    ObjectProperty.IsTriangulated
      (fun K : DModA ↦ K.IsPseudoCoherentRelativeTo R) := by
  sorry

-- Proof sketch: unfold relative pseudo-coherence as relative `m`-pseudo-coherence for all
-- integers `m`, equivalently apply the `obj₁`-`obj₂` to `obj₃` consequence of the triangulated
-- owner instance above.
/-- Lemma 15.82.6 (4): for a finite type ring map `R → A` and a distinguished triangle in
`D(A)`, if the first two terms are pseudo-coherent relative to `R`, then the third term is
pseudo-coherent relative to `R`. -/
theorem isPseudoCoherentRelativeTo_obj₃_of_distinguishedTriangle
    (T : Triangle DModA) (hT : T ∈ distTriang DModA)
    (h₁ : T.obj₁.IsPseudoCoherentRelativeTo R)
    (h₂ : T.obj₂.IsPseudoCoherentRelativeTo R) :
    T.obj₃.IsPseudoCoherentRelativeTo R := by
  sorry

-- Proof sketch: unfold relative pseudo-coherence as relative `m`-pseudo-coherence for all
-- integers `m`, equivalently apply the `obj₁`-`obj₃` to `obj₂` consequence of the triangulated
-- owner instance above.
/-- Lemma 15.82.6 (5): for a finite type ring map `R → A` and a distinguished triangle in
`D(A)`, if the first and third terms are pseudo-coherent relative to `R`, then the second term
is pseudo-coherent relative to `R`. -/
theorem isPseudoCoherentRelativeTo_obj₂_of_distinguishedTriangle
    (T : Triangle DModA) (hT : T ∈ distTriang DModA)
    (h₁ : T.obj₁.IsPseudoCoherentRelativeTo R)
    (h₃ : T.obj₃.IsPseudoCoherentRelativeTo R) :
    T.obj₂.IsPseudoCoherentRelativeTo R := by
  sorry

-- Proof sketch: unfold relative pseudo-coherence as relative `m`-pseudo-coherence for all
-- integers `m`, equivalently apply the `obj₂`-`obj₃` to `obj₁` consequence of the triangulated
-- owner instance above.
/-- Lemma 15.82.6 (6): for a finite type ring map `R → A` and a distinguished triangle in
`D(A)`, if the second and third terms are pseudo-coherent relative to `R`, then the first term
is pseudo-coherent relative to `R`. -/
theorem isPseudoCoherentRelativeTo_obj₁_of_distinguishedTriangle
    (T : Triangle DModA) (hT : T ∈ distTriang DModA)
    (h₂ : T.obj₂.IsPseudoCoherentRelativeTo R)
    (h₃ : T.obj₃.IsPseudoCoherentRelativeTo R) :
    T.obj₁.IsPseudoCoherentRelativeTo R := by
  sorry

end

end CategoryTheory
