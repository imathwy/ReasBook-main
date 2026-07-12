import Mathlib
import StacksProject_2024.Chap15.Lemma_15_65_2

noncomputable section

open CategoryTheory ObjectProperty Pretriangulated
open scoped ZeroObject

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} {A : Type v}
variable [CommRing R] [CommRing A] [Algebra R A] [Algebra.FiniteType R A]

local notation "DModA" => DerivedCategory (ModuleCat A)

/-- Helper for Lemma 15.82.6: a derived `A`-complex is `m`-pseudo-coherent relative to `R` if it
becomes `m`-pseudo-coherent after restriction along every surjective polynomial presentation of
`A` over `R`. -/
abbrev DerivedCategory.IsMPseudoCoherentRelativeTo
    (R : Type u) [CommRing R] ⦃A : Type v⦄ [CommRing A] [Algebra R A]
    [Algebra.FiniteType R A] (K : DerivedCategory (ModuleCat A)) (m : ℤ) : Prop :=
  ∀ (n : ℕ) (α : MvPolynomial (Fin n) R →ₐ[R] A), Function.Surjective α →
    ((ModuleCat.restrictScalars α.toRingHom).mapDerivedCategory.obj K).IsMPseudoCoherent m

/-- Helper for Lemma 15.82.6: a derived `A`-complex is pseudo-coherent relative to `R` if it is
`m`-pseudo-coherent relative to `R` for every integer `m`. -/
abbrev DerivedCategory.IsPseudoCoherentRelativeTo
    (R : Type u) [CommRing R] ⦃A : Type v⦄ [CommRing A] [Algebra R A]
    [Algebra.FiniteType R A] (K : DerivedCategory (ModuleCat A)) : Prop :=
  ∀ m : ℤ, K.IsMPseudoCoherentRelativeTo R m

/-- Helper for Lemma 15.82.6: the zero cochain complex over a ring. -/
private abbrev zeroCpx {S : Type*} [Ring S] : CochainComplex (ModuleCat S) ℤ := 0

/-- Helper for Lemma 15.82.6: the zero cochain complex is termwise finite free. -/
private instance zero_isTermwiseFiniteFree {S : Type*} [Ring S] :
    (zeroCpx (S := S)).IsTermwiseFiniteFree where
  out i := by
    let E0 : CochainComplex (ModuleCat S) ℤ := zeroCpx (S := S)
    change Module.Free S ↥(E0.X i) ∧ Module.Finite S ↥(E0.X i)
    -- Each degree of the zero complex is a zero module, hence free and finite.
    let hzero : Limits.IsZero (E0.X i) := by
      simpa [E0] using
        (HomologicalComplex.eval (ModuleCat S) (ComplexShape.up ℤ) i).map_isZero
          (Limits.isZero_zero (CochainComplex (ModuleCat S) ℤ))
    letI : Subsingleton ↥(E0.X i) := ModuleCat.subsingleton_of_isZero hzero
    have hfree : Module.Free S (E0.X i) :=
      Module.Free.of_subsingleton (R := S) (N := ↥(E0.X i))
    have hfinite : Module.Finite S (E0.X i) :=
      let e : ModuleCat.of S PUnit ≅ E0.X i :=
        (ModuleCat.isZero_of_subsingleton (ModuleCat.of S PUnit)).isoZero ≪≫ hzero.isoZero.symm
      Module.Finite.equiv e.toLinearEquiv
    exact And.intro hfree hfinite

/-- Helper for Lemma 15.82.6: the zero object of `D(S)` is `m`-pseudo-coherent. -/
private theorem zero_isMPseudoCoherent {S : Type*} [Ring S] (m : ℤ) :
    (0 : DerivedCategory (ModuleCat S)).IsMPseudoCoherent m := by
  let E0 : CochainComplex (ModuleCat S) ℤ := zeroCpx (S := S)
  let hQ0 : Limits.IsZero (DerivedCategory.Q.obj E0) :=
    (DerivedCategory.Q).map_isZero (Limits.isZero_zero (CochainComplex (ModuleCat S) ℤ))
  let e : DerivedCategory.Q.obj E0 ≅ (0 : DerivedCategory (ModuleCat S)) :=
    hQ0.iso (Limits.isZero_zero (DerivedCategory (ModuleCat S)))
  refine ⟨E0, ?_, inferInstance, e.hom, ?_, ?_⟩
  · -- The zero complex is bounded above and below at every cutoff.
    exact ⟨0, 0, inferInstance, inferInstance⟩
  · intro i hi
    -- The homology comparison is an isomorphism because the chosen map is an isomorphism.
    infer_instance
  · -- The degree-`m` homology map is an epimorphism for the same reason.
    infer_instance

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
/-- Helper for Lemma 15.82.6: shifting a derived `A`-complex translates relative
`m`-pseudo-coherence by the same amount. -/
theorem isMPseudoCoherentRelativeTo_shift_iff (K : DModA) (n m : ℤ) :
    (K⟦n⟧).IsMPseudoCoherentRelativeTo R (m - n) ↔ K.IsMPseudoCoherentRelativeTo R m := by
  constructor
  · intro hK
    intro d α hα
    let F := (ModuleCat.restrictScalars α.toRingHom).mapDerivedCategory
    let e : F.obj (K⟦n⟧) ≅ (F.obj K)⟦n⟧ := (F.commShiftIso n).app K
    -- Compare the restricted shifted object with the shift of the restricted object.
    have hshift : (F.obj (K⟦n⟧)).IsMPseudoCoherent (m - n) := hK d α hα
    have hshift' : ((F.obj K)⟦n⟧).IsMPseudoCoherent (m - n) :=
      isMPseudoCoherent_of_iso e (m - n) hshift
    exact (isMPseudoCoherent_shift_iff (F.obj K) n m).1 hshift'
  · intro hK
    intro d α hα
    let F := (ModuleCat.restrictScalars α.toRingHom).mapDerivedCategory
    let e : F.obj (K⟦n⟧) ≅ (F.obj K)⟦n⟧ := (F.commShiftIso n).app K
    -- Apply the absolute shift equivalence after restricting scalars.
    have hbase : (F.obj K).IsMPseudoCoherent m := hK d α hα
    have hshift' : ((F.obj K)⟦n⟧).IsMPseudoCoherent (m - n) :=
      (isMPseudoCoherent_shift_iff (F.obj K) n m).2 hbase
    exact isMPseudoCoherent_of_iso e.symm (m - n) hshift'

/-- Lemma 15.82.6 (1): for a finite type ring map `R → A` and a distinguished triangle in
`D(A)`, if the first term is `(m + 1)`-pseudo-coherent relative to `R` and the second term is
`m`-pseudo-coherent relative to `R`, then the third term is `m`-pseudo-coherent relative to
`R`. -/
@[stacks 0674]
theorem isMPseudoCoherentRelativeTo_obj₃_of_distinguishedTriangle
    {m : ℤ} (T : Triangle DModA) (hT : T ∈ distTriang DModA)
    (h₁ : T.obj₁.IsMPseudoCoherentRelativeTo R (m + 1))
    (h₂ : T.obj₂.IsMPseudoCoherentRelativeTo R m) :
    T.obj₃.IsMPseudoCoherentRelativeTo R m := by
  intro n α hα
  let F := (ModuleCat.restrictScalars α.toRingHom).mapDerivedCategory
  let Tα : Triangle (DerivedCategory (ModuleCat (MvPolynomial (Fin n) R))) := F.mapTriangle.obj T
  have hTα : Tα ∈ distTriang (DerivedCategory (ModuleCat (MvPolynomial (Fin n) R))) := by
    -- Restrict the distinguished triangle to the chosen polynomial presentation.
    simpa [Tα] using F.map_distinguished T hT
  -- The relative hypotheses become the absolute hypotheses on the restricted triangle.
  exact isMPseudoCoherent_obj₃_of_distinguishedTriangle Tα hTα (h₁ n α hα) (h₂ n α hα)

instance isMPseudoCoherentRelativeTo_isClosedUnderIsomorphisms (m : ℤ) :
    ObjectProperty.IsClosedUnderIsomorphisms
      (fun K : DModA ↦ K.IsMPseudoCoherentRelativeTo R m) where
  of_iso e hK := by
    intro n α hα
    let F := (ModuleCat.restrictScalars α.toRingHom).mapDerivedCategory
    let P : ObjectProperty (DerivedCategory (ModuleCat (MvPolynomial (Fin n) R))) :=
      fun K ↦ K.IsMPseudoCoherent m
    -- Transport the absolute statement across the restricted isomorphism.
    exact P.prop_of_iso (F.mapIso e) (hK n α hα)

/-- For fixed `m`, relative `m`-pseudo-coherent objects of `D(A)` satisfy the canonical
`ObjectProperty.IsTriangulatedClosed₂` two-out-of-three axiom. -/
instance isMPseudoCoherentRelativeTo_isTriangulatedClosed₂ (m : ℤ) :
    ObjectProperty.IsTriangulatedClosed₂
      (fun K : DModA ↦ K.IsMPseudoCoherentRelativeTo R m) := by
  refine .mk' ?_
  intro T hT h₁ h₃
  have h₃' : (T.obj₃⟦-1⟧).IsMPseudoCoherentRelativeTo R (m + 1) := by
    -- Rewrite the shifted third vertex into the index needed for `invRotate`.
    simpa using (isMPseudoCoherentRelativeTo_shift_iff (R := R) T.obj₃ (-1) m).2 h₃
  exact isMPseudoCoherentRelativeTo_obj₃_of_distinguishedTriangle T.invRotate
    (inv_rot_of_distTriang T hT) h₃' h₁

-- Proof sketch: fix a surjective polynomial presentation `P → A`, restrict the distinguished
-- triangle from `D(A)` to `D(P)`, and apply the second distinguished-triangle closure statement
-- for `m`-pseudo-coherence over `P`.
/-- Lemma 15.82.6 (2): for a finite type ring map `R → A` and a distinguished triangle in
`D(A)`, if the first and third terms are `m`-pseudo-coherent relative to `R`, then the second
term is `m`-pseudo-coherent relative to `R`. -/
@[stacks 0674]
theorem isMPseudoCoherentRelativeTo_obj₂_of_distinguishedTriangle
    {m : ℤ} (T : Triangle DModA) (hT : T ∈ distTriang DModA)
    (h₁ : T.obj₁.IsMPseudoCoherentRelativeTo R m)
    (h₃ : T.obj₃.IsMPseudoCoherentRelativeTo R m) :
    T.obj₂.IsMPseudoCoherentRelativeTo R m := by
  let P : ObjectProperty DModA := fun K ↦ K.IsMPseudoCoherentRelativeTo R m
  -- Invoke the canonical fixed-`m` owner-level two-out-of-three statement.
  exact P.ext_of_isTriangulatedClosed₂ T hT h₁ h₃

-- Proof sketch: fix a surjective polynomial presentation `P → A`, restrict the distinguished
-- triangle from `D(A)` to `D(P)`, and apply the third distinguished-triangle closure statement
-- for `m`-pseudo-coherence over `P`.
/-- Lemma 15.82.6 (3): for a finite type ring map `R → A` and a distinguished triangle in
`D(A)`, if the second term is `(m + 1)`-pseudo-coherent relative to `R` and the third term is
`m`-pseudo-coherent relative to `R`, then the first term is `(m + 1)`-pseudo-coherent relative
to `R`. -/
@[stacks 0674]
theorem isMPseudoCoherentRelativeTo_obj₁_of_distinguishedTriangle
    {m : ℤ} (T : Triangle DModA) (hT : T ∈ distTriang DModA)
    (h₂ : T.obj₂.IsMPseudoCoherentRelativeTo R (m + 1))
    (h₃ : T.obj₃.IsMPseudoCoherentRelativeTo R m) :
    T.obj₁.IsMPseudoCoherentRelativeTo R (m + 1) := by
  have hshift : (T.obj₁⟦(1 : ℤ)⟧).IsMPseudoCoherentRelativeTo R m :=
    isMPseudoCoherentRelativeTo_obj₃_of_distinguishedTriangle T.rotate
      (rot_of_distTriang T hT) h₂ h₃
  have hshift' : (T.obj₁⟦(1 : ℤ)⟧).IsMPseudoCoherentRelativeTo R ((m + 1) - 1) := by
    -- Normalize the index so the shift equivalence matches the goal.
    simpa using hshift
  exact (isMPseudoCoherentRelativeTo_shift_iff (R := R) T.obj₁ 1 (m + 1)).1 hshift'

instance isPseudoCoherentRelativeTo_isClosedUnderIsomorphisms :
    ObjectProperty.IsClosedUnderIsomorphisms
      (fun K : DModA ↦ K.IsPseudoCoherentRelativeTo R) where
  of_iso e hK := by
    rw [DerivedCategory.IsPseudoCoherentRelativeTo] at hK ⊢
    intro m
    let P : ObjectProperty DModA := fun K ↦ K.IsMPseudoCoherentRelativeTo R m
    -- Relative pseudo-coherence is the degreewise fixed-`m` condition.
    exact P.prop_of_iso e (hK m)

/-- Helper for Lemma 15.82.6: the zero object of `D(A)` is pseudo-coherent relative to `R`. -/
private theorem isPseudoCoherentRelativeTo_zero :
    (0 : DModA).IsPseudoCoherentRelativeTo R := by
  rw [DerivedCategory.IsPseudoCoherentRelativeTo]
  intro m
  intro n α hα
  let F := (ModuleCat.restrictScalars α.toRingHom).mapDerivedCategory
  have hzero : Limits.IsZero (F.obj (0 : DModA)) :=
    Functor.map_isZero F (Limits.isZero_zero DModA)
  let e : F.obj (0 : DModA) ≅ (0 : DerivedCategory (ModuleCat (MvPolynomial (Fin n) R))) :=
    hzero.iso (Limits.isZero_zero _)
  -- Transport the absolute zero-object statement back along the restricted zero isomorphism.
  exact
    isMPseudoCoherent_of_iso e.symm m
      (zero_isMPseudoCoherent (S := MvPolynomial (Fin n) R) m)

-- Proof sketch: combine the degreewise distinguished-triangle closure from parts `(1)`-`(3)` with
-- the defining universal quantification of `IsPseudoCoherentRelativeTo`, exactly as in the
-- absolute analogue `Lemma 15.65.6`. The previous instance supplies the needed closure under
-- isomorphisms for the owner object property.
/-- Canonical owner form of Lemma 15.82.6 (4)-(6): pseudo-coherent objects of `D(A)` relative to
`R` form a triangulated object property. -/
instance isPseudoCoherentRelativeTo_isTriangulated :
    ObjectProperty.IsTriangulated
      (fun K : DModA ↦ K.IsPseudoCoherentRelativeTo R) := by
  refine
    { exists_zero := ?_
      toIsStableUnderShift := ?_
      toIsTriangulatedClosed₂ := ?_ }
  · -- Use the canonical zero object together with the direct relative proof above.
    exact ⟨(0 : DModA), Limits.isZero_zero DModA, isPseudoCoherentRelativeTo_zero (R := R)⟩
  · refine { isStableUnderShiftBy := ?_ }
    intro n
    refine IsStableUnderShiftBy.mk ?_
    intro K hK
    rw [prop_shift_iff]
    rw [DerivedCategory.IsPseudoCoherentRelativeTo] at hK ⊢
    intro m
    -- Shift stability is just the degreewise relative shift equivalence.
    simpa using (isMPseudoCoherentRelativeTo_shift_iff (R := R) K n (m + n)).2 (hK (m + n))
  · refine .mk' ?_
    intro T hT h₁ h₃
    rw [DerivedCategory.IsPseudoCoherentRelativeTo] at h₁ h₃ ⊢
    intro m
    -- Apply the fixed-`m` two-out-of-three theorem degreewise.
    exact isMPseudoCoherentRelativeTo_obj₂_of_distinguishedTriangle T hT (h₁ m) (h₃ m)

-- Proof sketch: unfold relative pseudo-coherence as relative `m`-pseudo-coherence for all
-- integers `m`, equivalently apply the `obj₁`-`obj₂` to `obj₃` consequence of the triangulated
-- owner instance above.
/-- Lemma 15.82.6 (4): for a finite type ring map `R → A` and a distinguished triangle in
`D(A)`, if the first two terms are pseudo-coherent relative to `R`, then the third term is
pseudo-coherent relative to `R`. -/
@[stacks 0674]
theorem isPseudoCoherentRelativeTo_obj₃_of_distinguishedTriangle
    (T : Triangle DModA) (hT : T ∈ distTriang DModA)
    (h₁ : T.obj₁.IsPseudoCoherentRelativeTo R)
    (h₂ : T.obj₂.IsPseudoCoherentRelativeTo R) :
    T.obj₃.IsPseudoCoherentRelativeTo R := by
  let P : ObjectProperty DModA := fun K ↦ K.IsPseudoCoherentRelativeTo R
  -- This is the `obj₁`-`obj₂` to `obj₃` consequence of the triangulated owner.
  exact P.ext_of_isTriangulatedClosed₃ T hT h₁ h₂

-- Proof sketch: unfold relative pseudo-coherence as relative `m`-pseudo-coherence for all
-- integers `m`, equivalently apply the `obj₁`-`obj₃` to `obj₂` consequence of the triangulated
-- owner instance above.
/-- Lemma 15.82.6 (5): for a finite type ring map `R → A` and a distinguished triangle in
`D(A)`, if the first and third terms are pseudo-coherent relative to `R`, then the second term
is pseudo-coherent relative to `R`. -/
@[stacks 0674]
theorem isPseudoCoherentRelativeTo_obj₂_of_distinguishedTriangle
    (T : Triangle DModA) (hT : T ∈ distTriang DModA)
    (h₁ : T.obj₁.IsPseudoCoherentRelativeTo R)
    (h₃ : T.obj₃.IsPseudoCoherentRelativeTo R) :
    T.obj₂.IsPseudoCoherentRelativeTo R := by
  let P : ObjectProperty DModA := fun K ↦ K.IsPseudoCoherentRelativeTo R
  -- This is the `obj₁`-`obj₃` to `obj₂` consequence of the triangulated owner.
  exact P.ext_of_isTriangulatedClosed₂ T hT h₁ h₃

-- Proof sketch: unfold relative pseudo-coherence as relative `m`-pseudo-coherence for all
-- integers `m`, equivalently apply the `obj₂`-`obj₃` to `obj₁` consequence of the triangulated
-- owner instance above.
/-- Lemma 15.82.6 (6): for a finite type ring map `R → A` and a distinguished triangle in
`D(A)`, if the second and third terms are pseudo-coherent relative to `R`, then the first term
is pseudo-coherent relative to `R`. -/
@[stacks 0674]
theorem isPseudoCoherentRelativeTo_obj₁_of_distinguishedTriangle
    (T : Triangle DModA) (hT : T ∈ distTriang DModA)
    (h₂ : T.obj₂.IsPseudoCoherentRelativeTo R)
    (h₃ : T.obj₃.IsPseudoCoherentRelativeTo R) :
    T.obj₁.IsPseudoCoherentRelativeTo R := by
  let P : ObjectProperty DModA := fun K ↦ K.IsPseudoCoherentRelativeTo R
  -- This is the `obj₂`-`obj₃` to `obj₁` consequence of the triangulated owner.
  exact P.ext_of_isTriangulatedClosed₁ T hT h₂ h₃

end

end CategoryTheory
