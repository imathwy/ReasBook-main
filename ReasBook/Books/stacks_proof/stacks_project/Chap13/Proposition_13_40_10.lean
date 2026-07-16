import Mathlib
import stacks_proof.stacks_project.Chap13.Lemma_13_5_8
import stacks_proof.stacks_project.Chap13.Lemma_13_6_6
import stacks_proof.stacks_project.Chap13.Definition_13_6_7
import stacks_proof.stacks_project.Chap13.Lemma_13_35_1
import stacks_proof.stacks_project.Chap13.Definition_13_40_1
import stacks_proof.stacks_project.Chap13.Lemma_13_40_4
import stacks_proof.stacks_project.Chap13.Lemma_13_40_7
import stacks_proof.stacks_project.Chap13.Lemma_13_40_8
import stacks_proof.stacks_project.Chap13.Definition_13_40_9
import stacks_proof.stacks_project.Chap13.Lemma_13_5_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Localization
open CategoryTheory.Limits
open CategoryTheory.MorphismProperty
open CategoryTheory.Pretriangulated
open scoped CategoryTheory.ObjectProperty.ExtensionProductNotation
open scoped CategoryTheory.ObjectProperty

noncomputable section

universe v u

namespace CategoryTheory.ObjectProperty

section

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

private theorem inverseImage_trW_rightOrthogonal_le_isomorphisms
    (A B : ObjectProperty D) [A.IsTriangulated] [A.IsClosedUnderIsomorphisms]
    (hB : B ≤ A^⊥) :
    (B.trW).inverseImage A.ι ≤ isomorphisms A.FullSubcategory := by
  intro X Y f hf
  rw [MorphismProperty.inverseImage_iff] at hf
  obtain ⟨Z, g, h, hT, hBZ⟩ := hf
  have hAZ : A Z :=
    A.ext_of_isTriangulatedClosed₃ (Triangle.mk (A.ι.map f) g h) hT X.2 Y.2
  have hZorth : (A^⊥) Z := hB _ hBZ
  have hZzero : IsZero Z := by
    refine (IsZero.iff_id_eq_zero Z).2 ?_
    exact hZorth (𝟙 Z) hAZ
  haveI : IsIso (A.ι.map f) := ((Triangle.mk (A.ι.map f) g h).isZero₃_iff_isIso₁ hT).1 hZzero
  letI : A.ι.ReflectsIsomorphisms := Functor.FullyFaithful.reflectsIsomorphisms A.fullyFaithfulι
  exact Functor.ReflectsIsomorphisms.reflects A.ι f

end

section

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] [IsTriangulated D]
variable (A B : ObjectProperty D)

/- Domain-style sampling for Proposition 13.40.10:
- primary domain: semi-orthogonal decompositions and admissible triangulated subcategories;
- sampled owner declarations:
  `IsRightAdmissible`,
  `IsLeftAdmissible`,
  `ObjectProperty.rightOrthogonal`,
  `ObjectProperty.leftOrthogonal`,
  `ObjectProperty.extensionProduct`,
  `P.trW.Q : D ⥤ D / P`,
  `Functor.rightAdjoint`,
  `Functor.leftAdjoint`,
  `Localization.uniq`;
- best owner abstractions:
  the source-facing TFAE statement stays at the admissibility/orthogonal-extension-product layer,
  while the comparison functors to Verdier quotients should be expressed directly through the
  canonical orthogonal owners `A^⊥` and `^⊥B`, and the adjoint-description statements should use
  the chosen inclusion adjoints together with the inverse functors of the canonical quotient
  equivalences;
- primitive data: object properties `A`, `B` and the admissibility hypotheses;
- derived API: the orthogonal equalities, the extension-product condition, and the quotient
  comparison equivalences, plus the resulting identifications of the inclusion adjoints as
  composites through those quotient equivalences;
- source/core/bridge triage:
  `source-facing`: the TFAE theorem for admissibility and semi-orthogonal decomposition;
  `core/canonical`: orthogonals, extension product, and the quotient owner `D / P`;
  `bridge/view`: the comparison functors from admissible subcategories to the corresponding
    Verdier quotients, together with the description of the inclusion adjoints via quasi-inverses
    to those comparison functors.

The comparison theorems below should therefore target the canonical quotients by `A^⊥` and `^⊥B`
rather than an arbitrary equal copy, and the adjoint-description theorems should be stated as
functor isomorphisms rather than wrapper definitions. -/

/-- Helper for Proposition 13.40.10: if `A ⋆ B = ⊤` and `B` is right-orthogonal to `A`, then the
right orthogonal `A^⊥` is already contained in `B`. -/
lemma rightOrthogonal_le_of_triangle_decomposition
    [A.IsTriangulated] [A.IsClosedUnderIsomorphisms] [B.IsClosedUnderIsomorphisms]
    (hBA : B ≤ A^⊥) (htop : A ⋆ B = ⊤) :
    A^⊥ ≤ B := by
  intro X hX
  have htopX : (A ⋆ B) X := by
    rw [htop]
    trivial
  rw [extensionProduct_iff] at htopX
  rcases htopX with ⟨A', B', f, g, h, hT, hA', hB'⟩
  have hB'orth : A^⊥ B' := hBA _ hB'
  have hA'orth : A^⊥ A' := by
    -- Proof comment: both the middle and last terms already lie in `A^⊥`, so the first term does
    -- as well by triangulated closure of the orthogonal.
    exact (A^⊥).ext_of_isTriangulatedClosed₁ (Triangle.mk f g h) hT hX hB'orth
  have hA'zero : IsZero A' := by
    -- Proof comment: an object lying in both `A` and `A^⊥` has zero identity morphism.
    rw [A.rightOrthogonal_iff] at hA'orth
    refine (IsZero.iff_id_eq_zero A').2 ?_
    exact hA'orth (𝟙 A') hA'
  letI : IsZero A' := hA'zero
  have hshiftzero : IsZero ((Triangle.mk f g h).rotate.obj₃) := by
    -- Proof comment: shifting a zero object keeps it zero, so the rotated triangle has zero
    -- third vertex.
    simpa using (inferInstance : IsZero (A'⟦(1 : ℤ)⟧))
  have hgisIso : IsIso ((Triangle.mk f g h).rotate.mor₁) := by
    -- Proof comment: in the rotated distinguished triangle, zero third vertex forces
    -- `X ⟶ B'` to be an isomorphism.
    simpa using
      ((Triangle.mk f g h).rotate.isZero₃_iff_isIso₁ (rot_of_distTriang _ hT)).1 hshiftzero
  letI : IsIso ((Triangle.mk f g h).rotate.mor₁) := hgisIso
  -- Proof comment: transport membership in `B` across the resulting isomorphism `X ≅ B'`.
  exact B.prop_of_iso (asIso ((Triangle.mk f g h).rotate.mor₁)).symm hB'

/-- Helper for Proposition 13.40.10: if `A ⋆ B = ⊤` and `B` is right-orthogonal to `A`, then the
left orthogonal `^⊥B` is already contained in `A`. -/
lemma leftOrthogonal_le_of_triangle_decomposition
    [B.IsTriangulated] [A.IsClosedUnderIsomorphisms]
    (hBA : B ≤ A^⊥) (htop : A ⋆ B = ⊤) :
    ^⊥B ≤ A := by
  have hAleft : A ≤ ^⊥B := by
    intro X hX
    rw [B.leftOrthogonal_iff]
    intro Y f hY
    exact (hBA _ hY) f hX
  intro X hX
  have htopX : (A ⋆ B) X := by
    rw [htop]
    trivial
  rw [extensionProduct_iff] at htopX
  rcases htopX with ⟨A', B', f, g, h, hT, hA', hB'⟩
  have hA'left : ^⊥B A' := hAleft _ hA'
  have hB'left : ^⊥B B' := by
    -- Proof comment: both the first and middle terms already lie in `^⊥B`, so the third term
    -- does too by triangulated closure of the left orthogonal.
    exact (^⊥B).ext_of_isTriangulatedClosed₃ (Triangle.mk f g h) hT hA'left hX
  have hB'zero : IsZero B' := by
    -- Proof comment: an object lying in both `B` and `^⊥B` has zero identity morphism.
    rw [B.leftOrthogonal_iff] at hB'left
    refine (IsZero.iff_id_eq_zero B').2 ?_
    exact hB'left (𝟙 B') hB'
  have hfIso : IsIso f := by
    -- Proof comment: once the third vertex vanishes, the first morphism becomes an isomorphism.
    simpa using ((Triangle.mk f g h).isZero₃_iff_isIso₁ hT).1 hB'zero
  letI : IsIso f := hfIso
  -- Proof comment: transport membership in `A` across the isomorphism `A' ≅ X`.
  exact A.prop_of_iso (asIso f) hA'

-- Proof sketch: combine Lemma `13.40.7` for `A` with Lemma `13.40.8` for `B`. The condition
-- `B = A^⊥` identifies the right-admissible and left-admissible descriptions, while
-- the triangle condition is exactly the extension-product statement `A ⋆ B = ⊤`
-- together with the orthogonality inclusion `B ≤ A^⊥`, under the source-facing hypotheses that
-- `A` and `B` are strictly full triangulated subcategories.
/-- Proposition 13.40.10: the following are equivalent for subcategories `A, B` of a triangulated
category `D`: `A` is right admissible with `B = A^⊥`, `B` is left admissible with
`A = ^⊥B`, and `A` and `B` are strictly full triangulated subcategories such that `B` is
right-orthogonal to `A` and every object of `D` fits into a distinguished triangle
`A' ⟶ X ⟶ B' ⟶ A'⟦1⟧` with `A' ∈ A` and `B' ∈ B`. -/
@[stacks 0H0P]
theorem tfae_rightAdmissible_leftAdmissible_orthogonal_triangleDecomposition :
    List.TFAE
      [ IsRightAdmissible A ∧ B = A^⊥
      , IsLeftAdmissible B ∧ A = ^⊥B
      , A.IsTriangulated ∧ A.IsClosedUnderIsomorphisms ∧
          B.IsTriangulated ∧ B.IsClosedUnderIsomorphisms ∧
          B ≤ A^⊥ ∧ A ⋆ B = ⊤ ] := by
  tfae_have 1 → 3 := by
    rintro ⟨hA, rfl⟩
    letI : IsRightAdmissible A := hA
    -- Proof comment: Lemma 13.40.7 turns right admissibility into the canonical decomposition
    -- `A ⋆ A^⊥ = ⊤`, and the orthogonal owner contributes the remaining source-facing fields.
    refine ⟨inferInstance, inferInstance, inferInstance, inferInstance, le_rfl, ?_⟩
    exact (A.isLeftAdjoint_iff_extensionProduct_rightOrthogonal_eq_top).1
      (inferInstance : A.ι.IsLeftAdjoint)
  tfae_have 3 → 1 := by
    rintro ⟨hAtri, hAiso, hBtri, hBiso, hBA, htop⟩
    letI : A.IsTriangulated := hAtri
    letI : A.IsClosedUnderIsomorphisms := hAiso
    letI : B.IsClosedUnderIsomorphisms := hBiso
    have hAorthTop : A ⋆ A^⊥ = ⊤ := by
      -- Proof comment: enlarge the right factor from `B` to `A^⊥` using the given
      -- orthogonality inclusion.
      apply top_unique
      simpa [htop] using (monotone_extensionProduct_right A hBA : A ⋆ B ≤ A ⋆ A^⊥)
    have hAdj : A.ι.IsLeftAdjoint :=
      (A.isLeftAdjoint_iff_extensionProduct_rightOrthogonal_eq_top).2 hAorthTop
    have hEq : B = A^⊥ := by
      -- Proof comment: one inclusion is assumed, and the reverse inclusion is the triangle
      -- decomposition argument above.
      apply le_antisymm
      · exact hBA
      · exact rightOrthogonal_le_of_triangle_decomposition (A := A) (B := B) hBA htop
    exact ⟨⟨hAtri, hAiso, hAdj⟩, hEq⟩
  tfae_have 2 → 3 := by
    rintro ⟨hB, hAeq⟩
    letI : IsLeftAdmissible B := hB
    subst hAeq
    -- Proof comment: Lemma 13.40.8 gives the left-admissible decomposition
    -- `(^⊥B) ⋆ B = ⊤`, and the defining orthogonality immediately yields `B ≤ (^⊥B)^⊥`.
    refine ⟨inferInstance, inferInstance, inferInstance, inferInstance, ?_, ?_⟩
    · intro Y hY
      rw [(^⊥B).rightOrthogonal_iff]
      intro X f hX
      rw [B.leftOrthogonal_iff] at hX
      exact hX f hY
    · exact (B.isRightAdjoint_iff_leftOrthogonal_extensionProduct_eq_top).1
        (inferInstance : B.ι.IsRightAdjoint)
  tfae_have 3 → 2 := by
    rintro ⟨hAtri, hAiso, hBtri, hBiso, hBA, htop⟩
    letI : B.IsTriangulated := hBtri
    letI : A.IsClosedUnderIsomorphisms := hAiso
    have hAleft : A ≤ ^⊥B := by
      -- Proof comment: the assumed inclusion `B ≤ A^⊥` is exactly the source-facing
      -- orthogonality statement saying every object of `A` lies in `^⊥B`.
      intro X hX
      rw [B.leftOrthogonal_iff]
      intro Y f hY
      exact (hBA _ hY) f hX
    have hleftTop : (^⊥B) ⋆ B = ⊤ := by
      -- Proof comment: enlarge the left factor from `A` to `^⊥B` using the derived inclusion.
      apply top_unique
      simpa [htop] using (monotone_extensionProduct_left B hAleft : A ⋆ B ≤ (^⊥B) ⋆ B)
    have hAdj : B.ι.IsRightAdjoint :=
      (B.isRightAdjoint_iff_leftOrthogonal_extensionProduct_eq_top).2 hleftTop
    have hEq : A = ^⊥B := by
      -- Proof comment: one inclusion is immediate from orthogonality, and the reverse inclusion
      -- again comes from the source triangle decomposition.
      apply le_antisymm
      · exact hAleft
      · exact leftOrthogonal_le_of_triangle_decomposition (A := A) (B := B) hBA htop
    exact ⟨⟨hBtri, hBiso, hAdj⟩, hEq⟩
  tfae_finish

end

section

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
variable (A : ObjectProperty D)

private instance : ((A^⊥).trW.Q : D ⥤ D / (A^⊥)).IsLocalization (A^⊥).trW :=
  Functor.q_isLocalization (A^⊥).trW

-- Proof sketch: an object lies in the kernel of the chosen right adjoint exactly when every map
-- from an object of `A` to it vanishes. The forward direction is immediate from the adjunction.
-- Conversely, if `X ∈ A^⊥`, then the counit `A.ι.obj (A.ι.rightAdjoint.obj X) ⟶ X` is zero, so
-- the identity of `A.ι.rightAdjoint.obj X` is zero by adjunction, hence `A.ι.rightAdjoint.obj X`
-- is a zero object.
/-- Under right admissibility, the kernel of the chosen right adjoint to the inclusion `A ⥤ D`
is exactly the right orthogonal `A^⊥`. -/
theorem rightAdmissible_rightAdjoint_kernel_eq_rightOrthogonal
    [IsRightAdmissible A] :
    Functor.kernel A.ι.rightAdjoint = A^⊥ := by
  let adj : A.ι ⊣ A.ι.rightAdjoint := Adjunction.ofIsLeftAdjoint A.ι
  ext X
  constructor
  · intro hX
    rw [A.rightOrthogonal_iff]
    intro Y f hY
    exact (adj.homEquiv ⟨Y, hY⟩ X).injective (hX.eq_of_tgt _ _)
  · intro hX
    rw [A.rightOrthogonal_iff] at hX
    have hzero : adj.counit.app X = 0 :=
      hX (adj.counit.app X) (A.ι.rightAdjoint.obj X).2
    refine (IsZero.iff_id_eq_zero _).2 ?_
    apply (adj.homEquiv (A.ι.rightAdjoint.obj X) X).symm.injective
    rw [Adjunction.homEquiv_symm_id]
    rw [hzero]
    rw [Adjunction.homEquiv_counit]
    simp
    rfl

-- Proof sketch: the chosen right adjoint is exact by the triangulated-adjunction API. The
-- Bousfield-localization description of a right adjoint to a fully faithful inclusion identifies
-- the morphisms it inverts with the inverse image of isomorphisms; the exact-functor kernel owner
-- rewrites that morphism property as `(Functor.kernel A.ι.rightAdjoint).trW`, and the previous
-- theorem identifies this kernel with `A^⊥`.
/-- Under right admissibility, the chosen right adjoint to the
inclusion `A ⥤ D` is a localization functor for the Verdier morphism property `(A^⊥).trW`. -/
theorem rightAdmissible_rightAdjoint_isLocalization
    [IsRightAdmissible A] :
    A.ι.rightAdjoint.IsLocalization (A^⊥).trW := by
  let adj : A.ι ⊣ A.ι.rightAdjoint := Adjunction.ofIsLeftAdjoint A.ι
  letI := adj.rightAdjointCommShift ℤ
  letI := adj.commShift_of_leftAdjoint ℤ
  letI : A.ι.rightAdjoint.IsTriangulated := adj.isTriangulated_rightAdjoint
  rw [← rightAdmissible_rightAdjoint_kernel_eq_rightOrthogonal A]
  rw [kernel_trW_eq_inverseImage_isomorphisms_of_exactFunctor A.ι.rightAdjoint]
  rw [← ObjectProperty.isColocal_eq_inverseImage_isomorphisms adj]
  exact ObjectProperty.isLocalization_isColocal adj

-- Proof sketch: the chosen right adjoint is itself a localization at `(A^⊥).trW`. Uniqueness of
-- localization functors identifies the corresponding comparison equivalence with the canonical
-- functor `A ⥤ D / (A^⊥)`.
/-- If `A` is right admissible, then the canonical comparison functor
`A ⥤ D / (A^⊥)` is an equivalence. Under the additional ambient hypothesis
`[IsTriangulated D]`, the canonical exactness instances upgrade this to the triangulated
equivalence appearing in Proposition 13.40.10. -/
theorem rightAdmissibleComparisonFunctor_isEquivalence
    [IsRightAdmissible A] :
    Functor.IsEquivalence (A.ι ⋙ (A^⊥).trW.Q) := by
  letI : A.ι.rightAdjoint.IsLocalization (A^⊥).trW :=
    rightAdmissible_rightAdjoint_isLocalization A
  let quotientFunctor : D ⥤ D / (A^⊥) := (A^⊥).trW.Q
  letI : quotientFunctor.IsLocalization (A^⊥).trW := by
    change ((A^⊥).trW.Q : D ⥤ D / (A^⊥)).IsLocalization (A^⊥).trW
    infer_instance
  let e : A.FullSubcategory ≌ D / (A^⊥) :=
    Localization.uniq A.ι.rightAdjoint quotientFunctor (A^⊥).trW
  let adj : A.ι ⊣ A.ι.rightAdjoint := Adjunction.ofIsLeftAdjoint A.ι
  let i : e.functor ≅ A.ι ⋙ quotientFunctor :=
    (Functor.leftUnitor e.functor).symm ≪≫
      Functor.isoWhiskerRight (asIso adj.unit) e.functor ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft A.ι
        (Localization.compUniqFunctor A.ι.rightAdjoint quotientFunctor (A^⊥).trW)
  letI : Functor.IsEquivalence e.functor := by infer_instance
  -- Proof comment: transport the localization equivalence across the canonical comparison iso.
  exact Functor.isEquivalence_of_iso i

private instance [IsRightAdmissible A] : Functor.IsEquivalence (A.ι ⋙ (A^⊥).trW.Q) :=
  rightAdmissibleComparisonFunctor_isEquivalence A

-- Proof sketch: both `A.ι.rightAdjoint` and the Verdier quotient functor `(A^⊥).trW.Q` localize
-- at `(A^⊥).trW`, so `Localization.compUniqInverse` identifies `A.ι.rightAdjoint` with
-- `(A^⊥).trW.Q` composed with the inverse functor of the canonical localization equivalence. The
-- left adjoint `A.ι` is fully faithful, so its unit is an isomorphism; this identifies that
-- canonical localization equivalence with the comparison equivalence
-- `A.ι ⋙ (A^⊥).trW.Q`. Uniqueness of right adjoints for a fixed left adjoint
-- then transports the inverse functor accordingly.
/-- Under right admissibility, the chosen right adjoint to the inclusion `A ⥤ D` is canonically
isomorphic to the composite `D ⥤ D / (A^⊥) ⥤ A`, where the second functor is a quasi-inverse to
the comparison equivalence `A.ι ⋙ (A^⊥).trW.Q : A ⥤ D / (A^⊥)`. This is the
adjoint-description part of Proposition 13.40.10. -/
noncomputable def rightAdmissible_rightAdjointIso_quotientCompInverse
    [IsRightAdmissible A] :
    A.ι.rightAdjoint ≅
      (A^⊥).trW.Q ⋙ (A.ι ⋙ (A^⊥).trW.Q).asEquivalence.inverse :=
  letI : A.ι.rightAdjoint.IsLocalization (A^⊥).trW :=
    rightAdmissible_rightAdjoint_isLocalization A
  let quotientFunctor : D ⥤ D / (A^⊥) := (A^⊥).trW.Q
  letI : quotientFunctor.IsLocalization (A^⊥).trW := by
    change ((A^⊥).trW.Q : D ⥤ D / (A^⊥)).IsLocalization (A^⊥).trW
    infer_instance
  let comparisonFunctor : A.FullSubcategory ⥤ D / (A^⊥) := A.ι ⋙ quotientFunctor
  letI : comparisonFunctor.IsEquivalence := by
    change Functor.IsEquivalence (A.ι ⋙ (A^⊥).trW.Q)
    infer_instance
  let e : A.FullSubcategory ≌ D / (A^⊥) :=
    Localization.uniq A.ι.rightAdjoint quotientFunctor (A^⊥).trW
  let adj : A.ι ⊣ A.ι.rightAdjoint := Adjunction.ofIsLeftAdjoint A.ι
  let i : e.functor ≅ comparisonFunctor :=
    (Functor.leftUnitor e.functor).symm ≪≫
      Functor.isoWhiskerRight (asIso adj.unit) e.functor ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft A.ι
        (Localization.compUniqFunctor A.ι.rightAdjoint quotientFunctor (A^⊥).trW)
  let j : e.inverse ≅ comparisonFunctor.asEquivalence.inverse :=
    Adjunction.rightAdjointUniq (e.changeFunctor i).toAdjunction
      comparisonFunctor.asEquivalence.toAdjunction
  (Localization.compUniqInverse A.ι.rightAdjoint quotientFunctor (A^⊥).trW).symm ≪≫
    Functor.isoWhiskerLeft quotientFunctor j

end

section

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
variable (B : ObjectProperty D)

private instance : ((^⊥B).trW.Q : D ⥤ D / (^⊥B)).IsLocalization (^⊥B).trW :=
  Functor.q_isLocalization (^⊥B).trW

-- Proof sketch: this is the dual kernel computation. If `B.ι.leftAdjoint.obj X` is zero, then
-- every morphism `X ⟶ Y` with `Y ∈ B` vanishes by adjunction. Conversely, if `X ∈ ^⊥B`, then the
-- unit `X ⟶ B.ι.obj (B.ι.leftAdjoint.obj X)` is zero, so the identity of
-- `B.ι.leftAdjoint.obj X` is zero by adjunction.
/-- Under left admissibility, the kernel of the chosen left adjoint to the inclusion `B ⥤ D`
is exactly the left orthogonal `^⊥B`. -/
theorem leftAdmissible_leftAdjoint_kernel_eq_leftOrthogonal
    [IsLeftAdmissible B] :
    Functor.kernel B.ι.leftAdjoint = ^⊥B := by
  let adj : B.ι.leftAdjoint ⊣ B.ι := Adjunction.ofIsRightAdjoint B.ι
  ext X
  constructor
  · intro hX
    rw [B.leftOrthogonal_iff]
    intro Y f hY
    exact (adj.homEquiv X ⟨Y, hY⟩).symm.injective (hX.eq_of_src _ _)
  · intro hX
    rw [B.leftOrthogonal_iff] at hX
    have hzero : adj.unit.app X = 0 :=
      hX (adj.unit.app X) (B.ι.leftAdjoint.obj X).2
    refine (IsZero.iff_id_eq_zero _).2 ?_
    apply (adj.homEquiv X (B.ι.leftAdjoint.obj X)).injective
    rw [Adjunction.homEquiv_id]
    rw [hzero]
    rw [Adjunction.homEquiv_unit]
    simp
    rfl

-- Proof sketch: dually, the chosen left adjoint is exact by the triangulated-adjunction API. The
-- Bousfield-localization description of a left adjoint to a fully faithful right adjoint rewrites
-- the inverted morphisms as the inverse image of isomorphisms, hence as the `trW` owner of its
-- kernel; the previous theorem identifies that kernel with `^⊥B`.
/-- Under left admissibility, the chosen left adjoint to the inclusion
`B ⥤ D` is a localization functor for the Verdier morphism property `(^⊥B).trW`. -/
theorem leftAdmissible_leftAdjoint_isLocalization
    [IsLeftAdmissible B] :
    B.ι.leftAdjoint.IsLocalization (^⊥B).trW := by
  let adj : B.ι.leftAdjoint ⊣ B.ι := Adjunction.ofIsRightAdjoint B.ι
  letI := adj.leftAdjointCommShift ℤ
  letI := adj.commShift_of_rightAdjoint ℤ
  letI : B.ι.leftAdjoint.IsTriangulated := adj.isTriangulated_leftAdjoint
  rw [← leftAdmissible_leftAdjoint_kernel_eq_leftOrthogonal B]
  rw [kernel_trW_eq_inverseImage_isomorphisms_of_exactFunctor B.ι.leftAdjoint]
  rw [← ObjectProperty.isLocal_eq_inverseImage_isomorphisms adj]
  exact ObjectProperty.isLocalization_isLocal adj

-- Proof sketch: this is the dual localization-uniqueness argument. The chosen left adjoint and
-- the quotient functor both localize at `(^⊥B).trW`, so the canonical comparison functor is
-- identified with an equivalence.
/-- If `B` is left admissible, then the canonical comparison functor
`B ⥤ D / (^⊥B)` is an equivalence. Under the additional ambient hypothesis
`[IsTriangulated D]`, the canonical exactness instances upgrade this to the second triangulated
equivalence appearing in Proposition 13.40.10. -/
theorem leftAdmissibleComparisonFunctor_isEquivalence
    [IsLeftAdmissible B] :
    Functor.IsEquivalence (B.ι ⋙ (^⊥B).trW.Q) := by
  letI : B.ι.leftAdjoint.IsLocalization (^⊥B).trW :=
    leftAdmissible_leftAdjoint_isLocalization B
  let quotientFunctor : D ⥤ D / (^⊥B) := (^⊥B).trW.Q
  letI : quotientFunctor.IsLocalization (^⊥B).trW := by
    change ((^⊥B).trW.Q : D ⥤ D / (^⊥B)).IsLocalization (^⊥B).trW
    infer_instance
  let e : B.FullSubcategory ≌ D / (^⊥B) :=
    Localization.uniq B.ι.leftAdjoint quotientFunctor (^⊥B).trW
  let adj : B.ι.leftAdjoint ⊣ B.ι := Adjunction.ofIsRightAdjoint B.ι
  let i : e.functor ≅ B.ι ⋙ quotientFunctor :=
    (Functor.leftUnitor e.functor).symm ≪≫
      Functor.isoWhiskerRight (asIso adj.counit).symm e.functor ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft B.ι
        (Localization.compUniqFunctor B.ι.leftAdjoint quotientFunctor (^⊥B).trW)
  letI : Functor.IsEquivalence e.functor := by infer_instance
  -- Proof comment: transport the canonical localization equivalence across the comparison iso.
  exact Functor.isEquivalence_of_iso i

private instance [IsLeftAdmissible B] : Functor.IsEquivalence (B.ι ⋙ (^⊥B).trW.Q) :=
  leftAdmissibleComparisonFunctor_isEquivalence B

-- Proof sketch: both `B.ι.leftAdjoint` and the Verdier quotient functor `(^⊥B).trW.Q` localize
-- at `(^⊥B).trW`, so `Localization.compUniqInverse` identifies `B.ι.leftAdjoint` with
-- `(^⊥B).trW.Q` composed with the inverse functor of the canonical localization equivalence.
-- Since `B.ι` is fully faithful, the counit of `B.ι.leftAdjoint ⊣ B.ι` is an isomorphism, which
-- identifies that canonical localization equivalence with the comparison equivalence
-- `B.ι ⋙ (^⊥B).trW.Q`.
-- Uniqueness of right adjoints then transports the inverse functor.
/-- Under left admissibility, the chosen left adjoint to the inclusion `B ⥤ D` is canonically
isomorphic to the composite `D ⥤ D / (^⊥B) ⥤ B`, where the second functor is a quasi-inverse to
the comparison equivalence `B.ι ⋙ (^⊥B).trW.Q : B ⥤ D / (^⊥B)`. This is the dual
adjoint-description part of Proposition 13.40.10. -/
noncomputable def leftAdmissible_leftAdjointIso_quotientCompInverse
    [IsLeftAdmissible B] :
    B.ι.leftAdjoint ≅
      (^⊥B).trW.Q ⋙ (B.ι ⋙ (^⊥B).trW.Q).asEquivalence.inverse :=
  letI : B.ι.leftAdjoint.IsLocalization (^⊥B).trW :=
    leftAdmissible_leftAdjoint_isLocalization B
  let quotientFunctor : D ⥤ D / (^⊥B) := (^⊥B).trW.Q
  letI : quotientFunctor.IsLocalization (^⊥B).trW := by
    change ((^⊥B).trW.Q : D ⥤ D / (^⊥B)).IsLocalization (^⊥B).trW
    infer_instance
  let comparisonFunctor : B.FullSubcategory ⥤ D / (^⊥B) := B.ι ⋙ quotientFunctor
  letI : comparisonFunctor.IsEquivalence := by
    change Functor.IsEquivalence (B.ι ⋙ (^⊥B).trW.Q)
    infer_instance
  let e : B.FullSubcategory ≌ D / (^⊥B) :=
    Localization.uniq B.ι.leftAdjoint quotientFunctor (^⊥B).trW
  let adj : B.ι.leftAdjoint ⊣ B.ι := Adjunction.ofIsRightAdjoint B.ι
  let i : e.functor ≅ comparisonFunctor :=
    (Functor.leftUnitor e.functor).symm ≪≫
      Functor.isoWhiskerRight (asIso adj.counit).symm e.functor ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft B.ι
        (Localization.compUniqFunctor B.ι.leftAdjoint quotientFunctor (^⊥B).trW)
  let j : e.inverse ≅ comparisonFunctor.asEquivalence.inverse :=
    Adjunction.rightAdjointUniq (e.changeFunctor i).toAdjunction
      comparisonFunctor.asEquivalence.toAdjunction
  (Localization.compUniqInverse B.ι.leftAdjoint quotientFunctor (^⊥B).trW).symm ≪≫
    Functor.isoWhiskerLeft quotientFunctor j

end

end CategoryTheory.ObjectProperty
