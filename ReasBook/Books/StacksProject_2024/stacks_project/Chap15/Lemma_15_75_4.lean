import StacksProject_2024.Chap15.Definition_15_75_1
import StacksProject_2024.Chap15.Lemma_15_65_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open CategoryTheory.Pretriangulated

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [Ring R]

local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "PerfectObj" => (DerivedCategory.IsPerfect : ObjectProperty DMod)
local notation "Cpx" => CochainComplex (ModuleCat R) ℤ

/-- Helper for Lemma 15.75.4: shifting a bounded finite-projective complex preserves bounded
finite-projectivity. -/
theorem isBoundedFiniteProjective_shift
    (L : Cpx) [hL : CochainComplex.IsBoundedFiniteProjective L] (n : ℤ) :
    CochainComplex.IsBoundedFiniteProjective (L⟦n⟧) := by
  rcases hL.bounded with ⟨a, b, hge, hle⟩
  letI : L.IsStrictlyGE a := hge
  letI : L.IsStrictlyLE b := hle
  refine ⟨?_, ?_, ?_⟩
  · -- Proof comment: the shift translates any support interval `[a, b]` to `[a - n, b - n]`.
    refine ⟨a - n, b - n, ?_, ?_⟩
    · simpa using L.isStrictlyGE_shift a n (a - n) (by omega)
    · simpa using L.isStrictlyLE_shift b n (b - n) (by omega)
  · -- Proof comment: each shifted term is definitionally the translated original term.
    intro i
    simpa using hL.finite (i + n)
  · -- Proof comment: projectivity is transported along the same translated term identification.
    intro i
    simpa using hL.projective (i + n)

instance (L : Cpx) [CochainComplex.IsBoundedFiniteProjective L] (n : ℤ) :
    CochainComplex.IsBoundedFiniteProjective (L⟦n⟧) :=
  isBoundedFiniteProjective_shift (R := R) L n

/-- Helper for Lemma 15.75.4: the mapping cone of a morphism between bounded finite-projective
complexes is again bounded finite-projective. -/
theorem isBoundedFiniteProjective_mappingCone
    {L M : Cpx} (f : L ⟶ M)
    [hL : CochainComplex.IsBoundedFiniteProjective L]
    [hM : CochainComplex.IsBoundedFiniteProjective M] :
    CochainComplex.IsBoundedFiniteProjective (CochainComplex.mappingCone f) := by
  rcases hL.bounded with ⟨aL, bL, hLGE, hLLE⟩
  rcases hM.bounded with ⟨aM, bM, hMGE, hMLE⟩
  refine ⟨?_, ?_, ?_⟩
  · -- Proof comment: one interval containing the shifted source support and the target support
    -- contains every nonzero cone term.
    refine ⟨min (aL - 1) aM, max (bL - 1) bM, ?_, ?_⟩
    · rw [CochainComplex.isStrictlyGE_iff]
      intro i hi
      have hLi : i + 1 < aL := by omega
      have hMi : i < aM := by omega
      have hLzero : IsZero (L.X (i + 1)) := by
        letI : L.IsStrictlyGE aL := hLGE
        simpa using L.isZero_of_isStrictlyGE aL (i + 1) hLi
      have hMzero : IsZero (M.X i) := by
        letI : M.IsStrictlyGE aM := hMGE
        simpa using M.isZero_of_isStrictlyGE aM i hMi
      rw [CochainComplex.mappingCone.isZero_X_iff (φ := f) i]
      exact ⟨hLzero, hMzero⟩
    · rw [CochainComplex.isStrictlyLE_iff]
      intro i hi
      have hLi : bL < i + 1 := by omega
      have hMi : bM < i := by omega
      have hLzero : IsZero (L.X (i + 1)) := by
        letI : L.IsStrictlyLE bL := hLLE
        simpa using L.isZero_of_isStrictlyLE bL (i + 1) hLi
      have hMzero : IsZero (M.X i) := by
        letI : M.IsStrictlyLE bM := hMLE
        simpa using M.isZero_of_isStrictlyLE bM i hMi
      rw [CochainComplex.mappingCone.isZero_X_iff (φ := f) i]
      exact ⟨hLzero, hMzero⟩
  · -- Proof comment: each cone term is a biproduct of two finite modules.
    intro i
    let e :
        (CochainComplex.mappingCone f).X i ≅ ModuleCat.of R (L.X (i + 1) × M.X i) :=
      (HomologicalComplex.homotopyCofiber.XIsoBiprod f i (i + 1)
          (ComplexShape.up_mk i (i + 1) rfl)) ≪≫
        ModuleCat.biprodIsoProd _ _
    exact Module.Finite.equiv e.symm.toLinearEquiv
  · -- Proof comment: the same biproduct description preserves projectivity degreewise.
    intro i
    let e :
        (CochainComplex.mappingCone f).X i ≅ ModuleCat.of R (L.X (i + 1) × M.X i) :=
      (HomologicalComplex.homotopyCofiber.XIsoBiprod f i (i + 1)
          (ComplexShape.up_mk i (i + 1) rfl)) ≪≫
        ModuleCat.biprodIsoProd _ _
    exact Module.Projective.of_equiv e.symm.toLinearEquiv

instance {L M : Cpx} (f : L ⟶ M)
    [CochainComplex.IsBoundedFiniteProjective L]
    [CochainComplex.IsBoundedFiniteProjective M] :
    CochainComplex.IsBoundedFiniteProjective (CochainComplex.mappingCone f) :=
  isBoundedFiniteProjective_mappingCone (R := R) f

/-- Helper for Lemma 15.75.4: a bounded-above complex is a `ProjectiveMinus` complex once its
terms are projective. -/
private theorem minus_of_isStrictlyLE
    (L : Cpx) {b : ℤ} (hL : L.IsStrictlyLE b) :
    CochainComplex.minus (ModuleCat R) L :=
  (CochainComplex.minus_iff (ModuleCat R) L).2 ⟨b, hL⟩

/-- Helper for Lemma 15.75.4: a derived composite out of a bounded-above projective source can be
represented by a literal cochain map. -/
private theorem exists_projective_minus_representative_of_composite
    (P : CochainComplex.ProjectiveMinus (ModuleCat R))
    {K L : Cpx} (ξ : (P : Cpx) ⟶ K)
    (α : DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj L) :
    ∃ β : (P : Cpx) ⟶ L, DerivedCategory.Q.map β = DerivedCategory.Q.map ξ ≫ α := by
  let Ho := HomotopyCategory.quotient (ModuleCat R) (ComplexShape.up ℤ)
  let eP := (DerivedCategory.quotientCompQhIso (ModuleCat R)).app (P : Cpx)
  let eL := (DerivedCategory.quotientCompQhIso (ModuleCat R)).app L
  let δ : DerivedCategory.Qh.obj (Ho.obj P) ⟶ DerivedCategory.Qh.obj (Ho.obj L) :=
    eP.hom ≫ DerivedCategory.Q.map ξ ≫ α ≫ eL.inv
  obtain ⟨βh, hβh⟩ :=
    (CochainComplex.homotopyCategory_to_derived_bijective_of_boundedAbove_projective P L).surjective
      δ
  obtain ⟨β, hβ⟩ := Ho.map_surjective βh
  refine ⟨β, ?_⟩
  have hQh :
      DerivedCategory.Qh.map (Ho.map β) = δ := by
    simpa [hβ] using hβh
  -- Proof comment: conjugate the `Qh`-identity back along `quotientCompQhIso` to recover the
  -- desired `Q`-map equality.
  calc
    DerivedCategory.Q.map β =
        (Iso.homCongr eP eL) (DerivedCategory.Qh.map (Ho.map β)) := by
          change
            (DerivedCategory.quotientCompQhIso (ModuleCat R)).inv.app (P : Cpx) ≫
                DerivedCategory.Qh.map (Ho.map β) ≫
                  (DerivedCategory.quotientCompQhIso (ModuleCat R)).hom.app L =
              DerivedCategory.Q.map β
          have hnat :
              DerivedCategory.Qh.map (Ho.map β) ≫
                  (DerivedCategory.quotientCompQhIso (ModuleCat R)).hom.app L =
                (DerivedCategory.quotientCompQhIso (ModuleCat R)).hom.app (P : Cpx) ≫
                  DerivedCategory.Q.map β := by
            simpa [Functor.comp_map] using
              (DerivedCategory.quotientCompQhIso (ModuleCat R)).hom.naturality β
          calc
            (DerivedCategory.quotientCompQhIso (ModuleCat R)).inv.app (P : Cpx) ≫
                DerivedCategory.Qh.map (Ho.map β) ≫
                  (DerivedCategory.quotientCompQhIso (ModuleCat R)).hom.app L =
              (DerivedCategory.quotientCompQhIso (ModuleCat R)).inv.app (P : Cpx) ≫
                ((DerivedCategory.quotientCompQhIso (ModuleCat R)).hom.app (P : Cpx) ≫
                  DerivedCategory.Q.map β) := by
                    simpa [Category.assoc] using
                      congrArg
                        (fun k ↦
                          (DerivedCategory.quotientCompQhIso (ModuleCat R)).inv.app (P : Cpx) ≫
                            k)
                        hnat
            _ = DerivedCategory.Q.map β := by
                  simpa using
                    (Iso.inv_hom_id_assoc
                      ((DerivedCategory.quotientCompQhIso (ModuleCat R)).app (P : Cpx))
                      (DerivedCategory.Q.map β))
    _ = (Iso.homCongr eP eL) δ := by simpa [hQh]
    _ = DerivedCategory.Q.map ξ ≫ α := by
      change eP.inv ≫ (eP.hom ≫ DerivedCategory.Q.map ξ ≫ α ≫ eL.inv) ≫ eL.hom =
        DerivedCategory.Q.map ξ ≫ α
      simp [Category.assoc]

/-- Helper for Lemma 15.75.4: transporting a distinguished triangle along chosen representative
isomorphisms on the first two vertices keeps it distinguished. -/
private theorem transported_representative_triangle_distinguished
    (T : Triangle DMod) (hT : T ∈ distTriang DMod)
    {L M : Cpx}
    (e₁ : T.obj₁ ≅ DerivedCategory.Q.obj L)
    (e₂ : T.obj₂ ≅ DerivedCategory.Q.obj M) :
    Triangle.mk
        (e₁.inv ≫ T.mor₁ ≫ e₂.hom)
        (e₂.inv ≫ T.mor₂)
        (T.mor₃ ≫ e₁.hom⟦(1 : ℤ)⟧') ∈
      distTriang DMod := by
  -- Proof comment: distinguishedness is invariant under triangle isomorphism, so conjugating the
  -- first two vertices by the chosen representative isomorphisms preserves it.
  refine isomorphic_distinguished _ hT _ ?_
  refine Triangle.isoMk _ _ e₁.symm e₂.symm (Iso.refl _) ?_ ?_ ?_
  · simp [Category.assoc]
  · simp
  · simp [Category.assoc]

/-- Helper for Lemma 15.75.4: a strict representative of the first morphism compares its
mapping-cone triangle to the transported distinguished triangle. -/
private theorem exists_mappingCone_comparison_to_representative_triangle
    (T : Triangle DMod) (hT : T ∈ distTriang DMod)
    {L M : Cpx}
    (e₁ : T.obj₁ ≅ DerivedCategory.Q.obj L)
    (e₂ : T.obj₂ ≅ DerivedCategory.Q.obj M)
    (β : L ⟶ M)
    (hβ : DerivedCategory.Q.map β = e₁.inv ≫ T.mor₁ ≫ e₂.hom) :
    ∃ φ :
      DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle β) ⟶
        Triangle.mk
          (e₁.inv ≫ T.mor₁ ≫ e₂.hom)
          (e₂.inv ≫ T.mor₂)
          (T.mor₃ ≫ e₁.hom⟦(1 : ℤ)⟧'),
      φ.hom₁ = 𝟙 _ ∧ φ.hom₂ = 𝟙 _ := by
  let T' : Triangle DMod :=
    Triangle.mk
      (e₁.inv ≫ T.mor₁ ≫ e₂.hom)
      (e₂.inv ≫ T.mor₂)
      (T.mor₃ ≫ e₁.hom⟦(1 : ℤ)⟧')
  have hT' : T' ∈ distTriang DMod := by
    -- Proof comment: this is exactly the transported triangle from the previous helper.
    simpa [T'] using transported_representative_triangle_distinguished (R := R) T hT e₁ e₂
  have hCone :
      DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle β) ∈ distTriang DMod := by
    -- Proof comment: mapping-cone triangles are distinguished in the derived category.
    simpa using DerivedCategory.mappingCone_triangle_distinguished β
  obtain ⟨c, hc₂, hc₃⟩ :=
    complete_distinguished_triangle_morphism
      (DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle β))
      T'
      hCone hT'
      (𝟙 _) (𝟙 _)
      (by simpa [T'] using hβ)
  -- Proof comment: package the TR3 completion as an explicit triangle morphism.
  refine ⟨
    { hom₁ := 𝟙 _
      hom₂ := 𝟙 _
      hom₃ := c
      comm₁ := by simpa [T'] using hβ
      comm₂ := hc₂
      comm₃ := hc₃ },
    rfl, rfl⟩

/- Proof sketch: shift a bounded finite-projective representative termwise and transport the
result through `DerivedCategory.Q.commShiftIso`. -/
/-- Helper for Lemma 15.75.4: perfectness is stable under shifts in `D(R)`. -/
theorem isPerfect_shift
    (K : DMod) (n : ℤ) (hK : DerivedCategory.IsPerfect K) :
    DerivedCategory.IsPerfect (K⟦n⟧) := by
  rcases hK with ⟨L, e, hL⟩
  -- Proof comment: the shifted representative `L⟦n⟧` still has bounded finite-projective terms.
  refine ⟨L⟦n⟧, ?_, inferInstance⟩
  -- Proof comment: compare `K⟦n⟧` with `Q.obj (L⟦n⟧)` using the chosen representative isomorphism
  -- and the standard shift-commutation isomorphism for `Q`.
  exact ((shiftFunctor DMod n).mapIso e) ≪≫ ((DerivedCategory.Q.commShiftIso n).app L).symm

/- Proof sketch: choose bounded finite-projective representatives for the first two vertices,
strictify the first derived morphism between them, identify the third vertex with the mapping cone
via TR3, and then use that mapping cones preserve bounded finite-projectivity. -/
/-- Helper for Lemma 15.75.4: in a distinguished triangle of `D(R)`, if the first two objects are
perfect, then the third is perfect. -/
theorem isPerfect_obj₃_of_distinguishedTriangle
    (T : Triangle DMod) (hT : T ∈ distTriang DMod)
    (h₁ : DerivedCategory.IsPerfect T.obj₁) (h₂ : DerivedCategory.IsPerfect T.obj₂) :
    DerivedCategory.IsPerfect T.obj₃ := by
  rcases h₁ with ⟨L, e₁, hL⟩
  rcases h₂ with ⟨M, e₂, hM⟩
  rcases hL.bounded with ⟨_, bL, _, hLLE⟩
  letI : CochainComplex.IsBoundedFiniteProjective L := hL
  letI : CochainComplex.IsBoundedFiniteProjective M := hM
  have hLminus : CochainComplex.minus (ModuleCat R) L := by
    -- Proof comment: bounded-above support turns the first representative into a `ProjectiveMinus`
    -- complex, which is exactly the source API needed for strictifying derived morphisms.
    exact minus_of_isStrictlyLE (R := R) L hLLE
  let Lproj : CochainComplex.ProjectiveMinus (ModuleCat R) :=
    ⟨⟨L, hLminus⟩, fun i ↦ by infer_instance⟩
  obtain ⟨β, hβ⟩ :=
    exists_projective_minus_representative_of_composite
      (R := R) Lproj (𝟙 L) (e₁.inv ≫ T.mor₁ ≫ e₂.hom)
  have hβ' : DerivedCategory.Q.map β = e₁.inv ≫ T.mor₁ ≫ e₂.hom := by
    calc
      DerivedCategory.Q.map β =
          DerivedCategory.Q.map (𝟙 L) ≫ (e₁.inv ≫ T.mor₁ ≫ e₂.hom) := hβ
      _ = e₁.inv ≫ T.mor₁ ≫ e₂.hom := by simp
  obtain ⟨φ, hφ₁, hφ₂⟩ :=
    exists_mappingCone_comparison_to_representative_triangle
      (R := R) T hT e₁ e₂ β hβ'
  let T' : Triangle DMod :=
    Triangle.mk
      (e₁.inv ≫ T.mor₁ ≫ e₂.hom)
      (e₂.inv ≫ T.mor₂)
      (T.mor₃ ≫ e₁.hom⟦(1 : ℤ)⟧')
  have hT' : T' ∈ distTriang DMod := by
    -- Proof comment: this is the same transported distinguished triangle used in the TR3 step.
    simpa [T'] using transported_representative_triangle_distinguished (R := R) T hT e₁ e₂
  have hCone :
      DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle β) ∈ distTriang DMod := by
    simpa using DerivedCategory.mappingCone_triangle_distinguished β
  have hIso₁ : IsIso φ.hom₁ := by
    rw [hφ₁]
    exact ⟨⟨𝟙 _, by simp, by simp⟩⟩
  have hIso₂ : IsIso φ.hom₂ := by
    rw [hφ₂]
    exact ⟨⟨𝟙 _, by simp, by simp⟩⟩
  have hφ₃ : IsIso φ.hom₃ := by
    -- Proof comment: the comparison morphism is the identity on the first two vertices, so the
    -- triangulated two-out-of-three theorem forces the third component to be an isomorphism.
    simpa [hφ₁, hφ₂] using
      (Pretriangulated.isIso₃_of_isIso₁₂ φ hCone hT' hIso₁ hIso₂ : IsIso φ.hom₃)
  have hConePerfect :
      DerivedCategory.IsPerfect (DerivedCategory.Q.obj (CochainComplex.mappingCone β)) := by
    -- Proof comment: the mapping cone itself is a bounded finite-projective representative of its
    -- image in the derived category.
    refine ⟨CochainComplex.mappingCone β, Iso.refl _, ?_⟩
    infer_instance
  let φinv : T.obj₃ ⟶ DerivedCategory.Q.obj (CochainComplex.mappingCone β) :=
    Classical.choose hφ₃.out
  have hφ_hinv : φ.hom₃ ≫ φinv = 𝟙 _ := (Classical.choose_spec hφ₃.out).1
  have hφinv_h : φinv ≫ φ.hom₃ = 𝟙 _ := (Classical.choose_spec hφ₃.out).2
  let e₃ : DerivedCategory.Q.obj (CochainComplex.mappingCone β) ≅ T.obj₃ := by
    exact ⟨φ.hom₃, φinv, hφ_hinv, hφinv_h⟩
  exact ObjectProperty.prop_of_iso (P := PerfectObj) e₃ hConePerfect

/- Domain-style sampling for Lemma 15.75.4:
- primary domain: perfect objects in the derived category `D(R)` as an object property and their
  behavior with respect to distinguished triangles;
- sampled owner declarations:
  `DerivedCategory.IsPerfect`,
  `CochainComplex.IsBoundedFiniteProjective`,
  `ObjectProperty.IsTriangulated`,
  `ObjectProperty.IsStableUnderShift`;
- best owner abstraction: the canonical owner is the object property `PerfectObj`, and this file
  should expose its `ObjectProperty.IsTriangulated` instance directly rather than introducing a
  parallel eta-expanded surface for the same object property;
- primitive vs. derived:
  primitive data are the perfectness predicate `DerivedCategory.IsPerfect` and its defining
  bounded finite-projective representatives from Definition `15.75.1`;
  derived API is the triangulated closure statement for the perfectness object property;
- source/core/bridge triage:
  `source-facing`: the textbook two-out-of-three statement for perfect complexes in distinguished
    triangles;
  `core/canonical`: `ObjectProperty.IsTriangulated PerfectObj`;
  `bridge/view`: concrete bounded finite-projective representatives witnessing perfectness.

This file targets the `core/canonical` layer so downstream files can reuse the owner instance
directly instead of redeclaring parallel local copies.
-/
-- Proof sketch: use the canonical owner-level two-out-of-three statement for perfect complexes in
-- distinguished triangles, regarding perfectness as the object property on `D(R)` defined by
-- bounded finite-projective representatives.
/-- Lemma 15.75.4: the object property of being a perfect complex in `D(R)` is triangulated.
Equivalently, in a distinguished triangle of `D(R)`, if two of the three objects are perfect,
then so is the third. -/
instance perfectObjectProperty_isTriangulated :
    ObjectProperty.IsTriangulated PerfectObj := by
  refine
    { exists_zero := ?_
      toIsStableUnderShift := ?_
      toIsTriangulatedClosed₂ := ?_ }
  · -- Proof comment: the zero complex is itself a bounded finite-projective representative of the
    -- zero object in the derived category.
    classical
    let Z : Cpx := Classical.choose (HasZeroObject.zero (C := Cpx))
    let hZzero : IsZero Z := Classical.choose_spec (HasZeroObject.zero (C := Cpx))
    let hQZzero : IsZero (DerivedCategory.Q.obj Z) := Functor.map_isZero DerivedCategory.Q hZzero
    let zeroModule : ModuleCat R := ModuleCat.of R PUnit
    let hZeroModule : IsZero zeroModule := ModuleCat.isZero_of_subsingleton zeroModule
    have hZperfect : DerivedCategory.IsPerfect (DerivedCategory.Q.obj Z) := by
      refine ⟨Z, Iso.refl _, ?_⟩
      refine
        ⟨⟨0, 0,
            ?_,
            ?_⟩,
          ?_,
          ?_⟩
      · -- Proof comment: every term of a zero complex is zero, so the lower support bound is
        -- automatic.
        rw [CochainComplex.isStrictlyGE_iff]
        intro i hi
        exact Functor.map_isZero (HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℤ) i) hZzero
      · -- Proof comment: the same zero-term argument gives the upper support bound.
        rw [CochainComplex.isStrictlyLE_iff]
        intro i hi
        exact Functor.map_isZero (HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℤ) i) hZzero
      · intro i
        let hZi : IsZero (Z.X i) :=
          Functor.map_isZero (HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℤ) i) hZzero
        let eZi : Z.X i ≅ zeroModule :=
          hZi.isoZero ≪≫ hZeroModule.isoZero.symm
        exact Module.Finite.equiv eZi.symm.toLinearEquiv
      · intro i
        let hZi : IsZero (Z.X i) :=
          Functor.map_isZero (HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℤ) i) hZzero
        let eZi : Z.X i ≅ zeroModule :=
          hZi.isoZero ≪≫ hZeroModule.isoZero.symm
        exact Module.Projective.of_equiv eZi.symm.toLinearEquiv
    exact ⟨DerivedCategory.Q.obj Z, hQZzero, hZperfect⟩
  · refine ⟨fun n ↦ ⟨fun K hK ↦ ?_⟩⟩
    -- Proof comment: shift the chosen bounded finite-projective representative termwise.
    exact isPerfect_shift (R := R) K n hK
  · refine ObjectProperty.IsTriangulatedClosed₂.mk' ?_
    intro T hT h₁ h₃
    have h₃_shift : DerivedCategory.IsPerfect (T.obj₃⟦(-1 : ℤ)⟧) := by
      -- Proof comment: inverse rotation asks for the shifted third vertex as its first term.
      exact isPerfect_shift (R := R) T.obj₃ (-1) h₃
    -- Proof comment: apply the third-vertex clause to the inverse-rotated distinguished triangle.
    simpa using
      isPerfect_obj₃_of_distinguishedTriangle
        (R := R) (T := T.invRotate) (hT := inv_rot_of_distTriang _ hT) h₃_shift h₁

end

end CategoryTheory
