import Mathlib
import stacks_proof.stacks_project.Chap13.Lemma_13_11_6
import stacks_proof.stacks_project.Chap13.Lemma_13_35_7
import stacks_proof.stacks_project.Chap13.Remark_13_12_4
import stacks_proof.stacks_project.Chap13.Lemma_13_42_3
import stacks_proof.stacks_project.Chap15.Definition_15_75_1
import stacks_proof.stacks_project.Chap15.Lemma_15_65_2

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open CategoryTheory.Pretriangulated
open DerivedCategory.TStructure

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]

local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "DbMod" => boundedDerivedCategory (ModuleCat R)
local notation "H" => DerivedCategory.homologyFunctor (ModuleCat R)
local notation "Hb" => boundedDerivedHomologyFunctor (ModuleCat R)
local notation "PerfectObj" => (DerivedCategory.IsPerfect : ObjectProperty DMod)
local notation "Cpx" => CochainComplex (ModuleCat R) ℤ

/- Domain-style sampling for Lemma 15.75.7:
- primary domain: perfect objects in the bounded derived category `D^b(R)`, with the cohomology
  modules viewed through the chapter owners `DerivedCategory.IsPerfect` and `ModuleCat.IsPerfect`;
- sampled owner declarations:
  `boundedDerivedCategory`,
  `boundedDerivedHomologyFunctor`,
  `DerivedCategory.IsPerfect`,
  `ModuleCat.IsPerfect`,
  `CochainComplex.IsBoundedFiniteProjective`,
  `truncGE_step_homologyTriangle`,
  `singleFunctorIso_of_isGE_of_isLE`;
- best owner abstraction: this item is `source-facing`, while the core/canonical objects are the
  bounded derived object `K`, its ambient derived image `K.obj`, the lower truncation triangles,
  and the perfectness owner `K.obj.IsPerfect`;
- primitive vs. derived:
  primitive data are the bounded derived object `K` and the perfectness of each cohomology module
  `((Hb i).obj K)`;
  derived API is the perfectness of `K.obj`, obtained by peeling off one cohomology module at a
  time through the canonical truncation triangle;
- source/core/bridge triage:
  `source-facing`: the bounded-derived theorem below;
  `core/canonical`: `DerivedCategory.IsPerfect`, `CochainComplex.IsBoundedFiniteProjective`, and
    the standard truncation triangles;
  `bridge/view`: the bounded-derived homology functors `Hb i` and the single-object comparison
    isomorphisms in the derived category.

This file therefore follows the textbook truncation-induction route directly inside `D(R)`,
avoiding a parallel owner-level reformulation.
-/

/-- Helper for Lemma 15.75.7: shifting a bounded finite-projective complex preserves bounded
finite-projectivity. -/
theorem isBoundedFiniteProjective_shift
    (L : Cpx) [hL : CochainComplex.IsBoundedFiniteProjective L] (n : ℤ) :
    CochainComplex.IsBoundedFiniteProjective (L⟦n⟧) := by
  rcases hL.bounded with ⟨a, b, hge, hle⟩
  letI : L.IsStrictlyGE a := hge
  letI : L.IsStrictlyLE b := hle
  refine ⟨?_, ?_, ?_⟩
  · -- Proof comment: shifting translates the support interval by `-n`.
    refine ⟨a - n, b - n, ?_, ?_⟩
    · simpa using L.isStrictlyGE_shift a n (a - n) (by omega)
    · simpa using L.isStrictlyLE_shift b n (b - n) (by omega)
  · -- Proof comment: the shifted term in degree `i` is the original term in degree `i + n`.
    intro i
    simpa using hL.finite (i + n)
  · -- Proof comment: projectivity transports along the same translated term identification.
    intro i
    simpa using hL.projective (i + n)

instance (L : Cpx) [CochainComplex.IsBoundedFiniteProjective L] (n : ℤ) :
    CochainComplex.IsBoundedFiniteProjective (L⟦n⟧) :=
  isBoundedFiniteProjective_shift (R := R) L n

/-- Helper for Lemma 15.75.7: the mapping cone of a morphism between bounded finite-projective
complexes is again bounded finite-projective. -/
theorem isBoundedFiniteProjective_mappingCone
    {L M : Cpx} (f : L ⟶ M)
    [hL : CochainComplex.IsBoundedFiniteProjective L]
    [hM : CochainComplex.IsBoundedFiniteProjective M] :
    CochainComplex.IsBoundedFiniteProjective (CochainComplex.mappingCone f) := by
  rcases hL.bounded with ⟨aL, bL, hLGE, hLLE⟩
  rcases hM.bounded with ⟨aM, bM, hMGE, hMLE⟩
  refine ⟨?_, ?_, ?_⟩
  · -- Proof comment: a single interval covers both the shifted source and the target terms.
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
  · -- Proof comment: cone terms are biproducts of finite modules.
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

/-- Helper for Lemma 15.75.7: a bounded-above complex is a `ProjectiveMinus` complex once its
terms are projective. -/
private theorem minus_of_isStrictlyLE
    (L : Cpx) {b : ℤ} (hL : L.IsStrictlyLE b) :
    CochainComplex.minus (ModuleCat R) L :=
  (CochainComplex.minus_iff (ModuleCat R) L).2 ⟨b, hL⟩

/-- Helper for Lemma 15.75.7: a derived composite out of a bounded-above projective source can be
represented by an actual cochain map. -/
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
  -- Proof comment: conjugate the `Qh` equality back to the `Q`-level statement.
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

/-- Helper for Lemma 15.75.7: transporting a distinguished triangle along chosen representative
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
  -- Proof comment: distinguishedness is invariant under triangle isomorphism.
  refine isomorphic_distinguished _ hT _ ?_
  refine Triangle.isoMk _ _ e₁.symm e₂.symm (Iso.refl _) ?_ ?_ ?_
  · simp [Category.assoc]
  · simp
  · simp [Category.assoc]

/-- Helper for Lemma 15.75.7: a strict representative of the first morphism compares its
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
    simpa [T'] using transported_representative_triangle_distinguished (R := R) T hT e₁ e₂
  have hCone :
      DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle β) ∈ distTriang DMod := by
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

/-- Helper for Lemma 15.75.7: perfectness is stable under shifts in `D(R)`. -/
theorem isPerfect_shift
    (K : DMod) (n : ℤ) (hK : DerivedCategory.IsPerfect K) :
    DerivedCategory.IsPerfect (K⟦n⟧) := by
  rcases hK with ⟨L, e, hL⟩
  -- Proof comment: shift the bounded finite-projective representative termwise.
  refine ⟨L⟦n⟧, ?_, inferInstance⟩
  exact ((shiftFunctor DMod n).mapIso e) ≪≫ ((DerivedCategory.Q.commShiftIso n).app L).symm

/-- Helper for Lemma 15.75.7: in a distinguished triangle, perfectness of the first two vertices
implies perfectness of the third. -/
theorem isPerfect_obj₃_of_distinguishedTriangle
    (T : Triangle DMod) (hT : T ∈ distTriang DMod)
    (h₁ : DerivedCategory.IsPerfect T.obj₁) (h₂ : DerivedCategory.IsPerfect T.obj₂) :
    DerivedCategory.IsPerfect T.obj₃ := by
  -- Route correction: rather than searching for a separate abstract TR3 bridge, we use the
  -- source-faithful cone comparison directly and read the third isomorphism off that comparison.
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
    -- Proof comment: package the third component and its inverse into the final comparison
    -- isomorphism transporting perfectness to `T.obj₃`.
    exact ⟨φ.hom₃, φinv, hφ_hinv, hφinv_h⟩
  exact ObjectProperty.prop_of_iso (P := PerfectObj) e₃ hConePerfect

/-- Helper for Lemma 15.75.7: in a distinguished triangle, perfectness of the first and third
vertices implies perfectness of the middle. -/
theorem isPerfect_obj₂_of_distinguishedTriangle
    (T : Triangle DMod) (hT : T ∈ distTriang DMod)
    (h₁ : DerivedCategory.IsPerfect T.obj₁) (h₃ : DerivedCategory.IsPerfect T.obj₃) :
    DerivedCategory.IsPerfect T.obj₂ := by
  have h₃_shift : DerivedCategory.IsPerfect (T.obj₃⟦(-1 : ℤ)⟧) :=
    isPerfect_shift (R := R) T.obj₃ (-1) h₃
  -- Proof comment: in the inverse rotation, the original middle vertex becomes the third one.
  simpa [Triangle.invRotate_obj₃, Triangle.invRotate_obj₂] using
    isPerfect_obj₃_of_distinguishedTriangle
      (R := R) T.invRotate (inv_rot_of_distTriang _ hT) h₃_shift h₁

/-- Helper for Lemma 15.75.7: moving from the tail interval
`[a + 1, a + 1 + n]` to the full interval `[a, a + (n + 1)]`
is equivalent to remembering that the index is not `a`. -/
lemma mem_Icc_succ_trunc_iff (a j : ℤ) (n : ℕ) :
    j ∈ Set.Icc (a + 1) ((a + 1) + n) ↔ j ∈ Set.Icc a (a + (n + 1)) ∧ j ≠ a := by
  constructor
  · intro hj
    rcases hj with ⟨hleft, hright⟩
    constructor
    · constructor
      · omega
      · simpa [add_assoc, add_left_comm, add_comm] using hright
    · omega
  · rintro ⟨hj, hne⟩
    rcases hj with ⟨hleft, hright⟩
    constructor
    · have hlt : a < j := lt_of_le_of_ne hleft (by simpa [eq_comm] using hne)
      omega
    · simpa [add_assoc, add_left_comm, add_comm] using hright

/-- Helper for Lemma 15.75.7: a perfect module gives a perfect single object in any degree. -/
lemma singleFunctor_isPerfect_of_module_isPerfect
    (M : ModuleCat R) (i : ℤ) (hM : M.IsPerfect) :
    ((DerivedCategory.singleFunctor (ModuleCat R) i).obj M).IsPerfect := by
  let e :
      (((DerivedCategory.singleFunctor (ModuleCat R) i).obj M)⟦i⟧) ≅
        ((DerivedCategory.singleFunctor (ModuleCat R) (0 : ℤ)).obj M) :=
    ((DerivedCategory.singleFunctors (ModuleCat R)).shiftIso i 0 i (by simp)).app M
  have hShift :
      (((DerivedCategory.singleFunctor (ModuleCat R) i).obj M)⟦i⟧).IsPerfect := by
    -- Proof comment: after shifting by `i`, the degree-`i` single object becomes the degree-zero
    -- single object defining module perfectness.
    rw [ModuleCat.IsPerfect] at hM
    exact ObjectProperty.prop_of_iso (P := PerfectObj) e.symm hM
  have hBack :
      ((((DerivedCategory.singleFunctor (ModuleCat R) i).obj M)⟦i⟧)⟦(-i)⟧).IsPerfect :=
    isPerfect_shift (R := R) _ (-i) hShift
  -- Proof comment: shift back by `-i` and use the canonical double-shift isomorphism.
  exact ObjectProperty.prop_of_iso (P := PerfectObj) (shiftShiftNeg _ i) hBack

/-- Helper for Lemma 15.75.7: above the truncation cutoff, lower truncation preserves perfect
cohomology modules. -/
lemma truncGE_obj_homology_isPerfect_of_homology_isPerfect
    (K : DMod) (c i : ℤ) (hci : c ≤ i)
    (hperfect : ((H i).obj K).IsPerfect) :
    ((H i).obj ((t.truncGE c).obj K)).IsPerfect := by
  letI : IsIso ((H i).map ((t.truncGEπ c).app K)) :=
    isIso_homologyMap_truncGEπ_of_le (𝒜 := ModuleCat R) K c i hci
  let e :
      (H i).obj ((t.truncGE c).obj K) ≅ (H i).obj K :=
    (asIso ((H i).map ((t.truncGEπ c).app K))).symm
  -- Proof comment: identify the tail cohomology with the original module and transport
  -- perfectness through the degree-zero single-object embedding.
  rw [ModuleCat.IsPerfect] at hperfect ⊢
  exact ObjectProperty.prop_of_iso (P := PerfectObj)
    ((DerivedCategory.singleFunctor (ModuleCat R) (0 : ℤ)).mapIso e.symm) hperfect

/-- Helper for Lemma 15.75.7: if a derived object is supported in the finite interval
`[a, a + n]` and each cohomology module there is perfect, then the whole object is perfect. -/
theorem isPerfect_of_isGE_isLE_of_homology_isPerfect_upto
    (a : ℤ) (n : ℕ) (K : DMod)
    (hGE : K.IsGE a) (hLE : K.IsLE (a + n))
    (hH : ∀ i : Set.Icc a (a + n), ((H i.1).obj K).IsPerfect) :
    K.IsPerfect := by
  induction n generalizing a K with
  | zero =>
      letI : K.IsGE a := hGE
      letI : K.IsLE a := by simpa using hLE
      let e : K ≅ (DerivedCategory.singleFunctor (ModuleCat R) a).obj ((H a).obj K) :=
        singleFunctorIso_of_isGE_of_isLE (A := ModuleCat R) K a
      have hsingle :
          ((DerivedCategory.singleFunctor (ModuleCat R) a).obj ((H a).obj K)).IsPerfect := by
        -- Proof comment: in the one-degree case, `K` is exactly the single object on `H^a(K)`.
        exact singleFunctor_isPerfect_of_module_isPerfect ((H a).obj K) a (hH ⟨a, by simp⟩)
      exact ObjectProperty.prop_of_iso (P := PerfectObj) e.symm hsingle
  | succ n ih =>
      letI : K.IsGE a := hGE
      letI : K.IsLE (a + n + 1) := by
        convert hLE using 1
        omega
      let T := truncGE_step_homologyTriangle K a
      have hT : T ∈ distTriang DMod := by
        simpa [T] using truncGE_step_homology_triangle (K := K) a
      have h₁ : T.obj₁.IsPerfect := by
        -- Proof comment: the first vertex is the bottom cohomology term `H^a(K)[-a]`.
        simpa [T, truncGE_step_homologyTriangle] using
          singleFunctor_isPerfect_of_module_isPerfect
            ((H a).obj K) a (hH ⟨a, by
              constructor
              · omega
              · omega⟩)
      have hGEtail : ((t.truncGE (a + 1)).obj K).IsGE (a + 1) := by
        infer_instance
      have hLEtail : ((t.truncGE (a + 1)).obj K).IsLE ((a + 1) + n) := by
        convert (inferInstance : ((t.truncGE (a + 1)).obj K).IsLE (a + n + 1)) using 1
        omega
      have hHtail :
          ∀ i : Set.Icc (a + 1) ((a + 1) + n),
            ((H i.1).obj ((t.truncGE (a + 1)).obj K)).IsPerfect := by
        intro i
        have hi_step : i.1 ∈ Set.Icc a (a + (n + 1)) :=
          (mem_Icc_succ_trunc_iff a i.1 n).1 i.2 |>.1
        have hOrig : ((H i.1).obj K).IsPerfect := by
          exact hH ⟨i.1, by simpa [add_assoc, add_left_comm, add_comm] using hi_step⟩
        -- Proof comment: above the cutoff `a + 1`, lower truncation preserves `H^i`.
        exact truncGE_obj_homology_isPerfect_of_homology_isPerfect K (a + 1) i.1 i.2.1 hOrig
      have h₃ : T.obj₃.IsPerfect := by
        -- Proof comment: the induction hypothesis applies to the tail truncation.
        exact ih (a := a + 1) (K := (t.truncGE (a + 1)).obj K) hGEtail hLEtail hHtail
      have h₂ : T.obj₂.IsPerfect := by
        -- Proof comment: the local two-out-of-three lemma closes the truncation step.
        exact isPerfect_obj₂_of_distinguishedTriangle (R := R) T hT h₁ h₃
      have hπ : IsIso ((t.truncGEπ a).app K) :=
        (t.isGE_iff_isIso_truncGEπ_app a K).1 hGE
      -- Proof comment: because `K ∈ D^{≥ a}`, `τ_{≥ a}K` is canonically isomorphic to `K`.
      exact ObjectProperty.prop_of_iso (P := PerfectObj) (asIso ((t.truncGEπ a).app K)).symm h₂

/-- Lemma 15.75.7: if a bounded derived `R`-complex has perfect cohomology modules in every
degree, then the complex itself is perfect. -/
@[stacks 066U]
theorem isPerfect_of_bounded_of_homology_isPerfect
    (K : DbMod)
    (hH : ∀ i : ℤ, ((Hb i).obj K).IsPerfect) :
    K.obj.IsPerfect := by
  rcases (derivedCategory_t_bounded_iff K.obj).1 K.property with ⟨⟨c, hc⟩, ⟨d, hd⟩⟩
  let c' : ℤ := min c d
  have hGE : K.obj.IsGE c' := by
    -- Proof comment: move the lower support bound to `min c d`.
    rw [DerivedCategory.isGE_iff]
    intro i hi
    exact hc i (lt_of_lt_of_le hi (min_le_left _ _))
  have hLEd : K.obj.IsLE d := by
    -- Proof comment: keep the original upper support bound from the boundedness witness.
    rw [DerivedCategory.isLE_iff]
    intro i hi
    exact hd i hi
  have hnonneg : 0 ≤ d - c' := by
    dsimp [c']
    omega
  have hcd : c' + Int.toNat (d - c') = d := by
    rw [Int.toNat_of_nonneg hnonneg]
    omega
  have hLE : K.obj.IsLE (c' + Int.toNat (d - c')) := by
    rw [hcd]
    exact hLEd
  have hH' :
      ∀ i : Set.Icc c' (c' + Int.toNat (d - c')),
        ((H i.1).obj K.obj).IsPerfect := by
    intro i
    -- Proof comment: bounded-derived homology is just ambient homology after forgetting to `D(R)`.
    simpa [CategoryTheory.boundedDerivedHomologyFunctor, hcd] using hH i.1
  -- Proof comment: boundedness leaves only finitely many nonzero cohomology modules, so the
  -- truncation induction applies on the finite support interval.
  simpa [hcd] using
    isPerfect_of_isGE_isLE_of_homology_isPerfect_upto
      (R := R) c' (Int.toNat (d - c')) K.obj hGE hLE hH'

end

end CategoryTheory
