import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import StacksProject_2024.Chap12.Definition_12_12_1
import StacksProject_2024.Chap21.Lemma_21_9_1

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable (U : C) [HasFiniteProducts (Over U)] [HasProducts AddCommGrpCat.{v}]
variable {ι : Type w} (family : ι → Over U)

/- Domain-style sampling for Lemma 21.9.2:
- primary domain: cohomological `δ`-functors on abelian presheaves arising from the long exact
  homology sequence of short exact sequences of Čech complexes;
- sampled canonical declarations:
  `cechComplex`,
  `cechComplexOnPresheaves_exact`,
  `ShortComplex.ShortExact.map_of_exact`,
  `CohomologicalDeltaFunctor`,
  `HomologicalComplex.HomologySequence.δ_naturality`;
- best owner abstraction:
  `source-facing`: the Čech cohomology `δ`-functor attached to `family`;
  `core/canonical`: `CohomologicalDeltaFunctor` together with the homology-sequence API for the
    mapped short exact sequence of cochain complexes;
  `bridge/view`: restriction along `(Over.forget U).op`, the induced exact Čech-complex functor on
    presheaves, and the resulting connecting morphism.
- primitive data: `family`, the exact Čech-complex functor on `Over U`, and the mapped short exact
  sequence of cochain complexes;
- derived API: the degreewise cohomology functors, the connecting morphisms, and the assembled
  `CohomologicalDeltaFunctor`.

The public owner should therefore be `cechCohomologyDeltaFunctor`; the adjacent exactness windows
and naturality identities are derived from the canonical homology-sequence API and should not
remain as parallel public wrappers. The restriction-plus-Čech complex owner itself is already
provided by `21_9_0_1` as `cechComplexOnPresheaves`, and Lemma `21.9.1` now owns its exactness, so
this file should reuse that public source-facing API rather than redeclare a private duplicate.
-/

/-- The composite restriction-plus-Čech complex functor is additive. -/
private noncomputable instance cechComplexOnPresheaves_additive :
    (cechComplexOnPresheaves U family).Additive :=
  (exactFunctor_le_additiveFunctor
    (Cᵒᵖ ⥤ AddCommGrpCat)
    (CochainComplex AddCommGrpCat ℕ))
    (cechComplexOnPresheaves U family)
    (cechComplexOnPresheaves_exact U family)

/-- A short exact sequence of abelian presheaves induces a short exact sequence of Čech
complexes. -/
private theorem cechComplexOnPresheaves_map_shortExact
    {S : ShortComplex (Cᵒᵖ ⥤ AddCommGrpCat)} (hS : S.ShortExact) :
    (S.map (cechComplexOnPresheaves U family)).ShortExact := by
  let hExact := cechComplexOnPresheaves_exact U family
  rw [exactFunctor_iff] at hExact
  let _ : (cechComplexOnPresheaves U family).PreservesZeroMorphisms := by infer_instance
  let _ : PreservesFiniteLimits (cechComplexOnPresheaves U family) :=
    hExact.1
  let _ : PreservesFiniteColimits (cechComplexOnPresheaves U family) :=
    hExact.2
  exact hS.map_of_exact (cechComplexOnPresheaves U family)

/-- The additive degree-`n` Čech cohomology functor `F ↦ cechCohomology U family F n`. -/
abbrev cechCohomologyDegree (n : ℕ) :
    (Cᵒᵖ ⥤ AddCommGrpCat) ⥤+ AddCommGrpCat :=
  AdditiveFunctor.of
    (cechComplexOnPresheaves U family ⋙
      HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.up ℕ) n)

/-- Evaluating `cechCohomologyDegree U family n` at a presheaf recovers the degree-`n`
Čech cohomology object `cechCohomology U family F n`. -/
@[simp] theorem cechCohomologyDegree_obj_obj (n : ℕ)
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{v}) :
    (cechCohomologyDegree U family n).obj.obj F = cechCohomology U family F n :=
  rfl

/-- The connecting morphism in degree `n` attached to a short exact sequence of abelian
presheaves. -/
noncomputable def cechCohomologyConnectingMorphism
    {S : ShortComplex (Cᵒᵖ ⥤ AddCommGrpCat)} (hS : S.ShortExact) (n : ℕ) :
    cechCohomology U family S.X₃ n ⟶ cechCohomology U family S.X₁ (n + 1) :=
  (cechComplexOnPresheaves_map_shortExact U family hS).δ n (n + 1)
    (ComplexShape.up_mk n (n + 1) rfl)

/-- Helper for Lemma 21.9.2: the degree-`n` Čech cohomology functor sends a morphism of abelian
presheaves to the induced map on homology of the Čech cochain complexes. -/
@[simp] private theorem cechCohomologyDegree_map_eq
    {F G : Cᵒᵖ ⥤ AddCommGrpCat.{v}} (n : ℕ) (α : F ⟶ G) :
    ((cechCohomologyDegree U family n).obj.map α) =
      HomologicalComplex.homologyMap ((cechComplexOnPresheaves U family).map α) n :=
  rfl

omit [HasProducts AddCommGrpCat.{v}] in
/-- Helper for Lemma 21.9.2: the cochain complex shape `ComplexShape.up ℕ` has no relation into
degree `0`. -/
private theorem complexShapeUp_notRel_zero (i : ℕ) :
    ¬ (ComplexShape.up ℕ).Rel i 0 := by
  intro h
  simp at h

/-- Helper for Lemma 21.9.2: the degree-`0` Čech cohomology map induced by the first arrow of a
short exact sequence is monic. -/
private theorem cechCohomology_mono_map_f_zero
    {S : ShortComplex (Cᵒᵖ ⥤ AddCommGrpCat)} (hS : S.ShortExact) :
    Mono ((cechCohomologyDegree U family 0).obj.map S.f) := by
  -- Normalize the degree-zero map to the canonical homology map of the Čech complex morphism.
  rw [cechCohomologyDegree_map_eq]
  let hShortExact := cechComplexOnPresheaves_map_shortExact U family hS
  let _ : Mono ((cechComplexOnPresheaves U family).map S.f) := by
    simpa using hShortExact.mono_f
  let _ : Mono (((cechComplexOnPresheaves U family).map S.f).f 0) := by infer_instance
  exact HomologicalComplex.mono_homologyMap_of_mono_of_not_rel
    ((cechComplexOnPresheaves U family).map S.f) 0 complexShapeUp_notRel_zero

/-- Helper for Lemma 21.9.2: the image of the degree-`n` Čech cohomology map induced by `S.g`
lies in the kernel of the Čech connecting morphism. -/
@[simp, reassoc] private theorem cechCohomology_map_g_comp_connectingMorphism_aux
    {S : ShortComplex (Cᵒᵖ ⥤ AddCommGrpCat)} (hS : S.ShortExact) (n : ℕ) :
    ((cechCohomologyDegree U family n).obj.map S.g) ≫
        cechCohomologyConnectingMorphism U family hS n = 0 := by
  -- Normalize to the canonical homology-sequence composite `g ≫ δ`.
  rw [cechCohomologyDegree_map_eq]
  simpa only [cechCohomologyConnectingMorphism] using
    (cechComplexOnPresheaves_map_shortExact U family hS).comp_δ
      n (n + 1) (ComplexShape.up_mk n (n + 1) rfl)

/-- Helper for Lemma 21.9.2: the Čech connecting morphism lands in the kernel of the degree
`n + 1` map induced by `S.f`. -/
@[simp, reassoc] private theorem cechCohomologyConnectingMorphism_comp_map_f_aux
    {S : ShortComplex (Cᵒᵖ ⥤ AddCommGrpCat)} (hS : S.ShortExact) (n : ℕ) :
    cechCohomologyConnectingMorphism U family hS n ≫
        ((cechCohomologyDegree U family (n + 1)).obj.map S.f) = 0 := by
  -- Normalize to the canonical homology-sequence composite `δ ≫ f`.
  rw [cechCohomologyDegree_map_eq]
  simpa only [cechCohomologyConnectingMorphism] using
    (cechComplexOnPresheaves_map_shortExact U family hS).δ_comp
      n (n + 1) (ComplexShape.up_mk n (n + 1) rfl)

/-- Helper for Lemma 21.9.2: applying degree-`n` Čech cohomology to a short exact sequence
produces an exact two-term row. -/
private theorem cechCohomology_map_exact
    {S : ShortComplex (Cᵒᵖ ⥤ AddCommGrpCat)} (hS : S.ShortExact) (n : ℕ) :
    (S.map (cechCohomologyDegree U family n).obj).Exact := by
  -- This is the degreewise exactness window in homology for the mapped Čech complexes.
  simpa only [cechCohomologyDegree_map_eq] using
    (cechComplexOnPresheaves_map_shortExact U family hS).homology_exact₂ n

/-- Helper for Lemma 21.9.2: the adjacent Čech cohomology window
`Hⁿ(X₂) ⟶ Hⁿ(X₃) ⟶ Hⁿ⁺¹(X₁)` is exact. -/
private theorem cechCohomology_exact_map_g_connectingMorphism
    {S : ShortComplex (Cᵒᵖ ⥤ AddCommGrpCat)} (hS : S.ShortExact) (n : ℕ) :
    (ShortComplex.mk
      ((cechCohomologyDegree U family n).obj.map S.g)
      (cechCohomologyConnectingMorphism U family hS n)
      (cechCohomology_map_g_comp_connectingMorphism_aux U family hS n)).Exact := by
  -- This is the adjacent exactness statement `homology_exact₃` for the mapped Čech complexes.
  simpa only [cechCohomologyDegree_map_eq, cechCohomologyConnectingMorphism] using
    (cechComplexOnPresheaves_map_shortExact U family hS).homology_exact₃
      n (n + 1) (ComplexShape.up_mk n (n + 1) rfl)

/-- Helper for Lemma 21.9.2: the source-facing Čech window
`Hⁿ(X₃) ⟶ Hⁿ⁺¹(X₁) ⟶ Hⁿ⁺¹(X₂)` is definitionally the owner short complex from
`homology_exact₁`. -/
private theorem cechCohomologyConnectingWindow_eq_homologyExactOne
    {S : ShortComplex (Cᵒᵖ ⥤ AddCommGrpCat)} (hS : S.ShortExact) (n : ℕ) :
    ShortComplex.mk
        (cechCohomologyConnectingMorphism U family hS n)
        ((cechCohomologyDegree U family (n + 1)).obj.map S.f)
        (cechCohomologyConnectingMorphism_comp_map_f_aux U family hS n) =
      ShortComplex.mk
        ((cechComplexOnPresheaves_map_shortExact U family hS).δ n (n + 1)
          (ComplexShape.up_mk n (n + 1) rfl))
        (HomologicalComplex.homologyMap ((cechComplexOnPresheaves U family).map S.f) (n + 1))
        ((cechComplexOnPresheaves_map_shortExact U family hS).δ_comp
          n (n + 1) (ComplexShape.up_mk n (n + 1) rfl)) := by
  -- Match the displayed morphisms first; proof irrelevance then identifies the short complexes.
  change ShortComplex.mk
      ((cechComplexOnPresheaves_map_shortExact U family hS).δ n (n + 1)
        (ComplexShape.up_mk n (n + 1) rfl))
      ((cechCohomologyDegree U family (n + 1)).obj.map S.f)
      (cechCohomologyConnectingMorphism_comp_map_f_aux U family hS n) =
    ShortComplex.mk
      ((cechComplexOnPresheaves_map_shortExact U family hS).δ n (n + 1)
        (ComplexShape.up_mk n (n + 1) rfl))
      (HomologicalComplex.homologyMap ((cechComplexOnPresheaves U family).map S.f) (n + 1))
      ((cechComplexOnPresheaves_map_shortExact U family hS).δ_comp
        n (n + 1) (ComplexShape.up_mk n (n + 1) rfl))
  have hmap :
      (cechCohomologyDegree U family (n + 1)).obj.map S.f =
        HomologicalComplex.homologyMap ((cechComplexOnPresheaves U family).map S.f) (n + 1) := by
    exact cechCohomologyDegree_map_eq U family (n + 1) S.f
  cases hmap
  have hzero :
      cechCohomologyConnectingMorphism_comp_map_f_aux U family hS n =
        (cechComplexOnPresheaves_map_shortExact U family hS).δ_comp
          n (n + 1) (ComplexShape.up_mk n (n + 1) rfl) := by
    exact Subsingleton.elim _ _
  cases hzero
  rfl

/-- Helper for Lemma 21.9.2: the adjacent Čech cohomology window
`Hⁿ(X₃) ⟶ Hⁿ⁺¹(X₁) ⟶ Hⁿ⁺¹(X₂)` is exact. -/
private theorem cechCohomology_exact_connectingMorphism_map_f
    {S : ShortComplex (Cᵒᵖ ⥤ AddCommGrpCat)} (hS : S.ShortExact) (n : ℕ) :
    (ShortComplex.mk
      (cechCohomologyConnectingMorphism U family hS n)
      ((cechCohomologyDegree U family (n + 1)).obj.map S.f)
      (cechCohomologyConnectingMorphism_comp_map_f_aux U family hS n)).Exact := by
  -- Rewrite the short complex itself before invoking the owner exactness theorem.
  rw [cechCohomologyConnectingWindow_eq_homologyExactOne U family hS n]
  exact (cechComplexOnPresheaves_map_shortExact U family hS).homology_exact₁
      n (n + 1) (ComplexShape.up_mk n (n + 1) rfl)

/-- Helper for Lemma 21.9.2: the Čech connecting morphisms and degreewise cohomology maps form
the five-term exactness window required by `Definition 12.12.1`. -/
private theorem cechCohomology_exact₅
    {S : ShortComplex (Cᵒᵖ ⥤ AddCommGrpCat)} (hS : S.ShortExact) (n : ℕ) :
    (ComposableArrows.mk₅
      ((cechCohomologyDegree U family n).obj.map S.f)
      ((cechCohomologyDegree U family n).obj.map S.g)
      (cechCohomologyConnectingMorphism U family hS n)
      ((cechCohomologyDegree U family (n + 1)).obj.map S.f)
      ((cechCohomologyDegree U family (n + 1)).obj.map S.g)).Exact := by
  -- Assemble the five-term window from the already normalized adjacent exactness statements.
  exact CohomologicalDeltaFunctor.exact₅_of_adjacent_exactness
    (F := cechCohomologyDegree U family)
    (δ := fun {_} hS n ↦ cechCohomologyConnectingMorphism U family hS n)
    (map_g_comp_δ := fun {_} hS n ↦ cechCohomology_map_g_comp_connectingMorphism_aux U family hS n)
    (δ_comp_map_f := fun {_} hS n ↦ cechCohomologyConnectingMorphism_comp_map_f_aux U family hS n)
    (map_exact := fun {_} hS n ↦ cechCohomology_map_exact U family hS n)
    (exact_map_g_δ := fun {_} hS n ↦ cechCohomology_exact_map_g_connectingMorphism U family hS n)
    (exact_δ_map_f := fun {_} hS n ↦ cechCohomology_exact_connectingMorphism_map_f U family hS n)
    hS n

/-- Helper for Lemma 21.9.2: the Čech connecting morphisms are natural in morphisms of short
exact sequences of abelian presheaves. -/
private theorem cechCohomologyConnectingMorphism_naturality_eq
    {S T : ShortComplex (Cᵒᵖ ⥤ AddCommGrpCat)} (hS : S.ShortExact) (hT : T.ShortExact)
    (φ : S ⟶ T) (n : ℕ) :
    ((cechCohomologyDegree U family n).obj.map φ.τ₃) ≫
        cechCohomologyConnectingMorphism U family hS n =
      cechCohomologyConnectingMorphism U family hT n ≫
        ((cechCohomologyDegree U family (n + 1)).obj.map φ.τ₁) := by
  -- Rewrite only the four displayed morphisms to the owner homology-sequence spelling.
  simpa only [cechCohomologyDegree_map_eq, cechCohomologyConnectingMorphism, Category.assoc] using
    (HomologicalComplex.HomologySequence.δ_naturality
      ((cechComplexOnPresheaves U family).mapShortComplex.map φ)
      (cechComplexOnPresheaves_map_shortExact U family hS)
      (cechComplexOnPresheaves_map_shortExact U family hT)
      n (n + 1) (ComplexShape.up_mk n (n + 1) rfl)).symm

/-- Helper for Lemma 21.9.2: the Čech connecting morphisms are natural in morphisms of short
exact sequences of abelian presheaves. -/
private theorem cechCohomologyConnectingMorphism_naturality_aux
    {S T : ShortComplex (Cᵒᵖ ⥤ AddCommGrpCat)} (hS : S.ShortExact) (hT : T.ShortExact)
    (φ : S ⟶ T) (n : ℕ) :
    CommSq ((cechCohomologyDegree U family n).obj.map φ.τ₃)
      (cechCohomologyConnectingMorphism U family hS n)
      (cechCohomologyConnectingMorphism U family hT n)
      ((cechCohomologyDegree U family (n + 1)).obj.map φ.τ₁) := by
  -- Package the already normalized raw equation as the required commutative square.
  exact CommSq.mk (cechCohomologyConnectingMorphism_naturality_eq U family hS hT φ n)

/-- Lemma 21.9.2: for a family `family : ι → Over U`, the functors
`F ↦ cechCohomology U family F n` form a cohomological `δ`-functor from the abelian category of
abelian presheaves on `C` to `AddCommGrpCat`, i.e. to the category of `ℤ`-modules. -/
@[stacks 03AR]
noncomputable def cechCohomologyDeltaFunctor :
    CohomologicalDeltaFunctor (Cᵒᵖ ⥤ AddCommGrpCat) AddCommGrpCat where
  F := cechCohomologyDegree U family
  δ := fun {_} hS n ↦ cechCohomologyConnectingMorphism U family hS n
  mono_map_f_zero := fun {_} hS ↦ cechCohomology_mono_map_f_zero U family hS
  exact₅ := fun {_} hS n ↦ cechCohomology_exact₅ U family hS n
  δ_naturality := fun {_ _} hS hT φ n ↦
    cechCohomologyConnectingMorphism_naturality_aux U family hS hT φ n

/-- Evaluating `cechCohomologyDeltaFunctor U family` in degree `n` at a presheaf recovers the
degree-`n` Čech cohomology object `cechCohomology U family F n`. -/
@[simp] theorem cechCohomologyDeltaFunctor_obj_obj (n : ℕ)
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{v}) :
    (cechCohomologyDeltaFunctor U family n).obj.obj F = cechCohomology U family F n :=
  rfl

/-- The connecting morphism of `cechCohomologyDeltaFunctor U family` is the canonical one induced
by the long exact homology sequence of the mapped short exact sequence of Čech complexes. -/
@[simp] theorem cechCohomologyDeltaFunctor_δ
    {S : ShortComplex (Cᵒᵖ ⥤ AddCommGrpCat)} (hS : S.ShortExact) (n : ℕ) :
    (cechCohomologyDeltaFunctor U family).δ hS n =
      cechCohomologyConnectingMorphism U family hS n :=
  rfl

/-- The canonical connecting morphism annihilates the image of the degree-`n` Čech cohomology
map induced by `S.g`. -/
@[simp, reassoc] theorem cechCohomology_map_g_comp_connectingMorphism
    {S : ShortComplex (Cᵒᵖ ⥤ AddCommGrpCat)} (hS : S.ShortExact) (n : ℕ) :
    ((cechCohomologyDegree U family n).obj.map S.g) ≫
        cechCohomologyConnectingMorphism U family hS n =
      0 := by
  simpa only [cechCohomologyDeltaFunctor_δ] using
    (cechCohomologyDeltaFunctor U family).map_g_comp_δ hS n

/-- The canonical connecting morphism lands in the kernel of the degree-`n + 1` Čech cohomology
map induced by `S.f`. -/
@[simp, reassoc] theorem cechCohomologyConnectingMorphism_comp_map_f
    {S : ShortComplex (Cᵒᵖ ⥤ AddCommGrpCat)} (hS : S.ShortExact) (n : ℕ) :
    cechCohomologyConnectingMorphism U family hS n ≫
        ((cechCohomologyDegree U family (n + 1)).obj.map S.f) =
      0 := by
  simpa only [cechCohomologyDeltaFunctor_δ] using
    (cechCohomologyDeltaFunctor U family).δ_comp_map_f hS n

/-- The canonical connecting morphisms commute with morphisms of short exact sequences of abelian
presheaves. -/
theorem cechCohomologyConnectingMorphism_naturality
    {S T : ShortComplex (Cᵒᵖ ⥤ AddCommGrpCat)} (hS : S.ShortExact) (hT : T.ShortExact)
    (φ : S ⟶ T) (n : ℕ) :
    CommSq ((cechCohomologyDegree U family n).obj.map φ.τ₃)
      (cechCohomologyConnectingMorphism U family hS n)
      (cechCohomologyConnectingMorphism U family hT n)
      ((cechCohomologyDegree U family (n + 1)).obj.map φ.τ₁) := by
  exact cechCohomologyConnectingMorphism_naturality_aux U family hS hT φ n

end CategoryTheory
