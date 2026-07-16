import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_75_2
import stacks_proof.stacks_project.Chap10.Lemma_10_134_4_Jacobi_Zariski_sequence.Index

-- Declarations for this item will be appended below by the statement pipeline.

open Algebra
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open scoped TensorProduct

noncomputable section

universe u

section

variable {A B C : Type u}
variable [CommRing A] [CommRing B] [CommRing C]
variable [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C]

/- Semantic recall tooling (`lean_leansearch`) was unavailable in this session, so the statement
shape was checked against the local Chapter 10 cotangent-complex files and the upstream owners
`Algebra.H1Cotangent.exact_map_δ`, `Algebra.H1Cotangent.exact_δ_mapBaseChange`,
`KaehlerDifferential.exact_mapBaseChange_map`, and `KaehlerDifferential.map_surjective`. -/

set_option quotPrecheck false in
local notation "TorOmega[" n "]" =>
  (((Tor (ModuleCat B) n).obj (ModuleCat.of B Ω[B⁄A])).obj (ModuleCat.of B C))

set_option quotPrecheck false in
local notation "RawTorOmega[" n "]" =>
  (((Tor (ModuleCat B) n).obj (ModuleCat.of B C)).obj (ModuleCat.of B Ω[B⁄A]))

set_option quotPrecheck false in
local notation "SourceTorOwner[" n "](" X ")" =>
  (((Tor' (ModuleCat B) n).obj (ModuleCat.of B C)).obj (ModuleCat.of B X))

/-- Lemma 10.134.4 (Jacobi-Zariski sequence): for a tower of commutative rings `A → B → C`,
the canonical Jacobi-Zariski sequence
`H¹(L_{C/A}) → H¹(L_{C/B}) → C ⊗[B] Ω[B⁄A] → Ω[C⁄A] → Ω[C⁄B] → 0`
is exact at each intermediate term, and the terminal map is surjective. This is part (1) of the
statement. -/
@[stacks 00S2]
theorem jacobi_zariski_sequence_exact :
    Function.Exact (H1Cotangent.map A B C C) (H1Cotangent.δ A B C) ∧
      Function.Exact (H1Cotangent.δ A B C) (KaehlerDifferential.mapBaseChange A B C) ∧
      Function.Exact (KaehlerDifferential.mapBaseChange A B C)
        (KaehlerDifferential.map A B C C) ∧
      Function.Surjective (KaehlerDifferential.map A B C C) := by
  constructor
  · -- The first two arrows are the owner exact sequence on `H¹`.
    simpa using H1Cotangent.exact_map_δ A B C
  constructor
  · -- The connecting map and the base-change map are exact by the owner Jacobi-Zariski theorem.
    simpa using H1Cotangent.exact_δ_mapBaseChange A B C
  constructor
  · -- The Kähler-differential tail is the canonical transitivity exact sequence.
    simpa using KaehlerDifferential.exact_mapBaseChange_map A B C
  · -- The terminal map in the transitivity sequence is surjective.
    simpa using KaehlerDifferential.map_surjective A B C

omit [Algebra A C] [IsScalarTower A B C] in
/-- Helper for Lemma 10.134.4 (Jacobi-Zariski sequence): once the tensor of
`range(P.cotangentComplex) ↪ P.CotangentSpace` is injective, the exactness of
`H¹(L_{B/A}) ⊗ C → P.Cotangent ⊗ C → P.CotangentSpace ⊗ C` follows by factoring through the
range of `P.cotangentComplex`. -/
theorem tensor_h1Cotangent_exact_via_cotangent_range
    (P : Algebra.Extension A B)
    (hRangeInj :
      Function.Injective (((LinearMap.range P.cotangentComplex).subtype).lTensor C)) :
    Function.Exact ((P.h1Cotangentι).lTensor C) (LinearMap.baseChange C P.cotangentComplex) := by
  have hExactRange :
      Function.Exact ((P.h1Cotangentι).lTensor C) (P.cotangentComplex.rangeRestrict.lTensor C) := by
    have hExactRangeBase : Function.Exact P.h1Cotangentι P.cotangentComplex.rangeRestrict := by
      -- Exactness identifies `H¹(L_{B/A})` with the kernel of the range-restricted differential.
      rw [LinearMap.exact_iff, LinearMap.ker_rangeRestrict]
      exact LinearMap.exact_iff.mp P.exact_hCotangentι_cotangentComplex
    -- Tensoring preserves the exact `H¹ → P.Cotangent → range(d)` pair.
    simpa using
      lTensor_exact C hExactRangeBase (LinearMap.surjective_rangeRestrict P.cotangentComplex)
  -- The base-changed differential is the tensor of the factorization through its range.
  have hComp :
      Function.Exact ((P.h1Cotangentι).lTensor C)
        ((((LinearMap.range P.cotangentComplex).subtype).lTensor C) ∘
          ((P.cotangentComplex.rangeRestrict).lTensor C)) :=
    hExactRange.comp_injective (((LinearMap.range P.cotangentComplex).subtype).lTensor C)
      hRangeInj (by simp)
  have hFactor :
      P.cotangentComplex =
        ((LinearMap.range P.cotangentComplex).subtype).comp P.cotangentComplex.rangeRestrict := by
    rfl
  rw [LinearMap.baseChange_eq_ltensor, hFactor, LinearMap.lTensor_comp, LinearMap.coe_comp]
  exact hComp

omit [Algebra A C] [IsScalarTower A B C] in
/-- Helper for Lemma 10.134.4 (Jacobi-Zariski sequence): the six-term Tor/tensor owner applied to
`0 → range(d) → P.CotangentSpace → Ω[B⁄A] → 0` gives the exact raw row in the owner orientation
`Tor₁^B(C, Ω[B⁄A]) → C ⊗ range(d) → C ⊗ P.CotangentSpace`. -/
theorem tor_one_tensor_cotangent_row_exact_raw
    (P : Algebra.Extension A B) :
    ∃ δ :
        RawTorOmega[1] ⟶ ModuleCat.of B (C ⊗[B] LinearMap.range P.cotangentComplex),
      Function.Exact δ.hom (((LinearMap.range P.cotangentComplex).subtype).lTensor C) := by
  let S : ShortComplex (ModuleCat B) :=
    cotangent_range_shortComplex (A := A) (B := B) P
  have hS : S.ShortExact := cotangent_range_shortExact (A := A) (B := B) P
  let T := ModuleCat.torTensorSixTermSequence (ModuleCat.of B C) hS
  have hT : T.Exact := ModuleCat.torTensorSixTermSequence_exact (ModuleCat.of B C) hS
  refine ⟨T.map' 2 3, ?_⟩
  -- Exactness at the tensorized `range(d)` term is the `2 → 3 → 4` window of the public row.
  have hExactRaw : Function.Exact (T.map' 2 3).hom (T.map' 3 4).hom := by
    exact
      (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact (T.sc hT.toIsComplex 2)).1
        (hT.exact 2)
  have hmap34' : T.map' 3 4 = MonoidalCategoryStruct.whiskerLeft (ModuleCat.of B C) S.f := by
    dsimp [T]
    unfold ModuleCat.torTensorSixTermSequence ComposableArrows.mk₅ ComposableArrows.mk₄
    rfl
  have hmap34 :
      (T.map' 3 4).hom = (((LinearMap.range P.cotangentComplex).subtype).lTensor C) := by
    rw [hmap34']
    change ModuleCat.Hom.hom
        (MonoidalCategoryStruct.whiskerLeft
          (ModuleCat.of B C)
          (ModuleCat.ofHom ((LinearMap.range P.cotangentComplex).subtype))) =
      (((LinearMap.range P.cotangentComplex).subtype).lTensor C)
    rw [ModuleCat.hom_whiskerLeft]
    rfl
  simpa [hmap34] using hExactRaw

omit [Algebra A C] [IsScalarTower A B C] in
/-- Helper for Lemma 10.134.4 (Jacobi-Zariski sequence): vanishing of the raw owner
`Tor₁^B(C, Ω[B⁄A])` kills the incoming map in the first tensor row and forces
`C ⊗ range(d) → C ⊗ P.CotangentSpace` to stay injective. -/
theorem tensor_cotangent_range_subtype_injective_of_isZero_raw_tor1
    (P : Algebra.Extension.{u} A B)
    (hTor : IsZero (RawTorOmega[1])) :
    Function.Injective (((LinearMap.range P.cotangentComplex).subtype).lTensor C) := by
  obtain ⟨δ, hExact⟩ :=
    tor_one_tensor_cotangent_row_exact_raw (A := A) (B := B) (C := C) (P := P)
  -- The raw incoming `Tor₁` morphism vanishes once its source object is zero.
  have hδ : δ = 0 := hTor.eq_of_src _ _
  have hExactZero :
      Function.Exact
        (0 : RawTorOmega[1] →ₗ[B] C ⊗[B] LinearMap.range P.cotangentComplex)
        (((LinearMap.range P.cotangentComplex).subtype).lTensor C) := by
    simpa [hδ] using hExact
  -- Exactness with zero source identifies the kernel with the zero range.
  have hker :
      LinearMap.ker (((LinearMap.range P.cotangentComplex).subtype).lTensor C) = ⊥ := by
    have hrange :
        LinearMap.ker (((LinearMap.range P.cotangentComplex).subtype).lTensor C) =
          LinearMap.range
            (0 : RawTorOmega[1] →ₗ[B] C ⊗[B] LinearMap.range P.cotangentComplex) :=
      LinearMap.exact_iff.mp hExactZero
    rw [LinearMap.range_zero] at hrange
    simpa using hrange
  exact LinearMap.ker_eq_bot.mp hker

omit [Algebra A C] [IsScalarTower A B C] in
/-- Helper for Lemma 10.134.4 (Jacobi-Zariski sequence): the six-term Tor/tensor owner applied to
`0 → H¹(L_{B/A}) → P.Cotangent → range(d) → 0` gives the exact raw row in the owner orientation
`Tor₁^B(C, range(d)) → C ⊗ H¹(L_{B/A}) → C ⊗ P.Cotangent`. -/
theorem tor_one_tensor_h1_row_exact_raw
    (P : Algebra.Extension A B) :
    ∃ δ :
        (((Tor (ModuleCat B) 1).obj (ModuleCat.of B C)).obj
          (ModuleCat.of B (LinearMap.range P.cotangentComplex))) ⟶
          ModuleCat.of B (C ⊗[B] P.H1Cotangent),
      Function.Exact δ.hom ((P.h1Cotangentι).lTensor C) := by
  let S : ShortComplex (ModuleCat B) :=
    ShortComplex.moduleCatMk
      P.h1Cotangentι
      P.cotangentComplex.rangeRestrict
      (h1Cotangent_comp_rangeRestrict_eq_zero (A := A) (B := B) P)
  have hS : S.ShortExact := by
    -- The source proof's second row is exact before tensoring.
    refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
    · rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
      exact h1Cotangent_exact_rangeRestrict (A := A) (B := B) P
    · exact (ModuleCat.mono_iff_injective _).2 P.h1Cotangentι_injective
    · exact (ModuleCat.epi_iff_surjective _).2
        (LinearMap.surjective_rangeRestrict P.cotangentComplex)
  let T := ModuleCat.torTensorSixTermSequence (ModuleCat.of B C) hS
  have hT : T.Exact := ModuleCat.torTensorSixTermSequence_exact (ModuleCat.of B C) hS
  refine ⟨T.map' 2 3, ?_⟩
  -- Exactness at the tensorized `H¹` term is the same `2 → 3 → 4` window for the second row.
  have hExactRaw : Function.Exact (T.map' 2 3).hom (T.map' 3 4).hom := by
    exact
      (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact (T.sc hT.toIsComplex 2)).1
        (hT.exact 2)
  have hmap34' : T.map' 3 4 = MonoidalCategoryStruct.whiskerLeft (ModuleCat.of B C) S.f := by
    dsimp [T]
    unfold ModuleCat.torTensorSixTermSequence ComposableArrows.mk₅ ComposableArrows.mk₄
    rfl
  have hmap34 : (T.map' 3 4).hom = (P.h1Cotangentι).lTensor C := by
    rw [hmap34']
    change ModuleCat.Hom.hom
        (MonoidalCategoryStruct.whiskerLeft (ModuleCat.of B C) (ModuleCat.ofHom P.h1Cotangentι)) =
      (P.h1Cotangentι).lTensor C
    rw [ModuleCat.hom_whiskerLeft]
    rfl
  simpa [hmap34] using hExactRaw

omit [Algebra A C] [IsScalarTower A B C] in
/-- Helper for Lemma 10.134.4 (Jacobi-Zariski sequence): vanishing of the raw owner
`Tor₁^B(C, range(d))` kills the incoming map in the second tensor row and forces
`C ⊗ H¹(L_{B/A}) → C ⊗ P.Cotangent` to stay injective. -/
theorem tensor_h1Cotangent_injective_of_isZero_raw_tor1_cotangent_range
    (P : Algebra.Extension.{u} A B)
    (hTor :
      IsZero
        ((((Tor (ModuleCat B) 1).obj (ModuleCat.of B C)).obj
          (ModuleCat.of B (LinearMap.range P.cotangentComplex))))) :
    Function.Injective ((P.h1Cotangentι).lTensor C) := by
  obtain ⟨δ, hExact⟩ :=
    tor_one_tensor_h1_row_exact_raw (A := A) (B := B) (C := C) (P := P)
  -- The raw incoming `Tor₁(range(d))` morphism vanishes once its source object is zero.
  have hδ : δ = 0 := hTor.eq_of_src _ _
  have hExactZero :
      Function.Exact
        (0 :
          (((Tor (ModuleCat B) 1).obj (ModuleCat.of B C)).obj
            (ModuleCat.of B (LinearMap.range P.cotangentComplex))) →ₗ[B]
            C ⊗[B] P.H1Cotangent)
        ((P.h1Cotangentι).lTensor C) := by
    simpa [hδ] using hExact
  -- Exactness with zero source again turns the kernel into the zero submodule.
  have hker : LinearMap.ker ((P.h1Cotangentι).lTensor C) = ⊥ := by
    have hrange :
        LinearMap.ker ((P.h1Cotangentι).lTensor C) =
          LinearMap.range
            (0 :
              (((Tor (ModuleCat B) 1).obj (ModuleCat.of B C)).obj
                (ModuleCat.of B (LinearMap.range P.cotangentComplex))) →ₗ[B]
                C ⊗[B] P.H1Cotangent) :=
      LinearMap.exact_iff.mp hExactZero
    rw [LinearMap.range_zero] at hrange
    simpa using hrange
  exact LinearMap.ker_eq_bot.mp hker

/-- Helper for Lemma 10.134.4 (Jacobi-Zariski sequence): the degree-`n` `tor_flip_iso`
component as a linear equivalence on underlying `B`-modules. This packages the owner-side Tor
symmetry into the form needed for exactness and vanishing transport. -/
noncomputable def tor_flip_component_linear_equiv
    (n : ℕ) (X Y : ModuleCat B) :
    (((Tor (ModuleCat B) n).obj X).obj Y) ≃ₗ[B]
      ↑((((Functor.flip (Tor' (ModuleCat B) n)).obj X).obj Y)) :=
  ((((tor_flip_iso (ModuleCat B) n).app X).app Y)).toLinearEquiv

/-- Helper for Lemma 10.134.4 (Jacobi-Zariski sequence): the source-facing owner obtained from
`tor_flip_iso` is definitionally the fixed-coefficient `Tor'` owner `X ↦ Tor'(-, X)` evaluated at
`C`. This packages the boundary isomorphism in the exact form used by the source-row wrappers. -/
noncomputable def tor_flip_source_owner_linear_equiv
    (n : ℕ) (X : Type u) [AddCommGroup X] [Module B X] :
    (((Tor (ModuleCat B) n).obj (ModuleCat.of B X)).obj (ModuleCat.of B C)) ≃ₗ[B]
      ↑(SourceTorOwner[n](X)) :=
  tor_flip_component_linear_equiv (B := B) n (ModuleCat.of B X) (ModuleCat.of B C)

/-- Helper for Lemma 10.134.4 (Jacobi-Zariski sequence): the fixed-coefficient source owner
`SourceTorOwner[n](X)` is definitionally the `n`th left derived functor of `tensorRight X`
evaluated at `C`. This is the owner that the source proof computes from a projective resolution
of `C`. -/
theorem source_tor_owner_eq_leftDerived_obj
    (n : ℕ) (X : Type u) [AddCommGroup X] [Module B X] :
    SourceTorOwner[n](X) =
      ((tensorRight (ModuleCat.of B X)).leftDerived n).obj (ModuleCat.of B C) := by
  -- This is just the definitional expansion of `Tor'` in the fixed-coefficient orientation.
  rfl

/-- Helper for Lemma 10.134.4 (Jacobi-Zariski sequence): the `2 → 1 → 0` window of the fixed
projective resolution of `C`, tensored on the right with `X`. This is the concrete window whose
homology computes the degree-one source owner `Tor'₁(C, X)`. -/
private noncomputable abbrev source_owner_degree_one_window
    (X : Type u) [AddCommGroup X] [Module B X] : ShortComplex (ModuleCat B) :=
  (HomologicalComplex.shortComplexFunctor' (ModuleCat B) (ComplexShape.down ℕ) 2 1 0).obj
    (((tensorRight (ModuleCat.of B X)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (CategoryTheory.ProjectiveResolution.complex
        (CategoryTheory.projectiveResolution (ModuleCat.of B C))))

/-- Helper for Lemma 10.134.4 (Jacobi-Zariski sequence): the degree-one source owner
`Tor'₁(C, X)` is computed by the homology of the fixed `2 → 1 → 0` tensor window. -/
private noncomputable def source_owner_degree_one_window_homology_iso
    (X : Type u) [AddCommGroup X] [Module B X] :
    SourceTorOwner[1](X) ≅ ShortComplex.homology (source_owner_degree_one_window (B := B) (C := C) X) := by
  -- First identify the source owner with the first left derived functor of `tensorRight X`.
  erw [source_tor_owner_eq_leftDerived_obj (B := B) (C := C) 1 X]
  -- Then compute that left derived functor on the chosen projective resolution of `C`.
  exact
    ((CategoryTheory.projectiveResolution (ModuleCat.of B C)).isoLeftDerivedObj
      (tensorRight (ModuleCat.of B X)) 1) ≪≫
      (HomologicalComplex.homologyFunctorIso' (C := ModuleCat B) (c := ComplexShape.down ℕ)
        (i := 2) (j := 1) (k := 0) (by simp) (by simp)).app
        (((tensorRight (ModuleCat.of B X)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
          (CategoryTheory.ProjectiveResolution.complex
            (CategoryTheory.projectiveResolution (ModuleCat.of B C))))

/-- Helper for Lemma 10.134.4 (Jacobi-Zariski sequence): the `3 → 2 → 1` window of the fixed
projective resolution of `C`, tensored on the right with `X`. This is the concrete window whose
homology computes the degree-two source owner `Tor'₂(C, X)`. -/
private noncomputable abbrev source_owner_degree_two_window
    (X : Type u) [AddCommGroup X] [Module B X] : ShortComplex (ModuleCat B) :=
  (HomologicalComplex.shortComplexFunctor' (ModuleCat B) (ComplexShape.down ℕ) 3 2 1).obj
    (((tensorRight (ModuleCat.of B X)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (CategoryTheory.ProjectiveResolution.complex
        (CategoryTheory.projectiveResolution (ModuleCat.of B C))))

/-- Helper for Lemma 10.134.4 (Jacobi-Zariski sequence): the degree-two source owner
`Tor'₂(C, X)` is computed by the homology of the fixed `3 → 2 → 1` tensor window. -/
private noncomputable def source_owner_degree_two_window_homology_iso
    (X : Type u) [AddCommGroup X] [Module B X] :
    SourceTorOwner[2](X) ≅ ShortComplex.homology (source_owner_degree_two_window (B := B) (C := C) X) := by
  -- First identify the source owner with the second left derived functor of `tensorRight X`.
  erw [source_tor_owner_eq_leftDerived_obj (B := B) (C := C) 2 X]
  -- Then compute that left derived functor on the chosen projective resolution of `C`.
  exact
    ((CategoryTheory.projectiveResolution (ModuleCat.of B C)).isoLeftDerivedObj
      (tensorRight (ModuleCat.of B X)) 2) ≪≫
      (HomologicalComplex.homologyFunctorIso' (C := ModuleCat B) (c := ComplexShape.down ℕ)
        (i := 3) (j := 2) (k := 1) (by simp) (by simp)).app
        (((tensorRight (ModuleCat.of B X)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
          (CategoryTheory.ProjectiveResolution.complex
            (CategoryTheory.projectiveResolution (ModuleCat.of B C))))

/-- Helper for Lemma 10.134.4 (Jacobi-Zariski sequence): in degree `0`, the fixed-coefficient
source owner `Tor'₀(C, X)` is the ordinary tensor product `C ⊗[B] X`. This is the concrete
degree-zero endpoint needed to read the source-owner exact row against `S.f.hom.lTensor C`. -/
noncomputable def source_owner_degree_zero_tensor_linear_equiv
    (X : Type u) [AddCommGroup X] [Module B X] :
    SourceTorOwner[0](X) ≃ₗ[B] C ⊗[B] X :=
  by
    -- First unfold the source owner as the degree-zero left derived functor of `tensorRight X`.
    erw [source_tor_owner_eq_leftDerived_obj (B := B) (C := C) 0 X]
    -- Then use the canonical degree-zero comparison for the right exact functor `tensorRight X`.
    exact
      ((tensorRight (ModuleCat.of B X)).leftDerivedZeroIsoSelf.app
        (ModuleCat.of B C)).toLinearEquiv

/-- Helper for Lemma 10.134.4 (Jacobi-Zariski sequence): the projective-resolution model of
`fromLeftDerivedZero'` is natural in the functor variable. This is the fixed-resolution degree-zero
transport needed to compare `Tor'₀(C, -)` with literal tensor maps. -/
private theorem projectiveResolution_fromLeftDerivedZero'_nattrans
    {F G : ModuleCat B ⥤ ModuleCat B} [F.Additive] [G.Additive]
    (α : F ⟶ G) {X : ModuleCat B} (P : CategoryTheory.ProjectiveResolution X) :
    P.fromLeftDerivedZero' F ≫ α.app X =
      HomologicalComplex.opcyclesMap
          ((NatTrans.mapHomologicalComplex α (ComplexShape.down ℕ)).app P.complex) 0 ≫
        P.fromLeftDerivedZero' G := by
  -- Cancel the universal opcycles projection and use naturality of `α` on the augmentation.
  rw [← cancel_epi (HomologicalComplex.pOpcycles _ _)]
  have hPrefixF :
      ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex).pOpcycles 0 ≫
        P.fromLeftDerivedZero' F =
      F.map (P.π.f 0) := by
    simpa using
      CategoryTheory.ProjectiveResolution.pOpcycles_comp_fromLeftDerivedZero' (P := P) (F := F)
  have h₁ :
      ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex).pOpcycles 0 ≫
          P.fromLeftDerivedZero' F ≫ α.app X =
        F.map (P.π.f 0) ≫ α.app X := by
    simpa [Category.assoc] using congrArg (fun k ↦ k ≫ α.app X) hPrefixF
  have h₂ :
      F.map (P.π.f 0) ≫ α.app X =
        α.app (P.complex.X 0) ≫ G.map (P.π.f 0) := by
    simpa using α.naturality (P.π.f 0)
  have h₃ :
      α.app (P.complex.X 0) ≫ G.map (P.π.f 0) =
        ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex).pOpcycles 0 ≫
          HomologicalComplex.opcyclesMap
            ((NatTrans.mapHomologicalComplex α (ComplexShape.down ℕ)).app P.complex) 0 ≫
          P.fromLeftDerivedZero' G := by
    have hPrefixG :
        ((G.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex).pOpcycles 0 ≫
          P.fromLeftDerivedZero' G =
        G.map (P.π.f 0) := by
      simpa using
        CategoryTheory.ProjectiveResolution.pOpcycles_comp_fromLeftDerivedZero' (P := P) (F := G)
    have hOpcycles :
        ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex).pOpcycles 0 ≫
            HomologicalComplex.opcyclesMap
              ((NatTrans.mapHomologicalComplex α (ComplexShape.down ℕ)).app P.complex) 0 =
          α.app (P.complex.X 0) ≫
            ((G.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex).pOpcycles 0 := by
      simpa using
        HomologicalComplex.p_opcyclesMap
          (φ := (NatTrans.mapHomologicalComplex α (ComplexShape.down ℕ)).app P.complex)
          (i := 0)
    have h₃a :
        α.app (P.complex.X 0) ≫ G.map (P.π.f 0) =
          α.app (P.complex.X 0) ≫
            (((G.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex).pOpcycles 0 ≫
              P.fromLeftDerivedZero' G) := by
      simpa [Category.assoc] using congrArg (fun k ↦ α.app (P.complex.X 0) ≫ k) hPrefixG.symm
    have h₃b :
        α.app (P.complex.X 0) ≫
            (((G.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex).pOpcycles 0 ≫
              P.fromLeftDerivedZero' G) =
          ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex).pOpcycles 0 ≫
            HomologicalComplex.opcyclesMap
              ((NatTrans.mapHomologicalComplex α (ComplexShape.down ℕ)).app P.complex) 0 ≫
            P.fromLeftDerivedZero' G := by
      simpa [Category.assoc] using congrArg (fun k ↦ k ≫ P.fromLeftDerivedZero' G) hOpcycles.symm
    exact h₃a.trans h₃b
  exact h₁.trans (h₂.trans h₃)

/-- Helper for Lemma 10.134.4 (Jacobi-Zariski sequence): the canonical degree-zero comparison
`leftDerived 0 ≅ tensor` is natural for natural transformations between right exact additive
endofunctors of `ModuleCat B`. -/
private theorem leftDerivedZeroIsoSelf_hom_nattrans
    {F G : ModuleCat B ⥤ ModuleCat B} [F.Additive] [G.Additive]
    [PreservesFiniteColimits F] [PreservesFiniteColimits G]
    (α : F ⟶ G) :
    NatTrans.leftDerived α 0 ≫ G.leftDerivedZeroIsoSelf.hom =
      F.leftDerivedZeroIsoSelf.hom ≫ α := by
  apply NatTrans.ext
  funext X
  have hComp :
      (NatTrans.leftDerived α 0).app X ≫ G.fromLeftDerivedZero.app X =
        F.fromLeftDerivedZero.app X ≫ α.app X := by
    let P : CategoryTheory.ProjectiveResolution X :=
      CategoryTheory.projectiveResolution X
    rw [CategoryTheory.ProjectiveResolution.leftDerived_app_eq α P 0,
      CategoryTheory.ProjectiveResolution.fromLeftDerivedZero_eq P G,
      CategoryTheory.ProjectiveResolution.fromLeftDerivedZero_eq P F]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    have hIsoHomology :
        (HomologicalComplex.homologyFunctor (ModuleCat B) (ComplexShape.down ℕ) 0).map
            ((NatTrans.mapHomologicalComplex α (ComplexShape.down ℕ)).app P.complex) ≫
            (ChainComplex.isoHomologyι₀
              (((G.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex))).hom =
          (ChainComplex.isoHomologyι₀
            (((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex))).hom ≫
            HomologicalComplex.opcyclesMap
              ((NatTrans.mapHomologicalComplex α (ComplexShape.down ℕ)).app P.complex) 0 := by
      -- Replace the homology map by the corresponding map on opcycles through `isoHomologyι₀`.
      simpa [Category.assoc] using
        congrArg
          (fun k ↦
            (ChainComplex.isoHomologyι₀
              (((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex))).hom ≫
                k ≫
                  (ChainComplex.isoHomologyι₀
                    (((G.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex))).hom)
          (ChainComplex.isoHomologyι₀_inv_naturality
            (φ := (NatTrans.mapHomologicalComplex α (ComplexShape.down ℕ)).app P.complex))
    calc
      (P.isoLeftDerivedObj F 0).hom ≫
          (HomologicalComplex.homologyFunctor (ModuleCat B) (ComplexShape.down ℕ) 0).map
            ((NatTrans.mapHomologicalComplex α (ComplexShape.down ℕ)).app P.complex) ≫
          (ChainComplex.isoHomologyι₀
            (((G.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex))).hom ≫
          P.fromLeftDerivedZero' G =
        (P.isoLeftDerivedObj F 0).hom ≫
          (ChainComplex.isoHomologyι₀
            (((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex))).hom ≫
          HomologicalComplex.opcyclesMap
            ((NatTrans.mapHomologicalComplex α (ComplexShape.down ℕ)).app P.complex) 0 ≫
          P.fromLeftDerivedZero' G := by
            simpa [Category.assoc] using
              congrArg
                (fun k ↦ (P.isoLeftDerivedObj F 0).hom ≫ k ≫ P.fromLeftDerivedZero' G)
                hIsoHomology
      _ =
        (P.isoLeftDerivedObj F 0).hom ≫
          (ChainComplex.isoHomologyι₀
            (((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex))).hom ≫
          P.fromLeftDerivedZero' F ≫ α.app X := by
            simpa [Category.assoc] using
              congrArg
                (fun k ↦
                  (P.isoLeftDerivedObj F 0).hom ≫
                    (ChainComplex.isoHomologyι₀
                      (((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex))).hom ≫
                    k)
                (projectiveResolution_fromLeftDerivedZero'_nattrans (α := α) P).symm
  simpa [Functor.leftDerivedZeroIsoSelf] using hComp

/-- Helper for Lemma 10.134.4 (Jacobi-Zariski sequence): the degree-zero source-owner comparison
transports the source-owner map induced by `S.f` to the literal tensor map `S.f.hom.lTensor C`. -/
private theorem source_owner_degree_zero_tensor_map_transport
    (S : ShortComplex (ModuleCat B)) :
    ModuleCat.ofHom (S.f.hom.lTensor C) =
      (source_owner_degree_zero_tensor_linear_equiv
          (B := B) (C := C) (↑S.X₁)).toModuleIso.inv ≫
        (((Tor' (ModuleCat B) 0).obj (ModuleCat.of B C)).map S.f) ≫
        (source_owner_degree_zero_tensor_linear_equiv
          (B := B) (C := C) (↑S.X₂)).toModuleIso.hom := by
  let eMid :
      SourceTorOwner[0](↑S.X₁) ≅ ModuleCat.of B (C ⊗[B] ↑S.X₁) :=
    (source_owner_degree_zero_tensor_linear_equiv
      (B := B) (C := C) (↑S.X₁)).toModuleIso
  let eRight :
      SourceTorOwner[0](↑S.X₂) ≅ ModuleCat.of B (C ⊗[B] ↑S.X₂) :=
    (source_owner_degree_zero_tensor_linear_equiv
      (B := B) (C := C) (↑S.X₂)).toModuleIso
  have hNat :
      (((Tor' (ModuleCat B) 0).obj (ModuleCat.of B C)).map S.f) ≫ eRight.hom =
        eMid.hom ≫ ModuleCat.ofHom (S.f.hom.lTensor C) := by
    -- Read naturality of the degree-zero comparison at the fixed object `C`.
    simpa [eMid, eRight, Tor', Category.assoc, ModuleCat.hom_whiskerLeft] using
      congrArg
        (fun k ↦ k.app (ModuleCat.of B C))
        (leftDerivedZeroIsoSelf_hom_nattrans (B := B)
          (((tensoringRight (ModuleCat.{u} B)).map S.f)))
  -- Insert the identity `eMid.inv ≫ eMid.hom = 𝟙` and replace the middle factor by `hNat`.
  calc
    ModuleCat.ofHom (S.f.hom.lTensor C) =
      eMid.inv ≫ eMid.hom ≫ ModuleCat.ofHom (S.f.hom.lTensor C) := by
        simp
    _ = eMid.inv ≫ ((((Tor' (ModuleCat B) 0).obj (ModuleCat.of B C)).map S.f) ≫ eRight.hom) := by
        rw [hNat]
    _ =
      eMid.inv ≫ (((Tor' (ModuleCat B) 0).obj (ModuleCat.of B C)).map S.f) ≫ eRight.hom := by
        simp

/-- Helper for Lemma 10.134.4 (Jacobi-Zariski sequence): categorical projectivity of
`ModuleCat.of B X` implies the usual module-theoretic projectivity of `X`. This is the bridge
needed to invoke flatness when tensoring the fixed projective resolution of `C`. -/
theorem module_projective_of_categorical_projective
    (X : Type u) [AddCommGroup X] [Module B X]
    (hX : Projective (ModuleCat.of B X)) :
    Module.Projective B X := by
  -- Translate the categorical lifting property against epimorphisms into the usual linear lift
  -- against surjective linear maps.
  let _ : Small.{u} B := small_self B
  refine Module.Projective.of_lifting_property ?_
  intro M N _ _ _ _ f g hf
  let _ : Projective (ModuleCat.of B X) := hX
  have hf' : Epi (ModuleCat.ofHom f) := (ModuleCat.epi_iff_surjective _).mpr hf
  refine ⟨(Projective.factorThru (ModuleCat.ofHom g) (ModuleCat.ofHom f)).hom, ?_⟩
  exact congrArg ModuleCat.Hom.hom
    (Projective.factorThru_comp (ModuleCat.ofHom g) (ModuleCat.ofHom f))

/-- Helper for Lemma 10.134.4 (Jacobi-Zariski sequence): exactness is invariant under replacing
the middle module by a linearly equivalent one, provided the two adjacent maps are conjugated by
that equivalence. -/
theorem exact_conj_middle
    {M N N' P : Type u}
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup N'] [AddCommGroup P]
    [Module B M] [Module B N] [Module B N'] [Module B P]
    {f : M →ₗ[B] N} {g : N →ₗ[B] P} (e : N ≃ₗ[B] N')
    (h : Function.Exact f g) :
    Function.Exact (e.toLinearMap.comp f) (g.comp e.symm.toLinearMap) := by
  -- Rewrite exactness as an equality of kernel and range, then transport both sides along `e`.
  rw [LinearMap.exact_iff] at h
  rw [LinearMap.exact_iff]
  rw [LinearMap.ker_comp, LinearMap.range_comp, Submodule.map_equiv_eq_comap_symm]
  simp [h]

/-- Helper for Lemma 10.134.4 (Jacobi-Zariski sequence): in `ModuleCat B`, an exact pair
`X₁ ⟶ X₂ ⟶ X₃` with both arrows zero forces the middle object to be zero. This packages the
final exactness-to-vanishing step used in the dimension-shift argument. -/
theorem isZero_of_exact_zero_zero
    {X₁ X₂ X₃ : ModuleCat B} {f : X₁ ⟶ X₂} {g : X₂ ⟶ X₃}
    (hExact : Function.Exact f.hom g.hom) (hf : f = 0) (hg : g = 0) :
    IsZero X₂ := by
  let S : ShortComplex (ModuleCat B) :=
    ShortComplex.moduleCatMk f.hom g.hom (Function.Exact.linearMap_comp_eq_zero hExact)
  have hS : S.Exact := by
    -- Repackage the function-level exactness as exactness of the associated short complex.
    simpa [S] using
      (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact (S := S)).2 hExact
  -- Once both endpoint maps vanish, exactness forces the middle object to vanish.
  simpa [S] using hS.isZero_X₂ hf hg

/-- Helper for Lemma 10.134.4 (Jacobi-Zariski sequence): the fixed-coefficient source owner
attaches to every short exact row `0 → X₁ → X₂ → X₃ → 0` an exact row
`Tor'₁(C, X₃) → C ⊗[B] X₁ → C ⊗[B] X₂`. -/
theorem source_owner_tor_one_tensor_row_of_shortExact
    (S : ShortComplex (ModuleCat B)) (hS : S.ShortExact) :
    ∃ δ :
        SourceTorOwner[1](↑S.X₃) ⟶ ModuleCat.of B (C ⊗[B] ↑S.X₁),
      Function.Exact δ.hom (S.f.hom.lTensor C) := by
  -- Route correction: the public six-term sequence gives `Tor₁(C, X₃) → C ⊗ X₁`, but this helper
  -- needs the opposite owner `Tor'₁(C, X₃) → C ⊗ X₁`. As in the solved `(2,1)` row, we read the
  -- `(1,0)` window directly from the tensorized fixed projective resolution of `C` and then use
  -- the degree-zero source-owner comparison to identify the right endpoint with `S.f.hom.lTensor C`.
  let P : CategoryTheory.ProjectiveResolution (ModuleCat.of B C) :=
    CategoryTheory.projectiveResolution (ModuleCat.of B C)
  let φ :
      ((tensorRight (S.X₁ : ModuleCat.{u} B)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
          P.complex ⟶
        ((tensorRight (S.X₂ : ModuleCat.{u} B)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
          P.complex :=
    ((NatTrans.mapHomologicalComplex ((tensoringRight (ModuleCat.{u} B)).map S.f)
      (ComplexShape.down ℕ)).app P.complex)
  let ψ :
      ((tensorRight (S.X₂ : ModuleCat.{u} B)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
          P.complex ⟶
        ((tensorRight (S.X₃ : ModuleCat.{u} B)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
          P.complex :=
    ((NatTrans.mapHomologicalComplex ((tensoringRight (ModuleCat.{u} B)).map S.g)
      (ComplexShape.down ℕ)).app P.complex)
  have hzero : φ ≫ ψ = 0 := by
    -- The tensorized chain maps still compose to zero because they are left whiskerings of
    -- `S.f ≫ S.g = 0`.
    refine HomologicalComplex.Hom.ext ?_
    apply funext
    intro n
    apply ModuleCat.hom_ext
    ext x
    dsimp [φ, ψ]
    rw [← ModuleCat.hom_comp]
    rw [← MonoidalCategory.whiskerLeft_comp, S.zero]
    rw [ModuleCat.hom_whiskerLeft]
    change (LinearMap.lTensor (P.complex.X n) (0 : S.X₁ →ₗ[B] S.X₃)) x =
      (0 : P.complex.X n ⊗[B] S.X₁ →ₗ[B] P.complex.X n ⊗[B] S.X₃) x
    simp
  let T : ShortComplex (ChainComplex (ModuleCat.{u} B) ℕ) := ShortComplex.mk φ ψ hzero
  have hT : T.ShortExact := by
    -- Tensoring each degree of the chosen projective resolution with the short exact row `S`
    -- stays short exact because the resolution terms are projective, hence flat.
    refine HomologicalComplex.shortExact_of_degreewise_shortExact T ?_
    intro n
    refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
    · rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
      let _ : Module.Projective B (P.complex.X n) :=
        module_projective_of_categorical_projective (B := B) (P.complex.X n) (P.projective n)
      let _ : Module.Flat B (P.complex.X n) := Module.Flat.of_projective
      have hExactBase : Function.Exact S.f.hom S.g.hom := by
        exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).1 hS.exact
      simpa [T, φ, ψ, CategoryTheory.Functor.mapHomologicalComplex_map_f,
        ModuleCat.hom_whiskerLeft] using
        (Module.Flat.lTensor_exact (P.complex.X n) hExactBase)
    · exact (ModuleCat.mono_iff_injective _).2 <| by
        let _ : Module.Projective B (P.complex.X n) :=
          module_projective_of_categorical_projective (B := B) (P.complex.X n) (P.projective n)
        let _ : Module.Flat B (P.complex.X n) := Module.Flat.of_projective
        have hf : Function.Injective S.f.hom := (ModuleCat.mono_iff_injective _).1 hS.mono_f
        simpa [T, φ, CategoryTheory.Functor.mapHomologicalComplex_map_f,
          ModuleCat.hom_whiskerLeft] using
          (Module.Flat.lTensor_preserves_injective_linearMap (M := P.complex.X n) S.f.hom hf)
    · exact (ModuleCat.epi_iff_surjective _).2 <| by
        have hg : Function.Surjective S.g.hom := (ModuleCat.epi_iff_surjective _).1 hS.epi_g
        simpa [T, ψ, CategoryTheory.Functor.mapHomologicalComplex_map_f,
          ModuleCat.hom_whiskerLeft] using
          (LinearMap.lTensor_surjective (P.complex.X n) hg)
  let eLeft :
      SourceTorOwner[1](↑S.X₃) ≅ T.X₃.homology 1 := by
    -- This is the degree-one left-derived comparison computed on the fixed projective resolution.
    erw [source_tor_owner_eq_leftDerived_obj (B := B) (C := C) 1 (↑S.X₃)]
    exact P.isoLeftDerivedObj (tensorRight (S.X₃ : ModuleCat.{u} B)) 1
  let eMidOwner :
      SourceTorOwner[0](↑S.X₁) ≅ T.X₁.homology 0 := by
    -- The middle degree-zero source-owner term is computed on the same resolution.
    erw [source_tor_owner_eq_leftDerived_obj (B := B) (C := C) 0 (↑S.X₁)]
    exact P.isoLeftDerivedObj (tensorRight (S.X₁ : ModuleCat.{u} B)) 0
  let eRightOwner :
      SourceTorOwner[0](↑S.X₂) ≅ T.X₂.homology 0 := by
    -- Likewise for the right degree-zero endpoint.
    erw [source_tor_owner_eq_leftDerived_obj (B := B) (C := C) 0 (↑S.X₂)]
    exact P.isoLeftDerivedObj (tensorRight (S.X₂ : ModuleCat.{u} B)) 0
  have hRaw :
      Function.Exact (hT.δ 1 0 (by simp)).hom (HomologicalComplex.homologyMap T.f 0).hom := by
    -- The `(1,0)` window of the homology long exact sequence is exact for the tensorized row `T`.
    exact
      (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact
        (S := ShortComplex.mk _ _ (ShortComplex.ShortExact.δ_comp hT 1 0 (by simp)))).1
        (hT.homology_exact₁ 1 0 (by simp))
  have hPre :
      Function.Exact
        ((hT.δ 1 0 (by simp)).hom.comp eLeft.toLinearEquiv.toLinearMap)
        (HomologicalComplex.homologyMap T.f 0).hom := by
    -- Changing only the source of the first map is harmless because `eLeft` is bijective.
    simpa using
      (LinearEquiv.precomp_exact_iff_exact (e := eLeft.toLinearEquiv)).2 hRaw
  have hMidOwner :
      Function.Exact
        (eMidOwner.symm.toLinearEquiv.toLinearMap.comp
          (((hT.δ 1 0 (by simp)).hom).comp eLeft.toLinearEquiv.toLinearMap))
        ((HomologicalComplex.homologyMap T.f 0).hom.comp eMidOwner.toLinearEquiv.toLinearMap) := by
    -- Conjugate the middle term from raw homology to the degree-zero source owner `Tor'₀(C, X₁)`.
    exact exact_conj_middle (B := B) (e := eMidOwner.symm.toLinearEquiv) hPre
  have hMapOwnerCat :
      (((Tor' (ModuleCat B) 0).obj (ModuleCat.of B C)).map S.f) =
        eMidOwner.hom ≫ HomologicalComplex.homologyMap T.f 0 ≫ eRightOwner.inv := by
    -- The degree-zero source-owner map is the homology map of the same tensorized chain map.
    simpa [T, φ, source_tor_owner_eq_leftDerived_obj, Category.assoc, Tor'] using
      (CategoryTheory.ProjectiveResolution.leftDerived_app_eq
        ((tensoringRight (ModuleCat.{u} B)).map S.f) P 0)
  have hMapOwner :
      (((Tor' (ModuleCat B) 0).obj (ModuleCat.of B C)).map S.f).hom =
        eRightOwner.symm.toLinearEquiv.toLinearMap.comp
          ((HomologicalComplex.homologyMap T.f 0).hom.comp eMidOwner.toLinearEquiv.toLinearMap) := by
    exact congrArg ModuleCat.Hom.hom hMapOwnerCat
  let δOwner :
      SourceTorOwner[1](↑S.X₃) ⟶ SourceTorOwner[0](↑S.X₁) :=
    ModuleCat.ofHom
      (eMidOwner.symm.toLinearEquiv.toLinearMap.comp
        (((hT.δ 1 0 (by simp)).hom).comp eLeft.toLinearEquiv.toLinearMap))
  have hOwner :
      Function.Exact δOwner.hom
        ((((Tor' (ModuleCat B) 0).obj (ModuleCat.of B C)).map S.f).hom) := by
    -- Postcompose by the degree-zero source-owner identification on the right endpoint.
    rw [hMapOwner]
    have hPostOwner :
        Function.Exact δOwner.hom
          (eRightOwner.symm.toLinearEquiv.toLinearMap.comp
            ((HomologicalComplex.homologyMap T.f 0).hom.comp
              eMidOwner.toLinearEquiv.toLinearMap)) := by
      simpa [δOwner] using
        (LinearEquiv.postcomp_exact_iff_exact (e := eRightOwner.symm.toLinearEquiv)).2 hMidOwner
    simpa using hPostOwner
  let eMid :
      SourceTorOwner[0](↑S.X₁) ≅ ModuleCat.of B (C ⊗[B] ↑S.X₁) :=
    (source_owner_degree_zero_tensor_linear_equiv
      (B := B) (C := C) (↑S.X₁)).toModuleIso
  let eRight :
      SourceTorOwner[0](↑S.X₂) ≅ ModuleCat.of B (C ⊗[B] ↑S.X₂) :=
    (source_owner_degree_zero_tensor_linear_equiv
      (B := B) (C := C) (↑S.X₂)).toModuleIso
  have hMid :
      Function.Exact
        (eMid.toLinearEquiv.toLinearMap.comp δOwner.hom)
        ((((Tor' (ModuleCat B) 0).obj (ModuleCat.of B C)).map S.f).hom.comp
          eMid.symm.toLinearEquiv.toLinearMap) := by
    -- Conjugate the degree-zero source owner to the literal tensor product on the middle term.
    exact exact_conj_middle (B := B) (e := eMid.toLinearEquiv) hOwner
  have hMap :
      (S.f.hom.lTensor C) =
        eRight.toLinearEquiv.toLinearMap.comp
          ((((Tor' (ModuleCat B) 0).obj (ModuleCat.of B C)).map S.f).hom.comp
            eMid.symm.toLinearEquiv.toLinearMap) := by
    -- The degree-zero source-owner comparison is natural in the second tensor variable.
    exact congrArg ModuleCat.Hom.hom
      (source_owner_degree_zero_tensor_map_transport (B := B) (C := C) S)
  let δ :
      SourceTorOwner[1](↑S.X₃) ⟶ ModuleCat.of B (C ⊗[B] ↑S.X₁) :=
    ModuleCat.ofHom (eMid.toLinearEquiv.toLinearMap.comp δOwner.hom)
  refine ⟨δ, ?_⟩
  -- Finally, postcompose by the right degree-zero tensor comparison and rewrite the target map.
  rw [hMap]
  have hPost :
      Function.Exact δ.hom
        (eRight.toLinearEquiv.toLinearMap.comp
          ((((Tor' (ModuleCat B) 0).obj (ModuleCat.of B C)).map S.f).hom.comp
            eMid.symm.toLinearEquiv.toLinearMap)) := by
    simpa [δ] using
      (LinearEquiv.postcomp_exact_iff_exact (e := eRight.toLinearEquiv)).2 hMid
  simpa using hPost

/-- Helper for Lemma 10.134.4 (Jacobi-Zariski sequence): the fixed-coefficient source owner also
gives the one-degree-earlier prefix
`Tor'₂(C, X₃) → Tor'₁(C, X₁) → Tor'₁(C, X₂)` for a short exact row
`0 → X₁ → X₂ → X₃ → 0`. -/
theorem source_owner_tor_two_tor_one_prefix_of_shortExact
    (S : ShortComplex (ModuleCat B)) (hS : S.ShortExact) :
    ∃ δ :
        SourceTorOwner[2](↑S.X₃) ⟶ SourceTorOwner[1](↑S.X₁),
      Function.Exact δ.hom ((((Tor' (ModuleCat B) 1).obj (ModuleCat.of B C)).map S.f).hom) := by
  let P : CategoryTheory.ProjectiveResolution (ModuleCat.of B C) :=
    CategoryTheory.projectiveResolution (ModuleCat.of B C)
  let φ :
      ((tensorRight (S.X₁ : ModuleCat.{u} B)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
          P.complex ⟶
        ((tensorRight (S.X₂ : ModuleCat.{u} B)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
          P.complex :=
    ((NatTrans.mapHomologicalComplex ((tensoringRight (ModuleCat.{u} B)).map S.f)
      (ComplexShape.down ℕ)).app P.complex)
  let ψ :
      ((tensorRight (S.X₂ : ModuleCat.{u} B)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
          P.complex ⟶
        ((tensorRight (S.X₃ : ModuleCat.{u} B)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
          P.complex :=
    ((NatTrans.mapHomologicalComplex ((tensoringRight (ModuleCat.{u} B)).map S.g)
      (ComplexShape.down ℕ)).app P.complex)
  have hzero : φ ≫ ψ = 0 := by
    -- The tensorized chain maps still compose to zero because they are left whiskerings of
    -- `S.f ≫ S.g = 0`.
    refine HomologicalComplex.Hom.ext ?_
    apply funext
    intro n
    apply ModuleCat.hom_ext
    ext x
    dsimp [φ, ψ]
    rw [← ModuleCat.hom_comp]
    rw [← MonoidalCategory.whiskerLeft_comp, S.zero]
    rw [ModuleCat.hom_whiskerLeft]
    change (LinearMap.lTensor (P.complex.X n) (0 : S.X₁ →ₗ[B] S.X₃)) x =
      (0 : P.complex.X n ⊗[B] S.X₁ →ₗ[B] P.complex.X n ⊗[B] S.X₃) x
    simp
  let T : ShortComplex (ChainComplex (ModuleCat.{u} B) ℕ) := ShortComplex.mk φ ψ hzero
  have hT : T.ShortExact := by
    -- Tensoring each degree of the chosen projective resolution with the short exact row `S`
    -- stays short exact because the resolution terms are projective, hence flat.
    refine HomologicalComplex.shortExact_of_degreewise_shortExact T ?_
    intro n
    refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
    · rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
      let _ : Module.Projective B (P.complex.X n) :=
        module_projective_of_categorical_projective (B := B) (P.complex.X n) (P.projective n)
      let _ : Module.Flat B (P.complex.X n) := Module.Flat.of_projective
      have hExactBase : Function.Exact S.f.hom S.g.hom := by
        exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).1 hS.exact
      simpa [T, φ, ψ, CategoryTheory.Functor.mapHomologicalComplex_map_f,
        ModuleCat.hom_whiskerLeft] using
        (Module.Flat.lTensor_exact (P.complex.X n) hExactBase)
    · exact (ModuleCat.mono_iff_injective _).2 <| by
        let _ : Module.Projective B (P.complex.X n) :=
          module_projective_of_categorical_projective (B := B) (P.complex.X n) (P.projective n)
        let _ : Module.Flat B (P.complex.X n) := Module.Flat.of_projective
        have hf : Function.Injective S.f.hom := (ModuleCat.mono_iff_injective _).1 hS.mono_f
        simpa [T, φ, CategoryTheory.Functor.mapHomologicalComplex_map_f,
          ModuleCat.hom_whiskerLeft] using
          (Module.Flat.lTensor_preserves_injective_linearMap (M := P.complex.X n) S.f.hom hf)
    · exact (ModuleCat.epi_iff_surjective _).2 <| by
        have hg : Function.Surjective S.g.hom := (ModuleCat.epi_iff_surjective _).1 hS.epi_g
        simpa [T, ψ, CategoryTheory.Functor.mapHomologicalComplex_map_f,
          ModuleCat.hom_whiskerLeft] using
          (LinearMap.lTensor_surjective (P.complex.X n) hg)
  let eLeft :
      SourceTorOwner[2](↑S.X₃) ≅ T.X₃.homology 2 := by
    -- This is the degree-two left-derived comparison computed on the fixed projective resolution.
    erw [source_tor_owner_eq_leftDerived_obj (B := B) (C := C) 2 (↑S.X₃)]
    exact P.isoLeftDerivedObj (tensorRight (S.X₃ : ModuleCat.{u} B)) 2
  let eMid :
      SourceTorOwner[1](↑S.X₁) ≅ T.X₁.homology 1 := by
    -- The middle source-owner term is the degree-one left-derived functor on the same resolution.
    erw [source_tor_owner_eq_leftDerived_obj (B := B) (C := C) 1 (↑S.X₁)]
    exact P.isoLeftDerivedObj (tensorRight (S.X₁ : ModuleCat.{u} B)) 1
  let eRight :
      SourceTorOwner[1](↑S.X₂) ≅ T.X₂.homology 1 := by
    -- Likewise for the right endpoint.
    erw [source_tor_owner_eq_leftDerived_obj (B := B) (C := C) 1 (↑S.X₂)]
    exact P.isoLeftDerivedObj (tensorRight (S.X₂ : ModuleCat.{u} B)) 1
  have hRaw :
      Function.Exact (hT.δ 2 1 (by simp)).hom (HomologicalComplex.homologyMap T.f 1).hom := by
    -- The `(2,1)` window of the homology long exact sequence is exact for the tensorized row `T`.
    exact
      (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact
        (S := ShortComplex.mk _ _ (ShortComplex.ShortExact.δ_comp hT 2 1 (by simp)))).1
        (hT.homology_exact₁ 2 1 (by simp))
  have hPre :
      Function.Exact
        ((hT.δ 2 1 (by simp)).hom.comp eLeft.toLinearEquiv.toLinearMap)
        (HomologicalComplex.homologyMap T.f 1).hom := by
    -- Changing only the source of the first map is harmless because `eLeft` is bijective.
    simpa using
      (LinearEquiv.precomp_exact_iff_exact (e := eLeft.toLinearEquiv)).2 hRaw
  have hMid :
      Function.Exact
        (eMid.symm.toLinearEquiv.toLinearMap.comp
          (((hT.δ 2 1 (by simp)).hom).comp eLeft.toLinearEquiv.toLinearMap))
        ((HomologicalComplex.homologyMap T.f 1).hom.comp eMid.toLinearEquiv.toLinearMap) := by
    -- Conjugate the middle term from raw homology to the source-owner `Tor'₁(C, X₁)`.
    exact exact_conj_middle (B := B) (e := eMid.symm.toLinearEquiv) hPre
  have hMapCat :
      (((Tor' (ModuleCat B) 1).obj (ModuleCat.of B C)).map S.f) =
        eMid.hom ≫ HomologicalComplex.homologyMap T.f 1 ≫ eRight.inv := by
    -- The `Tor'₁` map is exactly the homology map of the tensorized chain map, transported by
    -- the chosen projective-resolution identifications.
    simpa [T, φ, source_tor_owner_eq_leftDerived_obj, Category.assoc, Tor'] using
      (CategoryTheory.ProjectiveResolution.leftDerived_app_eq
        ((tensoringRight (ModuleCat.{u} B)).map S.f) P 1)
  have hMap :
      (((Tor' (ModuleCat B) 1).obj (ModuleCat.of B C)).map S.f).hom =
        eRight.symm.toLinearEquiv.toLinearMap.comp
          ((HomologicalComplex.homologyMap T.f 1).hom.comp eMid.toLinearEquiv.toLinearMap) := by
    exact congrArg ModuleCat.Hom.hom hMapCat
  let δ :
      SourceTorOwner[2](↑S.X₃) ⟶ SourceTorOwner[1](↑S.X₁) :=
    ModuleCat.ofHom
      (eMid.symm.toLinearEquiv.toLinearMap.comp
        (((hT.δ 2 1 (by simp)).hom).comp eLeft.toLinearEquiv.toLinearMap))
  refine ⟨δ, ?_⟩
  -- Finally, transport the target from raw homology to the source-owner `Tor'₁(C, X₂)`.
  rw [hMap]
  have hPost :
      Function.Exact δ.hom
        (eRight.symm.toLinearEquiv.toLinearMap.comp
          ((HomologicalComplex.homologyMap T.f 1).hom.comp eMid.toLinearEquiv.toLinearMap)) := by
    simpa [δ] using
      (LinearEquiv.postcomp_exact_iff_exact (e := eRight.symm.toLinearEquiv)).2 hMid
  simpa using hPost

/-- Helper for Lemma 10.134.4 (Jacobi-Zariski sequence): if `X` is projective, then the fixed
source-owner term `Tor'₁(C, X)` vanishes because tensoring the chosen projective resolution of `C`
with `X` stays exact. -/
theorem isZero_source_owner_tor_one_of_projective
    (X : Type u) [AddCommGroup X] [Module B X] [Projective (ModuleCat.of B X)] :
    IsZero (SourceTorOwner[1](X)) := by
  let P : CategoryTheory.ProjectiveResolution (ModuleCat.of B C) :=
    CategoryTheory.projectiveResolution (ModuleCat.of B C)
  let _ : Module.Projective B X :=
    module_projective_of_categorical_projective (B := B) X inferInstance
  let _ : Module.Flat B X := Module.Flat.of_projective
  have hExactBase :
      Function.Exact (P.complex.d 2 1).hom (P.complex.d 1 0).hom := by
    -- The fixed projective resolution is exact in consecutive positive degrees.
    simpa using
      (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp (P.exact_succ 0)
  have hExactTensor :
      Function.Exact ((P.complex.d 2 1).hom.rTensor X) ((P.complex.d 1 0).hom.rTensor X) := by
    -- Flatness of `X` preserves the exact `2 → 1 → 0` window after tensoring on the right.
    exact Module.Flat.rTensor_exact X hExactBase
  have hWindowExact : (source_owner_degree_one_window (B := B) (C := C) X).Exact := by
    -- The explicit source-owner window is precisely the tensorized `2 → 1 → 0` resolution row.
    rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
    simpa [source_owner_degree_one_window, CategoryTheory.Functor.mapHomologicalComplex_obj_d,
      ModuleCat.hom_whiskerRight] using hExactTensor
  have hZeroHomology :
      IsZero (ShortComplex.homology (source_owner_degree_one_window (B := B) (C := C) X)) := by
    -- Exactness of the concrete window forces its homology to vanish.
    exact
      (source_owner_degree_one_window (B := B) (C := C) X).exact_iff_isZero_homology.1
        hWindowExact
  -- Transport the vanishing of the concrete window back to the source owner `Tor'₁(C, X)`.
  exact
    IsZero.of_iso hZeroHomology
      (source_owner_degree_one_window_homology_iso (B := B) (C := C) X)

omit [Algebra A C] [IsScalarTower A B C] in
/-- Helper for Lemma 10.134.4 (Jacobi-Zariski sequence): the canonical source-owner first row for
`0 → range(d) → P.CotangentSpace → Ω[B⁄A] → 0`, expressed directly in the fixed-coefficient
`Tor'(-, C)` owner. -/
theorem tor_one_tensor_cotangent_row_exact_source_owner
    (P : Algebra.Extension.{u} A B) :
    ∃ δ :
        SourceTorOwner[1](Ω[B⁄A]) ⟶
          ModuleCat.of B (C ⊗[B] LinearMap.range P.cotangentComplex),
      Function.Exact δ.hom (((LinearMap.range P.cotangentComplex).subtype).lTensor C) := by
  -- This is the first cotangent row as a direct specialization of the generic source-owner row.
  simpa [cotangent_range_shortComplex] using
    source_owner_tor_one_tensor_row_of_shortExact (B := B) (C := C)
      (cotangent_range_shortComplex (A := A) (B := B) P)
      (cotangent_range_shortExact (A := A) (B := B) P)

omit [Algebra A C] [IsScalarTower A B C] in
/-- Helper for Lemma 10.134.4 (Jacobi-Zariski sequence): the canonical source-owner second row for
`0 → H¹(L_{B/A}) → P.Cotangent → range(d) → 0`, again expressed in the fixed-coefficient
`Tor'(-, C)` owner. -/
theorem tor_one_tensor_h1_row_exact_source_owner
    (P : Algebra.Extension.{u} A B) :
    ∃ δ :
        SourceTorOwner[1](LinearMap.range P.cotangentComplex) ⟶
          ModuleCat.of B (C ⊗[B] P.H1Cotangent),
      Function.Exact δ.hom ((P.h1Cotangentι).lTensor C) := by
  let S : ShortComplex (ModuleCat B) :=
    ShortComplex.moduleCatMk
      P.h1Cotangentι
      P.cotangentComplex.rangeRestrict
      (h1Cotangent_comp_rangeRestrict_eq_zero (A := A) (B := B) P)
  have hS : S.ShortExact := by
    -- This is the second short exact row in the source proof, before tensoring with `C`.
    refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
    · rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
      exact h1Cotangent_exact_rangeRestrict (A := A) (B := B) P
    · exact (ModuleCat.mono_iff_injective _).2 P.h1Cotangentι_injective
    · exact (ModuleCat.epi_iff_surjective _).2
        (LinearMap.surjective_rangeRestrict P.cotangentComplex)
  -- This is the generic source-owner row specialized to the `H¹` short exact sequence.
  simpa [S] using
    source_owner_tor_one_tensor_row_of_shortExact (B := B) (C := C) S hS

omit [Algebra A C] [IsScalarTower A B C] in
/-- Helper for Lemma 10.134.4 (Jacobi-Zariski sequence): the first source row yields a canonical
incoming map from `Tor₁^B(Ω[B⁄A], C)` whose exactness at `range(P.cotangentComplex) ⊗ C` is the
only input needed to read off injectivity of the tensorized range inclusion. -/
theorem tor_one_tensor_cotangent_row_source_exact
    (P : Algebra.Extension.{u} A B) :
    ∃ δ :
        TorOmega[1] ⟶ ModuleCat.of B (C ⊗[B] LinearMap.range P.cotangentComplex),
      Function.Exact δ.hom (((LinearMap.range P.cotangentComplex).subtype).lTensor C) := by
  obtain ⟨δ, hExact⟩ :=
    tor_one_tensor_cotangent_row_exact_source_owner (A := A) (B := B) (C := C) P
  let e : TorOmega[1] ≃ₗ[B] ↑(SourceTorOwner[1](Ω[B⁄A])) :=
    tor_flip_source_owner_linear_equiv (B := B) 1 Ω[B⁄A]
  -- Precompose the canonical source-owner row with the `tor_flip_iso` boundary map.
  refine ⟨ModuleCat.ofHom (δ.hom.comp e.toLinearMap), ?_⟩
  simpa using (LinearEquiv.precomp_exact_iff_exact (e := e)).2 hExact

omit [Algebra A C] [IsScalarTower A B C] in
/-- Helper for Lemma 10.134.4 (Jacobi-Zariski sequence): the second source row yields a canonical
incoming map from `Tor₁^B(range(P.cotangentComplex), C)` whose exactness at
`P.H1Cotangent ⊗ C` is the source-facing input for tensoring the `H¹` inclusion. -/
theorem tor_one_tensor_h1_row_source_exact
    (P : Algebra.Extension.{u} A B) :
    ∃ δ :
        (((Tor (ModuleCat B) 1).obj (ModuleCat.of B (LinearMap.range P.cotangentComplex))).obj
          (ModuleCat.of B C)) ⟶ ModuleCat.of B (C ⊗[B] P.H1Cotangent),
      Function.Exact δ.hom ((P.h1Cotangentι).lTensor C) := by
  obtain ⟨δ, hExact⟩ :=
    tor_one_tensor_h1_row_exact_source_owner (A := A) (B := B) (C := C) P
  let e :
      (((Tor (ModuleCat B) 1).obj (ModuleCat.of B (LinearMap.range P.cotangentComplex))).obj
        (ModuleCat.of B C)) ≃ₗ[B]
        ↑(SourceTorOwner[1](LinearMap.range P.cotangentComplex)) :=
    tor_flip_source_owner_linear_equiv (B := B) 1
      (LinearMap.range P.cotangentComplex)
  -- Again, the public source row is just the canonical source-owner row precomposed with
  -- `tor_flip_iso`.
  refine ⟨ModuleCat.ofHom (δ.hom.comp e.toLinearMap), ?_⟩
  simpa using (LinearEquiv.precomp_exact_iff_exact (e := e)).2 hExact

omit [Algebra A C] [IsScalarTower A B C] in
/-- Helper for Lemma 10.134.4 (Jacobi-Zariski sequence): the short exact row
`0 → range(d) → P.CotangentSpace → Ω[B⁄A] → 0` stays left-exact after tensoring with `C` when
`Tor₁^B(Ω[B⁄A], C)` vanishes. -/
theorem tensor_cotangent_range_subtype_injective_of_tor1
    (P : Algebra.Extension.{u} A B)
    (hTor : IsZero (TorOmega[1])) :
    Function.Injective (((LinearMap.range P.cotangentComplex).subtype).lTensor C) := by
  obtain ⟨δOwner, hExactOwner⟩ :=
    tor_one_tensor_cotangent_row_exact_source_owner (A := A) (B := B) (C := C) P
  let e : TorOmega[1] ≃ₗ[B] ↑(SourceTorOwner[1](Ω[B⁄A])) :=
    tor_flip_source_owner_linear_equiv (B := B) 1 Ω[B⁄A]
  let δ : TorOmega[1] ⟶ ModuleCat.of B (C ⊗[B] LinearMap.range P.cotangentComplex) :=
    ModuleCat.ofHom (δOwner.hom.comp e.toLinearMap)
  have hExact : Function.Exact δ.hom (((LinearMap.range P.cotangentComplex).subtype).lTensor C) := by
    -- This is the public first row obtained by precomposing the canonical source-owner row.
    simpa [δ] using (LinearEquiv.precomp_exact_iff_exact (e := e)).2 hExactOwner
  -- Killing the incoming public `Tor₁(Ω[B⁄A], C)` term forces the tensorized range inclusion to
  -- identify with the kernel inclusion.
  have hδ : δ = 0 := hTor.eq_of_src _ _
  have hExactZero :
      Function.Exact
        (0 : TorOmega[1] →ₗ[B] C ⊗[B] LinearMap.range P.cotangentComplex)
        (((LinearMap.range P.cotangentComplex).subtype).lTensor C) := by
    simpa [hδ] using hExact
  have hker :
      LinearMap.ker (((LinearMap.range P.cotangentComplex).subtype).lTensor C) = ⊥ := by
    have hrange :
        LinearMap.ker (((LinearMap.range P.cotangentComplex).subtype).lTensor C) =
          LinearMap.range
            (0 : TorOmega[1] →ₗ[B] C ⊗[B] LinearMap.range P.cotangentComplex) :=
      LinearMap.exact_iff.mp hExactZero
    rw [LinearMap.range_zero] at hrange
    simpa using hrange
  exact LinearMap.ker_eq_bot.mp hker

omit [Algebra A C] [IsScalarTower A B C] in
/-- Helper for Lemma 10.134.4 (Jacobi-Zariski sequence): if
`Tor₁^B(range(P.cotangentComplex), C)` vanishes, then tensoring
`P.H1Cotangent ↪ P.Cotangent` with `C` stays injective. -/
theorem tensor_h1Cotangent_injective_of_isZero_tor1_cotangent_range
    (P : Algebra.Extension.{u} A B)
    (hTor :
      IsZero
        ((((Tor (ModuleCat B) 1).obj (ModuleCat.of B (LinearMap.range P.cotangentComplex))).obj
          (ModuleCat.of B C)))) :
    Function.Injective ((P.h1Cotangentι).lTensor C) := by
  obtain ⟨δ, hExact⟩ :
      ∃ δ :
          (((Tor (ModuleCat B) 1).obj (ModuleCat.of B (LinearMap.range P.cotangentComplex))).obj
            (ModuleCat.of B C)) ⟶ ModuleCat.of B (C ⊗[B] P.H1Cotangent),
        Function.Exact δ.hom ((P.h1Cotangentι).lTensor C) :=
    tor_one_tensor_h1_row_source_exact (A := A) (B := B) (C := C) P
  -- Killing the incoming `Tor₁(range(d), C)` term identifies the tensorized inclusion with a
  -- kernel inclusion.
  have hδ : δ = 0 := hTor.eq_of_src _ _
  have hExactZero :
      Function.Exact
        (0 :
          ((((Tor (ModuleCat B) 1).obj (ModuleCat.of B (LinearMap.range P.cotangentComplex))).obj
            (ModuleCat.of B C))) →ₗ[B]
            C ⊗[B] P.H1Cotangent)
        ((P.h1Cotangentι).lTensor C) := by
    simpa [hδ] using hExact
  have hker : LinearMap.ker ((P.h1Cotangentι).lTensor C) = ⊥ := by
    have hrange :
        LinearMap.ker ((P.h1Cotangentι).lTensor C) =
          LinearMap.range
            (0 :
              ((((Tor (ModuleCat B) 1).obj (ModuleCat.of B (LinearMap.range P.cotangentComplex))).obj
                (ModuleCat.of B C))) →ₗ[B]
                C ⊗[B] P.H1Cotangent) :=
      LinearMap.exact_iff.mp hExactZero
    rw [LinearMap.range_zero] at hrange
    simpa using hrange
  exact LinearMap.ker_eq_bot.mp hker

omit [Algebra A C] [IsScalarTower A B C] in
/-- Helper for Lemma 10.134.4 (Jacobi-Zariski sequence): the projective cotangent-space row
converts `Tor₂^B(Ω[B⁄A], C) = 0` into `Tor₁^B(range(P.cotangentComplex), C) = 0`. -/
theorem isZero_tor1_cotangent_range_of_isZero_tor2
    (P : Algebra.Extension A B)
    [Projective (ModuleCat.of B P.CotangentSpace)]
    (hTor : IsZero (TorOmega[2])) :
    IsZero
      ((((Tor (ModuleCat B) 1).obj (ModuleCat.of B (LinearMap.range P.cotangentComplex))).obj
        (ModuleCat.of B C))) := by
  obtain ⟨δ, hExact⟩ :=
    source_owner_tor_two_tor_one_prefix_of_shortExact (B := B) (C := C)
      (cotangent_range_shortComplex (A := A) (B := B) P)
      (cotangent_range_shortExact (A := A) (B := B) P)
  let eLeft : TorOmega[2] ≃ₗ[B] ↑(SourceTorOwner[2](Ω[B⁄A])) :=
    tor_flip_source_owner_linear_equiv (B := B) (C := C) 2 Ω[B⁄A]
  let eMid :
      (((Tor (ModuleCat B) 1).obj (ModuleCat.of B (LinearMap.range P.cotangentComplex))).obj
        (ModuleCat.of B C)) ≃ₗ[B]
        ↑(SourceTorOwner[1](LinearMap.range P.cotangentComplex)) :=
    tor_flip_source_owner_linear_equiv (B := B) (C := C) 1
      (LinearMap.range P.cotangentComplex)
  have hLeftSource : IsZero (SourceTorOwner[2](Ω[B⁄A])) := by
    -- Move the public `Tor₂(Ω[B⁄A], C)` vanishing into the fixed-coefficient source owner.
    exact IsZero.of_iso hTor eLeft.toModuleIso.symm
  have hRightSource : IsZero (SourceTorOwner[1](P.CotangentSpace)) := by
    -- Projectivity of the cotangent space kills the degree-one source-owner endpoint.
    exact isZero_source_owner_tor_one_of_projective (B := B) (C := C) P.CotangentSpace
  let g :
      SourceTorOwner[1](LinearMap.range P.cotangentComplex) ⟶
        SourceTorOwner[1](P.CotangentSpace) :=
    (((Tor' (ModuleCat B) 1).obj (ModuleCat.of B C)).map
      (ModuleCat.ofHom ((LinearMap.range P.cotangentComplex).subtype)))
  have hδ : δ = 0 := hLeftSource.eq_of_src _ _
  have hg : g = 0 := hRightSource.eq_of_tgt _ _
  have hMidSource :
      IsZero (SourceTorOwner[1](LinearMap.range P.cotangentComplex)) := by
    -- Exactness with both endpoint maps equal to zero forces the middle source-owner term to
    -- vanish.
    exact isZero_of_exact_zero_zero (B := B) hExact hδ hg
  -- Return to the public source-facing owner `Tor₁(range(d), C)`.
  exact IsZero.of_iso hMidSource eMid.toModuleIso

omit [Algebra A C] [IsScalarTower A B C] in
/-- Continuation of Lemma 10.134.4 (Jacobi-Zariski sequence): if `Tor₁^B(Ω[B⁄A], C)` and
`Tor₂^B(Ω[B⁄A], C)` vanish, then tensoring the canonical inclusion
`H¹(L_{B/A}) ↪ (NL_{B/A})₁` identifies `C ⊗[B] H¹(L_{B/A})` with the first homology of the
tensor-product naive cotangent complex. Concretely, the tensor of `h1Cotangentι` is injective and
exact with the base-changed cotangent map. -/
theorem tensor_h1Cotangent_exact_of_tor_vanishing
    (hTor1 : IsZero (TorOmega[1]))
    (hTor2 : IsZero (TorOmega[2])) :
    let P := (Generators.self A B).toExtension
    Function.Injective ((P.h1Cotangentι).lTensor C) ∧
      Function.Exact ((P.h1Cotangentι).lTensor C) (LinearMap.baseChange C P.cotangentComplex) :=
  by
    let P : Algebra.Extension A B := (Generators.self A B).toExtension
    change Function.Injective ((P.h1Cotangentι).lTensor C) ∧
      Function.Exact ((P.h1Cotangentι).lTensor C) (LinearMap.baseChange C P.cotangentComplex)
    constructor
    · -- Route correction: first dimension-shift along the projective cotangent-space row, then
      -- tensor the `H¹ → P.Cotangent → range(d)` short exact sequence.
      have hRangeTor1 :
          IsZero
            ((((Tor (ModuleCat B) 1).obj (ModuleCat.of B (LinearMap.range P.cotangentComplex))).obj
              (ModuleCat.of B C))) :=
        isZero_tor1_cotangent_range_of_isZero_tor2
          (A := A) (B := B) (C := C) P hTor2
      exact tensor_h1Cotangent_injective_of_isZero_tor1_cotangent_range
        (A := A) (B := B) (C := C) P hRangeTor1
    · -- The exactness part only needs the `Tor₁` vanishing on `Ω[B⁄A]`.
      have hRangeInj :
          Function.Injective (((LinearMap.range P.cotangentComplex).subtype).lTensor C) := by
        -- The cotangent-space row is the first short exact sequence in the source proof.
        exact tensor_cotangent_range_subtype_injective_of_tor1
          (A := A) (B := B) (C := C) P hTor1
      exact tensor_h1Cotangent_exact_via_cotangent_range (A := A) (B := B) (C := C) P hRangeInj

end
