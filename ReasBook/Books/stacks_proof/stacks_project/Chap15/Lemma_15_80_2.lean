import Mathlib
import StacksProject_2024.Chap10.Definition_10_109_10
import StacksProject_2024.Chap10.Lemma_10_109_8
import StacksProject_2024.Chap10.Lemma_10_109_12
import StacksProject_2024.Chap10.Definition_10_110_7
import StacksProject_2024.Chap10.Lemma_10_110_8
import StacksProject_2024.Chap13.Lemma_13_19_8
import StacksProject_2024.Chap13.Lemma_13_19_11
import StacksProject_2024.Chap13.Lemma_13_27_3
import StacksProject_2024.Chap13.Lemma_13_35_4
import StacksProject_2024.Chap13.Lemma_13_36_1
import StacksProject_2024.Chap15.Definition_15_65_1
import StacksProject_2024.Chap15.Lemma_15_65_11
import StacksProject_2024.Chap15.Lemma_15_65_17
import StacksProject_2024.Chap15.Lemma_15_66_1
import StacksProject_2024.Chap15.Lemma_15_79_1
import StacksProject_2024.Chap15.Lemma_15_80_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory.ObjectProperty
open CategoryTheory.Pretriangulated
open CategoryTheory.Abelian
open scoped CategoryTheory.ObjectProperty.ExtensionProductNotation
open scoped CategoryTheory.ObjectProperty.GeneratedNotation
open scoped DerivedExt

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

local notation "Cpx" => CochainComplex (ModuleCat R) ℤ
local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "PerfectObj" => (DerivedCategory.IsPerfect : ObjectProperty DMod)
local notation "KQ" => HomotopyCategory.quotient (ModuleCat R) (ComplexShape.up ℤ)

/-- Helper for Lemma 15.80.2: the image of the singleton object property under a functor is the
isomorphism closure of the singleton on the image object. -/
lemma map_singleton_eq_isoClosure_singleton
    {C : Type*} [Category C] {D : Type*} [Category D]
    (F : C ⥤ D) (E : C) :
    (ObjectProperty.singleton E).map F = (ObjectProperty.singleton (F.obj E)).isoClosure := by
  ext Y
  constructor
  · rintro ⟨X, hX, ⟨e⟩⟩
    rw [ObjectProperty.singleton_iff] at hX
    subst hX
    exact ⟨F.obj E, by simp, ⟨e.symm⟩⟩
  · rintro ⟨Y', hY', ⟨e⟩⟩
    rw [ObjectProperty.singleton_iff] at hY'
    subst hY'
    exact ⟨E, by simp, ⟨e.symm⟩⟩

/-- Helper for Lemma 15.80.2: exact functors carry bounded shift intervals of a single object to
the corresponding bounded shift intervals of the image object. -/
lemma map_objectShiftInterval
    {C : Type*} [Category C] [HasShift C ℤ]
    {D : Type*} [Category D] [HasShift D ℤ]
    (F : C ⥤ D) [F.CommShift ℤ] (E : C) (a b : ℤ) :
    (objectShiftInterval E a b).map F = objectShiftInterval (F.obj E) a b := by
  -- Rewrite the interval owner through `shiftInterval`, then use the exact-functor transport
  -- theorem together with the explicit description of the image of a singleton owner.
  simpa [ObjectProperty.objectShiftInterval, map_singleton_eq_isoClosure_singleton]
    using
      (ObjectProperty.map_shiftInterval (F := F)
        ((ObjectProperty.singleton E).isoClosure) a b)

/-- Helper for Lemma 15.80.2: exact functors carry additive-extension stages into the
corresponding stages of the image property. -/
lemma map_additiveExtensionStage_le
    {C : Type*} [Category C] [Limits.HasZeroObject C] [Preadditive C] [HasShift C ℤ]
    [(n : ℤ) → (shiftFunctor C n).Additive] [Pretriangulated C]
    {D : Type*} [Category D] [Limits.HasZeroObject D] [Preadditive D] [HasShift D ℤ]
    [(n : ℤ) → (shiftFunctor D n).Additive] [Pretriangulated D]
    (F : C ⥤ D) [F.Additive] [F.CommShift ℤ] [Functor.IsTriangulated F]
    (P : ObjectProperty C) (n : ℕ+) :
    (CategoryTheory.ObjectProperty.additiveExtensionStage P n).map F ≤
      CategoryTheory.ObjectProperty.additiveExtensionStage (P.map F) n := by
  -- First transport the iterated extension stage, then close under retracts on the target side.
  dsimp [CategoryTheory.ObjectProperty.additiveExtensionStage]
  have hiter :
      (P.additiveClosure.extensionProductIter n.natPred).map F ≤
        ((P.map F).additiveClosure.extensionProductIter n.natPred) := by
    exact
      (ObjectProperty.map_extensionProductIter_le (F := F) P.additiveClosure n.natPred).trans <|
        ObjectProperty.monotone_extensionProductIter
          (ObjectProperty.map_additiveClosure_le (F := F) P)
          n.natPred
  exact
    (ObjectProperty.map_retractClosure_le (F := F)
      (P := P.additiveClosure.extensionProductIter n.natPred)).trans <|
      ObjectProperty.monotone_retractClosure hiter

/-- Helper for Lemma 15.80.2: exact functors carry the `n`-th generated stage of an object into
the `n`-th generated stage of its image. -/
lemma map_objectGeneratedStage_le
    {C : Type*} [Category C] [Limits.HasZeroObject C] [Preadditive C] [HasShift C ℤ]
    [(n : ℤ) → (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]
    {D : Type*} [Category D] [Limits.HasZeroObject D] [Preadditive D] [HasShift D ℤ]
    [(n : ℤ) → (shiftFunctor D n).Additive] [Pretriangulated D] [IsTriangulated D]
    (F : C ⥤ D) [F.Additive] [F.CommShift ℤ] [Functor.IsTriangulated F]
    (E : C) (n : ℕ+) :
    ((⟨E⟩_n : ObjectProperty C).map F) ≤ (⟨F.obj E⟩_n : ObjectProperty D) := by
  -- Rewrite both generated stages as suprema of interval stages and transport each interval stage
  -- separately through the exact functor.
  rw [objectGeneratedStage_eq_iSup_intervalStages E n]
  rw [objectGeneratedStage_eq_iSup_intervalStages (F.obj E) n]
  rw [map_iSup]
  refine iSup_le fun m ↦ ?_
  refine
    (map_additiveExtensionStage_le (F := F)
      (P := objectShiftInterval E (-(m : ℤ)) (m : ℤ)) n).trans ?_
  -- The shift interval itself maps to the corresponding interval on the image object.
  simpa [map_objectShiftInterval]

/-- Helper for Lemma 15.80.2: a stage bound in the perfect derived category transports to the
ambient derived category along the full-subcategory inclusion. -/
lemma mem_objectGeneratedStage_of_strong_generator_in_DPerf
    {n : ℕ+}
    (hstage : (⟨ringSingleInPerfectDerived R⟩_n : ObjectProperty (DPerf R)) = ⊤)
    {K : DMod} (hK : K.IsPerfect) :
    (⟨ringSingle⟩_n : ObjectProperty DMod) K := by
  let iPerf : DPerf R ⥤ DMod := ObjectProperty.ι PerfectObj
  have hmap :
      ((⟨ringSingleInPerfectDerived R⟩_n : ObjectProperty (DPerf R)).map iPerf) ≤
        (⟨ringSingle⟩_n : ObjectProperty DMod) := by
    -- Transport the generated stage from `D_{perf}(R)` into the ambient derived category.
    simpa [iPerf, ringSingleInPerfectDerived] using
      map_objectGeneratedStage_le (F := iPerf) (E := ringSingleInPerfectDerived R) n
  have hsource :
      (⟨ringSingleInPerfectDerived R⟩_n : ObjectProperty (DPerf R)) ⟨K, hK⟩ := by
    -- Evaluate the stage-equality hypothesis on the perfect object `K`.
    simpa [hstage] using (show (⊤ : ObjectProperty (DPerf R)) ⟨K, hK⟩ from trivial)
  have hmapped :
      (((⟨ringSingleInPerfectDerived R⟩_n : ObjectProperty (DPerf R)).map iPerf) K) := by
    -- The full-subcategory inclusion forgets only the perfectness witness.
    simpa [iPerf] using ObjectProperty.prop_map_obj iPerf hsource
  exact hmap hmapped

/-- Helper for Lemma 15.80.2: an object supported in degrees `≤ -s - 1` has no maps to
`N[0]⟦s⟧`. -/
lemma hom_eq_zero_of_isLE_low_to_shifted_single
    (s : ℕ+) {C : DMod} (hC : C.IsLE (-((s : ℕ) : ℤ) - 1))
    (N : ModuleCat R)
    (f : C ⟶ ((ModuleCat.single0Functor : ModuleCat R ⥤ DMod).obj N)⟦(s : ℤ)⟧) :
    f = 0 := by
  have hsub :
      Subsingleton
        (C ⟶ ((ModuleCat.single0Functor : ModuleCat R ⥤ DMod).obj N)⟦(s : ℤ)⟧) := by
    -- Reinterpret the morphism group as a shifted Hom group and apply the canonical vanishing
    -- range for `Ext`.
    simpa using
      shiftedHom_subsingleton_of_lt_sub
        C
        ((ModuleCat.single0Functor : ModuleCat R ⥤ DMod).obj N)
        (-((s : ℕ) : ℤ) - 1)
        0
        (s : ℤ)
        hC
        (inferInstance :
          (((ModuleCat.single0Functor : ModuleCat R ⥤ DMod).obj N)).IsGE 0)
        (by omega)
  exact Subsingleton.elim _ _

/-- Helper for Lemma 15.80.2: finite global dimension gives regularity together with an exact
finite Krull-dimension witness. -/
lemma exists_regularRing_and_ringKrullDim_eq_of_finite_global_dimension
    [IsFiniteGlobalDimensionRing R] :
    ∃ n : ℕ, IsRegularRing R ∧ ringKrullDim R = n := by
  refine ⟨globalDimension R, ?_⟩
  -- Apply the Chapter 10 TFAE at the actual global dimension.
  exact
    ((finiteGlobalDimension_regularRing_localizations_tfae (R := R) (globalDimension R)).out 0 1).mp
      ⟨inferInstance, rfl⟩

/-- Helper for Lemma 15.80.2: the degree-zero complex of a finite module is `m`-pseudo-coherent
in every negative degree bound needed for the generator length. -/
lemma finite_single_isMPseudoCoherent_at_neg_generator_length
    (s : ℕ+) (M : ModuleCat R) [Module.Finite R M] :
    DerivedCategory.IsMPseudoCoherent
      (((ModuleCat.single0Functor : ModuleCat R ⥤ DMod).obj M))
      (-((s : ℕ) : ℤ)) := by
  have hPseudo : M.IsPseudoCoherent := by
    -- Over a Noetherian ring, finite modules are pseudo-coherent.
    simpa using
      (_root_.Module.isPseudoCoherent_iff_finite (R := R) (M := ↥M)).2
        (show Module.Finite R ↥M from inferInstance)
  -- Specialize uniform pseudo-coherence to the negative generator bound.
  rw [ModuleCat.IsPseudoCoherent, isPseudoCoherent_iff_forall_isMPseudoCoherent] at hPseudo
  simpa [ModuleCat.IsMPseudoCoherent] using hPseudo (-((s : ℕ) : ℤ))

/-- Helper for Lemma 15.80.2: a bounded-above projective-minus complex that is also bounded below
and termwise finite free already represents a perfect object of `D(R)`. -/
lemma projective_minus_q_obj_isPerfect_of_strictlyGE_finiteFree
    (P : CochainComplex.ProjectiveMinus (ModuleCat R))
    (hPge : ∃ a : ℤ, (P : Cpx).IsStrictlyGE a)
    (hPfinite : ∀ i : ℤ, Module.Finite R ((P : Cpx).X i)) :
    (DerivedCategory.Q.obj (P : Cpx)).IsPerfect := by
  obtain ⟨a, hPge'⟩ := hPge
  obtain ⟨b, hPle⟩ := CochainComplex.MinusWithTermsIn.exists_isStrictlyLE P
  refine ⟨(P : Cpx), Iso.refl _, ?_⟩
  -- Proof comment: combine the lower bound supplied by the approximation with the built-in upper
  -- bound of `ProjectiveMinus` and the termwise projectivity/finite hypotheses.
  refine (CochainComplex.isBoundedFiniteProjective_iff (R := R) (L := (P : Cpx))).2 ?_
  refine ⟨⟨a, b, hPge', hPle⟩, hPfinite, ?_⟩
  intro i
  infer_instance

/-- Helper for Lemma 15.80.2: the source proof’s left-tail coefficient module is the cokernel of
`d^{-s-1} : P^{-s-1} ⟶ P^{-s}`. -/
abbrev projective_minus_tail_cokernel
    (s : ℕ+) (P : CochainComplex.ProjectiveMinus (ModuleCat R)) : ModuleCat R :=
  cokernel ((P : Cpx).d (-((s : ℕ) : ℤ) - 1) (-((s : ℕ) : ℤ)))

/-- Helper for Lemma 15.80.2: the defining tail cokernel projection kills the incoming
differential. -/
lemma projective_minus_tail_d_comp_cokernel_π_eq_zero
    (s : ℕ+) (P : CochainComplex.ProjectiveMinus (ModuleCat R)) :
    (P : Cpx).d (-((s : ℕ) : ℤ) - 1) (-((s : ℕ) : ℤ)) ≫
      cokernel.π ((P : Cpx).d (-((s : ℕ) : ℤ) - 1) (-((s : ℕ) : ℤ))) = 0 := by
  -- Proof comment: this is the universal relation of the cokernel of `d^{-s-1}`.
  simp

/-- Helper for Lemma 15.80.2: the left-tail cokernel projection gives the explicit chain-level
map `P^• ⟶ C[-s]` appearing in the textbook proof. -/
noncomputable def projective_minus_tail_to_single
    (s : ℕ+) (P : CochainComplex.ProjectiveMinus (ModuleCat R)) :
    (P : Cpx) ⟶
      (CochainComplex.singleFunctor (ModuleCat R) (-((s : ℕ) : ℤ))).obj
        (projective_minus_tail_cokernel (R := R) s P) :=
  (CochainComplex.HomComplex.Cocycle.toSingleMk
      (cokernel.π ((P : Cpx).d (-((s : ℕ) : ℤ) - 1) (-((s : ℕ) : ℤ))))
      (by omega)
      (-((s : ℕ) : ℤ) - 1)
      (by omega)
      (projective_minus_tail_d_comp_cokernel_π_eq_zero (R := R) s P)).homOf

/-- Helper for Lemma 15.80.2: every chain map from `P` to a single complex in degree `-s`
factors through the explicit tail-cokernel map. -/
lemma projective_minus_tail_to_single_postcompose_surjective
    (s : ℕ+)
    (P : CochainComplex.ProjectiveMinus (ModuleCat R))
    {N : ModuleCat R}
    (g : (P : Cpx) ⟶
      (CochainComplex.singleFunctor (ModuleCat R) (-((s : ℕ) : ℤ))).obj N) :
    ∃ φ : projective_minus_tail_cokernel (R := R) s P ⟶ N,
      projective_minus_tail_to_single (R := R) s P ≫
          (CochainComplex.singleFunctor (ModuleCat R) (-((s : ℕ) : ℤ))).map φ = g := by
  let φ : projective_minus_tail_cokernel (R := R) s P ⟶ N :=
    cokernel.desc
      ((P : Cpx).d (-((s : ℕ) : ℤ) - 1) (-((s : ℕ) : ℤ)))
      (g.f (-((s : ℕ) : ℤ)) ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (-((s : ℕ) : ℤ)) N).hom)
      (by
        -- Proof comment: the `(-s)` component of a chain map into the single complex is a cocycle,
        -- so it descends along the cokernel of `d^{-s-1}`.
        simpa [Category.assoc, HomologicalComplex.single_obj_d] using
          congrArg
            (fun f : (P : Cpx).X (-((s : ℕ) : ℤ) - 1) ⟶
                ((CochainComplex.singleFunctor (ModuleCat R) (-((s : ℕ) : ℤ))).obj N).X
                  (-((s : ℕ) : ℤ)) ↦
              f ≫
                (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (-((s : ℕ) : ℤ)) N).hom)
            (g.comm (-((s : ℕ) : ℤ) - 1) (-((s : ℕ) : ℤ)) (by simp)))
  refine ⟨φ, ?_⟩
  -- Proof comment: maps into a single complex are determined by their distinguished degree
  -- component, and that component is exactly the descended cokernel morphism `φ`.
  apply HomologicalComplex.to_single_hom_ext
  simp [φ, projective_minus_tail_to_single, Category.assoc]

/-- Helper for Lemma 15.80.2: for an approximation
`α : Q(P) ⟶ M[0]` at degree `-s`, precomposition by `α` is injective on morphisms to
`N[0]⟦s⟧`. -/
lemma approximation_precompose_shifted_single_mono_at_top
    (s : ℕ+)
    {P : CochainComplex.ProjectiveMinus (ModuleCat R)}
    {M : ModuleCat R}
    {α : DerivedCategory.Q.obj ((P : CochainComplex (ModuleCat R) ℤ)) ⟶
      ((ModuleCat.single0Functor : ModuleCat R ⥤ DMod).obj M)}
    (hαiso : ∀ i : ℤ, -((s : ℕ) : ℤ) < i → IsIso ((H i).map α))
    (hαepi : Epi ((H (-((s : ℕ) : ℤ))).map α))
    (N : ModuleCat R) :
    Function.Injective
      (fun g :
        ((ModuleCat.single0Functor : ModuleCat R ⥤ DMod).obj M) ⟶
          ((ModuleCat.single0Functor : ModuleCat R ⥤ DMod).obj N)⟦(s : ℤ)⟧ ↦
        α ≫ g) := by
  obtain ⟨C, β, δ, hT⟩ := distinguished_cocone_triangle α
  have hCone : C.IsLE (-((s : ℕ) : ℤ) - 1) := by
    -- The approximation triangle places its cone one step lower in the standard aisle.
    simpa using
      approximation_cone_isLE_pred
        (T := Triangle.mk α β δ) hT (-((s : ℕ) : ℤ)) hαiso hαepi
  intro g₁ g₂ hgg
  apply sub_eq_zero.mp
  have hsub : α ≫ (g₁ - g₂) = 0 := by
    -- Exactness is applied to the difference of the two candidate lifts.
    rw [Preadditive.comp_sub, sub_eq_zero]
    exact hgg
  obtain ⟨u, hu⟩ := (Triangle.mk α β δ).yoneda_exact₂ hT (g₁ - g₂) hsub
  have hu_zero : u = 0 := by
    -- The cone has no maps to the top shifted single object in this degree range.
    exact hom_eq_zero_of_isLE_low_to_shifted_single (R := R) s hCone N u
  rw [hu, hu_zero]
  simp

/-- Helper for Lemma 15.80.2: if a single degree-`s` extension class is universal for
postcomposition in the second variable, then proving that universal class is zero kills every
degree-`s` extension class out of the same source module. -/
lemma ext_eq_zero_of_universal_postcomp_zero
    {s : ℕ} {M C : ModuleCat R}
    (ξ : Ext M C s)
    (hξ :
      ∀ (N : ModuleCat R) (e : Ext M N s), ∃ φ : C ⟶ N,
        ((Abelian.Ext.mk₀ φ).postcomp M (Nat.add_zero s)) ξ = e)
    (hξzero : ξ = 0) :
    ∀ (N : ModuleCat R) (e : Ext M N s), e = 0 := by
  intro N e
  -- Proof comment: rewrite the target class as a postcomposition of the universal class and then
  -- use that postcomposition preserves zero.
  rcases hξ N e with ⟨φ, rfl⟩
  simp [hξzero]

/-- Helper for Lemma 15.80.2: transporting a morphism along source and target isomorphisms
preserves addition. -/
private theorem iso_homCongrAddEquiv_map_add
    {C : Type*} [Category C] [Preadditive C] {X Y X₁ Y₁ : C}
    (α : X ≅ X₁) (β : Y ≅ Y₁) (f g : X ⟶ Y) :
    α.homCongr β (f + g) = α.homCongr β f + α.homCongr β g := by
  -- Proof comment: `Iso.homCongr` is composition with isomorphism legs, so additivity is exactly
  -- bilinearity of composition.
  simp [Iso.homCongr, Preadditive.comp_add, Preadditive.add_comp]

/-- Helper for Lemma 15.80.2: isomorphisms on source and target induce an additive equivalence on
Hom groups. -/
private noncomputable def isoHomCongrAddEquiv
    {C : Type*} [Category C] [Preadditive C] {X Y X₁ Y₁ : C}
    (α : X ≅ X₁) (β : Y ≅ Y₁) :
    (X ⟶ Y) ≃+ (X₁ ⟶ Y₁) :=
  { toEquiv := α.homCongr β
    map_add' := iso_homCongrAddEquiv_map_add α β }

/-- Helper for Lemma 15.80.2: the strict single complex in degree `-s`, after passing to `D(R)`,
is canonically the shift of the degree-zero single object by `s`. -/
noncomputable def projective_minus_tail_single_shift_iso
    (s : ℕ+) (N : ModuleCat R) :
    DerivedCategory.Q.obj
        ((CochainComplex.singleFunctor (ModuleCat R) (-((s : ℕ) : ℤ))).obj N) ≅
      ((ModuleCat.single0Functor : ModuleCat R ⥤ DMod).obj N)⟦(s : ℤ)⟧ :=
  ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat R) (-((s : ℕ) : ℤ))).app N) ≪≫
    (((DerivedCategory.singleFunctors (ModuleCat R)).shiftIso
      (s : ℤ) (-((s : ℕ) : ℤ)) 0 (by omega)).app N).symm

/-- Helper for Lemma 15.80.2: homotopy-category maps from the approximation complex into the
strict single complex in degree `-s` identify additively with shifted derived morphisms out of
`Q(P)`. -/
noncomputable def projective_minus_to_shifted_single_add_equiv
    (s : ℕ+) (P : CochainComplex.ProjectiveMinus (ModuleCat R)) (N : ModuleCat R) :
    (((KQ).obj (P : Cpx)) ⟶
      ((KQ).obj
        ((CochainComplex.singleFunctor (ModuleCat R) (-((s : ℕ) : ℤ))).obj N))) ≃+
      (DerivedCategory.Q.obj (P : Cpx) ⟶
        ((ModuleCat.single0Functor : ModuleCat R ⥤ DMod).obj N)⟦(s : ℤ)⟧) :=
  ((AddEquiv.ofBijective
      (DerivedCategory.Qh.mapAddHom :
        (((KQ).obj (P : Cpx)) ⟶
            ((KQ).obj
              ((CochainComplex.singleFunctor (ModuleCat R) (-((s : ℕ) : ℤ))).obj N))) →+ _)
      (CochainComplex.homotopyCategory_to_derived_bijective_of_boundedAbove_projective
        P
        ((CochainComplex.singleFunctor (ModuleCat R) (-((s : ℕ) : ℤ))).obj N))).trans
    (isoHomCongrAddEquiv
      ((DerivedCategory.quotientCompQhIso (ModuleCat R)).app (P : Cpx))
      ((DerivedCategory.quotientCompQhIso (ModuleCat R)).app
        ((CochainComplex.singleFunctor (ModuleCat R) (-((s : ℕ) : ℤ))).obj N)))).trans
    (isoHomCongrAddEquiv
      (Iso.refl _)
      (projective_minus_tail_single_shift_iso (R := R) s N))

/-- Helper for Lemma 15.80.2: the explicit tail cocycle `P ⟶ C[-s]` transported to the shifted
derived target `C[0]⟦s⟧`. -/
noncomputable def projective_minus_tail_shifted_map
    (s : ℕ+)
    (P : CochainComplex.ProjectiveMinus (ModuleCat R))
    :
    DerivedCategory.Q.obj (P : Cpx) ⟶
      ((ModuleCat.single0Functor : ModuleCat R ⥤ DMod).obj
        (projective_minus_tail_cokernel (R := R) s P))⟦(s : ℤ)⟧ :=
  projective_minus_to_shifted_single_add_equiv (R := R) s P
      (projective_minus_tail_cokernel (R := R) s P)
    ((KQ).map (projective_minus_tail_to_single (R := R) s P))

/-- Helper for Lemma 15.80.2: conjugating the `Qh`-image of a strict cochain map along the
canonical comparison `quotientCompQhIso` recovers its `Q`-image. -/
lemma quotientCompQhIso_homCongr_map_local
    {K L : Cpx} (f : K ⟶ L) :
    (Iso.homCongr ((DerivedCategory.quotientCompQhIso (ModuleCat R)).app K)
      ((DerivedCategory.quotientCompQhIso (ModuleCat R)).app L))
      (DerivedCategory.Qh.map ((KQ).map f)) =
    DerivedCategory.Q.map f := by
  -- Proof comment: rewrite the `Iso.homCongr` expression as literal composition with the
  -- comparison isomorphism, then use naturality of `quotientCompQhIso`.
  change
    (DerivedCategory.quotientCompQhIso (ModuleCat R)).inv.app K ≫
        DerivedCategory.Qh.map ((KQ).map f) ≫
          (DerivedCategory.quotientCompQhIso (ModuleCat R)).hom.app L =
      DerivedCategory.Q.map f
  have hnat :
      DerivedCategory.Qh.map ((KQ).map f) ≫
          (DerivedCategory.quotientCompQhIso (ModuleCat R)).hom.app L =
        (DerivedCategory.quotientCompQhIso (ModuleCat R)).hom.app K ≫
          DerivedCategory.Q.map f := by
    simpa [Functor.comp_map] using
      ((DerivedCategory.quotientCompQhIso (ModuleCat R)).hom.naturality f).symm
  calc
    (DerivedCategory.quotientCompQhIso (ModuleCat R)).inv.app K ≫
        DerivedCategory.Qh.map ((KQ).map f) ≫
          (DerivedCategory.quotientCompQhIso (ModuleCat R)).hom.app L =
      (DerivedCategory.quotientCompQhIso (ModuleCat R)).inv.app K ≫
        ((DerivedCategory.quotientCompQhIso (ModuleCat R)).hom.app K ≫
          DerivedCategory.Q.map f) := by
            simpa [Category.assoc] using
              congrArg
                (fun k ↦ (DerivedCategory.quotientCompQhIso (ModuleCat R)).inv.app K ≫ k)
                hnat
    _ = DerivedCategory.Q.map f := by
      simpa [Category.assoc] using
        Iso.inv_hom_id_assoc
          ((DerivedCategory.quotientCompQhIso (ModuleCat R)).app K)
          (DerivedCategory.Q.map f)

/-- Helper for Lemma 15.80.2: transporting a homotopy-category postcomposition step through
`quotientCompQhIso` yields postcomposition by the corresponding derived morphism. -/
lemma quotientCompQhIso_homCongr_postcompose
    {K L M : Cpx}
    (x : DerivedCategory.Qh.obj ((KQ).obj K) ⟶ DerivedCategory.Qh.obj ((KQ).obj L))
    (f : L ⟶ M) :
    (Iso.homCongr ((DerivedCategory.quotientCompQhIso (ModuleCat R)).app K)
      ((DerivedCategory.quotientCompQhIso (ModuleCat R)).app M))
      (x ≫ DerivedCategory.Qh.map ((KQ).map f)) =
    (Iso.homCongr ((DerivedCategory.quotientCompQhIso (ModuleCat R)).app K)
      ((DerivedCategory.quotientCompQhIso (ModuleCat R)).app L))
      x ≫
        DerivedCategory.Q.map f := by
  -- Proof comment: peel apart `Iso.homCongr` and factor the right-hand tail through the
  -- transported strict map.
  calc
    (Iso.homCongr ((DerivedCategory.quotientCompQhIso (ModuleCat R)).app K)
      ((DerivedCategory.quotientCompQhIso (ModuleCat R)).app M))
      (x ≫ DerivedCategory.Qh.map ((KQ).map f)) =
      (DerivedCategory.quotientCompQhIso (ModuleCat R)).inv.app K ≫
        (x ≫ DerivedCategory.Qh.map ((KQ).map f)) ≫
          (DerivedCategory.quotientCompQhIso (ModuleCat R)).hom.app M := by
            rfl
    _ =
      ((DerivedCategory.quotientCompQhIso (ModuleCat R)).inv.app K ≫
          x ≫
            (DerivedCategory.quotientCompQhIso (ModuleCat R)).hom.app L) ≫
        ((DerivedCategory.quotientCompQhIso (ModuleCat R)).inv.app L ≫
          DerivedCategory.Qh.map ((KQ).map f) ≫
            (DerivedCategory.quotientCompQhIso (ModuleCat R)).hom.app M) := by
              simp [Category.assoc]
    _ =
      ((Iso.homCongr ((DerivedCategory.quotientCompQhIso (ModuleCat R)).app K)
          ((DerivedCategory.quotientCompQhIso (ModuleCat R)).app L)) x) ≫
        DerivedCategory.Q.map f := by
          simp [quotientCompQhIso_homCongr_map_local, Category.assoc]

/-- Helper for Lemma 15.80.2: the canonical comparison from the strict degree `-s` single complex
to the shifted degree-zero single object is natural in the module. -/
lemma projective_minus_tail_single_shift_iso_naturality
    (s : ℕ+) {C N : ModuleCat R} (φ : C ⟶ N) :
    DerivedCategory.Q.map
        ((CochainComplex.singleFunctor (ModuleCat R) (-((s : ℕ) : ℤ))).map φ) ≫
      (projective_minus_tail_single_shift_iso (R := R) s N).hom =
    (projective_minus_tail_single_shift_iso (R := R) s C).hom ≫
      ((ModuleCat.single0Functor : ModuleCat R ⥤ DMod).map φ)⟦(s : ℤ)⟧' := by
  let e₁ :
      ∀ X : ModuleCat R,
        DerivedCategory.Q.obj
            ((CochainComplex.singleFunctor (ModuleCat R) (-((s : ℕ) : ℤ))).obj X) ≅
          (DerivedCategory.singleFunctor (ModuleCat R) (-((s : ℕ) : ℤ))).obj X :=
    fun X ↦ (DerivedCategory.singleFunctorIsoCompQ (ModuleCat R) (-((s : ℕ) : ℤ))).app X
  let e₂ :
      ∀ X : ModuleCat R,
        (DerivedCategory.singleFunctor (ModuleCat R) (-((s : ℕ) : ℤ))).obj X ≅
          ((ModuleCat.single0Functor : ModuleCat R ⥤ DMod).obj X)⟦(s : ℤ)⟧ :=
    fun X ↦
      (((DerivedCategory.singleFunctors (ModuleCat R)).shiftIso
        (s : ℤ) (-((s : ℕ) : ℤ)) 0 (by omega)).app X).symm
  have h₁ :
      DerivedCategory.Q.map
          ((CochainComplex.singleFunctor (ModuleCat R) (-((s : ℕ) : ℤ))).map φ) ≫
        (e₁ N).hom =
      (e₁ C).hom ≫
        (DerivedCategory.singleFunctor (ModuleCat R) (-((s : ℕ) : ℤ))).map φ := by
    -- Proof comment: this is the naturality square of `singleFunctorIsoCompQ`.
    simpa [e₁, Functor.comp_map] using
      ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat R) (-((s : ℕ) : ℤ))).hom.naturality φ)
  have h₂ :
      (DerivedCategory.singleFunctor (ModuleCat R) (-((s : ℕ) : ℤ))).map φ ≫
        (e₂ N).hom =
      (e₂ C).hom ≫
        ((ModuleCat.single0Functor : ModuleCat R ⥤ DMod).map φ)⟦(s : ℤ)⟧' := by
    -- Proof comment: the `singleFunctors.shiftIso` comparison commutes with maps of modules.
    simpa [e₂, Functor.comp_map] using
      ((((DerivedCategory.singleFunctors (ModuleCat R)).shiftIso
        (s : ℤ) (-((s : ℕ) : ℤ)) 0 (by omega)).symm).hom.naturality φ)
  calc
    DerivedCategory.Q.map
        ((CochainComplex.singleFunctor (ModuleCat R) (-((s : ℕ) : ℤ))).map φ) ≫
      (projective_minus_tail_single_shift_iso (R := R) s N).hom =
      DerivedCategory.Q.map
          ((CochainComplex.singleFunctor (ModuleCat R) (-((s : ℕ) : ℤ))).map φ) ≫
        (e₁ N).hom ≫ (e₂ N).hom := by
          simp [projective_minus_tail_single_shift_iso, e₁, e₂, Category.assoc]
    _ =
      (e₁ C).hom ≫
        (DerivedCategory.singleFunctor (ModuleCat R) (-((s : ℕ) : ℤ))).map φ ≫
          (e₂ N).hom := by
            simpa [Category.assoc] using
              congrArg (fun k ↦ k ≫ (e₂ N).hom) h₁
    _ =
      (e₁ C).hom ≫
        (e₂ C).hom ≫
          ((ModuleCat.single0Functor : ModuleCat R ⥤ DMod).map φ)⟦(s : ℤ)⟧' := by
            simpa [Category.assoc] using
              congrArg (fun k ↦ (e₁ C).hom ≫ k) h₂
    _ =
      (projective_minus_tail_single_shift_iso (R := R) s C).hom ≫
        ((ModuleCat.single0Functor : ModuleCat R ⥤ DMod).map φ)⟦(s : ℤ)⟧' := by
          simp [projective_minus_tail_single_shift_iso, e₁, e₂, Category.assoc]

/-- Helper for Lemma 15.80.2: the additive equivalence from strict single-complex maps to shifted
derived morphisms is compatible with postcomposition by a module map. -/
lemma projective_minus_to_shifted_single_add_equiv_postcompose
    (s : ℕ+)
    (P : CochainComplex.ProjectiveMinus (ModuleCat R))
    {C N : ModuleCat R}
    (f : ((KQ).obj (P : Cpx)) ⟶
      ((KQ).obj
        ((CochainComplex.singleFunctor (ModuleCat R) (-((s : ℕ) : ℤ))).obj C)))
    (φ : C ⟶ N) :
    projective_minus_to_shifted_single_add_equiv (R := R) s P N
        (f ≫
          (KQ).map ((CochainComplex.singleFunctor (ModuleCat R) (-((s : ℕ) : ℤ))).map φ)) =
      projective_minus_to_shifted_single_add_equiv (R := R) s P C f ≫
        ((ModuleCat.single0Functor : ModuleCat R ⥤ DMod).map φ)⟦(s : ℤ)⟧' := by
  let ePC :
      (DerivedCategory.Qh.obj ((KQ).obj (P : Cpx)) ⟶
          DerivedCategory.Qh.obj
            ((KQ).obj
              ((CochainComplex.singleFunctor (ModuleCat R) (-((s : ℕ) : ℤ))).obj C))) ≃+
        (DerivedCategory.Q.obj (P : Cpx) ⟶
          DerivedCategory.Q.obj
            ((CochainComplex.singleFunctor (ModuleCat R) (-((s : ℕ) : ℤ))).obj C)) :=
    isoHomCongrAddEquiv
      ((DerivedCategory.quotientCompQhIso (ModuleCat R)).app (P : Cpx))
      ((DerivedCategory.quotientCompQhIso (ModuleCat R)).app
        ((CochainComplex.singleFunctor (ModuleCat R) (-((s : ℕ) : ℤ))).obj C))
  let ePN :
      (DerivedCategory.Qh.obj ((KQ).obj (P : Cpx)) ⟶
          DerivedCategory.Qh.obj
            ((KQ).obj
              ((CochainComplex.singleFunctor (ModuleCat R) (-((s : ℕ) : ℤ))).obj N))) ≃+
        (DerivedCategory.Q.obj (P : Cpx) ⟶
          DerivedCategory.Q.obj
            ((CochainComplex.singleFunctor (ModuleCat R) (-((s : ℕ) : ℤ))).obj N)) :=
    isoHomCongrAddEquiv
      ((DerivedCategory.quotientCompQhIso (ModuleCat R)).app (P : Cpx))
      ((DerivedCategory.quotientCompQhIso (ModuleCat R)).app
        ((CochainComplex.singleFunctor (ModuleCat R) (-((s : ℕ) : ℤ))).obj N))
  -- Proof comment: first transport postcomposition through `quotientCompQhIso`, then through the
  -- strict-single-to-shifted-single comparison.
  calc
    projective_minus_to_shifted_single_add_equiv (R := R) s P N
        (f ≫
          (KQ).map ((CochainComplex.singleFunctor (ModuleCat R) (-((s : ℕ) : ℤ))).map φ)) =
      (Iso.homCongr (Iso.refl (DerivedCategory.Q.obj (P : Cpx)))
          (projective_minus_tail_single_shift_iso (R := R) s N))
        (ePN
          (DerivedCategory.Qh.map
            (f ≫
              (KQ).map
                ((CochainComplex.singleFunctor (ModuleCat R) (-((s : ℕ) : ℤ))).map φ)))) := by
          rfl
    _ =
      (Iso.homCongr (Iso.refl (DerivedCategory.Q.obj (P : Cpx)))
          (projective_minus_tail_single_shift_iso (R := R) s N))
        (ePN (DerivedCategory.Qh.map f ≫
          DerivedCategory.Qh.map
            ((KQ).map
              ((CochainComplex.singleFunctor (ModuleCat R) (-((s : ℕ) : ℤ))).map φ)))) := by
                simp
    _ =
      (Iso.homCongr (Iso.refl (DerivedCategory.Q.obj (P : Cpx)))
          (projective_minus_tail_single_shift_iso (R := R) s N))
        (ePC (DerivedCategory.Qh.map f) ≫
          DerivedCategory.Q.map
            ((CochainComplex.singleFunctor (ModuleCat R) (-((s : ℕ) : ℤ))).map φ)) := by
              simpa [ePC, ePN] using
                quotientCompQhIso_homCongr_postcompose (R := R)
                  (x := DerivedCategory.Qh.map f)
                  ((CochainComplex.singleFunctor (ModuleCat R) (-((s : ℕ) : ℤ))).map φ)
    _ =
      (Iso.homCongr (Iso.refl (DerivedCategory.Q.obj (P : Cpx)))
          (projective_minus_tail_single_shift_iso (R := R) s C))
        (ePC (DerivedCategory.Qh.map f)) ≫
          ((ModuleCat.single0Functor : ModuleCat R ⥤ DMod).map φ)⟦(s : ℤ)⟧' := by
            simpa [Iso.homCongr, Category.assoc] using
              congrArg
                (fun k ↦ ePC (DerivedCategory.Qh.map f) ≫ k)
                (projective_minus_tail_single_shift_iso_naturality (R := R) s φ)
    _ =
      projective_minus_to_shifted_single_add_equiv (R := R) s P C f ≫
        ((ModuleCat.single0Functor : ModuleCat R ⥤ DMod).map φ)⟦(s : ℤ)⟧' := by
          rfl

/-- Helper for Lemma 15.80.2: every shifted derived morphism out of the approximation complex
factors through the transported tail map by postcomposition in the target module. -/
lemma projective_minus_tail_shifted_map_factorization
    (s : ℕ+)
    (P : CochainComplex.ProjectiveMinus (ModuleCat R))
    {N : ModuleCat R}
    (g : DerivedCategory.Q.obj (P : Cpx) ⟶
      ((ModuleCat.single0Functor : ModuleCat R ⥤ DMod).obj N)⟦(s : ℤ)⟧) :
    ∃ φ : projective_minus_tail_cokernel (R := R) s P ⟶ N,
      projective_minus_tail_shifted_map (R := R) s P ≫
          ((ModuleCat.single0Functor : ModuleCat R ⥤ DMod).map φ)⟦(s : ℤ)⟧' = g := by
  let e :=
    projective_minus_to_shifted_single_add_equiv (R := R) s P N
  obtain ⟨γ, hγ⟩ := (KQ).map_surjective (e.symm g)
  obtain ⟨φ, hφ⟩ :=
    projective_minus_tail_to_single_postcompose_surjective (R := R) s P γ
  refine ⟨φ, ?_⟩
  have heγ :
      e ((KQ).map γ) = g := by
    rw [hγ]
    exact e.apply_symm_apply g
  calc
    projective_minus_tail_shifted_map (R := R) s P ≫
        ((ModuleCat.single0Functor : ModuleCat R ⥤ DMod).map φ)⟦(s : ℤ)⟧' =
      e
        ((KQ).map (projective_minus_tail_to_single (R := R) s P) ≫
          (KQ).map
            ((CochainComplex.singleFunctor (ModuleCat R) (-((s : ℕ) : ℤ))).map φ)) := by
              symm
              simpa [projective_minus_tail_shifted_map] using
                projective_minus_to_shifted_single_add_equiv_postcompose
                  (R := R) s P
                  ((KQ).map (projective_minus_tail_to_single (R := R) s P)) φ
    _ = e ((KQ).map γ) := by
      simpa [Functor.map_comp] using congrArg (fun k ↦ e ((KQ).map k)) hφ
    _ = g := heγ

/-- Helper for Lemma 15.80.2: an approximation complex for a degree-zero module object has zero
cohomology in the negative window `[-s, -1]`. -/
lemma approximation_source_homology_isZero_neg_window
    (s : ℕ+)
    {P : CochainComplex.ProjectiveMinus (ModuleCat R)}
    {M : ModuleCat R}
    {α : DerivedCategory.Q.obj ((P : CochainComplex (ModuleCat R) ℤ)) ⟶
      ((ModuleCat.single0Functor : ModuleCat R ⥤ DMod).obj M)}
    (hαiso : ∀ i : ℤ, -((s : ℕ) : ℤ) < i → IsIso ((H i).map α))
    (hαepi : Epi ((H (-((s : ℕ) : ℤ))).map α)) :
    ∀ i : ℤ, -((s : ℕ) : ℤ) ≤ i → i ≤ -1 →
      IsZero ((H i).obj (DerivedCategory.Q.obj (P : Cpx))) := by
  intro i hi_low hi_high
  have htarget : IsZero ((H i).obj ((ModuleCat.single0Functor : ModuleCat R ⥤ DMod).obj M)) := by
    -- Proof comment: a degree-zero module object has no negative cohomology.
    exact DerivedCategory.isZero_of_isGE _ 0 i (by omega)
  by_cases his : i = -((s : ℕ) : ℤ)
  · subst his
    have hmor_zero : (H (-((s : ℕ) : ℤ))).map α = 0 := by
      -- Proof comment: the target cohomology object is zero at degree `-s`, so the comparison
      -- morphism to it is the zero map.
      exact htarget.eq_of_tgt _ _
    -- Proof comment: the approximation also makes this map epi, hence the source cohomology
    -- object itself must vanish.
    exact IsZero.of_epi_eq_zero ((H (-((s : ℕ) : ℤ))).map α) hmor_zero
  · have hαiso' : IsIso ((H i).map α) := by
      -- Proof comment: away from the bottom degree `-s`, the approximation is an isomorphism on
      -- cohomology in the entire negative window.
      exact hαiso i (by omega)
    -- Proof comment: transport the zero target cohomology back across the homology isomorphism.
    exact (asIso ((H i).map α)).isZero_iff.2 htarget

/-- Helper for Lemma 15.80.2: once the textbook `s`-ghost row has been constructed with the
correct source, target, and total composite, Lemma `15.80.1` kills the transported tail map. -/
lemma projective_minus_tail_shifted_map_eq_zero_of_exists_ghost_row
    (s : ℕ+)
    (P : CochainComplex.ProjectiveMinus (ModuleCat R))
    (hPstage : (⟨ringSingle⟩_s : ObjectProperty DMod) (DerivedCategory.Q.obj (P : Cpx)))
    (hrow :
      ∃ X : ComposableArrows DMod s,
        X.left = DerivedCategory.Q.obj (P : Cpx) ∧
        X.right =
          ((ModuleCat.single0Functor : ModuleCat R ⥤ DMod).obj
            (projective_minus_tail_cokernel (R := R) s P))⟦(s : ℤ)⟧ ∧
        (∀ j : ℕ, (hj : j < s) → ∀ i : ℤ, (H i).map (X.arrow j hj).hom = 0) ∧
        X.hom = projective_minus_tail_shifted_map (R := R) s P) :
    projective_minus_tail_shifted_map (R := R) s P = 0 := by
  rcases hrow with ⟨X, rfl, rfl, hghost, hhom⟩
  -- Proof comment: after identifying the row endpoints with the approximation source and the
  -- shifted tail target, the remaining vanishing is exactly Lemma `15.80.1`.
  rw [← hhom]
  exact ghost_composite_zero_of_mem_objectGeneratedStage (R := R) hPstage hghost

/-- Helper for Lemma 15.80.2: the textbook tail complexes built from the left-tail cokernel of
`P` yield an `s`-step ghost row in `D(R)` whose total composite is the transported tail map. -/
lemma projective_minus_tail_ghost_row_witness_of_homology_window
    (s : ℕ+)
    (P : CochainComplex.ProjectiveMinus (ModuleCat R))
    (hvanish : ∀ i : ℤ, -((s : ℕ) : ℤ) ≤ i → i ≤ -1 →
      IsZero ((H i).obj (DerivedCategory.Q.obj (P : Cpx)))) :
    ∃ X : ComposableArrows DMod s,
      X.left = DerivedCategory.Q.obj (P : Cpx) ∧
      X.right =
        ((ModuleCat.single0Functor : ModuleCat R ⥤ DMod).obj
          (projective_minus_tail_cokernel (R := R) s P))⟦(s : ℤ)⟧ ∧
      (∀ j : ℕ, (hj : j < s) → ∀ i : ℤ, (H i).map (X.arrow j hj).hom = 0) ∧
      X.hom = projective_minus_tail_shifted_map (R := R) s P := by
  -- TODO: package the strict textbook row
  -- `P → K₁ → ⋯ → K_s = single(projective_minus_tail_cokernel s P, -s)`, transport it once
  -- through `Q` and `projective_minus_tail_single_shift_iso`, use `hvanish` to show each step is
  -- ghost, and identify the transported composite with `projective_minus_tail_shifted_map`.
  sorry

/-- Helper for Lemma 15.80.2: the source-proof ghost row forces the transported tail morphism to
vanish once the approximation complex lies in the `s`-th stage generated by `R[0]` and has the
textbook vanishing window `H^{-s}(P)=\cdots=H^{-1}(P)=0`. -/
lemma projective_minus_tail_shifted_map_eq_zero_of_mem_objectGeneratedStage
    (s : ℕ+)
    (P : CochainComplex.ProjectiveMinus (ModuleCat R))
    (hPstage : (⟨ringSingle⟩_s : ObjectProperty DMod) (DerivedCategory.Q.obj (P : Cpx))) :
    (hvanish : ∀ i : ℤ, -((s : ℕ) : ℤ) ≤ i → i ≤ -1 →
      IsZero ((H i).obj (DerivedCategory.Q.obj (P : Cpx)))) →
    projective_minus_tail_shifted_map (R := R) s P = 0 := by
  intro hvanish
  -- Route correction: isolate the source-faithful row construction as a separate witness lemma,
  -- so the current theorem is only the formal application of Lemma `15.80.1`.
  have hrow :=
    projective_minus_tail_ghost_row_witness_of_homology_window (R := R) s P hvanish
  -- Proof comment: once the witness row is available, the vanishing is exactly the previously
  -- isolated formal endgame.
  exact
    projective_minus_tail_shifted_map_eq_zero_of_exists_ghost_row
      (R := R) s P hPstage hrow

/-- Helper for Lemma 15.80.2: once the approximation `α : Q(P) ⟶ M[0]` is chosen, the remaining
source-faithful task is to factor `α ≫ g` through the transported tail morphism and kill that
transported morphism by the textbook `s`-ghost row. -/
lemma shifted_single_hom_eq_zero_of_module_via_strong_generator_ghost_chain
    (s : ℕ+)
    (hstage : ∀ {K : DMod}, K.IsPerfect → (⟨ringSingle⟩_s : ObjectProperty DMod) K)
    (M N : ModuleCat R) [Module.Finite R M]
    (g : ((ModuleCat.single0Functor : ModuleCat R ⥤ DMod).obj M) ⟶
      ((ModuleCat.single0Functor : ModuleCat R ⥤ DMod).obj N)⟦(s : ℤ)⟧) :
    g = 0 := by
  rcases exists_projectiveMinus_finiteFree_approximation_of_isMPseudoCoherent
      (R := R)
      (((ModuleCat.single0Functor : ModuleCat R ⥤ DMod).obj M))
      (-((s : ℕ) : ℤ))
      (finite_single_isMPseudoCoherent_at_neg_generator_length (R := R) s M) with
    ⟨P, hPge, _hPfree, hPfinite, α, hαiso, hαepi⟩
  have hPperfect : (DerivedCategory.Q.obj (P : Cpx)).IsPerfect := by
    -- Proof comment: the approximation complex is bounded on both sides and termwise finite free,
    -- hence perfect in the derived category.
    exact
      projective_minus_q_obj_isPerfect_of_strictlyGE_finiteFree
        (R := R) P hPge hPfinite
  have hPstage : (⟨ringSingle⟩_s : ObjectProperty DMod) (DerivedCategory.Q.obj (P : Cpx)) := by
    -- Proof comment: transport the strong-generator stage bound to this perfect approximation.
    exact hstage hPperfect
  have hPwindow :
      ∀ i : ℤ, -((s : ℕ) : ℤ) ≤ i → i ≤ -1 →
        IsZero ((H i).obj (DerivedCategory.Q.obj (P : Cpx))) := by
    -- Proof comment: the approximation to `M[0]` has the exact negative-window vanishing used by
    -- the textbook ghost-chain argument.
    exact approximation_source_homology_isZero_neg_window (R := R) s hαiso hαepi
  have hαmono :=
    approximation_precompose_shifted_single_mono_at_top
      (R := R) s (α := α) hαiso hαepi N
  let ξ :=
    projective_minus_tail_shifted_map (R := R) s P
  obtain ⟨φ, hfactor⟩ :=
    projective_minus_tail_shifted_map_factorization (R := R) s P (α ≫ g)
  have hξzero : ξ = 0 := by
    -- Proof comment: the only remaining source-faithful input is the textbook ghost-chain
    -- comparison for the transported tail map.
    simpa [ξ] using
      projective_minus_tail_shifted_map_eq_zero_of_mem_objectGeneratedStage
        (R := R) s P hPstage hPwindow
  -- Route correction: the earlier blocked route tried to package the universal class directly in
  -- `Ext`. The source proof works better on the shifted-Hom surface `M[0] ⟶ N[0]⟦s⟧`, where the
  -- approximation injectivity and the textbook ghost chain interact directly.
  apply hαmono
  calc
    α ≫ g = ξ ≫ ((ModuleCat.single0Functor : ModuleCat R ⥤ DMod).map φ)⟦(s : ℤ)⟧' := by
      simpa [ξ] using hfactor.symm
    _ = 0 := by
      simp [hξzero]

/-- Helper for Lemma 15.80.2: once every perfect object lies in the `s`-th stage generated by
`R[0]`, every degree-`s` `Ext` class out of a finite module vanishes. -/
lemma ext_eq_zero_of_module_via_strong_generator_ghost_chain
    (s : ℕ+)
    (hstage : ∀ {K : DMod}, K.IsPerfect → (⟨ringSingle⟩_s : ObjectProperty DMod) K)
    (M N : ModuleCat R) [Module.Finite R M]
    (e : Ext M N (s : ℕ)) :
    e = 0 := by
  let g :
      ((ModuleCat.single0Functor : ModuleCat R ⥤ DMod).obj M) ⟶
        ((ModuleCat.single0Functor : ModuleCat R ⥤ DMod).obj N)⟦(s : ℤ)⟧ :=
    (CategoryTheory.Abelian.Ext.homEquiv
      (C := ModuleCat R) (X := M) (Y := N) (n := (s : ℕ))) e
  have hg : g = 0 := by
    -- Proof comment: the shifted-Hom vanishing lemma is the source-faithful core of the proof;
    -- `Ext` is only converted to and from that surface at the endpoints.
    exact
      shifted_single_hom_eq_zero_of_module_via_strong_generator_ghost_chain
        (R := R) s hstage M N g
  apply
    (CategoryTheory.Abelian.Ext.homEquiv
      (C := ModuleCat R) (X := M) (Y := N) (n := (s : ℕ))).injective
  simpa using hg

/-- Helper for Lemma 15.80.2: strong generation of `R[0]` in the perfect derived category forces
finite global dimension. -/
-- TODO: transport the stage witness from `DPerf R` to `D(R)` using
-- `mem_objectGeneratedStage_of_strong_generator_in_DPerf`, build the finite-free
-- projective-minus approximation of `M[0]`, kill maps into `N[0][s]` by Lemma `15.80.1`,
-- deduce `Ext^s_R(M,N)=0` for finite `M`, and convert that uniform vanishing to
-- `IsFiniteGlobalDimensionRing R` via Lemma `10.109.12`.
lemma isFiniteGlobalDimensionRing_of_ringSingleInPerfectDerived_isStrongGenerator
    (hstrong : IsStrongGenerator (ringSingleInPerfectDerived R)) :
    IsFiniteGlobalDimensionRing R := by
  rcases hstrong with ⟨s, hs⟩
  have hs_succ : s.natPred + 1 = (s : ℕ) := PNat.natPred_add_one s
  have hstage :
      ∀ {K : DMod}, K.IsPerfect → (⟨ringSingle⟩_s : ObjectProperty DMod) K := by
    intro K hK
    -- Transport the strong-generator stage bound from `D_{perf}(R)` to the ambient derived
    -- category.
    exact mem_objectGeneratedStage_of_strong_generator_in_DPerf (R := R) hs hK
  have hprojective :
      ∀ (M : ModuleCat R) [Module.Finite R M], HasProjectiveDimensionLE M s.natPred := by
    intro M hM
    -- Reduce the projective-dimension claim to vanishing of the degree-`s` `Ext` group.
    refine ((moduleCat_projectiveDimensionLE_ext_vanishing_tfae M s.natPred).out 0 2).mpr ?_
    intro N e
    -- Invoke the isolated ghost-chain vanishing step.
    exact ext_eq_zero_of_module_via_strong_generator_ghost_chain (R := R) s hstage M N e
  have hglobal : HasGlobalDimensionLE R s.natPred := by
    -- The Chapter 10 finite/cyclic criterion upgrades the finite-module projective-dimension
    -- bound to a uniform global-dimension bound.
    exact
      ((globalDimensionLE_tfae_finite_and_cyclic_modules (R := R) s.natPred).out 0 1).mpr
        hprojective
  exact ⟨⟨s.natPred, hglobal⟩⟩

/-
Domain-style sampling for Lemma 15.80.2:
- primary domain: strong generators in the perfect derived category of a Noetherian ring and the
  Chapter 10 owner API for regular rings of finite Krull dimension;
- sampled owner declarations:
  `IsStrongGenerator`,
  `ringSingleInPerfectDerived`,
  `IsRegularRing`,
  `finiteGlobalDimension_regularRing_localizations_tfae`;
- best owner abstraction: the ring-side owner inside the conclusion is `IsRegularRing R`, but the
  source-facing main theorem must keep the combined finite-dimensional regularity conclusion
  `∃ n : ℕ, IsRegularRing R ∧ ringKrullDim R = n`;
- primitive vs. derived: primitive data here is only the strong-generation hypothesis on `R[0]`
  in `D_{perf}(R)`; the source-facing combined existential conclusion is the full derived API; the
  regularity owner `IsRegularRing R` and the explicit dimension witness remain logically derived
  consequences rather than separate public declarations;
- source/core/bridge triage:
  `source-facing`: the implication from strong generation of `R[0]` to the existence of a finite
    Krull-dimension witness together with `IsRegularRing R`;
  `core/canonical`: `IsRegularRing R`;
  `bridge/view`: any downstream extraction of the explicit equality `ringKrullDim R = n` from the
    source-facing existential conclusion.
-/

-- Proof sketch: apply the strong-generation hypothesis to the canonical object `R[0]` in
-- `D_{perf}(R)` and use Lemma `15.80.1` to force vanishing of composites of sufficiently many
-- ghosts. Represent finite modules by bounded finite free complexes in `D_{perf}(R)` to deduce
-- vanishing of high `Ext`, hence finite global dimension by Lemma `10.109.12`, and then conclude
-- with Lemma `10.110.8` that `R` is regular of some finite Krull dimension.
/-- Lemma 15.80.2: if the canonical object `R[0]` is a strong generator of the perfect derived
category `D_{perf}(R)`, then `R` is a regular ring of finite Krull dimension. -/
@[stacks 0FXI]
theorem exists_regularRing_and_ringKrullDim_eq_of_ringSingleInPerfectDerived_isStrongGenerator
    (hstrong : IsStrongGenerator (ringSingleInPerfectDerived R)) :
    ∃ n : ℕ, IsRegularRing R ∧ ringKrullDim R = n := by
  -- Reduce the target to the Chapter 10 finite-global-dimension criterion.
  letI := isFiniteGlobalDimensionRing_of_ringSingleInPerfectDerived_isStrongGenerator
    (R := R) hstrong
  exact exists_regularRing_and_ringKrullDim_eq_of_finite_global_dimension (R := R)

end

end CategoryTheory
