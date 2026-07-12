import Mathlib
import StacksProject_2024.Chap17.«17_19_2_1»
import StacksProject_2024.Chap06.Definition_6_16_2
import StacksProject_2024.Chap06.Lemma_6_29_1
import StacksProject_2024.Chap07.Lemma_7_11_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty Opposite TopCat
open CategoryTheory.Limits.CoproductsFromFiniteFiltered
open TopologicalSpace
open TopologicalSpace.Opens
open scoped TopCat

noncomputable section

universe u

section

variable {X : TopCat.{u}}
variable [HasWeakSheafify (Opens.grothendieckTopology X) (Type u)]

attribute [local instance] CategoryTheory.Types.instConcreteCategory
attribute [local instance] CategoryTheory.Types.instFunLike

local instance (ι : Type u) : HasColimitsOfShape (Discrete ι) (TopCat.Sheaf (Type u) X) :=
  by
    let _ : HasColimitsOfShape (Discrete ι) (Type u) := by infer_instance
    change HasColimitsOfShape (Discrete ι)
      (CategoryTheory.Sheaf (Opens.grothendieckTopology X) (Type u))
    exact CategoryTheory.Sheaf.instHasColimitsOfShape

/-- Helper for Lemma 17.19.2: finite partial coproduct diagrams indexed by
`Finset (Discrete ι)` admit colimits in the sheaf category. This is the local infrastructure
needed for the source-faithful finite-subcoproduct presentation route. -/
local instance (ι : Type u) :
    HasColimitsOfShape (Finset (Discrete ι)) (TopCat.Sheaf (Type u) X) := by
  -- Here the ambient `Type` category already has these colimits, so we only need to transfer
  -- them across the sheaf construction.
  let _ : HasColimitsOfShape (Finset (Discrete ι)) (Type u) := by infer_instance
  change HasColimitsOfShape (Finset (Discrete ι))
    (CategoryTheory.Sheaf (Opens.grothendieckTopology X) (Type u))
  exact CategoryTheory.Sheaf.instHasColimitsOfShape

local instance : HasColimitsOfShape WalkingParallelPair (TopCat.Sheaf (Type u) X) :=
  by
    let _ : HasColimitsOfShape WalkingParallelPair (Type u) := by infer_instance
    change HasColimitsOfShape WalkingParallelPair
      (CategoryTheory.Sheaf (Opens.grothendieckTopology X) (Type u))
    exact CategoryTheory.Sheaf.instHasColimitsOfShape

/-- Helper for Lemma 17.19.2: the full coproduct of a sheaf family is the colimit of the
finite-subcoproduct diagram indexed by `Finset (Discrete ι)`. This supplies the source-faithful
target diagram used later to cut an infinite coproduct down to finite stages. -/
noncomputable def finite_subcoproducts_sheaf_cocone_isColimit
    {ι : Type u} (F : ι → Sh(X)) :
    IsColimit (finiteSubcoproductsCocone F) := by
  -- This is exactly Mathlib's finite-subcoproduct colimit construction, specialized to sheaves.
  exact isColimitFiniteSubproductsCocone F

/-- Helper for Lemma 17.19.2: the colimit of the finite-subcoproduct diagram is canonically the
full coproduct sheaf. -/
noncomputable def finite_subcoproducts_sheaf_colimit_iso
    {ι : Type u} (F : ι → Sh(X)) :
    ∐ F ≅ colimit (liftToFinsetObj (Discrete.functor F)) := by
  -- Compare the standard finite-subcoproduct colimit cocone with the ambient coproduct cocone.
  exact (finite_subcoproducts_sheaf_cocone_isColimit (X := X) F).coconePointUniqueUpToIso
    (colimit.isColimit (liftToFinsetObj (Discrete.functor F)))

/-- Helper for Lemma 17.19.2: the `hom` of the finite-subcoproduct colimit isomorphism sends the
explicit finite-stage coproduct inclusion to the corresponding colimit leg. -/
lemma finite_subcoproducts_sheaf_colimit_iso_hom_app
    {ι : Type u} (F : ι → Sh(X)) (s : Finset (Discrete ι)) :
    Limits.Sigma.desc (fun i : s ↦ Limits.Sigma.ι F i.1.as) ≫
        (finite_subcoproducts_sheaf_colimit_iso (X := X) F).hom =
      colimit.ι (liftToFinsetObj (Discrete.functor F)) s := by
  -- Proof comment: compare the two colimit cocones at the finite stage `s`, then normalize the
  -- cocone leg of `finiteSubcoproductsCocone`.
  rw [show Limits.Sigma.desc (fun i : s ↦ Limits.Sigma.ι F i.1.as) =
      (finiteSubcoproductsCocone F).ι.app s by
      rw [finiteSubcoproductsCocone_ι_app]]
  simpa [finite_subcoproducts_sheaf_colimit_iso] using
    (IsColimit.comp_coconePointUniqueUpToIso_hom
      (finite_subcoproducts_sheaf_cocone_isColimit (X := X) F)
      (colimit.isColimit (liftToFinsetObj (Discrete.functor F)))
      s)

/-- Helper for Lemma 17.19.2: once a finite-subcoproduct transition map on sections is identified
with the corresponding tagged-union inclusion, that inclusion is injective. -/
lemma sigma_inclusion_injective
    {ι : Type u} {s t : Finset (Discrete ι)} (hs : s ≤ t)
    (G : t → Type u) :
    Function.Injective
      (fun x : Sigma (fun y : s ↦ G ⟨y.1, hs y.2⟩) =>
        match x with
        | ⟨a, xa⟩ => ((⟨(⟨a.1, hs a.2⟩ : t), xa⟩) : Sigma G)) := by
  -- TODO: compare the two sigma witnesses by extracting equality of their tagged indices first,
  -- then transport along that equality to identify the dependent components.
  sorry

/-- Helper for Lemma 17.19.2: the transition maps in the finite-subcoproduct diagram are
monomorphisms. This is the source-faithful input needed to apply Lemma `6.29.1` to sections over
quasi-compact basis opens. -/
lemma finite_subcoproduct_transition_mono
    {ι : Type u} (F : ι → Sh(X))
    {s t : Finset (Discrete ι)} (h : s ⟶ t) :
    Mono ((liftToFinsetObj (Discrete.functor F)).map h) := by
  -- TODO: identify the section map with the tagged-sigma inclusion from
  -- `sigma_inclusion_injective`, then use `sheaf_mono_iff_app_injective`.
  sorry

/- Domain-style sampling for Lemma 17.19.2:
- primary domain: filtered-colimit presentations of set-valued sheaves by finite coequalizers of
  lower-shriek constant sheaves;
- sampled owner declarations:
  `CategoryTheory.ObjectProperty.ind`,
  `HasFiniteBasisLowerShriekConstantCoequalizerPresentation`,
  `j![U, S]`,
  `coequalizer`;
- best owner abstraction: the filtered-colimit statement should use the canonical owner
  `CategoryTheory.ObjectProperty.ind`, while the repeated stagewise finite coproduct/coequalizer
  data from Equation `17.19.2.1` should be factored through the source-facing predicate
  `HasFiniteBasisLowerShriekConstantCoequalizerPresentation`;
- primitive data: a filtered colimit presentation of `ℱ`;
- derived API: the `ObjectProperty.ind` packaging of that presentation by the Chapter 17 owner
  predicate.

Source/core/bridge triage:
- `source-facing`: the filtered-colimit presentation relative to the basis `B`;
- `core/canonical`: `CategoryTheory.ObjectProperty.ind` and the Chapter 17 finite-basis
  coequalizer-presentation owner;
- `bridge/view`: the compact-open bridge used by the later spectral-space consequences.
-/

/-- Helper for Lemma 17.19.2: every sheaf admits one possibly infinite coequalizer presentation
whose source and target are coproducts of lower-shriek constant sheaves on basis members with
finite fibres. -/
lemma exists_basis_open_extensionByZeroConstant_infinite_coequalizer_presentation
    (B : Set (Opens X)) (hB : Opens.IsBasis B) (ℱ : Sh(X)) :
    ∃ (A K : Type u) (U : A → Opens X) (V : K → Opens X)
      (S : A → Type u) (T : K → Type u),
      ∃ (left right :
        (∐ fun b : K ↦ j![V b, T b]) ⟶
          (∐ fun a : A ↦ j![U a, S a]))
        (_ : ℱ ≅ coequalizer left right),
          (∀ a, U a ∈ B) ∧
            (∀ b, V b ∈ B) ∧
              (∀ a, Finite (S a)) ∧
                ∀ b, Finite (T b) := by
  -- Start from the epimorphic basis-open coproduct presentation of Lemma `17.19.1`.
  obtain ⟨A, U, S, hU, hS, π, hπ⟩ :=
    exists_epi_from_coproduct_of_basis_extension_by_empty_constant_sheaves B hB ℱ
  -- Apply the same presentation theorem to the kernel pair of that epimorphism.
  obtain ⟨K, V, T, hV, hT, ψ, hψ⟩ :=
    exists_epi_from_coproduct_of_basis_extension_by_empty_constant_sheaves B hB (pullback π π)
  let left :
      (∐ fun b : K ↦ j![V b, T b]) ⟶
        (∐ fun a : A ↦ j![U a, S a]) :=
    ψ ≫ pullback.fst π π
  let right :
      (∐ fun b : K ↦ j![V b, T b]) ⟶
        (∐ fun a : A ↦ j![U a, S a]) :=
    ψ ≫ pullback.snd π π
  have hπeq : left ≫ π = right ≫ π := by
    -- The two composites agree because the pullback projections equalize `π`.
    dsimp [left, right]
    simp [Category.assoc, pullback.condition]
  have hloc : TopCat.Presheaf.IsLocallySurjective π.hom :=
    (TopCat.Sheaf.isLocallySurjective_iff_epi π).2 hπ
  have hkernel : IsColimit (Cofork.ofπ π pullback.condition) :=
    CategoryTheory.Sheaf.isColimitCoforkOfIsLocallySurjective π hloc
  have hcofork : IsColimit (Cofork.ofπ π hπeq) := by
    refine Cofork.IsColimit.ofExistsUnique ?_
    intro s
    have hsq : left ≫ s.π = right ≫ s.π := s.condition
    letI : Epi ψ := hψ
    have hpb : pullback.fst π π ≫ s.π = pullback.snd π π ≫ s.π := by
      apply (cancel_epi ψ).1
      simpa [left, right, Category.assoc] using hsq
    exact Cofork.IsColimit.existsUnique hkernel s.π hpb
  let e : ℱ ≅ coequalizer left right :=
    hcofork.coconePointUniqueUpToIso (colimit.isColimit (parallelPair left right))
  exact ⟨A, K, U, V, S, T, left, right, e, hU, hV, hS, hT⟩

/-- Helper for Lemma 17.19.2: unpacking `ObjectProperty.ind` for the Chapter 17 finite
basis-open coequalizer predicate is exactly the existence of an explicit filtered colimit
presentation whose stages satisfy that predicate. -/
lemma ind_hasFiniteBasisLowerShriekConstantCoequalizerPresentation_iff_universeFlexible
    (B : Set (Opens X)) (ℱ : Sh(X)) :
    ind (HasFiniteBasisLowerShriekConstantCoequalizerPresentation B) ℱ ↔
      ∃ (I : Type _) (_ : SmallCategory I) (_ : IsFiltered I)
        (pres : ColimitPresentation I ℱ),
          ∀ i, HasFiniteBasisLowerShriekConstantCoequalizerPresentation B (pres.diag.obj i) := by
  -- TODO: either supply the owner-level finitely presentable bridge needed for
  -- `ObjectProperty.ind_iff_exists`, or re-express this local smallness normalization in the exact
  -- universe form expected by `ObjectProperty.ind`.
  sorry

/-- Helper for Lemma 17.19.2: the file-local `Type u`-small version of the previous unpacking is
the normalization needed by the later finite-stage assembly. -/
lemma ind_hasFiniteBasisLowerShriekConstantCoequalizerPresentation_iff
    (B : Set (Opens X)) (ℱ : Sh(X)) :
    ind (HasFiniteBasisLowerShriekConstantCoequalizerPresentation B) ℱ ↔
      ∃ (I : Type _) (_ : SmallCategory I) (_ : IsFiltered I)
        (pres : ColimitPresentation I ℱ),
          ∀ i, HasFiniteBasisLowerShriekConstantCoequalizerPresentation B (pres.diag.obj i) := by
  -- TODO: deduce the file-local statement from the universe-flexible normalization once that owner
  -- unfolding has been repaired.
  sorry

/-- Helper for Lemma 17.19.2: on the top open, a morphism from the singleton constant sheaf is
determined by the image of the canonical singleton generator. -/
theorem top_section_to_singleton_constant_hom_left_inv
    {Y : TopCat.{u}}
    [HasWeakSheafify (Opens.grothendieckTopology Y) (Type u)]
    (ℱ : Sh(Y))
    (α :
      ((constantSheaf (Opens.grothendieckTopology Y) (Type u)).obj SingletonType) ⟶ ℱ) :
    top_section_to_singleton_constant_hom ℱ
        (α.hom.app (op (⊤ : Opens Y)) (singleton_constant_top_section Y)) = α := by
  let adj :=
    CategoryTheory.constantSheafAdj (Opens.grothendieckTopology Y) (Type u)
      (top_open_isTerminal Y)
  -- The constant-sheaf adjunction reduces the left inverse check to the unique point of the
  -- singleton type.
  apply (adj.homEquiv SingletonType ℱ).injective
  have hSymm :
      (adj.homEquiv SingletonType ℱ)
          (top_section_to_singleton_constant_hom ℱ
            (α.hom.app (op (⊤ : Opens Y)) (singleton_constant_top_section Y))) =
        (Equiv.funUnique SingletonType _).symm
          (α.hom.app (op (⊤ : Opens Y)) (singleton_constant_top_section Y)) := by
    exact Equiv.apply_symm_apply (adj.homEquiv SingletonType ℱ)
      ((Equiv.funUnique SingletonType _).symm
        (α.hom.app (op (⊤ : Opens Y)) (singleton_constant_top_section Y)))
  have hEval :
      (Equiv.funUnique SingletonType _).symm
          (α.hom.app (op (⊤ : Opens Y)) (singleton_constant_top_section Y)) =
        (adj.homEquiv SingletonType ℱ) α := by
    ext x
    have hx : x = default := Subsingleton.elim _ _
    subst hx
    have hunit := congrFun
      (adj.homEquiv_unit (X := SingletonType) (Y := ℱ) (f := α)) default
    simpa [singleton_constant_top_section] using hunit.symm
  exact hSymm.trans hEval

/-- Helper for Lemma 17.19.2: a morphism out of `j![U, SingletonType]` is determined by the image
of the canonical generator over `U`. -/
theorem section_to_lowerShriek_singleton_hom_left_inv
    (ℱ : Sh(X)) (U : Opens X) (α : j![U, SingletonType] ⟶ ℱ) :
    section_to_lowerShriek_singleton_hom ℱ U
        (α.hom.app (op U) (lowerShriek_singleton_generator_section (X := X) U)) = α := by
  let constSingleton :=
    (constantSheaf (Opens.grothendieckTopology (extensionByZeroOpenSubsetSpace U))
      (Type u)).obj SingletonType
  let adj := OpenSubsetExtensionByInitial.sheafExtensionByInitialAdjunction (C := Type u) U
  let W : (Opens (extensionByZeroOpenSubsetSpace U))ᵒᵖ :=
    op (⊤ : Opens (extensionByZeroOpenSubsetSpace U))
  let topGenerator :
      ((TopCat.Sheaf.pullback (Type u) (extensionByZeroOpenSubsetInclusion U)).obj
        (j![U, SingletonType])).presheaf.obj W :=
    (((OpenSubsetExtensionByInitial.sheafExtensionByInitialUnitIso U).hom.app
      constSingleton).hom.app W)
      (singleton_constant_top_section (extensionByZeroOpenSubsetSpace U))
  have htransport :
      ambient_section_to_pullback_top_section ℱ U
          (α.hom.app (op U) (lowerShriek_singleton_generator_section (X := X) U)) =
        ((adj.homEquiv constSingleton ℱ) α).hom.app W
          (singleton_constant_top_section (extensionByZeroOpenSubsetSpace U)) := by
    -- Route correction: compare pullback top-open sections first, then transport back to the
    -- ambient open `U`.
    have hEval :
        ((adj.homEquiv constSingleton ℱ) α).hom.app W
            (singleton_constant_top_section (extensionByZeroOpenSubsetSpace U)) =
          (((TopCat.Sheaf.pullback (Type u) (extensionByZeroOpenSubsetInclusion U)).map α).hom.app
            W) topGenerator := by
      have hunit := congrArg
        (fun κ ↦ κ.hom.app W (singleton_constant_top_section (extensionByZeroOpenSubsetSpace U)))
        (adj.homEquiv_unit (X := constSingleton) (Y := ℱ) (f := α))
      simpa [W, topGenerator, FunctorToTypes.map_comp_apply] using hunit
    have hAmbient :
        α.hom.app (op U) (lowerShriek_singleton_generator_section (X := X) U) =
          pullback_top_section_to_ambient_section ℱ U
            (((adj.homEquiv constSingleton ℱ) α).hom.app W
              (singleton_constant_top_section (extensionByZeroOpenSubsetSpace U))) := by
      calc
        α.hom.app (op U) (lowerShriek_singleton_generator_section (X := X) U) =
          pullback_top_section_to_ambient_section ℱ U
            ((((TopCat.Sheaf.pullback (Type u) (extensionByZeroOpenSubsetInclusion U)).map α).hom.app
              W) topGenerator) := by
          symm
          simpa [W, topGenerator, lowerShriek_singleton_generator_section] using
            (pullback_top_section_to_ambient_section_naturality
              (φ := α) U topGenerator)
        _ = pullback_top_section_to_ambient_section ℱ U
              (((adj.homEquiv constSingleton ℱ) α).hom.app W
                (singleton_constant_top_section (extensionByZeroOpenSubsetSpace U))) := by
          exact congrArg (pullback_top_section_to_ambient_section ℱ U) hEval.symm
    calc
      ambient_section_to_pullback_top_section ℱ U
          (α.hom.app (op U) (lowerShriek_singleton_generator_section (X := X) U)) =
        ambient_section_to_pullback_top_section ℱ U
          (pullback_top_section_to_ambient_section ℱ U
            (((adj.homEquiv constSingleton ℱ) α).hom.app W
              (singleton_constant_top_section (extensionByZeroOpenSubsetSpace U)))) := by
        rw [hAmbient]
      _ = ((adj.homEquiv constSingleton ℱ) α).hom.app W
            (singleton_constant_top_section (extensionByZeroOpenSubsetSpace U)) := by
        exact ambient_section_transport_roundtrip ℱ U _
  -- After transporting through `j_! ⊣ j^{-1}`, the result is the top-open left inverse above.
  apply (adj.homEquiv constSingleton ℱ).injective
  have hSymm :
      (adj.homEquiv constSingleton ℱ)
          (section_to_lowerShriek_singleton_hom ℱ U
            (α.hom.app (op U) (lowerShriek_singleton_generator_section (X := X) U))) =
        top_section_to_singleton_constant_hom
          ((TopCat.Sheaf.pullback (Type u) (extensionByZeroOpenSubsetInclusion U)).obj ℱ)
          (ambient_section_to_pullback_top_section ℱ U
            (α.hom.app (op U) (lowerShriek_singleton_generator_section (X := X) U))) := by
    exact Equiv.apply_symm_apply (adj.homEquiv constSingleton ℱ)
      (top_section_to_singleton_constant_hom
        ((TopCat.Sheaf.pullback (Type u) (extensionByZeroOpenSubsetInclusion U)).obj ℱ)
        (ambient_section_to_pullback_top_section ℱ U
          (α.hom.app (op U) (lowerShriek_singleton_generator_section (X := X) U))))
  have hEval :
      top_section_to_singleton_constant_hom
          ((TopCat.Sheaf.pullback (Type u) (extensionByZeroOpenSubsetInclusion U)).obj ℱ)
          (ambient_section_to_pullback_top_section ℱ U
            (α.hom.app (op U) (lowerShriek_singleton_generator_section (X := X) U))) =
        (adj.homEquiv constSingleton ℱ) α := by
    rw [htransport]
    exact top_section_to_singleton_constant_hom_left_inv
      ((TopCat.Sheaf.pullback (Type u) (extensionByZeroOpenSubsetInclusion U)).obj ℱ)
      ((adj.homEquiv constSingleton ℱ) α)
  exact hSymm.trans hEval

/-- Helper for Lemma 17.19.2: maps from `j![U, SingletonType]` are equivalent to sections over
`U`. -/
noncomputable def lowerShriek_singleton_hom_equiv_section
    (ℱ : Sh(X)) (U : Opens X) :
    (j![U, SingletonType] ⟶ ℱ) ≃ ℱ.presheaf.obj (op U) where
  toFun α := α.hom.app (op U) (lowerShriek_singleton_generator_section (X := X) U)
  invFun s := section_to_lowerShriek_singleton_hom ℱ U s
  left_inv α := section_to_lowerShriek_singleton_hom_left_inv ℱ U α
  right_inv s := section_to_lowerShriek_singleton_hom_generator ℱ U s

/-- Helper for Lemma 17.19.2: postcomposing a singleton lower-shriek map corresponds to applying
the target morphism to the distinguished section over `U`. -/
theorem section_to_lowerShriek_singleton_hom_comp
    {ℱ 𝒢 : Sh(X)} (φ : ℱ ⟶ 𝒢) (U : Opens X)
    (s : ℱ.presheaf.obj (op U)) :
    section_to_lowerShriek_singleton_hom ℱ U s ≫ φ =
      section_to_lowerShriek_singleton_hom 𝒢 U (φ.hom.app (op U) s) := by
  -- The singleton-source equivalence lets us compare the two morphisms by their generator image.
  apply (lowerShriek_singleton_hom_equiv_section (X := X) 𝒢 U).injective
  calc
    (section_to_lowerShriek_singleton_hom ℱ U s ≫ φ).hom.app (op U)
        (lowerShriek_singleton_generator_section (X := X) U) =
      φ.hom.app (op U)
        ((section_to_lowerShriek_singleton_hom ℱ U s).hom.app (op U)
          (lowerShriek_singleton_generator_section (X := X) U)) := by
      rfl
    _ = φ.hom.app (op U) s := by
      rw [section_to_lowerShriek_singleton_hom_generator]
    _ = (section_to_lowerShriek_singleton_hom 𝒢 U (φ.hom.app (op U) s)).hom.app (op U)
          (lowerShriek_singleton_generator_section (X := X) U) := by
      symm
      exact section_to_lowerShriek_singleton_hom_generator 𝒢 U (φ.hom.app (op U) s)

/-- Helper for Lemma 17.19.2: once the distinguished generator section factors through a subobject,
the entire singleton lower-shriek map factors through that subobject. -/
lemma factor_lowerShriek_singleton_map_through
    {𝒢₀ 𝒢 : Sh(X)} (ι : 𝒢₀ ⟶ 𝒢) (U : Opens X)
    (α : j![U, SingletonType] ⟶ 𝒢)
    (s₀ : 𝒢₀.presheaf.obj (op U))
    (hs₀ :
      ι.hom.app (op U) s₀ =
        α.hom.app (op U) (lowerShriek_singleton_generator_section (X := X) U)) :
    ∃ α₀ : j![U, SingletonType] ⟶ 𝒢₀, α₀ ≫ ι = α := by
  refine ⟨section_to_lowerShriek_singleton_hom 𝒢₀ U s₀, ?_⟩
  calc
    section_to_lowerShriek_singleton_hom 𝒢₀ U s₀ ≫ ι =
      section_to_lowerShriek_singleton_hom 𝒢 U (ι.hom.app (op U) s₀) := by
      exact section_to_lowerShriek_singleton_hom_comp ι U s₀
    _ = section_to_lowerShriek_singleton_hom 𝒢 U
          (α.hom.app (op U) (lowerShriek_singleton_generator_section (X := X) U)) := by
      rw [hs₀]
    _ = α := section_to_lowerShriek_singleton_hom_left_inv 𝒢 U α

/-- Helper for Lemma 17.19.2: on a quasi-compact basis open `V b`, every section of the full
target coproduct already comes from one finite target subcoproduct. -/
lemma compactBasisSectionFactorsThroughFiniteTargetSubcoproduct
    (B : Set (Opens X))
    (hqc : ∀ U, U ∈ B → IsCompact (U : Set X))
    {A K : Type u} {U : A → Opens X} {V : K → Opens X}
    {S : A → Type u}
    (hU : ∀ a, U a ∈ B) (hV : ∀ b, V b ∈ B)
    (b : K)
    (s : (∐ fun a : A ↦ j![U a, S a]).presheaf.obj (op (V b))) :
    ∃ t : Finset (Discrete A),
      ∃ s₀ :
        ((liftToFinsetObj (Discrete.functor (fun a : A ↦ j![U a, S a]))).obj t).presheaf.obj
          (op (V b)),
        ((finiteSubcoproductsCocone (fun a : A ↦ j![U a, S a])).ι.app t).hom.app
            (op (V b)) s₀ = s := by
  -- TODO: apply Lemma `6.29.1 (3)` to the finite-subcoproduct diagram using
  -- `finite_subcoproduct_transition_mono`, transport a compact-open section across the comparison
  -- isomorphism `finite_subcoproducts_sheaf_colimit_iso`, and then choose a stage representative
  -- in the resulting filtered colimit of section types.
  sorry

/-- Helper for Lemma 17.19.2: a morphism from the singleton lower-shriek sheaf on a compact basis
open factors through one finite target subcoproduct. -/
lemma lowerShriekSingletonMapFactorsThroughFiniteTargetSubcoproduct
    (B : Set (Opens X))
    (hqc : ∀ U, U ∈ B → IsCompact (U : Set X))
    {A K : Type u} {U : A → Opens X} {V : K → Opens X}
    {S : A → Type u}
    (hU : ∀ a, U a ∈ B) (hV : ∀ b, V b ∈ B)
    (b : K)
    (α : j![V b, SingletonType] ⟶ (∐ fun a : A ↦ j![U a, S a])) :
    ∃ t : Finset (Discrete A),
      ∃ α₀ :
        j![V b, SingletonType] ⟶
          (liftToFinsetObj (Discrete.functor (fun a : A ↦ j![U a, S a]))).obj t,
        α₀ ≫ ((finiteSubcoproductsCocone (fun a : A ↦ j![U a, S a])).ι.app t) = α := by
  obtain ⟨t, s₀, hs₀⟩ :=
    compactBasisSectionFactorsThroughFiniteTargetSubcoproduct
      (X := X) B hqc hU hV b
      (α.hom.app (op (V b))
        (lowerShriek_singleton_generator_section (X := X) (V b)))
  refine ⟨t, ?_⟩
  exact factor_lowerShriek_singleton_map_through
    (((finiteSubcoproductsCocone (fun a : A ↦ j![U a, S a])).ι.app t))
    (V b) α s₀ hs₀

/-- Helper for Lemma 17.19.2: a lower-shriek constant sheaf on a finite set is canonically the
coproduct of its singleton summands. -/
noncomputable def lowerShriekFiniteConstantIsoCoproductSingleton
    (U : Opens X) (T : Type u) [Finite T] :
    -- TODO: compare both sides by the universal property of coproducts, using the established
    -- equivalence between maps out of `j![U, SingletonType]` and sections over `U`.
    j![U, T] ≅ ∐ fun t : T ↦ j![U, SingletonType] := sorry

/-- Helper for Lemma 17.19.2: a map out of a finite-fibre lower-shriek summand factors through one
finite target subcoproduct after decomposing the source into singleton summands. -/
lemma finiteFiberLowerShriekMapFactorsThroughFiniteTargetSubcoproduct
    (B : Set (Opens X))
    (hqc : ∀ U, U ∈ B → IsCompact (U : Set X))
    {A K : Type u} {U : A → Opens X} {V : K → Opens X}
    {S : A → Type u} {T : K → Type u}
    (hU : ∀ a, U a ∈ B) (hV : ∀ b, V b ∈ B) (hT : ∀ b, Finite (T b))
    (b : K)
    (α : j![V b, T b] ⟶ (∐ fun a : A ↦ j![U a, S a])) :
    ∃ t : Finset (Discrete A),
      ∃ α₀ :
        j![V b, T b] ⟶
          (liftToFinsetObj (Discrete.functor (fun a : A ↦ j![U a, S a]))).obj t,
        -- TODO: decompose `j![V b, T b]` into singleton lower-shriek summands via
        -- `lowerShriekFiniteConstantIsoCoproductSingleton`, factor each singleton map through a
        -- finite target stage, and combine the finitely many supports.
        α₀ ≫ ((finiteSubcoproductsCocone (fun a : A ↦ j![U a, S a])).ι.app t) = α := sorry

/-- Helper for Lemma 17.19.2: both arrows contributed by one source summand of the infinite
parallel pair factor through a common finite target subcoproduct. -/
lemma sourceSummandParallelPairFactorsThroughCommonFiniteTargetSubcoproduct
    (B : Set (Opens X))
    (hqc : ∀ U, U ∈ B → IsCompact (U : Set X))
    {A K : Type u} {U : A → Opens X} {V : K → Opens X}
    {S : A → Type u} {T : K → Type u}
    (hU : ∀ a, U a ∈ B) (hV : ∀ b, V b ∈ B) (hT : ∀ b, Finite (T b))
    (left right :
      (∐ fun b : K ↦ j![V b, T b]) ⟶
        (∐ fun a : A ↦ j![U a, S a]))
    (b : K) :
    ∃ t : Finset (Discrete A),
      ∃ left₀ right₀ :
        j![V b, T b] ⟶
          (liftToFinsetObj (Discrete.functor (fun a : A ↦ j![U a, S a]))).obj t,
        left₀ ≫ ((finiteSubcoproductsCocone (fun a : A ↦ j![U a, S a])).ι.app t) =
            Limits.Sigma.ι (fun b : K ↦ j![V b, T b]) b ≫ left ∧
          right₀ ≫ ((finiteSubcoproductsCocone (fun a : A ↦ j![U a, S a])).ι.app t) =
            Limits.Sigma.ι (fun b : K ↦ j![V b, T b]) b ≫ right := by
  -- TODO: take the union of the two finite target supports obtained from the left and right
  -- branch factorizations and enlarge both maps to that common target stage.
  sorry

/-- Helper for Lemma 17.19.2: a chosen finite factorization of one source summand of the infinite
parallel pair can be enlarged along any bigger finite target support. -/
lemma sourceSummandParallelPairFactorsThroughTargetStage
    (B : Set (Opens X))
    (hqc : ∀ U, U ∈ B → IsCompact (U : Set X))
    {A K : Type u} {U : A → Opens X} {V : K → Opens X}
    {S : A → Type u} {T : K → Type u}
    (hU : ∀ a, U a ∈ B) (hV : ∀ b, V b ∈ B) (hT : ∀ b, Finite (T b))
    (left right :
      (∐ fun b : K ↦ j![V b, T b]) ⟶
        (∐ fun a : A ↦ j![U a, S a]))
    (b : K) (t : Finset (Discrete A))
    (ht : (Classical.choose
      (sourceSummandParallelPairFactorsThroughCommonFiniteTargetSubcoproduct
        (X := X) B hqc hU hV hT left right b)) ≤ t) :
    ∃ leftₜ rightₜ :
        j![V b, T b] ⟶
          (liftToFinsetObj (Discrete.functor (fun a : A ↦ j![U a, S a]))).obj t,
      leftₜ ≫ ((finiteSubcoproductsCocone (fun a : A ↦ j![U a, S a])).ι.app t) =
          Limits.Sigma.ι (fun b : K ↦ j![V b, T b]) b ≫ left ∧
        rightₜ ≫ ((finiteSubcoproductsCocone (fun a : A ↦ j![U a, S a])).ι.app t) =
          Limits.Sigma.ι (fun b : K ↦ j![V b, T b]) b ≫ right := by
  -- TODO: whisker the chosen common-support factorization along the transition map into `t`.
  sorry

/-- Helper for Lemma 17.19.2: support-closed finite source/target pairs for a support selector. -/
abbrev supportPairIndex
    {K A : Type u} (supp : Finset (Discrete K) → Finset (Discrete A)) :=
  { p : Finset (Discrete K) × Finset (Discrete A) // supp p.1 ≤ p.2 }

/-- Helper for Lemma 17.19.2: if a finite-support target selector sends unions into unions, then
support-closed finite source/target pairs form a filtered thin category. -/
lemma isFiltered_supportPairStages
    {K A : Type u} [DecidableEq (Discrete K)] [DecidableEq (Discrete A)]
    (supp : Finset (Discrete K) → Finset (Discrete A))
    (hsupp_union :
      ∀ s₁ s₂ : Finset (Discrete K), supp (s₁ ∪ s₂) ≤ supp s₁ ∪ supp s₂) :
    IsFiltered (supportPairIndex supp) := by
  -- Proof comment: this index category is a preorder, so filteredness reduces to building one
  -- object and common upper bounds for pairs of objects.
  letI : Nonempty (supportPairIndex supp) := ⟨⟨(∅, supp ∅), le_rfl⟩⟩
  letI : IsDirectedOrder (supportPairIndex supp) :=
    IsDirected.mk (fun X Y ↦
      ⟨⟨(X.1.1 ∪ Y.1.1, X.1.2 ∪ Y.1.2),
          le_trans (hsupp_union _ _) (sup_le_sup X.2 Y.2)⟩,
        ⟨le_sup_left, le_sup_left⟩,
        ⟨le_sup_right, le_sup_right⟩⟩)
  infer_instance

/-- Helper for Lemma 17.19.2: the finite-union support selector built from component supports
vanishes on the empty finite source support. -/
lemma supportOfComponents_empty
    {K A : Type u} [DecidableEq (Discrete K)] [DecidableEq (Discrete A)]
    (componentSupport : K → Finset (Discrete A)) :
    (∅ : Finset (Discrete K)).biUnion (fun b ↦ componentSupport b.as) = ∅ := by
  -- Proof comment: the empty source support contributes no target indices to the biunion.
  simp

/-- Helper for Lemma 17.19.2: the finite-union support selector built from component supports is
monotone in the finite source support. -/
lemma supportOfComponents_mono
    {K A : Type u} [DecidableEq (Discrete K)] [DecidableEq (Discrete A)]
    (componentSupport : K → Finset (Discrete A)) :
    Monotone (fun s : Finset (Discrete K) ↦ s.biUnion (fun b ↦ componentSupport b.as)) := by
  -- Proof comment: move the witnessing source component across the source-support inclusion.
  intro s t hst a ha
  rcases Finset.mem_biUnion.mp ha with ⟨b, hb, hba⟩
  exact Finset.mem_biUnion.mpr ⟨b, hst hb, hba⟩

/-- Helper for Lemma 17.19.2: the finite-union support selector sends unions of source supports
into unions of target supports. -/
lemma supportOfComponents_union_le
    {K A : Type u} [DecidableEq (Discrete K)] [DecidableEq (Discrete A)]
    (componentSupport : K → Finset (Discrete A))
    (s₁ s₂ : Finset (Discrete K)) :
    (s₁ ∪ s₂).biUnion (fun b ↦ componentSupport b.as) ≤
      s₁.biUnion (fun b ↦ componentSupport b.as) ∪
        s₂.biUnion (fun b ↦ componentSupport b.as) := by
  -- Proof comment: split the witness for membership in the biunion according to the left or
  -- right half of the source-support union.
  intro a ha
  rcases Finset.mem_biUnion.mp ha with ⟨b, hb, hba⟩
  rcases Finset.mem_union.mp hb with hb | hb
  · exact Finset.mem_union.mpr <| Or.inl <| Finset.mem_biUnion.mpr ⟨b, hb, hba⟩
  · exact Finset.mem_union.mpr <| Or.inr <| Finset.mem_biUnion.mpr ⟨b, hb, hba⟩

/-- Helper for Lemma 17.19.2: if a source component belongs to a finite source support, then its
chosen finite target support is contained in the associated biunion support. -/
lemma componentSupport_le_supportOf_mem
    {K A : Type u} [DecidableEq (Discrete K)] [DecidableEq (Discrete A)]
    (componentSupport : K → Finset (Discrete A))
    {b : K} {s : Finset (Discrete K)} (hb : (Discrete.mk b) ∈ s) :
    componentSupport b ≤ s.biUnion (fun c ↦ componentSupport c.as) := by
  -- Proof comment: every target index in the chosen support of `b` appears in the biunion via
  -- the witness that `b` itself lies in the finite source support.
  intro a ha
  exact Finset.mem_biUnion.mpr ⟨Discrete.mk b, hb, ha⟩

/-- Helper for Lemma 17.19.2: the first projection from support-closed finite source/target pairs
to the underlying finite source support. -/
def supportPairSourceProjection
    {K A : Type u} (supp : Finset (Discrete K) → Finset (Discrete A)) :
    supportPairIndex supp ⥤ Finset (Discrete K) where
  obj p := p.1.1
  map {p q} f := homOfLE (show p.1.1 ≤ q.1.1 from (leOfHom f).1)
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- Helper for Lemma 17.19.2: the second projection from support-closed finite source/target
pairs to the underlying finite target support. -/
def supportPairTargetProjection
    {K A : Type u} (supp : Finset (Discrete K) → Finset (Discrete A)) :
    supportPairIndex supp ⥤ Finset (Discrete A) where
  obj p := p.1.2
  map {p q} f := homOfLE (show p.1.2 ≤ q.1.2 from (leOfHom f).2)
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- Helper for Lemma 17.19.2: the source projection from support-closed pairs is final because it
is right adjoint to the canonical graph embedding `s ↦ (s, supp s)`. -/
lemma supportPairSourceProjection_final
    {K A : Type u} (supp : Finset (Discrete K) → Finset (Discrete A))
    (hsupp_mono : Monotone supp) :
    Functor.Final (supportPairSourceProjection supp) := by
  -- TODO: rebuild the graph-embedding adjunction with explicit pair-order witnesses, then apply
  -- `Functor.final_of_adjunction` as in the Chapter 18 support-pair source projection.
  sorry

/-- Helper for Lemma 17.19.2: the target projection from support-closed pairs is final because it
is right adjoint to the constant-empty-source embedding `t ↦ (∅, t)`. -/
lemma supportPairTargetProjection_final
    {K A : Type u} (supp : Finset (Discrete K) → Finset (Discrete A))
    (hsupp_empty : supp ∅ = ∅) :
    Functor.Final (supportPairTargetProjection supp) := by
  -- TODO: rebuild the empty-source adjunction with explicit pair-order witnesses and conclude
  -- finality from `Functor.final_of_adjunction`, mirroring the Chapter 18 target projection proof.
  sorry

/-- Helper for Lemma 17.19.2: a support-closed finite stage already has a finite basis-open
lower-shriek constant coequalizer presentation once its two finite arrows are fixed. -/
private theorem hasFiniteBasisLowerShriekConstantCoequalizerPresentation_of_supportPairStage
    {ℱ₀ : Sh(X)} {A K : Type u}
    (U : A → Opens X) (V : K → Opens X)
    (S : A → Type u) (T : K → Type u)
    (hU : ∀ a, U a ∈ B) (hV : ∀ b, V b ∈ B)
    (hS : ∀ a, Finite (S a)) (hT : ∀ b, Finite (T b))
    {supp : Finset (Discrete K) → Finset (Discrete A)}
    (p : supportPairIndex supp)
    (left right :
      (∐ fun b : p.1.1 ↦ j![V b.1.as, T b.1.as]) ⟶
        (∐ fun a : p.1.2 ↦ j![U a.1.as, S a.1.as]))
    (e : ℱ₀ ≅ coequalizer left right) :
    HasFiniteBasisLowerShriekConstantCoequalizerPresentation B ℱ₀ := by
  -- Proof comment: reindex the stage along the finite subtype carriers supplied by the two
  -- supports; these carriers are finite because they are finite subsets.
  exact
    ⟨p.1.2, p.1.1, inferInstance, inferInstance,
      (fun a : p.1.2 ↦ U a.1.as), (fun b : p.1.1 ↦ V b.1.as),
      (fun a : p.1.2 ↦ S a.1.as), (fun b : p.1.1 ↦ T b.1.as),
      left, right, e,
      (fun a ↦ hU a.1.as), (fun b ↦ hV b.1.as),
      (fun a ↦ hS a.1.as), (fun b ↦ hT b.1.as)⟩

/-- Helper for Lemma 17.19.2: once the source and target indexing sets are finite, the displayed
basis-open coequalizer presentation is already one stage of the desired `ObjectProperty.ind`
witness. -/
lemma ind_of_finite_basis_open_extensionByZeroConstant_coequalizer_presentation
    (B : Set (Opens X)) (ℱ : Sh(X))
    {A K : Type u} [Finite A] [Finite K] {U : A → Opens X} {V : K → Opens X}
    {S : A → Type u} {T : K → Type u}
    (left right :
      (∐ fun b : K ↦ j![V b, T b]) ⟶
        (∐ fun a : A ↦ j![U a, S a]))
    (e : ℱ ≅ coequalizer left right)
    (hU : ∀ a, U a ∈ B) (hV : ∀ b, V b ∈ B)
    (hS : ∀ a, Finite (S a)) (hT : ∀ b, Finite (T b)) :
    ind (HasFiniteBasisLowerShriekConstantCoequalizerPresentation B) ℱ := by
  -- Once both index types are finite, the given coequalizer presentation itself is a valid stage,
  -- so the canonical inclusion `P ≤ ind P` closes the goal.
  exact CategoryTheory.ObjectProperty.le_ind _ _ <|
    ⟨A, K, ‹Finite A›, ‹Finite K›, U, V, S, T, left, right, e, hU, hV, hS, hT⟩

/-- Helper for Lemma 17.19.2: after fixing one infinite basis-open coequalizer presentation of
`ℱ`, quasi-compactness of the basis opens should restrict it to finite subdiagrams and hence build
the required filtered-colimit witness. -/
lemma ind_of_basis_open_extensionByZeroConstant_infinite_coequalizer_presentation
    (B : Set (Opens X))
    (hqc : ∀ U, U ∈ B → IsCompact (U : Set X))
    (ℱ : Sh(X))
    {A K : Type u} {U : A → Opens X} {V : K → Opens X}
    {S : A → Type u} {T : K → Type u}
    (left right :
      (∐ fun b : K ↦ j![V b, T b]) ⟶
        (∐ fun a : A ↦ j![U a, S a]))
    (e : ℱ ≅ coequalizer left right)
    (hU : ∀ a, U a ∈ B) (hV : ∀ b, V b ∈ B)
    (hS : ∀ a, Finite (S a)) (hT : ∀ b, Finite (T b)) :
    ind (HasFiniteBasisLowerShriekConstantCoequalizerPresentation B) ℱ := by
  -- TODO: port the Chapter 18 support-pair filtered-colimit assembly after the finite-support
  -- source factorization and finality helpers are stabilized for this sheaf setting.
  sorry

-- Proof sketch: start from the epimorphic coproduct presentation of Lemma `17.19.1`, apply the
-- same construction to the kernel pair, and then restrict to finite subdiagrams. Quasi-compactness
-- of the basis opens and Lemma `6.29.1` let sections over the relevant opens commute with the
-- filtered colimit, so the resulting finite coequalizer stages indexed by finite subsets form a
-- filtered colimit presentation of `ℱ`.
/-- Lemma 17.19.2: if `X` has a basis `B` of quasi-compact opens, then every sheaf of sets on `X`
is a filtered colimit of sheaves admitting finite coequalizer presentations by lower-shriek
constant sheaves on members of `B` with finite fibres. We state this in the canonical owner form
`ObjectProperty.ind`, using the source-facing Chapter 17 predicate
`HasFiniteBasisLowerShriekConstantCoequalizerPresentation` for the stagewise condition. -/
@[stacks 0CAI]
theorem exists_filteredColimitPresentation_by_finite_basis_open_extensionByZeroConstantSheaf_coequalizers
    (B : Set (Opens X)) (hB : Opens.IsBasis B)
    (hqc : ∀ U, U ∈ B → IsCompact (U : Set X))
    (ℱ : Sh(X)) :
    ind (HasFiniteBasisLowerShriekConstantCoequalizerPresentation B) ℱ := by
  -- First build the source-proof infinite coequalizer presentation of `ℱ`.
  rcases
      exists_basis_open_extensionByZeroConstant_infinite_coequalizer_presentation
        (X := X) B hB ℱ with
    ⟨A, K, U, V, S, T, left, right, e, hU, hV, hS, hT⟩
  -- Then pass from the infinite presentation to the filtered system of finite restrictions.
  exact
    ind_of_basis_open_extensionByZeroConstant_infinite_coequalizer_presentation
      (X := X) B hqc ℱ left right e hU hV hS hT

end
