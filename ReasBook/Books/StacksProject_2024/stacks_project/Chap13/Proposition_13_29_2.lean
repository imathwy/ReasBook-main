import Mathlib
import StacksProject_2024.stacks_project.Chap12.Definition_12_5_3
import StacksProject_2024.stacks_project.Chap13.Lemma_13_11_2
import StacksProject_2024.stacks_project.Chap13.Lemma_13_15_2
import StacksProject_2024.stacks_project.Chap13.Lemma_13_15_4
import StacksProject_2024.stacks_project.Chap13.Lemma_13_29_1
import StacksProject_2024.stacks_project.Chap13.Situation_13_15_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open ComplexShape

noncomputable section

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory

section

variable {𝒜 : Type u₁} {ℬ : Type u₂}
  [Category.{v₁} 𝒜] [Category.{v₂} ℬ]
  [Abelian 𝒜] [Abelian ℬ] [HasDerivedCategory.{w} ℬ]

variable (F : 𝒜 ⥤ ℬ) [PreservesFiniteColimits F]

local instance : PreservesBinaryBiproducts F :=
  preservesBinaryBiproducts_of_preservesBinaryCoproducts F

local instance : F.Additive := Functor.additive_of_preservesBinaryBiproducts F

variable (P : ObjectProperty 𝒜)
  [P.ContainsZero] [P.IsClosedUnderFiniteCoproducts] [HasEpiCover P]
  [HasColimitsOfShape ℕ 𝒜] [HasColimitsOfShape ℕ ℬ]
  [HasExactColimitsOfShape ℕ 𝒜] [HasExactColimitsOfShape ℕ ℬ]
  [PreservesColimitsOfShape ℕ F]

local notation "Qis" => HomotopyCategory.quasiIso 𝒜 (up ℤ)
local notation "QisMinus" => boundedAboveHomotopyQuasiIso 𝒜
local notation "KtoD" => mapHomotopyCategoryToDerived F
local notation "KminusToDminus" => mapBoundedAboveHomotopyCategoryToDerivedAbove F

/- Domain-style sampling for Proposition 13.29.2:
- primary domain: unbounded left derived functors of additive functors, built from bounded-above
  acyclic resolutions and exact sequential colimits;
- sampled owner declarations:
  `Functor.HasPointwiseLeftDerivedFunctor`,
  `Functor.hasLeftDerivedFunctor_of_hasPointwiseLeftDerivedFunctor`,
  `UpperTruncationResolutionTower`,
  `Functor.hasPointwiseLeftDerivedFunctor_of_subset`;
- best owner abstraction: the canonical owner is
  `Functor.HasPointwiseLeftDerivedFunctor KtoD Qis`; the total left derived functor is then the
  standard bridge/view consequence;
- primitive-vs-derived split:
  primitive data: `P`, the bounded-above acyclicity hypothesis `hFacyclic`, and the exact
    sequential-colimit assumptions on `𝒜`, `ℬ`, and `F`;
  derived API: pointwise left-derived existence for `KtoD`, and then the total left derived
    functor by the canonical instance.

Source/core/bridge triage:
- `source-facing`: the proposition that `LF` is defined on all of `D(\mathcal A)`;
- `core/canonical`: `Functor.HasPointwiseLeftDerivedFunctor KtoD Qis`;
- `bridge/view`: the corollary upgrading the pointwise owner to
  `Functor.HasLeftDerivedFunctor KtoD Qis`.
-/

-- Proof sketch: use Lemma `13.15.4` to resolve each bounded-above truncation by a bounded-above
-- complex of objects in `P`, and Lemma `13.29.1` to assemble these into a sequential system whose
-- colimit is quasi-isomorphic to the original complex. The hypothesis `hFacyclic` shows that the
-- bounded-above stages compute the bounded-above left derived functor, while exact sequential
-- colimits in `𝒜` and `ℬ` and preservation of those colimits by `F` upgrade this computation from
-- bounded-above complexes to arbitrary complexes. Then apply the pointwise-to-total criterion for
-- left derived functors.
/-- Helper for Proposition 13.29.2: bounded-above homotopy objects whose terms all lie in `P`. -/
private abbrev termwiseObjectProperty
    (P : ObjectProperty 𝒜) : ObjectProperty (K⁻(𝒜)) :=
  fun X ↦
    let K : CochainComplex 𝒜 ℤ := X.obj.as
    ∀ i : ℤ, P (K.X i)

/-- Helper for Proposition 13.29.2: the mapping cone of a morphism between bounded-above
cochain complexes is again bounded above. -/
private lemma mappingCone_boundedAbove
    {K L : CochainComplex 𝒜 ℤ} (f : K ⟶ L)
    (hK : CochainComplex.minus 𝒜 K) (hL : CochainComplex.minus 𝒜 L) :
    CochainComplex.minus 𝒜 (mappingCone f) := by
  obtain ⟨nK, hnK⟩ := (CochainComplex.minus_iff 𝒜 K).1 hK
  obtain ⟨nL, hnL⟩ := (CochainComplex.minus_iff 𝒜 L).1 hL
  refine (CochainComplex.minus_iff 𝒜 (mappingCone f)).2 ⟨max nK nL, ?_⟩
  rw [isStrictlyLE_iff]
  intro i hi
  letI := hnK
  letI := hnL
  rw [mappingCone.isZero_X_iff]
  refine ⟨?_, ?_⟩
  · exact K.isZero_of_isStrictlyLE nK (i + 1) (lt_of_le_of_lt (le_max_left _ _) hi)
  · exact L.isZero_of_isStrictlyLE nL i (lt_of_le_of_lt (le_max_right _ _) hi)

/-- Helper for Proposition 13.29.2: an acyclic mapping cone yields a quasi-isomorphism. -/
private theorem quasiIso_of_mappingCone_acyclic
    {K L : CochainComplex 𝒜 ℤ} (f : K ⟶ L) (hCone : (mappingCone f).Acyclic) :
    QuasiIso f := by
  have hmem :
      HomotopyCategory.subcategoryAcyclic 𝒜
        ((HomotopyCategory.quotient 𝒜 (up ℤ)).obj (mappingCone f)) :=
    (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic
      (C := 𝒜) (mappingCone f)).2 hCone
  have hq :
      HomotopyCategory.quasiIso 𝒜 (up ℤ)
        ((HomotopyCategory.quotient 𝒜 (up ℤ)).map f) := by
    -- Proof comment: in the standard mapping-cone triangle, the acyclic cone is exactly the
    -- `trW` witness characterizing quasi-isomorphisms in the homotopy category.
    simpa [HomotopyCategory.quasiIso_eq_subcategoryAcyclic_W (C := 𝒜)] using
      ((HomotopyCategory.subcategoryAcyclic 𝒜).trW_iff_of_distinguished
        (CochainComplex.mappingCone.triangleh f)
        (HomotopyCategory.mappingCone_triangleh_distinguished f)).2 hmem
  exact (HomotopyCategory.quotient_map_mem_quasiIso_iff (C := 𝒜) (c := up ℤ) f).1 hq

/-- Helper for Proposition 13.29.2: a quasi-isomorphism has acyclic mapping cone. -/
private theorem mappingCone_acyclic_of_quasiIso
    {K L : CochainComplex 𝒜 ℤ} (f : K ⟶ L) (hf : QuasiIso f) :
    (mappingCone f).Acyclic := by
  have hq :
      HomotopyCategory.quasiIso 𝒜 (up ℤ)
        ((HomotopyCategory.quotient 𝒜 (up ℤ)).map f) := by
    rw [HomotopyCategory.quotient_map_mem_quasiIso_iff]
    exact hf
  have hmem :
      HomotopyCategory.subcategoryAcyclic 𝒜
        ((HomotopyCategory.quotient 𝒜 (up ℤ)).obj (mappingCone f)) := by
    -- Proof comment: in the standard mapping-cone triangle, membership in `trW` is equivalent to
    -- the cone object lying in the acyclic subcategory.
    exact
      ((HomotopyCategory.subcategoryAcyclic 𝒜).trW_iff_of_distinguished
        (CochainComplex.mappingCone.triangleh f)
        (HomotopyCategory.mappingCone_triangleh_distinguished f)).1
        (by simpa [HomotopyCategory.quasiIso_eq_subcategoryAcyclic_W (C := 𝒜)] using hq)
  exact
    (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic
      (C := 𝒜) (mappingCone f)).1 hmem

/-- Helper for Proposition 13.29.2: the cone of a morphism between termwise-`P` complexes is
again termwise in `P`. -/
private theorem mappingCone_termwiseObjectProperty
    {K L : CochainComplex 𝒜 ℤ} (f : K ⟶ L)
    (hK : ∀ i : ℤ, P (K.X i))
    (hL : ∀ i : ℤ, P (L.X i)) :
    ∀ i : ℤ, P ((mappingCone f).X i) := by
  intro i
  -- Proof comment: each cone term is canonically the biproduct of `K^{i + 1}` and `L^i`.
  let _ : ∀ p : ℤ, Limits.HasBinaryBiproduct (K.X (p + 1)) (L.X p) := fun p ↦ inferInstance
  let _ : HomologicalComplex.HasHomotopyCofiber f :=
    mappingCone_hasHomotopyCofiber (f := f)
  let e : (mappingCone f).X i ≅ K.X (i + 1) ⊞ L.X i :=
    HomologicalComplex.homotopyCofiber.XIsoBiprod f i (i + 1)
      (ComplexShape.up_mk i (i + 1) rfl)
  exact P.prop_of_iso e (P.prop_biprod (hK (i + 1)) (hL i))

/-- Helper for Proposition 13.29.2: the canonical bounded-above localization
`K^-(\mathcal B) ⟶ D^-(\mathcal B)` inverts bounded-above quasi-isomorphisms. -/
private theorem mapBoundedAboveHomotopyToDerivedAbove_map_isIso
    {X Y : K⁻(ℬ)} (f : X ⟶ Y) (hf : boundedAboveHomotopyQuasiIso ℬ f) :
    IsIso (mapBoundedAboveHomotopyToDerivedAbove.map f) := by
  let ιminus : D⁻(ℬ) ⥤ D(ℬ) := ObjectProperty.ι (DerivedCategory.TStructure.t.minus)
  have hUnderlying :
      IsIso (((HomotopyCategory.minus ℬ).ι ⋙ DerivedCategory.Qh).map f) := by
    -- Proof comment: after forgetting to the ambient homotopy category, this is the ordinary
    -- derived localization, which inverts quasi-isomorphisms by definition.
    change IsIso (DerivedCategory.Qh.map ((HomotopyCategory.minus ℬ).ι.map f))
    exact Localization.inverts
      (DerivedCategory.Qh : K(ℬ) ⥤ D(ℬ))
      (HomotopyCategory.quasiIso ℬ (up ℤ))
      ((HomotopyCategory.minus ℬ).ι.map f)
      (by simpa [boundedAboveHomotopyQuasiIso] using hf)
  have hLifted :
      IsIso (ιminus.map (mapBoundedAboveHomotopyToDerivedAbove.map f)) := by
    -- Proof comment: transport invertibility back along the fully faithful inclusion
    -- `D^-(\mathcal B) ↪ D(\mathcal B)`.
    exact
      ((NatIso.isIso_map_iff
        (ObjectProperty.liftCompιIso
          (DerivedCategory.TStructure.t.minus : ObjectProperty (D(ℬ)))
          ((HomotopyCategory.minus ℬ).ι ⋙ DerivedCategory.Qh)
          (fun K ↦ by simpa using qh_obj_mem_t_minus K))
        f)).2 hUnderlying
  let _ : IsIso (ιminus.map (mapBoundedAboveHomotopyToDerivedAbove.map f)) := hLifted
  exact isIso_of_fully_faithful ιminus (mapBoundedAboveHomotopyToDerivedAbove.map f)

/-- Helper for Proposition 13.29.2: if the image of a bounded-above morphism under
`mapBoundedAboveHomotopyCategory F` is a bounded-above quasi-isomorphism, then its image under
`KminusToDminus` is invertible. -/
private theorem isIso_KminusToDminus_map_of_mapped_boundedAbove_quasiIso
    {X Y : K⁻(𝒜)} (s : X ⟶ Y)
    (hs :
      boundedAboveHomotopyQuasiIso ℬ
        ((mapBoundedAboveHomotopyCategory F).map s)) :
    IsIso (KminusToDminus.map s) := by
  -- Proof comment: `KminusToDminus` is the composite
  -- `K^-(\mathcal A) ⟶ K^-(\mathcal B) ⟶ D^-(\mathcal B)`, so the previous localization helper
  -- applies directly to the mapped morphism.
  change
    IsIso
      (mapBoundedAboveHomotopyToDerivedAbove.map
        ((mapBoundedAboveHomotopyCategory F).map s))
  exact mapBoundedAboveHomotopyToDerivedAbove_map_isIso (f := _ ) hs

/-- Helper for Proposition 13.29.2: after forgetting the bounded-above restriction, the map of
`s` under `mapBoundedAboveHomotopyCategory F` is the ordinary homotopy-category image of the
underlying morphism. -/
private theorem mapBoundedAboveHomotopyCategory_map_eq
    {X Y : K⁻(𝒜)} (s : X ⟶ Y) :
    ((HomotopyCategory.minus ℬ).ι.map ((mapBoundedAboveHomotopyCategory F).map s)) =
      ((F.mapHomotopyCategory (up ℤ)).map ((HomotopyCategory.minus 𝒜).ι.map s)) := by
  -- Proof comment: the bounded-above functor is defined by restricting the ambient homotopy
  -- functor along the full-subcategory inclusion.
  simp [mapBoundedAboveHomotopyCategory]

/-- Helper for Proposition 13.29.2: the representative chain map of a bounded-above
quasi-isomorphism is itself a quasi-isomorphism. -/
private theorem quasiIso_out_of_boundedAbove_quasiIso
    {X Y : K⁻(𝒜)} (s : X ⟶ Y) (hs : QisMinus s) :
    QuasiIso (((HomotopyCategory.minus 𝒜).ι.map s).out) := by
  have hsAmbient :
      HomotopyCategory.quasiIso 𝒜 (up ℤ) ((HomotopyCategory.minus 𝒜).ι.map s) := hs
  -- Proof comment: pass from the bounded-above morphism to the chain-level representative by the
  -- quotient description of morphisms in the homotopy category.
  rw [← HomotopyCategory.quotient_map_out ((HomotopyCategory.minus 𝒜).ι.map s),
    HomotopyCategory.quotient_map_mem_quasiIso_iff] at hsAmbient
  exact hsAmbient

/-- Helper for Proposition 13.29.2: if a bounded-above chain map has terms in `P` on both sides
and is a quasi-isomorphism, then applying `F` yields another quasi-isomorphism. -/
private theorem mapped_quasiIso_of_termwiseObjectProperty
    (hFacyclic :
      ∀ (K : CochainComplex 𝒜 ℤ) (_ : CochainComplex.minus 𝒜 K) (_ : K.Acyclic)
        (_ : ∀ i : ℤ, P (K.X i)),
        ((F.mapHomologicalComplex (up ℤ)).obj K).Acyclic)
    {K L : CochainComplex 𝒜 ℤ} (f : K ⟶ L)
    (hKminus : CochainComplex.minus 𝒜 K)
    (hLminus : CochainComplex.minus 𝒜 L)
    (hK : ∀ i : ℤ, P (K.X i))
    (hL : ∀ i : ℤ, P (L.X i))
    (hf : QuasiIso f) :
    QuasiIso (((F.mapHomologicalComplex (up ℤ)).map f)) := by
  have hConeMinus : CochainComplex.minus 𝒜 (mappingCone f) :=
    mappingCone_boundedAbove (𝒜 := 𝒜) f hKminus hLminus
  have hConeAcyclic : (mappingCone f).Acyclic :=
    mappingCone_acyclic_of_quasiIso (𝒜 := 𝒜) f hf
  have hConeP : ∀ i : ℤ, P ((mappingCone f).X i) :=
    mappingCone_termwiseObjectProperty (𝒜 := 𝒜) (P := P) f hK hL
  have hMappedConeAcyclic :
      (mappingCone (((F.mapHomologicalComplex (up ℤ)).map f))).Acyclic := by
    -- Proof comment: the functor `F.mapHomologicalComplex` preserves the cone shape termwise, so
    -- the acyclicity hypothesis applies directly to the mapped cone.
    simpa using hFacyclic (mappingCone f) hConeMinus hConeAcyclic hConeP
  -- Proof comment: acyclicity of the mapped cone is exactly the cone criterion for the mapped
  -- chain map to be a quasi-isomorphism.
  exact quasiIso_of_mappingCone_acyclic (𝒜 := ℬ) (((F.mapHomologicalComplex (up ℤ)).map f))
    hMappedConeAcyclic

/-- Helper for Proposition 13.29.2: a bounded-above quasi-isomorphism between termwise-`P`
complexes is sent by `F` to a bounded-above quasi-isomorphism. -/
private theorem mapped_boundedAbove_quasiIso_of_termwiseObjectProperty
    (hFacyclic :
      ∀ (K : CochainComplex 𝒜 ℤ) (_ : CochainComplex.minus 𝒜 K) (_ : K.Acyclic)
        (_ : ∀ i : ℤ, P (K.X i)),
        ((F.mapHomologicalComplex (up ℤ)).obj K).Acyclic)
    {X Y : K⁻(𝒜)} (s : X ⟶ Y)
    (hX : termwiseObjectProperty (𝒜 := 𝒜) P X)
    (hY : termwiseObjectProperty (𝒜 := 𝒜) P Y)
    (hs : QisMinus s) :
    boundedAboveHomotopyQuasiIso ℬ ((mapBoundedAboveHomotopyCategory F).map s) := by
  let sAmbient : X.obj ⟶ Y.obj := (HomotopyCategory.minus 𝒜).ι.map s
  let f : X.obj.as ⟶ Y.obj.as := sAmbient.out
  have hXminus : CochainComplex.minus 𝒜 X.obj.as := by
    simpa [HomotopyCategory.minus] using X.property
  have hYminus : CochainComplex.minus 𝒜 Y.obj.as := by
    simpa [HomotopyCategory.minus] using Y.property
  have hf : QuasiIso f := by
    -- Proof comment: replace the bounded-above denominator by its chain-level representative.
    simpa [f, sAmbient] using
      quasiIso_out_of_boundedAbove_quasiIso (𝒜 := 𝒜) s hs
  have hMappedf : QuasiIso (((F.mapHomologicalComplex (up ℤ)).map f)) :=
    mapped_quasiIso_of_termwiseObjectProperty (𝒜 := 𝒜) (ℬ := ℬ) (F := F) (P := P) hFacyclic f
      hXminus hYminus hX hY hf
  change
    HomotopyCategory.quasiIso ℬ (up ℤ)
      ((HomotopyCategory.minus ℬ).ι.map ((mapBoundedAboveHomotopyCategory F).map s))
  rw [mapBoundedAboveHomotopyCategory_map_eq (F := F) s]
  rw [← HomotopyCategory.quotient_map_out
    (((F.mapHomotopyCategory (up ℤ)).map ((HomotopyCategory.minus 𝒜).ι.map s))),
    HomotopyCategory.quotient_map_mem_quasiIso_iff]
  -- Proof comment: after rewriting by `quotient_map_out`, the ambient mapped morphism is exactly
  -- the quotient of the mapped cochain representative `f`.
  simpa [f, sAmbient] using hMappedf

/-- Helper for Proposition 13.29.2: the bounded-above replacement theorem needed in the first
paragraph of the source proof. -/
private theorem exists_boundedAbove_termwise_P_quasiIso
    (a : ℤ) (K : CochainComplex 𝒜 ℤ) (hK : K.IsStrictlyLE a) :
    ∃ (Y : CochainComplex 𝒜 ℤ) (α : Y ⟶ K),
      CochainComplex.minus 𝒜 Y ∧ QuasiIso α ∧ ∀ i : ℤ, P (Y.X i) := by
  -- Proof comment: Proposition `13.29.2` uses the raw bounded-above replacement from
  -- Lemma `13.15.4`, without the subobject-closure detour from later results.
  obtain ⟨Y, α, hα⟩ :=
    exists_termwiseEpi_quasiIso_with_terms_in_of_isStrictlyLE P a K hK
  refine ⟨Y, α, ?_, hα.quasiIso, hα.term_mem⟩
  -- The replacement complex is bounded above by the same cutoff `a`.
  exact (CochainComplex.minus_iff 𝒜 Y).2 ⟨a, hα.strictlyLE⟩

/-- Helper for Proposition 13.29.2: a bounded-above homotopy object whose terms all lie in `P`
computes the unbounded left derived functor of `F`. -/
private theorem boundedAbove_termwise_P_computes_left_derived
    (hFacyclic :
      ∀ (K : CochainComplex 𝒜 ℤ) (_ : CochainComplex.minus 𝒜 K) (_ : K.Acyclic)
        (_ : ∀ i : ℤ, P (K.X i)),
        ((F.mapHomologicalComplex (up ℤ)).obj K).Acyclic)
    (X : K⁻(𝒜))
    (hX : termwiseObjectProperty (𝒜 := 𝒜) P X) :
    Functor.ComputesLeftDerivedAt KtoD Qis X.obj := by
  -- Proof comment: the first paragraph of the source proof is exactly the bounded-above subset
  -- criterion on `K^-(𝒜)`, with good objects defined by the termwise-`P` condition.
  let Pminus : ObjectProperty (K⁻(𝒜)) := termwiseObjectProperty (𝒜 := 𝒜) P
  have hP_reaches :
      ∀ Z : K⁻(𝒜), ∃ (Z' : K⁻(𝒜)) (s : Z' ⟶ Z), Pminus Z' ∧ QisMinus s := by
    intro Z
    let K : CochainComplex 𝒜 ℤ := Z.obj.as
    obtain ⟨a, hK⟩ := (CochainComplex.minus_iff 𝒜 K).1 Z.property
    -- Proof comment: resolve the bounded-above complex `Z` by the raw Lemma `13.15.4`
    -- replacement, then pass that replacement into `K^-(𝒜)`.
    obtain ⟨Y, α, hYminus, hα, hYmem⟩ :=
      exists_boundedAbove_termwise_P_quasiIso (𝒜 := 𝒜) (P := P) a K hK
    let Zc : Comp⁻(𝒜) := ⟨K, Z.property⟩
    have hZeq : (HomotopyCategory.Minus.quotient 𝒜).obj Zc = Z := by
      cases Z
      rfl
    let Yminus : Comp⁻(𝒜) := ⟨Y, hYminus⟩
    let Z' : K⁻(𝒜) := (HomotopyCategory.Minus.quotient 𝒜).obj Yminus
    let α' : Yminus ⟶ Zc := ⟨α⟩
    let s : Z' ⟶ Z := by
      simpa [Z', hZeq] using (HomotopyCategory.Minus.quotient 𝒜).map α'
    refine ⟨Z', s, ?_, ?_⟩
    · -- The chosen source is good by construction of the bounded-above replacement.
      intro i
      simpa [Pminus, termwiseObjectProperty, Z'] using hYmem i
    · -- The denominator stays a bounded-above quasi-isomorphism in the homotopy category.
      change HomotopyCategory.quasiIso 𝒜 (up ℤ)
        ((ObjectProperty.ι (HomotopyCategory.minus 𝒜)).map s)
      simpa [s, Z', hZeq] using
        (show HomotopyCategory.quasiIso 𝒜 (up ℤ)
            (((HomotopyCategory.quotient 𝒜 (up ℤ)).map α)) by
          rw [HomotopyCategory.quotient_map_mem_quasiIso_iff]
          exact hα)
  have hP_isIso :
      ∀ {X Y : K⁻(𝒜)} (s : X ⟶ Y), Pminus X → Pminus Y → QisMinus s →
        IsIso (KminusToDminus.map s) := by
    intro X Y s hX' hY' hs
    -- Proof comment: the cone argument is the only non-formal input needed to show that `F`
    -- inverts denominators between good bounded-above objects.
    have hsMapped :
        boundedAboveHomotopyQuasiIso ℬ
          ((mapBoundedAboveHomotopyCategory F).map s) :=
      mapped_boundedAbove_quasiIso_of_termwiseObjectProperty
        (F := F) (P := P) hFacyclic s hX' hY' hs
    exact isIso_KminusToDminus_map_of_mapped_boundedAbove_quasiIso (F := F) s hsMapped
  let _ : Functor.HasPointwiseLeftDerivedFunctor KminusToDminus QisMinus :=
    Functor.hasPointwiseLeftDerivedFunctor_of_subset
      (F := KminusToDminus) (S := QisMinus) Pminus hP_reaches hP_isIso
  have hXminus :
      Functor.ComputesLeftDerivedAt KminusToDminus QisMinus X :=
    Functor.computesLeftDerivedAt_of_mem_subset
      (F := KminusToDminus) (S := QisMinus) Pminus hP_reaches hP_isIso hX
  -- Proof comment: the canonical bounded-above/unbounded comparison transports the computation
  -- statement from `K^-(𝒜)` to the ambient homotopy category.
  exact (computes_left_derived_functor_at_iff_bounded_above F X).2 hXminus

/-- Helper for Proposition 13.29.2: exact sequential colimits preserve homology in `𝒜`. -/
local instance sequentialColim_preservesHomology :
    ((colim : (ℕ ⥤ 𝒜) ⥤ 𝒜).PreservesHomology) := by
  let G : (ℕ ⥤ 𝒜) ⥤ 𝒜 := colim
  -- Proof comment: exact functors between abelian categories preserve the finite limits and
  -- colimits entering the homology construction, so the standard exact-functor bridge applies.
  letI : PreservesFiniteLimits G := inferInstance
  letI : PreservesFiniteColimits G := inferInstance
  exact CategoryTheory.Functor.preservesHomologyOfExact G

/-- Helper for Proposition 13.29.2: in a sequential diagram of cochain complexes, the previous
differential at degree `i` forms a natural transformation on the degreewise diagrams. -/
private def prev_d_natTrans
    (S : ℕ ⥤ CochainComplex 𝒜 ℤ) (i : ℤ) :
    S ⋙ HomologicalComplex.eval 𝒜 (up ℤ) (i - 1) ⟶
      S ⋙ HomologicalComplex.eval 𝒜 (up ℤ) i where
  app n := (S.obj n).d (i - 1) i
  naturality _ _ f := by
    -- Proof comment: naturality is exactly the commutativity of differentials with a chain map.
    simpa using (S.map f).comm (i - 1) i

/-- Helper for Proposition 13.29.2: in a sequential diagram of cochain complexes, the next
differential at degree `i` forms a natural transformation on the degreewise diagrams. -/
private def next_d_natTrans
    (S : ℕ ⥤ CochainComplex 𝒜 ℤ) (i : ℤ) :
    S ⋙ HomologicalComplex.eval 𝒜 (up ℤ) i ⟶
      S ⋙ HomologicalComplex.eval 𝒜 (up ℤ) (i + 1) where
  app n := (S.obj n).d i (i + 1)
  naturality _ _ f := by
    -- Proof comment: this is the same differential-commutativity statement one degree higher.
    simpa using (S.map f).comm i (i + 1)

/-- Helper for Proposition 13.29.2: the consecutive degreewise differentials in a sequential
diagram still compose to zero inside the functor category. -/
private theorem degree_d_comp_eq_zero
    (S : ℕ ⥤ CochainComplex 𝒜 ℤ) (i : ℤ) :
    prev_d_natTrans (𝒜 := 𝒜) S i ≫ next_d_natTrans (𝒜 := 𝒜) S i = 0 := by
  -- Proof comment: check the equation componentwise and use `d ≫ d = 0` in each stage.
  ext n
  simpa using (S.obj n).d_comp_d (i - 1) i (i + 1)

/-- Helper for Proposition 13.29.2: the degree-`i` short complex attached to a sequential
diagram of cochain complexes, formed inside the functor category `ℕ ⥤ 𝒜`. -/
private def degree_shortComplex
    (S : ℕ ⥤ CochainComplex 𝒜 ℤ) (i : ℤ) :
    ShortComplex (ℕ ⥤ 𝒜) :=
  ShortComplex.mk
    (prev_d_natTrans (𝒜 := 𝒜) S i)
    (next_d_natTrans (𝒜 := 𝒜) S i)
    (degree_d_comp_eq_zero (𝒜 := 𝒜) S i)

/-- Helper for Proposition 13.29.2: evaluating the functor-category degree-`i` short complex at
a stage recovers the ordinary degree-`i` short complex of that stage. -/
private def degree_shortComplex_app_iso
    (S : ℕ ⥤ CochainComplex 𝒜 ℤ) (i : ℤ) (n : ℕ) :
    (degree_shortComplex (𝒜 := 𝒜) S i).map ((evaluation ℕ 𝒜).obj n) ≅
      (S.obj n).sc i :=
  -- Proof comment: after evaluation, both short complexes have the same three terms and
  -- differentials, so only the canonical `isoSc'` identification remains.
  (ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)) ≪≫
    ((S.obj n).isoSc' (i := i - 1) (j := i) (k := i + 1)
      (CochainComplex.prev ℤ i) (CochainComplex.next ℤ i)).symm

/-- Helper for Proposition 13.29.2: the first `mapShortComplex` compatibility condition for the
degree-`i` surface is the canonical colimit relation for the previous differential. -/
private theorem degree_shortComplex_colimit_map_prev
    (S : ℕ ⥤ CochainComplex 𝒜 ℤ) (i : ℤ) (n : ℕ) :
    colimit.ι (degree_shortComplex (𝒜 := 𝒜) S i).X₁ n ≫
        colim.map (prev_d_natTrans (𝒜 := 𝒜) S i) =
      (degree_shortComplex (𝒜 := 𝒜) S i).f.app n ≫
        colimit.ι (degree_shortComplex (𝒜 := 𝒜) S i).X₂ n := by
  -- Proof comment: this is exactly `colimit.ι_map`, rewritten on the chosen short-complex shape.
  simpa [degree_shortComplex] using
    (colimit.ι_map (prev_d_natTrans (𝒜 := 𝒜) S i) n)

/-- Helper for Proposition 13.29.2: the second `mapShortComplex` compatibility condition for the
degree-`i` surface is the canonical colimit relation for the next differential. -/
private theorem degree_shortComplex_colimit_map_next
    (S : ℕ ⥤ CochainComplex 𝒜 ℤ) (i : ℤ) (n : ℕ) :
    colimit.ι (degree_shortComplex (𝒜 := 𝒜) S i).X₂ n ≫
        colim.map (next_d_natTrans (𝒜 := 𝒜) S i) =
      (degree_shortComplex (𝒜 := 𝒜) S i).g.app n ≫
        colimit.ι (degree_shortComplex (𝒜 := 𝒜) S i).X₃ n := by
  -- Proof comment: this is the same cocone-leg identity for the next differential.
  simpa [degree_shortComplex] using
    (colimit.ι_map (next_d_natTrans (𝒜 := 𝒜) S i) n)

/-- Helper for Proposition 13.29.2: evaluating the chosen colimit cocone at degree `i` gives the
canonical cocone on the degree-`i` term diagram. -/
private def colimit_degree_term_cocone
    (S : ℕ ⥤ CochainComplex 𝒜 ℤ) [HasColimit S] (i : ℤ) :
    Cocone (S ⋙ HomologicalComplex.eval 𝒜 (up ℤ) i) :=
  (HomologicalComplex.eval 𝒜 (up ℤ) i).mapCocone (colimit.cocone S)

/-- Helper for Proposition 13.29.2: evaluation preserves the chosen sequential colimit, so the
degree-`i` evaluated cocone is colimiting. -/
private def colimit_degree_term_isColimit
    (S : ℕ ⥤ CochainComplex 𝒜 ℤ) [HasColimit S] (i : ℤ) :
    IsColimit (colimit_degree_term_cocone (𝒜 := 𝒜) S i) :=
  Limits.isColimitOfPreserves
    (HomologicalComplex.eval 𝒜 (up ℤ) i)
    (colimit.isColimit S)

/-- Helper for Proposition 13.29.2: the colimit of the degree-`i` terms is canonically the
degree-`i` term of the colimit complex. -/
private noncomputable def colimit_degree_term_iso
    (S : ℕ ⥤ CochainComplex 𝒜 ℤ) [HasColimit S] (i : ℤ) :
    colimit (S ⋙ HomologicalComplex.eval 𝒜 (up ℤ) i) ≅
      (colimit S).X i :=
  ((colimit_degree_term_isColimit (𝒜 := 𝒜) S i).coconePointUniqueUpToIso
    (colimit.isColimit (S ⋙ HomologicalComplex.eval 𝒜 (up ℤ) i))).symm

/-- Helper for Proposition 13.29.2: on each cocone leg, the degreewise colimit comparison is the
canonical degree map into the colimit complex. -/
private theorem colimit_degree_term_iso_hom_ι
    (S : ℕ ⥤ CochainComplex 𝒜 ℤ) [HasColimit S] (i : ℤ) (n : ℕ) :
    colimit.ι (S ⋙ HomologicalComplex.eval 𝒜 (up ℤ) i) n ≫
        (colimit_degree_term_iso (𝒜 := 𝒜) S i).hom =
      (colimit.ι S n).f i := by
  let e :
      (colimit S).X i ≅ colimit (S ⋙ HomologicalComplex.eval 𝒜 (up ℤ) i) :=
    (colimit_degree_term_isColimit (𝒜 := 𝒜) S i).coconePointUniqueUpToIso
      (colimit.isColimit (S ⋙ HomologicalComplex.eval 𝒜 (up ℤ) i))
  have h :=
    IsColimit.comp_coconePointUniqueUpToIso_hom
      (colimit_degree_term_isColimit (𝒜 := 𝒜) S i)
      (colimit.isColimit (S ⋙ HomologicalComplex.eval 𝒜 (up ℤ) i)) n
  -- Proof comment: compose the cocone-leg identity with the inverse comparison to recover the
  -- chosen direction for the canonical degreewise colimit comparison.
  simpa [colimit_degree_term_iso, colimit_degree_term_cocone, e] using
    (congrArg (fun f ↦ f ≫ e.inv) h).symm

/-- Helper for Proposition 13.29.2: the degreewise colimit comparison intertwines the previous
differential with the colimit of the previous-differential natural transformation. -/
private theorem colimit_degree_term_iso_prev_comm
    (S : ℕ ⥤ CochainComplex 𝒜 ℤ) [HasColimit S] (i : ℤ) :
    (colimit_degree_term_iso (𝒜 := 𝒜) S (i - 1)).hom ≫ (colimit S).d (i - 1) i =
      colim.map (prev_d_natTrans (𝒜 := 𝒜) S i) ≫
        (colimit_degree_term_iso (𝒜 := 𝒜) S i).hom := by
  -- Proof comment: compare both morphisms after precomposing with every cocone leg of the source
  -- colimit, where the claim reduces to naturality of the colimit cocone in the complex degree.
  apply colimit.hom_ext
  intro n
  calc
    colimit.ι (S ⋙ HomologicalComplex.eval 𝒜 (up ℤ) (i - 1)) n ≫
        (colimit_degree_term_iso (𝒜 := 𝒜) S (i - 1)).hom ≫ (colimit S).d (i - 1) i =
      (colimit.ι S n).f (i - 1) ≫ (colimit S).d (i - 1) i := by
        rw [Category.assoc, colimit_degree_term_iso_hom_ι]
    _ = (S.obj n).d (i - 1) i ≫ (colimit.ι S n).f i := by
        simpa using (colimit.ι S n).comm (i - 1) i
    _ = (prev_d_natTrans (𝒜 := 𝒜) S i).app n ≫
          colimit.ι (S ⋙ HomologicalComplex.eval 𝒜 (up ℤ) i) n ≫
            (colimit_degree_term_iso (𝒜 := 𝒜) S i).hom := by
        rw [colimit_degree_term_iso_hom_ι]
    _ = (colimit.ι (S ⋙ HomologicalComplex.eval 𝒜 (up ℤ) (i - 1)) n ≫
          colim.map (prev_d_natTrans (𝒜 := 𝒜) S i)) ≫
            (colimit_degree_term_iso (𝒜 := 𝒜) S i).hom := by
        rw [colimit.ι_map]
        simp [Category.assoc]
    _ = colimit.ι (S ⋙ HomologicalComplex.eval 𝒜 (up ℤ) (i - 1)) n ≫
          (colim.map (prev_d_natTrans (𝒜 := 𝒜) S i) ≫
            (colimit_degree_term_iso (𝒜 := 𝒜) S i).hom) := by
        simp [Category.assoc]

/-- Helper for Proposition 13.29.2: the degreewise colimit comparison intertwines the next
differential with the colimit of the next-differential natural transformation. -/
private theorem colimit_degree_term_iso_next_comm
    (S : ℕ ⥤ CochainComplex 𝒜 ℤ) [HasColimit S] (i : ℤ) :
    (colimit_degree_term_iso (𝒜 := 𝒜) S i).hom ≫ (colimit S).d i (i + 1) =
      colim.map (next_d_natTrans (𝒜 := 𝒜) S i) ≫
        (colimit_degree_term_iso (𝒜 := 𝒜) S (i + 1)).hom := by
  -- Proof comment: the proof is the same stagewise cocone-leg calculation one degree higher.
  apply colimit.hom_ext
  intro n
  calc
    colimit.ι (S ⋙ HomologicalComplex.eval 𝒜 (up ℤ) i) n ≫
        (colimit_degree_term_iso (𝒜 := 𝒜) S i).hom ≫ (colimit S).d i (i + 1) =
      (colimit.ι S n).f i ≫ (colimit S).d i (i + 1) := by
        rw [Category.assoc, colimit_degree_term_iso_hom_ι]
    _ = (S.obj n).d i (i + 1) ≫ (colimit.ι S n).f (i + 1) := by
        simpa using (colimit.ι S n).comm i (i + 1)
    _ = (next_d_natTrans (𝒜 := 𝒜) S i).app n ≫
          colimit.ι (S ⋙ HomologicalComplex.eval 𝒜 (up ℤ) (i + 1)) n ≫
            (colimit_degree_term_iso (𝒜 := 𝒜) S (i + 1)).hom := by
        rw [colimit_degree_term_iso_hom_ι]
    _ = (colimit.ι (S ⋙ HomologicalComplex.eval 𝒜 (up ℤ) i) n ≫
          colim.map (next_d_natTrans (𝒜 := 𝒜) S i)) ≫
            (colimit_degree_term_iso (𝒜 := 𝒜) S (i + 1)).hom := by
        rw [colimit.ι_map]
        simp [Category.assoc]
    _ = colimit.ι (S ⋙ HomologicalComplex.eval 𝒜 (up ℤ) i) n ≫
          (colim.map (next_d_natTrans (𝒜 := 𝒜) S i) ≫
            (colimit_degree_term_iso (𝒜 := 𝒜) S (i + 1)).hom) := by
        simp [Category.assoc]

/-- Helper for Proposition 13.29.2: the canonical colimit short complex of the sequential
degree-`i` surface identifies with the degree-`i` short complex of the colimit complex. -/
private noncomputable def colimit_degree_shortComplex_iso
    (S : ℕ ⥤ CochainComplex 𝒜 ℤ) [HasColimit S] (i : ℤ) :
    colim.mapShortComplex (degree_shortComplex (𝒜 := 𝒜) S i)
      (colimit.isColimit _)
      (colimit.cocone _)
      (colimit.cocone _)
      (colim.map (prev_d_natTrans (𝒜 := 𝒜) S i))
      (colim.map (next_d_natTrans (𝒜 := 𝒜) S i))
      (degree_shortComplex_colimit_map_prev (𝒜 := 𝒜) S i)
      (degree_shortComplex_colimit_map_next (𝒜 := 𝒜) S i) ≅
        (colimit S).sc i :=
  -- Proof comment: assemble the three degreewise colimit comparisons into a short-complex
  -- isomorphism, then identify the resulting three-term complex with `(colimit S).sc i`.
  (ShortComplex.isoMk
      (colimit_degree_term_iso (𝒜 := 𝒜) S (i - 1))
      (colimit_degree_term_iso (𝒜 := 𝒜) S i)
      (colimit_degree_term_iso (𝒜 := 𝒜) S (i + 1))
      (colimit_degree_term_iso_prev_comm (𝒜 := 𝒜) S i)
      (colimit_degree_term_iso_next_comm (𝒜 := 𝒜) S i)) ≪≫
    ((colimit S).isoSc' (i := i - 1) (j := i) (k := i + 1)
      (CochainComplex.prev ℤ i) (CochainComplex.next ℤ i)).symm

/-- Helper for Proposition 13.29.2: evaluating the functor-category degree-`i` short complex at
each stage defines the ordinary sequential diagram of stage short complexes. -/
private def degree_shortComplex_evalFunctor
    (S : ℕ ⥤ CochainComplex 𝒜 ℤ) (i : ℤ) :
    ℕ ⥤ ShortComplex 𝒜 where
  obj n := (degree_shortComplex (𝒜 := 𝒜) S i).map ((evaluation ℕ 𝒜).obj n)
  map f := (degree_shortComplex (𝒜 := 𝒜) S i).mapNatTrans ((evaluation ℕ 𝒜).map f)
  map_id n := by
    -- Proof comment: each component of the identity map is definitionally the identity.
    ext <;> simp
  map_comp f g := by
    -- Proof comment: evaluation of a composite agrees componentwise with successive evaluations.
    ext <;> simp

/-- Helper for Proposition 13.29.2: the evaluated degree-`i` short complex is naturally the
ordinary degree-`i` short-complex diagram of the stages. -/
private noncomputable def degree_shortComplex_app_natIso
    (S : ℕ ⥤ CochainComplex 𝒜 ℤ) (i : ℤ) :
    degree_shortComplex_evalFunctor (𝒜 := 𝒜) S i ≅
      S ⋙ HomologicalComplex.shortComplexFunctor 𝒜 (up ℤ) i :=
  NatIso.ofComponents
    (fun n ↦ degree_shortComplex_app_iso (𝒜 := 𝒜) S i n)
    (fun n m f ↦ by
      -- Proof comment: both sides are the short-complex morphism induced by the same chain map.
      ext <;> simp)

/-- Helper for Proposition 13.29.2: functor-category homology agrees with stagewise homology
after evaluation. -/
private noncomputable def degree_shortComplex_homology_eval_iso
    (S : ℕ ⥤ CochainComplex 𝒜 ℤ) (i : ℤ) :
    (degree_shortComplex (𝒜 := 𝒜) S i).homology ≅
      degree_shortComplex_evalFunctor (𝒜 := 𝒜) S i ⋙ ShortComplex.homologyFunctor 𝒜 :=
  NatIso.ofComponents
    (fun n ↦
      ((degree_shortComplex (𝒜 := 𝒜) S i).mapHomologyIso ((evaluation ℕ 𝒜).obj n)).symm)
    (fun n m f ↦ by
      -- Proof comment: isolate the functor-category-to-stagewise transport before the later
      -- colimit argument, so the homology comparison does not have to rediscover it.
      have h :=
        NatTrans.app_homology
          (τ := (evaluation ℕ 𝒜).map f) (S := degree_shortComplex (𝒜 := 𝒜) S i)
      simpa [degree_shortComplex_evalFunctor, Category.assoc] using
        congrArg
          (fun k ↦
            k ≫ (((degree_shortComplex (𝒜 := 𝒜) S i).mapHomologyIso
              ((evaluation ℕ 𝒜).obj m)).symm).hom)
          h)

/-- Helper for Proposition 13.29.2: the homology of the functor-category degree-`i` short
complex is the actual degree-`i` homology diagram of the sequential complex diagram. -/
private noncomputable def degree_shortComplex_homology_iso
    (S : ℕ ⥤ CochainComplex 𝒜 ℤ) (i : ℤ) :
    (degree_shortComplex (𝒜 := 𝒜) S i).homology ≅
      S ⋙ HomologicalComplex.homologyFunctor 𝒜 (up ℤ) i :=
  let e₁ := degree_shortComplex_homology_eval_iso (𝒜 := 𝒜) S i
  let e₂ :=
    Functor.mapIso (ShortComplex.homologyFunctor 𝒜)
      (degree_shortComplex_app_natIso (𝒜 := 𝒜) S i)
  let e₃ :
      (S ⋙ HomologicalComplex.shortComplexFunctor 𝒜 (up ℤ) i) ⋙
          ShortComplex.homologyFunctor 𝒜 ≅
        S ⋙ HomologicalComplex.homologyFunctor 𝒜 (up ℤ) i :=
    NatIso.ofComponents
      (fun n ↦ by
        -- Proof comment: on each stage, homology of the standard short complex is definitionally
        -- the degree-`i` homology object.
        exact Iso.refl _)
      (fun n m f ↦ by
        -- Proof comment: the map on homology of the standard short-complex functor is exactly
        -- `homologyMap`.
        rfl)
  -- Proof comment: compose the evaluation comparison, the short-complex identification, and the
  -- definitional identification of short-complex homology with complex homology.
  e₁ ≪≫ e₂ ≪≫ e₃

/-- Helper for Proposition 13.29.2: the universal sequential colimit cocone defines a natural
transformation from evaluation at stage `n` to the colimit functor on degreewise diagrams. -/
private theorem evaluationToColimit_naturality
    (n : ℕ) {A B : ℕ ⥤ 𝒜} (τ : A ⟶ B) :
    ((evaluation ℕ 𝒜).obj n).map τ ≫ colimit.ι B n =
      colimit.ι A n ≫ (colim : (ℕ ⥤ 𝒜) ⥤ 𝒜).map τ := by
  -- Proof comment: this is exactly the naturality of the universal colimit cocone.
  simpa using (colimit.ι_map τ n).symm

/-- Helper for Proposition 13.29.2: evaluation at a fixed stage maps naturally to the sequential
colimit functor on degreewise diagrams. -/
private def evaluationToColimitNatTrans
    (n : ℕ) :
    (evaluation ℕ 𝒜).obj n ⟶ (colim : (ℕ ⥤ 𝒜) ⥤ 𝒜) where
  app A := colimit.ι A n
  naturality _ _ τ := evaluationToColimit_naturality (𝒜 := 𝒜) n τ

/-- Helper for Proposition 13.29.2: the stage component of the homology-diagram identification
collapses the evaluation-side transport to the ordinary stage short-complex comparison. -/
private theorem degree_shortComplex_homology_iso_inv_app_comp_eval_inv
    (S : ℕ ⥤ CochainComplex 𝒜 ℤ) (i : ℤ) (n : ℕ) :
    (degree_shortComplex_homology_iso (𝒜 := 𝒜) S i).inv.app n ≫
        ((degree_shortComplex (𝒜 := 𝒜) S i).mapHomologyIso
          ((evaluation ℕ 𝒜).obj n)).inv =
      ShortComplex.homologyMap
        (degree_shortComplex_app_iso (𝒜 := 𝒜) S i n).inv := by
  -- Proof comment: unfold the stage component of the natural isomorphism and cancel the adjacent
  -- evaluation comparison.
  simp [degree_shortComplex_homology_iso, degree_shortComplex_homology_eval_iso,
    degree_shortComplex_app_natIso, Category.assoc]

/-- Helper for Proposition 13.29.2: after rewriting both endpoints of the universal stage leg
through the chosen short-complex identifications, the resulting short-complex morphism is the one
induced by the chain-map cocone leg `S_n ⟶ colim S`. -/
private theorem degree_shortComplex_transport_to_colimit_leg
    (S : ℕ ⥤ CochainComplex 𝒜 ℤ) (i : ℤ) (n : ℕ) :
    (degree_shortComplex_app_iso (𝒜 := 𝒜) S i n).inv ≫
        (degree_shortComplex (𝒜 := 𝒜) S i).mapNatTrans
          (evaluationToColimitNatTrans (𝒜 := 𝒜) n) ≫
        (colimit_degree_shortComplex_iso (𝒜 := 𝒜) S i).hom =
      (HomologicalComplex.shortComplexFunctor 𝒜 (up ℤ) i).map (colimit.ι S n) := by
  -- Proof comment: compare the transported short-complex map componentwise on the three terms,
  -- where each component is just the corresponding degree map of `colimit.ι S n`.
  ext <;> simp [degree_shortComplex_app_iso, evaluationToColimitNatTrans,
    colimit_degree_shortComplex_iso, colimit_degree_term_iso_hom_ι, Category.assoc]

/-- Helper for Proposition 13.29.2: exact sequential colimits identify the `i`th homology of the
colimit complex with the colimit of the `i`th homology diagram. -/
private noncomputable def homology_of_sequential_colimit_iso_colimit_homology
    (S : ℕ ⥤ CochainComplex 𝒜 ℤ) (i : ℤ) :
    ((HomologicalComplex.homologyFunctor 𝒜 (up ℤ) i).obj (colimit S)) ≅
      colimit (S ⋙ HomologicalComplex.homologyFunctor 𝒜 (up ℤ) i) := by
  -- Proof comment: package exactness on the degree-short-complex surface first, then transport to
  -- the actual homology diagram of the sequential tower.
  simpa [HomologicalComplex.homologyFunctor_obj] using
    ((ShortComplex.homologyMapIso
      (colimit_degree_shortComplex_iso (𝒜 := 𝒜) S i)).symm ≪≫
        (degree_shortComplex (𝒜 := 𝒜) S i).mapHomologyIso
          (colim : (ℕ ⥤ 𝒜) ⥤ 𝒜) ≪≫
        colim.mapIso (degree_shortComplex_homology_iso (𝒜 := 𝒜) S i))

/-- Helper for Proposition 13.29.2: exact sequential colimits identify the colimit of the
degreewise homology diagram with the homology of the colimit complex. -/
private noncomputable def colimit_homology_iso_of_exact_sequential
    (S : ℕ ⥤ CochainComplex 𝒜 ℤ) (i : ℤ) :
    colimit (S ⋙ HomologicalComplex.homologyFunctor 𝒜 (up ℤ) i) ≅
      (colimit S).homology i :=
  (homology_of_sequential_colimit_iso_colimit_homology (𝒜 := 𝒜) S i).symm

/-- Helper for Proposition 13.29.2: on each stage leg, the exact-colimit homology comparison is
exactly the homology map induced by the universal cocone map `S_n ⟶ colim S`. -/
private theorem colimit_homology_iso_of_exact_sequential_hom_ι
    (S : ℕ ⥤ CochainComplex 𝒜 ℤ) (i : ℤ) (n : ℕ) :
    colimit.ι (S ⋙ HomologicalComplex.homologyFunctor 𝒜 (up ℤ) i) n ≫
        (colimit_homology_iso_of_exact_sequential (𝒜 := 𝒜) S i).hom =
      HomologicalComplex.homologyMap (colimit.ι S n) i := by
  let T := degree_shortComplex (𝒜 := 𝒜) S i
  have h_leg :
      colimit.ι T.homology n =
        (T.mapHomologyIso ((evaluation ℕ 𝒜).obj n)).inv ≫
          ShortComplex.homologyMap
            (T.mapNatTrans (evaluationToColimitNatTrans (𝒜 := 𝒜) n)) ≫
          (T.mapHomologyIso (colim : (ℕ ⥤ 𝒜) ⥤ 𝒜)).hom := by
    -- Proof comment: apply `NatTrans.app_homology` to the evaluation-to-colimit natural
    -- transformation on the degree-`i` short-complex surface.
    simpa [T, evaluationToColimitNatTrans] using
      (NatTrans.app_homology
        (τ := evaluationToColimitNatTrans (𝒜 := 𝒜) n) (S := T))
  calc
    colimit.ι (S ⋙ HomologicalComplex.homologyFunctor 𝒜 (up ℤ) i) n ≫
        (colimit_homology_iso_of_exact_sequential (𝒜 := 𝒜) S i).hom =
      (degree_shortComplex_homology_iso (𝒜 := 𝒜) S i).inv.app n ≫
          colimit.ι T.homology n ≫
            (T.mapHomologyIso (colim : (ℕ ⥤ 𝒜) ⥤ 𝒜)).inv ≫
              (ShortComplex.homologyMapIso
                (colimit_degree_shortComplex_iso (𝒜 := 𝒜) S i)).hom := by
        -- Proof comment: move the stage leg across the colimit of the homology-diagram
        -- isomorphism.
        simpa [colimit_homology_iso_of_exact_sequential,
          homology_of_sequential_colimit_iso_colimit_homology, T, Category.assoc] using
          (colimit.ι_map (τ := (degree_shortComplex_homology_iso (𝒜 := 𝒜) S i).inv) n)
    _ =
      (degree_shortComplex_homology_iso (𝒜 := 𝒜) S i).inv.app n ≫
          (T.mapHomologyIso ((evaluation ℕ 𝒜).obj n)).inv ≫
            ShortComplex.homologyMap
              (T.mapNatTrans (evaluationToColimitNatTrans (𝒜 := 𝒜) n)) ≫
                (ShortComplex.homologyMapIso
                  (colimit_degree_shortComplex_iso (𝒜 := 𝒜) S i)).hom := by
        -- Proof comment: replace the middle colimit leg by the explicit homology naturality
        -- formula.
        simpa [Category.assoc] using
          congrArg
            (fun f ↦
              (degree_shortComplex_homology_iso (𝒜 := 𝒜) S i).inv.app n ≫
                f ≫
                  (T.mapHomologyIso (colim : (ℕ ⥤ 𝒜) ⥤ 𝒜)).inv ≫
                    (ShortComplex.homologyMapIso
                      (colimit_degree_shortComplex_iso (𝒜 := 𝒜) S i)).hom)
            h_leg
    _ =
      ShortComplex.homologyMap
          (degree_shortComplex_app_iso (𝒜 := 𝒜) S i n).inv ≫
            ShortComplex.homologyMap
              (T.mapNatTrans (evaluationToColimitNatTrans (𝒜 := 𝒜) n)) ≫
                (ShortComplex.homologyMapIso
                  (colimit_degree_shortComplex_iso (𝒜 := 𝒜) S i)).hom := by
        -- Proof comment: cancel the evaluation-side comparison inside the stage component of the
        -- homology-diagram identification.
        rw [degree_shortComplex_homology_iso_inv_app_comp_eval_inv (𝒜 := 𝒜)]
    _ =
      ShortComplex.homologyMap
        ((degree_shortComplex_app_iso (𝒜 := 𝒜) S i n).inv ≫
          T.mapNatTrans (evaluationToColimitNatTrans (𝒜 := 𝒜) n) ≫
            (colimit_degree_shortComplex_iso (𝒜 := 𝒜) S i).hom) := by
        -- Proof comment: collapse the three homology maps into the homology map of the composite
        -- short-complex morphism.
        simp [Category.assoc, ShortComplex.homologyMap_comp]
    _ =
      ShortComplex.homologyMap
        ((HomologicalComplex.shortComplexFunctor 𝒜 (up ℤ) i).map (colimit.ι S n)) := by
        rw [degree_shortComplex_transport_to_colimit_leg (𝒜 := 𝒜)]
    _ = HomologicalComplex.homologyMap (colimit.ι S n) i := by
        rfl

/-- Helper for Proposition 13.29.2: once the truncation cutoff contains degree `i`, the stage map
from an upper-truncation resolution tower to the target complex is a quasi-isomorphism in degree
`i`. -/
private theorem toTarget_quasiIsoAt_of_le_stage
    {K : CochainComplex 𝒜 ℤ}
    (T : UpperTruncationResolutionTower P K)
    (i : ℤ) {n : ℕ} (h : i ≤ (n : ℤ) + 1) :
    QuasiIsoAt (T.toTarget n) i := by
  -- Proof comment: the stage comparison is already a quasi-isomorphism, and the canonical
  -- truncation inclusion is a quasi-isomorphism in every degree at or below the cutoff.
  change QuasiIsoAt (T.comparison.app n ≫ K.ιTruncLE ((n : ℤ) + 1)) i
  have hcomparison : QuasiIsoAt (T.comparison.app n) i :=
    (T.isResolutionStage n).quasiIso.quasiIsoAt i
  have htrunc : QuasiIsoAt (K.ιTruncLE ((n : ℤ) + 1)) i := by
    simpa using CochainComplex.quasiIsoAt_ιTruncLE K ((n : ℤ) + 1) i h
  -- Proof comment: rewrite to the homology map and compose the two stagewise isomorphisms
  -- explicitly rather than leaving the composition to instance search.
  rw [quasiIsoAt_iff_isIso_homologyMap] at hcomparison htrunc ⊢
  letI : IsIso (HomologicalComplex.homologyMap (T.comparison.app n) i) := hcomparison
  letI : IsIso (HomologicalComplex.homologyMap (K.ιTruncLE ((n : ℤ) + 1)) i) := htrunc
  let e₁ : _ ≅ _ := asIso (HomologicalComplex.homologyMap (T.comparison.app n) i)
  let e₂ : _ ≅ _ := asIso (HomologicalComplex.homologyMap (K.ιTruncLE ((n : ℤ) + 1)) i)
  refine ⟨⟨e₂.inv ≫ e₁.inv, ?_, ?_⟩⟩
  · simp [HomologicalComplex.homologyMap_comp, Category.assoc, e₁, e₂]
  · simp [HomologicalComplex.homologyMap_comp, Category.assoc, e₁, e₂]

/-- Helper for Proposition 13.29.2: after a stage whose cutoff contains degree `i`, the induced
diagram on `i`th homology is eventually constant. -/
private theorem homologyDiagram_isEventuallyConstantFrom_of_le_stage
    {K : CochainComplex 𝒜 ℤ}
    (T : UpperTruncationResolutionTower P K)
    (i : ℤ) {n : ℕ} (h : i ≤ (n : ℤ) + 1) :
    CategoryTheory.Functor.IsEventuallyConstantFrom
      (T.diagram ⋙ HomologicalComplex.homologyFunctor 𝒜 (up ℤ) i) n := by
  intro j f
  have hnj : n ≤ j := leOfHom f
  have hsource : QuasiIsoAt (T.toTarget n) i :=
    toTarget_quasiIsoAt_of_le_stage (𝒜 := 𝒜) (P := P) T i h
  have htarget : QuasiIsoAt (T.toTarget j) i :=
    toTarget_quasiIsoAt_of_le_stage (𝒜 := 𝒜) (P := P) T i (by omega)
  have hcomp : T.diagram.map f ≫ T.toTarget j = T.toTarget n := by
    change T.diagram.map f ≫ T.cocone.ι.app j = T.cocone.ι.app n
    exact T.cocone.w f
  -- Proof comment: naturality of the cocone identifies the transition map with a morphism between
  -- two stage objects that are already quasi-isomorphic to the target in degree `i`.
  have hstep : QuasiIsoAt (T.diagram.map f) i := by
    letI : QuasiIsoAt (T.diagram.map f ≫ T.toTarget j) i := by
      simpa [hcomp] using hsource
    exact quasiIsoAt_of_comp_right (T.diagram.map f) (T.toTarget j) i
  rw [quasiIsoAt_iff_isIso_homologyMap] at hstep
  simpa [Functor.comp_map] using hstep

/-- Helper for Proposition 13.29.2: for each fixed degree, the homology cocone of an
upper-truncation resolution tower is colimiting because the stage maps to the target become
isomorphisms on that homology group after the cutoff passes the degree. -/
private noncomputable def toTarget_homologyCocone_isColimit
    {K : CochainComplex 𝒜 ℤ}
    (T : UpperTruncationResolutionTower P K)
    (i : ℤ) :
    IsColimit
      (((HomologicalComplex.homologyFunctor 𝒜 (up ℤ) i).mapCocone T.cocone)) := by
  let n0 : ℕ := Int.toNat i
  have hle : i ≤ (n0 : ℤ) + 1 := by
    -- Proof comment: any stage at `Int.toNat i` or later already contains degree `i`.
    by_cases hnonneg : 0 ≤ i
    · rw [Int.toNat_of_nonneg hnonneg]
      omega
    · have hnonpos : i ≤ 0 := le_of_not_ge hnonneg
      dsimp [n0]
      rw [Int.toNat_of_nonpos hnonpos]
      omega
  let hstable :
      CategoryTheory.Functor.IsEventuallyConstantFrom
        (T.diagram ⋙ HomologicalComplex.homologyFunctor 𝒜 (up ℤ) i) n0 :=
    homologyDiagram_isEventuallyConstantFrom_of_le_stage
      (𝒜 := 𝒜) (P := P) T i hle
  have hstage : QuasiIsoAt (T.toTarget n0) i :=
    toTarget_quasiIsoAt_of_le_stage (𝒜 := 𝒜) (P := P) T i hle
  rw [quasiIsoAt_iff_isIso_homologyMap] at hstage
  haveI :
      IsIso
        ((((HomologicalComplex.homologyFunctor 𝒜 (up ℤ) i).mapCocone
            T.cocone).ι.app n0)) := by
    -- Proof comment: the chosen stage leg is exactly the homology map of the stage comparison to
    -- the target.
    simpa [n0] using hstage
  -- Proof comment: eventual constancy upgrades the mapped cocone to a colimit cocone once one
  -- stage leg is known to be an isomorphism.
  exact hstable.isColimitOfIsIso
    (((HomologicalComplex.homologyFunctor 𝒜 (up ℤ) i).mapCocone T.cocone))

/-- Helper for Proposition 13.29.2: after identifying `H^i(colim T_n)` with the colimit of the
degree-`i` homology diagram, the homology map of `T.fromColimit` is exactly the universal morphism
to the mapped target cocone. -/
private theorem colimit_homology_iso_hom_comp_homologyMap_fromColimit
    {K : CochainComplex 𝒜 ℤ}
    (T : UpperTruncationResolutionTower P K)
    (i : ℤ) :
    (colimit_homology_iso_of_exact_sequential (𝒜 := 𝒜) (S := T.diagram) i).hom ≫
        HomologicalComplex.homologyMap T.fromColimit i =
      colimit.desc
        (T.diagram ⋙ HomologicalComplex.homologyFunctor 𝒜 (up ℤ) i)
        ((HomologicalComplex.homologyFunctor 𝒜 (up ℤ) i).mapCocone T.cocone) := by
  -- Proof comment: compare both morphisms after precomposing with each stage leg of the homology
  -- colimit. On those legs the claim is exactly `ι_comp_fromColimit`.
  apply colimit.hom_ext
  intro n
  calc
    colimit.ι (T.diagram ⋙ HomologicalComplex.homologyFunctor 𝒜 (up ℤ) i) n ≫
        (colimit_homology_iso_of_exact_sequential (𝒜 := 𝒜) (S := T.diagram) i).hom ≫
          HomologicalComplex.homologyMap T.fromColimit i =
      HomologicalComplex.homologyMap (colimit.ι T.diagram n) i ≫
        HomologicalComplex.homologyMap T.fromColimit i := by
        rw [Category.assoc, colimit_homology_iso_of_exact_sequential_hom_ι]
    _ = HomologicalComplex.homologyMap (colimit.ι T.diagram n ≫ T.fromColimit) i := by
        rw [HomologicalComplex.homologyMap_comp]
    _ = HomologicalComplex.homologyMap (T.toTarget n) i := by
        rw [UpperTruncationResolutionTower.ι_comp_fromColimit]
    _ = ((HomologicalComplex.homologyFunctor 𝒜 (up ℤ) i).mapCocone T.cocone).ι.app n := by
        rfl
    _ = colimit.ι (T.diagram ⋙ HomologicalComplex.homologyFunctor 𝒜 (up ℤ) i) n ≫
          colimit.desc
            (T.diagram ⋙ HomologicalComplex.homologyFunctor 𝒜 (up ℤ) i)
            ((HomologicalComplex.homologyFunctor 𝒜 (up ℤ) i).mapCocone T.cocone) := by
        simp [Category.assoc]

/-- Helper for Proposition 13.29.2: the canonical map from the colimit of an upper-truncation
resolution tower to the target complex is a quasi-isomorphism. -/
private theorem upper_truncation_fromColimit_quasiIso
    {K : CochainComplex 𝒜 ℤ}
    (T : UpperTruncationResolutionTower P K) :
    QuasiIso T.fromColimit := by
  -- Proof comment: rewrite the homology of the colimit as the colimit of stage homologies, then
  -- identify the resulting universal map with the mapped target cocone, which is already
  -- colimiting by eventual constancy after the cutoff passes the chosen degree.
  rw [quasiIso_iff_isIso_homologyMap]
  intro i
  have hdesc :
      IsIso
        (colimit.desc
          (T.diagram ⋙ HomologicalComplex.homologyFunctor 𝒜 (up ℤ) i)
          ((HomologicalComplex.homologyFunctor 𝒜 (up ℤ) i).mapCocone T.cocone)) := by
    let hcolim :=
      toTarget_homologyCocone_isColimit (𝒜 := 𝒜) (P := P) T i
    exact hcolim.hom_isIso
  have hcomp :
      IsIso
        ((colimit_homology_iso_of_exact_sequential (𝒜 := 𝒜) (S := T.diagram) i).hom ≫
          HomologicalComplex.homologyMap T.fromColimit i) := by
    rw [colimit_homology_iso_hom_comp_homologyMap_fromColimit (𝒜 := 𝒜) (P := P) T i]
    infer_instance
  exact
    (isIso_comp_left_iff
      ((colimit_homology_iso_of_exact_sequential (𝒜 := 𝒜) (S := T.diagram) i).hom)
      (HomologicalComplex.homologyMap T.fromColimit i)).1 hcomp

/-- Under the hypotheses of Proposition 13.29.2, the unbounded functor
`K(\mathcal A) ⟶ D(\mathcal B)` has a pointwise left derived functor at every object. This is the
canonical owner-level formulation; the source-facing proposition below is its standard corollary.
-/
theorem hasPointwiseLeftDerivedFunctor_of_boundedAbove_acyclic_property_and_exact_sequential_colimits
    (hFacyclic :
      ∀ (K : CochainComplex 𝒜 ℤ) (_ : CochainComplex.minus 𝒜 K) (_ : K.Acyclic)
        (_ : ∀ i : ℤ, P (K.X i)),
        ((F.mapHomologicalComplex (up ℤ)).obj K).Acyclic) :
    Functor.HasPointwiseLeftDerivedFunctor KtoD Qis := by
  -- Route correction: the bounded-above paragraph now runs directly from `Lemma 13.15.4`, using
  -- the cone criterion to show that bounded-above quasi-isomorphisms between termwise-`P`
  -- complexes are inverted by `KminusToDminus`.
  let _ := boundedAbove_termwise_P_computes_left_derived (F := F) (P := P) hFacyclic
  let _ := hFacyclic
  -- TODO: the exact-colimit homology comparison and the tower-level quasi-isomorphism route are
  -- now isolated above. The remaining source-faithful step is the final comparison claim: if
  -- `α : Q ⟶ P` is a quasi-isomorphism between two colimit objects of upper-truncation towers,
  -- show that `KtoD.map α` is invertible by passing stagewise bounded-above termwise-`P`
  -- refinements through exact sequential colimits of `H^i(F(-))`.
  sorry

/-- Proposition 13.29.2: let `F : 𝒜 ⥤ ℬ` be a right exact functor of abelian categories, and let
`P` be an object property on `𝒜` containing `0`, closed under finite direct sums, and admitting
an objectwise epimorphic cover of every object. Assume every bounded-above acyclic cochain
complex with terms in `P` is sent by `F` to an acyclic complex, that `𝒜` and `ℬ` have exact
sequential colimits, and that `F` preserves sequential colimits. Then the left derived functor
`LF` is defined on all of `D(𝒜)`. -/
theorem hasLeftDerivedFunctor_of_boundedAbove_acyclic_property_and_exact_sequential_colimits
    (hFacyclic :
      ∀ (K : CochainComplex 𝒜 ℤ) (_ : CochainComplex.minus 𝒜 K) (_ : K.Acyclic)
        (_ : ∀ i : ℤ, P (K.X i)),
        ((F.mapHomologicalComplex (up ℤ)).obj K).Acyclic) :
    Functor.HasLeftDerivedFunctor KtoD Qis := by
  let _ : Functor.HasPointwiseLeftDerivedFunctor KtoD Qis :=
    hasPointwiseLeftDerivedFunctor_of_boundedAbove_acyclic_property_and_exact_sequential_colimits
      F P hFacyclic
  infer_instance

end

end CategoryTheory
