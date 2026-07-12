import Mathlib
import StacksProject_2024.Chap12.Definition_12_5_3
import StacksProject_2024.Chap13.Definition_13_15_3
import StacksProject_2024.Chap13.Lemma_13_4_9
import StacksProject_2024.Chap13.Lemma_13_14_15
import StacksProject_2024.Chap13.Lemma_13_15_2
import StacksProject_2024.Chap13.Lemma_13_15_4
import StacksProject_2024.Chap13.Lemma_13_15_5
import StacksProject_2024.Chap13.Lemma_13_15_6
import StacksProject_2024.Chap13.Lemma_13_16_5
import StacksProject_2024.Chap13.Lemma_13_16_7_Leray_s_acyclicity_lemma

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.ObjectProperty
open ComplexShape
open scoped CategoryTheory

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory

section

variable {𝒜 : Type u₁} {ℬ : Type u₂}
  [Category.{v₁} 𝒜] [Category.{v₂} ℬ]
  [Abelian 𝒜] [Abelian ℬ] [HasDerivedCategory.{w} ℬ]
  (F : 𝒜 ⥤ ℬ) [F.Additive]

local notation "QisPlus" => boundedBelowHomotopyQuasiIso 𝒜
local notation "QisMinus" => boundedAboveHomotopyQuasiIso 𝒜
local notation "KplusToDplus" => mapBoundedBelowHomotopyCategoryToDerivedBelow F
local notation "KminusToDminus" => mapBoundedAboveHomotopyCategoryToDerivedAbove F

/- Domain-style sampling for Proposition 13.16.8:
- primary domain: bounded-below / bounded-above derived-functor existence and computation from
  acyclic resolutions in an abelian category;
- sampled owner declarations:
  `IsBoundedBelowRightAcyclicForAdditiveFunctor`,
  `IsTermwiseBoundedBelowRightAcyclicForAdditiveFunctor`,
  `IsBoundedAboveLeftAcyclicForAdditiveFunctor`,
  `IsTermwiseBoundedAboveLeftAcyclicForAdditiveFunctor`,
  `ObjectProperty.HasMonoEmbedding`,
  `ObjectProperty.HasEpiCover`;
- best owner abstraction: Proposition `13.16.8` is source-facing and bounded. Its acyclicity
  hypotheses should therefore be organized around the Chapter `13` owners
  `IsBoundedBelowRightAcyclicForAdditiveFunctor F`,
  `IsTermwiseBoundedBelowRightAcyclicForAdditiveFunctor F`,
  `IsBoundedAboveLeftAcyclicForAdditiveFunctor F`, and
  `IsTermwiseBoundedAboveLeftAcyclicForAdditiveFunctor F`, while the mono/epi reachability
  hypotheses are canonically owned by `ObjectProperty.HasMonoEmbedding` and
  `ObjectProperty.HasEpiCover`;
- primitive data: the additive functor `F` and the bounded mono/epi reachability owners for those
  bounded acyclicity predicates;
- derived API: pointwise and total bounded derived-functor existence, plus the computation
  theorems for termwise bounded-acyclic complexes.

Source/core/bridge triage:
- `source-facing`: the four bounded derived-functor existence statements and the two computation
  statements below;
- `core/canonical`: `IsBoundedBelowRightAcyclicForAdditiveFunctor`,
  `IsTermwiseBoundedBelowRightAcyclicForAdditiveFunctor`,
  `IsBoundedAboveLeftAcyclicForAdditiveFunctor`,
  `IsTermwiseBoundedAboveLeftAcyclicForAdditiveFunctor`,
  `ObjectProperty.HasMonoEmbedding`, and `ObjectProperty.HasEpiCover`;
- `bridge/view`: the bounded/unbounded comparison lemmas from `13.15.2`, which remain stronger
  companion transport API rather than the main public surface here.
-/

section Right

local notation "BoundedBelowRightAcyclic" =>
  (fun A : 𝒜 ↦ IsBoundedBelowRightAcyclicForAdditiveFunctor F A)

/-- Helper for Proposition 13.16.8: the canonical bounded-below localization
`K^+(\mathcal B) ⟶ D^+(\mathcal B)` inverts bounded-below quasi-isomorphisms. -/
private theorem mapBoundedBelowHomotopyToDerivedBelow_map_isIso
    {X Y : K⁺(ℬ)} (f : X ⟶ Y) (hf : boundedBelowHomotopyQuasiIso ℬ f) :
    IsIso (mapBoundedBelowHomotopyToDerivedBelow.map f) := by
  let ιplus : D⁺(ℬ) ⥤ D(ℬ) := ObjectProperty.ι (DerivedCategory.TStructure.t.plus)
  have hUnderlying :
      IsIso (((HomotopyCategory.plus ℬ).ι ⋙ DerivedCategory.Qh).map f) := by
    -- Proof comment: after forgetting to the ambient homotopy category, this is the ordinary
    -- derived localization, which inverts quasi-isomorphisms by definition.
    change IsIso (DerivedCategory.Qh.map ((HomotopyCategory.plus ℬ).ι.map f))
    exact Localization.inverts
      (DerivedCategory.Qh : K(ℬ) ⥤ D(ℬ))
      (HomotopyCategory.quasiIso ℬ (up ℤ))
      ((HomotopyCategory.plus ℬ).ι.map f)
      (by simpa [boundedBelowHomotopyQuasiIso] using hf)
  have hLifted :
      IsIso (ιplus.map (mapBoundedBelowHomotopyToDerivedBelow.map f)) := by
    -- Proof comment: compare the bounded-below quotient with the ambient derived quotient
    -- through the standard inclusion `D⁺(\mathcal B) ↪ D(\mathcal B)`.
    exact
      ((NatIso.isIso_map_iff
        (ObjectProperty.liftCompιIso
          (DerivedCategory.TStructure.t.plus : ObjectProperty (D(ℬ)))
          ((HomotopyCategory.plus ℬ).ι ⋙ DerivedCategory.Qh)
          (fun K ↦ by simpa using qh_obj_mem_t_plus K))
        f)).2 hUnderlying
  let _ : IsIso (ιplus.map (mapBoundedBelowHomotopyToDerivedBelow.map f)) := hLifted
  exact isIso_of_fully_faithful ιplus (mapBoundedBelowHomotopyToDerivedBelow.map f)

/-- Helper for Proposition 13.16.8: if the image of a bounded-below morphism under
`mapBoundedBelowHomotopyCategory F` is a bounded-below quasi-isomorphism, then its image under
`KplusToDplus` is invertible. -/
private theorem isIso_KplusToDplus_map_of_mapped_boundedBelow_quasiIso
    {X Y : K⁺(𝒜)} (s : X ⟶ Y)
    (hs :
      boundedBelowHomotopyQuasiIso ℬ
        ((mapBoundedBelowHomotopyCategory F).map s)) :
    IsIso (KplusToDplus.map s) := by
  -- Proof comment: `KplusToDplus` is the composite
  -- `K^+(\mathcal A) ⟶ K^+(\mathcal B) ⟶ D^+(\mathcal B)`, so the previous localization helper
  -- applies directly to the mapped morphism.
  change
    IsIso
      (mapBoundedBelowHomotopyToDerivedBelow.map
        ((mapBoundedBelowHomotopyCategory F).map s))
  exact mapBoundedBelowHomotopyToDerivedBelow_map_isIso (f := _ ) hs

/-- Helper for Proposition 13.16.8: the cone of a map between bounded-below complexes is again
bounded below. -/
private theorem mappingCone_boundedBelow
    {X Y : K⁺(𝒜)} (f : X.obj.as ⟶ Y.obj.as) :
    CochainComplex.plus 𝒜 (mappingCone f) := by
  -- Proof comment: propagate lower support bounds on the two source complexes through the
  -- explicit description of the mapping-cone terms.
  obtain ⟨n₁, hn₁⟩ : CochainComplex.plus 𝒜 X.obj.as := by
    simpa [HomotopyCategory.plus] using X.property
  obtain ⟨n₂, hn₂⟩ : CochainComplex.plus 𝒜 Y.obj.as := by
    simpa [HomotopyCategory.plus] using Y.property
  refine ⟨min (n₁ - 1) n₂, ?_⟩
  let K : CochainComplex 𝒜 ℤ := X.obj.as
  let L : CochainComplex 𝒜 ℤ := Y.obj.as
  let _ : K.IsStrictlyGE n₁ := by
    simpa [K] using hn₁
  let _ : L.IsStrictlyGE n₂ := by
    simpa [L] using hn₂
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  have hi₁ : i + 1 < n₁ := by
    have : i < n₁ - 1 := lt_of_lt_of_le hi (min_le_left _ _)
    linarith
  have hi₂ : i < n₂ := by
    exact lt_of_lt_of_le hi (min_le_right _ _)
  simp only [mappingCone.isZero_X_iff]
  exact ⟨K.isZero_of_isStrictlyGE n₁ _ hi₁, L.isZero_of_isStrictlyGE n₂ _ hi₂⟩

/-- Helper for Proposition 13.16.8: an acyclic cochain-level mapping cone yields a
quasi-isomorphism. -/
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
    -- Proof comment: the standard cone triangle turns acyclicity of the cone into the
    -- `trW`-criterion for quasi-isomorphisms.
    simpa [HomotopyCategory.quasiIso_eq_subcategoryAcyclic_W (C := 𝒜)] using
      ((HomotopyCategory.subcategoryAcyclic 𝒜).trW_iff_of_distinguished
        (CochainComplex.mappingCone.triangleh f)
        (HomotopyCategory.mappingCone_triangleh_distinguished f)).2 hmem
  exact (HomotopyCategory.quotient_map_mem_quasiIso_iff (C := 𝒜) (c := up ℤ) f).1 hq

/-- Helper for Proposition 13.16.8: a quasi-isomorphism has acyclic cochain-level mapping
cone. -/
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
    -- Proof comment: read the cone object as the third vertex in the standard distinguished
    -- triangle attached to `f`.
    exact
      ((HomotopyCategory.subcategoryAcyclic 𝒜).trW_iff_of_distinguished
        (CochainComplex.mappingCone.triangleh f)
        (HomotopyCategory.mappingCone_triangleh_distinguished f)).1
        (by simpa [HomotopyCategory.quasiIso_eq_subcategoryAcyclic_W (C := 𝒜)] using hq)
  exact
    (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic
      (C := 𝒜) (mappingCone f)).1 hmem

/-- Helper for Proposition 13.16.8: any morphism in `QisPlus` between bounded-below objects that
already compute the bounded-below right derived functor is inverted by `KplusToDplus`. -/
private theorem map_isIso_of_computesRightDerivedAt
    {X X' : K⁺(𝒜)} (s : X ⟶ X')
    (hs : QisPlus s)
    (hX : Functor.ComputesRightDerivedAt KplusToDplus QisPlus X)
    (hX' : Functor.ComputesRightDerivedAt KplusToDplus QisPlus X') :
    IsIso (KplusToDplus.map s) := by
  let η := (KplusToDplus).totalRightDerivedUnit QisPlus.Q QisPlus
  have hηX :
      IsIso (η.app X) := by
    exact
      (Functor.computesRightDerivedAt_iff
        (F := KplusToDplus) (S := QisPlus) (X := X)).1 hX
  have hηX' :
      IsIso (η.app X') := by
    exact
      (Functor.computesRightDerivedAt_iff
        (F := KplusToDplus) (S := QisPlus) (X := X')).1 hX'
  have htotal :
      IsIso (((KplusToDplus).totalRightDerived QisPlus.Q QisPlus).map (QisPlus.Q.map s)) := by
    exact Functor.totalRightDerived_map_isIso_of_mem (S := QisPlus) (F := KplusToDplus) s hs
  let _ : IsIso (η.app X) := hηX
  let _ : IsIso (η.app X') := hηX'
  let _ : IsIso (((KplusToDplus).totalRightDerived QisPlus.Q QisPlus).map (QisPlus.Q.map s)) :=
    htotal
  have hcomp : IsIso (KplusToDplus.map s ≫ η.app X') := by
    -- Proof comment: naturality of the total right-derived unit compares the source map with the
    -- already-invertible map on derived values.
    rw [NatTrans.naturality η s]
    infer_instance
  exact
    (isIso_comp_right_iff
      (KplusToDplus.map s)
      (η.app X')).1 hcomp

/-- Helper for Proposition 13.16.8: the zero object is bounded-below right acyclic. -/
private theorem isBoundedBelowRightAcyclic_zero :
    IsBoundedBelowRightAcyclicForAdditiveFunctor F (0 : 𝒜) := by
  -- Proof comment: transport the unbounded zero-object computation statement back to the
  -- bounded-below degree-zero owner via the comparison theorem of Lemma `13.16.4`.
  exact
    (isRightAcyclicForAdditiveFunctor_iff_isBoundedBelowRightAcyclic
      (F := F) (0 : 𝒜)).1
      (isRightAcyclicForAdditiveFunctor_zero (F := F))

/-- Helper for Proposition 13.16.8: the bounded-below right-acyclic owner contains the zero
object. -/
local instance boundedBelowRightAcyclic_containsZero :
    BoundedBelowRightAcyclic.ContainsZero where
  exists_zero := ⟨0, isZero_zero 𝒜, isBoundedBelowRightAcyclic_zero (F := F)⟩

/-- Helper for Proposition 13.16.8: cone terms inherit termwise bounded-below right acyclicity
from the source and target complexes. -/
private theorem mappingCone_termwise_boundedBelowRightAcyclic
    {K L : CochainComplex 𝒜 ℤ} (f : K ⟶ L)
    (hK : ∀ i : ℤ, BoundedBelowRightAcyclic (K.X i))
    (hL : ∀ i : ℤ, BoundedBelowRightAcyclic (L.X i)) :
    ∀ i : ℤ, BoundedBelowRightAcyclic ((mappingCone f).X i) := by
  intro i
  -- Proof comment: each cone term is canonically the biproduct of two adjacent source terms.
  let _ : ∀ p : ℤ, Limits.HasBinaryBiproduct (K.X (p + 1)) (L.X p) := fun p ↦ inferInstance
  let _ : HomologicalComplex.HasHomotopyCofiber f :=
    mappingCone_hasHomotopyCofiber (f := f)
  let e : (mappingCone f).X i ≅ K.X (i + 1) ⊞ L.X i :=
    HomologicalComplex.homotopyCofiber.XIsoBiprod f i (i + 1)
      (ComplexShape.up_mk i (i + 1) rfl)
  exact
    BoundedBelowRightAcyclic.prop_of_iso e
      (BoundedBelowRightAcyclic.prop_biprod (hK (i + 1)) (hL i))

/-- Helper for Proposition 13.16.8: after forgetting the bounded-below restriction, the image of
`s` under `mapBoundedBelowHomotopyCategory F` is the ordinary homotopy-category image of the
underlying morphism. -/
private theorem mapBoundedBelowHomotopyCategory_map_eq
    {X Y : K⁺(𝒜)} (s : X ⟶ Y) :
    ((HomotopyCategory.plus ℬ).ι.map ((mapBoundedBelowHomotopyCategory F).map s)) =
      ((F.mapHomotopyCategory (up ℤ)).map ((HomotopyCategory.plus 𝒜).ι.map s)) := by
  -- Proof comment: the bounded-below functor is the restriction of the ambient homotopy functor.
  simp [mapBoundedBelowHomotopyCategory]

/-- Helper for Proposition 13.16.8: the representative chain map of a bounded-below
quasi-isomorphism is itself a quasi-isomorphism. -/
private theorem quasiIso_out_of_boundedBelow_quasiIso
    {X Y : K⁺(𝒜)} (s : X ⟶ Y) (hs : QisPlus s) :
    QuasiIso (((HomotopyCategory.plus 𝒜).ι.map s).out) := by
  have hsAmbient :
      HomotopyCategory.quasiIso 𝒜 (up ℤ) ((HomotopyCategory.plus 𝒜).ι.map s) := hs
  -- Proof comment: replace the bounded-below morphism by its cochain-level representative.
  rw [← HomotopyCategory.quotient_map_out ((HomotopyCategory.plus 𝒜).ι.map s),
    HomotopyCategory.quotient_map_mem_quasiIso_iff] at hsAmbient
  exact hsAmbient

/-- Helper for Proposition 13.16.8: precomposing with an epimorphism does not change the image
subobject. -/
private theorem imageSubobject_comp_eq_of_epi {X Y Z : ℬ}
    (f : X ⟶ Y) [Epi f] (g : Y ⟶ Z) :
    imageSubobject (f ≫ g) = imageSubobject g := by
  -- Proof comment: the canonical comparison from the image of `f ≫ g` to the image of `g` is
  -- both mono and epi, hence an isomorphism of subobjects.
  have hle : imageSubobject (f ≫ g) ≤ imageSubobject g :=
    imageSubobject_comp_le f g
  haveI : Epi (Subobject.ofLE _ _ hle) :=
    imageSubobject_comp_le_epi_of_epi f g
  haveI : IsIso (Subobject.ofLE _ _ hle) :=
    isIso_of_mono_of_epi (Subobject.ofLE _ _ hle)
  refine Subobject.eq_of_comm (asIso (Subobject.ofLE _ _ hle)) ?_
  simp

/-- Helper for Proposition 13.16.8: the image-factor row
`im(dⁿ) ⟶ Iⁿ⁺¹ ⟶ im(dⁿ⁺¹)` is a short complex. -/
private theorem imageFactorShortComplex_comp_zero
    (I : CochainComplex 𝒜 ℤ) (n : ℤ) :
    image.ι (I.d n (n + 1)) ≫ factorThruImage (I.d (n + 1) (n + 2)) = 0 := by
  -- Proof comment: after postcomposing with the next image inclusion, this becomes `d² = 0`.
  apply (cancel_mono (image.ι (I.d (n + 1) (n + 2)))).1
  simpa [Category.assoc, image.fac] using I.d_comp_d n (n + 1) (n + 2)

/-- Helper for Proposition 13.16.8: the textbook row
`im(dⁿ) ⟶ Iⁿ⁺¹ ⟶ im(dⁿ⁺¹)` as a short complex. -/
private def imageFactorShortComplex
    (I : CochainComplex 𝒜 ℤ) (n : ℤ) : ShortComplex 𝒜 :=
  ShortComplex.mk
    (image.ι (I.d n (n + 1)))
    (factorThruImage (I.d (n + 1) (n + 2)))
    (imageFactorShortComplex_comp_zero I n)

/-- Helper for Proposition 13.16.8: the pair
`Iⁿ ⟶ Iⁿ⁺¹ ⟶ im(dⁿ⁺¹)` is exact whenever `I` is exact at degree `n + 1`. -/
private theorem exact_to_next_image_of_exactAt
    (I : CochainComplex 𝒜 ℤ) (n : ℤ)
    (hExactAt : I.ExactAt (n + 1)) :
    (ShortComplex.mk
      (I.d n (n + 1))
      (factorThruImage (I.d (n + 1) (n + 2)))
      (by
        apply (cancel_mono (image.ι (I.d (n + 1) (n + 2)))).1
        simpa [Category.assoc, image.fac] using I.d_comp_d n (n + 1) (n + 2))).Exact := by
  let S : ShortComplex 𝒜 :=
    ShortComplex.mk (I.d n (n + 1)) (I.d (n + 1) (n + 2)) (I.d_comp_d n (n + 1) (n + 2))
  let T : ShortComplex 𝒜 :=
    ShortComplex.mk
      (I.d n (n + 1))
      (factorThruImage (I.d (n + 1) (n + 2)))
      (by
        apply (cancel_mono (image.ι (I.d (n + 1) (n + 2)))).1
        simpa [Category.assoc, image.fac] using I.d_comp_d n (n + 1) (n + 2))
  have hS : S.Exact := by
    -- Proof comment: exactness at degree `n + 1` is exactly exactness of the row of consecutive
    -- differentials.
    simpa [S, HomologicalComplex.exactAt_iff] using hExactAt
  have hImageEqKernel :
      imageSubobject T.f = kernelSubobject T.g := by
    -- Proof comment: the kernel of `factorThruImage dⁿ⁺¹` agrees with the kernel of `dⁿ⁺¹`
    -- because the image inclusion is mono.
    calc
      imageSubobject T.f = kernelSubobject (I.d (n + 1) (n + 2)) := by
        simpa [S, T] using (ShortComplex.exact_iff_image_eq_kernel (S := S)).1 hS
      _ = kernelSubobject T.g := by
        symm
        simpa [T, image.fac, Category.assoc] using
          (Limits.kernelSubobject_comp_mono
            (factorThruImage (I.d (n + 1) (n + 2)))
            (image.ι (I.d (n + 1) (n + 2))))
  exact (ShortComplex.exact_iff_image_eq_kernel (S := T)).2 hImageEqKernel

/-- Helper for Proposition 13.16.8: acyclicity of `I` packages the textbook short exact row
`0 ⟶ im(dⁿ) ⟶ Iⁿ⁺¹ ⟶ im(dⁿ⁺¹) ⟶ 0`. -/
private theorem acyclic_image_shortExact_succ
    (I : CochainComplex 𝒜 ℤ) (hIacyclic : I.Acyclic) (n : ℤ) :
    (imageFactorShortComplex I n).ShortExact := by
  have hExactAt : I.ExactAt (n + 1) := by
    -- Proof comment: acyclicity is exactness at every degree.
    rw [← HomologicalComplex.exactAt_iff_isZero_homology]
    exact hIacyclic (n + 1)
  have hExact :
      (ShortComplex.mk
        (I.d n (n + 1))
        (factorThruImage (I.d (n + 1) (n + 2)))
        (by
          apply (cancel_mono (image.ι (I.d (n + 1) (n + 2)))).1
          simpa [Category.assoc, image.fac] using I.d_comp_d n (n + 1) (n + 2))).Exact :=
    exact_to_next_image_of_exactAt I n hExactAt
  have hImageExact : (imageFactorShortComplex I n).Exact := by
    -- Proof comment: replace the left map by the canonical image inclusion.
    simpa [imageFactorShortComplex] using
      (ShortComplex.exact_iff_exact_image_ι
        (ShortComplex.mk
          (I.d n (n + 1))
          (factorThruImage (I.d (n + 1) (n + 2)))
          (by
            apply (cancel_mono (image.ι (I.d (n + 1) (n + 2)))).1
            simpa [Category.assoc, image.fac] using I.d_comp_d n (n + 1) (n + 2)))).1
        hExact
  exact ShortComplex.ShortExact.mk' hImageExact inferInstance inferInstance

/-- Helper for Proposition 13.16.8: one source-proof induction step on the image objects
`Jⁿ = im(dⁿ)`. -/
private theorem boundedBelowRightAcyclic_image_step
    (I : CochainComplex 𝒜 ℤ) (hIacyclic : I.Acyclic)
    (hTerms : ∀ n : ℤ, BoundedBelowRightAcyclic (I.X n))
    (n : ℤ)
    (hImage : BoundedBelowRightAcyclic (image (I.d n (n + 1)))) :
    BoundedBelowRightAcyclic (image (I.d (n + 1) (n + 2))) ∧
      ((imageFactorShortComplex I n).map F).ShortExact := by
  let S := imageFactorShortComplex I n
  have hS : S.ShortExact :=
    acyclic_image_shortExact_succ I hIacyclic n
  have hImageSucc :
      BoundedBelowRightAcyclic (image (I.d (n + 1) (n + 2))) := by
    -- Proof comment: the short exact row
    -- `0 ⟶ im(dⁿ) ⟶ Iⁿ⁺¹ ⟶ im(dⁿ⁺¹) ⟶ 0`
    -- is exactly the cokernel case of Lemma `13.16.5`.
    simpa [S, imageFactorShortComplex] using
      isBoundedBelowRightAcyclicForAdditiveFunctor_cokernel_of_shortExact
        (F := F) hS hImage (hTerms (n + 1))
  have hMappedShortExact : (S.map F).ShortExact := by
    -- Proof comment: once the left and middle terms are bounded-below right acyclic, the same
    -- chapter API gives short exactness after applying `F`.
    exact
      map_shortExact_of_isBoundedBelowRightAcyclicForAdditiveFunctor_left_middle
        (F := F) hS hImage (hTerms (n + 1))
  simpa [S] using And.intro hImageSucc hMappedShortExact

/-- Helper for Proposition 13.16.8: a mapped textbook row supplies the surjectivity of the
middle-to-image map needed in the source induction. -/
private theorem epi_map_factorThruImage_of_mapped_image_row
    (I : CochainComplex 𝒜 ℤ) (n : ℤ)
    (hRow : ((imageFactorShortComplex I n).map F).ShortExact) :
    Epi (F.map (factorThruImage (I.d (n + 1) (n + 2)))) := by
  -- Proof comment: this is exactly the right exactness component of the mapped short exact row
  -- `0 → F(Jⁿ) → F(Iⁿ⁺¹) → F(Jⁿ⁺¹) → 0`.
  simpa [imageFactorShortComplex] using hRow.epi_g

/-- Helper for Proposition 13.16.8: three consecutive mapped image rows recover exactness of the
mapped complex at the middle degree. -/
private theorem exactAt_map_of_three_mapped_image_rows
    (I : CochainComplex 𝒜 ℤ) (n : ℤ)
    (hPrev : ((imageFactorShortComplex I (n - 1)).map F).ShortExact)
    (hCurr : ((imageFactorShortComplex I n).map F).ShortExact)
    (hNext : ((imageFactorShortComplex I (n + 1)).map F).ShortExact) :
    (((F.mapHomologicalComplex (up ℤ)).obj I).ExactAt (n + 1)) := by
  let U : ShortComplex ℬ := (imageFactorShortComplex I n).map F
  let W : ShortComplex ℬ :=
    ShortComplex.mk
      (F.map (I.d n (n + 1)))
      (F.map (factorThruImage (I.d (n + 1) (n + 2))))
      (by
        -- Proof comment: factor the differential through the image row and then use `d² = 0`.
        rw [← F.map_comp]
        have hcomp :
            I.d n (n + 1) ≫ factorThruImage (I.d (n + 1) (n + 2)) = 0 := by
          calc
            I.d n (n + 1) ≫ factorThruImage (I.d (n + 1) (n + 2)) =
                factorThruImage (I.d n (n + 1)) ≫
                  (image.ι (I.d n (n + 1)) ≫ factorThruImage (I.d (n + 1) (n + 2))) := by
                    simp [Category.assoc, image.fac]
            _ = 0 := by
              simp [imageFactorShortComplex_comp_zero, Category.assoc]
        simpa using congrArg F.map hcomp)
  let D : ShortComplex ℬ :=
    ShortComplex.mk
      (F.map (I.d n (n + 1)))
      (F.map (I.d (n + 1) (n + 2)))
      (by
        -- Proof comment: this is the actual row of consecutive mapped differentials.
        simpa [Functor.map_comp] using congrArg F.map (I.d_comp_d n (n + 1) (n + 2)))
  let φ : W ⟶ U :=
    { τ₁ := F.map (factorThruImage (I.d n (n + 1)))
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      comm₁₂ := by
        simp [W, U, imageFactorShortComplex, Functor.map_comp, Category.assoc, image.fac]
      comm₂₃ := by
        simp [W, U, imageFactorShortComplex] }
  have hUExact : U.Exact := by
    -- Proof comment: the current mapped image row is already short exact by the source induction.
    simpa [U] using hCurr.exact
  haveI : Epi (F.map (factorThruImage (I.d n (n + 1)))) :=
    epi_map_factorThruImage_of_mapped_image_row (F := F) I (n - 1) hPrev
  have hWExact : W.Exact := by
    -- Proof comment: predecessor surjectivity upgrades the current image row to the row whose
    -- left map is the actual mapped differential.
    exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).2 hUExact
  let ψ : W ⟶ D :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := F.map (image.ι (I.d (n + 1) (n + 2)))
      comm₁₂ := by
        simp [W, D]
      comm₂₃ := by
        simp [W, D, Functor.map_comp, Category.assoc, image.fac] }
  haveI : Mono (F.map (image.ι (I.d (n + 1) (n + 2)))) := by
    -- Proof comment: the next mapped image row supplies the monomorphism into degree `n + 2`.
    simpa [imageFactorShortComplex] using hNext.mono_f
  have hDExact : D.Exact := by
    -- Proof comment: postcomposing with that mono upgrades exactness to the actual differential
    -- row of the mapped complex.
    exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono ψ).1 hWExact
  simpa [D, HomologicalComplex.exactAt_iff] using hDExact

/-- Helper for Proposition 13.16.8: the first mapped image row together with the vanishing term
below the support bound gives exactness at the initial nonzero degree. -/
private theorem exactAt_map_of_initial_mapped_image_row
    (I : CochainComplex 𝒜 ℤ) (n0 : ℤ) (hIge : I.IsStrictlyGE n0)
    (hStart : ((imageFactorShortComplex I (n0 - 1)).map F).ShortExact)
    (hNext : ((imageFactorShortComplex I n0).map F).ShortExact) :
    (((F.mapHomologicalComplex (up ℤ)).obj I).ExactAt n0) := by
  have hzeroPrev : IsZero (I.X (n0 - 1)) :=
    hIge.isZero_of_isStrictlyGE n0 (n0 - 1) (by omega)
  have hImagePrevZero : IsZero (image (I.d (n0 - 1) n0)) := by
    -- Proof comment: the initial image object is zero because it is the image of a map out of a
    -- zero term.
    let _ : Epi (factorThruImage (I.d (n0 - 1) n0)) := inferInstance
    exact IsZero.of_epi (factorThruImage (I.d (n0 - 1) n0)) hzeroPrev
  let U : ShortComplex ℬ := (imageFactorShortComplex I (n0 - 1)).map F
  let W : ShortComplex ℬ :=
    ShortComplex.mk
      (F.map (I.d (n0 - 1) n0))
      (F.map (factorThruImage (I.d n0 (n0 + 1))))
      (by
        -- Proof comment: this is the same source row as above, now started at the support bound.
        rw [← F.map_comp]
        have hcomp :
            I.d (n0 - 1) n0 ≫ factorThruImage (I.d n0 (n0 + 1)) = 0 := by
          calc
            I.d (n0 - 1) n0 ≫ factorThruImage (I.d n0 (n0 + 1)) =
                factorThruImage (I.d (n0 - 1) n0) ≫
                  (image.ι (I.d (n0 - 1) n0) ≫ factorThruImage (I.d n0 (n0 + 1))) := by
                    simp [Category.assoc, image.fac]
            _ = 0 := by
              simp [imageFactorShortComplex_comp_zero, Category.assoc]
        simpa using congrArg F.map hcomp)
  let D : ShortComplex ℬ :=
    ShortComplex.mk
      (F.map (I.d (n0 - 1) n0))
      (F.map (I.d n0 (n0 + 1)))
      (by
        -- Proof comment: this is the actual mapped differential row at degree `n0`.
        simpa [Functor.map_comp] using congrArg F.map (I.d_comp_d (n0 - 1) n0 (n0 + 1)))
  let φ : W ⟶ U :=
    { τ₁ := F.map (factorThruImage (I.d (n0 - 1) n0))
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      comm₁₂ := by
        simp [W, U, imageFactorShortComplex, Functor.map_comp, Category.assoc, image.fac]
      comm₂₃ := by
        simp [W, U, imageFactorShortComplex] }
  have hUExact : U.Exact := by
    -- Proof comment: the starting mapped image row is already short exact.
    simpa [U] using hStart.exact
  haveI : IsZero (F.obj (image (I.d (n0 - 1) n0))) := F.map_isZero hImagePrevZero
  haveI : Epi (F.map (factorThruImage (I.d (n0 - 1) n0))) := by
    -- Proof comment: the map lands in a zero object, so it is automatically epi.
    infer_instance
  have hWExact : W.Exact := by
    -- Proof comment: at the initial degree, the zero incoming image plays the role of the
    -- predecessor surjectivity.
    exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).2 hUExact
  let ψ : W ⟶ D :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := F.map (image.ι (I.d n0 (n0 + 1)))
      comm₁₂ := by
        simp [W, D]
      comm₂₃ := by
        simp [W, D, Functor.map_comp, Category.assoc, image.fac] }
  haveI : Mono (F.map (image.ι (I.d n0 (n0 + 1)))) := by
    -- Proof comment: the next mapped image row provides the needed monomorphism.
    simpa [imageFactorShortComplex] using hNext.mono_f
  have hDExact : D.Exact := by
    -- Proof comment: this upgrades the factor-through-image row to the actual mapped
    -- differential row at degree `n0`.
    exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono ψ).1 hWExact
  simpa [D, HomologicalComplex.exactAt_iff] using hDExact

/-- Helper for Proposition 13.16.8: the source proof reduces acyclicity of `F(I)` to the image
induction on `Jⁿ = im(dⁿ)` for an acyclic bounded-below complex `I`. -/
private theorem map_acyclic_of_acyclic_boundedBelow_rightAcyclic_terms
    (I : CochainComplex 𝒜 ℤ) (hIplus : CochainComplex.plus 𝒜 I)
    (hIacyclic : I.Acyclic)
    (hTerms : ∀ n : ℤ, BoundedBelowRightAcyclic (I.X n)) :
    ((F.mapHomologicalComplex (up ℤ)).obj I).Acyclic := by
  obtain ⟨n0, hIge⟩ := (CochainComplex.plus_iff 𝒜 I).1 hIplus
  have hImageBase : BoundedBelowRightAcyclic (image (I.d (n0 - 1) n0)) := by
    have hzeroPrev : IsZero (I.X (n0 - 1)) :=
      hIge.isZero_of_isStrictlyGE n0 (n0 - 1) (by omega)
    have hImagePrevZero : IsZero (image (I.d (n0 - 1) n0)) := by
      -- Proof comment: the initial image object is zero because the complex vanishes below `n0`.
      let _ : Epi (factorThruImage (I.d (n0 - 1) n0)) := inferInstance
      exact IsZero.of_epi (factorThruImage (I.d (n0 - 1) n0)) hzeroPrev
    exact
      BoundedBelowRightAcyclic.prop_of_iso hImagePrevZero.isoZero
        (isBoundedBelowRightAcyclic_zero (F := F))
  have hRowsAndImages :
      ∀ k : ℕ,
        BoundedBelowRightAcyclic (image (I.d (n0 + k) (n0 + k + 1))) ∧
          ((imageFactorShortComplex I (n0 - 1 + k)).map F).ShortExact := by
    intro k
    induction k with
    | zero =>
        -- Proof comment: start the source-proof induction at the first nonzero degree.
        simpa using
          boundedBelowRightAcyclic_image_step
            (F := F) I hIacyclic hTerms (n0 - 1) hImageBase
    | succ k ih =>
        -- Proof comment: one more application of the image-step lemma advances both the image
        -- object and the mapped short exact row.
        have hstep :=
          boundedBelowRightAcyclic_image_step
            (F := F) I hIacyclic hTerms (n0 + k) ih.1
        simpa [show n0 - 1 + (Nat.succ k : ℕ) = n0 + k by omega,
          show n0 + (Nat.succ k : ℕ) = n0 + k + 1 by omega] using hstep
  have hRow :
      ∀ k : ℕ, ((imageFactorShortComplex I (n0 - 1 + k)).map F).ShortExact := fun k ↦
        (hRowsAndImages k).2
  intro j
  by_cases hj : j < n0
  · -- Proof comment: below the support bound, the mapped complex already has zero middle term.
    rw [← HomologicalComplex.exactAt_iff_isZero_homology]
    have hzero : IsZero (((F.mapHomologicalComplex (up ℤ)).obj I).X j) := by
      simpa [Functor.mapHomologicalComplex_obj_X] using
        F.map_isZero (hIge.isZero_of_isStrictlyGE n0 j hj)
    simpa [HomologicalComplex.homology] using
      (ShortComplex.isZero_homology_of_isZero_X₂
        (((F.mapHomologicalComplex (up ℤ)).obj I).sc' (j - 1) j (j + 1)) hzero)
  · -- Proof comment: from the support bound onward, use the reconstructed mapped image rows.
    have hj' : n0 ≤ j := by omega
    let k : ℕ := Int.toNat (j - n0)
    have hk : j = n0 + k := by
      have hnonneg : 0 ≤ j - n0 := by omega
      rw [show ((k : ℤ)) = j - n0 by
        simp [k, hnonneg, Int.toNat_of_nonneg]]
      omega
    rw [hk, ← HomologicalComplex.exactAt_iff_isZero_homology]
    cases k with
    | zero =>
        -- Proof comment: the first nonzero degree uses the base image row and the next one.
        simpa using
          exactAt_map_of_initial_mapped_image_row
            (F := F) I n0 hIge (hRow 0) (hRow 1)
    | succ k =>
        -- Proof comment: every later degree is controlled by three consecutive mapped image rows.
        simpa [show n0 + (Nat.succ k : ℕ) = n0 + k + 1 by omega] using
          exactAt_map_of_three_mapped_image_rows
            (F := F) I (n0 + k) (hRow k) (hRow (k + 1)) (hRow (k + 2))

/-- Helper for Proposition 13.16.8: if a bounded-below chain map is a quasi-isomorphism and both
endpoint complexes are termwise bounded-below right acyclic, then its image under `F` is again a
quasi-isomorphism. -/
private theorem mapped_quasiIso_of_termwise_boundedBelowRightAcyclic
    {K L : CochainComplex 𝒜 ℤ} (f : K ⟶ L)
    (hKplus : CochainComplex.plus 𝒜 K)
    (hLplus : CochainComplex.plus 𝒜 L)
    (hK : ∀ i : ℤ, BoundedBelowRightAcyclic (K.X i))
    (hL : ∀ i : ℤ, BoundedBelowRightAcyclic (L.X i))
    (hf : QuasiIso f) :
    QuasiIso (((F.mapHomologicalComplex (up ℤ)).map f)) := by
  let Kplus : K⁺(𝒜) := (HomotopyCategory.Plus.quotient 𝒜).obj ⟨K, hKplus⟩
  let Lplus : K⁺(𝒜) := (HomotopyCategory.Plus.quotient 𝒜).obj ⟨L, hLplus⟩
  have hConePlus : CochainComplex.plus 𝒜 (mappingCone f) := by
    -- Proof comment: package the bounded-below source and target so the existing cone-boundedness
    -- theorem applies to the cochain representative `f`.
    simpa [Kplus, Lplus] using
      (mappingCone_boundedBelow (𝒜 := 𝒜) (X := Kplus) (Y := Lplus) f)
  have hConeAcyclic : (mappingCone f).Acyclic :=
    mappingCone_acyclic_of_quasiIso (𝒜 := 𝒜) f hf
  have hConeTerms :
      ∀ i : ℤ, BoundedBelowRightAcyclic ((mappingCone f).X i) :=
    mappingCone_termwise_boundedBelowRightAcyclic (F := F) f hK hL
  have hMappedConeAcyclic :
      (mappingCone (((F.mapHomologicalComplex (up ℤ)).map f))).Acyclic := by
    -- Proof comment: the mapped cone is acyclic once the source-faithful image induction is
    -- available for the acyclic bounded-below cone complex itself.
    simpa using
      map_acyclic_of_acyclic_boundedBelow_rightAcyclic_terms
        (F := F) (mappingCone f) hConePlus hConeAcyclic hConeTerms
  -- Proof comment: acyclicity of the mapped cone is exactly the cone criterion for the mapped
  -- chain map to be a quasi-isomorphism.
  exact quasiIso_of_mappingCone_acyclic (𝒜 := ℬ) (((F.mapHomologicalComplex (up ℤ)).map f))
    hMappedConeAcyclic

/-- Helper for Proposition 13.16.8: a bounded-below quasi-isomorphism between termwise bounded-
below right-acyclic complexes is sent by `F` to a bounded-below quasi-isomorphism. -/
private theorem mapped_boundedBelow_quasiIso_of_termwise_boundedBelowRightAcyclic
    {X Y : K⁺(𝒜)} (s : X ⟶ Y)
    (hX : IsTermwiseBoundedBelowRightAcyclicForAdditiveFunctor F X)
    (hY : IsTermwiseBoundedBelowRightAcyclicForAdditiveFunctor F Y)
    (hs : QisPlus s) :
    boundedBelowHomotopyQuasiIso ℬ ((mapBoundedBelowHomotopyCategory F).map s) := by
  let sAmbient : X.obj ⟶ Y.obj := (HomotopyCategory.plus 𝒜).ι.map s
  let f : X.obj.as ⟶ Y.obj.as := sAmbient.out
  have hXplus : CochainComplex.plus 𝒜 X.obj.as := by
    simpa [HomotopyCategory.plus] using X.property
  have hYplus : CochainComplex.plus 𝒜 Y.obj.as := by
    simpa [HomotopyCategory.plus] using Y.property
  have hf : QuasiIso f := by
    -- Proof comment: replace the bounded-below denominator by its chain-level representative.
    simpa [f, sAmbient] using
      quasiIso_out_of_boundedBelow_quasiIso (𝒜 := 𝒜) s hs
  have hMappedf : QuasiIso (((F.mapHomologicalComplex (up ℤ)).map f)) :=
    mapped_quasiIso_of_termwise_boundedBelowRightAcyclic
      (F := F) f hXplus hYplus hX hY hf
  change
    HomotopyCategory.quasiIso ℬ (up ℤ)
      ((HomotopyCategory.plus ℬ).ι.map ((mapBoundedBelowHomotopyCategory F).map s))
  rw [mapBoundedBelowHomotopyCategory_map_eq (F := F) s]
  rw [← HomotopyCategory.quotient_map_out
    (((F.mapHomotopyCategory (up ℤ)).map ((HomotopyCategory.plus 𝒜).ι.map s))),
    HomotopyCategory.quotient_map_mem_quasiIso_iff]
  -- Proof comment: after rewriting by `quotient_map_out`, the ambient mapped morphism is exactly
  -- the quotient of the mapped cochain representative `f`.
  simpa [f, sAmbient] using hMappedf

-- Proof sketch: resolve any bounded-below complex termwise by a quasi-isomorphic bounded-below
-- complex of bounded-below right `F`-acyclic objects using the mono-embedding hypothesis
-- degreewise and the
-- bounded-below resolution lemma. Then quasi-isomorphisms between such termwise right-acyclic
-- complexes are sent to quasi-isomorphisms, so Lemma `13.14.15` yields pointwise existence of
-- the bounded-below right derived functor at every object of `K^+(\mathcal A)`.
/-- Proposition 13.16.8: if every object of `𝒜` admits a monomorphism into an object that is
acyclic for the bounded-below right derived functor of `F`, formalized by the canonical owner
`ObjectProperty.HasMonoEmbedding BoundedBelowRightAcyclic`, then the bounded-below right derived
functor of `K^+(\mathcal A) ⥤ D^+(\mathcal B)` is everywhere defined in the canonical pointwise
sense `KplusToDplus.HasPointwiseRightDerivedFunctor QisPlus`. -/
@[stacks 05TA]
theorem boundedBelow_hasPointwiseRightDerivedFunctor_of_mono_into_boundedBelowRightAcyclic
    [HasMonoEmbedding BoundedBelowRightAcyclic] :
    Functor.HasPointwiseRightDerivedFunctor KplusToDplus QisPlus := by
  let I : ObjectProperty (K⁺(𝒜)) :=
    IsTermwiseBoundedBelowRightAcyclicForAdditiveFunctor F
  refine Functor.hasPointwiseRightDerivedFunctor_of_subset (F := KplusToDplus) (S := QisPlus) I
    ?_ ?_
  · intro X
    let K : CochainComplex 𝒜 ℤ := X.obj.as
    obtain ⟨a, hK⟩ := (CochainComplex.plus_iff 𝒜 K).1 X.property
    -- Proof comment: resolve `X` by a bounded-below quasi-isomorphic complex whose every term is
    -- bounded-below right `F`-acyclic.
    obtain ⟨Y, α, hα⟩ :=
      exists_termwiseMono_quasiIso_with_terms_in_of_isStrictlyGE
        (P := BoundedBelowRightAcyclic) a K hK
    let Xc : Comp⁺(𝒜) := ⟨K, X.property⟩
    have hXeq : (HomotopyCategory.Plus.quotient 𝒜).obj Xc = X := by
      cases X
      rfl
    let Yplus : Comp⁺(𝒜) := hα.toPlusWithTermsIn
    let X' : K⁺(𝒜) := (HomotopyCategory.Plus.quotient 𝒜).obj Yplus
    let α' : Xc ⟶ Yplus := ⟨α⟩
    let s : X ⟶ X' := by
      simpa [X', hXeq] using (HomotopyCategory.Plus.quotient 𝒜).map α'
    refine ⟨X', s, ?_, ?_⟩
    · -- Proof comment: the chosen target lies in the good subset by construction of the
      -- bounded-below replacement.
      intro n
      simpa [I, X'] using hα.toPlusWithTermsIn.term_mem n
    · -- Proof comment: the denominator remains a bounded-below quasi-isomorphism after passage to
      -- the bounded-below homotopy category.
      change HomotopyCategory.quasiIso 𝒜 (up ℤ)
        ((ObjectProperty.ι (HomotopyCategory.plus 𝒜)).map s)
      simpa [s, X', hXeq] using
        (show HomotopyCategory.quasiIso 𝒜 (up ℤ)
          (((HomotopyCategory.quotient 𝒜 (up ℤ)).map α)) by
          rw [HomotopyCategory.quotient_map_mem_quasiIso_iff]
          exact hα.quasiIso)
  · intro X Y s hX hY hs
    -- Proof comment: the remaining source-faithful step is to prove that applying `F` to the
    -- cone of `s` preserves acyclicity under the termwise bounded-below right-acyclicity
    -- hypotheses. Once that produces a mapped bounded-below quasi-isomorphism, invertibility in
    -- `D⁺(\mathcal B)` is formal.
    have hsMapped :
        boundedBelowHomotopyQuasiIso ℬ
          ((mapBoundedBelowHomotopyCategory F).map s) :=
      mapped_boundedBelow_quasiIso_of_termwise_boundedBelowRightAcyclic
        (F := F) s hX hY hs
    exact isIso_KplusToDplus_map_of_mapped_boundedBelow_quasiIso (F := F) s hsMapped

/-- Corollary: under the hypotheses of Proposition 13.16.8, the bounded-below total right
derived functor exists. -/
theorem boundedBelow_hasRightDerivedFunctor_of_mono_into_boundedBelowRightAcyclic
    [HasMonoEmbedding BoundedBelowRightAcyclic] :
    Functor.HasRightDerivedFunctor KplusToDplus QisPlus := by
  let _ : Functor.HasPointwiseRightDerivedFunctor KplusToDplus QisPlus :=
    boundedBelow_hasPointwiseRightDerivedFunctor_of_mono_into_boundedBelowRightAcyclic F
  infer_instance

-- Proof sketch: this is the bounded Leray acyclicity criterion of Lemma `13.16.7`, expressed
-- directly with the owner `IsTermwiseBoundedBelowRightAcyclicForAdditiveFunctor`.
/-- Any bounded-below complex whose terms are acyclic for the bounded-below right derived functor
computes the bounded-below right derived functor. -/
theorem computesRightDerivedFunctorAt_of_termwise_boundedBelowRightAcyclic
    [Functor.HasRightDerivedFunctor KplusToDplus QisPlus]
    (A : K⁺(𝒜))
    (hA : IsTermwiseBoundedBelowRightAcyclicForAdditiveFunctor F A) :
    Functor.ComputesRightDerivedAt KplusToDplus QisPlus A := by
  let hder : Functor.HasPointwiseRightDerivedFunctorAt KplusToDplus QisPlus A := inferInstance
  -- Proof comment: once the bounded-below right derived functor is globally defined, Lemma
  -- `13.16.7` applies directly to any termwise bounded-below right-acyclic complex.
  exact computesRightDerivedAt_of_termwise_boundedBelowRightAcyclic (F := F) A hder hA

end Right

section Left

local notation "BoundedAboveLeftAcyclic" =>
  IsBoundedAboveLeftAcyclicForAdditiveFunctor F

/-- Helper for Proposition 13.16.8: the canonical bounded-above localization
`K^-(\mathcal B) ⟶ D^-(\mathcal B)` inverts bounded-above quasi-isomorphisms. -/
private theorem mapBoundedAboveHomotopyToDerivedAbove_map_isIso
    {X Y : K⁻(ℬ)} (f : X ⟶ Y) (hf : boundedAboveHomotopyQuasiIso ℬ f) :
    IsIso (mapBoundedAboveHomotopyToDerivedAbove.map f) := by
  let ιminus : D⁻(ℬ) ⥤ D(ℬ) := ObjectProperty.ι (DerivedCategory.TStructure.t.minus)
  have hUnderlying :
      IsIso (((HomotopyCategory.minus ℬ).ι ⋙ DerivedCategory.Qh).map f) := by
    -- Proof comment: after forgetting to the ambient homotopy category, this is again the
    -- standard derived localization on `K(\mathcal B)`.
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

/-- Helper for Proposition 13.16.8: if the image of a bounded-above morphism under
`mapBoundedAboveHomotopyCategory F` is a bounded-above quasi-isomorphism, then its image under
`KminusToDminus` is invertible. -/
private theorem isIso_KminusToDminus_map_of_mapped_boundedAbove_quasiIso
    {X Y : K⁻(𝒜)} (s : X ⟶ Y)
    (hs :
      boundedAboveHomotopyQuasiIso ℬ
        ((mapBoundedAboveHomotopyCategory F).map s)) :
    IsIso (KminusToDminus.map s) := by
  -- Proof comment: the bounded-above case is identical formally to the bounded-below case.
  change
    IsIso
      (mapBoundedAboveHomotopyToDerivedAbove.map
        ((mapBoundedAboveHomotopyCategory F).map s))
  exact mapBoundedAboveHomotopyToDerivedAbove_map_isIso (f := _ ) hs

/-- Helper for Proposition 13.16.8: after forgetting the bounded-above restriction, the image of
`s` under `mapBoundedAboveHomotopyCategory F` is the ordinary homotopy-category image of the
underlying morphism. -/
private theorem mapBoundedAboveHomotopyCategory_map_eq
    {X Y : K⁻(𝒜)} (s : X ⟶ Y) :
    ((HomotopyCategory.minus ℬ).ι.map ((mapBoundedAboveHomotopyCategory F).map s)) =
      ((F.mapHomotopyCategory (up ℤ)).map ((HomotopyCategory.minus 𝒜).ι.map s)) := by
  -- Proof comment: the bounded-above functor is the restriction of the ambient homotopy functor.
  simp [mapBoundedAboveHomotopyCategory]

/-- Helper for Proposition 13.16.8: the representative chain map of a bounded-above
quasi-isomorphism is itself a quasi-isomorphism. -/
private theorem quasiIso_out_of_boundedAbove_quasiIso
    {X Y : K⁻(𝒜)} (s : X ⟶ Y) (hs : QisMinus s) :
    QuasiIso (((HomotopyCategory.minus 𝒜).ι.map s).out) := by
  have hsAmbient :
      HomotopyCategory.quasiIso 𝒜 (up ℤ) ((HomotopyCategory.minus 𝒜).ι.map s) := hs
  -- Proof comment: replace the bounded-above denominator by its cochain-level representative.
  rw [← HomotopyCategory.quotient_map_out ((HomotopyCategory.minus 𝒜).ι.map s),
    HomotopyCategory.quotient_map_mem_quasiIso_iff] at hsAmbient
  exact hsAmbient

/-- Helper for Proposition 13.16.8: the only remaining bounded-above denominator step is to show
that a quasi-isomorphism between termwise bounded-above left-acyclic complexes stays a
quasi-isomorphism after applying `F`. -/
private theorem mapped_boundedAbove_quasiIso_of_termwise_boundedAboveLeftAcyclic
    {X Y : K⁻(𝒜)} (s : X ⟶ Y)
    (hX : IsTermwiseBoundedAboveLeftAcyclicForAdditiveFunctor F X)
    (hY : IsTermwiseBoundedAboveLeftAcyclicForAdditiveFunctor F Y)
    (hs : QisMinus s) :
    boundedAboveHomotopyQuasiIso ℬ ((mapBoundedAboveHomotopyCategory F).map s) := by
  let sAmbient : X.obj ⟶ Y.obj := (HomotopyCategory.minus 𝒜).ι.map s
  let f : X.obj.as ⟶ Y.obj.as := sAmbient.out
  have hXminus : CochainComplex.minus 𝒜 X.obj.as := by
    simpa [HomotopyCategory.minus] using X.property
  have hYminus : CochainComplex.minus 𝒜 Y.obj.as := by
    simpa [HomotopyCategory.minus] using Y.property
  have hf : QuasiIso f := by
    -- Proof comment: first pass to the chain-level representative of the bounded-above
    -- denominator.
    simpa [f, sAmbient] using
      quasiIso_out_of_boundedAbove_quasiIso (𝒜 := 𝒜) s hs
  -- Route correction: the remaining source-faithful gap is the bounded-only opposite transport
  -- from termwise bounded-above left acyclicity for `F` to the finished bounded-below right
  -- acyclicity theorem for `F.op`.
  -- TODO: build the bounded-opposite transport package from the Agent C plan, apply
  -- `mapped_boundedBelow_quasiIso_of_termwise_boundedBelowRightAcyclic` to `F.op`, and transport
  -- the resulting bounded-below quasi-isomorphism back to the present bounded-above statement.
  let _ := hXminus
  let _ := hYminus
  let _ := hf
  let _ := hX
  let _ := hY
  sorry

-- Proof sketch: dualize the bounded-below argument. Use the epi-cover hypothesis by
-- bounded-above left-acyclic objects to choose bounded-above resolutions, then apply the dual
-- form of
-- Lemma `13.14.15` to obtain pointwise existence of the bounded-above left derived functor at
-- every object.
/-- If every object of `𝒜` is a quotient of an object that is acyclic for the bounded-above left
derived functor of `F`, formalized by the canonical owner
`ObjectProperty.HasEpiCover BoundedAboveLeftAcyclic`, then the bounded-above left derived
functor of `K^-(\mathcal A) ⥤ D^-(\mathcal B)` is everywhere defined in the canonical pointwise
sense `KminusToDminus.HasPointwiseLeftDerivedFunctor QisMinus`. -/
theorem boundedAbove_hasPointwiseLeftDerivedFunctor_of_epi_from_boundedAboveLeftAcyclic
    [HasEpiCover BoundedAboveLeftAcyclic] :
    Functor.HasPointwiseLeftDerivedFunctor KminusToDminus QisMinus := by
  let P : ObjectProperty (K⁻(𝒜)) :=
    IsTermwiseBoundedAboveLeftAcyclicForAdditiveFunctor F
  have hP_reaches :
      ∀ X : K⁻(𝒜), ∃ (X' : K⁻(𝒜)) (s : X' ⟶ X), P X' ∧ QisMinus s := by
    intro X
    let K : CochainComplex 𝒜 ℤ := X.obj.as
    obtain ⟨a, hK⟩ := (CochainComplex.minus_iff 𝒜 K).1 X.property
    -- Proof comment: resolve `X` by a bounded-above quasi-isomorphic complex whose every term is
    -- bounded-above left `F`-acyclic.
    obtain ⟨Y, α, hα⟩ :=
      exists_termwiseEpi_quasiIso_with_terms_in_of_isStrictlyLE
        (P := BoundedAboveLeftAcyclic) a K hK
    let Xc : Comp⁻(𝒜) := ⟨K, X.property⟩
    have hXeq : (HomotopyCategory.Minus.quotient 𝒜).obj Xc = X := by
      cases X
      rfl
    let Yminus : Comp⁻(𝒜) := hα.toMinusWithTermsIn
    let X' : K⁻(𝒜) := (HomotopyCategory.Minus.quotient 𝒜).obj Yminus
    let α' : Yminus ⟶ Xc := ⟨α⟩
    let s : X' ⟶ X := by
      simpa [X', hXeq] using (HomotopyCategory.Minus.quotient 𝒜).map α'
    refine ⟨X', s, ?_, ?_⟩
    · -- Proof comment: the chosen source lies in the good subset by construction of the
      -- bounded-above replacement.
      intro n
      simpa [P, X'] using hα.toMinusWithTermsIn.term_mem n
    · -- Proof comment: the denominator remains a bounded-above quasi-isomorphism after passage to
      -- the bounded-above homotopy category.
      change HomotopyCategory.quasiIso 𝒜 (up ℤ)
        ((ObjectProperty.ι (HomotopyCategory.minus 𝒜)).map s)
      simpa [s, X', hXeq] using
        (show HomotopyCategory.quasiIso 𝒜 (up ℤ)
          (((HomotopyCategory.quotient 𝒜 (up ℤ)).map α)) by
          rw [HomotopyCategory.quotient_map_mem_quasiIso_iff]
          exact hα.quasiIso)
  have hP_isIso :
      ∀ {X Y : K⁻(𝒜)} (s : X ⟶ Y), P X → P Y → QisMinus s →
        IsIso (KminusToDminus.map s) := by
    intro X Y s hX hY hs
    -- Proof comment: the only non-formal input is that `F` preserves quasi-isomorphisms between
    -- termwise bounded-above left-acyclic complexes.
    have hsMapped :
        boundedAboveHomotopyQuasiIso ℬ
          ((mapBoundedAboveHomotopyCategory F).map s) :=
      mapped_boundedAbove_quasiIso_of_termwise_boundedAboveLeftAcyclic
        (F := F) s hX hY hs
    exact isIso_KminusToDminus_map_of_mapped_boundedAbove_quasiIso (F := F) s hsMapped
  exact
    Functor.hasPointwiseLeftDerivedFunctor_of_subset
      (F := KminusToDminus) (S := QisMinus) P hP_reaches hP_isIso

/-- Corollary: under the dual hypotheses of Proposition 13.16.8, the bounded-above total left
derived functor exists. -/
theorem boundedAbove_hasLeftDerivedFunctor_of_epi_from_boundedAboveLeftAcyclic
    [HasEpiCover BoundedAboveLeftAcyclic] :
    Functor.HasLeftDerivedFunctor KminusToDminus QisMinus := by
  let _ : Functor.HasPointwiseLeftDerivedFunctor KminusToDminus QisMinus :=
    boundedAbove_hasPointwiseLeftDerivedFunctor_of_epi_from_boundedAboveLeftAcyclic F
  infer_instance

-- Proof sketch: this is the bounded-above dual of the bounded Leray acyclicity criterion,
-- expressed directly with the owner
-- `IsTermwiseBoundedAboveLeftAcyclicForAdditiveFunctor`.
/-- Any bounded-above complex whose terms are acyclic for the bounded-above left derived functor
computes the bounded-above left derived functor. -/
theorem computesLeftDerivedFunctorAt_of_termwise_boundedAboveLeftAcyclic
    [Functor.HasLeftDerivedFunctor KminusToDminus QisMinus]
    (A : K⁻(𝒜))
    (hA : IsTermwiseBoundedAboveLeftAcyclicForAdditiveFunctor F A) :
    Functor.ComputesLeftDerivedAt KminusToDminus QisMinus A := by
  let P : ObjectProperty (K⁻(𝒜)) :=
    IsTermwiseBoundedAboveLeftAcyclicForAdditiveFunctor F
  have hP_reaches :
      ∀ X : K⁻(𝒜), ∃ (X' : K⁻(𝒜)) (s : X' ⟶ X), P X' ∧ QisMinus s := by
    intro X
    let K : CochainComplex 𝒜 ℤ := X.obj.as
    obtain ⟨a, hK⟩ := (CochainComplex.minus_iff 𝒜 K).1 X.property
    -- Proof comment: reuse the same bounded-above termwise left-acyclic replacement as in the
    -- pointwise existence theorem.
    obtain ⟨Y, α, hα⟩ :=
      exists_termwiseEpi_quasiIso_with_terms_in_of_isStrictlyLE
        (P := BoundedAboveLeftAcyclic) a K hK
    let Xc : Comp⁻(𝒜) := ⟨K, X.property⟩
    have hXeq : (HomotopyCategory.Minus.quotient 𝒜).obj Xc = X := by
      cases X
      rfl
    let Yminus : Comp⁻(𝒜) := hα.toMinusWithTermsIn
    let X' : K⁻(𝒜) := (HomotopyCategory.Minus.quotient 𝒜).obj Yminus
    let α' : Yminus ⟶ Xc := ⟨α⟩
    let s : X' ⟶ X := by
      simpa [X', hXeq] using (HomotopyCategory.Minus.quotient 𝒜).map α'
    refine ⟨X', s, ?_, ?_⟩
    · -- Proof comment: the chosen source lies in the good subset by construction.
      intro n
      simpa [P, X'] using hα.toMinusWithTermsIn.term_mem n
    · -- Proof comment: the replacement morphism is still a bounded-above quasi-isomorphism.
      change HomotopyCategory.quasiIso 𝒜 (up ℤ)
        ((ObjectProperty.ι (HomotopyCategory.minus 𝒜)).map s)
      simpa [s, X', hXeq] using
        (show HomotopyCategory.quasiIso 𝒜 (up ℤ)
          (((HomotopyCategory.quotient 𝒜 (up ℤ)).map α)) by
          rw [HomotopyCategory.quotient_map_mem_quasiIso_iff]
          exact hα.quasiIso)
  have hP_isIso :
      ∀ {X Y : K⁻(𝒜)} (s : X ⟶ Y), P X → P Y → QisMinus s →
        IsIso (KminusToDminus.map s) := by
    intro X Y s hX hY hs
    -- Proof comment: this is exactly the same denominator-inversion bridge used above.
    have hsMapped :
        boundedAboveHomotopyQuasiIso ℬ
          ((mapBoundedAboveHomotopyCategory F).map s) :=
      mapped_boundedAbove_quasiIso_of_termwise_boundedAboveLeftAcyclic
        (F := F) s hX hY hs
    exact isIso_KminusToDminus_map_of_mapped_boundedAbove_quasiIso (F := F) s hsMapped
  -- Proof comment: once those two subset hypotheses are in place, the general subset criterion
  -- of Lemma `13.14.15` turns termwise bounded-above left acyclicity into a computation theorem.
  exact
    Functor.computesLeftDerivedAt_of_mem_subset
      (F := KminusToDminus) (S := QisMinus) P hP_reaches hP_isIso hA

end Left

end

end CategoryTheory
