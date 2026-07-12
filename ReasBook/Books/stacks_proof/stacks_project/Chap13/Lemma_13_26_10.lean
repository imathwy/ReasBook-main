import Mathlib
import StacksProject_2024.Chap13.Definition_13_13_2
import StacksProject_2024.Chap12.Lemma_12_19_7
import StacksProject_2024.Chap12.Lemma_12_19_15
import StacksProject_2024.Chap13.Lemma_13_26_3
import StacksProject_2024.Chap13.Lemma_13_26_4

open CategoryTheory
open CochainComplex
open scoped CategoryTheory

noncomputable section

universe u v

namespace CategoryTheory

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]
variable [Abelian (finiteFilteredObjectCat 𝒜)]

local notation "FilF" => finiteFilteredObjectCat 𝒜
local notation "QhFilt" => HomotopyCategory.quotient FilF (ComplexShape.up ℤ)
local notation "ιFiltInjPlus" =>
  CochainComplex.PlusWithTermsIn.ι (IsFilteredInjective : ObjectProperty FilF)
local notation "FAcOrth" => ObjectProperty.rightOrthogonal (FAc(𝒜))

variable {K : CochainComplex FilF ℤ}

/- Domain-style sampling for Lemma `13.26.10`.
- primary domain: filtered acyclic objects in the homotopy category `K(Fil^f(𝒜))`, bounded-below
  filtered-injective complexes, and right orthogonality against `FAc(𝒜)`;
- sampled owner declarations:
  `FAc(𝒜)`,
  `ObjectProperty.rightOrthogonal`,
  `HomotopyCategory.quotient_map_eq_zero_iff`,
  `CochainComplex.FilteredInjectivePlus`,
  `IsFilteredInjective`;
- best owner abstraction: the canonical owner is the right orthogonal
  `FAcOrth` in the filtered homotopy category, with the bounded-below filtered-injective target
  owned by the chapter abbreviation `CochainComplex.FilteredInjectivePlus 𝒜`;
- primitive data: a bounded-below filtered-injective complex
  `I : CochainComplex.FilteredInjectivePlus 𝒜`;
- derived API: membership of `((ιFiltInjPlus ⋙ QhFilt).obj I)` in `FAcOrth`, and the
  source-facing homotopy-to-zero statement obtained by
  `HomotopyCategory.quotient_map_eq_zero_iff`.

Source/core/bridge triage:
- `source-facing`: the textbook null-homotopy statement below;
- `core/canonical`: `ObjectProperty.rightOrthogonal` applied to `FAc(𝒜)`;
- `bridge/view`: `HomotopyCategory.quotient_map_eq_zero_iff`, which translates vanishing in the
  homotopy category into existence of a homotopy to zero.

This file therefore keeps the textbook statement as a thin bridge, while exposing the owner-level
orthogonality theorem directly on the filtered homotopy category. -/
namespace CochainComplex.FilteredInjectivePlus

/-- Helper for Lemma 13.26.10: filtered acyclicity gives exactness of the underlying row and
strictness of the outgoing differential at each degree. -/
private lemma filteredAcyclic_exact_and_strict_at
    (hK : FAc(𝒜) ((QhFilt).obj K)) (n : ℤ) :
    let S : ShortComplex (FilteredObject 𝒜) :=
      (K.sc n).map (ObjectProperty.ι (FilteredObject.IsFinite : ObjectProperty (FilteredObject 𝒜)))
    ShortComplex.Exact (S.map FilteredObject.forget) ∧ Strict S.g := by
  let S : ShortComplex (FilteredObject 𝒜) :=
    (K.sc n).map (ObjectProperty.ι (FilteredObject.IsFinite : ObjectProperty (FilteredObject 𝒜)))
  have hKgr :
      (((finiteFilteredObjectAssociatedGradedFunctor 𝒜).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K).Acyclic := by
    -- Proof comment: filtered acyclicity is defined by sending `K` to the associated-graded
    -- homotopy category, so for the chosen representative it becomes ordinary acyclicity of the
    -- associated-graded complex.
    rw [filteredAcyclic_iff] at hK
    rw [HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at hK
    simpa [filteredAssociatedGradedHomotopyFunctor, finiteFilteredAssociatedGradedFunctor,
      finiteFilteredObjectAssociatedGradedFunctor] using hK
  rw [HomologicalComplex.acyclic_iff] at hKgr
  have hS₁fin : S.X₁.IsFinite := (K.X n).property
  have hS₂fin : S.X₂.IsFinite := (K.X (n + 1)).property
  have hS₃fin : S.X₃.IsFinite := (K.X (n + 2)).property
  have hgr : ShortComplex.Exact (S.map ShortComplex.associatedGradedFunctor) := by
    -- Proof comment: the associated-graded row of `S` is exactly the degree-`n` short complex
    -- in the associated-graded complex of `K`.
    simpa [S, finiteFilteredObjectAssociatedGradedFunctor] using hKgr n
  refine ⟨?_, ?_⟩
  · -- Proof comment: forgetting the filtration after associated-graded exactness recovers the
    -- underlying exact row in `𝒜`.
    simpa [S] using
      (ShortComplex.underlying_exact_of_associatedGraded_exact
        (S := S) hS₁fin hS₂fin hS₃fin hgr)
  · -- Proof comment: the same associated-graded exactness forces the outgoing filtered
    -- differential in this row to be strict.
    exact
      (ShortComplex.strict_of_associatedGraded_exact
        (S := S) hS₁fin hS₂fin hS₃fin hgr).2

/-- Helper for Lemma 13.26.10: the canonical inclusion of a filtered subobject is strict. -/
private lemma strict_subobjectInclusion
    (X : FilteredObject 𝒜) (S : Subobject X.obj) :
    FilteredObject.Hom.Strict (X.subobjectInclusion S) := by
  letI : Mono (X.subobjectInclusion S).hom := by
    change Mono S.arrow
    infer_instance
  -- Proof comment: the induced filtration on the filtered subobject is exactly the pullback
  -- filtration appearing in the mono-side strictness criterion.
  refine (FilteredObject.Hom.strict_iff_induced_filtration_of_mono (X.subobjectInclusion S)).2 ?_
  rfl

/-- Helper for Lemma 13.26.10: a filtered isomorphism is strict. -/
private lemma strict_hom_of_iso {A B : FilteredObject 𝒜} (e : A ≅ B) :
    FilteredObject.Hom.Strict e.hom := by
  letI : Mono e.hom.hom := by
    infer_instance
  -- Proof comment: identify the induced filtration of `e.hom` with the source filtration by
  -- pulling a stage across `e.hom` and transporting it back with `e.inv`.
  refine (FilteredObject.Hom.strict_iff_induced_filtration_of_mono e.hom).2 ?_
  refine OrderHom.ext _ _ ?_
  funext i
  refine le_antisymm ?_ ?_
  · simpa using FilteredObject.Hom.pullback_preserves e.hom i
  · -- Proof comment: factor the pullback stage into `B.filtration i` and then return through the
    -- inverse filtered isomorphism to land in `A.filtration i`.
    refine Subobject.le_of_factors ?_
    let P : Subobject A.obj := (Subobject.pullback e.hom.hom).obj (B.filtration i)
    have hP :
        (B.filtration i).Factors (P.arrow ≫ e.hom.hom) := by
      rw [show P = (Subobject.pullback e.hom.hom).obj (B.filtration i) by rfl]
      rw [pullback_factors_iff]
      exact Subobject.factors_self P
    let u : (P : 𝒜) ⟶ B.filtration i :=
      (B.filtration i).factorThru (P.arrow ≫ e.hom.hom) hP
    let v : (B.filtration i : 𝒜) ⟶ A.filtration i :=
      (A.filtration i).factorThru ((B.filtration i).arrow ≫ e.inv.hom) (e.inv.preserves i)
    refine ⟨u ≫ v, ?_⟩
    calc
      u ≫ v ≫ (A.filtration i).arrow
          = u ≫ (B.filtration i).arrow ≫ e.inv.hom := by
              simp [v, Category.assoc]
      _ = P.arrow ≫ e.hom.hom ≫ e.inv.hom := by
            simp [u, Category.assoc]
      _ = P.arrow := by
            simp [Category.assoc]

/-- Helper for Lemma 13.26.10: a cycle map descends to the filtered coimage of the outgoing
differential once exactness identifies previous images with current kernels. -/
private lemma cycle_descends_to_filtered_coimage
    (I : CochainComplex.FilteredInjectivePlus 𝒜) (n : ℤ)
    (g : K.X n ⟶ I.X n) (hg : K.dTo n ≫ g = 0)
    (hExact : imageSubobject (K.dTo n).hom = kernelSubobject (K.dTo (n + 1)).hom) :
    ∃ gcoim : FilteredObject.Hom.coimage (K.dTo (n + 1)) ⟶ I.X n,
      (K.X n).toQuotient (kernelSubobject (K.dTo (n + 1)).hom) ≫ gcoim = g := by
  have himage_zero :
      (K.X n).subobjectInclusion (imageSubobject (K.dTo n).hom) ≫ g = 0 := by
    -- Proof comment: kill the previous image by cancelling the epimorphic map onto it.
    apply FilteredObject.forget.map_injective
    apply (cancel_epi (factorThruImageSubobject (K.dTo n).hom)).1
    simpa [Category.assoc, imageSubobject_arrow_comp] using congrArg FilteredObject.Hom.hom hg
  have hkernel_zero :
      (K.X n).subobjectInclusion (kernelSubobject (K.dTo (n + 1)).hom) ≫ g = 0 := by
    -- Proof comment: the acyclic exactness row identifies this kernel with the previous image.
    simpa [hExact] using himage_zero
  let gcoim :=
    FilteredObject.Hom.descToCokernel
      ((K.X n).subobjectInclusion (kernelSubobject (K.dTo (n + 1)).hom)) g hkernel_zero
  refine ⟨gcoim, ?_⟩
  -- Proof comment: the quotient by the kernel subobject is exactly the filtered coimage owner.
  simpa [FilteredObject.Hom.coimage, FilteredObject.toQuotient] using
    FilteredObject.Hom.toCokernel_descToCokernel
      ((K.X n).subobjectInclusion (kernelSubobject (K.dTo (n + 1)).hom)) g hkernel_zero

/-- Helper for Lemma 13.26.10: strictness of a filtered differential makes the canonical map from
its filtered coimage to the literal filtered image-subobject strict. -/
private lemma coimage_to_image_subobject_strict_of_strict
    {A B : FilteredObject 𝒜} (f : A ⟶ B) (hf : FilteredObject.Hom.Strict f) :
    FilteredObject.Hom.Strict (FilteredObject.Hom.coimageToImageSubobject f) := by
  have hIsoComparison : IsIso (FilteredObject.Hom.coimageImageComparison f) :=
    (strict_iff_coimageImageComparison_isIso f).1 hf
  have htransport :
      FilteredObject.Hom.coimageToImageSubobject f =
        FilteredObject.Hom.coimageImageComparison f ≫
          (FilteredObject.Hom.imageSubobjectFilteredObjectIsoImage f).inv := by
    -- Proof comment: undo the final transport from the literal image subobject to `image f`.
    apply FilteredObject.Hom.ext
    simp [FilteredObject.Hom.coimageImageComparison, Category.assoc]
  have hIsoSub :
      IsIso (FilteredObject.Hom.coimageToImageSubobject f) := by
    rw [htransport]
    infer_instance
  -- Proof comment: any filtered isomorphism is strict, so the literal comparison inherits
  -- strictness from its isomorphism structure.
  exact strict_hom_of_iso (asIso (FilteredObject.Hom.coimageToImageSubobject f))

/-- Helper for Lemma 13.26.10: the filtered differential factors through its coimage, the literal
filtered image-subobject, and the image inclusion into the codomain. -/
private lemma coimage_to_image_subobject_factorisation
    {A B : FilteredObject 𝒜} (f : A ⟶ B) :
    A.toQuotient (kernelSubobject f.hom) ≫
        FilteredObject.Hom.coimageToImageSubobject f ≫
          B.subobjectInclusion (imageSubobject f.hom) =
      f := by
  -- Proof comment: forgetting the filtration reduces this to the standard abelian
  -- coimage-image factorization for `f.hom`.
  apply FilteredObject.forget.map_injective
  change
    cokernel.π (kernelSubobject f.hom).arrow ≫
        (FilteredObject.Hom.coimageToImageSubobject f).hom ≫
          (imageSubobject f.hom).arrow =
      f.hom
  simpa [FilteredObject.Hom.coimageToImageSubobject, FilteredObject.toQuotient, Category.assoc]
    using Abelian.coimage_image_factorisation f.hom

/-- Helper for Lemma 13.26.10: a degreewise map annihilating the previous differential should lift
across the image of the next differential in a filtered acyclic complex. -/
private lemma exists_homotopy_component_of_cycle
    (I : CochainComplex.FilteredInjectivePlus 𝒜) (hK : FAc(𝒜) ((QhFilt).obj K))
    (n : ℤ) (g : K.X n ⟶ I.X n) (hg : K.dTo n ≫ g = 0) :
    ∃ h : K.X (n + 1) ⟶ I.X n, K.dTo (n + 1) ≫ h = g := by
  have hrow := filteredAcyclic_exact_and_strict_at (K := K) hK n
  have hExact :
      imageSubobject (K.dTo n).hom = kernelSubobject (K.dTo (n + 1)).hom := by
    -- Proof comment: forgetting the filtered row identifies exactness with the usual
    -- `image = kernel` statement in the ambient abelian category.
    let S : ShortComplex (FilteredObject 𝒜) :=
      (K.sc n).map
        (ObjectProperty.ι (FilteredObject.IsFinite : ObjectProperty (FilteredObject 𝒜)))
    simpa [S] using
      (ShortComplex.exact_iff_image_eq_kernel (S := S.map FilteredObject.forget)).1 hrow.1
  obtain ⟨gcoim, hgcoim⟩ := cycle_descends_to_filtered_coimage I n g hg hExact
  have hstrict_coimage :
      FilteredObject.Hom.Strict (FilteredObject.Hom.coimageToImageSubobject (K.dTo (n + 1))) := by
    -- Proof comment: strictness of the differential upgrades the coimage-to-image comparison to a
    -- strict map in the filtered category.
    exact coimage_to_image_subobject_strict_of_strict (K.dTo (n + 1)) hrow.2
  let u := FilteredObject.Hom.coimageToImageSubobject (K.dTo (n + 1))
  letI : Mono u := by
    change Mono u.hom
    infer_instance
  letI : IsFilteredInjective (I.X n) := I.property n
  obtain ⟨gimg, hgimg⟩ := IsFilteredInjective.factors (f := gcoim) (u := u) hstrict_coimage
  have hstrict_image :
      FilteredObject.Hom.Strict
        ((K.X (n + 1)).subobjectInclusion (imageSubobject (K.dTo (n + 1)).hom)) := by
    -- Proof comment: once the image object is chosen explicitly as a filtered subobject of
    -- `K.X (n + 1)`, its inclusion is strict by the induced-filtration criterion.
    exact strict_subobjectInclusion (K.X (n + 1)) (imageSubobject (K.dTo (n + 1)).hom)
  let v := (K.X (n + 1)).subobjectInclusion (imageSubobject (K.dTo (n + 1)).hom)
  letI : Mono v := by
    change Mono v.hom
    infer_instance
  obtain ⟨h, hh⟩ := IsFilteredInjective.factors (f := gimg) (u := v) hstrict_image
  refine ⟨h, ?_⟩
  -- Proof comment: substitute the two filtered-injective extensions into the canonical
  -- coimage-image factorization of the outgoing differential `K.dTo (n + 1)`.
  calc
    K.dTo (n + 1) ≫ h
        = (K.X n).toQuotient (kernelSubobject (K.dTo (n + 1)).hom) ≫ u ≫ v ≫ h := by
            rw [coimage_to_image_subobject_factorisation (K.dTo (n + 1))]
    _ = (K.X n).toQuotient (kernelSubobject (K.dTo (n + 1)).hom) ≫ u ≫ gimg := by
          rw [hh]
    _ = (K.X n).toQuotient (kernelSubobject (K.dTo (n + 1)).hom) ≫ gcoim := by
          rw [hgimg]
    _ = g := hgcoim

/-- Helper for Lemma 13.26.10: below the lower bound of the bounded-below target, every
component of a cochain map vanishes. -/
private lemma map_component_eq_zero_of_lt_lower_bound
    {I : CochainComplex FilF ℤ} (α : K ⟶ I) {a n : ℤ}
    (hI : I.IsStrictlyGE a) (hn : n < a) :
    α.f n = 0 := by
  let hzero : IsZero (I.X n) := I.isZero_of_isStrictlyGE a n hn
  -- Proof comment: the codomain object is zero in this degree, so any map into it is zero.
  exact hzero.eq_of_tgt _ _

/-- Helper for Lemma 13.26.10: once the degreewise formula
`αⁿ = d_Kⁿ ≫ hⁿ + hⁿ⁻¹ ≫ d_Iⁿ⁻¹` is available with the canonical cochain indexing, the map is
the standard null-homotopic map and hence homotopic to zero. -/
private lemma homotopy_of_component_formula
    {I : CochainComplex FilF ℤ} (α : K ⟶ I)
    (h : ∀ n : ℤ, K.X (n + 1) ⟶ I.X n)
    (hα : ∀ n : ℤ, α.f n = K.dTo (n + 1) ≫ h n + h (n - 1) ≫ I.dTo n) :
    Nonempty (Homotopy α 0) := by
  let hh : ∀ i j, (ComplexShape.up ℤ).Rel j i → (K.X i ⟶ I.X j) :=
    fun i j hij ↦ by
      -- Proof comment: in cochain degree conventions, `Rel j i` means `i = j + 1`.
      obtain rfl : i = j + 1 := by simpa using hij.symm
      simpa using h j
  have hmap : α = Homotopy.nullHomotopicMap' hh := by
    apply HomologicalComplex.hom_ext
    intro n
    -- Proof comment: `nullHomotopicMap'` computes each degree by the same two-term formula.
    rw [Homotopy.nullHomotopicMap'_f
      (show (ComplexShape.up ℤ).Rel (n - 1) n by simp)
      (show (ComplexShape.up ℤ).Rel n (n + 1) by simp)]
    simpa [hh] using hα n
  refine ⟨(Homotopy.ofEq hmap).trans ?_⟩
  -- Proof comment: the canonical map constructed from `hh` comes with a canonical homotopy to
  -- zero.
  exact Homotopy.nullHomotopy' hh

/-- Helper for Lemma 13.26.10: at the lower bound of the bounded-below target, the previous
component of a cochain map vanishes, so the degree-`a` component is already a cycle. -/
private lemma base_cycle_at_lower_bound
    (I : CochainComplex.FilteredInjectivePlus 𝒜) (α : K ⟶ I)
    {a : ℤ} (hI : (I : CochainComplex FilF ℤ).IsStrictlyGE a) :
    K.dTo a ≫ α.f a = 0 := by
  have hvanish :
      α.f (a - 1) = 0 :=
    map_component_eq_zero_of_lt_lower_bound (K := K) α hI (show a - 1 < a by omega)
  -- Proof comment: the chain-map square at degrees `a - 1` and `a` identifies the incoming
  -- differential of `α.f a` with the vanished previous component.
  calc
    K.dTo a ≫ α.f a = α.f (a - 1) ≫ I.dTo a := by
      simpa using (α.comm (a - 1) a).symm
    _ = 0 := by simp [hvanish]

/-- Helper for Lemma 13.26.10: once the previous correction term is fixed, the next corrected
component is again a cycle. -/
private lemma successor_corrected_cycle_vanishes
    (I : CochainComplex.FilteredInjectivePlus 𝒜) (α : K ⟶ I)
    {a : ℤ} (k : ℕ)
    (sPrev : K.X (a + (k : ℤ)) ⟶ I.X (a + (k : ℤ) - 1))
    (s : K.X (a + (k : ℤ) + 1) ⟶ I.X (a + (k : ℤ)))
    (hs :
      K.dTo (a + (k : ℤ) + 1) ≫ s =
        α.f (a + (k : ℤ)) - sPrev ≫ I.dTo (a + (k : ℤ))) :
    K.dTo (a + (k : ℤ) + 1) ≫
        (α.f (a + (k : ℤ) + 1) - s ≫ I.dTo (a + (k : ℤ) + 1)) =
      0 := by
  have hcomm :
      K.dTo (a + (k : ℤ) + 1) ≫ α.f (a + (k : ℤ) + 1) =
        α.f (a + (k : ℤ)) ≫ I.dTo (a + (k : ℤ) + 1) := by
    simpa using (α.comm (a + (k : ℤ)) (a + (k : ℤ) + 1)).symm
  -- Proof comment: rewrite the chain-map square at the next degree, substitute the recursive
  -- identity for `s`, and then use `d ∘ d = 0` on the target complex.
  calc
    K.dTo (a + (k : ℤ) + 1) ≫
        (α.f (a + (k : ℤ) + 1) - s ≫ I.dTo (a + (k : ℤ) + 1))
        =
      α.f (a + (k : ℤ)) ≫ I.dTo (a + (k : ℤ) + 1) -
        (K.dTo (a + (k : ℤ) + 1) ≫ s) ≫ I.dTo (a + (k : ℤ) + 1) := by
          rw [Preadditive.comp_sub, hcomm]
          simp [Category.assoc]
    _ =
      α.f (a + (k : ℤ)) ≫ I.dTo (a + (k : ℤ) + 1) -
        (α.f (a + (k : ℤ)) - sPrev ≫ I.dTo (a + (k : ℤ))) ≫
          I.dTo (a + (k : ℤ) + 1) := by
            rw [hs]
    _ = sPrev ≫ I.dTo (a + (k : ℤ)) ≫ I.dTo (a + (k : ℤ) + 1) := by
          simp only [Category.assoc, Preadditive.sub_comp, Preadditive.comp_sub]
          abel
    _ = 0 := by
          simpa [Category.assoc] using
            congrArg
              (fun t ↦ sPrev ≫ t)
              (I.d_comp_d (a + (k : ℤ) - 1) (a + (k : ℤ)) (a + (k : ℤ) + 1))

/-- Helper for Lemma 13.26.10: recursively construct the degreewise correction maps above the
lower bound of the target complex. -/
private lemma recursive_components_above_lower_bound
    (I : CochainComplex.FilteredInjectivePlus 𝒜) (α : K ⟶ I)
    (hK : FAc(𝒜) ((QhFilt).obj K))
    {a : ℤ} (hI : (I : CochainComplex FilF ℤ).IsStrictlyGE a) :
    ∃ s : ∀ k : ℕ, K.X (a + (k : ℤ) + 1) ⟶ I.X (a + (k : ℤ)),
      K.dTo (a + 1) ≫ s 0 = α.f a ∧
        ∀ k : ℕ,
          K.dTo (a + (k : ℤ) + 2) ≫ s (k + 1) =
            α.f (a + (k : ℤ) + 1) - s k ≫ I.dTo (a + (k : ℤ) + 1) := by
  obtain ⟨s0, hs0⟩ :=
    exists_homotopy_component_of_cycle
      (K := K) I hK a (α.f a)
      (base_cycle_at_lower_bound (K := K) I α hI)
  let P : ℕ → Sort _ := fun k ↦
    Σ' sPrev : K.X (a + (k : ℤ)) ⟶ I.X (a + (k : ℤ) - 1),
      Σ' s : K.X (a + (k : ℤ) + 1) ⟶ I.X (a + (k : ℤ)),
        K.dTo (a + (k : ℤ) + 1) ≫ s =
          α.f (a + (k : ℤ)) - sPrev ≫ I.dTo (a + (k : ℤ))
  let F : ∀ k : ℕ, P k :=
    Nat.rec
      (by
        -- Proof comment: initialize the recursion with zero previous correction below the lower
        -- bound and the first lift `s 0`.
        refine ⟨0, s0, ?_⟩
        simpa using hs0)
      (fun k prev ↦ by
        let sPrev : K.X (a + (k : ℤ)) ⟶ I.X (a + (k : ℤ) - 1) := prev.1
        let s : K.X (a + (k : ℤ) + 1) ⟶ I.X (a + (k : ℤ)) := prev.2.1
        let hs : K.dTo (a + (k : ℤ) + 1) ≫ s =
            α.f (a + (k : ℤ)) - sPrev ≫ I.dTo (a + (k : ℤ)) := prev.2.2
        have hcycle :
            K.dTo (a + (k : ℤ) + 1) ≫
                (α.f (a + (k : ℤ) + 1) - s ≫ I.dTo (a + (k : ℤ) + 1)) =
              0 :=
          successor_corrected_cycle_vanishes (K := K) I α k sPrev s hs
        obtain ⟨sNext, hsNext⟩ :=
          exists_homotopy_component_of_cycle
            (K := K) I hK (a + (k : ℤ) + 1)
            (α.f (a + (k : ℤ) + 1) - s ≫ I.dTo (a + (k : ℤ) + 1))
            hcycle
        -- Proof comment: the next recursive state stores the current correction as the new
        -- previous term and the freshly lifted correction as the new current term.
        refine ⟨s, sNext, ?_⟩
        simpa [Int.ofNat_succ, add_assoc, add_left_comm, add_comm] using hsNext)
  let s : ∀ k : ℕ, K.X (a + (k : ℤ) + 1) ⟶ I.X (a + (k : ℤ)) := fun k ↦ (F k).2.1
  refine ⟨s, ?_, ?_⟩
  · -- Proof comment: the base recursive equation is the initial lifted cycle with zero previous
    -- correction.
    simpa [s] using (F 0).2.2
  · intro k
    -- Proof comment: by construction, the previous term stored in `F (k + 1)` is exactly `s k`.
    simpa [s] using (F (k + 1)).2.2

/-- Helper for Lemma 13.26.10: convert the recursive Nat-indexed correction terms above the lower
bound into a global integer-indexed homotopy formula. -/
private lemma integer_component_formula_of_recursive_components
    (I : CochainComplex.FilteredInjectivePlus 𝒜) (α : K ⟶ I)
    {a : ℤ} (hI : (I : CochainComplex FilF ℤ).IsStrictlyGE a)
    (s : ∀ k : ℕ, K.X (a + (k : ℤ) + 1) ⟶ I.X (a + (k : ℤ)))
    (hs0 : K.dTo (a + 1) ≫ s 0 = α.f a)
    (hstep : ∀ k : ℕ,
      K.dTo (a + (k : ℤ) + 2) ≫ s (k + 1) =
        α.f (a + (k : ℤ) + 1) - s k ≫ I.dTo (a + (k : ℤ) + 1)) :
    ∃ h : ∀ n : ℤ, K.X (n + 1) ⟶ I.X n,
      ∀ n : ℤ, α.f n = K.dTo (n + 1) ≫ h n + h (n - 1) ≫ I.dTo n := by
  let h : ∀ n : ℤ, K.X (n + 1) ⟶ I.X n := fun n ↦
    if hn : a ≤ n then
      let k : ℕ := Int.toNat (n - a)
      have hk : a + (k : ℤ) = n := by
        dsimp [k]
        rw [Int.toNat_of_nonneg (sub_nonneg.mpr hn)]
        omega
      -- Proof comment: above the lower bound, the Nat-indexed recursive component already has
      -- the required degree after rewriting `n = a + k`.
      simpa [hk, add_assoc] using s k
    else
      0
  refine ⟨h, ?_⟩
  intro n
  by_cases hn : n < a
  · have hα0 :
        α.f n = 0 :=
      map_component_eq_zero_of_lt_lower_bound (K := K) α hI hn
    have hh :
        h n = 0 := by
      simp [h, not_le.mpr hn]
    have hhPrev :
        h (n - 1) = 0 := by
      have hnPrev : n - 1 < a := by omega
      simp [h, not_le.mpr hnPrev]
    -- Proof comment: below the lower bound, both correction terms vanish and so does `α.f n`.
    calc
      α.f n = 0 := hα0
      _ = K.dTo (n + 1) ≫ h n + h (n - 1) ≫ I.dTo n := by
            simp [hh, hhPrev]
  · have hna : a ≤ n := le_of_not_gt hn
    let k : ℕ := Int.toNat (n - a)
    have hk : a + (k : ℤ) = n := by
      dsimp [k]
      rw [Int.toNat_of_nonneg (sub_nonneg.mpr hna)]
      omega
    cases k with
    | zero =>
        have hn_eq : n = a := by
          omega
        have hkToNat : Int.toNat (n - a) = 0 := by
          rw [show n - a = 0 by omega]
        have hh :
            h n = s 0 := by
          simp [h, hna, hkToNat, hn_eq]
        have hhPrev :
            h (n - 1) = 0 := by
          have hnPrev : n - 1 < a := by
            omega
          simp [h, not_le.mpr hnPrev]
        -- Proof comment: the first recursive equation is the base cycle lift, and the previous
        -- correction term still vanishes one degree below the lower bound.
        calc
          α.f n = α.f a := by simpa [hn_eq]
          _ = K.dTo (a + 1) ≫ s 0 := by simpa using hs0.symm
          _ = K.dTo (n + 1) ≫ h n + h (n - 1) ≫ I.dTo n := by
                simp [hn_eq, hh, hhPrev]
    | succ k =>
        have hn_eq : n = a + (k : ℤ) + 1 := by
          omega
        have hnaPrev : a ≤ n - 1 := by
          omega
        have hkToNat : Int.toNat (n - a) = k + 1 := by
          rw [show n - a = ((k + 1 : ℕ) : ℤ) by omega, Int.toNat_of_nonneg]
          exact Int.ofNat_nonneg (k + 1)
        have hkPrevToNat : Int.toNat ((n - 1) - a) = k := by
          rw [show (n - 1) - a = (k : ℤ) by omega, Int.toNat_of_nonneg]
          exact Int.ofNat_nonneg k
        have hh :
            h n = s (k + 1) := by
          simp [h, hna, hkToNat, hn_eq, add_assoc, add_left_comm, add_comm]
        have hhPrev :
            h (n - 1) = s k := by
          simp [h, hnaPrev, hkPrevToNat, hn_eq, add_assoc, add_left_comm, add_comm]
        -- Proof comment: for a successor degree above the lower bound, the recursive step gives
        -- the desired decomposition into the new correction and the transported previous one.
        calc
          α.f n = α.f (a + (k : ℤ) + 1) := by simpa [hn_eq]
          _ =
              K.dTo (a + (k : ℤ) + 2) ≫ s (k + 1) +
                s k ≫ I.dTo (a + (k : ℤ) + 1) := by
                  exact (sub_eq_iff_eq_add'.mp (hstep k)).symm
          _ = K.dTo (n + 1) ≫ h n + h (n - 1) ≫ I.dTo n := by
                simp [hn_eq, hh, hhPrev, add_assoc]

/-- Helper for Lemma 13.26.10: a map from a filtered acyclic complex to a bounded-below filtered-
injective complex is null-homotopic. -/
private theorem null_homotopic_of_filteredAcyclic_to_filteredInjectivePlus
    (I : CochainComplex.FilteredInjectivePlus 𝒜) (α : K ⟶ I)
    (hK : FAc(𝒜) ((QhFilt).obj K)) :
    Nonempty (Homotopy α 0) := by
  -- Route correction: reduce the source proof to degreewise cycles instead of repeatedly
  -- correcting whole chain maps. The missing piece is the image-row lift in
  -- `exists_homotopy_component_of_cycle`, now corrected to use the incoming differential
  -- `K.dTo n` and the outgoing factorization map `K.dTo (n + 1)`.
  obtain ⟨a, hI⟩ := I.exists_isStrictlyGE
  let _ : (I : CochainComplex FilF ℤ).IsStrictlyGE a := hI
  obtain ⟨s, hs0, hstep⟩ :=
    recursive_components_above_lower_bound (K := K) I α hK hI
  obtain ⟨h, hα⟩ :=
    integer_component_formula_of_recursive_components (K := K) I α hI s hs0 hstep
  -- Proof comment: once the recursive components are translated to the standard cochain formula,
  -- the canonical null-homotopy constructor finishes the proof.
  exact homotopy_of_component_formula (K := K) α h hα

-- Proof sketch: pass to the homotopy category of `Fil^f(𝒜)` and argue degreewise on associated
-- graded pieces as in the ordinary injective case. Filtered acyclicity kills the source, while
-- bounded-belowness and termwise filtered injectivity place the target in the right orthogonal of
-- `FAc(𝒜)`.
/-- A bounded-below complex of filtered injectives lies in the right orthogonal of the filtered
acyclic subcategory of `K(Fil^f(𝒜))`. -/
theorem rightOrthogonal (I : CochainComplex.FilteredInjectivePlus 𝒜) :
    FAcOrth ((ιFiltInjPlus ⋙ QhFilt).obj I) := by
  rw [ObjectProperty.rightOrthogonal_iff]
  intro X f hX
  obtain ⟨L, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
  obtain ⟨α, rfl⟩ := QhFilt.map_surjective f
  exact (HomotopyCategory.quotient_map_eq_zero_iff α).2
    (null_homotopic_of_filteredAcyclic_to_filteredInjectivePlus I α hX).some

end CochainComplex.FilteredInjectivePlus

-- Proof sketch: apply the owner theorem
-- `CochainComplex.FilteredInjectivePlus.rightOrthogonal` in the filtered homotopy
-- category and translate the resulting vanishing statement back to a homotopy by
-- `HomotopyCategory.quotient_map_eq_zero_iff`.
/-- Lemma 13.26.10: if `K^•` is filtered acyclic and `I^•` is bounded below with filtered
injective terms, then every morphism `K^• ⟶ I^•` is homotopic to zero. -/
@[stacks 05TX]
theorem homotopic_to_zero_of_filteredAcyclic_to_boundedBelow_termwiseFilteredInjective
    (I : CochainComplex.FilteredInjectivePlus 𝒜) (α : K ⟶ I)
    (hK : FAc(𝒜) ((QhFilt).obj K)) :
    Nonempty (Homotopy α 0) :=
  null_homotopic_of_filteredAcyclic_to_filteredInjectivePlus I α hK

end CategoryTheory
