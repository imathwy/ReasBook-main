import Mathlib.Tactic.StacksAttribute
import Mathlib.Algebra.Category.Grp.AB
import StacksProject_2024.Chap13.Lemma_13_35_4
import StacksProject_2024.Chap13.Lemma_13_37_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Limits.CoproductsFromFiniteFiltered
open CategoryTheory.ObjectProperty
open CategoryTheory.Pretriangulated
open Opposite
open scoped CategoryTheory.ObjectProperty.GeneratedNotation

noncomputable section

universe w v u r

local instance : HasCountableCoproducts AddCommGrpCat.{v} :=
  hasCountableCoproducts_of_sequentialColimits

section

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] [IsTriangulated D]
  [HasCoproducts.{max u v w} D]
variable {I : Type w} (E : I → D)

/- Domain-style sampling for Lemma 13.37.4:
- primary domain: compact objects and finitely generated extension stages in a triangulated
  category, expressed through `ObjectProperty`;
- sampled owner declarations:
  `ObjectProperty.objectGeneratedProperty`,
  `ObjectProperty.objectGeneratedProperty_le_iff`,
  `ObjectProperty.objectGeneratedStage`,
  `ObjectProperty.additiveExtensionStage`,
  `CategoryTheory.ObjectProperty.GeneratedNotation`;
- best owner abstraction: the source-facing statement should express the factor object as lying in
  the generated triangulated subcategory `⟨∐ fun j ↦ E (ι j)⟩` attached to a finite coproduct of
  generators, and the stronger stage-level statement should use the canonical coproduct stage
  `⟨∐ fun j ↦ E (ι j)⟩_m`; any finite-family additive-extension presentation is a derived bridge,
  not the public owner;
- primitive-vs-derived split:
  primitive data are the finite index type `J`, the chosen subfamily `ι : J → I`, and the finite
  coproduct `∐ fun j ↦ E (ι j)`;
  derived API is the stage-level witness `⟨∐ fun j ↦ E (ι j)⟩_m A`, whose internal description is
  `additiveExtensionStage ((singleton (∐ fun j ↦ E (ι j))).shiftClosure ℤ) m A`.

Source/core/bridge triage:
- `source-facing`: the compact-factorization theorem for a finite subfamily of generators;
- `core/canonical`: `objectGeneratedProperty` with the textbook notation `⟨-⟩`;
- `bridge/view`: the companion theorem below retains the stronger finite-coproduct stage witness
  `⟨∐ fun j ↦ E (ι j)⟩_m`. -/

-- Proof sketch: first prove the stronger stage-level statement below, producing a factor object in
-- a canonical generated stage `⟨∐ fun j ↦ E (ι j)⟩_m` attached to finitely many chosen generators.
-- Then pass from that stage witness to membership in the generated triangulated subcategory of the
-- same finite coproduct, since `⟨∐ fun j ↦ E (ι j)⟩` is the supremum of its positive stages.
/-- Helper for Lemma 13.37.4: membership in the generated property of a finite generator coproduct
comes from some positive stage of that same coproduct. -/
private theorem finite_generator_coproduct_stage_witness
    {A : D} {J : Type*} [Finite J] (ι : J → I)
    (hA : ⟨∐ fun j : J ↦ E (ι j)⟩ A) :
    ∃ m : ℕ+, (⟨∐ fun j : J ↦ E (ι j)⟩_m) A := by
  -- The generated property is the supremum of its positive stages, so membership already carries
  -- the required stage witness.
  rw [objectGeneratedProperty, prop_iSup_iff] at hA
  exact hA

/-- Helper for Lemma 13.37.4: once the factor object lies in the generated property of a finite
generator coproduct, the stage index is extracted by unfolding `⟨-⟩` as a supremum. -/
private theorem stage_factorization_of_generated_factorization
    {X C : D} {f : C ⟶ X}
    (h :
      ∃ (A : D) (J : Type (max u v w)) (_ : Finite J) (ι : J → I),
        ⟨∐ fun j : J ↦ E (ι j)⟩ A ∧
        ∃ (g : C ⟶ A) (k : A ⟶ X), g ≫ k = f) :
    ∃ (A : D) (J : Type (max u v w)) (_ : Finite J) (ι : J → I) (m : ℕ+),
        (⟨∐ fun j : J ↦ E (ι j)⟩_m) A ∧
        ∃ (g : C ⟶ A) (k : A ⟶ X), g ≫ k = f := by
  rcases h with ⟨A, J, hJ, ι, hA, g, k, hgk⟩
  letI : Finite J := hJ
  -- Extract the positive stage witness before returning the same factorization data.
  obtain ⟨m, hm⟩ := finite_generator_coproduct_stage_witness E ι hA
  exact ⟨A, J, hJ, ι, m, hm, g, k, hgk⟩

/-- Helper for Lemma 13.37.4: a morphism into `X (n + 1)` with zero connecting composite lifts
through the stage map `X n ⟶ X (n + 1)`. -/
private theorem lift_zero_connecting
    {X : ℕ → D} {map : ∀ n : ℕ, X n ⟶ X (n + 1)} {Y : ℕ → D}
    {triangleHom : ∀ n : ℕ, Y n ⟶ X n}
    {triangleConnecting : ∀ n : ℕ, X (n + 1) ⟶ (Y n)⟦(1 : ℤ)⟧}
    (hR : IsGeneratingFamilyApproximation E X map Y triangleHom triangleConnecting) {C : D}
    (n : ℕ) {d : C ⟶ X (n + 1)} (hd : d ≫ triangleConnecting n = 0) :
    ∃ u : C ⟶ X n, u ≫ map n = d := by
  let T : Triangle D := Triangle.mk (triangleHom n) (map n) (triangleConnecting n)
  have hT : T ∈ distTriang D := by
    simpa [T] using
      IsGeneratingFamilyApproximation.triangleDistinguished E hR n
  -- Read the vanishing hypothesis as exactness at the third vertex of the approximation triangle.
  obtain ⟨u, hu⟩ := T.coyoneda_exact₃ hT d (by simpa [T] using hd)
  exact ⟨u, by simpa [T] using hu.symm⟩

/-- Helper for Lemma 13.37.4: each summand of a finite coproduct of generators already belongs to
the generated property of that finite coproduct. -/
private theorem finiteGeneratorCoproductSummand_mem_objectGeneratedProperty
    {K : Type (max u v w)} [Finite K] (τ : K → I) (k : K) :
    let F : D := ∐ fun j : K ↦ E (τ j)
    ⟨F⟩ (E (τ k)) := by
  let F : D := ∐ fun j : K ↦ E (τ j)
  let P : ObjectProperty D := ⟨F⟩
  have hF : P F := objectGeneratedProperty_contains F
  have hBiprod : P (⨁ fun j : K ↦ E (τ j)) := by
    -- Move the generated object property across the canonical finite biproduct/coproduct
    -- comparison before taking the chosen summand retract.
    simpa [F, P] using
      P.prop_of_iso (biproduct.isoCoproduct (fun j : K ↦ E (τ j))).symm hF
  -- Every summand is a retract of the chosen finite biproduct.
  exact
    ObjectProperty.IsStableUnderRetracts.of_biproduct
      P (fun j : K ↦ E (τ j)) hBiprod k

/-- Helper for Lemma 13.37.4: a finite coproduct of shifted generators belongs to the generated
property of the corresponding finite unshifted coproduct of generators. -/
private theorem finiteShiftCoproduct_mem_objectGeneratedProperty
    {K : Type (max u v w)} [Finite K] (τ : K → I) (s : K → ℤ) :
    let F : D := ∐ fun k : K ↦ E (τ k)
    ⟨F⟩ (∐ fun k : K ↦ E (τ k)⟦s k⟧) := by
  let F : D := ∐ fun k : K ↦ E (τ k)
  let P : ObjectProperty D := ⟨F⟩
  let _ : P.IsClosedUnderFiniteCoproducts := inferInstance
  have hshift : ∀ k : K, P (E (τ k)⟦s k⟧) := by
    intro k
    -- Recover the unshifted summand from the finite coproduct, then use shift-stability of the
    -- generated triangulated subcategory.
    have hbase : P (E (τ k)) := by
      simpa [F, P] using
        finiteGeneratorCoproductSummand_mem_objectGeneratedProperty E τ k
    exact P.le_shift (s k) _ hbase
  -- Close under the finite coproduct of the shifted summands.
  simpa [P] using P.prop_coproduct hshift

/-- Helper for Lemma 13.37.4: two finite generator-coproduct owners can be merged into one owner
indexed by the sum type. -/
private theorem generatedProperty_mem_sumGeneratorCoproduct
    {A₁ A₂ : D} {J₁ J₂ : Type (max u v w)} [Finite J₁] [Finite J₂]
    (ι₁ : J₁ → I) (ι₂ : J₂ → I)
    (h₁ : ⟨∐ fun j : J₁ ↦ E (ι₁ j)⟩ A₁)
    (h₂ : ⟨∐ fun j : J₂ ↦ E (ι₂ j)⟩ A₂) :
    let F : D := ∐ fun j : Sum J₁ J₂ ↦ E (Sum.elim ι₁ ι₂ j)
    ⟨F⟩ (A₁ ⨿ A₂) := by
  let F₁ : D := ∐ fun j : J₁ ↦ E (ι₁ j)
  let F₂ : D := ∐ fun j : J₂ ↦ E (ι₂ j)
  let F : D := ∐ fun j : Sum J₁ J₂ ↦ E (Sum.elim ι₁ ι₂ j)
  let P : ObjectProperty D := ⟨F⟩
  have hF₁ : P F₁ := by
    let _ : P.IsClosedUnderFiniteCoproducts := inferInstance
    have hsummand : ∀ j : J₁, P (E (ι₁ j)) := by
      intro j
      -- View each left-family generator as a summand of the combined coproduct indexed by
      -- `J₁ ⊕ J₂`.
      simpa [F, P] using
        finiteGeneratorCoproductSummand_mem_objectGeneratedProperty
          E (fun j : Sum J₁ J₂ ↦ Sum.elim ι₁ ι₂ j) (Sum.inl j)
    simpa [F₁, P] using P.prop_coproduct hsummand
  have hF₂ : P F₂ := by
    let _ : P.IsClosedUnderFiniteCoproducts := inferInstance
    have hsummand : ∀ j : J₂, P (E (ι₂ j)) := by
      intro j
      -- The same combined coproduct also contains every right-family generator as a summand.
      simpa [F, P] using
        finiteGeneratorCoproductSummand_mem_objectGeneratedProperty
          E (fun j : Sum J₁ J₂ ↦ Sum.elim ι₁ ι₂ j) (Sum.inr j)
    simpa [F₂, P] using P.prop_coproduct hsummand
  have hle₁ : ⟨F₁⟩ ≤ P := objectGeneratedProperty_le_of_mem F₁ P hF₁
  have hle₂ : ⟨F₂⟩ ≤ P := objectGeneratedProperty_le_of_mem F₂ P hF₂
  let _ : P.IsClosedUnderBinaryCoproducts := inferInstance
  -- Move both factor objects into the combined generated property, then close under `⨿`.
  simpa [P] using P.prop_coprod A₁ A₂ (hle₁ _ h₁) (hle₂ _ h₂)

/-- Helper for Lemma 13.37.4: the finite-support diagram of a family has colimit the ambient
coproduct. -/
private noncomputable def finiteSubcoproductsColimitIso
    {C : Type*} [Category C] [HasFiniteCoproducts C]
    {ι : Type*} [HasColimitsOfShape (Finset (Discrete ι)) C]
    [HasColimitsOfShape (Discrete ι) C] (F : ι → C) :
    ∐ F ≅ colimit (liftToFinsetObj (Discrete.functor F)) :=
  (isColimitFiniteSubproductsCocone F).coconePointUniqueUpToIso
    (colimit.isColimit (liftToFinsetObj (Discrete.functor F)))

/-- Helper for Lemma 13.37.4: the finite-support comparison sends a finite-stage inclusion to the
corresponding colimit leg. -/
private theorem finiteSubcoproductsColimitIso_hom_app
    {C : Type*} [Category C] [HasFiniteCoproducts C]
    {ι : Type*} [HasColimitsOfShape (Finset (Discrete ι)) C]
    [HasColimitsOfShape (Discrete ι) C] (F : ι → C) (s : Finset (Discrete ι)) :
    Limits.Sigma.desc (fun i : s ↦ Limits.Sigma.ι F i.1.as) ≫
        (finiteSubcoproductsColimitIso F).hom =
      colimit.ι (liftToFinsetObj (Discrete.functor F)) s := by
  -- The colimit comparison is characterized by the finite-support cocone legs.
  rw [show Limits.Sigma.desc (fun i : s ↦ Limits.Sigma.ι F i.1.as) =
      (finiteSubcoproductsCocone F).ι.app s by
      rw [finiteSubcoproductsCocone_ι_app]]
  simpa [finiteSubcoproductsColimitIso] using
    (IsColimit.comp_coconePointUniqueUpToIso_hom
      (isColimitFiniteSubproductsCocone F)
      (colimit.isColimit (liftToFinsetObj (Discrete.functor F)))
      s)

/-- Helper for Lemma 13.37.4: on a singleton stage, the finite-support comparison is the ordinary
summand inclusion into the filtered colimit. -/
private theorem finiteSubcoproductsColimitIso_hom_singleton
    {C : Type*} [Category C] [HasFiniteCoproducts C]
    {ι : Type*} [HasColimitsOfShape (Finset (Discrete ι)) C]
    [HasColimitsOfShape (Discrete ι) C] (F : ι → C) (i : Discrete ι) :
    Limits.Sigma.desc
        (fun j : ({i} : Finset (Discrete ι)) ↦ Limits.Sigma.ι F j.1.as) ≫
        (finiteSubcoproductsColimitIso F).hom =
      colimit.ι (liftToFinsetObj (Discrete.functor F)) ({i} : Finset (Discrete ι)) := by
  simpa using finiteSubcoproductsColimitIso_hom_app F ({i} : Finset (Discrete ι))

/-- Helper for Lemma 13.37.4: the inverse finite-support comparison recovers the explicit
finite-stage coproduct inclusion. -/
private theorem finiteSubcoproductsColimitIso_inv_app
    {C : Type*} [Category C] [HasFiniteCoproducts C]
    {ι : Type*} [HasColimitsOfShape (Finset (Discrete ι)) C]
    [HasColimitsOfShape (Discrete ι) C] (F : ι → C) (s : Finset (Discrete ι)) :
    colimit.ι (liftToFinsetObj (Discrete.functor F)) s ≫
        (finiteSubcoproductsColimitIso F).inv =
      Limits.Sigma.desc (fun i : s ↦ Limits.Sigma.ι F i.1.as) := by
  -- The inverse comparison is determined by the same cocone-leg computation.
  rw [show Limits.Sigma.desc (fun i : s ↦ Limits.Sigma.ι F i.1.as) =
      (finiteSubcoproductsCocone F).ι.app s by
      rw [finiteSubcoproductsCocone_ι_app]]
  simpa [finiteSubcoproductsColimitIso] using
    (IsColimit.comp_coconePointUniqueUpToIso_inv
      (isColimitFiniteSubproductsCocone F)
      (colimit.isColimit (liftToFinsetObj (Discrete.functor F)))
      s)

/-- Helper for Lemma 13.37.4: the inverse coproduct comparison identifies a summand inclusion on
the image coproduct with the image of the original summand inclusion for any coproduct-preserving
functor. -/
private theorem functor_coproductComparisonInv_ι
    {A : Type*} [Category A] (H : D ⥤ A)
    {K : Type*} (L : K → D)
    [HasCoproduct L]
    [HasCoproduct fun i ↦ H.obj (L i)]
    [PreservesColimitsOfShape (Discrete K) H]
    (k : K) :
    Sigma.ι (fun i ↦ H.obj (L i)) k ≫ (PreservesCoproduct.iso H L).inv =
      H.map (Sigma.ι L k) := by
  -- Rewrite the coproduct comparison through `sigmaComparison`, then cancel the inverse
  -- comparison on the right summand inclusion.
  have hhom :
      (PreservesCoproduct.iso H L).hom =
        inv (sigmaComparison H L) := by
    apply IsIso.eq_inv_of_hom_inv_id
    simpa [PreservesCoproduct.inv_hom] using
      (Iso.inv_hom_id (PreservesCoproduct.iso H L))
  have hι :
      H.map (Sigma.ι L k) ≫ (PreservesCoproduct.iso H L).hom =
        Sigma.ι (fun i ↦ H.obj (L i)) k := by
    rw [hhom]
    change H.map (Sigma.ι L k) ≫ inv (sigmaComparison H L) =
      Sigma.ι (fun i ↦ H.obj (L i)) k
    exact Limits.map_ι_comp_inv_sigmaComparison H L k
  calc
    Sigma.ι (fun i ↦ H.obj (L i)) k ≫ (PreservesCoproduct.iso H L).inv =
      (H.map (Sigma.ι L k) ≫ (PreservesCoproduct.iso H L).hom) ≫
        (PreservesCoproduct.iso H L).inv := by
          simpa [Category.assoc] using
            congrArg (fun t ↦ t ≫ (PreservesCoproduct.iso H L).inv) hι.symm
    _ = H.map (Sigma.ι L k) := by
          rw [hhom]
          simp

/-- Helper for Lemma 13.37.4: mapping a coproduct desc through `preadditiveCoyoneda` is the same
as first transporting to the coproduct of image objects and then descending there. -/
private theorem functor_sigmaDescEq
    {A : Type*} [Category A] (H : D ⥤ A)
    {B : D} {K : Type*} (L : K → D)
    [HasCoproduct L]
    [HasCoproduct fun i ↦ H.obj (L i)]
    [PreservesColimitsOfShape (Discrete K) H]
    (g : ∐ L ⟶ B) :
    Limits.Sigma.desc (fun k ↦ H.map (Sigma.ι L k ≫ g)) =
      (PreservesCoproduct.iso H L).inv ≫ H.map g := by
  -- Compare both coproduct maps on each summand after transporting the summand inclusion through
  -- the inverse coproduct comparison.
  apply Limits.Sigma.hom_ext
  intro k
  calc
    Sigma.ι (fun i ↦ H.obj (L i)) k ≫
        Limits.Sigma.desc (fun i ↦ H.map (Sigma.ι L i ≫ g)) =
      H.map (Sigma.ι L k ≫ g) := by
        rw [Limits.Sigma.ι_desc]
    _ = H.map (Sigma.ι L k) ≫ H.map g := by
        rw [Functor.map_comp]
    _ = (Sigma.ι (fun i ↦ H.obj (L i)) k ≫ (PreservesCoproduct.iso H L).inv) ≫ H.map g := by
        rw [functor_coproductComparisonInv_ι H L k]
    _ =
      Sigma.ι (fun i ↦ H.obj (L i)) k ≫
        ((PreservesCoproduct.iso H L).inv ≫ H.map g) := by
          simp

/-- Helper for Lemma 13.37.4: the inverse coproduct comparison identifies a summand inclusion on
the image coproduct with the image of the original summand inclusion. -/
private theorem preadditiveCoyoneda_coproductComparisonInv_ι
    {C : D} {K : Type*} (L : K → D)
    [HasCoproduct L]
    [HasCoproduct fun i ↦ (preadditiveCoyoneda.obj (op C)).obj (L i)]
    [PreservesColimitsOfShape (Discrete K) (preadditiveCoyoneda.obj (op C))]
    (k : K) :
    Sigma.ι (fun i ↦ (preadditiveCoyoneda.obj (op C)).obj (L i)) k ≫
        (PreservesCoproduct.iso (preadditiveCoyoneda.obj (op C)) L).inv =
      (preadditiveCoyoneda.obj (op C)).map (Sigma.ι L k) := by
  -- Reuse the functor-level comparison lemma at the represented additive Hom functor.
  simpa using
    functor_coproductComparisonInv_ι (preadditiveCoyoneda.obj (op C)) L k

/-- Helper for Lemma 13.37.4: mapping a coproduct desc through `preadditiveCoyoneda` is the same
as first transporting to the coproduct of Hom-groups and then descending there. -/
private theorem preadditiveCoyoneda_sigmaDescEq
    {C A : D} {K : Type*} (L : K → D)
    [HasCoproduct L]
    [HasCoproduct fun i ↦ (preadditiveCoyoneda.obj (op C)).obj (L i)]
    [PreservesColimitsOfShape (Discrete K) (preadditiveCoyoneda.obj (op C))]
    (g : ∐ L ⟶ A) :
    Limits.Sigma.desc
        (fun k ↦ (preadditiveCoyoneda.obj (op C)).map (Sigma.ι L k ≫ g)) =
      (PreservesCoproduct.iso (preadditiveCoyoneda.obj (op C)) L).inv ≫
        (preadditiveCoyoneda.obj (op C)).map g := by
  -- Reuse the functor-level coproduct-desc comparison at `preadditiveCoyoneda`.
  simpa using
    functor_sigmaDescEq (preadditiveCoyoneda.obj (op C)) L g

/-- Helper for Lemma 13.37.4: after transporting a coproduct along `PreservesCoproduct.iso`, the
image of a summand inclusion is the corresponding summand inclusion in the image coproduct. -/
private theorem functor_map_ι_comp_coproductComparisonHom
    {A : Type*} [Category A] (H : D ⥤ A)
    {K : Type*} (L : K → D)
    [HasCoproduct L]
    [HasCoproduct fun i ↦ H.obj (L i)]
    [PreservesColimitsOfShape (Discrete K) H]
    (k : K) :
    H.map (Sigma.ι L k) ≫ (PreservesCoproduct.iso H L).hom =
      Sigma.ι (fun i ↦ H.obj (L i)) k := by
  -- Rewrite the comparison isomorphism through the explicit `sigmaComparison`, then use the
  -- standard summand computation there.
  have hhom :
      (PreservesCoproduct.iso H L).hom =
        inv (sigmaComparison H L) := by
    apply IsIso.eq_inv_of_hom_inv_id
    simpa [PreservesCoproduct.inv_hom] using
      (Iso.inv_hom_id (PreservesCoproduct.iso H L))
  rw [hhom]
  simpa using Limits.map_ι_comp_inv_sigmaComparison H L k

/-- Helper for Lemma 13.37.4: the transported coproduct comparison `hom` is the inverse of the
standard `sigmaComparison`. -/
private theorem coproductComparisonHom_eq_inv_sigmaComparison
    {A : Type*} [Category A] (H : D ⥤ A)
    {K : Type*} (L : K → D)
    [HasCoproduct L]
    [HasCoproduct fun i ↦ H.obj (L i)]
    [PreservesColimitsOfShape (Discrete K) H] :
    (PreservesCoproduct.iso H L).hom = inv (sigmaComparison H L) := by
  apply IsIso.eq_inv_of_hom_inv_id
  simpa [PreservesCoproduct.inv_hom] using
    (Iso.inv_hom_id (PreservesCoproduct.iso H L))

/-- Helper for Lemma 13.37.4: transporting a finite-stage inclusion through the represented-Hom
coproduct comparisons gives the explicit inclusion into the full image coproduct. -/
private theorem functor_finiteStageInclusion
    {A : Type*} [Category A] (H : D ⥤ A)
    {K : Type*} (L : K → D)
    [HasCoproduct L]
    [HasCoproduct fun i ↦ H.obj (L i)]
    [PreservesColimitsOfShape (Discrete K) H]
    (s : Finset (Discrete K))
    [HasCoproduct fun i : s ↦ L i.1.as]
    [HasCoproduct fun i : s ↦ H.obj (L i.1.as)]
    [PreservesColimitsOfShape (Discrete ↥s) H] :
    (PreservesCoproduct.iso H (fun i : s ↦ L i.1.as)).inv ≫
        H.map (Limits.Sigma.desc (fun i : s ↦ Limits.Sigma.ι L i.1.as)) ≫
        (PreservesCoproduct.iso H L).hom =
      Limits.Sigma.desc
        (fun i : s ↦ Limits.Sigma.ι (fun k ↦ H.obj (L k)) i.1.as) := by
  -- Route correction: the finite-stage bridge is functorial, so later universe repairs can reuse
  -- the same normalization lemma after replacing `preadditiveCoyoneda` by an ulifted target.
  have hdesc :
      (PreservesCoproduct.iso H (fun i : s ↦ L i.1.as)).inv ≫
          H.map (Limits.Sigma.desc (fun i : s ↦ Limits.Sigma.ι L i.1.as)) =
        Limits.Sigma.desc
          (fun i : s ↦
            H.map
              (Sigma.ι (fun j : s ↦ L j.1.as) i ≫
                Limits.Sigma.desc (fun j : s ↦ Limits.Sigma.ι L j.1.as))) := by
    have hsigma :
        Limits.Sigma.desc
            (fun i : s ↦
              H.map
                (Sigma.ι (fun j : s ↦ L j.1.as) i ≫
                  Limits.Sigma.desc (fun j : s ↦ Limits.Sigma.ι L j.1.as))) =
          (PreservesCoproduct.iso H (fun i : s ↦ L i.1.as)).inv ≫
            H.map (Limits.Sigma.desc (fun i : s ↦ Limits.Sigma.ι L i.1.as)) :=
      functor_sigmaDescEq H (fun i : s ↦ L i.1.as)
        (Limits.Sigma.desc (fun i : s ↦ Limits.Sigma.ι L i.1.as))
    simpa using hsigma.symm
  calc
    (PreservesCoproduct.iso H (fun i : s ↦ L i.1.as)).inv ≫
        H.map (Limits.Sigma.desc (fun i : s ↦ Limits.Sigma.ι L i.1.as)) ≫
        (PreservesCoproduct.iso H L).hom =
      Limits.Sigma.desc
        (fun i : s ↦
          H.map
            (Sigma.ι (fun j : s ↦ L j.1.as) i ≫
              Limits.Sigma.desc (fun j : s ↦ Limits.Sigma.ι L j.1.as))) ≫
        (PreservesCoproduct.iso H L).hom := by
          simpa [Category.assoc] using
            congrArg (fun t ↦ t ≫ (PreservesCoproduct.iso H L).hom) hdesc
    _ =
      Limits.Sigma.desc
        (fun i : s ↦ Limits.Sigma.ι (fun k ↦ H.obj (L k)) i.1.as) := by
        apply Limits.Sigma.hom_ext
        intro i
        calc
          Sigma.ι (fun j : s ↦ H.obj (L j.1.as)) i ≫
              Limits.Sigma.desc
                (fun j : s ↦
                  H.map
                    (Sigma.ι (fun k : s ↦ L k.1.as) j ≫
                      Limits.Sigma.desc (fun k : s ↦ Limits.Sigma.ι L k.1.as))) ≫
              (PreservesCoproduct.iso H L).hom =
            H.map
                (Sigma.ι (fun j : s ↦ L j.1.as) i ≫
                  Limits.Sigma.desc (fun j : s ↦ Limits.Sigma.ι L j.1.as)) ≫
              (PreservesCoproduct.iso H L).hom := by
                simpa [Category.assoc] using
                  congrArg
                    (fun t ↦ t ≫ (PreservesCoproduct.iso H L).hom)
                    (Limits.Sigma.ι_desc
                      (fun j : s ↦
                        H.map
                          (Sigma.ι (fun k : s ↦ L k.1.as) j ≫
                            Limits.Sigma.desc (fun k : s ↦ Limits.Sigma.ι L k.1.as)))
                      i)
          _ = H.map (Sigma.ι L i.1.as) ≫ (PreservesCoproduct.iso H L).hom := by
                simpa using
                  congrArg
                    (fun t ↦ H.map t ≫ (PreservesCoproduct.iso H L).hom)
                    (Limits.Sigma.ι_desc (fun j : s ↦ Limits.Sigma.ι L j.1.as) i)
          _ = Sigma.ι (fun k ↦ H.obj (L k)) i.1.as := by
                simpa using
                  functor_map_ι_comp_coproductComparisonHom H L i.1.as
          _ =
            Sigma.ι (fun j : s ↦ H.obj (L j.1.as)) i ≫
              Limits.Sigma.desc
                (fun j : s ↦ Limits.Sigma.ι (fun k ↦ H.obj (L k)) j.1.as) := by
                simpa using
                  (Limits.Sigma.ι_desc
                    (fun j : s ↦ Limits.Sigma.ι (fun k ↦ H.obj (L k)) j.1.as)
                    i).symm

/-- Helper for Lemma 13.37.4: transporting a finite-stage inclusion through the represented-Hom
coproduct comparisons gives the explicit inclusion into the full image coproduct. -/
private theorem preadditiveCoyoneda_finiteStageInclusion
    {C : D} {K : Type*} (L : K → D)
    [HasCoproduct L]
    [HasCoproduct fun i ↦ (preadditiveCoyoneda.obj (op C)).obj (L i)]
    [PreservesColimitsOfShape (Discrete K) (preadditiveCoyoneda.obj (op C))]
    (s : Finset (Discrete K))
    [HasCoproduct fun i : s ↦ L i.1.as]
    [HasCoproduct fun i : s ↦ (preadditiveCoyoneda.obj (op C)).obj (L i.1.as)]
    [PreservesColimitsOfShape (Discrete ↥s) (preadditiveCoyoneda.obj (op C))] :
    (PreservesCoproduct.iso (preadditiveCoyoneda.obj (op C)) (fun i : s ↦ L i.1.as)).inv ≫
        (preadditiveCoyoneda.obj (op C)).map
          (Limits.Sigma.desc (fun i : s ↦ Limits.Sigma.ι L i.1.as)) ≫
    (PreservesCoproduct.iso (preadditiveCoyoneda.obj (op C)) L).hom =
      Limits.Sigma.desc
        (fun i : s ↦
          Limits.Sigma.ι
            (fun k ↦ (preadditiveCoyoneda.obj (op C)).obj (L k))
            i.1.as) := by
  simpa using functor_finiteStageInclusion (preadditiveCoyoneda.obj (op C)) L s

/-- Helper for Lemma 13.37.4: every element of the finite-support colimit of an image coproduct
is already represented at one finite stage. -/
private theorem existsFiniteSupportRepresentativeOfImageCoproduct
    {J : Type r} (G : J → AddCommGrpCat.{r})
    [HasColimit (liftToFinsetObj (Discrete.functor G))]
    (z : (colimit
      (liftToFinsetObj (Discrete.functor G)) :
        AddCommGrpCat.{r})) :
    ∃ s : Finset (Discrete J), ∃ x :
      (liftToFinsetObj (Discrete.functor G)).obj s,
      colimit.ι
          (liftToFinsetObj (Discrete.functor G)) s x = z := by
  letI : IsFiltered (Finset (Discrete J)) := inferInstance
  letI : PreservesFilteredColimits (forget AddCommGrpCat.{r}) :=
    AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits
  letI : PreservesFilteredColimitsOfSize.{0, 0} (forget AddCommGrpCat.{r}) :=
    CategoryTheory.Limits.preservesFilteredColimitsOfSize_shrink
      (forget AddCommGrpCat.{r})
  letI : PreservesColimit (liftToFinsetObj (Discrete.functor G)) (forget AddCommGrpCat.{r}) := by
    infer_instance
  -- Concrete filtered colimits in `AddCommGrpCat` are jointly covered by the finite-stage legs.
  exact Concrete.colimit_exists_rep (liftToFinsetObj (Discrete.functor G)) z

/-- Helper for Lemma 13.37.4: the finite-support filtered-colimit model exists for every
`Type (max u v)`-indexed image family in `AddCommGrpCat`. -/
private theorem imageCoproductFiniteSupportHasColimit
    {J : Type (max u v)} (G : J → AddCommGrpCat.{max u v}) :
    HasColimit (liftToFinsetObj (Discrete.functor G)) := by
  infer_instance

/-- Helper for Lemma 13.37.4: evaluating the image of a finite-stage coproduct desc on a point of
the image coproduct is the same as first transporting that point across `sigmaComparison`. -/
private theorem functorMapDesc_sigmaComparison_apply
    (H : D ⥤ AddCommGrpCat.{r})
    {K : Type*} (L : K → D)
    [HasCoproduct L]
    (s : Finset (Discrete K))
    [HasCoproduct fun i : s ↦ L i.1.as]
    [HasCoproduct fun i : s ↦ H.obj (L i.1.as)]
    [PreservesColimitsOfShape (Discrete ↥s) H]
    (x : (∐ fun i : s ↦ H.obj (L i.1.as) : AddCommGrpCat.{r})) :
    H.map (Limits.Sigma.desc (fun k : s ↦ Limits.Sigma.ι L k.1.as))
        ((sigmaComparison H (fun k : s ↦ L k.1.as)) x) =
      (Limits.Sigma.desc (fun i : s ↦ H.map (Limits.Sigma.ι L i.1.as))) x := by
  have hinv :
      (PreservesCoproduct.iso H (fun i : s ↦ L i.1.as)).inv =
        sigmaComparison H (fun i : s ↦ L i.1.as) := by
    -- The inverse preserved-coproduct comparison is definitionally `sigmaComparison`.
    rfl
  have hdesc :
      Limits.Sigma.desc (fun i : s ↦ H.map (Limits.Sigma.ι L i.1.as)) =
        sigmaComparison H (fun i : s ↦ L i.1.as) ≫
          H.map (Limits.Sigma.desc (fun i : s ↦ Limits.Sigma.ι L i.1.as)) := by
    -- Normalize the transported desc map before evaluating it at the chosen representative.
    simpa [hinv] using
      (functor_sigmaDescEq H (fun i : s ↦ L i.1.as)
        (Limits.Sigma.desc (fun i : s ↦ Limits.Sigma.ι L i.1.as)))
  -- Apply the normalized morphism equality to the chosen representative.
  rw [hdesc]
  rfl

/-- Helper for Lemma 13.37.4: a compact map into a `Type (max u v)`-indexed coproduct factors
through a finite subcoproduct. -/
private theorem factorThroughFiniteSubcoproductSmall
    {C : D} (hC : IsCompactObject C)
    {J : Type (max u v)} (L : J → D) [HasCoproduct L] (f : C ⟶ ∐ L) :
    ∃ (K : Type (max u v)) (_ : Finite K) (τ : K → J)
      (g : C ⟶ ∐ fun k : K ↦ L (τ k)) (h : (∐ fun k : K ↦ L (τ k)) ⟶ ∐ L),
      g ≫ h = f := by
  let H : D ⥤ AddCommGrpCat.{v} := preadditiveCoyoneda.obj (op C)
  let Hlift : D ⥤ AddCommGrpCat.{max u v} := H ⋙ AddCommGrpCat.uliftFunctor.{max u v, v}
  let G : J → AddCommGrpCat.{max u v} := fun j ↦ Hlift.obj (L j)
  let z :
      (colimit (liftToFinsetObj (Discrete.functor G)) :
        AddCommGrpCat.{max u v}) :=
    (((PreservesCoproduct.iso Hlift L).hom ≫ (finiteSubcoproductsColimitIso G).hom) (ULift.up f))
  -- First choose a finite stage representing the image of `f` inside the filtered colimit model.
  obtain ⟨s, x, hx⟩ := existsFiniteSupportRepresentativeOfImageCoproduct G z
  let gLift :
      Hlift.obj (∐ fun k : s ↦ L k.1.as) :=
    (sigmaComparison Hlift (fun k : s ↦ L k.1.as)) x
  refine
    ⟨s, inferInstance, fun k ↦ k.1.as,
      gLift.down,
      Limits.Sigma.desc (fun k : s ↦ Limits.Sigma.ι L k.1.as), ?_⟩
  have hz :
      (Limits.Sigma.desc
          (fun i : s ↦
            Limits.Sigma.ι (fun k ↦ Hlift.obj (L k)) i.1.as)) x =
        ((PreservesCoproduct.iso Hlift L).hom) (ULift.up f) := by
    -- Move the chosen representative back across the finite-support colimit comparison.
    have hleft :
        ((colimit.ι (liftToFinsetObj (Discrete.functor G)) s) ≫
            (finiteSubcoproductsColimitIso G).inv) x =
          (Limits.Sigma.desc
              (fun i : s ↦
                Limits.Sigma.ι (fun k ↦ Hlift.obj (L k)) i.1.as)) x := by
      simpa [G] using
        congrArg
          (fun t ↦ t x)
          (finiteSubcoproductsColimitIso_inv_app G s)
    have hright :
        ((colimit.ι (liftToFinsetObj (Discrete.functor G)) s) ≫
            (finiteSubcoproductsColimitIso G).inv) x =
          ((PreservesCoproduct.iso Hlift L).hom) (ULift.up f) := by
      simpa [z] using
        congrArg (fun y ↦ (finiteSubcoproductsColimitIso G).inv y) hx
    exact hleft.symm.trans hright
  have himage :
      ((PreservesCoproduct.iso Hlift L).hom)
          (Hlift.map (Limits.Sigma.desc (fun k : s ↦ Limits.Sigma.ι L k.1.as)) gLift) =
        ((PreservesCoproduct.iso Hlift L).hom) (ULift.up f) := by
    -- The finite-stage inclusion computed under `preadditiveCoyoneda` matches the original image
    -- of `f` in the ambient coproduct of Hom-groups.
    have hstage :
        ((PreservesCoproduct.iso Hlift L).hom)
            (Hlift.map (Limits.Sigma.desc (fun k : s ↦ Limits.Sigma.ι L k.1.as)) gLift) =
          (Limits.Sigma.desc
              (fun i : s ↦
                Limits.Sigma.ι (fun k ↦ Hlift.obj (L k)) i.1.as)) x := by
      -- First evaluate the finite-stage desc on the chosen representative in the image coproduct.
      have hdesc_eval :
          Hlift.map (Limits.Sigma.desc (fun k : s ↦ Limits.Sigma.ι L k.1.as)) gLift =
            (Limits.Sigma.desc
                (fun i : s ↦ Hlift.map (Limits.Sigma.ι L i.1.as))) x := by
        -- Evaluate the normalized finite-stage desc at the chosen representative.
        simpa [gLift] using
          functorMapDesc_sigmaComparison_apply Hlift L s x
      have hraw :
          ((PreservesCoproduct.iso Hlift L).hom)
              ((Limits.Sigma.desc
                  (fun i : s ↦ Hlift.map (Limits.Sigma.ι L i.1.as))) x) =
            (Limits.Sigma.desc
                (fun i : s ↦
                  Limits.Sigma.ι (fun k ↦ Hlift.obj (L k)) i.1.as)) x := by
        simpa [Category.assoc] using
          congrArg
            (fun t ↦ t x)
            (functor_finiteStageInclusion Hlift L s)
      calc
        ((PreservesCoproduct.iso Hlift L).hom)
            (Hlift.map (Limits.Sigma.desc (fun k : s ↦ Limits.Sigma.ι L k.1.as)) gLift) =
          ((PreservesCoproduct.iso Hlift L).hom)
              ((Limits.Sigma.desc
                  (fun i : s ↦ Hlift.map (Limits.Sigma.ι L i.1.as))) x) := by
                    rw [hdesc_eval]
        _ =
          (Limits.Sigma.desc
              (fun i : s ↦
                Limits.Sigma.ι (fun k ↦ Hlift.obj (L k)) i.1.as)) x := hraw
    exact hstage.trans hz
  -- Finally cancel the represented-Hom coproduct comparison to recover the original morphism.
  have hfinalLift :
      Hlift.map (Limits.Sigma.desc (fun k : s ↦ Limits.Sigma.ι L k.1.as)) gLift =
        ULift.up f := by
    exact (ConcreteCategory.bijective_of_isIso (PreservesCoproduct.iso Hlift L).hom).1 himage
  simpa [Hlift, gLift] using congrArg ULift.down hfinalLift

/-- Helper for Lemma 13.37.4: a compact map into a coproduct factors through a finite
subcoproduct. -/
private theorem factorThroughFiniteSubcoproduct
    [UnivLE.{max u v w, max u v}] {C : D} (hC : IsCompactObject C)
    {J : Type (max u v w)} (L : J → D) (f : C ⟶ ∐ L) :
    ∃ (K : Type (max u v w)) (_ : Finite K) (τ : K → J)
      (g : C ⟶ ∐ fun k : K ↦ L (τ k)) (h : (∐ fun k : K ↦ L (τ k)) ⟶ ∐ L),
      g ≫ h = f := by
  let H : D ⥤ AddCommGrpCat.{v} := preadditiveCoyoneda.obj (op C)
  let Hlift : D ⥤ AddCommGrpCat.{max u v w} := H ⋙ AddCommGrpCat.uliftFunctor.{max u v w, v}
  let _ : IsCompactObject C := hC
  have hH :
      PreservesColimitsOfShape (Discrete J) (preadditiveCoyoneda.obj (op C)) := by
    infer_instance
  let _ : PreservesColimitsOfShape (Discrete J) H := by
    simpa [H] using hH
  haveI : PreservesColimitsOfShape (Discrete J) Hlift := by
    dsimp [Hlift]
    infer_instance
  let G : J → AddCommGrpCat.{max u v w} := fun j ↦ Hlift.obj (L j)
  let z :
      (colimit (liftToFinsetObj (Discrete.functor G)) :
        AddCommGrpCat.{max u v w}) :=
    (((PreservesCoproduct.iso Hlift L).hom ≫ (finiteSubcoproductsColimitIso G).hom) (ULift.up f))
  -- Represent the image of `f` by a concrete point at one finite stage of the filtered colimit.
  obtain ⟨s, x, hx⟩ := existsFiniteSupportRepresentativeOfImageCoproduct G z
  let gLift :
      Hlift.obj (∐ fun k : s ↦ L k.1.as) :=
    (sigmaComparison Hlift (fun k : s ↦ L k.1.as)) x
  refine
    ⟨s, inferInstance, fun k ↦ k.1.as,
      gLift.down,
      Limits.Sigma.desc (fun k : s ↦ Limits.Sigma.ι L k.1.as), ?_⟩
  have hz :
      (Limits.Sigma.desc
          (fun i : s ↦
            Limits.Sigma.ι (fun k ↦ Hlift.obj (L k)) i.1.as)) x =
        ((PreservesCoproduct.iso Hlift L).hom) (ULift.up f) := by
    -- Move the chosen representative back through the finite-support colimit comparison.
    have hleft :
        ((colimit.ι (liftToFinsetObj (Discrete.functor G)) s) ≫
            (finiteSubcoproductsColimitIso G).inv) x =
          (Limits.Sigma.desc
              (fun i : s ↦
                Limits.Sigma.ι (fun k ↦ Hlift.obj (L k)) i.1.as)) x := by
      simpa [G] using
        congrArg
          (fun t ↦ t x)
          (finiteSubcoproductsColimitIso_inv_app G s)
    have hright :
        ((colimit.ι (liftToFinsetObj (Discrete.functor G)) s) ≫
            (finiteSubcoproductsColimitIso G).inv) x =
          ((PreservesCoproduct.iso Hlift L).hom) (ULift.up f) := by
      simpa [z] using
        congrArg (fun y ↦ (finiteSubcoproductsColimitIso G).inv y) hx
    exact hleft.symm.trans hright
  have himage :
      ((PreservesCoproduct.iso Hlift L).hom)
          (Hlift.map (Limits.Sigma.desc (fun k : s ↦ Limits.Sigma.ι L k.1.as)) gLift) =
        ((PreservesCoproduct.iso Hlift L).hom) (ULift.up f) := by
    -- Evaluate the finite-stage inclusion in the image coproduct and compare it with `z`.
    have hstage :
        ((PreservesCoproduct.iso Hlift L).hom)
            (Hlift.map (Limits.Sigma.desc (fun k : s ↦ Limits.Sigma.ι L k.1.as)) gLift) =
          (Limits.Sigma.desc
              (fun i : s ↦
                Limits.Sigma.ι (fun k ↦ Hlift.obj (L k)) i.1.as)) x := by
      have hdesc_eval :
          Hlift.map (Limits.Sigma.desc (fun k : s ↦ Limits.Sigma.ι L k.1.as)) gLift =
            (Limits.Sigma.desc
                (fun i : s ↦ Hlift.map (Limits.Sigma.ι L i.1.as))) x := by
        -- Normalize the evaluation of the desc map at the chosen representative.
        simpa [gLift] using
          functorMapDesc_sigmaComparison_apply Hlift L s x
      have hraw :
          ((PreservesCoproduct.iso Hlift L).hom)
              ((Limits.Sigma.desc
                  (fun i : s ↦ Hlift.map (Limits.Sigma.ι L i.1.as))) x) =
            (Limits.Sigma.desc
                (fun i : s ↦
                  Limits.Sigma.ι (fun k ↦ Hlift.obj (L k)) i.1.as)) x := by
        simpa [Category.assoc] using
          congrArg
            (fun t ↦ t x)
            (functor_finiteStageInclusion Hlift L s)
      calc
        ((PreservesCoproduct.iso Hlift L).hom)
            (Hlift.map (Limits.Sigma.desc (fun k : s ↦ Limits.Sigma.ι L k.1.as)) gLift) =
          ((PreservesCoproduct.iso Hlift L).hom)
              ((Limits.Sigma.desc
                  (fun i : s ↦ Hlift.map (Limits.Sigma.ι L i.1.as))) x) := by
                    rw [hdesc_eval]
        _ =
          (Limits.Sigma.desc
              (fun i : s ↦
                Limits.Sigma.ι (fun k ↦ Hlift.obj (L k)) i.1.as)) x := hraw
    exact hstage.trans hz
  -- Cancel the represented-Hom coproduct comparison to recover the original morphism `f`.
  have hfinalLift :
      Hlift.map (Limits.Sigma.desc (fun k : s ↦ Limits.Sigma.ι L k.1.as)) gLift =
        ULift.up f := by
    exact (ConcreteCategory.bijective_of_isIso (PreservesCoproduct.iso Hlift L).hom).1 himage
  simpa [Hlift, gLift] using congrArg ULift.down hfinalLift

/-- Helper for Lemma 13.37.4: a finite coproduct of shifted compact generators is compact. -/
private theorem finiteShiftCoproduct_isCompactObject
    (hcompact : ∀ i : I, IsCompactObject (E i))
    {K : Type (max u v w)} [Finite K] (τ : K → I) (s : K → ℤ) :
    IsCompactObject (∐ fun k : K ↦ E (τ k)⟦s k⟧) := by
  let P : ObjectProperty D := IsCompactObject
  let _ : P.IsClosedUnderFiniteCoproducts := inferInstance
  have hsummand : ∀ k : K, P (E (τ k)⟦s k⟧) := by
    intro k
    -- Compactness is triangulated, so every shift of a compact generator stays compact.
    exact P.le_shift (s k) _ (hcompact (τ k))
  simpa [P] using P.prop_coproduct hsummand

/-- Helper for Lemma 13.37.4: a map from a compact object into an arbitrary direct sum of shifts
of the generators already factors through a finite shifted subcoproduct. -/
private theorem compactFactorThroughFiniteShiftCoproductOfIsDirectSumOfShifts
    [UnivLE.{max u v w, max u v}]
    {X C : D} (hX : IsDirectSumOfShifts E X) (hC : IsCompactObject C) (f : C ⟶ X) :
    ∃ (K : Type (max u v w)) (_ : Finite K) (τ : K → I) (s : K → ℤ),
      let A : D := ∐ fun k : K ↦ E (τ k)⟦s k⟧
      ∃ (g : C ⟶ A) (h : A ⟶ X), g ≫ h = f := by
  rcases hX with ⟨J, τ, σ, ⟨e⟩⟩
  let L : J → D := fun j ↦ E (τ j)⟦σ j⟧
  -- Factor the pullback of `f` to the explicit direct-sum witness through a finite subcoproduct.
  obtain ⟨K, hK, κ, g, h, hg⟩ := factorThroughFiniteSubcoproduct hC L (f ≫ e.inv)
  refine ⟨K, hK, fun i ↦ τ (κ i), fun i ↦ σ (κ i), g, ?_, ?_⟩
  · exact h ≫ e.hom
  · -- Postcompose the finite-stage factorization with the witness isomorphism back to `X`.
    calc
      g ≫ (h ≫ e.hom) =
          (g ≫ h) ≫ e.hom := by
            simp [Category.assoc]
      _ = (f ≫ e.inv) ≫ e.hom := by rw [hg]
      _ = f := by simp [Category.assoc]

/-- Helper for Lemma 13.37.4: after shifting the source back by `-1`, a compact map into
`X⟦1⟧` factors through the shift of a finite shifted coproduct. -/
private theorem compactFactorThroughFiniteShiftOfDirectSumOfShifts
    [UnivLE.{max u v w, max u v}]
    {X C : D} (hX : IsDirectSumOfShifts E X) (hC : IsCompactObject C)
    (f : C ⟶ X⟦(1 : ℤ)⟧) :
    ∃ (K : Type (max u v w)) (_ : Finite K) (τ : K → I) (s : K → ℤ),
      let A : D := ∐ fun k : K ↦ E (τ k)⟦s k⟧
      ∃ (g : C ⟶ A⟦(1 : ℤ)⟧) (h : A⟦(1 : ℤ)⟧ ⟶ X⟦(1 : ℤ)⟧), g ≫ h = f := by
  -- Route correction: shift the source back, factor there, and transport the factorization
  -- forward across the standard shift comparison isomorphisms.
  let P : ObjectProperty D := IsCompactObject
  have hCshift : IsCompactObject (C⟦(-1 : ℤ)⟧) := by
    -- Compactness is stable under shifts, so the shifted source is still compact.
    simpa [P] using P.le_shift (-1 : ℤ) C hC
  let f' : C⟦(-1 : ℤ)⟧ ⟶ X :=
    f⟦(-1 : ℤ)⟧' ≫
      (shiftFunctorCompIsoId D (1 : ℤ) (-1 : ℤ) (add_neg_cancel (1 : ℤ))).hom.app X
  obtain ⟨J, hJ, ι, s, g', h', hg'h'⟩ :=
    compactFactorThroughFiniteShiftCoproductOfIsDirectSumOfShifts E hX hCshift f'
  letI : Finite J := hJ
  let A : D := ∐ fun j : J ↦ E (ι j)⟦s j⟧
  have hshiftComp :
      ((shiftFunctorCompIsoId D (1 : ℤ) (-1 : ℤ) (add_neg_cancel (1 : ℤ))).hom.app X)⟦(1 : ℤ)⟧' =
        (shiftFunctorCompIsoId D (-1 : ℤ) (1 : ℤ)
          (neg_add_cancel (1 : ℤ))).hom.app (X⟦(1 : ℤ)⟧) := by
    simpa using
      (shift_shiftFunctorCompIsoId_add_neg_cancel_hom_app
        (1 : ℤ) X)
  have hshiftCompAssoc :
      (shiftFunctorCompIsoId D (-1 : ℤ) (1 : ℤ) (neg_add_cancel (1 : ℤ))).inv.app C ≫
          f⟦(-1 : ℤ)⟧'⟦(1 : ℤ)⟧' ≫
            ((shiftFunctorCompIsoId D (1 : ℤ) (-1 : ℤ)
              (add_neg_cancel (1 : ℤ))).hom.app X)⟦(1 : ℤ)⟧' =
        (shiftFunctorCompIsoId D (-1 : ℤ) (1 : ℤ) (neg_add_cancel (1 : ℤ))).inv.app C ≫
          f⟦(-1 : ℤ)⟧'⟦(1 : ℤ)⟧' ≫
            (shiftFunctorCompIsoId D (-1 : ℤ) (1 : ℤ)
              (neg_add_cancel (1 : ℤ))).hom.app (X⟦(1 : ℤ)⟧) := by
    -- Rewrite the shifted comparison isomorphism once, without unfolding the whole construction.
    simpa [Category.assoc] using
      congrArg
        (fun t ↦
          (shiftFunctorCompIsoId D (-1 : ℤ) (1 : ℤ) (neg_add_cancel (1 : ℤ))).inv.app C ≫
            f⟦(-1 : ℤ)⟧'⟦(1 : ℤ)⟧' ≫ t)
        hshiftComp
  refine ⟨J, hJ, ι, s, ?_, h'⟦(1 : ℤ)⟧', ?_⟩
  · -- Shift the source-side factorization forward and identify `C` with `C⟦-1⟧⟦1⟧`.
    exact
      (shiftFunctorCompIsoId D (-1 : ℤ) (1 : ℤ) (neg_add_cancel (1 : ℤ))).inv.app C ≫
        g'⟦(1 : ℤ)⟧'
  · have hfactorShift :
        ((shiftFunctorCompIsoId D (-1 : ℤ) (1 : ℤ) (neg_add_cancel (1 : ℤ))).inv.app C ≫
            g'⟦(1 : ℤ)⟧') ≫
            h'⟦(1 : ℤ)⟧' =
          (shiftFunctorCompIsoId D (-1 : ℤ) (1 : ℤ) (neg_add_cancel (1 : ℤ))).inv.app C ≫
            f⟦(-1 : ℤ)⟧'⟦(1 : ℤ)⟧' ≫
              ((shiftFunctorCompIsoId D (1 : ℤ) (-1 : ℤ)
                (add_neg_cancel (1 : ℤ))).hom.app X)⟦(1 : ℤ)⟧' := by
      calc
        ((shiftFunctorCompIsoId D (-1 : ℤ) (1 : ℤ) (neg_add_cancel (1 : ℤ))).inv.app C ≫
            g'⟦(1 : ℤ)⟧') ≫
            h'⟦(1 : ℤ)⟧' =
          (shiftFunctorCompIsoId D (-1 : ℤ) (1 : ℤ) (neg_add_cancel (1 : ℤ))).inv.app C ≫
            (g' ≫ h')⟦(1 : ℤ)⟧' := by
              simp [Functor.map_comp, Category.assoc]
        _ =
          (shiftFunctorCompIsoId D (-1 : ℤ) (1 : ℤ) (neg_add_cancel (1 : ℤ))).inv.app C ≫
            f'⟦(1 : ℤ)⟧' := by
              rw [hg'h']
        _ =
          (shiftFunctorCompIsoId D (-1 : ℤ) (1 : ℤ) (neg_add_cancel (1 : ℤ))).inv.app C ≫
            (f⟦(-1 : ℤ)⟧' ≫
                (shiftFunctorCompIsoId D (1 : ℤ) (-1 : ℤ)
                  (add_neg_cancel (1 : ℤ))).hom.app X)⟦(1 : ℤ)⟧' := by
              rfl
        _ =
          (shiftFunctorCompIsoId D (-1 : ℤ) (1 : ℤ) (neg_add_cancel (1 : ℤ))).inv.app C ≫
            f⟦(-1 : ℤ)⟧'⟦(1 : ℤ)⟧' ≫
              ((shiftFunctorCompIsoId D (1 : ℤ) (-1 : ℤ)
                (add_neg_cancel (1 : ℤ))).hom.app X)⟦(1 : ℤ)⟧' := by
              simp [Functor.map_comp]
    have hfinal :
        (shiftFunctorCompIsoId D (-1 : ℤ) (1 : ℤ) (neg_add_cancel (1 : ℤ))).inv.app C ≫
          f⟦(-1 : ℤ)⟧'⟦(1 : ℤ)⟧' ≫
            (shiftFunctorCompIsoId D (-1 : ℤ) (1 : ℤ)
              (neg_add_cancel (1 : ℤ))).hom.app (X⟦(1 : ℤ)⟧) = f := by
      simpa [Category.assoc] using
        (shiftFunctorCompIsoId_naturality_1
          f (-1 : ℤ) (1 : ℤ) (neg_add_cancel (1 : ℤ)))
    exact hfactorShift.trans (hshiftCompAssoc.trans hfinal)

/-- Helper for Lemma 13.37.4: the finite shifted coproduct factorization can be recast as a
factorization through an object of `⟨∐ fun j ↦ E (ι j)⟩`. -/
private theorem compactFactorThroughGeneratedOfDirectSumOfShifts
    [UnivLE.{max u v w, max u v}]
    {X C : D} (hX : IsDirectSumOfShifts E X) (hC : IsCompactObject C) (f : C ⟶ X) :
    ∃ (A : D) (J : Type (max u v w)) (_ : Finite J) (ι : J → I),
      ⟨∐ fun j : J ↦ E (ι j)⟩ A ∧
      ∃ (g : C ⟶ A) (h : A ⟶ X), g ≫ h = f := by
  -- Replace the explicit finite shifted coproduct by its generated-property membership.
  obtain ⟨K, hK, τ, s, g, h, hgh⟩ :=
    compactFactorThroughFiniteShiftCoproductOfIsDirectSumOfShifts
      E hX hC f
  letI : Finite K := hK
  refine ⟨∐ fun k : K ↦ E (τ k)⟦s k⟧, K, hK, τ, ?_, g, h, hgh⟩
  simpa using finiteShiftCoproduct_mem_objectGeneratedProperty E τ s

/-- Helper for Lemma 13.37.4: after shifting the source back by `-1`, a factorization through an
object of `⟨∐ fun j ↦ E (ι j)⟩` can be shifted forward to factor maps into `X⟦1⟧`. -/
private theorem compactFactorThroughGeneratedShiftOfDirectSumOfShifts
    [UnivLE.{max u v w, max u v}]
    {X C : D} (hX : IsDirectSumOfShifts E X) (hC : IsCompactObject C)
    (f : C ⟶ X⟦(1 : ℤ)⟧) :
    ∃ (A : D) (J : Type (max u v w)) (_ : Finite J) (ι : J → I),
      ⟨∐ fun j : J ↦ E (ι j)⟩ A ∧
      ∃ (g : C ⟶ A⟦(1 : ℤ)⟧) (h : A⟦(1 : ℤ)⟧ ⟶ X⟦(1 : ℤ)⟧), g ≫ h = f := by
  obtain ⟨J, hJ, ι, s, g, h, hgh⟩ :=
    compactFactorThroughFiniteShiftOfDirectSumOfShifts E hX hC f
  letI : Finite J := hJ
  refine ⟨∐ fun j : J ↦ E (ι j)⟦s j⟧, J, hJ, ι, ?_, g, h, hgh⟩
  -- The finite shifted coproduct lies in the generated subcategory of its unshifted owner.
  simpa using finiteShiftCoproduct_mem_objectGeneratedProperty E ι s

/-- Helper for Lemma 13.37.4: the source-faithful induction should first factor through an object
of the generated property `⟨∐ fun j ↦ E (ι j)⟩`; the public theorem then extracts the stage
parameter `m`. -/
private theorem generatedProperty_mem_of_triangle
    {A₁ A₂ A : D} {J : Type (max u v w)} [Finite J] (ι : J → I)
    {a : A₁ ⟶ A₂} {b : A₂ ⟶ A} {δ : A ⟶ A₁⟦(1 : ℤ)⟧}
    (hT : Triangle.mk a b δ ∈ distTriang D)
    (h₁ : ⟨∐ fun j : J ↦ E (ι j)⟩ A₁)
    (h₂ : ⟨∐ fun j : J ↦ E (ι j)⟩ A₂) :
    ⟨∐ fun j : J ↦ E (ι j)⟩ A := by
  let P : ObjectProperty D := ⟨∐ fun j : J ↦ E (ι j)⟩
  -- Close the generated property under the third vertex of a distinguished triangle.
  exact P.ext_of_isTriangulatedClosed₃ (Triangle.mk a b δ) hT h₁ h₂

/-- Helper for Lemma 13.37.4: if the residual difference into `X (n + 1)` has zero connecting
composite, the induction hypothesis on `X n` upgrades it to a finite-generator factorization of
the original residual. -/
private theorem factorZeroConnectingDifferenceThroughPreviousStage
    {X : ℕ → D} {map : ∀ n : ℕ, X n ⟶ X (n + 1)} {Y : ℕ → D}
    {triangleHom : ∀ n : ℕ, Y n ⟶ X n}
    {triangleConnecting : ∀ n : ℕ, X (n + 1) ⟶ (Y n)⟦(1 : ℤ)⟧}
    (hR : IsGeneratingFamilyApproximation E X map Y triangleHom triangleConnecting)
    (n : ℕ)
    (ih :
      ∀ {C' : D}, IsCompactObject C' → ∀ f' : C' ⟶ X n,
        ∃ (A' : D) (J' : Type (max u v w)) (_ : Finite J') (ι' : J' → I),
          ⟨∐ fun j : J' ↦ E (ι' j)⟩ A' ∧
          ∃ (g' : C' ⟶ A') (h' : A' ⟶ X n), g' ≫ h' = f')
    {C : D} (hC : IsCompactObject C)
    {d : C ⟶ X (n + 1)} (hd : d ≫ triangleConnecting n = 0) :
    ∃ (A' : D) (J' : Type (max u v w)) (_ : Finite J') (ι' : J' → I),
      ⟨∐ fun j : J' ↦ E (ι' j)⟩ A' ∧
      ∃ (g' : C ⟶ A') (h' : A' ⟶ X (n + 1)), g' ≫ h' = d := by
  obtain ⟨u, hu⟩ := lift_zero_connecting E hR n hd
  obtain ⟨A', J', hJ', ι', hA', g', h', hg'h'⟩ := ih hC u
  refine ⟨A', J', hJ', ι', hA', g', h' ≫ map n, ?_⟩
  -- First factor through `X n`, then postcompose with the transition map to recover `d`.
  calc
    g' ≫ (h' ≫ map n) = (g' ≫ h') ≫ map n := by simp [Category.assoc]
    _ = u ≫ map n := by rw [hg'h']
    _ = d := hu

/-- Helper for Lemma 13.37.4: the only shift transport in the successor step is the `preimage`
rewrite that turns a map `A⟦1⟧ ⟶ Y⟦1⟧` into the `mor₃` square needed by TR3. -/
private theorem shiftPreimageTriangleSquare
    {A C X Y : D} {g : C ⟶ A⟦(1 : ℤ)⟧} {h : A⟦(1 : ℤ)⟧ ⟶ Y⟦(1 : ℤ)⟧}
    {f : C ⟶ X} {δ : X ⟶ Y⟦(1 : ℤ)⟧} (hg : g ≫ h = f ≫ δ) :
    let a : A ⟶ Y := (shiftFunctor D (1 : ℤ)).preimage h
    g ≫ a⟦(1 : ℤ)⟧' = f ≫ δ := by
  -- Rewrite the shifted target once through `Functor.map_preimage`, then keep the rest of the
  -- successor proof in triangle-field form.
  dsimp
  simpa [Functor.map_preimage] using hg

/-- Helper for Lemma 13.37.4: two finite generator-coproduct owners can be transported to the
common owner indexed by the sum type. -/
private theorem generatedProperty_mem_commonOwner
    {A₁ A₂ : D} {J₁ J₂ : Type (max u v w)} [Finite J₁] [Finite J₂]
    (ι₁ : J₁ → I) (ι₂ : J₂ → I)
    (h₁ : ⟨∐ fun j : J₁ ↦ E (ι₁ j)⟩ A₁)
    (h₂ : ⟨∐ fun j : J₂ ↦ E (ι₂ j)⟩ A₂) :
    let F : D := ∐ fun j : Sum J₁ J₂ ↦ E (Sum.elim ι₁ ι₂ j)
    ⟨F⟩ A₁ ∧ ⟨F⟩ A₂ := by
  let F₁ : D := ∐ fun j : J₁ ↦ E (ι₁ j)
  let F₂ : D := ∐ fun j : J₂ ↦ E (ι₂ j)
  let F : D := ∐ fun j : Sum J₁ J₂ ↦ E (Sum.elim ι₁ ι₂ j)
  let P : ObjectProperty D := ⟨F⟩
  have hF₁ : P F₁ := by
    let _ : P.IsClosedUnderFiniteCoproducts := inferInstance
    have hsummand : ∀ j : J₁, P (E (ι₁ j)) := by
      intro j
      -- View each left summand inside the combined finite coproduct owner.
      simpa [F, P] using
        finiteGeneratorCoproductSummand_mem_objectGeneratedProperty
          E (fun j : Sum J₁ J₂ ↦ Sum.elim ι₁ ι₂ j) (Sum.inl j)
    simpa [F₁, P] using P.prop_coproduct hsummand
  have hF₂ : P F₂ := by
    let _ : P.IsClosedUnderFiniteCoproducts := inferInstance
    have hsummand : ∀ j : J₂, P (E (ι₂ j)) := by
      intro j
      -- The same owner also contains every right summand.
      simpa [F, P] using
        finiteGeneratorCoproductSummand_mem_objectGeneratedProperty
          E (fun j : Sum J₁ J₂ ↦ Sum.elim ι₁ ι₂ j) (Sum.inr j)
    simpa [F₂, P] using P.prop_coproduct hsummand
  have hle₁ : ⟨F₁⟩ ≤ P := objectGeneratedProperty_le_of_mem F₁ P hF₁
  have hle₂ : ⟨F₂⟩ ≤ P := objectGeneratedProperty_le_of_mem F₂ P hF₂
  -- Transport each factor object into the common owner before applying triangle closure.
  exact ⟨hle₁ _ h₁, hle₂ _ h₂⟩

/-- Helper for Lemma 13.37.4: once the constructed factor and the original map have the same
connecting composite, the residual difference lands in the kernel of the connecting morphism. -/
private theorem residualDifference_triangleConnecting_zero
    {A₁ A C X Y : D} {a : A₁ ⟶ Y} {g₁ : C ⟶ A₁⟦(1 : ℤ)⟧}
    {δA : A ⟶ A₁⟦(1 : ℤ)⟧} {g : C ⟶ A} {k : A ⟶ X} {f : C ⟶ X}
    {δ : X ⟶ Y⟦(1 : ℤ)⟧}
    (h₁ : g₁ ≫ a⟦(1 : ℤ)⟧' = f ≫ δ)
    (h₂ : g ≫ δA = g₁)
    (h₃ : δA ≫ a⟦(1 : ℤ)⟧' = k ≫ δ) :
    (f - (g ≫ k)) ≫ δ = 0 := by
  -- Rewrite the residual through the two `mor₃` identities, so the difference collapses to zero.
  calc
    (f - (g ≫ k)) ≫ δ = f ≫ δ - g ≫ (k ≫ δ) := by
      simp [Preadditive.sub_comp, Category.assoc]
    _ = f ≫ δ - g ≫ (δA ≫ a⟦(1 : ℤ)⟧') := by rw [h₃]
    _ = f ≫ δ - g₁ ≫ a⟦(1 : ℤ)⟧' := by rw [← h₂]; simp [Category.assoc]
    _ = 0 := by rw [h₁]; simp

/-- Helper for Lemma 13.37.4: the first successor-step package factors the connecting composite
through a finite shifted coproduct and then completes the resulting `mor₃` square by `TR3`. -/
private theorem succConnectingFactorTriangle
    {X : ℕ → D} {map : ∀ n : ℕ, X n ⟶ X (n + 1)} {Y : ℕ → D}
    {triangleHom : ∀ n : ℕ, Y n ⟶ X n}
    {triangleConnecting : ∀ n : ℕ, X (n + 1) ⟶ (Y n)⟦(1 : ℤ)⟧}
    [UnivLE.{max u v w, max u v}]
    (hcompact : ∀ i : I, IsCompactObject (E i))
    (hR : IsGeneratingFamilyApproximation E X map Y triangleHom triangleConnecting)
    (n : ℕ) {C : D} (hC : IsCompactObject C) (f : C ⟶ X (n + 1)) :
    ∃ (A₁ : D) (J₁ : Type (max u v w)) (_ : Finite J₁) (ι₁ : J₁ → I),
      ⟨∐ fun j : J₁ ↦ E (ι₁ j)⟩ A₁ ∧
      ∃ (C' : D) (g₁ : C ⟶ A₁⟦(1 : ℤ)⟧) (a : A₁ ⟶ Y n)
        (topMor1 : A₁ ⟶ C') (topMor2 : C' ⟶ C) (u : C' ⟶ X n),
        Triangle.mk topMor1 topMor2 g₁ ∈ distTriang D ∧
        IsCompactObject C' ∧
        g₁ ≫ a⟦(1 : ℤ)⟧' = f ≫ triangleConnecting n ∧
        topMor1 ≫ u = a ≫ triangleHom n ∧
        topMor2 ≫ f = u ≫ map n := by
  obtain ⟨J₁, hJ₁, ι₁, s₁, g₁, h₁, hg₁h₁⟩ :=
    compactFactorThroughFiniteShiftOfDirectSumOfShifts
      E (IsGeneratingFamilyApproximation.pieces E hR n) hC
      (f ≫ triangleConnecting n)
  letI : Finite J₁ := hJ₁
  let A₁ : D := ∐ fun j : J₁ ↦ E (ι₁ j)⟦s₁ j⟧
  let a : A₁ ⟶ Y n := (shiftFunctor D (1 : ℤ)).preimage h₁
  have hA₁ : ⟨∐ fun j : J₁ ↦ E (ι₁ j)⟩ A₁ := by
    -- Forget the explicit shifts only after recording the finite shifted coproduct.
    simpa [A₁] using finiteShiftCoproduct_mem_objectGeneratedProperty E ι₁ s₁
  have hA₁compact : IsCompactObject A₁ := by
    -- The stronger finite-shift factorization keeps the left vertex compact.
    simpa [A₁] using finiteShiftCoproduct_isCompactObject E hcompact ι₁ s₁
  have hcomm₃ : g₁ ≫ a⟦(1 : ℤ)⟧' = f ≫ triangleConnecting n := by
    -- Route correction: rewrite the shifted map once via `preimage` before applying `TR3`.
    simpa [A₁, a, Functor.map_preimage] using hg₁h₁
  obtain ⟨C', topMor1, topMor2, hTtop⟩ := distinguished_cocone_triangle₂ g₁
  obtain ⟨u, hu₁, hu₂⟩ :=
    complete_distinguished_triangle_morphism₂
      (Triangle.mk topMor1 topMor2 g₁)
      (Triangle.mk (triangleHom n) (map n) (triangleConnecting n))
      hTtop
      (IsGeneratingFamilyApproximation.triangleDistinguished E hR n)
      a f hcomm₃
  have hC' : IsCompactObject C' := by
    -- The new middle object is compact because compact objects form a triangulated subcategory.
    exact
      (show IsCompactObject C' from
        show (IsCompactObject : ObjectProperty D) C' from
          ObjectProperty.ext_of_isTriangulatedClosed₂
            (IsCompactObject : ObjectProperty D)
            (Triangle.mk topMor1 topMor2 g₁) hTtop hA₁compact hC)
  exact ⟨A₁, J₁, hJ₁, ι₁, hA₁, C', g₁, a, topMor1, topMor2, u,
    hTtop, hC', hcomm₃, hu₁, hu₂⟩

/-- Helper for Lemma 13.37.4: after factoring the compact cone object through the previous stage,
merge the two finite owners and use two `TR3` completions to build the middle factor object. -/
private theorem succMiddleFactorAssembly
    {X : ℕ → D} {map : ∀ n : ℕ, X n ⟶ X (n + 1)} {Y : ℕ → D}
    {triangleHom : ∀ n : ℕ, Y n ⟶ X n}
    {triangleConnecting : ∀ n : ℕ, X (n + 1) ⟶ (Y n)⟦(1 : ℤ)⟧}
    (hR : IsGeneratingFamilyApproximation E X map Y triangleHom triangleConnecting)
    (n : ℕ)
    {A₁ C' C A₂ : D}
    {J₁ J₂ : Type (max u v w)} [Finite J₁] [Finite J₂]
    (ι₁ : J₁ → I) (ι₂ : J₂ → I)
    (hA₁ : ⟨∐ fun j : J₁ ↦ E (ι₁ j)⟩ A₁)
    (hA₂ : ⟨∐ fun j : J₂ ↦ E (ι₂ j)⟩ A₂)
    {g₁ : C ⟶ A₁⟦(1 : ℤ)⟧} {a : A₁ ⟶ Y n}
    {topMor1 : A₁ ⟶ C'} {topMor2 : C' ⟶ C} {u : C' ⟶ X n}
    (hTtop : Triangle.mk topMor1 topMor2 g₁ ∈ distTriang D)
    (hu₁ : topMor1 ≫ u = a ≫ triangleHom n)
    {g₂ : C' ⟶ A₂} {k₂ : A₂ ⟶ X n}
    (hg₂k₂ : g₂ ≫ k₂ = u) :
    ∃ (A : D) (δA : A ⟶ A₁⟦(1 : ℤ)⟧) (r : C ⟶ A) (k : A ⟶ X (n + 1)),
      ⟨∐ fun j : Sum J₁ J₂ ↦ E (Sum.elim ι₁ ι₂ j)⟩ A ∧
      r ≫ δA = g₁ ∧
      δA ≫ a⟦(1 : ℤ)⟧' = k ≫ triangleConnecting n := by
  have hCommon :
      let F : D := ∐ fun j : Sum J₁ J₂ ↦ E (Sum.elim ι₁ ι₂ j)
      ⟨F⟩ A₁ ∧ ⟨F⟩ A₂ := by
    -- Move both factor objects to the common owner indexed by `J₁ ⊕ J₂`.
    simpa using generatedProperty_mem_commonOwner E ι₁ ι₂ hA₁ hA₂
  have hA₁' :
      ⟨∐ fun j : Sum J₁ J₂ ↦ E (Sum.elim ι₁ ι₂ j)⟩ A₁ := hCommon.1
  have hA₂' :
      ⟨∐ fun j : Sum J₁ J₂ ↦ E (Sum.elim ι₁ ι₂ j)⟩ A₂ := hCommon.2
  let a₂ : A₁ ⟶ A₂ := topMor1 ≫ g₂
  obtain ⟨A, b₂, δA, hTmid⟩ := distinguished_cocone_triangle a₂
  obtain ⟨r, hr₂, hr₃⟩ :=
    complete_distinguished_triangle_morphism
      (Triangle.mk topMor1 topMor2 g₁)
      (Triangle.mk a₂ b₂ δA)
      hTtop hTmid
      (𝟙 A₁) g₂
      (by simp [a₂])
  have hcomm₁₂ : a₂ ≫ k₂ = a ≫ triangleHom n := by
    -- Substitute the induction-hypothesis factorization into the first square.
    calc
      a₂ ≫ k₂ = topMor1 ≫ (g₂ ≫ k₂) := by simp [a₂, Category.assoc]
      _ = a ≫ triangleHom n := by rw [hg₂k₂, hu₁]
  obtain ⟨k, hk₂, hk₃⟩ :=
    complete_distinguished_triangle_morphism
      (Triangle.mk a₂ b₂ δA)
      (Triangle.mk (triangleHom n) (map n) (triangleConnecting n))
      hTmid
      (IsGeneratingFamilyApproximation.triangleDistinguished E hR n)
      a k₂ hcomm₁₂
  have hA :
      ⟨∐ fun j : Sum J₁ J₂ ↦ E (Sum.elim ι₁ ι₂ j)⟩ A := by
    -- The common owner is triangulated, so the cone object stays inside it.
    exact
      generatedProperty_mem_of_triangle
        E (Sum.elim ι₁ ι₂) hTmid hA₁' hA₂'
  exact ⟨A, δA, r, k, hA, by simpa using hr₃.symm, hk₃⟩

/-- Helper for Lemma 13.37.4: the source-faithful induction should first factor through an object
of the generated property `⟨∐ fun j ↦ E (ι j)⟩`; the public theorem then extracts the stage
parameter `m`. -/
private theorem compactFactorSuccOfApproximation
    {X : ℕ → D} {map : ∀ n : ℕ, X n ⟶ X (n + 1)} {Y : ℕ → D}
    {triangleHom : ∀ n : ℕ, Y n ⟶ X n}
    {triangleConnecting : ∀ n : ℕ, X (n + 1) ⟶ (Y n)⟦(1 : ℤ)⟧}
    [UnivLE.{max u v w, max u v}]
    (hcompact : ∀ i : I, IsCompactObject (E i))
    (hR : IsGeneratingFamilyApproximation E X map Y triangleHom triangleConnecting)
    (n : ℕ)
    (ih :
      ∀ {C' : D}, IsCompactObject C' → ∀ f' : C' ⟶ X n,
        ∃ (A' : D) (J' : Type (max u v w)) (_ : Finite J') (ι' : J' → I),
          ⟨∐ fun j : J' ↦ E (ι' j)⟩ A' ∧
          ∃ (g' : C' ⟶ A') (h' : A' ⟶ X n), g' ≫ h' = f')
    {C : D} (hC : IsCompactObject C) (f : C ⟶ X (n + 1)) :
    ∃ (A : D) (J : Type (max u v w)) (_ : Finite J) (ι : J → I),
        ⟨∐ fun j : J ↦ E (ι j)⟩ A ∧
        ∃ (g : C ⟶ A) (h : A ⟶ X (n + 1)), g ≫ h = f := by
  -- Route correction: package the two `TR3` completions into separate helpers before doing the
  -- residual-difference correction, so the successor step follows the source proof directly.
  obtain ⟨A₁, J₁, hJ₁, ι₁, hA₁, C', g₁, a, topMor1, topMor2, u,
      hTtop, hC', hcomm₃, hu₁, hu₂⟩ :=
    succConnectingFactorTriangle E hcompact hR n hC f
  letI : Finite J₁ := hJ₁
  obtain ⟨A₂, J₂, hJ₂, ι₂, hA₂, g₂, k₂, hg₂k₂⟩ := ih hC' u
  letI : Finite J₂ := hJ₂
  obtain ⟨A, δA, r, k, hA, hrδ, hδk⟩ :=
    succMiddleFactorAssembly E hR n ι₁ ι₂ hA₁ hA₂ hTtop hu₁ hg₂k₂
  have hresidual :
      (f - (r ≫ k)) ≫ triangleConnecting n = 0 := by
    -- The two structural packages ensure the residual factors through the previous stage.
    exact residualDifference_triangleConnecting_zero hcomm₃ hrδ hδk
  obtain ⟨A₃, J₃, hJ₃, ι₃, hA₃, g₃, h₃, hg₃h₃⟩ :=
    factorZeroConnectingDifferenceThroughPreviousStage
      E hR n (fun hC'' f'' ↦ ih hC'' f'') hC hresidual
  letI : Finite J₃ := hJ₃
  let F : D := ∐ fun j : Sum (Sum J₁ J₂) J₃ ↦ E (Sum.elim (Sum.elim ι₁ ι₂) ι₃ j)
  let P : ObjectProperty D := ⟨F⟩
  have hCoprod : P (A ⨿ A₃) := by
    -- First put the two factor objects under a common coproduct owner.
    simpa [F, P] using
      generatedProperty_mem_sumGeneratorCoproduct
        E (Sum.elim ι₁ ι₂) ι₃ hA hA₃
  have hBiprod : P (A ⊞ A₃) := by
    -- The chosen binary biproduct is canonically isomorphic to the chosen coproduct.
    exact P.prop_of_iso (biprod.isoCoprod A A₃).symm hCoprod
  refine
    ⟨A ⊞ A₃, Sum (Sum J₁ J₂) J₃, inferInstance,
      Sum.elim (Sum.elim ι₁ ι₂) ι₃, hBiprod,
      biprod.lift r g₃, biprod.desc k h₃, ?_⟩
  -- The final factorization is the constructed factor plus the lifted residual correction.
  calc
    biprod.lift r g₃ ≫ biprod.desc k h₃ = r ≫ k + g₃ ≫ h₃ := by
      simpa using (biprod.lift_desc r g₃ k h₃)
    _ = r ≫ k + (f - (r ≫ k)) := by rw [hg₃h₃]
    _ = f := by
      abel

/-- Helper for Lemma 13.37.4: the source-faithful induction should first factor through an object
of the generated property `⟨∐ fun j ↦ E (ι j)⟩`; the public theorem then extracts the stage
parameter `m`. -/
private theorem compactFactorApproximationGeneratedLarge
    {X : ℕ → D} {map : ∀ n : ℕ, X n ⟶ X (n + 1)} {Y : ℕ → D}
    {triangleHom : ∀ n : ℕ, Y n ⟶ X n}
    {triangleConnecting : ∀ n : ℕ, X (n + 1) ⟶ (Y n)⟦(1 : ℤ)⟧}
    [UnivLE.{max u v w, max u v}]
    (hcompact : ∀ i : I, IsCompactObject (E i))
    (hR : IsGeneratingFamilyApproximation E X map Y triangleHom triangleConnecting) {C : D}
    (hC : IsCompactObject C) (n : ℕ) (f : C ⟶ X n) :
    ∃ (A : D) (J : Type (max u v w)) (_ : Finite J) (ι : J → I),
        ⟨∐ fun j : J ↦ E (ι j)⟩ A ∧
        ∃ (g : C ⟶ A) (h : A ⟶ X n), g ≫ h = f := by
  induction n generalizing C with
  | zero =>
      -- The initial stage is already a direct sum of shifts of generators.
      simpa using
        compactFactorThroughGeneratedOfDirectSumOfShifts
          E (IsGeneratingFamilyApproximation.initial E hR) hC f
  | succ n ih =>
      -- The successor step is the source-faithful triangle argument packaged above.
      exact compactFactorSuccOfApproximation E hcompact hR n (fun {C'} hC' f' ↦ ih hC' f') hC f

/-- Helper for Lemma 13.37.4: a finite owner indexed in `Type (max u v w)` can be reindexed by
`Fin (Fintype.card J)` without changing the generated property of the factor object. -/
private theorem shrinkFiniteGeneratedOwner
    {A : D} {J : Type (max u v w)} [Finite J] (ι : J → I)
    (hA : ⟨∐ fun j : J ↦ E (ι j)⟩ A) :
    ∃ (K : Type (max u v)) (_ : Finite K) (κ : K → I),
      ⟨∐ fun k : K ↦ E (κ k)⟩ A := by
  classical
  letI : Fintype J := Fintype.ofFinite J
  let F : D := ∐ fun j : J ↦ E (ι j)
  let K : Type (max u v) := ULift.{max u v, 0} (Fin (Fintype.card J))
  let e : K ≃ J := (Equiv.ulift : K ≃ Fin (Fintype.card J)).trans (Fintype.equivFin J).symm
  let F' : D := ∐ fun k : K ↦ E (ι (e k))
  let P : ObjectProperty D := ⟨F'⟩
  have hF' : P F' := by
    -- The smaller owner obviously generates itself.
    simpa [P] using objectGeneratedProperty_contains F'
  have hF : P F := by
    -- Reindex the same finite coproduct through `Fintype.equivFin` before transporting
    -- generated-property membership.
    simpa [F', P] using
      P.prop_of_iso (Sigma.reindex e (fun j : J ↦ E (ι j))) hF'
  have hle : ⟨F⟩ ≤ P := objectGeneratedProperty_le_of_mem F P hF
  refine ⟨K, inferInstance, fun k ↦ ι (e k), ?_⟩
  -- Once the owner itself is in the smaller generated property, the factor object follows by
  -- monotonicity.
  simpa [K, F', P] using hle A hA

/-- Helper for Lemma 13.37.4: after proving the large-owner induction, shrink the finite owner to
the public universe level `Type (max u v)`. -/
private theorem compact_factors_through_finite_generator_coproduct_generated
    {X : ℕ → D} {map : ∀ n : ℕ, X n ⟶ X (n + 1)} {Y : ℕ → D}
    {triangleHom : ∀ n : ℕ, Y n ⟶ X n}
    {triangleConnecting : ∀ n : ℕ, X (n + 1) ⟶ (Y n)⟦(1 : ℤ)⟧}
    [UnivLE.{max u v w, max u v}]
    (hcompact : ∀ i : I, IsCompactObject (E i))
    (hR : IsGeneratingFamilyApproximation E X map Y triangleHom triangleConnecting) {C : D}
    (hC : IsCompactObject C) (n : ℕ) (f : C ⟶ X n) :
    ∃ (A : D) (J : Type (max u v)) (_ : Finite J) (ι : J → I),
        ⟨∐ fun j : J ↦ E (ι j)⟩ A ∧
        ∃ (g : C ⟶ A) (h : A ⟶ X n), g ≫ h = f := by
  -- Route correction: the heavy induction is already packaged in
  -- `compactFactorApproximationGeneratedLarge`; only the owner universe still needs shrinking.
  rcases
      compactFactorApproximationGeneratedLarge E hcompact hR hC n f with
    ⟨A, J, hJ, ι, hA, g, h, hgh⟩
  letI : Finite J := hJ
  -- Reindex the finite owner while keeping the factor object and factorization maps unchanged.
  rcases shrinkFiniteGeneratedOwner E ι hA with ⟨K, hK, κ, hA'⟩
  exact ⟨A, K, hK, κ, hA', g, h, hgh⟩

/-- A stage-level strengthening of Lemma 13.37.4: the factor object can be placed in an explicit
generated stage attached to a finite coproduct of chosen generators. -/
private theorem compact_factors_through_finite_generator_coproduct_stage
    {X : ℕ → D} {map : ∀ n : ℕ, X n ⟶ X (n + 1)} {Y : ℕ → D}
    {triangleHom : ∀ n : ℕ, Y n ⟶ X n}
    {triangleConnecting : ∀ n : ℕ, X (n + 1) ⟶ (Y n)⟦(1 : ℤ)⟧}
    [UnivLE.{max u v w, max u v}]
    (hcompact : ∀ i : I, IsCompactObject (E i))
    (hR : IsGeneratingFamilyApproximation E X map Y triangleHom triangleConnecting) {C : D}
    (hC : IsCompactObject C) (n : ℕ) (f : C ⟶ X n) :
    ∃ (A : D) (J : Type (max u v)) (_ : Finite J) (ι : J → I) (m : ℕ+),
        (⟨∐ fun j : J ↦ E (ι j)⟩_m) A ∧
        ∃ (g : C ⟶ A) (h : A ⟶ X n), g ≫ h = f := by
  rcases
      compact_factors_through_finite_generator_coproduct_generated
        E hcompact hR hC n f with
    ⟨A, J, hJ, ι, hA, g, h, hgh⟩
  letI : Finite J := hJ
  -- Extract the positive stage witness from the generated-property membership.
  obtain ⟨m, hm⟩ := finite_generator_coproduct_stage_witness E ι hA
  exact ⟨A, J, hJ, ι, m, hm, g, h, hgh⟩

/-- Lemma 13.37.4: let
`X₀ ⟶ X₁ ⟶ X₂ ⟶ ⋯`
be a chosen generating-family resolution as in Lemma `13.37.3`, and let `C` be a compact
object.
Then any morphism from `C` to the stage `X n` factors through an object of the generated
triangulated subcategory `⟨E_{i₁} ⊕ ⋯ ⊕ E_{i_t}⟩` for some finite subfamily of the generators.
Here `X 0` corresponds to the textbook object `X₁`. -/
@[stacks 09SP]
theorem compact_factors_through_finite_generator_stage
    {X : ℕ → D} {map : ∀ n : ℕ, X n ⟶ X (n + 1)} {Y : ℕ → D}
    {triangleHom : ∀ n : ℕ, Y n ⟶ X n}
    {triangleConnecting : ∀ n : ℕ, X (n + 1) ⟶ (Y n)⟦(1 : ℤ)⟧}
    (hcompact : ∀ i : I, IsCompactObject (E i))
    (hR : IsGeneratingFamilyApproximation E X map Y triangleHom triangleConnecting) {C : D}
    (hC : IsCompactObject C) (n : ℕ) (f : C ⟶ X n) :
    ∃ (B : D) (J : Type (max u v)) (_ : Finite J) (ι : J → I),
        ⟨∐ fun j : J ↦ E (ι j)⟩ B ∧
        ∃ (g : C ⟶ B) (h : B ⟶ X n), g ≫ h = f := by
  -- Route correction: the existing finite-coproduct helper closes the theorem only after a
  -- universe-smallness bridge for `I`; without such a bridge, the required compactness instance
  -- for the large direct sum is unavailable in the current statement.
  -- TODO: repair the statement by adding the missing universe-smallness side condition (for
  -- example `[UnivLE.{w, max u v}]` or the equivalent stronger bridge), then reuse
  -- `compact_factors_through_finite_generator_coproduct_generated`.
  sorry

end
