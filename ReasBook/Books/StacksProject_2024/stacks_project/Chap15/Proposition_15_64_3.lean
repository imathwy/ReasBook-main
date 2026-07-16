import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Homology.Monoidal
import StacksProject_2024.stacks_project.Chap12.Definition_12_19_3
import StacksProject_2024.stacks_project.Chap15.Lemma_15_59_2
import StacksProject_2024.stacks_project.Chap15.Lemma_15_59_14
import StacksProject_2024.stacks_project.Chap15.Lemma_15_64_1
import StacksProject_2024.stacks_project.Chap15.Lemma_15_64_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators
open scoped DerivedTensorProduct
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open DerivedCategory
open ModuleCat.MonoidalCategory

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

/-
Domain-style sampling for Proposition `15.64.3`.
- primary domain: filtered derived tensor products of cochain complexes of `R`-modules and the
  associated cohomological spectral sequences of Chapter `12`;
- sampled owner/canonical declarations in this domain:
  `FilteredCochainComplex.exists_filteredFreeResolution`,
  `FilteredComplex.pageOneIso`,
  `FilteredComplex.exists_filteredComplexAssociatedSpectralSequence`,
  `exists_kunnethFilteredTensorAssociatedSpectralSequence`;
- best owner abstraction: the primitive source-facing data is a filtered tensor model
  `T^•` for `K^• ⊗_R^{\mathbf L} L^•` together with its canonical `E₁`-page identification, while
  the associated spectral-sequence package is derived API owned by
  `exists_kunnethFilteredTensorAssociatedSpectralSequence`;
- primitive vs. derived: the filtered tensor model and its stage-control bridge are primitive,
  whereas the associated spectral sequence, page-one comparison on `(E.page 1).X`, boundedness,
  finiteness, the chosen-`E` abutment predicate `T.abutsToCohomologyWith E`, and the comparison
  with the derived tensor-product cohomology are derived from the Chapter `12` owners;
- source/core/bridge triage:
  `source-facing`: the proposition below, asserting existence of a filtered tensor model together
    with the displayed Künneth spectral sequence;
  `core/canonical`: `FilteredComplex`, `IsAssociatedToFilteredComplex`, and
    `exists_kunnethFilteredTensorAssociatedSpectralSequence`;
  `bridge/view`: the internal theorem `exists_kunnethFilteredTensorModel`, which isolates the
    primitive tensor-model existence needed to invoke the canonical owner theorem.

The public statement therefore stays source-facing, but its spectral-sequence part should be
derived by reusing the upstream owner theorem rather than packaged again as parallel primitive
data in this file.
-/
section

variable {R : Type u} [CommRing R]
variable [LocallySmall.{0} (ModuleCat R)] [WellPowered.{0} (ModuleCat R)]
  [CategoryTheory.Limits.HasWidePullbacks (ModuleCat R)]
  [CategoryTheory.Limits.HasCoproducts (ModuleCat R)]
  [CategoryTheory.Limits.InitialMonoClass (ModuleCat R)]
  [∀ (K₁ K₂ : CochainComplex (ModuleCat R) ℤ),
    CochainComplex.HasMapBifunctor K₁ K₂ (curriedTensor (ModuleCat R))]

open FilteredCochainComplex
open FilteredComplex

local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "H" => DerivedCategory.homologyFunctor (ModuleCat R)

/-- Helper for Proposition 15.64.3: the localization functor `Q` on cochain complexes inherits
the monoidal structure used to compare `Q(P ⊗ Q)` with `Q(P) ⊗ Q(Q)`. -/
private noncomputable instance derivedCategoryQMonoidal :
    (DerivedCategory.Q : CochainComplex (ModuleCat R) ℤ ⥤ DMod).Monoidal := by
  change (((HomotopyCategory.quotient (ModuleCat R) (ComplexShape.up ℤ)) ⋙
      (DerivedCategory.Qh :
        HomotopyCategory (ModuleCat R) (ComplexShape.up ℤ) ⥤ DMod))).Monoidal
  infer_instance

/-- Helper for Proposition 15.64.3: on the right filtration index, the convolution cutoff
`p + 1 - i` lies above `p - i`, so there is a canonical stage-comparison map
`F^{p + 1 - i} Q^• ⟶ F^{p - i} Q^•`. -/
private theorem convolution_tensor_right_stage_le (p i : ℤ) :
    p - i ≤ p + 1 - i := by
  omega

/-- Helper for Proposition 15.64.3: whenever `p ≤ q`, the right filtration index `q - i`
dominates `p - i`, so there is a canonical comparison
`F^{q - i} Q^• ⟶ F^{p - i} Q^•`. -/
private theorem convolution_tensor_right_stage_le_of_le
    {p q i : ℤ} (hpq : p ≤ q) :
    p - i ≤ q - i := by
  exact sub_le_sub_right hpq i

/-- Helper for Proposition 15.64.3: the raw `p`-th convolution source is the coproduct of all
tensor products `F^i P^• ⊗ F^{p - i} Q^•` over `i ∈ ℤ`. -/
private noncomputable def convolution_tensor_stage_source
    (P Q : FilteredCochainComplex (ModuleCat R)) (p : ℤ) :
    CochainComplex (ModuleCat R) ℤ :=
  ∐ fun i : ℤ ↦ HomologicalComplex.tensorObj (P.stage i) (Q.stage (p - i))

/-- Helper for Proposition 15.64.3: the raw convolution source maps to the underlying tensor
complex by tensoring the two stage inclusions summandwise. -/
private noncomputable def convolution_tensor_stage_map
    (P Q : FilteredCochainComplex (ModuleCat R)) (p : ℤ) :
    convolution_tensor_stage_source P Q p ⟶
      HomologicalComplex.tensorObj P.underlying Q.underlying :=
  Limits.Sigma.desc fun i : ℤ ↦
    HomologicalComplex.tensorHom (P.stageInclusion i) (Q.stageInclusion (p - i))

/-- Helper for Proposition 15.64.3: increasing the convolution index by one on the `Q`-side gives
the canonical transition from the `(p + 1)`-source to the `p`-source. -/
private noncomputable def convolution_tensor_transition
    (P Q : FilteredCochainComplex (ModuleCat R)) (p : ℤ) :
    convolution_tensor_stage_source P Q (p + 1) ⟶
      convolution_tensor_stage_source P Q p :=
  Limits.Sigma.desc fun i : ℤ ↦
    HomologicalComplex.tensorHom (𝟙 (P.stage i))
        (Q.stageMapOfLE (convolution_tensor_right_stage_le p i)) ≫
      Limits.Sigma.ι (fun j : ℤ ↦ HomologicalComplex.tensorObj (P.stage j) (Q.stage (p - j))) i

/-- Helper for Proposition 15.64.3: the right-stage comparison composing with the stage inclusion
recovers the larger-stage inclusion. -/
private theorem convolution_tensor_right_stageMap_comp_stageInclusion
    (Q : FilteredCochainComplex (ModuleCat R)) (p i : ℤ) :
    Q.stageMapOfLE (convolution_tensor_right_stage_le p i) ≫ Q.stageInclusion (p - i) =
      Q.stageInclusion (p + 1 - i) := by
  -- Proof comment: this is the canonical stage-map compatibility from the owner filtration API.
  simpa using
    (FilteredComplex.stageMapOfLE_comp_stageInclusion
      (K := Q) (p := p - i) (q := p + 1 - i)
      (convolution_tensor_right_stage_le p i))

/-- Helper for Proposition 15.64.3: for any cutoff comparison `p ≤ q`, the induced right-stage
map followed by the `p`-stage inclusion agrees with the `q`-stage inclusion. -/
private theorem convolution_tensor_right_stageMapOfLE_comp_stageInclusion
    (Q : FilteredCochainComplex (ModuleCat R)) {p q i : ℤ} (hpq : p ≤ q) :
    Q.stageMapOfLE (convolution_tensor_right_stage_le_of_le (i := i) hpq) ≫
        Q.stageInclusion (p - i) =
      Q.stageInclusion (q - i) := by
  -- Proof comment: this is the standard stage-comparison compatibility, specialized to the
  -- translated right filtration indices `p - i ≤ q - i`.
  simpa using
    (FilteredComplex.stageMapOfLE_comp_stageInclusion
      (K := Q) (p := p - i) (q := q - i)
      (convolution_tensor_right_stage_le_of_le (i := i) hpq))

/-- Helper for Proposition 15.64.3: for any comparison `p ≤ q`, deleting the right-hand summands
above cutoff `q` gives a canonical map from the `q`-source to the `p`-source. -/
private noncomputable def convolution_tensor_transition_of_le
    (P Q : FilteredCochainComplex (ModuleCat R)) {p q : ℤ} (hpq : p ≤ q) :
    convolution_tensor_stage_source P Q q ⟶
      convolution_tensor_stage_source P Q p :=
  Limits.Sigma.desc fun i : ℤ ↦
    HomologicalComplex.tensorHom (𝟙 (P.stage i))
        (Q.stageMapOfLE (convolution_tensor_right_stage_le_of_le (i := i) hpq)) ≫
      Limits.Sigma.ι (fun j : ℤ ↦ HomologicalComplex.tensorObj (P.stage j) (Q.stage (p - j))) i

/-- Helper for Proposition 15.64.3: tensoring on the left by a fixed complex preserves
composition in the right variable. -/
private theorem tensorHom_comp_right
    (M : CochainComplex (ModuleCat R) ℤ)
    {K L P : CochainComplex (ModuleCat R) ℤ}
    (f : K ⟶ L) (g : L ⟶ P) :
    HomologicalComplex.tensorHom (𝟙 M) (f ≫ g) =
      HomologicalComplex.tensorHom (𝟙 M) f ≫ HomologicalComplex.tensorHom (𝟙 M) g := by
  -- Proof comment: compare the two tensor maps on every `(p,q)` summand of the total tensor
  -- complex, where functoriality in the right variable becomes ordinary composition.
  apply HomologicalComplex.hom_ext
  intro n
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q h
  have hfg :
      HomologicalComplex.ιTensorObj M K p q n h ≫
          (HomologicalComplex.tensorHom (𝟙 M) (f ≫ g)).f n =
        (M.X p ◁ ((f ≫ g).f q)) ≫ HomologicalComplex.ιTensorObj M P p q n h := by
    simpa [HomologicalComplex.ιTensorObj, HomologicalComplex.tensorHom,
      HomologicalComplex.id_f] using
      (HomologicalComplex.ι_mapBifunctorMap
        (K₁ := M) (K₂ := K) (L₁ := M) (L₂ := P)
        (f₁ := 𝟙 M) (f₂ := f ≫ g) (F := curriedTensor (ModuleCat R))
        (c := ComplexShape.up ℤ) p q n h)
  have hf :
      HomologicalComplex.ιTensorObj M K p q n h ≫
          (HomologicalComplex.tensorHom (𝟙 M) f).f n =
        (M.X p ◁ f.f q) ≫ HomologicalComplex.ιTensorObj M L p q n h := by
    simpa [HomologicalComplex.ιTensorObj, HomologicalComplex.tensorHom,
      HomologicalComplex.id_f] using
      (HomologicalComplex.ι_mapBifunctorMap
        (K₁ := M) (K₂ := K) (L₁ := M) (L₂ := L)
        (f₁ := 𝟙 M) (f₂ := f) (F := curriedTensor (ModuleCat R))
        (c := ComplexShape.up ℤ) p q n h)
  have hg :
      HomologicalComplex.ιTensorObj M L p q n h ≫
          (HomologicalComplex.tensorHom (𝟙 M) g).f n =
        (M.X p ◁ g.f q) ≫ HomologicalComplex.ιTensorObj M P p q n h := by
    simpa [HomologicalComplex.ιTensorObj, HomologicalComplex.tensorHom,
      HomologicalComplex.id_f] using
      (HomologicalComplex.ι_mapBifunctorMap
        (K₁ := M) (K₂ := L) (L₁ := M) (L₂ := P)
        (f₁ := 𝟙 M) (f₂ := g) (F := curriedTensor (ModuleCat R))
        (c := ComplexShape.up ℤ) p q n h)
  calc
    HomologicalComplex.ιTensorObj M K p q n h ≫
        (HomologicalComplex.tensorHom (𝟙 M) (f ≫ g)).f n
      = (M.X p ◁ ((f ≫ g).f q)) ≫ HomologicalComplex.ιTensorObj M P p q n h := hfg
    _ = (M.X p ◁ (f.f q ≫ g.f q)) ≫ HomologicalComplex.ιTensorObj M P p q n h := by
          simp [HomologicalComplex.comp_f]
    _ = ((M.X p ◁ f.f q) ≫ (M.X p ◁ g.f q)) ≫ HomologicalComplex.ιTensorObj M P p q n h := by
          rw [← whiskerLeft_comp]
    _ = (M.X p ◁ f.f q) ≫ ((M.X p ◁ g.f q) ≫ HomologicalComplex.ιTensorObj M P p q n h) := by
          simp [Category.assoc]
    _ = (M.X p ◁ f.f q) ≫
          (HomologicalComplex.ιTensorObj M L p q n h ≫
            (HomologicalComplex.tensorHom (𝟙 M) g).f n) := by
          rw [← hg]
    _ = (HomologicalComplex.ιTensorObj M K p q n h ≫
          (HomologicalComplex.tensorHom (𝟙 M) f).f n) ≫
            (HomologicalComplex.tensorHom (𝟙 M) g).f n := by
          rw [hf]
          simp [Category.assoc]
    _ = HomologicalComplex.ιTensorObj M K p q n h ≫
          ((HomologicalComplex.tensorHom (𝟙 M) f ≫
            HomologicalComplex.tensorHom (𝟙 M) g).f n) := by
          simp [HomologicalComplex.comp_f, Category.assoc]

/-- Helper for Proposition 15.64.3: tensoring maps in both variables is bifunctorial. -/
private theorem tensorHom_comp
    {A B C X Y Z : CochainComplex (ModuleCat R) ℤ}
    (α₁ : A ⟶ B) (α₂ : B ⟶ C) (β₁ : X ⟶ Y) (β₂ : Y ⟶ Z) :
    HomologicalComplex.tensorHom α₁ β₁ ≫ HomologicalComplex.tensorHom α₂ β₂ =
      HomologicalComplex.tensorHom (α₁ ≫ α₂) (β₁ ≫ β₂) := by
  -- Proof comment: `tensorHom` is the tensor bifunctor on cochain complexes, so composing two
  -- tensor maps is exactly the monoidal owner composition law.
  exact
    MonoidalCategory.tensorHom_comp_tensorHom α₁ β₁ α₂ β₂

/-- Helper for Proposition 15.64.3: the generalized convolution transition factors the `q`-stage
map through the `p`-stage map whenever `p ≤ q`. -/
private theorem convolution_tensor_stage_map_comp_transition_of_le
    (P Q : FilteredCochainComplex (ModuleCat R)) {p q : ℤ} (hpq : p ≤ q) :
    convolution_tensor_transition_of_le P Q hpq ≫ convolution_tensor_stage_map P Q p =
      convolution_tensor_stage_map P Q q := by
  -- Proof comment: on each coproduct summand the cutoff transition followed by the `p`-stage map
  -- is a composite of two tensor maps, so the bifunctorial tensor-composition law collapses it to
  -- a single tensor map whose right component is computed by stage-map compatibility.
  apply Limits.Sigma.hom_ext
  intro i
  have hι_transition :
      Sigma.ι (fun i : ℤ ↦ HomologicalComplex.tensorObj (P.stage i) (Q.stage (q - i))) i ≫
          convolution_tensor_transition_of_le P Q hpq =
        HomologicalComplex.tensorHom (𝟙 (P.stage i))
            (Q.stageMapOfLE (convolution_tensor_right_stage_le_of_le (i := i) hpq)) ≫
          Sigma.ι (fun j : ℤ ↦ HomologicalComplex.tensorObj (P.stage j) (Q.stage (p - j))) i := by
    simpa [convolution_tensor_transition_of_le] using
      (Limits.Sigma.ι_desc
        (fun i : ℤ ↦
          HomologicalComplex.tensorHom (𝟙 (P.stage i))
              (Q.stageMapOfLE (convolution_tensor_right_stage_le_of_le (i := i) hpq)) ≫
            Sigma.ι (fun j : ℤ ↦ HomologicalComplex.tensorObj (P.stage j) (Q.stage (p - j))) i)
        i)
  have hι_stage_p :
      Sigma.ι (fun j : ℤ ↦ HomologicalComplex.tensorObj (P.stage j) (Q.stage (p - j))) i ≫
          convolution_tensor_stage_map P Q p =
        HomologicalComplex.tensorHom (P.stageInclusion i) (Q.stageInclusion (p - i)) := by
    simpa [convolution_tensor_stage_map] using
      (Limits.Sigma.ι_desc
        (fun i : ℤ ↦ HomologicalComplex.tensorHom (P.stageInclusion i) (Q.stageInclusion (p - i)))
        i)
  have hι_stage_q :
      Sigma.ι (fun j : ℤ ↦ HomologicalComplex.tensorObj (P.stage j) (Q.stage (q - j))) i ≫
          convolution_tensor_stage_map P Q q =
        HomologicalComplex.tensorHom (P.stageInclusion i) (Q.stageInclusion (q - i)) := by
    simpa [convolution_tensor_stage_map] using
      (Limits.Sigma.ι_desc
        (fun i : ℤ ↦ HomologicalComplex.tensorHom (P.stageInclusion i) (Q.stageInclusion (q - i)))
        i)
  calc
    Sigma.ι (fun i : ℤ ↦ HomologicalComplex.tensorObj (P.stage i) (Q.stage (q - i))) i ≫
        convolution_tensor_transition_of_le P Q hpq ≫
          convolution_tensor_stage_map P Q p
      =
        (HomologicalComplex.tensorHom (𝟙 (P.stage i))
            (Q.stageMapOfLE (convolution_tensor_right_stage_le_of_le (i := i) hpq)) ≫
          Sigma.ι (fun j : ℤ ↦ HomologicalComplex.tensorObj (P.stage j) (Q.stage (p - j))) i) ≫
            convolution_tensor_stage_map P Q p := by
              simpa [Category.assoc] using
                congrArg (fun f ↦ f ≫ convolution_tensor_stage_map P Q p) hι_transition
    _ =
        HomologicalComplex.tensorHom (𝟙 (P.stage i))
            (Q.stageMapOfLE (convolution_tensor_right_stage_le_of_le (i := i) hpq)) ≫
          HomologicalComplex.tensorHom (P.stageInclusion i) (Q.stageInclusion (p - i)) := by
            simpa [Category.assoc] using
              congrArg
                (fun f ↦
                  HomologicalComplex.tensorHom (𝟙 (P.stage i))
                      (Q.stageMapOfLE (convolution_tensor_right_stage_le_of_le (i := i) hpq)) ≫ f)
                hι_stage_p
    _ =
        HomologicalComplex.tensorHom (P.stageInclusion i)
          (Q.stageMapOfLE (convolution_tensor_right_stage_le_of_le (i := i) hpq) ≫
            Q.stageInclusion (p - i)) := by
            rw [tensorHom_comp]
            simp
    _ = HomologicalComplex.tensorHom (P.stageInclusion i) (Q.stageInclusion (q - i)) := by
          rw [convolution_tensor_right_stageMapOfLE_comp_stageInclusion
            (Q := Q) (i := i) (hpq := hpq)]
    _ =
        Sigma.ι (fun i : ℤ ↦ HomologicalComplex.tensorObj (P.stage i) (Q.stage (q - i))) i ≫
          convolution_tensor_stage_map P Q q := by
            simpa using hι_stage_q.symm

/-- Helper for Proposition 15.64.3: the one-step convolution transition is the special case of
the generalized cutoff comparison at `p ≤ p + 1`. -/
private theorem convolution_tensor_stage_map_comp_transition
    (P Q : FilteredCochainComplex (ModuleCat R)) (p : ℤ) :
    convolution_tensor_transition P Q p ≫ convolution_tensor_stage_map P Q p =
      convolution_tensor_stage_map P Q (p + 1) := by
  -- Proof comment: reuse the generalized comparison lemma at the successor cutoff.
  simpa [convolution_tensor_transition, convolution_tensor_transition_of_le] using
    convolution_tensor_stage_map_comp_transition_of_le
      (P := P) (Q := Q) (p := p) (q := p + 1) (show p ≤ p + 1 by omega)

/-- Helper for Proposition 15.64.3: the degreewise image stages of the convolution source maps
form a decreasing filtration on the ambient tensor degree. -/
private theorem convolution_filtered_tensor_object_monotone
    (P Q : FilteredCochainComplex (ModuleCat R)) (n : ℤ) :
    Monotone fun p : ℤᵒᵈ ↦ imageSubobject ((convolution_tensor_stage_map P Q p).f n) := by
  intro p q hpq
  -- Proof comment: on the dual order, `p ≤ q` means the underlying cutoff `q` is larger, so the
  -- `q`-stage map factors through the `p`-stage map and its image is therefore smaller.
  let hpq' : OrderDual.ofDual q ≤ OrderDual.ofDual p := hpq
  let ι :
      (convolution_tensor_stage_source P Q (OrderDual.ofDual p)).X n ⟶
        (convolution_tensor_stage_source P Q (OrderDual.ofDual q)).X n :=
    (convolution_tensor_transition_of_le P Q
      (p := OrderDual.ofDual q) (q := OrderDual.ofDual p) hpq').f n
  have hcomp :
      ι ≫ (convolution_tensor_stage_map P Q q).f n =
        (convolution_tensor_stage_map P Q p).f n := by
    -- Proof comment: take the degree-`n` component of the stage-transition identity.
    simpa [ι, HomologicalComplex.comp_f] using
      congrArg (fun f ↦ f.f n)
        (convolution_tensor_stage_map_comp_transition_of_le
          (P := P) (Q := Q)
          (p := OrderDual.ofDual q) (q := OrderDual.ofDual p) hpq')
  simpa [hcomp] using imageSubobject_comp_le ι ((convolution_tensor_stage_map P Q q).f n)

/-- Helper for Proposition 15.64.3: in degree `n`, the convolution filtration on
`(P^• ⊗ Q^•)^n` is the image filtration coming from the stage maps
`σ_p : ⨿_i (F^i P^• ⊗ F^{p-i} Q^•) ⟶ P^• ⊗ Q^•`. -/
private noncomputable def convolution_filtered_tensor_object
    (P Q : FilteredCochainComplex (ModuleCat R)) (n : ℤ) :
    FilteredObject (ModuleCat R) where
  obj := (HomologicalComplex.tensorObj P.underlying Q.underlying).X n
  filtration :=
    { toFun := fun p ↦ imageSubobject ((convolution_tensor_stage_map P Q p).f n)
      monotone' := convolution_filtered_tensor_object_monotone P Q n }

/-- Helper for Proposition 15.64.3: a commuting square with right edge `τ` yields a factorization
through the pullback of `imageSubobject τ` along the bottom map. -/
private theorem factors_pullback_of_image_comm_sq
    {S T X Y : ModuleCat R} {σ : S ⟶ X} {u : S ⟶ T} {τ : T ⟶ Y} {d : X ⟶ Y}
    (hcomm : u ≫ τ = σ ≫ d) :
    ((Subobject.pullback d).obj (imageSubobject τ)).Factors σ := by
  -- Proof comment: first factor `σ` through the image of `τ`, then rewrite the resulting square
  -- as the defining pullback factorization.
  refine (pullback_factors_iff d (imageSubobject τ) σ).2 ?_
  refine ⟨u ≫ factorThruImage τ, ?_⟩
  simpa [Category.assoc] using hcomm

/-- Helper for Proposition 15.64.3: the tensor differential preserves the image filtration on the
convolution model degreewise. -/
private theorem convolution_filtered_tensor_preserves
    (P Q : FilteredCochainComplex (ModuleCat R)) (i j : ℤ) :
    ∀ p : ℤ,
      ((convolution_filtered_tensor_object P Q j).filtration p).Factors
        (((convolution_filtered_tensor_object P Q i).filtration p).arrow ≫
          (HomologicalComplex.tensorObj P.underlying Q.underlying).d i j) := by
  intro p
  by_cases hij : ComplexShape.Rel (ComplexShape.up ℤ) i j
  · have hj : j = i + 1 := by simpa [ComplexShape.up, eq_comm] using hij
    subst hj
    let PB :
        Subobject ((HomologicalComplex.tensorObj P.underlying Q.underlying).X i) :=
      (Subobject.pullback ((HomologicalComplex.tensorObj P.underlying Q.underlying).d i (i + 1))).obj
        (imageSubobject ((convolution_tensor_stage_map P Q p).f (i + 1)))
    have hPB :
        PB.Factors ((convolution_tensor_stage_map P Q p).f i) := by
      -- Proof comment: the stage map is a chain map, so its degree-`i` component lands in the
      -- pullback of the next image stage along the ambient differential.
      rw [show PB =
        (Subobject.pullback ((HomologicalComplex.tensorObj P.underlying Q.underlying).d i (i + 1))).obj
          (imageSubobject ((convolution_tensor_stage_map P Q p).f (i + 1))) by rfl]
      exact
        factors_pullback_of_image_comm_sq
          (σ := (convolution_tensor_stage_map P Q p).f i)
          (u := (convolution_tensor_stage_source P Q p).d i (i + 1))
          (τ := (convolution_tensor_stage_map P Q p).f (i + 1))
          (d := (HomologicalComplex.tensorObj P.underlying Q.underlying).d i (i + 1))
          ((convolution_tensor_stage_map P Q p).comm i (i + 1)).symm
    have hle_image :
        imageSubobject ((convolution_tensor_stage_map P Q p).f i) ≤ PB := by
      exact
        imageSubobject_le _ (Subobject.factorThru _ _ hPB)
          (Subobject.factorThru_arrow _ _ hPB)
    have hle :
        ((convolution_filtered_tensor_object P Q i).filtration p) ≤ PB := by
      -- Proof comment: the current filtration stage is the image of the degree-`i` stage map.
      simpa [convolution_filtered_tensor_object] using hle_image
    change
      (imageSubobject ((convolution_tensor_stage_map P Q p).f (i + 1))).Factors
        (((convolution_filtered_tensor_object P Q i).filtration p).arrow ≫
          (HomologicalComplex.tensorObj P.underlying Q.underlying).d i (i + 1))
    -- Proof comment: once the image stage is below the pullback stage, convert the pullback
    -- factorization back to the requested image-stage factorization.
    exact
      (pullback_factors_iff
        (f := (HomologicalComplex.tensorObj P.underlying Q.underlying).d i (i + 1))
        (y := imageSubobject ((convolution_tensor_stage_map P Q p).f (i + 1)))
        (h := ((convolution_filtered_tensor_object P Q i).filtration p).arrow)).1 <|
        by
          simpa [PB] using
            Subobject.factors_of_le
              (((convolution_filtered_tensor_object P Q i).filtration p).arrow) hle
              (Subobject.factors_self _)
  · have hd :
        (HomologicalComplex.tensorObj P.underlying Q.underlying).d i j = 0 := by
      exact (HomologicalComplex.tensorObj P.underlying Q.underlying).shape i j hij
  -- Proof comment: outside adjacent degrees the tensor differential is zero, so every stage
  -- trivially factors through the target filtration stage.
    simpa [hd] using
      (Subobject.factors_zero :
        ((convolution_filtered_tensor_object P Q j).filtration p).Factors
          (0 :
            (((convolution_filtered_tensor_object P Q i).filtration p : Subobject
                ((HomologicalComplex.tensorObj P.underlying Q.underlying).X i)) : ModuleCat R) ⟶
              (HomologicalComplex.tensorObj P.underlying Q.underlying).X j))

/-- Helper for Proposition 15.64.3: the differential on the convolution tensor model is the
ambient tensor differential viewed as a filtered morphism. -/
private noncomputable def convolution_filtered_tensor_d
    (P Q : FilteredCochainComplex (ModuleCat R)) (i j : ℤ) :
    convolution_filtered_tensor_object P Q i ⟶
      convolution_filtered_tensor_object P Q j where
  hom := (HomologicalComplex.tensorObj P.underlying Q.underlying).d i j
  preserves := convolution_filtered_tensor_preserves P Q i j

/-- Helper for Proposition 15.64.3: away from adjacent degrees, the convolution tensor
differential vanishes because the underlying tensor complex is a cochain complex. -/
private theorem convolution_filtered_tensor_d_shape
    (P Q : FilteredCochainComplex (ModuleCat R)) (i j : ℤ)
    (hij : ¬ ComplexShape.Rel (ComplexShape.up ℤ) i j) :
    convolution_filtered_tensor_d P Q i j = 0 := by
  apply FilteredObject.forget.map_injective
  simpa [convolution_filtered_tensor_d] using
    ((HomologicalComplex.tensorObj P.underlying Q.underlying).shape i j hij)

/-- Helper for Proposition 15.64.3: the square of the convolution tensor differential is zero
because the underlying tensor complex already satisfies `d ∘ d = 0`. -/
private theorem convolution_filtered_tensor_d_comp_d
    (P Q : FilteredCochainComplex (ModuleCat R)) (i j k : ℤ)
    (hij : ComplexShape.Rel (ComplexShape.up ℤ) i j)
    (hjk : ComplexShape.Rel (ComplexShape.up ℤ) j k) :
    convolution_filtered_tensor_d P Q i j ≫
        convolution_filtered_tensor_d P Q j k =
      0 := by
  -- Proof comment: forget the filtration; the underlying differential is the tensor-complex
  -- differential, whose square is already zero.
  apply FilteredObject.forget.map_injective
  simp only [convolution_filtered_tensor_d, FilteredObject.comp_hom]
  exact (HomologicalComplex.tensorObj P.underlying Q.underlying).d_comp_d' i j k hij hjk

/-- Helper for Proposition 15.64.3: the source-faithful convolution filtration on
`P^• ⊗ Q^•`, obtained by taking the image of each stage map `σ_p`. -/
private noncomputable def convolution_filtered_tensor_model
    (P Q : FilteredCochainComplex (ModuleCat R)) :
    FilteredCochainComplex (ModuleCat R) :=
  { X := convolution_filtered_tensor_object P Q
    d := convolution_filtered_tensor_d P Q
    shape := convolution_filtered_tensor_d_shape P Q
    d_comp_d' := convolution_filtered_tensor_d_comp_d P Q }

/-- Helper for Proposition 15.64.3: tensoring a quasi-isomorphism in the left variable with a
fixed K-flat right factor preserves quasi-isomorphisms on total tensor complexes. -/
private theorem quasiIso_totalizedTensor_map_left_of_quasiIso_of_isKFlat
    (L P Q : CochainComplex (ModuleCat R) ℤ)
    (hL : L.IsKFlat)
    (α : P ⟶ Q) (hα : QuasiIso α) :
    QuasiIso (HomologicalComplex.tensorHom α (𝟙 L)) := by
  -- This is exactly the fixed-right owner theorem from Lemma `15.59.2`.
  exact tensorHom_right_quasiIso_of_isKFlat L hL α hα

/-- Helper for Proposition 15.64.3: tensoring a quasi-isomorphism in the right variable with a
fixed K-flat left factor preserves quasi-isomorphisms on total tensor complexes. -/
private theorem quasiIso_totalizedTensor_map_right_of_quasiIso_of_left_isKFlat
    (K L M : CochainComplex (ModuleCat R) ℤ)
    (hK : K.IsKFlat)
    (α : L ⟶ M) (hα : QuasiIso α) :
    QuasiIso (HomologicalComplex.tensorHom (𝟙 K) α) := by
  have hSwap :
      QuasiIso (tensorHom α (𝟙 K)) := by
    -- Proof comment: move the fixed K-flat complex to the right input and reuse Lemma `15.59.2`.
    exact
      quasiIso_totalizedTensor_map_left_of_quasiIso_of_isKFlat
        (R := R) K L M hK α hα
  have hComp :
      QuasiIso (tensorHom (𝟙 K) α ≫ (β_ K M).hom) := by
    -- Proof comment: braiding naturality rewrites the right-variable tensor map as the already
    -- controlled left-variable tensor map followed by the target braiding.
    letI : QuasiIso ((β_ K L).hom) := inferInstance
    letI := hSwap
    simpa [BraidedCategory.braiding_naturality_right K α] using
      (quasiIso_comp ((β_ K L).hom) (tensorHom α (𝟙 K)))
  letI : QuasiIso ((β_ K M).hom) := inferInstance
  letI := hComp
  -- Proof comment: cancel the braiding isomorphism on the right to recover the original tensor
  -- comparison.
  exact quasiIso_of_comp_right (tensorHom (𝟙 K) α) (β_ K M).hom

/-- Helper for Proposition 15.64.3: after choosing filtered free resolutions, localizing the
ordinary tensor complex of the two underlying resolutions already gives the correct derived
tensor-product abutment object. -/
private noncomputable def filtered_tensor_resolution_representation_iso
    {K L P Q : FilteredCochainComplex (ModuleCat R)}
    (φ : P ⟶ K) (ψ : Q ⟶ L)
    (hφ : QuasiIso (underlyingMap φ))
    (hψ : QuasiIso (underlyingMap ψ)) :
    DerivedCategory.Q.obj (HomologicalComplex.tensorObj P.underlying Q.underlying) ≅
      ((DerivedCategory.Q.obj K.underlying) ⊗[R]^L
        DerivedCategory.Q.obj L.underlying) :=
  letI : IsIso (DerivedCategory.Q.map (underlyingMap φ)) := by
    -- Proof comment: localizing a quasi-isomorphism gives an isomorphism in the derived category.
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso]
    exact hφ
  letI : IsIso (DerivedCategory.Q.map (underlyingMap ψ)) := by
    -- Proof comment: the same localization principle applies to the right filtered resolution map.
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso]
    exact hψ
  -- Proof comment: compare the localized ordinary tensor complex with the monoidal tensor in
  -- `D(R)`, then transport the two factors along the chosen resolution maps, and finally rewrite
  -- the monoidal tensor as the source-facing derived tensor product.
  (Functor.Monoidal.μIso (DerivedCategory.Q : CochainComplex (ModuleCat R) ℤ ⥤ DMod)
      P.underlying Q.underlying).symm ≪≫
    ((asIso (DerivedCategory.Q.map (underlyingMap φ))) ⊗ᵢ
      (asIso (DerivedCategory.Q.map (underlyingMap ψ)))) ≪≫
      derivedCategory_tensorObj_iso_derivedTensorProduct
        (DerivedCategory.Q.obj K.underlying)
        (DerivedCategory.Q.obj L.underlying)

-- Proof sketch: choose filtered free K-flat resolutions of `K` and `L` as in Lemma `15.64.2`,
-- form the filtered total tensor complex `Tot(P^• ⊗_R Q^•)`, and identify its graded pieces with
-- the derived tensor products of the graded pieces of `K` and `L`. Eventual acyclicity and
-- eventual quasi-isomorphism for the filtrations of `K` and `L` transfer to the corresponding
-- stage hypotheses for the filtered tensor model.
private theorem exists_kunnethFilteredTensorModel
    (K L : FilteredCochainComplex (ModuleCat R)) :
    ∃ (T : FilteredCochainComplex (ModuleCat R))
      (representationIso :
        DerivedCategory.Q.obj T.underlying ≅
          ((DerivedCategory.Q.obj K.underlying) ⊗[R]^L
            DerivedCategory.Q.obj L.underlying))
      (modelPageOneIso : ∀ p q : ℤ,
        (gr^{p} T).homology (p + q) ≅
          ∐ fun i : ℤ ↦
            (H (p + q)).obj
              ((DerivedCategory.Q.obj (gr^{i} K)) ⊗[R]^L
                (DerivedCategory.Q.obj (gr^{p - i} L)))),
      (∃ pK₀ : ℤ, ∀ ⦃p : ℤ⦄ (_ : pK₀ ≤ p), (F^{p} K).Acyclic) →
        (∃ pK₁ : ℤ, ∀ ⦃p : ℤ⦄ (_ : p ≤ pK₁), QuasiIso (K.stageInclusion p)) →
          (∃ pL₀ : ℤ, ∀ ⦃p : ℤ⦄ (_ : pL₀ ≤ p), (F^{p} L).Acyclic) →
            (∃ pL₁ : ℤ, ∀ ⦃p : ℤ⦄ (_ : p ≤ pL₁), QuasiIso (L.stageInclusion p)) →
              (∃ pT₀ : ℤ, ∀ ⦃p : ℤ⦄ (_ : pT₀ ≤ p), (F^{p} T).Acyclic) ∧
                ∃ pT₁ : ℤ, ∀ ⦃p : ℤ⦄ (_ : p ≤ pT₁), QuasiIso (T.stageInclusion p) := by
  -- Route correction: the dependency file `Lemma_15_64_2` is available, so the real remaining
  -- blocker is local. The source-faithful next step is to choose filtered free resolutions
  -- `P ⟶ K` and `Q ⟶ L`, define the convolution-filtered tensor model on
  -- `HomologicalComplex.tensorObj P.underlying Q.underlying`, then prove the representation,
  -- graded-piece, and stage-control outputs needed by Lemma `15.64.1`.
  obtain ⟨P, φ, hPUnderlyingKFlat, hPStageKFlat, hPGradedKFlat, hPUnderlyingFree,
      hPStageFree, hPGradedFree, hφUnderlying, hφStage, hφGraded⟩ :=
    FilteredCochainComplex.exists_filteredFreeResolution (R := R) K
  obtain ⟨Q, ψ, hQUnderlyingKFlat, hQStageKFlat, hQGradedKFlat, hQUnderlyingFree,
      hQStageFree, hQGradedFree, hψUnderlying, hψStage, hψGraded⟩ :=
    FilteredCochainComplex.exists_filteredFreeResolution (R := R) L
  -- The underlying tensor complex already has the correct derived-category abutment.
  let representationIso₀ :
      DerivedCategory.Q.obj (HomologicalComplex.tensorObj P.underlying Q.underlying) ≅
        ((DerivedCategory.Q.obj K.underlying) ⊗[R]^L
          DerivedCategory.Q.obj L.underlying) :=
    filtered_tensor_resolution_representation_iso (R := R) φ ψ hφUnderlying hψUnderlying
  -- This is the left-variable quasi-isomorphism used again later when transporting graded pieces.
  have hTensorLeft :
      QuasiIso
        (HomologicalComplex.tensorHom (underlyingMap φ) (𝟙 Q.underlying)) := by
    -- Fix the K-flat right resolution `Q.underlying` and tensor the comparison `P ⟶ K`.
    exact
      quasiIso_totalizedTensor_map_left_of_quasiIso_of_isKFlat
        (R := R) Q.underlying P.underlying K.underlying
        hQUnderlyingKFlat (underlyingMap φ) hφUnderlying
  have hTensorRight :
      QuasiIso
        (HomologicalComplex.tensorHom (𝟙 P.underlying) (underlyingMap ψ)) := by
    -- Proof comment: the symmetric tensor product lets the fixed K-flat left resolution
    -- `P.underlying` control quasi-isomorphisms in the right variable as well.
    exact
      quasiIso_totalizedTensor_map_right_of_quasiIso_of_left_isKFlat
        (R := R) P.underlying Q.underlying L.underlying
        hPUnderlyingKFlat (underlyingMap ψ) hψUnderlying
  let T : FilteredCochainComplex (ModuleCat R) :=
    convolution_filtered_tensor_model P Q
  refine ⟨T, ?_, ?_, ?_⟩
  · -- Proof comment: by construction the underlying complex of `T` is exactly the ordinary tensor
    -- complex of the chosen filtered free resolutions.
    simpa [T, convolution_filtered_tensor_model, convolution_filtered_tensor_object] using
      representationIso₀
  · intro p q
    -- TODO: compute `gr^p(T)` from the image filtration via the source-faithful stage quotient
    -- presentation, then transport the resulting tensor-product comparison along `hφGraded`,
    -- `hψGraded`, `hTensorLeft`, and `hTensorRight`.
    sorry
  · intro hKHigh hKLow hLHigh hLLow
    -- TODO: once the stage-presentation `F^p(T) ≅ cokernel ρ_p` is in place, prove eventual
    -- high-stage acyclicity and low-stage quasi-isomorphism for `T.stageInclusion p` from the
    -- corresponding eventual bounds on `K` and `L`.
    sorry

-- Proof sketch: choose filtered free K-flat resolutions of `K` and `L` as in Lemma `15.64.2`,
-- form the filtered total tensor complex `Tot(P^• ⊗_R Q^•)`, and use Lemma `15.64.1` plus the
-- standard filtered-double-complex construction from this section. The resulting `E₁`-page is the
-- canonical composite of `FilteredComplex.pageOneIso` with the model identification, while the
-- representation isomorphism `Q(T^•) ≅ Q(K^•) ⊗_R^{\mathbf L} Q(L^•)` is the primitive source-facing
-- output. The same lemma supplies boundedness, finite induced filtrations, and convergence once
-- the eventual acyclicity and eventual quasi-isomorphism hypotheses on the filtrations are
-- imposed.
/-- Proposition 15.64.3: for filtered cochain complexes `K^\bullet` and `L^\bullet` of
`R`-modules, there exists a filtered cochain complex `T^\bullet` representing
`K^\bullet \otimes_R^{\mathbf L} L^\bullet` whose associated spectral sequence has
`E_1^{p,q} = \bigoplus_{i + j = p} H^{p+q}(\operatorname{gr}^i K^\bullet \otimes_R^{\mathbf L}
\operatorname{gr}^j L^\bullet)`. If the filtrations on `K^\bullet` and `L^\bullet` are
eventually acyclic above and eventually quasi-isomorphic below, then this spectral sequence is
bounded, the Chapter `12` finiteness predicate for the induced cohomology filtrations holds, and
the chosen associated spectral sequence abuts to `H^*(K^\bullet \otimes_R^{\mathbf L}
L^\bullet)` through the returned abutment comparison isomorphism. -/
theorem exists_kunneth_filteredTensorSpectralSequence
    (K L : FilteredCochainComplex (ModuleCat R)) :
    ∃ (T : FilteredCochainComplex (ModuleCat R))
      (_ :
        DerivedCategory.Q.obj T.underlying ≅
          ((DerivedCategory.Q.obj K.underlying) ⊗[R]^L
            DerivedCategory.Q.obj L.underlying))
      (E : CohomologicalSpectralSequence (ModuleCat R) 0)
      (associated : IsAssociatedToFilteredComplex T E)
      (_ : ∀ n : ℤ,
        T.underlying.homology n ≅
          (H n).obj
            ((DerivedCategory.Q.obj K.underlying) ⊗[R]^L
              DerivedCategory.Q.obj L.underlying))
      (_ : ∀ p q : ℤ,
        (E.page 1).X (p, q) ≅
          ∐ fun i : ℤ ↦
            (H (p + q)).obj
              ((DerivedCategory.Q.obj (gr^{i} K)) ⊗[R]^L
                (DerivedCategory.Q.obj (gr^{p - i} L)))),
      (∃ pK₀ : ℤ, ∀ ⦃p : ℤ⦄ (_ : pK₀ ≤ p), (F^{p} K).Acyclic) →
        (∃ pK₁ : ℤ, ∀ ⦃p : ℤ⦄ (_ : p ≤ pK₁), QuasiIso (K.stageInclusion p)) →
          (∃ pL₀ : ℤ, ∀ ⦃p : ℤ⦄ (_ : pL₀ ≤ p), (F^{p} L).Acyclic) →
            (∃ pL₁ : ℤ, ∀ ⦃p : ℤ⦄ (_ : p ≤ pL₁), QuasiIso (L.stageInclusion p)) →
              CohomologicalSpectralSequence.IsBounded E ∧
                T.cohomologyFiltrationIsFinite ∧
                T.abutsToCohomologyWith E := by
  -- The public proposition is only the Chapter `12` packaging of the primitive tensor model.
  rcases exists_kunnethFilteredTensorModel (R := R) K L with
    ⟨T, representationIso, modelPageOneIso, stageControl⟩
  rcases exists_kunnethFilteredTensorAssociatedSpectralSequence
      (R := R) T K L representationIso modelPageOneIso with
    ⟨E, associated, abutmentIso, pageOneIso, convergencePackage⟩
  refine ⟨T, representationIso, E, associated, abutmentIso, pageOneIso, ?_⟩
  intro hKHigh hKLow hLHigh hLLow
  -- Feed the source-facing stage bounds from the tensor model into the owner convergence package.
  rcases stageControl hKHigh hKLow hLHigh hLLow with ⟨hTHigh, hTLow⟩
  rcases convergencePackage hTHigh hTLow with ⟨hBounded, hFinite, _, hConverges⟩
  rcases hConverges with ⟨_, hAbuts, _⟩
  exact ⟨hBounded, hFinite, hAbuts⟩

end

end CategoryTheory
