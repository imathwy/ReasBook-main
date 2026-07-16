import Mathlib
import stacks_proof.stacks_project.Chap13.Definition_13_34_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open DerivedCategory
open DerivedCategory.TStructure

noncomputable section

universe w v u

namespace CategoryTheory

section

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [HasDerivedCategory.{w} 𝒜]

local notation "H" => DerivedCategory.homologyFunctor 𝒜

/- Domain-style sampling for Remark 13.34.5:
- primary domain: the canonical truncation tower of a derived object and Milnor triangles for its
  sequential inverse limit;
- sampled owner declarations:
  `DerivedCategory.TStructure.t.truncGE`,
  `DerivedCategory.TStructure.t.truncGEπ`,
  `CategoryTheory.Triangulated.TStructure.natTransTruncGEOfLE`,
  `CategoryTheory.SequentialInverseSystem.transitionMap`,
  `CategoryTheory.HasMilnorTriangle`,
  `CategoryTheory.HasMilnorTriangle.WithMap`;
- best owner abstraction: the primitive truncation data are already owned by the canonical
  `t`-structure on `DerivedCategory 𝒜`; this file should keep only the source-facing specialization
  to the tower `n ↦ τ_{\ge -n} K` and the compatible-comparison predicate for its Milnor limit;
- primitive-vs-derived split:
  primitive data are the truncation functors/maps from the owner `t`;
  the stage/tower notation and the comparison predicate are the derived source-facing API, with
  the chosen first map in the Milnor triangle factored through `HasMilnorTriangle.WithMap`.

Source/core/bridge triage:
- `source-facing`: the tower `(\tau_{\ge -n} K)_n` and compatibility of a comparison map
  `K ⟶ R \!\varprojlim_n \tau_{\ge -n} K`;
- `core/canonical`: `t.truncGE`, `t.truncGEπ`, `t.natTransTruncGEOfLE`, and the chapter Milnor
  owner `HasMilnorTriangle`;
- `bridge/view`: the specialized stage/tower abbreviations below,
  `HasMilnorTriangle.WithMap` for the chosen product comparison map, and the canonical cone from
  `K` to that tower. -/

private abbrev truncationGEIndex (n : ℕ) : ℤ :=
  -((n : ℕ) : ℤ)

private theorem truncationGEIndex_succ_le (n : ℕ) :
    truncationGEIndex (n + 1) ≤ truncationGEIndex n :=
  neg_le_neg (show ((n : ℕ) : ℤ) ≤ (((n + 1 : ℕ)) : ℤ) from
    Int.ofNat_le.mpr (Nat.le_succ n))

private noncomputable abbrev derivedTruncationGEStage (K : DerivedCategory 𝒜) (n : ℕ) :
    DerivedCategory 𝒜 :=
  (t.truncGE (truncationGEIndex n)).obj K

/-- The transition morphism `τ_{\ge -(n + 1)} K ⟶ τ_{\ge -n} K` in the truncation tower of
`K`. -/
private noncomputable abbrev derivedTruncationGEStep (K : DerivedCategory 𝒜) (n : ℕ) :
    derivedTruncationGEStage K (n + 1) ⟶ derivedTruncationGEStage K n :=
  (t.natTransTruncGEOfLE (truncationGEIndex (n + 1)) (truncationGEIndex n)
    (truncationGEIndex_succ_le n)).app K

/-- The inverse system `n ↦ τ_{\ge -n} K` in `D(\mathcal A)`. -/
noncomputable abbrev derivedTruncationGETower (K : DerivedCategory 𝒜) :
    SequentialInverseSystem (DerivedCategory 𝒜) :=
  Functor.ofOpSequence (derivedTruncationGEStep K)

/-- A chosen product object for the truncation tower of `K`. -/
private noncomputable abbrev truncationTowerProduct
    (K : DerivedCategory 𝒜)
    [HasProduct (inverseSystemFamily (derivedTruncationGETower K))] :
    DerivedCategory 𝒜 :=
  ∏ᶜ inverseSystemFamily (derivedTruncationGETower K)

/-- The canonical truncation morphism `K ⟶ τ_{\ge -n} K` in the derived-category `t`-structure. -/
noncomputable abbrev derivedTruncationGEToStage (K : DerivedCategory 𝒜) (n : ℕ) :
    K ⟶ (derivedTruncationGETower K).obj (Opposite.op n) :=
  (t.truncGEπ (truncationGEIndex n)).app K

/-- The canonical truncation maps `K ⟶ τ_{\ge -n} K` form a cone over the truncation tower, with
respect to the canonical transition morphisms of `derivedTruncationGETower K`. -/
theorem derivedTruncationGEToStage_comp_step (K : DerivedCategory 𝒜) (n : ℕ) :
    derivedTruncationGEToStage K (n + 1) ≫
        (derivedTruncationGETower K).transitionMap (Nat.le_succ n) =
      derivedTruncationGEToStage K n := by
  simpa [derivedTruncationGETower, SequentialInverseSystem.transitionMap,
    derivedTruncationGEToStage, derivedTruncationGEStep, truncationGEIndex] using
    t.π_natTransTruncGEOfLE_app (truncationGEIndex (n + 1)) (truncationGEIndex n)
      (truncationGEIndex_succ_le n)
      K

attribute [reassoc, simp] derivedTruncationGEToStage_comp_step

/-- A morphism `c : K ⟶ L` is a compatible comparison from `K` to a chosen derived limit of its
truncation tower if `L` fits into the Milnor triangle of Definition 13.34.1 and the composites
with the stage projections recover the canonical truncation maps
`K ⟶ τ_{\ge -n} K`. -/
def IsTruncationDerivedLimitComparison
    (K L : DerivedCategory 𝒜) (c : K ⟶ L) : Prop :=
  ∃ _ : HasProduct (inverseSystemFamily (derivedTruncationGETower K)),
    ∃ ι : L ⟶ ∏ᶜ inverseSystemFamily (derivedTruncationGETower K),
      HasMilnorTriangle.WithMap (derivedTruncationGETower K) ι ∧
      ∀ n : ℕ, c ≫ ι ≫ Pi.π (inverseSystemFamily (derivedTruncationGETower K)) n =
        derivedTruncationGEToStage K n

/-- A compatible truncation-limit comparison presents its target as a derived limit of the
truncation tower. -/
theorem IsTruncationDerivedLimitComparison.isDerivedLimit
    {K L : DerivedCategory 𝒜} {c : K ⟶ L}
    (hc : IsTruncationDerivedLimitComparison K L c) :
    IsDerivedLimit (derivedTruncationGETower K) L := by
  rcases hc with ⟨hP, _, hι, _⟩
  let _ : HasProduct (inverseSystemFamily (derivedTruncationGETower K)) := hP
  exact ⟨hP, hι.hasMilnorTriangle (derivedTruncationGETower K)⟩

/-- Helper for Remark 13.34.5: an explicit isomorphism built from an `IsIso` witness. -/
private noncomputable def isoOfIsIso
    {C : Type*} [Category C] {X Y : C} {f : X ⟶ Y} (hf : IsIso f) :
    X ≅ Y := by
  let invf := hf.out.choose
  have h₁ : f ≫ invf = 𝟙 X := hf.out.choose_spec.1
  have h₂ : invf ≫ f = 𝟙 Y := hf.out.choose_spec.2
  exact ⟨f, invf, h₁, h₂⟩

/-- Helper for Remark 13.34.5: any two chosen products of the truncation tower are canonically
isomorphic. -/
private noncomputable def truncationTowerProductIso
    (K : DerivedCategory 𝒜)
    [hP : HasProduct (inverseSystemFamily (derivedTruncationGETower K))]
    [hQ : HasProduct (inverseSystemFamily (derivedTruncationGETower K))] :
    @truncationTowerProduct _ _ _ _ K hP ≅
      @truncationTowerProduct _ _ _ _ K hQ := by
  letI := hP
  let c' :
      Fan (inverseSystemFamily (derivedTruncationGETower K)) :=
    Fan.mk
      (by
        letI := hQ
        exact ∏ᶜ inverseSystemFamily (derivedTruncationGETower K))
      (fun n ↦ by
        letI := hQ
        exact Pi.π (inverseSystemFamily (derivedTruncationGETower K)) n)
  let hc' : IsLimit c' := by
    letI := hQ
    simpa [c'] using
      (productIsProduct (inverseSystemFamily (derivedTruncationGETower K)))
  exact hc'.conePointUniqueUpToIso
    (productIsProduct (inverseSystemFamily (derivedTruncationGETower K)))

/-- Helper for Remark 13.34.5: the canonical product isomorphism preserves each stage
projection. -/
private theorem truncationTowerProductIso_hom_comp_π
    (K : DerivedCategory 𝒜)
    [hP : HasProduct (inverseSystemFamily (derivedTruncationGETower K))]
    [hQ : HasProduct (inverseSystemFamily (derivedTruncationGETower K))]
    (n : ℕ) :
    (truncationTowerProductIso (K := K)).hom ≫
        (by
          letI := hQ
          exact Pi.π (inverseSystemFamily (derivedTruncationGETower K)) n) =
      (by
        letI := hP
        exact Pi.π (inverseSystemFamily (derivedTruncationGETower K)) n) := by
  letI := hP
  let c' :
      Fan (inverseSystemFamily (derivedTruncationGETower K)) :=
    Fan.mk
      (by
        letI := hQ
        exact ∏ᶜ inverseSystemFamily (derivedTruncationGETower K))
      (fun i ↦ by
        letI := hQ
        exact Pi.π (inverseSystemFamily (derivedTruncationGETower K)) i)
  let hc' : IsLimit c' := by
    letI := hQ
    simpa [c'] using
      (productIsProduct (inverseSystemFamily (derivedTruncationGETower K)))
  simpa [truncationTowerProductIso, c'] using
    hc'.conePointUniqueUpToIso_hom_comp
      (productIsProduct (inverseSystemFamily (derivedTruncationGETower K)))
      ⟨n⟩

attribute [reassoc] truncationTowerProductIso_hom_comp_π

/-- Helper for Remark 13.34.5: the canonical product isomorphism intertwines the Milnor
difference map. -/
private theorem truncationTowerProductIso_hom_comm_difference
    (K : DerivedCategory 𝒜)
    [hP : HasProduct (inverseSystemFamily (derivedTruncationGETower K))]
    [hQ : HasProduct (inverseSystemFamily (derivedTruncationGETower K))] :
    (truncationTowerProductIso (K := K)).hom ≫
        (by
          letI := hQ
          exact derivedLimitDifferenceMap (derivedTruncationGETower K)) =
      (by
        letI := hP
        exact derivedLimitDifferenceMap (derivedTruncationGETower K)) ≫
        (truncationTowerProductIso (K := K)).hom := by
  letI := hQ
  apply Pi.hom_ext
  intro n
  -- Compare both sides after projection to the `n`th stage.
  have hleft :
      (truncationTowerProductIso (K := K)).hom ≫
          derivedLimitDifferenceMap (derivedTruncationGETower K) ≫
          Pi.π (inverseSystemFamily (derivedTruncationGETower K)) n =
        Pi.π (inverseSystemFamily (derivedTruncationGETower K)) n -
          Pi.π (inverseSystemFamily (derivedTruncationGETower K)) (n + 1) ≫
            (derivedTruncationGETower K).transitionMap (Nat.le_succ n) := by
    have hπn := truncationTowerProductIso_hom_comp_π (K := K) n
    have hπsucc := truncationTowerProductIso_hom_comp_π (K := K) (n + 1)
    calc
      (truncationTowerProductIso (K := K)).hom ≫
          derivedLimitDifferenceMap (derivedTruncationGETower K) ≫
          Pi.π (inverseSystemFamily (derivedTruncationGETower K)) n =
        (truncationTowerProductIso (K := K)).hom ≫
            (Pi.π (inverseSystemFamily (derivedTruncationGETower K)) n -
              Pi.π (inverseSystemFamily (derivedTruncationGETower K)) (n + 1) ≫
                (derivedTruncationGETower K).transitionMap (Nat.le_succ n)) := by
            rw [derivedLimitDifferenceMap_comp_π]
      _ =
        (truncationTowerProductIso (K := K)).hom ≫
            Pi.π (inverseSystemFamily (derivedTruncationGETower K)) n -
          (truncationTowerProductIso (K := K)).hom ≫
            Pi.π (inverseSystemFamily (derivedTruncationGETower K)) (n + 1) ≫
              (derivedTruncationGETower K).transitionMap (Nat.le_succ n) := by
            rw [Preadditive.comp_sub]
      _ = Pi.π (inverseSystemFamily (derivedTruncationGETower K)) n -
          Pi.π (inverseSystemFamily (derivedTruncationGETower K)) (n + 1) ≫
            (derivedTruncationGETower K).transitionMap (Nat.le_succ n) := by
            rw [hπn]
            simpa [Category.assoc] using
              congrArg
                (fun g ↦
                  Pi.π (inverseSystemFamily (derivedTruncationGETower K)) n -
                    g ≫ (derivedTruncationGETower K).transitionMap (Nat.le_succ n))
                hπsucc
  have hright :
      (by
        letI := hP
        exact derivedLimitDifferenceMap (derivedTruncationGETower K)) ≫
          (truncationTowerProductIso (K := K)).hom ≫
          Pi.π (inverseSystemFamily (derivedTruncationGETower K)) n =
        Pi.π (inverseSystemFamily (derivedTruncationGETower K)) n -
          Pi.π (inverseSystemFamily (derivedTruncationGETower K)) (n + 1) ≫
            (derivedTruncationGETower K).transitionMap (Nat.le_succ n) := by
    letI := hP
    calc
      derivedLimitDifferenceMap (derivedTruncationGETower K) ≫
          (truncationTowerProductIso (K := K)).hom ≫
          Pi.π (inverseSystemFamily (derivedTruncationGETower K)) n =
        derivedLimitDifferenceMap (derivedTruncationGETower K) ≫
          Pi.π (inverseSystemFamily (derivedTruncationGETower K)) n := by
            simpa [Category.assoc] using
              congrArg
                (fun g ↦ derivedLimitDifferenceMap (derivedTruncationGETower K) ≫ g)
                (truncationTowerProductIso_hom_comp_π (K := K) n)
      _ = Pi.π (inverseSystemFamily (derivedTruncationGETower K)) n -
          Pi.π (inverseSystemFamily (derivedTruncationGETower K)) (n + 1) ≫
            (derivedTruncationGETower K).transitionMap (Nat.le_succ n) := by
            simpa using
              derivedLimitDifferenceMap_comp_π (derivedTruncationGETower K) n
  simpa [Category.assoc] using hleft.trans hright.symm

/-- Helper for Remark 13.34.5: after fixing one product object for the truncation tower, any
compatible comparison can be transported to that same product. -/
private theorem exists_fixed_product_comparison_of_comparison
    {K L : DerivedCategory 𝒜} {c : K ⟶ L}
    [hP : HasProduct (inverseSystemFamily (derivedTruncationGETower K))]
    (hc : IsTruncationDerivedLimitComparison K L c) :
    ∃ ι : L ⟶ ∏ᶜ inverseSystemFamily (derivedTruncationGETower K),
      HasMilnorTriangle.WithMap (derivedTruncationGETower K) ι ∧
        ∀ n : ℕ, c ≫ ι ≫ Pi.π (inverseSystemFamily (derivedTruncationGETower K)) n =
          derivedTruncationGEToStage K n := by
  rcases hc with ⟨hP', ι', hι', hcomp⟩
  letI := hP'
  let e := truncationTowerProductIso (K := K)
  rcases hι' with ⟨δ', hδ'⟩
  refine ⟨ι' ≫ e.hom, ?_, ?_⟩
  · -- Transport the distinguished triangle along the product isomorphism.
    refine ⟨e.inv ≫ δ', ?_⟩
    let T :
        Triangle (DerivedCategory 𝒜) :=
      Triangle.mk ι' (derivedLimitDifferenceMap (derivedTruncationGETower K)) δ'
    let T' :
        Triangle (DerivedCategory 𝒜) :=
      Triangle.mk
        (ι' ≫ e.hom)
        (by
          letI := hP
          exact derivedLimitDifferenceMap (derivedTruncationGETower K))
        (e.inv ≫ δ')
    have hIso :
        T ≅ T' := by
      refine Triangle.isoMk _ _ (Iso.refl _) e e ?_ ?_ ?_
      · simp [T, T']
      · simpa [T, T'] using
          (truncationTowerProductIso_hom_comm_difference (K := K)).symm
      · simp [T, T']
    exact isomorphic_distinguished _ hδ' _ hIso.symm
  · intro n
    -- The transported map has the same stagewise composites because the product isomorphism fixes
    -- every projection.
    calc
      c ≫ (ι' ≫ e.hom) ≫ Pi.π (inverseSystemFamily (derivedTruncationGETower K)) n =
          c ≫ ι' ≫ (e.hom ≫ Pi.π (inverseSystemFamily (derivedTruncationGETower K)) n) := by
            simp [Category.assoc]
      _ = c ≫ ι' ≫ Pi.π (inverseSystemFamily (derivedTruncationGETower K)) n := by
            rw [truncationTowerProductIso_hom_comp_π (K := K) n]
      _ = derivedTruncationGEToStage K n := hcomp n

/-- Helper for Remark 13.34.5: `H^n` of the canonical map `K ⟶ τ_{\ge n} K` is an
isomorphism. -/
private theorem homology_map_truncGEπ_isIso
    (K : DerivedCategory 𝒜) (n : ℤ) :
    IsIso ((H n).map ((t.truncGEπ n).app K)) := by
  let T : Triangle (DerivedCategory 𝒜) := (t.triangleLTGE n).obj K
  have hT : T ∈ distTriang (DerivedCategory 𝒜) := by
    simpa [T] using t.triangleLTGE_distinguished n K
  have h₁ : T.obj₁.IsLE (n - 1) := by
    dsimp [T]
    infer_instance
  -- The long exact sequence degenerates because the left term has no `n`th cohomology.
  have hmor₁_zero : (H n).map T.mor₁ = 0 := by
    letI := h₁
    exact (isZero_of_isLE T.obj₁ (n - 1) n (by omega)).eq_of_src _ _
  have hδ_zero : HomologySequence.δ T n (n + 1) rfl = 0 := by
    letI := h₁
    exact (isZero_of_isLE T.obj₁ (n - 1) (n + 1) (by omega)).eq_of_tgt _ _
  letI : Epi ((H n).map T.mor₂) :=
    (HomologySequence.epi_homologyMap_mor₂_iff T hT n (n + 1) rfl).2 hδ_zero
  letI : Mono ((H n).map T.mor₂) :=
    (HomologySequence.mono_homologyMap_mor₂_iff T hT n).2 hmor₁_zero
  simpa [T] using isIso_of_mono_of_epi ((H n).map T.mor₂)

/-- Helper for Remark 13.34.5: once `-m ≤ i`, the map `K ⟶ τ_{\ge -m} K` induces an
isomorphism on `H^i`. -/
private theorem homology_map_derivedTruncationGEToStage_isIso
    (K : DerivedCategory 𝒜) (i : ℤ) (m : ℕ)
    (hmi : -((m : ℕ) : ℤ) ≤ i) :
    IsIso ((H i).map (derivedTruncationGEToStage K m)) := by
  let f := derivedTruncationGEToStage K m
  let Y := (derivedTruncationGETower K).obj (Opposite.op m)
  let eK :
      (H i).obj K ≅ (H i).obj ((t.truncGE i).obj K) :=
    isoOfIsIso (homology_map_truncGEπ_isIso (K := K) i)
  let eY :
      (H i).obj Y ≅ (H i).obj ((t.truncGE i).obj Y) :=
    isoOfIsIso (homology_map_truncGEπ_isIso (K := Y) i)
  -- Naturality of `t.truncGEπ i` compares the desired map with its image under `t.truncGE i`.
  have hf :
      (H i).map f ≫ eY.hom =
        eK.hom ≫ (H i).map ((t.truncGE i).map f) := by
    change
      (H i).map f ≫ (H i).map ((t.truncGEπ i).app Y) =
        (H i).map ((t.truncGEπ i).app K) ≫ (H i).map ((t.truncGE i).map f)
    simpa [Functor.map_comp, derivedTruncationGEToStage, Y] using
      congrArg ((H i).map) (NatTrans.naturality (t.truncGEπ i) f)
  have hmiddle : IsIso ((H i).map ((t.truncGE i).map f)) := by
    haveI : IsIso ((t.truncGE i).map f) :=
      t.isIso_truncGE_map_truncGEπ_app i (truncationGEIndex m) hmi K
    exact Functor.map_isIso (H i) ((t.truncGE i).map f)
  -- The right-hand composite is an isomorphism, so `H^i(f)` is too.
  have hcomp : IsIso ((H i).map f ≫ eY.hom) := by
    rw [hf]
    letI : IsIso ((H i).map ((t.truncGE i).map f)) := hmiddle
    change IsIso (eK.hom ≫ (H i).map ((t.truncGE i).map f))
    infer_instance
  letI : IsIso ((H i).map f ≫ eY.hom) := hcomp
  exact IsIso.of_isIso_comp_right ((H i).map f) eY.hom

/-- Helper for Remark 13.34.5: for a compatible comparison, `H^i(c)` is an isomorphism exactly
when the projection from the chosen Milnor model to a sufficiently high truncation stage is. -/
private theorem compatible_comparison_homology_map_iff_projection_isIso
    {K L : DerivedCategory 𝒜} {c : K ⟶ L}
    [HasProduct (inverseSystemFamily (derivedTruncationGETower K))]
    {ι : L ⟶ ∏ᶜ inverseSystemFamily (derivedTruncationGETower K)}
    (hcomp : ∀ n : ℕ, c ≫ ι ≫ Pi.π (inverseSystemFamily (derivedTruncationGETower K)) n =
      derivedTruncationGEToStage K n)
    (i : ℤ) (m : ℕ) (hmi : -((m : ℕ) : ℤ) ≤ i) :
    IsIso ((H i).map c) ↔
      IsIso ((H i).map (ι ≫ Pi.π (inverseSystemFamily (derivedTruncationGETower K)) m)) := by
  have hstage : IsIso ((H i).map (derivedTruncationGEToStage K m)) :=
    homology_map_derivedTruncationGEToStage_isIso (K := K) i m hmi
  have hfactor :
      (H i).map c ≫
          (H i).map (ι ≫ Pi.π (inverseSystemFamily (derivedTruncationGETower K)) m) =
        (H i).map (derivedTruncationGEToStage K m) := by
    simpa [Functor.map_comp] using congrArg ((H i).map) (hcomp m)
  constructor
  · intro hc
    letI : IsIso ((H i).map c) := hc
    have hcompIso :
        IsIso
          ((H i).map c ≫
            (H i).map (ι ≫ Pi.π (inverseSystemFamily (derivedTruncationGETower K)) m)) := by
      rw [hfactor]
      exact hstage
    exact
      IsIso.of_isIso_comp_left
        ((H i).map c)
        ((H i).map (ι ≫ Pi.π (inverseSystemFamily (derivedTruncationGETower K)) m))
  · intro hι
    letI : IsIso ((H i).map (ι ≫ Pi.π (inverseSystemFamily (derivedTruncationGETower K)) m)) := hι
    have hcompIso :
        IsIso
          ((H i).map c ≫
            (H i).map (ι ≫ Pi.π (inverseSystemFamily (derivedTruncationGETower K)) m)) := by
      rw [hfactor]
      exact hstage
    exact
      IsIso.of_isIso_comp_right
        ((H i).map c)
        ((H i).map (ι ≫ Pi.π (inverseSystemFamily (derivedTruncationGETower K)) m))

/-- Helper for Remark 13.34.5: two Milnor presentations over the same chosen product object are
canonically isomorphic over that product. -/
private theorem milnor_presentation_iso_of_same_product
    {K L L' : DerivedCategory 𝒜}
    [HasProduct (inverseSystemFamily (derivedTruncationGETower K))]
    {ι : L ⟶ ∏ᶜ inverseSystemFamily (derivedTruncationGETower K)}
    {ι' : L' ⟶ ∏ᶜ inverseSystemFamily (derivedTruncationGETower K)}
    (hι : HasMilnorTriangle.WithMap (derivedTruncationGETower K) ι)
    (hι' : HasMilnorTriangle.WithMap (derivedTruncationGETower K) ι') :
    ∃ e : L ≅ L', e.hom ≫ ι' = ι := by
  rcases hι with ⟨δ, hδ⟩
  rcases hι' with ⟨δ', hδ'⟩
  let T :
      Triangle (DerivedCategory 𝒜) :=
    Triangle.mk ι (derivedLimitDifferenceMap (derivedTruncationGETower K)) δ
  let T' :
      Triangle (DerivedCategory 𝒜) :=
    Triangle.mk ι' (derivedLimitDifferenceMap (derivedTruncationGETower K)) δ'
  -- Complete the identity square on the two product terms to a morphism of distinguished
  -- triangles, then use two-out-of-three.
  obtain ⟨a, ha₁, ha₃⟩ :=
    complete_distinguished_triangle_morphism₁
      T T' hδ hδ' (𝟙 _) (𝟙 _)
      (by simp [T, T'])
  let φ : T ⟶ T' :=
    Triangle.homMk T T' a (𝟙 _) (𝟙 _)
      (by simpa [T, T'] using ha₁)
      (by simp [T, T'])
      (by simpa [T, T'] using ha₃)
  have ha : IsIso a := by
    haveI : IsIso φ.hom₂ := by
      simpa [φ] using (show IsIso (𝟙 (truncationTowerProduct K)) by infer_instance)
    haveI : IsIso φ.hom₃ := by
      simpa [φ] using (show IsIso (𝟙 (truncationTowerProduct K)) by infer_instance)
    have : IsIso φ.hom₁ :=
      Pretriangulated.isIso₁_of_isIso₂₃ φ hδ hδ' (by infer_instance) (by infer_instance)
    simpa using this
  exact ⟨isoOfIsIso ha, by simpa [T, T'] using ha₁.symm⟩

/-- Helper for Remark 13.34.5: a morphism in `D(\mathcal A)` is an isomorphism exactly when it
induces isomorphisms on all cohomology objects. -/
private theorem derivedCategory_isIso_iff_homology_map_isIso
    {X Y : DerivedCategory 𝒜} (f : X ⟶ Y) :
    IsIso f ↔ ∀ i : ℤ, IsIso ((H i).map f) := by
  constructor
  · intro hf
    intro i
    letI : IsIso f := hf
    exact Functor.map_isIso (H i) f
  · intro hf
    -- Lift the arrow to the homotopy category and detect quasi-isomorphisms there.
    obtain ⟨g, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage (F := Qh.mapArrow) (Arrow.mk f)
    have hq : HomotopyCategory.quasiIso 𝒜 (ComplexShape.up ℤ) g.hom := by
      rw [HomotopyCategory.mem_quasiIso_iff]
      intro i
      haveI : IsIso e.hom := e.isIso_hom
      let eleft :
          (H i).obj (Qh.obj g.left) ≅ (H i).obj X :=
        Functor.mapIso (H i) (isoOfIsIso (Functor.map_isIso Arrow.leftFunc e.hom))
      let eright :
          (H i).obj (Qh.obj g.right) ≅ (H i).obj Y :=
        Functor.mapIso (H i) (isoOfIsIso (Functor.map_isIso Arrow.rightFunc e.hom))
      let ef : (H i).obj X ≅ (H i).obj Y := isoOfIsIso (hf i)
      have hw :
          (H i).map (Arrow.Hom.left e.hom) ≫ (H i).map f =
            (H i).map (Qh.map g.hom) ≫ (H i).map (Arrow.Hom.right e.hom) := by
        simpa [Functor.map_comp] using congrArg ((H i).map) (Arrow.w e.hom)
      have hcomp :
          IsIso ((H i).map (Qh.map g.hom) ≫ (H i).map (Arrow.Hom.right e.hom)) := by
        haveI : IsIso (eleft.hom ≫ ef.hom) := by infer_instance
        rw [← hw]
        change IsIso (eleft.hom ≫ ef.hom)
        infer_instance
      have heright : eright.hom = (H i).map (Arrow.Hom.right e.hom) := by
        rfl
      haveI :
          IsIso ((H i).map (Qh.map g.hom) ≫ eright.hom) := by
        rw [heright]
        exact hcomp
      have hmap : IsIso ((H i).map (Qh.map g.hom)) := by
        exact IsIso.of_isIso_comp_right ((H i).map (Qh.map g.hom)) eright.hom
      rw [← NatIso.isIso_map_iff (homologyFunctorFactorsh 𝒜 i) g.hom]
      exact hmap
    have hQg : IsIso (Qh.map g.hom) := (DerivedCategory.isIso_Qh_map_iff g.hom).2 hq
    haveI : IsIso e.hom := e.isIso_hom
    exact (Arrow.isIso_iff_isIso_of_isIso e.hom).1 hQg

-- Proof sketch: for each degree `i` and each `m > -i`, compatibility gives a factorization
-- `H^i(K) ⟶ H^i(L) ⟶ H^i(τ_{\ge -m} K)` whose composite is the identity on `H^i(K)`. Since
-- `τ_{\ge -m} K` agrees with `K` on `i`th cohomology in this range, `H^i(c)` is an isomorphism
-- if and only if the second map is. That criterion depends only on the chosen derived-limit data,
-- so it is unchanged if one replaces `c` or the homotopy limit object by another compatible
-- choice.
/-- Remark 13.34.5: if `c : K ⟶ L` and `c' : K ⟶ L'` are compatible morphisms from `K` to chosen
derived limits of the tower `(\tau_{\ge -n} K)_n`, then `c` is an isomorphism if and only if
`c'` is. Hence the property that the canonical map
`K \to R\!\varprojlim_n \tau_{\ge -n} K` is an isomorphism is independent of the choice of the
comparison morphism and of the chosen homotopy limit. -/
@[stacks 0H72]
theorem derivedTruncationLimitComparison_isIso_iff
    {K L L' : DerivedCategory 𝒜} {c : K ⟶ L} {c' : K ⟶ L'}
    (hc : IsTruncationDerivedLimitComparison K L c)
    (hc' : IsTruncationDerivedLimitComparison K L' c') :
    IsIso c ↔ IsIso c' := by
  rcases hc with ⟨hP, ι, hι, hcomp⟩
  letI : HasProduct (inverseSystemFamily (derivedTruncationGETower K)) := hP
  obtain ⟨ι', hι', hcomp'⟩ :=
    exists_fixed_product_comparison_of_comparison (K := K) (L := L') (c := c') hc'
  obtain ⟨e, he⟩ :=
    milnor_presentation_iso_of_same_product (K := K) (L := L) (L' := L') hι hι'
  have hdeg :
      ∀ i : ℤ, IsIso ((H i).map c) ↔ IsIso ((H i).map c') := by
    intro i
    let m : ℕ := Int.natAbs i
    have hmi : -((m : ℕ) : ℤ) ≤ i := by
      cases i <;> omega
    have hciff :=
      compatible_comparison_homology_map_iff_projection_isIso
        (K := K) (L := L) (c := c) (ι := ι) hcomp i m hmi
    have hciff' :=
      compatible_comparison_homology_map_iff_projection_isIso
        (K := K) (L := L') (c := c') (ι := ι') hcomp' i m hmi
    have heproj :
        IsIso ((H i).map (ι ≫ Pi.π (inverseSystemFamily (derivedTruncationGETower K)) m)) ↔
          IsIso ((H i).map (ι' ≫ Pi.π (inverseSystemFamily (derivedTruncationGETower K)) m)) := by
      have hEq :
          (H i).map e.hom ≫
              (H i).map (ι' ≫ Pi.π (inverseSystemFamily (derivedTruncationGETower K)) m) =
            (H i).map (ι ≫ Pi.π (inverseSystemFamily (derivedTruncationGETower K)) m) := by
        have hπ :
            e.hom ≫ (ι' ≫ Pi.π (inverseSystemFamily (derivedTruncationGETower K)) m) =
              ι ≫ Pi.π (inverseSystemFamily (derivedTruncationGETower K)) m := by
          simpa [Category.assoc] using
            congrArg
              (fun f ↦ f ≫ Pi.π (inverseSystemFamily (derivedTruncationGETower K)) m)
              he
        simpa [Functor.map_comp, Category.assoc] using congrArg ((H i).map) hπ
      constructor
      · intro hproj
        haveI : IsIso ((H i).map e.hom) := Functor.map_isIso (H i) e.hom
        have hcompIso :
            IsIso
              ((H i).map e.hom ≫
                (H i).map (ι' ≫ Pi.π (inverseSystemFamily (derivedTruncationGETower K)) m)) := by
          rw [hEq]
          exact hproj
        exact
          IsIso.of_isIso_comp_left
            ((H i).map e.hom)
            ((H i).map (ι' ≫ Pi.π (inverseSystemFamily (derivedTruncationGETower K)) m))
      · intro hproj'
        haveI : IsIso ((H i).map e.hom) := Functor.map_isIso (H i) e.hom
        haveI :
            IsIso ((H i).map (ι' ≫ Pi.π (inverseSystemFamily (derivedTruncationGETower K)) m)) :=
          hproj'
        have hcompIso :
            IsIso
              ((H i).map e.hom ≫
                (H i).map (ι' ≫ Pi.π (inverseSystemFamily (derivedTruncationGETower K)) m)) := by
          infer_instance
        rw [hEq] at hcompIso
        exact hcompIso
    exact hciff.trans (heproj.trans hciff'.symm)
  -- Conclude by conservativity of all cohomology functors on the derived category.
  rw [derivedCategory_isIso_iff_homology_map_isIso c,
    derivedCategory_isIso_iff_homology_map_isIso c']
  constructor
  · intro hcIso
    intro i
    exact (hdeg i).1 (hcIso i)
  · intro hcIso
    intro i
    exact (hdeg i).2 (hcIso i)

end

end CategoryTheory
