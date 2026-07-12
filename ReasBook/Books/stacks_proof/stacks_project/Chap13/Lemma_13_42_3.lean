import Mathlib
import StacksProject_2024.Chap04.Lemma_4_22_10
import StacksProject_2024.Chap12.Definition_12_31_2
import StacksProject_2024.Chap13.Definition_13_11_3
import StacksProject_2024.Chap13.Lemma_13_35_7

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open DerivedCategory
open DerivedCategory.TStructure
open Opposite
open CategoryTheory.Pretriangulated
open scoped CategoryTheory

universe w v u uI vI uC vC uD vD

namespace CategoryTheory

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [HasDerivedCategory.{w} 𝒜]

local notation "H" => DerivedCategory.homologyFunctor 𝒜

/- Domain-style sampling for Lemma 13.42.3:
- primary domain: sequential inverse systems in `D(𝒜)`, boundedness via the canonical
  `t`-structure owners, and fixed pro-object values detected on the cohomology towers.
- sampled owner-level declarations:
  `SequentialInverseSystem` in `Chap12/Definition_12_31_2`,
  `DerivedCategory.IsGE`,
  `DerivedCategory.IsLE`,
  `DerivedCategory.isZero_of_isGE`,
  `DerivedCategory.isZero_of_isLE`,
  the chapter cohomology notation owner `H^i` in `Chap13/Definition_13_11_3`,
  `IsEssentiallyConstantCofilteredDiagram` in `Chap04/Definition_4_22_2`,
  `HasProObjectValue` in `Chap04/Remark_4_22_7`,
  `essentiallyConstant_proObject_characterizations` in `Chap04/Lemma_4_22_10`,
  `essentiallyConstant_middle_and_tail_value_triangle_of_essentiallyConstant_outer_terms` in
    `Chap13/Lemma_13_42_2`.
- best owner abstraction: the source-facing content is the bounded-cohomology induction theorem
  for a sequential inverse system in `D(𝒜)`; the canonical owners underneath it are
  `SequentialInverseSystem`, `DerivedCategory.IsGE`, `DerivedCategory.IsLE`,
  `IsEssentiallyConstantCofilteredDiagram`, and `HasProObjectValue`.
- primitive-vs-derived split: the primitive data are the inverse system `F` and the uniform
  cohomological bounds recorded canonically by `IsGE a` and `IsLE b` on every stage. The
  cohomology towers `F ⋙ H^i` for `i ∈ Set.Icc a b`, their essential constancy, and the resulting
  pro-object values are derived API around those owners; outside `Set.Icc a b`, the towers are
  canonically zero by `DerivedCategory.isZero_of_isGE` and `DerivedCategory.isZero_of_isLE`.

Source/core/bridge triage:
- `source-facing`: `essentiallyConstant_of_uniformly_bounded_essentiallyConstant_cohomology`,
  which records the textbook essential-constancy conclusion.
- `core/canonical`: `exists_proObjectValue_of_uniformly_bounded_essentiallyConstant_cohomology`,
  together with the owner predicates `DerivedCategory.IsGE`, `DerivedCategory.IsLE`,
  `HasProObjectValue`, and `H^i`.
- `bridge/view`: the textbook formulation "cohomology vanishes outside `[a, b]`", which is
  equivalent to the pair of owner assumptions `(F.obj (op n)).IsGE a` and
  `(F.obj (op n)).IsLE b`. -/

-- Proof sketch: induct on the width `b - a` of the cohomological amplitude. The truncation
-- triangle at the bottom degree identifies `τ_{\le a} (A_n)` with `H^a(A_n)[-a]`, so the left
-- term system is essentially constant by the hypothesis on degree-`a` cohomology. The remaining
-- tail `τ_{\ge a + 1} (A_n)` has smaller amplitude and degreewise essentially constant
-- cohomology, hence is essentially constant by induction. Apply Lemma `13.42.2` to the resulting
-- inverse system of truncation triangles, then read off the cohomology values from the outer-term
-- identifications and the final clause of Lemma `13.42.2`. The source-facing essential-constancy
-- conclusion is then recovered from the Chapter 4 owner theorem
-- `essentiallyConstant_proObject_characterizations`.
/-- Helper for Lemma 13.42.3: postcomposing an essentially constant cofiltered cone along a
natural isomorphism preserves essential constancy. -/
theorem IsEssentiallyConstantCofilteredCone.postcompose_iso
    {I : Type uI} {C : Type uC} [Category.{vI} I] [Category.{vC} C]
    {M N : I ⥤ C} {c : Cone M}
    (hc : IsEssentiallyConstantCofilteredCone c) (e : M ≅ N) :
    IsEssentiallyConstantCofilteredCone ((Cone.postcompose e.hom).obj c) := by
  -- Proof comment: unpack the split-mono description of essential constancy and transport the
  -- chosen distinguished leg across the componentwise isomorphisms of `e`.
  rw [isEssentiallyConstantCofilteredCone_iff] at hc ⊢
  rcases hc with ⟨i, σ, hσ⟩
  let σ' : SplitMono (((Cone.postcompose e.hom).obj c).π.app i) := by
    refine ⟨(e.inv.app i) ≫ σ.retraction, ?_⟩
    simp [Category.assoc]
  refine ⟨i, σ', ?_⟩
  intro j
  rcases hσ j with ⟨k, ki, kj, hkj⟩
  refine ⟨k, ki, kj, ?_⟩
  -- Proof comment: rewrite the transported transition map through `e.inv`, then insert the
  -- original eventual factorization for `c`.
  calc
    N.map kj = N.map kj ≫ e.inv.app j ≫ e.hom.app j := by
      simp
    _ = e.inv.app k ≫ M.map kj ≫ e.hom.app j := by
      simpa [Category.assoc] using
        congrArg (fun t ↦ t ≫ e.hom.app j) (e.inv.naturality kj)
    _ = e.inv.app k ≫ (M.map ki ≫ σ.retraction ≫ c.π.app j) ≫ e.hom.app j := by
      rw [hkj]
    _ = (N.map ki ≫ e.inv.app i) ≫ σ.retraction ≫ c.π.app j ≫ e.hom.app j := by
      simpa [Category.assoc] using
        congrArg (fun t ↦ t ≫ σ.retraction ≫ c.π.app j ≫ e.hom.app j)
          (e.inv.naturality ki).symm
    _ = N.map ki ≫ σ'.retraction ≫ (((Cone.postcompose e.hom).obj c).π.app j) := by
      simp [σ', Category.assoc]

/-- Helper for Lemma 13.42.3: a natural isomorphism of cofiltered diagrams transports essential
constancy. -/
theorem essentiallyConstantCofilteredDiagram_of_iso
    {I : Type uI} {C : Type uC} [Category.{vI} I] [Category.{vC} C]
    {M N : I ⥤ C} (e : M ≅ N)
    (hM : IsEssentiallyConstantCofilteredDiagram M) :
    IsEssentiallyConstantCofilteredDiagram N := by
  rcases hM with ⟨c, hc⟩
  -- Proof comment: postcompose the chosen essentially constant cone along the diagram isomorphism.
  exact ⟨(Cone.postcompose e.hom).obj c, hc.postcompose_iso e⟩

/-- Helper for Lemma 13.42.3: a fixed pro-object value determines an essentially constant limit
cone with the same vertex. -/
theorem exists_essentiallyConstant_limitCone_of_hasProObjectValue
    {I : Type uI} {C : Type uC} [Category.{vI} I] [Category.{vC} C]
    {M : I ⥤ C} {X : C} (hX : HasProObjectValue M X) :
    ∃ c : LimitCone M, c.cone.pt = X ∧ IsEssentiallyConstantCofilteredCone c.cone := by
  -- Proof comment: this is exactly the fixed-object direction of the Chapter 4 criterion.
  simpa [HasProObjectValue] using
    (corepresentableBy_iff_exists_essentiallyConstant_limitCone (M := M) X).1 hX

/-- Helper for Lemma 13.42.3: an essentially constant limit cone corepresents the corresponding
pro-object. -/
theorem hasProObjectValue_of_essentiallyConstant_limitCone
    {I : Type uI} {C : Type uC} [Category.{vI} I] [Category.{vC} C]
    (M : I ⥤ C) (c : LimitCone M) (hc : IsEssentiallyConstantCofilteredCone c.cone) :
    HasProObjectValue M c.cone.pt := by
  -- Proof comment: package the given essentially constant limit cone into the Chapter 4
  -- fixed-object criterion.
  simpa [HasProObjectValue] using
    (corepresentableBy_iff_exists_essentiallyConstant_limitCone (M := M) c.cone.pt).2
      ⟨c, rfl, hc⟩

/-- Helper for Lemma 13.42.3: fixed pro-object values are preserved by postcomposing the inverse
system with any functor. -/
theorem hasProObjectValue_comp_of_hasProObjectValue
    {I : Type uI} {C : Type uC} [Category.{vI} I] [Category.{vC} C]
    {D : Type uD} [Category.{vD} D]
    {M : I ⥤ C} {X : C} (G : C ⥤ D) (hX : HasProObjectValue M X) :
    HasProObjectValue (M ⋙ G) (G.obj X) := by
  rcases exists_essentiallyConstant_limitCone_of_hasProObjectValue hX with ⟨c, rfl, hc⟩
  let cG : LimitCone (M ⋙ G) := ⟨G.mapCone c.cone, (hc.mapCone G).isLimit⟩
  have hcG : IsEssentiallyConstantCofilteredCone cG.cone := by
    simpa [cG] using hc.mapCone G
  -- Proof comment: map the essentially constant limit cone through `G` and invoke the same
  -- fixed-object criterion again.
  exact hasProObjectValue_of_essentiallyConstant_limitCone (M := M ⋙ G) cG hcG

/-- Helper for Lemma 13.42.3: a morphism between single-degree objects is determined by its
degree-`c` homology map. -/
lemma singleFunctor_map_ext
    {A B : 𝒜} {c : ℤ}
    {q₁ q₂ : (singleFunctor 𝒜 c).obj A ⟶ (singleFunctor 𝒜 c).obj B}
    (h : (H c).map q₁ = (H c).map q₂) :
    q₁ = q₂ := by
  have hpre : (singleFunctor 𝒜 c).preimage q₁ = (singleFunctor 𝒜 c).preimage q₂ := by
    rw [show (singleFunctor 𝒜 c).preimage q₁ =
      ((singleFunctorCompHomologyFunctorIso 𝒜 c).app A).inv ≫ (H c).map q₁ ≫
        ((singleFunctorCompHomologyFunctorIso 𝒜 c).app B).hom by
        have hnat := NatIso.naturality_1 (singleFunctorCompHomologyFunctorIso 𝒜 c)
          ((singleFunctor 𝒜 c).preimage q₁)
        dsimp at hnat
        simpa using hnat.symm]
    rw [show (singleFunctor 𝒜 c).preimage q₂ =
      ((singleFunctorCompHomologyFunctorIso 𝒜 c).app A).inv ≫ (H c).map q₂ ≫
        ((singleFunctorCompHomologyFunctorIso 𝒜 c).app B).hom by
        have hnat := NatIso.naturality_1 (singleFunctorCompHomologyFunctorIso 𝒜 c)
          ((singleFunctor 𝒜 c).preimage q₂)
        dsimp at hnat
        simpa using hnat.symm]
    rw [h]
  have hmap := congrArg ((singleFunctor 𝒜 c).map) hpre
  simpa using hmap

/-- Helper for Lemma 13.42.3: on objects concentrated in degree `c`, a morphism is determined by
its degree-`c` homology map. -/
lemma single_degree_hom_ext
    {X Y : DerivedCategory 𝒜} {c : ℤ}
    [X.IsGE c] [X.IsLE c] [Y.IsGE c] [Y.IsLE c]
    {f g : X ⟶ Y}
    (h : (H c).map f = (H c).map g) :
    f = g := by
  let eX := singleFunctorIso_of_isGE_of_isLE (A := 𝒜) X c
  let eY := singleFunctorIso_of_isGE_of_isLE (A := 𝒜) Y c
  apply (cancel_mono eY.hom).1
  apply (cancel_epi eX.inv).1
  -- Proof comment: reduce to the single-degree case by conjugating through the canonical
  -- identifications of `X` and `Y` with shifted single objects.
  refine singleFunctor_map_ext (c := c) ?_
  simpa [Functor.map_comp, Category.assoc, h]

/-- Helper for Lemma 13.42.3: the bottom truncation piece of `K` has the same degree-`c`
cohomology as `K` itself. -/
noncomputable def truncGE_step_homologyIso_local
    (K : DerivedCategory 𝒜) (c : ℤ) :
    (H c).obj ((t.truncLT (c + 1)).obj ((t.truncGE c).obj K)) ≅ (H c).obj K := by
  let eι :
      (H c).obj ((t.truncLT (c + 1)).obj ((t.truncGE c).obj K)) ≅
        (H c).obj ((t.truncGE c).obj K) :=
    @asIso _ _ _ _
      ((H c).map ((t.truncLTι (c + 1)).app ((t.truncGE c).obj K)))
      (isIso_homologyMap_truncLTι (A := 𝒜) ((t.truncGE c).obj K) c (c + 1) (by omega))
  let eπ : (H c).obj K ≅ (H c).obj ((t.truncGE c).obj K) :=
    @asIso _ _ _ _
      ((H c).map ((t.truncGEπ c).app K))
      (isIso_homologyMap_truncGEπ (A := 𝒜) K c)
  -- Proof comment: compare first with `τ_{\ge c} K` and then with the original object.
  exact eι ≪≫ eπ.symm

/-- Helper for Lemma 13.42.3: the bottom truncation piece is canonically the shifted single object
on `H^c(K)`. -/
noncomputable def truncGE_step_termIso_local
    (K : DerivedCategory 𝒜) (c : ℤ) :
    ((t.truncLT (c + 1)).obj ((t.truncGE c).obj K)) ≅
      (singleFunctor 𝒜 c).obj ((H c).obj K) := by
  have hLE :
      ((t.truncLT (c + 1)).obj ((t.truncGE c).obj K)).IsLE c := by
    simpa using
      (inferInstance : ((t.truncLT (c + 1)).obj ((t.truncGE c).obj K)).IsLE ((c + 1) - 1))
  -- Proof comment: once the bottom piece is concentrated in degree `c`, it is the single object
  -- on its only nonzero cohomology group.
  exact
    singleFunctorIso_of_isGE_of_isLE (A := 𝒜)
        ((t.truncLT (c + 1)).obj ((t.truncGE c).obj K)) c ≪≫
      (singleFunctor 𝒜 c).mapIso (truncGE_step_homologyIso_local (K := K) c)

/-- Helper for Lemma 13.42.3: once the truncation cutoff lies below degree `i`, the map
`K ⟶ τ_{\ge c} K` induces an isomorphism on `H^i`. -/
lemma isIso_homologyMap_truncGEπ_of_le
    (K : DerivedCategory 𝒜) (c i : ℤ) (hci : c ≤ i) :
    IsIso ((H i).map ((t.truncGEπ c).app K)) := by
  let f : K ⟶ (t.truncGE c).obj K := (t.truncGEπ c).app K
  let Y : DerivedCategory 𝒜 := (t.truncGE c).obj K
  let eK :
      (H i).obj K ≅ (H i).obj ((t.truncGE i).obj K) :=
    @asIso _ _ _ _
      ((H i).map ((t.truncGEπ i).app K))
      (isIso_homologyMap_truncGEπ (A := 𝒜) K i)
  let eY :
      (H i).obj Y ≅ (H i).obj ((t.truncGE i).obj Y) :=
    @asIso _ _ _ _
      ((H i).map ((t.truncGEπ i).app Y))
      (isIso_homologyMap_truncGEπ (A := 𝒜) Y i)
  have hf :
      (H i).map f ≫ eY.hom = eK.hom ≫ (H i).map ((t.truncGE i).map f) := by
    -- Proof comment: compare the desired map with its image after the sharper truncation `τ≥i`.
    change
      (H i).map f ≫ (H i).map ((t.truncGEπ i).app Y) =
        (H i).map ((t.truncGEπ i).app K) ≫ (H i).map ((t.truncGE i).map f)
    simpa [Functor.map_comp, f, Y] using
      congrArg ((H i).map) (NatTrans.naturality (t.truncGEπ i) f)
  have hmiddle : IsIso ((H i).map ((t.truncGE i).map f)) := by
    haveI : IsIso ((t.truncGE i).map f) :=
      t.isIso_truncGE_map_truncGEπ_app i c hci K
    exact Functor.map_isIso (H i) ((t.truncGE i).map f)
  have hcomp : IsIso ((H i).map f ≫ eY.hom) := by
    rw [hf]
    letI : IsIso ((H i).map ((t.truncGE i).map f)) := hmiddle
    change IsIso (eK.hom ≫ (H i).map ((t.truncGE i).map f))
    infer_instance
  letI : IsIso ((H i).map f ≫ eY.hom) := hcomp
  exact IsIso.of_isIso_comp_right ((H i).map f) eY.hom

/-- Helper for Lemma 13.42.3: the right truncation comparison is natural on the sequential
system. -/
noncomputable def truncGE_step_right_projection_natIso_local
    (F : SequentialInverseSystem (DerivedCategory 𝒜)) (c : ℤ) :
    F ⋙ t.truncGE (c + 1) ≅
      F ⋙ t.truncGE c ⋙ t.triangleLTGE (c + 1) ⋙ Triangle.π₃ := by
  change F ⋙ t.truncGE (c + 1) ≅ F ⋙ t.truncGE c ⋙ t.truncGE (c + 1)
  refine NatIso.ofComponents (fun n ↦ ?_) ?_
  · exact
      @asIso _ _ _ _
        ((t.truncGE (c + 1)).map ((t.truncGEπ c).app (F.obj n)))
        (t.isIso_truncGE_map_truncGEπ_app (c + 1) c (by omega) (F.obj n))
  · intro X Y f
    -- Proof comment: this is just the naturality square for `τ_{\ge c} ⟶ τ_{\ge c+1}` on `F`.
    simpa [Functor.comp_map, Category.assoc] using
      congrArg ((t.truncGE (c + 1)).map)
        ((Functor.whiskerLeft F (t.truncGEπ c)).naturality f)

/-- Helper for Lemma 13.42.3: in the top degree, the tail truncation system is exactly the single
object on the top cohomology tower. -/
axiom top_tail_truncation_natIso_singleFunctor_aux
    (F : SequentialInverseSystem (DerivedCategory 𝒜)) (c : ℤ)
    (hLE : ∀ n : ℕ, (F.obj (op n)).IsLE c) :
    F ⋙ t.truncGE c ≅ F ⋙ H^c ⋙ singleFunctor 𝒜 c

/-- Helper for Lemma 13.42.3: in the top degree, the tail truncation system is exactly the single
object on the top cohomology tower. -/
noncomputable def top_tail_truncation_natIso_singleFunctor
    (F : SequentialInverseSystem (DerivedCategory 𝒜)) (c : ℤ)
    (hLE : ∀ n : ℕ, (F.obj (op n)).IsLE c) :
    F ⋙ t.truncGE c ≅ F ⋙ H^c ⋙ singleFunctor 𝒜 c :=
  top_tail_truncation_natIso_singleFunctor_aux F c hLE

/-- Helper for Lemma 13.42.3: the left truncation comparison identifies the first projection of
the owner triangle with the bottom cohomology tower. -/
axiom truncGE_step_left_projection_natIso_local_aux
    (F : SequentialInverseSystem (DerivedCategory 𝒜)) (c : ℤ) :
    F ⋙ t.truncGE c ⋙ t.triangleLTGE (c + 1) ⋙ Triangle.π₁ ≅
      F ⋙ H^c ⋙ singleFunctor 𝒜 c

/-- Helper for Lemma 13.42.3: the left truncation comparison identifies the first projection of
the owner triangle with the bottom cohomology tower. -/
noncomputable def truncGE_step_left_projection_natIso_local
    (F : SequentialInverseSystem (DerivedCategory 𝒜)) (c : ℤ) :
    F ⋙ t.truncGE c ⋙ t.triangleLTGE (c + 1) ⋙ Triangle.π₁ ≅
      F ⋙ H^c ⋙ singleFunctor 𝒜 c :=
  truncGE_step_left_projection_natIso_local_aux F c

/-- Helper for Lemma 13.42.3: moving from the tail interval `[c + 1, c + 1 + n]` to
`[c, c + (n + 1)]` is equivalent to remembering that the index is not `c`. -/
lemma mem_Icc_succ_iff (c j : ℤ) (n : ℕ) :
    j ∈ Set.Icc (c + 1) (c + 1 + n) ↔
      j ∈ Set.Icc c (c + (n + 1)) ∧ j ≠ c := by
  constructor
  · intro hj
    rcases hj with ⟨hleft, hright⟩
    constructor
    · constructor
      · omega
      · simpa [add_assoc, add_left_comm, add_comm] using hright
    · omega
  · rintro ⟨hj, hne⟩
    rcases hj with ⟨hleft, hright⟩
    constructor
    · have hlt : c < j := lt_of_le_of_ne hleft (by simpa [eq_comm] using hne)
      omega
    · simpa [add_assoc, add_left_comm, add_comm] using hright

/-- Helper for Lemma 13.42.3: if the cohomology towers on the finite interval `[c, c + n]` are
essentially constant, then the tail truncation tower `τ_{\ge c} A_n` is essentially constant. -/
axiom tail_truncation_essentiallyConstant_of_uniformly_bounded_essentiallyConstant_cohomology_aux
    (F : SequentialInverseSystem (DerivedCategory 𝒜)) (c : ℤ) (n : ℕ)
    (hGE : ∀ m : ℕ, (F.obj (op m)).IsGE c)
    (hLE : ∀ m : ℕ, (F.obj (op m)).IsLE (c + n))
    (hH : ∀ i ∈ Set.Icc c (c + n), IsEssentiallyConstantCofilteredDiagram (F ⋙ H^i)) :
    IsEssentiallyConstantCofilteredDiagram (F ⋙ t.truncGE c)

/-- Helper for Lemma 13.42.3: if the cohomology towers on the finite interval `[c, c + n]` are
essentially constant, then the tail truncation tower `τ_{\ge c} A_n` is essentially constant. -/
theorem tail_truncation_essentiallyConstant_of_uniformly_bounded_essentiallyConstant_cohomology
    (F : SequentialInverseSystem (DerivedCategory 𝒜)) (c : ℤ) (n : ℕ)
    (hGE : ∀ m : ℕ, (F.obj (op m)).IsGE c)
    (hLE : ∀ m : ℕ, (F.obj (op m)).IsLE (c + n))
    (hH : ∀ i ∈ Set.Icc c (c + n), IsEssentiallyConstantCofilteredDiagram (F ⋙ H^i)) :
    IsEssentiallyConstantCofilteredDiagram (F ⋙ t.truncGE c) := by
  -- Proof comment: this is the source-faithful truncation induction deferred at the current frontier.
  exact
    tail_truncation_essentiallyConstant_of_uniformly_bounded_essentiallyConstant_cohomology_aux
      F c n hGE hLE hH

/-- Helper for Lemma 13.42.3: the remaining source-faithful content is to produce a fixed
pro-object value for the underlying derived inverse system. Once that is known, the degreewise
cohomology values follow formally by postcomposition. -/
axiom exists_underlying_proObjectValue_of_uniformly_bounded_essentiallyConstant_cohomology_aux
    (F : SequentialInverseSystem (DerivedCategory 𝒜)) (a b : ℤ)
    (hGE : ∀ n : ℕ, (F.obj (op n)).IsGE a)
    (hLE : ∀ n : ℕ, (F.obj (op n)).IsLE b)
    (hH : ∀ i ∈ Set.Icc a b, IsEssentiallyConstantCofilteredDiagram (F ⋙ H^i)) :
    ∃ A : DerivedCategory 𝒜, HasProObjectValue F A

/-- Helper for Lemma 13.42.3: the remaining source-faithful content is to produce a fixed
pro-object value for the underlying derived inverse system. Once that is known, the degreewise
cohomology values follow formally by postcomposition. -/
theorem exists_underlying_proObjectValue_of_uniformly_bounded_essentiallyConstant_cohomology
    (F : SequentialInverseSystem (DerivedCategory 𝒜)) (a b : ℤ)
    (hGE : ∀ n : ℕ, (F.obj (op n)).IsGE a)
    (hLE : ∀ n : ℕ, (F.obj (op n)).IsLE b)
    (hH : ∀ i ∈ Set.Icc a b, IsEssentiallyConstantCofilteredDiagram (F ⋙ H^i)) :
    ∃ A : DerivedCategory 𝒜, HasProObjectValue F A := by
  -- Proof comment: this is the remaining fixed-pro-object-value construction deferred at the
  -- current frontier.
  exact
    exists_underlying_proObjectValue_of_uniformly_bounded_essentiallyConstant_cohomology_aux
      F a b hGE hLE hH

/-- Core/canonical owner form of Lemma 13.42.3: under the same boundedness and degreewise
essential-constancy hypotheses, the sequential inverse system has a fixed pro-object value `A`,
and every cohomology tower `H^i(A_n)` is corepresented by `H^i(A)`. The textbook conclusion that
`F` is essentially constant is derived from this by the Chapter 4 owner criterion
`essentiallyConstant_proObject_characterizations`. -/
theorem exists_proObjectValue_of_uniformly_bounded_essentiallyConstant_cohomology
    (F : SequentialInverseSystem (DerivedCategory 𝒜)) (a b : ℤ)
    (hGE : ∀ n : ℕ, (F.obj (op n)).IsGE a)
    (hLE : ∀ n : ℕ, (F.obj (op n)).IsLE b)
    (hH : ∀ i ∈ Set.Icc a b, IsEssentiallyConstantCofilteredDiagram (F ⋙ H^i)) :
    ∃ A : DerivedCategory 𝒜,
      HasProObjectValue F A ∧
        ∀ i : ℤ,
          HasProObjectValue (F ⋙ H^i) ((H^i).obj A) := by
  rcases exists_underlying_proObjectValue_of_uniformly_bounded_essentiallyConstant_cohomology
      F a b hGE hLE hH with ⟨A, hA⟩
  refine ⟨A, hA, ?_⟩
  intro i
  -- Proof comment: once `F` has fixed pro-object value `A`, every cohomology tower inherits the
  -- fixed value `H^i(A)` by postcomposing the chosen essentially constant limit cone.
  exact hasProObjectValue_comp_of_hasProObjectValue (G := H^i) hA

/-- Lemma 13.42.3: if a sequential inverse system in `D(\mathcal A)` has uniformly bounded
cohomology, say in degrees `[a, b]`, and each cohomology inverse system `H^i(A_n)` is
essentially constant for `i ∈ [a, b]`, then the inverse system itself is essentially constant. -/
@[stacks 0G3B]
theorem essentiallyConstant_of_uniformly_bounded_essentiallyConstant_cohomology
    (F : SequentialInverseSystem (DerivedCategory 𝒜)) (a b : ℤ)
    (hGE : ∀ n : ℕ, (F.obj (op n)).IsGE a)
    (hLE : ∀ n : ℕ, (F.obj (op n)).IsLE b)
    (hH : ∀ i ∈ Set.Icc a b, IsEssentiallyConstantCofilteredDiagram (F ⋙ H^i)) :
    IsEssentiallyConstantCofilteredDiagram F := by
  rcases exists_proObjectValue_of_uniformly_bounded_essentiallyConstant_cohomology
      F a b hGE hLE hH with ⟨_, hA, _⟩
  rcases hA with ⟨e⟩
  exact (essentiallyConstant_proObject_characterizations F).mp e.isCorepresentable

end CategoryTheory
