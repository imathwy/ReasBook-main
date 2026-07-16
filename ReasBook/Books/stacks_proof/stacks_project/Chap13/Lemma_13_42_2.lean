import Mathlib
import stacks_proof.stacks_project.Chap12.Definition_12_31_2
import stacks_proof.stacks_project.Chap04.Lemma_4_22_10
import stacks_proof.stacks_project.Chap04.Lemma_4_22_13
import stacks_proof.stacks_project.Chap13.Lemma_13_42_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Limits.CostructuredArrow
open CategoryTheory.Pretriangulated
open Opposite

universe uI vI uC vC uD vD

namespace CategoryTheory

/-
Domain-style sampling for Lemma 13.42.2:
- primary domain: essentially constant cofiltered diagrams and fixed pro-object values in a
  pretriangulated/triangulated setting.
- inspected owner-level declarations:
  `SequentialInverseSystem` in `Chap12/Definition_12_31_2`,
  `IsEssentiallyConstantCofilteredDiagram` in `Chap04/Definition_4_22_2`,
  `HasProObjectValue` in `Chap04/Remark_4_22_7`,
  `hasProObjectValue_iff_exists_stageMap_homColimitComparison` in
    `Chap04/Lemma_4_22_10`,
  `Triangle.π₁`, `Triangle.π₂`, `Triangle.π₃` in mathlib.
- best owner abstraction: the sequential diagram owner `SequentialInverseSystem`, the
  essential-constancy owner `IsEssentiallyConstantCofilteredDiagram`, the fixed pro-object-value
  owner `HasProObjectValue M X`, and the stage-map comparison owner `HasHomColimitComparison`.
- primitive-vs-derived split: the primitive data are the inverse system `T`, the positive stage
  `n + 1`, the fixed distinguished triangle `T'`, and the morphism from that stage to `T'`;
  the owner-level conclusions `HasProObjectValue` and
  `IsEssentiallyConstantCofilteredDiagram (T ⋙ Triangle.π₂)` are derived from the corresponding
  Hom-colimit comparison data via Lemma `4.22.10`.

Source/core/bridge triage:
- `source-facing`: after some positive stage, the system admits a fixed distinguished triangle
  together with a morphism of distinguished triangles from that stage whose three components
  satisfy the Hom-colimit comparison criterion.
- `core/canonical`: `HasProObjectValue`, `IsEssentiallyConstantCofilteredDiagram`, `Triangle D`,
  and `HasHomColimitComparison`.
- `bridge/view`: the companion owner-level consequences below, obtained from the source-facing
  stage-map theorem via
  `hasProObjectValue_iff_exists_stageMap_homColimitComparison`. -/

section

variable {D : Type uD} [Category.{vD} D] [HasZeroObject D] [Preadditive D] [HasShift D ℤ]
  [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D]

/-- Helper for Lemma 13.42.2: postcomposing an essentially constant cofiltered cone along a
natural isomorphism preserves essential constancy. -/
private theorem cofilteredCone_postcompose_iso
    {I : Type uI} [Category.{vI} I] {M N : I ⥤ D} {c : Cone M}
    (hc : IsEssentiallyConstantCofilteredCone c) (e : M ≅ N) :
    IsEssentiallyConstantCofilteredCone ((Cone.postcompose e.hom).obj c) := by
  -- Proof comment: unpack the chosen split-mono cone leg and transport its factorization data
  -- across the componentwise isomorphisms of the diagram isomorphism `e`.
  rw [isEssentiallyConstantCofilteredCone_iff] at hc ⊢
  rcases hc with ⟨i, σ, hσ⟩
  have hsplit : SplitMono (((Cone.postcompose e.hom).obj c).π.app i) := by
    refine ⟨(e.inv.app i) ≫ σ.retraction, ?_⟩
    simp [Category.assoc, σ.id]
  refine ⟨i, hsplit, ?_⟩
  intro j
  rcases hσ j with ⟨k, ki, kj, hkj⟩
  refine ⟨k, ki, kj, ?_⟩
  -- Proof comment: rewrite the transported transition map through `e.inv`, then insert the
  -- original eventual factorization coming from the chosen essentially constant cone on `M`.
  calc
    N.map kj = N.map kj ≫ e.inv.app j ≫ e.hom.app j := by
      simp [Category.assoc]
    _ = e.inv.app k ≫ M.map kj ≫ e.hom.app j := by
      rw [e.inv.naturality kj]
      simp [Category.assoc]
    _ = e.inv.app k ≫ (M.map ki ≫ σ.retraction ≫ c.π.app j) ≫ e.hom.app j := by
      rw [hkj]
    _ = N.map ki ≫ (e.inv.app i ≫ σ.retraction) ≫ (((Cone.postcompose e.hom).obj c).π.app j) := by
      rw [← e.inv.naturality ki]
      simp [Category.assoc]

/-- Helper for Lemma 13.42.2: a natural isomorphism of cofiltered diagrams transports essential
constancy. -/
private theorem cofilteredDiagram_of_iso
    {I : Type uI} [Category.{vI} I] {M N : I ⥤ D} (e : M ≅ N)
    (hM : IsEssentiallyConstantCofilteredDiagram M) :
    IsEssentiallyConstantCofilteredDiagram N := by
  rcases hM with ⟨c, hc⟩
  -- Proof comment: postcompose the chosen essentially constant cone along the diagram
  -- isomorphism and reuse the transported split-mono/factorization data above.
  exact ⟨(Cone.postcompose e.hom).obj c, cofilteredCone_postcompose_iso hc e⟩

/-- Helper for Lemma 13.42.2: reindexing a sequential inverse system along the canonical
`OrderDual ℕ` equivalence preserves essential constancy. -/
private theorem essentiallyConstant_reindex_orderDual_equivalence
    {F : SequentialInverseSystem D} (hF : IsEssentiallyConstantCofilteredDiagram F) :
    IsEssentiallyConstantCofilteredDiagram
      (((CategoryTheory.orderDualEquivalence ℕ).functor) ⋙ F) := by
  let e := CategoryTheory.orderDualEquivalence ℕ
  -- Proof comment: `e.functor` is initial because it comes from an equivalence, so
  -- Lemma 4.22.13 transports essential constancy directly to the pulled-back system.
  exact (essentiallyConstantCofilteredDiagram_iff_comp_initial (H := e.functor) F).1 hF

/-- Helper for Lemma 13.42.2: after reindexing to `OrderDual ℕ`, Lemma 13.42.1 supplies the raw
tail direct-sum decomposition for an essentially constant sequential inverse system. -/
private theorem hasTailDirectSumDecomposition_of_essentiallyConstant_sequential
    {F : SequentialInverseSystem D} (hF : IsEssentiallyConstantCofilteredDiagram F) :
    HasTailDirectSumDecomposition (((CategoryTheory.orderDualEquivalence ℕ).functor) ⋙ F) := by
  -- Proof comment: the reindexing helper puts the sequential system into the exact `OrderDual`
  -- format expected by Lemma 13.42.1.
  exact
    (isEssentiallyConstantCofilteredDiagram_iff_hasEventuallyConstantDirectSumDecomposition
      (((CategoryTheory.orderDualEquivalence ℕ).functor) ⋙ F)).1
      (essentiallyConstant_reindex_orderDual_equivalence hF)

/-- Helper for Lemma 13.42.2: evaluating a tail direct-sum decomposition at a concrete stage
produces the expected projection/section pair onto the fixed summand. -/
private theorem stage_split_of_tail_direct_sum_decomposition
    {F : SequentialInverseSystem D}
    (hF : HasTailDirectSumDecomposition (((CategoryTheory.orderDualEquivalence ℕ).functor) ⋙ F)) :
    ∃ (N : ℕ) (A : D) (Z : OrderDual (Set.Ici N) ⥤ D)
      (e :
        ((((CategoryTheory.orderDualEquivalence ℕ).functor) ⋙ F).tail N) ≅
          (Functor.const (OrderDual (Set.Ici N))).obj A ⊞ Z),
      ∀ m (hm : N ≤ m),
        let p : F.obj (op m) ⟶ A := (e.app ⟨m, hm⟩).hom ≫ biprod.fst
        let i : A ⟶ F.obj (op m) := biprod.inl ≫ (e.app ⟨m, hm⟩).inv
        i ≫ p = 𝟙 A := by
  rcases hF with ⟨N, A, Z, e, hzero⟩
  refine ⟨N, A, Z, e, ?_⟩
  intro m hm
  -- Proof comment: the stagewise projection/section pair is just `biprod.fst` and `biprod.inl`
  -- transported across the evaluated tail isomorphism.
  simp [Category.assoc]

/-- Helper for Lemma 13.42.2: the fixed-summand projection obtained from a tail direct-sum
decomposition is preserved by every later transition map on the tail. -/
private theorem stage_projection_naturality_of_tail_direct_sum_decomposition
    {F : SequentialInverseSystem D}
    (hF : HasTailDirectSumDecomposition (((CategoryTheory.orderDualEquivalence ℕ).functor) ⋙ F)) :
    ∃ (N : ℕ) (A : D) (Z : OrderDual (Set.Ici N) ⥤ D)
      (e :
        ((((CategoryTheory.orderDualEquivalence ℕ).functor) ⋙ F).tail N) ≅
          (Functor.const (OrderDual (Set.Ici N))).obj A ⊞ Z),
      ∀ ⦃m m' : ℕ⦄ (hm : N ≤ m) (hm' : N ≤ m') (hmm' : m ≤ m'),
        F.transitionMap hmm' ≫ ((e.app ⟨m, hm⟩).hom ≫ biprod.fst) =
          (e.app ⟨m', hm'⟩).hom ≫ biprod.fst := by
  rcases hF with ⟨N, A, Z, e, hzero⟩
  refine ⟨N, A, Z, e, ?_⟩
  intro m m' hm hm' hmm'
  -- Proof comment: this is the `biprod.fst` component of the functoriality equation from
  -- `tailDirectSumIso_hom_naturality`; the constant summand is acted on by the identity.
  let j : Set.Ici N := ⟨m, hm⟩
  let j' : Set.Ici N := ⟨m', hm'⟩
  have hnat :
      ((((CategoryTheory.orderDualEquivalence ℕ).functor) ⋙ F).tail N).mapLE
          (show j ≤ j' from hmm') ≫
          (e.app j).hom =
        (e.app j').hom ≫
          (((Functor.const (OrderDual (Set.Ici N))).obj A ⊞ Z).mapLE
            (show j ≤ j' from hmm')) := by
    simpa [j, j'] using
      tailDirectSumIso_hom_naturality (F := (((CategoryTheory.orderDualEquivalence ℕ).functor) ⋙ F))
        (i := N) (A := A) (Z := Z) e (j := j) (j' := j') (show j ≤ j' from hmm')
  -- Proof comment: postcompose with `biprod.fst`; the biproduct transition map acts by the
  -- identity on the constant summand.
  simpa [Functor.tail, Functor.mapLE, SequentialInverseSystem.transitionMap, j, j',
    Category.assoc] using congrArg (fun f ↦ f ≫ biprod.fst) hnat

/-- Helper for Lemma 13.42.2: transition morphisms in a cofiltered preorder-indexed diagram
factor through every intermediate tail stage. -/
private theorem mapLE_comp
    {J : Type*} [Preorder J] {F : OrderDual J ⥤ D}
    {j j' j'' : J} (hjj' : j ≤ j') (hj'j'' : j' ≤ j'') :
    F.mapLE (show j ≤ j'' from le_trans hjj' hj'j'') =
      F.mapLE hj'j'' ≫ F.mapLE hjj' := by
  -- Proof comment: this is just `Functor.map_comp` on the unique composite in the preorder
  -- category, rewritten back into the tail-notation `mapLE`.
  have hh :
      homOfLE (show (j'' : OrderDual J) ≤ j from le_trans hjj' hj'j'') =
        homOfLE (show (j'' : OrderDual J) ≤ j' from hj'j'') ≫
          homOfLE (show (j' : OrderDual J) ≤ j from hjj') := by
    subsingleton
  simpa [Functor.mapLE, Functor.map_comp] using congrArg F.map hh

/-- Helper for Lemma 13.42.2: from the eventual-zero clause on the complementary tail, one can
choose a later positive stage whose transition map back to any fixed base stage is already zero. -/
private theorem zero_kill_stage_of_eventually_zero_tail
    {N : ℕ} {Z : OrderDual (Set.Ici N) ⥤ D}
    (hzero : ∀ j : Set.Ici N, ∃ j' : Set.Ici N, ∃ hjj' : j ≤ j', Z.mapLE hjj' = 0)
    {m₀ : ℕ} (hm₀ : N ≤ m₀) :
    ∃ n : ℕ, ∃ hn : m₀ ≤ n + 1,
      Z.mapLE
          (show (⟨m₀, hm₀⟩ : Set.Ici N) ≤
              ⟨n + 1, Nat.le_trans hm₀ hn⟩ from hn) = 0 := by
  let j : Set.Ici N := ⟨m₀, hm₀⟩
  rcases hzero j with ⟨j', hjj', hz⟩
  let j'' : Set.Ici N := ⟨j'.1 + 1, Nat.le_trans j'.2 (Nat.le_add_right j'.1 1)⟩
  have hj'j'' : j' ≤ j'' := Nat.le_add_right j'.1 1
  refine ⟨j'.1, Nat.le_trans hjj' hj'j'', ?_⟩
  -- Proof comment: once the transition to `j'` is zero, any further transition factors through
  -- that zero map by `mapLE_comp`, so the map from the later positive stage `j''.1 = j'.1 + 1`
  -- back to the chosen base stage also vanishes.
  simpa [j, j''] using calc
    Z.mapLE (show j ≤ j'' from Nat.le_trans hjj' hj'j'') =
        Z.mapLE hj'j'' ≫ Z.mapLE hjj' := by
          rw [mapLE_comp (F := Z) hjj' hj'j'']
    _ = 0 := by simp [hz]

/-- Helper for Lemma 13.42.2: the fixed-summand section coming from a tail direct-sum
decomposition is preserved by every later transition map. -/
private theorem stage_section_naturality_of_tail_direct_sum_decomposition
    {F : SequentialInverseSystem D} {N : ℕ} {A : D}
    {Z : OrderDual (Set.Ici N) ⥤ D}
    (e :
      ((((CategoryTheory.orderDualEquivalence ℕ).functor) ⋙ F).tail N) ≅
        (Functor.const (OrderDual (Set.Ici N))).obj A ⊞ Z)
    ⦃m m' : ℕ⦄ (hm : N ≤ m) (hm' : N ≤ m') (hmm' : m ≤ m') :
    biprod.inl ≫ (e.app ⟨m', hm'⟩).inv ≫ F.transitionMap hmm' =
      biprod.inl ≫ (e.app ⟨m, hm⟩).inv := by
  let j : Set.Ici N := ⟨m, hm⟩
  let j' : Set.Ici N := ⟨m', hm'⟩
  have hnat :
      (((Functor.const (OrderDual (Set.Ici N))).obj A ⊞ Z).mapLE
          (show j ≤ j' from hmm')) ≫
          (e.app j).inv =
        (e.app j').inv ≫
          ((((CategoryTheory.orderDualEquivalence ℕ).functor) ⋙ F).tail N).mapLE
            (show j ≤ j' from hmm') := by
    simpa [j, j'] using
      e.inv.naturality (homOfLE (show j ≤ j' from hmm'))
  -- Proof comment: the constant summand is transported by the identity, so precomposing with
  -- `biprod.inl` removes the tail transition on the split side entirely.
  simpa [Functor.tail, Functor.mapLE, SequentialInverseSystem.transitionMap, j, j',
    Category.assoc] using congrArg (fun f ↦ biprod.inl ≫ f) hnat

/-- Helper for Lemma 13.42.2: the fixed-summand projection coming from a tail direct-sum
decomposition is preserved by every later transition map. -/
private theorem stage_projection_naturality_of_tail_direct_sum_iso
    {F : SequentialInverseSystem D} {N : ℕ} {A : D}
    {Z : OrderDual (Set.Ici N) ⥤ D}
    (e :
      ((((CategoryTheory.orderDualEquivalence ℕ).functor) ⋙ F).tail N) ≅
        (Functor.const (OrderDual (Set.Ici N))).obj A ⊞ Z)
    ⦃m m' : ℕ⦄ (hm : N ≤ m) (hm' : N ≤ m') (hmm' : m ≤ m') :
    F.transitionMap hmm' ≫ ((e.app ⟨m, hm⟩).hom ≫ biprod.fst) =
      (e.app ⟨m', hm'⟩).hom ≫ biprod.fst := by
  let j : Set.Ici N := ⟨m, hm⟩
  let j' : Set.Ici N := ⟨m', hm'⟩
  have hnat :
      ((((CategoryTheory.orderDualEquivalence ℕ).functor) ⋙ F).tail N).mapLE
          (show j ≤ j' from hmm') ≫
          (e.app j).hom =
        (e.app j').hom ≫
          (((Functor.const (OrderDual (Set.Ici N))).obj A ⊞ Z).mapLE
            (show j ≤ j' from hmm')) := by
    simpa [j, j'] using
      tailDirectSumIso_hom_naturality
        (F := (((CategoryTheory.orderDualEquivalence ℕ).functor) ⋙ F))
        (i := N) (A := A) (Z := Z) e (j := j) (j' := j')
        (show j ≤ j' from hmm')
  -- Proof comment: postcompose with `biprod.fst`; the constant summand transition is the
  -- identity, so only the stage projection remains.
  simpa [Functor.tail, Functor.mapLE, SequentialInverseSystem.transitionMap, j, j',
    Category.assoc] using congrArg (fun f ↦ f ≫ biprod.fst) hnat

/-- Helper for Lemma 13.42.2: after transporting through the outer tail splittings, the
`C ⟶ A⟦(1 : ℤ)⟧` component of the connecting morphism is independent of the chosen later stage. -/
private theorem fixed_connecting_component_of_outer_tail_splits
    {T : SequentialInverseSystem (Triangle D)}
    {N₁ N₃ m₀ k : ℕ} {A C : D}
    {Z₁ : OrderDual (Set.Ici N₁) ⥤ D} {Z₃ : OrderDual (Set.Ici N₃) ⥤ D}
    (e₁ :
      ((((CategoryTheory.orderDualEquivalence ℕ).functor) ⋙ (T ⋙ Triangle.π₁)).tail N₁) ≅
        (Functor.const (OrderDual (Set.Ici N₁))).obj A ⊞ Z₁)
    (e₃ :
      ((((CategoryTheory.orderDualEquivalence ℕ).functor) ⋙ (T ⋙ Triangle.π₃)).tail N₃) ≅
        (Functor.const (OrderDual (Set.Ici N₃))).obj C ⊞ Z₃)
    (hm₀₁ : N₁ ≤ m₀) (hm₀₃ : N₃ ≤ m₀)
    (hk₁ : N₁ ≤ k) (hk₃ : N₃ ≤ k) (hm₀k : m₀ ≤ k) :
    biprod.inl ≫ (e₃.app ⟨k, hk₃⟩).inv ≫ (T.obj (op k)).mor₃ ≫
        ((e₁.app ⟨k, hk₁⟩).hom ≫ biprod.fst)⟦(1 : ℤ)⟧' =
      biprod.inl ≫ (e₃.app ⟨m₀, hm₀₃⟩).inv ≫ (T.obj (op m₀)).mor₃ ≫
        ((e₁.app ⟨m₀, hm₀₁⟩).hom ≫ biprod.fst)⟦(1 : ℤ)⟧' := by
  have hproj :
      (T ⋙ Triangle.π₁).transitionMap hm₀k ≫
          ((e₁.app ⟨m₀, hm₀₁⟩).hom ≫ biprod.fst) =
        (e₁.app ⟨k, hk₁⟩).hom ≫ biprod.fst := by
    -- Proof comment: on the first outer term, the fixed-summand projection is constant along
    -- the tail because the direct-sum decomposition is natural.
    simpa using
      stage_projection_naturality_of_tail_direct_sum_iso
        (F := T ⋙ Triangle.π₁) e₁ hm₀₁ hk₁ hm₀k
  have hproj_shift :
      ((T ⋙ Triangle.π₁).transitionMap hm₀k)⟦(1 : ℤ)⟧' ≫
          ((e₁.app ⟨m₀, hm₀₁⟩).hom ≫ biprod.fst)⟦(1 : ℤ)⟧' =
        ((e₁.app ⟨k, hk₁⟩).hom ≫ biprod.fst)⟦(1 : ℤ)⟧' := by
    -- Proof comment: shift the first-term projection equality so that it matches the target of
    -- the third morphism in the triangles.
    simpa [Functor.map_comp] using congrArg (fun f ↦ f⟦(1 : ℤ)⟧') hproj
  have hsec :
      biprod.inl ≫ (e₃.app ⟨k, hk₃⟩).inv ≫ (T ⋙ Triangle.π₃).transitionMap hm₀k =
        biprod.inl ≫ (e₃.app ⟨m₀, hm₀₃⟩).inv := by
    -- Proof comment: on the third outer term, the fixed summand is carried identically through
    -- the tail transitions.
    simpa using
      stage_section_naturality_of_tail_direct_sum_decomposition
        (F := T ⋙ Triangle.π₃) e₃ hm₀₃ hk₃ hm₀k
  -- Proof comment: rewrite the later-stage fixed component through the transition morphism of the
  -- triangle system, then move the constant summand section and projection back to the base stage.
  calc
    biprod.inl ≫ (e₃.app ⟨k, hk₃⟩).inv ≫ (T.obj (op k)).mor₃ ≫
        ((e₁.app ⟨k, hk₁⟩).hom ≫ biprod.fst)⟦(1 : ℤ)⟧' =
      biprod.inl ≫ (e₃.app ⟨k, hk₃⟩).inv ≫ (T.obj (op k)).mor₃ ≫
        ((T ⋙ Triangle.π₁).transitionMap hm₀k)⟦(1 : ℤ)⟧' ≫
        ((e₁.app ⟨m₀, hm₀₁⟩).hom ≫ biprod.fst)⟦(1 : ℤ)⟧' := by
          rw [Category.assoc, Category.assoc, hproj_shift]
    _ = biprod.inl ≫ (e₃.app ⟨k, hk₃⟩).inv ≫ (T ⋙ Triangle.π₃).transitionMap hm₀k ≫
        (T.obj (op m₀)).mor₃ ≫
        ((e₁.app ⟨m₀, hm₀₁⟩).hom ≫ biprod.fst)⟦(1 : ℤ)⟧' := by
          rw [← Category.assoc, ← Category.assoc, ← Category.assoc,
            (T.transitionMap hm₀k).comm₃]
    _ = biprod.inl ≫ (e₃.app ⟨m₀, hm₀₃⟩).inv ≫ (T.obj (op m₀)).mor₃ ≫
        ((e₁.app ⟨m₀, hm₀₁⟩).hom ≫ biprod.fst)⟦(1 : ℤ)⟧' := by
          rw [hsec]

/-- Helper for Lemma 13.42.2: once the complementary third-tail transition back to the base stage
is zero, the later-stage third morphism restricts to the fixed connecting morphism on the outer
summands. -/
private theorem connecting_square_of_outer_tail_splits
    {T : SequentialInverseSystem (Triangle D)}
    {N₁ N₃ m₀ m : ℕ} {A C : D}
    {Z₁ : OrderDual (Set.Ici N₁) ⥤ D} {Z₃ : OrderDual (Set.Ici N₃) ⥤ D}
    (e₁ :
      ((((CategoryTheory.orderDualEquivalence ℕ).functor) ⋙ (T ⋙ Triangle.π₁)).tail N₁) ≅
        (Functor.const (OrderDual (Set.Ici N₁))).obj A ⊞ Z₁)
    (e₃ :
      ((((CategoryTheory.orderDualEquivalence ℕ).functor) ⋙ (T ⋙ Triangle.π₃)).tail N₃) ≅
        (Functor.const (OrderDual (Set.Ici N₃))).obj C ⊞ Z₃)
    (hm₀₁ : N₁ ≤ m₀) (hm₀₃ : N₃ ≤ m₀)
    (hm₁ : N₁ ≤ m) (hm₃ : N₃ ≤ m) (hm₀m : m₀ ≤ m)
    (hzero₃_stage :
      Z₃.mapLE
          (show (⟨m₀, hm₀₃⟩ : Set.Ici N₃) ≤
              ⟨m, hm₃⟩ from hm₀m) = 0) :
    let a_m : (T.obj (op m)).obj₁ ⟶ A := (e₁.app ⟨m, hm₁⟩).hom ≫ biprod.fst
    let c_m : (T.obj (op m)).obj₃ ⟶ C := (e₃.app ⟨m, hm₃⟩).hom ≫ biprod.fst
    let δ : C ⟶ A⟦(1 : ℤ)⟧ :=
      biprod.inl ≫ (e₃.app ⟨m₀, hm₀₃⟩).inv ≫ (T.obj (op m₀)).mor₃ ≫
        ((e₁.app ⟨m₀, hm₀₁⟩).hom ≫ biprod.fst)⟦(1 : ℤ)⟧'
    in (T.obj (op m)).mor₃ ≫ a_m⟦(1 : ℤ)⟧' = c_m ≫ δ := by
  dsimp
  have hproj_shift :
      ((T ⋙ Triangle.π₁).transitionMap hm₀m)⟦(1 : ℤ)⟧' ≫
          ((e₁.app ⟨m₀, hm₀₁⟩).hom ≫ biprod.fst)⟦(1 : ℤ)⟧' =
        ((e₁.app ⟨m, hm₁⟩).hom ≫ biprod.fst)⟦(1 : ℤ)⟧' := by
    have hproj :
        (T ⋙ Triangle.π₁).transitionMap hm₀m ≫
            ((e₁.app ⟨m₀, hm₀₁⟩).hom ≫ biprod.fst) =
          (e₁.app ⟨m, hm₁⟩).hom ≫ biprod.fst := by
      simpa using
        stage_projection_naturality_of_tail_direct_sum_iso
          (F := T ⋙ Triangle.π₁) e₁ hm₀₁ hm₁ hm₀m
    simpa [Functor.map_comp] using congrArg (fun f ↦ f⟦(1 : ℤ)⟧') hproj
  apply (cancel_epi ((e₃.app ⟨m, hm₃⟩).inv)).1
  apply biprod.hom_ext
  · -- Proof comment: the `C`-summand is exactly the stage-independent connecting component from
    -- the previous helper.
    simpa [Category.assoc] using
      fixed_connecting_component_of_outer_tail_splits
        (T := T) e₁ e₃ hm₀₁ hm₀₃ hm₁ hm₃ hm₀m
  · -- Proof comment: the complementary `Z₃`-summand factors through the vanishing transition
    -- back to the base stage, so it contributes nothing to the outer square.
    calc
      biprod.inr ≫ (e₃.app ⟨m, hm₃⟩).inv ≫ (T.obj (op m)).mor₃ ≫
          ((e₁.app ⟨m, hm₁⟩).hom ≫ biprod.fst)⟦(1 : ℤ)⟧' =
        biprod.inr ≫ (e₃.app ⟨m, hm₃⟩).inv ≫ (T.obj (op m)).mor₃ ≫
          ((T ⋙ Triangle.π₁).transitionMap hm₀m)⟦(1 : ℤ)⟧' ≫
          ((e₁.app ⟨m₀, hm₀₁⟩).hom ≫ biprod.fst)⟦(1 : ℤ)⟧' := by
            rw [Category.assoc, Category.assoc, hproj_shift]
      _ = biprod.inr ≫ (e₃.app ⟨m, hm₃⟩).inv ≫ (T ⋙ Triangle.π₃).transitionMap hm₀m ≫
          (T.obj (op m₀)).mor₃ ≫
          ((e₁.app ⟨m₀, hm₀₁⟩).hom ≫ biprod.fst)⟦(1 : ℤ)⟧' := by
            rw [← Category.assoc, ← Category.assoc, ← Category.assoc,
              (T.transitionMap hm₀m).comm₃]
      _ = Z₃.mapLE (show (⟨m₀, hm₀₃⟩ : Set.Ici N₃) ≤ ⟨m, hm₃⟩ from hm₀m) ≫
          (biprod.inr ≫ (e₃.app ⟨m₀, hm₀₃⟩).inv ≫ (T.obj (op m₀)).mor₃ ≫
            ((e₁.app ⟨m₀, hm₀₁⟩).hom ≫ biprod.fst)⟦(1 : ℤ)⟧') := by
            have hnat :
                biprod.inr ≫ (e₃.app ⟨m, hm₃⟩).inv ≫ (T ⋙ Triangle.π₃).transitionMap hm₀m =
                  Z₃.mapLE (show (⟨m₀, hm₀₃⟩ : Set.Ici N₃) ≤ ⟨m, hm₃⟩ from hm₀m) ≫
                    biprod.inr ≫ (e₃.app ⟨m₀, hm₀₃⟩).inv := by
              let j : Set.Ici N₃ := ⟨m₀, hm₀₃⟩
              let j' : Set.Ici N₃ := ⟨m, hm₃⟩
              have hnat' :
                  (((Functor.const (OrderDual (Set.Ici N₃))).obj C ⊞ Z₃).mapLE
                      (show j ≤ j' from hm₀m)) ≫ (e₃.app j).inv =
                    (e₃.app j').inv ≫
                      ((((CategoryTheory.orderDualEquivalence ℕ).functor) ⋙
                        (T ⋙ Triangle.π₃)).tail N₃).mapLE (show j ≤ j' from hm₀m) := by
                simpa [j, j'] using
                  e₃.inv.naturality (homOfLE (show j ≤ j' from hm₀m))
              simpa [Functor.tail, Functor.mapLE, SequentialInverseSystem.transitionMap, j, j',
                Category.assoc] using congrArg (fun f ↦ biprod.inr ≫ f) hnat'.symm
            rw [hnat]
            simp [Category.assoc]
      _ = 0 := by simp [hzero₃_stage, Category.assoc]
      _ = biprod.inr ≫ (e₃.app ⟨m, hm₃⟩).inv ≫
          ((e₃.app ⟨m, hm₃⟩).hom ≫ biprod.fst) ≫
          (biprod.inl ≫ (e₃.app ⟨m₀, hm₀₃⟩).inv ≫ (T.obj (op m₀)).mor₃ ≫
            ((e₁.app ⟨m₀, hm₀₁⟩).hom ≫ biprod.fst)⟦(1 : ℤ)⟧') := by
            simp [Category.assoc]

/-- Helper for Lemma 13.42.2: equality in a sequential colimit of types can be checked after
transporting both representatives to a common later stage. -/
private theorem sequential_colimit_eq_at_common_stage
    {F : ℕ ⥤ Type*} {i j : ℕ} {x : F.obj i} {y : F.obj j}
    (h : colimit.ι F i x = colimit.ι F j y) :
    ∃ k, ∃ hi : i ≤ k, ∃ hj : j ≤ k,
      F.map (homOfLE hi) x = F.map (homOfLE hj) y := by
  -- Proof comment: this is the standard filtered-colimit equality criterion specialized to the
  -- linear order `ℕ`.
  rcases (Types.FilteredColimit.colimit_eq_iff (F := F)).1 h with ⟨k, f, g, hfg⟩
  exact ⟨k, leOfHom f, leOfHom g, by simpa [homOfLE_leOfHom] using hfg⟩

/-- Helper for Lemma 13.42.2: when the complementary summand transition from `k` back to `j` is
zero, every map out of `F_j` becomes represented at stage `k` by the fixed-summand projection. -/
private theorem stage_projection_representation_after_zero_tail_transition
    {F : SequentialInverseSystem D} {N : ℕ} {A : D}
    {Z : OrderDual (Set.Ici N) ⥤ D}
    (e :
      ((((CategoryTheory.orderDualEquivalence ℕ).functor) ⋙ F).tail N) ≅
        (Functor.const (OrderDual (Set.Ici N))).obj A ⊞ Z)
    {j k : ℕ} (hj : N ≤ j) (hk : N ≤ k) (hjk : j ≤ k)
    (hz : Z.mapLE (show (⟨j, hj⟩ : Set.Ici N) ≤ ⟨k, hk⟩ from hjk) = 0)
    {W : D} (f : F.obj (op j) ⟶ W) :
    F.transitionMap hjk ≫ f =
      ((e.app ⟨k, hk⟩).hom ≫ biprod.fst) ≫
        (biprod.inl ≫ (e.app ⟨j, hj⟩).inv ≫ f) := by
  have hnat :
      F.transitionMap hjk ≫ (e.app ⟨j, hj⟩).hom =
        (e.app ⟨k, hk⟩).hom ≫
          (((Functor.const (OrderDual (Set.Ici N))).obj A ⊞ Z).mapLE
            (show (⟨j, hj⟩ : Set.Ici N) ≤ ⟨k, hk⟩ from hjk)) := by
    -- Proof comment: the direct-sum splitting is natural along the tail transition `j ≤ k`.
    simpa [Functor.tail, Functor.mapLE, SequentialInverseSystem.transitionMap] using
      tailDirectSumIso_hom_naturality
        (F := (((CategoryTheory.orderDualEquivalence ℕ).functor) ⋙ F))
        (i := N) (A := A) (Z := Z) e
        (j := ⟨j, hj⟩) (j' := ⟨k, hk⟩) (show (⟨j, hj⟩ : Set.Ici N) ≤ ⟨k, hk⟩ from hjk)
  -- Proof comment: with `Z.mapLE = 0`, the biproduct transition is just projection to the fixed
  -- `A`-summand followed by the inclusion of that summand at stage `j`.
  calc
    F.transitionMap hjk ≫ f =
      F.transitionMap hjk ≫ (e.app ⟨j, hj⟩).hom ≫ (e.app ⟨j, hj⟩).inv ≫ f := by
        simp [Category.assoc]
    _ =
      (e.app ⟨k, hk⟩).hom ≫
        (((Functor.const (OrderDual (Set.Ici N))).obj A ⊞ Z).mapLE
          (show (⟨j, hj⟩ : Set.Ici N) ≤ ⟨k, hk⟩ from hjk)) ≫
        (e.app ⟨j, hj⟩).inv ≫ f := by
          rw [hnat]
    _ =
      (e.app ⟨k, hk⟩).hom ≫ biprod.fst ≫ biprod.inl ≫ (e.app ⟨j, hj⟩).inv ≫ f := by
          simp [Functor.mapLE, hz, Category.assoc]
    _ =
      ((e.app ⟨k, hk⟩).hom ≫ biprod.fst) ≫
        (biprod.inl ≫ (e.app ⟨j, hj⟩).inv ≫ f) := by
          simp [Category.assoc]

/-- Helper for Lemma 13.42.2: the fixed-summand stage projection from a tail direct-sum
decomposition is surjective on the canonical Hom-colimit comparison map. -/
private theorem stage_projection_hom_colimit_surjective_of_tail_split
    {F : SequentialInverseSystem D} {N m : ℕ} {A : D}
    {Z : OrderDual (Set.Ici N) ⥤ D}
    (e :
      ((((CategoryTheory.orderDualEquivalence ℕ).functor) ⋙ F).tail N) ≅
        (Functor.const (OrderDual (Set.Ici N))).obj A ⊞ Z)
    (hzero : ∀ j : Set.Ici N, ∃ j' : Set.Ici N, ∃ hjj' : j ≤ j', Z.mapLE hjj' = 0)
    (hm : N ≤ m) :
    ∀ W : D, Function.Surjective
      (fun g : A ⟶ W ↦
        colimit.ι (F.op ⋙ uliftYoneda.obj W) m
          (ULift.up (((e.app ⟨m, hm⟩).hom ≫ biprod.fst) ≫ g))) := by
  intro W x
  obtain ⟨j, y, rfl⟩ := Types.jointly_surjective' x
  rcases y with ⟨f⟩
  let j₀ : ℕ := max m j
  have hj₀ : N ≤ j₀ := Nat.le_trans hm (Nat.le_max_left m j)
  let f₀ : F.obj (op j₀) ⟶ W := F.transitionMap (Nat.le_max_right m j) ≫ f
  have hclass_j₀ :
      colimit.ι (F.op ⋙ uliftYoneda.obj W) j (ULift.up f) =
        colimit.ι (F.op ⋙ uliftYoneda.obj W) j₀ (ULift.up f₀) := by
    -- Proof comment: first move the given colimit representative to the common later stage
    -- `j₀ = max m j`.
    refine Types.colimit_sound (F := F.op ⋙ uliftYoneda.obj W)
      (f := homOfLE (Nat.le_max_right m j)) ?_
    exact congrArg ULift.up rfl
  rcases hzero ⟨j₀, hj₀⟩ with ⟨k, hj₀k, hz⟩
  have hmk : m ≤ k := Nat.le_trans (Nat.le_max_left m j) hj₀k
  let g : A ⟶ W := biprod.inl ≫ (e.app ⟨j₀, hj₀⟩).inv ≫ f₀
  have hrep_k :
      F.transitionMap hj₀k ≫ f₀ =
        ((e.app ⟨k, k.2⟩).hom ≫ biprod.fst) ≫ g := by
    -- Proof comment: once the complementary transition to stage `j₀` is zero, only the fixed
    -- `A`-summand survives at the later stage `k`.
    simpa [g, Category.assoc] using
      stage_projection_representation_after_zero_tail_transition
        (F := F) (A := A) (Z := Z) e hj₀ k.2 hj₀k hz f₀
  have hclass_k :
      colimit.ι (F.op ⋙ uliftYoneda.obj W) j₀ (ULift.up f₀) =
        colimit.ι (F.op ⋙ uliftYoneda.obj W) k
          (ULift.up (F.transitionMap hj₀k ≫ f₀)) := by
    -- Proof comment: transport the stage-`j₀` representative to the later stage where the
    -- complementary summand has vanished.
    refine Types.colimit_sound (F := F.op ⋙ uliftYoneda.obj W) (f := homOfLE hj₀k) ?_
    exact congrArg ULift.up rfl
  have hforward_k :
      colimit.ι (F.op ⋙ uliftYoneda.obj W) m
          (ULift.up (((e.app ⟨m, hm⟩).hom ≫ biprod.fst) ≫ g)) =
        colimit.ι (F.op ⋙ uliftYoneda.obj W) k
          (ULift.up (((e.app ⟨k, k.2⟩).hom ≫ biprod.fst) ≫ g)) := by
    have hproj :
        F.transitionMap hmk ≫ ((e.app ⟨m, hm⟩).hom ≫ biprod.fst) =
          (e.app ⟨k, k.2⟩).hom ≫ biprod.fst := by
      -- Proof comment: the fixed-summand projection is constant along the tail.
      simpa using
        stage_projection_naturality_of_tail_direct_sum_iso
          (F := F) e hm k.2 hmk
    have hproj_g :
        F.transitionMap hmk ≫ (((e.app ⟨m, hm⟩).hom ≫ biprod.fst) ≫ g) =
          ((e.app ⟨k, k.2⟩).hom ≫ biprod.fst) ≫ g := by
      simpa [Category.assoc] using congrArg (fun t ↦ t ≫ g) hproj
    refine Types.colimit_sound (F := F.op ⋙ uliftYoneda.obj W) (f := homOfLE hmk) ?_
    exact congrArg ULift.up hproj_g
  refine ⟨g, ?_⟩
  -- Proof comment: compare the chosen `g` with the original colimit class by transporting both
  -- representatives to the common later stage `k`.
  calc
    colimit.ι (F.op ⋙ uliftYoneda.obj W) m
        (ULift.up (((e.app ⟨m, hm⟩).hom ≫ biprod.fst) ≫ g)) =
      colimit.ι (F.op ⋙ uliftYoneda.obj W) k
        (ULift.up (((e.app ⟨k, k.2⟩).hom ≫ biprod.fst) ≫ g)) := hforward_k
    _ =
      colimit.ι (F.op ⋙ uliftYoneda.obj W) k
        (ULift.up (F.transitionMap hj₀k ≫ f₀)) := by rw [hrep_k]
    _ =
      colimit.ι (F.op ⋙ uliftYoneda.obj W) j₀ (ULift.up f₀) := hclass_k.symm
    _ =
      colimit.ι (F.op ⋙ uliftYoneda.obj W) j (ULift.up f) := hclass_j₀.symm

/-- Helper for Lemma 13.42.2: the fixed-summand stage projection from a tail direct-sum
decomposition is injective on the canonical Hom-colimit comparison map. -/
private theorem stage_projection_hom_colimit_injective_of_tail_split
    {F : SequentialInverseSystem D} {N m : ℕ} {A : D}
    {Z : OrderDual (Set.Ici N) ⥤ D}
    (e :
      ((((CategoryTheory.orderDualEquivalence ℕ).functor) ⋙ F).tail N) ≅
        (Functor.const (OrderDual (Set.Ici N))).obj A ⊞ Z)
    (hm : N ≤ m) :
    ∀ W : D, Function.Injective
      (fun g : A ⟶ W ↦
        colimit.ι (F.op ⋙ uliftYoneda.obj W) m
          (ULift.up (((e.app ⟨m, hm⟩).hom ≫ biprod.fst) ≫ g))) := by
  intro W g₁ g₂ hEq
  rcases sequential_colimit_eq_at_common_stage
      (F := F.op ⋙ uliftYoneda.obj W) hEq with ⟨k, hmk₁, hmk₂, hstage⟩
  have hmk : m ≤ k := hmk₁
  have hk : N ≤ k := Nat.le_trans hm hmk
  have hproj₁ :
      F.transitionMap hmk ≫ ((e.app ⟨m, hm⟩).hom ≫ biprod.fst) =
        (e.app ⟨k, hk⟩).hom ≫ biprod.fst := by
    -- Proof comment: both representatives are compared after transporting to the same later
    -- stage `k`, where the stage projection is canonical.
    simpa using
      stage_projection_naturality_of_tail_direct_sum_iso
        (F := F) e hm hk hmk
  have hproj₁_g₁ :
      F.transitionMap hmk ≫ (((e.app ⟨m, hm⟩).hom ≫ biprod.fst) ≫ g₁) =
        ((e.app ⟨k, hk⟩).hom ≫ biprod.fst) ≫ g₁ := by
    simpa [Category.assoc] using congrArg (fun t ↦ t ≫ g₁) hproj₁
  have hproj₁_g₂ :
      F.transitionMap hmk₂ ≫ (((e.app ⟨m, hm⟩).hom ≫ biprod.fst) ≫ g₂) =
        ((e.app ⟨k, hk⟩).hom ≫ biprod.fst) ≫ g₂ := by
    simpa [Category.assoc] using
      congrArg (fun t ↦ t ≫ g₂)
        (stage_projection_naturality_of_tail_direct_sum_iso
          (F := F) e hm hk hmk₂)
  have hstage' :
      ((e.app ⟨k, hk⟩).hom ≫ biprod.fst) ≫ g₁ =
        ((e.app ⟨k, hk⟩).hom ≫ biprod.fst) ≫ g₂ := by
    -- Proof comment: equality in the colimit forces equality of the two transported stage
    -- representatives at the common later stage.
    simpa [hproj₁_g₁, hproj₁_g₂] using congrArg ULift.down hstage
  have hsplit :
      (biprod.inl ≫ (e.app ⟨k, hk⟩).inv) ≫
          ((e.app ⟨k, hk⟩).hom ≫ biprod.fst) = 𝟙 A := by
    -- Proof comment: the chosen section at stage `k` retracts the fixed-summand projection.
    simp [Category.assoc]
  calc
    g₁ = (𝟙 A) ≫ g₁ := by simp
    _ =
      ((biprod.inl ≫ (e.app ⟨k, hk⟩).inv) ≫
        ((e.app ⟨k, hk⟩).hom ≫ biprod.fst)) ≫ g₁ := by rw [hsplit]
    _ =
      ((biprod.inl ≫ (e.app ⟨k, hk⟩).inv) ≫
        ((e.app ⟨k, hk⟩).hom ≫ biprod.fst)) ≫ g₂ := by rw [hstage']
    _ = (𝟙 A) ≫ g₂ := by rw [hsplit]
    _ = g₂ := by simp

/-- Helper for Lemma 13.42.2: every fixed-summand stage projection produced by a tail direct-sum
decomposition satisfies the stage-map Hom-colimit comparison criterion of Lemma `4.22.10`. -/
private theorem has_hom_colimit_comparison_of_stage_projection_from_tail_split
    {F : SequentialInverseSystem D} {N m : ℕ} {A : D}
    {Z : OrderDual (Set.Ici N) ⥤ D}
    (e :
      ((((CategoryTheory.orderDualEquivalence ℕ).functor) ⋙ F).tail N) ≅
        (Functor.const (OrderDual (Set.Ici N))).obj A ⊞ Z)
    (hzero : ∀ j : Set.Ici N, ∃ j' : Set.Ici N, ∃ hjj' : j ≤ j', Z.mapLE hjj' = 0)
    (hm : N ≤ m) :
    HasHomColimitComparison F
      (CostructuredArrow.mk ((e.app ⟨m, hm⟩).hom ≫ biprod.fst)) := by
  intro W
  classical
  let forward : (A ⟶ W) → colimit (F.op ⋙ uliftYoneda.obj W) := fun g ↦
    colimit.ι (F.op ⋙ uliftYoneda.obj W) m
      (ULift.up (((e.app ⟨m, hm⟩).hom ≫ biprod.fst) ≫ g))
  have hbij : Function.Bijective forward := by
    refine ⟨?_, ?_⟩
    · exact stage_projection_hom_colimit_injective_of_tail_split (F := F) e hm W
    · exact stage_projection_hom_colimit_surjective_of_tail_split (F := F) e hzero hm W
  refine ⟨⟨Equiv.ofBijective forward hbij, ?_⟩⟩
  intro g
  rfl

/-- Helper for Lemma 13.42.2: the canonical additive comparison map attached to a stage map
`p : F_m ⟶ X`. This is the additive-owner version of the Chapter 4 comparison function
`g ↦ [p ≫ g]`, and it is the map that will enter the five-lemma argument for the middle term. -/
private noncomputable abbrev preadditive_yoneda_comparison_map
    {F : SequentialInverseSystem D} {m : ℕ} {X : D}
    (p : F.obj (op m) ⟶ X) (W : D) :
    (preadditiveYoneda.obj W).obj (op X) ⟶ colimit (F.op ⋙ preadditiveYoneda.obj W) :=
  (preadditiveYoneda.obj W).map (op p) ≫ colimit.ι (F.op ⋙ preadditiveYoneda.obj W) m

/-- Helper for Lemma 13.42.2: the additive comparison map evaluates on a morphism `g : X ⟶ W`
by sending it to the colimit class of the composite `p ≫ g`. -/
private theorem preadditive_yoneda_comparison_map_apply
    {F : SequentialInverseSystem D} {m : ℕ} {X W : D}
    (p : F.obj (op m) ⟶ X) (g : X ⟶ W) :
    preadditive_yoneda_comparison_map (F := F) p W g =
      colimit.ι (F.op ⋙ preadditiveYoneda.obj W) m
        ((preadditiveYoneda.obj W).map (op p) g) := rfl

/-- Helper for Lemma 13.42.2: after forgetting the additive structure, the colimit of the
additive `preadditiveYoneda` diagram agrees with the Chapter 4 `uliftYoneda` colimit. This is the
transport bridge between the additive five-lemma surface and the owner-level Hom-colimit
comparison criterion. -/
private noncomputable def preadditive_yoneda_ulift_colimit_iso
    {F : SequentialInverseSystem D} (W : D) :
    colimit (F.op ⋙ uliftYoneda.obj W) ≅
      (forget AddCommGrpCat).obj (colimit (F.op ⋙ preadditiveYoneda.obj W)) := by
  let G : ℕ ⥤ AddCommGrpCat := F.op ⋙ preadditiveYoneda.obj W
  letI : PreservesFilteredColimits (forget AddCommGrpCat) :=
    AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits
  letI : PreservesFilteredColimitsOfSize.{0, 0} (forget AddCommGrpCat) :=
    preservesFilteredColimitsOfSize_shrink (forget AddCommGrpCat)
  letI : PreservesColimit G (forget AddCommGrpCat) := by
    infer_instance
  let e₁ :
      colimit (F.op ⋙ uliftYoneda.obj W) ≅
        colimit (F.op ⋙ yoneda.obj W) :=
    HasColimit.isoOfNatIso (Functor.isoWhiskerLeft F.op uliftYonedaIsoYoneda)
  let e₂ :
      colimit (F.op ⋙ yoneda.obj W) ≅
        (forget AddCommGrpCat).obj (colimit G) := by
    -- Proof comment: after rewriting away the additive decoration, this is the standard
    -- preserved-colimit comparison for `forget AddCommGrpCat`.
    simpa [G, whiskering_preadditiveYoneda, Functor.assoc] using
      (asIso (colimit.post G (forget AddCommGrpCat)))
  exact e₁ ≪≫ e₂

/-- Helper for Lemma 13.42.2: the additive-to-`uliftYoneda` colimit bridge sends the canonical
stage class of `f : F_m ⟶ W` to the same stage class in the additive colimit. -/
private theorem preadditive_yoneda_ulift_colimit_iso_hom_ι
    {F : SequentialInverseSystem D} {m : ℕ} {W : D} (f : F.obj (op m) ⟶ W) :
    (preadditive_yoneda_ulift_colimit_iso (F := F) W).hom
        (colimit.ι (F.op ⋙ uliftYoneda.obj W) m (ULift.up f)) =
      colimit.ι (F.op ⋙ preadditiveYoneda.obj W) m f := by
  let G : ℕ ⥤ AddCommGrpCat := F.op ⋙ preadditiveYoneda.obj W
  letI : PreservesFilteredColimits (forget AddCommGrpCat) :=
    AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits
  letI : PreservesFilteredColimitsOfSize.{0, 0} (forget AddCommGrpCat) :=
    preservesFilteredColimitsOfSize_shrink (forget AddCommGrpCat)
  letI : PreservesColimit G (forget AddCommGrpCat) := by
    infer_instance
  let e₁ :
      colimit (F.op ⋙ uliftYoneda.obj W) ≅
        colimit (F.op ⋙ yoneda.obj W) :=
    HasColimit.isoOfNatIso (Functor.isoWhiskerLeft F.op uliftYonedaIsoYoneda)
  let e₂ :
      colimit (F.op ⋙ yoneda.obj W) ≅
        (forget AddCommGrpCat).obj (colimit G) := by
    simpa [G, whiskering_preadditiveYoneda, Functor.assoc] using
      (asIso (colimit.post G (forget AddCommGrpCat)))
  -- Proof comment: first move from `uliftYoneda` to plain Yoneda, then apply the canonical
  -- filtered-colimit comparison for `forget AddCommGrpCat`.
  change (e₁ ≪≫ e₂).hom (colimit.ι (F.op ⋙ uliftYoneda.obj W) m (ULift.up f)) =
    colimit.ι G m f
  have h₁ :
      e₁.hom (colimit.ι (F.op ⋙ uliftYoneda.obj W) m (ULift.up f)) =
        colimit.ι (F.op ⋙ yoneda.obj W) m f := by
    simpa using
      congrFun
        (HasColimit.isoOfNatIso_ι_hom_assoc
          (e := Functor.isoWhiskerLeft F.op uliftYonedaIsoYoneda) (j := m))
        (ULift.up f)
  have h₂ :
      e₂.hom (colimit.ι (F.op ⋙ yoneda.obj W) m f) =
        colimit.ι G m f := by
    -- Proof comment: evaluate `colimit.post` on the stage leg and simplify away the whiskering
    -- equality between `preadditiveYoneda` and the ordinary Yoneda embedding.
    simpa [G, whiskering_preadditiveYoneda, Functor.assoc] using
      congrFun (colimit.ι_post G (forget AddCommGrpCat) m) f
  calc
    (e₁ ≪≫ e₂).hom (colimit.ι (F.op ⋙ uliftYoneda.obj W) m (ULift.up f)) =
      e₂.hom (e₁.hom (colimit.ι (F.op ⋙ uliftYoneda.obj W) m (ULift.up f))) := by
        rfl
    _ = e₂.hom (colimit.ι (F.op ⋙ yoneda.obj W) m f) := by rw [h₁]
    _ = colimit.ι G m f := h₂

/-- Helper for Lemma 13.42.2: the Chapter 4 stage-map Hom-colimit comparison for `p` is exactly
the statement that every additive comparison map `preadditive_yoneda_comparison_map p W` is an
isomorphism. -/
private theorem preadditive_yoneda_comparison_isIso_iff_hasHomColimitComparison
    {F : SequentialInverseSystem D} {m : ℕ} {X : D}
    (p : F.obj (op m) ⟶ X) :
    HasHomColimitComparison F (CostructuredArrow.mk p) ↔
      ∀ W : D, IsIso (preadditive_yoneda_comparison_map (F := F) p W) := by
  constructor
  · intro hp W
    classical
    let G : ℕ ⥤ AddCommGrpCat := F.op ⋙ preadditiveYoneda.obj W
    rcases hp W with ⟨e, he⟩
    let e' : (X ⟶ W) ≃ (forget AddCommGrpCat).obj (colimit G) :=
      e.trans (preadditive_yoneda_ulift_colimit_iso (F := F) W).toEquiv
    have hfun :
        (fun g : X ⟶ W ↦ preadditive_yoneda_comparison_map (F := F) p W g) = e' := by
      funext g
      -- Proof comment: the owner comparison formula for `e` becomes the additive comparison map
      -- after transporting the colimit class across the bridge above.
      calc
        preadditive_yoneda_comparison_map (F := F) p W g =
          (preadditive_yoneda_ulift_colimit_iso (F := F) W).hom
            (colimit.ι (F.op ⋙ uliftYoneda.obj W) m (ULift.up (p ≫ g))) := by
              simpa [preadditive_yoneda_comparison_map_apply] using
                (preadditive_yoneda_ulift_colimit_iso_hom_ι (F := F) (m := m) (W := W) (p ≫ g)).symm
        _ = e' g := by
              simp [e', he g]
    have hbij :
        Function.Bijective (fun g : X ⟶ W ↦ preadditive_yoneda_comparison_map (F := F) p W g) := by
      rw [hfun]
      exact e'.bijective
    exact (ConcreteCategory.isIso_iff_bijective _).2 hbij
  · intro hp
    intro W
    classical
    let G : ℕ ⥤ AddCommGrpCat := F.op ⋙ preadditiveYoneda.obj W
    have hbij :
        Function.Bijective
          (fun g : X ⟶ W ↦ preadditive_yoneda_comparison_map (F := F) p W g) := by
      -- Proof comment: once the additive comparison is an isomorphism, its underlying function
      -- is bijective in the concrete category `AddCommGrpCat`.
      exact (ConcreteCategory.isIso_iff_bijective _).1 (hp W)
    let eAdd :
        (X ⟶ W) ≃ (forget AddCommGrpCat).obj (colimit G) :=
      Equiv.ofBijective
        (fun g : X ⟶ W ↦ preadditive_yoneda_comparison_map (F := F) p W g) hbij
    refine ⟨?_⟩
    refine ⟨eAdd.trans (preadditive_yoneda_ulift_colimit_iso (F := F) W).symm.toEquiv, ?_⟩
    intro g
    -- Proof comment: invert the bridge from the previous helper and read the additive comparison
    -- map on the canonical stage representative `p ≫ g`.
    apply (preadditive_yoneda_ulift_colimit_iso (F := F) W).hom.injective
    calc
      (preadditive_yoneda_ulift_colimit_iso (F := F) W).hom
          ((eAdd.trans (preadditive_yoneda_ulift_colimit_iso (F := F) W).symm.toEquiv) g) =
        eAdd g := by
          simp [eAdd]
      _ = preadditive_yoneda_comparison_map (F := F) p W g := rfl
      _ =
        (preadditive_yoneda_ulift_colimit_iso (F := F) W).hom
          (colimit.ι (F.op ⋙ uliftYoneda.obj W) m (ULift.up (p ≫ g))) := by
            simpa [preadditive_yoneda_comparison_map_apply] using
              (preadditive_yoneda_ulift_colimit_iso_hom_ι (F := F) (m := m) (W := W) (p ≫ g)).symm

/-- Helper for Lemma 13.42.2: in the inverse-rotated five-term row for `preadditiveYoneda`, the
five vertical slot maps are the opposites of the expected additive comparison maps for the three
components of the triangle morphism. -/
private theorem inverse_rotated_preadditive_yoneda_slot_maps
    {T : SequentialInverseSystem (Triangle D)} {m : ℕ} {T' : Triangle D}
    (φ : T.obj (op m) ⟶ T') (W : D) :
    let H : D ⥤ AddCommGrpCatᵒᵖ := (preadditiveYoneda.obj W).rightOp
    let R₁ : Triangle D := (T.obj (op m)).invRotate
    let R₂ : Triangle D := T'.invRotate
    let ψ : R₁ ⟶ R₂ := (invRotate D).map φ
    let ψ₅ :
        H.homologySequenceComposableArrows₅ R₁ (0 : ℤ) 1 rfl ⟶
          H.homologySequenceComposableArrows₅ R₂ (0 : ℤ) 1 rfl :=
      ComposableArrows.homMk₅
        ((H.shift (0 : ℤ)).map ψ.hom₁) ((H.shift (0 : ℤ)).map ψ.hom₂)
        ((H.shift (0 : ℤ)).map ψ.hom₃) ((H.shift (1 : ℤ)).map ψ.hom₁)
        ((H.shift (1 : ℤ)).map ψ.hom₂) ((H.shift (1 : ℤ)).map ψ.hom₃)
        (by simpa [Functor.map_comp] using congrArg ((H.shift (0 : ℤ)).map) ψ.comm₁)
        (by simpa [Functor.map_comp] using congrArg ((H.shift (0 : ℤ)).map) ψ.comm₂)
        (by simpa using (H.homologySequenceδ_naturality R₁ R₂ ψ (0 : ℤ) 1 rfl).symm)
        (by simpa [Functor.map_comp] using congrArg ((H.shift (1 : ℤ)).map) ψ.comm₁)
        (by simpa [Functor.map_comp] using congrArg ((H.shift (1 : ℤ)).map) ψ.comm₂)
    let Ψ := δlastFunctor.map ψ₅
    ComposableArrows.app' Ψ 0 =
        (preadditive_yoneda_comparison_map
          (F := T ⋙ Triangle.π₁) φ.hom₁ (W⟦(1 : ℤ)⟧)).op ∧
      ComposableArrows.app' Ψ 1 =
        (preadditive_yoneda_comparison_map
          (F := T ⋙ Triangle.π₃) φ.hom₃ W).op ∧
      ComposableArrows.app' Ψ 2 =
        (preadditive_yoneda_comparison_map
          (F := T ⋙ Triangle.π₂) φ.hom₂ W).op ∧
      ComposableArrows.app' Ψ 3 =
        (preadditive_yoneda_comparison_map
          (F := T ⋙ Triangle.π₁) φ.hom₁ W).op ∧
      ComposableArrows.app' Ψ 4 =
        (preadditive_yoneda_comparison_map
          (F := T ⋙ Triangle.π₃) φ.hom₃ (W⟦(-1 : ℤ)⟧)).op := by
  -- Proof comment: after inverse rotation, the five-term row has the source-book order
  -- `A[1], C, B, A, C[-1]`; unfolding the `preadditiveYoneda` shifts identifies each vertical
  -- component with the corresponding stage-comparison map, now viewed in the opposite category.
  dsimp
  repeat' constructor
  all_goals
    simp [preadditive_yoneda_comparison_map, Functor.map_comp, Triangle.invRotate]

/-- Helper for Lemma 13.42.2: once the outer comparison maps are isomorphisms, the inverse-rotated
five-term `preadditiveYoneda` row and the abelian five-lemma force the middle comparison map to
be an isomorphism as well. -/
private theorem middle_preadditive_yoneda_comparison_isIso_of_triangle_morphism
    {T : SequentialInverseSystem (Triangle D)} {m : ℕ} {T' : Triangle D}
    (hT : ∀ n : ℕ, T.obj (op n) ∈ distTriang D) (hT' : T' ∈ distTriang D)
    (φ : T.obj (op m) ⟶ T')
    (hφ₁ : HasHomColimitComparison
      (T ⋙ Triangle.π₁) (CostructuredArrow.mk φ.hom₁))
    (hφ₃ : HasHomColimitComparison
      (T ⋙ Triangle.π₃) (CostructuredArrow.mk φ.hom₃)) :
    ∀ W : D, IsIso (preadditive_yoneda_comparison_map (F := T ⋙ Triangle.π₂) φ.hom₂ W) := by
  intro W
  classical
  let H : D ⥤ AddCommGrpCatᵒᵖ := (preadditiveYoneda.obj W).rightOp
  let R₁ : Triangle D := (T.obj (op m)).invRotate
  let R₂ : Triangle D := T'.invRotate
  have hR₁ : R₁ ∈ distTriang D := by
    -- Proof comment: inverse rotation puts the middle component into the centered slot while
    -- preserving distinguishedness.
    simpa [R₁] using inv_rot_of_distTriang (T.obj (op m)) (hT m)
  have hR₂ : R₂ ∈ distTriang D := by
    -- Proof comment: the same inverse-rotation step applies to the fixed target triangle.
    simpa [R₂] using inv_rot_of_distTriang T' hT'
  let ψ : R₁ ⟶ R₂ := (invRotate D).map φ
  let ψ₅ :
      H.homologySequenceComposableArrows₅ R₁ (0 : ℤ) 1 rfl ⟶
        H.homologySequenceComposableArrows₅ R₂ (0 : ℤ) 1 rfl :=
    ComposableArrows.homMk₅
      ((H.shift (0 : ℤ)).map ψ.hom₁) ((H.shift (0 : ℤ)).map ψ.hom₂)
      ((H.shift (0 : ℤ)).map ψ.hom₃) ((H.shift (1 : ℤ)).map ψ.hom₁)
      ((H.shift (1 : ℤ)).map ψ.hom₂) ((H.shift (1 : ℤ)).map ψ.hom₃)
      (by simpa [Functor.map_comp] using congrArg ((H.shift (0 : ℤ)).map) ψ.comm₁)
      (by simpa [Functor.map_comp] using congrArg ((H.shift (0 : ℤ)).map) ψ.comm₂)
      (by simpa using (H.homologySequenceδ_naturality R₁ R₂ ψ (0 : ℤ) 1 rfl).symm)
      (by simpa [Functor.map_comp] using congrArg ((H.shift (1 : ℤ)).map) ψ.comm₁)
      (by simpa [Functor.map_comp] using congrArg ((H.shift (1 : ℤ)).map) ψ.comm₂)
  let Ψ := δlastFunctor.map ψ₅
  let E₁ : ComposableArrows AddCommGrpCatᵒᵖ 4 :=
    (H.homologySequenceComposableArrows₅ R₁ (0 : ℤ) 1 rfl).δlast
  let E₂ : ComposableArrows AddCommGrpCatᵒᵖ 4 :=
    (H.homologySequenceComposableArrows₅ R₂ (0 : ℤ) 1 rfl).δlast
  have hE₁ : E₁.Exact := by
    -- Proof comment: this is the inverse-rotated centered five-term exact row on the source
    -- distinguished triangle.
    simpa [E₁] using (H.homologySequenceComposableArrows₅_exact R₁ hR₁ (0 : ℤ) 1 rfl).δlast
  have hE₂ : E₂.Exact := by
    -- Proof comment: the same five-term exactness statement holds for the target triangle.
    simpa [E₂] using (H.homologySequenceComposableArrows₅_exact R₂ hR₂ (0 : ℤ) 1 rfl).δlast
  rcases inverse_rotated_preadditive_yoneda_slot_maps (T := T) (m := m) (T' := T') φ W with
    ⟨h₀map, h₁map, h₂map, h₃map, h₄map⟩
  have h₀iso : IsIso (ComposableArrows.app' Ψ 0) := by
    -- Proof comment: slot `0` is the `A`-comparison one degree higher, so `hφ₁` applies at
    -- `W⟦(1 : ℤ)⟧`.
    rw [h₀map]
    letI :
        IsIso
          (preadditive_yoneda_comparison_map
            (F := T ⋙ Triangle.π₁) φ.hom₁ (W⟦(1 : ℤ)⟧)) :=
      (preadditive_yoneda_comparison_isIso_iff_hasHomColimitComparison
        (F := T ⋙ Triangle.π₁) φ.hom₁).1 hφ₁ (W⟦(1 : ℤ)⟧)
    infer_instance
  have h₁iso : IsIso (ComposableArrows.app' Ψ 1) := by
    -- Proof comment: slot `1` is the comparison map on the third term at the test object `W`.
    rw [h₁map]
    letI :
        IsIso
          (preadditive_yoneda_comparison_map
            (F := T ⋙ Triangle.π₃) φ.hom₃ W) :=
      (preadditive_yoneda_comparison_isIso_iff_hasHomColimitComparison
        (F := T ⋙ Triangle.π₃) φ.hom₃).1 hφ₃ W
    infer_instance
  have h₃iso : IsIso (ComposableArrows.app' Ψ 3) := by
    -- Proof comment: slot `3` is the unshifted first-term comparison.
    rw [h₃map]
    letI :
        IsIso
          (preadditive_yoneda_comparison_map
            (F := T ⋙ Triangle.π₁) φ.hom₁ W) :=
      (preadditive_yoneda_comparison_isIso_iff_hasHomColimitComparison
        (F := T ⋙ Triangle.π₁) φ.hom₁).1 hφ₁ W
    infer_instance
  have h₄iso : IsIso (ComposableArrows.app' Ψ 4) := by
    -- Proof comment: slot `4` is the third-term comparison at `W⟦(-1 : ℤ)⟧`.
    rw [h₄map]
    letI :
        IsIso
          (preadditive_yoneda_comparison_map
            (F := T ⋙ Triangle.π₃) φ.hom₃ (W⟦(-1 : ℤ)⟧)) :=
      (preadditive_yoneda_comparison_isIso_iff_hasHomColimitComparison
        (F := T ⋙ Triangle.π₃) φ.hom₃).1 hφ₃ (W⟦(-1 : ℤ)⟧)
    infer_instance
  have h₀epi : Epi (ComposableArrows.app' Ψ 0) := by
    letI : IsIso (ComposableArrows.app' Ψ 0) := h₀iso
    infer_instance
  have h₄mono : Mono (ComposableArrows.app' Ψ 4) := by
    letI : IsIso (ComposableArrows.app' Ψ 4) := h₄iso
    infer_instance
  have hmid : IsIso (ComposableArrows.app' Ψ 2) :=
    Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono hE₁ hE₂ Ψ h₀epi h₁iso h₃iso h₄mono
  -- Proof comment: slot `2` is the opposite of the additive comparison map for `φ.hom₂`, so
  -- the five-lemma conclusion reflects back across `op`.
  rw [h₂map] at hmid
  letI :
      IsIso ((preadditive_yoneda_comparison_map (F := T ⋙ Triangle.π₂) φ.hom₂ W).op) := hmid
  exact isIso_of_op (preadditive_yoneda_comparison_map (F := T ⋙ Triangle.π₂) φ.hom₂ W)

private theorem middle_hasHomColimitComparison_of_triangle_morphism
    {T : SequentialInverseSystem (Triangle D)} {m : ℕ} {T' : Triangle D}
    (hT : ∀ n : ℕ, T.obj (op n) ∈ distTriang D) (hT' : T' ∈ distTriang D)
    (φ : T.obj (op m) ⟶ T')
    (hφ₁ : HasHomColimitComparison
      (T ⋙ Triangle.π₁) (CostructuredArrow.mk φ.hom₁))
    (hφ₃ : HasHomColimitComparison
      (T ⋙ Triangle.π₃) (CostructuredArrow.mk φ.hom₃)) :
    HasHomColimitComparison
      (T ⋙ Triangle.π₂) (CostructuredArrow.mk φ.hom₂) := by
  intro W
  classical
  let R₁ : Triangle D := (T.obj (op m)).invRotate
  let R₂ : Triangle D := T'.invRotate
  have hR₁ : R₁ ∈ distTriang D := by
    -- Proof comment: inverse rotation moves the source triangle into the orientation where
    -- `Hom(-, W)` places the middle term in the central slot of the five-term exact row.
    simpa [R₁] using inv_rot_of_distTriang (T.obj (op m)) (hT m)
  have hR₂ : R₂ ∈ distTriang D := by
    -- Proof comment: the same inverse-rotation step applies to the fixed target triangle.
    simpa [R₂] using inv_rot_of_distTriang T' hT'
  let ψ : R₁ ⟶ R₂ := (invRotate D).map φ
  -- Route correction: the unresolved step is no longer the outer tail decomposition. The only
  -- remaining work is to compare the inverse-rotated five-term `Hom(-, W)` rows through `ψ`,
  -- identify slots `0,1,3,4` with the outer comparison maps for `W⟦(-1 : ℤ)⟧`, `W`, and
  -- `W⟦(1 : ℤ)⟧`, and then apply `Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono`.
  --
  -- TODO: bridge the additive colimit of `F.op ⋙ preadditiveYoneda.obj W` to the Chapter 4
  -- `uliftYoneda` colimit, then normalize the inverse-rotated five-term row so that its slot-2
  -- vertical map is `preadditive_yoneda_comparison_map (F := T ⋙ Triangle.π₂) φ.hom₂ W`.
  have _hψ : R₁ ⟶ R₂ := ψ
  have _hR₁ : R₁ ∈ distTriang D := hR₁
  have _hR₂ : R₂ ∈ distTriang D := hR₂
  have _hφ₁ : HasHomColimitComparison
      (T ⋙ Triangle.π₁) (CostructuredArrow.mk φ.hom₁) := hφ₁
  have _hφ₃ : HasHomColimitComparison
      (T ⋙ Triangle.π₃) (CostructuredArrow.mk φ.hom₃) := hφ₃
  -- Proof comment: the additive-side five-lemma helper gives pointwise `IsIso` on the
  -- `preadditiveYoneda` comparison map, and the Chapter 4 owner bridge turns that back into the
  -- requested `HasHomColimitComparison` statement.
  exact
    (preadditive_yoneda_comparison_isIso_iff_hasHomColimitComparison
      (F := T ⋙ Triangle.π₂) φ.hom₂).2
      (middle_preadditive_yoneda_comparison_isIso_of_triangle_morphism
        (T := T) (m := m) (T' := T') hT hT' φ hφ₁ hφ₃)

-- Proof sketch: first rewrite the outer systems using Lemma 13.42.1 so that, on a tail, their
-- terms split as fixed summands plus essentially zero complements. The connecting morphisms on the
-- fixed summands define a single map `C ⟶ A⟦1⟧`; choose a distinguished triangle on that map, then
-- use `TR3` to compare one stage with it. Applying the homological functors `Hom(-, D)` shows that
-- the three components of that stage map corepresent the original inverse systems, so in
-- particular the three projected systems have fixed pro-object values given by the components of
-- `T'`, so the middle term system is essentially constant as well.
/-- Lemma 13.42.2, source-facing form: for a sequential inverse system of distinguished triangles
in a triangulated category, and in fact already in a pretriangulated category, if the first and
third term systems are essentially constant, then after some positive stage the system admits a
fixed distinguished triangle together with a morphism of distinguished triangles from that stage,
whose three components satisfy the stage-map comparison criterion of Lemma `4.22.10`.

The owner-level pro-object-value and essential-constancy consequences are recorded below as thin
companions. -/
@[stacks 0G3A]
theorem essentiallyConstant_middle_and_tail_value_triangle_of_essentiallyConstant_outer_terms
    {T : SequentialInverseSystem (Triangle D)} (hT : ∀ n : ℕ, T.obj (op n) ∈ distTriang D)
    (h₁ : IsEssentiallyConstantCofilteredDiagram (T ⋙ Triangle.π₁))
    (h₃ : IsEssentiallyConstantCofilteredDiagram (T ⋙ Triangle.π₃)) :
    ∃ (T' : Triangle D) (n : ℕ),
      T' ∈ distTriang D ∧
        ∃ φ : T.obj (op (n + 1)) ⟶ T',
          HasHomColimitComparison
            (T ⋙ Triangle.π₁)
            (CostructuredArrow.mk φ.hom₁) ∧
          HasHomColimitComparison
            (T ⋙ Triangle.π₂)
            (CostructuredArrow.mk φ.hom₂) ∧
          HasHomColimitComparison
            (T ⋙ Triangle.π₃)
            (CostructuredArrow.mk φ.hom₃) := by
  -- Route correction: the source proof must first identify a stable connecting morphism on a
  -- common tail of the outer direct-sum decompositions, then complete that outer square by TR3.
  have h₁tail :
      HasTailDirectSumDecomposition
        (((CategoryTheory.orderDualEquivalence ℕ).functor) ⋙ (T ⋙ Triangle.π₁)) := by
    -- Proof comment: this is the first outer-system instance of the reindex-then-split step.
    exact hasTailDirectSumDecomposition_of_essentiallyConstant_sequential h₁
  have h₃tail :
      HasTailDirectSumDecomposition
        (((CategoryTheory.orderDualEquivalence ℕ).functor) ⋙ (T ⋙ Triangle.π₃)) := by
    -- Proof comment: the same tail decomposition is available for the third term system.
    exact hasTailDirectSumDecomposition_of_essentiallyConstant_sequential h₃
  rcases h₁tail with ⟨N₁, A, Z₁, e₁, hzero₁⟩
  rcases h₃tail with ⟨N₃, C, Z₃, e₃, hzero₃⟩
  let m₀ : ℕ := max N₁ N₃ + 1
  have hm₀₁ : N₁ ≤ m₀ := by
    exact Nat.le_trans (Nat.le_max_left N₁ N₃) (Nat.le_add_right (max N₁ N₃) 1)
  have hm₀₃ : N₃ ≤ m₀ := by
    exact Nat.le_trans (Nat.le_max_right N₁ N₃) (Nat.le_add_right (max N₁ N₃) 1)
  rcases zero_kill_stage_of_eventually_zero_tail (Z := Z₃) hzero₃ hm₀₃ with
    ⟨n, hm₀n, hzero₃_stage⟩
  -- Proof comment: the proof is now aligned with the source's first real move. We have a common
  -- base stage `m₀`, the raw tail decompositions on both outer systems, and a later positive stage
  -- `n + 1` where the third complementary transition back to `m₀` vanishes.
  let a : (T.obj (op (n + 1))).obj₁ ⟶ A :=
    (e₁.app ⟨n + 1, Nat.le_trans hm₀₁ hm₀n⟩).hom ≫ biprod.fst
  let c : (T.obj (op (n + 1))).obj₃ ⟶ C :=
    (e₃.app ⟨n + 1, Nat.le_trans hm₀₃ hm₀n⟩).hom ≫ biprod.fst
  let baseProj₁ : (T.obj (op m₀)).obj₁ ⟶ A :=
    (e₁.app ⟨m₀, hm₀₁⟩).hom ≫ biprod.fst
  let baseSplit₃ : C ⟶ (T.obj (op m₀)).obj₃ :=
    biprod.inl ≫ (e₃.app ⟨m₀, hm₀₃⟩).inv
  let δ : C ⟶ A⟦(1 : ℤ)⟧ :=
    baseSplit₃ ≫ (T.obj (op m₀)).mor₃ ≫ baseProj₁⟦(1 : ℤ)⟧'
  obtain ⟨B, f, g, hT'⟩ := Pretriangulated.distinguished_cocone_triangle₂ δ
  let T' : Triangle D := Triangle.mk f g δ
  have hcomm : (T.obj (op (n + 1))).mor₃ ≫ a⟦(1 : ℤ)⟧' = c ≫ δ := by
    -- Proof comment: the later-stage outer square is exactly the `C`-summand identity from the
    -- chosen base stage, with the complementary `Z₃`-summand killed by `hzero₃_stage`.
    simpa [a, c, baseProj₁, baseSplit₃, δ] using
      connecting_square_of_outer_tail_splits
        (T := T) e₁ e₃ hm₀₁ hm₀₃
        (Nat.le_trans hm₀₁ hm₀n) (Nat.le_trans hm₀₃ hm₀n) hm₀n hzero₃_stage
  obtain ⟨b, hb₁, hb₂⟩ :=
    complete_distinguished_triangle_morphism₂
      (T.obj (op (n + 1))) T' (hT (n + 1)) hT' a c hcomm
  let φ : T.obj (op (n + 1)) ⟶ T' := Triangle.homMk _ _ a b c hb₁ hb₂ hcomm
  refine ⟨T', n, ?_, φ, ?_, ?_, ?_⟩
  · simpa [T'] using hT'
  · -- Proof comment: the first component of `φ` is exactly the stage projection to the fixed
    -- outer summand supplied by the first tail direct-sum decomposition.
    simpa [φ, a] using
      has_hom_colimit_comparison_of_stage_projection_from_tail_split
        (F := T ⋙ Triangle.π₁) e₁ hzero₁ (Nat.le_trans hm₀₁ hm₀n)
  · -- Proof comment: the middle component is the only non-tail-splitting step. It is delegated
    -- to the inverse-rotated five-term `Hom(-, W)` comparison helper extracted above.
    exact
      middle_hasHomColimitComparison_of_triangle_morphism
        (T := T) (m := n + 1) (T' := T') hT (by simpa [T'] using hT') φ
        (by
          simpa [φ, a] using
            has_hom_colimit_comparison_of_stage_projection_from_tail_split
              (F := T ⋙ Triangle.π₁) e₁ hzero₁ (Nat.le_trans hm₀₁ hm₀n))
        (by
          simpa [φ, c] using
            has_hom_colimit_comparison_of_stage_projection_from_tail_split
              (F := T ⋙ Triangle.π₃) e₃ hzero₃ (Nat.le_trans hm₀₃ hm₀n))
  · -- Proof comment: the third component of `φ` is the analogous stage projection on the third
    -- outer system, so the same tail-splitting comparison lemma applies verbatim.
    simpa [φ, c] using
      has_hom_colimit_comparison_of_stage_projection_from_tail_split
        (F := T ⋙ Triangle.π₃) e₃ hzero₃ (Nat.le_trans hm₀₃ hm₀n)

/-- Owner-level companion to Lemma 13.42.2: the fixed distinguished triangle produced there has
vertices corepresenting the three projected inverse systems. -/
theorem exists_proObjectValue_triangle_of_essentiallyConstant_outer_terms
    {T : SequentialInverseSystem (Triangle D)} (hT : ∀ n : ℕ, T.obj (op n) ∈ distTriang D)
    (h₁ : IsEssentiallyConstantCofilteredDiagram (T ⋙ Triangle.π₁))
    (h₃ : IsEssentiallyConstantCofilteredDiagram (T ⋙ Triangle.π₃)) :
    ∃ T' : Triangle D,
      T' ∈ distTriang D ∧
        HasProObjectValue (T ⋙ Triangle.π₁) T'.obj₁ ∧
        HasProObjectValue (T ⋙ Triangle.π₂) T'.obj₂ ∧
        HasProObjectValue (T ⋙ Triangle.π₃) T'.obj₃ := by
  -- Proof comment: unpack the source-facing stage-map theorem and convert each Hom-colimit
  -- comparison component into the owner predicate `HasProObjectValue`.
  rcases essentiallyConstant_middle_and_tail_value_triangle_of_essentiallyConstant_outer_terms
      (hT := hT) h₁ h₃ with
    ⟨T', n, hT', φ, hφ₁, hφ₂, hφ₃⟩
  refine ⟨T', hT', ?_, ?_, ?_⟩
  · -- The first vertex is corepresented by the first component of the stage map.
    exact
      (hasProObjectValue_iff_exists_stageMap_homColimitComparison (T ⋙ Triangle.π₁) T'.obj₁).2
        ⟨CostructuredArrow.mk φ.hom₁, hφ₁⟩
  · -- The middle vertex is corepresented by the middle component of the same stage map.
    exact
      (hasProObjectValue_iff_exists_stageMap_homColimitComparison (T ⋙ Triangle.π₂) T'.obj₂).2
        ⟨CostructuredArrow.mk φ.hom₂, hφ₂⟩
  · -- The third vertex is corepresented by the third component of the same stage map.
    exact
      (hasProObjectValue_iff_exists_stageMap_homColimitComparison (T ⋙ Triangle.π₃) T'.obj₃).2
        ⟨CostructuredArrow.mk φ.hom₃, hφ₃⟩

/-- Owner-level consequence of Lemma 13.42.2: if the outer terms of a sequential inverse system
of distinguished triangles are essentially constant, then so is the middle term system. -/
theorem essentiallyConstant_middle_of_essentiallyConstant_outer_terms
    {T : SequentialInverseSystem (Triangle D)} (hT : ∀ n : ℕ, T.obj (op n) ∈ distTriang D)
    (h₁ : IsEssentiallyConstantCofilteredDiagram (T ⋙ Triangle.π₁))
    (h₃ : IsEssentiallyConstantCofilteredDiagram (T ⋙ Triangle.π₃)) :
    IsEssentiallyConstantCofilteredDiagram (T ⋙ Triangle.π₂) := by
  -- Proof comment: the previous owner-level companion gives a fixed pro-object value for the
  -- middle system, and Chapter 4 turns that corepresentability into essential constancy.
  rcases exists_proObjectValue_triangle_of_essentiallyConstant_outer_terms
      (hT := hT) h₁ h₃ with
    ⟨T', _, _, h₂, _⟩
  rcases h₂ with ⟨e⟩
  exact (essentiallyConstant_proObject_characterizations (T ⋙ Triangle.π₂)).mp
    e.isCorepresentable

end

end CategoryTheory
