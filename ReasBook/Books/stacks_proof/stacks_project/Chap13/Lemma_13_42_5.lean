import Mathlib
import stacks_proof.stacks_project.Chap12.Definition_12_31_2
import stacks_proof.stacks_project.Chap13.Definition_13_11_3
import stacks_proof.stacks_project.Chap13.Lemma_13_42_3
import stacks_proof.stacks_project.Chap13.Lemma_13_42_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open DerivedCategory
open Opposite
open SequentialProObjectMorphismRep
open scoped CategoryTheory ZeroObject

universe w v u

namespace CategoryTheory

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [HasDerivedCategory.{w} 𝒜]

local notation "H" => DerivedCategory.homologyFunctor 𝒜

namespace SequentialProObjectMorphismRep

variable {C : Type u} [Category.{v} C]
variable {X Y : SequentialInverseSystem C}

/-- Helper for Lemma 13.42.5: an `Equivalent (s ≫ ofNatTrans α) (idRep Y)` witness produces the
explicit late-stage target-transition factorization used in the cone argument. -/
theorem equivalent_comp_ofNatTrans_idRep_target_transition_factorization
    (α : X ⟶ Y) (s : SequentialProObjectMorphismRep Y X)
    (hEq : Equivalent (compRep s (ofNatTrans α)) (idRep Y)) (n : ℕ) :
    ∃ (m : ℕ) (hnm : n ≤ m) (t : Y.obj (op m) ⟶ X.obj (op n)),
      Y.transitionMap hnm = t ≫ α.app (op n) := by
  rcases hEq with ⟨reindex', h₁, h₂, hmaps⟩
  refine ⟨reindex' n, h₂ n, Y.transitionMap (h₁ n) ≫ s.map n, ?_⟩
  have hcomp :
      (compRep s (ofNatTrans α)).map n = s.map n ≫ α.app (op n) := by
    rfl
  have hid : (idRep Y).map n = 𝟙 (Y.obj (op n)) := by
    rfl
  have hstage := hmaps n
  rw [hcomp, hid] at hstage
  -- Proof comment: after unfolding the common-refinement equation at stage `n`, the right-hand
  -- side is the identity map on `Y_n`, so the equation is exactly the desired factorization.
  simpa [SequentialInverseSystem.transitionMap, Category.assoc] using hstage.symm

/-- Helper for Lemma 13.42.5: an `Equivalent (ofNatTrans α ≫ s) (idRep X)` witness produces the
explicit late-stage source-transition factorization used in the connecting-map step. -/
theorem equivalent_comp_ofNatTrans_idRep_source_transition_factorization
    (α : X ⟶ Y) (s : SequentialProObjectMorphismRep Y X)
    (hEq : Equivalent (compRep (ofNatTrans α) s) (idRep X)) (n : ℕ) :
    ∃ (m : ℕ) (hnm : n ≤ m) (t : Y.obj (op m) ⟶ X.obj (op n)),
      X.transitionMap hnm = α.app (op m) ≫ t := by
  rcases hEq with ⟨reindex', h₁, h₂, hmaps⟩
  refine ⟨reindex' n, h₂ n, Y.transitionMap (h₁ n) ≫ s.map n, ?_⟩
  have hcomp :
      (compRep (ofNatTrans α) s).map n = α.app (op (s.reindex n)) ≫ s.map n := by
    rfl
  have hid : (idRep X).map n = 𝟙 (X.obj (op n)) := by
    rfl
  have hmaps' := hmaps n
  rw [hcomp, hid] at hmaps'
  have hnaturality :
      X.transitionMap (h₁ n) ≫ α.app (op (s.reindex n)) =
        α.app (op (reindex' n)) ≫ Y.transitionMap (h₁ n) := by
    -- Proof comment: this is the naturality square of `α` for the transition
    -- `A_{reindex' n} ⟶ A_{s.reindex n}` selected by the common refinement.
    exact α.naturality (homOfLE (h₁ n)).op
  -- Proof comment: rewrite the first factor by naturality of `α` so the transition map is taken
  -- in `Y` at the later stage `reindex' n`, then reassociate.
  calc
    X.transitionMap (h₂ n) =
        X.transitionMap (h₁ n) ≫ α.app (op (s.reindex n)) ≫ s.map n := by
          simpa [SequentialInverseSystem.transitionMap, Category.assoc] using hmaps'.symm
    _ = (X.transitionMap (h₁ n) ≫ α.app (op (s.reindex n))) ≫ s.map n := by
          simp [Category.assoc]
    _ = (α.app (op (reindex' n)) ≫ Y.transitionMap (h₁ n)) ≫ s.map n := by
          rw [hnaturality]
    _ = α.app (op (reindex' n)) ≫ (Y.transitionMap (h₁ n) ≫ s.map n) := by
          rfl

end SequentialProObjectMorphismRep

/- Domain-style sampling for Lemma 13.42.5:
- primary domain: morphisms of sequential inverse systems in `D(𝒜)`, controlled through the
  Chapter 4 owner `SequentialProObjectMorphismRep` and detected on cohomology towers.
- inspected owner-level declarations:
  `SequentialInverseSystem`,
  `SequentialProObjectMorphismRep.ofNatTrans`,
  `SequentialProObjectMorphismRep.IsProIsomorphism`,
  `SequentialProObjectMorphismRep.isProIsomorphism_toProObjectHom_app_bijective`,
  `DerivedCategory.IsGE`,
  `DerivedCategory.IsLE`,
  `essentiallyConstant_of_uniformly_bounded_essentiallyConstant_cohomology`,
  `triangleFirstToSecond_isProIsomorphism_of_proZero_third`.
- best owner abstraction: the source-facing result is that the sequential representative attached
  to `α` is a pro-isomorphism; the owner-level bridge to Hom-colimit bijectivity is already
  upstream, so it should not be recopied locally.
- primitive data: the sequential inverse systems `A` and `B`, the natural transformation `α`, the
  uniform cohomological bounds on both systems expressed by the canonical owners `IsGE` / `IsLE`,
  and the degreewise owner-level pro-isomorphism hypotheses on the cohomology towers `A ⋙ H^i`
  and `B ⋙ H^i` in the
  bounded window `Set.Icc a b`.
- derived API: `(ofNatTrans α).IsProIsomorphism`; Hom-colimit bijectivity is derived from the
  upstream owner theorem `isProIsomorphism_toProObjectHom_app_bijective`.

Source/core/bridge triage:
- `source-facing`: the main theorem below, asserting that `α` induces a pro-isomorphism in
  `D(𝒜)`.
- `core/canonical`: `SequentialInverseSystem`, `SequentialProObjectMorphismRep`, and
  `.IsProIsomorphism`.
- `bridge/view`: the Hom-colimit evaluation map `.toProObjectHom.app X`, supplied upstream rather
  than by a second local wrapper theorem. -/

-- Proof sketch: choose a compatible inverse system of distinguished triangles extending the maps
-- `α.app (op n) : A.obj (op n) ⟶ B.obj (op n)`. The boundedness assumptions and the degreewise
-- pro-isomorphism
-- hypothesis imply, by Lemma `13.42.3`, that the cone system has pro-zero cohomology and hence is
-- pro-zero in `D(𝒜)`; outside `[a, b]` the cone cohomology towers are already zero by the uniform
-- bounds. Then Lemma `13.42.4` gives a pro-isomorphism for those triangles, and the owner-level
-- bridge `SequentialProObjectMorphismRep.isProIsomorphism_toProObjectHom_app_bijective` turns
-- that into bijectivity of the induced Hom-colimit map for every test object.
/-- Helper for Lemma 13.42.5: if a natural transformation of sequential inverse systems is already
a pro-isomorphism, then every sufficiently late transition map in the target tower factors through
the stage map of the transformation. -/
theorem eventually_factors_target_transition_of_ofNatTrans_isProIsomorphism
    {C : Type u} [Category.{v} C]
    {X Y : SequentialInverseSystem C} (α : X ⟶ Y)
    (hα : (ofNatTrans α).IsProIsomorphism) (n : ℕ) :
    ∃ (m : ℕ) (hnm : n ≤ m) (t : Y.obj (op m) ⟶ X.obj (op n)),
      Y.transitionMap hnm = t ≫ α.app (op n) := by
  rcases hα with ⟨s, -, hs⟩
  -- Proof comment: the target-side half of the pro-isomorphism witness is exactly the normalized
  -- common-refinement statement proved in the owner namespace above.
  exact
    SequentialProObjectMorphismRep.equivalent_comp_ofNatTrans_idRep_target_transition_factorization
      α s hs n

/-- Helper for Lemma 13.42.5: if a natural transformation of sequential inverse systems is already
a pro-isomorphism, then every sufficiently late transition map in the source tower factors through
the later stage map of the transformation. -/
theorem eventually_factors_source_transition_of_ofNatTrans_isProIsomorphism
    {C : Type u} [Category.{v} C]
    {X Y : SequentialInverseSystem C} (α : X ⟶ Y)
    (hα : (ofNatTrans α).IsProIsomorphism) (n : ℕ) :
    ∃ (m : ℕ) (hnm : n ≤ m) (t : Y.obj (op m) ⟶ X.obj (op n)),
      X.transitionMap hnm = α.app (op m) ≫ t := by
  rcases hα with ⟨s, hs, -⟩
  -- Proof comment: the source-side half of the pro-isomorphism witness becomes the claimed
  -- factorization after one naturality rewrite, already packaged by the owner-level helper.
  exact
    SequentialProObjectMorphismRep.equivalent_comp_ofNatTrans_idRep_source_transition_factorization
      α s hs n

/-- Helper for Lemma 13.42.5: the chosen third object in a distinguished triangle extending the
stage map `α_n`. -/
noncomputable def cone_triangle_stage_obj₃
    {A B : SequentialInverseSystem (D(𝒜))} (α : A ⟶ B) (n : ℕ) :
    D(𝒜) :=
  Classical.choose (distinguished_cocone_triangle (α.app (op n)))

/-- Helper for Lemma 13.42.5: the chosen second morphism in a distinguished triangle extending the
stage map `α_n`. -/
noncomputable def cone_triangle_stage_mor₂
    {A B : SequentialInverseSystem (D(𝒜))} (α : A ⟶ B) (n : ℕ) :
    B.obj (op n) ⟶ cone_triangle_stage_obj₃ (𝒜 := 𝒜) α n :=
  Classical.choose (Classical.choose_spec (distinguished_cocone_triangle (α.app (op n))))

/-- Helper for Lemma 13.42.5: the chosen connecting morphism in a distinguished triangle
extending the stage map `α_n`. -/
noncomputable def cone_triangle_stage_mor₃
    {A B : SequentialInverseSystem (D(𝒜))} (α : A ⟶ B) (n : ℕ) :
    cone_triangle_stage_obj₃ (𝒜 := 𝒜) α n ⟶ A.obj (op n)⟦(1 : ℤ)⟧ :=
  Classical.choose
    (Classical.choose_spec (Classical.choose_spec
      (distinguished_cocone_triangle (α.app (op n)))))

/-- Helper for Lemma 13.42.5: the chosen distinguished triangle on the stage morphism
`α.app (op n)`. -/
noncomputable def cone_triangle_stage
    {A B : SequentialInverseSystem (D(𝒜))} (α : A ⟶ B) (n : ℕ) :
    Triangle (D(𝒜)) :=
  Triangle.mk
    (α.app (op n))
    (cone_triangle_stage_mor₂ (𝒜 := 𝒜) α n)
    (cone_triangle_stage_mor₃ (𝒜 := 𝒜) α n)

/-- Helper for Lemma 13.42.5: the chosen stage triangle has first morphism exactly
`α.app (op n)`. -/
@[simp] theorem cone_triangle_stage_mor₁
    {A B : SequentialInverseSystem (D(𝒜))} (α : A ⟶ B) (n : ℕ) :
    (cone_triangle_stage (𝒜 := 𝒜) α n).mor₁ = α.app (op n) := by
  rfl

/-- Helper for Lemma 13.42.5: the chosen stage triangle extending `α_n` is distinguished. -/
theorem cone_triangle_stage_distinguished
    {A B : SequentialInverseSystem (D(𝒜))} (α : A ⟶ B) (n : ℕ) :
    cone_triangle_stage (𝒜 := 𝒜) α n ∈ distTriang (D(𝒜)) := by
  -- Proof comment: `cone_triangle_stage` is built by selecting the canonical TR1 witness
  -- `distinguished_cocone_triangle (α_n)`, so the final component of the nested `choose_spec`
  -- data is exactly the desired distinguishedness statement.
  simpa [cone_triangle_stage, cone_triangle_stage_obj₃, cone_triangle_stage_mor₂,
    cone_triangle_stage_mor₃] using
    (Classical.choose_spec
      (Classical.choose_spec
        (Classical.choose_spec
          (distinguished_cocone_triangle (α.app (op n))))))

/-- Helper for Lemma 13.42.5: the naturality square of `α` extends to a morphism between the
chosen distinguished triangles at consecutive stages. -/
theorem exists_cone_triangle_stage_successor_morphism
    {A B : SequentialInverseSystem (D(𝒜))} (α : A ⟶ B) (n : ℕ) :
    ∃ φ : cone_triangle_stage (𝒜 := 𝒜) α (n + 1) ⟶ cone_triangle_stage (𝒜 := 𝒜) α n,
      φ.hom₁ = A.stepMap n ∧ φ.hom₂ = B.stepMap n := by
  have hdist_succ :
      cone_triangle_stage (𝒜 := 𝒜) α (n + 1) ∈ distTriang (D(𝒜)) :=
    cone_triangle_stage_distinguished (𝒜 := 𝒜) α (n + 1)
  have hdist_curr :
      cone_triangle_stage (𝒜 := 𝒜) α n ∈ distTriang (D(𝒜)) :=
    cone_triangle_stage_distinguished (𝒜 := 𝒜) α n
  have hcomm :
      (cone_triangle_stage (𝒜 := 𝒜) α (n + 1)).mor₁ ≫ B.stepMap n =
        A.stepMap n ≫ (cone_triangle_stage (𝒜 := 𝒜) α n).mor₁ := by
    -- Proof comment: after rewriting the first morphisms of the chosen triangles, the required
    -- square is exactly the naturality square of `α` for the successor map.
    simpa [cone_triangle_stage_mor₁, SequentialInverseSystem.stepMap,
      SequentialInverseSystem.transitionMap] using
      (α.naturality (homOfLE (Nat.le_succ n)).op).symm
  obtain ⟨c, hc₂, hc₃⟩ :=
    complete_distinguished_triangle_morphism
      (cone_triangle_stage (𝒜 := 𝒜) α (n + 1))
      (cone_triangle_stage (𝒜 := 𝒜) α n)
      hdist_succ hdist_curr (A.stepMap n) (B.stepMap n) hcomm
  -- Proof comment: TR3 supplies the third component completing the morphism of distinguished
  -- triangles; the first two components are the transition maps of `A` and `B`.
  refine ⟨Triangle.homMk _ _ (A.stepMap n) (B.stepMap n) c hcomm hc₂ hc₃, rfl, rfl⟩

/-- Helper for Lemma 13.42.5: the chosen successor morphism between the cone triangles. -/
noncomputable def cone_triangle_stage_successor_morphism
    {A B : SequentialInverseSystem (D(𝒜))} (α : A ⟶ B) (n : ℕ) :
    cone_triangle_stage (𝒜 := 𝒜) α (n + 1) ⟶ cone_triangle_stage (𝒜 := 𝒜) α n :=
  Classical.choose (exists_cone_triangle_stage_successor_morphism (𝒜 := 𝒜) α n)

/-- Helper for Lemma 13.42.5: the first component of the chosen successor morphism is the
transition map in `A`. -/
@[simp] theorem cone_triangle_stage_successor_morphism_hom₁
    {A B : SequentialInverseSystem (D(𝒜))} (α : A ⟶ B) (n : ℕ) :
    (cone_triangle_stage_successor_morphism (𝒜 := 𝒜) α n).hom₁ = A.stepMap n :=
  (Classical.choose_spec
    (exists_cone_triangle_stage_successor_morphism (𝒜 := 𝒜) α n)).1

/-- Helper for Lemma 13.42.5: the second component of the chosen successor morphism is the
transition map in `B`. -/
@[simp] theorem cone_triangle_stage_successor_morphism_hom₂
    {A B : SequentialInverseSystem (D(𝒜))} (α : A ⟶ B) (n : ℕ) :
    (cone_triangle_stage_successor_morphism (𝒜 := 𝒜) α n).hom₂ = B.stepMap n :=
  (Classical.choose_spec
    (exists_cone_triangle_stage_successor_morphism (𝒜 := 𝒜) α n)).2

/-- Helper for Lemma 13.42.5: the inverse system of distinguished triangles obtained by choosing
cones on each stage map of `α` and completing the successor squares by TR3. -/
noncomputable def coneTriangleSystem
    {A B : SequentialInverseSystem (D(𝒜))} (α : A ⟶ B) :
    SequentialInverseSystem (Triangle (D(𝒜))) :=
  Functor.ofOpSequence (cone_triangle_stage_successor_morphism (𝒜 := 𝒜) α)

/-- Helper for Lemma 13.42.5: the `OrderDual ℕ`-indexed cone tower obtained by reindexing the
canonical sequential cone system along `orderDualEquivalence ℕ`. -/
abbrev coneTriangleOrderDualSystem
    {A B : SequentialInverseSystem (D(𝒜))} (α : A ⟶ B) :
    OrderDual ℕ ⥤ Triangle (D(𝒜)) :=
  ((CategoryTheory.orderDualEquivalence ℕ).functor) ⋙ coneTriangleSystem (𝒜 := 𝒜) α

/-- Helper for Lemma 13.42.5: every stage of the chosen cone tower is distinguished. -/
theorem cone_triangle_system_distinguished
    {A B : SequentialInverseSystem (D(𝒜))} (α : A ⟶ B) (n : ℕ) :
    (coneTriangleSystem (𝒜 := 𝒜) α).obj (op n) ∈ distTriang (D(𝒜)) := by
  -- Proof comment: `coneTriangleSystem` was assembled from the already distinguished stage
  -- triangles, so its `n`-th object is exactly `cone_triangle_stage α n`.
  simpa [coneTriangleSystem] using
    cone_triangle_stage_distinguished (𝒜 := 𝒜) α n

/-- Helper for Lemma 13.42.5: outside the cohomological window `[a - 1, b]`, the third object in
the chosen cone triangle has zero cohomology. -/
theorem cone_triangle_system_third_isZero_outside_window
    {A B : SequentialInverseSystem (D(𝒜))} (α : A ⟶ B) (a b p : ℤ)
    (hAGE : ∀ n : ℕ, (A.obj (op n)).IsGE a)
    (hALE : ∀ n : ℕ, (A.obj (op n)).IsLE b)
    (hBGE : ∀ n : ℕ, (B.obj (op n)).IsGE a)
    (hBLE : ∀ n : ℕ, (B.obj (op n)).IsLE b)
    (n : ℕ) (hp : p < a - 1 ∨ b < p) :
    IsZero ((H^p).obj ((coneTriangleSystem (𝒜 := 𝒜) α).obj (op n)).obj₃) := by
  let Tn : Triangle (D(𝒜)) := cone_triangle_stage (𝒜 := 𝒜) α n
  have hTn : Tn ∈ distTriang (D(𝒜)) := by
    -- Proof comment: the `n`-th stage of the cone tower is exactly the distinguished triangle
    -- selected on `α.app (op n)`.
    simpa [Tn] using cone_triangle_stage_distinguished (𝒜 := 𝒜) α n
  have hA_zero : IsZero ((H^p).obj Tn.obj₁) := by
    -- Proof comment: the first vertex is `A_n`, whose cohomology vanishes below `a` and above
    -- `b`; the hypothesis `hp` lies strictly outside the larger cone window.
    dsimp [Tn, cone_triangle_stage]
    rcases hp with hp | hp
    · exact isZero_of_isGE (A.obj (op n)) a p (by omega)
    · exact isZero_of_isLE (A.obj (op n)) b p (by omega)
  have hB_zero : IsZero ((H^p).obj Tn.obj₂) := by
    -- Proof comment: the second vertex is `B_n`, with the same boundedness hypothesis.
    dsimp [Tn, cone_triangle_stage]
    rcases hp with hp | hp
    · exact isZero_of_isGE (B.obj (op n)) a p (by omega)
    · exact isZero_of_isLE (B.obj (op n)) b p (by omega)
  have hA_succ_zero : IsZero ((H^(p + 1)).obj Tn.obj₁) := by
    -- Proof comment: the connecting morphism lands in `H^{p+1}(A_n)`, which is still outside
    -- the original `[a, b]` window when `p` is outside `[a - 1, b]`.
    dsimp [Tn, cone_triangle_stage]
    rcases hp with hp | hp
    · exact isZero_of_isGE (A.obj (op n)) a (p + 1) (by omega)
    · exact isZero_of_isLE (A.obj (op n)) b (p + 1) (by omega)
  have hmor₁_zero : (H^p).map Tn.mor₁ = 0 := by
    -- Proof comment: the source of the first cohomology map is already zero.
    exact hA_zero.eq_of_src _ _
  have hδ_zero : HomologySequence.δ Tn p (p + 1) rfl = 0 := by
    -- Proof comment: the connecting morphism lands in the zero object `H^{p+1}(A_n)`.
    exact hA_succ_zero.eq_of_tgt _ _
  letI : Epi ((H^p).map Tn.mor₂) :=
    (HomologySequence.epi_homologyMap_mor₂_iff Tn hTn p (p + 1) rfl).2 hδ_zero
  letI : Mono ((H^p).map Tn.mor₂) :=
    (HomologySequence.mono_homologyMap_mor₂_iff Tn hTn p).2 hmor₁_zero
  -- Proof comment: exactness upgrades the middle cohomology map to an isomorphism, so the
  -- third cohomology term is zero because the second one already is.
  simpa [Tn, coneTriangleSystem] using
    (IsZero.of_iso hB_zero (asIso ((H^p).map Tn.mor₂)))

/-- Helper for Lemma 13.42.5: the third vertex of the chosen cone tower is uniformly bounded in
degrees `[a - 1, b]`. -/
theorem cone_triangle_system_third_bounds
    {A B : SequentialInverseSystem (D(𝒜))} (α : A ⟶ B) (a b : ℤ)
    (hAGE : ∀ n : ℕ, (A.obj (op n)).IsGE a)
    (hALE : ∀ n : ℕ, (A.obj (op n)).IsLE b)
    (hBGE : ∀ n : ℕ, (B.obj (op n)).IsGE a)
    (hBLE : ∀ n : ℕ, (B.obj (op n)).IsLE b)
    (n : ℕ) :
    (((coneTriangleSystem (𝒜 := 𝒜) α).obj (op n)).obj₃).IsGE (a - 1) ∧
      (((coneTriangleSystem (𝒜 := 𝒜) α).obj (op n)).obj₃).IsLE b := by
  constructor
  · -- Proof comment: `IsGE (a - 1)` is the canonical reformulation of low-degree vanishing.
    rw [DerivedCategory.isGE_iff]
    intro p hp
    exact
      cone_triangle_system_third_isZero_outside_window (𝒜 := 𝒜) α a b p
        hAGE hALE hBGE hBLE n (Or.inl hp)
  · -- Proof comment: `IsLE b` is the canonical reformulation of high-degree vanishing.
    rw [DerivedCategory.isLE_iff]
    intro p hp
    exact
      cone_triangle_system_third_isZero_outside_window (𝒜 := 𝒜) α a b p
        hAGE hALE hBGE hBLE n (Or.inr hp)

/-- Helper for Lemma 13.42.5: after reindexing the sequential cone tower to the `OrderDual ℕ`
owner expected by Lemma 13.42.4, the first-to-second morphism still represents the original
inverse-system map `α`. -/
theorem ofOrderDualNatTrans_cone_triangle_first_to_second_eq_ofNatTrans
    {A B : SequentialInverseSystem (D(𝒜))} (α : A ⟶ B) :
    ofOrderDualNatTrans
        (Functor.whiskerLeft (coneTriangleOrderDualSystem (𝒜 := 𝒜) α) Triangle.π₁Toπ₂) =
      ofNatTrans α := by
  -- Proof comment: both representatives are built with identity reindexing, and after exposing
  -- the successor map of `coneTriangleSystem` the stage maps are literally the components
  -- `α.app (op n)`.
  rfl

/-- Helper for Lemma 13.42.5: the zero maps are compatible with the successor transition maps of
any sequential inverse system. -/
theorem zero_cone_compat
    {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasZeroObject C]
    (F : SequentialInverseSystem C) (n : ℕ) :
    (((Functor.const ℕᵒᵖ).obj (0 : C)).map (homOfLE (Nat.le_succ n)).op) ≫
        (0 : (0 : C) ⟶ F.obj (op n)) =
      (0 : (0 : C) ⟶ F.obj (op (n + 1))) ≫ F.stepMap n := by
  -- Proof comment: every composite starting from the zero morphism is zero, so the successor
  -- compatibility needed for `NatTrans.ofOpSequence` is automatic.
  simp [SequentialInverseSystem.stepMap]

/-- Helper for Lemma 13.42.5: the zero object defines the canonical zero cone over a sequential
inverse system. -/
noncomputable def zeroCone
    {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasZeroObject C]
    (F : SequentialInverseSystem C) : Cone F :=
  Cone.mk 0 <|
    NatTrans.ofOpSequence
      (fun n ↦ (0 : 0 ⟶ F.obj (op n)))
      (zero_cone_compat F)

/-- Helper for Lemma 13.42.5: each leg of the canonical zero cone is split mono. -/
noncomputable def zeroCone_leg_splitMono
    {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasZeroObject C]
    (F : SequentialInverseSystem C) (n : ℕ) :
    SplitMono ((zeroCone F).π.app (op n)) := by
  -- Proof comment: the distinguished leg is the zero morphism `0 ⟶ F_n`, and the retraction
  -- back to the zero object is again zero because `𝟙 0 = 0`.
  change SplitMono (0 : 0 ⟶ F.obj (op n))
  refine ⟨0, ?_⟩
  simp

/-- Helper for Lemma 13.42.5: if every transition map in a sequential inverse system is
eventually zero, then the canonical zero cone is essentially constant. -/
theorem zeroCone_isEssentiallyConstant_of_eventually_zero_transition
    {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasZeroObject C]
    (F : SequentialInverseSystem C)
    (hzero : ∀ n : ℕ, ∃ (m : ℕ) (hnm : n ≤ m), F.transitionMap hnm = 0) :
    IsEssentiallyConstantCofilteredCone (zeroCone F) := by
  rw [isEssentiallyConstantCofilteredCone_iff]
  refine ⟨op 0, zeroCone_leg_splitMono F 0, ?_⟩
  intro j
  rcases hzero j.unop with ⟨m, hjm, hmap⟩
  refine ⟨op m, (homOfLE (Nat.zero_le m)).op, (homOfLE hjm).op, ?_⟩
  -- Proof comment: the textbook eventual-vanishing hypothesis is exactly the factorization
  -- condition for the zero cone, because the right-hand side collapses to zero.
  simpa [zeroCone, SequentialInverseSystem.transitionMap] using hmap

/-- Helper for Lemma 13.42.5: eventual vanishing of transition maps forces the inverse system to
be essentially constant with value `0`. -/
theorem essentiallyConstant_of_eventually_zero_transition
    {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasZeroObject C]
    (F : SequentialInverseSystem C)
    (hzero : ∀ n : ℕ, ∃ (m : ℕ) (hnm : n ≤ m), F.transitionMap hnm = 0) :
    IsEssentiallyConstantCofilteredDiagram F := by
  -- Proof comment: package the canonical zero cone together with the eventual-zero factorization
  -- just proved.
  exact ⟨zeroCone F, zeroCone_isEssentiallyConstant_of_eventually_zero_transition F hzero⟩

/-- Helper for Lemma 13.42.5: eventual vanishing of transition maps gives pro-object value `0`. -/
theorem hasProObjectValue_zero_of_eventually_zero_transition
    {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasZeroObject C]
    (F : SequentialInverseSystem C)
    (hzero : ∀ n : ℕ, ∃ (m : ℕ) (hnm : n ≤ m), F.transitionMap hnm = 0) :
    HasProObjectValue F (0 : C) := by
  let c : LimitCone F :=
    ⟨zeroCone F, (zeroCone_isEssentiallyConstant_of_eventually_zero_transition F hzero).isLimit⟩
  have hc : IsEssentiallyConstantCofilteredCone c.cone := by
    -- Proof comment: `c` uses the canonical zero cone, so the previous essential-constancy
    -- witness applies without further transport.
    simpa [c] using
      zeroCone_isEssentiallyConstant_of_eventually_zero_transition F hzero
  -- Proof comment: once the zero cone is an essentially constant limit cone, Chapter 4 upgrades
  -- it to the fixed pro-object value statement.
  exact hasProObjectValue_of_essentiallyConstant_limitCone (M := F) c hc

/-- Helper for Lemma 13.42.5: transition maps in a sequential inverse system factor through every
intermediate stage. -/
theorem transitionMap_factor
    {C : Type u} [Category.{v} C] (F : SequentialInverseSystem C)
    {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) :
    F.transitionMap (Nat.le_trans hij hjk) =
      F.transitionMap hjk ≫ F.transitionMap hij := by
  -- Proof comment: in `ℕᵒᵖ`, the unique arrow `k ⟶ i` factors through every intermediate stage
  -- `j`, and `transitionMap` is `F.map` of that factorization.
  have hh :
      (homOfLE (Nat.le_trans hij hjk)).op =
        (homOfLE hjk).op ≫ (homOfLE hij).op := by
    subsingleton
  simpa [SequentialInverseSystem.transitionMap] using congrArg F.map hh

/-- Helper for Lemma 13.42.5: the first projection of the cone triangle system has the same
transition maps as the original inverse system `A`. -/
theorem cone_triangle_system_first_transitionMap
    {A B : SequentialInverseSystem (D(𝒜))} (α : A ⟶ B)
    {n m : ℕ} (hnm : n ≤ m) :
    ((coneTriangleSystem (𝒜 := 𝒜) α ⋙ Triangle.π₁).transitionMap hnm) =
      A.transitionMap hnm := by
  induction hnm with
  | refl =>
      simp [SequentialInverseSystem.transitionMap]
  | @step m h ih =>
      rw [transitionMap_factor (F := coneTriangleSystem (𝒜 := 𝒜) α ⋙ Triangle.π₁)
          h (Nat.le_succ m)]
      rw [transitionMap_factor (F := A) h (Nat.le_succ m)]
      rw [ih]
      -- Proof comment: the successor map of the cone tower was chosen so that its first
      -- component is exactly the successor map of `A`.
      simpa [coneTriangleSystem, SequentialInverseSystem.stepMap,
        SequentialInverseSystem.transitionMap, Functor.ofOpSequence_map_homOfLE_succ] using
        cone_triangle_stage_successor_morphism_hom₁ (𝒜 := 𝒜) α m

/-- Helper for Lemma 13.42.5: the second projection of the cone triangle system has the same
transition maps as the original inverse system `B`. -/
theorem cone_triangle_system_second_transitionMap
    {A B : SequentialInverseSystem (D(𝒜))} (α : A ⟶ B)
    {n m : ℕ} (hnm : n ≤ m) :
    ((coneTriangleSystem (𝒜 := 𝒜) α ⋙ Triangle.π₂).transitionMap hnm) =
      B.transitionMap hnm := by
  induction hnm with
  | refl =>
      simp [SequentialInverseSystem.transitionMap]
  | @step m h ih =>
      rw [transitionMap_factor (F := coneTriangleSystem (𝒜 := 𝒜) α ⋙ Triangle.π₂)
          h (Nat.le_succ m)]
      rw [transitionMap_factor (F := B) h (Nat.le_succ m)]
      rw [ih]
      -- Proof comment: the second component of each chosen successor morphism is the transition
      -- map in `B`, so the longer transition maps match by induction.
      simpa [coneTriangleSystem, SequentialInverseSystem.stepMap,
        SequentialInverseSystem.transitionMap, Functor.ofOpSequence_map_homOfLE_succ] using
        cone_triangle_stage_successor_morphism_hom₂ (𝒜 := 𝒜) α m

/-- Helper for Lemma 13.42.5: the middle cohomology map and the connecting map in the
five-term exact sequence compose to zero. -/
theorem homology_map_mor₂_comp_delta_zero
    (T : Triangle (D(𝒜))) (hT : T ∈ distTriang (D(𝒜))) (p : ℤ)
    :
    (H^p).map T.mor₂ ≫ HomologySequence.δ T p (p + 1) rfl = 0 := by
  -- Proof comment: the two displayed maps are consecutive arrows in the long exact sequence.
  simpa using
    (((H 0).homologySequenceComposableArrows₅_exact T hT p (p + 1) rfl).toIsComplex.zero 1)

/-- Helper for Lemma 13.42.5: the middle cohomology map and the connecting map form an exact
short complex in the five-term cohomology row of a distinguished triangle. -/
theorem homology_map_mor₂_delta_exact
    (T : Triangle (D(𝒜))) (hT : T ∈ distTriang (D(𝒜))) (p : ℤ) :
    (ShortComplex.mk
      ((H^p).map T.mor₂)
      (HomologySequence.δ T p (p + 1) rfl)
      (homology_map_mor₂_comp_delta_zero (𝒜 := 𝒜) T hT p)).Exact := by
  -- Proof comment: exactness at `H^p(T.obj₃)` is exactly the `i = 1` short-complex slice of the
  -- canonical five-term exact cohomology sequence.
  simpa [homology_map_mor₂_comp_delta_zero] using
    (((H 0).homologySequenceComposableArrows₅_exact T hT p (p + 1) rfl).exact 1)

/-- Helper for Lemma 13.42.5: any map into `H^p(T.obj₃)` killed by the connecting map composes
trivially with every morphism annihilating the image of `H^p(T.obj₂) ⟶ H^p(T.obj₃)`. -/
theorem homology_comp_zero_of_delta_zero_of_map_mor₂_comp_zero
    (T : Triangle (D(𝒜))) (hT : T ∈ distTriang (D(𝒜))) (p : ℤ)
    {W Y : 𝒜} (γ : W ⟶ (H^p).obj T.obj₃) (η : (H^p).obj T.obj₃ ⟶ Y)
    (hγ : γ ≫ HomologySequence.δ T p (p + 1) rfl = 0)
    (hη : (H^p).map T.mor₂ ≫ η = 0) :
    γ ≫ η = 0 := by
  -- Route correction: the source proof only needs the composite through stage `n` to vanish on
  -- `Ker(δ) = Im(β)`, not an explicit lift through `β`. The owner lemma `comp_eq_zero` records
  -- this exactness consequence directly and avoids a false factorization statement.
  exact
    (homology_map_mor₂_delta_exact (𝒜 := 𝒜) T hT p).comp_eq_zero hγ hη

/-- Helper for Lemma 13.42.5: the connecting morphism and the next cohomology map in a
distinguished triangle compose to zero. -/
theorem homology_delta_comp_map_mor₁_zero
    (T : Triangle (D(𝒜))) (hT : T ∈ distTriang (D(𝒜))) (p : ℤ) :
    HomologySequence.δ T p (p + 1) rfl ≫ (H^(p + 1)).map T.mor₁ = 0 := by
  -- Proof comment: these are the next two consecutive arrows in the same five-term exact row.
  simpa using
    (((H 0).homologySequenceComposableArrows₅_exact T hT p (p + 1) rfl).toIsComplex.zero 2)

/-- Helper for Lemma 13.42.5: outside the cone window `[a - 1, b]`, every cohomology transition
map in the third-vertex tower is already zero because the target object has zero cohomology. -/
theorem cone_cohomology_transition_zero_of_outside_window
    {A B : SequentialInverseSystem (D(𝒜))} (α : A ⟶ B) (a b p : ℤ)
    (hAGE : ∀ n : ℕ, (A.obj (op n)).IsGE a)
    (hALE : ∀ n : ℕ, (A.obj (op n)).IsLE b)
    (hBGE : ∀ n : ℕ, (B.obj (op n)).IsGE a)
    (hBLE : ∀ n : ℕ, (B.obj (op n)).IsLE b)
    {n k : ℕ} (hnk : n ≤ k) (hp : p < a - 1 ∨ b < p) :
    (((coneTriangleSystem (𝒜 := 𝒜) α ⋙ Triangle.π₃) ⋙ H^p).transitionMap hnk) = 0 := by
  let F : SequentialInverseSystem 𝒜 :=
    ((coneTriangleSystem (𝒜 := 𝒜) α ⋙ Triangle.π₃) ⋙ H^p)
  have hz : IsZero (F.obj (op n)) := by
    -- Proof comment: the target stage `n` is already zero in degree `p`, so every incoming map
    -- into it must vanish.
    simpa [F] using
      cone_triangle_system_third_isZero_outside_window (𝒜 := 𝒜) α a b p
        hAGE hALE hBGE hBLE n hp
  exact hz.eq_of_tgt _ _

/-- Helper for Lemma 13.42.5: inside the cohomological window `[a - 1, b]`, the textbook
`m`-then-`k` long-exact-sequence argument forces every cone cohomology tower to have eventually
zero transition maps. -/
theorem cone_cohomology_eventually_zero_transition_in_window
    {A B : SequentialInverseSystem (D(𝒜))} (α : A ⟶ B) (a b p : ℤ)
    (hAGE : ∀ n : ℕ, (A.obj (op n)).IsGE a)
    (hALE : ∀ n : ℕ, (A.obj (op n)).IsLE b)
    (hBGE : ∀ n : ℕ, (B.obj (op n)).IsGE a)
    (hBLE : ∀ n : ℕ, (B.obj (op n)).IsLE b)
    (hH : ∀ i ∈ Set.Icc a b,
      (ofNatTrans (Functor.whiskerRight α (H^i))).IsProIsomorphism)
    (hp : p ∈ Set.Icc (a - 1) b) (n : ℕ) :
    ∃ (k : ℕ) (hnk : n ≤ k),
      (((coneTriangleSystem (𝒜 := 𝒜) α ⋙ Triangle.π₃) ⋙ H^p).transitionMap hnk) = 0 := by
  -- TODO: finish the boundary-aware `m`-then-`k` long-exact-sequence argument on the cone tower.
  -- The proved frontier already includes the cone system, the identification of its first and
  -- second transition maps with those of `A` and `B`, the outside-window zero-transition lemma,
  -- and the exactness helpers `homology_comp_zero_of_delta_zero_of_map_mor₂_comp_zero` and
  -- `homology_delta_comp_map_mor₁_zero`. The remaining work is to package those ingredients into
  -- the three in-window cases `p = a - 1`, `a ≤ p < b`, and `p = b`.
  sorry

/-- Helper for Lemma 13.42.5: every cone cohomology tower has eventually zero transition maps,
combining the trivial outside-window vanishing with the in-window long-exact-sequence argument. -/
theorem cone_cohomology_eventually_zero_transition
    {A B : SequentialInverseSystem (D(𝒜))} (α : A ⟶ B) (a b p : ℤ)
    (hAGE : ∀ n : ℕ, (A.obj (op n)).IsGE a)
    (hALE : ∀ n : ℕ, (A.obj (op n)).IsLE b)
    (hBGE : ∀ n : ℕ, (B.obj (op n)).IsGE a)
    (hBLE : ∀ n : ℕ, (B.obj (op n)).IsLE b)
    (hH : ∀ i ∈ Set.Icc a b,
      (ofNatTrans (Functor.whiskerRight α (H^i))).IsProIsomorphism)
    (n : ℕ) :
    ∃ (k : ℕ) (hnk : n ≤ k),
      (((coneTriangleSystem (𝒜 := 𝒜) α ⋙ Triangle.π₃) ⋙ H^p).transitionMap hnk) = 0 := by
  by_cases hp : p ∈ Set.Icc (a - 1) b
  · exact
      cone_cohomology_eventually_zero_transition_in_window (𝒜 := 𝒜) α a b p
        hAGE hALE hBGE hBLE hH hp n
  · have houtside : p < a - 1 ∨ b < p := by
      by_cases hlt : p < a - 1
      · exact Or.inl hlt
      · right
        have hge : a - 1 ≤ p := by
          omega
        have hnot : ¬ p ≤ b := by
          intro hpb
          exact hp ⟨hge, hpb⟩
        omega
    refine ⟨n + 1, Nat.le_succ n, ?_⟩
    exact
      cone_cohomology_transition_zero_of_outside_window (𝒜 := 𝒜) α a b p
        hAGE hALE hBGE hBLE (Nat.le_succ n) houtside

/-- Helper for Lemma 13.42.5: a uniformly bounded inverse system in `D(\mathcal A)` whose
cohomology towers all have fixed pro-object value `0` must itself have fixed pro-object value
`0`. -/
theorem hasProObjectValue_zero_of_uniformly_bounded_zero_cohomology
    (F : SequentialInverseSystem (D(𝒜))) (l u : ℤ)
    (hGE : ∀ n : ℕ, (F.obj (op n)).IsGE l)
    (hLE : ∀ n : ℕ, (F.obj (op n)).IsLE u)
    (hH : ∀ i ∈ Set.Icc l u, HasProObjectValue (F ⋙ H^i) (0 : 𝒜)) :
    HasProObjectValue F (0 : D(𝒜)) := by
  have hEssential :
      ∀ i ∈ Set.Icc l u, IsEssentiallyConstantCofilteredDiagram (F ⋙ H^i) := by
    intro i hi
    rcases hH i hi with ⟨e⟩
    -- Proof comment: a fixed pro-object value is stronger than essential constancy, and the
    -- Chapter 4 characterization records exactly this implication.
    exact (essentiallyConstant_proObject_characterizations (F ⋙ H^i)).mp e.isCorepresentable
  rcases exists_proObjectValue_of_uniformly_bounded_essentiallyConstant_cohomology
      F l u hGE hLE hEssential with ⟨X, hX, hHX⟩
  have hOutside :
      ∀ i : ℤ, i ∉ Set.Icc l u → HasProObjectValue (F ⋙ H^i) (0 : 𝒜) := by
    intro i hi
    have houtside : i < l ∨ u < i := by
      by_cases hlt : i < l
      · exact Or.inl hlt
      · right
        have hli : l ≤ i := by omega
        have hnot : ¬ i ≤ u := by
          intro hiu
          exact hi ⟨hli, hiu⟩
        omega
    -- Proof comment: outside the bounded window, every stage of `F ⋙ H^i` is already zero, so
    -- every sufficiently late transition map is zero for the trivial reason that its target is
    -- zero.
    exact
      hasProObjectValue_zero_of_eventually_zero_transition (F := F ⋙ H^i) <| by
        intro n
        refine ⟨n + 1, Nat.le_succ n, ?_⟩
        have hz : IsZero ((F ⋙ H^i).obj (op n)) := by
          rcases houtside with hlt | hgt
          · simpa using isZero_of_isGE (F.obj (op n)) l i hlt
          · simpa using isZero_of_isLE (F.obj (op n)) u i hgt
        exact hz.eq_of_tgt _ _
  have hXi_zero : ∀ i : ℤ, IsZero ((H^i).obj X) := by
    intro i
    by_cases hi : i ∈ Set.Icc l u
    · rcases hH i hi with ⟨e₀⟩
      rcases hHX i with ⟨eX⟩
      let e : (0 : 𝒜) ≅ (H^i).obj X :=
        Functor.CorepresentableBy.uniqueUpToIso e₀ eX
      -- Proof comment: in the bounded window, both `0` and `H^i(X)` corepresent the same
      -- pro-object of cohomology groups, so they are canonically isomorphic.
      exact IsZero.of_iso (isZero_zero 𝒜) e
    · rcases hOutside i hi with ⟨e₀⟩
      rcases hHX i with ⟨eX⟩
      let e : (0 : 𝒜) ≅ (H^i).obj X :=
        Functor.CorepresentableBy.uniqueUpToIso e₀ eX
      -- Proof comment: outside the bounded window, the cohomology tower is stagewise zero, so
      -- the same uniqueness-of-corepresentation argument again forces `H^i(X)` to vanish.
      exact IsZero.of_iso (isZero_zero 𝒜) e
  have hXGE : X.IsGE (u + 1) := by
    -- Proof comment: all cohomology objects of `X` below degree `u + 1` vanish, so `X` lies in
    -- the nonnegative aisle shifted to `u + 1`.
    rw [DerivedCategory.isGE_iff]
    intro i hi
    exact hXi_zero i
  have hXLE : X.IsLE u := by
    -- Proof comment: the same vanishing statement above degree `u` places `X` in `D^{≤ u}`.
    rw [DerivedCategory.isLE_iff]
    intro i hi
    exact hXi_zero i
  have hIdZero : 𝟙 X = 0 := by
    -- Proof comment: orthogonality between `D^{≤ u}` and `D^{≥ u + 1}` kills the identity of
    -- `X`, hence `X` is the zero object of the derived category.
    exact
      DerivedCategory.TStructure.t.zero_of_isLE_of_isGE
        (𝟙 X) u (u + 1) (by omega) hXLE hXGE
  have hZero : IsZero X := by
    exact (IsZero.iff_id_eq_zero X).2 hIdZero
  rcases hX with ⟨eX⟩
  -- Proof comment: transport the fixed pro-object value from `X` to the zero object along the
  -- canonical isomorphism `X ≅ 0`.
  exact ⟨Functor.CorepresentableBy.ofIso eX hZero.isoZero⟩

/-- Lemma 13.42.5: if `α : A ⟶ B` is a morphism of sequential inverse systems in `D(\mathcal A)`
and there exist integers `a` and `b` such that both systems have cohomology supported in
`[a, b]`, while for every degree `i ∈ [a, b]` the induced morphism of inverse systems on `H^i` is a
pro-isomorphism in `\mathcal A`, then `α` is a pro-isomorphism of inverse systems in
`D(\mathcal A)`. -/
@[stacks 0G3D]
theorem ofNatTrans_isProIsomorphism_of_uniformlyBounded_homologywise_proIso
    {A B : SequentialInverseSystem (D(𝒜))} (α : A ⟶ B) (a b : ℤ)
    (hAGE : ∀ n : ℕ, (A.obj (op n)).IsGE a)
    (hALE : ∀ n : ℕ, (A.obj (op n)).IsLE b)
    (hBGE : ∀ n : ℕ, (B.obj (op n)).IsGE a)
    (hBLE : ∀ n : ℕ, (B.obj (op n)).IsLE b)
    (hH : ∀ i ∈ Set.Icc a b,
      (ofNatTrans (Functor.whiskerRight α (H^i))).IsProIsomorphism) :
    (ofNatTrans α).IsProIsomorphism := by
  -- Proof comment: the source proof first chooses a compatible inverse system of distinguished
  -- triangles extending `α`, then proves the third-term cohomology towers are pro-zero by exact
  --ness and `homology_comp_zero_of_delta_zero_of_map_mor₂_comp_zero`, and finally applies Lemmas
  -- `13.42.3`
  -- and `13.42.4`.
  -- Route correction: the previous route asked exactness to produce literal factorization through
  -- `H^p(B_m) ⟶ H^p(C_m)`, but the owner API only gives the weaker and correct composite-zero
  -- consequence used by the source proof.
  let T : OrderDual ℕ ⥤ Triangle (D(𝒜)) := coneTriangleSystem (𝒜 := 𝒜) α
  have hT : ∀ n : ℕ, T.obj (op n) ∈ distTriang (D(𝒜)) := by
    intro n
    -- Proof comment: the stagewise TR1 choices were assembled into `T` without altering the
    -- distinguished triangles themselves.
    simpa [T] using cone_triangle_system_distinguished (𝒜 := 𝒜) α n
  have hThirdGE : ∀ n : ℕ, ((T.obj (op n)).obj₃).IsGE (a - 1) := by
    intro n
    -- Proof comment: the stagewise cone bounds are now packaged in the canonical owner form
    -- needed by Lemma `13.42.3`.
    exact (cone_triangle_system_third_bounds (𝒜 := 𝒜) α a b hAGE hALE hBGE hBLE n).1
  have hThirdLE : ∀ n : ℕ, ((T.obj (op n)).obj₃).IsLE b := by
    intro n
    -- Proof comment: the same stagewise cone bounds give the uniform upper cutoff.
    exact (cone_triangle_system_third_bounds (𝒜 := 𝒜) α a b hAGE hALE hBGE hBLE n).2
  suffices h₃ : HasProObjectValue (T ⋙ Triangle.π₃) (0 : D(𝒜)) by
    have hIso :
        (ofOrderDualNatTrans (Functor.whiskerLeft T Triangle.π₁Toπ₂)).IsProIsomorphism :=
      triangleFirstToSecond_isProIsomorphism_of_proZero_third (T := T) hT h₃
    -- Proof comment: once the third vertex system is pro-zero, Lemma `13.42.4` returns the
    -- desired pro-isomorphism for the first maps in the distinguished triangle tower, which is
    -- exactly `α` by the stagewise identification above.
    simpa [T, cone_triangle_system_first_to_second_rep_eq (𝒜 := 𝒜) α] using hIso
  have hConeCohZero :
      ∀ p : ℤ, HasProObjectValue ((T ⋙ Triangle.π₃) ⋙ H^p) (0 : 𝒜) := by
    intro p
    -- Proof comment: each cone cohomology tower is pro-zero because its transition maps vanish
    -- eventually, either immediately outside the window or by the source-book `m`-then-`k`
    -- exactness argument inside the window.
    exact
      hasProObjectValue_zero_of_eventually_zero_transition
        (((T ⋙ Triangle.π₃) ⋙ H^p))
        (cone_cohomology_eventually_zero_transition (𝒜 := 𝒜) α a b p
          hAGE hALE hBGE hBLE hH)
  -- Proof comment: Lemma `13.42.3` now applies to the third-vertex system with bounds
  -- `[a - 1, b]`; the closer above identifies its fixed pro-object value with `0`.
  exact
    hasProObjectValue_zero_of_uniformly_bounded_zero_cohomology
      (𝒜 := 𝒜) (F := T ⋙ Triangle.π₃) (a - 1) b hThirdGE hThirdLE
      (fun p hp ↦ hConeCohZero p)

end CategoryTheory
