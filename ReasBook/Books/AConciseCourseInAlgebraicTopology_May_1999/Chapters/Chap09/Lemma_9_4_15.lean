import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
import Mathlib.CategoryTheory.Functor.OfSequence
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap05.Construction_5_2_5
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap05.Definition_5_1_10
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap05.Proposition_5_2_6
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Lemma_9_4_15.ClosedEmbeddingSupport
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Definition_9_6_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits GrpCat.FilteredColimits MonCat.FilteredColimits
open Lemma9415Support
open scoped Topology Topology.Homotopy unitInterval

universe u v

noncomputable section

variable {α : Type u} [TopologicalSpace α]

-- Semantic recall: `lean_leansearch` found no dedicated theorem formalizing sequential colimits of
-- higher homotopy groups, so the faithful owner here is the `GrpCat`-valued sequential diagram
-- `i ↦ π_ (n + 1) (X i)` attached to the explicit inclusion-sequence colimit from
-- `Construction 5.2.5`.

/-- The recursively propagated basepoint in the `i`th stage of a monotone inclusion sequence. -/
def inclusionSequenceBasepoint (X : ℕ → Set α) (hX : Monotone X) (x : X 0) : (i : ℕ) → X i
  | 0 => x
  | i + 1 =>
      ⟨(inclusionSequenceBasepoint X hX x i).1,
        hX (Nat.le_succ i) (inclusionSequenceBasepoint X hX x i).2⟩

/-- A target-basepoint equality specializes the canonical `homotopyGroupMap` to the chosen
basepoint `b`. -/
private def homotopyGroupMapOverEq
    {A B : Type u} [TopologicalSpace A] [TopologicalSpace B]
    {a : A} {b : B} (f : C(A, B)) (hf : f a = b) (n : ℕ) :
    π_ n A a → π_ n B b :=
  match hf with
  | rfl => homotopyGroupMap f n a

/-- The induced map on positive-degree homotopy groups preserves the unit element. -/
private theorem homotopyGroupMapOverEq_one
    {A B : Type u} [TopologicalSpace A] [TopologicalSpace B]
    {a : A} {b : B} (f : C(A, B)) (hf : f a = b) (n : ℕ) :
    homotopyGroupMapOverEq f hf (n + 1) 1 = 1 := by
  -- Specialize to the literally matching target basepoint and reuse the standard `π_*` unit law.
  cases hf
  rw [homotopyGroupMapOverEq]
  exact homotopyGroupMap_one f n a

/-- The induced map on positive-degree homotopy groups preserves multiplication. -/
private theorem homotopyGroupMapOverEq_mul
    {A B : Type u} [TopologicalSpace A] [TopologicalSpace B]
    {a : A} {b : B} (f : C(A, B)) (hf : f a = b) (n : ℕ)
    (p q : π_ (n + 1) A a) :
    homotopyGroupMapOverEq f hf (n + 1) (p * q) =
      homotopyGroupMapOverEq f hf (n + 1) p * homotopyGroupMapOverEq f hf (n + 1) q := by
  -- Once the target basepoint is definitionally `f a`, this is the usual multiplicativity theorem.
  cases hf
  rw [homotopyGroupMapOverEq]
  exact homotopyGroupMap_mul f n a p q

/-- A based continuous map induces a group homomorphism on positive-degree homotopy groups. -/
private def homotopyGroupMonoidHomOverEq
    {A B : Type u} [TopologicalSpace A] [TopologicalSpace B]
    {a : A} {b : B} (f : C(A, B)) (hf : f a = b) (n : ℕ) :
    π_ (n + 1) A a →* π_ (n + 1) B b where
  toFun := homotopyGroupMapOverEq f hf (n + 1)
  map_one' := homotopyGroupMapOverEq_one f hf n
  map_mul' := homotopyGroupMapOverEq_mul f hf n

/-- The `i`th positive-degree homotopy group in the sequential inclusion system, viewed in
`GrpCat`. -/
abbrev inclusionSequenceHomotopyGroupStage
    (X : ℕ → Set α) (hX : Monotone X) (n : ℕ) (x : X 0) (i : ℕ) : GrpCat :=
  GrpCat.of (π_ (n + 1) (X i) (inclusionSequenceBasepoint X hX x i))

/-- The successor map on the sequential system `i ↦ π_ (n + 1) (X i)` induced by the inclusion
`X i ↪ X (i + 1)`, bundled as a morphism in `GrpCat`. -/
def inclusionSequenceHomotopyGroupStepMap
    (X : ℕ → Set α) (hX : Monotone X) (n : ℕ) (x : X 0) (i : ℕ) :
    inclusionSequenceHomotopyGroupStage X hX n x i ⟶
      inclusionSequenceHomotopyGroupStage X hX n x (i + 1) :=
  GrpCat.ofHom <| homotopyGroupMonoidHomOverEq ((inclusionSequenceStageMap X hX i).hom) rfl n

/-- The sequential `GrpCat`-diagram of positive-degree homotopy groups associated to a monotone
sequence of inclusions. -/
def inclusionSequenceHomotopyGroupDiagram
    (X : ℕ → Set α) (hX : Monotone X) (n : ℕ) (x : X 0) : ℕ ⥤ GrpCat :=
  Functor.ofSequence (inclusionSequenceHomotopyGroupStepMap X hX n x)

@[simp] theorem inclusionSequenceHomotopyGroupDiagram_map_succ
    (X : ℕ → Set α) (hX : Monotone X) (n : ℕ) (x : X 0) (i : ℕ) :
    (inclusionSequenceHomotopyGroupDiagram X hX n x).map (homOfLE (Nat.le_add_right i 1)) =
      inclusionSequenceHomotopyGroupStepMap X hX n x i := by
  exact Functor.ofSequence_map_homOfLE_succ (inclusionSequenceHomotopyGroupStepMap X hX n x) i

/-- The distinguished basepoint of the inclusion-sequence colimit, coming from stage `0`. -/
def inclusionSequenceColimitBasepoint (X : ℕ → Set α) (x : X 0) :
    inclusionSequenceColimit X :=
  inclusionSequenceColimitInclusion X 0 x

/-- Every compact cube representative of a class in `π_ (n + 1)` factors through some finite
stage.

This is the cube-model version of the compact-sphere factorization input used in the source proof
of Lemma 9.4.15. -/
def inclusionSequenceColimitHasCompactLoopFactorization
    (X : ℕ → Set α) (n : ℕ) : Prop :=
  ∀ (f : C(I^(Fin (n + 1)), inclusionSequenceColimit X)),
    ∃ i, ∃ g : C(I^(Fin (n + 1)), X i), (inclusionSequenceColimitHom X i).hom.comp g = f

/-- Every compact cylinder representative of a based homotopy in degree `n + 1` factors through
some finite stage.

This is the compact-cylinder factorization input used for injectivity in Lemma 9.4.15. The
`ULift` only matches universe levels of the target colimit. -/
def inclusionSequenceColimitHasCompactCylinderFactorization
    (X : ℕ → Set α) (n : ℕ) : Prop :=
  ∀ (f : C(ULift.{u} (I × I^(Fin (n + 1))), inclusionSequenceColimit X)),
    ∃ k, ∃ g : C(ULift.{u} (I × I^(Fin (n + 1))), X k),
      (inclusionSequenceColimitHom X k).hom.comp g = f

/-- The homotopy group of the inclusion-sequence colimit, using the final topology from
`Construction 5.2.5` rather than the inherited subtype topology, bundled in `GrpCat`. -/
abbrev inclusionSequenceColimitHomotopyGroup
    (X : ℕ → Set α) (n : ℕ) (x : X 0) : GrpCat :=
  let _ : TopologicalSpace (inclusionSequenceColimit X) := (inclusionSequenceColimit X).str
  GrpCat.of (π_ (n + 1) (inclusionSequenceColimit X) (inclusionSequenceColimitBasepoint X x))

/-- Every propagated stage basepoint maps to the same point of the inclusion-sequence colimit. -/
private theorem inclusionSequenceColimitBasepoint_eq
    (X : ℕ → Set α) (hX : Monotone X) (x : X 0) (i : ℕ) :
    (inclusionSequenceColimitHom X i).hom (inclusionSequenceBasepoint X hX x i) =
      inclusionSequenceColimitBasepoint X x := by
  induction i with
  | zero =>
      -- At stage `0` the propagated basepoint is the original chosen basepoint.
      rfl
  | succ i ih =>
      -- Move one step forward using the colimit cocone compatibility, then apply the induction.
      have hstep :=
        congrArg
          (fun f ↦ f (inclusionSequenceBasepoint X hX x i))
          (congrArg TopCat.Hom.hom (inclusionSequenceColimitHom_naturality X hX i))
      simpa [inclusionSequenceBasepoint] using hstep.trans ih

/-- Helper for Lemma 9.4.15: the induced map on homotopy groups of a composite is the composite
of the induced maps. -/
private theorem homotopyGroupMap_comp
    {A B C : Type u} [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
    (f : C(A, B)) (g : C(B, C)) (q : ℕ) (a : A) :
    homotopyGroupMap (g.comp f) q a =
      (homotopyGroupMap g q (f a)) ∘ homotopyGroupMap f q a := by
  -- Reduce the quotient statement to representatives, where both sides are literally `g ∘ f`.
  funext x
  refine Quotient.inductionOn x ?_
  intro γ
  rfl

/-- Helper for Lemma 9.4.15: the specialized based map does not depend on which proof of
`f a = b` is chosen. -/
private theorem homotopyGroupMapOverEq_proof_irrel
    {A B : Type u} [TopologicalSpace A] [TopologicalSpace B]
    {a : A} {b : B} (f : C(A, B)) (h₁ h₂ : f a = b) (q : ℕ) :
    homotopyGroupMapOverEq f h₁ q = homotopyGroupMapOverEq f h₂ q := by
  -- Both specialized maps reduce to the same literal map once the target basepoint is matched.
  cases h₁
  cases h₂
  rfl

/-- Helper for Lemma 9.4.15: equal continuous maps induce equal specialized based maps on
homotopy groups once the basepoint equalities are matched. -/
private theorem homotopyGroupMapOverEq_congr
    {A B : Type u} [TopologicalSpace A] [TopologicalSpace B]
    {a : A} {b : B} {f g : C(A, B)} (hfg : f = g)
    (hf : f a = b) (hg : g a = b) (q : ℕ) :
    homotopyGroupMapOverEq f hf q = homotopyGroupMapOverEq g hg q := by
  -- After identifying the two maps, only proof irrelevance for the chosen basepoint equality
  -- remains.
  cases hfg
  exact homotopyGroupMapOverEq_proof_irrel f hf hg q

/-- Helper for Lemma 9.4.15: postcomposing a generalized loop and then identifying the target
basepoint via `hf` gives a generalized loop at `b`. -/
private theorem genLoopMapOverEqLoop_boundary
    {A B : Type u} [TopologicalSpace A] [TopologicalSpace B]
    {a : A} {b : B} (f : C(A, B)) (hf : f a = b) (q : ℕ)
    (γ : Ω^ (Fin q) A a) :
    ∀ t ∈ Cube.boundary (Fin q), (genLoopMap f γ).1 t = b := by
  intro t ht
  calc
    (genLoopMap f γ).1 t = f a := by
      simpa using congrArg f (γ.2 t ht)
    _ = b := hf

/-- Helper for Lemma 9.4.15: the postcomposition representative viewed at the chosen target
basepoint `b`. -/
private def genLoopMapOverEqLoop
    {A B : Type u} [TopologicalSpace A] [TopologicalSpace B]
    {a : A} {b : B} (f : C(A, B)) (hf : f a = b) {q : ℕ}
    (γ : Ω^ (Fin q) A a) :
    Ω^ (Fin q) B b :=
  ⟨(genLoopMap f γ).1, genLoopMapOverEqLoop_boundary f hf q γ⟩

/-- Helper for Lemma 9.4.15: the specialized based map sends a generalized-loop class to the class
of its postcomposition, viewed at the target basepoint chosen by `hf`. -/
private theorem homotopyGroupMapOverEq_mk
    {A B : Type u} [TopologicalSpace A] [TopologicalSpace B]
    {a : A} {b : B} (f : C(A, B)) (hf : f a = b) (q : ℕ)
    (γ : Ω^ (Fin q) A a) :
    homotopyGroupMapOverEq f hf q ⟦γ⟧ =
      (⟦genLoopMapOverEqLoop f hf γ⟧ : π_ q B b) := by
  -- Reduce to the definitional case where the target basepoint is literally `f a`.
  cases hf
  simpa [homotopyGroupMapOverEq, genLoopMapOverEqLoop] using homotopyGroupMap_mk f q a γ

/-- Helper for Lemma 9.4.15: composing two based maps composes their induced homotopy-group maps.
-/
private theorem homotopyGroupMapOverEq_comp
    {A B C : Type u} [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
    {a : A} {b : B} {c : C}
    (f : C(A, B)) (hf : f a = b) (g : C(B, C)) (hg : g b = c) (q : ℕ) :
    (homotopyGroupMapOverEq g hg q) ∘ (homotopyGroupMapOverEq f hf q) =
      homotopyGroupMapOverEq (g.comp f) (by simpa [ContinuousMap.comp_apply, hf] using hg) q := by
  -- After synchronizing both target basepoints definitionally, this is the ordinary composition
  -- law for `homotopyGroupMap`.
  cases hf
  cases hg
  simpa [homotopyGroupMapOverEq] using (homotopyGroupMap_comp f g q a).symm

/-- Helper for Lemma 9.4.15: the specialized induced map of the identity is the identity. -/
private theorem homotopyGroupMapOverEq_id
    {A : Type u} [TopologicalSpace A] {a : A} (q : ℕ) :
    homotopyGroupMapOverEq (ContinuousMap.id A) (a := a) (b := a) rfl q = id := by
  -- After matching the target basepoint definitionally, this is the standard identity law on `π_`.
  simp [homotopyGroupMapOverEq, homotopyGroupMap_id]

/-- The `i`th leg from the stage positive-degree homotopy group to the positive-degree homotopy
group of the colimit space. -/
private def inclusionSequenceHomotopyGroupCoconeMap
    (X : ℕ → Set α) (hX : Monotone X) (n : ℕ) (x : X 0) (i : ℕ) :
    inclusionSequenceHomotopyGroupStage X hX n x i ⟶
      inclusionSequenceColimitHomotopyGroup X n x :=
  let _ : TopologicalSpace (inclusionSequenceColimit X) := (inclusionSequenceColimit X).str
  GrpCat.ofHom <|
    homotopyGroupMonoidHomOverEq
      ((inclusionSequenceColimitHom X i).hom)
      (inclusionSequenceColimitBasepoint_eq X hX x i)
      n

/-- The stage-to-colimit maps are compatible with the successor maps in the homotopy-group
diagram. -/
private theorem inclusionSequenceHomotopyGroupCoconeMap_naturality
    (X : ℕ → Set α) (hX : Monotone X) (n : ℕ) (x : X 0) (i : ℕ) :
    (inclusionSequenceHomotopyGroupDiagram X hX n x).map (homOfLE (Nat.le_add_right i 1)) ≫
        inclusionSequenceHomotopyGroupCoconeMap X hX n x (i + 1) =
      inclusionSequenceHomotopyGroupCoconeMap X hX n x i ≫
        ((Functor.const ℕ).obj (inclusionSequenceColimitHomotopyGroup X n x)).map
          (homOfLE (Nat.le_add_right i 1)) := by
  -- The constant-diagram side is the identity, so it remains to identify the two stage-to-colimit
  -- induced maps via functoriality of `homotopyGroupMap`.
  ext η
  simp only [Functor.const_obj_map,
    inclusionSequenceHomotopyGroupDiagram_map_succ, inclusionSequenceHomotopyGroupStepMap,
    inclusionSequenceHomotopyGroupCoconeMap, homotopyGroupMonoidHomOverEq]
  let p :
      (((inclusionSequenceColimitHom X (i + 1)).hom).comp
          ((inclusionSequenceStageMap X hX i).hom))
        (inclusionSequenceBasepoint X hX x i) =
        inclusionSequenceColimitBasepoint X x := by
    -- The composite sends the propagated stage basepoint to the ambient basepoint by the successor
    -- case of `inclusionSequenceColimitBasepoint_eq`.
    simpa [ContinuousMap.comp_apply, inclusionSequenceBasepoint, inclusionSequenceStageMap_apply]
      using inclusionSequenceColimitBasepoint_eq X hX x (i + 1)
  let q :
      (inclusionSequenceColimitHom X i).hom
        (inclusionSequenceBasepoint X hX x i) =
        inclusionSequenceColimitBasepoint X x := by
    -- This is the same composite basepoint equality, rewritten to the naturality-normalized map.
    simpa [ContinuousMap.comp_apply, inclusionSequenceBasepoint, inclusionSequenceStageMap_apply]
      using inclusionSequenceColimitBasepoint_eq X hX x (i + 1)
  have hcomp :
      (homotopyGroupMapOverEq ((inclusionSequenceColimitHom X (i + 1)).hom)
          (inclusionSequenceColimitBasepoint_eq X hX x (i + 1)) (n + 1)) ∘
        (homotopyGroupMapOverEq ((inclusionSequenceStageMap X hX i).hom) rfl (n + 1)) =
        homotopyGroupMapOverEq
          (((inclusionSequenceColimitHom X (i + 1)).hom).comp
            ((inclusionSequenceStageMap X hX i).hom))
          p
          (n + 1) := by
    -- Collapse the consecutive stage and colimit maps to the induced map of their composite.
    simpa using
      homotopyGroupMapOverEq_comp
        ((inclusionSequenceStageMap X hX i).hom) rfl
        ((inclusionSequenceColimitHom X (i + 1)).hom)
        (inclusionSequenceColimitBasepoint_eq X hX x (i + 1))
        (n + 1)
  have hnat :
      ((inclusionSequenceColimitHom X (i + 1)).hom).comp
          ((inclusionSequenceStageMap X hX i).hom) =
        (inclusionSequenceColimitHom X i).hom := by
    -- Read the point-set equality directly from cocone naturality in `TopCat`.
    exact congrArg TopCat.Hom.hom (inclusionSequenceColimitHom_naturality X hX i)
  have hcongr :
      homotopyGroupMapOverEq
          (((inclusionSequenceColimitHom X (i + 1)).hom).comp
            ((inclusionSequenceStageMap X hX i).hom))
          p
          (n + 1) =
        homotopyGroupMapOverEq ((inclusionSequenceColimitHom X i).hom) q (n + 1) := by
    -- Replace the composite map by the naturality-normalized stage-to-colimit map.
    exact homotopyGroupMapOverEq_congr hnat p q (n + 1)
  have hproof :
      homotopyGroupMapOverEq ((inclusionSequenceColimitHom X i).hom)
          q
          (n + 1) =
        homotopyGroupMapOverEq ((inclusionSequenceColimitHom X i).hom)
          (inclusionSequenceColimitBasepoint_eq X hX x i)
          (n + 1) := by
    -- The final induced map is insensitive to which proof of the same basepoint equality is used.
    exact homotopyGroupMapOverEq_proof_irrel
      ((inclusionSequenceColimitHom X i).hom)
      _
      _
      (n + 1)
  calc
    ((homotopyGroupMapOverEq ((inclusionSequenceColimitHom X (i + 1)).hom)
          (inclusionSequenceColimitBasepoint_eq X hX x (i + 1)) (n + 1)) ∘
        (homotopyGroupMapOverEq ((inclusionSequenceStageMap X hX i).hom) rfl (n + 1))) η =
      homotopyGroupMapOverEq
          (((inclusionSequenceColimitHom X (i + 1)).hom).comp
            ((inclusionSequenceStageMap X hX i).hom))
          p
          (n + 1) η := by
        exact congrArg (fun k ↦ k η) hcomp
    _ =
      homotopyGroupMapOverEq ((inclusionSequenceColimitHom X i).hom)
          q
          (n + 1) η := by
        exact congrArg (fun k ↦ k η) hcongr
    _ =
      homotopyGroupMapOverEq ((inclusionSequenceColimitHom X i).hom)
          (inclusionSequenceColimitBasepoint_eq X hX x i)
          (n + 1) η := by
        exact congrArg (fun k ↦ k η) hproof

/-- The canonical cocone from the sequential diagram of stage homotopy groups to the homotopy
group of the inclusion-sequence colimit. -/
def inclusionSequenceHomotopyGroupCocone
    (X : ℕ → Set α) (hX : Monotone X) (n : ℕ) (x : X 0) :
    Cocone (inclusionSequenceHomotopyGroupDiagram X hX n x) where
  pt := inclusionSequenceColimitHomotopyGroup X n x
  ι :=
    NatTrans.ofSequence
      (inclusionSequenceHomotopyGroupCoconeMap X hX n x)
      (inclusionSequenceHomotopyGroupCoconeMap_naturality X hX n x)

/-- The filtered colimit in `GrpCat` of the sequential positive-degree homotopy-group diagram. -/
abbrev inclusionSequenceHomotopyGroupColimit
    (X : ℕ → Set α) (hX : Monotone X) (n : ℕ) (x : X 0) : GrpCat :=
  GrpCat.FilteredColimits.colimit (inclusionSequenceHomotopyGroupDiagram X hX n x)

/-- The canonical comparison morphism
`colim_i π_ (n + 1) (X i) ⟶ π_ (n + 1) (inclusionSequenceColimit X)` in `GrpCat`, attached to the
sequential homotopy-group cocone. -/
noncomputable def inclusionSequenceHomotopyGroupColimitDesc
    (X : ℕ → Set α) (hX : Monotone X) (n : ℕ) (x : X 0) :
    inclusionSequenceHomotopyGroupColimit X hX n x ⟶
      inclusionSequenceColimitHomotopyGroup X n x :=
  (GrpCat.FilteredColimits.colimitCoconeIsColimit
    (inclusionSequenceHomotopyGroupDiagram X hX n x)).desc
      (inclusionSequenceHomotopyGroupCocone X hX n x)

/-- The comparison morphism evaluates a filtered-colimit generator by the corresponding stage
map to the colimit homotopy group. -/
private theorem inclusionSequenceHomotopyGroupColimitDesc_apply_mk
    (X : ℕ → Set α) (hX : Monotone X) (n : ℕ) (x : X 0) (i : ℕ)
    (η : π_ (n + 1) (X i) (inclusionSequenceBasepoint X hX x i)) :
    inclusionSequenceHomotopyGroupColimitDesc X hX n x
        (G.mk (inclusionSequenceHomotopyGroupDiagram X hX n x) ⟨i, η⟩) =
      inclusionSequenceHomotopyGroupCoconeMap X hX n x i η := by
  -- Evaluate the colimit `desc` on the `i`th cocone leg and then on the chosen generator.
  have hfac :=
    congrArg GrpCat.Hom.hom
      ((GrpCat.FilteredColimits.colimitCoconeIsColimit
          (inclusionSequenceHomotopyGroupDiagram X hX n x)).fac
        (inclusionSequenceHomotopyGroupCocone X hX n x) i)
  exact congrArg (fun f ↦ f η) hfac

/-- Helper for Lemma 9.4.15: every homotopy-group class in the colimit space is represented by a
loop from some finite stage, so the canonical comparison map is surjective. -/
private theorem inclusionSequenceHomotopyGroupColimitDesc_surjective
    (X : ℕ → Set α) (hX : Monotone X)
    (n : ℕ) (hloop : inclusionSequenceColimitHasCompactLoopFactorization X n) (x : X 0) :
    Function.Surjective (inclusionSequenceHomotopyGroupColimitDesc X hX n x) := by
  intro η
  refine Quotient.inductionOn η ?_
  intro γ
  obtain ⟨i, g, hg⟩ := hloop γ.1
  have hboundary :
      ∀ t ∈ Cube.boundary (Fin (n + 1)), g t = inclusionSequenceBasepoint X hX x i := by
    intro t ht
    apply Lemma9415Support.inclusionSequenceColimitInclusion_injective X i
    calc
      inclusionSequenceColimitInclusion X i (g t) =
          ((inclusionSequenceColimitHom X i).hom.comp g) t := by
            rfl
      _ = γ.1 t := by
            simpa [ContinuousMap.comp_apply] using congrArg (fun h ↦ h t) hg
      _ = inclusionSequenceColimitBasepoint X x := by
            exact γ.2 t ht
      _ = inclusionSequenceColimitInclusion X i (inclusionSequenceBasepoint X hX x i) := by
            symm
            exact inclusionSequenceColimitBasepoint_eq X hX x i
  let γi : Ω^ (Fin (n + 1)) (X i) (inclusionSequenceBasepoint X hX x i) := ⟨g, hboundary⟩
  refine ⟨G.mk (inclusionSequenceHomotopyGroupDiagram X hX n x) ⟨i, ⟦γi⟧⟩, ?_⟩
  have hloop :
      genLoopMapOverEqLoop ((inclusionSequenceColimitHom X i).hom)
          (inclusionSequenceColimitBasepoint_eq X hX x i) γi = γ := by
    -- The factored stage loop represents exactly the original colimit loop.
    apply GenLoop.ext
    intro t
    simpa [γi, genLoopMapOverEqLoop, ContinuousMap.comp_apply] using congrArg (fun h ↦ h t) hg
  calc
    inclusionSequenceHomotopyGroupColimitDesc X hX n x
        (G.mk (inclusionSequenceHomotopyGroupDiagram X hX n x) ⟨i, ⟦γi⟧⟩) =
      inclusionSequenceHomotopyGroupCoconeMap X hX n x i ⟦γi⟧ := by
        exact inclusionSequenceHomotopyGroupColimitDesc_apply_mk X hX n x i ⟦γi⟧
    _ =
      (⟦genLoopMapOverEqLoop ((inclusionSequenceColimitHom X i).hom)
          (inclusionSequenceColimitBasepoint_eq X hX x i) γi⟧ :
        π_ (n + 1) (inclusionSequenceColimit X) (inclusionSequenceColimitBasepoint X x)) := by
        exact homotopyGroupMapOverEq_mk
          ((inclusionSequenceColimitHom X i).hom)
          (inclusionSequenceColimitBasepoint_eq X hX x i)
          (n + 1)
          γi
    _ = ⟦γ⟧ := by
        simpa [hloop]

/-- Helper for Lemma 9.4.15: any forward stage map carries the propagated basepoint to the
propagated basepoint of the later stage. -/
private theorem inclusionSequenceDiagram_map_basepoint
    (X : ℕ → Set α) (hX : Monotone X) (x : X 0) {i j : ℕ} (hij : i ≤ j) :
    ((inclusionSequenceDiagram X hX).map (homOfLE hij))
        (inclusionSequenceBasepoint X hX x i) =
      inclusionSequenceBasepoint X hX x j := by
  -- Compare both points after applying the injective inclusion into the colimit.
  apply Lemma9415Support.inclusionSequenceColimitInclusion_injective X j
  calc
    inclusionSequenceColimitInclusion X j
        (((inclusionSequenceDiagram X hX).map (homOfLE hij))
          (inclusionSequenceBasepoint X hX x i)) =
      inclusionSequenceColimitInclusion X i (inclusionSequenceBasepoint X hX x i) := by
        exact congrArg
          (fun f ↦ f (inclusionSequenceBasepoint X hX x i))
          (congrArg TopCat.Hom.hom
            (Lemma9415Support.inclusionSequenceColimitHom_naturality_of_le X hX hij))
    _ = inclusionSequenceColimitBasepoint X x := by
        exact inclusionSequenceColimitBasepoint_eq X hX x i
    _ = inclusionSequenceColimitInclusion X j (inclusionSequenceBasepoint X hX x j) := by
        symm
        exact inclusionSequenceColimitBasepoint_eq X hX x j

/-- Helper for Lemma 9.4.15: transporting a generalized loop along a forward stage map preserves
the boundary value after identifying the propagated basepoints. -/
private theorem transportedStageGenLoop_boundary
    (X : ℕ → Set α) (hX : Monotone X) (x : X 0) {n i j : ℕ} (hij : i ≤ j)
    (γ : Ω^ (Fin (n + 1)) (X i) (inclusionSequenceBasepoint X hX x i)) :
    ∀ t ∈ Cube.boundary (Fin (n + 1)),
      (genLoopMap (((inclusionSequenceDiagram X hX).map (homOfLE hij)).hom) γ).1 t =
        inclusionSequenceBasepoint X hX x j := by
  -- The transported loop takes boundary points to the image of the old basepoint, hence to the
  -- propagated later-stage basepoint.
  intro t ht
  calc
    ((inclusionSequenceDiagram X hX).map (homOfLE hij)).hom (γ t) =
      ((inclusionSequenceDiagram X hX).map (homOfLE hij)).hom
        (inclusionSequenceBasepoint X hX x i) := by
        simpa using
          congrArg (((inclusionSequenceDiagram X hX).map (homOfLE hij)).hom) (γ.2 t ht)
    _ = inclusionSequenceBasepoint X hX x j := by
        exact inclusionSequenceDiagram_map_basepoint X hX x hij

/-- Helper for Lemma 9.4.15: transport a generalized loop to any later stage of the sequential
diagram. -/
private def transportedStageGenLoop
    (X : ℕ → Set α) (hX : Monotone X) (x : X 0) {n i j : ℕ} (hij : i ≤ j)
    (γ : Ω^ (Fin (n + 1)) (X i) (inclusionSequenceBasepoint X hX x i)) :
    Ω^ (Fin (n + 1)) (X j) (inclusionSequenceBasepoint X hX x j) :=
  ⟨(genLoopMap (((inclusionSequenceDiagram X hX).map (homOfLE hij)).hom) γ).1,
    transportedStageGenLoop_boundary X hX x hij γ⟩

/-- Helper for Lemma 9.4.15: transporting a generalized loop along the identity stage map leaves
it unchanged. -/
@[simp] private theorem transportedStageGenLoop_refl
    (X : ℕ → Set α) (hX : Monotone X) (x : X 0) {n i : ℕ}
    (γ : Ω^ (Fin (n + 1)) (X i) (inclusionSequenceBasepoint X hX x i)) :
    transportedStageGenLoop X hX x (Nat.le_refl i) γ = γ := by
  -- At equal indices the stage diagram map is literally the identity, so the transported loop and
  -- the original loop agree pointwise.
  apply GenLoop.ext
  intro t
  have hmap :
      ((inclusionSequenceDiagram X hX).map (homOfLE (Nat.le_refl i))).hom =
        ContinuousMap.id (X i) := by
    -- Identify the forward map at a reflexive stage inequality with the identity map.
    simpa using congrArg TopCat.Hom.hom ((inclusionSequenceDiagram X hX).map_id i)
  -- Route correction: compare the underlying transported map at `t`, then rewrite the stage map
  -- itself to the identity.
  change ((inclusionSequenceDiagram X hX).map (homOfLE (Nat.le_refl i))).hom (γ t) = γ t
  exact (congrArg (fun f ↦ f (γ t)) hmap).trans rfl

/-- Helper for Lemma 9.4.15: the successor-step postcomposition representative is exactly the
one-step transported generalized loop. -/
private theorem genLoopMapOverEqLoop_stageMap_eq_transportedStageGenLoop
    (X : ℕ → Set α) (hX : Monotone X) (x : X 0) {n i : ℕ}
    (γ : Ω^ (Fin (n + 1)) (X i) (inclusionSequenceBasepoint X hX x i)) :
    genLoopMapOverEqLoop ((inclusionSequenceStageMap X hX i).hom) rfl γ =
      transportedStageGenLoop X hX x (Nat.le_succ i) γ := by
  -- Both loop representatives are defined by postcomposing `γ` with the successor inclusion, so
  -- their underlying maps coincide pointwise.
  apply GenLoop.ext
  intro t
  -- Route correction: rewrite the transported side to the canonical successor diagram map first,
  -- then both sides are the same evaluation.
  change ((inclusionSequenceStageMap X hX i).hom) (γ t) =
    ((inclusionSequenceDiagram X hX).map (homOfLE (Nat.le_succ i))).hom (γ t)
  have hmap :
      ((inclusionSequenceDiagram X hX).map (homOfLE (Nat.le_succ i))).hom =
        (inclusionSequenceStageMap X hX i).hom := by
    simpa using congrArg TopCat.Hom.hom (inclusionSequenceDiagram_map_succ X hX i)
  exact (congrArg (fun f ↦ f (γ t)) hmap).symm

/-- Helper for Lemma 9.4.15: transporting a generalized loop in two steps agrees with the direct
transport to the final stage. -/
private theorem transportedStageGenLoop_trans
    (X : ℕ → Set α) (hX : Monotone X) (x : X 0) {n i j k : ℕ}
    (hij : i ≤ j) (hjk : j ≤ k)
    (γ : Ω^ (Fin (n + 1)) (X i) (inclusionSequenceBasepoint X hX x i)) :
    transportedStageGenLoop X hX x (hij.trans hjk) γ =
      transportedStageGenLoop X hX x hjk (transportedStageGenLoop X hX x hij γ) := by
  -- Both transports are induced by the same composite stage map, so they agree pointwise.
  apply GenLoop.ext
  intro t
  symm
  simpa [transportedStageGenLoop, genLoopMap, ContinuousMap.comp_assoc] using
    congrArg (fun f ↦ f (γ t))
      (congrArg TopCat.Hom.hom
        ((inclusionSequenceDiagram X hX).map_comp (homOfLE hij) (homOfLE hjk)).symm)

/-- Helper for Lemma 9.4.15: the successor map in the homotopy-group diagram sends a class to the
class of the corresponding one-step transported generalized loop. -/
@[simp] private theorem inclusionSequenceHomotopyGroupStepMap_mk
    (X : ℕ → Set α) (hX : Monotone X) (n : ℕ) (x : X 0) (i : ℕ)
    (γ : Ω^ (Fin (n + 1)) (X i) (inclusionSequenceBasepoint X hX x i)) :
    inclusionSequenceHomotopyGroupStepMap X hX n x i
        (⟦γ⟧ : π_ (n + 1) (X i) (inclusionSequenceBasepoint X hX x i)) =
      (⟦transportedStageGenLoop X hX x (Nat.le_succ i) γ⟧ :
        π_ (n + 1) (X (i + 1)) (inclusionSequenceBasepoint X hX x (i + 1))) := by
  -- The successor map is the induced map of the stage inclusion, and the resulting generalized
  -- loop representative is exactly the one-step transport.
  change
    homotopyGroupMapOverEq ((inclusionSequenceStageMap X hX i).hom) rfl (n + 1) ⟦γ⟧ =
      (⟦transportedStageGenLoop X hX x (Nat.le_succ i) γ⟧ :
        π_ (n + 1) (X (i + 1)) (inclusionSequenceBasepoint X hX x (i + 1)))
  rw [homotopyGroupMapOverEq_mk]
  exact congrArg
    (fun δ ↦ (⟦δ⟧ :
      π_ (n + 1) (X (i + 1)) (inclusionSequenceBasepoint X hX x (i + 1))))
    (genLoopMapOverEqLoop_stageMap_eq_transportedStageGenLoop X hX x γ)

/-- Helper for Lemma 9.4.15: the `GrpCat` diagram map on a homotopy-group class is represented by
the corresponding transported generalized loop. -/
private theorem inclusionSequenceHomotopyGroupDiagram_map_mk
    (X : ℕ → Set α) (hX : Monotone X) (n : ℕ) (x : X 0) {i j : ℕ} (hij : i ≤ j)
    (γ : Ω^ (Fin (n + 1)) (X i) (inclusionSequenceBasepoint X hX x i)) :
    (inclusionSequenceHomotopyGroupDiagram X hX n x).map (homOfLE hij)
        (⟦γ⟧ : π_ (n + 1) (X i) (inclusionSequenceBasepoint X hX x i)) =
      (⟦transportedStageGenLoop X hX x hij γ⟧ :
        π_ (n + 1) (X j) (inclusionSequenceBasepoint X hX x j)) := by
  induction j, hij using Nat.le_induction with
  | base =>
      -- At a fixed stage the diagram map is the identity, and so is the transport.
      simp
  | succ j hij ih =>
      -- Decompose the forward map to `j + 1` into the map to `j` followed by the successor step.
      rw [← homOfLE_comp hij (Nat.le_succ j), Functor.map_comp]
      rw [CategoryTheory.comp_apply, ih, inclusionSequenceHomotopyGroupDiagram_map_succ]
      have hstep :=
        inclusionSequenceHomotopyGroupStepMap_mk X hX n x j
          (transportedStageGenLoop X hX x hij γ)
      have hproof : hij.trans (Nat.le_succ j) = Nat.le_succ_of_le hij :=
        Subsingleton.elim _ _
      -- Reassociate the representative with the direct transport to the final stage.
      calc
        inclusionSequenceHomotopyGroupStepMap X hX n x j
            ((⟦transportedStageGenLoop X hX x hij γ⟧ :
              π_ (n + 1) (X j) (inclusionSequenceBasepoint X hX x j))) =
          (⟦transportedStageGenLoop X hX x (Nat.le_succ j)
              (transportedStageGenLoop X hX x hij γ)⟧ :
            π_ (n + 1) (X (j + 1)) (inclusionSequenceBasepoint X hX x (j + 1))) := hstep
        _ = (⟦transportedStageGenLoop X hX x (Nat.le_succ_of_le hij) γ⟧ :
            π_ (n + 1) (X (j + 1)) (inclusionSequenceBasepoint X hX x (j + 1))) := by
          simpa [hproof] using
            congrArg
              (fun δ ↦ (⟦δ⟧ :
                π_ (n + 1) (X (j + 1)) (inclusionSequenceBasepoint X hX x (j + 1))))
              (transportedStageGenLoop_trans X hX x hij (Nat.le_succ j) γ).symm

/-- Helper for Lemma 9.4.15: a relative homotopy in the colimit that factors through stage `k`
induces a relative homotopy between the corresponding transported loops in any common later
stage. -/
private theorem factoredRelativeHomotopyCommonStage
    (X : ℕ → Set α) (hX : Monotone X) (x : X 0) (n : ℕ)
    {i j k m : ℕ} (him : i ≤ m) (hjm : j ≤ m) (hkm : k ≤ m)
    (γi : Ω^ (Fin (n + 1)) (X i) (inclusionSequenceBasepoint X hX x i))
    (γj : Ω^ (Fin (n + 1)) (X j) (inclusionSequenceBasepoint X hX x j))
    (F : ContinuousMap.HomotopyRel
      (genLoopMap ((inclusionSequenceColimitHom X i).hom) γi).1
      (genLoopMap ((inclusionSequenceColimitHom X j).hom) γj).1
      (Cube.boundary (Fin (n + 1))))
    (g : C(I × I^(Fin (n + 1)), X k))
    (hg : (inclusionSequenceColimitHom X k).hom.comp g = F.toContinuousMap) :
    GenLoop.Homotopic
      (transportedStageGenLoop X hX x him γi)
      (transportedStageGenLoop X hX x hjm γj) := by
  let stageHom : C(I × I^(Fin (n + 1)), X m) :=
    (((inclusionSequenceDiagram X hX).map (homOfLE hkm)).hom).comp g
  have hstage_zero :
      stageHom.curry 0 = (transportedStageGenLoop X hX x him γi).1 := by
    -- Compare the two endpoint maps after including them into the colimit, where both are
    -- identified by the factored homotopy and cocone naturality.
    ext z
    have hz :
        stageHom.curry 0 z = (transportedStageGenLoop X hX x him γi).1 z := by
      apply Lemma9415Support.inclusionSequenceColimitInclusion_injective X m
      calc
        inclusionSequenceColimitInclusion X m (stageHom (0, z)) =
            (inclusionSequenceColimitHom X k).hom (g (0, z)) := by
              change
                ((inclusionSequenceColimitHom X m).hom
                  (((inclusionSequenceDiagram X hX).map (homOfLE hkm)).hom (g (0, z)))) =
                  (inclusionSequenceColimitHom X k).hom (g (0, z))
              exact congrArg
                (fun f ↦ f (g (0, z)))
                (congrArg TopCat.Hom.hom
                  (Lemma9415Support.inclusionSequenceColimitHom_naturality_of_le X hX hkm))
        _ = F.toContinuousMap (0, z) := by
              simpa [stageHom, ContinuousMap.comp_apply] using congrArg (fun f ↦ f (0, z)) hg
        _ = (genLoopMap ((inclusionSequenceColimitHom X i).hom) γi).1 z := by
              simpa using F.apply_zero z
        _ = inclusionSequenceColimitInclusion X m
              ((transportedStageGenLoop X hX x him γi).1 z) := by
              change
                (inclusionSequenceColimitHom X i).hom (γi z) =
                  (inclusionSequenceColimitHom X m).hom
                    (((inclusionSequenceDiagram X hX).map (homOfLE him)).hom (γi z))
              symm
              exact congrArg
                (fun f ↦ f (γi z))
                (congrArg TopCat.Hom.hom
                  (Lemma9415Support.inclusionSequenceColimitHom_naturality_of_le X hX him))
    simpa using congrArg Subtype.val hz
  have hstage_one :
      stageHom.curry 1 = (transportedStageGenLoop X hX x hjm γj).1 := by
    -- The terminal face is handled identically using the right endpoint of the colimit homotopy.
    ext z
    have hz :
        stageHom.curry 1 z = (transportedStageGenLoop X hX x hjm γj).1 z := by
      apply Lemma9415Support.inclusionSequenceColimitInclusion_injective X m
      calc
        inclusionSequenceColimitInclusion X m (stageHom (1, z)) =
            (inclusionSequenceColimitHom X k).hom (g (1, z)) := by
              change
                ((inclusionSequenceColimitHom X m).hom
                  (((inclusionSequenceDiagram X hX).map (homOfLE hkm)).hom (g (1, z)))) =
                  (inclusionSequenceColimitHom X k).hom (g (1, z))
              exact congrArg
                (fun f ↦ f (g (1, z)))
                (congrArg TopCat.Hom.hom
                  (Lemma9415Support.inclusionSequenceColimitHom_naturality_of_le X hX hkm))
        _ = F.toContinuousMap (1, z) := by
              simpa [stageHom, ContinuousMap.comp_apply] using congrArg (fun f ↦ f (1, z)) hg
        _ = (genLoopMap ((inclusionSequenceColimitHom X j).hom) γj).1 z := by
              simpa using F.apply_one z
        _ = inclusionSequenceColimitInclusion X m
              ((transportedStageGenLoop X hX x hjm γj).1 z) := by
              change
                (inclusionSequenceColimitHom X j).hom (γj z) =
                  (inclusionSequenceColimitHom X m).hom
                    (((inclusionSequenceDiagram X hX).map (homOfLE hjm)).hom (γj z))
              symm
              exact congrArg
                (fun f ↦ f (γj z))
                (congrArg TopCat.Hom.hom
                  (Lemma9415Support.inclusionSequenceColimitHom_naturality_of_le X hX hjm))
    simpa using congrArg Subtype.val hz
  have hstage_boundary :
      ∀ t z, z ∈ Cube.boundary (Fin (n + 1)) → stageHom (t, z) = stageHom (0, z) := by
    -- On the boundary, the stage-factorized homotopy agrees with its initial face because the
    -- colimit homotopy is relative to the boundary and stage inclusion into the colimit is
    -- injective.
    intro t z hz
    apply Lemma9415Support.inclusionSequenceColimitInclusion_injective X m
    calc
      inclusionSequenceColimitInclusion X m (stageHom (t, z)) =
          F.toContinuousMap (t, z) := by
            calc
              inclusionSequenceColimitInclusion X m (stageHom (t, z)) =
                  (inclusionSequenceColimitHom X k).hom (g (t, z)) := by
                    change
                      ((inclusionSequenceColimitHom X m).hom
                        (((inclusionSequenceDiagram X hX).map (homOfLE hkm)).hom (g (t, z)))) =
                        (inclusionSequenceColimitHom X k).hom (g (t, z))
                    exact congrArg
                      (fun f ↦ f (g (t, z)))
                      (congrArg TopCat.Hom.hom
                        (Lemma9415Support.inclusionSequenceColimitHom_naturality_of_le X hX hkm))
              _ = F.toContinuousMap (t, z) := by
                    simpa [stageHom, ContinuousMap.comp_apply] using
                      congrArg (fun f ↦ f (t, z)) hg
      _ = F.toContinuousMap (0, z) := by
            exact (F.eq_fst t hz).trans (F.apply_zero z).symm
      _ = inclusionSequenceColimitInclusion X m (stageHom (0, z)) := by
            calc
              F.toContinuousMap (0, z) = (inclusionSequenceColimitHom X k).hom (g (0, z)) := by
                simpa [stageHom, ContinuousMap.comp_apply] using
                  (congrArg (fun f ↦ f (0, z)) hg).symm
              _ = inclusionSequenceColimitInclusion X m (stageHom (0, z)) := by
                change
                  (inclusionSequenceColimitHom X k).hom (g (0, z)) =
                    ((inclusionSequenceColimitHom X m).hom
                      (((inclusionSequenceDiagram X hX).map (homOfLE hkm)).hom (g (0, z))))
                exact
                  (congrArg
                    (fun f ↦ f (g (0, z)))
                    (congrArg TopCat.Hom.hom
                      (Lemma9415Support.inclusionSequenceColimitHom_naturality_of_le X hX hkm))).symm
  let Hstage :
      ContinuousMap.HomotopyRel (stageHom.curry 0) (stageHom.curry 1)
        (Cube.boundary (Fin (n + 1))) :=
    { toHomotopy := { stageHom with
        map_zero_left := by
          intro z
          rfl
        map_one_left := by
          intro z
          rfl }
      prop' := by
        intro t z hz
        exact hstage_boundary t z hz }
  -- Cast the stage-factorized homotopy to the transported endpoint loops proved above.
  exact ⟨ContinuousMap.HomotopyRel.cast Hstage hstage_zero hstage_one⟩

/-- Helper for Lemma 9.4.15: the comparison map from the filtered colimit of stage homotopy
groups to the homotopy group of the colimit space is injective once the compact cylinder domain
used by relative homotopies factors through finite stages. -/
private theorem colimitDesc_injective_of_compactCylinderFactorization
    (X : ℕ → Set α) (hX : Monotone X)
    (n : ℕ) (x : X 0)
    (hfactorCylinder :
      ∀ (f : C(ULift.{u} (I × I^(Fin (n + 1))), inclusionSequenceColimit X)),
        ∃ k, ∃ g : C(ULift.{u} (I × I^(Fin (n + 1))), X k),
          (inclusionSequenceColimitHom X k).hom.comp g = f)
    :
    Function.Injective (inclusionSequenceHomotopyGroupColimitDesc X hX n x) := by
  let F := inclusionSequenceHomotopyGroupDiagram X hX n x
  let FM := F ⋙ forget₂ GrpCat MonCat
  intro u v huv
  obtain ⟨i, ηi, rfl⟩ := M.mk_surjective FM u
  obtain ⟨j, ηj, rfl⟩ := M.mk_surjective FM v
  obtain ⟨γi, rfl⟩ := Quotient.mk_surjective ηi
  obtain ⟨γj, rfl⟩ := Quotient.mk_surjective ηj
  have hclasses :
      (⟦genLoopMapOverEqLoop ((inclusionSequenceColimitHom X i).hom)
          (inclusionSequenceColimitBasepoint_eq X hX x i) γi⟧ :
        π_ (n + 1) (inclusionSequenceColimit X) (inclusionSequenceColimitBasepoint X x)) =
      (⟦genLoopMapOverEqLoop ((inclusionSequenceColimitHom X j).hom)
          (inclusionSequenceColimitBasepoint_eq X hX x j) γj⟧ :
        π_ (n + 1) (inclusionSequenceColimit X) (inclusionSequenceColimitBasepoint X x)) := by
    have hiDesc :
        inclusionSequenceHomotopyGroupColimitDesc X hX n x
            (G.mk F ⟨i, (⟦γi⟧ :
              π_ (n + 1) (X i) (inclusionSequenceBasepoint X hX x i))⟩) =
          (⟦genLoopMapOverEqLoop ((inclusionSequenceColimitHom X i).hom)
              (inclusionSequenceColimitBasepoint_eq X hX x i) γi⟧ :
            π_ (n + 1) (inclusionSequenceColimit X)
              (inclusionSequenceColimitBasepoint X x)) := by
      calc
        inclusionSequenceHomotopyGroupColimitDesc X hX n x
            (G.mk F ⟨i, (⟦γi⟧ :
              π_ (n + 1) (X i) (inclusionSequenceBasepoint X hX x i))⟩) =
          inclusionSequenceHomotopyGroupCoconeMap X hX n x i
            (⟦γi⟧ : π_ (n + 1) (X i) (inclusionSequenceBasepoint X hX x i)) := by
              exact
                inclusionSequenceHomotopyGroupColimitDesc_apply_mk X hX n x i
                  (⟦γi⟧ : π_ (n + 1) (X i) (inclusionSequenceBasepoint X hX x i))
        _ =
          (⟦genLoopMapOverEqLoop ((inclusionSequenceColimitHom X i).hom)
              (inclusionSequenceColimitBasepoint_eq X hX x i) γi⟧ :
            π_ (n + 1) (inclusionSequenceColimit X)
              (inclusionSequenceColimitBasepoint X x)) := by
                exact homotopyGroupMapOverEq_mk
                  ((inclusionSequenceColimitHom X i).hom)
                  (inclusionSequenceColimitBasepoint_eq X hX x i)
                  (n + 1)
                  γi
    have hjDesc :
        inclusionSequenceHomotopyGroupColimitDesc X hX n x
            (G.mk F ⟨j, (⟦γj⟧ :
              π_ (n + 1) (X j) (inclusionSequenceBasepoint X hX x j))⟩) =
          (⟦genLoopMapOverEqLoop ((inclusionSequenceColimitHom X j).hom)
              (inclusionSequenceColimitBasepoint_eq X hX x j) γj⟧ :
            π_ (n + 1) (inclusionSequenceColimit X)
              (inclusionSequenceColimitBasepoint X x)) := by
      calc
        inclusionSequenceHomotopyGroupColimitDesc X hX n x
            (G.mk F ⟨j, (⟦γj⟧ :
              π_ (n + 1) (X j) (inclusionSequenceBasepoint X hX x j))⟩) =
          inclusionSequenceHomotopyGroupCoconeMap X hX n x j
            (⟦γj⟧ : π_ (n + 1) (X j) (inclusionSequenceBasepoint X hX x j)) := by
              exact
                inclusionSequenceHomotopyGroupColimitDesc_apply_mk X hX n x j
                  (⟦γj⟧ : π_ (n + 1) (X j) (inclusionSequenceBasepoint X hX x j))
        _ =
          (⟦genLoopMapOverEqLoop ((inclusionSequenceColimitHom X j).hom)
              (inclusionSequenceColimitBasepoint_eq X hX x j) γj⟧ :
            π_ (n + 1) (inclusionSequenceColimit X)
              (inclusionSequenceColimitBasepoint X x)) := by
                exact homotopyGroupMapOverEq_mk
                  ((inclusionSequenceColimitHom X j).hom)
                  (inclusionSequenceColimitBasepoint_eq X hX x j)
                  (n + 1)
                  γj
    -- Evaluate the comparison map on both stage generators and rewrite each side by the
    -- corresponding generalized-loop representative in the colimit.
    exact hiDesc.symm.trans (huv.trans hjDesc)
  rcases Quotient.exact hclasses with hhom
  rcases hhom with ⟨Hcolimit⟩
  let K := ULift.{u} (I × I^(Fin (n + 1)))
  let uliftHomeomorph : K ≃ₜ I × I^(Fin (n + 1)) := Homeomorph.ulift
  let downMap : C(K, I × I^(Fin (n + 1))) :=
    ⟨uliftHomeomorph, uliftHomeomorph.continuous_toFun⟩
  let fUp : C(K, inclusionSequenceColimit X) :=
    Hcolimit.toContinuousMap.comp downMap
  obtain ⟨k, gUp, hgUp⟩ := hfactorCylinder fUp
  let upMap : C(I × I^(Fin (n + 1)), K) :=
    ⟨uliftHomeomorph.symm, uliftHomeomorph.symm.continuous_toFun⟩
  let g : C(I × I^(Fin (n + 1)), X k) :=
    gUp.comp upMap
  have hg : (inclusionSequenceColimitHom X k).hom.comp g = Hcolimit.toContinuousMap := by
    ext z
    have hEval := congrArg (fun h : C(K, inclusionSequenceColimit X) ↦ h (ULift.up z)) hgUp
    simpa [g, fUp, upMap, downMap, ContinuousMap.comp_apply] using congrArg Subtype.val hEval
  let m : ℕ := max i (max j k)
  have him : i ≤ m := Nat.le_max_left _ _
  have hjm : j ≤ m := (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hkm : k ≤ m := (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hcommon :
      GenLoop.Homotopic
        (transportedStageGenLoop X hX x him γi)
        (transportedStageGenLoop X hX x hjm γj) :=
    factoredRelativeHomotopyCommonStage X hX x n him hjm hkm γi γj Hcolimit g hg
  have hmap :
      (inclusionSequenceHomotopyGroupDiagram X hX n x).map (homOfLE him)
          (⟦γi⟧ : π_ (n + 1) (X i) (inclusionSequenceBasepoint X hX x i)) =
        (inclusionSequenceHomotopyGroupDiagram X hX n x).map (homOfLE hjm)
          (⟦γj⟧ : π_ (n + 1) (X j) (inclusionSequenceBasepoint X hX x j)) := by
    have hcommonQuot :
        (⟦transportedStageGenLoop X hX x him γi⟧ :
          π_ (n + 1) (X m) (inclusionSequenceBasepoint X hX x m)) =
        (⟦transportedStageGenLoop X hX x hjm γj⟧ :
          π_ (n + 1) (X m) (inclusionSequenceBasepoint X hX x m)) :=
      Quotient.sound hcommon
    have hjMap :
        (inclusionSequenceHomotopyGroupDiagram X hX n x).map (homOfLE hjm)
            (⟦γj⟧ : π_ (n + 1) (X j) (inclusionSequenceBasepoint X hX x j)) =
          (⟦transportedStageGenLoop X hX x hjm γj⟧ :
            π_ (n + 1) (X m) (inclusionSequenceBasepoint X hX x m)) :=
      inclusionSequenceHomotopyGroupDiagram_map_mk X hX n x hjm γj
    -- Compare both diagram images in the common later stage by the factored cylinder homotopy.
    exact
      (inclusionSequenceHomotopyGroupDiagram_map_mk X hX n x him γi).trans
        (hcommonQuot.trans hjMap.symm)
  -- With both generators equal in a common later stage, the filtered-colimit quotient identifies
  -- the original two classes.
  exact G.mk_eq F
    ⟨i, (⟦γi⟧ : π_ (n + 1) (X i) (inclusionSequenceBasepoint X hX x i))⟩
    ⟨j, (⟦γj⟧ : π_ (n + 1) (X j) (inclusionSequenceBasepoint X hX x j))⟩
    ⟨m, homOfLE him, homOfLE hjm, hmap⟩

/-- Helper for Lemma 9.4.15: the comparison map from the filtered colimit of stage homotopy
groups to the homotopy group of the colimit space is injective. -/
private theorem inclusionSequenceHomotopyGroupColimitDesc_injective
    (X : ℕ → Set α) (hX : Monotone X)
    (n : ℕ) (hcylinder : inclusionSequenceColimitHasCompactCylinderFactorization X n)
    (x : X 0) :
    Function.Injective (inclusionSequenceHomotopyGroupColimitDesc X hX n x) := by
  exact colimitDesc_injective_of_compactCylinderFactorization X hX n x hcylinder

/-- The canonical map from the explicit colimit model sends the distinguished basepoint to the
stage-`0` basepoint of any cocone point. -/
private theorem inclusionSequenceColimitDesc_basepoint
    (X : ℕ → Set α) (hX : Monotone X) (s : Cocone (inclusionSequenceDiagram X hX))
    (x : X 0) :
    (inclusionSequenceColimitDesc hX s).hom (inclusionSequenceColimitBasepoint X x) =
      s.ι.app 0 x := by
  simpa [inclusionSequenceColimitBasepoint, inclusionSequenceColimitInclusion] using
    congrArg (fun f ↦ f x)
      (congrArg TopCat.Hom.hom (inclusionSequenceColimitDesc_fac hX s 0))

/-- Helper for Lemma 9.4.15: a homeomorphism induces an isomorphism on positive-degree homotopy
groups after aligning the basepoints. -/
private theorem homotopyGroupMonoidHomOverEq_isIso_of_homeomorph
    {A B : Type u} [TopologicalSpace A] [TopologicalSpace B]
    (h : A ≃ₜ B) {a : A} {b : B} (ha : h a = b) (n : ℕ) :
    IsIso
      (GrpCat.ofHom
        (homotopyGroupMonoidHomOverEq
          (f := ⟨h, h.continuous_toFun⟩)
          ha
          n)) := by
  let f : C(A, B) := ⟨h, h.continuous_toFun⟩
  let g : C(B, A) := ⟨h.symm, h.symm.continuous_toFun⟩
  have hb : g b = a := by
    exact (h.symm_apply_eq).2 ha.symm
  have hgf : g.comp f = ContinuousMap.id A := by
    ext x
    simp [f, g]
  have hfg : f.comp g = ContinuousMap.id B := by
    ext y
    simp [f, g]
  have hgfBase : (g.comp f) a = a := by
    simpa [ContinuousMap.comp_apply, f, g, ha] using hb
  have hfgBase : (f.comp g) b = b := by
    simpa [ContinuousMap.comp_apply, f, g, hb] using ha
  have hleft :
      Function.LeftInverse
        (homotopyGroupMapOverEq g hb (n + 1))
        (homotopyGroupMapOverEq f ha (n + 1)) := by
    intro η
    have hcomp :=
      homotopyGroupMapOverEq_comp f ha g hb (n + 1)
    have hcompη := congrFun hcomp η
    have hcongr :=
      homotopyGroupMapOverEq_congr hgf hgfBase rfl (n + 1)
    have hcongrη := congrFun hcongr η
    exact hcompη.trans <| hcongrη.trans <| by
      simpa using congrFun (homotopyGroupMapOverEq_id (a := a) (n + 1)) η
  have hright :
      Function.RightInverse
        (homotopyGroupMapOverEq g hb (n + 1))
        (homotopyGroupMapOverEq f ha (n + 1)) := by
    intro η
    have hcomp :=
      homotopyGroupMapOverEq_comp g hb f ha (n + 1)
    have hcompη := congrFun hcomp η
    have hcongr :=
      homotopyGroupMapOverEq_congr hfg hfgBase rfl (n + 1)
    have hcongrη := congrFun hcongr η
    exact hcompη.trans <| hcongrη.trans <| by
      simpa using congrFun (homotopyGroupMapOverEq_id (a := b) (n + 1)) η
  let hbij :
      Function.Bijective
        (homotopyGroupMonoidHomOverEq
          (f := f)
          ha
          n) :=
    ⟨hleft.injective, hright.surjective⟩
  let e :
      GrpCat.of (π_ (n + 1) A a) ≅
        GrpCat.of (π_ (n + 1) B b) :=
    (MulEquiv.ofBijective
      (homotopyGroupMonoidHomOverEq
        (f := f)
        ha
        n)
      hbij).toGrpIso
  change IsIso e.hom
  simpa [e, f] using (e.isIso_hom : IsIso e.hom)

/-- Helper for Lemma 9.4.15: the canonical map from the explicit colimit to another colimit
cocone point is exactly the cocone-uniqueness isomorphism. -/
private theorem inclusionSequenceColimitDesc_eq_coconeIso_hom
    (X : ℕ → Set α) (hX : Monotone X)
    (s : Cocone (inclusionSequenceDiagram X hX)) (hs : IsColimit s) :
    inclusionSequenceColimitDesc hX s =
      ((inclusionSequenceColimitCoconeIsColimit hX).coconePointUniqueUpToIso hs).hom := by
  let e := (inclusionSequenceColimitCoconeIsColimit hX).coconePointUniqueUpToIso hs
  -- Both maps out of the explicit colimit agree on every stage leg, so colimit uniqueness
  -- identifies them.
  symm
  exact inclusionSequenceColimitDesc_uniq hX s e.hom fun i ↦ by
    simpa [e] using
      Limits.IsColimit.comp_coconePointUniqueUpToIso_hom
        (inclusionSequenceColimitCoconeIsColimit hX) hs i

/-- The canonical comparison morphism from the filtered colimit of stage homotopy groups to the
positive-degree homotopy group of any cocone point of the sequential diagram. -/
noncomputable def sequentialColimitHomotopyGroupColimitDesc
    (X : ℕ → Set α) (hX : Monotone X)
    (s : Cocone (inclusionSequenceDiagram X hX)) (n : ℕ) (x : X 0) :
    inclusionSequenceHomotopyGroupColimit X hX n x ⟶
      GrpCat.of (π_ (n + 1) s.pt (s.ι.app 0 x)) :=
  inclusionSequenceHomotopyGroupColimitDesc X hX n x ≫
    GrpCat.ofHom
      (homotopyGroupMonoidHomOverEq
        (inclusionSequenceColimitDesc hX s).hom
        (inclusionSequenceColimitDesc_basepoint X hX s x) n)

/-- Lemma 9.4.15: if `s` is a colimit cocone for a sequential diagram of inclusions
`X i ↪ X (i + 1)`, then the canonical comparison morphism
`colim_i π_ (n + 1) (X i) ⟶ π_ (n + 1) (s.pt)` is an isomorphism in `GrpCat`
for the basepoint `s.ι.app 0 x` induced by `x : X 0`.

The explicit final-topology union `inclusionSequenceColimit X` from Construction 5.2.5 remains
the supporting concrete model used by the specialization below, but it is not part of the public
hypothesis list of the source-facing statement.

This formalizes the source's `π_n` statement in positive degree using `π_ (n + 1)`. -/
instance sequentialColimitHomotopyGroupColimitDesc_isIso
    (X : ℕ → Set α) (hX : Monotone X)
    (s : Cocone (inclusionSequenceDiagram X hX)) (hs : IsColimit s)
    (hloop : ∀ q, inclusionSequenceColimitHasCompactLoopFactorization X q)
    (hcylinder : ∀ q, inclusionSequenceColimitHasCompactCylinderFactorization X q)
    (n : ℕ)
    (x : X 0) :
    IsIso (sequentialColimitHomotopyGroupColimitDesc X hX s n x) := by
  -- TODO: the remaining blocker is statement-side. The explicit-model proof below needs
  -- compact-source factorization hypotheses, but the public cocone theorem currently has no
  -- hypotheses from which those side conditions can be recovered.
  sorry

/-- Supporting specialization to the explicit final-topology union model
`inclusionSequenceColimit X` in the compactly generated weak Hausdorff setting of
Proposition 5.2.6. -/
instance inclusionSequenceHomotopyGroupColimitDesc_isIso
    (X : ℕ → Set α) (hX : Monotone X)
    (hcg : ∀ i, CompactlyGeneratedWeakHausdorffSpace.{u, u} (X i))
    (hclosed : ∀ i, IsClosed {x : X (i + 1) | x.1 ∈ X i})
    (hloop : ∀ q, inclusionSequenceColimitHasCompactLoopFactorization X q)
    (hcylinder : ∀ q, inclusionSequenceColimitHasCompactCylinderFactorization X q)
    (n : ℕ)
    (x : X 0) :
    IsIso (inclusionSequenceHomotopyGroupColimitDesc X hX n x) := by
  -- TODO: the compact loop/cylinder factorization route proposed for this specialization is not
  -- valid under only `hcg` and `hclosed`; even simple closed filtrations of `[0,1]` show those
  -- factorization statements are false for cube representatives. A different proof or stronger
  -- hypotheses are needed.
  sorry
