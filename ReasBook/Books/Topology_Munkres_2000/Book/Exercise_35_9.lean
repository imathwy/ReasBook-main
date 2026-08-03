module

public import Mathlib.Topology.Coherent
public import Mathlib.Topology.TietzeExtension

public section

open Set

namespace Topology.CoherentSequence

universe u v

variable {X : Type u} (S : ℕ → Set X)
  (t : (n : ℕ) → TopologicalSpace (S n))

/-- The source-semantic conditions for an increasing closed exhaustion by independently
topologized stages. -/
class IsClosedExhaustion : Prop where
  cover : ⋃ n, S n = Set.univ
  monotone : Monotone S
  induced_succ (n : ℕ) :
    t n = TopologicalSpace.induced (Set.inclusion (monotone (Nat.le_succ n))) (t (n + 1))
  isClosed_succ (n : ℕ) :
    IsClosed[t (n + 1)] (Subtype.val ⁻¹' S n)

/-- The closed-exhaustion condition is equivalent to its four defining properties. -/
theorem isClosedExhaustion_iff :
    IsClosedExhaustion S t ↔
      ∃ h : Monotone S,
        (⋃ n, S n = Set.univ) ∧
        (∀ n, t n = TopologicalSpace.induced (Set.inclusion (h (Nat.le_succ n))) (t (n + 1))) ∧
        (∀ n, IsClosed[t (n + 1)] (Subtype.val ⁻¹' S n)) := by
  -- The existential formulation only makes the monotonicity witness explicit.
  constructor
  · intro h
    exact ⟨h.monotone, h.cover, h.induced_succ, h.isClosed_succ⟩
  · rintro ⟨hmon, hcover, hinduced, hclosed⟩
    exact ⟨hcover, hmon, hinduced, hclosed⟩

/-- The final topology for Exercise 35.9, declared by openness on every stage. -/
abbrev topology : TopologicalSpace X :=
  ⨆ n, TopologicalSpace.coinduced (Subtype.val : S n → X) (t n)

/-- Helper for Exercise 35.9: an earlier stage is closedly embedded in every later stage. -/
lemma isClosedEmbedding_inclusion [IsClosedExhaustion S t] {n m : ℕ} (h : n ≤ m) :
    let _ : TopologicalSpace (S n) := t n
    let _ : TopologicalSpace (S m) := t m
    Topology.IsClosedEmbedding
      (Set.inclusion (IsClosedExhaustion.monotone (S := S) (t := t) h)) := by
  -- Successor inclusions are closed embeddings by the exhaustion hypotheses.
  have hsucc (k : ℕ) :
      let _ : TopologicalSpace (S k) := t k
      let _ : TopologicalSpace (S (k + 1)) := t (k + 1)
      Topology.IsClosedEmbedding
        (Set.inclusion (IsClosedExhaustion.monotone (S := S) (t := t) (Nat.le_succ k))) := by
    letI : TopologicalSpace (S k) := t k
    letI : TopologicalSpace (S (k + 1)) := t (k + 1)
    refine ⟨⟨⟨IsClosedExhaustion.induced_succ k⟩,
      Set.inclusion_injective _⟩, ?_⟩
    rw [Set.range_inclusion]
    exact IsClosedExhaustion.isClosed_succ k
  -- Compose these successor embeddings along the inequality.
  induction m, h using Nat.le_induction with
  | base =>
      letI : TopologicalSpace (S n) := t n
      have hinclusion :
          Set.inclusion (IsClosedExhaustion.monotone (S := S) (t := t) (Nat.le_refl n)) =
            (id : S n → S n) := by
        funext x
        rfl
      rw [hinclusion]
      exact Topology.IsClosedEmbedding.id
  | succ m hnm hm =>
      letI : TopologicalSpace (S n) := t n
      letI : TopologicalSpace (S m) := t m
      letI : TopologicalSpace (S (m + 1)) := t (m + 1)
      rw [← Set.inclusion_comp_inclusion
        (IsClosedExhaustion.monotone (S := S) (t := t) hnm)
        (IsClosedExhaustion.monotone (S := S) (t := t) (Nat.le_succ m))]
      exact (hsucc m).comp hm

/-- Helper for Exercise 35.9: the image in the union of a closed stage subset is closed. -/
lemma isClosed_image_subtypeVal [IsClosedExhaustion S t] (n : ℕ) {C : Set (S n)}
    (hC : IsClosed[t n] C) :
    IsClosed[topology S t] ((Subtype.val : S n → X) '' C) := by
  -- Test the image on each coinduced stage and compare the two stage indices.
  rw [isClosed_iSup_iff]
  intro m
  rw [isClosed_coinduced]
  rcases le_total m n with hmn | hnm
  · have hpre :
        (Subtype.val : S m → X) ⁻¹' ((Subtype.val : S n → X) '' C) =
          Set.inclusion (IsClosedExhaustion.monotone (S := S) (t := t) hmn) ⁻¹' C := by
      ext x
      simp only [mem_preimage, mem_image]
      constructor
      · rintro ⟨y, hy, hxy⟩
        have : y = Set.inclusion
            (IsClosedExhaustion.monotone (S := S) (t := t) hmn) x := Subtype.ext hxy
        simpa only [this] using hy
      · intro hx
        exact ⟨Set.inclusion (IsClosedExhaustion.monotone (S := S) (t := t) hmn) x, hx, rfl⟩
    rw [hpre]
    exact hC.preimage (isClosedEmbedding_inclusion S t hmn).continuous
  · have himage :
        (Subtype.val : S m → X) ⁻¹' ((Subtype.val : S n → X) '' C) =
          Set.inclusion (IsClosedExhaustion.monotone (S := S) (t := t) hnm) '' C := by
      ext x
      simp only [mem_preimage, mem_image]
      constructor
      · rintro ⟨y, hy, hxy⟩
        exact ⟨y, hy, Subtype.ext hxy⟩
      · rintro ⟨y, hy, hxy⟩
        exact ⟨y, hy, congrArg Subtype.val hxy⟩
    rw [himage]
    exact (isClosedEmbedding_inclusion S t hnm).isClosedMap C hC

/-- Helper for Exercise 35.9: every stage is closedly embedded in the coherent union. -/
lemma isClosedEmbedding_subtypeVal [IsClosedExhaustion S t] (n : ℕ) :
    let _ : TopologicalSpace (S n) := t n
    let _ : TopologicalSpace X := topology S t
    Topology.IsClosedEmbedding (Subtype.val : S n → X) := by
  -- Continuity is supplied by the corresponding coinduced summand; closedness uses the image lemma.
  letI : TopologicalSpace (S n) := t n
  letI : TopologicalSpace X := topology S t
  refine Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
    (continuous_iSup_rng continuous_coinduced_rng) Subtype.val_injective ?_
  intro C hC
  exact isClosed_image_subtypeVal S t n hC

/-- The final topology in Exercise 35.9 is coherent with the family of stages. -/
theorem isCoherentWith [IsClosedExhaustion S t] :
    let _ : TopologicalSpace X := topology S t
    Topology.IsCoherentWith (Set.range S) := by
  -- Closedness in the final topology is exactly stagewise closedness.
  letI : TopologicalSpace X := topology S t
  refine Topology.IsCoherentWith.of_isClosed fun C hC ↦ ?_
  rw [isClosed_iSup_iff]
  intro n
  rw [isClosed_coinduced]
  have hstage := hC (S n) ⟨n, rfl⟩
  letI : TopologicalSpace (S n) := t n
  rw [(isClosedEmbedding_subtypeVal S t n).isInducing.eq_induced]
  exact hstage

/-- Every stage in Exercise 35.9 has its given topology as the induced subspace topology. -/
theorem isInducing [IsClosedExhaustion S t] (n : ℕ) :
    let _ : TopologicalSpace (S n) := t n
    let _ : TopologicalSpace X := topology S t
    Topology.IsInducing (Subtype.val : S n → X) := by
  -- This is the inducing projection of the stage closed embedding.
  letI : TopologicalSpace (S n) := t n
  letI : TopologicalSpace X := topology S t
  exact (isClosedEmbedding_subtypeVal S t n).isInducing

/-- Every stage in Exercise 35.9 is closed in the coherent union. -/
theorem isClosed [IsClosedExhaustion S t] (n : ℕ) :
    IsClosed[topology S t] (S n) := by
  -- The range of the canonical stage embedding is the stage itself.
  letI : TopologicalSpace (S n) := t n
  letI : TopologicalSpace X := topology S t
  simpa only [Subtype.range_coe] using (isClosedEmbedding_subtypeVal S t n).isClosed_range

/-- A map from the coherent union in Exercise 35.9 is continuous exactly when its
restriction to every stage is continuous. -/
theorem continuous_iff {Y : Type v} (tY : TopologicalSpace Y) (f : X → Y) :
    Continuous[topology S t, tY] f ↔
      ∀ n, Continuous[t n, tY] (f ∘ Subtype.val) := by
  simp only [continuous_iSup_dom, continuous_coinduced_dom]

/-- Helper for Exercise 35.9: a stagewise separator with values in `Set.Icc 0 1`. -/
structure StageSeparator (A B : Set X) (n : ℕ) where
  toContinuousMap : @ContinuousMap (S n) ℝ (t n) inferInstance
  eq_zero : Set.EqOn toContinuousMap 0 ((Subtype.val : S n → X) ⁻¹' A)
  eq_one : Set.EqOn toContinuousMap 1 ((Subtype.val : S n → X) ⁻¹' B)
  mem_Icc : ∀ x, toContinuousMap x ∈ Set.Icc (0 : ℝ) 1

/-- Helper for Exercise 35.9: a stage separator exists on the initial stage. -/
lemma exists_stageSeparator_zero [IsClosedExhaustion S t]
    [∀ n, let _ : TopologicalSpace (S n) := t n; T4Space (S n)]
    {A B : Set X} (hA : IsClosed[topology S t] A) (hB : IsClosed[topology S t] B)
    (hAB : Disjoint A B) : Nonempty (StageSeparator S t A B 0) := by
  -- Restrict the two global closed sets and apply Urysohn's lemma on the first stage.
  letI : TopologicalSpace (S 0) := t 0
  letI : TopologicalSpace X := topology S t
  have hA0 : IsClosed ((Subtype.val : S 0 → X) ⁻¹' A) :=
    hA.preimage (isClosedEmbedding_subtypeVal S t 0).continuous
  have hB0 : IsClosed ((Subtype.val : S 0 → X) ⁻¹' B) :=
    hB.preimage (isClosedEmbedding_subtypeVal S t 0).continuous
  have hAB0 : Disjoint ((Subtype.val : S 0 → X) ⁻¹' A)
      ((Subtype.val : S 0 → X) ⁻¹' B) := hAB.preimage _
  obtain ⟨f, hfA, hfB, hfIcc⟩ :=
    exists_continuous_zero_one_of_isClosed hA0 hB0 hAB0
  exact ⟨⟨f, hfA, hfB, hfIcc⟩⟩

/-- Helper for Exercise 35.9: a stage separator extends compatibly to the next stage. -/
lemma StageSeparator.exists_extension [IsClosedExhaustion S t]
    [∀ n, let _ : TopologicalSpace (S n) := t n; T4Space (S n)]
    {A B : Set X} (hA : IsClosed[topology S t] A) (hB : IsClosed[topology S t] B)
    (hAB : Disjoint A B) {n : ℕ} (f : StageSeparator S t A B n) :
    ∃ g : StageSeparator S t A B (n + 1),
      g.toContinuousMap ∘ Set.inclusion
        (IsClosedExhaustion.monotone (S := S) (t := t) (Nat.le_succ n)) =
        f.toContinuousMap := by
  classical
  letI : TopologicalSpace (S n) := t n
  letI : TopologicalSpace (S (n + 1)) := t (n + 1)
  letI : TopologicalSpace X := topology S t
  let e : S n → S (n + 1) :=
    Set.inclusion (IsClosedExhaustion.monotone (S := S) (t := t) (Nat.le_succ n))
  let E : Set (S (n + 1)) := Set.range e
  let A' : Set (S (n + 1)) := (Subtype.val : S (n + 1) → X) ⁻¹' A
  let B' : Set (S (n + 1)) := (Subtype.val : S (n + 1) → X) ⁻¹' B
  have he : Topology.IsClosedEmbedding e := isClosedEmbedding_inclusion S t (Nat.le_succ n)
  have hE : IsClosed E := he.isClosed_range
  have hA' : IsClosed A' := hA.preimage (isClosedEmbedding_subtypeVal S t (n + 1)).continuous
  have hB' : IsClosed B' := hB.preimage (isClosedEmbedding_subtypeVal S t (n + 1)).continuous
  have hAB' : Disjoint A' B' := hAB.preimage _
  -- First extend the old map, retaining the interval bound.
  obtain ⟨F, hFIcc, hFf⟩ :=
    f.toContinuousMap.exists_extension_forall_mem_of_isClosedEmbedding
      (t := Set.Icc (0 : ℝ) 1) f.mem_Icc ⟨0, by norm_num⟩ he
  let q : S (n + 1) → ℝ := E.piecewise F (A'.piecewise 0 1)
  have hqE : Set.EqOn q F E := Set.piecewise_eqOn E F (A'.piecewise 0 1)
  have hqA : Set.EqOn q 0 A' := by
    intro x hxA
    change E.piecewise F (A'.piecewise 0 1) x = 0
    by_cases hxE : x ∈ E
    · rw [Set.piecewise_eq_of_mem E F (A'.piecewise 0 1) hxE]
      obtain ⟨y, rfl⟩ := hxE
      have hFy : F (e y) = f.toContinuousMap y := congr_fun hFf y
      rw [hFy]
      exact f.eq_zero (show (y : X) ∈ A by exact hxA)
    · rw [Set.piecewise_eq_of_notMem E F (A'.piecewise 0 1) hxE,
        @Set.piecewise_eq_of_mem _ _ A' _ _ _ _ hxA]
      rfl
  have hqB : Set.EqOn q 1 B' := by
    intro x hxB
    change E.piecewise F (A'.piecewise 0 1) x = 1
    by_cases hxE : x ∈ E
    · rw [Set.piecewise_eq_of_mem E F (A'.piecewise 0 1) hxE]
      obtain ⟨y, rfl⟩ := hxE
      have hFy : F (e y) = f.toContinuousMap y := congr_fun hFf y
      rw [hFy]
      exact f.eq_one (show (y : X) ∈ B by exact hxB)
    · have hxA : x ∉ A' := fun hxA ↦ Set.disjoint_left.1 hAB' hxA hxB
      rw [Set.piecewise_eq_of_notMem E F (A'.piecewise 0 1) hxE,
        @Set.piecewise_eq_of_notMem _ _ A' _ _ _ _ hxA]
      rfl
  have hqContinuous : ContinuousOn q (E ∪ A' ∪ B') := by
    have hqEContinuous : ContinuousOn q E := F.continuous.continuousOn.congr hqE
    have hqAContinuous : ContinuousOn q A' := continuousOn_const.congr hqA
    have hqBContinuous : ContinuousOn q B' := continuousOn_const.congr hqB
    exact (hqEContinuous.union_of_isClosed hqAContinuous hE hA').union_of_isClosed
      hqBContinuous (hE.union hA') hB'
  let D : Set (S (n + 1)) := E ∪ A' ∪ B'
  let qD : C(D, ℝ) := ⟨D.restrict q, hqContinuous.restrict⟩
  have hqDIcc : ∀ x, qD x ∈ Set.Icc (0 : ℝ) 1 := by
    rintro x
    rcases x with ⟨x, hx⟩
    change x ∈ (E ∪ A') ∪ B' at hx
    rcases hx with (hxE | hxA) | hxB
    · rw [show qD ⟨x, Or.inl (Or.inl hxE)⟩ = F x by exact hqE hxE]
      exact hFIcc x
    · rw [show qD ⟨x, Or.inl (Or.inr hxA)⟩ = 0 by exact hqA hxA]
      norm_num
    · rw [show qD ⟨x, Or.inr hxB⟩ = 1 by exact hqB hxB]
      norm_num
  -- Extend the glued closed-union map to the whole next stage.
  obtain ⟨g, hgIcc, hgq⟩ := qD.exists_restrict_eq_forall_mem_of_closed
    (t := Set.Icc (0 : ℝ) 1) hqDIcc ⟨0, by norm_num⟩ ((hE.union hA').union hB')
  refine ⟨⟨g, ?_, ?_, hgIcc⟩, ?_⟩
  · intro x hxA
    have hxD : x ∈ D := by
      change x ∈ (E ∪ A') ∪ B'
      exact Or.inl (Or.inr hxA)
    calc
      g x = qD ⟨x, hxD⟩ := congrArg (fun k : C(D, ℝ) ↦ k ⟨x, hxD⟩) hgq
      _ = 0 := hqA hxA
  · intro x hxB
    have hxD : x ∈ D := by
      change x ∈ (E ∪ A') ∪ B'
      exact Or.inr hxB
    simpa only [ContinuousMap.restrict_apply, qD, Set.restrict_apply] using
      congrArg (fun k : C(D, ℝ) ↦ k ⟨x, hxD⟩) hgq |>.trans (hqB hxB)
  · funext x
    have hxE : e x ∈ E := ⟨x, rfl⟩
    have hxD : e x ∈ D := by
      change e x ∈ (E ∪ A') ∪ B'
      exact Or.inl (Or.inl hxE)
    calc
      g (e x) = qD ⟨e x, hxD⟩ := by
        exact congrArg (fun k : C(D, ℝ) ↦ k ⟨e x, hxD⟩) hgq
      _ = F (e x) := hqE hxE
      _ = f.toContinuousMap x := congr_fun hFf x

/-- Exercise 35.9: A coherent increasing union of closed normal stages is normal. -/
instance instT4Space [IsClosedExhaustion S t]
    [∀ n, let _ : TopologicalSpace (S n) := t n; T4Space (S n)] :
    let _ : TopologicalSpace X := topology S t
    T4Space X := by
  classical
  letI : TopologicalSpace X := topology S t
  -- Every point lies in a stage, where its singleton is closed.
  have hT1 : T1Space X := by
    refine ⟨fun x ↦ ?_⟩
    have hxcover : ∃ n, x ∈ S n := by
      have hx : x ∈ ⋃ n, S n := by
        rw [IsClosedExhaustion.cover (S := S) (t := t)]
        exact Set.mem_univ x
      simpa only [Set.mem_iUnion] using hx
    obtain ⟨n, hxn⟩ := hxcover
    letI : TopologicalSpace (S n) := t n
    have himage : (Subtype.val : S n → X) '' ({⟨x, hxn⟩} : Set (S n)) = {x} := by
      ext y
      simp only [mem_image, mem_singleton_iff]
      constructor
      · rintro ⟨z, rfl, rfl⟩
        rfl
      · intro hy
        subst y
        exact ⟨⟨x, hxn⟩, rfl, rfl⟩
    rw [← himage]
    exact isClosed_image_subtypeVal S t n isClosed_singleton
  letI : T1Space X := hT1
  let normal : NormalSpace X := ⟨fun A B hA hB hAB ↦ by
  -- Recursively choose compatible Urysohn separators on all stages.
  let f0 : StageSeparator S t A B 0 := Classical.choice
    (exists_stageSeparator_zero S t hA hB hAB)
  let next (n : ℕ) (f : StageSeparator S t A B n) : StageSeparator S t A B (n + 1) :=
    Classical.choose (f.exists_extension S t hA hB hAB)
  let fs : (n : ℕ) → StageSeparator S t A B n :=
    fun n ↦ Nat.rec f0 (fun n f ↦ next n f) n
  have hnext (n : ℕ) :
      (fs (n + 1)).toContinuousMap ∘ Set.inclusion
        (IsClosedExhaustion.monotone (S := S) (t := t) (Nat.le_succ n)) =
        (fs n).toContinuousMap := by
    exact Classical.choose_spec ((fs n).exists_extension S t hA hB hAB)
  have hcompatible {n m : ℕ} (hnm : n ≤ m) (x : X) (hxn : x ∈ S n) (hxm : x ∈ S m) :
      (fs n).toContinuousMap ⟨x, hxn⟩ = (fs m).toContinuousMap ⟨x, hxm⟩ := by
    induction m, hnm using Nat.le_induction with
    | base => rfl
    | succ m hnm ih =>
        have hxm' : x ∈ S m := IsClosedExhaustion.monotone (S := S) (t := t) hnm hxn
        calc
          (fs n).toContinuousMap ⟨x, hxn⟩ = (fs m).toContinuousMap ⟨x, hxm'⟩ :=
            ih hxm'
          _ = (fs (m + 1)).toContinuousMap ⟨x, hxm⟩ := by
            symm
            exact congr_fun (hnext m) ⟨x, hxm'⟩
  have hagree (n m : ℕ) (x : X) (hxn : x ∈ S n) (hxm : x ∈ S m) :
      (fs n).toContinuousMap ⟨x, hxn⟩ = (fs m).toContinuousMap ⟨x, hxm⟩ := by
    rcases le_total n m with hnm | hmn
    · exact hcompatible hnm x hxn hxm
    · exact (hcompatible hmn x hxm hxn).symm
  let g : X → ℝ := Set.liftCover S (fun n ↦ (fs n).toContinuousMap) hagree
    (IsClosedExhaustion.cover (S := S) (t := t))
  have hgContinuous : Continuous g := by
    rw [continuous_iff S t _ g]
    intro n
    letI : TopologicalSpace (S n) := t n
    have hrestrict : g ∘ Subtype.val = (fs n).toContinuousMap := by
      funext x
      exact Set.liftCover_coe (hS := IsClosedExhaustion.cover (S := S) (t := t)) x
    rw [hrestrict]
    exact (fs n).toContinuousMap.continuous
  have hgA : Set.EqOn g 0 A := by
    intro x hxA
    obtain ⟨n, hxn⟩ : ∃ n, x ∈ S n := by
      have hx : x ∈ ⋃ n, S n := by
        rw [IsClosedExhaustion.cover (S := S) (t := t)]
        exact Set.mem_univ x
      simpa only [Set.mem_iUnion] using hx
    rw [show g x = (fs n).toContinuousMap ⟨x, hxn⟩ by
      exact Set.liftCover_coe (hS := IsClosedExhaustion.cover (S := S) (t := t)) ⟨x, hxn⟩]
    exact (fs n).eq_zero hxA
  have hgB : Set.EqOn g 1 B := by
    intro x hxB
    obtain ⟨n, hxn⟩ : ∃ n, x ∈ S n := by
      have hx : x ∈ ⋃ n, S n := by
        rw [IsClosedExhaustion.cover (S := S) (t := t)]
        exact Set.mem_univ x
      simpa only [Set.mem_iUnion] using hx
    rw [show g x = (fs n).toContinuousMap ⟨x, hxn⟩ by
      exact Set.liftCover_coe (hS := IsClosedExhaustion.cover (S := S) (t := t)) ⟨x, hxn⟩]
    exact (fs n).eq_one hxB
  -- The inverse images of the two half-lines are disjoint open neighborhoods.
  refine ⟨g ⁻¹' Set.Iio (1 / 2 : ℝ), g ⁻¹' Set.Ioi (1 / 2 : ℝ),
    isOpen_Iio.preimage hgContinuous, isOpen_Ioi.preimage hgContinuous, ?_, ?_, ?_⟩
  · intro x hxA
    change g x < (1 / 2 : ℝ)
    rw [hgA hxA]
    norm_num
  · intro x hxB
    change (1 / 2 : ℝ) < g x
    rw [hgB hxB]
    norm_num
  · exact (Set.Ioi_disjoint_Iio_same.preimage g).symm
  ⟩
  letI : NormalSpace X := normal
  exact T4Space.mk

end Topology.CoherentSequence
