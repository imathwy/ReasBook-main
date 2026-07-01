import Mathlib

open scoped DirectSum
open HomogeneousIdeal

universe u v w

section

/- Domain triage:
* source-facing: graded Nakayama over the irrelevant ideal for `ℤ`-graded modules.
* core/canonical owners: `HomogeneousIdeal.irrelevant`, `DirectSum.Decomposition`,
  `SetLike.GradedSMul`, and `LinearMap.reduceModIdeal`.
* bridge/view: reduction modulo the canonical ideal `S₊.toIdeal`.

Primitive data are the graded ring `𝒜`, the graded module pieces, and the canonical irrelevant
ideal `S₊`. The public theorems are source-facing graded Nakayama statements built from those
owners, not replacement owners for the ordinary ungraded Nakayama API.

Relevant owner declarations sampled for this refinement:
* `HomogeneousIdeal.irrelevant`
* `LinearMap.reduceModIdeal`
* `subsingleton_of_ideal_smul_top_eq_top_of_isNilpotent`
* `span_eq_top_of_quotient_span_eq_top_of_isNilpotent`

The last two give the same ungraded statement-shapes but are not exact replacements here: the
graded irrelevance hypothesis carries additional source-facing content.
-/

local instance : AddAction ℕ ℤ := AddAction.compHom ℤ Int.ofNatHom.toAddMonoidHom

variable {A : Type u} {M : Type v} {N : Type w}
variable [CommRing A]
variable [AddCommGroup M] [Module A M]
variable [AddCommGroup N] [Module A N]
variable (𝒜 : ℕ → Submodule A A)

local notation "S₊" => (HomogeneousIdeal.irrelevant 𝒜)

section GradedModule

variable (ℳ : ℤ → Submodule A M)
variable [GradedRing 𝒜] [DirectSum.Decomposition ℳ] [SetLike.GradedSMul 𝒜 ℳ]

/-- Helper for Lemma 10.56.1: the span of homogeneous elements is a homogeneous submodule. -/
lemma span_isHomogeneous_of_isHomogeneousElem {t : Set M}
    (ht : ∀ x ∈ t, SetLike.IsHomogeneousElem ℳ x) :
    (Submodule.span A t).IsHomogeneous ℳ := by
  intro i x hx
  -- Each generator contributes only its own homogeneous component, so span induction preserves
  -- closure under `DirectSum.decompose`.
  refine Submodule.span_induction
    (p := fun y _ => ((DirectSum.decompose ℳ y i : ℳ i) : M) ∈ Submodule.span A t) ?_ ?_ ?_ ?_ hx
  · intro y hy
    rcases ht y hy with ⟨j, hj⟩
    by_cases hji : j = i
    · subst hji
      simpa [DirectSum.decompose_of_mem_same ℳ hj] using
        (Submodule.subset_span hy : y ∈ Submodule.span A t)
    · simpa [DirectSum.decompose_of_mem_ne ℳ hj hji] using
        (Submodule.zero_mem (Submodule.span A t))
  · simpa using (Submodule.zero_mem (Submodule.span A t))
  · intro y z _ _ hy hz
    simpa [DirectSum.decompose_add] using (Submodule.add_mem (Submodule.span A t) hy hz)
  · intro a y _ hy
    simpa [map_smul] using (Submodule.smul_mem (Submodule.span A t) a hy)

/-- Helper for Lemma 10.56.1: a finitely generated homogeneous submodule admits a finite
homogeneous generating set. -/
lemma exists_finset_homogeneous_span_eq_of_isHomogeneous
    (P : Submodule A M) (hP : P.IsHomogeneous ℳ) (hPfg : P.FG) :
    ∃ s : Finset M,
      (∀ x ∈ s, SetLike.IsHomogeneousElem ℳ x) ∧
        (∀ x ∈ s, x ∈ P) ∧
          Submodule.span A (s : Set M) = P := by
  classical
  obtain ⟨t, htP⟩ := hPfg
  let s : Finset M :=
    t.biUnion fun x =>
      (DirectSum.decompose ℳ x).support.image fun i => (DirectSum.decompose ℳ x i : M)
  have hs_homogeneous : ∀ x ∈ s, SetLike.IsHomogeneousElem ℳ x := by
    intro x hx
    rcases Finset.mem_biUnion.mp hx with ⟨y, hy, hx⟩
    rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
    exact ⟨i, (DirectSum.decompose ℳ y i).2⟩
  have hs_mem : ∀ x ∈ s, x ∈ P := by
    intro x hx
    rcases Finset.mem_biUnion.mp hx with ⟨y, hy, hx⟩
    have hyP : y ∈ P := by
      rw [← htP]
      exact Submodule.subset_span hy
    rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
    exact (Submodule.IsHomogeneous.mem_iff ℳ hP).1 hyP i
  have hspan_le : Submodule.span A (t : Set M) ≤ Submodule.span A (s : Set M) := by
    refine Submodule.span_le.mpr ?_
    intro y hy
    -- Replace each original generator by the sum of its homogeneous components.
    rw [← DirectSum.sum_support_decompose ℳ y]
    refine Submodule.sum_mem _ fun i hi => ?_
    exact Submodule.subset_span <| by
      exact Finset.mem_biUnion.mpr ⟨y, hy, Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩
  refine ⟨s, hs_homogeneous, hs_mem, le_antisymm ?_ ?_⟩
  · refine Submodule.span_le.mpr ?_
    intro x hx
    exact hs_mem x hx
  · rw [← htP]
    exact hspan_le

/-- Helper for Lemma 10.56.1: a chosen homogeneous degree witness for a homogeneous element. -/
noncomputable def homogeneousDegree (x : M) (hx : SetLike.IsHomogeneousElem ℳ x) : ℤ :=
  Classical.choose hx

/-- Helper for Lemma 10.56.1: the chosen degree witness places the element in the corresponding
graded piece. -/
lemma homogeneousDegree_mem (x : M) (hx : SetLike.IsHomogeneousElem ℳ x) :
    x ∈ ℳ (homogeneousDegree ℳ x hx) :=
  Classical.choose_spec hx

/-- Helper for Lemma 10.56.1: the chosen homogeneous degree recovers the unique nonzero
homogeneous component. -/
lemma decompose_homogeneousDegree_eq (x : M) (hx : SetLike.IsHomogeneousElem ℳ x) :
    DirectSum.decompose ℳ x (homogeneousDegree ℳ x hx) = x := by
  simpa using DirectSum.decompose_of_mem_same ℳ (homogeneousDegree_mem ℳ x hx)

/-- Helper for Lemma 10.56.1: a positive ring degree shifts a module degree strictly upward. -/
lemma positive_vadd_ne_of_le {i : ℕ} {d e : ℤ} (hi : 0 < i) (hde : d ≤ e) :
    i +ᵥ e ≠ d := by
  change (i : ℤ) + e ≠ d
  have hi' : (0 : ℤ) < i := by exact_mod_cast hi
  linarith

/-- Helper for Lemma 10.56.1: a positive-degree homogeneous scalar moves a homogeneous vector
strictly above every weakly smaller degree component. -/
lemma decompose_single_homogeneous_smul_component_eq_zero
    {a : A} {i : ℕ} (ha : a ∈ 𝒜 i)
    {y : M} {e d : ℤ} (hy : y ∈ ℳ e)
    (hi : 0 < i) (hd : d ≤ e) :
    ((DirectSum.decompose ℳ ((a : A) • y) d : ℳ d) : M) = 0 := by
  -- A homogeneous scalar of positive degree shifts `y` into degree `i + e`.
  have hsmul : (a • y) ∈ ℳ (i +ᵥ e) := SetLike.GradedSMul.smul_mem ha hy
  -- Since `d ≤ e`, the shifted degree cannot equal `d`, so the `d`-component vanishes.
  simpa using
    (DirectSum.decompose_of_mem_ne ℳ hsmul (positive_vadd_ne_of_le hi hd))

/-- Helper for Lemma 10.56.1: an irrelevant coefficient kills every component at or below the
degree of a homogeneous element. -/
lemma decompose_irrelevant_smul_homogeneous_eq_zero
    {y : M} (hy : SetLike.IsHomogeneousElem ℳ y)
    {d : ℤ} (hd : d ≤ homogeneousDegree ℳ y hy)
    {r : A} (hr : r ∈ S₊.toIdeal) :
    ((DirectSum.decompose ℳ (r • y) d : ℳ d) : M) = 0 := by
  classical
  let e : ℤ := homogeneousDegree ℳ y hy
  have hy_mem : y ∈ ℳ e := homogeneousDegree_mem ℳ y hy
  have hr0 : ((DirectSum.decompose 𝒜 r 0 : 𝒜 0) : A) = 0 := by
    -- Membership in the irrelevant ideal exactly says the degree-zero coefficient vanishes.
    have hproj0 : GradedRing.proj 𝒜 0 r = 0 := by
      simpa [HomogeneousIdeal.mem_irrelevant_iff] using hr
    simpa [GradedRing.proj_apply] using hproj0
  have hsum :
      ∑ i ∈ (DirectSum.decompose 𝒜 r).support,
        (DirectSum.decompose ℳ ((((DirectSum.decompose 𝒜 r) i : 𝒜 i) : A) • y) d : ℳ d) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro i hi
    by_cases hi0 : i = 0
    · subst hi0
      -- The degree-zero coefficient is zero, so its scalar action contributes nothing.
      simp [hr0]
    · have hi_pos : 0 < i := Nat.pos_iff_ne_zero.mpr hi0
      -- Every positive-degree homogeneous coefficient shifts `y` strictly above degree `d`.
      apply Subtype.ext
      simpa using
        (decompose_single_homogeneous_smul_component_eq_zero (𝒜 := 𝒜) (ℳ := ℳ)
          (a := (((DirectSum.decompose 𝒜 r) i : 𝒜 i) : A))
          (ha := SetLike.coe_mem _)
          (hy := hy_mem) hi_pos hd)
  -- Route correction: expand `r` into homogeneous pieces first; this keeps the coercion bridge
  -- confined to the single-piece lemma above instead of inside a wider induction.
  rw [← DirectSum.sum_support_decompose 𝒜 r, Finset.sum_smul, DirectSum.decompose_sum]
  have happly :
      (((∑ i ∈ (DirectSum.decompose 𝒜 r).support,
          DirectSum.decompose ℳ ((((DirectSum.decompose 𝒜 r) i : 𝒜 i) : A) • y)) d : ℳ d)) =
        ∑ i ∈ (DirectSum.decompose 𝒜 r).support,
          (DirectSum.decompose ℳ ((((DirectSum.decompose 𝒜 r) i : 𝒜 i) : A) • y) d : ℳ d) := by
    simpa using
      (DFinsupp.finset_sum_apply
        ((DirectSum.decompose 𝒜 r).support)
        (fun i ↦ DirectSum.decompose ℳ ((((DirectSum.decompose 𝒜 r) i : 𝒜 i) : A) • y))
        d)
  rw [happly]
  simpa using congrArg (fun z : ℳ d ↦ (z : M)) hsum

/-- Helper for Lemma 10.56.1: for an element of the span, every irrelevant scalar has its
degree-`d` component inside a fixed homogeneous submodule once all generators outside the
submodule have degree at least `d`. -/
lemma decompose_irrelevant_smul_span_mem_of_min_degree
    {P : Submodule A M} (hP : P.IsHomogeneous ℳ)
    (s : Finset M)
    (hs_homogeneous : ∀ x ∈ s, SetLike.IsHomogeneousElem ℳ x)
    (d : ℤ)
    (hs_min :
      ∀ x, ∀ hx : x ∈ s, x ∉ P → d ≤ homogeneousDegree ℳ x (hs_homogeneous x hx))
    {y : M}
    (hy : y ∈ Submodule.span A (s : Set M))
    {r : A} (hr : r ∈ S₊.toIdeal) :
    ((DirectSum.decompose ℳ (r • y) d : ℳ d) : M) ∈ P := by
  -- Keep the irrelevant coefficient quantified while we induct on the span expression for `y`.
  have hspan :
      ∀ {y : M}, y ∈ Submodule.span A (s : Set M) →
        ∀ {r : A}, r ∈ S₊.toIdeal ->
          ((DirectSum.decompose ℳ (r • y) d : ℳ d) : M) ∈ P := by
    refine Submodule.span_induction
      (p := fun y _ ↦ ∀ {r : A}, r ∈ S₊.toIdeal ->
        ((DirectSum.decompose ℳ (r • y) d : ℳ d) : M) ∈ P) ?_ ?_ ?_ ?_
    · intro x hx r hr
      by_cases hxP : x ∈ P
      · -- If the generator already lies in `P`, then so do all homogeneous components of `r • x`.
        have hrx : r • x ∈ P := Submodule.smul_mem P r hxP
        exact (Submodule.IsHomogeneous.mem_iff ℳ hP).1 hrx d
      · -- Otherwise the minimal-degree hypothesis forces the relevant component to vanish.
        have hzero :
            ((DirectSum.decompose ℳ (r • x) d : ℳ d) : M) = 0 :=
          decompose_irrelevant_smul_homogeneous_eq_zero (𝒜 := 𝒜) (ℳ := ℳ)
            (y := x) (hy := hs_homogeneous x hx)
            (d := d) (hd := hs_min x hx hxP) (r := r) hr
        exact hzero ▸ P.zero_mem
    · intro r hr
      -- The zero vector contributes only the zero homogeneous component.
      simpa using (P.zero_mem : (0 : M) ∈ P)
    · intro y z hy' hz' hyP hzP r hr
      -- Additivity of `DirectSum.decompose` keeps the component inside `P`.
      simpa [smul_add, DirectSum.decompose_add] using Submodule.add_mem P (hyP hr) (hzP hr)
    · intro a y hy' hyP r hr
      -- Replace `r • (a • y)` by `(a * r) • y`, and keep the coefficient inside the ideal.
      have har : a * r ∈ S₊.toIdeal := Ideal.mul_mem_left _ _ hr
      simpa [smul_smul, mul_assoc, mul_comm, mul_left_comm] using (hyP har)
  exact hspan hy hr

/-- Helper for Lemma 10.56.1: the degree-`d` component of an element of `S₊ • span(s)` already
lies in a graded submodule whenever every generator outside that submodule has degree at least
`d`. -/
lemma decompose_mem_of_irrelevant_smul_span_of_min_degree
    {P : Submodule A M} (hP : P.IsHomogeneous ℳ)
    (s : Finset M)
    (hs_homogeneous : ∀ x ∈ s, SetLike.IsHomogeneousElem ℳ x)
    (d : ℤ)
    (hs_min :
      ∀ x, ∀ hx : x ∈ s, x ∉ P → d ≤ homogeneousDegree ℳ x (hs_homogeneous x hx))
    {z : M}
    (hz : z ∈ S₊.toIdeal • Submodule.span A (s : Set M)) :
    ((DirectSum.decompose ℳ z d : ℳ d) : M) ∈ P := by
  -- Route correction: once the stronger span lemma is available, the outer `S₊ • span(s)` layer is
  -- a direct `Submodule.smul_induction_on` with no new degree bookkeeping.
  refine Submodule.smul_induction_on hz ?_ ?_
  · intro r hr y hy
    exact decompose_irrelevant_smul_span_mem_of_min_degree (𝒜 := 𝒜) (ℳ := ℳ)
      (P := P) hP s hs_homogeneous d hs_min hy hr
  · intro y z hyP hzP
    -- The degree-`d` projection is additive on the ambient module.
    simpa [DirectSum.decompose_add] using Submodule.add_mem P hyP hzP

/-- Helper for Lemma 10.56.1: a minimal-degree homogeneous generator lying in `S₊ • span(s)` must
vanish. -/
lemma eq_zero_of_mem_irrelevant_smul_span_of_min_degree
    (s : Finset M)
    (hs_homogeneous : ∀ x ∈ s, SetLike.IsHomogeneousElem ℳ x)
    {x : M} (hx : x ∈ s)
    (hx_min :
      ∀ y, ∀ hy : y ∈ s, x ≠ y →
        homogeneousDegree ℳ x (hs_homogeneous x hx) ≤
          homogeneousDegree ℳ y (hs_homogeneous y hy))
    (hx_smul : x ∈ S₊.toIdeal • Submodule.span A (s : Set M)) :
    x = 0 := by
  by_cases hx_zero : x = 0
  · exact hx_zero
  -- Send the minimal generator to degree `homogeneousDegree x`; every other generator lies in a
  -- weakly larger degree, so the component lemma forces that degree piece to be zero.
  let d : ℤ := homogeneousDegree ℳ x (hs_homogeneous x hx)
  have hs_min_bot :
      ∀ y, ∀ hy : y ∈ s, y ∉ (⊥ : Submodule A M) →
        d ≤ homogeneousDegree ℳ y (hs_homogeneous y hy) := by
    intro y hy hy_ne_bot
    by_cases hxy : x = y
    · subst hxy
      exact le_rfl
    · exact hx_min y hy hxy
  have hcomponent_mem :
      ((DirectSum.decompose ℳ x d : ℳ d) : M) ∈ (⊥ : Submodule A M) :=
    decompose_mem_of_irrelevant_smul_span_of_min_degree (𝒜 := 𝒜) (ℳ := ℳ)
      (P := ⊥)
      (hP := by
        intro i y hy
        simp only [Submodule.mem_bot] at hy ⊢
        simpa [hy])
      s hs_homogeneous d hs_min_bot hx_smul
  have hcomponent_zero : ((DirectSum.decompose ℳ x d : ℳ d) : M) = 0 := by
    simpa using hcomponent_mem
  simpa [d, decompose_homogeneousDegree_eq ℳ x (hs_homogeneous x hx)] using hcomponent_zero

/-- Helper for Lemma 10.56.1: a homogeneous generator of minimal degree among those outside a
fixed homogeneous submodule already lies in that submodule once it belongs to
`P ⊔ S₊ • span(s)`. -/
lemma mem_of_mem_sup_irrelevant_smul_span_of_min_degree
    {P : Submodule A M} (hP : P.IsHomogeneous ℳ)
    (s : Finset M)
    (hs_homogeneous : ∀ x ∈ s, SetLike.IsHomogeneousElem ℳ x)
    {x : M} (hx : x ∈ s)
    (hx_min :
      ∀ y, ∀ hy : y ∈ s, y ∉ P →
        homogeneousDegree ℳ x (hs_homogeneous x hx) ≤
          homogeneousDegree ℳ y (hs_homogeneous y hy))
    (hx_sup : x ∈ P ⊔ S₊.toIdeal • Submodule.span A (s : Set M)) :
    x ∈ P := by
  let d : ℤ := homogeneousDegree ℳ x (hs_homogeneous x hx)
  have hs_min :
      ∀ y, ∀ hy : y ∈ s, y ∉ P → d ≤ homogeneousDegree ℳ y (hs_homogeneous y hy) := by
    intro y hy hyP
    simpa [d] using hx_min y hy hyP
  rcases Submodule.mem_sup.mp hx_sup with ⟨p, hp, z, hz, hx_eq⟩
  have hp_component : ((DirectSum.decompose ℳ p d : ℳ d) : M) ∈ P :=
    (Submodule.IsHomogeneous.mem_iff ℳ hP).1 hp d
  have hz_component : ((DirectSum.decompose ℳ z d : ℳ d) : M) ∈ P :=
    decompose_mem_of_irrelevant_smul_span_of_min_degree (𝒜 := 𝒜) (ℳ := ℳ)
      (P := P) hP s hs_homogeneous d hs_min hz
  have hx_component :
      ((DirectSum.decompose ℳ x d : ℳ d) : M) =
        ((DirectSum.decompose ℳ p d : ℳ d) : M) +
          ((DirectSum.decompose ℳ z d : ℳ d) : M) := by
    rw [← hx_eq, DirectSum.decompose_add]
    rfl
  have hx_self : ((DirectSum.decompose ℳ x d : ℳ d) : M) = x := by
    simpa [d] using decompose_homogeneousDegree_eq ℳ x (hs_homogeneous x hx)
  -- Project the decomposition to the minimal degree; both projected summands already lie in `P`.
  rw [← hx_self, hx_component]
  exact Submodule.add_mem P hp_component hz_component

/-- Helper for Lemma 10.56.1: if `P ⊔ S₊ • span(s) = ⊤` for a finite homogeneous generating set,
then every generator already lies in the homogeneous submodule `P`. -/
lemma le_of_homogeneous_span_sup_irrelevant_eq_top
    {P : Submodule A M} (hP : P.IsHomogeneous ℳ)
    (s : Finset M)
    (hs_homogeneous : ∀ x ∈ s, SetLike.IsHomogeneousElem ℳ x)
    (hspan : P ⊔ S₊.toIdeal • Submodule.span A (s : Set M) = ⊤) :
    Submodule.span A (s : Set M) ≤ P := by
  classical
  refine Submodule.span_le.mpr ?_
  intro x hx
  by_cases hxP : x ∈ P
  · exact hxP
  · let t : Finset M := s.filter fun y ↦ y ∉ P
    have ht_nonempty : t.Nonempty := by
      refine Finset.nonempty_iff_ne_empty.mpr ?_
      intro ht_empty
      have hx_t : x ∈ t := Finset.mem_filter.mpr ⟨hx, hxP⟩
      simpa [t, ht_empty] using hx_t
    obtain ⟨y, hy, hy_min⟩ :=
      Finset.exists_min_image t.attach
        (fun z : {z // z ∈ t} =>
          homogeneousDegree ℳ z.1 (hs_homogeneous z.1 (Finset.mem_filter.mp z.2).1))
        ht_nonempty.attach
    have hy_mem : y.1 ∈ s := (Finset.mem_filter.mp y.2).1
    have hy_not_mem : y.1 ∉ P := (Finset.mem_filter.mp y.2).2
    have hy_min' :
        ∀ z, ∀ hz : z ∈ s, z ∉ P →
          homogeneousDegree ℳ y.1 (hs_homogeneous y.1 hy_mem) ≤
            homogeneousDegree ℳ z (hs_homogeneous z hz) := by
      intro z hz hzP
      exact hy_min ⟨z, Finset.mem_filter.mpr ⟨hz, hzP⟩⟩ (by simp)
    have hy_sup : y.1 ∈ P ⊔ S₊.toIdeal • Submodule.span A (s : Set M) := by
      rw [hspan]
      exact Submodule.mem_top
    have hy_memP : y.1 ∈ P :=
      mem_of_mem_sup_irrelevant_smul_span_of_min_degree (𝒜 := 𝒜) (ℳ := ℳ)
        (P := P) hP s hs_homogeneous hy_mem hy_min' hy_sup
    exact False.elim <| hy_not_mem hy_memP

/-- Helper for Lemma 10.56.1: if a finite homogeneous generating set spans `M` and `S₊ M = M`,
then the module is trivial. -/
lemma subsingleton_of_homogeneous_span_eq_top_of_irrelevant
    (s : Finset M)
    (hs_homogeneous : ∀ x ∈ s, SetLike.IsHomogeneousElem ℳ x)
    (hspan : Submodule.span A (s : Set M) = ⊤)
    (hM : S₊.toIdeal • (⊤ : Submodule A M) = ⊤) :
    Subsingleton M := by
  classical
  -- Strong induction on the number of chosen homogeneous generators.
  induction hs_card : s.card using Nat.strong_induction_on generalizing s with
  | h n ih =>
      subst hs_card
      by_cases hs_empty : s = ∅
      · have hbot_top : (⊥ : Submodule A M) = ⊤ := by
          simpa [hs_empty] using hspan
        have hsubmodules : Subsingleton (Submodule A M) := subsingleton_of_bot_eq_top hbot_top
        exact (Submodule.subsingleton_iff A).mp hsubmodules
      · have hs_nonempty : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr hs_empty
        obtain ⟨x, hx, hx_min⟩ :=
          Finset.exists_min_image s.attach
            (fun z : {z // z ∈ s} => homogeneousDegree ℳ z.1 (hs_homogeneous z.1 z.2))
            hs_nonempty.attach
        have hx_mem : x.1 ∈ s := x.2
        have hx_min' :
            ∀ y, ∀ hy : y ∈ s, x.1 ≠ y →
              homogeneousDegree ℳ x.1 (hs_homogeneous x.1 hx_mem) ≤
                homogeneousDegree ℳ y (hs_homogeneous y hy) := by
          intro y hy hxy
          exact hx_min ⟨y, hy⟩ (by simp)
        have hx_smul :
            x.1 ∈ S₊.toIdeal • Submodule.span A (s : Set M) := by
          simpa [hspan] using (show x.1 ∈ S₊.toIdeal • (⊤ : Submodule A M) from by
            rw [hM]
            exact Submodule.mem_top)
        have hx_zero :
            x.1 = 0 :=
          eq_zero_of_mem_irrelevant_smul_span_of_min_degree (𝒜 := 𝒜) (ℳ := ℳ)
            s hs_homogeneous hx_mem hx_min' hx_smul
        have hspan_erase_le :
            Submodule.span A (s : Set M) ≤ Submodule.span A ((s.erase x.1 : Finset M) : Set M) := by
          refine Submodule.span_le.mpr ?_
          intro y hy
          by_cases hxy : y = x.1
          · subst hxy
            rw [hx_zero]
            exact Submodule.zero_mem _
          · exact Submodule.subset_span <| Finset.mem_erase.mpr ⟨hxy, hy⟩
        have hspan_erase : Submodule.span A ((s.erase x.1 : Finset M) : Set M) = ⊤ := by
          apply top_unique
          simpa [hspan] using hspan_erase_le
        have hcard_erase : (s.erase x.1).card < s.card := by
          simpa using Finset.card_erase_lt_of_mem hx_mem
        have hs_homogeneous_erase :
            ∀ y ∈ s.erase x.1, SetLike.IsHomogeneousElem ℳ y := by
          intro y hy
          exact hs_homogeneous y (Finset.mem_of_mem_erase hy)
        exact ih (s.erase x.1).card hcard_erase (s := s.erase x.1)
          hs_homogeneous_erase hspan_erase rfl

/-- A finite graded module admits a finite homogeneous generating set. -/
theorem exists_finset_homogeneous_span_eq_top [Module.Finite A M] :
    ∃ s : Finset M,
      (∀ x ∈ s, SetLike.IsHomogeneousElem ℳ x) ∧
        Submodule.span A (s : Set M) = ⊤ := by
  -- Specialize the general homogeneous-submodule generator lemma to the top submodule.
  obtain ⟨s, hs_homogeneous, _hs_mem, hs_span⟩ :=
    exists_finset_homogeneous_span_eq_of_isHomogeneous (ℳ := ℳ) (P := ⊤)
      (hP := by
        intro i x hx
        simp)
      Module.Finite.fg_top
  exact ⟨s, hs_homogeneous, hs_span⟩

/-- Helper for Lemma 10.56.1: the graded form of part (1) keeps the module grading explicit so
the minimal-degree induction can be applied before the public wrapper forgets `ℳ`. -/
theorem subsingleton_of_irrelevant_ideal_smul_top_eq_top_with_grading
    (ℳ' : ℤ → Submodule A M)
    [DirectSum.Decomposition ℳ'] [SetLike.GradedSMul 𝒜 ℳ']
    [Module.Finite A M]
    (hM : S₊.toIdeal • (⊤ : Submodule A M) = ⊤) :
    Subsingleton M := by
  -- Choose finite homogeneous generators and feed them to the minimal-degree induction.
  obtain ⟨s, hs_homogeneous, hspan⟩ :=
    exists_finset_homogeneous_span_eq_top (ℳ := ℳ')
  exact subsingleton_of_homogeneous_span_eq_top_of_irrelevant
    (𝒜 := 𝒜) (ℳ := ℳ') s hs_homogeneous hspan hM

/-- Lemma 10.56.1 (1): if `S₊ M = M` and `M` is finite, then `M` is the zero module.
The canonical Lean conclusion is `Subsingleton M`.  The module grading is part of the
source statement and is intentionally visible in this wrapper. -/
-- Proof sketch: choose homogeneous generators of minimal degree and use `S₊ M = M` to force the
-- minimal-degree generator to vanish, then induct on the number of generators.
theorem subsingleton_of_irrelevant_ideal_smul_top_eq_top
    (ℳ' : ℤ → Submodule A M)
    [DirectSum.Decomposition ℳ'] [SetLike.GradedSMul 𝒜 ℳ']
    [Module.Finite A M]
    (hM : S₊.toIdeal • (⊤ : Submodule A M) = ⊤) :
    Subsingleton M := by
  exact subsingleton_of_irrelevant_ideal_smul_top_eq_top_with_grading
    (𝒜 := 𝒜) (ℳ' := ℳ') hM

/-- Lemma 10.56.1 (1), source-facing submodule form. -/
theorem eq_bot_of_irrelevant_ideal_smul_eq_top
    (ℳ' : ℤ → Submodule A M)
    [DirectSum.Decomposition ℳ'] [SetLike.GradedSMul 𝒜 ℳ']
    [Module.Finite A M]
    (hM : S₊.toIdeal • (⊤ : Submodule A M) = ⊤) :
    (⊤ : Submodule A M) = ⊥ := by
  let _ : Subsingleton M :=
    subsingleton_of_irrelevant_ideal_smul_top_eq_top (𝒜 := 𝒜) (ℳ' := ℳ') hM
  exact (⊤ : Submodule A M).eq_bot_of_subsingleton

/-- Helper for Lemma 10.56.1: the quotient by a homogeneous submodule inherits the graded pieces
by mapping each component through the quotient map. -/
def quotient_grading (N : Submodule A M) (i : ℤ) : Submodule A (M ⧸ N) :=
  (ℳ i).map N.mkQ

/-- Helper for Lemma 10.56.1: after quotienting by `N`, the hypothesis
`N ⊔ S₊ • N' = ⊤` becomes `S₊ • image(N') = ⊤`. -/
lemma mkQ_sup_irrelevant_smul_image_eq_top
    {N N' : Submodule A M}
    (hM : N ⊔ S₊.toIdeal • N' = ⊤) :
    S₊.toIdeal • (N'.map N.mkQ) = ⊤ := by
  -- Map the source equality to the quotient and collapse the image of `N` to zero.
  have hmap := congrArg (Submodule.map N.mkQ) hM
  simpa [Submodule.map_sup, Submodule.mkQ_map_self, Submodule.map_smul'',
    Submodule.map_top, Submodule.range_mkQ, bot_sup_eq] using hmap

/-- Lemma 10.56.1 (2): if `M = N + S₊ N'` with `N'` finite, then the `ℤ`-graded submodule `N`
already equals `M`. -/
-- Proof sketch: pass to the quotient `M / N`, where the image of `N'` is finite and is equal to
-- its own `S₊`-multiple, then apply part (1).
theorem eq_top_of_sup_irrelevant_ideal_smul_eq_top
    {N N' : Submodule A M}
    (hN : N.IsHomogeneous ℳ)
    (hN' : N'.IsHomogeneous ℳ)
    (hN'fg : N'.FG)
    (hM : N ⊔ S₊.toIdeal • N' = ⊤) :
    N = ⊤ := by
  classical
  obtain ⟨s, hs_homogeneous, _hs_mem, hs_span⟩ :=
    exists_finset_homogeneous_span_eq_of_isHomogeneous (ℳ := ℳ) (P := N') hN' hN'fg
  have hspan_top : N ⊔ S₊.toIdeal • Submodule.span A (s : Set M) = ⊤ := by
    simpa [hs_span] using hM
  have hs_le : Submodule.span A (s : Set M) ≤ N :=
    le_of_homogeneous_span_sup_irrelevant_eq_top (𝒜 := 𝒜) (ℳ := ℳ)
      (P := N) hN s hs_homogeneous hspan_top
  have hN'le : N' ≤ N := by
    rw [← hs_span]
    exact hs_le
  have hsmul_le : S₊.toIdeal • N' ≤ N := by
    exact (smul_mono_right _ hN'le).trans Submodule.smul_le_right
  -- Once `N'` is absorbed into `N`, the original `sup` equality collapses to `N = ⊤`.
  apply top_unique
  rw [← hM]
  exact sup_le le_rfl hsmul_le

end GradedModule

section GradedLinearMap

variable (ℳ : ℤ → Submodule A M) (ℕₘ : ℤ → Submodule A N)
variable [GradedRing 𝒜]
variable [DirectSum.Decomposition ℳ] [SetLike.GradedSMul 𝒜 ℳ]
variable [DirectSum.Decomposition ℕₘ] [SetLike.GradedSMul 𝒜 ℕₘ]

/-- Helper for Lemma 10.56.1: a degree-preserving linear map commutes with the homogeneous
projections coming from the chosen decompositions. -/
lemma decompose_map_eq_of_mapsTo
    (f : N →ₗ[A] M)
    (hf : ∀ i, Set.MapsTo f (ℕₘ i) (ℳ i))
    (y : N) (i : ℤ) :
    ((DirectSum.decompose ℳ (f y) i : ℳ i) : M) =
      f ((DirectSum.decompose ℕₘ y i : ℕₘ i) : N) := by
  classical
  let s : Finset ℤ := (DirectSum.decompose ℕₘ y).support
  let g : ℤ → N := fun j ↦ ((DirectSum.decompose ℕₘ y j : ℕₘ j) : N)
  have hdecomp :
      DirectSum.decompose ℳ (f y) =
        ∑ j ∈ s, DirectSum.decompose ℳ (f (g j)) := by
    -- Expand `y` into homogeneous pieces and apply `f` termwise before projecting.
    rw [show y = ∑ j ∈ s, g j by
      simp [s, g, DirectSum.sum_support_decompose]]
    rw [map_sum, DirectSum.decompose_sum]
  have hcoord :
      ((DirectSum.decompose ℳ (f y) i : ℳ i) : M) =
        ∑ j ∈ s, ((DirectSum.decompose ℳ (f (g j)) i : ℳ i) : M) := by
    simpa [DirectSum.sum_apply] using
      congrArg (fun z : ⨁ j, ℳ j ↦ (z i : M)) hdecomp
  have hterm :
      ∀ j ∈ s,
        ((DirectSum.decompose ℳ (f (g j)) i : ℳ i) : M) =
          if h : j = i then f ((DirectSum.decompose ℕₘ y i : ℕₘ i) : N) else 0 := by
    intro j hj
    by_cases hji : j = i
    · subst j
      have hmem : f (g i) ∈ ℳ i := hf i (DirectSum.decompose ℕₘ y i).2
      simpa [g] using (DirectSum.decompose_of_mem_same ℳ hmem)
    · have hmem : f (g j) ∈ ℳ j := hf j (DirectSum.decompose ℕₘ y j).2
      simpa [g, hji] using (DirectSum.decompose_of_mem_ne ℳ hmem hji)
  rw [Finset.sum_congr rfl hterm] at hcoord
  by_cases hi : i ∈ s
  · rw [Finset.sum_eq_single_of_mem i hi] at hcoord
    · simpa using hcoord
    · intro j hj hji
      simp [hji]
  · have hi_zero : ((DirectSum.decompose ℕₘ y i : ℕₘ i) : N) = 0 := by
      have hi_zero' : (DirectSum.decompose ℕₘ y i : ℕₘ i) = 0 := by
        by_contra hzero
        exact hi (by simpa [s, DFinsupp.mem_support_iff, hzero])
      exact congrArg (fun z : ℕₘ i ↦ (z : N)) hi_zero'
    rw [Finset.sum_eq_zero] at hcoord
    · simpa [hi_zero] using hcoord
    · intro j hj
      have hji : j ≠ i := by
        intro hji
        exact hi (hji ▸ hj)
      simp [hji]

/-- Helper for Lemma 10.56.1: the range of a degree-preserving linear map is a homogeneous
submodule. -/
lemma range_isHomogeneous_of_mapsTo
    (f : N →ₗ[A] M)
    (hf : ∀ i, Set.MapsTo f (ℕₘ i) (ℳ i)) :
    (LinearMap.range f).IsHomogeneous ℳ := by
  intro i x hx
  rcases hx with ⟨y, rfl⟩
  -- Project each image element degreewise by projecting its source witness first.
  exact ⟨((DirectSum.decompose ℕₘ y i : ℕₘ i) : N),
    (decompose_map_eq_of_mapsTo (ℳ := ℳ) (ℕₘ := ℕₘ) f hf y i).symm⟩

/-- Helper for Lemma 10.56.1: surjectivity modulo `S₊` is equivalent to the range together with
`S₊ M` generating the whole target. -/
lemma reduceModIdeal_surjective_iff_range_sup_irrelevant_smul_top_eq_top
    (f : N →ₗ[A] M) :
    Function.Surjective (f.reduceModIdeal S₊.toIdeal) ↔
      LinearMap.range f ⊔ S₊.toIdeal • (⊤ : Submodule A M) = ⊤ := by
  constructor
  · intro hquot
    apply top_unique
    intro m hm
    obtain ⟨q, hq⟩ :=
      hquot (Submodule.Quotient.mk (p := S₊.toIdeal • (⊤ : Submodule A M)) m)
    obtain ⟨n, rfl⟩ := Submodule.mkQ_surjective (S₊.toIdeal • (⊤ : Submodule A N)) q
    have hsub' : f n - m ∈ S₊.toIdeal • (⊤ : Submodule A M) := by
      exact (Submodule.Quotient.eq (S₊.toIdeal • (⊤ : Submodule A M))).mp <| by
        simpa [LinearMap.reduceModIdeal_apply] using hq
    have hsub : m - f n ∈ S₊.toIdeal • (⊤ : Submodule A M) := by
      -- Negating the quotient relation swaps the order of the difference.
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        Submodule.neg_mem (S₊.toIdeal • (⊤ : Submodule A M)) hsub'
    exact Submodule.mem_sup.mpr
      ⟨f n, ⟨n, rfl⟩, m - f n, hsub, by
        simp [sub_eq_add_neg, add_left_comm]⟩
  · intro hsup x
    obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective (S₊.toIdeal • (⊤ : Submodule A M)) x
    have hm : m ∈ LinearMap.range f ⊔ S₊.toIdeal • (⊤ : Submodule A M) := by
      rw [hsup]
      exact Submodule.mem_top
    rcases Submodule.mem_sup.mp hm with ⟨y, hy, z, hz, rfl⟩
    rcases hy with ⟨n, rfl⟩
    refine ⟨Submodule.Quotient.mk (p := S₊.toIdeal • (⊤ : Submodule A N)) n, ?_⟩
    -- The quotient class of the `S₊`-part vanishes, so the class is represented by `f n`.
    apply (Submodule.Quotient.eq (S₊.toIdeal • (⊤ : Submodule A M))).2
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      Submodule.neg_mem (S₊.toIdeal • (⊤ : Submodule A M)) hz

/-- Lemma 10.56.1 (3): a map of `ℤ`-graded modules is surjective if the induced map modulo `S₊` is
surjective and the target is finite as a graded module. The quotient reduction is expressed by the
canonical owner `LinearMap.reduceModIdeal`. -/
-- Proof sketch: apply part (2) to the image submodule of `f`, using the surjectivity on quotients
-- to write the target as the image plus `S₊` times the whole target.
theorem surjective_of_irrelevant_reduceModIdeal_surjective
    (f : N →ₗ[A] M)
    (hf : ∀ i, Set.MapsTo f (ℕₘ i) (ℳ i))
    [Module.Finite A M]
    (hquot : Function.Surjective (f.reduceModIdeal S₊.toIdeal)) :
    Function.Surjective f := by
  have hRangeHom : (LinearMap.range f).IsHomogeneous ℳ :=
    range_isHomogeneous_of_mapsTo (ℳ := ℳ) (ℕₘ := ℕₘ) f hf
  have hRangeTop : LinearMap.range f = ⊤ := by
    -- Apply the submodule form of graded Nakayama to the image submodule and `⊤`.
    exact eq_top_of_sup_irrelevant_ideal_smul_eq_top (𝒜 := 𝒜) (ℳ := ℳ)
      (N := LinearMap.range f) (N' := ⊤) hRangeHom
      (by
        intro i x hx
        simp)
      Module.Finite.fg_top
      (reduceModIdeal_surjective_iff_range_sup_irrelevant_smul_top_eq_top
        (𝒜 := 𝒜) (f := f) |>.1 hquot)
  exact LinearMap.range_eq_top.1 hRangeTop

end GradedLinearMap

section GradedModule

variable (ℳ : ℤ → Submodule A M)
variable [GradedRing 𝒜] [DirectSum.Decomposition ℳ] [SetLike.GradedSMul 𝒜 ℳ]

/-- Lemma 10.56.1 (4): a finite set of homogeneous elements generating `M / S₊ M` already
generates the finite `ℤ`-graded module `M`. -/
-- Proof sketch: map the direct sum of the twists `S(-dᵢ)` attached to the chosen homogeneous
-- generators to `M` and apply part (3) to the induced surjective map on the quotients modulo `S₊`.
theorem span_eq_top_of_quotient_span_eq_top_of_homogeneous
    [Module.Finite A M]
    (s : Finset M)
    (hs_homogeneous : ∀ x ∈ s, SetLike.IsHomogeneousElem ℳ x)
    (hspan :
      Submodule.span A
        ((S₊.toIdeal • (⊤ : Submodule A M)).mkQ '' (s : Set M)) = ⊤) :
    Submodule.span A (s : Set M) = ⊤ := by
  let P : Submodule A M := Submodule.span A (s : Set M)
  have hP : P.IsHomogeneous ℳ :=
    span_isHomogeneous_of_isHomogeneousElem (ℳ := ℳ) hs_homogeneous
  have hsup : P ⊔ S₊.toIdeal • (⊤ : Submodule A M) = ⊤ := by
    have hmap : Submodule.map ((S₊.toIdeal • (⊤ : Submodule A M)).mkQ) P = ⊤ := by
      -- Push the chosen span through the quotient map first.
      rw [show P = Submodule.span A (s : Set M) by rfl, Submodule.map_span]
      exact hspan
    rwa [Submodule.map_mkQ_eq_top, sup_comm] at hmap
  -- Apply the submodule form of graded Nakayama with `N' = ⊤`.
  simpa [P] using
    eq_top_of_sup_irrelevant_ideal_smul_eq_top (𝒜 := 𝒜) (ℳ := ℳ)
      (N := P) (N' := ⊤) hP
      (by
        intro i x hx
        simp)
      Module.Finite.fg_top hsup

end GradedModule

end
