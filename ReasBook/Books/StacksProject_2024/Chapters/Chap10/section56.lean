import Mathlib
import Mathlib.Algebra.Group.Submonoid.Finsupp
import Mathlib.RingTheory.GradedAlgebra.FiniteType
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Submodule
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Subsemiring
import Mathlib.RingTheory.GradedAlgebra.RingHom
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.Polynomial.IsIntegral
import Mathlib.RingTheory.PolynomialAlgebra

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_10_56_1 (from Chap10) -/
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

/-! ### Lemma_10_56_2 (from Chap10) -/
universe u

section

variable {S : Type u} [CommRing S]

/-- Helper for Lemma 10.56.2: a weighted degree at least `card ι * m` contains one generator block
of degree `m`. -/
lemma exists_generator_degree_block
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (δ : ι → ℕ) (hδ : ∀ i, 0 < δ i)
    {m T : ℕ} (_hm : 0 < m) (hdiv : ∀ i, δ i ∣ m)
    (hT : Fintype.card ι ≤ T) (e : ι → ℕ)
    (he : ∑ i, e i * δ i = T * m) :
    ∃ i, m / δ i ≤ e i := by
  classical
  by_contra hblock
  push Not at hblock
  have hlt : ∀ i, e i * δ i < m := by
    intro i
    have hi : e i < m / δ i := hblock i
    have hmul := Nat.mul_lt_mul_of_pos_right hi (hδ i)
    simpa [Nat.div_mul_cancel (hdiv i)] using hmul
  have hsum_lt : ∑ i, e i * δ i < ∑ _ : ι, m := by
    let i0 : ι := Classical.choice ‹Nonempty ι›
    refine Finset.sum_lt_sum (fun i _ ↦ le_of_lt (hlt i)) ?_
    exact ⟨i0, Finset.mem_univ _, hlt i0⟩
  have hcard_mul : Fintype.card ι * m ≤ T * m := by
    exact Nat.mul_le_mul_right m hT
  have hcontra : T * m < T * m := by
    calc
      T * m = ∑ i, e i * δ i := he.symm
      _ < ∑ _ : ι, m := hsum_lt
      _ = Fintype.card ι * m := by simp
      _ ≤ T * m := hcard_mul
  exact Nat.lt_irrefl _ hcontra

/-- Helper for Lemma 10.56.2: if the weighted degree is `(n + 1) * card ι * m`, then one can
factor off a submonomial of weighted degree `card ι * m`. -/
lemma weighted_subexponent_of_multiple_degree
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (δ : ι → ℕ) (hδ : ∀ i, 0 < δ i)
    {m : ℕ} (hm : 0 < m) (hdiv : ∀ i, δ i ∣ m) :
    ∀ {k T : ℕ} (hk : k ≤ Fintype.card ι) (hT : Fintype.card ι + k - 1 ≤ T)
      (e : ι → ℕ) (he : ∑ i, e i * δ i = T * m),
      ∃ a : ι → ℕ, (∀ i, a i ≤ e i) ∧ ∑ i, a i * δ i = k * m := by
  intro k
  induction k with
  | zero =>
      intro T _hk _hT e _he
      -- The zero block is given by the zero subexponent.
      refine ⟨0, fun i ↦ Nat.zero_le _, by simp⟩
  | succ k ih =>
      intro T hk hT e he
      -- First extract one degree-`m` block, then recurse on the remaining exponents.
      have hT' : Fintype.card ι + k ≤ T := by
        simpa [Nat.add_assoc] using hT
      have hcard_le : Fintype.card ι ≤ T := le_trans (Nat.le_add_right _ _) hT'
      rcases exists_generator_degree_block δ hδ hm hdiv hcard_le e he with ⟨i, hi⟩
      let b : ι → ℕ := Pi.single i (m / δ i)
      let e' : ι → ℕ := fun j ↦ e j - b j
      have hb_le : ∀ j, b j ≤ e j := by
        intro j
        by_cases hj : j = i
        · subst hj
          simp [b, hi]
        · simp [b, hj]
      have hb_sum : ∑ j, b j * δ j = m := by
        -- The extracted block contributes exactly degree `m`.
        rw [Fintype.sum_eq_single i]
        · simp [b, Nat.div_mul_cancel (hdiv i)]
        · intro j hj
          simp [b, hj]
      have he'_sum : ∑ j, e' j * δ j = (T - 1) * m := by
        have hle_term : ∀ j ∈ Finset.univ, b j * δ j ≤ e j * δ j := by
          intro j _hj
          exact Nat.mul_le_mul_right (δ j) (hb_le j)
        calc
          ∑ j, e' j * δ j = ∑ j, (e j * δ j - b j * δ j) := by
            simp_rw [e', tsub_mul]
          _ = (∑ j, e j * δ j) - ∑ j, b j * δ j := by
            exact Finset.sum_tsub_distrib (s := Finset.univ) hle_term
          _ = T * m - m := by rw [he, hb_sum]
          _ = (T - 1) * m := by
            rcases T.eq_zero_or_pos with rfl | hTpos
            · exact (False.elim <| Nat.not_lt_zero _ <| lt_of_lt_of_le
                (lt_of_lt_of_le (Nat.succ_pos k) hk) hcard_le)
            · obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hTpos.ne'
              simp [Nat.succ_mul]
      have hk' : k ≤ Fintype.card ι := Nat.le_of_succ_le hk
      have hT'' : Fintype.card ι + k - 1 ≤ T - 1 := by
        exact Nat.sub_le_sub_right hT' 1
      rcases ih hk' hT'' e' he'_sum with ⟨a, ha_le, ha_sum⟩
      refine ⟨fun j ↦ a j + b j, ?_, ?_⟩
      · intro j
        exact add_le_of_le_tsub_right_of_le (hb_le j) (ha_le j)
      · -- Adding back the extracted block restores one more degree-`m` summand.
        calc
          ∑ j, (a j + b j) * δ j = (∑ j, a j * δ j) + ∑ j, b j * δ j := by
            simp_rw [add_mul]
            rw [Finset.sum_add_distrib]
          _ = k * m + m := by rw [ha_sum, hb_sum]
          _ = (k + 1) * m := by rw [Nat.succ_mul]

/-- Helper for Lemma 10.56.2: a homogeneous monomial of weighted degree `n * card ι * m` lies in
the `𝒜 0`-subalgebra generated by the degree-`card ι * m` piece. -/
lemma generator_monomial_mem_adjoin_degree_piece
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (𝒜 : ℕ → Submodule ℤ S) [GradedAlgebra 𝒜]
    (v : ι → S) (δ : ι → ℕ) (hδ : ∀ i, 0 < δ i)
    (hv : ∀ i, v i ∈ 𝒜 (δ i))
    {m : ℕ} (hm : 0 < m) (hdiv : ∀ i, δ i ∣ m) :
    ∀ (n : ℕ) (e : ι → ℕ),
      (∑ i, e i * δ i = n * (Fintype.card ι * m)) →
      ∏ i, v i ^ e i ∈ Algebra.adjoin (𝒜 0) (𝒜 (Fintype.card ι * m) : Set S) := by
  classical
  by_cases hι : Nonempty ι
  · letI := hι
    let d : ℕ := Fintype.card ι * m
    -- Follow the Stacks factorization argument by peeling off one degree-`d` block at a time.
    refine Nat.twoStepInduction ?_ ?_ ?_
    · intro e he
      have hmem :
          ∏ i, v i ^ e i ∈ 𝒜 (∑ i, e i • δ i) :=
        SetLike.prod_pow_mem_graded 𝒜 δ v e (fun i _ ↦ hv i)
      have hzero : ∑ i, e i • δ i = 0 := by
        simpa [smul_eq_mul, d] using he
      have hmem0 : ∏ i, v i ^ e i ∈ 𝒜 0 := by
        simpa [smul_eq_mul] using (hzero ▸ hmem)
      -- Degree-zero elements already lie in the base algebra.
      let y : 𝒜 0 := ⟨∏ i, v i ^ e i, hmem0⟩
      exact Subalgebra.algebraMap_mem _ y
    · intro e he
      have hmem :
          ∏ i, v i ^ e i ∈ 𝒜 (∑ i, e i • δ i) :=
        SetLike.prod_pow_mem_graded 𝒜 δ v e (fun i _ ↦ hv i)
      have hone : ∑ i, e i • δ i = d := by
        simpa [smul_eq_mul, d] using he
      have hmemd : ∏ i, v i ^ e i ∈ 𝒜 d := by
        simpa [smul_eq_mul] using (hone ▸ hmem)
      -- A degree-`d` monomial is one of the generators.
      exact Algebra.subset_adjoin hmemd
    · intro n _ihn ihn1 e he
      let d : ℕ := Fintype.card ι * m
      have hcard_pos : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr hι
      have hbound :
          Fintype.card ι + Fintype.card ι - 1 ≤ (n + 2) * Fintype.card ι := by
        have htwo_le : Fintype.card ι + Fintype.card ι ≤ (n + 2) * Fintype.card ι := by
          simpa [Nat.add_mul, two_mul, add_assoc, add_left_comm, add_comm] using
            (Nat.le_add_left (Fintype.card ι + Fintype.card ι) (n * Fintype.card ι))
        exact (Nat.sub_le _ _).trans htwo_le
      have he_mul : ∑ i, e i * δ i = ((n + 2) * Fintype.card ι) * m := by
        calc
          ∑ i, e i * δ i = (n + 2) * d := he
          _ = ((n + 2) * Fintype.card ι) * m := by
            simp [d, Nat.mul_assoc]
      rcases weighted_subexponent_of_multiple_degree δ hδ hm hdiv
          (k := Fintype.card ι) (T := (n + 2) * Fintype.card ι) le_rfl hbound e he_mul with
        ⟨a, ha_le, ha_sum⟩
      let b : ι → ℕ := fun i ↦ e i - a i
      have ha_sum' : ∑ i, a i * δ i = d := by
        simpa [d] using ha_sum
      have hb_sum : ∑ i, b i * δ i = (n + 1) * d := by
        have hle_term : ∀ j ∈ Finset.univ, a j * δ j ≤ e j * δ j := by
          intro j _hj
          exact Nat.mul_le_mul_right (δ j) (ha_le j)
        calc
          ∑ i, b i * δ i = ∑ i, (e i * δ i - a i * δ i) := by
            simp_rw [b, tsub_mul]
          _ = (∑ i, e i * δ i) - ∑ i, a i * δ i := by
            exact Finset.sum_tsub_distrib (s := Finset.univ) hle_term
          _ = (n + 2) * d - d := by rw [he, ha_sum']
          _ = (n + 1) * d := by
            have hd' : (n + 2) * d = (n + 1) * d + d := by
              rw [show n + 2 = (n + 1) + 1 by simp, Nat.add_mul, one_mul]
            rw [hd', Nat.add_sub_cancel]
      have ha_mem :
          ∏ i, v i ^ a i ∈ Algebra.adjoin (𝒜 0) (𝒜 d : Set S) := by
        have hmem :
            ∏ i, v i ^ a i ∈ 𝒜 (∑ i, a i • δ i) :=
          SetLike.prod_pow_mem_graded 𝒜 δ v a (fun i _ ↦ hv i)
        have hmemd : ∏ i, v i ^ a i ∈ 𝒜 d := by
          simpa [smul_eq_mul, ha_sum, d] using hmem
        exact Algebra.subset_adjoin hmemd
      have hb_mem :
          ∏ i, v i ^ b i ∈ Algebra.adjoin (𝒜 0) (𝒜 d : Set S) :=
        ihn1 b hb_sum
      have hsplit :
          ∏ i, v i ^ e i = (∏ i, v i ^ a i) * ∏ i, v i ^ b i := by
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl ?_
        intro i _hi
        calc
          v i ^ e i = v i ^ (a i + b i) := by
            dsimp [b]
            rw [Nat.add_sub_of_le (ha_le i)]
          _ = v i ^ a i * v i ^ b i := by rw [pow_add]
      -- The factored monomial is a product of one degree-`d` block and a shorter monomial.
      rw [hsplit]
      exact (Algebra.adjoin (𝒜 0) (𝒜 d : Set S)).mul_mem ha_mem hb_mem
  · haveI : IsEmpty ι := not_nonempty_iff.mp hι
    intro n e _he
    -- With no generators, the unique monomial is `1`.
    simpa using (Algebra.one_mem (Algebra.adjoin (𝒜 0) (𝒜 (Fintype.card ι * m) : Set S)))

/-- Helper for Lemma 10.56.2: finite homogeneous generators imply that every degree divisible by
`card ι * m` lies in the `𝒜 0`-subalgebra generated by the degree-`card ι * m` piece. -/
lemma multiple_degree_piece_subset_adjoin_degree_piece_of_finite_generators
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (𝒜 : ℕ → Submodule ℤ S) [GradedAlgebra 𝒜]
    (v : ι → S) (δ : ι → ℕ) (hδ : ∀ i, 0 < δ i)
    (hv : ∀ i, v i ∈ 𝒜 (δ i))
    (hgen : Algebra.adjoin (𝒜 0) (Set.range v) = ⊤)
    {m : ℕ} (hm : 0 < m) (hdiv : ∀ i, δ i ∣ m)
    (n : ℕ) :
    (𝒜 (n * (Fintype.card ι * m)) : Set S) ⊆
      Algebra.adjoin (𝒜 0) (𝒜 (Fintype.card ι * m) : Set S) := by
  intro x hx
  let d : ℕ := Fintype.card ι * m
  have hx_span : x ∈ Submodule.span (𝒜 0) (Submonoid.closure (Set.range v)) := by
    -- Rewrite the finite-generation hypothesis in the span form used by span induction.
    rw [← Algebra.adjoin_eq_span, hgen]
    trivial
  have hcomponent :
      ((DirectSum.decompose 𝒜 x (n * d) : S) ∈
        Algebra.adjoin (𝒜 0) (𝒜 d : Set S)) := by
    clear hx
    induction hx_span using Submodule.span_induction with
    | mem y hy =>
        obtain ⟨ai, rfl⟩ := Submonoid.exists_of_mem_closure_range v y hy
        by_cases H : ∑ i, ai i * δ i = n * d
        · have hprod_mem :
            ∏ i, v i ^ ai i ∈ 𝒜 (n * d) := by
            have hmem :
                ∏ i, v i ^ ai i ∈ 𝒜 (∑ i, ai i • δ i) :=
              SetLike.prod_pow_mem_graded 𝒜 δ v ai (fun i _ ↦ hv i)
            simpa [smul_eq_mul, H] using hmem
          simpa [d, DirectSum.decompose_of_mem_same 𝒜 hprod_mem] using
            generator_monomial_mem_adjoin_degree_piece 𝒜 v δ hδ hv hm hdiv n ai H
        · have hprod_mem :
            ∏ i, v i ^ ai i ∈ 𝒜 (∑ i, ai i * δ i) := by
            simpa [smul_eq_mul] using
              (SetLike.prod_pow_mem_graded 𝒜 δ v ai (fun i _ ↦ hv i))
          simpa [d, DirectSum.decompose_of_mem_ne 𝒜 hprod_mem H] using
            (show (0 : S) ∈ Algebra.adjoin (𝒜 0) (𝒜 d : Set S) from
              (Algebra.adjoin (𝒜 0) (𝒜 d : Set S)).zero_mem)
    | zero =>
        simpa [d] using
          (show (0 : S) ∈ Algebra.adjoin (𝒜 0) (𝒜 d : Set S) from
            (Algebra.adjoin (𝒜 0) (𝒜 d : Set S)).zero_mem)
    | add y z hy hz hy' hz' =>
        -- The fixed-degree component is additive.
        simpa [d, DirectSum.decompose_add, AddMemClass.coe_add] using
          (Algebra.adjoin (𝒜 0) (𝒜 d : Set S)).add_mem hy' hz'
    | smul r y hy hy' =>
        -- Multiplication by a degree-zero scalar stays inside the target subalgebra.
        rw [Algebra.smul_def]
        have hdecomp :
            (DirectSum.decompose 𝒜 ((algebraMap (𝒜 0) S) r * y) (n * d) : S) =
              (algebraMap (𝒜 0) S r : S) * (DirectSum.decompose 𝒜 y (n * d) : S) := by
          simpa using
            (DirectSum.coe_decompose_mul_of_left_mem_zero (𝒜 := 𝒜)
              (a := (algebraMap (𝒜 0) S r : S)) (b := y) (j := n * d) (SetLike.coe_mem r))
        rw [hdecomp]
        exact (Algebra.adjoin (𝒜 0) (𝒜 d : Set S)).mul_mem
          (Subalgebra.algebraMap_mem _ r) hy'
  -- The input element is already homogeneous of the target degree.
  simpa [d, DirectSum.decompose_of_mem_same 𝒜 hx] using hcomponent

/-- Helper for Lemma 10.56.2: once a graded ring has finitely many positive-degree homogeneous
generators, the Veronese subalgebra for any common multiple period is generated in degree `1`. -/
lemma veronese_adjoin_eq_of_finite_homogeneous_generators
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (𝒜 : ℕ → Submodule ℤ S) [GradedAlgebra 𝒜]
    (v : ι → S) (δ : ι → ℕ) (hδ : ∀ i, 0 < δ i)
    (hv : ∀ i, v i ∈ 𝒜 (δ i))
    (hgen : Algebra.adjoin (𝒜 0) (Set.range v) = ⊤)
    {m : ℕ} (hm : 0 < m) (hdiv : ∀ i, δ i ∣ m) :
    Algebra.adjoin (𝒜 0) (⋃ n : ℕ, (𝒜 (n * (Fintype.card ι * m)) : Set S)) =
      Algebra.adjoin (𝒜 0) (𝒜 (Fintype.card ι * m) : Set S) := by
  refine le_antisymm ?_ ?_
  · -- Every divisible-degree homogeneous piece already lies in the degree-`d` algebra.
    apply Algebra.adjoin_le
    intro x hx
    rcases Set.mem_iUnion.mp hx with ⟨n, hx⟩
    exact multiple_degree_piece_subset_adjoin_degree_piece_of_finite_generators
      𝒜 v δ hδ hv hgen hm hdiv n hx
  · -- The degree-`d` piece is one of the pieces appearing in the Veronese union.
    apply Algebra.adjoin_le
    intro x hx
    exact Algebra.subset_adjoin <| Set.mem_iUnion.mpr ⟨1, by simpa using hx⟩

/-- A source-facing consequence of the canonical Veronese-generation equality: every degree-`n * d`
piece of the ambient grading lies in the `𝒜 0`-subalgebra generated by the degree-`d` piece. -/
theorem subset_adjoin_degree_d_of_veronese_adjoin_eq
    (𝒜 : ℕ → Submodule ℤ S) [GradedAlgebra 𝒜] {d : ℕ+}
    (hgen :
      Algebra.adjoin (𝒜 0) (⋃ n : ℕ, (𝒜 (n * (d : ℕ)) : Set S)) =
        Algebra.adjoin (𝒜 0) (𝒜 (d : ℕ) : Set S))
    (n : ℕ) :
    (𝒜 (n * (d : ℕ)) : Set S) ⊆ Algebra.adjoin (𝒜 0) (𝒜 (d : ℕ) : Set S) := by
  intro x hx
  have hx' : x ∈ Algebra.adjoin (𝒜 0) (⋃ n : ℕ, (𝒜 (n * (d : ℕ)) : Set S)) :=
    Algebra.subset_adjoin <| Set.mem_iUnion.mpr ⟨n, hx⟩
  exact hgen ▸ hx'

/-- Lemma 10.56.2: if a graded ring is finitely generated over its degree-zero piece, then there
is some positive integer `d₀` such that every positive multiple `d` of `d₀` has its `d`-th
Veronese subring generated in degree `1` over degree `0` (Stacks, Tag `00JL`). The public entry is
the canonical equality between the `𝒜 0`-subalgebra generated by the degree-`d` piece and the
`𝒜 0`-subalgebra generated by all pieces in degrees divisible by `d`; the finite-type input is the
mathlib owner theorem `GradedAlgebra.exists_finset_adjoin_eq_top_and_homogeneous_ne_zero`. -/
-- Proof sketch: use `GradedAlgebra.exists_finset_adjoin_eq_top_and_homogeneous_ne_zero` to choose
-- finitely many positive-degree homogeneous generators of `S` over `S₀ = 𝒜 0`; if `d₀` is a common
-- multiple of their degrees, then the usual Stacks-project argument shows that the `d`-th
-- Veronese subring is generated over `S₀` by its degree-`d` piece whenever `d₀ ∣ d`.
lemma sufficiently_divisible_veronese_generated_in_degree_one
    (𝒜 : ℕ → Submodule ℤ S) [GradedAlgebra 𝒜] [Algebra.FiniteType (𝒜 0) S] :
    ∃ d₀ : ℕ+, ∀ ⦃d : ℕ+⦄, (d₀ : ℕ) ∣ (d : ℕ) →
      Algebra.adjoin (𝒜 0) (⋃ n : ℕ, (𝒜 (n * (d : ℕ)) : Set S)) =
        Algebra.adjoin (𝒜 0) (𝒜 (d : ℕ) : Set S) := by
  classical
  obtain ⟨s, hs, hsdeg⟩ := GradedAlgebra.exists_finset_adjoin_eq_top_and_homogeneous_ne_zero 𝒜
  by_cases hsne : s.Nonempty
  · let v : s → S := fun i ↦ i
    choose δ hδ_ne hv using fun i : s ↦ hsdeg i i.2
    have hδ : ∀ i : s, 0 < δ i := fun i ↦ Nat.pos_of_ne_zero (hδ_ne i)
    let m : ℕ := ∏ i : s, δ i
    have hm : 0 < m := by
      dsimp [m]
      exact Finset.prod_pos (fun i _ ↦ hδ i)
    have hdiv : ∀ i : s, δ i ∣ m := by
      intro i
      dsimp [m]
      simpa using Finset.dvd_prod_of_mem δ (Finset.mem_univ i)
    have hs_range : Algebra.adjoin (𝒜 0) (Set.range v) = ⊤ := by
      simpa [v] using hs
    have hs_sub_nonempty : Nonempty ↥s := ⟨⟨hsne.choose, hsne.choose_spec⟩⟩
    let d₀ : ℕ+ := ⟨Fintype.card s * m, Nat.mul_pos (Fintype.card_pos_iff.mpr hs_sub_nonempty) hm⟩
    refine ⟨d₀, ?_⟩
    intro d hdvd
    rcases hdvd with ⟨q, hq⟩
    -- Route correction: instead of transporting one fixed equality through divisibility rewrites,
    -- rerun the finite-generator lemma with the rescaled common multiple `q * m`.
    have hq_pos : 0 < q := by
      refine Nat.pos_of_ne_zero ?_
      intro hq0
      have : (d : ℕ) ≠ 0 := d.ne_zero
      exact this (by simpa [hq, hq0, d₀])
    have hmq : 0 < q * m := Nat.mul_pos hq_pos hm
    have hdivq : ∀ i : s, δ i ∣ q * m := by
      intro i
      rcases hdiv i with ⟨c, hc⟩
      exact ⟨q * c, by
        simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using congrArg (fun t ↦ q * t) hc⟩
    have hperiod :=
      veronese_adjoin_eq_of_finite_homogeneous_generators
        (ι := s) 𝒜 v δ hδ hv hs_range hmq hdivq
    simpa [hq, d₀, m, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hperiod
  · have hs0 : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hsne
    refine ⟨1, ?_⟩
    intro d _hdvd
    have hbase_top : (⊥ : Subalgebra (𝒜 0) S) = ⊤ := by
      simpa [hs0] using hs
    have hleft : Algebra.adjoin (𝒜 0) (⋃ n : ℕ, (𝒜 (n * (d : ℕ)) : Set S)) = ⊤ := by
      apply top_unique
      rw [← hbase_top]
      exact bot_le
    have hright : Algebra.adjoin (𝒜 0) (𝒜 (d : ℕ) : Set S) = ⊤ := by
      apply top_unique
      rw [← hbase_top]
      exact bot_le
    rw [hleft, hright]

end

/-! ### Lemma_10_56_3 (from Chap10) -/
universe u v

open scoped Polynomial

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
variable {𝒜 : ℕ → AddSubgroup R} [GradedRing 𝒜]
variable {ℬ : ℕ → AddSubgroup S} [GradedRing ℬ]

/-- Helper for Lemma 10.56.3: the zeroth graded projection commutes with the structure map of a
graded ring homomorphism. -/
lemma proj_zero_algebraMap_eq [Algebra R S]
    (hgraded : ∀ i {r : R}, r ∈ 𝒜 i → algebraMap R S r ∈ ℬ i) (r : R) :
    GradedRing.projZeroRingHom ℬ (algebraMap R S r) =
      algebraMap R S (GradedRing.projZeroRingHom 𝒜 r) := by
  let f : 𝒜 →+*ᵍ ℬ :=
    { __ := algebraMap R S
      map_mem := fun {i} {x} hx => hgraded i hx }
  -- The graded ring map commutes with direct-sum decomposition, hence also with the degree-zero
  -- projection.
  rw [GradedRing.projZeroRingHom_apply, GradedRing.projZeroRingHom_apply]
  exact (GradedRingHom.map_directSumDecompose (𝒜 := 𝒜) (ℬ := ℬ) f (x := r) (i := 0)).symm

/-- Helper for Lemma 10.56.3: the degree-zero component of an integral element is still integral
over the base ring. -/
lemma isIntegral_proj_zero [Algebra R S]
    (hgraded : ∀ i {r : R}, r ∈ 𝒜 i → algebraMap R S r ∈ ℬ i) {x : S}
    (hx : IsIntegral R x) :
    IsIntegral R (GradedRing.proj ℬ 0 x) := by
  have hcomp :
      (algebraMap R S).comp (GradedRing.projZeroRingHom 𝒜) =
        (GradedRing.projZeroRingHom ℬ).comp (algebraMap R S) := by
    -- The compatibility needed by `IsIntegral.map_of_comp_eq` is exactly the gradedness of the
    -- structure map at degree zero.
    ext r
    simpa [RingHom.comp_apply] using (proj_zero_algebraMap_eq hgraded r).symm
  -- Apply the integral polynomial through the compatible degree-zero projection map.
  have hzero : IsIntegral R (GradedRing.projZeroRingHom ℬ x) :=
    IsIntegral.map_of_comp_eq (φ := GradedRing.projZeroRingHom 𝒜)
      (ψ := GradedRing.projZeroRingHom ℬ) hcomp hx
  simpa [GradedRing.proj_apply, GradedRing.projZeroRingHom_apply] using hzero

/-- Helper for Lemma 10.56.3: every graded ring homomorphism preserves each homogeneous
projection. -/
lemma proj_algebraMap_eq [Algebra R S]
    (hgraded : ∀ i {r : R}, r ∈ 𝒜 i → algebraMap R S r ∈ ℬ i) (i : ℕ) (r : R) :
    GradedRing.proj ℬ i (algebraMap R S r) =
      algebraMap R S (GradedRing.proj 𝒜 i r) := by
  let f : 𝒜 →+*ᵍ ℬ :=
    { __ := algebraMap R S
      map_mem := fun {j} {x} hx => hgraded j hx }
  -- The graded ring map commutes with the direct-sum decomposition degree by degree.
  exact (GradedRingHom.map_directSumDecompose (𝒜 := 𝒜) (ℬ := ℬ) f (x := r) (i := i)).symm

/-- Helper for Lemma 10.56.3: the degree-zero generator of the direct sum maps to the constant
polynomial `1`. -/
lemma gradingToPolynomial_hone (ℬ : ℕ → AddSubgroup S) [GradedRing ℬ] :
    ((Polynomial.monomial 0).toAddMonoidHom.comp (AddSubgroupClass.subtype (ℬ 0)))
      (1 : ℬ 0) = (1 : S[X]) := by
  -- The degree-zero homogeneous unit gives the constant polynomial.
  simp

/-- Helper for Lemma 10.56.3: multiplication of homogeneous pieces becomes multiplication of the
corresponding monomials. -/
lemma gradingToPolynomial_hmul (ℬ : ℕ → AddSubgroup S) [GradedRing ℬ]
    {i j : ℕ} (ai : ℬ i) (aj : ℬ j) :
    ((Polynomial.monomial (i + j)).toAddMonoidHom.comp
        (AddSubgroupClass.subtype (ℬ (i + j))))
        ⟨(ai : S) * (aj : S), SetLike.GradedMul.mul_mem ai.2 aj.2⟩ =
      ((Polynomial.monomial i).toAddMonoidHom.comp (AddSubgroupClass.subtype (ℬ i))) ai *
        ((Polynomial.monomial j).toAddMonoidHom.comp (AddSubgroupClass.subtype (ℬ j))) aj := by
  -- Multiplication of monomials records both the degree sum and the coefficient product.
  simpa using (Polynomial.monomial_mul_monomial i j (ai : S) (aj : S)).symm

/-- Helper for Lemma 10.56.3: the canonical polynomial attached to a graded element is the sum of
its homogeneous components placed in the corresponding degrees. -/
noncomputable def gradingToPolynomialRingHom (ℬ : ℕ → AddSubgroup S) [GradedRing ℬ] :
    S →+* S[X] :=
  let f : ∀ i, ℬ i →+ S[X] :=
    fun i => (Polynomial.monomial i).toAddMonoidHom.comp (AddSubgroupClass.subtype (ℬ i))
  (DirectSum.toSemiring f (gradingToPolynomial_hone (ℬ := ℬ))
      fun {_ _} ai aj => gradingToPolynomial_hmul (ℬ := ℬ) ai aj).comp
    (DirectSum.decomposeRingEquiv ℬ).toRingHom

/-- Helper for Lemma 10.56.3: the coefficient of degree `i` in the grading polynomial is the `i`th
homogeneous projection. -/
lemma coeff_gradingToPolynomialRingHom (i : ℕ) (x : S) :
    (gradingToPolynomialRingHom (ℬ := ℬ) x).coeff i = GradedRing.proj ℬ i x := by
  letI : ∀ j (y : ℬ j), Decidable (y ≠ 0) := fun _ y => by
    classical
    exact inferInstance
  -- Expand the direct-sum decomposition of `x`, then read off the `i`th coefficient.
  change
    ((DirectSum.toSemiring
        (fun i =>
          (Polynomial.monomial i).toAddMonoidHom.comp (AddSubgroupClass.subtype (ℬ i)))
        (gradingToPolynomial_hone (ℬ := ℬ))
        (fun {i j} ai aj => gradingToPolynomial_hmul (ℬ := ℬ) ai aj))
      (DirectSum.decompose ℬ x)).coeff i = GradedRing.proj ℬ i x
  rw [← DirectSum.sum_support_of (DirectSum.decompose ℬ x), map_sum, Polynomial.finset_sum_coeff]
  by_cases hi : i ∈ (DirectSum.decompose ℬ x).support
  · rw [Finset.sum_eq_single i]
    · simpa [DirectSum.toSemiring_of, AddMonoidHom.comp_apply, Polynomial.coeff_monomial,
        GradedRing.proj_apply]
    · intro j hj hji
      simpa [DirectSum.toSemiring_of, AddMonoidHom.comp_apply, Polynomial.coeff_monomial, hji]
    · intro hnot
      exact (hnot hi).elim
  · have hzero : GradedRing.proj ℬ i x = 0 := by
      by_contra hne
      exact hi ((GradedRing.mem_support_iff (𝒜 := ℬ) x i).2 hne)
    rw [Finset.sum_eq_zero]
    · simpa [hzero]
    · intro j hj
      by_cases hji : j = i
      · subst hji
        exact (hi hj).elim
      · simpa [DirectSum.toSemiring_of, AddMonoidHom.comp_apply, Polynomial.coeff_monomial, hji]

/-- Helper for Lemma 10.56.3: expanding the grading polynomial recovers the finite sum over the
direct-sum support. -/
lemma gradingToPolynomialRingHom_apply [∀ i (x : ℬ i), Decidable (x ≠ 0)] (x : S) :
    gradingToPolynomialRingHom (ℬ := ℬ) x =
      ∑ i ∈ (DirectSum.decompose ℬ x).support, Polynomial.monomial i (GradedRing.proj ℬ i x) := by
  ext i
  -- Equality of polynomials is equality of their coefficients, and the coefficient formula is
  -- exactly the previous helper.
  rw [coeff_gradingToPolynomialRingHom, Polynomial.finset_sum_coeff]
  by_cases hi : i ∈ (DirectSum.decompose ℬ x).support
  · rw [Finset.sum_eq_single i]
    · rw [Polynomial.coeff_monomial]
      simp
    · intro j hj hji
      rw [Polynomial.coeff_monomial]
      simp [hji]
    · intro hnot
      exact (hnot hi).elim
  · rw [Finset.sum_eq_zero]
    · have hzero : GradedRing.proj ℬ i x = 0 := by
        by_contra hne
        exact hi ((GradedRing.mem_support_iff (𝒜 := ℬ) x i).2 hne)
      simpa [hzero]
    · intro j hj
      rw [Polynomial.coeff_monomial]
      by_cases hji : j = i
      · subst hji
        exact (hi hj).elim
      · simp [hji]

/-- Helper for Lemma 10.56.3: the grading polynomial commutes with the structure map of a graded
ring homomorphism. -/
lemma gradingToPolynomialRingHom_algebraMap [Algebra R S]
    (hgraded : ∀ i {r : R}, r ∈ 𝒜 i → algebraMap R S r ∈ ℬ i) (r : R) :
    gradingToPolynomialRingHom (ℬ := ℬ) (algebraMap R S r) =
      Polynomial.map (algebraMap R S) (gradingToPolynomialRingHom (ℬ := 𝒜) r) := by
  ext i
  -- Equality of coefficients reduces the compatibility to the projection-level commutation lemma.
  rw [Polynomial.coeff_map, coeff_gradingToPolynomialRingHom, coeff_gradingToPolynomialRingHom]
  exact proj_algebraMap_eq hgraded i r

/-- Helper for Lemma 10.56.3: every homogeneous projection of an integral element is integral. -/
lemma isIntegral_proj [Algebra R S]
    (hgraded : ∀ i {r : R}, r ∈ 𝒜 i → algebraMap R S r ∈ ℬ i) {i : ℕ} {x : S}
    (hx : IsIntegral R x) :
    IsIntegral R (GradedRing.proj ℬ i x) := by
  letI : Algebra R[X] S[X] := Polynomial.algebra R S
  have hcomp :
      (algebraMap R[X] S[X]).comp (gradingToPolynomialRingHom (ℬ := 𝒜)) =
        (gradingToPolynomialRingHom (ℬ := ℬ)).comp (algebraMap R S) := by
    -- The grading polynomial construction is functorial for the graded structure map.
    ext r n
    change
      (Polynomial.map (algebraMap R S) ((gradingToPolynomialRingHom (ℬ := 𝒜)) r)).coeff n =
        ((gradingToPolynomialRingHom (ℬ := ℬ)) ((algebraMap R S) r)).coeff n
    rw [Polynomial.coeff_map, coeff_gradingToPolynomialRingHom, coeff_gradingToPolynomialRingHom]
    exact (proj_algebraMap_eq hgraded n r).symm
  have hpoly : IsIntegral R[X] (gradingToPolynomialRingHom (ℬ := ℬ) x) :=
    IsIntegral.map_of_comp_eq (φ := gradingToPolynomialRingHom (ℬ := 𝒜))
      (ψ := gradingToPolynomialRingHom (ℬ := ℬ)) hcomp hx
  -- Once the whole grading polynomial is integral over `R[X]`, each coefficient is integral over
  -- `R`.
  have hcoeff :
      IsIntegral R ((gradingToPolynomialRingHom (ℬ := ℬ) x).coeff i) :=
    (Polynomial.isIntegral_iff_isIntegral_coeff.mp hpoly) i
  simpa [coeff_gradingToPolynomialRingHom] using hcoeff

/-- Lemma 10.56.3: if the structure map `R → S` preserves the `ℕ`-gradings, then the integral
closure of `R` in `S` is a graded `R`-subalgebra of `S`. The canonical owner-level Lean form is
that the underlying subsemiring of `integralClosure R S` is homogeneous for the grading on `S`. -/
-- Proof sketch: equip the target with the algebra structure coming from the graded ring
-- homomorphism, then package all homogeneous pieces into a single grading polynomial; integrality
-- of that polynomial forces integrality of each coefficient.
lemma integralClosure_isHomogeneous [Algebra R S]
    (hgraded : ∀ i {r : R}, r ∈ 𝒜 i → algebraMap R S r ∈ ℬ i) :
    DirectSum.SetLike.IsHomogeneous ℬ (integralClosure R S).toSubsemiring := by
  intro i x hx
  -- Route correction: instead of reconstructing the Laurent-polynomial induction inline, use the
  -- canonical grading polynomial whose coefficients are exactly the homogeneous projections.
  change IsIntegral R (GradedRing.proj ℬ i x)
  exact isIntegral_proj hgraded hx

/-- Companion bridge: the owner-level homogeneous-subsemiring statement implies the homogeneous
`R`-submodule statement for the same integral closure. -/
theorem integralClosure_toSubmodule_isHomogeneous [Algebra R S]
    (hgraded : ∀ i {r : R}, r ∈ 𝒜 i → algebraMap R S r ∈ ℬ i) :
    (integralClosure R S).toSubmodule.IsHomogeneous ℬ := by
  simpa [Submodule.IsHomogeneous] using integralClosure_isHomogeneous hgraded

end
