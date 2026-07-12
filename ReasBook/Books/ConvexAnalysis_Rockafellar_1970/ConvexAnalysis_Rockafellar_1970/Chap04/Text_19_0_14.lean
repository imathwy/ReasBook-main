import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_2_3_11
import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_8_4_5

-- Declarations for this item will be appended below by the statement pipeline.

section

open scoped Pointwise Rockafellar

open Set

/-!
Source/core/bridge triage:

- `source-facing`: the item fixes a polytope `C ⊆ ℝ^n`, a nonempty subset `S ⊆ C`, defines the
  translation parameter set `D = {y | S + y = C}`, and asserts that `D` is again a polytope.
- `core/canonical`: the project owner predicate for the conclusion is `Set.IsPolytope`, while the
  owner abstraction for set translation is `Set.vaddSet`, written `y +ᵥ S`, and the owner
  abstraction for translation invariance is `Set.lineal`.
- `bridge/view`: the Chapter 2 lineality theorem offers both intrinsic translation and
  singleton-addition views; this file keeps the source-facing bridge at the intrinsic
  translation-equality layer `z +ᵥ C = C` when relating the parameter set to `lin[R](C)`.

Domain-style sampling used here:
- `Set.vaddSet`;
- `Set.IsPolytope`;
- `Set.lineal`;
- `Convex.mem_lineal_iff_vadd_eq_self`;
- the source-facing translation notation `y +ᵥ S`.

Primitive data vs derived API:
- primitive source-facing data: the subset `S`, the ambient polytope `C`, and the translation set
  of parameters sending `S` onto `C`, exposed below as `Set.translationCover S C`;
- derived API: the bridge from that parameter set to `lin[R](C)`, its canonical translation
  description `y₀ +ᵥ lin[R](C)`, and the theorem that this parameter set is a polytope.

Ambient level: the translation-cover owner itself lives on the intrinsic affine-action layer
`[VAdd E P]` rather than the stronger additive-group-on-points layer. The lineality bridge uses
the Chapter 2 scalar layer for `lin[R](C)` and convexity over `R`, while the final polytope
theorem uses boundedness of finite convex hulls in ordered normed-field spaces. In each case,
specializing to `E = EuclideanSpace ℝ (Fin n)` recovers the textbook formulation.

Layer target: `source-facing`.
-/

namespace Set

variable {E P : Type*} [VAdd E P]

/- The set of translation parameters that send `S` exactly onto `C`. -/
def translationCover (S C : Set P) : Set E :=
  {y | y +ᵥ S = C}

/- Membership in `translationCover S C` means that translating `S` by `y` yields exactly
`C`. -/
@[simp]
theorem mem_translationCover_iff {S C : Set P} {y : E} :
    y ∈ translationCover S C ↔ y +ᵥ S = C :=
  Iff.rfl

end Set

variable {E : Type*} [AddCommGroup E]

variable {R : Type*} [Zero R] [LE R] [SMul R E]

-- Proof sketch: if `y₀ ∈ translationCover S C`, then
-- `y +ᵥ S = C` is equivalent to `(y - y₀) +ᵥ C = C`; bridge this to
-- `Set.mem_lineal_iff_vadd_eq_self` at the intrinsic translation-invariance layer.
/-- Primitive bridge form: once one translation parameter `y₀` sending `S` onto `C` is fixed, the
other parameters are exactly the translate of the lineality space of `C` by `y₀`, under the
recession/translation bridge hypothesis. -/
theorem mem_translationCover_iff_sub_mem_lineal_of_hrec
    {S C : Set E} (hrec : ∀ z : E, z ∈ 0⁺[R] C ↔ z +ᵥ C ⊆ C) {y₀ y : E}
    (hy₀ : y₀ ∈ translationCover S C) :
    y ∈ translationCover S C ↔ y - y₀ ∈ lin[R](C) := by
  rw [Set.mem_translationCover_iff] at hy₀
  have hshift : (y - y₀) +ᵥ C = y +ᵥ S := by
    rw [← hy₀]
    ext x
    constructor
    · rintro ⟨u, hu, rfl⟩
      rcases hu with ⟨s, hs, rfl⟩
      exact ⟨s, hs, by simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]⟩
    · rintro ⟨s, hs, rfl⟩
      refine ⟨y₀ +ᵥ s, ?_, by simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]⟩
      exact ⟨s, hs, rfl⟩
  rw [Set.mem_lineal_iff_vadd_eq_self hrec]
  constructor
  · intro hy
    calc
      (y - y₀) +ᵥ C = y +ᵥ S := hshift
      _ = C := hy
  · intro hy
    rw [Set.mem_translationCover_iff]
    calc
      y +ᵥ S = (y - y₀) +ᵥ C := hshift.symm
      _ = C := hy

/-- With a fixed parameter `y₀` sending `S` onto `C`, the whole translation cover set is the
canonical translate `y₀ +ᵥ lin[R](C)`, under the recession/translation bridge hypothesis. -/
theorem translationCover_eq_vadd_lineal_of_hrec
    {S C : Set E} (hrec : ∀ z : E, z ∈ 0⁺[R] C ↔ z +ᵥ C ⊆ C) {y₀ : E}
    (hy₀ : y₀ ∈ translationCover S C) :
    translationCover S C = y₀ +ᵥ lin[R](C) := by
  ext y
  rw [Set.mem_vadd_set]
  constructor
  · intro hy
    exact ⟨y - y₀, (mem_translationCover_iff_sub_mem_lineal_of_hrec hrec hy₀).mp hy, by
      simp [vadd_eq_add, sub_eq_add_neg]⟩
  · rintro ⟨z, hz, rfl⟩
    exact (mem_translationCover_iff_sub_mem_lineal_of_hrec hrec hy₀).mpr <| by
      simpa [vadd_eq_add, sub_eq_add_neg] using hz

variable {R : Type*} [Ring R] [LinearOrder R] [IsStrictOrderedRing R] [FloorSemiring R]
variable [Module R E]

/-- Convex specialization of `mem_translationCover_iff_sub_mem_lineal_of_hrec`. -/
theorem mem_translationCover_iff_sub_mem_lineal
    {S C : Set E} (hC_convex : Convex R C) {y₀ y : E}
    (hy₀ : y₀ ∈ translationCover S C) :
    y ∈ translationCover S C ↔ y - y₀ ∈ lin[R](C) := by
  exact mem_translationCover_iff_sub_mem_lineal_of_hrec
    (hrec := fun z => hC_convex.mem_recessionCone_iff_vadd_subset_self z) hy₀

/-- Convex specialization of `translationCover_eq_vadd_lineal_of_hrec`. -/
theorem translationCover_eq_vadd_lineal
    {S C : Set E} (hC_convex : Convex R C) {y₀ : E}
    (hy₀ : y₀ ∈ translationCover S C) :
    translationCover S C = y₀ +ᵥ lin[R](C) := by
  exact translationCover_eq_vadd_lineal_of_hrec
    (hrec := fun z => hC_convex.mem_recessionCone_iff_vadd_subset_self z) hy₀

-- Proof sketch: if `translationCover S C` is empty, it is the convex hull of the empty finite
-- set and hence a polytope. Otherwise choose `y₀` in it and rewrite the whole set as
-- `y₀ +ᵥ lin[K](C)` via `translationCover_eq_vadd_lineal`. For a
-- bounded convex set, a nonzero lineality direction would then keep translating any point
-- of `C` along an unbounded arithmetic progression inside `C`, impossible for a bounded set.
-- Hence `lin[K](C) = {0}`, so the
-- translation cover set is either empty or the singleton `{y₀}`, and in either case it is a
-- polytope. The polytope corollary only uses the canonical boundedness of finite convex hulls.
-- The textbook hypothesis `S ⊆ C` is redundant for this conclusion and is omitted.
section Normed

variable {K : Type*} [NormedField K] [LinearOrder K]
  [IsStrictOrderedRing K] [FloorSemiring K] [NormSMulClass ℤ K]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace K V]

omit [LinearOrder K] [IsStrictOrderedRing K] [FloorSemiring K] in
private theorem not_isBounded_range_add_natCast_smul (x y : V) (hy : y ≠ 0) :
    ¬ Bornology.IsBounded (Set.range fun n : ℕ ↦ x + (n : K) • y) := by
  intro hbounded
  obtain ⟨R, hR⟩ := hbounded.subset_closedBall (0 : V)
  have hy_norm : 0 < ‖y‖ := norm_pos_iff.mpr hy
  obtain ⟨n, hn⟩ := exists_nat_gt ((R + ‖x‖) / ‖y‖)
  have hnorm : ‖x + (n : K) • y‖ ≤ R := by
    have hxR : x + (n : K) • y ∈ Metric.closedBall (0 : V) R := hR ⟨n, rfl⟩
    simpa [Metric.mem_closedBall, dist_eq_norm, sub_zero] using hxR
  have hny : ‖(n : K)‖ * ‖y‖ ≤ R + ‖x‖ := by
    calc
      ‖(n : K)‖ * ‖y‖ = ‖(n : K) • y‖ := by
        simpa using (norm_smul (n : K) y).symm
      _ = ‖(x + (n : K) • y) - x‖ := by simp
      _ ≤ ‖x + (n : K) • y‖ + ‖x‖ := norm_sub_le _ _
      _ ≤ R + ‖x‖ := add_le_add hnorm le_rfl
  have hgt' : R + ‖x‖ < (n : ℝ) * ‖y‖ := (div_lt_iff₀ hy_norm).mp hn
  have hgt : R + ‖x‖ < ‖(n : K)‖ * ‖y‖ := by
    calc
      R + ‖x‖ < (n : ℝ) * ‖y‖ := hgt'
      _ = ‖(n : K)‖ * ‖y‖ := by simp [norm_natCast]
  exact not_lt_of_ge hny hgt

omit [FloorSemiring K] in
private theorem lineal_eq_singleton_zero_of_nonempty_of_isBounded
    {C : Set V} (hC_nonempty : C.Nonempty) (hC_bounded : Bornology.IsBounded C) :
    lin[K](C) = ({0} : Set V) := by
  ext y
  constructor
  · intro hy
    rcases hC_nonempty with ⟨x, hx⟩
    have hy_forall := Set.mem_lineal_iff_forall.mp hy
    have hrange_subset : Set.range (fun n : ℕ ↦ x + (n : K) • y) ⊆ C := by
      rintro _ ⟨n, rfl⟩
      simpa using hy_forall.2 x hx (n : K) (Nat.cast_nonneg n)
    by_cases hy_zero : y = 0
    · simp [hy_zero]
    · exact False.elim <|
        not_isBounded_range_add_natCast_smul x y hy_zero (hC_bounded.subset hrange_subset)
  · intro hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    rw [Set.mem_lineal_iff]
    constructor <;> simpa using (zero_mem_recessionCone (R := K) C)

/-- Text 19.0.14: if `C` is convex and bounded in an ordered normed `K`-space, and at least one
of `S`
or `C` is nonempty, then the set `{y | y +ᵥ S = C}` of translation vectors carrying `S` onto `C`
is itself a polytope, possibly empty. Specializing to `K = ℝ`,
`E = EuclideanSpace ℝ (Fin n)`, and `S.Nonempty` recovers the textbook `ℝ^n` statement. -/
theorem isPolytope_translationCover_of_convex_of_isBounded
    {S C : Set V} (hC_convex : Convex K C) (hC_bounded : Bornology.IsBounded C)
    (hSC_nonempty : S.Nonempty ∨ C.Nonempty) :
    ((translationCover S C : Set V)).IsPolytope K := by
  classical
  by_cases hcover_nonempty : ((translationCover S C : Set V)).Nonempty
  · rcases hcover_nonempty with ⟨y₀, hy₀⟩
    have hy₀_cover : y₀ +ᵥ S = C := Set.mem_translationCover_iff.mp hy₀
    have hC_nonempty : C.Nonempty := by
      rcases hSC_nonempty with hS_nonempty | hC_nonempty
      · rcases hS_nonempty with ⟨s, hs⟩
        refine ⟨y₀ +ᵥ s, ?_⟩
        have hs_cover : y₀ +ᵥ s ∈ y₀ +ᵥ S := by
          rw [Set.mem_vadd_set]
          exact ⟨s, hs, rfl⟩
        simpa [hy₀_cover] using hs_cover
      · exact hC_nonempty
    have hlineal :
        lin[K](C) = ({0} : Set V) :=
      lineal_eq_singleton_zero_of_nonempty_of_isBounded
        hC_nonempty hC_bounded
    have hcover_eq : (translationCover S C : Set V) = ({y₀} : Set V) := by
      calc
        (translationCover S C : Set V) = y₀ +ᵥ lin[K](C) :=
          translationCover_eq_vadd_lineal hC_convex hy₀
        _ = y₀ +ᵥ ({0} : Set V) := by simp [hlineal]
        _ = ({y₀} : Set V) := by simp
    rw [hcover_eq]
    exact ⟨{y₀}, Set.finite_singleton y₀, by simp [convexHull_singleton]⟩
  · have hcover_eq : (translationCover S C : Set V) = (∅ : Set V) :=
      Set.not_nonempty_iff_eq_empty.mp hcover_nonempty
    rw [hcover_eq]
    exact ⟨∅, Set.finite_empty, by simp [convexHull_empty]⟩

/-- Field-generic polytope form: if `C` is a `K`-polytope in an ordered normed `K`-space and
bounded, and at least one of `S` or `C` is nonempty, then the set `{y | y +ᵥ S = C}` of
translation vectors carrying `S` onto `C` is itself a `K`-polytope, possibly empty. -/
theorem Set.IsPolytope.translationCover_of_isBounded
    {S C : Set V} (hC : C.IsPolytope K) (hC_bounded : Bornology.IsBounded C)
    (hSC_nonempty : S.Nonempty ∨ C.Nonempty) :
    ((translationCover S C : Set V)).IsPolytope K := by
  exact isPolytope_translationCover_of_convex_of_isBounded
    (hC.convex) hC_bounded hSC_nonempty

/-- Text 19.0.14, scalar-generic polytope form: if `C` is a `K`-polytope in an ordered normed
`K`-space and at least one of `S` or `C` is nonempty, then `{y | y +ᵥ S = C}` is a
`K`-polytope. -/
theorem Set.IsPolytope.translationCover
    [OrderClosedTopology K] [CompactIccSpace K]
    {S C : Set V} (hC : C.IsPolytope K) (hSC_nonempty : S.Nonempty ∨ C.Nonempty) :
    ((translationCover S C : Set V)).IsPolytope K := by
  refine hC.translationCover_of_isBounded ?_ hSC_nonempty
  rcases hC.exists_finset with ⟨t, rfl⟩
  exact (t.finite_toSet.isCompact_convexHull K).isBounded

end Normed

end
