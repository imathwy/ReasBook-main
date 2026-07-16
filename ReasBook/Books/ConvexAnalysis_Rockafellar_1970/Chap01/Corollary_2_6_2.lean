import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_2_5_10

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators Pointwise Rockafellar

universe u v

/-
Source/core/bridge triage:
- `source-facing`: Corollary 2.6.2 describes the carrier of the generated convex cone as the set
  of all finite positive linear combinations of a subset of an additive commutative monoid with
  distributive scalar action over an ordered semiring.
- `core/canonical`: mathlib's owner abstraction for the smallest convex cone containing `S` is
  `ConvexCone.hull R S`.
- `bridge/view`: this file should expose only the carrier-description theorem relating the source
  presentation to the owner abstraction, using the canonical hull API rather than a parallel local
  set owner.
- Primitive data vs derived API: `S` is the only primitive datum; the finite-support coefficient
  family is the derived witness datum, while the closure properties of the positive-combination
  set are derived local bridge lemmas (`Set.IsCone` plus additive closure) used to apply
  `Set.IsCone.hull_eq`.
- Domain-style sampling: this item is guided by `ConvexCone`, `ConvexCone.hull`,
  `ConvexCone.hull_le_iff`, and `ConvexCone.subset_hull`.
- Layer target: `bridge/view`.
-/

namespace Set

variable {R : Type v} [Zero R] [LT R]
variable {E : Type u} [AddCommMonoid E] [SMul R E]

/-- The set of finite positive linear combinations of points of `S`, encoded via finitely
supported nonzero coefficients whose support lies in `S`. -/
def positiveLinearCombination (R : Type v) [Zero R] [LT R]
    {E : Type u} [AddCommMonoid E] [SMul R E] (S : Set E) : Set E :=
  {x | ∃ c : E →₀ R,
    c ≠ 0 ∧
    (∀ y ∈ c.support, y ∈ S) ∧
    (∀ y ∈ c.support, 0 < c y) ∧
    c.sum (fun y a ↦ a • y) = x}

/-- Textbook shorthand for finite positive linear combinations of points of a set. -/
scoped[Rockafellar] notation:max "cone⁺[" r "] " s => Set.positiveLinearCombination r s

@[simp] theorem mem_positiveLinearCombination (S : Set E) {x : E} :
    x ∈ (cone⁺[R] S) ↔
      ∃ c : E →₀ R,
        c ≠ 0 ∧
        (∀ y ∈ c.support, y ∈ S) ∧
        (∀ y ∈ c.support, 0 < c y) ∧
        c.sum (fun y a ↦ a • y) = x :=
  Iff.rfl

end Set

private theorem coeff_nonneg {R : Type v} [Zero R] [Preorder R] {E : Type u} {c : E →₀ R}
    (hcpos : ∀ y ∈ c.support, 0 < c y) :
    ∀ z, 0 ≤ c z := by
  intro z
  by_cases hz : z ∈ c.support
  · exact le_of_lt (hcpos z hz)
  · have hz0 : c z = 0 := by simpa [Finsupp.mem_support_iff] using hz
    simp [hz0]

section HullCharacterization

-- Minimal scalar-order layer used in this file: positivity of products (`mul_pos`),
-- additive monotonicity for strict/non-strict positivity lemmas, and `0 < 1`.
-- This avoids the stronger bundled assumption `IsStrictOrderedRing`.
variable {R : Type v} [Semiring R] [PartialOrder R]
variable [AddLeftMono R] [AddLeftStrictMono R]
variable [ZeroLEOneClass R] [Nontrivial R] [PosMulStrictMono R]
variable {E : Type u} [AddCommMonoid E] [Module R E]

omit [AddLeftMono R] [AddLeftStrictMono R] [ZeroLEOneClass R] [Nontrivial R] in
private theorem smul_mem_positiveLinearCombinationSet (S : Set E) :
    ∀ ⦃r : R⦄, 0 < r → ∀ ⦃x : E⦄, x ∈ (cone⁺[R] S) →
      r • x ∈ (cone⁺[R] S) := by
  intro r hr x hx
  rcases hx with ⟨c, hcn, hcS, hcpos, rfl⟩
  refine ⟨r • c, ?_, ?_, ?_, ?_⟩
  · refine Finsupp.support_nonempty_iff.1 ?_
    rcases (Finsupp.support_nonempty_iff.2 hcn) with ⟨y, hy⟩
    refine ⟨y, ?_⟩
    rw [Finsupp.mem_support_iff]
    have hy' : 0 < (r • c) y := by
      simpa [Pi.smul_apply, smul_eq_mul] using mul_pos hr (hcpos y hy)
    exact ne_of_gt hy'
  · intro y hy
    exact hcS y (Finsupp.support_smul hy)
  · intro y hy
    exact mul_pos hr (hcpos y (Finsupp.support_smul hy))
  · calc
      (r • c).sum (fun y a ↦ a • y) = c.sum (fun y a ↦ (r * a) • y) := by
        exact (c.sum_smul_index (fun _ ↦ by simp) :
          (r • c).sum (fun y a ↦ a • y) = c.sum (fun y a ↦ (r * a) • y))
      _ = r • c.sum (fun y a ↦ a • y) := by
        rw [Finsupp.smul_sum]
        congr with y a
        rw [smul_smul]

omit [ZeroLEOneClass R] [Nontrivial R] [PosMulStrictMono R] in
private theorem add_mem_positiveLinearCombinationSet (S : Set E) :
    ∀ ⦃x y : E⦄,
      x ∈ (cone⁺[R] S) →
      y ∈ (cone⁺[R] S) →
      x + y ∈ (cone⁺[R] S) := by
  classical
  intro x y hx hy
  rcases hx with ⟨c, hcn, hcS, hcpos, rfl⟩
  rcases hy with ⟨d, _hdn, hdS, hdpos, rfl⟩
  refine ⟨c + d, ?_, ?_, ?_, ?_⟩
  · refine Finsupp.support_nonempty_iff.1 ?_
    rcases (Finsupp.support_nonempty_iff.2 hcn) with ⟨z, hz⟩
    refine ⟨z, ?_⟩
    rw [Finsupp.mem_support_iff]
    have hz' : 0 < (c + d) z := by
      simpa [Finsupp.add_apply] using
        add_pos_of_pos_of_nonneg (hcpos z hz) (coeff_nonneg hdpos z)
    exact ne_of_gt hz'
  · intro z hz
    rcases Finset.mem_union.mp (Finsupp.support_add hz) with hzc | hzd
    · exact hcS z hzc
    · exact hdS z hzd
  · intro z hz
    rcases Finset.mem_union.mp (Finsupp.support_add hz) with hzc | hzd
    · simpa [Finsupp.add_apply] using
        add_pos_of_pos_of_nonneg (hcpos z hzc) (coeff_nonneg hdpos z)
    · simpa [Finsupp.add_apply] using
        add_pos_of_nonneg_of_pos (coeff_nonneg hcpos z) (hdpos z hzd)
  · simpa using
      (c.sum_add_index
        (fun _ _ ↦ by simp)
        (fun z _ a b ↦ add_smul a b z) :
          (c + d).sum (fun z a ↦ a • z) =
            c.sum (fun z a ↦ a • z) + d.sum (fun z a ↦ a • z))

namespace Set

-- Every point of `S` is a finite positive linear combination of points of `S`
-- (singleton witness with coefficient `1`).
omit [AddLeftMono R] [AddLeftStrictMono R] [PosMulStrictMono R] in
theorem subset_positiveLinearCombination (S : Set E) :
    S ⊆ (cone⁺[R] S) := by
  intro y hy
  refine ⟨Finsupp.single y 1, Finsupp.single_ne_zero.2 one_ne_zero, ?_, ?_, ?_⟩
  · intro z hz
    have hzy : z = y := by simpa [Finsupp.support_single_ne_zero] using hz
    simpa [hzy] using hy
  · intro z hz
    have hzy : z = y := by simpa [Finsupp.support_single_ne_zero] using hz
    simp [hzy]
  · simp

-- The finite positive linear-combination carrier is a cone in the source-facing owner
-- sense of Definition 2.5.9.
omit [AddLeftMono R] [AddLeftStrictMono R] [ZeroLEOneClass R] [Nontrivial R] in
theorem isCone_positiveLinearCombination (S : Set E) :
    Set.IsCone R (cone⁺[R] S) := by
  intro r hr x hx
  exact smul_mem_positiveLinearCombinationSet (S := S) hr hx

-- The finite positive linear-combination carrier is closed under pointwise set addition.
omit [ZeroLEOneClass R] [Nontrivial R] [PosMulStrictMono R] in
theorem add_subset_positiveLinearCombination (S : Set E) :
    (cone⁺[R] S) + (cone⁺[R] S) ⊆ (cone⁺[R] S) := by
  intro z hz
  rcases hz with ⟨x, hx, y, hy, rfl⟩
  exact add_mem_positiveLinearCombinationSet (S := S) hx hy

end Set

omit [AddLeftMono R] [AddLeftStrictMono R]
  [ZeroLEOneClass R] [Nontrivial R] [PosMulStrictMono R] in
private theorem positiveLinearCombination_subset_hull (S : Set E) :
    (cone⁺[R] S) ⊆ ConvexCone.hull R S := by
  intro x hx
  rcases hx with ⟨c, hcn, hcS, hcpos, rfl⟩
  have hcn' : c.support.Nonempty := Finsupp.support_nonempty_iff.2 hcn
  have hterm : ∀ y ∈ c.support, c y • y ∈ ConvexCone.hull R S := by
    intro y hy
    exact (ConvexCone.hull R S).smul_mem (hcpos y hy) (ConvexCone.subset_hull (hcS y hy))
  have hsum_mem :
      ∀ s : Finset E, s.Nonempty →
        (∀ y ∈ s, c y • y ∈ ConvexCone.hull R S) →
        s.sum (fun y ↦ c y • y) ∈ ConvexCone.hull R S := by
    intro s hs hs_mem
    revert hs_mem
    refine hs.cons_induction ?_ ?_
    · intro y hs_mem
      simpa only [Finset.sum_singleton] using hs_mem y (by simp)
    · intro y t hy ht ih hs_mem
      have hy_mem : c y • y ∈ ConvexCone.hull R S := hs_mem y (by simp)
      have ht_mem : ∀ z ∈ t, c z • z ∈ ConvexCone.hull R S := by
        intro z hz
        exact hs_mem z (by simp [hz])
      simpa [Finset.sum_cons, hy] using
        (ConvexCone.hull R S).add_mem hy_mem (ih ht_mem)
  simpa using hsum_mem c.support hcn' hterm

namespace ConvexCone

/-- Corollary 2.6.2 owner bridge: the carrier of the convex-cone hull of `S` is exactly the set
of finite positive linear combinations of points of `S`. -/
-- Proof sketch: the positive-combination carrier is itself a convex-cone owner containing `S`,
-- so `hull R S` maps into `hull R (cone⁺[R] S)` and this hull is fixed by `Set.IsCone.hull_eq`;
-- the converse is the finite-sum closure argument in `positiveLinearCombination_subset_hull`.
theorem hull_eq_positiveLinearCombination (S : Set E) :
    (ConvexCone.hull R S : Set E) = (cone⁺[R] S) := by
  ext x
  constructor
  · intro hx
    have hmono : (ConvexCone.hull R S : ConvexCone R E) ≤ ConvexCone.hull R (cone⁺[R] S) :=
      ConvexCone.hull_min
        (fun y hy ↦ ConvexCone.subset_hull ((Set.subset_positiveLinearCombination (R := R) S) hy))
    have hx' : x ∈ (ConvexCone.hull R (cone⁺[R] S) : Set E) := hmono hx
    have hfix :
        (ConvexCone.hull R (cone⁺[R] S) : Set E) = (cone⁺[R] S) :=
      (Set.isCone_positiveLinearCombination (R := R) (S := S)).hull_eq
        (Set.add_subset_positiveLinearCombination (R := R) S)
    exact hfix ▸ hx'
  · intro hx
    exact positiveLinearCombination_subset_hull S hx

/-- Corollary 2.6.2: a point lies in the convex-cone hull of `S` exactly when it is a finite
positive linear combination of points of `S`. -/
theorem mem_hull_iff_mem_positiveLinearCombination (S : Set E) {x : E} :
    x ∈ ConvexCone.hull R S ↔ x ∈ (cone⁺[R] S) := by
  have hEq : (ConvexCone.hull R S : Set E) = (cone⁺[R] S) :=
    ConvexCone.hull_eq_positiveLinearCombination (R := R) (S := S)
  constructor
  · intro hx
    exact hEq ▸ hx
  · intro hx
    change x ∈ (ConvexCone.hull R S : Set E)
    exact hEq.symm ▸ hx

/-- Corollary 2.6.2 in witness form: a point lies in the convex-cone hull of `S` exactly when it
admits a finite positive linear-combination witness on `S`. -/
theorem mem_hull_iff_exists_positiveLinearCombination (S : Set E) {x : E} :
    x ∈ ConvexCone.hull R S ↔
      ∃ c : E →₀ R,
        c ≠ 0 ∧
        (∀ y ∈ c.support, y ∈ S) ∧
        (∀ y ∈ c.support, 0 < c y) ∧
        c.sum (fun y a ↦ a • y) = x := by
  exact
    (mem_hull_iff_mem_positiveLinearCombination (S := S) (x := x)).trans
      (Set.mem_positiveLinearCombination (R := R) (S := S))

end ConvexCone

end HullCharacterization
