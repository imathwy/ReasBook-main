import Mathlib
import Mathlib.Geometry.Convex.Cone.Pointed

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_2_6_1 (from Chap01) -/
open scoped Pointwise Rockafellar

universe u
universe v

variable {R : Type v} [DivisionSemiring R] [PartialOrder R] [PosMulReflectLT R]
  [ZeroLEOneClass R] [AddLeftMono R]
variable {E : Type u} [AddCommMonoid E] [Module R E]

/-
Source/core/bridge triage:
- `source-facing`: Corollary 2.6.1 says that a subset of a module over a partially ordered
  division semiring is a convex cone exactly when it contains
  every finite positive linear combination of its elements.
- `core/canonical`: the source owner remains `Set.IsConvexCone R K`; finite positive
  combinations are exposed on theorem surfaces by the chapter notation `cone⁺[R] K`.
- `bridge/view`: this item is proved directly on the source-facing layer: finite-support
  positive-combination witnesses are consumed by cone closure plus additive closure, and the
  converse direction reconstructs cone closure and additive closure from singleton/two-point
  witnesses before applying `Set.IsCone.convex_of_add_subset`.
- Primitive data vs derived API: the subset `K` is the only primitive datum. The positive
  combination witness is derived theorem data, canonically packaged by a `Finsupp`; the
  closure criteria are derived proof data rather than part of the public file surface.
- Domain-style sampling: this item is guided by `Set.IsCone.smul_mem`, `Set.IsConvexCone.add_mem`,
  `Set.IsCone.convex_of_add_subset`, and `cone⁺[R]`.
- Layer target: `source-facing`.
-/

namespace Set

/-- Helper for Corollary 2.6.1: the file-local carrier of finite positive linear combinations of
points of `S`, encoded by a nonzero finitely supported coefficient family with positive support
contained in `S`. -/
def positiveLinearCombinationCarrier (R : Type v) [Zero R] [LT R]
    {E : Type u} [AddCommMonoid E] [SMul R E] (S : Set E) : Set E :=
  {x | ∃ c : E →₀ R,
    c ≠ 0 ∧
    (∀ y ∈ c.support, y ∈ S) ∧
    (∀ y ∈ c.support, 0 < c y) ∧
    c.sum (fun y a ↦ a • y) = x}

/-- Helper for Corollary 2.6.1: the textbook shorthand for the positive linear-combination
carrier. -/
scoped[Rockafellar] notation:max "cone⁺[" r "] " s => Set.positiveLinearCombinationCarrier r s

/-- Helper for Corollary 2.6.1: membership in the positive linear-combination carrier is exactly
the existence of a positive finitely supported witness. -/
@[simp] theorem mem_positiveLinearCombinationCarrier (S : Set E) {x : E} :
    x ∈ (cone⁺[R] S) ↔
      ∃ c : E →₀ R,
        c ≠ 0 ∧
        (∀ y ∈ c.support, y ∈ S) ∧
        (∀ y ∈ c.support, 0 < c y) ∧
        c.sum (fun y a ↦ a • y) = x :=
  Iff.rfl

end Set

/- Corollary 2.6.1: a subset of a module over a partially ordered division semiring is a convex
cone exactly when it contains every finite positive linear combination of its elements. -/
-- Proof sketch: the forward implication evaluates finite-support positive-combination witnesses
-- by induction on support using cone closure and additive closure of a convex cone. The reverse
-- implication reconstructs cone closure and additive closure from singleton/two-point witnesses
-- before applying `Set.IsCone.convex_of_add_subset`.
namespace Set.IsConvexCone

/-- Helper for Corollary 2.6.1: a finite positive linear combination of points of a convex cone
still belongs to that cone. -/
theorem finsupp_sum_mem_of_positive_support {K : Set E} (hK : Set.IsConvexCone R K)
    {c : E →₀ R} (hcn : c ≠ 0)
    (hcK : ∀ y ∈ c.support, y ∈ K)
    (hcpos : ∀ y ∈ c.support, 0 < c y) :
    c.sum (fun y a ↦ a • y) ∈ K := by
  -- Each supported term belongs to `K` by positive scalar closure.
  have hterm : ∀ y ∈ c.support, c y • y ∈ K := by
    intro y hy
    exact hK.isCone.smul_mem (hcpos y hy) (hcK y hy)
  have hcn' : c.support.Nonempty := Finsupp.support_nonempty_iff.2 hcn
  -- A nonempty finite sum of supported terms stays in `K` by repeated additive closure.
  have hsum_mem :
      ∀ s : Finset E, s.Nonempty →
        (∀ y ∈ s, c y • y ∈ K) →
        s.sum (fun y ↦ c y • y) ∈ K := by
    intro s hs hs_mem
    revert hs_mem
    refine hs.cons_induction ?_ ?_
    · intro y hs_mem
      have hy_mem : y ∈ ({y} : Finset E) := by simp
      simpa [Finset.sum_singleton] using hs_mem y hy_mem
    · intro y t hy ht ih hs_mem
      have hy_cons : y ∈ Finset.cons y t hy := by simp [Finset.mem_cons]
      have hy_mem : c y • y ∈ K := hs_mem y hy_cons
      have ht_mem : t.sum (fun z ↦ c z • z) ∈ K := by
        apply ih
        intro z hz
        have hz_cons : z ∈ Finset.cons y t hy := by simp [Finset.mem_cons, hz]
        exact hs_mem z hz_cons
      simpa [Finset.sum_cons, hy] using hK.add_mem hy_mem ht_mem
  exact hsum_mem c.support hcn' hterm

/-- Helper for Corollary 2.6.1: containment of all positive linear combinations reconstructs
positive-scalar closure, hence a cone structure. -/
theorem isCone_of_positiveLinearCombination_subset {K : Set E}
    (hPos : (cone⁺[R] K) ⊆ K) :
    Set.IsCone R K := by
  intro c hc x hx
  have hsingle_ne : Finsupp.single x c ≠ 0 := Finsupp.single_ne_zero.2 hc.ne'
  -- The singleton witness keeps support and positivity aligned with the target point.
  have hsupport_mem : ∀ y ∈ (Finsupp.single x c).support, y ∈ K := by
    intro y hy
    have hyx : y = x := by
      simpa [Finsupp.support_single_ne_zero x hc.ne'] using hy
    simpa [hyx] using hx
  have hsupport_pos : ∀ y ∈ (Finsupp.single x c).support, 0 < (Finsupp.single x c) y := by
    intro y hy
    have hyx : y = x := by
      simpa [Finsupp.support_single_ne_zero x hc.ne'] using hy
    simpa [hyx] using hc
  have hsum :
      (Finsupp.single x c).sum (fun y a ↦ a • y) = c • x := by
    simp
  have hx_combo : c • x ∈ (cone⁺[R] K) := by
    exact ⟨Finsupp.single x c, hsingle_ne, hsupport_mem, hsupport_pos, hsum⟩
  exact hPos hx_combo

/-- Helper for Corollary 2.6.1: if a set contains all of its finite positive linear combinations,
then it is a convex cone. -/
theorem of_positiveLinearCombination_subset {K : Set E}
    (hPos : (cone⁺[R] K) ⊆ K) :
    Set.IsConvexCone R K := by
  -- Route correction: use the source proof directly by first recovering cone closure and
  -- additive closure, then invoke Theorem 2.6's cone-to-convex bridge.
  have hcone : Set.IsCone R K := isCone_of_positiveLinearCombination_subset (R := R) hPos
  have hadd : K + K ⊆ K := by
    classical
    intro z hz
    rcases hz with ⟨x, hx, y, hy, rfl⟩
    by_cases hxy : x = y
    · subst hxy
      -- When the two points coincide, the sum is a positive scalar multiple.
      have htwo_pos : (0 : R) < 2 := zero_lt_two
      have htwo_mem : (2 : R) • x ∈ K := hcone.smul_mem htwo_pos hx
      simpa [two_smul] using htwo_mem
    · -- When the points are distinct, the sum itself is a two-point positive combination.
      have hne : Finsupp.single x (1 : R) + Finsupp.single y (1 : R) ≠ 0 := by
        intro hzero
        have hxzero :
            (Finsupp.single x (1 : R) + Finsupp.single y (1 : R)) x = 0 := by
          simp [hzero]
        have hxone :
            (Finsupp.single x (1 : R) + Finsupp.single y (1 : R)) x = 1 := by
          simp [Finsupp.add_apply, hxy]
        exact one_ne_zero (hxone.symm.trans hxzero)
      have hsupport_mem :
          ∀ w ∈ (Finsupp.single x (1 : R) + Finsupp.single y (1 : R)).support, w ∈ K := by
        intro w hw
        have hw_union :
            w ∈ (Finsupp.single x (1 : R)).support ∪ (Finsupp.single y (1 : R)).support :=
          Finsupp.support_add hw
        rcases Finset.mem_union.mp hw_union with hwx | hwy
        · have hwx' : w = x := by
            simpa [Finsupp.support_single_ne_zero x (one_ne_zero : (1 : R) ≠ 0)] using hwx
          simpa [hwx'] using hx
        · have hwy' : w = y := by
            simpa [Finsupp.support_single_ne_zero y (one_ne_zero : (1 : R) ≠ 0)] using hwy
          simpa [hwy'] using hy
      have hsupport_pos :
          ∀ w ∈ (Finsupp.single x (1 : R) + Finsupp.single y (1 : R)).support,
            0 < (Finsupp.single x (1 : R) + Finsupp.single y (1 : R)) w := by
        intro w hw
        have hw_union :
            w ∈ (Finsupp.single x (1 : R)).support ∪ (Finsupp.single y (1 : R)).support :=
          Finsupp.support_add hw
        rcases Finset.mem_union.mp hw_union with hwx | hwy
        · have hwx' : w = x := by
            simpa [Finsupp.support_single_ne_zero x (one_ne_zero : (1 : R) ≠ 0)] using hwx
          simp [Finsupp.add_apply, hwx', hxy]
        · have hwy' : w = y := by
            simpa [Finsupp.support_single_ne_zero y (one_ne_zero : (1 : R) ≠ 0)] using hwy
          simp [Finsupp.add_apply, hwy', hxy]
      have hz_combo : x + y ∈ (cone⁺[R] K) := by
        refine ⟨Finsupp.single x (1 : R) + Finsupp.single y (1 : R), hne,
          hsupport_mem, hsupport_pos, ?_⟩
        -- Compute the witness sum by splitting the two singleton contributions.
        rw [Finsupp.sum_add_index (by simp) (fun _ a b ↦ by simp [add_smul])]
        rw [Finsupp.sum_single_index (by simp), Finsupp.sum_single_index (by simp)]
        simp
      exact hPos hz_combo
  exact ⟨hcone, hcone.convex_of_add_subset hadd⟩

/-- Corollary 2.6.1 in owner-prefixed form: a subset is a convex cone exactly when it contains
all finite positive linear combinations of its points. -/
theorem iff_positiveLinearCombination_subset (K : Set E) :
    Set.IsConvexCone R K ↔ (cone⁺[R] K) ⊆ K := by
  constructor
  · intro hK x hx
    rcases (Set.mem_positiveLinearCombinationCarrier (R := R) (S := K)).1 hx with
      ⟨c, hcn, hcK, hcpos, hsum⟩
    -- The forward implication is the source proof: evaluate the finite positive combination.
    have hmem : c.sum (fun y a ↦ a • y) ∈ K :=
      hK.finsupp_sum_mem_of_positive_support hcn hcK hcpos
    simpa [hsum] using hmem
  · intro hPos
    -- The reverse implication rebuilds the cone and addition axioms from witnesses.
    exact of_positiveLinearCombination_subset (R := R) hPos

end Set.IsConvexCone

/-! ### Corollary_2_6_2 (from Chap01) -/
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

/-! ### Corollary_2_6_3 (from Chap01) -/
open scoped Pointwise Rockafellar

universe u v

variable {R : Type v} [Semifield R] [PartialOrder R] [IsOrderedRing R] [PosMulReflectLT R]
variable {E : Type u} [AddCommMonoid E] [Module R E]

local notation "R>0" => Set.Ioi (0 : R)
local notation "R≥0" => Set.Ici (0 : R)

/-
Source/core/bridge triage:
- `source-facing`: Corollary 2.6.3 identifies the convex cone generated by a convex set
  `C ⊆ E` with the origin together with the positive ray through `C`.
- `core/canonical`: in this chapter the generated-cone owner is `PointedCone.hull R C`, not
  `ConvexCone.hull R C`; the latter drops the origin and therefore changes the source semantics.
- `bridge/view`: the source proof controls `insert 0 (R≥0 • C)` directly and packages it as a
  pointed cone via `PointedCone.ofConeComb`, so the final equality comes from hull minimality plus
  the obvious reverse inclusion.
- Primitive data vs derived API: the primitive source data are the set `C` and its convexity.
  The positive-ray carrier description is derived owner API from `PointedCone.hull R C`.
- Domain-style sampling: this refinement is governed by the project owner declarations
  `PointedCone.hull` from Definition 2.6.10,
  `PointedCone.ofConeComb`, `PointedCone.subset_hull`, `Submodule.span_le`, and the mathlib
  convexity owner `Convex`.
- Layer target: `source-facing`, expressed directly through the chapter owner `PointedCone.hull`.
-/

namespace PointedCone

/-- Helper for Corollary 2.6.3: the origin belongs to the inserted nonnegative ray. -/
lemma zero_mem_insert_zero_nonnegativeRay (C : Set E) :
    (0 : E) ∈ insert 0 (R≥0 • C) := by
  simp

/-- Helper for Corollary 2.6.3: every point of `C` lies in the inserted nonnegative ray via the
scalar `1`. -/
lemma subset_insert_zero_nonnegativeRay (C : Set E) :
    C ⊆ insert 0 (R≥0 • C) := by
  intro x hx
  right
  exact Set.mem_smul.mpr ⟨1, zero_le_one, x, hx, one_smul R x⟩

/-- Helper for Corollary 2.6.3: a nonnegative conical combination of two nonnegative ray points
over a convex set stays on the same nonnegative ray. -/
lemma smul_add_smul_mem_nonnegativeRay_of_convex
    (C : Set E) (hC : Convex R C) {a b r s : R} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hr : 0 ≤ r) (hs : 0 ≤ s) {z w : E} (hz : z ∈ C) (hw : w ∈ C) :
    a • (r • z) + b • (s • w) ∈ R≥0 • C := by
  let p : R := a * r
  let q : R := b * s
  have hp0 : 0 ≤ p := mul_nonneg ha hr
  have hq0 : 0 ≤ q := mul_nonneg hb hs
  by_cases hpq0 : p + q = 0
  · have hpq : p = 0 ∧ q = 0 := (add_eq_zero_iff_of_nonneg hp0 hq0).1 hpq0
    have hp : p = 0 := hpq.1
    have hq : q = 0 := hpq.2
    -- If the total weight vanishes, the whole combination is the zero multiple of any point of `C`.
    exact Set.mem_smul.mpr ⟨0, by simp, z, hz, by
      simp [p, q, hp, hq, smul_smul]⟩
  · have hpq : 0 < p + q :=
      lt_of_le_of_ne (add_nonneg hp0 hq0) (Ne.symm hpq0)
    have hweights : p / (p + q) + q / (p + q) = 1 := by
      field_simp [hpq.ne']
    have hu : (p / (p + q)) • z + (q / (p + q)) • w ∈ C :=
      hC hz hw (div_nonneg hp0 hpq.le) (div_nonneg hq0 hpq.le) hweights
    have hrepr :
        a • (r • z) + b • (s • w) =
          (p + q) • ((p / (p + q)) • z + (q / (p + q)) • w) := by
      -- Normalize by the positive total weight to expose a convex combination inside `C`.
      calc
        a • (r • z) + b • (s • w) = p • z + q • w := by
          simp [p, q, smul_smul]
        _ = (p + q) • ((p / (p + q)) • z + (q / (p + q)) • w) := by
          symm
          rw [smul_add, smul_smul, smul_smul]
          congr 1 <;> field_simp [hpq.ne']
    exact Set.mem_smul.mpr ⟨p + q, hpq.le, _, hu, hrepr.symm⟩

/-- Helper for Corollary 2.6.3: `insert 0 (R≥0 • C)` is closed under two-point conical
combinations whenever `C` is convex. -/
lemma insert_zero_nonnegativeRay_closed_under_cone_combination
    (C : Set E) (hC : Convex R C) :
    ∀ x ∈ insert 0 (R≥0 • C), ∀ y ∈ insert 0 (R≥0 • C), ∀ a : R, 0 ≤ a → ∀ b : R, 0 ≤ b →
      a • x + b • y ∈ insert 0 (R≥0 • C) := by
  intro x hx y hy a ha b hb
  rcases hx with rfl | hx
  · rcases hy with rfl | hy
    · -- The zero-zero branch is immediate.
      left
      simp
    · rcases Set.mem_smul.mp hy with ⟨r, hr, z, hz, rfl⟩
      -- Scaling a nonnegative-ray point by another nonnegative scalar stays on the same ray.
      right
      exact Set.mem_smul.mpr ⟨b * r, mul_nonneg hb hr, z, hz, by simp [smul_smul]⟩
  · rcases Set.mem_smul.mp hx with ⟨r, hr, z, hz, rfl⟩
    rcases hy with rfl | hy
    · -- This is the symmetric zero branch.
      right
      exact Set.mem_smul.mpr ⟨a * r, mul_nonneg ha hr, z, hz, by simp [smul_smul]⟩
    · rcases Set.mem_smul.mp hy with ⟨s, hs, w, hw, rfl⟩
      -- The hard branch is the source proof: normalize by the total weight and use convexity.
      right
      exact smul_add_smul_mem_nonnegativeRay_of_convex
        (C := C) hC ha hb hr hs hz hw

/-- Helper for Corollary 2.6.3: the generated cone lies in the inserted nonnegative ray of a
convex set. -/
lemma cone_subset_insert_zero_nonnegativeRay_of_convex
    (C : Set E) (hC : Convex R C) :
    (cone[R] C : Set E) ⊆ insert 0 (R≥0 • C) := by
  let K : PointedCone R E :=
    PointedCone.ofConeComb (insert 0 (R≥0 • C))
      ⟨0, zero_mem_insert_zero_nonnegativeRay (R := R) (E := E) C⟩
      (insert_zero_nonnegativeRay_closed_under_cone_combination (R := R) (C := C) hC)
  have hsubset : C ⊆ (K : Set E) := by
    simpa [K] using subset_insert_zero_nonnegativeRay (R := R) (E := E) C
  have hHull_le : (cone[R] C : PointedCone R E) ≤ K := Submodule.span_le.mpr hsubset
  intro x hx
  have hxK : x ∈ K := hHull_le hx
  simpa [K] using hxK

/-- Helper for Corollary 2.6.3: the inserted nonnegative ray is contained in the generated cone. -/
lemma insert_zero_nonnegativeRay_subset_cone (C : Set E) :
    insert 0 (R≥0 • C) ⊆ (cone[R] C : Set E) := by
  intro x hx
  rcases hx with rfl | hx
  · -- The pointed cone hull already contains the origin.
    exact (cone[R] C).zero_mem
  · rcases Set.mem_smul.mp hx with ⟨r, hr, y, hy, rfl⟩
    -- Start from the generator `y ∈ C` and then close under nonnegative scaling in the hull.
    exact (cone[R] C).smul_mem hr (PointedCone.subset_hull hy)

/-- Helper for Corollary 2.6.3: adjoining the origin converts the strict positive ray into the
nonnegative ray. -/
lemma insert_zero_positiveRay_eq_insert_zero_nonnegativeRay (C : Set E) :
    insert 0 (R>0 • C) = insert 0 (R≥0 • C) := by
  ext x
  constructor
  · intro hx
    rcases hx with rfl | hx
    · left
      rfl
    · rcases Set.mem_smul.mp hx with ⟨r, hr, y, hy, rfl⟩
      right
      exact Set.mem_smul.mpr ⟨r, hr.le, y, hy, rfl⟩
  · intro hx
    rcases hx with rfl | hx
    · left
      rfl
    · rcases Set.mem_smul.mp hx with ⟨r, hr, y, hy, rfl⟩
      by_cases hr0 : r = 0
      · -- The only new nonnegative-scalar case is `r = 0`, which collapses to the inserted origin.
        left
        simp [hr0]
      · right
        exact Set.mem_smul.mpr ⟨r, lt_of_le_of_ne hr (Ne.symm hr0), y, hy, rfl⟩

/-- Helper for Corollary 2.6.3: if `C` is nonempty, then adjoining the origin to the positive ray
already gives the full nonnegative ray. -/
lemma insert_zero_positiveRay_eq_nonnegativeRay_of_nonempty
    (C : Set E) (hC_nonempty : C.Nonempty) :
    insert 0 (R>0 • C) = R≥0 • C := by
  ext x
  constructor
  · intro hx
    rcases hx with rfl | hx
    · rcases hC_nonempty with ⟨y, hy⟩
      exact Set.mem_smul.mpr ⟨0, by simp, y, hy, by simp⟩
    · rcases Set.mem_smul.mp hx with ⟨r, hr, y, hy, rfl⟩
      exact Set.mem_smul.mpr ⟨r, hr.le, y, hy, rfl⟩
  · intro hx
    rcases Set.mem_smul.mp hx with ⟨r, hr, y, hy, rfl⟩
    by_cases hr0 : r = 0
    · left
      simp [hr0]
    · right
      exact Set.mem_smul.mpr ⟨r, lt_of_le_of_ne hr (Ne.symm hr0), y, hy, rfl⟩

/-- Corollary 2.6.3: if `C` is convex, then the convex cone generated by `C` is exactly the origin
together with the nonnegative ray through `C`. -/
theorem cone_eq_insert_zero_nonnegativeRay_of_convex (C : Set E) (hC : Convex R C) :
    (cone[R] C : Set E) = insert 0 (R≥0 • C) := by
  -- Route correction: avoid the later Corollary 2.6.11 and prove the hull equality directly.
  refine Set.Subset.antisymm ?_ ?_
  · exact cone_subset_insert_zero_nonnegativeRay_of_convex (R := R) (C := C) hC
  · exact insert_zero_nonnegativeRay_subset_cone (R := R) (C := C)

/-- Bridge form of Corollary 2.6.3: if `C` is convex, then the generated cone is exactly the origin
together with the strictly positive ray through `C`. -/
theorem cone_eq_insert_zero_positiveRay_of_convex (C : Set E) (hC : Convex R C) :
    (cone[R] C : Set E) = insert 0 (R>0 • C) := by
  -- After proving the nonnegative-ray form, the positive-ray statement is just the `r = 0` split.
  calc
    (cone[R] C : Set E) = insert 0 (R≥0 • C) :=
      cone_eq_insert_zero_nonnegativeRay_of_convex (R := R) (C := C) hC
    _ = insert 0 (R>0 • C) :=
      (insert_zero_positiveRay_eq_insert_zero_nonnegativeRay (R := R) (E := E) C).symm

/-- Nonempty convex specialization of Corollary 2.6.3 in nonnegative-ray form:
for `C ≠ ∅`, the generated cone is exactly `(R≥0 • C)`. This is the cleaner
source-facing surface; `cone_eq_insert_zero_positiveRay_of_convex` is the empty-set-safe bridge
statement. -/
theorem cone_eq_nonnegativeRay_of_convex (C : Set E) (hC : Convex R C) (hC_nonempty : C.Nonempty) :
    (cone[R] C : Set E) = R≥0 • C := by
  -- For nonempty `C`, the inserted origin is already absorbed by the positive ray.
  calc
    (cone[R] C : Set E) = insert 0 (R>0 • C) :=
      cone_eq_insert_zero_positiveRay_of_convex (R := R) (C := C) hC
    _ = R≥0 • C :=
      insert_zero_positiveRay_eq_nonnegativeRay_of_nonempty (R := R) (E := E) C hC_nonempty

end PointedCone

/-! ### Theorem_2_6 (from Chap01) -/
open scoped Pointwise

universe u v

/- 
Source/core/bridge triage:
- `source-facing`: Theorem 2.6 characterizes convex cones by closure under addition together with
  closure under positive scalar multiplication. The primitive source-facing owner is the cone
  predicate `Set.IsCone R K`; once that is fixed, convexity is exactly additive closure.
- `core/canonical`: convexity itself is read through the canonical criterion
  `convex_iff_add_mem`; no module-only convexity criterion is needed for this item.
  no bundled-cone wrapper is needed in this item.
- `bridge/view`: the reverse direction is the direct cone-plus-convex-combination argument:
  positive-scalar closure from `Set.IsCone` plus pointwise additive closure yields convexity; the
  set-level bridge `K + K ⊆ K` is then a derived restatement.
- Primitive data vs derived API: the primitive source data are `Set.IsCone R K` and pointwise
  additive closure; `K + K ⊆ K` and convexity are derived API.
- Domain-style sampling used here: `Set.IsCone`, `Set.IsCone.smul_mem`, `Set.add_mem_add`,
  `convex_iff_add_mem`, and `add_halves`.
- Layer target: `source-facing`.
-/

/- Definition 2.5.9: the source-facing cone predicate used in Theorem 2.6 is the chapter owner
`Set.IsCone R`. -/
section

variable {R : Type v} [Semiring R] [PartialOrder R]
variable {E : Type u} [AddCommMonoid E] [MulActionWithZero R E]

#check (Set.IsCone R : Set E → Prop)

end

namespace Set.IsCone

section WeakLayer

variable {R : Type v} [Semiring R] [PartialOrder R]
variable {E : Type u} [AddCommMonoid E] [MulActionWithZero R E]

/-- Weak-layer constructor: in a cone, pointwise additive closure implies convexity. -/
theorem convex_of_add_mem {K : Set E} (hcone : Set.IsCone R K)
    (hadd : ∀ ⦃x y : E⦄, x ∈ K → y ∈ K → x + y ∈ K) :
    Convex R K := by
  refine convex_iff_add_mem.2 ?_
  intro x hx y hy a b ha hb hab
  by_cases ha0 : a = 0
  · have hb1 : b = 1 := by simpa [ha0] using hab
    simpa [ha0, hb1] using hy
  · by_cases hb0 : b = 0
    · have ha1 : a = 1 := by simpa [hb0] using hab
      simpa [hb0, ha1] using hx
    · have ha_pos : (0 : R) < a := lt_of_le_of_ne ha (Ne.symm ha0)
      have hb_pos : (0 : R) < b := lt_of_le_of_ne hb (Ne.symm hb0)
      exact hadd (hcone.smul_mem ha_pos hx) (hcone.smul_mem hb_pos hy)

/-- Weak-layer set form: in a cone, closure under pointwise set addition implies convexity. -/
theorem convex_of_add_subset {K : Set E} (hcone : Set.IsCone R K)
    (hadd : K + K ⊆ K) :
    Convex R K := by
  refine hcone.convex_of_add_mem ?_
  intro x y hx hy
  exact hadd (Set.add_mem_add hx hy)

end WeakLayer

section DivisionWeakLayer

variable {R : Type v} [DivisionSemiring R] [PartialOrder R]
variable [PosMulReflectLT R]
variable [ZeroLEOneClass R] [AddLeftMono R]
variable {E : Type u} [AddCommMonoid E] [DistribMulAction R E]

/-- Division-layer constructor: in a cone, convexity implies closure under pointwise addition. -/
theorem add_mem_of_convex {K : Set E} (hcone : Set.IsCone R K)
    (hconv : Convex R K) :
    ∀ ⦃x y : E⦄, x ∈ K → y ∈ K → x + y ∈ K := by
  intro x y hx hy
  have htwo_pos : (0 : R) < 2 := by
    exact (zero_lt_two : (0 : R) < 2)
  have htwo_ne : (2 : R) ≠ 0 := htwo_pos.ne'
  letI : NeZero (2 : R) := ⟨htwo_ne⟩
  have hhalf_nonneg : (0 : R) ≤ (1 / 2 : R) := by
    exact one_div_nonneg.2 (le_of_lt htwo_pos)
  have hxy : (1 / 2 : R) • x + (1 / 2 : R) • y ∈ K :=
    (convex_iff_add_mem.mp hconv) hx hy hhalf_nonneg hhalf_nonneg (add_halves 1)
  have hsum : (2 : R) • ((1 / 2 : R) • x + (1 / 2 : R) • y) ∈ K :=
    hcone.smul_mem htwo_pos hxy
  have htwo_inv : (2 : R) * (2 : R)⁻¹ = 1 := mul_inv_cancel₀ htwo_ne
  simpa [one_div, smul_add, smul_smul, htwo_inv] using hsum

/-- Division-layer set form: in a cone, convexity implies closure under pointwise set addition. -/
theorem add_subset_of_convex {K : Set E} (hcone : Set.IsCone R K)
    (hconv : Convex R K) :
    K + K ⊆ K := by
  intro z hz
  rcases hz with ⟨x, hx, y, hy, rfl⟩
  exact hcone.add_mem_of_convex hconv hx hy

end DivisionWeakLayer

section DivisionModuleLayer

variable {R : Type v} [DivisionSemiring R] [PartialOrder R]
variable [PosMulReflectLT R]
variable [ZeroLEOneClass R] [AddLeftMono R]
variable {E : Type u} [AddCommMonoid E] [Module R E]

/-- Theorem 2.6: a cone in a module over a partially ordered division semiring is convex if and
only if it is closed under addition. -/
theorem convex_iff_add_mem {K : Set E} (hcone : Set.IsCone R K) :
    Convex R K ↔ ∀ ⦃x y : E⦄, x ∈ K → y ∈ K → x + y ∈ K := by
  constructor
  · intro hconv
    exact hcone.add_mem_of_convex hconv
  · intro hadd
    exact hcone.convex_of_add_mem hadd

/-- Set-level bridge for Theorem 2.6: in a cone, convexity is equivalent to closure of `K` under
pointwise set addition. -/
theorem convex_iff_add_subset {K : Set E} (hcone : Set.IsCone R K) :
    Convex R K ↔ K + K ⊆ K := by
  constructor
  · intro hconv
    exact hcone.add_subset_of_convex hconv
  · intro hadd
    exact hcone.convex_of_add_subset hadd

end DivisionModuleLayer

end Set.IsCone

/-! ### Definition_2_6_10 (from Chap01) -/
/-
Source/core/bridge triage:
- `source-facing`: Definition 2.6.10 names the convex cone generated by a subset `S` as the cone
  obtained by adjoining the origin to the positive-combination cone from Corollary 2.6.2.
- `core/canonical`: mathlib's owner abstraction for convex cones containing `0` is
  `PointedCone`; the generated-cone owner is the existing mathlib declaration
  `PointedCone.hull R S`.
- `bridge/view`: coercing `PointedCone.hull R S` to a `ConvexCone` or to its underlying set
  forgets only the distinguished condition `0 ∈ cone S` while preserving the generated-cone
  semantics.
- Primitive data vs derived API: this item introduces only the canonical generated-cone
  construction, so the public API should present textbook `cone[R] S` directly as
  `PointedCone.hull R S`.
-/

/- Canonicalization decision record (this pass):
- Codomain/ambient check: this item is set/module-valued and does not require an extended codomain.
- Scalar/ambient check: the owner `PointedCone.hull` is already at the primitive ordered-semiring
  layer, so no scalar weakening is forced here.
- Owner check: keep the intrinsic owner `PointedCone.hull`; do not introduce a parallel wrapper
  owner.
- Topology check: this item is not topology-facing, so no intrinsic/relative topology rewrite
  applies.
- Notation check: retain textbook `cone[R] S` notation by declaring it in the `Rockafellar`
  scope at the canonical owner `PointedCone.hull`; open that scope here to preserve the existing
  chapter-facing notation surface.
-/

namespace Rockafellar

/-- Textbook notation for the convex cone generated by a set, on the canonical owner
`PointedCone.hull`. -/
scoped notation:max "cone[" r "] " s => PointedCone.hull r s

end Rockafellar

open scoped Rockafellar

/- Definition 2.6.10 is notation-level: the source-facing generated cone `cone[R] S` is the
canonical owner `PointedCone.hull R S`. -/
#check PointedCone.hull

/-! ### Corollary_2_6_11 (from Chap01) -/
open scoped BigOperators Pointwise Rockafellar

universe u v

variable {R : Type v} [Semifield R] [PartialOrder R] [IsOrderedRing R] [PosMulReflectLT R]
variable {E : Type u} [AddCommMonoid E] [Module R E]

namespace Rockafellar

/-- Textbook notation for the nonnegative ray through a set. -/
scoped notation:max "ray[" r "] " s => (Set.Ici (0 : r) • s)

end Rockafellar

local notation "R>0" => Set.Ioi (0 : R)

/-
Source/core/bridge triage:
- `source-facing`: Corollary 2.6.11 identifies the convex cone generated by `S ⊆ E` with the
  convex hull of the ray generated by `S`, where that ray is the set of all nonnegative scalar
  multiples of points of `S`.
- `core/canonical`: the owner abstractions are `PointedCone.hull R S` for the generated convex
  cone containing `0` (source notation: `cone[R] S`) and `convexHull R` for the convex hull.
- `bridge/view`: the source-facing ray is expressed by the notation `ray[R] S`, while the more
  decomposition-friendly bridge view is
  `insert (0 : E) (R>0 • S)`; the proof bridge is the canonical
  `Submodule.span_induction` for `PointedCone.hull` together with `convexHull_smul` to propagate
  nonnegative scaling through the convex hull.
- Primitive data vs derived API: `S` is the only primitive datum. The ray, the generated pointed
  cone, and the convex-hull membership witnesses are all derived from canonical owner API, so the
  public surface should stay limited to the source-facing nonnegative-ray corollary together with
  the minimal zero-plus-positive-ray bridge needed for empty-set applications.
- Domain-style sampling: this item follows the owner abstraction `PointedCone.hull R S`, the
  span induction principle `Submodule.span_induction`, and the convex-hull APIs
  `convexHull_min` and `convexHull_smul`.
- Layer target: keep Corollary 2.6.11 source-facing, and keep
  `insert (0 : E) (R>0 • S)` only as a bridge/view companion for the empty-set case.
-/

namespace PointedCone

/-- The generated pointed cone is the convex hull of the origin together with the nonnegative
ray through `S`. -/
-- Proof sketch: prove first that `convexHull R (insert 0 (ray[R] S))` is stable
-- under nonnegative scalar multiplication; this follows from `convexHull_smul` and nonnegative-ray
-- stability. Then use `Submodule.span_induction` on `PointedCone.hull` to get the forward
-- inclusion, while the reverse inclusion is `convexHull_min`.
theorem hull_eq_convexHull_zero_union_nonnegativeRay (S : Set E) :
    (cone[R] S : Set E) = convexHull R (insert (0 : E) (ray[R] S)) := by
  let T : Set E := insert (0 : E) (ray[R] S)
  have hzero_mem : (0 : E) ∈ convexHull R T := subset_convexHull R T (by simp [T])
  have hrT : ∀ {r : R}, 0 ≤ r → r • T ⊆ T := by
    intro r hr z hz
    rcases Set.mem_smul_set.mp hz with ⟨y, hy, rfl⟩
    rcases hy with rfl | hy
    · left
      simp
    · rcases Set.mem_smul.mp hy with ⟨a, ha, x, hx, rfl⟩
      right
      exact Set.mem_smul.mpr ⟨r * a, mul_nonneg hr ha, x, hx, by simp [smul_smul]⟩
  have hsmul_convexHull : ∀ {r : R}, 0 ≤ r → r • convexHull R T ⊆ convexHull R T := by
    intro r hr z hz
    have hz' : z ∈ convexHull R (r • T) := by
      simpa [convexHull_smul] using hz
    exact (convexHull_min ((hrT hr).trans (subset_convexHull R T)) (convex_convexHull R T)) hz'
  refine Set.Subset.antisymm ?_ ?_
  · intro x hx
    refine Submodule.span_induction (p := fun y _ ↦ y ∈ convexHull R T) ?_ ?_ ?_ ?_ hx
    · intro y hy
      exact subset_convexHull R T (by
        right
        exact Set.mem_smul.mpr ⟨1, by simp, y, hy, by simp⟩)
    · simpa using hzero_mem
    · intro y z _ _ hy hz
      have htwo_pos : (0 : R) < (2 : R) := two_pos
      have htwo_ne : (2 : R) ≠ 0 := ne_of_gt htwo_pos
      have htwo_mul_inv : (2 : R) * ((2 : R)⁻¹) = 1 := by
        simpa using (mul_inv_cancel₀ htwo_ne : (2 : R) * ((2 : R)⁻¹) = 1)
      have hhalf_nonneg : (0 : R) ≤ (1 / (2 : R) : R) := by
        exact (one_div_nonneg).2 (le_of_lt htwo_pos)
      have hhalf_sum : (1 / (2 : R) : R) + (1 / (2 : R) : R) = 1 := by
        calc
          (1 / (2 : R) : R) + (1 / (2 : R) : R) = (2 : R) * ((2 : R)⁻¹) := by
            simp [one_div, two_mul]
          _ = 1 := htwo_mul_inv
      have hmid :
          (1 / (2 : R) : R) • y + (1 / (2 : R) : R) • z ∈ convexHull R T :=
        (convex_convexHull R T) hy hz hhalf_nonneg hhalf_nonneg hhalf_sum
      have hscaled :
          (2 : R) • ((1 / (2 : R) : R) • y + (1 / (2 : R) : R) • z) ∈ convexHull R T :=
        (hsmul_convexHull (show 0 ≤ (2 : R) by exact le_of_lt htwo_pos))
          (Set.mem_smul_set.mpr ⟨_, hmid, rfl⟩)
      simpa [smul_add, smul_smul, one_div, htwo_mul_inv] using hscaled
    · intro a y _ hy
      exact (hsmul_convexHull (show 0 ≤ (a : R) by exact a.2))
        (Set.mem_smul_set.mpr ⟨y, hy, rfl⟩)
  · refine convexHull_min ?_ (hull R S).convex
    intro x hx
    rcases hx with rfl | hx
    · exact (hull R S).zero_mem
    · rcases Set.mem_smul.mp hx with ⟨r, hr, y, hy, rfl⟩
      exact (hull R S).smul_mem hr (subset_hull hy)

/-- Bridge form of Corollary 2.6.11: the generated pointed cone is the convex hull of the origin
together with the strictly positive ray through `S`. -/
theorem hull_eq_convexHull_zero_union_positiveRay (S : Set E) :
    (cone[R] S : Set E) = convexHull R (insert (0 : E) (R>0 • S)) := by
  rw [hull_eq_convexHull_zero_union_nonnegativeRay]
  congr 1
  ext x
  constructor
  · intro hx
    rcases hx with rfl | hx
    · left
      rfl
    · rcases Set.mem_smul.mp hx with ⟨r, hr, y, hy, rfl⟩
      by_cases hr0 : r = 0
      · left
        simp [hr0]
      · right
        exact Set.mem_smul.mpr
          ⟨r, lt_of_le_of_ne hr (Ne.symm hr0), y, hy, rfl⟩
  · intro hx
    rcases hx with rfl | hx
    · left
      rfl
    · rcases Set.mem_smul.mp hx with ⟨r, hr, y, hy, rfl⟩
      right
      exact Set.mem_smul.mpr ⟨r, hr.le, y, hy, rfl⟩

section

variable {R' : Type v} [PartialOrder R'] [Zero R']
variable {E' : Type u} [Zero E'] [SMulWithZero R' E']

/-- For a nonempty set, adjoining `0` to the strict positive ray equals the nonnegative ray. -/
theorem _root_.Set.insert_zero_smul_Ioi_eq_smul_Ici (S : Set E') (hS : S.Nonempty) :
    insert (0 : E') ((Set.Ioi (0 : R')) • S) = ray[R'] S := by
  refine Set.Subset.antisymm ?_ ?_
  · intro x hx
    rcases hx with rfl | hx
    · rcases hS with ⟨y, hy⟩
      exact Set.mem_smul.mpr ⟨0, by simp, y, hy, by simp⟩
    · rcases Set.mem_smul.mp hx with ⟨r, hr, y, hy, rfl⟩
      exact Set.mem_smul.mpr ⟨r, by simpa using hr.le, y, hy, rfl⟩
  · intro x hx
    rcases Set.mem_smul.mp hx with ⟨r, hr, y, hy, rfl⟩
    by_cases hzero : r = 0
    · left
      simp [hzero]
    · right
      exact Set.mem_smul.mpr
        ⟨r, by simpa using lt_of_le_of_ne hr (Ne.symm hzero), y, hy, rfl⟩

end

/-- Corollary 2.6.11: for a nonempty subset `S ⊆ E` of a module over an ordered semifield,
the convex cone generated by `S` is the convex hull of the ray of all nonnegative scalar multiples
of points of `S`. -/
-- Proof sketch: start from `hull_eq_convexHull_zero_union_nonnegativeRay` and remove the inserted
-- origin via `Set.insert_zero_smul_Ioi_eq_smul_Ici` on the positive-ray bridge form.
theorem hull_eq_convexHull_nonnegativeRay (S : Set E) (hS : S.Nonempty) :
    (cone[R] S : Set E) = convexHull R (ray[R] S) := by
  rw [hull_eq_convexHull_zero_union_positiveRay]
  simp [Set.insert_zero_smul_Ioi_eq_smul_Ici (S := S) hS]

end PointedCone

/-! ### Proposition_2_6_12 (from Chap01) -/
open scoped Pointwise

section

universe u

variable (R : Type*) {E : Type u} [Zero R] [LE R] [SMul R E]

/-
Source/core/bridge triage:
- `source-facing`: Proposition 2.6.12 says that a convex set `C` is the section at height `1` of
  a convex cone in one higher dimension, while the concrete lifted model is the subset
  `homogenizationSet C = {(λ, x) | 0 ≤ λ, x ∈ λ • C}`.
- `core/canonical`: the owner abstractions are the source-facing set `homogenizationSet C` and the
  generated pointed cone `PointedCone.hull R (Prod.mk 1 '' C)` from Definition 2.6.10.
- `bridge/view`: the canonical bridge identifies the generated pointed cone with
  `insert 0 (homogenizationSet C)`, so later chapter files can use the source-facing owner
  `homogenizationSet C` while still reusing the chapter-level cone owner from
  Definition 2.6.10.
- Primitive data vs derived API: the primitive concrete data are the lifted set
  `homogenizationSet C` and the lift image `Prod.mk 1 '' C`; the pointed-cone bridge and the
  unit-section equivalences are derived API from the canonical generated-cone owner.
  `PointedCone.ofConeComb`, `PointedCone.mem_hull_set`, and the source-facing convex-combination
  structure of `homogenizationSet`.
- Layer target: `bridge/view`.
-/

/-- The lifted set `K_C = {(λ, x) | 0 ≤ λ, x ∈ λ • C}` attached to a subset `C`. -/
def homogenizationSet (C : Set E) : Set (R × E) :=
  {p | 0 ≤ p.1 ∧ p.2 ∈ p.1 • C}

scoped[Rockafellar] notation "K[" R " | " C "]" => homogenizationSet R C

open scoped Rockafellar

/-- Membership in `homogenizationSet C` means having nonnegative first coordinate and second
coordinate in the corresponding scalar multiple of `C`. -/
theorem mem_homogenizationSet_iff (C : Set E) (p : R × E) :
    p ∈ K[R | C] ↔ 0 ≤ p.1 ∧ p.2 ∈ p.1 • C :=
  Iff.rfl

end

open scoped Rockafellar

section

universe u

variable (R : Type*) [One R] {E : Type u}

/-- The canonical height-`1` lift `{(1, x) | x ∈ C}` of a set `C`. -/
def unitLift (C : Set E) : Set (R × E) :=
  Prod.mk (1 : R) '' C

scoped[Rockafellar] notation "L[" R " | " C "]" => unitLift R C

@[simp] theorem mem_unitLift_iff (C : Set E) (x : E) :
    ((1 : R), x) ∈ L[R | C] ↔ x ∈ C := by
  constructor
  · rintro ⟨y, hy, hxy⟩
    cases hxy
    simpa using hy
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- The height-`1` section of a subset of `R × E`. -/
def unitSection (S : Set (R × E)) : Set E :=
  Prod.mk (1 : R) ⁻¹' S

scoped[Rockafellar] notation "U[" R " | " S "]" => unitSection R (S : Set _)

@[simp] theorem mem_unitSection_iff (S : Set (R × E)) (x : E) :
    x ∈ U[R | S] ↔ ((1 : R), x) ∈ S :=
  Iff.rfl

/-- The height-`1` section turns intersections in `R × E` into intersections in `E`. -/
@[simp] theorem unitSection_inter (S T : Set (R × E)) :
    U[R | S ∩ T] = U[R | S] ∩ U[R | T] := by
  ext x
  rfl

end

section

universe u

variable {R : Type*} {E : Type u}
  [Semiring R] [PartialOrder R] [IsOrderedRing R]
  [AddCommMonoid E] [Module R E]

namespace PointedCone

/-- Projecting the generated cone of the unit lift `{(1, x) | x ∈ C}` to the second coordinate
recovers exactly the generated cone of `C`. -/
theorem map_cone_unitLift_eq_cone (C : Set E) :
    (cone[R] (L[R | C])).map (LinearMap.snd R R E) = cone[R] C := by
  have hlift_comap :
      L[R | C] ⊆ (cone[R] C).comap (LinearMap.snd R R E) := by
    intro p hp
    rcases hp with ⟨x, hx, rfl⟩
    simpa [PointedCone.mem_comap] using
      (PointedCone.subset_hull (R := R) (s := C) hx : x ∈ cone[R] C)
  have hmap_le :
      (cone[R] (L[R | C])).map (LinearMap.snd R R E) ≤ cone[R] C := by
    intro y hy
    rcases hy with ⟨p, hp, rfl⟩
    exact (Submodule.span_le.2 hlift_comap hp : LinearMap.snd R R E p ∈ cone[R] C)
  have hsubset : C ⊆ (cone[R] (L[R | C])).map (LinearMap.snd R R E) := by
    intro x hx
    exact ⟨(1, x), PointedCone.subset_hull (R := R) (s := L[R | C]) ⟨x, hx, rfl⟩, rfl⟩
  have hcone_le_map :
      (cone[R] C : PointedCone R E) ≤ (cone[R] (L[R | C])).map (LinearMap.snd R R E) := by
    exact Submodule.span_le.mpr hsubset
  exact le_antisymm hmap_le hcone_le_map

/-- Set-level projection form of `map_cone_unitLift_eq_cone`. -/
@[simp] theorem snd_image_cone_unitLift_eq_cone (C : Set E) :
    LinearMap.snd R R E '' (cone[R] (L[R | C]) : Set (R × E)) = (cone[R] C : Set E) := by
  simpa [PointedCone.map] using
    congrArg (fun K : PointedCone R E => (K : Set E)) (map_cone_unitLift_eq_cone (R := R) C)

end PointedCone

end

open scoped Rockafellar

section

universe u

variable {R : Type*} {E : Type u} [Monoid R] [Zero R] [LE R] [ZeroLEOneClass R]
  [MulAction R E]

/-- At height `1`, the unit section of `homogenizationSet C` is exactly `C`. -/
@[simp] theorem mem_unitSection_homogenizationSet_iff (C : Set E) (x : E) :
    x ∈ U[R | K[R | C]] ↔ x ∈ C := by
  rw [mem_unitSection_iff, mem_homogenizationSet_iff R C]
  constructor
  · intro hx
    rcases Set.mem_smul_set.mp hx.2 with ⟨y, hy, hyx⟩
    have hxy : y = x := by
      exact (one_smul R y).symm.trans hyx
    simpa [hxy] using hy
  · intro hx
    refine ⟨zero_le_one, Set.mem_smul_set.mpr ⟨x, hx, ?_⟩⟩
    change (1 : R) • x = x
    exact one_smul R x

/-- At height `1`, the unit section of `homogenizationSet C` is exactly `C`. -/
@[simp] theorem unitSection_homogenizationSet_eq (C : Set E) :
    U[R | K[R | C]] = C := by
  ext x
  simpa using (mem_unitSection_homogenizationSet_iff (R := R) (C := C) (x := x))

/-- Raw ambient view of `mem_unitSection_homogenizationSet_iff` at height `1`. -/
@[simp] theorem mem_homogenizationSet_one_iff (C : Set E) (x : E) :
    ((1 : R), x) ∈ K[R | C] ↔ x ∈ C := by
  exact
    (mem_unitSection_iff (R := R) (S := K[R | C]) (x := x)).symm.trans
      (mem_unitSection_homogenizationSet_iff (R := R) (C := C) (x := x))

end

section

universe u

variable {R : Type*} {E : Type u} [Semifield R] [PartialOrder R] [IsOrderedRing R]
  [PosMulReflectLT R] [AddCommMonoid E] [Module R E]

omit [PosMulReflectLT R] in
private theorem smul_mem_homogenizationSet
    (C : Set E) {a : R} (ha : 0 < a) {p : R × E} (hp : p ∈ K[R | C]) :
    a • p ∈ K[R | C] := by
  rcases p with ⟨r, x⟩
  rcases (mem_homogenizationSet_iff R C (r, x)).1 hp with ⟨hr, hx⟩
  refine (mem_homogenizationSet_iff R C _).2 ?_
  constructor
  · exact mul_nonneg ha.le hr
  · have hx' : a • x ∈ a • (r • C) := Set.smul_mem_smul_set hx
    simpa [smul_smul, mul_assoc, mul_left_comm, mul_comm] using hx'

private theorem combo_mem_homogenizationSet
    (C : Set E) (hC : Convex R C) {p q : R × E} {a b : R}
    (hp : p ∈ K[R | C]) (hq : q ∈ K[R | C])
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a • p + b • q ∈ K[R | C] := by
  rcases p with ⟨r₁, x₁⟩
  rcases q with ⟨r₂, x₂⟩
  rcases (mem_homogenizationSet_iff R C (r₁, x₁)).1 hp with ⟨hr₁, hx₁⟩
  rcases (mem_homogenizationSet_iff R C (r₂, x₂)).1 hq with ⟨hr₂, hx₂⟩
  rcases Set.mem_smul_set.mp hx₁ with ⟨y₁, hy₁, hyx₁⟩
  rcases Set.mem_smul_set.mp hx₂ with ⟨y₂, hy₂, hyx₂⟩
  change (a * r₁ + b * r₂, a • x₁ + b • x₂) ∈ K[R | C]
  let r : R := a * r₁ + b * r₂
  have hr_nonneg : 0 ≤ r := add_nonneg (mul_nonneg ha hr₁) (mul_nonneg hb hr₂)
  refine (mem_homogenizationSet_iff R C _).2 ⟨hr_nonneg, ?_⟩
  change a • x₁ + b • x₂ ∈ r • C
  by_cases hr : r = 0
  · rw [hr]
    have hsum : a * r₁ + b * r₂ = 0 := by simpa [r] using hr
    have hzero_terms :=
      (add_eq_zero_iff_of_nonneg (mul_nonneg ha hr₁) (mul_nonneg hb hr₂)).1 hsum
    have har₁ : a * r₁ = 0 := hzero_terms.1
    have hbr₂ : b * r₂ = 0 := hzero_terms.2
    have hx₁' : (a * r₁) • y₁ = a • x₁ := by
      simpa [smul_smul, mul_assoc, mul_left_comm, mul_comm] using congrArg (fun z ↦ a • z) hyx₁
    have hx₂' : (b * r₂) • y₂ = b • x₂ := by
      simpa [smul_smul, mul_assoc, mul_left_comm, mul_comm] using congrArg (fun z ↦ b • z) hyx₂
    refine Set.mem_smul_set.mpr ⟨y₁, hy₁, ?_⟩
    calc
      (0 : R) • y₁ = 0 := by simp
      _ = (a * r₁) • y₁ + (b * r₂) • y₂ := by simp [har₁, hbr₂]
      _ = a • x₁ + b • x₂ := by rw [hx₁', hx₂']
  · have hr_pos : 0 < r := lt_of_le_of_ne hr_nonneg (by simpa [eq_comm] using hr)
    let α : R := a * r₁ / r
    let β : R := b * r₂ / r
    have hα_nonneg : 0 ≤ α := by
      dsimp [α]
      exact div_nonneg (mul_nonneg ha hr₁) hr_nonneg
    have hβ_nonneg : 0 ≤ β := by
      dsimp [β]
      exact div_nonneg (mul_nonneg hb hr₂) hr_nonneg
    have hαβ : α + β = 1 := by
      calc
        α + β = (a * r₁ + b * r₂) / r := by
          dsimp [α, β]
          rw [← add_div]
        _ = r / r := by rfl
        _ = 1 := by field_simp [hr]
    have hmem : α • y₁ + β • y₂ ∈ C := hC hy₁ hy₂ hα_nonneg hβ_nonneg hαβ
    have hx₁' : (a * r₁) • y₁ = a • x₁ := by
      simpa [smul_smul, mul_assoc, mul_left_comm, mul_comm] using congrArg (fun z ↦ a • z) hyx₁
    have hx₂' : (b * r₂) • y₂ = b • x₂ := by
      simpa [smul_smul, mul_assoc, mul_left_comm, mul_comm] using congrArg (fun z ↦ b • z) hyx₂
    refine Set.mem_smul_set.mpr ⟨α • y₁ + β • y₂, hmem, ?_⟩
    calc
      r • (α • y₁ + β • y₂) = (r * α) • y₁ + (r * β) • y₂ := by
        rw [smul_add, smul_smul, smul_smul]
      _ = (a * r₁) • y₁ + (b * r₂) • y₂ := by
        congr 1
        · dsimp [α]
          field_simp [hr]
        · dsimp [β]
          field_simp [hr]
      _ = a • x₁ + b • x₂ := by rw [hx₁', hx₂']

/-- The homogenization set of a convex set is convex. -/
theorem Convex.homogenizationSet {C : Set E} (hC : Convex R C) :
    Convex R (K[R | C]) := by
  exact convex_iff_add_mem.2 <| by
    intro p hp q hq a b ha hb _
    exact combo_mem_homogenizationSet C hC hp hq ha hb

/-- The intersection of the homogenization sets of two convex sets is convex. -/
theorem Convex.homogenizationSet_inter {C₁ C₂ : Set E}
    (hC₁ : Convex R C₁) (hC₂ : Convex R C₂) :
    Convex R (K[R | C₁] ∩ K[R | C₂]) :=
  hC₁.homogenizationSet.inter hC₂.homogenizationSet

/-- The pointwise sum of the homogenization sets of two convex sets is convex. -/
theorem Convex.homogenizationSet_add {C₁ C₂ : Set E}
    (hC₁ : Convex R C₁) (hC₂ : Convex R C₂) :
    Convex R (K[R | C₁] + K[R | C₂]) :=
  hC₁.homogenizationSet.add hC₂.homogenizationSet

/- For a convex set `C`, the pointed cone generated by `{(1, x) | x ∈ C}` is exactly the
source-facing homogenization set together with the origin. This is the exact owner-level bridge
between the chapter's source-facing set `homogenizationSet C` and the canonical pointed-cone hull;
the nonempty specialization below removes the inserted origin. -/
theorem pointedConeHull_lift_eq_insert_homogenizationSet
    (C : Set E) (hC : Convex R C) :
    (cone[R] (L[R | C]) : Set (R × E)) = insert 0 (K[R | C]) := by
  ext p
  constructor
  · intro hp
    let K : PointedCone R (R × E) :=
      PointedCone.ofConeComb (insert 0 (K[R | C])) ⟨0, by simp⟩ <| by
        intro x hx y hy a ha b hb
        rcases hx with rfl | hx
        · rcases hy with rfl | hy
          · simp
          · by_cases hb0 : b = 0
            · simp [hb0]
            · right
              simpa [zero_smul] using
                smul_mem_homogenizationSet C (lt_of_le_of_ne hb (by simpa [eq_comm] using hb0)) hy
        · rcases hy with rfl | hy
          · by_cases ha0 : a = 0
            · simp [ha0]
            · right
              simpa [zero_smul, add_comm] using
                smul_mem_homogenizationSet C (lt_of_le_of_ne ha (by simpa [eq_comm] using ha0)) hx
          · right
            exact combo_mem_homogenizationSet C hC hx hy ha hb
    have hHull_le : PointedCone.hull R (L[R | C]) ≤ K :=
      Submodule.span_le.mpr fun p hp ↦ by
        rcases hp with ⟨x, hx, rfl⟩
        right
        exact (mem_homogenizationSet_iff R C ((1 : R), x)).2 ⟨zero_le_one, by simpa⟩
    exact hHull_le hp
  · rintro (rfl | hp)
    · exact (cone[R] (L[R | C])).zero_mem
    · rcases (mem_homogenizationSet_iff R C p).1 hp with ⟨hp1, hp2⟩
      by_cases hzero : p = 0
      · simp [hzero]
      · have hp1ne : p.1 ≠ 0 := by
          intro hp10
          rcases Set.mem_smul_set.mp (hp10 ▸ hp2) with ⟨x, hx, hx0⟩
          apply hzero
          ext
          · simp [hp10]
          · simpa [eq_comm] using hx0
        rcases Set.mem_smul_set.mp hp2 with ⟨x, hx, hpx⟩
        have hx_hull : ((1 : R), x) ∈ cone[R] (L[R | C]) :=
          PointedCone.subset_hull ⟨x, hx, rfl⟩
        have hp_hull :
            p.1 • ((1 : R), x) ∈ cone[R] (L[R | C]) :=
          (cone[R] (L[R | C])).smul_mem hp1 hx_hull
        simpa [hpx] using hp_hull

/-- Pointwise form of `pointedConeHull_lift_eq_insert_homogenizationSet`. -/
@[simp] theorem mem_pointedConeHull_lift_iff (C : Set E) (hC : Convex R C) (p : R × E) :
    p ∈ (cone[R] (L[R | C]) : Set (R × E)) ↔ p = 0 ∨ p ∈ K[R | C] := by
  rw [pointedConeHull_lift_eq_insert_homogenizationSet (R := R) (C := C) hC]
  exact Set.mem_insert_iff

/-- If `C` is nonempty and convex, then the inserted origin in
`pointedConeHull_lift_eq_insert_homogenizationSet` is already contained in `homogenizationSet C`,
so the source-facing homogenization set is exactly the canonical pointed cone generated by its
lift `{(1, x) | x ∈ C}`. -/
theorem homogenizationSet_eq_pointedConeHull
    (C : Set E) (hC : Convex R C) (hC_nonempty : C.Nonempty) :
    K[R | C] = (cone[R] (L[R | C]) : Set (R × E)) := by
  have hzero : (0 : R × E) ∈ K[R | C] := by
    rcases hC_nonempty with ⟨x, hx⟩
    refine (mem_homogenizationSet_iff R C 0).2 ⟨le_rfl, ?_⟩
    exact Set.mem_smul_set.mpr ⟨x, hx, by simp⟩
  rw [pointedConeHull_lift_eq_insert_homogenizationSet C hC, Set.insert_eq_of_mem hzero]

/-- Canonical owner-oriented form of `homogenizationSet_eq_pointedConeHull`: for nonempty convex
`C`, the generated pointed cone of the unit lift equals `homogenizationSet C`. -/
@[simp] theorem pointedConeHull_lift_eq_homogenizationSet
    (C : Set E) (hC : Convex R C) (hC_nonempty : C.Nonempty) :
    (cone[R] (L[R | C]) : Set (R × E)) = K[R | C] := by
  simpa [eq_comm] using homogenizationSet_eq_pointedConeHull (R := R) C hC hC_nonempty

/-- Proposition 2.6.12, pointwise form: a point `x` lies in `C` exactly when `((1, x) : R × E)`
lies in the height-`1` section of the canonical pointed cone generated by the lift
`{(1, y) | y ∈ C}`. -/
-- Proof sketch: rewrite the canonical pointed cone by
-- `pointedConeHull_lift_eq_insert_homogenizationSet`. At height `1`, the origin is impossible, so
-- the section reduces to the height-`1` homogenization membership bridge
-- `mem_homogenizationSet_one_iff`.
theorem mem_unitSection_pointedConeHull_lift_iff (C : Set E) (hC : Convex R C) (x : E) :
    x ∈ U[R | cone[R] (L[R | C])] ↔ x ∈ C := by
  rw [mem_unitSection_iff, pointedConeHull_lift_eq_insert_homogenizationSet C hC]
  simp [mem_homogenizationSet_one_iff]

/-- Proposition 2.6.12: a convex set `C` is the height-`1` preimage of the canonical pointed cone
generated by its lift `{(1, x) | x ∈ C}` in `R × E`. -/
@[simp] theorem unitSection_pointedConeHull_lift_eq (C : Set E) (hC : Convex R C) :
    U[R | cone[R] (L[R | C])] = C := by
  ext x
  exact mem_unitSection_pointedConeHull_lift_iff C hC x

/-- Compatibility orientation of `unitSection_pointedConeHull_lift_eq`. -/
theorem convex_eq_unitSection_homogenizationCone (C : Set E) (hC : Convex R C) :
    C = U[R | cone[R] (L[R | C])] := by
  simpa [eq_comm] using (unitSection_pointedConeHull_lift_eq (R := R) C hC)

end
