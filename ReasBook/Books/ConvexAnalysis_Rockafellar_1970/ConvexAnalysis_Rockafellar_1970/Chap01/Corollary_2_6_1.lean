import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_2_5_10

-- Declarations for this item will be appended below by the statement pipeline.

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
