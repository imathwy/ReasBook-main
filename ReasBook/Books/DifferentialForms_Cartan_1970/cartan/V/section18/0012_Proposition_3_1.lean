import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped NNReal Topology Pointwise SetRel Uniformity

universe u v

-- Domain sampling: this file lives in the compact-open/compact-convergence topology of
-- `ContinuousMap`. The owner declarations inspected before refinement were
-- `Filter.HasBasis.nhds_continuousMapConst`, `ContinuousMap.nhds_compactOpen`,
-- `ContinuousMap.instSecondCountableTopology`, and `ContinuousMap.instMetrizableSpace`.
-- The source-facing `V(K, ε)` notation is kept only as a specialization/bridge on top of that
-- owner API.

section CompactNeighborhood

variable {X : Type u} [TopologicalSpace X]
variable {E : Type v} [PseudoMetricSpace E] [Zero E]
variable {D : Set X}

/-- The neighborhood `V(K, ε)` of the zero function in the compact-convergence topology on
`C(D, E)`, written for a compact subset `K` of the domain subtype `D`. The textbook case is
`E = ℂ`. -/
def continuousMapCompactNeighborhood (K : Set D) (ε : ℝ) : Set C(D, E) :=
  { f | MapsTo f K (Metric.ball 0 ε) }

local notation "V(" K ", " ε ")" => continuousMapCompactNeighborhood K ε

/-- Membership in `V(K, ε)` is the expected pointwise ball condition on `K`. -/
theorem mem_continuousMapCompactNeighborhood_iff {K : Set D} {ε : ℝ} {f : C(D, E)} :
    f ∈ V(K, ε) ↔ ∀ z ∈ K, f z ∈ Metric.ball 0 ε :=
  Iff.rfl

/-- Proposition 3.1 (1): the canonical compact-convergence topology on `C(D, E)` has the sets
`V(K, ε)` as a neighborhood basis at `0`. The textbook case is `E = ℂ`. -/
theorem continuousMap_hasBasis_nhds_zero (D : Set X) :
    (𝓝 (0 : C(D, E))).HasBasis
      (fun p : Set D × ℝ ↦ IsCompact p.1 ∧ 0 < p.2)
      (fun p ↦ V(p.1, p.2)) := by
  simpa [continuousMapCompactNeighborhood] using
    Metric.nhds_basis_ball.nhds_continuousMapConst

end CompactNeighborhood

section TopologicalAddGroup

variable {X : Type u} [TopologicalSpace X]
variable {E : Type v} [PseudoMetricSpace E] [AddCommGroup E] [IsTopologicalAddGroup E]

local notation "V(" K ", " ε ")" => continuousMapCompactNeighborhood K ε

/-- Proposition 3.1 (2): among translation-invariant topologies on `C(D, E)`, the one whose
neighborhoods of `0` have basis `V(K, ε)` is unique. The textbook case is `E = ℂ`. -/
theorem continuousMap_topology_eq_of_isTopologicalAddGroup_and_hasBasis_nhds_zero
    (D : Set X) (t : TopologicalSpace C(D, E))
    (hadd : @IsTopologicalAddGroup (C(D, E)) t inferInstance)
    (hbasis : (@nhds (C(D, E)) t 0).HasBasis
      (fun p : Set D × ℝ ↦ IsCompact p.1 ∧ 0 < p.2)
      (fun p ↦ V(p.1, p.2))) :
    t = (inferInstance : TopologicalSpace C(D, E)) := by
  -- Compare the neighborhoods of `0` through the common compact-open basis, then use
  -- translation-invariance of additive topologies to recover the whole topology.
  have hzero :
      (@nhds (C(D, E)) t 0) = (@nhds (C(D, E)) ContinuousMap.compactOpen 0) := by
    exact Filter.HasBasis.eq_of_same_basis hbasis
      (continuousMap_hasBasis_nhds_zero (X := X) (E := E) D)
  have htop : t = ContinuousMap.compactOpen := by
    exact IsTopologicalAddGroup.ext hadd inferInstance hzero
  simpa using htop

end TopologicalAddGroup

section Metrization

variable {X : Type u} [TopologicalSpace X] [LocallyCompactSpace X] [SecondCountableTopology X]
variable {E : Type v} [TopologicalSpace E] [TopologicalSpace.MetrizableSpace E]
variable [AddCommGroup E] [IsTopologicalAddGroup E]

/-- Helper for Proposition 3.1: an open subtype of a locally compact second-countable space is
locally compact and sigma-compact, so the compact-convergence space `C(D, E)` is metrizable. -/
lemma continuousMap_metrizable_preconditions_of_isOpen
    (D : Set X) (hD : IsOpen D) : TopologicalSpace.MetrizableSpace C(D, E) := by
  -- Restrict the ambient local compactness to the open subtype and let the standard
  -- sigma-compactness instance finish the metrizable `ContinuousMap` instance search.
  letI : LocallyCompactSpace D := hD.locallyCompactSpace
  letI : SigmaCompactSpace D := sigmaCompactSpace_of_locallyCompact_secondCountable
  infer_instance

section AdditiveInvariantMetric

variable {G : Type*} [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
variable [FirstCountableTopology G] [T2Space G]

/-- Helper for Proposition 3.1: a first-countable Hausdorff topological additive group admits a
countable antitone basis at `0` that is symmetric and stable under triple addition. -/
lemma exists_symmetric_antitone_basis_nhds_zero :
    ∃ w : ℕ → Set G,
      (@nhds G inferInstance 0).HasAntitoneBasis w ∧
      (∀ n, ∀ x ∈ w n, -x ∈ w n) ∧
      ∀ n, w (n + 1) + w (n + 1) + w (n + 1) ⊆ w n := by
  -- Start from the standard controlled basis and symmetrize it on every fourth step so that
  -- two applications of the addition control yield the required triple-sum closure.
  obtain ⟨u, hu, hu_add⟩ := IsTopologicalAddGroup.exists_antitone_basis_nhds_zero (G := G)
  let v : ℕ → Set G := fun n ↦ u (2 * n) ∩ {x | -x ∈ u (2 * n)}
  let w : ℕ → Set G := fun n ↦ v (2 * n)
  have hv_antitone : Antitone v := by
    intro m n hmn
    refine inter_subset_inter ?_ ?_
    · exact hu.antitone (by omega)
    · exact fun _ hx ↦ hu.antitone (by omega) hx
  have hw_antitone : Antitone w := by
    intro m n hmn
    exact hv_antitone (by omega)
  have hv_mem : ∀ n, v n ∈ 𝓝 (0 : G) := by
    intro n
    refine Filter.inter_mem
      (hu.toHasBasis.mem_of_mem trivial) ?_
    have hU : u (2 * n) ∈ 𝓝 (- (0 : G)) := by
      simpa using (hu.toHasBasis.mem_of_mem trivial : u (2 * n) ∈ 𝓝 (0 : G))
    exact (continuous_neg : Continuous fun x : G ↦ -x).continuousAt.preimage_mem_nhds
      hU
  have hw_basis : (@nhds G inferInstance 0).HasAntitoneBasis w := by
    refine ⟨⟨?_⟩, hw_antitone⟩
    intro s
    constructor
    · intro hs
      rcases hu.toHasBasis.mem_iff.mp hs with ⟨n, -, hn⟩
      refine ⟨n, trivial, ?_⟩
      intro x hx
      exact hn (hu.antitone (by omega) (hx.1))
    · rintro ⟨n, -, hn⟩
      exact Filter.mem_of_superset (hv_mem (2 * n)) hn
  have hv_neg : ∀ n, ∀ x ∈ v n, -x ∈ v n := by
    intro n x hx
    rcases hx with ⟨hx₁, hx₂⟩
    exact ⟨hx₂, by simpa using hx₁⟩
  have hw_neg : ∀ n, ∀ x ∈ w n, -x ∈ w n := by
    intro n x hx
    exact hv_neg (2 * n) x hx
  have hv_add : ∀ n, v (n + 1) + v (n + 1) ⊆ v n := by
    intro n z hz
    rcases hz with ⟨x, hx, y, hy, rfl⟩
    refine ⟨?_, ?_⟩
    · have hx₁ : x ∈ u (2 * n + 1) := hu.antitone (by omega) hx.1
      have hy₁ : y ∈ u (2 * n + 1) := hu.antitone (by omega) hy.1
      exact hu_add (2 * n) ⟨x, hx₁, y, hy₁, rfl⟩
    · have hx' : -x ∈ u (2 * n + 1) := hu.antitone (by omega) hx.2
      have hy' : -y ∈ u (2 * n + 1) := hu.antitone (by omega) hy.2
      have hsum : (-x) + (-y) ∈ u (2 * n) := hu_add (2 * n) ⟨-x, hx', -y, hy', rfl⟩
      simpa [add_comm, neg_add_rev] using hsum
  have hw_add3 : ∀ n, w (n + 1) + w (n + 1) + w (n + 1) ⊆ w n := by
    intro n z hz
    rcases hz with ⟨ab, hab, c, hc, rfl⟩
    rcases hab with ⟨a, ha, b, hb, rfl⟩
    have hab : a + b ∈ v (2 * n + 1) := by
      exact hv_add (2 * n + 1) ⟨a, ha, b, hb, rfl⟩
    have hbc : c ∈ v (2 * n + 1) := hv_antitone (by omega) hc
    exact hv_add (2 * n) ⟨a + b, hab, c, hbc, by abel⟩
  exact ⟨w, hw_basis, hw_neg, hw_add3⟩

/-- Helper for Proposition 3.1: the entourage `{(x,y) | y - x ∈ w n}` is symmetric when `w n`
is closed under negation. -/
lemma translation_entourage_isSymm
    {w : ℕ → Set G} (hw_neg : ∀ n, ∀ x ∈ w n, -x ∈ w n) (n : ℕ) :
    SetRel.IsSymm ({p : G × G | p.2 - p.1 ∈ w n} : SetRel G G) := by
  constructor
  intro x y hxy
  -- Swapping `(x,y)` negates the difference, so symmetry follows from `-w n ⊆ w n`.
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hw_neg n _ hxy

/-- Helper for Proposition 3.1: the translated entourages inherit the triple-composition control
from the basis at `0`. -/
lemma translation_entourage_comp_subset
    {w : ℕ → Set G} (hw_antitone : Antitone w)
    (hw_add3 : ∀ n, w (n + 1) + w (n + 1) + w (n + 1) ⊆ w n) :
    ∀ ⦃m n : ℕ⦄, m < n →
      ({p : G × G | p.2 - p.1 ∈ w n} : SetRel G G) ○
          (({p : G × G | p.2 - p.1 ∈ w n} : SetRel G G) ○
            ({p : G × G | p.2 - p.1 ∈ w n} : SetRel G G))
        ⊆ ({p : G × G | p.2 - p.1 ∈ w m} : SetRel G G) := by
  intro m n hmn
  rintro ⟨x, z⟩ ⟨y, hxy, y', hyy', hy'z⟩
  have hstep : w n ⊆ w (m + 1) := hw_antitone (Nat.succ_le_of_lt hmn)
  have hxy' : y - x ∈ w (m + 1) := hstep hxy
  have hyy'' : y' - y ∈ w (m + 1) := hstep hyy'
  have hy'z' : z - y' ∈ w (m + 1) := hstep hy'z
  -- The three successive differences telescope to `z - x`.
  have hsum : ((y - x) + (y' - y)) + (z - y') ∈ w m := by
    exact hw_add3 m ⟨(y - x) + (y' - y), ⟨y - x, hxy', y' - y, hyy'', rfl⟩, z - y', hy'z', rfl⟩
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hsum

/-- Helper for Proposition 3.1: simultaneous left translation does not change membership in the
entourage defined by differences landing in `w n`. -/
lemma translation_entourage_vadd_mem_iff
    {w : ℕ → Set G} (a x y : G) (n : ℕ) :
    (a + x) ~[{p : G × G | p.2 - p.1 ∈ w n}] (a + y) ↔
      x ~[{p : G × G | p.2 - p.1 ∈ w n}] y := by
  -- Rewrite the entourage membership as a statement about the translated difference.
  change (a + y) - (a + x) ∈ w n ↔ y - x ∈ w n
  -- The common left-translation cancels from the difference.
  have hsub : (a + y) - (a + x) = y - x := by
    abel_nf
  constructor <;> intro h <;> simpa [hsub] using h

/-- Helper for Proposition 3.1: the owner pre-distance attached to an entourage basis `U`. -/
noncomputable def basisPreNNDist (U : ℕ → SetRel G G) : G → G → ℝ≥0 :=
  fun x y =>
    letI : DecidablePred fun n => (x, y) ∉ U n := fun n => Classical.propDecidable _
    letI := Classical.propDecidable (∃ n, (x, y) ∉ U n);
    if h : ∃ n, (x, y) ∉ U n then (1 / 2 : ℝ≥0) ^ Nat.find h else 0

/-- Helper for Proposition 3.1: the minimal separating index defining the owner pre-distance is
unchanged by simultaneous left translation when the entourage basis is translation-invariant. -/
lemma basis_preNNDist_vadd_invariant
    (U : ℕ → SetRel G G)
    (hU_vadd : ∀ a n x y, (a + x) ~[U n] (a + y) ↔ x ~[U n] y) :
    ∀ a x y, basisPreNNDist U (a + x) (a + y) = basisPreNNDist U x y := by
  classical
  intro a x y
  unfold basisPreNNDist
  let p : ℕ → Prop := fun n => (x, y) ∉ U n
  let q : ℕ → Prop := fun n => (a + x, a + y) ∉ U n
  letI : DecidablePred p := fun n => Classical.propDecidable _
  letI : DecidablePred q := fun n => Classical.propDecidable _
  have hpq : ∀ n, p n ↔ q n := by
    intro n
    -- Complement membership is preserved because the original entourage membership is.
    simp [p, q, hU_vadd a n x y]
  by_cases hp : ∃ n, p n
  · have hq : ∃ n, q n := by
      rcases hp with ⟨n, hn⟩
      exact ⟨n, (hpq n).mp hn⟩
    have hfind : Nat.find hq = Nat.find hp := by
      symm
      exact Nat.find_congr' (p := p) (q := q) (hp := hp) (hq := hq) (fun {n} => hpq n)
    -- Both translated and untranslated pairs use the same minimal separating index.
    simp [hp, hq, p, q]
    simpa [p, q] using hfind
  · have hq : ¬ ∃ n, q n := by
      intro hq
      apply hp
      rcases hq with ⟨n, hn⟩
      exact ⟨n, (hpq n).mpr hn⟩
    -- If no entourage separates one pair, none separates the translated pair either.
    simp [hp, hq, p, q]

/-- Helper for Proposition 3.1: the owner pre-distance is symmetric when the entourage basis is
symmetric. -/
lemma basisPreNNDist_comm
    (U : ℕ → SetRel G G)
    (hU_symm : ∀ n, SetRel.IsSymm (U n)) :
    ∀ x y, basisPreNNDist U x y = basisPreNNDist U y x := by
  classical
  intro x y
  unfold basisPreNNDist
  let p : ℕ → Prop := fun n => (x, y) ∉ U n
  let q : ℕ → Prop := fun n => (y, x) ∉ U n
  letI : DecidablePred p := fun n => Classical.propDecidable _
  letI : DecidablePred q := fun n => Classical.propDecidable _
  have hpq : ∀ n, p n ↔ q n := by
    intro n
    constructor
    · intro hxy hyx
      letI : (U n).IsSymm := hU_symm n
      exact hxy (SetRel.symm (R := U n) hyx)
    · intro hyx hxy
      letI : (U n).IsSymm := hU_symm n
      exact hyx (SetRel.symm (R := U n) hxy)
  by_cases hp : ∃ n, p n
  · have hq : ∃ n, q n := by
      rcases hp with ⟨n, hn⟩
      exact ⟨n, (hpq n).mp hn⟩
    have hfind₁ : Nat.find hp ≤ Nat.find hq := by
      exact Nat.find_mono (p := p) (q := q) (fun n hn => (hpq n).mpr hn) (hp := hp) (hq := hq)
    have hfind₂ : Nat.find hq ≤ Nat.find hp := by
      exact Nat.find_mono (p := q) (q := p) (fun n hn => (hpq n).mp hn) (hp := hq) (hq := hp)
    have hfind : Nat.find hp = Nat.find hq := le_antisymm hfind₁ hfind₂
    -- The minimal separating index is unchanged when the two endpoints are swapped.
    change (if hp' : ∃ n, p n then (1 / 2 : ℝ≥0) ^ Nat.find hp' else 0) =
        if hq' : ∃ n, q n then (1 / 2 : ℝ≥0) ^ Nat.find hq' else 0
    rw [dif_pos hp, dif_pos hq]
    simpa [hfind]
  · have hq : ¬ ∃ n, q n := by
      intro hq
      apply hp
      rcases hq with ⟨n, hn⟩
      exact ⟨n, (hpq n).mpr hn⟩
    -- If one orientation is never separated, the swapped one is never separated either.
    change (if hp' : ∃ n, p n then (1 / 2 : ℝ≥0) ^ Nat.find hp' else 0) =
        if hq' : ∃ n, q n then (1 / 2 : ℝ≥0) ^ Nat.find hq' else 0
    rw [dif_neg hp, dif_neg hq]

/-- Helper for Proposition 3.1: the owner pre-distance vanishes exactly on inseparable pairs for
an antitone entourage basis. -/
lemma basisPreNNDist_zero_iff_inseparable [UniformSpace G]
    {U : ℕ → SetRel G G} (hU_basis : (𝓤 G).HasAntitoneBasis U) {x y : G} :
    basisPreNNDist U x y = 0 ↔ @Inseparable G (inferInstance : UniformSpace G).toTopologicalSpace x y := by
  classical
  -- This is the owner `hd₀` step specialized to the chosen translated entourage basis.
  refine Iff.trans ?_
    ((hU_basis.toHasBasis.inseparable_iff_uniformity (x := x) (y := y)).symm)
  simp only [basisPreNNDist, true_imp_iff]
  split_ifs with h
  · simp [h, pow_eq_zero_iff']
  · simpa only [not_exists, Classical.not_not, eq_self_iff_true, true_iff] using h

/-- Helper for Proposition 3.1: powers of `1/2` detect exactly when a pair leaves the `n`-th
entourage of an antitone basis. -/
lemma basisPreNNDist_pow_le_iff [UniformSpace G]
    {U : ℕ → SetRel G G} (hU_basis : (𝓤 G).HasAntitoneBasis U) {x y : G} {n : ℕ} :
    ((1 / 2 : ℝ≥0) ^ n ≤ basisPreNNDist U x y) ↔ (x, y) ∉ U n := by
  classical
  let p : ℕ → Prop := fun m => (x, y) ∉ U m
  letI : DecidablePred p := fun m => Classical.propDecidable _
  have hr₀ : 0 < (1 / 2 : ℝ≥0) := half_pos one_pos
  have hr₁ : (1 / 2 : ℝ≥0) < 1 := NNReal.half_lt_self one_ne_zero
  -- Compare the threshold `((1 / 2)^n)` with the minimal separating index `Nat.find`.
  change ((1 / 2 : ℝ≥0) ^ n ≤
      (if h : ∃ m, p m then (1 / 2 : ℝ≥0) ^ Nat.find h else 0)) ↔ p n
  split_ifs with h
  · rw [(pow_right_strictAnti₀ hr₀ hr₁).le_iff_ge, Nat.find_le_iff]
    exact ⟨fun ⟨m, hmn, hm⟩ hn => hm (hU_basis.antitone hmn hn), fun h' => ⟨n, le_rfl, h'⟩⟩
  · push Not at h
    constructor
    · intro hn
      exact False.elim <| not_le_of_gt (pow_pos hr₀ _) hn
    · intro hp
      exact False.elim <| h n hp

/-- Helper for Proposition 3.1: the owner pre-distance is controlled by twice the path
distance obtained from `PseudoMetricSpace.ofPreNNDist`. -/
lemma basisPreNNDist_le_two_mul_dist [UniformSpace G]
    {U : ℕ → SetRel G G} (hU_basis : (𝓤 G).HasAntitoneBasis U)
    (hU_symm : ∀ n, SetRel.IsSymm (U n))
    (hU_comp : ∀ ⦃m n⦄, m < n → U n ○ (U n ○ U n) ⊆ U m) :
    letI I : PseudoMetricSpace G := PseudoMetricSpace.ofPreNNDist (basisPreNNDist U)
      (fun x => (basisPreNNDist_zero_iff_inseparable (G := G) (U := U) hU_basis).2 rfl)
      (basisPreNNDist_comm (G := G) U hU_symm)
    ∀ x y, ↑(basisPreNNDist U x y) ≤ 2 * dist x y := by
  classical
  letI I : PseudoMetricSpace G := PseudoMetricSpace.ofPreNNDist (basisPreNNDist U)
    (fun x => (basisPreNNDist_zero_iff_inseparable (G := G) (U := U) hU_basis).2 rfl)
    (basisPreNNDist_comm (G := G) U hU_symm)
  -- The source route now uses the owner four-point estimate to compare `basisPreNNDist` with
  -- the path pseudometric generated from the same pre-distance.
  intro x y
  refine PseudoMetricSpace.le_two_mul_dist_ofPreNNDist (basisPreNNDist U)
    (fun x => (basisPreNNDist_zero_iff_inseparable (G := G) (U := U) hU_basis).2 rfl)
    (basisPreNNDist_comm (G := G) U hU_symm) (fun x₁ x₂ x₃ x₄ => ?_) x y
  by_cases H : ∃ n, (x₁, x₄) ∉ U n
  · -- If the endpoints separate at level `Nat.find H`, one of the three intermediate edges must.
    let p : ℕ → Prop := fun n => (x₁, x₄) ∉ U n
    letI : DecidablePred p := fun n => Classical.propDecidable _
    have Hp : ∃ n, p n := H
    change ((if h : ∃ n, p n then (1 / 2 : ℝ≥0) ^ Nat.find h else 0) ≤
        2 * max (basisPreNNDist U x₁ x₂) (max (basisPreNNDist U x₂ x₃) (basisPreNNDist U x₃ x₄)))
    rw [dif_pos Hp]
    rw [← div_le_iff₀' zero_lt_two, ← mul_one_div (_ ^ _), ← pow_succ]
    simp only [le_max_iff, basisPreNNDist_pow_le_iff (G := G) (U := U) hU_basis, ← not_and_or]
    rintro ⟨h₁₂, h₂₃, h₃₄⟩
    refine Nat.find_spec Hp (hU_comp (lt_add_one <| Nat.find Hp) ?_)
    exact ⟨x₂, h₁₂, x₃, h₂₃, h₃₄⟩
  · -- If the endpoints are never separated, the left-hand side is already zero.
    simpa [basisPreNNDist, H] using (zero_le : (0 : ℝ≥0) ≤ 2 * max (basisPreNNDist U x₁ x₂)
      (max (basisPreNNDist U x₂ x₃) (basisPreNNDist U x₃ x₄)))

/-- Helper for Proposition 3.1: translating every intermediate vertex of an owner path preserves
its total `d`-cost. -/
  lemma path_sum_vadd_eq_of_vadd_invariant
    (d : G → G → ℝ≥0)
    (hd_vadd : ∀ a x y, d (a + x) (a + y) = d x y) :
    ∀ a x y l,
      (((a + x) :: l.map (fun z => a + z)).zipWith d (l.map (fun z => a + z) ++ [a + y])).sum =
        (((x :: l).zipWith d (l ++ [y])).sum) := by
  intro a x y l
  induction l generalizing x with
  | nil =>
      -- With no intermediate vertices, the path has a single translated edge.
      simp only [List.map_nil, List.nil_append, List.zipWith_cons_cons, List.zipWith_nil_right,
        List.sum_cons, List.sum_nil, hd_vadd]
  | cons z l ih =>
      -- Peel off the first edge and use the induction hypothesis on the remaining translated path.
      simp only [List.map_cons, List.cons_append, List.zipWith_cons_cons, List.sum_cons, hd_vadd]
      rw [ih z]

/-- Helper for Proposition 3.1: the path pseudometric built from `PseudoMetricSpace.ofPreNNDist`
inherits simultaneous left-translation invariance from the owner pre-distance. -/
lemma dist_ofPreNNDist_vadd_eq
    (d : G → G → ℝ≥0) (dist_self : ∀ x, d x x = 0)
    (dist_comm : ∀ x y, d x y = d y x)
    (hd_vadd : ∀ a x y, d (a + x) (a + y) = d x y) :
    letI I : PseudoMetricSpace G := PseudoMetricSpace.ofPreNNDist d dist_self dist_comm
    ∀ a x y : G, dist (a + x) (a + y) = dist x y := by
  letI I : PseudoMetricSpace G := PseudoMetricSpace.ofPreNNDist d dist_self dist_comm
  intro a x y
  -- Compare the owner `dist_ofPreNNDist` infima by translating every intermediate list vertex.
  rw [PseudoMetricSpace.dist_ofPreNNDist, PseudoMetricSpace.dist_ofPreNNDist]
  refine congrArg (fun r : ℝ≥0 => (r : ℝ)) ?_
  apply le_antisymm
  · refine le_ciInf fun l => ?_
    calc
      (⨅ l' : List G, (((a + x) :: l').zipWith d (l' ++ [a + y])).sum : ℝ≥0) ≤
          (((a + x) :: l.map (fun z => a + z)).zipWith d
            (l.map (fun z => a + z) ++ [a + y])).sum := by
        exact ciInf_le (OrderBot.bddBelow _) (l.map (fun z => a + z))
      _ = (((x :: l).zipWith d (l ++ [y])).sum : ℝ≥0) :=
        path_sum_vadd_eq_of_vadd_invariant (G := G) d hd_vadd a x y l
  · refine le_ciInf fun l => ?_
    calc
      (⨅ l' : List G, (((x :: l').zipWith d (l' ++ [y])).sum : ℝ≥0)) ≤
          (((x :: l.map (fun z => -a + z)).zipWith d
            (l.map (fun z => -a + z) ++ [y])).sum : ℝ≥0) := by
        exact ciInf_le (OrderBot.bddBelow _) (l.map (fun z => -a + z))
      _ = (((a + x) :: l).zipWith d (l ++ [a + y])).sum := by
        simpa [add_assoc] using
          (path_sum_vadd_eq_of_vadd_invariant (G := G) d hd_vadd (-a) (a + x) (a + y) l)

/-- Helper for Proposition 3.1: the `ofPreNNDist` path pseudometric makes every left translation
an isometry. -/
lemma isIsometricVAdd_ofPreNNDist
    (d : G → G → ℝ≥0) (dist_self : ∀ x, d x x = 0)
    (dist_comm : ∀ x y, d x y = d y x)
    (hd_vadd : ∀ a x y, d (a + x) (a + y) = d x y) :
    letI I : PseudoMetricSpace G := PseudoMetricSpace.ofPreNNDist d dist_self dist_comm
    @IsIsometricVAdd G G I.toPseudoEMetricSpace inferInstance := by
  letI I : PseudoMetricSpace G := PseudoMetricSpace.ofPreNNDist d dist_self dist_comm
  -- Package the translated distance equality into the additive isometry structure expected later.
  refine ⟨fun a => Isometry.of_dist_eq fun x y => ?_⟩
  simpa using dist_ofPreNNDist_vadd_eq (G := G) d dist_self dist_comm hd_vadd a x y

/-- Helper for Proposition 3.1: a translated entourage basis packages into a compatible
translation-invariant pseudometric. -/
lemma pseudoMetricSpace_of_translation_invariant_entourage_basis [UniformSpace G]
    {U : ℕ → SetRel G G} (hU_basis : (𝓤 G).HasAntitoneBasis U)
    (hU_symm : ∀ n, SetRel.IsSymm (U n))
    (hU_comp : ∀ ⦃m n⦄, m < n → U n ○ (U n ○ U n) ⊆ U m)
    (hd_vadd : ∀ a x y, basisPreNNDist U (a + x) (a + y) = basisPreNNDist U x y) :
    ∃ I : PseudoMetricSpace G,
      I.toUniformSpace = (inferInstance : UniformSpace G) ∧
      @IsIsometricVAdd G G I.toPseudoEMetricSpace inferInstance := by
  classical
  have hr : (1 / 2 : ℝ≥0) ∈ Ioo (0 : ℝ≥0) 1 := ⟨half_pos one_pos, NNReal.half_lt_self one_ne_zero⟩
  let d : G → G → ℝ≥0 := basisPreNNDist U
  letI I : PseudoMetricSpace G := PseudoMetricSpace.ofPreNNDist d
    (fun x => (basisPreNNDist_zero_iff_inseparable (G := G) (U := U) hU_basis).2 rfl)
    (basisPreNNDist_comm (G := G) U hU_symm)
  have hdist_le : ∀ x y, dist x y ≤ d x y := PseudoMetricSpace.dist_ofPreNNDist_le _ _ _
  have hd_le : ∀ x y, ↑(d x y) ≤ 2 * dist x y := by
    -- Reuse the owner four-point estimate proved above for the current local pseudometric.
    simpa [d] using
      (basisPreNNDist_le_two_mul_dist (G := G) (U := U) hU_basis hU_symm hU_comp)
  have hIso : @IsIsometricVAdd G G I.toPseudoEMetricSpace inferInstance := by
    -- Package the pre-distance translation invariance as isometric left translations.
    simpa [d] using
      (isIsometricVAdd_ofPreNNDist (G := G) d
        (fun x => (basisPreNNDist_zero_iff_inseparable (G := G) (U := U) hU_basis).2 rfl)
        (basisPreNNDist_comm (G := G) U hU_symm) hd_vadd)
  -- The owner basis comparison shows that the `dist`-uniformity is exactly the original one.
  rw [mem_Ioo, ← NNReal.coe_lt_coe, ← NNReal.coe_lt_coe] at hr
  refine ⟨I, UniformSpace.ext <| (Metric.uniformity_basis_dist_pow hr.1 hr.2).ext hU_basis.toHasBasis ?_ ?_,
    hIso⟩
  · intro n hn
    refine ⟨n, hn, fun x hx => (hdist_le _ _).trans_lt ?_⟩
    rwa [← NNReal.coe_pow, NNReal.coe_lt_coe, ← not_le,
      basisPreNNDist_pow_le_iff (G := G) (U := U) hU_basis, Classical.not_not]
  · intro n hn
    refine ⟨n + 1, trivial, fun x hx => ?_⟩
    rw [mem_setOf_eq] at hx
    contrapose! hx
    refine le_trans ?_ ((div_le_iff₀' zero_lt_two).2 (hd_le x.1 x.2))
    rwa [← NNReal.coe_two, ← NNReal.coe_div, ← NNReal.coe_pow, NNReal.coe_le_coe, pow_succ,
      mul_one_div, div_le_iff₀ zero_lt_two, div_mul_cancel₀ _ two_ne_zero,
      basisPreNNDist_pow_le_iff (G := G) (U := U) hU_basis]

/-- Helper for Proposition 3.1: a first-countable Hausdorff topological additive group admits a
compatible translation-invariant metric. -/
theorem exists_translation_invariant_metric_of_firstCountable_topologicalAddGroup :
    ∃ m : MetricSpace G,
      m.toUniformSpace.toTopologicalSpace = (inferInstance : TopologicalSpace G) ∧
      @IsIsometricVAdd G G m.toPseudoMetricSpace.toPseudoEMetricSpace inferInstance := by
  classical
  letI : UniformSpace G := IsTopologicalAddGroup.rightUniformSpace G
  haveI : IsUniformAddGroup G := isUniformAddGroup_of_addCommGroup
  obtain ⟨w, hw_basis, hw_neg, hw_add3⟩ :=
    exists_symmetric_antitone_basis_nhds_zero (G := G)
  let U : ℕ → SetRel G G := fun n ↦ {p | p.2 - p.1 ∈ w n}
  -- Route correction: the verified prefix is the entourage-level Birkhoff-Kakutani setup.
  have hU_basis : (𝓤 G).HasAntitoneBasis U := by
    rw [uniformity_eq_comap_nhds_zero G]
    simpa [U] using hw_basis.comap (fun p : G × G ↦ p.2 - p.1)
  have hU_symm : ∀ n, SetRel.IsSymm (U n) := by
    intro n
    simpa [U] using translation_entourage_isSymm (G := G) hw_neg n
  have hU_comp : ∀ ⦃m n⦄, m < n → U n ○ (U n ○ U n) ⊆ U m := by
    intro m n hmn
    simpa [U] using translation_entourage_comp_subset (G := G) hw_basis.antitone hw_add3 hmn
  have hU_vadd : ∀ a n x y, (a + x) ~[U n] (a + y) ↔ x ~[U n] y := by
    intro a n x y
    simpa [U] using translation_entourage_vadd_mem_iff (G := G) (w := w) a x y n
  let d : G → G → ℝ≥0 := basisPreNNDist U
  have hd_vadd : ∀ a x y, d (a + x) (a + y) = d x y := by
    intro a x y
    -- The source proof first checks translation invariance for the pre-distance `d`.
    simpa [d] using basis_preNNDist_vadd_invariant (G := G) U hU_vadd a x y
  let u : UniformSpace G := inferInstance
  have ht0 : ∀ x y, (∀ r ∈ u.uniformity, (x, y) ∈ r) → x = y := by
    simpa [u] using ((t0Space_iff_uniformity (α := G)).1 inferInstance)
  let t : TopologicalSpace G := inferInstance
  obtain ⟨I, hI_uniformity, hI_isometricVAdd⟩ :=
    pseudoMetricSpace_of_translation_invariant_entourage_basis
      (G := G) (U := U) hU_basis hU_symm hU_comp (by simpa [d] using hd_vadd)
  have hI_uniformity_filter : I.toUniformSpace.uniformity = u.uniformity := by
    exact congrArg (fun v : UniformSpace G => v.uniformity) hI_uniformity
  have hI_topology : I.toUniformSpace.toTopologicalSpace = t := by
    simpa [t, u] using congrArg (fun v : UniformSpace G => v.toTopologicalSpace) hI_uniformity
  letI : TopologicalSpace G := I.toUniformSpace.toTopologicalSpace
  letI : UniformSpace G := I.toUniformSpace
  letI : PseudoMetricSpace G := I
  letI : T0Space G := by
    refine (t0Space_iff_uniformity (α := G)).2 ?_
    intro x y hxy
    refine ht0 x y ?_
    intro r hr
    have hr' : r ∈ I.toUniformSpace.uniformity := by
      exact hI_uniformity_filter.symm ▸ hr
    exact hxy r hr'
  -- Route correction: after packaging the owner pseudometric, only the standard T₀ metric
  -- upgrade remains.
  refine ⟨MetricSpace.ofT0PseudoMetricSpace G, ?_, ?_⟩
  · simpa [t] using hI_topology
  · change @IsIsometricVAdd G G I.toPseudoEMetricSpace inferInstance
    simpa using hI_isometricVAdd

end AdditiveInvariantMetric

/-- Proposition 3.1 (3): for an open set `D ⊆ X`, the canonical topology on `C(D, E)` is induced
by some translation-invariant metric. The textbook case is `X = ℂ` and `E = ℂ`. -/
theorem continuousMap_exists_translationInvariant_metric_of_isOpen
    (D : Set X) (hD : IsOpen D) :
    ∃ m : MetricSpace C(D, E),
      m.toUniformSpace.toTopologicalSpace = (inferInstance : TopologicalSpace C(D, E)) ∧
      @IsIsometricVAdd (C(D, E)) (C(D, E))
        m.toPseudoMetricSpace.toPseudoEMetricSpace inferInstance := by
  -- Route correction: instead of forcing a concrete compact-exhaustion metric locally, first
  -- metrize `C(D, E)` via the standard owner instance and then upgrade it with the additive-group
  -- invariant-metric construction.
  letI : TopologicalSpace.MetrizableSpace C(D, E) :=
    continuousMap_metrizable_preconditions_of_isOpen D hD
  exact exists_translation_invariant_metric_of_firstCountable_topologicalAddGroup

end Metrization
