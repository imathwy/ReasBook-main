module

public import Topology_Munkres_2000.Book.Exercise_30_9.Antidiagonal
import all Topology_Munkres_2000.Book.Exercise_30_9.Antidiagonal
public import Mathlib.Data.Rat.Encodable
public import Mathlib.Topology.Baire.LocallyCompactRegular
public import Mathlib.Topology.Baire.Lemmas
public import Mathlib.Topology.DerivedSet
public import Mathlib.Topology.UnitInterval

public section

open Set

namespace SorgenfreyPlane

/-- The set of rational real parameters. -/
def rationalParameters : Set ℝ :=
  Set.range (fun q : ℚ ↦ (q : ℝ))

/-- The set of irrational real parameters. -/
def irrationalParameters : Set ℝ :=
  rationalParametersᶜ

/-- The rational part of the anti-diagonal in the Sorgenfrey plane. -/
def rationalAntiDiagonal : Set (SorgenfreyLine × SorgenfreyLine) :=
  antiDiagonalPoint '' rationalParameters

/-- The irrational part of the anti-diagonal in the Sorgenfrey plane. -/
def irrationalAntiDiagonal : Set (SorgenfreyLine × SorgenfreyLine) :=
  antiDiagonalPoint '' irrationalParameters

/-- The half-open basis square based at the anti-diagonal point with parameter `x`. -/
def basisSquare (x δ : ℝ) : Set (SorgenfreyLine × SorgenfreyLine) :=
  (SorgenfreyLine.toReal ⁻¹' Ico x (x + δ)) ×ˢ
    (SorgenfreyLine.toReal ⁻¹' Ico (-x) (-x + δ))

/-- The set `Kₙ` of irrational parameters whose reciprocal-scale basis square lies in `V`. -/
def coveringSet (V : Set (SorgenfreyLine × SorgenfreyLine)) (n : ℕ+) : Set ℝ :=
  {x | x ∈ Icc 0 1 ∧ x ∈ irrationalParameters ∧ basisSquare x (1 / (n : ℝ)) ⊆ V}

/-- The open parallelogram with anti-diagonal parameter in `(a, b)` and vertical offset in
`(0, 1 / n)`. -/
def parallelogram (a b : ℝ) (n : ℕ+) : Set (SorgenfreyLine × SorgenfreyLine) :=
  {p | ∃ x ∈ Ioo a b, ∃ ε ∈ Ioo (0 : ℝ) (1 / (n : ℝ)),
    p = (SorgenfreyLine.toReal.symm x, SorgenfreyLine.toReal.symm (-x + ε))}

/-- Membership in `coveringSet V n` records the interval, irrationality, and square-inclusion
conditions defining `Kₙ`. -/
theorem mem_coveringSet_iff (V : Set (SorgenfreyLine × SorgenfreyLine)) (n : ℕ+) (x : ℝ) :
    x ∈ coveringSet V n ↔
      x ∈ Icc 0 1 ∧ x ∈ irrationalParameters ∧ basisSquare x (1 / (n : ℝ)) ⊆ V := Iff.rfl

/-- Membership in `parallelogram a b n` is witnessed by its anti-diagonal coordinate and positive
vertical offset. -/
theorem mem_parallelogram_iff (a b : ℝ) (n : ℕ+) (p : SorgenfreyLine × SorgenfreyLine) :
    p ∈ parallelogram a b n ↔
      ∃ x ∈ Ioo a b, ∃ ε ∈ Ioo (0 : ℝ) (1 / (n : ℝ)),
        p = (SorgenfreyLine.toReal.symm x, SorgenfreyLine.toReal.symm (-x + ε)) := Iff.rfl

/-- Helper for Exercise 31.9: the standard anti-diagonal parameterization has its stated
coordinate pair. -/
private lemma antiDiagonalPoint_eq_coordinatePair (x : ℝ) :
    antiDiagonalPoint x =
      (SorgenfreyLine.toReal.symm x, SorgenfreyLine.toReal.symm (-x)) := by
  -- Route correction: the public import kept `antiDiagonalPoint` opaque, while the local
  -- implementation import exposes its defining coordinate pair at this bridge.
  rfl

/-- The rational real parameters form a countable set. -/
theorem rationalParameters_countable : rationalParameters.Countable := by
  -- Real rational parameters are the range of the canonical cast from `ℚ`.
  exact Set.countable_range fun q : ℚ ↦ (q : ℝ)

/-- The coordinate parallelogram used in Exercise 31.9 is open in the Sorgenfrey plane. -/
theorem isOpen_parallelogram (a b : ℝ) (n : ℕ+) : IsOpen (parallelogram a b n) := by
  -- Refine each represented point by a product of lower-limit basis intervals.
  let productBasis := SorgenfreyLine.isTopologicalBasis_lowerLimitBasis.prod
    SorgenfreyLine.isTopologicalBasis_lowerLimitBasis
  refine productBasis.isOpen_iff.mpr ?_
  rintro p ⟨x, hx, ε, hε, rfl⟩
  let c := min b (x + (1 / (n : ℝ) - ε) / 2)
  let d := -x + ε + (1 / (n : ℝ) - ε) / 2
  have hgap : 0 < (1 / (n : ℝ) - ε) / 2 := by
    linarith [hε.2]
  have hxc : x < c := by
    exact lt_min hx.2 (lt_add_of_pos_right x hgap)
  have hxd : -x + ε < d := by
    exact lt_add_of_pos_right (-x + ε) hgap
  refine ⟨Ico x c ×ˢ Ico (-x + ε) d, ?_, ?_, ?_⟩
  · exact ⟨Ico x c, ⟨x, c, hxc, rfl⟩, Ico (-x + ε) d,
      ⟨-x + ε, d, hxd, rfl⟩, rfl⟩
  · exact ⟨Set.left_mem_Ico.mpr hxc, Set.left_mem_Ico.mpr hxd⟩
  · -- The sum of the two coordinate increases stays below the permitted offset.
    rintro p ⟨hp₁, hp₂⟩
    refine ⟨SorgenfreyLine.toReal p.1, ?_,
      SorgenfreyLine.toReal p.1 + SorgenfreyLine.toReal p.2, ?_, ?_⟩
    · have hp₁Lower : x ≤ SorgenfreyLine.toReal p.1 := hp₁.1
      have hp₁Upper : SorgenfreyLine.toReal p.1 < c := hp₁.2
      exact ⟨hx.1.trans_le hp₁Lower, hp₁Upper.trans_le (min_le_left b _)⟩
    · constructor
      · have hp₁Lower : x ≤ SorgenfreyLine.toReal p.1 := hp₁.1
        have hp₂Lower : -x + ε ≤ SorgenfreyLine.toReal p.2 := hp₂.1
        linarith [hp₁Lower, hp₂Lower, hε.1]
      · have hp₁Upper : SorgenfreyLine.toReal p.1 <
            x + (1 / (n : ℝ) - ε) / 2 :=
          hp₁.2.trans_le (min_le_right b _)
        have hp₂Upper : SorgenfreyLine.toReal p.2 <
            -x + ε + (1 / (n : ℝ) - ε) / 2 := hp₂.2
        linarith [hp₁Upper, hp₂Upper]
    · apply Prod.ext
      · apply SorgenfreyLine.toReal.injective
        simp only [Equiv.apply_symm_apply]
      · apply SorgenfreyLine.toReal.injective
        simp only [Equiv.apply_symm_apply]
        ring

/-- Helper for Exercise 31.9 (1): The unit interval is covered by the reciprocal-scale sets
`Kₙ` together with the rational parameters in the unit interval. -/
theorem unitInterval_cover (V : Set (SorgenfreyLine × SorgenfreyLine)) (hV : IsOpen V)
    (hB : irrationalAntiDiagonal ⊆ V) :
    Icc (0 : ℝ) 1 =
      (⋃ n : ℕ+, coveringSet V n) ∪ (Icc (0 : ℝ) 1 ∩ rationalParameters) := by
  -- Refine an irrational anti-diagonal point to one product basis rectangle.
  let productBasis := SorgenfreyLine.isTopologicalBasis_lowerLimitBasis.prod
    SorgenfreyLine.isTopologicalBasis_lowerLimitBasis
  ext x
  constructor
  · intro hx
    by_cases hxRat : x ∈ rationalParameters
    · exact Or.inr ⟨hx, hxRat⟩
    · have hxIrr : x ∈ irrationalParameters := by
        exact hxRat
      have hxPoint : antiDiagonalPoint x ∈ V := by
        apply hB
        exact ⟨x, hxIrr, rfl⟩
      obtain ⟨w, hwBasis, hxw, hwV⟩ :=
        productBasis.exists_subset_of_mem_open hxPoint hV
      rcases hwBasis with ⟨s, hs, t, ht, rfl⟩
      rcases hs with ⟨a, c, hac, rfl⟩
      rcases ht with ⟨d, e, hde, rfl⟩
      have hxwReal : (x ∈ Ico a c) ∧ (-x ∈ Ico d e) := by
        rw [antiDiagonalPoint_eq_coordinatePair] at hxw
        change (a ≤ x ∧ x < c) ∧ d ≤ -x ∧ -x < e at hxw
        exact hxw
      have hxc : 0 < c - x := by
        exact sub_pos.mpr hxwReal.1.2
      have hxe : 0 < e + x := by
        have hupper : -x < e := hxwReal.2.2
        linarith
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt (lt_min hxc hxe)
      let n : ℕ+ := ⟨k + 1, Nat.succ_pos k⟩
      have hnSmall : 1 / (n : ℝ) < min (c - x) (e + x) := by
        simpa only [n, PNat.val, Nat.cast_add, Nat.cast_one] using hk
      have hSquare : basisSquare x (1 / (n : ℝ)) ⊆ Ico a c ×ˢ Ico d e := by
        rintro p ⟨hp₁, hp₂⟩
        constructor
        · change a ≤ SorgenfreyLine.toReal p.1 ∧ SorgenfreyLine.toReal p.1 < c
          have hp₁Upper : SorgenfreyLine.toReal p.1 < c := by
            linarith [hp₁.2, hnSmall.trans_le (min_le_left _ _)]
          exact ⟨hxwReal.1.1.trans hp₁.1, hp₁Upper⟩
        · change d ≤ SorgenfreyLine.toReal p.2 ∧ SorgenfreyLine.toReal p.2 < e
          have hp₂Upper : SorgenfreyLine.toReal p.2 < e := by
            linarith [hp₂.2, hnSmall.trans_le (min_le_right _ _)]
          exact ⟨hxwReal.2.1.trans hp₂.1, hp₂Upper⟩
      exact Or.inl (Set.mem_iUnion.mpr
        ⟨n, ⟨hx, hxIrr, hSquare.trans hwV⟩⟩)
  · -- Every reciprocal-scale set and every exceptional singleton stays in `[0, 1]`.
    rintro (hxK | hxRat)
    · obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hxK
      exact hn.1
    · exact hxRat.1

/-- Helper for Exercise 31.9: in a perfect Baire space, a countable cover modulo a
countable exceptional set has a member whose closure has nonempty interior. -/
private lemma existsInteriorClosureOfCountableException
    {X : Type*} [TopologicalSpace X] [BaireSpace X] [Nonempty X] [T1Space X]
    [PerfectSpace X]
    {ι : Type*} [Countable ι] (s : ι → Set X) (c : Set X) (hc : c.Countable)
    (hcover : Set.univ ⊆ (⋃ i, s i) ∪ c) :
    ∃ i, (interior (closure (s i))).Nonempty := by
  classical
  letI : Countable c := hc.to_subtype
  let f : Sum ι c → Set X := fun j ↦
    match j with
    | Sum.inl i => closure (s i)
    | Sum.inr x => {x.1}
  have hfClosed : ∀ j, IsClosed (f j) := by
    -- Family members are closures; exceptional points contribute closed singletons.
    intro j
    cases j with
    | inl i => exact isClosed_closure
    | inr x => exact isClosed_singleton
  have hfCover : ⋃ j, f j = (Set.univ : Set X) := by
    -- Enlarge the given cover by taking closures and indexing each exception separately.
    apply top_unique
    intro x _
    rcases hcover (Set.mem_univ x) with hx | hx
    · obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
      exact Set.mem_iUnion.mpr ⟨Sum.inl i, subset_closure hxi⟩
    · have hxSingleton : x ∈ f (Sum.inr ⟨x, hx⟩) := by
        simp [f]
      exact Set.mem_iUnion.mpr ⟨Sum.inr ⟨x, hx⟩, hxSingleton⟩
  obtain ⟨j, hj⟩ := nonempty_interior_of_iUnion_of_closed hfClosed hfCover
  cases j with
  | inl i =>
      exact ⟨i, hj⟩
  | inr x =>
      -- Perfectness rules out a singleton as the Baire member with interior.
      have hsingleton : (interior ({x.1} : Set X)).Nonempty := by
        simpa only [f] using hj
      rw [interior_singleton] at hsingleton
      obtain ⟨y, hy⟩ := hsingleton
      have hfalse : False := hy
      exact hfalse.elim

/-- Helper for Exercise 31.9 (2): The closure of some reciprocal-scale set `Kₙ` contains a
nonempty open real interval. -/
theorem coveringSet_closure_hasInterval (V : Set (SorgenfreyLine × SorgenfreyLine))
    (hV : IsOpen V) (hB : irrationalAntiDiagonal ⊆ V) :
    ∃ n : ℕ+, ∃ a b : ℝ, a < b ∧ Ioo a b ⊆ closure (coveringSet V n) := by
  -- Apply the countable-exception Baire lemma on the ordinary unit interval subtype.
  let interval := Icc (0 : ℝ) 1
  let family : ℕ+ → Set interval := fun n ↦ Subtype.val ⁻¹' coveringSet V n
  let exception : Set interval := Subtype.val ⁻¹' rationalParameters
  have hException : exception.Countable := by
    exact rationalParameters_countable.preimage Subtype.val_injective
  have hCover : Set.univ ⊆ (⋃ n, family n) ∪ exception := by
    intro x _
    have hx := Set.ext_iff.mp (unitInterval_cover V hV hB) x.1
    have hxCovered := hx.mp x.2
    rcases hxCovered with hxK | hxRat
    · obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hxK
      exact Or.inl (Set.mem_iUnion.mpr ⟨n, hn⟩)
    · exact Or.inr hxRat.2
  obtain ⟨n, hn⟩ :=
    existsInteriorClosureOfCountableException family exception hException hCover
  obtain ⟨z, hz⟩ := hn
  have hRelativeOpen : IsOpen (interior (closure (family n))) := isOpen_interior
  rw [isOpen_induced_iff] at hRelativeOpen
  obtain ⟨O, hO, hOpre⟩ := hRelativeOpen
  have hzO : z.1 ∈ O := by
    have hzPre : z ∈ Subtype.val ⁻¹' O := by
      rw [hOpre]
      exact hz
    exact hzPre
  have hzClosureInterior : z.1 ∈ closure (Ioo (0 : ℝ) 1) := by
    rw [closure_Ioo zero_ne_one]
    exact z.2
  have hOpenInterior : (O ∩ Ioo (0 : ℝ) 1).Nonempty := by
    obtain ⟨y, hyO, hyInterior⟩ :=
      mem_closure_iff.mp hzClosureInterior O hO hzO
    exact ⟨y, hyO, hyInterior⟩
  obtain ⟨a, b, hab, hIoo⟩ := (hO.inter isOpen_Ioo).exists_Ioo_subset hOpenInterior
  refine ⟨n, a, b, hab, ?_⟩
  -- Transport relative closure membership back through the continuous subtype inclusion.
  intro y hy
  have hyOI : y ∈ O ∩ Ioo (0 : ℝ) 1 := hIoo hy
  let yInterval : interval := ⟨y, ⟨hyOI.2.1.le, hyOI.2.2.le⟩⟩
  have hyRelativeInterior : yInterval ∈ interior (closure (family n)) := by
    rw [← hOpre]
    exact hyOI.1
  have hyRelativeClosure : yInterval ∈ closure (family n) :=
    interior_subset hyRelativeInterior
  exact continuous_subtype_val.closure_preimage_subset (coveringSet V n) hyRelativeClosure

/-- Helper for Exercise 31.9 (3): If `(a, b)` lies in the closure of `Kₙ`, then `V` contains
the associated open parallelogram. -/
theorem parallelogram_subset (V : Set (SorgenfreyLine × SorgenfreyLine)) (n : ℕ+) (a b : ℝ)
    (hK : Ioo a b ⊆ closure (coveringSet V n)) :
    parallelogram a b n ⊆ V := by
  -- Sample `Kₙ` immediately to the left of the represented anti-diagonal parameter.
  rintro p ⟨x, hx, ε, hε, rfl⟩
  let c := max a (x - ε)
  let t := (c + x) / 2
  have hcx : c < x := by
    exact max_lt hx.1 (sub_lt_self x hε.1)
  have htInterval : t ∈ Ioo a b := by
    constructor
    · have hct : c < t := by
        dsimp [t]
        linarith
      exact lt_of_le_of_lt (le_max_left a (x - ε)) hct
    · dsimp [t]
      linarith [hcx, hx.2]
  have htOpen : t ∈ Ioo c x := by
    dsimp [t]
    constructor
    · linarith
    · linarith
  obtain ⟨y, hyOpen, hyK⟩ :=
    mem_closure_iff.mp (hK htInterval) (Ioo c x) isOpen_Ioo htOpen
  have hyBounds : x - ε < y ∧ y < x := by
    exact ⟨(le_max_right a (x - ε)).trans_lt hyOpen.1, hyOpen.2⟩
  have hpSquare :
      (SorgenfreyLine.toReal.symm x, SorgenfreyLine.toReal.symm (-x + ε)) ∈
        basisSquare y (1 / (n : ℝ)) := by
    constructor
    · simp only [Set.mem_preimage, Set.mem_Ico, Equiv.apply_symm_apply]
      have hupper : x < y + 1 / (n : ℝ) := by
        linarith [hyBounds.1, hε.2]
      exact ⟨hyBounds.2.le, hupper⟩
    · simp only [Set.mem_preimage, Set.mem_Ico, Equiv.apply_symm_apply]
      constructor
      · linarith [hyBounds.1]
      · linarith [hyBounds.2, hε.2]
  exact hyK.2.2 hpSquare

/-- Helper for Exercise 31.9 (4): Every rational anti-diagonal point whose parameter lies in
`(a, b)` is a limit point of `V`. -/
theorem rationalAntiDiagonal_mem_derivedSet (V : Set (SorgenfreyLine × SorgenfreyLine))
    (n : ℕ+) (a b : ℝ) (q : ℚ) (hP : parallelogram a b n ⊆ V)
    (hq : (q : ℝ) ∈ Ioo a b) :
    antiDiagonalPoint (q : ℝ) ∈ derivedSet V := by
  -- Refine an arbitrary neighborhood to a product of lower-limit basis intervals.
  rw [mem_derivedSet, accPt_iff_nhds]
  let productBasis := SorgenfreyLine.isTopologicalBasis_lowerLimitBasis.prod
    SorgenfreyLine.isTopologicalBasis_lowerLimitBasis
  intro W hW
  obtain ⟨w, ⟨hwBasis, hpointW⟩, hwW⟩ := productBasis.nhds_hasBasis.mem_iff.mp hW
  rcases hwBasis with ⟨s, hs, t, ht, rfl⟩
  rcases hs with ⟨c, d, hcd, rfl⟩
  rcases ht with ⟨e, f, hef, rfl⟩
  have hpointWReal : ((q : ℝ) ∈ Ico c d) ∧ (-(q : ℝ) ∈ Ico e f) := by
    rw [antiDiagonalPoint_eq_coordinatePair] at hpointW
    change (c ≤ (q : ℝ) ∧ (q : ℝ) < d) ∧ e ≤ -(q : ℝ) ∧ -(q : ℝ) < f at hpointW
    exact hpointW
  have hvertical : 0 < f + (q : ℝ) := by
    have hupper : -(q : ℝ) < f := hpointWReal.2.2
    linarith
  have hreciprocal : 0 < 1 / (n : ℝ) := by
    positivity
  let ε := min (1 / (n : ℝ)) (f + (q : ℝ)) / 2
  have hε : ε ∈ Ioo (0 : ℝ) (1 / (n : ℝ)) := by
    dsimp [ε]
    constructor
    · positivity
    · linarith [min_le_left (1 / (n : ℝ)) (f + (q : ℝ))]
  let point : SorgenfreyLine × SorgenfreyLine :=
    (SorgenfreyLine.toReal.symm (q : ℝ),
      SorgenfreyLine.toReal.symm (-(q : ℝ) + ε))
  have hpointRect : point ∈ Ico c d ×ˢ Ico e f := by
    dsimp [point]
    change (c ≤ (q : ℝ) ∧ (q : ℝ) < d) ∧
      e ≤ -(q : ℝ) + ε ∧ -(q : ℝ) + ε < f
    constructor
    · exact hpointWReal.1
    · constructor
      · have hlower : e ≤ -(q : ℝ) := hpointWReal.2.1
        linarith [hε.1]
      · dsimp [ε]
        linarith [min_le_right (1 / (n : ℝ)) (f + (q : ℝ))]
  have hpointParallelogram : point ∈ parallelogram a b n := by
    exact ⟨(q : ℝ), hq, ε, hε, rfl⟩
  have hpointV : point ∈ V := hP hpointParallelogram
  have hpointNe : point ≠ antiDiagonalPoint (q : ℝ) := by
    intro heq
    rw [antiDiagonalPoint_eq_coordinatePair] at heq
    have hsecond := congrArg (fun z ↦ SorgenfreyLine.toReal z.2) heq
    simp only [point, Equiv.apply_symm_apply] at hsecond
    linarith [hε.1]
  exact ⟨point, ⟨hwW hpointRect, hpointV⟩, hpointNe⟩

/-- Exercise 31.9 (5): No open set containing the rational anti-diagonal is disjoint from an open
set containing the irrational anti-diagonal. -/
theorem no_disjoint_open_superset (V : Set (SorgenfreyLine × SorgenfreyLine)) (hV : IsOpen V)
    (hB : irrationalAntiDiagonal ⊆ V) (U : Set (SorgenfreyLine × SorgenfreyLine)) (hU : IsOpen U)
    (hA : rationalAntiDiagonal ⊆ U) :
    ¬ Disjoint U V := by
  -- The Baire interval contains a rational parameter whose anti-diagonal point is limiting for `V`.
  obtain ⟨n, a, b, hab, hK⟩ := coveringSet_closure_hasInterval V hV hB
  obtain ⟨q, haq, hqb⟩ := exists_rat_btwn hab
  have hP : parallelogram a b n ⊆ V := parallelogram_subset V n a b hK
  have hderived : antiDiagonalPoint (q : ℝ) ∈ derivedSet V :=
    rationalAntiDiagonal_mem_derivedSet V n a b q hP ⟨haq, hqb⟩
  have hpointA : antiDiagonalPoint (q : ℝ) ∈ rationalAntiDiagonal := by
    refine ⟨(q : ℝ), ?_, rfl⟩
    exact ⟨q, rfl⟩
  have hpointU : antiDiagonalPoint (q : ℝ) ∈ U := hA hpointA
  have hpointClosure : antiDiagonalPoint (q : ℝ) ∈ closure V :=
    derivedSet_subset_closure V hderived
  -- Openness of `U` makes it a neighborhood meeting `V`, contradicting disjointness.
  intro hdisjoint
  obtain ⟨p, hpU, hpV⟩ := mem_closure_iff.mp hpointClosure U hU hpointU
  exact Set.disjoint_left.mp hdisjoint hpU hpV

end SorgenfreyPlane
