import Mathlib
import Mathlib.Order.KrullDimension
import Mathlib.Tactic.Recall
import Mathlib.Topology.Sets.Closeds

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_5_11_1 (from Chap05) -/
/- Definition 5.11.1: for an irreducible closed subset `Y` of `X`, the codimension `codim(Y, X)`
is the canonical order-theoretic notion `Order.coheight Y` in the poset `IrreducibleCloseds X`. -/
recall Order.coheight

/- Companion recall: for `Y : IrreducibleCloseds X`, the codimension of `Y` in `X` is also the
Krull dimension of the upper interval of irreducible closed subsets of `X` containing `Y`, via the
canonical theorem `Order.coheight_eq_krullDim_Ici`. -/
recall Order.coheight_eq_krullDim_Ici

/-! ### Lemma_5_11_2 (from Chap05) -/
universe u

open Set TopologicalSpace Order

variable {X : Type u} [TopologicalSpace X]

/-
Domain-style sampling for codimension under open restriction:
- primary domain: irreducible closed subsets under open-subspace inclusion, measured by
  `Order.coheight`
- inspected owner declarations:
  `TopologicalSpace.IrreducibleCloseds.map`,
  `TopologicalSpace.IrreducibleCloseds.map_strictMono_of_isInducing`,
  `Order.coheight_orderIso`,
  `subset_closure_inter_of_isPreirreducible_of_isOpen`
- best owner abstraction: `IrreducibleCloseds` together with the canonical ambient map
  `IrreducibleCloseds.map` along an inducing/open embedding, and codimension as `coheight`

Layer triage:
- `source-facing`: restriction of an irreducible closed subset to an open subspace, and the
  codimension invariance statement
- `core/canonical`: `IrreducibleCloseds`, `IrreducibleCloseds.map`, and `Order.coheight`
- `bridge/view`: `restrictOpen`, which is the inverse-side view of the canonical map on
  irreducible closed subsets for the open embedding `Subtype.val : U → X`

Primitive data is just the irreducible closed set and the open embedding. The order comparison on
upper intervals is derived API, so the codimension statement should be proved through the canonical
owner abstractions rather than through a parallel chain-length wrapper.
-/

namespace TopologicalSpace.IrreducibleCloseds

/-- The irreducible closed subset of an open subspace obtained by intersecting an ambient
irreducible closed subset that meets the open. -/
def restrictOpen (Y : IrreducibleCloseds X) (U : Opens X)
    (hYU : ((Y : Set X) ∩ U).Nonempty) : IrreducibleCloseds U :=
  ⟨Subtype.val ⁻¹' (Y : Set X),
    by
      have hYU' : ((Y : Set X) ∩ Set.range (Subtype.val : U → X)).Nonempty := by
        simpa using hYU
      simpa using Y.isIrreducible.preimage U.isOpenEmbedding' hYU',
    Y.isClosed.preimage continuous_subtype_val⟩

@[simp] theorem coe_restrictOpen (Y : IrreducibleCloseds X) (U : Opens X)
    (hYU : ((Y : Set X) ∩ U).Nonempty) :
    (Y.restrictOpen U hYU : Set U) = Subtype.val ⁻¹' (Y : Set X) :=
  rfl

end TopologicalSpace.IrreducibleCloseds

open TopologicalSpace.IrreducibleCloseds

private theorem inter_nonempty_of_le (Y T : IrreducibleCloseds X) (U : Opens X)
    (hYU : ((Y : Set X) ∩ U).Nonempty) (hYT : Y ≤ T) : ((T : Set X) ∩ U).Nonempty :=
  hYU.mono fun _ hx ↦ ⟨hYT hx.1, hx.2⟩

private theorem closure_inter_eq (Y : IrreducibleCloseds X) (U : Opens X)
    (hYU : ((Y : Set X) ∩ U).Nonempty) : closure ((Y : Set X) ∩ U) = (Y : Set X) := by
  apply Subset.antisymm
  · exact closure_minimal (inter_subset_left) Y.isClosed
  ·
    exact subset_closure_inter_of_isPreirreducible_of_isOpen
      Y.isIrreducible.isPreirreducible U.isOpen hYU

private noncomputable def restrictOpenIciOrderIso (Y : IrreducibleCloseds X) (U : Opens X)
    (hYU : ((Y : Set X) ∩ U).Nonempty) : Set.Ici (Y.restrictOpen U hYU) ≃o Set.Ici Y :=
  let e : Set.Ici (Y.restrictOpen U hYU) ≃ Set.Ici Y :=
    { toFun := fun Z ↦
        ⟨IrreducibleCloseds.map (Subtype.val : U → X) continuous_subtype_val Z.1, by
          change (Y : Set X) ⊆
            (IrreducibleCloseds.map (Subtype.val : U → X) continuous_subtype_val Z.1 : Set X)
          rw [IrreducibleCloseds.coe_map]
          calc
            (Y : Set X) = closure ((Y : Set X) ∩ U) := (closure_inter_eq Y U hYU).symm
            _ ⊆ closure ((Subtype.val : U → X) '' (Z.1 : Set U)) := by
              refine closure_mono ?_
              intro x hx
              have hx' : (⟨x, hx.2⟩ : U) ∈ (Y.restrictOpen U hYU : Set U) := by
                simpa [coe_restrictOpen] using hx.1
              exact ⟨⟨x, hx.2⟩, Z.2 hx', rfl⟩
        ⟩
      invFun := fun T ↦
        ⟨T.1.restrictOpen U (inter_nonempty_of_le Y T.1 U hYU T.2), by
          intro x hx
          exact T.2 (by simpa [coe_restrictOpen] using hx)
        ⟩
      left_inv := by
        intro Z
        have hEmbedding := U.isOpenEmbedding'.isEmbedding
        apply Subtype.ext
        apply IrreducibleCloseds.ext
        ext x
        change x ∈
            Subtype.val ⁻¹'
              closure ((Subtype.val : U → X) '' ((Z.1 : IrreducibleCloseds U) : Set U)) ↔
          x ∈ ((Z.1 : IrreducibleCloseds U) : Set U)
        rw [← hEmbedding.closure_eq_preimage_closure_image
          (((Z.1 : IrreducibleCloseds U) : Set U))]
        simp [Z.1.isClosed.closure_eq]
      right_inv := by
        intro T
        have hTU : ((T.1 : Set X) ∩ U).Nonempty := inter_nonempty_of_le Y T.1 U hYU T.2
        apply Subtype.ext
        apply IrreducibleCloseds.ext
        ext x
        simp [IrreducibleCloseds.coe_map, coe_restrictOpen, Set.image_preimage_eq_inter_range,
          closure_inter_eq T.1 U hTU] }
  e.toOrderIso
    (by
      intro A B hAB
      exact IrreducibleCloseds.map_mono continuous_subtype_val hAB)
    (by
      intro A B hAB
      change
        ((A.1.restrictOpen U (inter_nonempty_of_le Y A.1 U hYU A.2) : Set U) ⊆
          (B.1.restrictOpen U (inter_nonempty_of_le Y B.1 U hYU B.2) : Set U))
      intro x hx
      simpa [coe_restrictOpen] using hAB (by simpa [coe_restrictOpen] using hx))

-- Proof sketch: by Definition 5.11.1, codimension is `coheight`, equivalently the Krull dimension
-- of the upper interval by `Order.coheight_eq_krullDim_Ici`. The map
-- `T ↦ closure (Subtype.val '' T)` gives an order isomorphism between the intervals above
-- `Y.restrictOpen U hYU` in `IrreducibleCloseds U` and above `Y` in `IrreducibleCloseds X`.
/-- Lemma 5.11.2: if an irreducible closed subset `Y` meets an open subspace `U`, then its
codimension, expressed canonically as `coheight`, is unchanged after restricting to `U`. -/
theorem codim_irreducibleClosed_restrictOpen_eq (Y : IrreducibleCloseds X) (U : Opens X)
    (hYU : ((Y : Set X) ∩ U).Nonempty) :
    coheight Y = coheight (Y.restrictOpen U hYU) := by
  apply WithBot.coe_injective
  rw [Order.coheight_eq_krullDim_Ici, Order.coheight_eq_krullDim_Ici]
  simpa using Order.krullDim_eq_of_orderIso (restrictOpenIciOrderIso Y U hYU).symm

/-! ### Example_5_11_3 (from Chap05) -/
open Set Order TopologicalSpace Topology
open scoped unitInterval

/- Domain-style sampling for Example 5.11.3:
- primary domain: Noetherian topological spaces and codimension of irreducible closed subsets;
- inspected owner declarations: `IrreducibleCloseds`, `coheight`, `NoetherianSpace`, and the
  chapter recall `Definition_5_11_1`;
- best owner abstraction: the source-facing example space should be the named type
  `TailTopologyUnitInterval`; the canonical owners `IrreducibleCloseds` and `coheight` should then
  be used directly on that space, without parallel codimension wrappers;
- primitive-vs-derived split: the only primitive data here is the carrier `[0, 1]` together with
  its tail topology; the bundled irreducible closed subset `{0}` and its codimension are derived
  API from the canonical owners.

Layer triage:
- `source-facing`: the example space `TailTopologyUnitInterval` and the codimension statement for
  the irreducible closed subset `{0}`;
- `core/canonical`: `IrreducibleCloseds`, `coheight`, and `NoetherianSpace`;
- `bridge/view`: the named irreducible closed subset `tailTopologyUnitIntervalZero`. -/

/-- The point set `[0, 1]` equipped with the tail topology from Example 5.11.3. -/
structure TailTopologyUnitInterval where
  val : I

namespace TailTopologyUnitInterval

instance : Coe TailTopologyUnitInterval ℝ where
  coe x := x.val

@[ext]
theorem ext {x y : TailTopologyUnitInterval} (h : x.val = y.val) : x = y := by
  cases x
  cases y
  simpa using h

instance : Zero TailTopologyUnitInterval := ⟨⟨0⟩⟩

@[simp] theorem coe_eq_zero {x : TailTopologyUnitInterval} : (x : ℝ) = 0 ↔ x = 0 := by
  constructor
  · intro hx
    -- Equality in the ambient interval subtype reduces to equality of real coordinates.
    apply TailTopologyUnitInterval.ext
    change x.val = ⟨0, by constructor <;> norm_num⟩
    apply Subtype.ext
    simpa using hx
  · rintro rfl
    rfl

@[simp] theorem coe_zero : ((0 : TailTopologyUnitInterval) : ℝ) = 0 :=
  rfl

end TailTopologyUnitInterval

/-- The right endpoint of the `n`th closed initial segment `[0, 1 - 1 / (n + 1)]`. -/
private noncomputable def tailCut (n : ℕ) : ℝ :=
  1 - 1 / (n + 1 : ℝ)

/-- The basic open tail `(1 - 1 / (n + 1), 1]` in the topology from Example 5.11.3. -/
private noncomputable def tailTopologyUnitIntervalBasicOpen (n : ℕ) : Set TailTopologyUnitInterval :=
  { x | tailCut n < x }

private theorem tailCut_nonneg (n : ℕ) : 0 ≤ tailCut n := by
  -- Bound the reciprocal term by `1`, then rewrite the cutoff as a subtraction.
  dsimp [tailCut]
  have hle : (1 : ℝ) / (n + 1 : ℝ) ≤ 1 := by
    have hcast : (1 : ℝ) ≤ n + 1 := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    simpa using one_div_le_one_div_of_le zero_lt_one hcast
  exact sub_nonneg.mpr hle

private theorem tailCut_le_one (n : ℕ) : tailCut n ≤ 1 := by
  -- The cutoff is obtained by subtracting a nonnegative quantity from `1`.
  dsimp [tailCut]
  exact sub_le_self _ (by positivity)

private theorem tailCut_lt_one (n : ℕ) : tailCut n < 1 := by
  -- The reciprocal term is strictly positive, so the cutoff stays below `1`.
  dsimp [tailCut]
  exact sub_lt_self _ (by positivity)

private theorem tailCut_strictMono : StrictMono tailCut := by
  intro n m hnm
  -- Increasing the index decreases the reciprocal term, hence increases the cutoff.
  dsimp [tailCut]
  have hdiv : (1 : ℝ) / (m + 1 : ℝ) < 1 / (n + 1 : ℝ) := by
    exact one_div_lt_one_div_of_lt (by positivity)
      (by exact_mod_cast Nat.succ_lt_succ hnm)
  linarith

private theorem exists_tailCut_ge_of_ne_one (x : TailTopologyUnitInterval) (hx : (x : ℝ) ≠ 1) :
    ∃ n, (x : ℝ) ≤ tailCut n := by
  -- Since `x < 1`, some reciprocal `1 / (n + 1)` is smaller than the gap to `1`.
  have hxlt : (x : ℝ) < 1 := lt_of_le_of_ne x.val.2.2 hx
  have hgap : 0 < 1 - (x : ℝ) := sub_pos.mpr hxlt
  rcases exists_nat_one_div_lt hgap with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  dsimp [tailCut]
  linarith

private noncomputable def tailRankValue (x : TailTopologyUnitInterval) : ℕ∞ :=
  if hx : (x : ℝ) = 1 then ⊤ else Nat.find (exists_tailCut_ge_of_ne_one x hx)

private noncomputable def tailRank (x : TailTopologyUnitInterval) : WithUpper ℕ∞ :=
  WithUpper.toUpper (tailRankValue x)

/-- The topology on `[0, 1]` from Example 5.11.3, realized as the topology induced from the
canonical upper topology on the stage order `ℕ∞`. -/
@[reducible] noncomputable instance : TopologicalSpace TailTopologyUnitInterval :=
  TopologicalSpace.induced tailRank inferInstance

private theorem tailRank_inducing : IsInducing tailRank :=
  ⟨rfl⟩

private theorem tailRankValue_tailCut_lt_iff (x : TailTopologyUnitInterval) (n : ℕ) :
    tailCut n < (x : ℝ) ↔ (n : ℕ∞) < tailRankValue x := by
  by_cases hx : (x : ℝ) = 1
  · -- At the top point, every cutoff lies below `1`, so the rank is `⊤`.
    simp [tailRankValue, hx, tailCut_lt_one]
  · -- Away from `1`, the rank is the least cutoff index whose closed segment contains `x`.
    let m : ℕ := Nat.find (exists_tailCut_ge_of_ne_one x hx)
    have hm_spec : (x : ℝ) ≤ tailCut m := by
      dsimp [m]
      exact Nat.find_spec (exists_tailCut_ge_of_ne_one x hx)
    have hm_min : ∀ {k : ℕ}, (x : ℝ) ≤ tailCut k → m ≤ k := by
      intro k hk
      dsimp [m]
      exact Nat.find_min' (exists_tailCut_ge_of_ne_one x hx) hk
    have hcut : tailCut n < (x : ℝ) ↔ n < m := by
      constructor
      · intro hn
        by_contra hnm
        exact (not_lt_of_ge
          (hm_spec.trans (tailCut_strictMono.monotone (Nat.not_lt.mp hnm)))) hn
      · intro hnm
        by_contra hn
        exact Nat.not_lt_of_ge (hm_min (le_of_not_gt hn)) hnm
    simpa [tailRankValue, hx, m] using hcut

private theorem tailRankValue_eq_zero_iff (x : TailTopologyUnitInterval) :
    tailRankValue x = 0 ↔ (x : ℝ) = 0 := by
  constructor
  · intro hx
    -- Rank zero means the first cutoff does not lie strictly below `x`.
    have hnot : ¬ tailCut 0 < (x : ℝ) := by
      intro hlt
      have hgt : (0 : ℕ∞) < tailRankValue x := (tailRankValue_tailCut_lt_iff x 0).1 hlt
      simp [hx] at hgt
    have hxnonneg : 0 ≤ (x : ℝ) := x.val.2.1
    have hxnotgt : ¬ 0 < (x : ℝ) := by
      simpa [tailCut] using hnot
    linarith
  · intro hx
    -- At `0`, the absence of a positive cutoff forces the rank to be exactly `0`.
    have hle : tailRankValue x ≤ 0 := by
      refine le_of_not_gt ?_
      intro hgt
      have hlt : tailCut 0 < (x : ℝ) := (tailRankValue_tailCut_lt_iff x 0).2 hgt
      simp [hx, tailCut] at hlt
    simpa using hle

private theorem tailTopologyUnitIntervalBasicOpen_eq_preimage (n : ℕ) :
    tailTopologyUnitIntervalBasicOpen n =
      tailRank ⁻¹' (((Set.Iic (WithUpper.toUpper (n : ℕ∞))) : Set (WithUpper ℕ∞))ᶜ) := by
  ext x
  simp [tailTopologyUnitIntervalBasicOpen, tailRank, tailRankValue_tailCut_lt_iff]

private noncomputable def tailPoint (n : ℕ) : TailTopologyUnitInterval where
  val := ⟨tailCut n, tailCut_nonneg n, tailCut_le_one n⟩

@[simp] private theorem coe_tailPoint (n : ℕ) : ((tailPoint n : TailTopologyUnitInterval) : ℝ) = tailCut n :=
  rfl

@[simp] private theorem tailPoint_zero : tailPoint 0 = 0 := by
  -- The first sample point is the left endpoint of the interval.
  apply TailTopologyUnitInterval.ext
  apply Subtype.ext
  simp [tailPoint, tailCut]

private theorem tailRankValue_tailPoint (n : ℕ) : tailRankValue (tailPoint n) = n := by
  have hx : ((tailPoint n : TailTopologyUnitInterval) : ℝ) ≠ 1 := by
    -- Sample points lie strictly below `1`, so the non-top branch of `tailRankValue` applies.
    simpa [coe_tailPoint] using (tailCut_lt_one n).ne
  have hfind : Nat.find (exists_tailCut_ge_of_ne_one (tailPoint n) hx) = n := by
    -- The point `tailPoint n` lies on the `n`th cutoff, and strict monotonicity forces minimality.
    apply le_antisymm
    · exact Nat.find_min' (exists_tailCut_ge_of_ne_one (tailPoint n) hx)
        (by simp [coe_tailPoint])
    · have hspec : tailCut n ≤ tailCut (Nat.find (exists_tailCut_ge_of_ne_one (tailPoint n) hx)) := by
        simpa [coe_tailPoint] using Nat.find_spec (exists_tailCut_ge_of_ne_one (tailPoint n) hx)
      by_contra hle
      have hlt : Nat.find (exists_tailCut_ge_of_ne_one (tailPoint n) hx) < n :=
        Nat.lt_of_not_ge hle
      exact (not_le_of_gt (tailCut_strictMono hlt)) hspec
  rw [tailRankValue, dif_neg hx]
  simpa using hfind

private theorem tailTopologyUnitInterval_zero_isClosed :
    IsClosed ({(0 : TailTopologyUnitInterval)} : Set TailTopologyUnitInterval) := by
  -- The singleton `{0}` is the pullback of the closed initial segment `Iic 0` under the rank map.
  have hset :
      ({(0 : TailTopologyUnitInterval)} : Set TailTopologyUnitInterval) =
        tailRank ⁻¹' (Set.Iic (WithUpper.toUpper (0 : ℕ∞))) := by
    ext x
    rw [Set.mem_singleton_iff, Set.mem_preimage, Set.mem_Iic]
    simpa [tailRank, tailRankValue_eq_zero_iff] using
      (TailTopologyUnitInterval.coe_eq_zero (x := x)).symm
  rw [hset]
  exact isClosed_Iic.preimage tailRank_inducing.continuous

/-- The irreducible closed subset `{0}` of the tail-topology unit interval. -/
def tailTopologyUnitIntervalZero :
    IrreducibleCloseds TailTopologyUnitInterval :=
  ⟨{0}, isIrreducible_singleton, tailTopologyUnitInterval_zero_isClosed⟩

@[simp] theorem coe_tailTopologyUnitIntervalZero :
    (tailTopologyUnitIntervalZero : Set TailTopologyUnitInterval) = {0} :=
  rfl

private def tailPointClosure (n : ℕ) : IrreducibleCloseds TailTopologyUnitInterval :=
  ⟨closure ({tailPoint n} : Set TailTopologyUnitInterval), isIrreducible_singleton.closure,
    isClosed_closure⟩

private theorem coe_tailPointClosure (n : ℕ) :
    (tailPointClosure n : Set TailTopologyUnitInterval) =
      tailRank ⁻¹' (Set.Iic (WithUpper.toUpper (n : ℕ∞))) := by
  -- Compute closures in the upper-topology model and pull them back along the inducing map.
  change closure ({tailPoint n} : Set TailTopologyUnitInterval) =
      tailRank ⁻¹' (Set.Iic (WithUpper.toUpper (n : ℕ∞)))
  rw [Topology.IsInducing.closure_eq_preimage_closure_image tailRank_inducing, Set.image_singleton]
  rw [Topology.IsUpper.closure_singleton]
  simp [tailRank, tailRankValue_tailPoint]

private theorem tailPointClosure_zero :
    tailPointClosure 0 = tailTopologyUnitIntervalZero := by
  ext x
  simp [tailPointClosure, tailTopologyUnitIntervalZero, tailPoint_zero,
    tailTopologyUnitInterval_zero_isClosed.closure_eq]

/-- Helper for Example 5.11.3: the upper-topology space `WithUpper ℕ∞` is Noetherian because every
nonempty subset has a minimum, and any open containing that minimum contains the whole subset. -/
private theorem withUpper_enat_noetherian : NoetherianSpace (WithUpper ℕ∞) := by
  rw [TopologicalSpace.noetherianSpace_iff_isCompact]
  intro s
  rw [isCompact_iff_finite_subcover]
  intro ι U hUo hs
  have hwf : WellFounded ((· < ·) : WithUpper ℕ∞ → WithUpper ℕ∞ → Prop) := by
    simpa using (wellFounded_lt : WellFounded ((· < ·) : ℕ∞ → ℕ∞ → Prop))
  by_cases hsne : s.Nonempty
  · -- A minimum of `s` lies in some cover member, and upperness makes that member cover all of `s`.
    let m : WithUpper ℕ∞ := WellFounded.min hwf s hsne
    have hm_mem : m ∈ s := WellFounded.min_mem hwf s hsne
    rcases Set.mem_iUnion.1 (hs hm_mem) with ⟨i, him⟩
    refine ⟨({i} : Finset ι), ?_⟩
    intro x hx
    have hmx : m ≤ x := WellFounded.min_le hwf hx
    have hUpper : IsUpperSet (U i) := Topology.IsUpper.isUpperSet_of_isOpen (hUo i)
    have hxU : x ∈ U i := hUpper hmx him
    simp [hxU]
  · -- The empty set is compact with the empty finite subcover.
    refine ⟨(∅ : Finset ι), ?_⟩
    simp [Set.not_nonempty_iff_eq_empty.mp hsne]

/-- The tail-topology unit interval is a Noetherian topological space. -/
instance : NoetherianSpace TailTopologyUnitInterval := by
  have _ : NoetherianSpace (WithUpper ℕ∞) := withUpper_enat_noetherian
  -- Transfer Noetherianity along the inducing rank map.
  exact tailRank_inducing.noetherianSpace

private theorem tailPointClosure_strictMono : StrictMono tailPointClosure := by
  intro n m hnm
  -- The closure formula turns the sample closures into a strict chain of initial segments.
  show (tailPointClosure n : Set TailTopologyUnitInterval) ⊂
      (tailPointClosure m : Set TailTopologyUnitInterval)
  refine Set.ssubset_iff_subset_ne.2 ⟨?_, ?_⟩
  · intro x hx
    rw [coe_tailPointClosure] at hx ⊢
    have hx' : tailRank x ≤ WithUpper.toUpper (n : ℕ∞) := by
      simpa [Set.mem_preimage] using hx
    have hnm' : WithUpper.toUpper (n : ℕ∞) ≤ WithUpper.toUpper (m : ℕ∞) := by
      show (((n : ℕ∞) : WithUpper ℕ∞) ≤ (((m : ℕ∞) : WithUpper ℕ∞)))
      exact_mod_cast hnm.le
    change tailRank x ∈ Set.Iic (WithUpper.toUpper (m : ℕ∞))
    exact le_trans hx' hnm'
  · intro hEq
    have hm_mem : tailPoint m ∈ (tailPointClosure m : Set TailTopologyUnitInterval) := by
      rw [coe_tailPointClosure]
      simp [tailRank, tailRankValue_tailPoint]
    have hm_notmem : tailPoint m ∉ (tailPointClosure n : Set TailTopologyUnitInterval) := by
      rw [coe_tailPointClosure]
      simp [tailRank, tailRankValue_tailPoint, not_le_of_gt hnm]
    exact hm_notmem (hEq ▸ hm_mem)

/-- Example 5.11.3: in the topology on `[0, 1]` whose opens are `∅`, `[0, 1]`, and the tails
`(1 - 1 / n, 1]`, the irreducible closed subset `{0}` has infinite codimension. -/
theorem tailTopologyUnitInterval_zero_codimension_eq_top :
    coheight tailTopologyUnitIntervalZero = ⊤ := by
  -- The closures of the sample points form arbitrarily long strict chains above `{0}`.
  apply Order.coheight_eq_top_iff.mpr
  intro n
  refine ⟨(LTSeries.range n).map tailPointClosure tailPointClosure_strictMono, ?_, ?_⟩
  · simp [tailPointClosure_zero, LTSeries.head_map]
  · simp

/-! ### Definition_5_11_4 (from Chap05) -/
universe u

open TopologicalSpace Order

variable {X : Type u} [TopologicalSpace X]

/- Domain-style sampling for catenarity on topological spaces:
- earlier chapter owner: `Order.coheight` on `IrreducibleCloseds X`, recalled in
  `Definition_5_11_1`
- mathlib interval bridge: `Order.coheight_bot_eq_krullDim`
- ambient owner for absolute dimension: `topologicalKrullDim`

Layer triage:
- `source-facing`: the relative codimension `codimBetween` and the catenary predicate
  `CatenarySpace`
- `core/canonical`: `coheight` and `krullDim` on the posets `IrreducibleCloseds X` and
  `Set.Icc T T'`
- `bridge/view`: the interval specialization of `Order.coheight_bot_eq_krullDim`

Primitive data belongs to `CatenarySpace`; any derived API should stay atomic. The relative
codimension remains source-facing, but it should be a thin specialization of the chapter owner
`Order.coheight`, not a parallel replacement for it.
-/

/-- The relative codimension of comparable irreducible closed subsets, realized as the thin
interval specialization of `Order.coheight`. -/
noncomputable abbrev codimBetween (T T' : IrreducibleCloseds X) (hTT' : T ≤ T') : ℕ∞ :=
  let _ : Fact (T ≤ T') := ⟨hTT'⟩
  coheight (⊥ : Set.Icc T T')

/-- The source-facing relative codimension agrees with the Krull dimension of the interval
`[T, T']`. -/
theorem codimBetween_eq_krullDim {T T' : IrreducibleCloseds X} (hTT' : T ≤ T') :
    codimBetween T T' hTT' = krullDim (Set.Icc T T') := by
  let _ : Fact (T ≤ T') := ⟨hTT'⟩
  change coheight (⊥ : Set.Icc T T') = krullDim (Set.Icc T T')
  exact coheight_bot_eq_krullDim

/-- Definition 5.11.4: a topological space is catenary if every comparable pair of irreducible
closed subsets has finite relative codimension; maximal chains in the corresponding interval have
that common length. -/
class CatenarySpace (X : Type u) [TopologicalSpace X] : Prop where
  finite_codimBetween {T T' : IrreducibleCloseds X} (hTT' : T ≤ T') :
    codimBetween T T' hTT' < ⊤
  maximalIrreducibleClosedChainsHaveLength {T T' : IrreducibleCloseds X}
      (hTT' : T ≤ T') (s : Set (Set.Icc T T')) (hs : IsMaxChain (· ≤ ·) s) :
      s.encard = ENat.toNat (codimBetween T T' hTT') + 1

/-- A catenary-space hypothesis can be supplied through `Fact` when a proposition-valued instance
is the natural interface. -/
instance instFactCatenarySpace [CatenarySpace X] : Fact (CatenarySpace X) := ⟨inferInstance⟩

namespace CatenarySpace

/-- Helper for Definition 5.11.4: the lower interval below a point of `[T, T'']` is order-isomorphic
to the interval `[T, a]`. -/
def iic_orderIso_interval {T T'' : IrreducibleCloseds X} [Fact (T ≤ T'')]
    (a : Set.Icc T T'') : Set.Iic a ≃o Set.Icc T a.1 where
  toFun x := by
    refine ⟨(x : IrreducibleCloseds X), ?_, ?_⟩
    · exact x.1.2.1
    · exact x.2
  invFun y := by
    refine ⟨⟨(y : IrreducibleCloseds X), ?_, ?_⟩, ?_⟩
    · exact y.2.1
    · exact y.2.2.trans a.2.2
    · exact y.2.2
  left_inv x := by
    ext
    rfl
  right_inv y := by
    ext
    rfl
  map_rel_iff' := by
    intro x y
    rfl

/-- Helper for Definition 5.11.4: the upper interval above a point of `[T, T'']` is order-isomorphic
to the interval `[a, T'']`. -/
def ici_orderIso_interval {T T'' : IrreducibleCloseds X} [Fact (T ≤ T'')]
    (a : Set.Icc T T'') : Set.Ici a ≃o Set.Icc a.1 T'' where
  toFun x := by
    refine ⟨(x : IrreducibleCloseds X), ?_, ?_⟩
    · exact x.2
    · exact x.1.2.2
  invFun y := by
    refine ⟨⟨(y : IrreducibleCloseds X), ?_, ?_⟩, ?_⟩
    · exact a.2.1.trans y.2.1
    · exact y.2.2
    · exact y.2.1
  left_inv x := by
    ext
    rfl
  right_inv y := by
    ext
    rfl
  map_rel_iff' := by
    intro x y
    rfl

/-- Helper for Definition 5.11.4: the part of a maximal chain lying below a chosen element is again
a maximal chain in the lower interval. -/
lemma maxChain_iic_of_mem {α : Type*} [Preorder α] {s : Set α} {a : α}
    (hs : IsMaxChain (· ≤ ·) s) (ha : a ∈ s) :
    IsMaxChain (· ≤ ·) (Subtype.val ⁻¹' s : Set (Set.Iic a)) := by
  constructor
  · -- Restricting a chain to a subtype preserves comparability.
    simpa using hs.isChain.preimage (r := (· ≤ ·)) (s := (· ≤ ·))
      (f := Subtype.val) Subtype.val_injective (fun _ _ h ↦ h)
  · intro t ht hsubset
    -- Extend a larger lower chain by the unchanged upper slice of `s`.
    have h_union_chain : IsChain (· ≤ ·) (Subtype.val '' t ∪ {x | x ∈ s ∧ a ≤ x}) := by
      rw [isChain_union]
      refine ⟨?_, ?_, ?_⟩
      · simpa using ht.image_of_map_rel (r := (· ≤ ·)) (s := (· ≤ ·))
          (f := Subtype.val) (fun _ _ h ↦ h)
      · simpa using hs.isChain.mono (by
          intro x hx
          exact hx.1)
      · intro x hx y hy hxy
        left
        rcases hx with ⟨x', hx', rfl⟩
        exact x'.2.trans hy.2
    have hs_subset : s ⊆ (Subtype.val '' t ∪ {x | x ∈ s ∧ a ≤ x}) := by
      intro x hx
      by_cases hxa : x ≤ a
      · left
        refine ⟨⟨x, hxa⟩, ?_, rfl⟩
        exact hsubset hx
      · right
        refine ⟨hx, ?_⟩
        cases hs.isChain.total hx ha with
        | inl h => exact (hxa h).elim
        | inr h => exact h
    have hs_eq : s = (Subtype.val '' t ∪ {x | x ∈ s ∧ a ≤ x}) := hs.2 h_union_chain hs_subset
    -- Maximality of `s` forces the lower slice to be unchanged.
    apply Set.Subset.antisymm hsubset
    intro x hx
    have : ((x : α) ∈ (Subtype.val '' t ∪ {x | x ∈ s ∧ a ≤ x})) := Or.inl ⟨x, hx, rfl⟩
    exact hs_eq.symm ▸ this

/-- Helper for Definition 5.11.4: the part of a maximal chain lying above a chosen element is again
a maximal chain in the upper interval. -/
lemma maxChain_ici_of_mem {α : Type*} [Preorder α] {s : Set α} {a : α}
    (hs : IsMaxChain (· ≤ ·) s) (ha : a ∈ s) :
    IsMaxChain (· ≤ ·) (Subtype.val ⁻¹' s : Set (Set.Ici a)) := by
  constructor
  · -- Restricting a chain to a subtype preserves comparability.
    simpa using hs.isChain.preimage (r := (· ≤ ·)) (s := (· ≤ ·))
      (f := Subtype.val) Subtype.val_injective (fun _ _ h ↦ h)
  · intro t ht hsubset
    -- Extend a larger upper chain by the unchanged lower slice of `s`.
    have h_union_chain : IsChain (· ≤ ·) ({x | x ∈ s ∧ x ≤ a} ∪ Subtype.val '' t) := by
      rw [isChain_union]
      refine ⟨?_, ?_, ?_⟩
      · simpa using hs.isChain.mono (by
          intro x hx
          exact hx.1)
      · simpa using ht.image_of_map_rel (r := (· ≤ ·)) (s := (· ≤ ·))
          (f := Subtype.val) (fun _ _ h ↦ h)
      · intro x hx y hy hxy
        left
        rcases hy with ⟨y', hy', rfl⟩
        exact hx.2.trans y'.2
    have hs_subset : s ⊆ ({x | x ∈ s ∧ x ≤ a} ∪ Subtype.val '' t) := by
      intro x hx
      by_cases hax : a ≤ x
      · right
        refine ⟨⟨x, hax⟩, ?_, rfl⟩
        exact hsubset hx
      · left
        refine ⟨hx, ?_⟩
        cases hs.isChain.total hx ha with
        | inl h => exact h
        | inr h => exact (hax h).elim
    have hs_eq : s = ({x | x ∈ s ∧ x ≤ a} ∪ Subtype.val '' t) := hs.2 h_union_chain hs_subset
    -- Maximality of `s` forces the upper slice to be unchanged.
    apply Set.Subset.antisymm hsubset
    intro x hx
    have : ((x : α) ∈ ({x | x ∈ s ∧ x ≤ a} ∪ Subtype.val '' t)) := Or.inr ⟨x, hx, rfl⟩
    exact hs_eq.symm ▸ this

/-- Helper for Definition 5.11.4: splitting a chain at a chosen point counts the point once. -/
lemma encard_split_at_mem {α : Type*} [PartialOrder α] {s : Set α} {a : α}
    (hs : IsChain (· ≤ ·) s) (ha : a ∈ s) :
    ({x | x ∈ s ∧ x ≤ a}.encard) + ({x | x ∈ s ∧ a ≤ x}.encard) = s.encard + 1 := by
  -- The lower and upper slices cover the chain because every point is comparable with `a`.
  have h_union : {x | x ∈ s ∧ x ≤ a} ∪ {x | x ∈ s ∧ a ≤ x} = s := by
    ext x
    constructor
    · intro hx
      exact hx.elim (fun hx' ↦ hx'.1) (fun hx' ↦ hx'.1)
    · intro hx
      cases hs.total hx ha with
      | inl h => exact Or.inl ⟨hx, h⟩
      | inr h => exact Or.inr ⟨hx, h⟩
  -- Their intersection is the singleton `{a}` by antisymmetry.
  have h_inter : {x | x ∈ s ∧ x ≤ a} ∩ {x | x ∈ s ∧ a ≤ x} = ({a} : Set α) := by
    ext x
    constructor
    · intro hx
      have hxa : x ≤ a := hx.1.2
      have hax : a ≤ x := hx.2.2
      exact Set.mem_singleton_iff.mpr (le_antisymm hxa hax)
    · intro hx
      rcases Set.mem_singleton_iff.mp hx with rfl
      exact ⟨⟨ha, le_rfl⟩, ha, le_rfl⟩
  -- Now the standard inclusion-exclusion formula gives the count.
  calc
    {x | x ∈ s ∧ x ≤ a}.encard + {x | x ∈ s ∧ a ≤ x}.encard
        = ({x | x ∈ s ∧ x ≤ a} ∪ {x | x ∈ s ∧ a ≤ x}).encard
            + ({x | x ∈ s ∧ x ≤ a} ∩ {x | x ∈ s ∧ a ≤ x}).encard := by
            simpa [add_comm] using
              (Set.encard_union_add_encard_inter {x | x ∈ s ∧ x ≤ a} {x | x ∈ s ∧ a ≤ x}).symm
    _ = s.encard + ({a} : Set α).encard := by rw [h_union, h_inter]
    _ = s.encard + 1 := by simp

-- Proof sketch: compare maximal chains in `[T, T'']` with the concatenation of their restrictions
-- to `[T, T']` and `[T', T'']`. In a catenary space those maximal chains have lengths prescribed by
-- `codimBetween`, so the common length in the large interval is the sum of the common lengths in
-- the adjacent intervals.
/-- In a catenary space, relative codimension is additive along chains of irreducible closed
subsets. -/
theorem codimBetween_additive [CatenarySpace X] {T T' T'' : IrreducibleCloseds X}
    (hTT' : T ≤ T') (hT'T'' : T' ≤ T'') :
    codimBetween T T'' (hTT'.trans hT'T'') =
      codimBetween T T' hTT' + codimBetween T' T'' hT'T'' := by
  let hTT'' : T ≤ T'' := hTT'.trans hT'T''
  let _ : Fact (T ≤ T'') := ⟨hTT''⟩
  let a : Set.Icc T T'' := ⟨T', hTT', hT'T''⟩
  obtain ⟨s, ha⟩ := Flag.exists_mem a
  let lower : Set (Set.Iic a) := Subtype.val ⁻¹' (s : Set (Set.Icc T T''))
  let upper : Set (Set.Ici a) := Subtype.val ⁻¹' (s : Set (Set.Icc T T''))
  -- The chosen maximal chain splits into maximal lower and upper subchains.
  have hlower : IsMaxChain (· ≤ ·) lower := by
    simpa [lower] using maxChain_iic_of_mem s.maxChain ha
  have hupper : IsMaxChain (· ≤ ·) upper := by
    simpa [upper] using maxChain_ici_of_mem s.maxChain ha
  have hlower_image :
      Subtype.val '' lower = {x | x ∈ (s : Set (Set.Icc T T'')) ∧ x ≤ a} := by
    ext x
    constructor
    · rintro ⟨x', hx', rfl⟩
      exact ⟨hx', x'.2⟩
    · intro hx
      exact ⟨⟨x, hx.2⟩, hx.1, rfl⟩
  have hupper_image :
      Subtype.val '' upper = {x | x ∈ (s : Set (Set.Icc T T'')) ∧ a ≤ x} := by
    ext x
    constructor
    · rintro ⟨x', hx', rfl⟩
      exact ⟨hx', x'.2⟩
    · intro hx
      exact ⟨⟨x, hx.2⟩, hx.1, rfl⟩
  -- Transport the lower slice to `[T, T']` and read off its length from catenarity.
  have hlower_len :
      lower.encard = ENat.toNat (codimBetween T T' hTT') + 1 := by
    have htransport :
        IsMaxChain (· ≤ ·) (iic_orderIso_interval a '' lower) :=
      (IsMaxChain.image (iic_orderIso_interval a) hlower)
    have hlen :=
      CatenarySpace.maximalIrreducibleClosedChainsHaveLength
        (X := X) (T := T) (T' := T') hTT' (iic_orderIso_interval a '' lower) htransport
    rw [← (iic_orderIso_interval a).injective.encard_image lower]
    simpa [a] using hlen
  -- Transport the upper slice to `[T', T'']` and read off its length from catenarity.
  have hupper_len :
      upper.encard = ENat.toNat (codimBetween T' T'' hT'T'') + 1 := by
    have htransport :
        IsMaxChain (· ≤ ·) (ici_orderIso_interval a '' upper) :=
      (IsMaxChain.image (ici_orderIso_interval a) hupper)
    have hlen :=
      CatenarySpace.maximalIrreducibleClosedChainsHaveLength
        (X := X) (T := T') (T' := T'') hT'T'' (ici_orderIso_interval a '' upper) htransport
    rw [← (ici_orderIso_interval a).injective.encard_image upper]
    simpa [a] using hlen
  -- The full chain also has the catenary length for `[T, T'']`.
  have hs_len :
      (s : Set (Set.Icc T T'')).encard = ENat.toNat (codimBetween T T'' hTT'') + 1 :=
    CatenarySpace.maximalIrreducibleClosedChainsHaveLength
      (X := X) (T := T) (T' := T'') hTT'' (s : Set (Set.Icc T T'')) s.maxChain
  -- Counting the split chain yields an equality of natural chain lengths.
  have hsplit :
      (ENat.toNat (codimBetween T T' hTT') + 1 : ℕ∞) +
          (ENat.toNat (codimBetween T' T'' hT'T'') + 1) =
        (ENat.toNat (codimBetween T T'' hTT'') + 1) + 1 := by
    have hcard :=
      encard_split_at_mem (α := Set.Icc T T'') s.chain_le ha
    rw [← hlower_image, ← hupper_image] at hcard
    rw [(Subtype.val_injective.encard_image lower), (Subtype.val_injective.encard_image upper)] at hcard
    rw [hlower_len, hupper_len, hs_len] at hcard
    exact hcard
  have hnat :
      ENat.toNat (codimBetween T T'' hTT'') =
        ENat.toNat (codimBetween T T' hTT') + ENat.toNat (codimBetween T' T'' hT'T'') := by
    have hnat' :
        ENat.toNat (codimBetween T T' hTT') + 1 +
            (ENat.toNat (codimBetween T' T'' hT'T'') + 1) =
          (ENat.toNat (codimBetween T T'' hTT'') + 1) + 1 := by
      exact_mod_cast hsplit
    omega
  -- Finiteness upgrades the equality of natural lengths back to an equality in `ℕ∞`.
  have hfinite_big : codimBetween T T'' hTT'' ≠ ⊤ :=
    ne_of_lt <| CatenarySpace.finite_codimBetween (X := X) hTT''
  have hfinite_left : codimBetween T T' hTT' ≠ ⊤ :=
    ne_of_lt <| CatenarySpace.finite_codimBetween (X := X) hTT'
  have hfinite_right : codimBetween T' T'' hT'T'' ≠ ⊤ :=
    ne_of_lt <| CatenarySpace.finite_codimBetween (X := X) hT'T''
  calc
    codimBetween T T'' hTT'' = ENat.toNat (codimBetween T T'' hTT'') := by
      symm
      exact ENat.coe_toNat hfinite_big
    _ = ENat.toNat (codimBetween T T' hTT') + ENat.toNat (codimBetween T' T'' hT'T'') := by
      exact_mod_cast hnat
    _ = codimBetween T T' hTT' + codimBetween T' T'' hT'T'' := by
      rw [ENat.coe_toNat hfinite_left, ENat.coe_toNat hfinite_right]

end CatenarySpace

/-! ### Lemma_5_11_5 (from Chap05) -/
universe u v

open Set TopologicalSpace Order
open TopologicalSpace.IrreducibleCloseds

variable {X : Type u} [TopologicalSpace X]

/- Domain-style sampling for catenarity locality:
- chapter owner: `CatenarySpace X` from `Definition_5_11_4`
- same-domain chapter companion: `catenarySpace_iff`
- mathlib locality pattern for open subspaces: `IsLocallyClosed.locallyCompactSpace`
- mathlib owner-level open-cover locality patterns:
  `TopologicalSpace.IsOpenCover.jacobsonSpace_iff` and
  `TopologicalSpace.IsOpenCover.quasiSober_iff_forall`

Layer triage:
- `source-facing`: the existential open-cover statement `Lemma 5.11.5`
- `core/canonical`: the owner class `CatenarySpace`
- `bridge/view`: restriction to an open subspace and locality on a fixed open cover

Primitive data belongs to `CatenarySpace`; the restriction and open-cover statements are derived
API for that owner. The locally closed restriction theorem is a reusable bridge/view companion for
the source-facing “moreover” clause, while the public surface keeps the owner-level fixed-cover
theorem and the source-facing existential restatement.
-/

/-- Helper for Lemma 5.11.5: if an open set meets a smaller irreducible closed subset, then it
also meets every larger irreducible closed subset. -/
private theorem inter_nonempty_of_le (Y T : IrreducibleCloseds X) (U : Opens X)
    (hYU : ((Y : Set X) ∩ U).Nonempty) (hYT : Y ≤ T) :
    ((T : Set X) ∩ U).Nonempty :=
  hYU.mono fun _ hx ↦ ⟨hYT hx.1, hx.2⟩

/-- Helper for Lemma 5.11.5: mapping a restricted irreducible closed subset back to the ambient
space recovers the original subset. -/
@[simp] private theorem map_restrictOpen_eq (Y : IrreducibleCloseds X) (U : Opens X)
    (hYU : ((Y : Set X) ∩ U).Nonempty) :
    IrreducibleCloseds.map (Subtype.val : U → X) continuous_subtype_val
      (Y.restrictOpen U hYU) = Y := by
  -- The intersection with the open is dense in the irreducible closed set, so taking closure after
  -- mapping back to the ambient space returns the original set.
  apply IrreducibleCloseds.ext
  rw [IrreducibleCloseds.coe_map, IrreducibleCloseds.coe_restrictOpen]
  calc
    closure ((Subtype.val : U → X) '' (Subtype.val ⁻¹' (Y : Set X))) =
        closure (((Y : Set X) ∩ Set.range (Subtype.val : U → X))) := by
          congr 1
          ext x
          simp
    _ = closure ((Y : Set X) ∩ U) := by
          congr 1
          ext x
          simp
    _ = (Y : Set X) := by
          apply Subset.antisymm
          · exact closure_minimal inter_subset_left Y.isClosed
          · exact subset_closure_inter_of_isPreirreducible_of_isOpen
              Y.isIrreducible.isPreirreducible U.isOpen hYU

/-- Helper for Lemma 5.11.5: restricting the ambient image of an irreducible closed subset of an
open subspace gives back the original subset. -/
@[simp] private theorem restrictOpen_map_eq (U : Opens X) (Y : IrreducibleCloseds U)
    (hYU : (((IrreducibleCloseds.map (Subtype.val : U → X) continuous_subtype_val Y :
      IrreducibleCloseds X) : Set X) ∩ U).Nonempty) :
    (IrreducibleCloseds.map (Subtype.val : U → X) continuous_subtype_val Y).restrictOpen U hYU = Y := by
  -- Route correction: instead of unfolding the subtype twice, use the embedding formula
  -- `closure_eq_preimage_closure_image` for the open embedding `Subtype.val : U → X`.
  have hEmbedding := U.isOpenEmbedding'.isEmbedding
  apply IrreducibleCloseds.ext
  ext x
  change x ∈
      Subtype.val ⁻¹'
        closure ((Subtype.val : U → X) '' ((Y : IrreducibleCloseds U) : Set U)) ↔
    x ∈ ((Y : IrreducibleCloseds U) : Set U)
  rw [← hEmbedding.closure_eq_preimage_closure_image (((Y : IrreducibleCloseds U) : Set U))]
  simp [Y.isClosed.closure_eq]

/-- Helper for Lemma 5.11.5: an interval of irreducible closed subsets in an open subspace is
order-isomorphic to the corresponding interval of their ambient closures. -/
private noncomputable def open_subspace_interval_orderIso (U : Opens X)
    {S S' : IrreducibleCloseds U} (_hSS' : S ≤ S') :
    Set.Icc S S' ≃o
      Set.Icc
        (IrreducibleCloseds.map (Subtype.val : U → X) continuous_subtype_val S)
        (IrreducibleCloseds.map (Subtype.val : U → X) continuous_subtype_val S') := by
  classical
  let x : U := Classical.choose S.isIrreducible.nonempty
  have hx : x ∈ (S : Set U) := Classical.choose_spec S.isIrreducible.nonempty
  let hSU :
      (((IrreducibleCloseds.map (Subtype.val : U → X) continuous_subtype_val S :
        IrreducibleCloseds X) : Set X) ∩ U).Nonempty := by
    refine ⟨x, ?_, x.2⟩
    rw [IrreducibleCloseds.coe_map]
    exact subset_closure ⟨x, hx, rfl⟩
  let e :
      Set.Icc S S' ≃
        Set.Icc
          (IrreducibleCloseds.map (Subtype.val : U → X) continuous_subtype_val S)
          (IrreducibleCloseds.map (Subtype.val : U → X) continuous_subtype_val S') :=
    { toFun := fun Z : Set.Icc S S' ↦
      show
        Set.Icc
          (IrreducibleCloseds.map (Subtype.val : U → X) continuous_subtype_val S)
          (IrreducibleCloseds.map (Subtype.val : U → X) continuous_subtype_val S') from
      ⟨IrreducibleCloseds.map (Subtype.val : U → X) continuous_subtype_val Z.1,
        IrreducibleCloseds.map_mono continuous_subtype_val Z.2.1,
        IrreducibleCloseds.map_mono continuous_subtype_val Z.2.2⟩
      invFun := fun T :
          Set.Icc
            (IrreducibleCloseds.map (Subtype.val : U → X) continuous_subtype_val S)
            (IrreducibleCloseds.map (Subtype.val : U → X) continuous_subtype_val S') ↦
      show Set.Icc S S' from
      ⟨T.1.restrictOpen U (inter_nonempty_of_le
          (IrreducibleCloseds.map (Subtype.val : U → X) continuous_subtype_val S) T.1 U hSU T.2.1),
        by
          intro x hx
          change (x : X) ∈ (T.1 : Set X)
          exact T.2.1 (by
            show (x : X) ∈
              (IrreducibleCloseds.map (Subtype.val : U → X) continuous_subtype_val S : Set X)
            rw [IrreducibleCloseds.coe_map]
            exact subset_closure ⟨x, hx, rfl⟩),
        by
          intro x hx
          have hx' : (x : X) ∈ (T.1 : Set X) := by
            simpa [IrreducibleCloseds.coe_restrictOpen] using hx
          have hx'' :
              x ∈
                Subtype.val ⁻¹'
                  closure ((Subtype.val : U → X) '' ((S' : IrreducibleCloseds U) : Set U)) := by
            simpa [IrreducibleCloseds.coe_map] using T.2.2 hx'
          rw [← U.isOpenEmbedding'.isEmbedding.closure_eq_preimage_closure_image
            (((S' : IrreducibleCloseds U) : Set U))] at hx''
          simpa [S'.isClosed.closure_eq] using hx''⟩
      left_inv := by
        intro Z
        apply Subtype.ext
        simpa [hSU] using restrictOpen_map_eq U Z.1
          (inter_nonempty_of_le
            (IrreducibleCloseds.map (Subtype.val : U → X) continuous_subtype_val S)
            (IrreducibleCloseds.map (Subtype.val : U → X) continuous_subtype_val Z.1) U hSU
            (IrreducibleCloseds.map_mono continuous_subtype_val Z.2.1))
      right_inv := by
        intro T
        apply Subtype.ext
        simpa using map_restrictOpen_eq T.1 U
          (inter_nonempty_of_le
            (IrreducibleCloseds.map (Subtype.val : U → X) continuous_subtype_val S) T.1 U hSU T.2.1) }
  exact e.toOrderIso
    (by
      intro A B hAB
      exact IrreducibleCloseds.map_mono continuous_subtype_val hAB)
    (by
      intro A B hAB
      change
        ((A.1.restrictOpen U
            (inter_nonempty_of_le
              (IrreducibleCloseds.map (Subtype.val : U → X) continuous_subtype_val S) A.1 U hSU
              A.2.1) : Set U) ⊆
          (B.1.restrictOpen U
            (inter_nonempty_of_le
              (IrreducibleCloseds.map (Subtype.val : U → X) continuous_subtype_val S) B.1 U hSU
              B.2.1) : Set U))
      intro x hx
      simpa [IrreducibleCloseds.coe_restrictOpen] using hAB
        (by simpa [IrreducibleCloseds.coe_restrictOpen] using hx))

/-- Helper for Lemma 5.11.5: relative codimension is unchanged when passing between an interval in
an open subspace and the corresponding interval of ambient closures. -/
private theorem codimBetween_open_eq (U : Opens X) {S S' : IrreducibleCloseds U} (hSS' : S ≤ S') :
    codimBetween S S' hSS' =
      codimBetween
        (IrreducibleCloseds.map (Subtype.val : U → X) continuous_subtype_val S)
        (IrreducibleCloseds.map (Subtype.val : U → X) continuous_subtype_val S')
        (IrreducibleCloseds.map_mono continuous_subtype_val hSS') := by
  -- Compare both codimensions through the Krull dimensions of the corresponding intervals.
  apply WithBot.coe_injective
  calc
    codimBetween S S' hSS' = krullDim (Set.Icc S S') :=
      codimBetween_eq_krullDim hSS'
    _ =
        krullDim
          (Set.Icc
            (IrreducibleCloseds.map (Subtype.val : U → X) continuous_subtype_val S)
            (IrreducibleCloseds.map (Subtype.val : U → X) continuous_subtype_val S')) :=
      Order.krullDim_eq_of_orderIso (open_subspace_interval_orderIso U hSS')
    _ =
        codimBetween
          (IrreducibleCloseds.map (Subtype.val : U → X) continuous_subtype_val S)
          (IrreducibleCloseds.map (Subtype.val : U → X) continuous_subtype_val S')
          (IrreducibleCloseds.map_mono continuous_subtype_val hSS') :=
      (codimBetween_eq_krullDim (IrreducibleCloseds.map_mono continuous_subtype_val hSS')).symm

/-- Helper for Lemma 5.11.5: open subspaces of catenary spaces are catenary. -/
private theorem catenarySpace_opens [CatenarySpace X] (U : Opens X) : CatenarySpace U := by
  refine ⟨?_, ?_⟩
  · intro S S' hSS'
    -- Transport the interval to the ambient space and reuse the ambient finiteness statement.
    have hfinite :
        codimBetween
            (IrreducibleCloseds.map (Subtype.val : U → X) continuous_subtype_val S)
            (IrreducibleCloseds.map (Subtype.val : U → X) continuous_subtype_val S')
            (IrreducibleCloseds.map_mono continuous_subtype_val hSS') < ⊤ :=
      CatenarySpace.finite_codimBetween
        (IrreducibleCloseds.map_mono continuous_subtype_val hSS')
    simpa [codimBetween_open_eq U hSS'] using hfinite
  · intro S S' hSS' s hs
    -- Send a maximal chain in the local interval to the ambient interval, apply catenarity there,
    -- and then rewrite the codimension back through the interval order isomorphism.
    let e := open_subspace_interval_orderIso U hSS'
    have hsImage : IsMaxChain (· ≤ ·) (e '' s) := IsMaxChain.image e hs
    have hlen :
        (e '' s).encard =
          ENat.toNat
              (codimBetween
                (IrreducibleCloseds.map (Subtype.val : U → X) continuous_subtype_val S)
                (IrreducibleCloseds.map (Subtype.val : U → X) continuous_subtype_val S')
                (IrreducibleCloseds.map_mono continuous_subtype_val hSS')) +
            1 :=
      CatenarySpace.maximalIrreducibleClosedChainsHaveLength
        (IrreducibleCloseds.map_mono continuous_subtype_val hSS') (e '' s) hsImage
    calc
      s.encard = (e '' s).encard := by rw [e.injective.encard_image]
      _ =
          ENat.toNat
              (codimBetween
                (IrreducibleCloseds.map (Subtype.val : U → X) continuous_subtype_val S)
                (IrreducibleCloseds.map (Subtype.val : U → X) continuous_subtype_val S')
                (IrreducibleCloseds.map_mono continuous_subtype_val hSS')) +
            1 := hlen
      _ = ENat.toNat (codimBetween S S' hSS') + 1 := by
          rw [codimBetween_open_eq U hSS']

/-- Helper for Lemma 5.11.5: for a closed subtype, mapping an irreducible closed subset to the
ambient space is just its set-theoretic image. -/
private theorem map_subtype_val_eq_image_of_isClosed {S : Set X} (hS : IsClosed S)
    (T : IrreducibleCloseds S) :
    ((IrreducibleCloseds.map (Subtype.val : S → X) continuous_subtype_val T :
        IrreducibleCloseds X) : Set X) =
      (Subtype.val : S → X) '' (T : Set S) := by
  -- The image of a closed subset of a closed subtype is closed in the ambient space, so the
  -- closure built into `IrreducibleCloseds.map` does not enlarge the set.
  rw [IrreducibleCloseds.coe_map, closure_eq_iff_isClosed]
  exact hS.isClosedMap_subtype_val _ T.isClosed

/-- Helper for Lemma 5.11.5: an ambient irreducible closed subset contained in a closed subtype
pulls back to an irreducible closed subset of that subtype. -/
private noncomputable def preimage_irreducibleClosed_of_subset {S : Set X} (hS : IsClosed S)
    (T : IrreducibleCloseds X) (hTS : (T : Set X) ⊆ S) : IrreducibleCloseds S := by
  refine ⟨Subtype.val ⁻¹' (T : Set X), ?_, T.isClosed.preimage continuous_subtype_val⟩
  -- The pullback is homeomorphic to `T` because `T` already lies in the range of the subtype map.
  let e : (Subtype.val ⁻¹' (T : Set X) : Set S) ≃ₜ (T : Set X) :=
    hS.isClosedEmbedding_subtypeVal.isEmbedding.homeomorphOfSubsetRange fun x hx ↦
      ⟨⟨x, hTS hx⟩, rfl⟩
  exact (isIrreducible_iff_irreducibleSpace).2 <|
    (e.irreducibleSpace_iff).2 (Subtype.irreducibleSpace T.isIrreducible)

/-- Helper for Lemma 5.11.5: the ambient image of an irreducible closed subset of a closed
subspace still lies inside that closed subspace. -/
private theorem map_subtype_val_subset_of_isClosed {S : Set X} (hS : IsClosed S)
    (T : IrreducibleCloseds S) :
    ((IrreducibleCloseds.map (Subtype.val : S → X) continuous_subtype_val T :
        IrreducibleCloseds X) : Set X) ⊆ S := by
  -- After rewriting the mapped subset as an image, membership is immediate from the subtype data.
  rw [map_subtype_val_eq_image_of_isClosed hS T]
  rintro x ⟨y, hy, rfl⟩
  exact y.2

/-- Helper for Lemma 5.11.5: an interval of irreducible closed subsets in a closed subspace is
order-isomorphic to the corresponding ambient interval. -/
private noncomputable def closed_subspace_interval_order_iso {S : Set X} (hS : IsClosed S)
    {T T' : IrreducibleCloseds S} (_hTT' : T ≤ T') :
    Set.Icc T T' ≃o
      Set.Icc
        (IrreducibleCloseds.map (Subtype.val : S → X) continuous_subtype_val T)
        (IrreducibleCloseds.map (Subtype.val : S → X) continuous_subtype_val T') := by
  classical
  let e :
      Set.Icc T T' ≃
        Set.Icc
          (IrreducibleCloseds.map (Subtype.val : S → X) continuous_subtype_val T)
          (IrreducibleCloseds.map (Subtype.val : S → X) continuous_subtype_val T') :=
    { toFun := fun Z ↦
        -- Map each irreducible closed subset of the subtype to its ambient image.
        ⟨IrreducibleCloseds.map (Subtype.val : S → X) continuous_subtype_val Z.1,
          IrreducibleCloseds.map_mono continuous_subtype_val Z.2.1,
          IrreducibleCloseds.map_mono continuous_subtype_val Z.2.2⟩
      invFun := fun Z ↦
        -- Pull back ambient subsets using that the upper endpoint already lies in `S`.
        let ZS :
            IrreducibleCloseds S :=
          preimage_irreducibleClosed_of_subset hS Z.1
            (Set.Subset.trans Z.2.2 (map_subtype_val_subset_of_isClosed hS T'))
        ⟨ZS,
          by
            intro x hx
            change (x : X) ∈ (Z.1 : Set X)
            have hxT :
                (x : X) ∈
                  (IrreducibleCloseds.map (Subtype.val : S → X) continuous_subtype_val T :
                    Set X) := by
              rw [map_subtype_val_eq_image_of_isClosed hS T]
              exact ⟨x, hx, rfl⟩
            exact Z.2.1 hxT,
          by
            intro x hx
            have hxZ : (x : X) ∈ (Z.1 : Set X) := by
              simpa using hx
            have hxT' :
                (x : X) ∈
                  (IrreducibleCloseds.map (Subtype.val : S → X) continuous_subtype_val T' :
                    Set X) := Z.2.2 hxZ
            rw [map_subtype_val_eq_image_of_isClosed hS T'] at hxT'
            rcases hxT' with ⟨y, hy, hyx⟩
            have hyx' : y = x := Subtype.ext hyx
            simpa [hyx'] using hy⟩
      left_inv := by
        intro Z
        apply Subtype.ext
        apply IrreducibleCloseds.ext
        ext x
        -- Pulling back the ambient image along the injective subtype map recovers the same set.
        change
          (x : X) ∈
              (IrreducibleCloseds.map (Subtype.val : S → X) continuous_subtype_val Z.1 : Set X) ↔
            x ∈ (Z.1 : Set S)
        rw [map_subtype_val_eq_image_of_isClosed hS Z.1]
        simp
      right_inv := by
        intro Z
        apply Subtype.ext
        apply IrreducibleCloseds.ext
        ext x
        -- The pulled-back set maps back to `Z` because every point of `Z` already lies in `S`.
        rw [map_subtype_val_eq_image_of_isClosed hS
          (preimage_irreducibleClosed_of_subset hS Z.1
            (Set.Subset.trans Z.2.2 (map_subtype_val_subset_of_isClosed hS T')))]
        constructor
        · rintro ⟨y, hy, rfl⟩
          exact hy
        · intro hx
          refine ⟨⟨x, Set.Subset.trans Z.2.2 (map_subtype_val_subset_of_isClosed hS T') hx⟩, ?_, rfl⟩
          exact hx }
  exact e.toOrderIso
    (by
      intro A B hAB
      exact IrreducibleCloseds.map_mono continuous_subtype_val hAB)
    (by
      intro A B hAB
      change
        ((preimage_irreducibleClosed_of_subset hS A.1
            (Set.Subset.trans A.2.2 (map_subtype_val_subset_of_isClosed hS T')) : Set S) ⊆
          (preimage_irreducibleClosed_of_subset hS B.1
            (Set.Subset.trans B.2.2 (map_subtype_val_subset_of_isClosed hS T')) : Set S))
      intro x hx
      exact hAB (by simpa using hx))

/-- Helper for Lemma 5.11.5: relative codimension is unchanged when passing between a closed
subspace interval and the corresponding ambient interval. -/
private theorem codimBetween_closed_eq {S : Set X} (hS : IsClosed S)
    {T T' : IrreducibleCloseds S} (hTT' : T ≤ T') :
    codimBetween T T' hTT' =
      codimBetween
        (IrreducibleCloseds.map (Subtype.val : S → X) continuous_subtype_val T)
        (IrreducibleCloseds.map (Subtype.val : S → X) continuous_subtype_val T')
        (IrreducibleCloseds.map_mono continuous_subtype_val hTT') := by
  -- Compare both codimensions through the Krull dimensions of the order-isomorphic intervals.
  apply WithBot.coe_injective
  calc
    codimBetween T T' hTT' = krullDim (Set.Icc T T') :=
      codimBetween_eq_krullDim hTT'
    _ =
        krullDim
          (Set.Icc
            (IrreducibleCloseds.map (Subtype.val : S → X) continuous_subtype_val T)
            (IrreducibleCloseds.map (Subtype.val : S → X) continuous_subtype_val T')) :=
      Order.krullDim_eq_of_orderIso (closed_subspace_interval_order_iso hS hTT')
    _ =
        codimBetween
          (IrreducibleCloseds.map (Subtype.val : S → X) continuous_subtype_val T)
          (IrreducibleCloseds.map (Subtype.val : S → X) continuous_subtype_val T')
          (IrreducibleCloseds.map_mono continuous_subtype_val hTT') :=
      (codimBetween_eq_krullDim (IrreducibleCloseds.map_mono continuous_subtype_val hTT')).symm

/-- Helper for Lemma 5.11.5: closed subspaces of catenary spaces are catenary. -/
theorem IsClosed.catenarySpace_subtype [CatenarySpace X] {S : Set X}
    (hS : IsClosed S) : CatenarySpace S := by
  refine ⟨?_, ?_⟩
  · intro T T' hTT'
    -- Transport finite codimension to the ambient interval inside `X`.
    have hfinite :
        codimBetween
            (IrreducibleCloseds.map (Subtype.val : S → X) continuous_subtype_val T)
            (IrreducibleCloseds.map (Subtype.val : S → X) continuous_subtype_val T')
            (IrreducibleCloseds.map_mono continuous_subtype_val hTT') < ⊤ :=
      CatenarySpace.finite_codimBetween
        (IrreducibleCloseds.map_mono continuous_subtype_val hTT')
    simpa [codimBetween_closed_eq hS hTT'] using hfinite
  · intro T T' hTT' s hs
    -- Compare maximal chains through the interval order isomorphism to the ambient interval.
    let e := closed_subspace_interval_order_iso hS hTT'
    have hsImage : IsMaxChain (· ≤ ·) (e '' s) := IsMaxChain.image e hs
    have hlen :
        (e '' s).encard =
          ENat.toNat
              (codimBetween
                (IrreducibleCloseds.map (Subtype.val : S → X) continuous_subtype_val T)
                (IrreducibleCloseds.map (Subtype.val : S → X) continuous_subtype_val T')
                (IrreducibleCloseds.map_mono continuous_subtype_val hTT')) +
            1 :=
      CatenarySpace.maximalIrreducibleClosedChainsHaveLength
        (IrreducibleCloseds.map_mono continuous_subtype_val hTT') (e '' s) hsImage
    calc
      s.encard = (e '' s).encard := by rw [e.injective.encard_image]
      _ =
          ENat.toNat
              (codimBetween
                (IrreducibleCloseds.map (Subtype.val : S → X) continuous_subtype_val T)
                (IrreducibleCloseds.map (Subtype.val : S → X) continuous_subtype_val T')
                (IrreducibleCloseds.map_mono continuous_subtype_val hTT')) +
            1 := hlen
      _ = ENat.toNat (codimBetween T T' hTT') + 1 := by
          rw [codimBetween_closed_eq hS hTT']

/-- Helper for Lemma 5.11.5: a homeomorphism transports catenarity across spaces. -/
private noncomputable def irreducibleCloseds_orderIso_of_homeomorph {X' : Type v}
    [TopologicalSpace X'] (e : X ≃ₜ X') : IrreducibleCloseds X ≃o IrreducibleCloseds X' := by
  let e' : IrreducibleCloseds X ≃ IrreducibleCloseds X' :=
    { toFun := fun T ↦ IrreducibleCloseds.map e e.continuous T
      invFun := fun T ↦ IrreducibleCloseds.map e.symm e.symm.continuous T
      left_inv := by
        intro T
        apply IrreducibleCloseds.ext
        rw [IrreducibleCloseds.coe_map, IrreducibleCloseds.coe_map]
        -- A homeomorphism maps closed sets to closed sets and the inverse cancels set-theoretically.
        rw [closure_eq_iff_isClosed.mpr (e.isClosedMap _ T.isClosed), Set.image_image]
        simpa using T.isClosed.closure_eq
      right_inv := by
        intro T
        apply IrreducibleCloseds.ext
        rw [IrreducibleCloseds.coe_map, IrreducibleCloseds.coe_map]
        rw [closure_eq_iff_isClosed.mpr (e.symm.isClosedMap _ T.isClosed), Set.image_image]
        simpa using T.isClosed.closure_eq }
  exact e'.toOrderIso
    (by
      intro A B hAB
      exact IrreducibleCloseds.map_mono e.continuous hAB)
    (by
      intro A B hAB
      exact IrreducibleCloseds.map_mono e.symm.continuous hAB)

/-- Helper for Lemma 5.11.5: an order isomorphism restricts to the corresponding intervals. -/
private noncomputable def orderIso_interval {α β : Type*} [Preorder α] [Preorder β]
    (e : α ≃o β) (a b : α) : Set.Icc a b ≃o Set.Icc (e a) (e b) where
  toFun x := ⟨e x.1, e.monotone x.2.1, e.monotone x.2.2⟩
  invFun y := ⟨e.symm y.1, by simpa using e.symm.monotone y.2.1, by
    simpa using e.symm.monotone y.2.2⟩
  left_inv x := by
    ext
    simp
  right_inv y := by
    ext
    simp
  map_rel_iff' := by
    intro x y
    simpa using e.le_iff_le

namespace Homeomorph

/-- Helper for Lemma 5.11.5: homeomorphic spaces have the same catenary property. -/
theorem catenarySpace {X' : Type v} [TopologicalSpace X'] (e : X ≃ₜ X')
    [CatenarySpace X] : CatenarySpace X' := by
  let eI : IrreducibleCloseds X' ≃o IrreducibleCloseds X :=
    irreducibleCloseds_orderIso_of_homeomorph e.symm
  refine ⟨?_, ?_⟩
  · intro T T' hTT'
    let eInt := orderIso_interval eI T T'
    -- Transport the codimension computation through the interval order isomorphism from `e.symm`.
    have hfinite : codimBetween (eI T) (eI T') (eI.monotone hTT') < ⊤ :=
      CatenarySpace.finite_codimBetween (eI.monotone hTT')
    have hcodim :
        codimBetween T T' hTT' = codimBetween (eI T) (eI T') (eI.monotone hTT') := by
      apply WithBot.coe_injective
      calc
        codimBetween T T' hTT' = krullDim (Set.Icc T T') :=
          codimBetween_eq_krullDim hTT'
        _ = krullDim (Set.Icc (eI T) (eI T')) :=
          Order.krullDim_eq_of_orderIso eInt
        _ = codimBetween (eI T) (eI T') (eI.monotone hTT') :=
          (codimBetween_eq_krullDim (eI.monotone hTT')).symm
    simpa [hcodim] using hfinite
  · intro T T' hTT' s hs
    -- Send a maximal chain through the interval equivalence induced by the homeomorphism.
    let eInt := orderIso_interval eI T T'
    have hsImage : IsMaxChain (· ≤ ·) (eInt '' s) := IsMaxChain.image eInt hs
    have hlen :
        (eInt '' s).encard =
          ENat.toNat (codimBetween (eI T) (eI T') (eI.monotone hTT')) + 1 :=
      CatenarySpace.maximalIrreducibleClosedChainsHaveLength
        (eI.monotone hTT') (eInt '' s) hsImage
    have hcodim :
        codimBetween T T' hTT' = codimBetween (eI T) (eI T') (eI.monotone hTT') := by
      apply WithBot.coe_injective
      calc
        codimBetween T T' hTT' = krullDim (Set.Icc T T') :=
          codimBetween_eq_krullDim hTT'
        _ = krullDim (Set.Icc (eI T) (eI T')) :=
          Order.krullDim_eq_of_orderIso eInt
        _ = codimBetween (eI T) (eI T') (eI.monotone hTT') :=
          (codimBetween_eq_krullDim (eI.monotone hTT')).symm
    calc
      s.encard = (eInt '' s).encard := by rw [eInt.injective.encard_image]
      _ = ENat.toNat (codimBetween (eI T) (eI T') (eI.monotone hTT')) + 1 := hlen
      _ = ENat.toNat (codimBetween T T' hTT') + 1 := by rw [hcodim]

end Homeomorph

-- Proof sketch: write a locally closed subset as an open subset of its closure. Closed irreducible
-- subsets of the subtype correspond to closed irreducible subsets of the ambient space meeting the
-- locally closed piece, and the interval of irreducible closed subsets is preserved under this
-- correspondence.
/-- A locally closed subspace of a catenary space is catenary. This is the reusable bridge/view
form of the “moreover” clause in Lemma 5.11.5. -/
protected theorem IsLocallyClosed.catenarySpace [CatenarySpace X] {Y : Set X}
    (hY : IsLocallyClosed Y) : CatenarySpace Y := by
  -- Route correction: first descend catenarity to `closure Y`, then restrict to the open subset
  -- cut out by `Y`, and only at the end transport back along the canonical homeomorphism.
  let V : Opens (closure Y) := ⟨Subtype.val ⁻¹' Y, hY.isOpen_preimage_val_closure⟩
  let eV : V ≃ₜ ((closure Y) ∩ Y : Set X) :=
    (Homeomorph.setCongr (by
      ext y
      constructor
      · intro hy
        exact ⟨y.2, hy⟩
      · intro hy
        exact hy.2)).trans
      (isClosed_closure.isClosedEmbedding_subtypeVal.isEmbedding.homeomorphOfSubsetRange
        fun y hy ↦ ⟨⟨y, hy.1⟩, rfl⟩)
  let eY : Y ≃ₜ ((closure Y) ∩ Y : Set X) :=
    Homeomorph.setCongr (by
      ext y
      constructor
      · intro hy
        exact ⟨subset_closure hy, hy⟩
      · intro hy
        exact hy.2)
  let e : Y ≃ₜ V := eY.trans eV.symm
  letI : CatenarySpace (closure Y) := isClosed_closure.catenarySpace_subtype
  haveI : CatenarySpace V := catenarySpace_opens V
  -- The locally closed subtype is homeomorphic to the corresponding open subset of its closure.
  exact e.symm.catenarySpace

namespace TopologicalSpace.IsOpenCover

-- Proof sketch: the forward implication restricts catenarity to each open member of the cover
-- using the open-subspace theorem above. For the converse, compare irreducible closed chains in
-- `X` with their restrictions to a cover member meeting the lower endpoint.
/-- Catenarity is local on the target for open covers. -/
theorem catenarySpace_iff {ι : Type v} {U : ι → Opens X} (hU : IsOpenCover U) :
    CatenarySpace X ↔ ∀ i, CatenarySpace (U i) := by
  constructor
  · intro hX i
    haveI : CatenarySpace X := hX
    exact catenarySpace_opens (U i)
  · intro hCat
    refine ⟨?_, ?_⟩
    · intro T T' hTT'
      -- Choose a cover member meeting the lower endpoint so the whole interval restricts there.
      obtain ⟨x, hx⟩ := T.isIrreducible.nonempty
      obtain ⟨i, hxi⟩ := hU.exists_mem x
      let TU : IrreducibleCloseds (U i) := T.restrictOpen (U i) ⟨x, hx, hxi⟩
      let T'U : IrreducibleCloseds (U i) :=
        T'.restrictOpen (U i) (inter_nonempty_of_le T T' (U i) ⟨x, hx, hxi⟩ hTT')
      have hTUU : TU ≤ T'U := by
        intro y hy
        exact hTT' (by simpa [TU, T'U, IrreducibleCloseds.coe_restrictOpen] using hy)
      haveI : CatenarySpace (U i) := hCat i
      have hfinite : codimBetween TU T'U hTUU < ⊤ :=
        CatenarySpace.finite_codimBetween hTUU
      have hcodim :
          codimBetween TU T'U hTUU = codimBetween T T' hTT' := by
        -- Compare the restricted interval with the ambient interval via the open-subspace order
        -- isomorphism, then rewrite the codomain interval using `map_restrictOpen_eq`.
        let e :=
          (open_subspace_interval_orderIso (U i) hTUU).trans <|
            OrderIso.setCongr
              (Set.Icc
                (IrreducibleCloseds.map (Subtype.val : U i → X) continuous_subtype_val TU)
                (IrreducibleCloseds.map (Subtype.val : U i → X) continuous_subtype_val T'U))
              (Set.Icc T T') (by simp [TU, T'U])
        apply WithBot.coe_injective
        calc
          codimBetween TU T'U hTUU = krullDim (Set.Icc TU T'U) :=
            codimBetween_eq_krullDim hTUU
          _ = krullDim (Set.Icc T T') := Order.krullDim_eq_of_orderIso e
          _ = codimBetween T T' hTT' := (codimBetween_eq_krullDim hTT').symm
      simpa [hcodim] using hfinite
    · intro T T' hTT' s hs
      -- Restrict the whole interval to one cover member through the lower endpoint, apply the
      -- local catenary length formula there, and transport the answer back to `X`.
      obtain ⟨x, hx⟩ := T.isIrreducible.nonempty
      obtain ⟨i, hxi⟩ := hU.exists_mem x
      let TU : IrreducibleCloseds (U i) := T.restrictOpen (U i) ⟨x, hx, hxi⟩
      let T'U : IrreducibleCloseds (U i) :=
        T'.restrictOpen (U i) (inter_nonempty_of_le T T' (U i) ⟨x, hx, hxi⟩ hTT')
      have hTUU : TU ≤ T'U := by
        intro y hy
        exact hTT' (by simpa [TU, T'U, IrreducibleCloseds.coe_restrictOpen] using hy)
      haveI : CatenarySpace (U i) := hCat i
      let e :=
        (open_subspace_interval_orderIso (U i) hTUU).trans <|
          OrderIso.setCongr
            (Set.Icc
              (IrreducibleCloseds.map (Subtype.val : U i → X) continuous_subtype_val TU)
              (IrreducibleCloseds.map (Subtype.val : U i → X) continuous_subtype_val T'U))
            (Set.Icc T T') (by simp [TU, T'U])
      have hsLocal : IsMaxChain (· ≤ ·) (e.symm '' s) := IsMaxChain.image e.symm hs
      have hlenLocal :
          (e.symm '' s).encard = ENat.toNat (codimBetween TU T'U hTUU) + 1 :=
        CatenarySpace.maximalIrreducibleClosedChainsHaveLength hTUU (e.symm '' s) hsLocal
      have hcodim :
          codimBetween TU T'U hTUU = codimBetween T T' hTT' := by
        apply WithBot.coe_injective
        calc
          codimBetween TU T'U hTUU = krullDim (Set.Icc TU T'U) :=
            codimBetween_eq_krullDim hTUU
          _ = krullDim (Set.Icc T T') := Order.krullDim_eq_of_orderIso e
          _ = codimBetween T T' hTT' := (codimBetween_eq_krullDim hTT').symm
      calc
        s.encard = (e.symm '' s).encard := by rw [e.symm.injective.encard_image]
        _ = ENat.toNat (codimBetween TU T'U hTUU) + 1 := hlenLocal
        _ = ENat.toNat (codimBetween T T' hTT') + 1 := by rw [hcodim]

end TopologicalSpace.IsOpenCover

-- Proof sketch: the canonical owner-level locality statement is
-- `TopologicalSpace.IsOpenCover.catenarySpace_iff`. The forward implication chooses a trivial open
-- cover, while the converse applies that theorem to the given cover.
/-- Lemma 5.11.5: a topological space is catenary if and only if it admits an open cover by
catenary open subspaces.
This is the source-facing existential bridge for the canonical locality theorem
`TopologicalSpace.IsOpenCover.catenarySpace_iff`. -/
theorem catenarySpace_iff_hasOpenCoverByCatenarySpaces :
    CatenarySpace X ↔
      ∃ (ι : Type v) (U : ι → Opens X), IsOpenCover U ∧ ∀ i, CatenarySpace (U i) := by
  constructor
  · intro hX
    haveI : CatenarySpace X := hX
    refine ⟨ULift Unit, fun _ ↦ (⊤ : Opens X), ?_, ?_⟩
    · simp [TopologicalSpace.IsOpenCover]
    · intro i
      simpa using catenarySpace_opens (⊤ : Opens X)
  · rintro ⟨ι, U, hU, hUcat⟩
    exact hU.catenarySpace_iff.2 hUcat
