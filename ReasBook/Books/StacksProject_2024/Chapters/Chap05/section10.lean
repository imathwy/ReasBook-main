import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_5_10_1 (from Chap05) -/
universe u

open Set TopologicalSpace Order

variable {X : Type u} [TopologicalSpace X]

/- 
Domain-style sampling:
- primary domain: topological Krull dimension, built from chains of irreducible closed subsets and
  then localized over open neighbourhoods of a point;
- sampled owner declarations:
  `Order.krullDim`,
  `Order.krullDim_eq_iSup_length`,
  `Order.krullDim_eq_bot_iff`,
  `topologicalKrullDim`,
  `OpenNhdsOf`.

Layer triage:
- `source-facing`: `topologicalKrullDimAt` and its minimum-attainment lemmas;
- `core/canonical`: `Order.krullDim`, `LTSeries`, and mathlib's `topologicalKrullDim`;
- `bridge/view`: the source-facing restatements of `topologicalKrullDim` via chain lengths and the
  empty-space criterion, together with the `sInf` reformulation of `topologicalKrullDimAt`.

Primitive data are only the point `x` and the owner-indexed family
`fun U : OpenNhdsOf x ↦ topologicalKrullDim U`; the set-valued `sInf` description, minimum
property, and realization lemmas are derived API from that indexed infimum.
-/

/-- Definition 5.10.1 (1): a chain of irreducible closed subsets of `X` is the canonical
order-theoretic notion `LTSeries`. -/
abbrev irreducible_closed_chain (X : Type u) [TopologicalSpace X] :=
  LTSeries (IrreducibleCloseds X)

-- Proof sketch: unfold the abbreviation.
/-- The chain abbreviation is exactly the canonical strict series type on irreducible closed
subsets. -/
theorem irreducible_closed_chain_def (X : Type u) [TopologicalSpace X] :
    irreducible_closed_chain X = LTSeries (IrreducibleCloseds X) := by
  -- Unfold the source-facing abbreviation to expose the canonical owner type.
  rfl

/-- Definition 5.10.1 (2): for a chain of irreducible closed subsets of `X`, its length is the
canonical field `p.length`, i.e. `RelSeries.length`. -/
abbrev irreducible_closed_chain_length {X : Type u} [TopologicalSpace X]
    (p : irreducible_closed_chain X) : ℕ :=
  p.length

-- Proof sketch: unfold the abbreviation.
/-- The chain-length abbreviation is exactly the length field of the underlying strict series. -/
theorem irreducible_closed_chain_length_def {X : Type u} [TopologicalSpace X]
    (p : irreducible_closed_chain X) :
    irreducible_closed_chain_length p = p.length := by
  -- Unfold the source-facing length abbreviation and read off the canonical projection.
  rfl

/- Canonical owner for the Krull dimension of a topological space. -/
recall topologicalKrullDim

/-- Bridge between the owner poset `IrreducibleCloseds X` and the underlying space: the poset of
irreducible closed subsets is empty exactly when the space itself is empty. -/
theorem isEmpty_irreducibleCloseds_iff :
    IsEmpty (IrreducibleCloseds X) ↔ IsEmpty X := by
  constructor
  · intro h
    exact ⟨fun x ↦ h.false
      ⟨closure ({x} : Set X), isIrreducible_singleton.closure, isClosed_closure⟩⟩
  · intro h
    exact ⟨fun Z ↦ by
      rcases Z.isIrreducible.nonempty with ⟨x, hx⟩
      exact h.false x⟩

-- Proof sketch: unfold `topologicalKrullDim` and `Order.krullDim`.
/-- Definition 5.10.1 (3): the Krull dimension of `X` is the supremum of the lengths of chains of
irreducible closed subsets of `X`. -/
theorem topologicalKrullDim_eq_iSup_length_irreducibleCloseds :
    topologicalKrullDim X =
      ⨆ p : LTSeries (IrreducibleCloseds X), (p.length : WithBot ℕ∞) :=
  rfl

-- Proof sketch: unfold `topologicalKrullDim` and apply the general order-theoretic characterization
-- `Order.krullDim_eq_bot_iff` to the poset `IrreducibleCloseds X`.
/-- Definition 5.10.1 (4): the Krull dimension of `X` is `-∞` exactly when `X` is empty. -/
theorem topologicalKrullDim_eq_bot_iff :
    topologicalKrullDim X = ⊥ ↔ IsEmpty X := by
  rw [topologicalKrullDim, krullDim_eq_bot_iff, isEmpty_irreducibleCloseds_iff]

/-- Definition 5.10.1 (5): the Krull dimension of `X` at a point `x` is the minimum of the Krull
dimensions of the open neighbourhoods of `x`. -/
noncomputable def topologicalKrullDimAt (x : X) : WithBot ℕ∞ :=
  ⨅ U : OpenNhdsOf x, topologicalKrullDim U

section LocalKrullDimAt

variable (x : X)

local notation "localKrullDimValues" =>
  Set.range fun U : OpenNhdsOf x ↦ topologicalKrullDim U

/-- Definition 5.10.1 (6): `topologicalKrullDimAt x` is the minimum of the dimensions of the open
neighbourhoods of `x`. -/
theorem isLeast_topologicalKrullDimAt :
    IsLeast localKrullDimValues (topologicalKrullDimAt x) := by
  simpa [topologicalKrullDimAt] using
    isLeast_csInf (Set.range_nonempty fun U : OpenNhdsOf x ↦ topologicalKrullDim U)

/-- The local Krull dimension is bounded above by the dimension of every open neighbourhood of the
point. -/
theorem topologicalKrullDimAt_le (U : OpenNhdsOf x) :
    topologicalKrullDimAt x ≤ topologicalKrullDim U := by
  exact (isLeast_topologicalKrullDimAt x).2 ⟨U, rfl⟩

/-- There is an open neighbourhood of `x` whose dimension realizes `topologicalKrullDimAt x`. -/
theorem exists_openNhdsOf_topologicalKrullDimAt_eq :
    ∃ U : OpenNhdsOf x, topologicalKrullDimAt x = topologicalKrullDim U := by
  rcases (isLeast_topologicalKrullDimAt x).1 with ⟨U, hU⟩
  exact ⟨U, hU.symm⟩

end LocalKrullDimAt

/-! ### Lemma_5_10_2 (from Chap05) -/
universe u

open Set TopologicalSpace Order

variable {X : Type u} [TopologicalSpace X]

/- 
Domain-style sampling for global versus local topological Krull dimension:
- primary domain: topological Krull dimension on a space and its localization at a point via open
  neighbourhoods;
- inspected owner declarations:
  `topologicalKrullDim`,
  `Order.krullDim_eq_iSup_coheight`,
  `Order.coheight_eq_krullDim_Ici`,
  `subset_closure_inter_of_isPreirreducible_of_isOpen`,
  `TopologicalSpace.IrreducibleCloseds.map`;
- best owner abstraction: the global owner is `topologicalKrullDim X`, with the hard inequality
  proved by passing through the canonical `Order.coheight` of irreducible closed subsets and
  restricting those subsets to open neighbourhoods of a chosen point through the ambient subtype
  map.

Layer triage:
- `source-facing`: `topologicalKrullDim_eq_iSup_topologicalKrullDimAt`;
- `core/canonical`: `topologicalKrullDim`, `Order.krullDim_eq_iSup_coheight`, and
  `Order.coheight_le_krullDim`;
- `bridge/view`: the local owner `topologicalKrullDimAt`, its infimum API from
  `Definition_5_10_1`, and the density statement
  `subset_closure_inter_of_isPreirreducible_of_isOpen`.

Primitive data are only the ambient space and its open neighbourhoods. The local infimum
`topologicalKrullDimAt` already provides the source-facing owner; the restriction argument should
therefore stay inside the canonical poset of irreducible closed subsets rather than introducing a
parallel chain package.
-/

/-- Helper for Lemma 5.10.2: the preimage of an irreducible closed subset along the subtype map of
an open set is irreducible as soon as the open set meets the subset. -/
private theorem restrictOpenIrreducibleClosed_isIrreducible
    (Y : IrreducibleCloseds X) (U : Opens X)
    (hYU : ((Y : Set X) ∩ (U : Set X)).Nonempty) :
    IsIrreducible (Subtype.val ⁻¹' (Y : Set X) : Set U) := by
  -- Convert nonemptiness of the intersection with `U` into nonemptiness of the intersection with
  -- the range of the subtype map, so the standard preimage lemma applies.
  have hRange : Set.range (Subtype.val : U → X) = (U : Set X) := by
    ext x
    simp
  have hYU' : ((Y : Set X) ∩ Set.range (Subtype.val : U → X)).Nonempty := by
    simpa [hRange] using hYU
  simpa using Y.isIrreducible.preimage U.isOpenEmbedding' hYU'

/-- Helper for Lemma 5.10.2: intersecting an irreducible closed subset with an open that meets it
defines an irreducible closed subset of the corresponding open subspace. -/
private noncomputable def restrictOpenIrreducibleClosed
    (Y : IrreducibleCloseds X) (U : Opens X)
    (hYU : ((Y : Set X) ∩ (U : Set X)).Nonempty) : IrreducibleCloseds U :=
  ⟨Subtype.val ⁻¹' (Y : Set X),
    restrictOpenIrreducibleClosed_isIrreducible Y U hYU,
    Y.isClosed.preimage continuous_subtype_val⟩

/-- Helper for Lemma 5.10.2: the carrier of the restricted irreducible closed subset is the
expected preimage under the subtype map. -/
@[simp] private theorem coe_restrictOpenIrreducibleClosed
    (Y : IrreducibleCloseds X) (U : Opens X)
    (hYU : ((Y : Set X) ∩ (U : Set X)).Nonempty) :
    (restrictOpenIrreducibleClosed Y U hYU : Set U) = Subtype.val ⁻¹' (Y : Set X) :=
  rfl

/-- Helper for Lemma 5.10.2: if an open set meets `Y`, then it meets every irreducible closed set
containing `Y`. -/
private theorem inter_nonempty_of_le
    (Y T : IrreducibleCloseds X) (U : Opens X)
    (hYU : ((Y : Set X) ∩ (U : Set X)).Nonempty) (hYT : Y ≤ T) :
    ((T : Set X) ∩ (U : Set X)).Nonempty :=
  hYU.mono fun _ hx ↦ ⟨hYT hx.1, hx.2⟩

/-- Helper for Lemma 5.10.2: when an irreducible closed subset meets an open, its intersection with
that open is dense in the subset. -/
theorem closure_inter_eq_of_irreducibleClosed_meets_open
    (Y : IrreducibleCloseds X) (U : Opens X)
    (hYU : ((Y : Set X) ∩ (U : Set X)).Nonempty) :
    closure ((Y : Set X) ∩ (U : Set X)) = (Y : Set X) := by
  -- One inclusion uses closedness of `Y`; the other is the standard density lemma for nonempty
  -- opens in a preirreducible subspace.
  apply Subset.antisymm
  · exact closure_minimal inter_subset_left Y.isClosed
  ·
    exact subset_closure_inter_of_isPreirreducible_of_isOpen
      Y.isIrreducible.isPreirreducible U.isOpen hYU

/-- Helper for Lemma 5.10.2: an irreducible closed subset through `x` contributes its coheight to
every open neighbourhood of `x`. -/
private theorem coheight_le_topologicalKrullDim_openNhdsOf_of_mem
    (Y : IrreducibleCloseds X) {x : X} (hx : x ∈ (Y : Set X)) (U : OpenNhdsOf x) :
    Order.coheight Y ≤ topologicalKrullDim U := by
  -- Restrict every irreducible closed superset of `Y` to the neighbourhood `U`; this gives an
  -- injective monotone map on the upper interval above `Y`.
  have hYU : ((Y : Set X) ∩ (U : Set X)).Nonempty := ⟨x, hx, U.2⟩
  let f : Set.Ici Y → IrreducibleCloseds U := fun T ↦
    restrictOpenIrreducibleClosed T.1 U.toOpens (inter_nonempty_of_le Y T.1 U.toOpens hYU T.2)
  have hf_mono : Monotone f := by
    intro A B hAB
    simpa [f, coe_restrictOpenIrreducibleClosed] using Set.preimage_mono hAB
  have hmap :
      ∀ T : Set.Ici Y,
        TopologicalSpace.IrreducibleCloseds.map (Subtype.val : U → X) continuous_subtype_val
          (f T) = T.1 := by
    intro T
    have hRange : Set.range (Subtype.val : U → X) = (U : Set X) := by
      ext z
      simp
    have hImage :
        (Subtype.val : U → X) '' (Subtype.val ⁻¹' ((T.1 : IrreducibleCloseds X) : Set X)) =
          ((T.1 : IrreducibleCloseds X) : Set X) ∩ Set.range (Subtype.val : U → X) := by
      ext z
      simp
    -- Mapping the restriction back to `X` recovers the original irreducible closed set because
    -- the intersection with `U` is dense in that set.
    apply IrreducibleCloseds.ext
    rw [TopologicalSpace.IrreducibleCloseds.coe_map]
    rw [coe_restrictOpenIrreducibleClosed]
    calc
      closure ((Subtype.val : U → X) '' (Subtype.val ⁻¹' ((T.1 : IrreducibleCloseds X) : Set X))) =
          closure ((((T.1 : IrreducibleCloseds X) : Set X) ∩ Set.range (Subtype.val : U → X))) := by
            simp [hImage]
      _ = closure ((((T.1 : IrreducibleCloseds X) : Set X) ∩ (U : Set X))) := by
            rw [hRange]
      _ = ((T.1 : IrreducibleCloseds X) : Set X) := by
            exact closure_inter_eq_of_irreducibleClosed_meets_open T.1 U.toOpens
              (inter_nonempty_of_le Y T.1 U.toOpens hYU T.2)
  have hf_injective : Function.Injective f := by
    intro A B hAB
    -- Applying the ambient map back to `X` shows that equal restrictions come from equal ambient
    -- irreducible closed subsets.
    apply Subtype.ext
    simpa [hmap A, hmap B] using congrArg
      (TopologicalSpace.IrreducibleCloseds.map (Subtype.val : U → X) continuous_subtype_val) hAB
  rw [Order.coheight_eq_krullDim_Ici]
  simpa [topologicalKrullDim] using
    Order.krullDim_le_of_strictMono f (hf_mono.strictMono_of_injective hf_injective)

/-- Helper for Lemma 5.10.2: an irreducible closed subset through `x` contributes its coheight to
the local Krull dimension at `x`. -/
private theorem coheight_le_topologicalKrullDimAt_of_mem
    (Y : IrreducibleCloseds X) {x : X} (hx : x ∈ (Y : Set X)) :
    Order.coheight Y ≤ topologicalKrullDimAt x := by
  -- Bound the local infimum by showing that every neighbourhood of `x` has dimension at least the
  -- coheight of `Y`.
  refine le_iInf fun U ↦ ?_
  exact coheight_le_topologicalKrullDim_openNhdsOf_of_mem Y hx U

-- Proof sketch: the hard inequality chooses a point on an irreducible closed subset witnessing
-- global coheight and restricts the upper interval above that subset to every neighbourhood of the
-- point; the easy inequality evaluates the infimum defining `topologicalKrullDimAt` at `⊤`.
/-- Lemma 5.10.2: the Krull dimension of a topological space is the supremum of the local Krull
dimensions at its points. -/
theorem topologicalKrullDim_eq_iSup_topologicalKrullDimAt
    {X : Type u} [TopologicalSpace X] :
    topologicalKrullDim X = ⨆ x : X, topologicalKrullDimAt x := by
  refine le_antisymm ?_ ?_
  · rw [topologicalKrullDim, Order.krullDim_eq_iSup_coheight]
    -- Route correction: replace the earlier shortcut through the later open-restriction lemma by a
    -- direct restriction argument inside the upper interval above each irreducible closed subset.
    refine iSup_le fun Y ↦ ?_
    obtain ⟨x, hx⟩ := Y.isIrreducible.nonempty
    exact le_iSup_of_le x (coheight_le_topologicalKrullDimAt_of_mem Y hx)
  · refine iSup_le fun x ↦ ?_
    let U : OpenNhdsOf x := ⊤
    have hU : topologicalKrullDim U ≤ topologicalKrullDim X := by
      -- The total space is itself an open neighbourhood of `x`, so the local infimum is bounded
      -- by the global dimension.
      simpa [U] using topologicalKrullDim_subspace_le X (Set.univ : Set X)
    exact (topologicalKrullDimAt_le x U).trans hU

/-! ### Example_5_10_3 (from Chap05) -/
open Order TopologicalSpace

universe u

variable (X : Type u) [TopologicalSpace X]

/- Domain-style sampling for topological Krull dimension in Hausdorff spaces:
- primary domain: topological Krull dimension via the poset `IrreducibleCloseds X`;
- same-domain declarations inspected:
  `topologicalKrullDim`,
  `Order.krullDim_nonpos_iff_forall_isMax`,
  `Order.krullDim_nonneg_iff`,
  `IrreducibleCloseds.exists_eq_singleton`;
- best owner abstraction: `topologicalKrullDim X`, reduced to the order-theoretic owner
  `krullDim (IrreducibleCloseds X)`;
- primitive-vs-derived split: the primitive input is only the Hausdorff and nonempty structure on
  `X`; the singleton description of irreducible closed subsets is already derived upstream in
  `Example_5_8_13`, and the Euclidean-space statement is a specialization of the general theorem.

Layer triage:
- `source-facing`: `topologicalKrullDim_eq_zero_of_nonempty_t2`;
- `core/canonical`: `topologicalKrullDim` and the order-theoretic `krullDim` lemmas;
- `bridge/view`: `euclideanSpace_topologicalKrullDim_eq_zero`.
-/

-- Proof sketch: reuse the upstream chapter theorem that every irreducible closed subset of a
-- Hausdorff space is a singleton, so every element of `IrreducibleCloseds X` is maximal. The
-- order-theoretic criterion `krullDim_nonpos_iff_forall_isMax` gives `topologicalKrullDim X ≤ 0`,
-- and `krullDim_nonneg_iff` turns nonemptiness of `X` into the reverse inequality.
/-- A nonempty Hausdorff space has topological Krull dimension `0`. -/
theorem topologicalKrullDim_eq_zero_of_nonempty_t2 [T2Space X] [Nonempty X] :
    topologicalKrullDim X = 0 := by
  refine le_antisymm ?_ ?_
  · rw [topologicalKrullDim, krullDim_nonpos_iff_forall_isMax]
    intro Z Y hZY
    obtain ⟨z, hZ⟩ := IrreducibleCloseds.exists_eq_singleton Z
    obtain ⟨y, hY⟩ := IrreducibleCloseds.exists_eq_singleton Y
    have hz : z = y := by
      have : z ∈ (Y : Set X) := hZY <| by simp [hZ]
      simp [hY] at this
      exact this
    simp [hZ, hY, hz]
  · rw [topologicalKrullDim, krullDim_nonneg_iff]
    exact ‹Nonempty X›.map fun x ↦ ({x} : IrreducibleCloseds X)

/-- Example 5.10.3: the topological Krull dimension of the usual Euclidean space `ℝ^n`, modeled as
`EuclideanSpace ℝ (Fin n)`, is `0`. -/
theorem euclideanSpace_topologicalKrullDim_eq_zero (n : ℕ) :
    topologicalKrullDim (EuclideanSpace ℝ (Fin n)) = 0 := by
  simpa using topologicalKrullDim_eq_zero_of_nonempty_t2 (EuclideanSpace ℝ (Fin n))

/-! ### Example_5_10_4 (from Chap05) -/
open Set TopologicalSpace Order Topology Specialization
open Topology.IsUpperSet
open Topology.WithUpperSet

/- Domain-style sampling for finite Alexandrov chain examples:
- primary domain: topological Krull dimension in Alexandrov-discrete spaces, with the two-point
  example organized around mathlib's canonical Sierpiński-space owner `Prop`;
- sampled canonical declarations:
  `topologicalKrullDim`,
  `homeoWithUpperSetTopologyorderIso`,
  `irreducibleSetEquivPoints`,
  `Topology.IsUpperSet.isOpen_iff_isUpperSet`;
- best owner abstraction: the canonical Sierpiński space `Prop`, with the finite upper-set chain
  `WithUpperSet (Fin (n + 1))` kept only as a bridge/view model for the general chain dimension
  computation;
- primitive-vs-derived split: the primitive bridge data are the chain model
  `WithUpperSet (Fin (n + 1))`, the local `T0Space`/`QuasiSober` instances used to apply
  `irreducibleSetEquivPoints`, and the order identifications of `Specialization Prop` with `Fin 2`;
  the explicit description of the Sierpiński opens and the resulting dimension statements are
  derived API.

Layer triage:
- `source-facing`: the canonical Sierpiński space `Prop`, its open-set classification, and its
  topological Krull dimension;
- `core/canonical`: `topologicalKrullDim`, `homeoWithUpperSetTopologyorderIso`,
  `irreducibleSetEquivPoints`, and the Sierpiński topology on `Prop`;
- `bridge/view`: the finite-chain model `WithUpperSet (Fin (n + 1))` and its comparison
  homeomorphism with the two-point Sierpiński space.
-/

instance (n : ℕ) : Fintype (WithUpperSet (Fin (n + 1))) :=
  inferInstanceAs (Fintype (Fin (n + 1)))

instance (n : ℕ) : LinearOrder (WithUpperSet (Fin (n + 1))) :=
  inferInstanceAs (LinearOrder (Fin (n + 1)))

private noncomputable def finSuccOrderIsoIic (n : ℕ) : Fin (n + 1) ≃o Set.Iic n where
  toFun i := ⟨i.1, Nat.le_of_lt_succ i.2⟩
  invFun i := ⟨i.1, Nat.lt_succ_of_le i.2⟩
  left_inv i := by
    ext
    rfl
  right_inv i := by
    ext
    rfl
  map_rel_iff' := by
    simp

private lemma krullDim_fin_succ (n : ℕ) : Order.krullDim (Fin (n + 1)) = n := by
  rw [Order.krullDim_eq_of_orderIso (finSuccOrderIsoIic n)]
  simpa using (Order.height_eq_krullDim_Iic n).symm

private lemma finiteChain_closed_eq_Iic (n : ℕ)
    (s : IrreducibleCloseds (WithUpperSet (Fin (n + 1)))) :
    ∃ a : WithUpperSet (Fin (n + 1)), (s : Set (WithUpperSet (Fin (n + 1)))) = Set.Iic a := by
  classical
  obtain ⟨a, ha⟩ := (s : Set (WithUpperSet (Fin (n + 1)))).toFinite.exists_maximal
    s.isIrreducible.nonempty
  have ha_mem : a ∈ (s : Set (WithUpperSet (Fin (n + 1)))) := (maximal_iff_forall_gt.mp ha).1
  have ha_max :
      ∀ ⦃b : WithUpperSet (Fin (n + 1))⦄, a < b → b ∉ (s : Set (WithUpperSet (Fin (n + 1)))) :=
    (maximal_iff_forall_gt.mp ha).2
  have hsLower : IsLowerSet (s : Set (WithUpperSet (Fin (n + 1)))) :=
    isClosed_iff_isLower.1 s.isClosed
  refine ⟨a, Set.ext fun b ↦ ?_⟩
  constructor
  · intro hb
    have : ¬ a < b := by
      intro hab
      exact ha_max hab hb
    exact le_of_not_gt this
  · intro hb
    exact hsLower hb ha_mem

private instance finiteChainT0Space (n : ℕ) : T0Space (WithUpperSet (Fin (n + 1))) := by
  refine ⟨fun x y hxy ↦ ?_⟩
  apply Iic_injective
  simpa [inseparable_iff_closure_eq, IsUpperSet.closure_singleton] using hxy

private instance finiteChainQuasiSober (n : ℕ) : QuasiSober (WithUpperSet (Fin (n + 1))) where
  sober {S} hS hSclosed := by
    obtain ⟨a, ha : S = Set.Iic a⟩ := finiteChain_closed_eq_Iic n ⟨S, hS, hSclosed⟩
    refine ⟨a, isGenericPoint_def.2 ?_⟩
    rw [IsUpperSet.closure_singleton, ha.symm]

-- Proof sketch: the irreducible closed subsets of this Alexandrov chain are exactly the nonempty
-- initial segments, and the maximal strict chains of those initial segments have length `n`.
/-- The `(n + 1)`-point Alexandrov chain `WithUpperSet (Fin (n + 1))` has topological Krull
dimension `n`. -/
theorem topologicalKrullDim_withUpperSet_fin_succ (n : ℕ) :
    topologicalKrullDim (WithUpperSet (Fin (n + 1))) = n := by
  let e : IrreducibleCloseds (WithUpperSet (Fin (n + 1))) ≃o Fin (n + 1) :=
    (show IrreducibleCloseds (WithUpperSet (Fin (n + 1))) ≃o
        Specialization (WithUpperSet (Fin (n + 1))) from irreducibleSetEquivPoints).trans
      (orderIsoSpecializationWithUpperSetTopology (Fin (n + 1))).symm
  rw [topologicalKrullDim, Order.krullDim_eq_of_orderIso e]
  simpa using krullDim_fin_succ n

private def withUpperSetHomeomorphOfOrderIso {α β : Type*} [Preorder α] [Preorder β]
    (e : α ≃o β) : WithUpperSet α ≃ₜ WithUpperSet β where
  toEquiv := e.toEquiv
  continuous_toFun := continuous_def.2 fun _ hs ↦ IsUpperSet.preimage hs e.monotone
  continuous_invFun := continuous_def.2 fun _ hs ↦ IsUpperSet.preimage hs e.symm.monotone

private noncomputable def propOrderIsoFinTwo : Prop ≃o Fin 2 where
  toFun p := by
    classical
    exact if p then 1 else 0
  invFun i := i = 1
  left_inv p := by
    classical
    by_cases hp : p <;> simp [hp]
  right_inv i := by
    classical
    fin_cases i <;> simp
  map_rel_iff' := by
    intro p q
    classical
    by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

private noncomputable def propOrderIsoSpecialization : Prop ≃o Specialization Prop where
  toEquiv := Specialization.toEquiv
  map_rel_iff' := by
    intro p q
    simp [IsUpperSet.specializes_iff_le]

/-- The canonical Sierpiński space `Prop` is homeomorphic to the two-point Alexandrov chain
`WithUpperSet (Fin 2)`. Under this identification, `False` is the closed point and `True` is the
generic point. -/
noncomputable def sierpinskiHomeomorphTwoPointChain : Prop ≃ₜ WithUpperSet (Fin 2) :=
  (homeoWithUpperSetTopologyorderIso Prop).trans
    (withUpperSetHomeomorphOfOrderIso (propOrderIsoSpecialization.symm.trans propOrderIsoFinTwo))

/-- A subset of the canonical Sierpiński space is open exactly when it is `∅`, `{True}`, or
`univ`. -/
theorem isOpen_sierpinskiSpace_iff (s : Set Prop) :
    IsOpen s ↔ s = ∅ ∨ s = {True} ∨ s = univ := by
  rw [isOpen_iff_isUpperSet]
  constructor
  · intro hs
    by_cases hFalse : False ∈ s
    · right
      right
      ext p
      by_cases hp : p
      · have hTrue : True ∈ s := hs (by simp) hFalse
        simp [hp, hTrue]
      · simp [hp, hFalse]
    · by_cases hTrue : True ∈ s
      · right
        left
        ext p
        by_cases hp : p <;> simp [hp, hFalse, hTrue]
      · left
        ext p
        by_cases hp : p <;> simp [hp, hFalse, hTrue]
  · rintro (rfl | rfl | rfl)
    · exact isUpperSet_empty
    · simpa only [isOpen_iff_isUpperSet] using (isOpen_singleton_true : IsOpen ({True} : Set Prop))
    · exact isUpperSet_univ

-- Proof sketch: transport the chain computation for `WithUpperSet (Fin 2)` across the canonical
-- Sierpiński-space homeomorphism above.
/-- Example 5.10.4: the canonical Sierpiński space `Prop`, whose open sets are exactly `∅`,
`{True}`, and `univ`, has topological Krull dimension `1`. -/
theorem sierpinskiSpace_topologicalKrullDim : topologicalKrullDim Prop = 1 := by
  calc
    topologicalKrullDim Prop = topologicalKrullDim (WithUpperSet (Fin 2)) := by
      simpa using IsHomeomorph.topologicalKrullDim_eq
        (sierpinskiHomeomorphTwoPointChain : Prop → WithUpperSet (Fin 2))
        sierpinskiHomeomorphTwoPointChain.isHomeomorph
    _ = 1 := by
      simpa using topologicalKrullDim_withUpperSet_fin_succ 1

/-! ### Definition_5_10_5 (from Chap05) -/
universe u

variable {X : Type u} [TopologicalSpace X]

namespace TopologicalSpace

/-
Domain-style sampling for equidimensionality on topological spaces:
- earlier chapter owner: `topologicalKrullDim`, recalled in `Definition_5_10_1`
- mathlib owner for irreducible components: `irreducibleComponents`
- component closedness bridge: `isClosed_of_mem_irreducibleComponents`
- singleton-component bridge for irreducible spaces: `irreducibleComponents_eq_singleton`
- no earlier project/mathlib owner for equidimensionality itself, so this file should own the
  source-facing predicate and build it from the canonical component owner

Layer triage:
- `source-facing`: `EquidimensionalSpace`
- `core/canonical`: the canonical owner type `irreducibleComponents X`
- `bridge/view`: coercing a component `Z : irreducibleComponents X` to the subset `(Z : Set X)`

Primitive data belongs only to `EquidimensionalSpace.topologicalKrullDim_eq`; set-membership
restatements are derived API and do not need to remain as parallel public owners.
-/

/-- Definition 5.10.5: a topological space is equidimensional if every irreducible component of
the space has the same topological Krull dimension. -/
class EquidimensionalSpace (X : Type u) [TopologicalSpace X] : Prop where
  topologicalKrullDim_eq (Z₁ Z₂ : irreducibleComponents X) :
    topologicalKrullDim Z₁ = topologicalKrullDim Z₂

variable [EquidimensionalSpace X]

/-- Textbook-form bridge: in an equidimensional space, any two irreducible components viewed as
subsets have the same topological Krull dimension. -/
theorem topologicalKrullDim_eq_of_mem_irreducibleComponents {Z₁ Z₂ : Set X}
    (hZ₁ : Z₁ ∈ irreducibleComponents X) (hZ₂ : Z₂ ∈ irreducibleComponents X) :
    topologicalKrullDim Z₁ = topologicalKrullDim Z₂ :=
  EquidimensionalSpace.topologicalKrullDim_eq ⟨Z₁, hZ₁⟩ ⟨Z₂, hZ₂⟩

/-- An irreducible topological space is equidimensional. -/
instance [IrreducibleSpace X] : EquidimensionalSpace X where
  topologicalKrullDim_eq Z₁ Z₂ := by
    letI : Subsingleton (irreducibleComponents X) := by
      rw [irreducibleComponents_eq_singleton]
      infer_instance
    simpa using
      congrArg (fun Z : irreducibleComponents X ↦ topologicalKrullDim Z)
        (Subsingleton.elim Z₁ Z₂)

end TopologicalSpace
