import Integer.Chapters.Chap07.section_7_3.ch7_sec7_3_theorem_7_9

open scoped BigOperators

-- Domain sampling for this theorem:
-- * primary domain: single-node flow covers and their lifted facet-defining inequalities
-- * core/canonical owner reused here: `single_node_flow_set`, `IsFlowCover`, `flow_cover_excess`,
--   and especially the zero-lifted cover owner `flow_cover_value`
-- * source-facing data kept here: an ordering of the cover `C`, its derived ordered coefficients
--   and partial sums, the cut index `r`, and the admissible lifting pairs from Theorem 7.16

section Theorem716

variable {n : ℕ}

/-
Source-facing ordered-cover data for Theorem 7.16.
-/
namespace OrderedFlowCover

/-- `enumerates C coverOrder` means that the finite ordering
`coverOrder : Fin C.card ↪ Fin n` enumerates the elements of the cover `C`. -/
def enumerates
    (C : Finset (Fin n)) (coverOrder : Fin C.card ↪ Fin n) : Prop :=
  Set.range coverOrder = (↑C : Set (Fin n))

/-- The ordered cover coefficient `a_{j_h}` attached to the `h`-th element of `coverOrder`,
written with the source indexing convention `h = 1, 2, ...`. -/
def weight
    (C : Finset (Fin n)) (a : Fin n → ℝ) (coverOrder : Fin C.card ↪ Fin n) : ℕ → ℝ
  | 0 => 0
  | h + 1 =>
      if hh : h < C.card then a (coverOrder ⟨h, hh⟩) else 0

/-- The source coefficient at position `h + 1` is `a` evaluated on the `h`-th entry of
`coverOrder` whenever that position lies in the ordered cover. -/
theorem weight_succ
    (C : Finset (Fin n)) (a : Fin n → ℝ) (coverOrder : Fin C.card ↪ Fin n)
    {h : ℕ} (hh : h < C.card) :
    weight C a coverOrder (h + 1) = a (coverOrder ⟨h, hh⟩) := by
  simp [weight, hh]

/-- The partial sums `μ_h = a_{j_1} + ⋯ + a_{j_h}` of the ordered cover coefficients. -/
def partialSum
    (C : Finset (Fin n)) (a : Fin n → ℝ) (coverOrder : Fin C.card ↪ Fin n) : ℕ → ℝ
  | 0 => 0
  | h + 1 =>
      partialSum C a coverOrder h +
        weight C a coverOrder (h + 1)

/-- The source partial sums satisfy `μ_{h+1} = μ_h + a_{j_{h+1}}`. -/
theorem partialSum_succ
    (C : Finset (Fin n)) (a : Fin n → ℝ) (coverOrder : Fin C.card ↪ Fin n) (h : ℕ) :
    partialSum C a coverOrder (h + 1) =
      partialSum C a coverOrder h +
        weight C a coverOrder (h + 1) := by
  rfl

/-- `isCutIndex a C coverOrder λ r` means that `r` is the last ordered cover
position among the first `C.card` cover coefficients whose coefficient still exceeds `λ`. -/
def isCutIndex
    (a : Fin n → ℝ) (C : Finset (Fin n)) (coverOrder : Fin C.card ↪ Fin n)
    (lam : ℝ) (r : ℕ) : Prop :=
  1 ≤ r ∧
    r ≤ C.card ∧
      lam < weight C a coverOrder r ∧
        ∀ h, r < h → h ≤ C.card → weight C a coverOrder h ≤ lam

/-- `admissiblePair a b C coverOrder r i αᵢ βᵢ` records the four source coefficient patterns from
Theorem 7.16 for a noncover index `i`, using the ordered cover coefficients `a_{j_h}` and their
partial sums `μ_h` derived from `coverOrder`. -/
def admissiblePair
    (a : Fin n → ℝ) (b : ℝ) (C : Finset (Fin n))
    (coverOrder : Fin C.card ↪ Fin n) (r : ℕ)
    (i : Fin n) (αᵢ βᵢ : ℝ) : Prop :=
  let lam := flow_cover_excess a b C
  let coverWeight := weight C a coverOrder
  let μ := partialSum C a coverOrder
  (αᵢ = 0 ∧ βᵢ = 0) ∨
    (∃ h : ℕ,
      2 ≤ h ∧
        h ≤ r ∧
          μ h - lam ≤ a i ∧
            αᵢ = lam / coverWeight h ∧
              βᵢ =
                lam * (((h - 1 : ℕ) : ℝ) - (μ h - lam) / coverWeight h)) ∨
      (∃ ℓ : ℕ,
        a i > μ ℓ - lam ∧
          (ℓ = r ∨ (ℓ < r ∧ a i ≤ μ ℓ)) ∧
            αᵢ = 1 ∧
              βᵢ = (ℓ : ℝ) * lam - μ ℓ) ∨
        ∃ ℓ : ℕ,
          ℓ < r ∧
            μ ℓ < a i ∧
              a i ≤ μ (ℓ + 1) - lam ∧
                αᵢ = lam / (a i + lam - μ ℓ) ∧
                  βᵢ =
                    (ℓ : ℝ) * lam - (lam * a i) / (a i + lam - μ ℓ)

/-- The left-hand side of the lifted flow-cover inequality `(7.16)`, written as the canonical
zero-lifted flow-cover owner `flow_cover_value a b C` on `C` together with the lifting
coefficients `(α_i, β_i)` on `N \ C`. -/
def flow_cover_lifted_value
    (a : Fin n → ℝ) (b : ℝ) (C : Finset (Fin n)) (α β : Fin n → ℝ)
    (p : (Fin n → ℝ) × (Fin n → ℝ)) : ℝ :=
  flow_cover_value a b C p +
    Finset.sum (Finset.univ \ C) (fun i ↦ α i * p.2 i + β i * p.1 i)

/-- `flow_cover_lifted_value a b C α β p` expands to the zero-lifted cover value on `C` plus the
lifting contribution on `Finset.univ \ C`. -/
theorem flow_cover_lifted_value_eq
    (a : Fin n → ℝ) (b : ℝ) (C : Finset (Fin n)) (α β : Fin n → ℝ)
    (p : (Fin n → ℝ) × (Fin n → ℝ)) :
    flow_cover_lifted_value a b C α β p =
      flow_cover_value a b C p +
        Finset.sum (Finset.univ \ C) (fun i ↦ α i * p.2 i + β i * p.1 i) :=
  rfl

/-- With zero lifting coefficients on `N \ C`, the lifted owner reduces to the canonical
zero-lifted flow-cover owner from Theorem 7.9. -/
theorem flow_cover_lifted_value_zero
    (a : Fin n → ℝ) (b : ℝ) (C : Finset (Fin n))
    (p : (Fin n → ℝ) × (Fin n → ℝ)) :
    flow_cover_lifted_value a b C (fun _ ↦ 0) (fun _ ↦ 0) p = flow_cover_value a b C p := by
  simp [flow_cover_lifted_value]

/-- The equality face cut out on `conv(T)` by a lifted flow-cover inequality over the single-node
flow set `T = single_node_flow_set a b` with right-hand side `δ`. -/
def flow_cover_lifted_face
    (a : Fin n → ℝ) (b : ℝ) (C : Finset (Fin n)) (α β : Fin n → ℝ) (δ : ℝ) :
    Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
  {p |
    p ∈ convexHull ℝ (single_node_flow_set a b) ∧
      flow_cover_lifted_value a b C α β p = δ}

/-- Membership in `flow_cover_lifted_face a b C α β δ` means lying in `conv(T)` and meeting the
lifted flow-cover inequality at equality. -/
theorem mem_flow_cover_lifted_face_iff
    (a : Fin n → ℝ) (b : ℝ) (C : Finset (Fin n)) (α β : Fin n → ℝ) (δ : ℝ)
    (p : (Fin n → ℝ) × (Fin n → ℝ)) :
    p ∈ flow_cover_lifted_face a b C α β δ ↔
      p ∈ convexHull ℝ (single_node_flow_set a b) ∧
        flow_cover_lifted_value a b C α β p = δ :=
  Iff.rfl

/-- The lifted flow-cover inequality `(7.16)` is facet-defining for the single-node flow set
`T = single_node_flow_set a b` when it is valid on `conv(T)` with right-hand side `δ` and the
equality face it cuts out is a facet of `conv(T)`. -/
def flow_cover_lifted_inequality_facet_defining
    (a : Fin n → ℝ) (b : ℝ) (C : Finset (Fin n)) (α β : Fin n → ℝ) (δ : ℝ) : Prop :=
  (∀ ⦃p : (Fin n → ℝ) × (Fin n → ℝ)⦄,
      p ∈ convexHull ℝ (single_node_flow_set a b) →
        flow_cover_lifted_value a b C α β p ≤ δ) ∧
    IsFacetOf
      (convexHull ℝ (single_node_flow_set a b))
      (flow_cover_lifted_face a b C α β δ)

/-- `flow_cover_lifted_inequality_facet_defining a b C α β δ` unfolds to validity on `conv(T)`
together with facetness of the corresponding equality face. -/
theorem flow_cover_lifted_inequality_facet_defining_iff
    (a : Fin n → ℝ) (b : ℝ) (C : Finset (Fin n)) (α β : Fin n → ℝ) (δ : ℝ) :
    flow_cover_lifted_inequality_facet_defining a b C α β δ ↔
      (∀ ⦃p : (Fin n → ℝ) × (Fin n → ℝ)⦄,
          p ∈ convexHull ℝ (single_node_flow_set a b) →
            flow_cover_lifted_value a b C α β p ≤ δ) ∧
        IsFacetOf
          (convexHull ℝ (single_node_flow_set a b))
          (flow_cover_lifted_face a b C α β δ) :=
  Iff.rfl

end OrderedFlowCover

open OrderedFlowCover

/-- Theorem 7.16 (Gu et al. [191]). Let `T = single_node_flow_set a b` with nonnegative
capacities `a`, let `C` be a flow cover for `T`, let `λ = flow_cover_excess a b C`, let
`coverOrder` enumerate the elements of `C` in nonincreasing order of their coefficients
`a_{j_h}`, and let `r` be the last ordered cover position with `a_{j_r} > λ`. Then the lifted
flow-cover inequality `(7.16)` is facet-defining for `T` if and only if, for each `i ∉ C`, the
pair `(α_i, β_i)` is one of the four source families listed in Theorem 7.16. -/
theorem flow_cover_inequality_facet_defining_iff_all_outside_pairs_admissible
    (a α β : Fin n → ℝ)
    (b : ℝ)
    (C : Finset (Fin n))
    (coverOrder : Fin C.card ↪ Fin n)
    (r : ℕ)
    (ha_nonneg : ∀ j, 0 ≤ a j)
    (hC : IsFlowCover a b C)
    (hcoverOrder : enumerates C coverOrder)
    (hordered : Antitone fun h : Fin C.card ↦ a (coverOrder h))
    (hr : isCutIndex a C coverOrder (flow_cover_excess a b C) r) :
    flow_cover_lifted_inequality_facet_defining a b C α β b ↔
      ∀ i, i ∉ C → admissiblePair a b C coverOrder r i (α i) (β i) := sorry

end Theorem716
