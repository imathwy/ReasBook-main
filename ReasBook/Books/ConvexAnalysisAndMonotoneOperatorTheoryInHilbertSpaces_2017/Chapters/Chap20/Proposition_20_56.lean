import BauschkeLean.Chap01.Text_1_0_11
import BauschkeLean.Chap09.Proposition_9_18
import BauschkeLean.Chap09.Definition_9_12
import BauschkeLean.Chap11.Definition_11_3
import BauschkeLean.Chap12.ProximityOperator
import BauschkeLean.Chap12.Proposition_12_26
import BauschkeLean.Chap13.Definition_13_34
import BauschkeLean.Chap13.Definition_13_1
import BauschkeLean.Chap13.Proposition_13_23
import BauschkeLean.Chap20.Definition_20_1
import BauschkeLean.Chap20.Definition_20_51
import BauschkeLean.Chap20.PairingEqualityOperator
import BauschkeLean.Chap16.Proposition_16_10

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace Pointwise SetValuedOperator
open ERealFunction

universe u

namespace SetValuedOperator

noncomputable section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/- Source/core/bridge triage:
- `source-facing`: Proposition 20.56 records the standard Fitzpatrick identities for a monotone
  operator.
- `core/canonical`: the owner abstractions are the Fitzpatrick function `F[_]`, Fenchel
  conjugation `∗`, transpose `ᵀ`, the Chapter 9 bridge `properIoi`, the Chapter 9 class `Γ₀`,
  and the Chapter 12 proximity operator notation `Prox[_, _]`.
- `bridge/view`: the `Γ₀` and proximity statements are bridges from the raw `EReal`-valued owner
  `F[A]` to the canonical packaged convex-analysis API.

Primitive data: the operator `A` and its Fitzpatrick owner `F[A]`.
Derived API: properness, `Γ₀` membership, transpose/conjugate comparisons, and proximal contact
identities. -/

attribute [-instance] Prod.toNorm Prod.seminormedAddCommGroup Prod.normedAddCommGroup
attribute [-instance] Prod.normedSpace Prod.pseudoMetricSpaceMax

attribute [local instance] ERealFunction.prod_pseudoMetricSpace_l2
attribute [local instance] ERealFunction.prod_normedAddCommGroup_l2
attribute [local instance] ERealFunction.prod_normedSpace_l2
attribute [local instance] ERealFunction.prod_innerProductSpace_l2

section

variable (A : SetValuedOperator H H)

/-- Helper for Proposition 20.56: if an `EReal`-valued family is `⊥` outside a set, then its
unrestricted supremum agrees with the supremum over the corresponding subtype. -/
private theorem iSup_eq_iSup_subtype_of_eq_bot_outside
    {α : Type*} {S : Set α} (φ : α → EReal) (hbot : ∀ x, x ∉ S → φ x = ⊥) :
    (⨆ x : α, φ x) = ⨆ x : S, φ x := by
  classical
  -- Compare the unrestricted supremum with the restricted one pointwise.
  refine le_antisymm ?_ ?_
  · refine iSup_le fun x ↦ ?_
    by_cases hx : x ∈ S
    · simpa using le_iSup (fun y : S ↦ φ y) ⟨x, hx⟩
    · rw [hbot x hx]
      exact bot_le
  · refine iSup_le fun x ↦ ?_
    simpa using le_iSup φ (x : α)

/-- A graph-nonempty Fitzpatrick function never attains `-∞`. -/
-- Proof sketch: choose a graph point `(y, v) ∈ gra A`; the corresponding Fitzpatrick supremand at
-- `(x, u)` is a finite real number, so the supremum defining `F_A(x, u)` is strictly above `⊥`.
theorem fitzpatrickFunction_ne_bot_of_graph_nonempty
    (hA_graph : (gra A).Nonempty) (p : H × H) :
    ⊥ < F[A] p := by
  rcases hA_graph with ⟨y, hy⟩
  let q : gra A := ⟨y, hy⟩
  -- Test the defining supremum at one concrete graph point to get a finite lower bound.
  have hq_le :
      (((⟪q.1.1, p.2⟫_ℝ + ⟪p.1, q.1.2⟫_ℝ - ⟪q.1.1, q.1.2⟫_ℝ : ℝ) : EReal)) ≤ F[A] p := by
    exact le_iSup (fun r : gra A ↦
      (((⟪r.1.1, p.2⟫_ℝ + ⟪p.1, r.1.2⟫_ℝ - ⟪r.1.1, r.1.2⟫_ℝ : ℝ) : EReal))) q
  have hq_bot :
      (⊥ : EReal) <
        (((⟪q.1.1, p.2⟫_ℝ + ⟪p.1, q.1.2⟫_ℝ - ⟪q.1.1, q.1.2⟫_ℝ : ℝ) : EReal)) := by
    exact EReal.bot_lt_coe _
  exact lt_of_lt_of_le hq_bot hq_le

/-- Helper for Proposition 20.56: the Fitzpatrick function is the Fenchel conjugate of the
inverse-graph indicator plus the pairing. This source-faithful identity is needed before the
statement-facing clause is packaged later in the file. -/
private theorem fitzpatrickFunction_eq_conjugate_inverseGraphIndicator_add_pairing_aux :
    F[A] = ((ι[gra A⁻¹]).asEReal + pairing)∗ := by
  let G : H × H → EReal := fun p ↦ (ι[gra A⁻¹] p : EReal) + pairing p
  let e : gra A⁻¹ ≃ gra A :=
    { toFun := fun p ↦ ⟨(p.1.2, p.1.1), by
        exact p.2⟩
      invFun := fun p ↦ ⟨(p.1.2, p.1.1), by
        exact p.2⟩
      left_inv := by
        intro p
        ext <;> rfl
      right_inv := by
        intro p
        ext <;> rfl }
  ext ⟨x, u⟩
  rw [fitzpatrickFunction]
  symm
  calc
    G∗ (x, u)
        = ⨆ p : gra A⁻¹,
            (((⟪x, p.1.1⟫_ℝ + ⟪u, p.1.2⟫_ℝ : ℝ) : EReal) - G p) := by
                rw [conjugate_apply_pair]
                exact iSup_eq_iSup_subtype_of_eq_bot_outside
                  (φ := fun p : H × H ↦
                    (((⟪x, p.1⟫_ℝ + ⟪u, p.2⟫_ℝ : ℝ) : EReal) - G p))
                  (hbot := fun p hp ↦ by
                    have hpair_ne_bot : pairing p ≠ ⊥ := by
                      change (((⟪p.1, p.2⟫_ℝ : ℝ) : EReal)) ≠ ⊥
                      exact EReal.coe_ne_bot _
                    simp [G, indicator_apply, hp, hpair_ne_bot])
    _ = ⨆ p : gra A⁻¹,
          ((⟪x, p.1.1⟫_ℝ + ⟪u, p.1.2⟫_ℝ - ⟪p.1.1, p.1.2⟫_ℝ : ℝ) : EReal) := by
            refine iSup_congr fun p ↦ ?_
            suffices
                (((⟪x, p.1.1⟫_ℝ + ⟪u, p.1.2⟫_ℝ : ℝ) : EReal) -
                  pairing (p.1.1, p.1.2)) =
                ((⟪x, p.1.1⟫_ℝ + ⟪u, p.1.2⟫_ℝ - ⟪p.1.1, p.1.2⟫_ℝ : ℝ) : EReal) by
              simpa [G, indicator_apply, p.2] using this
            rw [pairing_apply]
            simp
    _ = ⨆ p : gra A,
          ((⟪p.1.1, u⟫_ℝ + ⟪x, p.1.2⟫_ℝ - ⟪p.1.1, p.1.2⟫_ℝ : ℝ) : EReal) := by
            exact e.iSup_congr fun p ↦ by
              simp [e, real_inner_comm, add_comm]
    _ = F[A] (x, u) := by
          rfl

section

-- Proof sketch: if `(x, u) ∈ gra A`, then the infimum formula from Definition 20.51 reduces to
-- `⟪x, u⟫ - 0` because monotonicity gives the infimum term `0` and the graph point `(x, u)` shows
-- that this lower bound is attained.
/-- Proposition 20.56 (1): clause (i). On the graph of a monotone operator, the Fitzpatrick
function agrees with the pairing. -/
theorem fitzpatrickFunction_eq_inner_of_mem_graph
    (hA_mono : A.IsMonotone) {x u : H} (hxu : (x, u) ∈ gra A) :
    F[A] (x, u) = pairing (x, u) := by
  let gap : gra A → EReal :=
    fun p ↦ ((⟪x - p.1.1, u - p.1.2⟫_ℝ : ℝ) : EReal)
  let p0 : gra A := ⟨(x, u), hxu⟩
  have hmono_graph := (SetRel.isMonotone_iff (gra A)).1 hA_mono
  have hgap_nonneg : ∀ p : gra A, (0 : EReal) ≤ gap p := by
    intro p
    change (0 : EReal) ≤ ((⟪x - p.1.1, u - p.1.2⟫_ℝ : ℝ) : EReal)
    exact_mod_cast hmono_graph hxu p.2
  have hgap_inf : (⨅ p : gra A, gap p) = 0 := by
    -- Monotonicity gives a lower bound `0`, and the chosen graph point attains that bound.
    refine le_antisymm ?_ ?_
    · simpa [gap, p0] using iInf_le gap p0
    · refine le_iInf hgap_nonneg
  -- Insert the computed infimum back into the normal form from Definition 20.51.
  rw [fitzpatrickFunction_apply_eq_inner_sub_iInf, hgap_inf, pairing_apply]
  simp

-- Proof sketch: rewrite `F_A(x, u)` by the infimum formula. The inequality `F_A(x, u) ≤ ⟪x, u⟫`
-- is equivalent to nonnegativity of `⟪x - y, u - v⟫` for every `(y, v) ∈ gra A`, which is
-- exactly monotonicity of `gra A ∪ {(x, u)}`.
/-- Proposition 20.56 (4): clause (iii). The Fitzpatrick value at `(x, u)` lies below the pairing
if and only if adjoining `(x, u)` to `gra A` preserves monotonicity. -/
theorem fitzpatrickFunction_le_inner_iff_insert_graph_isMonotone
    (hA_mono : A.IsMonotone) (x u : H) :
    F[A] (x, u) ≤ pairing (x, u) ↔
      SetRel.IsMonotone (Set.insert (x, u) (gra A)) := by
  let gap : gra A → EReal :=
    fun p ↦ ((⟪x - p.1.1, u - p.1.2⟫_ℝ : ℝ) : EReal)
  let α : EReal := ⨅ p : gra A, gap p
  have hmono_graph := (SetRel.isMonotone_iff (gra A)).1 hA_mono
  have hle_iff : F[A] (x, u) ≤ pairing (x, u) ↔ (0 : EReal) ≤ α := by
    -- Cancel the common finite pairing term to isolate the gap infimum.
    rw [fitzpatrickFunction_apply_eq_inner_sub_iInf, pairing_apply]
    change (((⟪x, u⟫_ℝ : ℝ) : EReal) - α ≤ ((⟪x, u⟫_ℝ : ℝ) : EReal)) ↔ (0 : EReal) ≤ α
    constructor
    · intro hle
      have hshift :
          (-α) + ((⟪x, u⟫_ℝ : ℝ) : EReal) ≤
            (0 : EReal) + ((⟪x, u⟫_ℝ : ℝ) : EReal) := by
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hle
      have hneg : -α ≤ (0 : EReal) := by
        simpa using (EReal.addLECancellable_coe ⟪x, u⟫_ℝ).add_le_add_iff_right.mp hshift
      simpa using hneg
    · intro hα
      have hneg : -α ≤ (0 : EReal) := by
        simpa using hα
      have hshift :
          (-α) + ((⟪x, u⟫_ℝ : ℝ) : EReal) ≤
            (0 : EReal) + ((⟪x, u⟫_ℝ : ℝ) : EReal) := by
        simpa [add_comm, add_left_comm, add_assoc] using
          add_le_add_right hneg (((⟪x, u⟫_ℝ : ℝ) : EReal))
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hshift
  have hinsert_iff :
      SetRel.IsMonotone (Set.insert (x, u) (gra A)) ↔
        ∀ p : gra A, 0 ≤ ⟪x - p.1.1, u - p.1.2⟫_ℝ := by
    -- The only new monotonicity tests are between `(x, u)` and the original graph points.
    rw [SetRel.isMonotone_iff]
    constructor
    · intro hinsert p
      have hxu_insert : (x, u) ∈ Set.insert (x, u) (gra A) := Set.mem_insert _ _
      have hp_insert : ((p : H × H)) ∈ Set.insert (x, u) (gra A) := by
        exact Set.mem_insert_iff.mpr (Or.inr p.2)
      exact hinsert hxu_insert hp_insert
    · intro hgap a b y v ha hb
      rcases Set.mem_insert_iff.mp ha with hxy | ha_graph
      · cases hxy
        rcases Set.mem_insert_iff.mp hb with huv | hb_graph
        · cases huv
          simp
        · simpa using hgap ⟨(y, v), hb_graph⟩
      · rcases Set.mem_insert_iff.mp hb with huv | hb_graph
        · cases huv
          have hxy : 0 ≤ ⟪x - a, u - b⟫_ℝ := hgap ⟨(a, b), ha_graph⟩
          have hsym : ⟪a - x, b - u⟫_ℝ = ⟪x - a, u - b⟫_ℝ := by
            simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
              (inner_neg_neg (x - a) (u - b))
          simpa [hsym] using hxy
        · exact hmono_graph ha_graph hb_graph
  constructor
  · intro hle
    have hα : (0 : EReal) ≤ α := hle_iff.mp hle
    refine hinsert_iff.mpr ?_
    intro p
    have hgapE : (0 : EReal) ≤ gap p := le_trans hα (iInf_le gap p)
    have hgapE' : (0 : EReal) ≤ (((⟪x - p.1.1, u - p.1.2⟫_ℝ : ℝ) : EReal)) := by
      simpa [gap] using hgapE
    have hgapR : (0 : ℝ) ≤ ⟪x - p.1.1, u - p.1.2⟫_ℝ := by
      exact_mod_cast hgapE'
    exact hgapR
  · intro hinsert
    have hα : (0 : EReal) ≤ α := by
      refine le_iInf ?_
      intro p
      have hgapR : 0 ≤ ⟪x - p.1.1, u - p.1.2⟫_ℝ := (hinsert_iff.mp hinsert p)
      have hgapE : (0 : EReal) ≤ gap p := by
        change (0 : EReal) ≤ (((⟪x - p.1.1, u - p.1.2⟫_ℝ : ℝ) : EReal))
        exact_mod_cast hgapR
      exact hgapE
    exact hle_iff.mpr hα

-- Proof sketch: replace every graph value `F_A(y, v)` in the defining supremum by the pairing
-- `⟪y, v⟫` using clause (1), then compare that supremum with the unrestricted supremum defining
-- the transpose-conjugate owner `((F[A])∗)ᵀ`.
/-- Proposition 20.56 (5): clause (iv). The Fitzpatrick function is dominated by its
transpose-conjugate owner `((F_A)^*)^T`. -/
theorem fitzpatrickFunction_le_conjugate_transpose :
    A.IsMonotone → F[A] ≤ ((F[A])∗)ᵀ := by
  intro hA_mono
  rintro ⟨x, u⟩
  -- Compare the graph-restricted Fitzpatrick supremum with the full conjugate supremum.
  rw [fitzpatrickFunction, transpose_apply, conjugate_apply_pair]
  refine iSup_le fun p ↦ ?_
  have hp_eq :
      F[A] (p.1.1, p.1.2) = pairing (p.1.1, p.1.2) :=
    fitzpatrickFunction_eq_inner_of_mem_graph A hA_mono p.2
  exact le_iSup_of_le p.1 <| by
    rw [hp_eq, pairing_apply]
    simp [real_inner_comm]

-- Proof sketch: clause (3) places `F_A` in `Γ₀(H × H)`, so biconjugation bounds its conjugate by
-- the graph-indicator-plus-pairing function; evaluating the transpose-conjugate owner at a graph
-- point and combining clauses (1) and (5) forces equality.
/-- Proposition 20.56 (6): clause (v). At every graph point `(x, u)`, the transpose-conjugate
value `((F_A)^*)^T (x, u)` equals the pairing `⟪x, u⟫`. -/
theorem conjugateTranspose_fitzpatrickFunction_eq_inner_of_mem_graph
    (hA_mono : A.IsMonotone) {x u : H} (hxu : (x, u) ∈ gra A) :
    ((F[A])∗)ᵀ (x, u) = pairing (x, u) := by
  let G : H × H → EReal := (ι[gra A⁻¹]).asEReal + pairing
  have hgraph_eq :
      F[A] (x, u) = pairing (x, u) :=
    fitzpatrickFunction_eq_inner_of_mem_graph A hA_mono hxu
  have hupper :
      ((F[A])∗)ᵀ (x, u) ≤ pairing (x, u) := by
    have hxu_inv : (u, x) ∈ gra A⁻¹ := by
      simpa [SetValuedOperator.mem_inverse_iff] using hxu
    -- Reinterpret the transpose-conjugate owner as the biconjugate of the inverse-graph
    -- indicator plus the pairing, then apply the Fenchel biconjugate upper bound.
    rw [transpose_apply]
    calc
      F[A]∗ (u, x) = G∗∗ (u, x) := by
        rw [show F[A] = G∗ by
          change F[A] = ((ι[gra A⁻¹]).asEReal + pairing)∗
          exact fitzpatrickFunction_eq_conjugate_inverseGraphIndicator_add_pairing_aux A]
      _ ≤ G (u, x) := biconjugate_le _ (u, x)
      _ = pairing (u, x) := by
        simp [G, indicator_apply, hxu_inv]
      _ = pairing (x, u) := by
        simp [pairing_apply, real_inner_comm]
  -- Clause (iv) gives the reverse inequality after replacing `F[A](x, u)` by the pairing.
  refine le_antisymm hupper ?_
  calc
    pairing (x, u) = F[A] (x, u) := hgraph_eq.symm
    _ ≤ ((F[A])∗)ᵀ (x, u) := fitzpatrickFunction_le_conjugate_transpose A hA_mono (x, u)

end

-- Proof sketch: `fitzpatrickFunction_ne_bot_of_graph_nonempty` excludes the value `⊥`
-- everywhere, while clause (1) gives a graph point where `F_A` equals the finite pairing
-- `⟪x, u⟫`.
/-- If `gra A` is nonempty and `A` is monotone, then the Fitzpatrick function is proper. -/
theorem fitzpatrickFunction_isProper_of_graph_nonempty_of_monotone
    (hA_graph : (gra A).Nonempty) (hA_mono : A.IsMonotone) :
    IsProper F[A] := by
  refine ⟨?_, ?_⟩
  · intro p
    exact ne_of_gt (fitzpatrickFunction_ne_bot_of_graph_nonempty A hA_graph p)
  · rcases hA_graph with ⟨p, hp⟩
    refine ⟨p, ?_⟩
    rcases p with ⟨x, u⟩
    rw [ERealFunction.mem_dom_iff]
    have hgraph_eq :
        F[A] (x, u) = pairing (x, u) :=
      fitzpatrickFunction_eq_inner_of_mem_graph A hA_mono hp
    simp [hgraph_eq, pairing_apply]

-- Proof sketch: unfold the definitions of `gra A⁻¹`, the graph indicator, and Fenchel
-- conjugation on `H × H`; the resulting supremum is exactly the defining supremum of `F_A`.
/-- Proposition 20.56 (2): clause (ii). The Fitzpatrick function is the Fenchel conjugate of the
sum of the indicator of `gra A⁻¹` and the pairing function `(x, u) ↦ ⟪x, u⟫`. -/
theorem fitzpatrickFunction_eq_conjugate_inverseGraphIndicator_add_pairing :
    F[A] = ((ι[gra A⁻¹]).asEReal + pairing)∗ := by
  exact fitzpatrickFunction_eq_conjugate_inverseGraphIndicator_add_pairing_aux A

section

variable (hA_graph : (gra A).Nonempty) (hA_mono : A.IsMonotone)

local notation "FA" =>
  properIoi (F[A])
    (fitzpatrickFunction_isProper_of_graph_nonempty_of_monotone A hA_graph hA_mono)

-- Proof sketch: the previous conjugate formula identifies `F_A` as a Fenchel conjugate, so
-- conjugation theory gives convexity and lower semicontinuity; the properness theorem above
-- packages the same owner through the canonical Chapter 9 bridge `properIoi`.
/-- Proposition 20.56 (3): clause (ii). If `gra A` is nonempty and `A` is monotone, then the
Fitzpatrick function belongs to `Γ₀(H × H)`. -/
theorem fitzpatrickFunction_mem_gammaZero
    : FA ∈ Γ₀(H × H) := by
  let G : H × H → EReal := (ι[gra A⁻¹]).asEReal + pairing
  have hproper : IsProper F[A] :=
    fitzpatrickFunction_isProper_of_graph_nonempty_of_monotone A hA_graph hA_mono
  have hgamma : F[A] ∈ gamma (H × H) := by
    rw [show F[A] = G∗ by
      change F[A] = ((ι[gra A⁻¹]).asEReal + pairing)∗
      exact fitzpatrickFunction_eq_conjugate_inverseGraphIndicator_add_pairing_aux A]
    exact conjugate_mem_gamma G
  -- Package the raw `EReal` Fitzpatrick owner through the canonical Chapter 9 bridge.
  exact properIoi_mem_gammaZero_of_mem_gamma hproper hgamma

section Proximity

variable [CompleteSpace H]

attribute [local instance] ERealFunction.prod_completeSpace_l2

local notation "hFA" => fitzpatrickFunction_mem_gammaZero A hA_graph hA_mono

-- Proof sketch: clauses (1) and (6) give equality in Fenchel--Young at `((x, u), (u, x))` for
-- the canonical `Γ₀(H × H)` representative `properIoi (F[A]) ...` built from the ambient
-- graph-nonemptiness witness `hA_graph`, so `(u, x)` lies in its subdifferential at `(x, u)`.
-- Unfolding the proximal-point condition for the unit Moreau parameter then gives
-- `(x, u) = Prox_{F_A}(x + u, x + u)`.
/-- Proposition 20.56 (9): clause (viii). Every graph point of a monotone operator is a fixed
contact point of the proximity operator of its Fitzpatrick function. -/
theorem eq_prox_fitzpatrickFunction_of_mem_graph
    {x u : H} (hxu : (x, u) ∈ gra A) :
    (x, u) = Prox[FA, hFA] (x + u, x + u) := by
  have hsub : (u, x) ∈ (∂ FA) (x, u) := by
    -- Clauses (i) and (v) give equality in Fenchel--Young at `((x, u), (u, x))`.
    rw [mem_subdifferential_iff_fenchel_young_eq (f := FA) hFA.2.nonempty (x, u) (u, x)]
    have hpair_prod :
        (((⟪(x, u), (u, x)⟫_ℝ : ℝ) : EReal)) = pairing (x, u) + pairing (x, u) := by
      change (((⟪x, u⟫_ℝ + ⟪u, x⟫_ℝ : ℝ) : EReal)) =
        pairing (x, u) + pairing (x, u)
      simp [pairing_apply, real_inner_comm, EReal.coe_add]
    change F[A] (x, u) + F[A]∗ (u, x) = (((⟪(x, u), (u, x)⟫_ℝ : ℝ) : EReal))
    calc
      F[A] (x, u) + F[A]∗ (u, x) = pairing (x, u) + pairing (x, u) := by
        rw [fitzpatrickFunction_eq_inner_of_mem_graph A hA_mono hxu]
        simpa [transpose_apply] using
          congrArg (fun z : EReal => pairing (x, u) + z)
            (conjugateTranspose_fitzpatrickFunction_eq_inner_of_mem_graph A hA_mono hxu)
      _ = (((⟪(x, u), (u, x)⟫_ℝ : ℝ) : EReal)) := hpair_prod.symm
  -- Reinterpret the subgradient condition as the proximal-point variational inequality.
  apply eq_proximityOperator_of_isProxPoint FA (hasUniqueProxPoint_of_mem_gammaZero FA hFA)
  rw [isProxPoint_iff_forall_inner_add_le FA hFA.2 (x + u, x + u) (x, u)]
  rw [mem_subdifferential_iff] at hsub
  intro y
  have hres : (x + u, x + u) - (x, u) = (u, x) := by
    simp
  rw [hres]
  exact hsub y

end Proximity

end

-- Proof sketch: rewrite both Fitzpatrick functions from Definition 20.51; swapping the graph
-- coordinates turns `gra A` into `gra A⁻¹`, so the inverse-operator Fitzpatrick owner is the
-- transpose `F[A]ᵀ`.
/-- Proposition 20.56 (7): clause (vi). The Fitzpatrick function of the inverse operator is the
transpose of the Fitzpatrick function. -/
theorem fitzpatrickFunction_inverse_eq_transpose :
    F[A⁻¹] = (F[A])ᵀ := by
  let e : gra A⁻¹ ≃ gra A :=
    { toFun := fun p ↦ ⟨(p.1.2, p.1.1), by
        exact p.2⟩
      invFun := fun p ↦ ⟨(p.1.2, p.1.1), by
        exact p.2⟩
      left_inv := by
        intro p
        ext <;> rfl
      right_inv := by
        intro p
        ext <;> rfl }
  ext ⟨u, x⟩
  -- Reindex the inverse-graph supremum by swapping the graph coordinates.
  rw [fitzpatrickFunction, transpose_apply, fitzpatrickFunction]
  exact e.iSup_congr fun p ↦ by
    simp [e, real_inner_comm, add_comm]

-- Proof sketch: expand the Fitzpatrick supremum of `γ A`; graph points of `γ A` are exactly the
-- pairs `(y, γ • v)` with `(y, v) ∈ gra A`, and pulling the positive scalar `γ` out of the
-- supremand yields the displayed scaling identity.
/-- Proposition 20.56 (8): clause (vii). Positive scaling of the operator scales the Fitzpatrick
function by the same factor after rescaling the second variable. -/
theorem fitzpatrickFunction_smul_apply
    (x u : H) (γ : Set.Ioi (0 : ℝ)) :
    F[((γ : ℝ) • A)] (x, u) =
      (((γ : ℝ) : EReal) * F[A] (x, (γ : ℝ)⁻¹ • u)) := by
  have hγ_pos : 0 < (γ : ℝ) := by
    exact γ.2
  have hγ_ne : (γ : ℝ) ≠ 0 := ne_of_gt hγ_pos
  let e : gra A ≃ gra ((γ : ℝ) • A) :=
    { toFun := fun p ↦ ⟨(p.1.1, (γ : ℝ) • p.1.2), by
        exact Set.mem_smul_set.mpr ⟨p.1.2, p.2, rfl⟩⟩
      invFun := fun p ↦ ⟨(p.1.1, (γ : ℝ)⁻¹ • p.1.2), by
        have hp :
            p.1.2 ∈ ((γ : ℝ) • A) p.1.1 := by
          exact p.2
        rcases Set.mem_smul_set.mp hp with ⟨v, hv, hv_eq⟩
        have hpre : (γ : ℝ)⁻¹ • p.1.2 = v := by
          rw [← hv_eq, smul_smul, inv_mul_cancel₀ hγ_ne, one_smul]
        simpa [hpre] using hv⟩
      left_inv := by
        intro p
        ext <;> simp [smul_smul, inv_mul_cancel₀ hγ_ne]
      right_inv := by
        intro p
        ext <;> simp [smul_smul, mul_inv_cancel₀ hγ_ne] }
  -- Reindex the scaled graph and factor the positive scalar `γ` out of the supremum.
  rw [fitzpatrickFunction, fitzpatrickFunction]
  calc
    (⨆ p : gra ((γ : ℝ) • A),
        ((⟪p.1.1, u⟫_ℝ + ⟪x, p.1.2⟫_ℝ - ⟪p.1.1, p.1.2⟫_ℝ : ℝ) : EReal)) =
        ⨆ p : gra A,
          ((⟪p.1.1, u⟫_ℝ + ⟪x, (γ : ℝ) • p.1.2⟫_ℝ - ⟪p.1.1, (γ : ℝ) • p.1.2⟫_ℝ : ℝ) : EReal) := by
            exact e.symm.iSup_congr fun p ↦ by
              simp [e, smul_smul, mul_inv_cancel₀ hγ_ne]
    _ = ⨆ p : gra A,
          (((γ : ℝ) : EReal) *
            ((⟪p.1.1, (γ : ℝ)⁻¹ • u⟫_ℝ + ⟪x, p.1.2⟫_ℝ - ⟪p.1.1, p.1.2⟫_ℝ : ℝ) : EReal)) := by
            refine iSup_congr fun p ↦ ?_
            have hfirst :
                (γ : ℝ) * ⟪p.1.1, (γ : ℝ)⁻¹ • u⟫_ℝ = ⟪p.1.1, u⟫_ℝ := by
              calc
                (γ : ℝ) * ⟪p.1.1, (γ : ℝ)⁻¹ • u⟫_ℝ
                    = ((γ : ℝ) * (γ : ℝ)⁻¹) * ⟪p.1.1, u⟫_ℝ := by
                        rw [real_inner_smul_right]
                        ring
                _ = ⟪p.1.1, u⟫_ℝ := by
                      field_simp [hγ_ne]
            have hthird :
                ⟪p.1.1, (γ : ℝ) • p.1.2⟫_ℝ = (γ : ℝ) * ⟪p.1.1, p.1.2⟫_ℝ := by
              rw [real_inner_smul_right]
            have hsecond :
                ⟪x, (γ : ℝ) • p.1.2⟫_ℝ = (γ : ℝ) * ⟪x, p.1.2⟫_ℝ := by
              rw [real_inner_smul_right]
            have hreal :
                ⟪p.1.1, u⟫_ℝ + ⟪x, (γ : ℝ) • p.1.2⟫_ℝ -
                    ⟪p.1.1, (γ : ℝ) • p.1.2⟫_ℝ =
                  (γ : ℝ) *
                    (⟪p.1.1, (γ : ℝ)⁻¹ • u⟫_ℝ + ⟪x, p.1.2⟫_ℝ -
                      ⟪p.1.1, p.1.2⟫_ℝ) := by
              rw [← hfirst, hsecond, hthird]
              ring
            simpa [EReal.coe_mul] using congrArg (fun t : ℝ => (t : EReal)) hreal
    _ = ((γ : ℝ) : EReal) *
          (⨆ p : gra A,
            ((⟪p.1.1, (γ : ℝ)⁻¹ • u⟫_ℝ + ⟪x, p.1.2⟫_ℝ - ⟪p.1.1, p.1.2⟫_ℝ : ℝ) : EReal)) := by
            simpa using (ereal_mul_iSup_of_pos (α := γ)
              (φ := fun p : gra A ↦
                ((⟪p.1.1, (γ : ℝ)⁻¹ • u⟫_ℝ + ⟪x, p.1.2⟫_ℝ -
                  ⟪p.1.1, p.1.2⟫_ℝ : ℝ) : EReal))).symm

end

end

end SetValuedOperator
