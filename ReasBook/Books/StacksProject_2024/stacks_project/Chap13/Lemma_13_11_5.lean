import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open HomologicalComplex
open CochainComplex

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]
variable (K : CochainComplex C ℤ)

/- Domain-style sampling:
- primary domain: canonical truncations of cochain complexes and the quasi-isomorphism criteria
  attached to the maps `πTruncGE`, `ιTruncLE`, and `truncGEMap`;
- sampled owner declarations:
  `CochainComplex.πTruncGE`,
  `CochainComplex.ιTruncLE`,
  `CochainComplex.truncGEMap`,
  `CochainComplex.quasiIso_πTruncGE_iff`,
  `CochainComplex.quasiIso_ιTruncLE_iff`,
  `CategoryTheory.CommSq`;
- best owner abstraction: the primitive data are the canonical truncation objects/maps and the
  boundedness predicates `IsGE`, `IsLE`, `IsStrictlyGE`, `IsStrictlyLE`; the existence results in
  this file are derived API and should be stated directly in terms of those owners rather than
  through a separate wrapper class;
- source/core/bridge triage:
  `source-facing`: existence of bounded truncation replacements for a complex with eventually
    vanishing homology;
  `core/canonical`: the truncation maps and boundedness owners on `CochainComplex C ℤ`;
  `bridge/view`: the commuting-square formulation for the simultaneous lower/upper truncation.
-/

-- Proof sketch: choose a lower bound `a` below which all homology objects of `K` vanish, deduce
-- `K.IsGE a` from `HomologicalComplex.exactAt_iff_isZero_homology`, and then use the canonical
-- `QuasiIso` instance for `K.πTruncGE a`.
/-- Lemma 13.11.5 (1): if the homology of `K` vanishes in sufficiently negative degrees, then for
some lower truncation bound `a` the canonical map `K ⟶ K.truncGE a` is a quasi-isomorphism, and
`K.truncGE a` is bounded below. -/
theorem exists_quasiIso_to_truncGE_of_eventually_isZero_homology
    (hK : ∃ a : ℤ, ∀ n : ℤ, n < a → IsZero (K.homology n)) :
    ∃ a : ℤ, QuasiIso (K.πTruncGE a) ∧ (K.truncGE a).IsStrictlyGE a := by
  rcases hK with ⟨a, ha⟩
  have hGE : K.IsGE a := by
    rw [isGE_iff]
    intro n hn
    rw [exactAt_iff_isZero_homology]
    exact ha n hn
  letI : K.IsGE a := hGE
  exact ⟨a, inferInstance, inferInstance⟩

-- Proof sketch: choose an upper bound `b` above which all homology objects of `K` vanish, deduce
-- `K.IsLE b` from `HomologicalComplex.exactAt_iff_isZero_homology`, and then use the canonical
-- `QuasiIso` instance for `K.ιTruncLE b`.
/-- Lemma 13.11.5 (2): if the homology of `K` vanishes in sufficiently positive degrees, then for
some upper truncation bound `b` the canonical map `K.truncLE b ⟶ K` is a quasi-isomorphism, and
`K.truncLE b` is bounded above. -/
theorem exists_quasiIso_from_truncLE_of_eventually_isZero_homology
    (hK : ∃ b : ℤ, ∀ n : ℤ, b < n → IsZero (K.homology n)) :
    ∃ b : ℤ, QuasiIso (K.ιTruncLE b) ∧ (K.truncLE b).IsStrictlyLE b := by
  rcases hK with ⟨b, hb⟩
  have hLE : K.IsLE b := by
    rw [isLE_iff]
    intro n hn
    rw [exactAt_iff_isZero_homology]
    exact hb n hn
  letI : K.IsLE b := hLE
  exact ⟨b, inferInstance, inferInstance⟩

-- Proof sketch: choose bounds `a ≪ 0 ≪ b` so that the homology of `K` vanishes outside `[a, b]`,
-- take the canonical square formed by `K`, `K.truncGE a`, `K.truncLE b`, and
-- `(K.truncLE b).truncGE a`, use the first two clauses for the vertical and horizontal maps, and
-- use truncation naturality for commutativity.
/-- Lemma 13.11.5 (3): if the homology of `K` vanishes outside a finite range, then there are
truncation bounds `a ≤ b` for which the canonical square
`K ⟶ K.truncGE a`, `K.truncLE b ⟶ K`, `(K.truncLE b).truncGE a ⟶ K.truncGE a`
consists of quasi-isomorphisms, commutes, and has bounded middle-bottom complex. -/
theorem exists_quasiIso_truncation_square_of_eventually_isZero_homology
    (hK : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (K.homology n)) :
    ∃ a b : ℤ,
      a ≤ b ∧
      QuasiIso (K.πTruncGE a) ∧
      QuasiIso (K.ιTruncLE b) ∧
      QuasiIso ((K.truncLE b).πTruncGE a) ∧
      QuasiIso (truncGEMap (K.ιTruncLE b) a) ∧
      CommSq
        ((K.truncLE b).πTruncGE a)
        (K.ιTruncLE b)
        (truncGEMap (K.ιTruncLE b) a)
        (K.πTruncGE a) ∧
      ((K.truncLE b).truncGE a).IsStrictlyGE a ∧
      ((K.truncLE b).truncGE a).IsStrictlyLE b := by
  rcases hK with ⟨a₀, b₀, h⟩
  let a := min a₀ b₀
  let b := max a₀ b₀
  have hab : a ≤ b := by
    simpa [a, b] using min_le_max a₀ b₀
  have hGE : K.IsGE a := by
    rw [isGE_iff]
    intro n hn
    rw [exactAt_iff_isZero_homology]
    exact h n <| Or.inl <| lt_of_lt_of_le hn <| by
      dsimp [a]
      exact Int.min_le_left _ _
  have hLE : K.IsLE b := by
    rw [isLE_iff]
    intro n hn
    rw [exactAt_iff_isZero_homology]
    exact h n <| Or.inr <| lt_of_le_of_lt (by
      dsimp [b]
      exact Int.le_max_right _ _) hn
  letI : K.IsGE a := hGE
  letI : K.IsLE b := hLE
  have hTruncLEGE : (K.truncLE b).IsGE a := by
    rw [isGE_iff]
    intro n hn
    exact (exactAt_iff_of_quasiIsoAt (K.ιTruncLE b) n).2 <| by
      rw [exactAt_iff_isZero_homology]
      exact h n <| Or.inl <| lt_of_lt_of_le hn <| by
        dsimp [a]
        exact Int.min_le_left _ _
  letI : (K.truncLE b).IsGE a := hTruncLEGE
  refine ⟨a, b, hab, inferInstance, inferInstance, inferInstance, ?_, ?_, inferInstance,
    inferInstance⟩
  · have hQuasi :
        QuasiIso (truncGEMap (K.ιTruncLE b) a) ↔
          ∀ n : ℤ, a ≤ n → QuasiIsoAt (K.ιTruncLE b) n :=
      CochainComplex.quasiIso_truncGEMap_iff (K.ιTruncLE b) a
    exact hQuasi.2 fun n hn ↦ inferInstance
  · exact ⟨πTruncGE_naturality (K.ιTruncLE b) a⟩
