import Mathlib
import StacksProject_2024.Chap10.Lemma_10_52_6
import StacksProject_2024.Chap10.Lemma_10_52_11

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators
open IsLocalRing LocalizedModule

universe u v w

noncomputable section

section Length

local notation "AtPrime" => LocalizedModule.AtPrime

variable {A : Type u} {B : Type v} {M : Type w}
variable [CommRing A] [CommRing B] [IsLocalRing A] [Algebra A B]
variable [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]
variable [Finite (MaximalSpectrum B)]

local notation "κA" => Ideal.ResidueField (maximalIdeal A)

/-
Domain triage:
* primary domain: finite-length modules over a semilocal algebra, decomposed by maximal ideals and
  the corresponding residue-field extensions;
* sampled owner API:
  `CompositionSeries.factor_count_eq_length_localizedModule`,
  `module_length_eq_rank_quotient_of_isTorsionBySet`,
  `Module.length_eq_add_of_exact`,
  `Module.length_ne_top_iff`;
* source-facing layer: the semilocal localization formula and its finite-length corollary;
* core/canonical owners: `CompositionSeries (Submodule B M)` for the localized factor counts and
  `IsFiniteLength` / `Module.IsTorsionBySet` for finite-length and residue-field computations;
* bridge/view: this file keeps the source-facing sum formula while routing its local simple-factor
  terms through the owner statements from `10.52.11` and `10.52.6` instead of duplicating those
  lower-level APIs.
-/

section ResidueFieldData

variable
    (hcomap : ∀ m : MaximalSpectrum B,
      Ideal.comap (algebraMap A B) m.asIdeal = maximalIdeal A)

private abbrev residueFieldModule (m : MaximalSpectrum B) :
    Module κA (Ideal.ResidueField m.asIdeal) :=
  ((Ideal.ResidueField.map (maximalIdeal A) m.asIdeal (algebraMap A B) (hcomap m).symm).toAlgebra).toModule

variable
    (hfinitek : ∀ m : MaximalSpectrum B,
      let _ : Module κA (Ideal.ResidueField m.asIdeal) := residueFieldModule hcomap m
      Module.Finite κA (Ideal.ResidueField m.asIdeal))

/-- Helper for Lemma 10.52.12: the maximal ideal attached to a simple factor in a composition
series. -/
def CompositionSeries.factor_maximalSpectrum (s : CompositionSeries (Submodule B M))
    (i : Fin s.length) : MaximalSpectrum B :=
  ⟨Module.annihilator B (s.factor i), s.factor_annihilator_isMaximal i⟩

namespace CompositionSeries

/-- Helper for Lemma 10.52.12: one step in the composition series adds the length of the
corresponding factor after restricting scalars from `B` to `A`. -/
theorem step_length_eq_add_factor_length_restrictScalars
    (s : CompositionSeries (Submodule B M)) (i : Fin s.length) :
    Module.length A ↥((s i.succ).restrictScalars A) =
      Module.length A ↥((s i.castSucc).restrictScalars A) + Module.length A (s.factor i) := by
  let P : Submodule A M := (s i.succ).restrictScalars A
  let Q : Submodule A M := (s i.castSucc).restrictScalars A
  let N : Submodule A P := Q.comap P.subtype
  -- Compare the predecessor submodule with its comap inside the next term of the chain.
  have hN : Module.length A ↥N = Module.length A ↥(s i.castSucc) := by
    let e₀ := N.equivMapOfInjective P.subtype (Submodule.injective_subtype _)
    have hQP : Q ≤ P := by
      intro x hx
      exact CovBy.le (s.step i) hx
    have hmap : N.map P.subtype = Q := by
      rw [Submodule.map_comap_subtype, inf_of_le_right hQP]
    let e : N ≃ₗ[A] Q := e₀.trans <| LinearEquiv.ofEq _ _ hmap
    simpa using e.length_eq
  -- Apply additivity of length to the short exact sequence `0 → N → s i.succ → s.factor i → 0`.
  simpa [P, Q, N, hN, CompositionSeries.factor] using
    (Module.length_eq_add_of_exact N.subtype (Submodule.mkQ N)
      (Submodule.subtype_injective _) (Submodule.mkQ_surjective _)
      (LinearMap.exact_subtype_mkQ N))

/-- Helper for Lemma 10.52.12: the `A`-length of `M` is the sum of the `A`-lengths of the factors
in any `B`-composition series from `0` to `M`. -/
theorem length_eq_sum_factor_length_restrictScalars
    (s : CompositionSeries (Submodule B M)) (hs0 : s.head = ⊥) (hs1 : s.last = ⊤) :
    Module.length A M = ∑ i : Fin s.length, Module.length A (s.factor i) := by
  -- Prove by induction that every stage of the chain has length equal to the sum of earlier factors.
  have hprefix :
      ∀ n : ℕ, ∀ hn : n ≤ s.length,
        Module.length A ↥((s ⟨n, Nat.lt_succ_of_le hn⟩).restrictScalars A) =
          ∑ i : Fin n, Module.length A (s.factor ⟨i, Nat.lt_of_lt_of_le i.isLt hn⟩) := by
    intro n
    induction n with
    | zero =>
        intro hn
        -- The chain starts at `0`, so the initial partial sum is zero.
        have hs0A : (s ⟨0, Nat.lt_succ_of_le hn⟩).restrictScalars A = ⊥ := by
          simpa using congrArg (Submodule.restrictScalars A) hs0
        rw [hs0A, Module.length_bot]
        simp
    | succ n ih =>
        intro hn
        have hn' : n ≤ s.length := Nat.le_of_succ_le hn
        let i : Fin s.length := ⟨n, Nat.lt_of_succ_le hn⟩
        -- Add the next factor using the one-step exact sequence.
        calc
          Module.length A ↥((s ⟨n + 1, Nat.lt_succ_of_le hn⟩).restrictScalars A)
              = Module.length A ↥((s ⟨n, Nat.lt_succ_of_le hn'⟩).restrictScalars A) +
                  Module.length A (s.factor i) := by
                  simpa [i] using s.step_length_eq_add_factor_length_restrictScalars (A := A) i
          _ = (∑ j : Fin n, Module.length A (s.factor ⟨j, Nat.lt_of_lt_of_le j.isLt hn'⟩)) +
                Module.length A (s.factor i) := by
                  rw [ih hn']
          _ = ∑ j : Fin (n + 1),
                Module.length A (s.factor ⟨j, Nat.lt_of_lt_of_le j.isLt hn⟩) := by
                  symm
                  simpa [i] using
                    (Fin.sum_univ_castSucc
                      (f := fun j : Fin (n + 1) =>
                        Module.length A (s.factor ⟨j, Nat.lt_of_lt_of_le j.isLt hn⟩)))
  -- Evaluate the partial-sum formula at the last term of the composition series.
  have hlast : ((s (Fin.last s.length)).restrictScalars A : Submodule A M) = ⊤ := by
    simpa using congrArg (Submodule.restrictScalars A) hs1
  calc
    Module.length A M = Module.length A ↥((⊤ : Submodule A M)) := by
      simpa using (Module.length_top (R := A) (M := M)).symm
    _ = Module.length A ↥((s (Fin.last s.length)).restrictScalars A) := by
      rw [← hlast]
    _ = ∑ i : Fin s.length, Module.length A (s.factor i) := by
      simpa using hprefix s.length le_rfl

end CompositionSeries

/-- Helper for Lemma 10.52.12: after contracting `m` to `maximalIdeal A`, the `A`-length of the
residue field of `m` equals its `κ(maximalIdeal A)`-dimension. -/
theorem length_residueField_over_A_eq_finrank
    (hcomap : ∀ m : MaximalSpectrum B,
      Ideal.comap (algebraMap A B) m.asIdeal = maximalIdeal A)
    (hfinitek : ∀ m : MaximalSpectrum B,
      let _ : Module κA (Ideal.ResidueField m.asIdeal) := residueFieldModule hcomap m
      Module.Finite κA (Ideal.ResidueField m.asIdeal))
    (m : MaximalSpectrum B) :
    let _ : Module κA (Ideal.ResidueField m.asIdeal) := residueFieldModule hcomap m
    let _ : Module.Finite κA (Ideal.ResidueField m.asIdeal) := hfinitek m
    Module.length A (Ideal.ResidueField m.asIdeal) =
      (Module.finrank κA (Ideal.ResidueField m.asIdeal) : ENat) := by
  let _ : Algebra κA (Ideal.ResidueField m.asIdeal) :=
    (Ideal.ResidueField.map (maximalIdeal A) m.asIdeal (algebraMap A B) (hcomap m).symm).toAlgebra
  let _ : IsScalarTower A κA (Ideal.ResidueField m.asIdeal) := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    ext a
    exact (IsScalarTower.algebraMap_apply A B (Ideal.ResidueField m.asIdeal) a).trans
      ((Ideal.ResidueField.map_algebraMap (maximalIdeal A) m.asIdeal (algebraMap A B)
        (hcomap m).symm a).symm)
  let _ : Module κA (Ideal.ResidueField m.asIdeal) := residueFieldModule hcomap m
  let _ : Module.Finite κA (Ideal.ResidueField m.asIdeal) := hfinitek m
  have hsurj : Function.Surjective (algebraMap A κA) := by
    intro x
    obtain ⟨y, rfl⟩ := (Ideal.bijective_algebraMap_quotient_residueField (maximalIdeal A)).surjective x
    obtain ⟨a, rfl⟩ := (Ideal.Quotient.mk_surjective (I := maximalIdeal A)) y
    exact ⟨a, by
      simpa using (Ideal.algebraMap_quotient_residueField_mk (I := maximalIdeal A) a)⟩
  -- First pass from `A` to its residue field, then compute length over the field `κA`.
  calc
    Module.length A (Ideal.ResidueField m.asIdeal)
      = Module.length κA (Ideal.ResidueField m.asIdeal) := by
          exact Module.length_eq_of_surjective (R := κA) (M := Ideal.ResidueField m.asIdeal) hsurj
    _ = (Module.finrank κA (Ideal.ResidueField m.asIdeal) : ENat) := by
          simpa using (Module.length_eq_finrank κA (Ideal.ResidueField m.asIdeal))

namespace CompositionSeries

/-- Helper for Lemma 10.52.12: each simple factor in the chosen `B`-composition series contributes
the residue-field degree of the maximal ideal attached to that factor. -/
theorem factor_length_over_A_eq_residueField_degree
    (hcomap : ∀ m : MaximalSpectrum B,
      Ideal.comap (algebraMap A B) m.asIdeal = maximalIdeal A)
    (hfinitek : ∀ m : MaximalSpectrum B,
      let _ : Module κA (Ideal.ResidueField m.asIdeal) := residueFieldModule hcomap m
      Module.Finite κA (Ideal.ResidueField m.asIdeal))
    (s : CompositionSeries (Submodule B M)) (i : Fin s.length) :
    let m := s.factor_maximalSpectrum i
    let _ : Module κA (Ideal.ResidueField m.asIdeal) := residueFieldModule hcomap m
    let _ : Module.Finite κA (Ideal.ResidueField m.asIdeal) := hfinitek m
    Module.length A (s.factor i) =
      (Module.finrank κA (Ideal.ResidueField m.asIdeal) : ENat) := by
  let m := s.factor_maximalSpectrum i
  let _ : Algebra κA (Ideal.ResidueField m.asIdeal) :=
    (Ideal.ResidueField.map (maximalIdeal A) m.asIdeal (algebraMap A B) (hcomap m).symm).toAlgebra
  let _ : Module κA (Ideal.ResidueField m.asIdeal) := residueFieldModule hcomap m
  let _ : Module.Finite κA (Ideal.ResidueField m.asIdeal) := hfinitek m
  -- Identify the simple factor with the quotient by its annihilator and then with the residue field.
  have hfactor :
      Module.length A (s.factor i) = Module.length A (Ideal.ResidueField m.asIdeal) := by
    let J : Ideal B := Module.annihilator B (s.factor i)
    let _ : J.IsMaximal := s.factor_annihilator_isMaximal i
    let e₁ : s.factor i ≃ₗ[A] (B ⧸ J) := by
      let e := Classical.choice (s.factor_isomorphic_quotient_annihilator i)
      exact e.restrictScalars A
    let e₂ : (B ⧸ J) ≃ₗ[A] Ideal.ResidueField J := by
      let e : (B ⧸ J) ≃ₐ[B ⧸ J] Ideal.ResidueField J :=
        AlgEquiv.ofBijective
          (Algebra.ofId (B ⧸ J) (Ideal.ResidueField J))
          (Ideal.bijective_algebraMap_quotient_residueField J)
      exact e.toLinearEquiv.restrictScalars A
    simpa [m, J, CompositionSeries.factor_maximalSpectrum] using e₁.length_eq.trans e₂.length_eq
  -- Compute the `A`-length of the residue field using the finite `κA`-vector space structure.
  calc
    Module.length A (s.factor i) = Module.length A (Ideal.ResidueField m.asIdeal) := hfactor
    _ = (Module.finrank κA (Ideal.ResidueField m.asIdeal) : ENat) := by
          simpa using length_residueField_over_A_eq_finrank
            (A := A) (B := B) hcomap hfinitek m

/-- Helper for Lemma 10.52.12: regrouping factor-by-factor contributions by maximal ideal turns the
sum over the composition-series factors into the sum of localization lengths. -/
theorem sum_factor_weights_eq_sum_localized_lengths
    [Fintype (MaximalSpectrum B)]
    (s : CompositionSeries (Submodule B M)) (hs0 : s.head = ⊥) (hs1 : s.last = ⊤)
    (w : MaximalSpectrum B → ENat) :
    ∑ i : Fin s.length, w (s.factor_maximalSpectrum i) =
      ∑ m : MaximalSpectrum B,
        w m * Module.length (Localization.AtPrime m.asIdeal) (AtPrime m.asIdeal M) := by
  classical
  -- Regroup the factor contributions by the maximal ideal attached to each factor.
  rw [← Finset.sum_fiberwise' (s := Finset.univ) (fun i : Fin s.length ↦ s.factor_maximalSpectrum i) w]
  refine Finset.sum_congr rfl ?_
  intro m hm
  calc
    ∑ i ∈ Finset.univ.filter (fun i : Fin s.length => s.factor_maximalSpectrum i = m), w m
      = ((Finset.univ.filter (fun i : Fin s.length => s.factor_maximalSpectrum i = m)).card : ENat) *
          w m := by
            simp
    _ = w m * ENat.card { i : Fin s.length // s.factor_maximalSpectrum i = m } := by
          have hcard :
              ((Finset.univ.filter (fun i : Fin s.length => s.factor_maximalSpectrum i = m)).card :
                ENat) = ENat.card { i : Fin s.length // s.factor_maximalSpectrum i = m } := by
            simp [ENat.card_eq_coe_fintype_card, Fintype.card_subtype]
          rw [hcard, mul_comm]
    _ = w m * ENat.card { i : Fin s.length //
          Module.annihilator B (s.factor i) = m.asIdeal } := by
          congr 1
          apply ENat.card_congr
          refine
            { toFun := fun i ↦
                ⟨i.1, by
                  simpa [CompositionSeries.factor_maximalSpectrum] using
                    congrArg MaximalSpectrum.asIdeal i.2⟩
              invFun := fun i ↦
                ⟨i.1, by
                  cases m with
                  | mk m hm =>
                      cases i with
                      | mk j hj =>
                          dsimp [CompositionSeries.factor_maximalSpectrum] at hj ⊢
                          cases hj
                          rfl⟩
              left_inv := by intro i; cases i; rfl
              right_inv := by intro i; cases i; rfl }
    _ = w m * Module.length (Localization.AtPrime m.asIdeal) (AtPrime m.asIdeal M) := by
          rw [s.factor_count_eq_length_localizedModule hs0 hs1 m.asIdeal]

end CompositionSeries

-- Proof sketch: choose a composition series of the finite-length `B`-module `M`. By Lemma
-- 10.52.11, each factor is a residue field `J.ResidueField` for a unique maximal ideal `J` of
-- `B`, and the number of times `J.ResidueField` occurs is the length of `M` localized at `J`.
-- Restrict scalars to `A`, identify the `A`-length of each factor with the length of the induced
-- residue-field extension `κ(maximalIdeal A) → κ(J)` via Lemma 10.52.6, and sum the contributions
-- using additivity of length from Lemma 10.52.3.
/-- Lemma 10.52.12 (Tag `02M0`): if `A → B` maps the semilocal ring `B` to the local ring `A`
so that every maximal ideal of `B` lies over `maximalIdeal A`, every residue-field extension
`κ(m) / κ(maximalIdeal A)` is finite, and `M` has finite length as a `B`-module, then the
`A`-length of `M` is the sum of the residue-field degrees
`[κ(m) : κ(maximalIdeal A)]` times the lengths of the localizations `Mₘ`.

Canonical Lean form: the semilocal structure is expressed by `[Finite (MaximalSpectrum B)]`, the
finite-length hypothesis is the owner predicate `IsFiniteLength B M`, and the residue-field degree
is written as `Module.finrank`. -/
theorem length_eq_sum_residueFieldDegree_mul_length_localizedModule
    (hcomap : ∀ m : MaximalSpectrum B,
      Ideal.comap (algebraMap A B) m.asIdeal = maximalIdeal A)
    (hfinitek : ∀ m : MaximalSpectrum B,
      let _ : Module κA (Ideal.ResidueField m.asIdeal) := residueFieldModule hcomap m
      Module.Finite κA (Ideal.ResidueField m.asIdeal))
    (hM : IsFiniteLength B M) :
    let _ : Fintype (MaximalSpectrum B) := Fintype.ofFinite (MaximalSpectrum B)
    Module.length A M =
      ∑ m : MaximalSpectrum B,
        let _ : Module κA (Ideal.ResidueField m.asIdeal) := residueFieldModule hcomap m
        let _ : Module.Finite κA (Ideal.ResidueField m.asIdeal) := hfinitek m
        (Module.finrank κA (Ideal.ResidueField m.asIdeal) : ENat) *
          Module.length (Localization.AtPrime m.asIdeal) (AtPrime m.asIdeal M) := by
  let _ : Fintype (MaximalSpectrum B) := Fintype.ofFinite (MaximalSpectrum B)
  obtain ⟨s, hs0, hs1⟩ := isFiniteLength_iff_exists_compositionSeries.mp hM
  let weight : MaximalSpectrum B → ENat := fun m ↦
    let _ : Module κA (Ideal.ResidueField m.asIdeal) := residueFieldModule hcomap m
    let _ : Module.Finite κA (Ideal.ResidueField m.asIdeal) := hfinitek m
    (Module.finrank κA (Ideal.ResidueField m.asIdeal) : ENat)
  -- Follow the source proof: sum the `A`-lengths of the factors and then regroup by maximal ideal.
  calc
    Module.length A M = ∑ i : Fin s.length, Module.length A (s.factor i) := by
      simpa using s.length_eq_sum_factor_length_restrictScalars (A := A) hs0 hs1
    _ = ∑ i : Fin s.length, weight (s.factor_maximalSpectrum i) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      simpa [weight, CompositionSeries.factor_maximalSpectrum] using
        s.factor_length_over_A_eq_residueField_degree
          (A := A) hcomap hfinitek i
    _ = ∑ m : MaximalSpectrum B,
          weight m * Module.length (Localization.AtPrime m.asIdeal) (AtPrime m.asIdeal M) := by
            exact s.sum_factor_weights_eq_sum_localized_lengths (B := B) (M := M) hs0 hs1 weight

-- Proof sketch: apply the semilocal localization formula above. Each summand is finite because the
-- residue-field factor is finite by hypothesis and the localized length is bounded by the original
-- finite `B`-length. A finite sum of finite `ENat` values is finite.
/-- Under the hypotheses of the semilocal localization formula, `M` has finite length over `A`. -/
theorem isFiniteLength_of_finiteLength_over_semilocal
    (hcomap : ∀ m : MaximalSpectrum B,
      Ideal.comap (algebraMap A B) m.asIdeal = maximalIdeal A)
    (hfinitek : ∀ m : MaximalSpectrum B,
      let _ : Module κA (Ideal.ResidueField m.asIdeal) := residueFieldModule hcomap m
      Module.Finite κA (Ideal.ResidueField m.asIdeal))
    (hM : IsFiniteLength B M) :
    IsFiniteLength A M := by
  let _ : Fintype (MaximalSpectrum B) := Fintype.ofFinite (MaximalSpectrum B)
  obtain ⟨s, hs0, hs1⟩ := isFiniteLength_iff_exists_compositionSeries.mp hM
  -- The weighted localization formula expresses `Module.length A M` as a finite sum of finite terms.
  rw [← Module.length_ne_top_iff]
  rw [length_eq_sum_residueFieldDegree_mul_length_localizedModule (A := A) (B := B) (M := M)
    hcomap hfinitek hM]
  have hsum :
      (∑ m : MaximalSpectrum B,
          let _ : Module κA (Ideal.ResidueField m.asIdeal) := residueFieldModule hcomap m
          let _ : Module.Finite κA (Ideal.ResidueField m.asIdeal) := hfinitek m
          (Module.finrank κA (Ideal.ResidueField m.asIdeal) : ENat) *
            Module.length (Localization.AtPrime m.asIdeal) (AtPrime m.asIdeal M)) ≠ ⊤ := by
    simpa using
      (ENat.sum_ne_top (s := Finset.univ) (f := fun m : MaximalSpectrum B ↦
        let _ : Module κA (Ideal.ResidueField m.asIdeal) := residueFieldModule hcomap m
        let _ : Module.Finite κA (Ideal.ResidueField m.asIdeal) := hfinitek m
        (Module.finrank κA (Ideal.ResidueField m.asIdeal) : ENat) *
          Module.length (Localization.AtPrime m.asIdeal) (AtPrime m.asIdeal M))).2
        (fun m hm ↦ by
          let _ : Module κA (Ideal.ResidueField m.asIdeal) := residueFieldModule hcomap m
          let _ : Module.Finite κA (Ideal.ResidueField m.asIdeal) := hfinitek m
          -- Each coefficient is finite, and each localized length is a finite cardinality of factors.
          have hcoeff : (Module.finrank κA (Ideal.ResidueField m.asIdeal) : ENat) ≠ ⊤ := by
            simp
          have hloc : Module.length (Localization.AtPrime m.asIdeal) (AtPrime m.asIdeal M) ≠ ⊤ := by
            rw [← s.factor_count_eq_length_localizedModule hs0 hs1 m.asIdeal,
              ENat.card_eq_coe_fintype_card]
            simp
          exact WithTop.mul_ne_top hcoeff hloc)
  simpa using hsum

end ResidueFieldData

end Length
