import Mathlib
import stacks_proof.stacks_project.Chap10.Definition_10_135_1
import stacks_proof.stacks_project.Chap10.Lemma_10_114_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

section

variable {k : Type u} [Field k]
variable {S : Type v} [CommRing S] [Algebra k S]

/-
Source/core/bridge triage:
* source-facing: the textbook assertions for principal localizations `S_g`;
* core/canonical: the owner classes `IsGlobalCompleteIntersection k S` and
  `IsLocalCompleteIntersection k S` from Definition `10.135.1`;
* bridge/view: permanence along an arbitrary away-localization target `Sg` with
  `[IsLocalization.Away g Sg]`, of which `Localization.Away g` is the canonical model.

The primitive data live in the owner classes from Definition `10.135.1`. This file adds only the
derived principal-localization API from Lemma `10.135.2`; the concrete ring `Localization.Away g`
is only a specialization of the intrinsic away-localization owner.
-/

namespace IsGlobalCompleteIntersection

variable {Sg : Type w} [CommRing Sg] [Algebra S Sg] [Algebra k Sg] [IsScalarTower k S Sg]

open PrimeSpectrum

/- The source proof localizes a chosen finite presentation by adjoining one inverse variable.
The corresponding mathlib object is `Presentation.localizationAway` composed with the original
presentation. -/

/-- Helper for Lemma 10.135.2: reindex the localized composite presentation so that its variables
and relations are indexed by finite ordinals again. -/
noncomputable abbrev localized_comp_presentation
    (g : S) {n c : ℕ} (P : Algebra.Presentation k S (Fin n) (Fin c))
    [IsLocalization.Away g Sg] :
    Algebra.Presentation k Sg
      (Fin (Fintype.card (Unit ⊕ Fin n))) (Fin (Fintype.card (Unit ⊕ Fin c))) :=
  ((Algebra.Presentation.localizationAway Sg g).comp P).reindex
    (Fintype.equivFin (Unit ⊕ Fin n)).symm
    (Fintype.equivFin (Unit ⊕ Fin c)).symm

variable (Sg) in
/-- Helper for Lemma 10.135.2: adjoining one inverse variable does not change the presentation
dimension. -/
lemma localized_comp_presentation_dimension
    (g : S) {n c : ℕ} (P : Algebra.Presentation k S (Fin n) (Fin c))
    [IsLocalization.Away g Sg] :
    (localized_comp_presentation (Sg := Sg) g P).dimension = P.dimension := by
  -- Reindexing preserves the dimension, and the composite presentation adds one generator and one
  -- relation.
  rw [Algebra.Presentation.dimension_reindex]
  simp [Algebra.Presentation.dimension]
  omega

variable (Sg) in
/-- Helper for Lemma 10.135.2: localizing away from one element cannot increase Krull
dimension. -/
lemma ringKrullDim_localizationAway_le
    (g : S) [IsLocalization.Away g Sg] :
    ringKrullDim Sg ≤ ringKrullDim S := by
  -- Compare the height of every maximal ideal of the localization with its contracted ideal in
  -- the source ring.
  refine (ringKrullDim_le_iff_isMaximal_height_le (ringKrullDim S)).2 ?_
  intro J hJ
  let _ : J.IsPrime := hJ.isPrime
  rw [← IsLocalization.height_comap (Submonoid.powers g) J]
  -- The contracted ideal is still proper, so its height is bounded by the source Krull dimension.
  exact Ideal.height_le_ringKrullDim_of_ne_top <|
    Ideal.comap_ne_top (algebraMap S Sg) hJ.ne_top

variable (Sg) in
/-- Helper for Lemma 10.135.2: in the nontrivial branch, the localized presentation should still
realize the Krull dimension. -/
lemma mvPolynomial_quotient_le_dim_add_relation_count
    {n c : ℕ} (f : Fin c → MvPolynomial (Fin n) k)
    [Nontrivial ((MvPolynomial (Fin n) k) ⧸ Ideal.span (Set.range f))] :
    ((n : ℕ) : WithBot ℕ∞) ≤
      ringKrullDim ((MvPolynomial (Fin n) k) ⧸ Ideal.span (Set.range f)) + c := by
  let I : Ideal (MvPolynomial (Fin n) k) := Ideal.span (Set.range f)
  have hI : I ≠ ⊤ := Ideal.Quotient.nontrivial_iff.mp inferInstance
  obtain ⟨m, hmmax, hIm⟩ := Ideal.exists_le_maximal I hI
  let 𝔪 : MaximalSpectrum (MvPolynomial (Fin n) k) := ⟨m, hmmax⟩
  have hm_range : Set.range f ⊆ m := by
    -- The defining relations lie in the maximal ideal chosen above the relation ideal.
    intro x hx
    exact hIm (Ideal.subset_span hx)
  have hm_height : m.height = ((n : ℕ) : WithBot ℕ∞) := by
    -- Identify the height of `m` with the Krull dimension of the corresponding local ring.
    calc
      m.height = ringKrullDim (Localization.AtPrime m) := by
        symm
        exact IsLocalization.AtPrime.ringKrullDim_eq_height m (Localization.AtPrime m)
      _ = ((n : ℕ) : WithBot ℕ∞) := by
        simpa using ringKrullDim_localizationAtMaximal_mvPolynomial 𝔪
  have hrange :
      (Set.range f).encard ≤ c := by
    -- Duplicated relations are allowed, so only an upper bound by the index set cardinality is
    -- needed.
    rw [← Set.image_univ]
    simpa using (Set.encard_image_le f (Set.univ : Set (Fin c)))
  calc
    ((n : ℕ) : WithBot ℕ∞) = m.height := hm_height.symm
    _ ≤ ringKrullDim ((MvPolynomial (Fin n) k) ⧸ Ideal.span (Set.range f)) +
          (Set.range f).encard :=
        Ideal.height_le_ringKrullDim_quotient_add_encard (s := Set.range f) hm_range
    _ ≤ ringKrullDim ((MvPolynomial (Fin n) k) ⧸ Ideal.span (Set.range f)) + c := by
        gcongr
        exact WithBot.coe_le_coe.mpr hrange

variable (Sg) in
/-- Helper for Lemma 10.135.2: the explicit localized `(c + 1)`-relation quotient presentation
gives the source lower bound on the localized Krull dimension. -/
lemma localized_comp_presentation_relation_bound
    (g : S) {n c : ℕ} (P : Algebra.Presentation k S (Fin n) (Fin c))
    [IsLocalization.Away g Sg] [Nontrivial Sg] :
    ((Fintype.card (Unit ⊕ Fin n) : ℕ) : WithBot ℕ∞) ≤
      ringKrullDim Sg + Fintype.card (Unit ⊕ Fin c) := by
  let Q := localized_comp_presentation (Sg := Sg) g P
  rcases presentation_relation_quotient_model Q with ⟨e⟩
  letI :
      Nontrivial
        ((MvPolynomial (Fin (Fintype.card (Unit ⊕ Fin n))) k) ⧸
          Ideal.span (Set.range Q.relation)) :=
    e.toEquiv.nontrivial
  -- Transport the ambient polynomial-quotient inequality across the quotient model of the
  -- localized presentation.
  simpa [Q, ringKrullDim_eq_of_ringEquiv e.toRingEquiv] using
    mvPolynomial_quotient_le_dim_add_relation_count
      (f := Q.relation)

variable (Sg) in
/-- Helper for Lemma 10.135.2: in the nontrivial branch, the localized presentation should still
realize the Krull dimension. -/
lemma ringKrullDim_localized_comp_presentation
    (g : S) {n c : ℕ} (P : Algebra.Presentation k S (Fin n) (Fin c))
    (hP : ringKrullDim S = P.dimension) [IsLocalization.Away g Sg] [Nontrivial Sg] :
    ringKrullDim Sg = (localized_comp_presentation (Sg := Sg) g P).dimension := by
  apply le_antisymm
  · -- The source dimension controls the localized dimension, and the localized presentation keeps
    -- the same presentation dimension.
    calc
      ringKrullDim Sg ≤ ringKrullDim S :=
        ringKrullDim_localizationAway_le (Sg := Sg) g
      _ = P.dimension := hP
      _ = (localized_comp_presentation (Sg := Sg) g P).dimension := by
        exact_mod_cast (localized_comp_presentation_dimension (Sg := Sg) g P).symm
  · -- Route correction: the remaining source-faithful step is the lower bound coming from the
    -- localized `(c + 1)`-relation presentation and Krull's height theorem.
    have hupper : ringKrullDim Sg ≤ P.dimension := by
      calc
        ringKrullDim Sg ≤ ringKrullDim S :=
          ringKrullDim_localizationAway_le (Sg := Sg) g
        _ = P.dimension := hP
    have hbot : ringKrullDim Sg ≠ ⊥ := by
      -- The nontrivial localization has nonnegative Krull dimension, hence not `⊥`.
      intro hbot'
      simpa [hbot'] using (ringKrullDim_nonneg_of_nontrivial (R := Sg))
    have htop : ringKrullDim Sg ≠ ⊤ := by
      -- The existing upper bound shows that the dimension is finite.
      exact ne_of_lt <| lt_of_le_of_lt hupper <|
        WithBot.coe_lt_coe.mpr (ENat.coe_lt_top P.dimension)
    let d : ℕ := ((ringKrullDim Sg).unbot hbot).toNat
    have hdim : ringKrullDim Sg = d := by
      -- Replace the finite `WithBot ℕ∞` dimension by its natural-number value.
      have hneTop : (ringKrullDim Sg).unbot hbot ≠ ⊤ := by
        intro h
        exact htop (by
          simpa [WithBot.coe_unbot] using
            congrArg (fun x : ℕ∞ ↦ (x : WithBot ℕ∞)) h)
      have hdim' : ((ringKrullDim Sg).unbot hbot : WithBot ℕ∞) = d := by
        simpa [d] using
          congrArg (fun x : ℕ∞ ↦ (x : WithBot ℕ∞)) (ENat.coe_toNat hneTop).symm
      calc
        ringKrullDim Sg = (ringKrullDim Sg).unbot hbot := by
          exact (WithBot.coe_unbot (ringKrullDim Sg) hbot).symm
        _ = d := hdim'
    have hrelation :
        ((Fintype.card (Unit ⊕ Fin n) : ℕ) : WithBot ℕ∞) ≤
          ringKrullDim Sg + Fintype.card (Unit ⊕ Fin c) :=
      localized_comp_presentation_relation_bound (Sg := Sg) g P
    have hupper_nat : d ≤ P.dimension := by
      simpa [hdim] using hupper
    have hrelation_nat : n ≤ d + c := by
      -- Reassociate the localized bound into the standard `n + 1 ≤ (d + c) + 1` form and then
      -- strip the final `+ 1`.
      have hrelation' :
          ((n : ℕ) : WithBot ℕ∞) + 1 ≤ ((d : ℕ) : WithBot ℕ∞) + (c + 1) := by
        simpa [hdim, Fintype.card_sum, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm,
          ← WithBot.coe_add] using hrelation
      have hrelation'' :
          ((n : ℕ) : WithBot ℕ∞) + 1 ≤ (d + c : WithBot ℕ∞) + 1 := by
        simpa [← WithBot.coe_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hrelation'
      have hlt : (n : WithBot ℕ∞) < (d + c : WithBot ℕ∞) + 1 :=
        ENat.WithBot.add_one_le_iff.mp hrelation''
      have hle : ((n : ℕ) : WithBot ℕ∞) ≤ ((d : ℕ) : WithBot ℕ∞) + c := by
        simpa using (ENat.WithBot.lt_add_one_iff).mp hlt
      have hle' :
          (((n : ℕ) : ℕ∞) : WithBot ℕ∞) ≤ (((d + c : ℕ) : ℕ∞) : WithBot ℕ∞) := by
        simpa [← WithBot.coe_add, Nat.cast_add] using hle
      have hle_enat : (n : ℕ∞) ≤ (d + c : ℕ∞) := WithBot.coe_le_coe.mp hle'
      rwa [← ENat.coe_add, ENat.coe_le_coe] at hle_enat
    have hd_eq : d = P.dimension := by
      -- Source arithmetic: `n ≤ d + c` and `d ≤ n - c` force equality.
      have hPdim : P.dimension = n - c := presentation_dimension_eq_fin_sub P
      omega
    have hdim_eq : ringKrullDim Sg = P.dimension := by
      simpa [hd_eq] using hdim
    -- Rewrite the localized presentation dimension back to the original one.
    exact le_of_eq <| by
      rw [localized_comp_presentation_dimension (Sg := Sg) g P]
      exact hdim_eq.symm

-- Proof sketch: unwrap the source-facing owner witness
-- `IsGlobalCompleteIntersection.presentation_or_subsingleton`. The subsingleton convention is
-- preserved by any away-localization target `Sg`, and a presentation witness localizes along the
-- principal open subset without changing the presentation dimension.

/-- Lemma 10.135.2 (1): if a finite type `k`-algebra `S` is a global complete intersection, then
any away localization `Sg` of `S` at `g` is again a global complete intersection. The textbook
ring `S_g` is the special case `Sg = Localization.Away g`. -/
@[stacks 00SA]
theorem of_isLocalizationAway (g : S) (hS : IsGlobalCompleteIntersection k S)
    [IsLocalization.Away g Sg] : IsGlobalCompleteIntersection k Sg := by
  let _ : IsGlobalCompleteIntersection k S := hS
  refine ⟨?_⟩
  rcases hS.presentation_or_subsingleton with hsub | ⟨n, c, P, hP⟩
  · -- In the zero-ring convention, the away localization is again subsingleton.
    exact Or.inl <| by
      let _ : Subsingleton S := hsub
      have h01 : (0 : S) = 1 := Subsingleton.elim _ _
      have hzero : (0 : S) ∈ Submonoid.powers g := by
        rw [h01]
        exact Submonoid.one_mem _
      exact IsLocalization.subsingleton (S := Sg) hzero
  · by_cases hSg : Subsingleton Sg
    · -- If the localization collapses to the zero ring, the convention closes the proof.
      exact Or.inl hSg
    · -- Otherwise, use the localized presentation from the source proof.
      letI : Nontrivial Sg := not_subsingleton_iff_nontrivial.mp hSg
      refine Or.inr ⟨Fintype.card (Unit ⊕ Fin n), Fintype.card (Unit ⊕ Fin c),
        localized_comp_presentation (Sg := Sg) g P, ?_⟩
      -- The entire remaining numerical content is isolated in the presentation-localized helper.
      exact ringKrullDim_localized_comp_presentation (Sg := Sg) g P hP

end IsGlobalCompleteIntersection

namespace IsLocalCompleteIntersection

variable {Sg : Type w} [CommRing Sg] [Algebra S Sg] [Algebra k Sg] [IsScalarTower k S Sg]

open Finset

variable (Sg) in
/-- Helper for Lemma 10.135.2: the canonical map from a chart to its further localization away
from the image of `h` defines the needed algebra structure. -/
noncomputable abbrev away_chart_algebra (g h : S) [IsLocalization.Away g Sg] :
    Algebra (Localization.Away h) (Localization.Away (algebraMap S Sg h)) :=
  (IsLocalization.Away.map _ _ (algebraMap S Sg) h).toAlgebra

variable (Sg) in
/-- Helper for Lemma 10.135.2: mapping a finite basic-open cover along an away-localization map
preserves the unit-ideal condition. -/
lemma image_span_eq_top_of_isLocalizationAway
    (g : S) [IsLocalization.Away g Sg] [DecidableEq Sg] (s : Finset S)
    (hs : Ideal.span (s : Set S) = ⊤) :
    Ideal.span ((s.image (algebraMap S Sg) : Finset Sg) : Set Sg) = ⊤ := by
  -- Transport the span equality through the localization algebra map.
  calc
    Ideal.span ((s.image (algebraMap S Sg) : Finset Sg) : Set Sg)
        = Ideal.map (algebraMap S Sg) (Ideal.span (s : Set S)) := by
          simp [Finset.coe_image, Ideal.map_span]
    _ = Ideal.map (algebraMap S Sg) ⊤ := by rw [hs]
    _ = ⊤ := Ideal.map_top _

variable (Sg) in
/-- Helper for Lemma 10.135.2: localizing a global-complete-intersection chart once more along the
image of `g` stays a global complete intersection. -/
lemma global_completeIntersection_chart_of_localized_chart
    (g h : S) [IsLocalization.Away g Sg]
    (hh : IsGlobalCompleteIntersection k (Localization.Away h)) :
    IsGlobalCompleteIntersection k (Localization.Away (algebraMap S Sg h)) := by
  let _ : Algebra (Localization.Away h) (Localization.Away (algebraMap S Sg h)) :=
    away_chart_algebra (Sg := Sg) g h
  have hcomp :
      (algebraMap (Localization.Away h) (Localization.Away (algebraMap S Sg h))).comp
          (algebraMap S (Localization.Away h)) =
        (algebraMap Sg (Localization.Away (algebraMap S Sg h))).comp (algebraMap S Sg) := by
    -- This is the standard compatibility of the iterated-away-localization square.
    simp [RingHom.algebraMap_toAlgebra, IsLocalization.Away.map]
  have htower : IsScalarTower S (Localization.Away h) (Localization.Away (algebraMap S Sg h)) := by
    -- Repackage the compatibility square as the scalar-tower identity needed by the global lemma.
    apply IsScalarTower.of_algebraMap_eq
    intro x
    simp [RingHom.algebraMap_toAlgebra, IsLocalization.Away.map,
      ← IsScalarTower.algebraMap_apply]
  let _ : IsScalarTower S (Localization.Away h) (Localization.Away (algebraMap S Sg h)) := htower
  have hkTower : IsScalarTower k (Localization.Away h) (Localization.Away (algebraMap S Sg h)) := by
    -- The `k`-algebra structure factors through the same chart map.
    apply IsScalarTower.of_algebraMap_eq
    intro x
    have hx :=
      congrArg
        (fun f : S →+* Localization.Away (algebraMap S Sg h) ↦ f ((algebraMap k S) x))
        hcomp
    simpa [← IsScalarTower.algebraMap_apply] using hx.symm
  let _ : IsScalarTower k (Localization.Away h) (Localization.Away (algebraMap S Sg h)) := hkTower
  let _ : IsLocalization.Away (algebraMap S (Localization.Away h) g)
      (Localization.Away (algebraMap S Sg h)) :=
    IsLocalization.Away.commutes _ Sg (Localization.Away (algebraMap S Sg h)) h g
  -- Reapply the global complete-intersection permanence result to the localized chart.
  simpa using
    (IsGlobalCompleteIntersection.of_isLocalizationAway
      (k := k) (S := Localization.Away h)
      (Sg := Localization.Away (algebraMap S Sg h))
      (algebraMap S (Localization.Away h) g) hh)

-- Proof sketch: unwrap the owner field
-- `IsLocalCompleteIntersection.exists_basicOpen_cover`. Localizing the finite basic-open cover to
-- an arbitrary away-localization target `Sg` preserves the unit-ideal condition, and each chart
-- remains a global complete intersection by
-- `IsGlobalCompleteIntersection.of_isLocalizationAway`.

/-- Lemma 10.135.2 (2): if a finite type `k`-algebra `S` is a local complete intersection, then
any away localization `Sg` of `S` at `g` is again a local complete intersection. The textbook
ring `S_g` is the special case `Sg = Localization.Away g`. -/
@[stacks 00SA]
theorem of_isLocalizationAway (g : S) (hS : IsLocalCompleteIntersection k S)
    [IsLocalization.Away g Sg] : IsLocalCompleteIntersection k Sg := by
  let _ : IsLocalCompleteIntersection k S := hS
  classical
  rcases hS.exists_basicOpen_cover with ⟨s, hs, hglobal⟩
  refine ⟨s.image (algebraMap S Sg),
    image_span_eq_top_of_isLocalizationAway (Sg := Sg) g s hs, ?_⟩
  intro h' hh'
  rcases mem_image.mp hh' with ⟨h, hh, rfl⟩
  -- Each localized chart is the further localization of an original global-CI chart.
  exact global_completeIntersection_chart_of_localized_chart
    (Sg := Sg) g h (hglobal h hh)

end IsLocalCompleteIntersection

instance (g : S)
    [hS : IsGlobalCompleteIntersection k S] :
    IsGlobalCompleteIntersection k (Localization.Away g) :=
  IsGlobalCompleteIntersection.of_isLocalizationAway g hS

instance (g : S)
    [hS : IsLocalCompleteIntersection k S] :
    IsLocalCompleteIntersection k (Localization.Away g) :=
  IsLocalCompleteIntersection.of_isLocalizationAway g hS

end
