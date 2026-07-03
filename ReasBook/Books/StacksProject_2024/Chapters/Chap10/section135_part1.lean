import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_10_135_1 (from Chap10) -/
universe u v

variable {k : Type u} [Field k]
variable {S : Type v} [CommRing S] [Algebra k S]

/-
Source/core/bridge triage:
* source-facing: `IsGlobalCompleteIntersection k S` and `IsLocalCompleteIntersection k S`, the
  textbook field-algebra notions from Definition 10.135.1;
* core/canonical: finite algebra presentations `Algebra.Presentation k S (Fin n) (Fin c)` and the
  canonical finiteness owner `Algebra.FinitePresentation k S`;
* bridge/view: the quotient-presentation reformulation
  `IsGlobalCompleteIntersection.quotientPresentation_or_subsingleton`.

Primitive data for the global notion are presentation-level: either the zero-ring convention holds,
or there is a finite presentation whose presentation dimension matches `dim S`.
`Algebra.FinitePresentation k S` is derived from that source-facing data, while the quotient model
is bridge API only.
-/
/-- Definition 10.135.1 (1): a finite type `k`-algebra `S` is a global complete intersection over
`k` if either `S` is subsingleton (the zero-ring convention) or `S` admits a finite algebra
presentation whose presentation dimension equals `dim S`. For a presentation indexed by
`Fin n` generators and `Fin c` relations, this is the textbook condition `dim S = n - c`. -/
class IsGlobalCompleteIntersection (k : Type u) (S : Type v) [Field k] [CommRing S] [Algebra k S] :
    Prop where
  presentation_or_subsingleton :
    Subsingleton S ∨
      ∃ (n c : ℕ) (P : Algebra.Presentation k S (Fin n) (Fin c)),
        ringKrullDim S = P.dimension

namespace IsGlobalCompleteIntersection

/-- The global complete-intersection condition is invariant under `k`-algebra equivalence. -/
theorem of_algEquiv {T : Type*} [CommRing T] [Algebra k T]
    (hS : IsGlobalCompleteIntersection k S) (e : S ≃ₐ[k] T) :
    IsGlobalCompleteIntersection k T where
  presentation_or_subsingleton := by
    rcases hS.presentation_or_subsingleton with hsub | ⟨n, c, P, hP⟩
    · left
      exact ⟨fun x y ↦ by
        simpa using congrArg e (Subsingleton.elim (e.symm x) (e.symm y))⟩
    · right
      refine ⟨n, c, P.ofAlgEquiv e, ?_⟩
      calc
        ringKrullDim T = ringKrullDim S := by
          simpa using (ringKrullDim_eq_of_ringEquiv e.toRingEquiv).symm
        _ = P.dimension := hP
        _ = (P.ofAlgEquiv e).dimension := by
          exact_mod_cast (P.dimension_ofAlgEquiv e).symm

end IsGlobalCompleteIntersection

instance [h : IsGlobalCompleteIntersection k S] : Algebra.FinitePresentation k S := by
  rcases h.presentation_or_subsingleton with hS | ⟨n, c, P, _⟩
  · let _ : Subsingleton S := hS
    have hsurj : Function.Surjective (Algebra.ofId k S) := fun x ↦ ⟨0, Subsingleton.elim _ _⟩
    have hker : (RingHom.ker (algebraMap k S)).FG := by
      simpa [RingHom.ker_eq_top_of_subsingleton (algebraMap k S)] using Ideal.fg_top k
    have hfp' : (Algebra.ofId k S).FinitePresentation :=
      AlgHom.FinitePresentation.of_surjective (Algebra.ofId k S) hsurj <| by
        simpa [Algebra.toRingHom_ofId] using hker
    have hfp : (algebraMap k S).FinitePresentation := by
      simpa [AlgHom.FinitePresentation, Algebra.toRingHom_ofId] using hfp'
    exact (RingHom.finitePresentation_algebraMap).mp hfp
  · simpa using P.finitePresentation_of_isFinite

/-- Helper for Definition 10.135.1: a finite presentation identifies `S` with the quotient by the
span of its defining relations. -/
theorem presentation_relation_quotient_model {n c : ℕ}
    (P : Algebra.Presentation k S (Fin n) (Fin c)) :
    Nonempty ((MvPolynomial (Fin n) k ⧸ Ideal.span (Set.range P.relation)) ≃ₐ[k] S) := by
  -- Transport the quotient from the explicit span of relations to the kernel-based presentation.
  refine ⟨?_⟩
  exact (Ideal.quotientEquivAlgOfEq k P.span_range_relation_eq_ker).trans
    (P.quotientEquiv.restrictScalars k)

/-- Helper for Definition 10.135.1: a presentation with `Fin n` generators and `Fin c` relations
has presentation dimension `n - c`. -/
lemma presentation_dimension_eq_fin_sub {n c : ℕ}
    (P : Algebra.Presentation k S (Fin n) (Fin c)) :
    P.dimension = n - c := by
  -- Unfold presentation dimension and evaluate the cardinalities of the finite index sets.
  simpa [Algebra.Presentation.dimension]

/-- Textbook quotient-presentation form of `IsGlobalCompleteIntersection`. -/
theorem IsGlobalCompleteIntersection.quotientPresentation_or_subsingleton
    [IsGlobalCompleteIntersection k S] :
    Subsingleton S ∨
      ∃ (n c : ℕ) (f : Fin c → MvPolynomial (Fin n) k),
        Nonempty ((MvPolynomial (Fin n) k ⧸ Ideal.span (Set.range f)) ≃ₐ[k] S) ∧
          ringKrullDim S = n - c := by
  rcases (inferInstance : IsGlobalCompleteIntersection k S).presentation_or_subsingleton with
    hsub | ⟨n, c, P, hdim⟩
  · -- The zero-ring convention is one branch of the definition itself.
    exact Or.inl hsub
  · -- In the genuine presentation branch, reuse the chosen presentation data directly.
    refine Or.inr ⟨n, c, P.relation, presentation_relation_quotient_model P, ?_⟩
    -- Rewrite the stored presentation dimension into the textbook count `n - c`.
    rw [presentation_dimension_eq_fin_sub P] at hdim
    exact hdim

-- Proof sketch: the convention in the source declares every subsingleton `k`-algebra, hence in
-- particular the zero ring, to be a global complete intersection.
/-- Subsingleton `k`-algebras are global complete intersections by convention. -/
instance [Subsingleton S] : IsGlobalCompleteIntersection k S where
  presentation_or_subsingleton := .inl inferInstance

/-- Definition 10.135.1 (2): a `k`-algebra `S` is a local complete intersection over `k` if
`Spec(S)` is covered by finitely many basic opens `D(g)` such that each localization `S[g⁻¹]` is
a global complete intersection over `k`; algebraically, the cover is encoded by
`Ideal.span (s : Set S) = ⊤`. This cover condition already implies finite presentation, hence
finite type, by the standard locality theorem for `Algebra.FinitePresentation`. -/
class IsLocalCompleteIntersection (k : Type u) (S : Type v) [Field k] [CommRing S]
    [Algebra k S] : Prop where
  exists_basicOpen_cover :
    ∃ s : Finset S,
      Ideal.span (s : Set S) = ⊤ ∧
        ∀ g ∈ s, IsGlobalCompleteIntersection k (Localization.Away g)

instance [h : IsLocalCompleteIntersection k S] : Algebra.FinitePresentation k S := by
  rcases h.exists_basicOpen_cover with ⟨s, hs, hglobal⟩
  letI (g : s) : IsGlobalCompleteIntersection k (Localization.Away (g : S)) := hglobal g g.2
  letI (g : s) : Algebra.FinitePresentation k (Localization.Away (g : S)) := inferInstance
  exact Algebra.FinitePresentation.of_span_eq_top_target_of_isLocalizationAway
    (fun g : s ↦ (g : S)) (by simpa using hs) (fun g : s ↦ Localization.Away (g : S))

-- Proof sketch: take the single basic open `D(1) = Spec(S)`, whose localization is canonically
-- `S`, and apply the global complete intersection hypothesis.
/-- Every global complete intersection is a local complete intersection. -/
instance [IsGlobalCompleteIntersection k S] :
    IsLocalCompleteIntersection k S where
  exists_basicOpen_cover := by
    refine ⟨{1}, by simp, ?_⟩
    intro g hg
    have hg1 : g = (1 : S) := by simpa using hg
    subst hg1
    simpa using IsGlobalCompleteIntersection.of_algEquiv
      ‹IsGlobalCompleteIntersection k S›
      ((IsLocalization.atOne S (Localization.Away (1 : S))).restrictScalars k)

/-! ### Lemma_10_135_2 (from Chap10) -/
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

/-! ### Lemma_10_135_3 (from Chap10) -/
universe u v

section

variable {k : Type u} [Field k]
variable {S : Type v} [CommRing S] [Algebra k S]

/-
Domain-style sampling in the local-complete-intersection / Cohen-Macaulay interface:
- primary domain: commutative algebra of local complete intersections over a field and the
  resulting global Cohen-Macaulay ring property;
- sampled owner declarations:
  `IsLocalCompleteIntersection`,
  `IsGlobalCompleteIntersection`,
  `Module.LocallyCohenMacaulay`,
  `CohenMacaulayRing`;
- best owner abstraction: this file is a `bridge/view` from the source-facing field-algebra owner
  `IsLocalCompleteIntersection k S` to the chapter-global ring owner `CohenMacaulayRing S`;
- primitive data: only the owner hypothesis `hCI : IsLocalCompleteIntersection k S`;
- derived API: finite presentation and hence finite type of `S`, together with the primewise
  Cohen-Macaulay self-module statements packaged by `CohenMacaulayRing`.

Source/core/bridge triage:
* source-facing: Lemma `10.135.3`, asserting that a local complete intersection over a field is a
  Cohen-Macaulay ring;
* core/canonical: `IsLocalCompleteIntersection k S`, `Module.LocallyCohenMacaulay S S`, and
  `CohenMacaulayRing S`;
* bridge/view: passage to each localization `Localization.AtPrime q.asIdeal`, where the local
  complete-intersection hypothesis becomes a complete-intersection local ring and hence a
  Cohen-Macaulay self-module.

The public theorem should therefore take the source-level hypothesis explicitly and return the
global owner `CohenMacaulayRing S` directly, rather than hide the main input in an instance
argument.
-/
-- Proof sketch: for each prime `p` of `S`, localize at `p`. A local complete intersection over a
-- field stays a local complete intersection after localization, so `Sₚ` admits a presentation by
-- quotienting a regular local ring by a regular sequence. Regular local rings are
-- Cohen-Macaulay, and quotienting a Cohen-Macaulay local ring by a regular sequence remains
-- Cohen-Macaulay. Hence every prime localization of `S` is Cohen-Macaulay, which is exactly the
-- global `CohenMacaulayRing` condition. The theorem header does not repeat a separate finite-type
-- or Noetherian hypothesis, since that data is derived from `hCI`.
/-- Lemma 10.135.3: a finite type `k`-algebra that is a local complete intersection over `k` is a
Cohen-Macaulay ring. -/
theorem cohenMacaulayRing_of_isLocalCompleteIntersection
    (hCI : IsLocalCompleteIntersection k S) : CohenMacaulayRing S := by
  let _ : IsLocalCompleteIntersection k S := hCI
  sorry

end

/-! ### Lemma_10_135_4 (from Chap10) -/
noncomputable section

open Algebra Algebra.Extension RingTheory Sequence IsLocalRing

universe u v

section

variable {k : Type u} [Field k]
variable {S : Type v} [CommRing S] [Algebra k S]
variable {n c : ℕ}

/-- Some basic open neighbourhood of `q` is a global complete intersection over `k`. -/
abbrev isGlobalCompleteIntersectionNearPrime
    (K : Type u) [Field K] {S : Type v} [CommRing S] [Algebra K S] (q : PrimeSpectrum S) : Prop :=
  ∃ g : S, g ∉ q.asIdeal ∧ IsGlobalCompleteIntersection K (Localization.Away g)

/-- Some basic open neighbourhood of `q` is a local complete intersection over `k`. -/
abbrev isLocalCompleteIntersectionNearPrime
    (K : Type u) [Field K] {S : Type v} [CommRing S] [Algebra K S] (q : PrimeSpectrum S) : Prop :=
  ∃ g : S, g ∉ q.asIdeal ∧ IsLocalCompleteIntersection K (Localization.Away g)

namespace PolynomialPresentationAtPrime

/-- The prime of the chosen polynomial presentation lying over `q`. -/
abbrev prime
    (π : MvPolynomial (Fin n) k →ₐ[k] S) (q : PrimeSpectrum S) :
    PrimeSpectrum (MvPolynomial (Fin n) k) :=
  PrimeSpectrum.comap π.toRingHom q

/-- The localization of the polynomial ring at the prime lying over `q`. -/
abbrev localRing
    (π : MvPolynomial (Fin n) k →ₐ[k] S) (q : PrimeSpectrum S) : Type u :=
  Localization.AtPrime (prime π q).asIdeal

/-- The localized kernel ideal `I_{q'}` of the chosen polynomial presentation. -/
abbrev localizedKernelIdeal
    (π : MvPolynomial (Fin n) k →ₐ[k] S) (q : PrimeSpectrum S) :
    Ideal (localRing π q) :=
  Ideal.map
    (algebraMap (MvPolynomial (Fin n) k) (localRing π q))
    (RingHom.ker π.toRingHom)

/-- The quotient local ring `k[x₁, …, xₙ]_{q'} / I_{q'}` canonically modeling `S_q`. -/
abbrev localQuotientRing
    (π : MvPolynomial (Fin n) k →ₐ[k] S) (q : PrimeSpectrum S) :
    Type _ :=
  localRing π q ⧸ localizedKernelIdeal π q

/-- The localized conormal module `(I_{q'} / I_{q'}²)` of the localized kernel ideal. -/
abbrev localizedConormalModule
    (π : MvPolynomial (Fin n) k →ₐ[k] S) (q : PrimeSpectrum S) :
    Type _ :=
  (localizedKernelIdeal π q).Cotangent

/-- The localized kernel ideal of the chosen presentation is generated by `c` elements. -/
abbrev kernelGeneratedByCondition
    (π : MvPolynomial (Fin n) k →ₐ[k] S) (q : PrimeSpectrum S) (c : ℕ) : Prop :=
  ∃ xs : Fin c → localRing π q,
    Ideal.span (Set.range xs) = localizedKernelIdeal π q

/-- The localized conormal module of the chosen presentation is generated by `c` elements. -/
abbrev conormalGeneratedByCondition
    (π : MvPolynomial (Fin n) k →ₐ[k] S) (q : PrimeSpectrum S) (c : ℕ) : Prop :=
  ∃ xs : Fin c → localizedConormalModule π q,
    Submodule.span (localQuotientRing π q) (Set.range xs) = ⊤

/-- The localized conormal module of the chosen presentation is free of rank `c` over the
canonical quotient model `k[x₁, …, xₙ]_{q'} / I_{q'}` of `S_q`. -/
abbrev conormalFreeCondition
    (π : MvPolynomial (Fin n) k →ₐ[k] S) (q : PrimeSpectrum S) (c : ℕ) : Prop :=
  Nonempty
    (Module.Basis (Fin c) (localQuotientRing π q) (localizedConormalModule π q))

/-- The localized kernel ideal of the chosen presentation is generated by a regular sequence of
length `c`. -/
abbrev kernelGeneratedByRegularSequenceCondition
    (π : MvPolynomial (Fin n) k →ₐ[k] S) (q : PrimeSpectrum S) (c : ℕ) : Prop :=
  ∃ xs : Fin c → localRing π q,
    Sequence.IsRegular (localRing π q) (List.ofFn xs) ∧
      Ideal.span (Set.range xs) = localizedKernelIdeal π q

-- Proof sketch: localize the chosen polynomial presentation `π` at the prime
-- `q' = PrimeSpectrum.comap π.toRingHom q`. The localized polynomial ring is regular local, hence
-- Cohen-Macaulay, and the height hypothesis identifies the codimension with `c`. Then use
-- Nakayama, the Cohen-Macaulay criterion for ideals generated by `c` elements, freeness of the
-- conormal module for complete intersections, and the comparison between local complete
-- intersections and global complete intersections on a basic open neighbourhood of `q`.
/-- Lemma 10.135.4 (1): let `k` be a field, let `S` be a finite type `k`-algebra, let
`π : k[x₁, …, xₙ] → S` be a surjective polynomial presentation, and let `q : PrimeSpectrum S`.
Write `q' = PrimeSpectrum.comap π.toRingHom q` and assume that
`q'.asIdeal.height - q.asIdeal.height = c`. Then the following are equivalent: some basic open
neighbourhood of `q` is a global complete intersection over `k`; the localized kernel ideal
`I_{q'}` is generated by `c` elements; the localized conormal module
`I_{q'} / I_{q'}²` is generated by `c` elements over the quotient local ring
`k[x₁, …, xₙ]_{q'} / I_{q'}`; the same conormal module is free of rank `c`; and the localized
kernel ideal `I_{q'}` is generated by a regular sequence in the local ring
`k[x₁, …, xₙ]_{q'}`. -/
theorem tfae
    (π : MvPolynomial (Fin n) k →ₐ[k] S) (_ : Function.Surjective π) (q : PrimeSpectrum S)
    (hc : (prime π q).asIdeal.height - q.asIdeal.height = c) :
    List.TFAE
      [ isGlobalCompleteIntersectionNearPrime k q
      , kernelGeneratedByCondition π q c
      , conormalGeneratedByCondition π q c
      , conormalFreeCondition π q c
      , kernelGeneratedByRegularSequenceCondition π q c
      ] := sorry

-- Proof sketch: by the equivalence in part (1), the localized kernel ideal is generated by a
-- regular sequence of length `c`. In a local ring, any `c` generators of the same ideal are a
-- minimal generating family, hence have the same images modulo the maximal-ideal multiple by
-- Nakayama, and the Cohen-Macaulay complete-intersection criterion upgrades them to a regular
-- sequence as well.
/-- Lemma 10.135.4 (2): in the situation of part (1), if the localized kernel ideal `I_{q'}` is
generated by a regular sequence of length `c`, then any other family of `c` generators of
`I_{q'}` is again a regular sequence in the local ring `k[x₁, …, xₙ]_{q'}`. This is the
library-facing form of the textbook statement that any `c` elements generating
`I_{q'} / q' I_{q'}` form a regular sequence. -/
theorem generators_form_regularSequence
    (π : MvPolynomial (Fin n) k →ₐ[k] S) (q : PrimeSpectrum S)
    (hreg : kernelGeneratedByRegularSequenceCondition π q c)
    (xs : Fin c → localRing π q)
    (hxs : Ideal.span (Set.range xs) = localizedKernelIdeal π q) :
    Sequence.IsRegular (localRing π q) (List.ofFn xs) := sorry

end PolynomialPresentationAtPrime

end

/-! ### Definition_10_135_5 (from Chap10) -/
universe u v w

open Ideal RingTheory Sequence IsLocalRing

namespace RingHom

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- The kernel of a ring homomorphism is generated by a regular sequence in the source ring. -/
def KernelIsGeneratedByRegularSequence (f : R →+* S) : Prop :=
  ∃ fs : List R, IsRegular R fs ∧ Ideal.ofList fs = RingHom.ker f

end RingHom

namespace Ideal

variable {R : Type u} [CommRing R]

/-- An ideal is generated by a regular sequence in the ambient ring. -/
abbrev IsGeneratedByRegularSequence (I : Ideal R) : Prop :=
  (Ideal.Quotient.mk I).KernelIsGeneratedByRegularSequence

theorem isGeneratedByRegularSequence_iff (I : Ideal R) :
    I.IsGeneratedByRegularSequence ↔ ∃ fs : List R, IsRegular R fs ∧ Ideal.ofList fs = I := by
  constructor
  · rintro ⟨fs, hfs, hker⟩
    exact ⟨fs, hfs, hker.trans Ideal.mk_ker⟩
  · rintro ⟨fs, hfs, hI⟩
    exact ⟨fs, hfs, hI.trans Ideal.mk_ker.symm⟩

end Ideal

namespace Algebra

/-- Definition 10.135.5: a local `k`-algebra `S` essentially of finite type over `k` is a
complete intersection over `k` if there exists a regular local `k`-algebra `R` essentially of
finite type over `k` with a surjective `k`-algebra map `R → S` whose kernel is generated by a
regular sequence. The quotient model `S ≃ₐ[k] R ⧸ ker π` is derived from this primitive
presentation data, and in a local ring the condition `fs ⊆ maximalIdeal R` is recovered
internally from regularity rather than stored as owner data. -/
class IsCompleteIntersectionOver (k : Type u) (S : Type v) [Field k] [CommRing S] [Algebra k S] :
    Prop where
  exists_presentation :
    ∃ (R : Type (max u v w)) (_ : CommRing R) (_ : Algebra k R) (_ : Algebra.EssFiniteType k R)
      (_ : IsRegularLocalRing R) (π : R →ₐ[k] S),
        Function.Surjective π ∧
          π.toRingHom.KernelIsGeneratedByRegularSequence

section

variable {k : Type u} {S : Type v} [Field k] [CommRing S] [Algebra k S]

instance instEssFiniteTypeOfIsCompleteIntersectionOver
    [h : IsCompleteIntersectionOver.{u, v, w} k S] : Algebra.EssFiniteType k S := by
  rcases h.exists_presentation with ⟨R, _, _, _, _, π, hπ, ⟨fs, _, hfs⟩⟩
  let e : (R ⧸ Ideal.ofList fs) ≃ₐ[k] S := by
    exact (Ideal.quotientEquivAlgOfEq k hfs).trans (Ideal.quotientKerAlgEquivOfSurjective hπ)
  let _ : Algebra.EssFiniteType k (R ⧸ Ideal.ofList fs) := inferInstance
  exact (Algebra.EssFiniteType.iff_of_algEquiv e).mp inferInstance

theorem isLocalRing_of_isCompleteIntersectionOver
    [h : IsCompleteIntersectionOver.{u, v, w} k S] : IsLocalRing S := by
  rcases h.exists_presentation with ⟨R, _, _, _, _, π, hπ, ⟨fs, hfs, hker⟩⟩
  let e : (R ⧸ Ideal.ofList fs) ≃ₐ[k] S := by
    exact (Ideal.quotientEquivAlgOfEq k hker).trans (Ideal.quotientKerAlgEquivOfSurjective hπ)
  have hproper : Ideal.ofList fs ≠ ⊤ := by
    intro htop
    exact hfs.top_ne_smul <| by
      simp [htop]
  have : Nontrivial (R ⧸ Ideal.ofList fs) := Quotient.nontrivial_iff.mpr hproper
  have : IsLocalRing (R ⧸ Ideal.ofList fs) :=
    IsLocalRing.of_surjective'
      (Ideal.Quotient.mk (Ideal.ofList fs))
      Ideal.Quotient.mk_surjective
  let e' : (R ⧸ Ideal.ofList fs) ≃+* S := e.toRingEquiv
  exact e'.isLocalRing

end

section

variable {k : Type u} {S : Type v} [Field k] [CommRing S] [Algebra k S]
variable [Algebra.EssFiniteType k S]

-- Proof sketch: take `R = S` and the empty regular sequence. A regular local ring is already a
-- regular local presentation of itself, and `S ⧸ Ideal.ofList []` identifies with `S`.
/-- A regular local `k`-algebra essentially of finite type over `k` is a complete intersection
over `k`. -/
instance instIsCompleteIntersectionOverOfIsRegularLocalRing [IsRegularLocalRing S] :
    IsCompleteIntersectionOver.{u, v, w} k S where
  exists_presentation := by
    let e : ULift.{max u w} S ≃ₐ[k] S := ULift.algEquiv
    let π : ULift.{max u w} S →ₐ[k] S := e.toAlgHom
    let _ : Algebra.EssFiniteType k (ULift.{max u w} S) :=
      (Algebra.EssFiniteType.iff_of_algEquiv e).2 inferInstance
    let _ : IsRegularLocalRing (ULift.{max u w} S) :=
      IsRegularLocalRing.of_ringEquiv e.toRingEquiv.symm
    refine ⟨ULift.{max u w} S, inferInstance, inferInstance, inferInstance, inferInstance, π, ?_,
      ?_⟩
    · exact e.surjective
    · refine ⟨[], ?_, ?_⟩
      · simpa using (IsRegular.nil (ULift.{max u w} S) (ULift.{max u w} S))
      · rw [Ideal.ofList_nil]
        exact ((RingHom.injective_iff_ker_eq_bot π.toRingHom).mp e.injective).symm

end

end Algebra

/-! ### Lemma_10_135_6 (from Chap10) -/
universe u v w

open IsLocalRing

section

variable {A : Type u} {B : Type v} {C : Type w}
variable [CommRing A] [CommRing B] [CommRing C]
variable [IsRegularLocalRing A] [IsRegularLocalRing B] [IsLocalRing C]

/-- Helper for Lemma 10.135.6: the ideal generated by a finite family is the span of its range. -/
private theorem ideal_ofList_ofFn_eq_span_range {R : Type*} [CommRing R] {d : ℕ}
    (x : Fin d → R) :
    Ideal.ofList (List.ofFn x) = Ideal.span (Set.range x) := by
  -- Proof comment: `List.ofFn` and `Set.range` encode the same finite family.
  rw [Ideal.ofList]
  congr
  ext r
  constructor
  · intro hr
    rcases List.mem_ofFn.mp hr with ⟨i, rfl⟩
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact List.mem_ofFn.mpr ⟨i, rfl⟩

/-- Helper for Lemma 10.135.6: the range of an appended `Fin`-family is the union of the two
original ranges. -/
private theorem range_fin_append {α : Type*} {m n : ℕ} (x : Fin m → α) (y : Fin n → α) :
    Set.range (Fin.append x y) = Set.range x ∪ Set.range y := by
  ext a
  constructor
  · rintro ⟨i, rfl⟩
    refine Fin.addCases ?_ ?_ i
    · intro j
      exact Or.inl ⟨j, by simpa using Fin.append_left x y j⟩
    · intro j
      exact Or.inr ⟨j, by simpa using Fin.append_right x y j⟩
  · rintro (ha | ha)
    · rcases ha with ⟨i, rfl⟩
      exact ⟨Fin.castAdd n i, by simpa using Fin.append_left x y i⟩
    · rcases ha with ⟨i, rfl⟩
      exact ⟨Fin.natAdd m i, by simpa using Fin.append_right x y i⟩

/-- Helper for Lemma 10.135.6: over a surjective local map from a regular local ring, kernel
generation by a regular sequence is equivalent to having a finite generating family whose
cardinality matches the Krull-dimension drop. -/
private theorem kernel_generatedByRegularSequence_iff_exists_dim_span_eq_ker
    {R : Type*} {S : Type*} [CommRing R] [CommRing S]
    [IsRegularLocalRing R] [IsLocalRing S]
    (f : R →+* S) [IsLocalHom f] (hsurj : Function.Surjective f) :
    f.KernelIsGeneratedByRegularSequence ↔
      ∃ (d : ℕ) (_ : ringKrullDim S + d = ringKrullDim R) (x : Fin d → R),
        Ideal.span (Set.range x) = RingHom.ker f := by
  constructor
  · rintro ⟨fs, hfs_reg, hfs_ker⟩
    have hker_le_max : RingHom.ker f ≤ maximalIdeal R :=
      IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top f)
    have hfs_mem : ∀ r ∈ fs, r ∈ maximalIdeal R := by
      intro r hr
      apply hker_le_max
      rw [← hfs_ker, Ideal.ofList]
      exact Ideal.subset_span hr
    have hdim_quot :
        ringKrullDim (R ⧸ Ideal.ofList fs) + fs.length = ringKrullDim R :=
      (isRegular_iff_ringKrullDim_quotient_add_length_eq (R := R) (xs := fs) hfs_mem).1 hfs_reg
    let e : R ⧸ RingHom.ker f ≃+* S := RingHom.quotientKerEquivOfSurjective hsurj
    refine ⟨fs.length, ?_, List.get fs, ?_⟩
    · -- Proof comment: identify the quotient by the kernel with the target local ring.
      calc
        ringKrullDim S + fs.length = ringKrullDim (R ⧸ RingHom.ker f) + fs.length := by
          rw [← ringKrullDim_eq_of_ringEquiv e]
        _ = ringKrullDim (R ⧸ Ideal.ofList fs) + fs.length := by rw [hfs_ker]
        _ = ringKrullDim R := hdim_quot
    · -- Proof comment: rewrite the list witness as a `Fin`-indexed family via `List.get`.
      calc
        Ideal.span (Set.range (List.get fs)) = Ideal.ofList (List.ofFn (List.get fs)) := by
          rw [ideal_ofList_ofFn_eq_span_range]
        _ = Ideal.ofList fs := by rw [List.ofFn_get]
        _ = RingHom.ker f := hfs_ker
  · rintro ⟨d, hdim, x, hx_span⟩
    have hker_le_max : RingHom.ker f ≤ maximalIdeal R :=
      IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top f)
    have hx_mem : ∀ i : Fin d, x i ∈ maximalIdeal R := by
      intro i
      apply hker_le_max
      rw [← hx_span]
      exact Ideal.subset_span ⟨i, rfl⟩
    have hxs_mem : ∀ r ∈ List.ofFn x, r ∈ maximalIdeal R := by
      intro r hr
      rcases List.mem_ofFn.mp hr with ⟨i, rfl⟩
      exact hx_mem i
    let e : R ⧸ RingHom.ker f ≃+* S := RingHom.quotientKerEquivOfSurjective hsurj
    have hdim_ker :
        ringKrullDim (R ⧸ RingHom.ker f) + d = ringKrullDim R := by
      calc
        ringKrullDim (R ⧸ RingHom.ker f) + d = ringKrullDim S + d := by
          rw [ringKrullDim_eq_of_ringEquiv e]
        _ = ringKrullDim R := hdim
    have hofList_ker : Ideal.ofList (List.ofFn x) = RingHom.ker f := by
      calc
        Ideal.ofList (List.ofFn x) = Ideal.span (Set.range x) :=
          ideal_ofList_ofFn_eq_span_range x
        _ = RingHom.ker f := hx_span
    have hdim_quot :
        ringKrullDim (R ⧸ Ideal.ofList (List.ofFn x)) + (List.ofFn x).length = ringKrullDim R := by
      -- Proof comment: transport the target dimension equality back to the quotient by the kernel.
      rw [hofList_ker]
      simpa using hdim_ker
    refine ⟨List.ofFn x, ?_, ?_⟩
    · -- Proof comment: in a regular local ring, the dimension formula is the Cohen-Macaulay
      -- criterion for regularity of a list in the maximal ideal.
      exact
        (isRegular_iff_ringKrullDim_quotient_add_length_eq (R := R) (xs := List.ofFn x)
          hxs_mem).2 hdim_quot
    · exact hofList_ker

/-- Helper for Lemma 10.135.6: generators for `ker φ` together with lifts of generators for
`ker ψ` generate the kernel of the composite. -/
private theorem ker_comp_eq_comap_ker
    (φ : A →+* B) (ψ : B →+* C) :
    RingHom.ker (ψ.comp φ) = Ideal.comap φ (RingHom.ker ψ) := by
  -- Proof comment: membership in the composite kernel is exactly membership in the pulled-back
  -- kernel of the target map.
  ext a
  rw [RingHom.mem_ker, Ideal.mem_comap, RingHom.mem_ker, RingHom.comp_apply]

/-- Helper for Lemma 10.135.6: the comap of the span of a lifted finite family is the span of the
lifts together with the kernel of the surjection. -/
private theorem comap_span_range_eq_span_lifts_sup_ker
    (φ : A →+* B) (hφ : Function.Surjective φ) {d : ℕ}
    (y : Fin d → B) (yLift : Fin d → A)
    (hyLift : ∀ i, φ (yLift i) = y i) :
    Ideal.comap φ (Ideal.span (Set.range y)) =
      Ideal.span (Set.range yLift) ⊔ RingHom.ker φ := by
  have himage : φ '' Set.range yLift = Set.range y := by
    -- Proof comment: the chosen lifts hit exactly the original family.
    ext b
    constructor
    · rintro ⟨a, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, (hyLift i).symm⟩
    · rintro ⟨i, rfl⟩
      exact ⟨yLift i, ⟨i, rfl⟩, hyLift i⟩
  have hmap :
      Ideal.map φ (Ideal.span (Set.range yLift)) = Ideal.span (Set.range y) := by
    -- Proof comment: mapping the lifted span recovers the original span.
    rw [Ideal.map_span, himage]
  calc
    Ideal.comap φ (Ideal.span (Set.range y)) =
        Ideal.comap φ (Ideal.map φ (Ideal.span (Set.range yLift))) := by
          rw [hmap.symm]
    _ = Ideal.span (Set.range yLift) ⊔ Ideal.comap φ ⊥ := by
          rw [Ideal.comap_map_of_surjective (f := φ) hφ]
    _ = Ideal.span (Set.range yLift) ⊔ RingHom.ker φ := by
          rw [RingHom.ker_eq_comap_bot]

/-- Helper for Lemma 10.135.6: generators for `ker φ` together with lifts of generators for
`ker ψ` generate the kernel of the composite. -/
private theorem exists_dim_span_eq_composite_kernel_of_factor_spans
    (φ : A →+* B) (ψ : B →+* C) [IsLocalHom φ] [IsLocalHom ψ]
    (hφ : Function.Surjective φ)
    {dφ dψ : ℕ}
    (hφdim : ringKrullDim B + dφ = ringKrullDim A)
    (x : Fin dφ → A) (hx : Ideal.span (Set.range x) = RingHom.ker φ)
    (hψdim : ringKrullDim C + dψ = ringKrullDim B)
    (y : Fin dψ → B) (hy : Ideal.span (Set.range y) = RingHom.ker ψ) :
    ∃ (d : ℕ) (_ : ringKrullDim C + d = ringKrullDim A) (z : Fin d → A),
      Ideal.span (Set.range z) = RingHom.ker (ψ.comp φ) := by
  classical
  let yLift : Fin dψ → A := fun i ↦ Classical.choose (hφ (y i))
  have hyLift : ∀ i, φ (yLift i) = y i := by
    -- Proof comment: `Classical.choose` records the chosen lifts of the `ker ψ` generators.
    intro i
    exact Classical.choose_spec (hφ (y i))
  refine ⟨dφ + dψ, ?_, Fin.append x yLift, ?_⟩
  · -- Proof comment: the generator counts add along the surjective factorization.
    have hsum : ringKrullDim C + dψ + dφ = ringKrullDim A := by
      calc
        ringKrullDim C + dψ + dφ = ringKrullDim B + dφ := by rw [hψdim]
        _ = ringKrullDim A := hφdim
    simpa [add_assoc, add_left_comm, add_comm] using hsum
  · -- Proof comment: the appended family spans `ker φ ⊔ φ⁻¹(ker ψ) = ker (ψ ∘ φ)`.
    calc
      Ideal.span (Set.range (Fin.append x yLift)) =
          Ideal.span (Set.range x ∪ Set.range yLift) := by
            rw [range_fin_append]
      _ = Ideal.span (Set.range x) ⊔ Ideal.span (Set.range yLift) := by
            rw [Ideal.span_union]
      _ = RingHom.ker φ ⊔ Ideal.span (Set.range yLift) := by
            rw [hx]
      _ = Ideal.span (Set.range yLift) ⊔ RingHom.ker φ := by
            rw [sup_comm]
      _ = Ideal.comap φ (RingHom.ker ψ) := by
            rw [← hy, comap_span_range_eq_span_lifts_sup_ker φ hφ y yLift hyLift]
      _ = RingHom.ker (ψ.comp φ) := by
            rw [ker_comp_eq_comap_ker]

/-- Helper for Lemma 10.135.6: after quotienting by a chosen head generator that the quotient map
kills, the image of the full span is exactly the span of the tail images. -/
private theorem ideal_map_span_fin_cons_eq_span_tail_of_head_mem_ker
    {S : Type*} [CommRing S] (q : A →+* S) {d : ℕ} (x : A) (z : Fin d → A)
    (hx : q x = 0) :
    Ideal.map q (Ideal.span (Set.range (Fin.cons x z))) =
      Ideal.span (Set.range fun i : Fin d ↦ q (z i)) := by
  -- Proof comment: mapping the head-plus-tail span kills the head generator and keeps exactly the
  -- tail image family.
  rw [Ideal.map_span]
  apply le_antisymm
  · refine Ideal.span_le.2 ?_
    rintro _ ⟨a, ⟨i, rfl⟩, rfl⟩
    refine Fin.cases ?_ ?_ i
    · simpa [hx]
    · intro j
      exact Ideal.subset_span ⟨j, rfl⟩
  · refine Ideal.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    exact Ideal.subset_span ⟨z i, ⟨Fin.succ i, rfl⟩, rfl⟩

/-- Helper for Lemma 10.135.6: quotienting by an element already in `ker φ` identifies the image
of the composite kernel with the kernel of the descended composite map. -/
private theorem map_composite_kernel_eq_descended_kernel_after_head_quotient
    (φ : A →+* B) (ψ : B →+* C) {x : A} (hx : x ∈ RingHom.ker φ) :
    let I : Ideal A := Ideal.span ({x} : Set A)
    let φbar : A ⧸ I →+* B := Ideal.Quotient.lift I φ
      (by
        -- Proof comment: the quotient ideal is generated by an element already killed by `φ`.
        intro a ha
        have hIle : I ≤ RingHom.ker φ := by
          simpa [I] using
            (Ideal.span_singleton_le_iff_mem (I := RingHom.ker φ) (x := x)).2 hx
        simpa [RingHom.mem_ker] using hIle ha)
    Ideal.map (Ideal.Quotient.mk I) (RingHom.ker (ψ.comp φ)) =
      RingHom.ker (ψ.comp φbar) := by
  let I : Ideal A := Ideal.span ({x} : Set A)
  let φbar : A ⧸ I →+* B := Ideal.Quotient.lift I φ
    (by
      -- Proof comment: `φ` vanishes on the principal ideal generated by `x`.
      intro a ha
      have hIle : I ≤ RingHom.ker φ := by
        simpa [I] using
          (Ideal.span_singleton_le_iff_mem (I := RingHom.ker φ) (x := x)).2 hx
      simpa [RingHom.mem_ker] using hIle ha)
  ext y
  constructor
  · intro hy
    rcases (Ideal.mem_map_iff_of_surjective
      (f := Ideal.Quotient.mk I) (hf := Ideal.Quotient.mk_surjective)
      (I := RingHom.ker (ψ.comp φ)) (y := y)).1 hy with ⟨a, ha, rfl⟩
    -- Proof comment: a representative from the composite kernel still maps to zero after
    -- descending `φ` through the quotient.
    rw [RingHom.mem_ker] at ha ⊢
    simpa [φbar, I, RingHom.comp_apply] using ha
  · intro hy
    rcases Ideal.Quotient.mk_surjective y with ⟨a, rfl⟩
    rw [RingHom.mem_ker] at hy
    -- Proof comment: any quotient element in the descended kernel has a representative already in
    -- the original composite kernel.
    refine (Ideal.mem_map_iff_of_surjective
      (f := Ideal.Quotient.mk I) (hf := Ideal.Quotient.mk_surjective)
      (I := RingHom.ker (ψ.comp φ))
      (y := Ideal.Quotient.mk I a)).2 ?_
    refine ⟨a, ?_, rfl⟩
    rw [RingHom.mem_ker]
    simpa [φbar, I, RingHom.comp_apply] using hy

/-- Helper for Lemma 10.135.6: if a finite family generates an ideal, then the corresponding
subtype-valued family spans that ideal as a module. -/
private theorem span_subtype_eq_top_of_ideal_span_eq
    (I : Ideal A) {d : ℕ} (w : Fin d → A) (hw : Ideal.span (Set.range w) = I) :
    Submodule.span A (Set.range fun i : Fin d ↦ (⟨w i, by
      rw [← hw]
      exact Ideal.subset_span ⟨i, rfl⟩⟩ : I)) = ⊤ := by
  -- Proof comment: this is the ambient-ideal/span statement rewritten inside the ideal subtype.
  exact
    (Submodule.span_range_subtype_eq_top_iff
      (p := I) (s := w) (hs := fun i ↦ by
        rw [← hw]
        exact Ideal.subset_span ⟨i, rfl⟩)).2 <| by
          simpa using hw

/-- Helper for Lemma 10.135.6: an element of `I` has nonzero class in `I / 𝔪 I` precisely when it
does not lie in `𝔪 I`. -/
private theorem quotient_class_ne_zero_of_not_mem_maximalIdeal_mul
    (I : Ideal A) {x : A} (hxI : x ∈ I) (hx_not_mem : x ∉ maximalIdeal A * I) :
    let N : Submodule A I := maximalIdeal A • (⊤ : Submodule A I)
    (Submodule.mkQ N ⟨x, hxI⟩ : I ⧸ N) ≠ 0 := by
  let N : Submodule A I := maximalIdeal A • (⊤ : Submodule A I)
  -- Proof comment: `Submodule.mem_smul_top_iff` converts the quotient-zero condition back to the
  -- ideal product `𝔪 I`.
  intro hx_zero
  apply hx_not_mem
  exact
    (Submodule.mem_smul_top_iff (I := maximalIdeal A) (N := I) ⟨x, hxI⟩).1 <|
      (Submodule.Quotient.mk_eq_zero N).1 hx_zero

/-- Helper for Lemma 10.135.6: if `x ∈ I` survives in `I / 𝔪 I`, then `x` can be inserted as the
head of a finite generating family of `I`. -/
private theorem exists_fin_cons_span_eq_of_mem_not_mem_maximalIdeal_mul
    (I : Ideal A) (hI : I ≤ maximalIdeal A) {n : ℕ} {x : A} (hxI : x ∈ I)
    (hx_not_mem : x ∉ maximalIdeal A * I) (w : Fin (n + 1) → A)
    (hw : Ideal.span (Set.range w) = I) :
    ∃ z : Fin n → A, Ideal.span (Set.range (Fin.cons x z)) = I := by
  -- TODO: follow the source proof in `I / 𝔪 I`: use
  -- `span_subtype_eq_top_of_ideal_span_eq` to view `w` as a spanning family of the finite
  -- `A`-module `I`, use `quotient_class_ne_zero_of_not_mem_maximalIdeal_mul` to show the class of
  -- `x` in `I / 𝔪 I` is nonzero, choose a nonzero coefficient in a linear-combination expression
  -- of that class against the quotient images of `w`, pivot one generator to replace it by `x`,
  -- and then apply `span_eq_top_of_quotient_span_eq_top_of_le_ring_jacobson` to lift the quotient
  -- spanning statement back to `I`.
  sorry

/-- Helper for Lemma 10.135.6: the remaining hard implication is the textbook induction from a
dimension-count presentation of `ker (A → C)` to the corresponding dimension-count presentation of
`ker (B → C)`. -/
private theorem composite_kernel_dim_generators_implies_right_kernel_dim_generators
    (φ : A →+* B) (ψ : B →+* C) [IsLocalHom φ] [IsLocalHom ψ]
    (hφ : Function.Surjective φ) (hψ : Function.Surjective ψ) :
    (∃ (d : ℕ) (_ : ringKrullDim C + d = ringKrullDim A) (x : Fin d → A),
        Ideal.span (Set.range x) = RingHom.ker (ψ.comp φ)) →
      ∃ (d : ℕ) (_ : ringKrullDim C + d = ringKrullDim B) (y : Fin d → B),
        Ideal.span (Set.range y) = RingHom.ker ψ := by
  -- Route correction: the kernel-transport plumbing is now isolated in
  -- `map_composite_kernel_eq_descended_kernel_after_head_quotient`, so the only remaining work is
  -- the source-faithful Nakayama decrement: choose `x ∈ RingHom.ker φ` with nonzero cotangent
  -- class, show it can be taken as a head generator of `RingHom.ker (ψ.comp φ)`, quotient by
  -- `Ideal.span ({x} : Set A)`, and recurse on the shorter prefix from Lemma `10.106.4`.
  sorry

/- Domain-style sampling pass.

Primary domain: surjective local homomorphisms of regular local rings, with kernels generated by
regular sequences and compared through quotient dimension formulas.

Sampled owner declarations:
* `RingHom.KernelIsGeneratedByRegularSequence`;
* `Module.regularLocalRing_selfModule_cohenMacaulay`;
* `Module.isRegular_iff_ringKrullDim_quotient_add_length_eq`;
* `IsLocalRing.exists_regularSystemOfParameters_with_prefix_span_eq_of_quotient_isRegularLocalRing`.

Best owner abstraction: the kernel predicate
`RingHom.KernelIsGeneratedByRegularSequence` is the primitive source-facing owner. The numerical
clauses about `dim(A) - dim(C)` and `dim(B) - dim(C)` generators are derived API, obtained by
combining the Cohen-Macaulay self-module owner for regular local rings with the quotient
dimension criterion for regular sequences, plus the parameter-system presentation of kernels of
surjections whose source and quotient are regular local.

Primitive vs. derived:
* primitive data: the surjective local maps `A → B → C` and the owner predicates on
  `RingHom.ker (ψ.comp φ)` and `RingHom.ker ψ`;
* derived API: finite generating families of those kernels whose cardinalities match the relevant
  dimension drops.

Source/core/bridge triage:
* source-facing: the `List.TFAE` comparison between the two kernels in Lemma `10.135.6`;
* core/canonical: `RingHom.KernelIsGeneratedByRegularSequence` and the regular-local/Cohen-Macaulay
  owner theorems above;
* bridge/view: the explicit `Fin d → A` and `Fin d → B` families spanning the two kernels.
-/

-- Proof sketch: `A` and `B` are Cohen-Macaulay as modules over themselves by the regular-local
-- owner instance from Lemma `10.106.3`. For each surjective map onto the regular local quotient
-- `C`, Lemma `10.104.2` converts the kernel regular-sequence owner into the additive dimension
-- criterion `ringKrullDim C + d = ringKrullDim _` together with a `d`-element generating family.
-- Lemma `10.106.4` supplies the same expected-number-of-generators presentation for the kernel of
-- `φ`, so the two kernel conditions are equivalent by comparing the composite quotient
-- `A ⧸ ker (ψ.comp φ)` with the successive quotients through `B`.
/-- Lemma 10.135.6: for surjective local ring homomorphisms `A → B → C` with `A` and `B` regular
local, the following are equivalent: the kernel of `A → C` is generated by a regular sequence, the
kernel of `A → C` is generated by `dim(A) - dim(C)` elements, the kernel of `B → C` is generated by
a regular sequence, and the kernel of `B → C` is generated by `dim(B) - dim(C)` elements. -/
theorem ker_generatedBy_regularSequence_tfae_of_surjective_local_of_isRegularLocalRing
    (φ : A →+* B) (ψ : B →+* C) [IsLocalHom φ] [IsLocalHom ψ]
    (hφ : Function.Surjective φ) (hψ : Function.Surjective ψ) :
    List.TFAE
      [ (ψ.comp φ).KernelIsGeneratedByRegularSequence
      , ∃ (d : ℕ) (_ : ringKrullDim C + d = ringKrullDim A) (x : Fin d → A),
          Ideal.span (Set.range x) = RingHom.ker (ψ.comp φ)
      , ψ.KernelIsGeneratedByRegularSequence
      , ∃ (d : ℕ) (_ : ringKrullDim C + d = ringKrullDim B) (y : Fin d → B),
          Ideal.span (Set.range y) = RingHom.ker ψ
      ] := by
  tfae_have 1 ↔ 2 := by
    -- Proof comment: over a regular local source, kernel regular sequences are equivalent to the
    -- expected-number-of-generators criterion.
    simpa using
      (kernel_generatedByRegularSequence_iff_exists_dim_span_eq_ker
        (R := A) (S := C) (f := ψ.comp φ) (hsurj := hψ.comp hφ))
  tfae_have 3 ↔ 4 := by
    -- Proof comment: the same Cohen--Macaulay criterion applies to the right-hand surjection.
    simpa using
      (kernel_generatedByRegularSequence_iff_exists_dim_span_eq_ker
        (R := B) (S := C) (f := ψ) (hsurj := hψ))
  tfae_have 4 → 2 := by
    rintro ⟨dψ, hψdim, y, hy⟩
    let e : A ⧸ RingHom.ker φ ≃+* B := RingHom.quotientKerEquivOfSurjective hφ
    have hquot : IsRegularLocalRing (A ⧸ RingHom.ker φ) := by
      exact IsRegularLocalRing.of_ringEquiv e.symm
    obtain ⟨c, x, hpart, hxparam⟩ :=
      exists_regularSystemOfParameters_with_prefix_span_eq_of_quotient_isRegularLocalRing
        (R := A) (I := RingHom.ker φ) hquot
    let xA : Fin c → A := fun i ↦ (x i : A)
    have hφreg : φ.KernelIsGeneratedByRegularSequence := by
      refine ⟨List.ofFn xA, ?_, ?_⟩
      · -- Proof comment: an initial segment of a regular system of parameters is a regular
        -- sequence.
        simpa [xA] using hpart.isRegular
      · -- Proof comment: the prefix parameter ideal is exactly `ker φ`.
        calc
          Ideal.ofList (List.ofFn xA) = Ideal.span (Set.range xA) := by
            rw [ideal_ofList_ofFn_eq_span_range]
          _ = parameterIdeal x := by
            rw [parameterIdeal_eq_span]
          _ = RingHom.ker φ := hxparam
    obtain ⟨dφ, hφdim, x', hx'⟩ :=
      (kernel_generatedByRegularSequence_iff_exists_dim_span_eq_ker
        (R := A) (S := B) (f := φ) (hsurj := hφ)).mp hφreg
    exact
      exists_dim_span_eq_composite_kernel_of_factor_spans
        φ ψ hφ hφdim x' hx' hψdim y hy
  tfae_have 2 → 4 := by
    -- Route correction: the hard direction stays source-faithful and is delegated to the
    -- induction helper on `ringKrullDim A - ringKrullDim B`.
    exact composite_kernel_dim_generators_implies_right_kernel_dim_generators φ ψ hφ hψ
  tfae_finish

end

/-! ### Lemma_10_135_7 (from Chap10) -/
universe u v w

section

open Algebra

variable {k : Type u} [Field k]
variable {S : Type v} [CommRing S] [Algebra k S] [IsLocalRing S] [Algebra.EssFiniteType k S]

/- Domain-style sampling pass.

Primary domain: local complete intersections over a field, regular local presentations, and
localization-at-a-prime models of global and local complete intersections.

Sampled owner declarations:
* `Algebra.IsCompleteIntersectionOver`;
* `IsGlobalCompleteIntersection`;
* `IsLocalCompleteIntersection`;
* `RingHom.KernelIsGeneratedByRegularSequence`.

Best owner abstraction: the primitive source-facing owner is
`Algebra.IsCompleteIntersectionOver k S`. The kernel condition lives on the canonical homomorphism
owner `RingHom.KernelIsGeneratedByRegularSequence`, while the global and local complete
intersection clauses should reuse the chapter owners `IsGlobalCompleteIntersection` and
`IsLocalCompleteIntersection` rather than introducing parallel local wrappers.

Primitive vs. derived:
* primitive data: the local `k`-algebra `S` with its essentially-finite-type structure;
* derived API: the universal and existential regular-local-presentation clauses, and the two
  prime-localization model clauses.

Source/core/bridge triage:
* source-facing: the `List.TFAE` theorem below;
* core/canonical: `Algebra.IsCompleteIntersectionOver`, `IsGlobalCompleteIntersection`,
  `IsLocalCompleteIntersection`, `RingHom.KernelIsGeneratedByRegularSequence`;
* bridge/view: the existence of a prime-localization model of a global or local complete
  intersection.
-/

-- Proof sketch: combine the definition of `Algebra.IsCompleteIntersectionOver k S` with the
-- comparison lemma for kernels along surjections from regular local rings in Lemma `10.135.6`.
-- The implication `(3) → (4)` is obtained by writing the chosen regular local ring as a
-- localization of a polynomial algebra and then applying Lemma `10.135.4`; `(4) → (5)` is
-- immediate. For `(5) → (2)`, compare any regular local presentation of `S` with a localization
-- of a local complete intersection using Lemma `10.126.7`, and transfer the regular-sequence
-- description of the kernel back through Lemma `10.135.6`.
/-- Lemma 10.135.7: let `k` be a field and let `S` be a local `k`-algebra essentially of finite
type over `k`. The following are equivalent: `S` is a complete intersection over `k`; for every
surjection `R →ₐ[k] S` with `R` a regular local ring essentially of finite presentation over `k`,
the kernel is generated by a regular sequence; there exists such a surjection whose kernel is
generated by `dim(R) - dim(S)` elements; `S` is isomorphic to the localization at a prime of a
global complete intersection over `k`; and `S` is isomorphic to the localization at a prime of a
local complete intersection over `k`. -/
theorem isCompleteIntersectionOver_tfae :
    List.TFAE
      [ IsCompleteIntersectionOver k S
      , ∀ (R : Type w) [CommRing R] [Algebra k R] [Algebra.EssFinitePresentation k R]
          [IsRegularLocalRing R] (π : R →ₐ[k] S),
          Function.Surjective π → π.toRingHom.KernelIsGeneratedByRegularSequence
      , ∃ (R : Type w) (_ : CommRing R) (_ : Algebra k R)
          (_ : Algebra.EssFinitePresentation k R) (_ : IsRegularLocalRing R) (π : R →ₐ[k] S),
          Function.Surjective π ∧
            ∃ (d : ℕ) (_ : ringKrullDim S + d = ringKrullDim R) (x : Fin d → R),
              Ideal.span (Set.range x) = RingHom.ker π.toRingHom
      , ∃ (A : Type w) (_ : CommRing A) (_ : Algebra k A) (a : PrimeSpectrum A)
          (e : S ≃ₐ[k] Localization.AtPrime a.asIdeal),
          IsGlobalCompleteIntersection k A
      , ∃ (A : Type w) (_ : CommRing A) (_ : Algebra k A) (a : PrimeSpectrum A)
          (e : S ≃ₐ[k] Localization.AtPrime a.asIdeal),
          IsLocalCompleteIntersection k A
      ] := sorry

end

/-! ### Lemma_10_135_8 (from Chap10) -/
noncomputable section

open Algebra
open PolynomialPresentationAtPrime

universe u v

section

variable {k : Type u} [Field k]
variable {S : Type v} [CommRing S] [Algebra k S] [Algebra.FiniteType k S]

/- Domain-style sampling pass.

Primary domain: complete intersections at a prime of a finite type algebra, compared through
localization and localized polynomial presentations.

Sampled owner declarations:
* `Algebra.IsCompleteIntersectionOver`;
* `PolynomialPresentationAtPrime.tfae`;
* `isLocalCompleteIntersectionNearPrime`;
* `isGlobalCompleteIntersectionNearPrime`.

Best owner abstraction: `Algebra.IsCompleteIntersectionOver` is the canonical owner for the local
ring condition at `q`, while the presentation-theoretic clause is derived from the existing owner
theorem `PolynomialPresentationAtPrime.tfae` rather than from a new local wrapper.

Primitive vs. derived:
* primitive data: the finite type `k`-algebra `S`, the prime `q`, and a chosen surjective
  polynomial presentation of `S`;
* derived API: the near-prime local/global complete intersection predicates and the five-condition
  `List.TFAE` for a chosen presentation.

Source/core/bridge triage:
* source-facing: the four-way `List.TFAE` below;
* core/canonical: `Algebra.IsCompleteIntersectionOver`;
* bridge/view: the basic-open neighborhood predicates and the localized polynomial-presentation
  criterion from `PolynomialPresentationAtPrime.tfae`.
-/

-- Proof sketch: apply Lemma `10.135.7` to the local ring `S_q`, whose being a complete
-- intersection over `k` is equivalent to being a localization at a prime of either a local or a
-- global complete intersection. The presentation-theoretic clause is then identified with the
-- corresponding criterion from Lemma `10.135.4`, and the finite-type hypothesis on `S` supplies
-- the essential finite-type hypothesis needed after localizing at `q`.
/-- Lemma 10.135.8: for a finite type `k`-algebra `S` and a prime `q` of `S`, the following are
equivalent: the local ring `S_q` is a complete intersection over `k`; some basic open
neighbourhood of `q` is a local complete intersection over `k`; some basic open neighbourhood of
`q` is a global complete intersection over `k`; and for every surjective polynomial presentation
of `S`, the localized defining ideal at the prime over `q` is generated by a regular sequence of
length equal to the codimension difference. -/
theorem completeIntersectionOver_atPrime_tfae
    (q : PrimeSpectrum S) :
    List.TFAE
      [ Algebra.IsCompleteIntersectionOver k (Localization.AtPrime q.asIdeal)
      , isLocalCompleteIntersectionNearPrime k q
      , isGlobalCompleteIntersectionNearPrime k q
      , (∀ {n : ℕ} (π : MvPolynomial (Fin n) k →ₐ[k] S) (_ : Function.Surjective π),
            kernelGeneratedByRegularSequenceCondition π q
              (ENat.toNat ((prime π q).asIdeal.height - q.asIdeal.height)))
      ] := sorry

end

/-! ### Lemma_10_135_9 (from Chap10) -/
universe u v

open Algebra

section

variable {k : Type u} [Field k]
variable {S : Type v} [CommRing S] [Algebra k S]

/- Domain-style sampling pass.

Primary domain: local complete intersections over a field and their detection on prime and maximal
localizations of an algebra.

Sampled owner declarations:
* `IsLocalCompleteIntersection`;
* `IsCompleteIntersectionOver`;
* `completeIntersectionOver_atPrime_tfae`;
* `MaximalSpectrum`.

Best owner abstraction: `IsLocalCompleteIntersection k S` is the source-facing owner on `S`,
while `IsCompleteIntersectionOver k _` is the canonical owner on each local ring. For the
maximal-local criterion, `MaximalSpectrum S` is the canonical indexing object, so the theorem
surface should use it directly instead of a raw ideal plus a maximality proof.

Primitive vs. derived:
* primitive data: the field `k` and the `k`-algebra `S`;
* derived API: finite presentation and finite type of `S` from
  `IsLocalCompleteIntersection k S`, together with the prime-local and maximal-local comparison
  clauses.

Source/core/bridge triage:
* source-facing: the three-way `List.TFAE` below;
* core/canonical: `IsLocalCompleteIntersection k S` and
  `IsCompleteIntersectionOver k _`;
* bridge/view: the specialization from all prime localizations to maximal localizations.
-/

-- Proof sketch: once one of the three clauses holds, the relevant finite-presentation and
-- finite-type hypotheses are recovered from the owner abstractions (`IsLocalCompleteIntersection`
-- or the primewise/maximal complete-intersection conditions). Then apply Lemma `10.135.8` at each
-- prime `q` to identify the local complete-intersection condition on `S` with the
-- complete-intersection condition on `S_q`. The implication from all prime local rings to all
-- maximal localizations is immediate, and the converse follows from the locality of the complete
-- intersection property together with quasi-compactness of `Spec S`.
/-- Lemma 10.135.9: for a `k`-algebra `S`, the following are equivalent: `S` is a
local complete intersection over `k`; every local ring `S_q` for `q : PrimeSpectrum S` is a
complete intersection over `k`; and every localization `S_m` at a maximal ideal `m` of `S` is a
complete intersection over `k`. -/
theorem isLocalCompleteIntersection_tfae_completeIntersectionOver_localRings :
    List.TFAE
      [ IsLocalCompleteIntersection k S
      , ∀ q : PrimeSpectrum S, IsCompleteIntersectionOver k (Localization.AtPrime q.asIdeal)
      , ∀ m : MaximalSpectrum S, IsCompleteIntersectionOver k (Localization.AtPrime m.asIdeal)
      ] := sorry

end

/-! ### Lemma_10_135_10 (from Chap10) -/
open scoped TensorProduct
open Algebra
open Algebra.TensorProduct

universe u v w

section

variable {k : Type u} [Field k]
variable {K : Type v} [Field K] [Algebra k K]
variable {S : Type w} [CommRing S] [Algebra k S] [Algebra.FiniteType k S]

local notation "S_K" => K ⊗[k] S
local notation "iSK" => (((includeRight : S →ₐ[k] S_K) : S →+* S_K))

/- Domain-style sampling pass.

Primary domain: local complete intersections under tensor base change along a field extension.

Sampled owner declarations:
* `IsCompleteIntersectionOver`;
* `completeIntersectionOver_atPrime_tfae`;
* `cohenMacaulay_localizationAtPrime_iff_of_tensorProduct_fieldExtension`;
* `Algebra.isSmoothAt_iff_isSmoothAt_tensor_fieldExtension`.

Best owner abstraction: the public statement should stay directly on the canonical local owner
`IsCompleteIntersectionOver` for the localized rings. The contraction `PrimeSpectrum.comap iSK qK`
is bridge/view data induced by the tensor-product owner map `iSK`; it should not be repackaged as
an extra local `abbrev`.

Primitive vs. derived:
* primitive data: the finite type `k`-algebra `S`, the extension field `K`, and the upstairs prime
  `qK : PrimeSpectrum S_K`;
* derived API: the downstairs prime `PrimeSpectrum.comap iSK qK` and the local-ring comparison
  theorem below.

Source/core/bridge triage:
* `source-facing`: invariance of the complete-intersection condition on the local rings at a prime
  under the base change `S ↦ K ⊗[k] S`;
* `core/canonical`: `IsCompleteIntersectionOver` on the two local rings;
* `bridge/view`: the contraction `PrimeSpectrum.comap iSK qK`.
-/

-- Proof sketch: use Lemma `10.135.8` to characterize complete intersections at a prime by the
-- presentation-theoretic criterion of Lemma `10.135.4`. After base change from `k` to `K`, the
-- relevant codimension is unchanged by Lemma `10.116.6`, and the minimal number of generators of
-- the localized defining ideal is preserved by the residue-field comparison and Nakayama's lemma.
/-- Lemma 10.135.10: for a field extension `K / k`, a finite type `k`-algebra `S`, and a prime
`qK` of `K ⊗[k] S` with corresponding prime `q` of `S`, the local ring `S_q` is a complete
intersection over `k` if and only if the local ring `(K ⊗[k] S)_{qK}` is a complete intersection
over `K`. -/
theorem isCompleteIntersectionOver_atPrime_iff_of_tensorProduct_fieldExtension
    (qK : PrimeSpectrum S_K) :
    let q := PrimeSpectrum.comap iSK qK
    IsCompleteIntersectionOver k (Localization.AtPrime q.asIdeal) ↔
      IsCompleteIntersectionOver K (Localization.AtPrime qK.asIdeal) := sorry

end
