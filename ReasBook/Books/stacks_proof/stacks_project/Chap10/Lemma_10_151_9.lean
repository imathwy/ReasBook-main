import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_112_1
import stacks_proof.stacks_project.Chap10.Lemma_10_114_1
import stacks_proof.stacks_project.Chap10.Lemma_10_125_5
import stacks_proof.stacks_project.Chap10.Lemma_10_140_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace Algebra

section

variable {k : Type u} [Field k]
variable {A : Type v} [CommRing A] [Algebra k A]
variable {n : ℕ}
variable [Algebra (MvPolynomial (Fin n) k) A]
variable [IsScalarTower k (MvPolynomial (Fin n) k) A]
variable [FiniteType (MvPolynomial (Fin n) k) A]

open KaehlerDifferential MvPolynomial
open scoped TensorProduct
open Algebra.HasGoingDown

local notation "P" => MvPolynomial (Fin n) k

omit [Algebra k A] [IsScalarTower k P A] in
/-- Helper for Chap10 Lemma 10 151 9: a finite-type algebra over a polynomial algebra over a
field is finitely presented. -/
lemma finitePresentation_mvPolynomial_algebra_of_finiteType :
    FinitePresentation P A := by
  -- The polynomial algebra over a field is Noetherian, so finite type upgrades to finite
  -- presentation by the standard Noetherian-base criterion.
  exact (Algebra.FinitePresentation.of_finiteType (R := P) (A := A)).mp inferInstance

/-- Helper for Chap10 Lemma 10 151 9: finite type over a polynomial algebra gives finite type
over the ground field. -/
lemma finiteType_over_base_of_mvPolynomial_finiteType (n : ℕ)
    [Algebra (MvPolynomial (Fin n) k) A]
    [IsScalarTower k (MvPolynomial (Fin n) k) A]
    [FiniteType (MvPolynomial (Fin n) k) A] :
    Algebra.FiniteType k A := by
  -- Compose finite generation along the tower `k → k[x_i] → A`.
  exact
    Algebra.FiniteType.trans (R := k) (S := MvPolynomial (Fin n) k) (A := A)
      inferInstance inferInstance

omit [FiniteType P A] in
/-- Helper for Chap10 Lemma 10 151 9: the Jacobi-Zariski base-change image for
`k → k[x_i] → A` is the span of the coordinate differentials in `Ω[A⁄k]`. -/
lemma range_mapBaseChange_mvPolynomial_eq_coordinateDifferentials_span :
    LinearMap.range (KaehlerDifferential.mapBaseChange k P A) =
      Submodule.span A (Set.range fun i : Fin n ↦ D k A (algebraMap P A (X i))) := by
  let b : Module.Basis (Fin n) P Ω[P⁄k] := KaehlerDifferential.mvPolynomialBasis k (Fin n)
  -- Compute the range of the base-change map by transporting the polynomial Kähler basis to
  -- `A ⊗[P] Ω[P⁄k]`.
  calc
    LinearMap.range (KaehlerDifferential.mapBaseChange k P A)
        = Submodule.map (KaehlerDifferential.mapBaseChange k P A) ⊤ := by
          exact LinearMap.range_eq_map _
    _ = Submodule.map (KaehlerDifferential.mapBaseChange k P A)
        (Submodule.span A (Set.range fun i : Fin n ↦ (b.baseChange A) i)) := by
          rw [(b.baseChange A).span_eq]
    _ = Submodule.span A ((KaehlerDifferential.mapBaseChange k P A) ''
        Set.range (fun i : Fin n ↦ (b.baseChange A) i)) := by
          rw [Submodule.map_span]
    _ = Submodule.span A (Set.range fun i : Fin n ↦ D k A (algebraMap P A (X i))) := by
          -- Each transported basis vector maps to the corresponding coordinate differential.
          congr 1
          ext x
          constructor
          · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
            refine ⟨i, ?_⟩
            simp [b, KaehlerDifferential.mapBaseChange_tmul, KaehlerDifferential.map_D]
          · rintro ⟨i, rfl⟩
            refine ⟨(b.baseChange A) i, ⟨i, rfl⟩, ?_⟩
            simp [b, KaehlerDifferential.mapBaseChange_tmul, KaehlerDifferential.map_D]

omit [FiniteType P A] in
/-- Helper for Chap10 Lemma 10 151 9: coordinate differentials generate `Ω[A⁄k]` exactly when
`A` is formally unramified over the polynomial subalgebra. -/
lemma coordinateDifferentials_span_top_iff_formallyUnramified_mvPolynomial :
    Submodule.span A (Set.range fun i : Fin n ↦ D k A (algebraMap P A (X i))) = ⊤ ↔
      FormallyUnramified P A := by
  let f : Ω[A⁄k] →ₗ[A] Ω[A⁄P] := KaehlerDifferential.map k P A A
  have hrange : LinearMap.range (KaehlerDifferential.mapBaseChange k P A) =
      Submodule.span A (Set.range fun i : Fin n ↦ D k A (algebraMap P A (X i))) :=
    range_mapBaseChange_mvPolynomial_eq_coordinateDifferentials_span (k := k) (A := A) (n := n)
  have hker : LinearMap.range (KaehlerDifferential.mapBaseChange k P A) = LinearMap.ker f := by
    simpa [f] using KaehlerDifferential.range_mapBaseChange k P A
  constructor
  · intro hspan
    rw [Algebra.formallyUnramified_iff]
    refine ⟨fun y z ↦ ?_⟩
    obtain ⟨y', rfl⟩ := KaehlerDifferential.map_surjective k P A y
    obtain ⟨z', rfl⟩ := KaehlerDifferential.map_surjective k P A z
    -- If the coordinate span is all of `Ω[A⁄k]`, exactness forces the comparison map to be zero.
    have hy : f y' = 0 := by
      have : y' ∈ LinearMap.ker f := by
        rw [← hker, hrange, hspan]
        exact Submodule.mem_top
      exact this
    have hz : f z' = 0 := by
      have : z' ∈ LinearMap.ker f := by
        rw [← hker, hrange, hspan]
        exact Submodule.mem_top
      exact this
    rw [hy, hz]
  · intro hform
    have hsub : Subsingleton Ω[A⁄P] := (Algebra.formallyUnramified_iff P A).mp hform
    -- Conversely, if `Ω[A⁄P]` is trivial, then the kernel is the whole source module.
    have hker_top : LinearMap.ker f = ⊤ := by
      ext x
      constructor
      · intro _
        exact Submodule.mem_top
      · intro _
        exact Subsingleton.elim (f x) 0
    rw [← hrange, hker, hker_top]

/-- Helper for Chap10 Lemma 10 151 9: the coordinate-differential spanning condition makes the
polynomial-algebra map quasi-finite. -/
lemma quasiFinite_of_coordinateDifferentials_span_mvPolynomial
    (hspan : Submodule.span A
      (Set.range fun i : Fin n ↦ D k A (algebraMap P A (X i))) = ⊤) :
    Algebra.QuasiFinite P A := by
  -- The span condition is exactly formal unramifiedness over `P`; finite type then supplies the
  -- standard quasi-finiteness instance.
  letI : FormallyUnramified P A :=
    coordinateDifferentials_span_top_iff_formallyUnramified_mvPolynomial.mp hspan
  infer_instance

omit [Algebra k A] [IsScalarTower k P A] in
/-- Helper for Chap10 Lemma 10 151 9: maximal ideals of a finite-type algebra over the
polynomial base contract to maximal ideals of that base. -/
lemma maximalSpectrum_under_mvPolynomial_isMaximal (m : MaximalSpectrum A) :
    (m.asIdeal.under P).IsMaximal := by
  letI : Field (A ⧸ m.asIdeal) := Ideal.Quotient.field m.asIdeal
  have hfinite : Module.Finite P (A ⧸ m.asIdeal) := by
    -- The Nullstellensatz over the Jacobson polynomial ring makes this residue field finite over
    -- the polynomial base.
    exact finite_of_finite_type_of_isJacobsonRing P (A ⧸ m.asIdeal)
  letI : Module.Finite P (A ⧸ m.asIdeal) := hfinite
  letI : Algebra.IsIntegral P (A ⧸ m.asIdeal) := Algebra.IsIntegral.of_finite P (A ⧸ m.asIdeal)
  have hmax_comap :
      (Ideal.comap (algebraMap P (A ⧸ m.asIdeal)) (⊥ : Ideal (A ⧸ m.asIdeal))).IsMaximal := by
    exact Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (⊥ : Ideal (A ⧸ m.asIdeal))
  have hcomap_eq :
      Ideal.comap (algebraMap P (A ⧸ m.asIdeal)) (⊥ : Ideal (A ⧸ m.asIdeal)) =
        m.asIdeal.under P := by
    -- The kernel of the quotient map `P → A/m` is exactly the contraction of `m`.
    ext x
    change Ideal.Quotient.mk m.asIdeal (algebraMap P A x) = 0 ↔
      (algebraMap P A) x ∈ m.asIdeal
    exact Ideal.Quotient.eq_zero_iff_mem
  simpa [hcomap_eq] using hmax_comap

omit [Algebra k A] [IsScalarTower k P A] [FiniteType P A] in
/-- Helper for Chap10 Lemma 10 151 9: an étale algebra over the polynomial base has equal
Krull dimensions after localizing at a prime and its contraction. -/
lemma ringKrullDim_localizationAtPrime_eq_of_etale_mvPolynomialBase
    {B : Type*} [CommRing B] [Algebra P B] [Etale P B]
    (q : Ideal B) [q.IsPrime] :
    ringKrullDim (Localization.AtPrime (q.under P)) =
      ringKrullDim (Localization.AtPrime q) := by
  -- Faithful flatness of the induced local map gives one inequality by the going-down dimension
  -- theorem.
  have hPB :
      ringKrullDim (Localization.AtPrime (q.under P)) ≤
        ringKrullDim (Localization.AtPrime q) := by
    letI :
        Module.FaithfullyFlat (Localization.AtPrime (q.under P)) (Localization.AtPrime q) :=
      Module.FaithfullyFlat.of_flat_of_isLocalHom
    simpa using
      ringKrullDim_le_of_surjective_comap_of_specializing_or_generalizing
        (algebraMap (Localization.AtPrime (q.under P)) (Localization.AtPrime q))
        PrimeSpectrum.comap_surjective_of_faithfullyFlat
        (.inr <| iff_generalizingMap_primeSpectrumComap.mp inferInstance)
  -- Étaleness supplies quasi-finiteness at every prime, giving the reverse inequality.
  have hBP :
      ringKrullDim (Localization.AtPrime q) ≤
        ringKrullDim (Localization.AtPrime (q.under P)) := by
    simpa using ringKrullDim_localizationAtPrime_le_of_quasiFiniteAt q
  exact le_antisymm hPB hBP

omit [Algebra k A] [IsScalarTower k P A] in
/-- Helper for Chap10 Lemma 10 151 9: étaleness over the polynomial algebra gives the expected
dimension for every maximal localization of `A`. -/
lemma localRingDimension_eq_of_etale_mvPolynomial [Etale P A] :
    ∀ m : MaximalSpectrum A, ringKrullDim (Localization.AtPrime m.asIdeal) = n := by
  intro m
  have hunder : (m.asIdeal.under P).IsMaximal :=
    maximalSpectrum_under_mvPolynomial_isMaximal (k := k) (A := A) (n := n) m
  let p : MaximalSpectrum P := ⟨m.asIdeal.under P, hunder⟩
  -- The contracted prime is maximal in affine `n`-space, so its local ring has dimension `n`.
  have hbase : ringKrullDim (Localization.AtPrime (m.asIdeal.under P)) = n := by
    simpa [p] using ringKrullDim_localizationAtMaximal_mvPolynomial (m := p)
  have hcompare :
      ringKrullDim (Localization.AtPrime (m.asIdeal.under P)) =
        ringKrullDim (Localization.AtPrime m.asIdeal) := by
    exact
      ringKrullDim_localizationAtPrime_eq_of_etale_mvPolynomialBase
        (k := k) (B := A) (n := n) m.asIdeal
  exact hcompare ▸ hbase

omit [IsScalarTower k P A] [FiniteType P A] in
/-- Helper for Chap10 Lemma 10 151 9: if the coordinate differentials span globally, then at
every prime the Kähler fiber has dimension at most the number of coordinates. -/
lemma kaehlerFiber_finrank_le_of_coordinateDifferentials_span
    (q : Ideal A) [q.IsPrime]
    (hspan : Submodule.span A
      (Set.range fun i : Fin n ↦ D k A (algebraMap P A (X i))) = ⊤) :
    Module.finrank (Ideal.ResidueField q)
      (TensorProduct A (Ideal.ResidueField q) Ω[A⁄k]) ≤ n := by
  let K := Ideal.ResidueField q
  -- Base-change the global spanning equality to the residue field at `q`.
  have hbase := congrArg (Submodule.baseChange K) hspan
  rw [Submodule.baseChange_span, Submodule.baseChange_top] at hbase
  have himage :
      (fun a : Ω[A⁄k] ↦ (1 : K) ⊗ₜ[A] a) ''
          Set.range (fun i : Fin n ↦ D k A (algebraMap P A (X i))) =
        Set.range (fun i : Fin n ↦ (1 : K) ⊗ₜ[A] D k A (algebraMap P A (X i))) := by
    ext x
    constructor
    · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨D k A (algebraMap P A (X i)), ⟨i, rfl⟩, rfl⟩
  have hspanK :
      Submodule.span K
        (Set.range (fun i : Fin n ↦ (1 : K) ⊗ₜ[A] D k A (algebraMap P A (X i)))) = ⊤ := by
    simpa [himage] using hbase
  -- A vector space spanned by a `Fin n`-indexed family has finrank at most `n`.
  simpa [Fintype.card_fin] using finrank_le_of_span_eq_top hspanK

/-- Helper for Chap10 Lemma 10 151 9: the local dimension equality and coordinate-differential
spanning imply smoothness over the ground field at each maximal ideal. -/
lemma isSmoothAt_maximal_of_localRingDimension_eq_and_coordinateDifferentials_span
    (hdim : ∀ m : MaximalSpectrum A, ringKrullDim (Localization.AtPrime m.asIdeal) = n)
    (hspan : Submodule.span A
      (Set.range fun i : Fin n ↦ D k A (algebraMap P A (X i))) = ⊤)
    (m : MaximalSpectrum A) :
    IsSmoothAt k m.asIdeal := by
  letI : Algebra.FiniteType k A :=
    finiteType_over_base_of_mvPolynomial_finiteType (k := k) (A := A) n
  -- The fiber finrank bound becomes the middle condition in the smoothness TFAE after using
  -- the assumed local dimension equality at `m`.
  have hle :=
    kaehlerFiber_finrank_le_of_coordinateDifferentials_span
      (k := k) (A := A) (n := n) m.asIdeal hspan
  have hleDim :
      Module.finrank (Ideal.ResidueField m.asIdeal)
        (TensorProduct A (Ideal.ResidueField m.asIdeal) Ω[A⁄k]) ≤
          ringKrullDim (Localization.AtPrime m.asIdeal) := by
    simpa [hdim m] using hle
  exact
    ((isSmoothAt_tfae_finrank_kaehlerFiber_le_eq
      (k := k) (S := A) m.asIdeal).out 0 1).mpr hleDim

/-- Helper for Chap10 Lemma 10 151 9: the same hypotheses make every maximal localization a
regular local ring. -/
lemma isRegularLocalRing_maximalLocalization_of_localRingDimension_eq_and_coordinateDifferentials_span
    (hdim : ∀ m : MaximalSpectrum A, ringKrullDim (Localization.AtPrime m.asIdeal) = n)
    (hspan : Submodule.span A
      (Set.range fun i : Fin n ↦ D k A (algebraMap P A (X i))) = ⊤)
    (m : MaximalSpectrum A) :
    IsRegularLocalRing (Localization.AtPrime m.asIdeal) := by
  letI : Algebra.FiniteType k A :=
    finiteType_over_base_of_mvPolynomial_finiteType (k := k) (A := A) n
  -- Smoothness at `m` over the field gives regularity of the local ring by Lemma 10.140.3.
  exact isRegularLocalRing_of_isSmoothAt m.asIdeal
    (isSmoothAt_maximal_of_localRingDimension_eq_and_coordinateDifferentials_span
      (k := k) (A := A) (n := n) hdim hspan m)

/-- Helper for Chap10 Lemma 10 151 9: the local dimension condition and coordinate-differential
generation imply flatness over the polynomial algebra. -/
lemma flat_of_localRingDimension_eq_and_coordinateDifferentials_span_mvPolynomial
    (hdim : ∀ m : MaximalSpectrum A, ringKrullDim (Localization.AtPrime m.asIdeal) = n)
    (hspan : Submodule.span A
      (Set.range fun i : Fin n ↦ D k A (algebraMap P A (X i))) = ⊤) :
    Module.Flat P A := by
  letI : Algebra.QuasiFinite P A :=
    quasiFinite_of_coordinateDifferentials_span_mvPolynomial hspan
  have hregular :
      ∀ m : MaximalSpectrum A, IsRegularLocalRing (Localization.AtPrime m.asIdeal) := by
    intro m
    -- The checked prefix reaches the maximal-local regularity input expected by the flat-locus
    -- or miracle-flatness bridge.
    exact
      isRegularLocalRing_maximalLocalization_of_localRingDimension_eq_and_coordinateDifferentials_span
        (k := k) (A := A) (n := n) hdim hspan m
  -- TODO: apply the local miracle-flatness or flat-locus criterion to turn the quasi-finite
  -- polynomial presentation, the maximal-local regularity facts `hregular`, and the dimension
  -- equalities `hdim` into global flatness over `P`. The missing dependency is the packaged
  -- bridge from these local regularity/dimension facts to `Module.Flat P A`.
  sorry

/- Domain-style sampling for Lemma 10.151.9:
- primary domain: finite-type étale criteria over a polynomial algebra over a field, combining the
  canonical étale owner with maximal-local dimension and Kähler-differential generation data;
- sampled owner declarations:
  `Algebra.Etale`,
  `etale_iff_flat_and_gUnramified`,
  `KaehlerDifferential.mvPolynomialBasis`,
  `ringKrullDim_localizationAtMaximal_mvPolynomial`;
- best owner abstraction: the core/canonical owner is `Algebra.Etale P A`; the local dimension
  clause on `MaximalSpectrum A` and the spanning condition for the coordinate differentials are
  bridge/view data encoding the source criterion, not a second owner abstraction;
- primitive data vs. derived API: the primitive source-facing data are the maximal-local dimension
  requirement and the generating family `D k A (algebraMap P A (X i))`. Unramifiedness, flatness,
  regular-locality, and finite presentation are derived owner-level consequences routed through
  `Etale`, `GUnramified`, and the chapter’s regular-local API.

Source/core/bridge triage:
- `source-facing`: the Stacks criterion below;
- `core/canonical`: `Algebra.Etale P A`;
- `bridge/view`: the maximal-spectrum local-dimension clause and the coordinate-differential span
  clause.
-/

-- Proof sketch: for the forward implication, étaleness gives unramifiedness and flatness. The
-- exact sequence for Kähler differentials of `k → k[x₁, …, xₙ] → A` identifies
-- `Ω[A⁄MvPolynomial (Fin n) k]` with the quotient of `Ω[A⁄k]` by the span of the coordinate
-- differentials, so unramifiedness forces that span to be all of `Ω[A⁄k]`. Quasi-finiteness of an
-- étale map over the `n`-dimensional polynomial algebra then gives the dimension formula for the
-- maximal local rings. For the reverse implication, the spanning condition forces the relative
-- differential module over `MvPolynomial (Fin n) k` to vanish, hence the map is unramified; the
-- local dimension condition and the regularity criterion make every maximal localization regular,
-- yielding flatness, and Lemma `10.151.8` then upgrades flatness plus unramified finite
-- presentation to étaleness.
/-- Lemma 10.151.9: for a finite type `k[x_1, \ldots, x_n]`-algebra `A`, the structural map
`k[x_1, \ldots, x_n] → A` is étale if and only if the local ring `A_m` has Krull dimension `n`
for every maximal ideal `m ⊂ A`, and the differentials of the images of the coordinate variables
generate `Ω[A⁄k]` as an `A`-module. -/
@[stacks 0G1C]
theorem etale_mvPolynomial_iff_localRingDimension_eq_and_coordinateDifferentials_span :
    Etale P A ↔
      ((∀ m : MaximalSpectrum A, ringKrullDim (Localization.AtPrime m.asIdeal) = n) ∧
        Submodule.span A (Set.range fun i : Fin n ↦ D k A (algebraMap P A (X i))) = ⊤) := by
  constructor
  · intro hetale
    letI : Etale P A := hetale
    -- Étaleness gives the local dimension comparison by the remaining dimension helper, and
    -- formal unramifiedness gives generation of `Ω[A⁄k]` by the coordinate differentials.
    refine ⟨localRingDimension_eq_of_etale_mvPolynomial (k := k) (A := A) (n := n), ?_⟩
    exact coordinateDifferentials_span_top_iff_formallyUnramified_mvPolynomial.mpr inferInstance
  · rintro ⟨hdim, hspan⟩
    letI : FinitePresentation P A := finitePresentation_mvPolynomial_algebra_of_finiteType
    letI : FormallyUnramified P A :=
      coordinateDifferentials_span_top_iff_formallyUnramified_mvPolynomial.mp hspan
    letI : Module.Flat P A :=
      flat_of_localRingDimension_eq_and_coordinateDifferentials_span_mvPolynomial hdim hspan
    -- Once finite presentation, formal unramifiedness, and flatness are in the instance context,
    -- the standard étale criterion closes the reverse implication.
    exact Etale.of_formallyUnramified_of_flat

end

end Algebra
