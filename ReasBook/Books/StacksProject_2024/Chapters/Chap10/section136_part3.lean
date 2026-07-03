import Mathlib
import Mathlib.RingTheory.Extension.Cotangent.Basis
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_10_136_9 (from Chap10) -/
open scoped TensorProduct

universe u v w

section

namespace Algebra

variable {R : Type u} {R' : Type v} {Rf : Type v} {S : Type w}
variable [CommRing R] [CommRing R'] [CommRing Rf] [CommRing S]
variable [Algebra R S] [Algebra R R'] [Algebra R Rf]

namespace Presentation

/-- Helper for Lemma 10.136.9: relative-global-complete-intersection presentations remain such
after arbitrary base change. -/
theorem IsRelativeGlobalCompleteIntersection.baseChange
    {n c : ℕ} {P : Algebra.Presentation R S (Fin n) (Fin c)}
    (hP : P.IsRelativeGlobalCompleteIntersection) :
    (P.baseChange R').IsRelativeGlobalCompleteIntersection := by
  intro p' hp'
  let p : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R R') p'
  let Pp : Algebra.Presentation p.asIdeal.ResidueField (p.asIdeal.Fiber S) (Fin n) (Fin c) :=
    P.baseChange p.asIdeal.ResidueField
  let e : p'.asIdeal.Fiber (R' ⊗[R] S) ≃ₐ[p'.asIdeal.ResidueField]
      p'.asIdeal.ResidueField ⊗[p.asIdeal.ResidueField] (p.asIdeal.Fiber S) :=
    (Algebra.TensorProduct.cancelBaseChange _ _ _ _ _).trans
      (Algebra.TensorProduct.cancelBaseChange _ _ _ _ _).symm
  have hp_nonempty : Nonempty (PrimeSpectrum (p.asIdeal.Fiber S)) := by
    -- Transport one prime of the new fiber to the scalar-extended old fiber, then contract it.
    rcases hp' with ⟨q'⟩
    let j :
        p.asIdeal.Fiber S →ₐ[p.asIdeal.ResidueField]
          p'.asIdeal.ResidueField ⊗[p.asIdeal.ResidueField] (p.asIdeal.Fiber S) :=
      Algebra.TensorProduct.includeRight
    let qTensor :
        PrimeSpectrum
          (p'.asIdeal.ResidueField ⊗[p.asIdeal.ResidueField] (p.asIdeal.Fiber S)) :=
      (PrimeSpectrum.comapEquiv e.toRingEquiv) q'
    exact ⟨PrimeSpectrum.comap j.toRingHom qTensor⟩
  haveI : Algebra.FinitePresentation p.asIdeal.ResidueField (p.asIdeal.Fiber S) := by
    simpa [Pp] using Pp.finitePresentation_of_isFinite
  haveI : Algebra.FiniteType p.asIdeal.ResidueField (p.asIdeal.Fiber S) := inferInstance
  -- Compare the new fiber with the old one after extending scalars between residue fields.
  calc
    ringKrullDim (p'.asIdeal.Fiber (R' ⊗[R] S))
        = ringKrullDim (p'.asIdeal.ResidueField ⊗[p.asIdeal.ResidueField] (p.asIdeal.Fiber S)) := by
          rw [ringKrullDim_eq_of_ringEquiv e.toRingEquiv]
    _ = ringKrullDim (p.asIdeal.Fiber S) := by
          symm
          exact ringKrullDim_tensorProduct_eq_of_fieldExtension
    _ = P.dimension := hP p hp_nonempty
    _ = (P.baseChange R').dimension := by
          simp [Algebra.Presentation.dimension]

/-- Helper for Lemma 10.136.9: transporting a relative global complete intersection across an
algebra equivalence preserves the property. -/
theorem IsRelativeGlobalCompleteIntersection.of_algEquiv
    {A : Type*} [CommRing A] [Algebra R A]
    {B : Type*} [CommRing B] [Algebra R B]
    (hA : Algebra.IsRelativeGlobalCompleteIntersection R A) (e : A ≃ₐ[R] B) :
    Algebra.IsRelativeGlobalCompleteIntersection R B := by
  rcases hA.exists_presentation with ⟨n, c, P, hP⟩
  refine Algebra.Presentation.toIsRelativeGlobalCompleteIntersection (P := P.ofAlgEquiv e) ?_
  intro p hp
  let ep : p.asIdeal.Fiber B ≃ₐ[R] p.asIdeal.Fiber A :=
    Algebra.TensorProduct.congr
      (AlgEquiv.refl : p.asIdeal.ResidueField ≃ₐ[R] p.asIdeal.ResidueField)
      e.symm
  have hpA : Nonempty (PrimeSpectrum (p.asIdeal.Fiber A)) := by
    -- Fiber nonemptiness is invariant under the induced tensor-product equivalence.
    have hp_nontrivial : Nontrivial (p.asIdeal.Fiber B) :=
      PrimeSpectrum.nonempty_iff_nontrivial.mp hp
    let _ : Nontrivial (p.asIdeal.Fiber B) := hp_nontrivial
    have hpA_nontrivial : Nontrivial (p.asIdeal.Fiber A) :=
      RingHom.domain_nontrivial ep.symm.toRingHom
    exact PrimeSpectrum.nonempty_iff_nontrivial.mpr hpA_nontrivial
  -- The source and target fibers are canonically tensor-congruent over the same residue field.
  calc
    ringKrullDim (p.asIdeal.Fiber B) = ringKrullDim (p.asIdeal.Fiber A) := by
      simpa [ep] using (ringKrullDim_eq_of_ringEquiv ep.toRingEquiv)
    _ = P.dimension := hP p hpA
    _ = (P.ofAlgEquiv e).dimension := by
      exact_mod_cast P.dimension_ofAlgEquiv e

end Presentation

namespace IsRelativeGlobalCompleteIntersection

-- Proof sketch: choose a finite presentation witness for `S` over `R`, base change that
-- presentation along `R → R'` using `Algebra.Presentation.baseChange`, and identify the fibers of
-- the new presentation with the base changes of the original fibers to transport the dimension
-- condition via Lemma 10.116.5.
/-- Lemma 10.136.9 (1): relative global complete intersections are stable under base change. -/
theorem baseChange (hS : IsRelativeGlobalCompleteIntersection R S) :
    IsRelativeGlobalCompleteIntersection R' (R' ⊗[R] S) := by
  rcases hS.exists_presentation with ⟨n, c, P, hP⟩
  -- Package the source presentation-level base-change witness back into the intrinsic owner.
  exact Algebra.Presentation.toIsRelativeGlobalCompleteIntersection
    (Algebra.Presentation.IsRelativeGlobalCompleteIntersection.baseChange
      (R' := R') hP)

-- Proof sketch: write `Localization.Away g` as a localization of the chosen presentation of `S`,
-- realized by adjoining one generator and one relation `h * X - 1`, and then check that each
-- fiber is the corresponding localization of the original fiber, so the presentation dimension is
-- unchanged.
/-- Lemma 10.136.9 (2): localizing away from an element of a relative global complete
intersection again yields a relative global complete intersection over the same base. -/
theorem localizationAway (hS : IsRelativeGlobalCompleteIntersection R S) (g : S) :
    IsRelativeGlobalCompleteIntersection R (Localization.Away g) := by
  rcases hS.exists_presentation with ⟨n, c, P, hP⟩
  let Q : Algebra.Presentation R (Localization.Away g)
      (Fin (Fintype.card (Unit ⊕ Fin n))) (Fin (Fintype.card (Unit ⊕ Fin c))) :=
    ((Algebra.Presentation.localizationAway (Localization.Away g) g).comp P).reindex
      (Fintype.equivFin (Unit ⊕ Fin n)).symm
      (Fintype.equivFin (Unit ⊕ Fin c)).symm
  refine Algebra.Presentation.toIsRelativeGlobalCompleteIntersection (P := Q) ?_
  intro p hp
  let _ : Algebra S (p.asIdeal.Fiber S) := Algebra.TensorProduct.rightAlgebra
  let e : p.asIdeal.Fiber (Localization.Away g) ≃ₐ[p.asIdeal.ResidueField]
      Localization.Away (algebraMap S (p.asIdeal.Fiber S) g) :=
    RingHom.fiber_localizationAway_algEquiv (R := R) (S := S) p g
  have hp_nonempty : Nonempty (PrimeSpectrum (p.asIdeal.Fiber S)) := by
    -- Transport one prime of the localized fiber through the canonical equivalence and contract it.
    rcases hp with ⟨q⟩
    let qLoc : PrimeSpectrum (Localization.Away (algebraMap S (p.asIdeal.Fiber S) g)) :=
      (PrimeSpectrum.comapEquiv e.toRingEquiv) q
    exact ⟨PrimeSpectrum.comap
      (algebraMap (p.asIdeal.Fiber S) (Localization.Away (algebraMap S (p.asIdeal.Fiber S) g)))
      qLoc⟩
  have hloc_nontrivial :
      Nontrivial (Localization.Away (algebraMap S (p.asIdeal.Fiber S) g)) := by
    have hp_nontrivial : Nontrivial (p.asIdeal.Fiber (Localization.Away g)) :=
      PrimeSpectrum.nonempty_iff_nontrivial.mp hp
    let _ : Nontrivial (p.asIdeal.Fiber (Localization.Away g)) := hp_nontrivial
    exact RingHom.domain_nontrivial e.symm.toRingHom
  let _ : Nontrivial (Localization.Away (algebraMap S (p.asIdeal.Fiber S) g)) := hloc_nontrivial
  -- Reindex the localized presentation and reuse the field-valued localization bound on each
  -- fiber.
  calc
    ringKrullDim (p.asIdeal.Fiber (Localization.Away g))
        = ringKrullDim (Localization.Away (algebraMap S (p.asIdeal.Fiber S) g)) := by
          rw [ringKrullDim_eq_of_ringEquiv e.toRingEquiv]
    _ =
        (IsGlobalCompleteIntersection.localized_comp_presentation
          (Sg := Localization.Away (algebraMap S (p.asIdeal.Fiber S) g))
          (algebraMap S (p.asIdeal.Fiber S) g)
          (P.baseChange p.asIdeal.ResidueField)).dimension := by
            exact
              IsGlobalCompleteIntersection.ringKrullDim_localized_comp_presentation
                (Sg := Localization.Away (algebraMap S (p.asIdeal.Fiber S) g))
                (algebraMap S (p.asIdeal.Fiber S) g)
                (P.baseChange p.asIdeal.ResidueField)
                (by
                  simpa [Algebra.Presentation.dimension] using hP p hp_nonempty)
    _ = (P.baseChange p.asIdeal.ResidueField).dimension := by
          simpa [Algebra.Presentation.dimension] using
            IsGlobalCompleteIntersection.localized_comp_presentation_dimension
              (Sg := Localization.Away (algebraMap S (p.asIdeal.Fiber S) g))
              (algebraMap S (p.asIdeal.Fiber S) g)
              (P.baseChange p.asIdeal.ResidueField)
    _ = P.dimension := by
          simp [Algebra.Presentation.dimension]
    _ = Q.dimension := by
          rw [show Q =
            ((Algebra.Presentation.localizationAway (Localization.Away g) g).comp P).reindex
              (Fintype.equivFin (Unit ⊕ Fin n)).symm
              (Fintype.equivFin (Unit ⊕ Fin c)).symm by
                rfl]
          rw [Algebra.Presentation.dimension_reindex]
          simp [Algebra.Presentation.dimension]
          omega

variable [Algebra Rf S] [IsScalarTower R Rf S]

-- Proof sketch: identify `S` with the base change `Rf ⊗[R] S` coming from the factorization
-- `R → Rf → S`, apply the base-change statement to `hS`, and transport the result across the
-- canonical localization tensor-product equivalence.
/-- Lemma 10.136.9 (3): if `R → S` factors through a localization `R_f`, then `S` is a relative
global complete intersection over `R_f`. -/
theorem of_isLocalizationAway (f : R) [IsLocalization.Away f Rf]
    (hS : IsRelativeGlobalCompleteIntersection R S) :
    IsRelativeGlobalCompleteIntersection Rf S := by
  have hbase : IsRelativeGlobalCompleteIntersection Rf (Rf ⊗[R] S) :=
    baseChange (R := R) (R' := Rf) hS
  let hu : IsUnit (algebraMap R S f) := by
    rw [show algebraMap R S f = algebraMap Rf S (algebraMap R Rf f) by
      rw [IsScalarTower.algebraMap_apply R Rf S]]
    exact (IsLocalization.Away.algebraMap_isUnit f).map (algebraMap Rf S)
  letI : IsLocalization.Away (algebraMap R S f) S :=
    IsLocalization.away_of_isUnit_of_bijective S hu Function.bijective_id
  letI : Algebra S (Rf ⊗[R] S) := Algebra.TensorProduct.rightAlgebra
  let eu : S ≃ₐ[S] Localization.Away (algebraMap R S f) :=
    IsLocalization.atUnit S (Localization.Away (algebraMap R S f)) (algebraMap R S f) hu
  let eS : Rf ⊗[R] S ≃ₐ[S] S :=
    (IsLocalization.Away.tensorRightEquiv S f Rf).trans eu.symm
  have hcomm :
      (eS : Rf ⊗[R] S →+* S).comp (algebraMap Rf (Rf ⊗[R] S)) = algebraMap Rf S := by
    -- Route correction: this is the same tensor-versus-localization compatibility used in the
    -- standard smooth localization argument, now only to transport the relative GCI owner.
    apply IsLocalization.ringHom_ext (Submonoid.powers f)
    ext r
    change eS (algebraMap Rf (Rf ⊗[R] S) (algebraMap R Rf r)) = algebraMap Rf S (algebraMap R Rf r)
    rw [← IsScalarTower.algebraMap_apply R Rf (Rf ⊗[R] S)]
    rw [← IsScalarTower.algebraMap_apply R Rf S]
    have hmap : algebraMap R (Rf ⊗[R] S) r = algebraMap S (Rf ⊗[R] S) (algebraMap R S r) :=
      IsScalarTower.algebraMap_apply R S (Rf ⊗[R] S) r
    rw [hmap]
    exact eS.commutes _
  let e : Rf ⊗[R] S ≃ₐ[Rf] S :=
    { __ := eS.toRingEquiv
      commutes' := by
        intro x
        exact RingHom.ext_iff.mp hcomm x }
  -- Transport the base-changed owner along the canonical tensor/localization equivalence.
  exact Algebra.Presentation.IsRelativeGlobalCompleteIntersection.of_algEquiv hbase e

end IsRelativeGlobalCompleteIntersection

end Algebra

end

/-! ### Lemma_10_136_10 (from Chap10) -/
open MvPolynomial
open scoped TensorProduct

universe u

section

variable {R : Type u} [CommRing R]
variable {n c : ℕ} (f : Fin c → MvPolynomial (Fin n) R)

/-
Domain-style sampling:
- primary domain: explicit polynomial presentations under localization away from one element;
- sampled owner declarations:
  `Algebra.IsRelativeGlobalCompleteIntersection`,
  `Algebra.IsRelativeGlobalCompleteIntersection.localizationAway`,
  `Algebra.Presentation.localizationAway`,
  `Algebra.Presentation.relation_comp_localizationAway_inl`;
- best owner abstraction:
  `Algebra.IsRelativeGlobalCompleteIntersection` remains the owner of the property, while the
  explicit quotient obtained by adjoining an inverse is the source-facing bridge/view for this
  lemma;
- primitive vs. derived:
  the primitive source-facing data are `h`, `g`, the explicit quotient presentation, and the
  comparison `Localization.Away g ≃ₐ[R] ...`; the relative-global-complete-intersection property
  should then be stated on that displayed quotient ring itself.
-/

local notation "PresentedIdeal" =>
  Ideal.span (Set.range f)

local notation "PresentedAlgebra" =>
  MvPolynomial (Fin n) R ⧸ PresentedIdeal

local notation "LocalizedPresentedAlgebra" =>
  fun h : MvPolynomial (Fin n) R ↦
    MvPolynomial (Fin (n + 1)) R ⧸
      Ideal.span
        (Set.range (fun i : Fin c ↦ rename Fin.castSuccEmb (f i)) ∪
          {rename Fin.castSuccEmb h * X (Fin.last n) - 1})

-- Proof sketch: apply Lemma `10.125.6` to the quotient map `(R / I) → (S / IS)` to find a basic
-- open neighbourhood of `V (IS)` on which all fibers have dimension at most `n - c`; choose
-- `g` cutting out the complementary closed set so that `g = 1` in `S / IS`, lift `g` to some
-- `h` in the polynomial ring, and use the standard presentation of `S_g` by adjoining an inverse
-- for `h` together with Definition `10.136.5`.
/-- Lemma 10.136.10 (1): if all fibers of `Spec (S / IS) → Spec (R / I)` have dimension `n - c`
for `S = R[x_1, \ldots, x_n] / (f_1, \ldots, f_c)`, then there exist `h` in the polynomial ring
and its image `g` in `S` such that `g = 1` in `S / IS`, the localization `S_g` is identified with
the explicit quotient obtained by adjoining an inverse for `h`, and that displayed quotient is a
relative global complete intersection over `R`. -/
theorem exists_relativeGlobalCompleteIntersection_localizationAway_of_fiberDimension_on_closedSet
    (I : Ideal R)
    (hdim : ∀ p : PrimeSpectrum R,
      I ≤ p.asIdeal →
        Nonempty (PrimeSpectrum (p.asIdeal.Fiber PresentedAlgebra)) →
          ringKrullDim (p.asIdeal.Fiber PresentedAlgebra) = (n - c : WithBot ℕ∞)) :
    ∃ (h : MvPolynomial (Fin n) R) (g : PresentedAlgebra)
      (_ : Localization.Away g ≃ₐ[R] LocalizedPresentedAlgebra h),
      Ideal.Quotient.mk PresentedIdeal h = g ∧
        Ideal.Quotient.mk (Ideal.map (algebraMap R PresentedAlgebra) I) g = 1 ∧
        Algebra.IsRelativeGlobalCompleteIntersection R (LocalizedPresentedAlgebra h) := sorry

-- Proof sketch: apply Lemma `10.125.6` to the fiber over `p` to obtain a basic open
-- neighbourhood of `Spec (S ⊗[R] κ(p))` on which all fibers have dimension at most `n - c`;
-- choose `g` whose image in the fiber ring is a unit, lift it to some `h`, and identify `S_g`
-- with the quotient obtained by adjoining an inverse for `h`, which is then a relative global
-- complete intersection by Definition `10.136.5`.
/-- Lemma 10.136.10 (2): if `dim (S ⊗[R] κ(p)) = n - c` for
`S = R[x_1, \ldots, x_n] / (f_1, \ldots, f_c)`, then there exist `h` in the polynomial ring and
its image `g` in `S` such that `g` becomes a unit in the fiber over `p`, the localization `S_g`
is identified with the explicit quotient obtained by adjoining an inverse for `h`, and that
displayed quotient is a relative global complete intersection over `R`. -/
theorem exists_relativeGlobalCompleteIntersection_localizationAway_of_fiberDimension_atPrime
    (p : PrimeSpectrum R)
    (hdim : ringKrullDim (p.asIdeal.Fiber PresentedAlgebra) = (n - c : WithBot ℕ∞)) :
    ∃ (h : MvPolynomial (Fin n) R) (g : PresentedAlgebra)
      (_ : Localization.Away g ≃ₐ[R] LocalizedPresentedAlgebra h),
      Ideal.Quotient.mk PresentedIdeal h = g ∧
        IsUnit (1 ⊗ₜ[R] g : p.asIdeal.Fiber PresentedAlgebra) ∧
        Algebra.IsRelativeGlobalCompleteIntersection R (LocalizedPresentedAlgebra h) := sorry

-- Proof sketch: use Lemma `10.125.6` at the prime `q` to find a principal open neighbourhood on
-- which the relative dimension is at most `n - c`; choose a generator `g` of that neighbourhood
-- with `g ∉ q`, lift it to some `h` in the polynomial ring, and then use the standard
-- localization presentation together with Definition `10.136.5`.
/-- Lemma 10.136.10 (3): if `dim_q (S / R) = n - c` for
`S = R[x_1, \ldots, x_n] / (f_1, \ldots, f_c)`, then there exist `h` in the polynomial ring and
its image `g` in `S` with `g ∉ q` such that the localization `S_g` is identified with the
explicit quotient obtained by adjoining an inverse for `h`, and that displayed quotient
presentation is a relative global complete intersection over `R`. -/
theorem exists_relativeGlobalCompleteIntersection_localizationAway_of_relativeDimensionAt
    (q : PrimeSpectrum PresentedAlgebra)
    (hdim : relativeDimensionAt R PresentedAlgebra q = (n - c : WithBot ℕ∞)) :
    ∃ (h : MvPolynomial (Fin n) R) (g : PresentedAlgebra)
      (_ : Localization.Away g ≃ₐ[R] LocalizedPresentedAlgebra h),
      Ideal.Quotient.mk PresentedIdeal h = g ∧
        g ∉ q.asIdeal ∧
        Algebra.IsRelativeGlobalCompleteIntersection R (LocalizedPresentedAlgebra h) := sorry

end

/-! ### Lemma_10_136_11 (from Chap10) -/
universe u

noncomputable section

section

namespace Algebra

variable {R : Type u} [CommRing R]

/- Domain-style sampling:
- primary domain: relative global complete intersections presented as explicit polynomial
  quotients, together with descent of coefficients to finite type `ℤ`-subalgebras;
- sampled owner declarations of the same kind:
  `Algebra.IsRelativeGlobalCompleteIntersection`,
  `Algebra.IsRelativeGlobalCompleteIntersection.exists_presentation`,
  `Algebra.instFinitePresentationOfIsRelativeGlobalCompleteIntersection`,
  `Algebra.IsRelativeGlobalCompleteIntersection.localizationAway`;
- best owner abstraction:
  the property being descended is the canonical chapter owner
  `Algebra.IsRelativeGlobalCompleteIntersection`; this lemma remains `source-facing` because the
  Stacks item also keeps track of explicit descended relations `f₀`, but those relations should
  serve only to describe the descended quotient ring, not to replace the owner-level predicate by
  one unpacked field of it;
- primitive vs. derived:
  the primitive source-facing data are the descended coefficient subalgebra and the lifted
  relations `f₀`; the fact that the descended quotient is a relative global complete intersection
  is the main owner-level conclusion, while any particular fiber-dimension formula for that
  displayed presentation is derived API.

Source/core/bridge triage:
- `source-facing`: descend the explicit quotient presentation by finitely many relations to a
  finite type `ℤ`-subalgebra;
- `core/canonical`: `Algebra.IsRelativeGlobalCompleteIntersection`;
- `bridge/view`: the explicit quotient description
  `MvPolynomial (Fin n) R₀ ⧸ Ideal.span (Set.range f₀)` of that descended model.
-/

-- Proof sketch: let `R₀` be the `ℤ`-subalgebra of `R` generated by the finitely many coefficients
-- of the `f i`. Choose lifts `f₀ i` of the relations to `MvPolynomial (Fin n) R₀`. For each
-- prime of the descended quotient, reduce to the owner-level relative-global-complete-
-- intersection condition on a finite type stage and enlarge `R₀` until the descended quotient
-- itself carries that owner predicate.
/-- Lemma 10.136.11: if the displayed quotient
`R[x₁, …, xₙ] / (f₁, …, f_c)` is a relative global complete intersection over `R`, then the
finitely many relations `fᵢ` descend to a finite type `ℤ`-subalgebra `R₀ ⊆ R` such that the
descended quotient over `R₀` is again a relative global complete intersection. -/
theorem exists_finiteType_zSubalgebra_of_relativeGCIQuotient
    {n c : ℕ} (f : Fin c → MvPolynomial (Fin n) R)
    (hfgci :
      IsRelativeGlobalCompleteIntersection R (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f))) :
    ∃ (R₀ : Subalgebra ℤ R) (_ : Algebra.FiniteType ℤ R₀)
      (f₀ : Fin c → MvPolynomial (Fin n) R₀),
        (∀ i, MvPolynomial.map R₀.val (f₀ i) = f i) ∧
          IsRelativeGlobalCompleteIntersection R₀
            (MvPolynomial (Fin n) R₀ ⧸ Ideal.span (Set.range f₀)) := sorry

end Algebra

end

/-! ### Lemma_10_136_12 (from Chap10) -/
universe u

open RingTheory Sequence

namespace Algebra

noncomputable section

section

variable {R : Type u} [CommRing R]
variable {n c : ℕ}

/- Domain-style sampling:
- primary domain: relative global complete intersections for explicit polynomial quotients,
  localized at primes and analyzed through regular sequences and conormal modules;
- sampled owner declarations:
  `Algebra.Presentation.naive`,
  `Algebra.Presentation.IsRelativeGlobalCompleteIntersection`,
  `Algebra.Presentation.toIsRelativeGlobalCompleteIntersection`,
  `PrimeSpectrum.comap`,
  `Ideal.Cotangent`;
- best owner abstraction:
  for the displayed quotient `R[x₁, …, xₙ] / (f₁, …, f_c)`, the source-facing owner layer is the
  naive presentation determined by `f` together with the presentation-level predicate
  `Algebra.Presentation.IsRelativeGlobalCompleteIntersection`; the intrinsic class
  `Algebra.IsRelativeGlobalCompleteIntersection R S` is only the bridge obtained by forgetting
  which presentation witnesses the fiber-dimension formula;
- primitive vs. derived:
  the primitive source-facing data are the relations `f`; the quotient map, the prime lying over a
  quotient prime, the localized polynomial ring, and the cotangent classes are derived API and
  should not be rebuilt as parallel public wrappers.

Source/core/bridge triage:
- `source-facing`: the three clauses of Lemma `10.136.12` for the explicit quotient
  `R[x₁, …, xₙ] / (f₁, …, f_c)`;
- `core/canonical`: the naive presentation of that quotient, equipped with
  `Algebra.Presentation.IsRelativeGlobalCompleteIntersection`, and the ambient owners
  `PrimeSpectrum.comap` and `Ideal.Cotangent`;
- `bridge/view`: the localized relation list, the quotients by its initial segments, and the
  explicit cotangent classes of the `fᵢ`, all written directly in terms of the quotient,
  localization, and cotangent owners rather than through local wrapper names.
-/

variable (f : Fin c → MvPolynomial (Fin n) R)

local notation "PresentedIdeal" => Ideal.span (Set.range f)
local notation "PresentedAlgebra" => MvPolynomial (Fin n) R ⧸ PresentedIdeal
local notation "PresentedPresentation" =>
  (Algebra.Presentation.naive : Algebra.Presentation R PresentedAlgebra (Fin n) (Fin c))
local notation "PresentedCotangent" => Ideal.Cotangent PresentedIdeal

-- Proof sketch: view `S = R[x₁, …, xₙ] / (f₁, …, f_c)` as the chosen quotient presentation.
-- For a prime `q` of `S`, descend the relative global complete intersection hypothesis to a
-- finite type `ℤ`-subalgebra, apply the Noetherian fibrewise criterion of Lemma `10.99.3`, and
-- then transport the resulting regularity statement to the localization at the corresponding prime
-- `q'` of the polynomial ring.
/-- Lemma 10.136.12 (1): for a relative global complete intersection presentation
`S = R[x₁, …, xₙ] / (f₁, …, f_c)` and a prime `q` of `S`, the defining equations `f₁, …, f_c`
form a regular sequence in the local ring `R[x₁, …, xₙ]_{q'}`, where `q'` is the prime of the
polynomial ring lying over `q`. -/
theorem relativeGCI_localized_relations_isRegular
    (hP : Algebra.Presentation.IsRelativeGlobalCompleteIntersection PresentedPresentation)
    (q : PrimeSpectrum PresentedAlgebra) :
    let q' := PrimeSpectrum.comap (Ideal.Quotient.mk PresentedIdeal) q
    let A := Localization.AtPrime q'.asIdeal
    Sequence.IsRegular A ((List.ofFn f).map (algebraMap (MvPolynomial (Fin n) R) A)) := sorry

-- Proof sketch: after proving part (1), apply the same Noetherian reduction together with
-- Lemma `10.99.3` to each nonempty prefix of the localized sequence. This yields flatness of the
-- successive quotients over the base ring `R`, and filtered-colimit exactness descends the result
-- from the finite type `ℤ`-subalgebras to the original ring.
/-- Lemma 10.136.12 (2): with the same presentation and prime `q`, every quotient
`R[x₁, …, xₙ]_{q'} / (f₁, …, f_i)` by a nonempty initial segment of the defining equations is flat
over `R`. -/
theorem relativeGCI_localized_prefix_quotients_flat
    (hP : Algebra.Presentation.IsRelativeGlobalCompleteIntersection PresentedPresentation)
    (q : PrimeSpectrum PresentedAlgebra) :
    let q' := PrimeSpectrum.comap (Ideal.Quotient.mk PresentedIdeal) q
    let A := Localization.AtPrime q'.asIdeal
    ∀ i : Fin c,
      Module.Flat R
        (A ⧸ Ideal.ofList (List.take (i + 1) ((List.ofFn f).map (algebraMap (MvPolynomial (Fin n) R) A)))) := sorry

-- Proof sketch: by part (1), the sequence `f₁, …, f_c` is regular in every localization of the
-- quotient presentation. Lemma `10.69.2` upgrades regularity to quasi-regularity, so the images of
-- the `fᵢ` generate the localized conormal module as a basis at every prime. Then apply the local
-- criterion for freeness from Lemma `10.23.1` to globalize those local bases.
/-- Lemma 10.136.12 (3): for a relative global complete intersection presentation
`S = R[x₁, …, xₙ] / (f₁, …, f_c)`, the conormal module `(f₁, …, f_c) / (f₁, …, f_c)^2` is free
over `S`, with basis given by the classes of the defining equations `fᵢ mod (f₁, …, f_c)^2`. -/
theorem relativeGCI_conormalModule_has_basis
    (hP : Algebra.Presentation.IsRelativeGlobalCompleteIntersection PresentedPresentation) :
    ∃ b : Module.Basis (Fin c) PresentedAlgebra PresentedCotangent,
      ∀ i,
        b i =
          Ideal.toCotangent PresentedIdeal ⟨f i, Ideal.subset_span (Set.mem_range_self i)⟩ := sorry

end

end

end Algebra

/-! ### Lemma_10_136_13 (from Chap10) -/
universe u v

namespace Algebra

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/- Domain-style sampling:
- primary domain: relative complete intersections and syntomic morphisms of commutative rings;
- sampled owner declarations:
  `RingHom.Syntomic`,
  `Algebra.IsRelativeGlobalCompleteIntersection`,
  `Algebra.Presentation.IsRelativeGlobalCompleteIntersection`,
  `Algebra.IsRelativeGlobalCompleteIntersection.baseChange`;
- best owner abstraction:
  `Algebra.IsRelativeGlobalCompleteIntersection R S` is the source-facing owner for the algebra,
  while `(algebraMap R S).Syntomic` is the canonical ring-hom owner on the conclusion side;
- primitive vs. derived:
  the relative global complete intersection witness is primitive data in the source-facing class,
  whereas syntomicity is derived API and should be exposed as a theorem under that owner rather
  than as a parallel standalone theorem name.
-/

namespace IsRelativeGlobalCompleteIntersection

-- Proof sketch: a relative global complete intersection is finitely presented by definition, and
-- each fiber is a global complete intersection, hence a local complete intersection. The only new
-- ingredient is flatness, which is obtained from the localized prefix-quotient flatness statement
-- of Lemma `10.136.12 (2)` after choosing a presentation locally at each prime of `S`.
/-- Lemma 10.136.13: a relative global complete intersection `R`-algebra is syntomic over `R`. -/
theorem syntomic (hS : IsRelativeGlobalCompleteIntersection R S) :
    (algebraMap R S).Syntomic := sorry

end IsRelativeGlobalCompleteIntersection

end

end Algebra

/-! ### Lemma_10_136_14 (from Chap10) -/
open scoped BigOperators
open Polynomial

universe u

namespace Polynomial

section

variable {A : Type u} [CommRing A]

/- Domain-style sampling:
* primary domain: splitting monic polynomials after finite flat base change in commutative algebra;
* sampled owner declarations:
  `Polynomial.Monic.exists_splits_map`,
  `Polynomial.Splits`,
  `Polynomial.Splits.eq_prod_roots_of_monic`,
  `RingHom.Syntomic`;
* best owner abstraction:
  the extension itself remains source-facing existential data, while the splitting conclusion
  should use the canonical owner `Polynomial.Splits`; the explicit linear-factor product is
  derived API from that owner for monic polynomials;
* primitive vs. derived:
  primitive data are the extension ring `A'` and its syntomic / finite free / faithfully flat
  structure over `A`; a chosen family of roots indexed by `Fin P.natDegree` is derived packaging
  and should not be primitive public output.
-/

-- Proof sketch: base change the universal elementary-symmetric factorization ring of Example
-- `10.136.8` along the map sending the elementary-symmetric coefficients to the coefficients of
-- `P`. The resulting algebra is finite free and faithfully flat by base change, and it is
-- syntomic by Lemma `10.136.13`. Its tautological roots show that
-- `P.map (algebraMap A A')` splits; the explicit linear-factor product is then derived from the
-- canonical owner lemma `Polynomial.Splits.eq_prod_roots_of_monic`.
/-- Lemma 10.136.14: a monic polynomial over `A` splits after a syntomic finite free faithfully
flat extension of `A`. -/
theorem exists_syntomic_finiteFree_faithfullyFlat_split_extension_of_monic
    (P : A[X]) (hP : P.Monic) :
    ∃ (A' : Type u) (_ : CommRing A') (_ : Algebra A A') (_ : (algebraMap A A').Syntomic)
      (_ : Module.Free A A') (_ : Module.Finite A A')
      (_ : (algebraMap A A').FaithfullyFlat),
      (P.map (algebraMap A A')).Splits := sorry

end

end Polynomial

/-! ### Lemma_10_136_15 (from Chap10) -/
noncomputable section

universe u v

namespace Algebra

open scoped TensorProduct
open Algebra.TensorProduct

section

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]

/-- The condition that some basic open neighbourhood of `q` is syntomic over `R`. -/
def SyntomicAtPrime (R : Type u) [CommRing R] {S : Type v} [CommRing S] [Algebra R S]
    (q : PrimeSpectrum S) : Prop :=
  ∃ g : S, g ∉ q.asIdeal ∧ (algebraMap R (Localization.Away g)).Syntomic

/-- The condition that some basic open neighbourhood of `q` is a relative global complete
intersection over `R`. -/
def RelativeGlobalCompleteIntersectionAtPrime (R : Type u) [CommRing R] {S : Type v} [CommRing S]
    [Algebra R S] (q : PrimeSpectrum S) : Prop :=
  ∃ g : S, g ∉ q.asIdeal ∧ IsRelativeGlobalCompleteIntersection R (Localization.Away g)

/-- The local fiber ring at `q` is a complete intersection over the residue field of the
contracted prime `q ∩ R`. -/
def FiberCompleteIntersectionAtPrime (R : Type u) [CommRing R] {S : Type v} [CommRing S]
    [Algebra R S] (q : PrimeSpectrum S) : Prop :=
  @IsCompleteIntersectionOver.{u, max u v, max u v}
    (q.asIdeal.under R).ResidueField (fiberLocalRingAt R S q) inferInstance inferInstance
    (fiberLocalRingAtResidueFieldAlgebra R S q)

/-- Some basic open neighbourhood of `q` is of finite presentation over `R`, the local map
`R_(q ∩ R) → S_q` is flat, and the local fiber ring at `q` is a complete intersection over
`κ(q ∩ R)`. -/
def FinitePresentationFlatAndFiberCompleteIntersectionAtPrime (R : Type u) [CommRing R]
    {S : Type v} [CommRing S] [Algebra R S] (q : PrimeSpectrum S) : Prop :=
  ∃ g : S, g ∉ q.asIdeal ∧
    FinitePresentation R (Localization.Away g) ∧
    (Localization.localRingHom (q.asIdeal.under R) q.asIdeal (algebraMap R S) rfl).Flat ∧
    FiberCompleteIntersectionAtPrime R q

-- Proof sketch: `(1) → (3)` is the local fiber criterion for syntomic morphisms, while
-- `(2) → (1)` is the earlier result that relative global complete intersections are syntomic.
-- For `(3) → (2)`, shrink around `q` so that a finite presentation of `S` is available, then use
-- the complete-intersection condition on the local fiber ring together with the standard
-- presentation-theoretic argument to obtain a relative global complete intersection after another
-- localization away from `q`.
/-- Lemma 10.136.15: for a prime `q` of `S` with contracted prime `q ∩ R`, the following are
equivalent: some basic open neighbourhood of `q` is syntomic over `R`; some basic open
neighbourhood of `q` is a relative global complete intersection over `R`; and some basic open
neighbourhood of `q` is of finite presentation over `R`, the local map
`R_(q ∩ R) → S_q` is flat, and the local fiber ring at `q` is a complete intersection over
`κ(q ∩ R)`. -/
theorem syntomicAtPrime_tfae
    (q : PrimeSpectrum S) :
    List.TFAE
      [ SyntomicAtPrime R q
      , RelativeGlobalCompleteIntersectionAtPrime R q
      , FinitePresentationFlatAndFiberCompleteIntersectionAtPrime R q
      ] := sorry

end

end Algebra

/-! ### Lemma_10_136_16 (from Chap10) -/
universe u

namespace Algebra

section

variable {R : Type u} [CommRing R]
variable {n : ℕ}

/- Domain-style sampling:
- primary domain: cotangent modules of explicit quotient presentations, localized away from one
  element, under the syntomic owner predicate on the localized ring map;
- sampled owner declarations:
  `RingHom.Syntomic`,
  `Ideal.Cotangent`,
  `LocalizedModule.Away`,
  `localized_presentation_cotangent_stable_equiv`;
- best owner abstraction: the public owner here is the pair of predicates
  `Module.Finite` / `Module.Projective` on the canonical localized cotangent module
  `LocalizedModule.Away g I.Cotangent`; the relative-global-complete-intersection presentation and
  the stable cotangent comparison are bridge/view input for the proof, not extra public data;
- primitive vs. derived:
  the primitive source-facing data are the quotient ideal `I` and the syntomic hypothesis on the
  localized quotient map `R → S_g`;
  a separate finite-generation hypothesis on `I` is derived proof input at most, not owner data
  for the localized conormal statement, so it should not remain in the public interface.

Source/core/bridge triage:
- `source-facing`: the Stacks lemma for an explicit quotient `S = R[x₁, …, xₙ] / I`;
- `core/canonical`: `RingHom.Syntomic`, `Ideal.Cotangent`, and `LocalizedModule.Away`;
- `bridge/view`: `syntomicAtPrime_tfae`, `relativeGCI_conormalModule_has_basis`, and
  `localized_presentation_cotangent_stable_equiv`.
-/

local notation "Poly" => MvPolynomial (Fin n) R

-- Proof sketch: by Lemma `10.136.15`, after refining the basic open `D(g)` we may assume the
-- localization is a relative global complete intersection over `R`. Lemma `10.136.12` then makes
-- the conormal module free for that refined presentation, and Lemma `10.134.16` transports this
-- finite projective structure back to the localization of the original conormal module.
/-- Lemma 10.136.16: let `S = R[x₁, …, xₙ] / I` with `I` finitely generated. If the localization
`S_g` is syntomic over `R`, then the localized conormal module `(I / I²)_g` is a finite
projective `S_g`-module. -/
theorem idealCotangent_localizedAway_finiteProjective_of_syntomic
    (I : Ideal Poly) (g : Poly ⧸ I)
    (hsyntomic : (algebraMap R (Localization.Away g)).Syntomic) :
    Module.Finite (Localization.Away g) (LocalizedModule.Away g I.Cotangent) ∧
      Module.Projective (Localization.Away g) (LocalizedModule.Away g I.Cotangent) := sorry

end

end Algebra

/-! ### Lemma_10_136_17 (from Chap10) -/
universe u v w

section

/- Domain-style sampling:
- primary domain: composition stability for syntomic ring maps and relative global complete
  intersections in commutative algebra;
- inspected owner declarations:
  `RingHom.Syntomic`,
  `RingHom.Flat.comp`,
  `RingHom.FinitePresentation.comp`,
  `RingHom.Syntomic.ofLocalizationSpanTarget`,
  `Algebra.IsRelativeGlobalCompleteIntersection`,
  `Algebra.IsRelativeGlobalCompleteIntersection.baseChange`;
- best owner abstractions:
  `RingHom.Syntomic` is a ring-hom property, so its canonical composition API should expose the
  owner-namespace theorem `RingHom.Syntomic.comp`, with the bundled witness
  `RingHom.Syntomic.stableUnderComposition` as derived API;
  `Algebra.IsRelativeGlobalCompleteIntersection R S` is already the source-facing algebra owner,
  so composition belongs in the owner namespace rather than as a parallel freestanding theorem;
- primitive vs. derived:
  flatness, finite presentation, and chosen presentation data remain derived API from the two
  owners and should not be repackaged here.
-/

namespace RingHom

variable {R : Type u} {S : Type v} {S' : Type w}
variable [CommRing R] [CommRing S] [CommRing S']

namespace Syntomic

-- Proof sketch: the composition of syntomic morphisms is flat by `RingHom.Flat.comp` and finitely
-- presented by `RingHom.FinitePresentation.comp`. For the fiber condition, apply the relative
-- global complete intersection neighborhood criterion from Lemma `10.136.15` and then the
-- composition statement for relative global complete intersections from part `(2)`.
/-- Lemma 10.136.17 (1): the composition of syntomic ring maps is syntomic. -/
theorem comp {f : R →+* S} {g : S →+* S'} (hf : f.Syntomic) (hg : g.Syntomic) :
    (g.comp f).Syntomic := by
  sorry

/-- Companion meta-property witness for Lemma 10.136.17 (1). -/
theorem stableUnderComposition : RingHom.StableUnderComposition RingHom.Syntomic := by
  intro R S T _ _ _ f g hf hg
  exact hf.comp hg

end Syntomic

end RingHom

namespace Algebra

variable {R : Type u} {S : Type v} {S' : Type w}
variable [CommRing R] [CommRing S] [CommRing S']
variable [Algebra R S] [Algebra S S'] [Algebra R S'] [IsScalarTower R S S']

namespace IsRelativeGlobalCompleteIntersection

-- Proof sketch: choose relative global complete intersection presentations for `S` over `R` and
-- for `S'` over `S`, concatenate the generators and lifted relations to obtain a presentation of
-- `S'` over `R`, and then bound the fiber dimensions by additivity of dimensions along the finite
-- type map between the fibers.
/-- Lemma 10.136.17 (2): relative global complete intersections are stable under composition. -/
theorem comp (hRS : IsRelativeGlobalCompleteIntersection R S)
    (hSS' : IsRelativeGlobalCompleteIntersection S S') :
    IsRelativeGlobalCompleteIntersection R S' := sorry

end IsRelativeGlobalCompleteIntersection

end Algebra

end

/-! ### Lemma_10_136_18 (from Chap10) -/
universe u v

namespace Algebra

section

variable {R : Type u} [CommRing R] (I : Ideal R)
variable {Sbar : Type v} [CommRing Sbar] [Algebra (R ⧸ I) Sbar]

-- Proof sketch: apply Lemma `10.136.15` to obtain a cover of `Spec S̄` by basic opens on which
-- the localization is a relative global complete intersection over `R ⧸ I`. For each such
-- localization, choose a presentation from Definition `10.136.5`, lift the defining equations to
-- `R`, form the corresponding quotient algebra over `R`, and then use Lemma `10.136.10` to shrink
-- once more so that this lift is itself a relative global complete intersection over `R`.
/-- Lemma 10.136.18: a syntomic `(R ⧸ I)`-algebra admits a unit-ideal cover by basic opens whose
localizations are reductions modulo `I` of relative global complete intersections over `R`. -/
theorem exists_relativeGlobalCompleteIntersection_lift_cover_of_quotient_syntomic
    (hSbar : (algebraMap (R ⧸ I) Sbar).Syntomic) :
    ∃ s : Set Sbar, Ideal.span s = ⊤ ∧
      ∀ g ∈ s, ∃ (S : Type (max u v)) (_ : CommRing S) (_ : Algebra R S)
        (_ : IsRelativeGlobalCompleteIntersection R S),
          Nonempty ((Localization.Away g) ≃ₐ[R ⧸ I] (S ⧸ Ideal.map (algebraMap R S) I)) := sorry

end

end Algebra
