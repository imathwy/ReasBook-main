import Mathlib
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_15_14_1 (from Chap15) -/
open Polynomial

universe u

/-
Definition 15.14.1 is `source-facing`: mathlib does not already provide an owner predicate for an
absolutely integrally closed commutative ring. The primitive data are exactly the canonical
polynomial splitting predicate on monic polynomials. The sampled canonical declarations in the same
domain are `Polynomial.Splits`, `IsAlgClosed`, and `IsAlgClosed.exists_root`; the owner here keeps
the ring-level source notion primitive, with root-existence API derived below.
-/
/-- Definition 15.14.1: a commutative ring `A` is absolutely integrally closed if every monic
polynomial over `A` splits, equivalently if every monic polynomial is a product of linear
factors. -/
class IsAbsolutelyIntegrallyClosed (A : Type u) [CommRing A] : Prop where
  splits (f : A[X]) (_ : f.Monic) : f.Splits

/-- An algebraically closed field is absolutely integrally closed. -/
instance {A : Type u} [Field A] [IsAlgClosed A] : IsAbsolutelyIntegrallyClosed A where
  splits f _ := IsAlgClosed.splits f

section

variable {A : Type u} [CommRing A]

/-- A monic polynomial over `A` splits if every monic polynomial of nonzero degree has a root. -/
private theorem splits_of_forall_monic_nonzero_degree_has_root
    (hroot : ∀ (f : A[X]) (_ : f.Monic) (_ : f.degree ≠ 0), ∃ a : A, f.IsRoot a) :
    ∀ f : A[X], f.Monic → f.Splits := by
  let P : ℕ → Prop := fun n ↦ ∀ f : A[X], f.natDegree = n → f.Monic → f.Splits
  have hP : ∀ n, P n := by
    intro n
    exact Nat.strong_induction_on n fun n ih f hdeg hf ↦ by
      by_cases hn : n = 0
      · exact Polynomial.splits_of_natDegree_eq_zero (hdeg.trans hn)
      · have hA : Nontrivial A := by
          by_contra hA
          haveI : Subsingleton A := not_nontrivial_iff_subsingleton.mp hA
          have hf0 : f = 0 := Subsingleton.elim _ _
          have hdeg0 : f.natDegree = 0 := by simp [hf0]
          exact hn (hdeg.symm.trans hdeg0)
        letI := hA
        obtain ⟨a, ha⟩ := hroot f hf <| by
          rw [degree_eq_natDegree hf.ne_zero, hdeg]
          exact_mod_cast hn
        have hfactor : (X - C a) * (f /ₘ (X - C a)) = f :=
          mul_divByMonic_eq_iff_isRoot.mpr ha
        have hquot_monic : (f /ₘ (X - C a)).Monic :=
          (monic_X_sub_C a).of_mul_monic_left <| by
            simpa [hfactor] using hf
        have hquot_deg : (f /ₘ (X - C a)).natDegree < n := by
          rw [natDegree_divByMonic f (monic_X_sub_C a), hdeg, natDegree_X_sub_C]
          exact Nat.sub_lt (Nat.pos_of_ne_zero hn) (by decide)
        rw [← hfactor]
        exact (Splits.X_sub_C a).mul <| ih _ hquot_deg _ rfl hquot_monic
  intro f hf
  exact hP f.natDegree f rfl hf

namespace IsAbsolutelyIntegrallyClosed

/-- In an absolutely integrally closed ring, every monic polynomial of nonzero degree has a root. -/
theorem exists_root [IsAbsolutelyIntegrallyClosed A] (f : A[X]) (hf : f.Monic)
    (hdeg : f.degree ≠ 0) : ∃ a : A, f.IsRoot a :=
  (IsAbsolutelyIntegrallyClosed.splits f hf).exists_eval_eq_zero hdeg

section

variable {K : Type u} [Field K] [IsAbsolutelyIntegrallyClosed K]

/-- An absolutely integrally closed field is algebraically closed. -/
theorem isAlgClosed : IsAlgClosed K := by
  refine IsAlgClosed.of_exists_root K fun f hf hirr ↦ ?_
  exact (IsAbsolutelyIntegrallyClosed.splits f hf).exists_eval_eq_zero
    (Polynomial.degree_pos_of_irreducible hirr).ne'

end

/-- A commutative ring is absolutely integrally closed if every monic polynomial of nonzero degree
has a root. -/
theorem of_exists_root
    (hroot : ∀ (f : A[X]) (_ : f.Monic) (_ : f.degree ≠ 0), ∃ a : A, f.IsRoot a) :
    IsAbsolutelyIntegrallyClosed A :=
  ⟨splits_of_forall_monic_nonzero_degree_has_root hroot⟩

end IsAbsolutelyIntegrallyClosed

end

/-! ### Lemma_15_14_2 (from Chap15) -/
open Polynomial

universe u

section

variable {A : Type u} [CommRing A]

/- Domain-style sampling for Lemma 15.14.2:
- primary domain: commutative algebra of absolutely integrally closed rings and root-existence for
  monic polynomials;
- sampled owner declarations:
  `IsAbsolutelyIntegrallyClosed`,
  `IsAbsolutelyIntegrallyClosed.exists_root`,
  `IsAbsolutelyIntegrallyClosed.of_exists_root`,
  `Polynomial.Splits.exists_eval_eq_zero`;
- best owner abstraction: the chapter owner `IsAbsolutelyIntegrallyClosed A`;
- primitive data: only the owner predicate `IsAbsolutelyIntegrallyClosed A`, whose primitive field
  is splitting of monic polynomials;
- derived API: the root-existence criterion for monic polynomials of nonzero degree.

Source/core/bridge triage:
- `source-facing`: the iff statement `absolutely_integrally_closed_iff_forall_monic_has_root`;
- `core/canonical`: `IsAbsolutelyIntegrallyClosed`;
- `bridge/view`: the forward and backward implications provided canonically by
  `IsAbsolutelyIntegrallyClosed.exists_root` and `IsAbsolutelyIntegrallyClosed.of_exists_root`.

This file therefore keeps the textbook iff statement, but only as a thin source-facing bridge over
the owner-level API from `Definition_15_14_1`.
-/

/-- Lemma 15.14.2: a ring is absolutely integrally closed if and only if every monic polynomial
over `A` of nonzero degree has a root in `A`. -/
theorem absolutely_integrally_closed_iff_forall_monic_has_root :
    IsAbsolutelyIntegrallyClosed A ↔
      ∀ (f : A[X]) (_ : f.Monic) (_ : f.degree ≠ 0), ∃ a : A, f.IsRoot a := by
  refine ⟨?_, IsAbsolutelyIntegrallyClosed.of_exists_root⟩
  intro hA f hf hdeg
  let _ : IsAbsolutelyIntegrallyClosed A := hA
  exact IsAbsolutelyIntegrallyClosed.exists_root f hf hdeg

end

/-! ### Lemma_15_14_3 (from Chap15) -/
universe u v

section

variable {A : Type u} [CommRing A]
variable [IsAbsolutelyIntegrallyClosed A]

/-
Domain-style sampling for Lemma 15.14.3:
- primary domain: commutative algebra of absolute integral closedness, polynomial splitting, and
  permanence under quotient and localization maps;
- sampled owner-level declarations:
  `IsAbsolutelyIntegrallyClosed`,
  `IsAbsolutelyIntegrallyClosed.exists_root`,
  `Polynomial.lifts_and_natDegree_eq_and_monic`,
  `IsLocalization.scaleRoots_commonDenom_mem_lifts`;
- best owner abstraction: the chapter owner `IsAbsolutelyIntegrallyClosed`;
- primitive data: the owner field `splits` for monic polynomials, together with the canonical
  quotient and localization ring maps used to transport that splitting data;
- derived API: root-existence results such as `IsAbsolutelyIntegrallyClosed.exists_root`, which are
  downstream consequences rather than primitive inputs here.

Source/core/bridge triage:
- `source-facing`: permanence of absolute integral closedness under quotients and localizations;
- `core/canonical`: `IsAbsolutelyIntegrallyClosed`;
- `bridge/view`: the quotient map `A →+* A ⧸ I` and the localization map `A →+* S`, through which
  the canonical splitting data is transported.
-/

-- Proof sketch: for a monic polynomial over `A ⧸ I`, lift its coefficients to `A`, keep the
-- leading coefficient equal to `1`, and use absolute integral closedness of `A` to split the
-- lifted monic polynomial. Mapping the resulting linear-factor decomposition through the quotient
-- map gives a splitting in `A ⧸ I`.
/-- Lemma 15.14.3 (1): any quotient ring `A ⧸ I` of an absolutely integrally closed ring `A` is
absolutely integrally closed. -/
instance (I : Ideal A) : IsAbsolutelyIntegrallyClosed (A ⧸ I) where
  splits f hf := by
    let φ : A →+* A ⧸ I := Ideal.Quotient.mk I
    have hf_lifts : f ∈ Polynomial.lifts (Ideal.Quotient.mk I) := by
      rw [Polynomial.mem_lifts]
      exact Polynomial.map_surjective φ Ideal.Quotient.mk_surjective f
    obtain ⟨g, hg, -, hg_monic⟩ :=
      Polynomial.lifts_and_natDegree_eq_and_monic hf_lifts hf
    simpa [← hg] using (IsAbsolutelyIntegrallyClosed.splits g hg_monic).map φ

-- Proof sketch: given a monic polynomial over a localization `S` of `A` at `M`, clear denominators from its
-- non-leading coefficients to obtain a monic polynomial over `A` after rescaling. Split that
-- monic polynomial in `A` using absolute integral closedness, then map the factorization to `S`
-- and undo the rescaling to obtain a splitting there.
/-- Lemma 15.14.3 (2): any localization of an absolutely integrally closed ring `A` is
absolutely integrally closed. -/
theorem isAbsolutelyIntegrallyClosed_of_isLocalization
    {S : Type v} [CommRing S] [Algebra A S] (M : Submonoid A) [IsLocalization M S] :
    IsAbsolutelyIntegrallyClosed S := by
  refine ⟨?_⟩
  intro f hf
  let d : M := IsLocalization.commonDenom M f.support f.coeff
  let φ : A →+* S := algebraMap A S
  have hf_lifts :
      f.scaleRoots (φ d) ∈ Polynomial.lifts φ := by
    exact IsLocalization.scaleRoots_commonDenom_mem_lifts M f ⟨1, by simp [hf.leadingCoeff]⟩
  obtain ⟨g, hg, -, hg_monic⟩ :=
    Polynomial.lifts_and_natDegree_eq_and_monic hf_lifts
      ((Polynomial.monic_scaleRoots_iff (φ d)).2 hf)
  have hsplits_scaled : (f.scaleRoots (φ d)).Splits := by
    simpa [← hg] using (IsAbsolutelyIntegrallyClosed.splits g hg_monic).map φ
  obtain ⟨v, hv⟩ := isUnit_iff_exists_inv.mp (IsLocalization.map_units S d)
  have hscale : (f.scaleRoots (φ d)).scaleRoots v = f := by
    rw [← Polynomial.scaleRoots_mul, hv, Polynomial.scaleRoots_one]
  simpa [hscale] using hsplits_scaled.scaleRoots v

instance (M : Submonoid A) : IsAbsolutelyIntegrallyClosed (Localization M) :=
  isAbsolutelyIntegrallyClosed_of_isLocalization M

end

/-! ### Lemma_15_14_4 (from Chap15) -/
open Polynomial

universe u

section

variable {A : Type u} [CommRing A]

/-
Domain-style sampling for Lemma 15.14.4:
- primary domain: commutative algebra of absolute integral closedness, integrality, and
  localization;
- sampled owner-level declarations:
  `IsAbsolutelyIntegrallyClosed`,
  `IsAbsolutelyIntegrallyClosed.exists_root`,
  `IsAbsolutelyIntegrallyClosed.of_exists_root`,
  `IsIntegrallyClosedIn`,
  `isIntegrallyClosedIn_iff`,
  `IsIntegrallyClosedIn.algebraMap_eq_of_integral`;
- best owner abstraction: the theorem is `source-facing`, but its proof should use the chapter
  owner `IsAbsolutelyIntegrallyClosed` through the canonical root-existence bridge, and the
  overring owner `IsIntegrallyClosedIn A (Localization S)` directly rather than the image-subring
  bridge view;
- primitive data: the owner predicate `IsAbsolutelyIntegrallyClosed A` and the integrally closed
  owner hypothesis `IsIntegrallyClosedIn A (Localization S)`;
- derived API: root existence for monic polynomials, obtained from
  `IsAbsolutelyIntegrallyClosed.exists_root`.

Source/core/bridge triage:
- `source-facing`: `isAbsolutelyIntegrallyClosed_of_isIntegrallyClosedIn_localization`;
- `core/canonical`: `IsAbsolutelyIntegrallyClosed`, `IsIntegrallyClosedIn`;
- `bridge/view`: the old image-subring packaging via `(algebraMap A (Localization S)).range`,
  which this refinement removes from the public hypothesis.
-/

-- Proof sketch: for a monic polynomial `f` over `A`, map it to a monic polynomial over
-- `Localization S`. Absolute integral closedness of the localization splits the image polynomial.
-- Every resulting root is integral over `A`, and `isIntegrallyClosedIn_iff` supplies injectivity
-- of the localization map together with descent of integral elements, yielding a root of `f`
-- already in `A`.
/-- Lemma 15.14.4: if `Localization S` is absolutely integrally closed and `A` is integrally
closed in `Localization S`, then `A` is absolutely integrally closed. -/
theorem isAbsolutelyIntegrallyClosed_of_isIntegrallyClosedIn_localization (S : Submonoid A)
    [IsIntegrallyClosedIn A (Localization S)]
    [IsAbsolutelyIntegrallyClosed (Localization S)] : IsAbsolutelyIntegrallyClosed A := by
  let φ : A →+* Localization S := algebraMap A (Localization S)
  have hφ : Function.Injective φ := (isIntegrallyClosedIn_iff.mp ‹IsIntegrallyClosedIn A (Localization S)›).1
  refine IsAbsolutelyIntegrallyClosed.of_exists_root fun f hf hdeg ↦ ?_
  let f' : (Localization S)[X] := f.map φ
  have hf' : f'.Monic := hf.map φ
  have hdeg' : f'.degree ≠ 0 := by
    simpa [f', Polynomial.degree_map_eq_of_injective hφ] using hdeg
  obtain ⟨x, hx⟩ := IsAbsolutelyIntegrallyClosed.exists_root f' hf' hdeg'
  have hxint : IsIntegral A x := ⟨f, hf, by simpa [f', φ] using hx.eq_zero⟩
  obtain ⟨a, ha⟩ := IsIntegrallyClosedIn.algebraMap_eq_of_integral hxint
  refine ⟨a, hφ ?_⟩
  have hxa : Polynomial.eval₂ φ (φ a) f = 0 := by
    simpa [φ, f', Polynomial.eval_map, ← ha] using hx.eq_zero
  calc
    φ (Polynomial.eval a f) = Polynomial.eval₂ φ (φ a) f := by
      symm
      exact Polynomial.eval₂_at_apply φ a
    _ = 0 := hxa
    _ = φ 0 := by simp

end

/-! ### Lemma_15_14_5 (from Chap15) -/
universe u

section

open scoped nonZeroDivisors

variable (A : Type u) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]

/-
Domain-style sampling for Lemma 15.14.5:
- primary domain: commutative algebra of absolutely integrally closed domains, fraction fields,
  and integrally closedness;
- sampled owner-level declarations:
  `IsAbsolutelyIntegrallyClosed`,
  `IsAlgClosed`,
  `IsIntegrallyClosed`,
  `isAbsolutelyIntegrallyClosed_of_isIntegrallyClosedIn_localization`;
- best owner abstraction: the theorem is `source-facing`, but its proof should pass through the
  canonical owners `IsAbsolutelyIntegrallyClosed`, `IsAlgClosed`, and `IsIntegrallyClosed`, with
  the fraction field viewed through the canonical localization owner `Localization A⁰`;
- primitive data: the normal-domain hypothesis `[IsIntegrallyClosed A]`, which already means
  `IsIntegrallyClosedIn A (FractionRing A)`, and the fraction-field localization `Localization A⁰`;
- derived API: root-existence and splitting consequences from
  `IsAbsolutelyIntegrallyClosed.exists_root` and the field instance
  `IsAbsolutelyIntegrallyClosed (Localization A⁰)` induced by algebraic closedness.

Source/core/bridge triage:
- `source-facing`: the iff statement comparing absolute integral closedness of `A` with algebraic
  closedness of its fraction field;
- `core/canonical`: `IsAbsolutelyIntegrallyClosed`, `IsAlgClosed`, `IsIntegrallyClosed`;
- `bridge/view`: the identification `FractionRing A = Localization A⁰`, which lets the backward
  implication reuse Lemma `15.14.4` directly instead of introducing a parallel fraction-field
  descent wrapper.
-/

-- Proof sketch: for `→`, apply Lemma `15.14.3` to the fraction field, which is a localization of
-- `A`, and use that an absolutely integrally closed field is algebraically closed. For `←`, an
-- algebraically closed fraction field is absolutely integrally closed as a ring, and then
-- Lemma `15.14.4` descends splitting of monic polynomials from the fraction field back to `A`
-- using integrally closedness of the normal domain `A`.
/-- Lemma 15.14.5: for a normal domain `A`, the ring `A` is absolutely integrally closed if and
only if its fraction field is algebraically closed. -/
theorem isAbsolutelyIntegrallyClosed_iff_isAlgClosed_fractionRing :
    IsAbsolutelyIntegrallyClosed A ↔ IsAlgClosed (FractionRing A) := by
  constructor
  · intro hA
    letI : IsAbsolutelyIntegrallyClosed A := hA
    change IsAlgClosed (Localization A⁰)
    letI : IsAbsolutelyIntegrallyClosed (Localization A⁰) := inferInstance
    exact IsAbsolutelyIntegrallyClosed.isAlgClosed
  · intro hFrac
    change IsAlgClosed (Localization A⁰) at hFrac
    letI : IsAlgClosed (Localization A⁰) := hFrac
    exact isAbsolutelyIntegrallyClosed_of_isIntegrallyClosedIn_localization A⁰

end

/-! ### Lemma_15_14_6 (from Chap15) -/
open CategoryTheory MorphismProperty
open CommRingCat

universe u v

namespace RingHom

section

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A]

/-- A ring map is finite free if it is finite and its codomain is a free module over the source via
the induced algebra structure. -/
abbrev FiniteFree (f : R →+* A) : Prop :=
  let _ : Algebra R A := f.toAlgebra
  RingHom.Finite f ∧ Module.Free R A

/-- An `R`-algebra map `f : R →+* A` is a filtered colimit of finite free `R`-algebras. This thin
source-facing wrapper hides the same-universe `ULift` presentation of the canonical owner
`CategoryTheory.MorphismProperty.ind (RingHom.toMorphismProperty RingHom.FiniteFree)`. -/
abbrev IsFilteredColimitOfFiniteFree (f : R →+* A) : Prop :=
  let _ : Algebra R A := f.toAlgebra
  let _ : Algebra R (ULift A) := ULift.algebra
  let _ : Algebra (ULift.{v} R) (ULift A) := ULift.algebra' R (ULift A)
  ind.{max u v, max u v, max u v + 1} (toMorphismProperty FiniteFree)
    (CommRingCat.ofHom (algebraMap (ULift.{v} R) (ULift A)))

end

end RingHom

section

variable (A : Type u) [CommRing A]

/-
Domain-style sampling for Lemma 15.14.6:
- primary domain: commutative algebra of absolutely integrally closed extensions and filtered
  colimit presentations of ring maps;
- sampled owner-level declarations:
  `RingHom.Finite`,
  `RingHom.FiniteFree`,
  `RingHom.IsFilteredColimitOfFiniteFree`,
  `RingHom.toMorphismProperty`,
  `IsAbsolutelyIntegrallyClosed`,
  `IsAbsolutelyIntegrallyClosed.exists_root`,
  `RingHom.finite_algebraMap`;
- best owner abstraction: the theorem is `source-facing`, but its filtered-colimit hypothesis
  should use the chapter-style ring-hom owner `(algebraMap A B).IsFilteredColimitOfFiniteFree`,
  whose hidden core/canonical content is
  `CategoryTheory.MorphismProperty.ind (RingHom.toMorphismProperty RingHom.FiniteFree)`;
  absolute integral closedness should use the chapter owner `IsAbsolutelyIntegrallyClosed B`;
- primitive data: an injective `A`-algebra structure on `B`, freeness of `B` over `A`, and the
  owner-level filtered-colimit predicate `(algebraMap A B).IsFilteredColimitOfFiniteFree`;
- derived API: root existence for monic polynomials over `B`, obtained from
  `IsAbsolutelyIntegrallyClosed B`.

Source/core/bridge triage:
- `source-facing`: `exists_absolutely_integrally_closed_free_extension`;
- `core/canonical`: `IsAbsolutelyIntegrallyClosed`, `RingHom.Finite`,
  `RingHom.FiniteFree`, `RingHom.IsFilteredColimitOfFiniteFree`;
- `bridge/view`: the hidden same-universe `ULift` presentation inside
  `RingHom.IsFilteredColimitOfFiniteFree`.
-/

-- Proof sketch: build the endofunctor `F(A)` adjoining roots of all monic polynomials over `A`,
-- note that each `F(A)` is free over `A` and a filtered colimit of finite free `A`-algebras, and
-- then take the directed colimit of the iterates `Fⁿ(A)`. Lemma `15.14.2` identifies the final
-- root-existence statement with `IsAbsolutelyIntegrallyClosed`.
/-- Lemma 15.14.6: for any commutative ring `A`, there exists an injective `A`-algebra `B` such
that `B` is free as an `A`-module, `B` is a filtered colimit of finite free `A`-algebras, and
`B` is absolutely integrally closed. -/
theorem exists_absolutely_integrally_closed_free_extension :
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra A B),
      Function.Injective (algebraMap A B) ∧
      Module.Free A B ∧
      (algebraMap A B).IsFilteredColimitOfFiniteFree ∧
      IsAbsolutelyIntegrallyClosed B := by
  sorry

end

/-! ### Lemma_15_14_7 (from Chap15) -/
open IsLocalRing
open Polynomial

universe u

section

variable {A : Type u} [CommRing A]

section

variable [IsLocalRing A] [IsAbsolutelyIntegrallyClosed A]

/-
Domain-style sampling for Lemma 15.14.7:
- primary domain: local commutative algebra of absolutely integrally closed rings, residue fields,
  and the canonical owners `HenselianLocalRing` and `StrictHenselianLocalRing`;
- sampled owner-level declarations:
  `HenselianLocalRing.TFAE`,
  `StrictHenselianLocalRing`,
  `IsAbsolutelyIntegrallyClosed.exists_root`,
  `Polynomial.Splits.roots_map_of_ne_zero`,
  `Polynomial.mem_roots`,
  `IsAbsolutelyIntegrallyClosed (A ⧸ I)`;
- best owner abstraction: the canonical local owner is `HenselianLocalRing`, upgraded to
  `StrictHenselianLocalRing` by the residue-field separable-closure clause; the source-facing
  localization statement is then derived by the existing absolute-integral-closed localization
  instance together with the local strict henselian owner instance below;
- primitive data: `HenselianLocalRing A` and `IsSepClosed (ResidueField A)`;
- derived API: strict henselianity of localizations at prime ideals.

Source/core/bridge triage:
- `source-facing`: the `#synth` entry for Lemma 15.14.7;
- `core/canonical`: `StrictHenselianLocalRing`, `HenselianLocalRing`, `IsSepClosed`;
- `bridge/view`: the local instance from absolute integral closedness together with the
  quotient/localization preservation instances for `IsAbsolutelyIntegrallyClosed`.
-/

private theorem exists_isRoot_of_residueField_isRoot
    (f : A[X]) (hf : f.Monic)
    {a₀ : ResidueField A} (ha₀ : aeval a₀ f = 0) :
    ∃ a : A, f.IsRoot a ∧ residue A a = a₀ := by
  classical
  have hf_split : f.Splits := IsAbsolutelyIntegrallyClosed.splits f hf
  obtain ⟨m, hm⟩ := splits_iff_exists_multiset'.mp hf_split
  have ha₀_eval : eval a₀ (f.map (residue A)) = 0 := by
    simpa [aeval_def, ResidueField.algebraMap_eq, eval_map] using ha₀
  have hzero : 0 ∈ m.map (fun a ↦ a₀ + residue A a) := by
    rw [← Multiset.prod_eq_zero_iff]
    rw [hm, hf.leadingCoeff, Polynomial.map_mul, eval_mul, Polynomial.map_multiset_prod,
      eval_multiset_prod] at ha₀_eval
    simpa using ha₀_eval
  rw [Multiset.mem_map] at hzero
  obtain ⟨a, ha, ha_zero⟩ := hzero
  refine ⟨-a, ?_, ?_⟩
  · rw [IsRoot, hm, hf.leadingCoeff, eval_mul, eval_C, one_mul, eval_multiset_prod]
    refine Multiset.prod_eq_zero ?_
    have hmem :
        eval (-a) (X + C a) ∈ Multiset.map (eval (-a)) (Multiset.map (fun x ↦ X + C x) m) :=
      Multiset.mem_map_of_mem _ (Multiset.mem_map_of_mem _ ha)
    simpa using hmem
  · calc
      residue A (-a) = -residue A a := by simp
      _ = a₀ := (eq_neg_of_add_eq_zero_left ha_zero).symm

-- Proof sketch: use absolute integral closedness to split every monic polynomial, then any
-- residue-field root of its reduction must come from the image of an actual root by the canonical
-- factorization over the residue field must come from one linear factor already present in the
-- split factorization over `A`. This gives the simple-root lifting clause in
-- `HenselianLocalRing.TFAE`. The residue field is a
-- quotient of an absolutely integrally closed ring, hence algebraically closed and therefore
-- separably closed.
/-- A local absolutely integrally closed ring is strictly henselian. -/
instance : StrictHenselianLocalRing A := by
  refine
    { toHenselianLocalRing := ?_
      toIsSepClosed := ?_ }
  · refine ((HenselianLocalRing.TFAE A).out 1 0).mp ?_
    intro f hf a₀ ha₀ _
    exact exists_isRoot_of_residueField_isRoot f hf ha₀
  · letI : IsAbsolutelyIntegrallyClosed (ResidueField A) := by
      simpa [IsLocalRing.ResidueField] using
        (inferInstance : IsAbsolutelyIntegrallyClosed (A ⧸ maximalIdeal A))
    letI : IsAlgClosed (ResidueField A) := IsAbsolutelyIntegrallyClosed.isAlgClosed
    exact inferInstance

end

-- Proof sketch: apply Lemma `15.14.3` to the localization `Localization.AtPrime p` to keep
-- absolute integral closedness, note that this localization is local, and then invoke the local
-- case to obtain the strict henselian structure.
variable (p : Ideal A) [p.IsPrime] [IsAbsolutelyIntegrallyClosed A]

/- Lemma 15.14.7: if `A` is absolutely integrally closed and `p` is a prime ideal of `A`, then
the local ring `Localization.AtPrime p` is strictly henselian. -/
#synth StrictHenselianLocalRing (Localization.AtPrime p)

end

/-! ### Lemma_15_14_8 (from Chap15) -/
universe u

section

variable {A : Type u} [CommRing A] [IsAbsolutelyIntegrallyClosed A]

namespace Ideal

/- Domain-style sampling:
- primary domain: henselian pairs over absolutely integrally closed rings, with the canonical
  owner `HenselianRing A I` and quotient idempotent lifting as derived API;
- sampled owner-level declarations:
  `HenselianRing`,
  `Ideal.HasFiniteAlgebraIdempotentLifting`,
  `Ideal.le_ring_jacobson_of_henselianRing`,
  `henselianRing_tfae_etaleLift_idempotents_gabberCriterion`,
  `quotientMk_injective_on_idempotents_of_le_jacobson`;
- best owner abstraction: this lemma is `source-facing`, but its proof should be organized around
  the existing henselian owner `HenselianRing A I` and the chapter-level idempotent-lifting owner
  `I.HasFiniteAlgebraIdempotentLifting`, not around a parallel local criterion;
- primitive data: the ideal `I`, the owner predicate `HenselianRing A I`, and the Jacobson plus
  quotient-idempotent surjectivity conditions from the source statement;
- derived API: injectivity of the quotient idempotent map from the Jacobson condition, the
  finite-algebra idempotent-lifting owner obtained from the chapter TFAE, and the resulting
  henselian conclusion.

Source/core/bridge triage:
- `source-facing`: the present equivalence specialized to absolutely integrally closed rings;
- `core/canonical`: `HenselianRing A I` and `I.HasFiniteAlgebraIdempotentLifting`;
- `bridge/view`: the internal Gabber-root-criterion step from Lemma `15.11.6` and the
  quotient-idempotent map `(Ideal.Quotient.mk I).idempotentMap`.
-/

-- Proof sketch: the forward implication should not rebuild idempotent lifting locally; instead,
-- specialize the finite-algebra idempotent clause of Lemma `15.11.6` to `B = A`. For the
-- converse, the source-specific step is first to turn surjectivity on quotient idempotents over
-- an absolutely integrally closed ring into Gabber's root criterion, and then immediately package
-- that step through the canonical owner `I.HasFiniteAlgebraIdempotentLifting`.

private theorem satisfiesGabberRootCriterion_of_le_jacobson_and_surjective_on_idempotents
    (I : Ideal A) (hI : I ≤ Ring.jacobson A)
    (hsurj : Function.Surjective (Ideal.Quotient.mk I).idempotentMap) :
    I.SatisfiesGabberRootCriterion := by
  refine ⟨hI, ?_⟩
  intro f hf
  -- Use absolute integral closedness to split `f`, then extract from the lifted idempotent data a
  -- root in `1 + I`; this is exactly the source-facing step not already packaged by the chapter
  -- TFAE owner.
  sorry

/-- Over an absolutely integrally closed ring, the source hypotheses in Lemma `15.14.8` imply the
henselian owner by way of Gabber's criterion. -/
private theorem henselianRing_of_le_jacobson_and_surjective_on_idempotents
    (I : Ideal A) (hI : I ≤ Ring.jacobson A)
    (hsurj : Function.Surjective (Ideal.Quotient.mk I).idempotentMap) :
    HenselianRing A I := by
  have hGabber : I.SatisfiesGabberRootCriterion :=
    satisfiesGabberRootCriterion_of_le_jacobson_and_surjective_on_idempotents I hI hsurj
  exact I.henselianRing_of_satisfiesGabberRootCriterion hGabber

/-- Lemma 15.14.8: for an absolutely integrally closed ring `A` and an ideal `I`, the pair
`(A, I)` is henselian if and only if `I` is contained in the Jacobson radical of `A` and the
quotient map `A → A ⧸ I` induces a surjection on idempotents. -/
theorem henselianRing_iff_le_jacobson_and_surjective_on_idempotents (I : Ideal A) :
    HenselianRing A I ↔
      I ≤ Ring.jacobson A ∧
        Function.Surjective (Ideal.Quotient.mk I).idempotentMap := by
  constructor
  · intro hH
    haveI := hH
    refine ⟨I.le_ring_jacobson_of_henselianRing, ?_⟩
    exact I.quotientMk_bijective_idempotentMap_of_henselianRing.surjective
  · rintro ⟨hI, hsurj⟩
    exact henselianRing_of_le_jacobson_and_surjective_on_idempotents I hI hsurj

end Ideal

end
