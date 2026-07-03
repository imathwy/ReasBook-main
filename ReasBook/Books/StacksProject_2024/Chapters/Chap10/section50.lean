import Mathlib
import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
import Mathlib.Algebra.Order.Hom.MonoidWithZero
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Valuation.Discrete.Basic
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.RingTheory.Valuation.ValuationRing
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_10_50_1 (from Chap10) -/
universe u

/-
Domain-style sampling pass for Definition 10.50.1.

Primary domain: valuation theory for local subrings of a field.

Sampled owner declarations:
* `LocalSubring.le_def`;
* `LocalSubring.isMax_iff`;
* `ValuationRing.range_algebraMap_eq`;
* `ValuationRing.iff_isInteger_or_isInteger`.

Owner abstraction: domination is the canonical order on `LocalSubring K`, while valuation-ring
structure is carried by `ValuationRing A` and `ValuationSubring K`. The image of `A` in its
fraction field is derived owner data `LocalSubring.range (algebraMap A (FractionRing A))`, so the
main theorem below stays a source-facing bridge from that image to the owner theorem
`LocalSubring.isMax_iff`.

Layering:
* source-facing: `valuationRing_iff_isMax_range_fractionRing`;
* core/canonical: `LocalSubring K`, `ValuationSubring K`, `ValuationRing A`;
* bridge/view: `LocalSubring.range (algebraMap A (FractionRing A))`.
-/

/- Definition 10.50.1: on local subrings of a field, the domination relation is the canonical
order `≤`; equivalently it is characterized by `LocalSubring.le_def`. -/
recall LocalSubring.le_def

/- Definition 10.50.1: the canonical mathlib notion of a valuation ring is `ValuationRing`. -/
recall ValuationRing

/- Definition 10.50.1: a local subring of a field is a valuation ring exactly when it is maximal
for the domination order. This owner theorem is `LocalSubring.isMax_iff`. -/
recall LocalSubring.isMax_iff

section

variable (A : Type u) [CommRing A] [IsDomain A] [IsLocalRing A]

local notation "K" => FractionRing A

/-- Definition 10.50.1: a local domain `A` is a valuation ring if and only if its image in its
fraction field is maximal for the domination order on local subrings. -/
theorem valuationRing_iff_isMax_range_fractionRing :
    ValuationRing A ↔ IsMax (LocalSubring.range (algebraMap A K)) := by
  let A0 : LocalSubring K := LocalSubring.range (algebraMap A K)
  change ValuationRing A ↔ IsMax A0
  constructor
  · intro
    let V : ValuationSubring K := (ValuationRing.valuation A K).valuationSubring
    have hV : V.toLocalSubring = A0 := by
      apply LocalSubring.toSubring_injective
      simpa [A0, V] using ValuationRing.range_algebraMap_eq A K
    simpa [hV] using V.isMax_toLocalSubring
  · intro hA
    rw [ValuationRing.iff_isInteger_or_isInteger A K]
    intro x
    obtain ⟨V, hV⟩ := LocalSubring.isMax_iff.mp hA
    have hV' : V.toSubring = A0.toSubring := congrArg LocalSubring.toSubring hV
    rcases V.mem_or_inv_mem x with hx | hx
    · left
      simpa [IsLocalization.IsInteger, RingHom.mem_range, hV'] using (show x ∈ V.toSubring from hx)
    · right
      simpa [IsLocalization.IsInteger, RingHom.mem_range, hV'] using
        (show x⁻¹ ∈ V.toSubring from hx)

end

section

variable {K : Type u} [Field K] (V : ValuationSubring K) (R : Subring K)

/- Definition 10.50.1: the Stacks phrase “`V` is centered on `R`” is exactly the containment
condition `R ≤ V.toSubring`. -/
#check R ≤ V.toSubring

end

/-! ### Lemma_10_50_2 (from Chap10) -/
universe u

section

variable (K : Type u) [Field K]

/- Lemma 10.50.2: let `K` be a field and let `A ⊂ K` be a local subring. Then there exists a
valuation ring with fraction field `K` dominating `A`. The primary domain is valuation theory for
local subrings of a field. This file is a `bridge/view` recall of the core owner theorem
`LocalSubring.exists_le_valuationSubring`: the primitive data are `K` and `A : LocalSubring K`,
while the domination relation `A ≤ B.toLocalSubring` is derived from the owner abstractions
`LocalSubring K` and `ValuationSubring K`. -/
recall LocalSubring.exists_le_valuationSubring

end

/-! ### Lemma_10_50_3 (from Chap10) -/
universe u

section

variable {A : Type u} [CommRing A] [IsDomain A] [ValuationRing A]

/- Lemma 10.50.3: let `A` be a valuation ring. Then `A` is a normal domain. This is a
`bridge/view` use of the chapter's owner predicate `IsIntegrallyClosed A`: the primitive data are
the commutative-domain and valuation-ring assumptions, while normality itself is the derived
canonical instance obtained upstream from the induced `IsBezout A` structure. -/
#check (inferInstance : IsIntegrallyClosed A)

end

/-! ### Lemma_10_50_4 (from Chap10) -/
/- Lemma 10.50.4: if `A` is a valuation ring with fraction field `K`, then for every `x : K`
either `x ∈ A` or `x⁻¹ ∈ A` or both. In mathlib the canonical form is
`ValuationRing.isInteger_or_isInteger`, stated using `IsLocalization.IsInteger`; under the
fraction-field hypotheses this is the precise library-facing formulation of the Stacks statement. -/
recall ValuationRing.isInteger_or_isInteger

/-! ### Lemma_10_50_5 (from Chap10) -/
universe u

section

variable {K : Type u} [Field K]

/-- Lemma 10.50.5: a subring of a field containing either `x` or `x⁻¹` for every `x : K`
is a valuation ring with fraction field the ambient field `K`. -/
-- Layering:
-- * source-facing: the theorem speaks about the given subring `A`.
-- * core/canonical owner: `ValuationSubring K`.
-- * bridge: instantiate the canonical owner `ValuationSubring.ofSubring A hA` and reuse its
--   derived `ValuationRing` and `IsFractionRing` instances.
theorem valuationRing_and_isFractionRing_of_mem_or_inv_mem (A : Subring K)
    (hA : ∀ x : K, x ∈ A ∨ x⁻¹ ∈ A) :
    ValuationRing A ∧ IsFractionRing A K := by
  let V : ValuationSubring K := ValuationSubring.ofSubring A hA
  change ValuationRing V ∧ IsFractionRing V K
  exact ⟨inferInstance, inferInstance⟩

end

/-! ### Lemma_10_50_6 (from Chap10) -/
universe u v

section

open DirectedSystem
open Ring.DirectLimit

variable {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
variable (A : I → Type u) [∀ i, CommRing (A i)] [∀ i, IsDomain (A i)] [∀ i, ValuationRing (A i)]
variable (φ : ∀ i j, i ≤ j → A i →+* A j) [DirectedSystem A (φ · · ·)]

local notation "A∞" => Ring.DirectLimit A (fun i j h ↦ φ i j h)
local notation "of∞" => of A (fun i j h ↦ φ i j h)

/-- A directed ring direct limit of domains is again a domain. -/
instance : IsDomain A∞ := by
  haveI : Nontrivial A∞ := by
    obtain ⟨i⟩ := ‹Nonempty I›
    refine ⟨⟨0, 1, ?_⟩⟩
    change (0 : A∞) ≠ 1
    rw [← (of∞ i).map_one]
    intro h
    rcases of.zero_exact h.symm with ⟨j, hij, hj⟩
    rw [(φ i j hij).map_one] at hj
    exact one_ne_zero hj
  haveI : NoZeroDivisors A∞ := by
    constructor
    intro x y hxy
    induction x using induction_on with
    | ih i x =>
        induction y using induction_on with
        | ih j y =>
            rcases exists_ge_ge i j with ⟨k, hik, hjk⟩
            have hk : of∞ k (φ i k hik x * φ j k hjk y) = 0 := by
              simpa [map_mul, of_f] using hxy
            rcases of.zero_exact hk with ⟨l, hkl, hzero⟩
            have hprod : φ i l (le_trans hik hkl) x * φ j l (le_trans hjk hkl) y = 0 := by
              simpa [map_mul, map_map' φ hik hkl x, map_map' φ hjk hkl y] using hzero
            rcases eq_zero_or_eq_zero_of_mul_eq_zero hprod with hx | hy
            · left
              simpa [of_f] using congrArg (of∞ l) hx
            · right
              simpa [of_f] using congrArg (of∞ l) hy
  exact NoZeroDivisors.to_isDomain A∞

-- The total divisibility relation of a valuation ring descends along the directed colimit.
omit [DirectedSystem A (φ · · ·)] in
private theorem directedSystem_directLimit_dvdTotal : @Std.Total A∞ (· ∣ ·) := by
  constructor
  intro x y
  induction x using induction_on with
  | ih i x =>
      induction y using induction_on with
      | ih j y =>
          rcases exists_ge_ge i j with ⟨k, hik, hjk⟩
          rcases ValuationRing.cond (φ i k hik x) (φ j k hjk y) with ⟨z, hz | hz⟩
          · left
            refine ⟨of∞ k z, ?_⟩
            simpa [map_mul, of_f] using congrArg (of∞ k) hz.symm
          · right
            refine ⟨of∞ k z, ?_⟩
            simpa [map_mul, of_f] using congrArg (of∞ k) hz.symm

/-- Lemma 10.50.6: the direct limit of a directed system of valuation rings over a directed set is
again a valuation ring. -/
instance directedSystem_directLimit_valuationRing :
    ValuationRing A∞ :=
  ValuationRing.iff_dvd_total.mpr (directedSystem_directLimit_dvdTotal A φ)

end

/-! ### Lemma_10_50_7 (from Chap10) -/
/- Domain triage:
* primary domain: valuation subrings of fields and their pullback along ring homomorphisms;
* owner abstraction: `ValuationSubring.comap`;
* sampled canonical declarations:
  `ValuationSubring`,
  `ValuationSubring.comap`,
  `ValuationSubring.mem_comap`,
  and the induced `ValuationRing` instance on any valuation subring;
* layer: `core/canonical`, since this item is only recalling the owner-side pullback construction and
  adds no new source-facing data.

Primitive-vs-derived split:
* primitive data: a valuation subring `B` of a field `L`, together with the ring map
  `algebraMap K L`;
* derived API: the contracted valuation subring `B.comap (algebraMap K L)` and the resulting
  `ValuationRing` structure on `K`.
-/
/- Lemma 10.50.7: if `L/K` is a field extension and `B` is a valuation subring of `L`, then the
intersection `K ∩ B` is the canonical pullback valuation subring `B.comap (algebraMap K L)` of
`K`. Since every valuation subring carries a `ValuationRing` instance, this is exactly the Stacks
Project statement that `K ∩ B` is a valuation ring. -/
recall ValuationSubring.comap

/-! ### Lemma_10_50_8 (from Chap10) -/
universe u v

section

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]

/- Domain triage:
* primary domain: valuation subrings of fields and algebraic field extensions;
* core/canonical owners: `ValuationSubring.comap`, `ValuationSubring.mem_comap`,
  `Algebra.IsIntegral.of_injective`, and `isField_of_isIntegral_of_isField'`;
* sampled owner-side declarations: the previous item `Lemma 10.50.7` already recalls
  `ValuationSubring.comap`, while mathlib provides the field criterion
  `isField_of_isIntegral_of_isField'` and the transport lemma
  `Algebra.IsIntegral.of_injective`;
* layer: `source-facing`, since the statement is the Stacks-project consequence for the contracted
  valuation subring, proved by composing those owner abstractions.

Primitive-vs-derived split:
* primitive data: the valuation subring `B : ValuationSubring L` and the algebraic extension
  hypothesis `[Algebra.IsAlgebraic K L]`;
* derived API: the contracted valuation subring `B.comap (algebraMap K L)`, the induced
  `K`-algebra structure on `B` once the contraction is all of `K`, and the resulting integrality
  of `B` over `K`.
-/

-- Proof sketch: if the contraction `B.comap (algebraMap K L)` were a field, then the valuation
-- condition plus inverse-closure would force it to contain all of `K`. Thus `B` becomes a
-- `K`-algebra, algebraic hence integral over `K`, so the domain `B` is itself a field.
/-- Lemma 10.50.8: if `L / K` is algebraic and `B` is a valuation subring of `L` that is not a
field, then the canonical pullback valuation subring `B.comap (algebraMap K L)` of `K`, i.e. the
intersection `K ∩ B`, is not a field. -/
theorem not_isField_comap_algebraMap_of_isAlgebraic [Algebra.IsAlgebraic K L]
    (B : ValuationSubring L) (hB : ¬ IsField B) :
    ¬ IsField (B.comap (algebraMap K L)) := by
  intro hcomap
  let A : ValuationSubring K := B.comap (algebraMap K L)
  have hA : IsField A := by simpa [A] using hcomap
  have hA_mem : ∀ k : K, k ∈ A := by
    intro k
    rcases A.mem_or_inv_mem k with hk | hk
    · exact hk
    · letI := hA.toField
      have hk' : (k⁻¹)⁻¹ ∈ A := by
        have hcoe : (((⟨k⁻¹, hk⟩ : A)⁻¹ : A) : K) = (k⁻¹)⁻¹ := by
          change A.subtype ((⟨k⁻¹, hk⟩ : A)⁻¹) = (A.subtype ⟨k⁻¹, hk⟩)⁻¹
          exact map_inv₀ A.subtype (⟨k⁻¹, hk⟩ : A)
        exact hcoe ▸ ((⟨k⁻¹, hk⟩ : A)⁻¹).2
      simpa using hk'
  letI : Algebra K B :=
    (RingHom.codRestrict (algebraMap K L) B fun k ↦
      show algebraMap K L k ∈ B from hA_mem k).toAlgebra
  haveI : Algebra.IsIntegral K L := ⟨fun x ↦
    (Algebra.IsAlgebraic.isAlgebraic x).isIntegral⟩
  let g : B →ₐ[K] L :=
    { toRingHom := B.subtype
      commutes' := fun _ ↦ rfl }
  haveI : Algebra.IsIntegral K B := Algebra.IsIntegral.of_injective g B.subtype_injective
  exact hB <| isField_of_isIntegral_of_isField' (Field.toIsField K)

end

/-! ### Lemma_10_50_9 (from Chap10) -/
universe u

section

variable {A : Type u} [CommRing A] [IsDomain A] [ValuationRing A]

omit [ValuationRing A] in
private instance isDomain_localization (S : Submonoid A) [Fact ((0 : A) ∉ S)] :
    IsDomain (Localization S) := by
  exact IsLocalization.isDomain_localization
    (le_nonZeroDivisors_of_noZeroDivisors Fact.out)

omit [IsDomain A] [ValuationRing A] in
private theorem mk'_dvd_mk'_of_mul_eq (S : Submonoid A) [Fact ((0 : A) ∉ S)] {a b c : A}
    (s t : S) (h : a * t * c = b * s) :
    IsLocalization.mk' (Localization S) a s ∣ IsLocalization.mk' (Localization S) b t := by
  have h_one : IsLocalization.mk' (Localization S) c (1 : S) =
      algebraMap A (Localization S) c :=
    IsLocalization.mk'_one (Localization S) c
  have h_mul : IsLocalization.mk' (Localization S) (a * c) (s * 1) =
      IsLocalization.mk' (Localization S) a s * IsLocalization.mk' (Localization S) c 1 :=
    IsLocalization.mk'_mul (Localization S) a c s 1
  refine ⟨algebraMap A (Localization S) c, ?_⟩
  rw [← h_one, ← h_mul]
  exact IsLocalization.mk'_eq_of_eq' (by
    simpa [mul_assoc, mul_left_comm, mul_comm] using h)

/-- Lemma 10.50.9: if `S` is a submonoid of a valuation ring `A` with `0 ∉ S`, then
`Localization S` is again a valuation ring. This is the Lean form of the source statement that any
localization of a valuation ring is again a valuation ring. The owner abstraction is
`ValuationRing.iff_dvd_total`; the proof below is the source-facing localization bridge. -/
instance valuationRing_localization (S : Submonoid A) [Fact ((0 : A) ∉ S)] :
    ValuationRing (Localization S) := by
  refine ValuationRing.iff_dvd_total.mpr ⟨fun x y ↦ ?_⟩
  obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq S x
  obtain ⟨b, t, rfl⟩ := IsLocalization.exists_mk'_eq S y
  obtain ⟨c, h | h⟩ := ValuationRing.cond (a * t) (b * s)
  · left
    exact mk'_dvd_mk'_of_mul_eq S s t h
  · right
    exact mk'_dvd_mk'_of_mul_eq S t s h

/-- Localization at a prime ideal of a valuation ring is again a valuation ring. -/
instance valuationRing_localization_atPrime (p : Ideal A) [p.IsPrime] :
    ValuationRing (Localization.AtPrime p) := by
  letI : Fact ((0 : A) ∉ p.primeCompl) := ⟨by
    simp [Ideal.primeCompl, Ideal.zero_mem p]⟩
  infer_instance

/-- Quotienting a valuation ring by a prime ideal again yields a valuation ring. This is the exact
owner theorem `Function.Surjective.valuationRing` applied to the quotient map. -/
instance valuationRing_quotient (p : Ideal A) [p.IsPrime] : ValuationRing (A ⧸ p) := by
  simpa using Function.Surjective.valuationRing
    (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective

end

/-! ### Lemma_10_50_10 (from Chap10) -/
noncomputable section

universe u v

open IsLocalRing

section ResiduePreimageSubring

variable (A' : Type u) [CommRing A'] [IsLocalRing A']
variable (A : Type v) [CommRing A] [Algebra A (ResidueField A')]

/-- The subring of `A'` consisting of elements whose residue class lies in the image of `A` in the
residue field of `A'`. -/
noncomputable def residuePreimageSubring : Subring A' :=
  Subring.comap (residue A') (algebraMap A (ResidueField A')).range

-- Proof sketch: unfold `residuePreimageSubring`; membership in a `Subring.comap` is exactly
-- membership of the image under `residue A'` in the target subring.
/-- An element of `A'` lies in `residuePreimageSubring A' A` exactly when its residue class comes
from `A`. -/
@[simp] theorem mem_residuePreimageSubring_iff (x : A') :
    x ∈ residuePreimageSubring A' A ↔
      residue A' x ∈ (algebraMap A (ResidueField A')).range := by
  rfl

-- Proof sketch: elements of the maximal ideal have zero residue class, and `0` is always in the
-- image of `A` in `ResidueField A'`.
/-- Any element of the maximal ideal of `A'` lies in `residuePreimageSubring A' A`. -/
theorem mem_residuePreimageSubring_of_mem_maximalIdeal {x : A'}
    (hx : x ∈ maximalIdeal A') :
    x ∈ residuePreimageSubring A' A := by
  have hres : residue A' x = 0 := (IsLocalRing.residue_eq_zero_iff x).mpr hx
  rw [mem_residuePreimageSubring_iff, hres]
  exact ⟨0, by simp⟩

end ResiduePreimageSubring

section

variable (A' : Type u) [CommRing A'] [IsDomain A'] [ValuationRing A']
variable (A : Type v) [CommRing A] [IsDomain A] [ValuationRing A]
variable [Algebra A (ResidueField A')] [IsFractionRing A (ResidueField A')]

private theorem mem_residuePreimageSubring_or_exists_mul_eq_one (x : A') :
    x ∈ residuePreimageSubring A' A ∨
      ∃ y : A', y ∈ residuePreimageSubring A' A ∧ x * y = 1 := by
  by_cases hx : residue A' x = 0
  · left
    exact mem_residuePreimageSubring_of_mem_maximalIdeal A' A <|
      (IsLocalRing.residue_eq_zero_iff x).mp hx
  · obtain hxA | hxA :=
      ValuationRing.isInteger_or_isInteger A (residue A' x)
    · left
      rw [mem_residuePreimageSubring_iff]
      simpa [IsLocalization.IsInteger, RingHom.mem_range] using hxA
    · have hxunit : IsUnit x := by
        refine (IsLocalRing.notMem_maximalIdeal).mp ?_
        intro hxmax
        exact hx ((IsLocalRing.residue_eq_zero_iff x).mpr hxmax)
      rcases hxunit with ⟨u, rfl⟩
      refine Or.inr ⟨↑u⁻¹, ?_, by simp⟩
      rw [mem_residuePreimageSubring_iff]
      simpa [IsLocalization.IsInteger, RingHom.mem_range] using hxA

-- Proof sketch: for every `x : A'`, either `residue A' x = 0`, in which case `x` lies in
-- `residuePreimageSubring A' A`, or the residue class of `x` is nonzero in `ResidueField A'`.
-- Since `A` is a valuation ring with fraction field `ResidueField A'`, either that residue class
-- or its inverse comes from `A`; in the inverse case, `x` is a unit and an inverse of `x` lies in
-- `residuePreimageSubring A' A`. Combining this dichotomy with `ValuationRing.cond` for `A'`
-- gives total divisibility on `residuePreimageSubring A' A`, hence a valuation-ring structure.
/-- Lemma 10.50.10: if `A'` is a valuation ring and its residue field is the fraction field of a
valuation ring `A`, then the subring of `A'` whose residue classes come from `A` is a valuation
ring. -/
theorem residuePreimageSubring_isValuationRing :
    ValuationRing (residuePreimageSubring A' A) := by
  rw [ValuationRing.iff_dvd_total]
  refine ⟨fun x y ↦ ?_⟩
  obtain ⟨c, hxy | hyx⟩ := ValuationRing.cond (x : A') (y : A')
  · obtain hc | ⟨d, hd, hcd⟩ := mem_residuePreimageSubring_or_exists_mul_eq_one A' A c
    · exact Or.inl ⟨⟨c, hc⟩, Subtype.ext hxy.symm⟩
    · refine Or.inr ⟨⟨d, hd⟩, ?_⟩
      apply Subtype.ext
      calc
        (x : A') = (x : A') * (c * d) := by simp [hcd]
        _ = ((x : A') * c) * d := by simp [mul_assoc]
        _ = y * d := by rw [hxy]
  · obtain hc | ⟨d, hd, hcd⟩ := mem_residuePreimageSubring_or_exists_mul_eq_one A' A c
    · exact Or.inr ⟨⟨c, hc⟩, Subtype.ext hyx.symm⟩
    · refine Or.inl ⟨⟨d, hd⟩, ?_⟩
      apply Subtype.ext
      calc
        (y : A') = (y : A') * (c * d) := by simp [hcd]
        _ = ((y : A') * c) * d := by simp [mul_assoc]
        _ = x * d := by rw [hyx]

end

/-! ### Lemma_10_50_11 (from Chap10) -/
universe u v

section

variable (A : Type u) (K : Type v) [CommRing A] [Field K] [Algebra A K]
  [IsFractionRing A K] [IsIntegrallyClosed A]

private instance :
    IsIntegrallyClosedIn ((algebraMap A K).range) K := by
  letI : Algebra A ((algebraMap A K).range) := RingHom.toAlgebra (algebraMap A K).rangeRestrict
  letI : IsScalarTower A ((algebraMap A K).range) K := .of_algebraMap_eq fun _ ↦ rfl
  letI : Algebra.IsIntegral A ((algebraMap A K).range) := {
    isIntegral := fun x ↦ by
      rcases x with ⟨x, ⟨a, rfl⟩⟩
      simpa using (isIntegral_algebraMap : IsIntegral A ((algebraMap A ((algebraMap A K).range)) a))
  }
  rw [Subring.isIntegrallyClosedIn_iff]
  intro x hx
  have hx' : IsIntegral A x := isIntegral_trans x hx
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hx'
  exact ⟨a, ha⟩

private instance [IsLocalRing A] :
    IsIntegrallyClosedIn (LocalSubring.range (algebraMap A K)).toSubring K := by
  simpa using (inferInstance : IsIntegrallyClosedIn ((algebraMap A K).range) K)

-- Proof sketch: apply the valuation-subring existence theorem to the subring
-- `(algebraMap A K).range`, using that a normal domain is integrally closed in its fraction field.
/-- Lemma 10.50.11 (1): if `x` is not in the embedded image of a normal domain `A` inside its
fraction field `K`, then there is a valuation subring of `K` containing `A` but not containing
`x`. -/
theorem exists_valuationSubring_not_mem_of_not_mem_range {x : K}
    (hx : x ∉ (algebraMap A K).range) :
    ∃ V : ValuationSubring K, (algebraMap A K).range ≤ V.toSubring ∧ x ∉ V := by
  simpa using Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn hx

-- Proof sketch: view the image of the local domain `A` in `K` as a local subring and apply the
-- local valuation-subring existence theorem for integrally closed local subrings of a field.
/-- Lemma 10.50.11 (2): if `A` is local and `x` is not in the embedded image of `A` inside `K`,
then there is a valuation subring of `K` dominating `A` and still excluding `x`. -/
theorem exists_valuationSubring_dominating_not_mem_of_not_mem_range [IsLocalRing A] {x : K}
    (hx : x ∉ (algebraMap A K).range) :
    ∃ V : ValuationSubring K, LocalSubring.range (algebraMap A K) ≤ V.toLocalSubring ∧ x ∉ V := by
  simpa using LocalSubring.exists_le_valuationSubring_of_isIntegrallyClosedIn hx

-- Proof sketch: identify the image of `A` in `K` with an integrally closed subring of the field
-- `K`, then apply the canonical `eq_iInf` theorem for valuation subrings containing that subring.
/-- Lemma 10.50.11 (3): a normal domain is the intersection of the valuation subrings of its
fraction field that contain its embedded image. -/
theorem range_eq_iInf_valuationSubrings :
    (algebraMap A K).range =
      ⨅ V : {V : ValuationSubring K // (algebraMap A K).range ≤ V.toSubring}, V.1.toSubring :=
  by
    simpa using (Subring.eq_iInf_of_isIntegrallyClosedIn :
      (algebraMap A K).range =
        ⨅ V : {V : ValuationSubring K // (algebraMap A K).range ≤ V.toSubring}, V.1.toSubring)

-- Proof sketch: apply the local-subring intersection theorem to the local image of `A` in `K`;
-- the dominating condition is encoded by the order relation on local subrings.
/-- Lemma 10.50.11 (4): if `A` is local, then its embedded image in `K` is the intersection of
the valuation subrings of `K` that dominate `A`. -/
theorem range_eq_iInf_dominating_valuationSubrings [IsLocalRing A] :
    (algebraMap A K).range =
      ⨅ V : {V : ValuationSubring K // LocalSubring.range (algebraMap A K) ≤ V.toLocalSubring},
        V.1.toSubring := by
  simpa using (LocalSubring.eq_iInf_of_isIntegrallyClosedIn :
    (LocalSubring.range (algebraMap A K)).toSubring =
      ⨅ V : {V : ValuationSubring K // LocalSubring.range (algebraMap A K) ≤ V.toLocalSubring},
        V.1.toSubring)

end

/-! ### Lemma_10_50_12 (from Chap10) -/
universe u

section

variable (A : Type u) [CommRing A] [IsDomain A] [ValuationRing A]

local notation "Γ" => (ValuationRing.ValueGroup A (FractionRing A))ˣ

/- Lemma 10.50.12: the value group from Definition 10.50.13, namely `Γ = Kˣ / Aˣ`, is a totally
ordered abelian group. The owner object is the with-zero value group
`ValuationRing.ValueGroup A (FractionRing A)`; the source-facing ordered abelian group structure
on `Γ` is given by the canonical owner-derived instances on units. -/
#check (inferInstance : CommGroup Γ)
#check (inferInstance : LinearOrder Γ)
#check (inferInstance : IsOrderedMonoid Γ)

end

/-! ### Definition_10_50_13 (from Chap10) -/
universe u

section

variable (A : Type u) [CommRing A] [IsDomain A] [ValuationRing A]

/- Definition 10.50.13: for a valuation ring `A`, the value group is the ordered abelian group
`Γ = Kˣ / Aˣ`. In mathlib, this group is represented by the unit group of the canonical owner
object `ValuationRing.ValueGroup A (FractionRing A)`. -/
#check (ValuationRing.ValueGroup A (FractionRing A))ˣ

end

/- Companion recall: the valuation associated to a valuation ring is the canonical valuation
`ValuationRing.valuation A (FractionRing A)` on its fraction field; its codomain is the with-zero
version of the value group from Definition 10.50.13, and restricting this map to
`A \ {0}` or to `(FractionRing A)ˣ` gives the textbook maps `v : A - \{0\} → Γ` and
`v : K^* → Γ`. -/
recall ValuationRing.valuation

/- Companion recall: adjoining `0` to the ordered abelian group from Definition 10.50.13 recovers
the canonical with-zero value group used by `ValuationRing.valuation`. -/
recall OrderMonoidIso.withZeroUnits

/- Companion recall: the further textbook condition that the value group be infinite cyclic is
formalized in mathlib by the standard predicate `IsDiscreteValuationRing A`. The corresponding
normalization of the associated with-zero value group by `ℤᵐ⁰` belongs to the separate
rank-one-discrete valuation API, not to the present definition of the value group itself. -/
recall IsDiscreteValuationRing

/- Companion recall: once `A` is a discrete valuation ring, the associated valuation on its
fraction field is canonically rank-one discrete. This is the bridge from the present value-group
definition to the `ℤᵐ⁰` normalization API. -/
recall IsDiscreteValuationRing.isRankOneDiscrete

/-! ### Lemma_10_50_14 (from Chap10) -/
universe u

open Valuation

noncomputable section

section

variable (A : Type u) [CommRing A] [IsDomain A] [ValuationRing A]

local notation "K[" A "]" => FractionRing A
local notation "Γ₀[" A "]" => ValuationRing.ValueGroup A (K[A])
local notation "Γ[" A "]" => (Γ₀[A])ˣ
local notation "v[" A "]" => ValuationRing.valuation A (FractionRing A)
local notation "va[" A "]" => Valuation.toAddValuation (v[A])
local notation "ι[" A "]" => algebraMap A (FractionRing A)

private theorem valuationRingValuation_ne_zero (a : { a : A // a ≠ 0 }) :
    v[A] (ι[A] (a : A)) ≠ 0 := by
  rw [Valuation.ne_zero_iff]
  exact (map_ne_zero_iff ι[A] (IsFractionRing.injective A K[A])).2 a.2

/-- The textbook valuation `v : A - \{0\} → Γ` attached to a valuation ring `A`, where
`Γ = (ValuationRing.ValueGroup A (FractionRing A))ˣ` is the source-facing value group from
Definition 10.50.13. This is the restriction of the canonical owner valuation
`ValuationRing.valuation A (FractionRing A)` to nonzero elements of `A`, with the zero value
excluded by passing to units. -/
def valuationRingNonzeroValuation (a : { a : A // a ≠ 0 }) : Γ[A] :=
  Units.mk0 (v[A] (ι[A] (a : A))) (valuationRingValuation_ne_zero A a)

@[simp] theorem valuationRingNonzeroValuation_coe (a : { a : A // a ≠ 0 }) :
    ((valuationRingNonzeroValuation A a : Γ[A]) : Γ₀[A]) = v[A] (ι[A] (a : A)) := by
  simp [valuationRingNonzeroValuation]

@[simp] theorem valuationRingNonzeroValuation_le_one (a : { a : A // a ≠ 0 }) :
    ((valuationRingNonzeroValuation A a : Γ[A]) : Γ₀[A]) ≤ 1 := by
  rw [valuationRingNonzeroValuation_coe]
  exact (ValuationRing.mem_integer_iff A K[A] (ι[A] (a : A))).2 ⟨(a : A), rfl⟩

@[simp] theorem valuationRingNonzeroValuation_toAdd (a : { a : A // a ≠ 0 }) :
    OrderDual.toDual (Additive.ofMul (((valuationRingNonzeroValuation A a : Γ[A]) : Γ₀[A]))) =
      va[A] (ι[A] (a : A)) := by
  simp [Valuation.toAddValuation_apply, valuationRingNonzeroValuation_coe]

/-- The source-facing cone condition in additive normalization: nonzero elements of a valuation
ring have nonnegative value. This is the textbook codomain restriction
`v : A \ {0} → Γ_{\ge 0}` expressed through the owner additive valuation. -/
theorem valuationRingNonzeroValuation_toAdd_nonneg (a : { a : A // a ≠ 0 }) :
    0 ≤ va[A] (ι[A] (a : A)) := by
  rw [← valuationRingNonzeroValuation_toAdd]
  simpa using valuationRingNonzeroValuation_le_one A a

-- Proof sketch: identify `A` with the integer ring of its associated valuation and transport the
-- standard criterion that valuation `1` is equivalent to being a unit.
/-- Lemma 10.50.14 (1): for a nonzero element of `A`, the associated valuation is `1` exactly when
it is a unit. -/
theorem valuationRingNonzeroValuation_eq_one_iff_isUnit (a : { a : A // a ≠ 0 }) :
    valuationRingNonzeroValuation A a = 1 ↔ IsUnit (a : A) := by
  let x : (ValuationRing.valuation A K[A]).integer := ValuationRing.equivInteger A K[A] (a : A)
  have hx : v[A] (algebraMap (ValuationRing.valuation A K[A]).integer K[A] x) = 1 ↔ IsUnit x :=
    ((Valuation.integer.integers (v[A])).isUnit_iff_valuation_eq_one).symm
  have hx' : ((valuationRingNonzeroValuation A a : Γ[A]) : Γ₀[A]) = 1 ↔ IsUnit (a : A) := by
    simpa [x, ValuationRing.coe_equivInteger_apply, valuationRingNonzeroValuation_coe] using hx
  constructor
  · intro h
    have hcoe : ((valuationRingNonzeroValuation A a : Γ[A]) : Γ₀[A]) = 1 := by
      rw [h]
      simp
    exact hx'.1 hcoe
  · intro h
    apply Units.ext
    exact hx'.2 h

/-- Lemma 10.50.14 (2): the associated valuation is multiplicative on products of nonzero
elements. -/
theorem valuationRingNonzeroValuation_mul (a b : { a : A // a ≠ 0 }) :
    valuationRingNonzeroValuation A ⟨(a : A) * (b : A), mul_ne_zero a.2 b.2⟩ =
      valuationRingNonzeroValuation A a * valuationRingNonzeroValuation A b := by
  apply Units.ext
  simp [valuationRingNonzeroValuation_coe]

/-- Lemma 10.50.14 (3): for nonzero `a`, `b`, and `a + b`, the associated valuation satisfies the
ultrametric inequality in multiplicative normalization. -/
theorem valuationRingNonzeroValuation_add_le_max
    (a b : { a : A // a ≠ 0 }) (hab : (a : A) + (b : A) ≠ 0) :
    valuationRingNonzeroValuation A ⟨(a : A) + (b : A), hab⟩ ≤
      max (valuationRingNonzeroValuation A a) (valuationRingNonzeroValuation A b) := by
  rw [← Units.val_le_val]
  simp [valuationRingNonzeroValuation_coe]

end

/-! ### Lemma_10_50_15 (from Chap10) -/
universe u

section

variable (A : Type u) [CommRing A] [IsDomain A]

/- Lemma 10.50.15: the canonical library-facing formulation is
`ValuationRing.iff_local_bezout_domain`, i.e. a domain is a valuation ring exactly when it is a
local Bézout domain. -/
recall ValuationRing.iff_local_bezout_domain

/-- A textbook-facing reformulation of `ValuationRing.iff_local_bezout_domain` using the explicit
condition that every finitely generated ideal is principal. This is a thin source-facing bridge;
the owner abstraction remains `IsBezout`. -/
lemma valuationRing_iff_isLocalRing_and_fgIdeals_principal :
    ValuationRing A ↔ IsLocalRing A ∧ ∀ I : Ideal A, I.FG → I.IsPrincipal := by
  constructor
  · intro hvaluation
    exact ⟨inferInstance, IsBezout.isPrincipal_of_FG⟩
  · rintro ⟨hlocal, hprincipal⟩
    exact ValuationRing.iff_local_bezout_domain.2 ⟨hlocal, ⟨hprincipal⟩⟩

end

/-! ### Lemma_10_50_16 (from Chap10) -/
noncomputable section

universe u v

open Valuation

section

variable {K : Type u} [Field K]
variable {Γ : Type v} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]

local instance : DecidableEq K := Classical.decEq K

/-- The nonarchimedean condition on a unit-group homomorphism, written in additive notation on
nonzero sums. -/
class IsNonarchimedeanUnitHom (v : Kˣ →* Multiplicative Γ) : Prop where
  map_add_ge_min :
    ∀ ⦃a b : K⦄, ∀ ha : a ≠ 0, ∀ hb : b ≠ 0, ∀ hab : a + b ≠ 0,
      min (Multiplicative.toAdd (v (Units.mk0 a ha)))
          (Multiplicative.toAdd (v (Units.mk0 b hb))) ≤
        Multiplicative.toAdd (v (Units.mk0 (a + b) hab))

-- The additive view of the owner map `v.rangeRestrict`.
private abbrev rangeRestrictToAdd (v : Kˣ →* Multiplicative Γ) (x : Kˣ) :
    v.range.toAddSubgroup' :=
  v.rangeRestrict x

/-- The extension of a unit-group homomorphism to all of `K`, now landing in the exact image
group `Im(v)` and sending `0` to `⊤`. -/
private def unitHomValue (v : Kˣ →* Multiplicative Γ) (x : K) :
    WithTop (v.range.toAddSubgroup') :=
  if hx : x = 0 then ⊤ else
    (rangeRestrictToAdd v (Units.mk0 x hx) : WithTop (v.range.toAddSubgroup'))

-- Proof sketch: unfold `unitHomValue`; the `if` branch for `x = 0` is immediate.
omit [LinearOrder Γ] [IsOrderedAddMonoid Γ] in
private theorem unitHomValue_zero (v : Kˣ →* Multiplicative Γ) :
    unitHomValue v 0 = ⊤ := by
  -- The zero branch of `unitHomValue` is definitionally `⊤`.
  simp [unitHomValue]

-- Proof sketch: unfold `unitHomValue` at `1`, note that `1 ≠ 0` in a field, and use that a group
-- homomorphism sends `1` to `1`, which corresponds to additive value `0`.
omit [LinearOrder Γ] [IsOrderedAddMonoid Γ] in
private theorem unitHomValue_one (v : Kˣ →* Multiplicative Γ) :
    unitHomValue v 1 = 0 := by
  -- Move to the nonzero branch and identify the restricted value of `1` with the zero element.
  have h1 : (1 : K) ≠ 0 := one_ne_zero
  unfold unitHomValue
  split_ifs with h
  · exact (h1 h).elim
  · have hzero : rangeRestrictToAdd v (Units.mk0 1 h) = 0 := by
      apply Subtype.ext
      change Multiplicative.toAdd (v (Units.mk0 1 h)) = 0
      rw [Units.mk0_one, map_one]
      rfl
    simpa using hzero

-- Proof sketch: split into the zero and nonzero cases for `a` and `b`; when both are nonzero,
-- rewrite through `Units.mk0` and use multiplicativity of the original homomorphism.
private theorem unitHomValue_mul (v : Kˣ →* Multiplicative Γ) :
    ∀ a b : K, unitHomValue v (a * b) = unitHomValue v a + unitHomValue v b := by
  intro a b
  -- The zero branches collapse immediately from the definition.
  by_cases ha : a = 0
  · simp [unitHomValue, ha]
  by_cases hb : b = 0
  · simp [unitHomValue, hb]
  -- In the nonzero branch, `Units.mk0_mul` matches the source multiplicativity exactly.
  have hab : a * b ≠ 0 := mul_ne_zero ha hb
  have hMul :
      unitHomValue v (a * b) =
        (rangeRestrictToAdd v (Units.mk0 (a * b) hab) : WithTop (v.range.toAddSubgroup')) := by
    simp [unitHomValue, hab]
  have hA :
      unitHomValue v a =
        (rangeRestrictToAdd v (Units.mk0 a ha) : WithTop (v.range.toAddSubgroup')) := by
    simp [unitHomValue, ha]
  have hB :
      unitHomValue v b =
        (rangeRestrictToAdd v (Units.mk0 b hb) : WithTop (v.range.toAddSubgroup')) := by
    simp [unitHomValue, hb]
  rw [hMul, hA, hB, ← WithTop.coe_add, WithTop.coe_eq_coe]
  -- The restricted value of a product is the sum of the restricted values in additive notation.
  apply Subtype.ext
  change
    Multiplicative.toAdd (v (Units.mk0 (a * b) hab)) =
      ↑(rangeRestrictToAdd v (Units.mk0 a ha) + rangeRestrictToAdd v (Units.mk0 b hb))
  rw [Units.mk0_mul _ _ hab, map_mul]
  rfl

-- Proof sketch: if one summand is zero, the claim reduces to the corresponding branch of
-- `unitHomValue`; otherwise apply the given minimum inequality on nonzero elements and coerce the
-- resulting inequality into `WithTop (v.range.toAddSubgroup')`.
omit [IsOrderedAddMonoid Γ] in
private theorem unitHomValue_add (v : Kˣ →* Multiplicative Γ) (hv : IsNonarchimedeanUnitHom v) :
    ∀ a b : K, min (unitHomValue v a) (unitHomValue v b) ≤ unitHomValue v (a + b) := by
  intro a b
  -- If the sum vanishes, the target is `⊤` and the inequality is automatic.
  by_cases hab : a + b = 0
  · rw [hab, unitHomValue_zero]
    exact le_top
  by_cases ha : a = 0
  · subst a
    simp [unitHomValue]
  by_cases hb : b = 0
  · subst b
    simp [unitHomValue]
  -- In the fully nonzero branch, transport the given inequality into `WithTop`.
  have hA :
      unitHomValue v a =
        (rangeRestrictToAdd v (Units.mk0 a ha) : WithTop (v.range.toAddSubgroup')) := by
    simp [unitHomValue, ha]
  have hB :
      unitHomValue v b =
        (rangeRestrictToAdd v (Units.mk0 b hb) : WithTop (v.range.toAddSubgroup')) := by
    simp [unitHomValue, hb]
  have hAB :
      unitHomValue v (a + b) =
        (rangeRestrictToAdd v (Units.mk0 (a + b) hab) : WithTop (v.range.toAddSubgroup')) := by
    simp [unitHomValue, hab]
  rw [hA, hB, hAB, ← WithTop.coe_min, WithTop.coe_le_coe]
  -- After removing the `WithTop` coercions, this is exactly the given nonarchimedean inequality.
  change
    min (Multiplicative.toAdd (v (Units.mk0 a ha))) (Multiplicative.toAdd (v (Units.mk0 b hb))) ≤
      Multiplicative.toAdd (v (Units.mk0 (a + b) hab))
  simpa [rangeRestrictToAdd] using hv.map_add_ge_min (a := a) (b := b) ha hb hab

end

section

variable {K : Type u} [Field K]
variable {Γ : Type v} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]

/-- The canonical additive valuation attached to a nonarchimedean unit-group homomorphism, valued
in the exact image group `Im(v)`. -/
def addValuationOfUnitHom (v : Kˣ →* Multiplicative Γ) (hv : IsNonarchimedeanUnitHom v) :
    AddValuation K (WithTop (v.range.toAddSubgroup')) :=
  AddValuation.of (unitHomValue v) (unitHomValue_zero v) (unitHomValue_one v)
    (unitHomValue_add v hv) (unitHomValue_mul v)

/-- The source-facing valuation subring `A` attached to `v`. -/
def valuationSubringOfUnitHom (v : Kˣ →* Multiplicative Γ) (hv : IsNonarchimedeanUnitHom v) :
    ValuationSubring K :=
  (addValuationOfUnitHom v hv).toValuation.valuationSubring

variable (v : Kˣ →* Multiplicative Γ) (hv : IsNonarchimedeanUnitHom v)

/-- On nonzero elements, `addValuationOfUnitHom v` is exactly the original unit-group
homomorphism, with codomain restricted to the exact image subgroup. -/
@[simp] theorem addValuationOfUnitHom_apply_of_ne_zero {x : K} (hx : x ≠ 0) :
    addValuationOfUnitHom v hv x =
      (rangeRestrictToAdd v (Units.mk0 x hx) : WithTop (v.range.toAddSubgroup')) := by
  simp [addValuationOfUnitHom, unitHomValue, hx]

/-- On units, `addValuationOfUnitHom v` lands in the exact image subgroup `Im(v)`. -/
@[simp] theorem addValuationOfUnitHom_apply_unit (x : Kˣ) :
    addValuationOfUnitHom v hv x = (rangeRestrictToAdd v x : WithTop (v.range.toAddSubgroup')) := by
  simp [addValuationOfUnitHom, unitHomValue, x.ne_zero]

/-- Lemma 10.50.16 (Tag 00IG): the induced additive valuation has exact value group `Im(v)`;
equivalently, every element of `Im(v)` is the value of some unit of `K`. -/
theorem addValuationOfUnitHom_surjective_on_valueGroup (γ : v.range.toAddSubgroup') :
    ∃ x : Kˣ, addValuationOfUnitHom v hv x = (γ : WithTop (v.range.toAddSubgroup')) := by
  rcases v.rangeRestrict_surjective γ with ⟨x, rfl⟩
  exact ⟨x, addValuationOfUnitHom_apply_unit v hv x⟩

omit [LinearOrder Γ] [IsOrderedAddMonoid Γ] in
private theorem rangeRestrict_eq_zero_iff (v : Kˣ →* Multiplicative Γ) (x : Kˣ) :
    ((rangeRestrictToAdd v x : WithTop (v.range.toAddSubgroup')) = 0) ↔
      Multiplicative.toAdd (v x) = 0 := by
  constructor
  · intro hx
    have hx' : rangeRestrictToAdd v x = 0 := by
      simpa using hx
    exact congrArg Subtype.val hx'
  · intro hx
    have hx' : rangeRestrictToAdd v x = 0 := by
      ext
      exact hx
    simpa using hx'

omit [IsOrderedAddMonoid Γ] in
private theorem rangeRestrict_nonneg_iff (v : Kˣ →* Multiplicative Γ) (x : Kˣ) :
    0 ≤ (rangeRestrictToAdd v x : WithTop (v.range.toAddSubgroup')) ↔
      0 ≤ Multiplicative.toAdd (v x) := by
  change
    (((0 : v.range.toAddSubgroup') : WithTop (v.range.toAddSubgroup')) ≤
        (rangeRestrictToAdd v x : WithTop (v.range.toAddSubgroup'))) ↔
      0 ≤ Multiplicative.toAdd (v x)
  rw [WithTop.coe_le_coe]
  rfl

omit [IsOrderedAddMonoid Γ] in
private theorem rangeRestrict_pos_iff (v : Kˣ →* Multiplicative Γ) (x : Kˣ) :
    0 < (rangeRestrictToAdd v x : WithTop (v.range.toAddSubgroup')) ↔
      0 < Multiplicative.toAdd (v x) := by
  change
    (((0 : v.range.toAddSubgroup') : WithTop (v.range.toAddSubgroup')) <
        (rangeRestrictToAdd v x : WithTop (v.range.toAddSubgroup'))) ↔
      0 < Multiplicative.toAdd (v x)
  rw [WithTop.coe_lt_coe]
  rfl

/-- Lemma 10.50.16 (Tag 00IG): the valuation subring attached to `v` is exactly the set of elements whose
induced additive value in `Im(v)` is nonnegative. This is the canonical library-facing form of the
source description `A = {x ∈ K | x = 0 or v(x) ≥ 0}`. -/
theorem mem_valuationSubringOfUnitHom_iff (x : K) :
    x ∈ valuationSubringOfUnitHom v hv ↔ 0 ≤ addValuationOfUnitHom v hv x := by
  rw [valuationSubringOfUnitHom, Valuation.mem_valuationSubring_iff]
  simpa [AddValuation.toValuation_apply] using
    (Multiplicative.ofAdd_le :
      Multiplicative.ofAdd (OrderDual.toDual (addValuationOfUnitHom v hv x)) ≤ 1 ↔
        OrderDual.toDual (addValuationOfUnitHom v hv x) ≤ 0)

/-- On nonzero elements, membership in the valuation subring is exactly nonnegativity of the
original homomorphism `v`. -/
theorem mem_valuationSubringOfUnitHom_iff_of_ne_zero {x : K} (hx : x ≠ 0) :
    x ∈ valuationSubringOfUnitHom v hv ↔ 0 ≤ Multiplicative.toAdd (v (Units.mk0 x hx)) := by
  rw [mem_valuationSubringOfUnitHom_iff, addValuationOfUnitHom_apply_of_ne_zero v hv hx]
  exact rangeRestrict_nonneg_iff v (Units.mk0 x hx)

/-- Lemma 10.50.16 (Tag 00IG): the source-facing description of `A`, written directly in terms of
the original unit-group homomorphism `v`. The universal quantifier only supplies the implicit proof
that a nonzero element of `K` defines a unit. -/
theorem mem_valuationSubringOfUnitHom_iff_eq_zero_or_nonneg (x : K) :
    x ∈ valuationSubringOfUnitHom v hv ↔
      x = 0 ∨ ∀ hx : x ≠ 0, 0 ≤ Multiplicative.toAdd (v (Units.mk0 x hx)) := by
  constructor
  · intro hxA
    by_cases hx : x = 0
    · exact Or.inl hx
    · exact Or.inr fun hx' ↦ (mem_valuationSubringOfUnitHom_iff_of_ne_zero v hv hx').mp hxA
  · rintro (rfl | hx)
    · rw [mem_valuationSubringOfUnitHom_iff]
      simp
    · by_cases hx0 : x = 0
      · rw [hx0, mem_valuationSubringOfUnitHom_iff]
        simp
      · exact (mem_valuationSubringOfUnitHom_iff_of_ne_zero v hv hx0).mpr (hx hx0)

/-- Lemma 10.50.16 (Tag 00IG): elements of the maximal ideal are exactly those with strictly
positive extended value. -/
theorem mem_maximalIdeal_valuationSubringOfUnitHom_iff {a : valuationSubringOfUnitHom v hv} :
    a ∈ IsLocalRing.maximalIdeal (valuationSubringOfUnitHom v hv) ↔
      0 < addValuationOfUnitHom v hv a := by
  simpa [valuationSubringOfUnitHom, AddValuation.toValuation_apply] using
    (((addValuationOfUnitHom v hv).toValuation).mem_maximalIdeal_iff :
      a ∈ IsLocalRing.maximalIdeal (((addValuationOfUnitHom v hv).toValuation).valuationSubring) ↔
        ((addValuationOfUnitHom v hv).toValuation) a < 1)

/-- On nonzero elements of the valuation subring, maximal-ideal membership is exactly positivity
of the original homomorphism `v`. -/
theorem mem_maximalIdeal_valuationSubringOfUnitHom_iff_of_ne_zero
    {a : valuationSubringOfUnitHom v hv} (ha : (a : K) ≠ 0) :
    a ∈ IsLocalRing.maximalIdeal (valuationSubringOfUnitHom v hv) ↔
      0 < Multiplicative.toAdd (v (Units.mk0 (a : K) ha)) := by
  rw [mem_maximalIdeal_valuationSubringOfUnitHom_iff, addValuationOfUnitHom_apply_of_ne_zero v hv ha]
  exact rangeRestrict_pos_iff v (Units.mk0 (a : K) ha)

/-- Lemma 10.50.16 (Tag 00IG): the source-facing description of the maximal ideal, written
directly in terms of the original unit-group homomorphism `v`. -/
theorem mem_maximalIdeal_valuationSubringOfUnitHom_iff_eq_zero_or_pos
    {a : valuationSubringOfUnitHom v hv} :
    a ∈ IsLocalRing.maximalIdeal (valuationSubringOfUnitHom v hv) ↔
      (a : K) = 0 ∨ ∀ ha : (a : K) ≠ 0, 0 < Multiplicative.toAdd (v (Units.mk0 (a : K) ha)) := by
  constructor
  · intro ha
    by_cases h0 : (a : K) = 0
    · exact Or.inl h0
    · exact Or.inr fun ha' ↦
        (mem_maximalIdeal_valuationSubringOfUnitHom_iff_of_ne_zero v hv ha').mp ha
  · intro ha'
    rcases ha' with h0 | ha
    · have : a = 0 := Subtype.ext h0
      cases this
      simp
    · by_cases h0 : (a : K) = 0
      · have : a = 0 := Subtype.ext h0
        cases this
        simp
      · exact (mem_maximalIdeal_valuationSubringOfUnitHom_iff_of_ne_zero v hv h0).mpr (ha h0)

/-- Lemma 10.50.16 (Tag 00IG): units in the valuation subring are exactly the nonzero elements
with value `0`. -/
theorem mem_unitGroup_valuationSubringOfUnitHom_iff (x : Kˣ) :
    x ∈ (valuationSubringOfUnitHom v hv).unitGroup ↔ Multiplicative.toAdd (v x) = 0 := by
  rw [show x ∈ (valuationSubringOfUnitHom v hv).unitGroup ↔ addValuationOfUnitHom v hv x = 0 by
    simpa [valuationSubringOfUnitHom, AddValuation.toValuation_apply] using
      Valuation.mem_unitGroup_iff K ((addValuationOfUnitHom v hv).toValuation) x]
  rw [addValuationOfUnitHom_apply_unit v hv x]
  simpa [Units.mk0_val] using rangeRestrict_eq_zero_iff v x

end

/-! ### Lemma_10_50_17 (from Chap10) -/
universe u

open Valuation

section

variable (A : Type u) [CommRing A] [IsDomain A] [ValuationRing A]

local notation "K" => FractionRing A
local notation "v" => ValuationRing.valuation A K
local notation "O" => Valuation.integer v
local notation "Γ" => ValuationRing.ValueGroup A K
local notation "Γ≤1" => { γ : Γ // γ ≤ (1 : Γ) }

/- Domain triage:
* primary domain: commutative algebra of ideals in valuation rings via the canonical value group;
* source-facing layer: the textbook correspondence between ideals of a valuation ring and initial
  segments of the integral cone of its value group, together with the prime-ideal compatibility;
* core/canonical owner abstraction for this item: the order isomorphism
  `Ideal O ≃o Order.Ideal Γ≤1`, built from the owner declarations
  `ValuationRing.equivInteger`, `leIdeal`, `leIdeal_mono`, `leIdeal_v_le_of_mem`, and
  `RingEquiv.idealComapOrderIso`;
* bridge/view layer: the public `valuationRing_ideal_correspondence` transports the integer-ring
  owner isomorphism back to ideals of `A`.
* primitive data vs. derived API: the primitive input is only the valuation ring `A` and its
  canonical valuation `v`; the order-ideal correspondence and valuation-prime condition are
  derived from the `leIdeal` family and the canonical ring equivalence `A ≃+* O`.
-/

private theorem valuation_surjective : Function.Surjective v := by
  intro γ
  refine Quotient.inductionOn γ ?_
  intro x
  exact ⟨x, rfl⟩

private theorem leIdeal_one : leIdeal v (1 : Γ) = ⊤ := by
  ext x
  constructor
  · intro _
    trivial
  · intro _
    exact x.2

private noncomputable def valuationRingIdealToOrderIdeal
    (I : Ideal O) : Order.Ideal Γ≤1 where
  carrier := { γ | leIdeal v γ.1 ≤ I }
  lower' := by
    intro γ δ hδγ hγ
    exact (leIdeal_mono v hδγ).trans hγ
  nonempty' := by
    refine ⟨⟨0, zero_le'⟩, ?_⟩
    change leIdeal v (0 : Γ) ≤ I
    rw [leIdeal_zero]
    exact bot_le
  directed' := by
    intro γ₁ hγ₁ γ₂ hγ₂
    by_cases h : γ₁ ≤ γ₂
    · exact ⟨γ₂, hγ₂, h, le_rfl⟩
    · exact ⟨γ₁, hγ₁, le_rfl, le_of_not_ge h⟩

private noncomputable def valuationRingOrderIdealToIdeal
    (J : Order.Ideal Γ≤1) : Ideal O where
  carrier := { x | ⟨v x, x.2⟩ ∈ J }
  zero_mem' := by
    obtain ⟨γ, hγ⟩ := J.nonempty
    refine J.lower ?_ hγ
    change (0 : Γ) ≤ γ.1
    exact zero_le'
  add_mem' := by
    intro x y hx hy
    by_cases hxy : v x ≤ v y
    · exact J.lower
        (show (⟨v (x + y), (x + y).2⟩ : Γ≤1) ≤ ⟨v y, y.2⟩ from
          by simpa [max_eq_right hxy] using Valuation.map_add v x y)
        hy
    · exact J.lower
        (show (⟨v (x + y), (x + y).2⟩ : Γ≤1) ≤ ⟨v x, x.2⟩ from
          by simpa [max_eq_left <| le_of_not_ge hxy] using Valuation.map_add v x y)
        hx
  smul_mem' := by
    intro a x hx
    refine J.lower (show (⟨v ((a : O) * x), ((a : O) * x).2⟩ : Γ≤1) ≤ ⟨v x, x.2⟩ from ?_) hx
    change v ((a : O) * x) ≤ v x
    simpa [Subring.smul_def, map_mul] using mul_le_of_le_one_left zero_le' a.2

private noncomputable def valuationRingIntegerIdealOrderIso :
    Ideal O ≃o Order.Ideal Γ≤1 where
  toFun := valuationRingIdealToOrderIdeal A
  invFun := valuationRingOrderIdealToIdeal A
  left_inv := by
    intro I
    ext x
    constructor
    · intro hx
      exact hx <| by simp [mem_leIdeal_iff]
    · intro hx
      simpa [valuationRingOrderIdealToIdeal, valuationRingIdealToOrderIdeal] using
        (leIdeal_v_le_of_mem v hx)
  right_inv := by
    intro J
    ext γ
    constructor
    · intro hγ
      obtain ⟨x, hx⟩ := valuation_surjective A γ.1
      let x' : (ValuationRing.valuation A K).integer := ⟨x, by
        simpa [Valuation.mem_integer_iff, hx] using γ.2⟩
      have hx' : x' ∈ leIdeal v γ.1 := by
        simp [mem_leIdeal_iff, x', hx]
      simpa [valuationRingOrderIdealToIdeal, hx, x'] using hγ hx'
    · intro hγ x hx
      exact J.lower hx hγ
  map_rel_iff' := by
    intro I J
    change valuationRingIdealToOrderIdeal A I ≤ valuationRingIdealToOrderIdeal A J ↔ I ≤ J
    constructor
    · intro h x hx
      have hx' : (⟨v x, x.2⟩ : Γ≤1) ∈ valuationRingIdealToOrderIdeal A I :=
        leIdeal_v_le_of_mem v hx
      exact (h hx') <| by simp [mem_leIdeal_iff]
    · intro h γ hγ
      exact hγ.trans h

namespace Order.Ideal

/-- The source-facing prime condition on an ideal of the integral value-group cone. In additive
normalization, this is exactly the textbook condition `γ + δ ∈ I → γ ∈ I ∨ δ ∈ I`. -/
def IsValuationPrime (J : Order.Ideal Γ≤1) : Prop :=
  (⟨1, le_rfl⟩ : Γ≤1) ∉ J ∧
    ∀ ⦃γ δ : Γ⦄, ∀ hγ : γ ≤ 1, ∀ hδ : δ ≤ 1,
      (⟨γ * δ, mul_le_one' hγ hδ⟩ : Γ≤1) ∈ J →
        (⟨γ, hγ⟩ : Γ≤1) ∈ J ∨ (⟨δ, hδ⟩ : Γ≤1) ∈ J

end Order.Ideal

private theorem valuationRingIntegerIdealOrderIso_isValuationPrime_iff (I : Ideal O) :
    I.IsPrime ↔ Order.Ideal.IsValuationPrime A (valuationRingIntegerIdealOrderIso A I) := by
  constructor
  · intro hI
    refine ⟨?_, ?_⟩
    · intro hOne
      have htop : (⊤ : Ideal O) ≤ I := by
        change leIdeal v (1 : Γ) ≤ I at hOne
        simpa [leIdeal_one A] using hOne
      exact hI.ne_top <| eq_top_iff.mpr htop
    · intro γ δ hγ hδ hγδ
      obtain ⟨x, hx⟩ := valuation_surjective A γ
      obtain ⟨y, hy⟩ := valuation_surjective A δ
      let x' : O := ⟨x, by simpa [Valuation.mem_integer_iff, hx] using hγ⟩
      let y' : O := ⟨y, by simpa [Valuation.mem_integer_iff, hy] using hδ⟩
      have hxy : x' * y' ∈ I := by
        apply hγδ
        simp [mem_leIdeal_iff, x', y', hx, hy, map_mul]
      rcases hI.mem_or_mem hxy with hxI | hyI
      · left
        simpa [valuationRingIdealToOrderIdeal, x', hx] using leIdeal_v_le_of_mem v hxI
      · right
        simpa [valuationRingIdealToOrderIdeal, y', hy] using leIdeal_v_le_of_mem v hyI
  · intro hI
    refine Ideal.isPrime_iff.mpr ⟨?_, ?_⟩
    · intro htop
      subst htop
      have hOne : (⟨1, le_rfl⟩ : Γ≤1) ∈ valuationRingIntegerIdealOrderIso A (⊤ : Ideal O) := by
        change leIdeal v (1 : Γ) ≤ (⊤ : Ideal O)
        simp [leIdeal_one A]
      exact hI.1 hOne
    · intro x y hxy
      have hxy' : (⟨v x * v y, mul_le_one' x.2 y.2⟩ : Γ≤1) ∈ valuationRingIntegerIdealOrderIso A I := by
        simpa [valuationRingIdealToOrderIdeal, map_mul] using leIdeal_v_le_of_mem v hxy
      rcases hI.2 x.2 y.2 hxy' with hx | hy
      · left
        exact hx <| by simp [mem_leIdeal_iff]
      · right
        exact hy <| by simp [mem_leIdeal_iff]

-- Proof sketch: identify an ideal of `A` with the initial segment of valuation values of its
-- elements in the canonical value group, restricted to the integral part `γ ≤ 1`; this gives the
-- inclusion-preserving bijection. Prime ideals correspond to the multiplicatively prime initial
-- segments, which in additive normalization are the textbook prime ideals of the nonnegative cone.
/-- Lemma 10.50.17: ideals of a valuation ring correspond bijectively, in an
inclusion-preserving way, to order ideals of the integral part of its canonical value group, and
this correspondence sends prime ideals to valuation-prime order ideals. -/
noncomputable def valuationRing_ideal_correspondence :
    Ideal A ≃o Order.Ideal Γ≤1 :=
  (ValuationRing.equivInteger A K).idealComapOrderIso.symm.trans
    (valuationRingIntegerIdealOrderIso A)

/-- Prime ideals correspond to multiplicatively prime ideals of the integral value-group cone under
`valuationRing_ideal_correspondence`; in additive normalization this is the textbook prime-ideal
condition on `Γ_{\ge 0}`. -/
theorem valuationRing_ideal_correspondence_isPrime_iff (I : Ideal A) :
    I.IsPrime ↔ Order.Ideal.IsValuationPrime A (valuationRing_ideal_correspondence A I) := by
  let e : A ≃+* O := ValuationRing.equivInteger A K
  simpa [valuationRing_ideal_correspondence, e] using
    (show I.IsPrime ↔ Order.Ideal.IsValuationPrime A (valuationRingIntegerIdealOrderIso A (I.map e)) from by
      constructor
      · intro hI
        letI : I.IsPrime := hI
        have hmap : (I.map e).IsPrime := Ideal.map_isPrime_of_equiv e
        exact (valuationRingIntegerIdealOrderIso_isValuationPrime_iff A (I.map e)).mp hmap
      · intro hI
        have hmap : (I.map e).IsPrime :=
          (valuationRingIntegerIdealOrderIso_isValuationPrime_iff A (I.map e)).mpr hI
        letI : (I.map e).IsPrime := hmap
        have hcomap : (Ideal.comap e (I.map e)).IsPrime := Ideal.comap_isPrime e (I.map e)
        rw [Ideal.comap_map_of_surjective e e.surjective] at hcomap
        have hs : I ⊔ Ideal.comap e ⊥ = I := by
          rw [Ideal.comap_bot_of_injective e e.injective, sup_of_le_left bot_le]
        exact hs ▸ hcomap)

end

/-! ### Lemma_10_50_18 (from Chap10) -/
universe u

section

variable (A : Type u) [CommRing A] [IsDomain A] [ValuationRing A]

-- This is a source-facing bridge over the owner theorem `IsDiscreteValuationRing.TFAE`: the
-- primitive ambient data are the domain and valuation-ring structures, while Noetherianity and the
-- DVR/field dichotomy remain theorem-level properties. For the forward direction, a valuation ring
-- is local, so the Noetherian local-domain TFAE upgrades `ValuationRing A` to
-- `IsDiscreteValuationRing A` once we exclude the field case; the reverse direction is by the
-- canonical `IsNoetherianRing` instances for DVRs and fields.
/-- Lemma 10.50.18: a valuation ring is Noetherian if and only if it is either a discrete
valuation ring or a field. -/
theorem valuationRing_isNoetherianRing_iff_isDiscreteValuationRing_or_isField :
    IsNoetherianRing A ↔ IsDiscreteValuationRing A ∨ IsField A := by
  constructor
  · intro hA
    by_cases hField : IsField A
    · exact Or.inr hField
    · letI : IsNoetherianRing A := hA
      exact Or.inl <|
        ((IsDiscreteValuationRing.TFAE A hField).out 1 0).mp (show ValuationRing A from inferInstance)
  · rintro (hDVR | hField)
    · letI : IsDiscreteValuationRing A := hDVR
      infer_instance
    · letI : Field A := hField.toField
      infer_instance

end
