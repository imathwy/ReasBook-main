import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Ideal IsLocalRing Algebra

universe u v w

section

variable {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable {L : Type v} [Field L] [Algebra A L]
variable {M : Type w} [Field M] [Algebra A M] [Algebra L M] [IsScalarTower A L M]

local notation "B" => integralClosure A L
local notation "C" => integralClosure A M

/- Domain-style sampling for unramifiedness in an integral-closure tower:
- primary domain: commutative algebra of unramified local extensions detected on integral closures
  over a discrete valuation ring;
- core/canonical owner: `Algebra.IsUnramifiedAt`;
- bridge APIs used here: `AlgHom.mapIntegralClosure`, `Ideal.under`, `Ideal.LiesOver.trans`, and
  `Algebra.IsUnramifiedAt.comp`;
- source/core/bridge triage: this item is a `bridge/view` lemma specialized to the tower
  `A ⊆ B ⊆ C`, while the actual owner predicate remains `Algebra.IsUnramifiedAt`.

Primitive data are only the pointwise unramified hypotheses on `B/A` and `C/B`. The induced
`B`-algebra structure on `C` is derived canonically from the tower map `L → M` via
`AlgHom.mapIntegralClosure`; no separate public tower-map wrapper is needed. -/

noncomputable local instance : Algebra B C :=
  ((IsScalarTower.toAlgHom A L M).mapIntegralClosure : B →ₐ[A] C).toAlgebra

local instance :
    IsScalarTower A B C := by
  refine IsScalarTower.of_algebraMap_eq ?_
  intro x
  ext
  simp [RingHom.algebraMap_toAlgebra, IsScalarTower.algebraMap_apply A L M]

private local instance algebraIsIntegral_base : Algebra.IsIntegral A B :=
  IsIntegralClosure.isIntegral_algebra A L

private local instance algebraIsIntegral_top : Algebra.IsIntegral A C :=
  IsIntegralClosure.isIntegral_algebra A M

private local instance algebraIsIntegral_tower : Algebra.IsIntegral B C :=
  Algebra.IsIntegral.tower_top A

-- Proof sketch: for `P : Ideal C`, let `p := P.under B`. Then `p` lies over `maximalIdeal A`,
-- and `P` lies over `p`. Apply the two hypotheses to get `Algebra.IsUnramifiedAt A p` and
-- `Algebra.IsUnramifiedAt B P`, then compose them with `Algebra.IsUnramifiedAt.comp`.
/-- Helper for Lemma 15.112.9: the contraction of a maximal ideal of the top integral closure to
the intermediate integral closure is again maximal. -/
private lemma under_isMaximal_integralClosure_tower
    (P : Ideal C) [P.IsMaximal] :
    (P.under B).IsMaximal := by
  -- View `P.under B` as a comap along the integral map `B → C`.
  simpa [Ideal.under_def] using
    (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P :
      (Ideal.comap (algebraMap B C) P).IsMaximal)

/-- Helper for Lemma 15.112.9: if a maximal ideal of the top integral closure lies over
`maximalIdeal A`, then its contraction to the intermediate integral closure still lies over
`maximalIdeal A`. -/
private lemma under_liesOver_maximalIdeal_of_liesOver_maximalIdeal
    (P : Ideal C) [P.LiesOver (maximalIdeal A)] :
    (P.under B).LiesOver (maximalIdeal A) := by
  -- Rewrite both lies-over statements as equalities of contracted ideals in the tower.
  rw [Ideal.liesOver_iff]
  calc
    maximalIdeal A = P.under A := (Ideal.liesOver_iff P (maximalIdeal A)).1 inferInstance
    _ = (P.under B).under A := by
      simp [Ideal.under_def, Ideal.comap_comap, IsScalarTower.algebraMap_eq A B C]

/-- Helper for Lemma 15.112.9: once unramifiedness is known on the contracted branch and on the
top branch over that contraction, the composition theorem yields unramifiedness over the base. -/
private lemma isUnramifiedAt_comp_of_under_branch
    (P : Ideal C) [P.IsMaximal] [P.LiesOver (maximalIdeal A)]
    [Algebra.IsUnramifiedAt A (P.under B)] [Algebra.IsUnramifiedAt B P] :
    Algebra.IsUnramifiedAt A P := by
  -- Route correction: compose along the intermediate branch `P.under B` rather than switching
  -- to ramification indices; this follows the source tower argument directly.
  letI : (P.under B).IsMaximal := under_isMaximal_integralClosure_tower P
  letI : (P.under B).IsPrime := Ideal.IsMaximal.isPrime inferInstance
  letI : P.IsPrime := Ideal.IsMaximal.isPrime inferInstance
  letI : P.LiesOver (P.under B) := by
    simpa using (Ideal.over_under (A := B) P)
  exact Algebra.IsUnramifiedAt.comp (P.under B) P

/-- Lemma 15.112.9: let `B = integralClosure A L` and `C = integralClosure A M`. If every maximal
ideal of `B` over `maximalIdeal A` is unramified over `A`, and every maximal ideal of `C` over
`maximalIdeal A` is unramified over the intermediate integral closure `B`, then every maximal
ideal of `C` over `maximalIdeal A` is unramified over `A`. -/
@[stacks 0EXS]
theorem isUnramifiedAt_of_integralClosure_tower
    (hL : ∀ (p : Ideal B) [p.IsMaximal] [p.LiesOver (maximalIdeal A)],
      Algebra.IsUnramifiedAt A p)
    (hM : ∀ (P : Ideal C) [P.IsMaximal] [P.LiesOver (maximalIdeal A)],
        Algebra.IsUnramifiedAt B P)
    (P : Ideal C) [P.IsMaximal] [P.LiesOver (maximalIdeal A)] :
    Algebra.IsUnramifiedAt A P := by
  -- First contract the branch to the intermediate integral closure.
  letI : (P.under B).IsMaximal := under_isMaximal_integralClosure_tower P
  letI : (P.under B).LiesOver (maximalIdeal A) :=
    under_liesOver_maximalIdeal_of_liesOver_maximalIdeal P
  -- Then install the two unramified branches supplied by the hypotheses.
  letI : Algebra.IsUnramifiedAt A (P.under B) := hL (P.under B)
  letI : Algebra.IsUnramifiedAt B P := hM P
  -- Finally compose the two branchwise unramifiedness facts along the tower.
  exact isUnramifiedAt_comp_of_under_branch (A := A) (L := L) (M := M) P

end
