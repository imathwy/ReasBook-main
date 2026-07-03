import Mathlib
import StacksProject_2024.Chap15.Lemma_15_82_10

noncomputable section

open CategoryTheory

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R A B : Type u}
variable [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
variable [Algebra.FiniteType R A] [Module.Finite A B]

local notation "DModA" => DerivedCategory (ModuleCat A)
local notation "DModB" => DerivedCategory (ModuleCat B)
local notation "restrictScalarsDerived" =>
  CategoryTheory.Functor.mapDerivedCategory (ModuleCat.restrictScalars (algebraMap A B))

private theorem finiteType_over_base
    (R A B : Type u)
    [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [Algebra.FiniteType R A] [Module.Finite A B] :
    Algebra.FiniteType R B := by
  exact
    Algebra.FiniteType.trans
      (inferInstance : Algebra.FiniteType R A)
      (inferInstance : Algebra.FiniteType A B)

/-
Domain-style sampling for Lemma 15.82.5:
- primary domain: relative pseudo-coherence in derived categories under restriction of scalars
  along a finite algebra map;
- sampled owner declarations:
  `DerivedCategory.IsMPseudoCoherentRelativeTo`,
  `DerivedCategory.IsPseudoCoherentRelativeTo`,
  `isMPseudoCoherent_iff_restrictScalars`,
  `isPseudoCoherent_iff_restrictScalars`;
- best owner abstraction: the source-facing content is the pair of comparison theorems below,
  while the canonical owner predicates are
  `DerivedCategory.IsMPseudoCoherentRelativeTo` and
  `DerivedCategory.IsPseudoCoherentRelativeTo`; the restriction construction itself is owned by
  `(ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory`;
- primitive vs. derived:
  primitive data are the relative pseudo-coherence owners, the finite-type structure on `A` over
  `R`, and the finite map hypothesis `[Module.Finite A B]`;
  the induced finite-type structure on `B` over `R` is derived internally by the canonical
  transitivity instance for finite type algebras;
- source/core/bridge triage:
  `source-facing`: the two comparison theorems below;
  `core/canonical`: `DerivedCategory.IsMPseudoCoherentRelativeTo`,
    `DerivedCategory.IsPseudoCoherentRelativeTo`, and `Functor.mapDerivedCategory`;
  `bridge/view`: restriction of scalars along `algebraMap A B`, together with the internal
    finite-type witness on `R → B`.
-/

-- Proof sketch: for any surjective polynomial presentation `P → A`, compose with the finite map
-- `A → B` to view `B` as a finite `P`-algebra, then apply Lemma `15.65.11` over `P` to compare
-- `m`-pseudo-coherence of `K` with that of its restriction along `A → B`.
/-- Lemma 15.82.5: let `R` be a ring, let `A → B` be a finite map of finite type `R`-algebras,
let `m ∈ ℤ`, and let `K` be a derived `B`-complex. Then `K` is `m`-pseudo-coherent relative to
`R` if and only if the same object, viewed by restriction of scalars as a derived `A`-complex, is
`m`-pseudo-coherent relative to `R`. -/
theorem isMPseudoCoherentRelativeTo_iff_restrictScalars_of_finite
    (K : DModB) (m : ℤ) :
    by
      letI : Algebra.FiniteType R B := finiteType_over_base R A B
      exact
        K.IsMPseudoCoherentRelativeTo R m ↔
          ((restrictScalarsDerived).obj K).IsMPseudoCoherentRelativeTo R m := by
  sorry

-- Proof sketch: apply the previous theorem for each integer `m`, using the canonical owner
-- `IsPseudoCoherentRelativeTo` as the universal quantification of the `m`-relative notion.
/-- Under the same finite-map hypotheses, relative pseudo-coherence over `R` is unchanged by
restricting scalars from `B` to `A`. -/
theorem isPseudoCoherentRelativeTo_iff_restrictScalars_of_finite
    (K : DModB) :
    by
      letI : Algebra.FiniteType R B := finiteType_over_base R A B
      exact
        K.IsPseudoCoherentRelativeTo R ↔
          ((restrictScalarsDerived).obj K).IsPseudoCoherentRelativeTo R := by
  sorry

end

end CategoryTheory
