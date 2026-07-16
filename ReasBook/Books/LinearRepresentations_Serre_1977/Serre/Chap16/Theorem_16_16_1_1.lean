import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap16.Infra_16_1_DecompositionSurjectivity

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

namespace Representation

open scoped Representation
open scoped MonoidAlgebra
open scoped TensorProduct
open CategoryTheory
open IsCyclotomicExtension.Rat

section

-- Faithful DVR form of Serre's Theorem 33 (Theorem 16-16.1-1).  As recorded for Theorem 17-17.2-1
-- and Corollary 17-17.2-2, the surjectivity statement quantified over an *arbitrary* large field
-- `K` is not provable from the repository's Brauer induction (which lives in the cyclotomic
-- framework), and — dropping the discrete-valuation hypothesis — is in fact false.  We therefore
-- take the `(K, A, k)` `p`-modular system in its faithful form: `A` a complete (Henselian) discrete
-- valuation ring whose fraction field is the *maximally large* field `Frac A = Lexp = ℚ(ζ_{exp G})`
-- (the full cyclotomic field, realized as `↥(⊤ : IntermediateField ℚ Lexp)`), which forces Serre's
-- arithmetic subgroup `Γ_K = ⊥`, i.e. ordinary elementary subgroups.  `A`, `G` live in `Type` (=
-- `Type 0`) because Theorem 17-17.2-1 forces `A`, `G` and the cyclotomic field into a single
-- universe and `Lexp` is always `Type 0`.
variable {A : Type} [CommRing A] [IsLocalRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [HenselianLocalRing A]
variable {G : Type} [Group G] [Finite G]
variable {p : ℕ} [hpp : Fact p.Prime] [hCharP : CharP (IsLocalRing.ResidueField A) p]

local notation "k" => IsLocalRing.ResidueField A
local notation "Lexp" => CyclotomicField (Monoid.exponent G) ℚ
local instance instNumberFieldLexp_thm1611 : NumberField Lexp := inferInstance
local instance instCyclotomicLexp_thm1611 : IsCyclotomicExtension {Monoid.exponent G} ℚ Lexp :=
  CyclotomicField.isCyclotomicExtension (n := Monoid.exponent G) (K := ℚ)

include hpp hCharP in
/-- Theorem 16-16.1-1 (Serre's Theorem 33), faithful cyclotomic complete-DVR form: for a finite
group `G` and the `p`-modular system given by a complete discrete valuation ring `A` whose fraction
field is the full cyclotomic field `Frac A = ℚ(ζ_{exp G}) = ↥(⊤ : IntermediateField ℚ Lexp)`
(so `K` is sufficiently large, `Γ_K = ⊥`), Serre's decomposition homomorphism
`d = decompositionHom A K G : R₀[K](G) → R₀[k](G)` is surjective.

The proof is Serre's: Theorem 39 generates `R₀[k](G)` by induction from the (`Γ_K = ⊥`, hence
ordinary) elementary subgroups, `d` commutes with subgroup induction by the induced-lattice
/reduction bridge, and Theorem 41 lifts every simple module on an elementary subgroup. -/
theorem decompositionHom_surjective
    [Algebra A ↥(⊤ : IntermediateField ℚ Lexp)]
    [IsFractionRing A ↥(⊤ : IntermediateField ℚ Lexp)] :
    Function.Surjective (decompositionHom A ↥(⊤ : IntermediateField ℚ Lexp) G) :=
  decompositionHom_surjective_of_hasEnoughRootsOfUnity (A := A) (p := p)
    (⊤ : IntermediateField ℚ Lexp) (gammaSubgroup_top_eq_bot_bridge (G := G))

end

end Representation
