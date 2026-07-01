import Mathlib
import stacks_project.Chap21.Definition_21_13_4
import stacks_project.Chap21.Lemma_21_13_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u v

namespace CategoryTheory
namespace Sheaf

variable {C : Type u} [Category.{max u v} C] {J : GrothendieckTopology C}
variable [HasSheafify J (Type (max u v))]
variable [HasSheafify J AddCommGrpCat.{max u v}]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [HasExt (Sheaf J AddCommGrpCat.{max u v})]

/-- The underlying presheaf morphism attached to a morphism of sheaves of sets. -/
abbrev underlyingPresheafHom {K K' : Sheaf J (Type (max u v))} (α : K' ⟶ K) :
    (sheafToPresheaf J (Type (max u v))).obj K' ⟶
      (sheafToPresheaf J (Type (max u v))).obj K :=
  (sheafToPresheaf J (Type (max u v))).map α

/-- Every positive cohomology group of `F` over an object of the site vanishes. -/
def ObjectwiseHigherCohomologyVanishes
    (F : Sheaf J AddCommGrpCat.{max u v}) : Prop :=
  ∀ (U : C) (n : ℕ), IsZero (F.H' (n + 1) U)

/-- The extended Čech complex on degree-zero cohomology is exact for locally surjective morphisms
of sheaves of sets, formalized by vanishing of the positive-degree `E₂^{p,0}` terms of any
associated Čech spectral sequence. -/
def HasExactExtendedCechComplexOnSheafSurjections
    (F : Sheaf J AddCommGrpCat.{max u v}) : Prop :=
  ∀ ⦃K K' : Sheaf J (Type (max u v))⦄ (α : K' ⟶ K)
    (hα : Presheaf.IsLocallySurjective J (underlyingPresheafHom α))
    (S : LocallySurjectiveCechSpectralSequence (underlyingPresheafHom α) F)
    (p : ℕ), 0 < p →
      IsZero ((S.spectralSequence.page 2 (by decide)).X (p, 0))

-- Proof sketch: for the forward implication, apply total acyclicity to the representable sheaves
-- `h_U^#` and to the Čech nerve levels of a locally surjective map of sheaves, then use the
-- spectral sequence from Lemma `21.13.2` to identify the `E₂^{p,0}` terms with the cohomology of
-- the extended Čech complex on `H^0(-, F)`. For the converse, start from a locally surjective
-- resolution of an arbitrary sheaf of sets by coproducts of representables and repeat the source
-- induction on the cohomological degree, using the vanishing on objects and the Čech exactness
-- hypothesis to force all relevant `E₂`-terms to vanish.
/-- Lemma 21.13.5: an abelian sheaf `F` on a site is totally acyclic if and only if all higher
cohomology groups `H^p(U, F)` vanish for every object `U` of the site and, for every surjective
morphism of sheaves of sets, the extended Čech complex on `H^0(-, F)` is exact. The Čech
exactness clause is formalized here by vanishing of the positive-degree `E₂^{p,0}` terms of the
associated Čech spectral sequence. -/
theorem isTotallyAcyclicOne_iff_objectwiseHigherCohomologyVanishes_and_exactExtendedCechComplex
    (F : Sheaf J AddCommGrpCat.{max u v}) :
    IsTotallyAcyclicOne F ↔
      ObjectwiseHigherCohomologyVanishes F ∧
        HasExactExtendedCechComplexOnSheafSurjections F := sorry

end Sheaf
end CategoryTheory
