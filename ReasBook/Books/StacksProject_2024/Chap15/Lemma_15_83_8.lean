import Mathlib
import Mathlib.Data.List.TFAE
import StacksProject_2024.Chap15.Lemma_15_82_10

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} {B : Type u} {A : Type u}
variable [CommRing R] [CommRing B] [CommRing A]
variable [Algebra R B] [Algebra B A] [Algebra R A] [IsScalarTower R B A]
variable [Module.Flat R B] [Algebra.FinitePresentation R B]
variable [Module.Flat R A] [Algebra.FinitePresentation R A]

local notation "DModA" => DerivedCategory (ModuleCat A)
local notation "DModB" => DerivedCategory (ModuleCat B)

-- Proof sketch: first use flat finite presentation to regard `R → B` and `R → A` as perfect, hence
-- pseudo-coherent, ring maps. Then apply Lemma `15.83.7` to identify absolute and relative
-- pseudo-coherence over `R` for both `A` and `B`, Lemma `15.82.15` to compare relative
-- pseudo-coherence over `R` and over `A`, and Lemma `15.65.11` together with surjectivity of
-- `B → A` to compare `K` with its restriction of scalars.
/-- Lemma 15.83.8: let `R → B → A` be ring maps with `B → A` surjective and with `R → B` and
`R → A` flat and of finite presentation. For `K ∈ D(A)`, the following are equivalent:
`K` is pseudo-coherent, `K` is pseudo-coherent relative to `R`, `K` is pseudo-coherent relative
to `A`, its restriction of scalars to `D(B)` is pseudo-coherent, and that restriction is
pseudo-coherent relative to `R`. -/
theorem isPseudoCoherent_tfae_of_surjective_of_flat_of_finitePresentation
    (K : DModA) (hφ : Function.Surjective (algebraMap B A)) :
    List.TFAE [
      K.IsPseudoCoherent,
      K.IsPseudoCoherentRelativeTo R,
      K.IsPseudoCoherentRelativeTo A,
      (((ModuleCat.restrictScalars (algebraMap B A)).mapDerivedCategory.obj K)).IsPseudoCoherent,
      (((ModuleCat.restrictScalars (algebraMap B A)).mapDerivedCategory.obj K)).IsPseudoCoherentRelativeTo R
    ] := sorry

-- Proof sketch: repeat the same comparison chain as in the pseudo-coherent case, now using the
-- `m`-pseudo-coherent variants of Lemmas `15.83.7`, `15.82.15`, and `15.65.11`.
/-- Under the same hypotheses, the analogous five-way equivalence also holds for
`m`-pseudo-coherence. -/
theorem isMPseudoCoherent_tfae_of_surjective_of_flat_of_finitePresentation
    (K : DModA) (m : ℤ) (hφ : Function.Surjective (algebraMap B A)) :
    List.TFAE [
      K.IsMPseudoCoherent m,
      K.IsMPseudoCoherentRelativeTo R m,
      K.IsMPseudoCoherentRelativeTo A m,
      (((ModuleCat.restrictScalars (algebraMap B A)).mapDerivedCategory.obj K)).IsMPseudoCoherent m,
      (((ModuleCat.restrictScalars (algebraMap B A)).mapDerivedCategory.obj K)).IsMPseudoCoherentRelativeTo R m
    ] := sorry

end

end CategoryTheory
