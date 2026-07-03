import Mathlib
import StacksProject_2024.Chap15.Definition_15_65_1
import StacksProject_2024.Chap15.Lemma_15_65_3
import StacksProject_2024.Chap15.Lemma_15_65_6
import StacksProject_2024.Chap15.Lemma_15_60_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open scoped DerivedTensorWithAlgebra

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R R' : Type u} [CommRing R] [CommRing R']

local notation "DModR" => DerivedCategory (ModuleCat R)

/- Domain-style sampling for Lemma 15.65.15:
- primary domain: faithful-flat descent of pseudo-coherence in derived categories of modules;
- sampled owner declarations:
  `DerivedCategory.IsMPseudoCoherent`,
  `DerivedCategory.IsPseudoCoherent`,
  `derivedTensorWithAlgebra`,
  `isPseudoCoherent_iff_forall_isMPseudoCoherent`;
- best owner abstraction: this file is `source-facing`, so the public descent statements should be
  organized around the actual ring map `f : R →+* R'`; the `core/canonical` owners remain the
  Chapter 15 predicates `K.IsMPseudoCoherent` and `K.IsPseudoCoherent` on `D(R)`, together with
  the derived scalar-extension owner `derivedTensorWithAlgebra f`, while the chapter base-change
  notation `K ⊗[R]^L[R']` remains the bridge view after passing from `f` to `f.toAlgebra`;
- primitive vs. derived:
  primitive data are the ring map `f`, the derived object `K`, the faithfully flatness of `f`,
  and the pseudo-coherence of the derived base change along `f`;
  the descent statements below are derived API over those owners, so there should be no parallel
  wrapper notion for faithful-flat descent itself;
- source/core/bridge triage:
  `source-facing`: descent of `m`-pseudo-coherence and pseudo-coherence;
  `core/canonical`: `DerivedCategory.IsMPseudoCoherent`,
    `DerivedCategory.IsPseudoCoherent`, and `derivedTensorWithAlgebra`;
  `bridge/view`: the chapter notation `K ⊗[R]^L[R']` for derived scalar extension along the
    explicit ring map `f`.

This file therefore keeps the source-facing descent theorems, but its public surface should stay
entirely on the existing owner predicates and the canonical scalar-extension owner notation, with
the ring map kept explicit rather than hidden in an ambient algebra instance.
-/

-- Proof sketch: use faithful flatness to reflect the vanishing range of cohomology from the
-- base-changed derived complex back to `K`, descend finiteness of the top surviving cohomology by
-- faithful-flat descent for modules, and then run the downward induction on the largest nonzero
-- cohomological degree as in the Stacks proof, applying Lemmas `15.65.7`, `15.65.3`, and
-- `15.65.2` to the cone construction.
/-- Lemma 15.65.15 (1): if the faithfully flat derived base change of a derived `R`-complex `K`
along a faithfully flat ring map `f : R →+* R'` is `m`-pseudo-coherent, then `K` is
`m`-pseudo-coherent. -/
theorem isMPseudoCoherent_of_faithfullyFlat_baseChange
    (f : R →+* R') (K : DModR) (m : ℤ)
    (hff : f.FaithfullyFlat)
    (hK : ((derivedTensorWithAlgebra f).obj K).IsMPseudoCoherent m) :
    K.IsMPseudoCoherent m := sorry

-- Proof sketch: apply part `(1)` for every integer `m` and then use the canonical owner theorem
-- `isPseudoCoherent_iff_forall_isMPseudoCoherent`.
/-- Lemma 15.65.15 (2): if the faithfully flat derived base change of a derived `R`-complex `K`
along a faithfully flat ring map `f : R →+* R'` is pseudo-coherent, then `K` is
pseudo-coherent. -/
theorem isPseudoCoherent_of_faithfullyFlat_baseChange
    (f : R →+* R') (K : DModR)
    (hff : f.FaithfullyFlat)
    (hK : ((derivedTensorWithAlgebra f).obj K).IsPseudoCoherent) :
    K.IsPseudoCoherent := by
  rw [isPseudoCoherent_iff_forall_isMPseudoCoherent] at hK ⊢
  intro m
  exact isMPseudoCoherent_of_faithfullyFlat_baseChange f K m hff (hK m)

end

end CategoryTheory
