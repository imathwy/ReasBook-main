import Mathlib
import stacks_project.Chap10.Proposition_10_88_6

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

namespace Module

section

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/- Domain-style sampling:
* primary domain: Mittag-Leffler modules over a commutative ring, organized around the finitely
  presented tensor-kernel criterion from Proposition `10.88.6`.
* inspected owner declarations:
  `directed_colimit_presentation_mittag_leffler_tfae` from `Proposition_10_88_6`,
  `Module.FinitePresentation.equiv_quotient`, and
  `Module.finitePresentation_of_projective`.
* best owner abstraction: the finitely presented tensor-kernel criterion, with finitely presented
  modules as the canonical auxiliary presentation objects.
* layer: `source-facing`; this lemma is the finite-free-source bridge to that criterion.
* primitive data: the module `M`, a finite free source module `F`, and a map `f : F →ₗ[R] M`.
* derived API: the finitely presented comparison module `Q` and the tensor-kernel comparison map
  produced from the criterion.
-/
-- Proof sketch: one direction specializes the finitely presented criterion from Proposition
-- `10.88.6` to finite free source modules. For the converse, given a map from a finitely presented
-- module, use the canonical finite free presentation of that source from
-- `Module.FinitePresentation.equiv_quotient`, apply the assumed finite-free condition on the
-- presenting free module, and descend the resulting comparison map through the quotient to recover
-- the finitely presented criterion.
/-- Lemma 10.88.10: an `R`-module `M` is Mittag-Leffler if and only if every map from a finite
free `R`-module to `M` has the same tensor kernels as some map to a finitely presented
`R`-module. -/
theorem mittagLeffler_iff_finiteFree_maps_share_tensor_kernels_with_finitelyPresented_maps :
    (∀ (P : ModuleCat.{max v w} R) [Module.FinitePresentation R P] (f : P →ₗ[R] M),
        ∃ (Q : ModuleCat.{max v w} R) (_ : Module.FinitePresentation R Q) (g : P →ₗ[R] Q),
          ∀ N : ModuleCat.{max v w} R,
            LinearMap.ker (f.rTensor N) = LinearMap.ker (g.rTensor N)) ↔
      ∀ (F : ModuleCat.{max v w} R) [Module.Free R F] [Module.Finite R F] (f : F →ₗ[R] M),
        ∃ (Q : ModuleCat.{max v w} R) (_ : Module.FinitePresentation R Q) (g : F →ₗ[R] Q),
          ∀ N : ModuleCat.{max v w} R,
            LinearMap.ker (f.rTensor N) = LinearMap.ker (g.rTensor N) := sorry

end

end Module
