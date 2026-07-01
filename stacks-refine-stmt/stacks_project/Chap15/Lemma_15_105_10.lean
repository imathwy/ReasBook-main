import stacks_project.Chap10.Lemma_10_39_10
import stacks_project.Chap15.Definition_15_105_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open Algebra.TensorProduct

universe u v w

namespace Algebra

section

variable {A : Type u} {B : Type v} {C : Type w}
variable [CommRing A] [CommRing B] [CommRing C]
variable [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]

/- Domain triage:
- primary domain: commutative algebra of faithfully flat descent for weakly étale ring maps;
- source-facing layer: part `(1)` is the tensor-square flatness descent statement appearing in the
  source text;
- core/canonical owners sampled for this file: `RingHom.FaithfullyFlat`,
  `flat_iff_flat_baseChange_of_faithfullyFlat`,
  `algebraMap_flat_of_flat_of_faithfullyFlat`, and the owner class `IsWeaklyEtale`;
- primitive data: faithful flatness of `B → C` and an explicit weakly étale owner proof on
  `A → C`;
- derived API: flatness of `A → B` and of the tensor-square multiplication `B ⊗[A] B → B`.

The file remains source-facing: there is no exact upstream owner theorem with this interface. The
refinement is to keep part `(1)` as the bridge theorem and expose part `(2)` as an owner theorem in
`IsWeaklyEtale`, matching the chapter's existing weakly étale API.
-/

-- Proof sketch: view `C ⊗[A] C → C` as the faithfully flat base change of
-- `B ⊗[A] B → B` along `B → C`. Then apply the flatness descent criterion of Lemma `10.39.9` to
-- descend flatness of `C` as a module over `C ⊗[A] C` to flatness of `B` as a module over
-- `B ⊗[A] B`.
/-- Lemma 15.105.10 (1): if `B → C` is faithfully flat and the multiplication map
`C ⊗[A] C → C` is flat, then the multiplication map `B ⊗[A] B → B` is flat. -/
theorem tensorSquareMul_flat_of_faithfullyFlat
    (hBC_ff : (algebraMap B C).FaithfullyFlat)
    (hflatMul : (lmul' A : C ⊗[A] C →ₐ[A] C).Flat) :
    (lmul' A : B ⊗[A] B →ₐ[A] B).Flat := sorry

namespace IsWeaklyEtale

-- Proof sketch: weakly étale means flatness of `A → C` together with flatness of the
-- multiplication map `C ⊗[A] C → C`. Use the derived owner theorem `IsWeaklyEtale.flat` for
-- `A → C`, convert it back to the module-flat instance needed by Lemma `10.39.10`, and descend
-- along the faithfully flat map `B → C`. Then descend the tensor-square flatness by part `(1)`.
/-- Lemma 15.105.10 (2): if `B → C` is faithfully flat and `A → C` is weakly étale, then
`A → B` is weakly étale. -/
theorem of_faithfullyFlat
    (hBC_ff : (algebraMap B C).FaithfullyFlat)
    (hAC : IsWeaklyEtale A C) :
    IsWeaklyEtale A B := by
  sorry

end IsWeaklyEtale

end

end Algebra
