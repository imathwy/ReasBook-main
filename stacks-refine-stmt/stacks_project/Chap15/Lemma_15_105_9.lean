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
- primary domain: commutative algebra of weakly étale ring maps and tensor-square multiplication
  under composition;
- source-facing layer: part `(1)` is the tensor-square flatness statement for the composite;
- core/canonical owners sampled for this file:
  `Algebra.IsWeaklyEtale`,
  `Module.Flat.trans`,
  and `RingHom.Flat.comp`;
- primitive data: the two flat tensor-square multiplication maps, together with the owner facts on
  `A → B` and `B → C` for the composition theorem in part `(2)`;
- derived API: the source-facing tensor-square flatness theorem `tensorSquareMul_flat_comp`;
- bridge/view: there is no separate upstream ring-map owner in this environment, so part `(2)` is
  the owner theorem `Algebra.IsWeaklyEtale.comp` itself.
-/

-- Proof sketch: factor `C ⊗[A] C → C` through the base change of `B ⊗[A] B → B` along
-- `B ⊗[A] B → C ⊗[A] C`, identify the intermediate map with `C ⊗[B] C → C`, and apply flat base
-- change together with stability of flat ring maps under composition.
/-- Lemma 15.105.9 (1): if the multiplication maps `B ⊗[A] B → B` and `C ⊗[B] C → C` are flat,
then the multiplication map `C ⊗[A] C → C` is flat. -/
theorem tensorSquareMul_flat_comp
    (hAB : (lmul' A : B ⊗[A] B →ₐ[A] B).Flat)
    (hBC : (lmul' B : C ⊗[B] C →ₐ[B] C).Flat) :
    (lmul' A : C ⊗[A] C →ₐ[A] C).Flat := by
  sorry

namespace IsWeaklyEtale

-- Proof sketch: compose flatness of `A → B` and `B → C` by `Module.Flat.trans`, and use part
-- `(1)` for the tensor-square multiplication clause of the composite.
/-- Lemma 15.105.9 (2): the composite of weakly étale ring maps is weakly étale. -/
theorem comp (hAB : IsWeaklyEtale A B) (hBC : IsWeaklyEtale B C) : IsWeaklyEtale A C := by
  letI : Module.Flat A B := hAB.moduleFlat
  letI : Module.Flat B C := hBC.moduleFlat
  exact
    { moduleFlat := Module.Flat.trans A B C
      flat_tensorSquareMultiplication :=
        tensorSquareMul_flat_comp hAB.flat_tensorSquareMultiplication
          hBC.flat_tensorSquareMultiplication }

end IsWeaklyEtale

end

end Algebra
