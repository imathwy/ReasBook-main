import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open Algebra

universe u v

section

variable {R : Type u} {A : Type u} {C : Type u}
variable [CommRing R] [CommRing A] [CommRing C]
variable [Algebra R A] [Algebra R C] [Algebra A C] [IsScalarTower R A C]
variable {ι : Type v} {m : ℕ}

/- Domain-style sampling:
- primary domain: Jacobi-Zariski/conormal exact sequences for composite algebra presentations;
- sampled owner declarations:
  `Generators.Cotangent.exact`,
  `Generators.Cotangent.surjective_map_ofComp`,
  `Generators.toExtension.CotangentSpace`,
  `Extension.Cotangent.map`,
  `LinearEquiv.postcomp_exact_iff_exact`;
- best owner abstraction: the upstream Jacobi-Zariski conormal sequence for a composite
  presentation, with this file adding only the source-facing identification of the right-hand
  conormal module with `C ⊗[A] LinearMap.ker q`;
- primitive data: presentations `P`, `Q`, the chosen map `q` on the canonical cotangent-space
  owner of `Q`, and the chosen identification `e`;
- derived API: exactness and surjectivity of the resulting source-facing sequence.

Source/core/bridge triage:
- `source-facing`: the exact sequence after identifying the conormal module of `Q` with
  `C ⊗[A] LinearMap.ker q`;
- `core/canonical`: `Generators.Cotangent.exact` and
  `Generators.Cotangent.surjective_map_ofComp`;
- `bridge/view`: the theorem below, obtained by postcomposing the canonical right map with `e`.
-/

-- Proof sketch: apply the Jacobi-Zariski exact sequence to the composite presentation
-- `R[x] → A` and a chosen presentation `A[y] → C`. The rightmost conormal module of the
-- `A[y] → C` presentation is then identified with `C ⊗[A] K` via the chosen linear equivalence
-- `e`, where `K = ker(q)`.
/-- 16.3.1.1: after identifying the conormal module of a presentation of `C` over `A` with
`C ⊗[A] K` for `K = ker(q)`, the composite presentation yields the exact sequence
`(I / I²) ⊗[A] C → J / J² → K ⊗[A] C → 0`, written in the library-facing tensor order
`C ⊗[A] (I / I²)` and `C ⊗[A] K`. -/
@[stacks 07EW]
theorem presentation_conormal_tensor_sequence
    (P : Generators R A ι)
    (Q : Generators A C (Fin m))
    (q : Q.toExtension.CotangentSpace →ₗ[A] P.toExtension.Cotangent)
    (e : Q.toExtension.Cotangent ≃ₗ[C] C ⊗[A] LinearMap.ker q) :
    Function.Exact
        ((Extension.Cotangent.map (Q.toComp P).toExtensionHom).liftBaseChange C)
        (e.toLinearMap ∘ₗ Extension.Cotangent.map (Q.ofComp P).toExtensionHom) ∧
      Function.Surjective
        (e.toLinearMap ∘ₗ Extension.Cotangent.map (Q.ofComp P).toExtensionHom) := by
  constructor
  · simpa only using
      e.postcomp_exact_iff_exact.2 (Generators.Cotangent.exact Q P)
  · simpa only using e.surjective.comp (Generators.Cotangent.surjective_map_ofComp Q P)

end
