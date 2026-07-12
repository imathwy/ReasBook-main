import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Algebra
open scoped TensorProduct

universe u v w

section

variable {A : Type u} {Aₛ : Type v} {B : Type w}
variable [CommRing A] [CommRing Aₛ] [CommRing B]
variable [Algebra A B]

/- Domain triage:
* primary domain: first cotangent homology under base localization and flat base change;
* sampled owner declarations:
  - `Algebra.H1Cotangent.map`, the canonical change-of-base map on first cotangent homology;
  - `Algebra.tensorH1CotangentOfFlat`, the owner flat base-change equivalence for `H¹(L_)`;
  - `Algebra.H1Cotangent.mapEquiv`, the canonical transport along an algebra equivalence;
  - `IsLocalization.algebraLid`, the canonical localization identification
    `Aₛ ⊗[A] B ≃ₐ[Aₛ] B`.
* best owner abstraction: the public object here is the canonical linear map
  `H1Cotangent.map A Aₛ B B`; no extra presentation-level wrapper or local comparison package is
  needed.
* primitive data: localization flatness over `A` and the canonical algebra equivalence
  `IsLocalization.algebraLid S Aₛ B`;
* derived API: the induced `Aₛ`-linear equivalence on `H¹(L_)`, whose underlying linear map is
  `H1Cotangent.map A Aₛ B B`.
* layer triage:
  - `source-facing`: bijectivity of the comparison `H¹(L_{B/A}) → H¹(L_{B/Aₛ})`;
  - `core/canonical`: `H1Cotangent.map A Aₛ B B`;
  - `bridge/view`: the canonical composite
    `moduleLid.symm ≪≫ₗ tensorH1CotangentOfFlat ≪≫ₗ H1Cotangent.mapEquiv (IsLocalization.algebraLid ...)`.
-/
-- Proof sketch: source localization is formally étale, so the Jacobi-Zariski comparison for
-- `A → Aₛ → B` is the owner-level map `H1Cotangent.map A Aₛ B B`; this is the canonical
-- `H¹` consequence of the source homotopy-equivalence statement for naive cotangent complexes.
/-- Lemma 10.134.11: if `S` is a multiplicative subset of `A` and `B` is an `Aₛ = S⁻¹A`-algebra,
then the canonical map from the first homology of the naive cotangent complex over `A` to the one
over `Aₛ` is bijective. This is the library-facing consequence of the source statement that
`NL_{B/A} → NL_{B/Aₛ}` is a homotopy equivalence. -/
@[stacks 07BS]
theorem h1Cotangent_map_bijective_of_isLocalization_source
    (S : Submonoid A) [Algebra A Aₛ] [IsLocalization S Aₛ] [Algebra Aₛ B]
    [IsScalarTower A Aₛ B] :
    Function.Bijective (H1Cotangent.map A Aₛ B B) := by
  letI : Module.Flat A Aₛ := IsLocalization.flat Aₛ S
  let e : H1Cotangent A B ≃ₗ[Aₛ] H1Cotangent Aₛ B :=
    (IsLocalization.moduleLid S Aₛ (H1Cotangent A B)).symm.trans
      ((Algebra.tensorH1CotangentOfFlat A B Aₛ).trans
        (H1Cotangent.mapEquiv Aₛ (Aₛ ⊗[A] B) B (IsLocalization.algebraLid S Aₛ B)))
  have h : ∀ x, e x = H1Cotangent.map A Aₛ B B x := by
    intro x
    simp only [e, LinearEquiv.trans_apply]
    rw [show (IsLocalization.moduleLid S Aₛ (H1Cotangent A B)).symm x = 1 ⊗ₜ[A] x by rfl]
    rw [Algebra.tensorH1CotangentOfFlat_tmul, one_smul]
    let eB : Aₛ ⊗[A] B ≃ₐ[Aₛ] B := IsLocalization.algebraLid S Aₛ B
    letI : Algebra B (Aₛ ⊗[A] B) := Algebra.TensorProduct.rightAlgebra
    letI := eB.toRingHom.toAlgebra
    letI : IsScalarTower Aₛ (Aₛ ⊗[A] B) B :=
      .of_algebraMap_eq' (((eB : Aₛ ⊗[A] B →ₐ[Aₛ] B)).comp_algebraMap).symm
    letI : TensorProduct.CompatibleSMul A Aₛ Aₛ B :=
      IsLocalization.tensorProduct_compatibleSMul S Aₛ Aₛ B
    letI : IsScalarTower B (Aₛ ⊗[A] B) B := .of_algebraMap_eq fun b ↦ by
      change b = eB (1 ⊗ₜ[A] b)
      simpa [IsLocalization.algebraLid] using
        (Algebra.TensorProduct.lidOfCompatibleSMul_tmul A Aₛ B (1 : Aₛ) b).symm
    simp only [H1Cotangent.mapEquiv, LinearEquiv.coe_mk, H1Cotangent.map]
    let f1 := ((Generators.self A B).defaultHom (Generators.self Aₛ (Aₛ ⊗[A] B))).toExtensionHom
    let f2 := ((Generators.self Aₛ (Aₛ ⊗[A] B)).defaultHom (Generators.self Aₛ B)).toExtensionHom
    let f := ((Generators.self A B).defaultHom (Generators.self Aₛ B)).toExtensionHom
    have hcomp := (Extension.H1Cotangent.map_comp_apply f1 f2 x).symm
    have hEq : Extension.H1Cotangent.map (f2.comp f1) = Extension.H1Cotangent.map f :=
      Extension.H1Cotangent.map_eq _ _
    exact hcomp.trans (by simpa using congrArg (fun g ↦ g x) hEq)
  have hmap : (e : H1Cotangent A B → H1Cotangent Aₛ B) = H1Cotangent.map A Aₛ B B := funext h
  simpa [hmap] using e.bijective

end
