import Mathlib.RepresentationTheory.Basic

namespace Representation

/-
Source/core/bridge triage:
* source-facing: Serre's external tensor-product notation `ρ₁ ⊠ ρ₂` for representations of the
  product monoid `G₁ × G₂`.
* core/canonical: the restricted tensor-product owner
  `(ρ₁.comp (MonoidHom.fst G₁ G₂)).tprod (ρ₂.comp (MonoidHom.snd G₁ G₂))`.
* bridge/view: this file exposes only the notation for the canonical owner, with no extra wrapper.

Primitive data are only the two representations `ρ₁` and `ρ₂`. The action of `G₁ × G₂` is
derived canonically by restricting along `MonoidHom.fst` and `MonoidHom.snd` and then applying
`Representation.tprod`.
-/
namespace ExternalTensor

/- Do `open scoped Representation.ExternalTensor` to use `ρ₁ ⊠ ρ₂` for the canonical external
tensor product `(ρ₁.comp (MonoidHom.fst G₁ G₂)).tprod (ρ₂.comp (MonoidHom.snd G₁ G₂))`. -/
set_option quotPrecheck false in
scoped notation:80 ρl:80 " ⊠ " ρr:81 =>
  (fun {k : Type _} {G₁ : Type _} {G₂ : Type _} [CommSemiring k] [Monoid G₁] [Monoid G₂]
    {V₁ : Type _} {V₂ : Type _} [AddCommMonoid V₁] [Module k V₁] [AddCommMonoid V₂]
    [Module k V₂] (ρ₁ : Representation k G₁ V₁) (ρ₂ : Representation k G₂ V₂) ↦
      Representation.tprod (ρ₁.comp (MonoidHom.fst G₁ G₂)) (ρ₂.comp (MonoidHom.snd G₁ G₂)))
    ρl ρr

end ExternalTensor

end Representation
