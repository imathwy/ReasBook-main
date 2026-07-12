import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace RingHom

/- Domain triage:
* primary domain: deformation-theoretic properties of surjective maps of local Artinian rings;
* sampled owner style: map properties in mathlib/project are packaged as owner predicates/classes
  such as `IsLocalHom`, while numerical length is already canonically `Module.length`;
* layer split: the source-facing owner here is the property of a ring map being a small extension,
  and surjectivity together with the kernel-length equation are primitive data for that owner.
-/

/-- Definition 10.141.1: a ring map `φ : B' →+* B` is a small extension if `B'` and `B` are local
Artinian rings, `φ` is surjective, and the kernel ideal `RingHom.ker φ` has length `1` as a
`B'`-module. -/
@[stacks 02HS]
class IsSmallExtension {B' : Type u} {B : Type v} [CommRing B'] [CommRing B]
    (φ : B' →+* B) : Prop where
  [instIsLocalRingSource : IsLocalRing B']
  [instIsArtinianRingSource : IsArtinianRing B']
  [instNontrivialTarget : Nontrivial B]
  surjective : Function.Surjective φ
  ker_length : Module.length B' (RingHom.ker φ) = 1

attribute [instance] IsSmallExtension.instIsLocalRingSource
attribute [instance] IsSmallExtension.instIsArtinianRingSource
attribute [instance] IsSmallExtension.instNontrivialTarget

theorem IsSmallExtension.isLocalRingTarget {B' : Type u} {B : Type v} [CommRing B'] [CommRing B]
    {φ : B' →+* B} [hφ : φ.IsSmallExtension] : IsLocalRing B := by
  let _ : Nontrivial B := hφ.instNontrivialTarget
  exact IsLocalRing.of_surjective' φ hφ.surjective

theorem IsSmallExtension.isArtinianRingTarget {B' : Type u} {B : Type v} [CommRing B']
    [CommRing B] {φ : B' →+* B} [hφ : φ.IsSmallExtension] : IsArtinianRing B :=
  hφ.surjective.isArtinianRing

section

variable {B' : Type u} {B : Type v} [CommRing B'] [CommRing B] (φ : B' →+* B)

/-- A surjective homomorphism of local Artinian rings with kernel of module length `1` is a small
extension. -/
instance [IsLocalRing B'] [IsArtinianRing B'] [Nontrivial B]
    (hφ : Function.Surjective φ) (hker : Module.length B' (RingHom.ker φ) = 1) :
    φ.IsSmallExtension :=
  { surjective := hφ
    ker_length := hker }

end

end RingHom
