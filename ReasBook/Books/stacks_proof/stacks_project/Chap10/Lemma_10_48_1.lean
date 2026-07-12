import Mathlib
import StacksProject_2024.Chap10.Lemma_10_48_4
import StacksProject_2024.Chap10.Lemma_10_48_6

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open Algebra.TensorProduct
open AlgebraicGeometry CommRingCat
open Topology

namespace Algebra

universe u

section

variable {k R S : Type u}
variable [Field k] [IsSepClosed k] [CommRing R] [Algebra k R] [CommRing S] [Algebra k S]

-- Proof sketch: first reinterpret connectedness of `Spec R` and `Spec S` as geometric
-- connectedness over the separably closed field `k` using Lemma `10.48.4`; then apply the
-- connected-components bijection induced by tensoring with a geometrically connected algebra from
-- Lemma `10.48.6`, and conclude that `Spec (R ⊗[k] S)` has a single connected component.
/-- Lemma 10.48.1 (Tag 037R): over a separably algebraically closed field `k`, if `Spec R` and
`Spec S` are connected, then `Spec (R ⊗[k] S)` is connected. This is stated in the canonical
prime-spectrum form. -/
@[stacks 037R]
theorem Lemma_10_48_1
    (hR : ConnectedSpace (PrimeSpectrum R))
    (hS : ConnectedSpace (PrimeSpectrum S)) :
    ConnectedSpace (PrimeSpectrum (R ⊗[k] S)) := by
  letI : ConnectedSpace (PrimeSpectrum R) := hR
  have hgeomS :
      geometrically (ConnectedSpace ·) (Spec.map (ofHom (algebraMap k S))) :=
    geometricallyConnected_iff_connectedSpace_primeSpectrum_of_isSepClosed.2 hS
  let e :
      ConnectedComponents (PrimeSpectrum (R ⊗[k] S)) →
        ConnectedComponents (PrimeSpectrum R) :=
    (PrimeSpectrum.continuous_comap (includeLeft : R →ₐ[k] R ⊗[k] S)).connectedComponentsMap
  have hbij : Function.Bijective e := (Lemma_10_48_6 hgeomS).2
  letI : Subsingleton (ConnectedComponents (PrimeSpectrum (R ⊗[k] S))) :=
    hbij.injective.subsingleton
  have hnonempty : Nonempty (PrimeSpectrum (R ⊗[k] S)) := by
    exact ConnectedComponents.nonempty_iff_nonempty.mp hbij.surjective.nonempty
  letI : Nonempty (PrimeSpectrum (R ⊗[k] S)) := hnonempty
  rw [connectedSpace_iff_connectedComponent]
  refine ⟨Classical.choice hnonempty, Set.eq_univ_of_forall fun y ↦ ?_⟩
  exact ConnectedComponents.coe_eq_coe'.mp <| Subsingleton.elim _ _

end

end Algebra
