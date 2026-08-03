module

public import Topology_Munkres_2000.Book.Definition_2_9
public import Topology_Munkres_2000.Book.Definition_2_10
import Mathlib.Logic.Equiv.Set

public section

universe u v

/-- Notation 2.3. For a bijection, the preimage of `B₀` under `f` is the image of
`B₀` under the inverse of `f`. -/
theorem preimage_eq_image_inverse {A : Type u} {B : Type v} (f : A → B)
    (hf : Function.Bijective f) (B₀ : Set B) :
    f ⁻¹' B₀ = (Equiv.ofBijective f hf).symm '' B₀ :=
  ((Equiv.ofBijective f hf).image_symm_eq_preimage B₀).symm
