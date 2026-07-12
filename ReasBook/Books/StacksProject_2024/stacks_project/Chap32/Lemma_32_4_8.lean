import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced
-- `AlgebraicGeometry.exists_mem_of_isClosed_of_nonempty` in
-- `Mathlib.AlgebraicGeometry.AffineTransitionLimit`; the statement below is the directed
-- inverse-system specialization matching the setup fixed in Situation `32.4.5`.

section

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
variable (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
variable [∀ i, CompactSpace ↥(D.obj i)]
variable [∀ i, QuasiSeparatedSpace ↥(D.obj i)]
variable [∀ {i i' : I} (hii' : i ≤ i'), IsAffineHom (D.map (homOfLE hii'))]

/-- Lemma 32.4.8: in Situation `32.4.5`, if each stage `S_i = D.obj i` is equipped with a
nonempty closed subset `Z_i` compatible with the transition morphisms
`f_{i',i} = D.map (homOfLE hii')`, then there exists a point of the limit scheme `S = c.pt`
whose image in every stage lies in `Z_i`. -/
@[stacks 01Z3]
theorem exists_limitPoint_mem_closed_of_compatible
    (Z : ∀ i : I, Set ↥(D.obj i))
    (hZ_closed : ∀ i, IsClosed (Z i))
    (hZ_nonempty : ∀ i, (Z i).Nonempty)
    (hZ_compat : ∀ {i i' : I} (hii' : i ≤ i'),
      Set.MapsTo (D.map (homOfLE hii')) (Z i') (Z i)) :
    ∃ s : c.pt, ∀ i, (c.π.app i) s ∈ Z i := sorry

end

end AlgebraicGeometry
