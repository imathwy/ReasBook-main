import Mathlib
import stacks_project.Chap10.Definition_10_153_1
import stacks_project.Chap10.Lemma_10_106_8

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
variable (R : I → Type u) [∀ i, CommRing (R i)]
variable (φ : ∀ i j, i ≤ j → R i →+* R j) [DirectedSystem R (φ · · ·)]
variable [∀ i j hij, IsLocalHom (φ i j hij)]

local notation "R∞" => Ring.DirectLimit R (fun i j h ↦ φ i j h)

-- Proof sketch: reuse the upstream direct-limit local-ring instance from Lemma `10.106.8` to put
-- a local-ring structure on `R∞`. For Hensel lifting, descend a monic polynomial over `R∞` and a
-- simple root in the residue field to a sufficiently large stage, apply the henselian property
-- there, and map the lifted root forward to the colimit.
/-- Lemma 10.154.8 (1): a filtered colimit of henselian local rings along local homomorphisms is
henselian. -/
instance directedSystem_directLimit_henselianLocalRing
    [∀ i, HenselianLocalRing (R i)] : HenselianLocalRing R∞ := by
  refine { toIsLocalRing := inferInstance, is_henselian := ?_ }
  sorry

-- Proof sketch: identify the residue field of `R∞` with the filtered colimit of the stage residue
-- fields along the induced maps; then every separable polynomial over the colimit residue field is
-- defined over some stage residue field, where it already splits because that field is separably
-- algebraically closed. Together with part (1), this gives the canonical Chapter 10 owner
-- `StrictHenselianLocalRing`.
/-- Lemma 10.154.8 (2): if the stage local rings are strictly henselian, then the filtered colimit
is strictly henselian; equivalently, its residue field is separably algebraically closed. -/
instance directedSystem_directLimit_strictHenselianLocalRing
    [∀ i, StrictHenselianLocalRing (R i)] : StrictHenselianLocalRing R∞ := by
  refine { toHenselianLocalRing := inferInstance, toIsSepClosed := ?_ }
  sorry

end
