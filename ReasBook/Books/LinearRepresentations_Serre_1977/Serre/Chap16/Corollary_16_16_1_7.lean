import LinearRepresentations_Serre_1977.Chap14.Corollary_14_14_4_3
import LinearRepresentations_Serre_1977.Chap16.Corollary_16_16_1_6

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open CategoryTheory
open scoped Representation

namespace Representation

section

-- Corollary 16-16.1-7 invokes Cartan injectivity (Cor. 16-16.1-6), so it inherits that result's
-- standing hypotheses: `k` is algebraically closed of characteristic `p`.
variable {p : ℕ}
variable {k : Type u} [Field k] [CharP k p] [IsAlgClosed k]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

/-
Domain-style sampling for Corollary 16-16.1-7:
* primary domain: the Cartan homomorphism `cartanHom k G : P₀[k](G) →+ R₀[k](G)` for finite
  projective `k[G]`-modules and the Chapter `14` classification of projective modules by their
  classes in `P₀[k](G)`;
* relevant owner declarations inspected in this domain:
  `cartanHom`,
  `cartanHom_projectiveClass_eq`,
  `cartanHom_injective`,
  `finiteProjectiveGroupAlgebraGrothendieckClass_eq_iff_nonempty_iso`;
* best owner abstraction: the canonical owner category `FiniteProjectiveGroupAlgebraModule k G`;
* source/core/bridge triage:
  source-facing: equality of the classes of `P.toFiniteRep` and `Q.toFiniteRep` in `R₀[k](G)`
    forces `P` and `Q` to be isomorphic;
  core/canonical: the owner map `cartanHom k G`;
  bridge/view: Chapter `14`'s owner-level classification theorem from equality in `P₀[k](G)` to
    an isomorphism in `FiniteProjectiveGroupAlgebraModule k G`.
* primitive data: the equality `hclass : [P.toFiniteRep]₀ = [Q.toFiniteRep]₀` in `R₀[k](G)`;
* derived API: equality of the projective classes via injectivity of `cartanHom k G`, then the
  resulting owner-level isomorphism.
The public surface should therefore use the canonical owner isomorphism `P ≅ Q`, not the
derived linear-equivalence bridge on underlying `k[G]`-modules.
-/

-- Proof sketch: equality of the classes of `P` and `Q` in `R_k(G)` means that their projective
-- classes in `P_k(G)` have the same image under the Cartan homomorphism. Corollary `16-16.1-6`
-- makes the Cartan homomorphism injective, so the projective classes coincide, and the Chapter 14
-- classification of projective modules by their Grothendieck classes then gives an isomorphism in
-- the canonical owner category `FiniteProjectiveGroupAlgebraModule k G`.
/-- Corollary 16-16.1-7: if two projective `k[G]`-modules have the same composition factors with
multiplicity, encoded here by equality of their classes in `R_k(G)`, then they are isomorphic as
objects of `FiniteProjectiveGroupAlgebraModule k G`. -/
theorem finiteProjectiveGroupAlgebraModule_iso_of_finiteRepGrothendieckClass_eq
    (P Q : FiniteProjectiveGroupAlgebraModule k G)
    (hclass : [P.toFiniteRep]₀ = [Q.toFiniteRep]₀) :
    Nonempty (P ≅ Q) := by
  exact
    (finiteProjectiveGroupAlgebraGrothendieckClass_eq_iff_nonempty_iso P Q).mp <|
      cartanHom_injective <| by
        simpa [cartanHom_projectiveClass_eq] using hclass

end

end Representation
