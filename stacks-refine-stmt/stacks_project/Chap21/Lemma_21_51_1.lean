import Mathlib
import Mathlib.CategoryTheory.Limits.ExactFunctor
import stacks_project.Chap07.Lemma_7_40_1
import stacks_project.Chap21.Definition_21_4_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open CategoryTheory.Sheaf

noncomputable section

universe u v

namespace CategoryTheory

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

-- Proof sketch: exactness at the middle term of a short exact sequence of abelian sheaves is
-- equivalent to local surjectivity on sections. For a weakly contractible object `U`, local
-- surjectivity upgrades to actual surjectivity on sections over `U`, so evaluating at `U`
-- preserves exact short complexes.
/-- Lemma 21.51.1 (1): if `U` is weakly contractible in the site `(\mathcal C, J)`, then the
sections functor `\mathcal F \mapsto \mathcal F(U)` on abelian sheaves is exact. -/
theorem weaklyContractible_sectionsFunctor_exact
    (U : C) [J.IsWeaklyContractible U] :
    exactFunctor (Sheaf J AddCommGrpCat.{v}) AddCommGrpCat.{v}
      ((sheafSections J AddCommGrpCat.{v}).obj (op U)) := sorry

-- Proof sketch: clause `(1)` makes `\Gamma(U,-)` an exact functor on the abelian category of
-- abelian sheaves, so Lemma `13.16.9` identifies its higher right derived functors with zero.
-- The degree-`p` cohomology object `H^p(U, \mathcal F)` is computed by those higher derived
-- functors.
/-- Lemma 21.51.1 (2): if `U` is weakly contractible, then every higher cohomology group
`H^p(U, \mathcal F)` of an abelian sheaf `\mathcal F` vanishes for `p > 0`. -/
theorem weaklyContractible_higherCohomology_isZero
    [HasSheafify J AddCommGrpCat.{v}]
    [HasExt (Sheaf J AddCommGrpCat.{v})]
    (U : C) [J.IsWeaklyContractible U]
    (F : Sheaf J AddCommGrpCat.{v}) (p : ℕ) (hp : 0 < p) :
    IsZero (F.H' p U) := sorry

-- Proof sketch: the structure morphism from the underlying sheaf of sets of a `\mathcal G`-torsor
-- to the terminal sheaf is locally surjective by local nonemptiness. Weak contractibility of `U`
-- upgrades this local surjectivity to a genuine section over `U`.
/-- Lemma 21.51.1 (3): if `U` is weakly contractible, then every `\mathcal G`-torsor on the site
has a section over `U`. -/
theorem weaklyContractible_torsor_sections_nonempty
    (U : C) [J.IsWeaklyContractible U]
    (G : Sheaf J GrpCat.{v}) (P : Torsor G) :
    Nonempty (P.Sections (op U)) := sorry

end

end CategoryTheory
