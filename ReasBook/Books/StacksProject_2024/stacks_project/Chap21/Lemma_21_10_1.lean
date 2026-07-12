import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import Mathlib.CategoryTheory.Sites.Sheafification

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasSheafify J AddCommGrpCat.{max u v}]

/- Domain-style sampling for Lemma 21.10.1:
- primary domain: abelian sheaves on a site, the sheafification adjunction, and preservation of
  injective objects by the forgetful functor to abelian presheaves;
- sampled owner declarations:
  `sheafificationAdjunction`,
  `presheafToSheaf`,
  `sheafToPresheaf`,
  `preservesInjectiveObjects_of_exact_leftAdjoint`;
- best owner abstraction: the canonical owner data are the adjunction
  `presheafToSheaf J AddCommGrpCat ⊣ sheafToPresheaf J AddCommGrpCat` and the Chapter 12 bridge
  `preservesInjectiveObjects_of_exact_leftAdjoint`; this file should expose only the source-facing
  consequence for one injective abelian sheaf, not a parallel local preservation API;
- primitive data: the abelian sheaf `F` and the assumption `Injective F`;
- derived API: exactness of abelian sheafification and preservation of injectives by the right
  adjoint. -/

/-- Helper for Lemma 21.10.1: forgetting an injective abelian sheaf to its underlying abelian
presheaf preserves injectivity because sheafification is an exact left adjoint. -/
private theorem injectiveUnderlyingAbelianPresheaf
    {F : Sheaf J AddCommGrpCat.{max u v}} (hF : Injective F) :
    Injective ((sheafToPresheaf J AddCommGrpCat.{max u v}).obj F) := by
  let G := sheafToPresheaf J AddCommGrpCat.{max u v}
  let L := presheafToSheaf J AddCommGrpCat.{max u v}
  let _ : L.PreservesMonomorphisms := by
    infer_instance
  let _ : G.PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      (sheafificationAdjunction J AddCommGrpCat.{max u v})
  -- Push injectivity through the left-exact sheafification adjunction once.
  simpa [G] using G.injective_obj_of_injective hF

/-- Lemma 21.10.1: an injective abelian sheaf on a site is injective as an abelian presheaf. -/
@[stacks 03F6]
theorem injective_underlying_abelian_presheaf
    (F : Sheaf J AddCommGrpCat.{max u v}) (hF : Injective F) :
    Injective ((sheafToPresheaf J AddCommGrpCat.{max u v}).obj F) := by
  -- Specialize the helper to the chosen injective sheaf.
  exact injectiveUnderlyingAbelianPresheaf hF

end CategoryTheory
