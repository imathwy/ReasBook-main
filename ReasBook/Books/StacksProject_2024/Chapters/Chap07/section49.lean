import Mathlib
import Mathlib.CategoryTheory.Sites.LocallySurjective
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_7_49_1 (from Chap07) -/
open CategoryTheory Opposite
open scoped CategoryTheory.GrothendieckTopology.PlusNotation

universe v u

namespace CategoryTheory.GrothendieckTopology

section

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable {ℱ : Cᵒᵖ ⥤ Type (max u v)}

/- Domain-style sampling for Lemma 7.49.1:
- primary domain: the plus construction for set-valued presheaves on a Grothendieck site;
- sampled owner API:
  `GrothendieckTopology.plusObj`,
  `GrothendieckTopology.toPlus`,
  `GrothendieckTopology.toPlusNatTrans`,
  `(J.plusFunctor (Type (max u v))).PreservesMonomorphisms`,
  `Presheaf.isLocallySurjective_toPlus`;
- best owner abstraction: `J.plusObj` with its canonical map `J.toPlus`, functorially packaged by
  `J.plusFunctor` and `J.toPlusNatTrans`;
- source/core/bridge triage:
  `source-facing`: the textbook lemma enumerates the canonical output `ℱ⁺`, the map
    `ℱ ⟶ ℱ⁺`, its functoriality, preservation of monomorphisms, and local surjectivity;
  `core/canonical`: the owner declarations listed above on `GrothendieckTopology` and
    `Presheaf`;
  `bridge/view`: the earlier chapter items Lemma 7.10.3, Lemma 7.10.4, and Lemma 7.10.8 are
    already source-facing recalls of these same owners.

Primitive data are only `J` and the presheaf `ℱ`: for set-valued presheaves, `Type (max u v)`
already supplies the limits and colimits used internally by the plus construction. The map
`J.toPlus ℱ`, its naturality, the monomorphism-preservation statement, and its local surjectivity
are all derived from that owner abstraction, so this file should stay at the direct recall/use
layer instead of introducing a parallel local wrapper.
-/

/- Lemma 7.49.1 (1): the plus construction sends a presheaf `ℱ` on `(C, J)` to the presheaf
`ℱ⁺`. -/
#check ℱ⁺

/- Lemma 7.49.1 (2): the plus construction comes with the canonical map
`J.toPlus ℱ : ℱ ⟶ ℱ⁺`. -/
#check J.toPlus ℱ

/- Lemma 7.49.1 (3): the assignment `ℱ ↦ (J.toPlus ℱ : ℱ ⟶ ℱ⁺)` is functorial, i.e. it
is the canonical natural transformation from the identity functor to the plus functor. -/
#check J.toPlusNatTrans (Type (max u v))

/- Lemma 7.49.1 (4): the plus construction sends monomorphisms of presheaves of sets to
monomorphisms. The owner-level canonical form is that the plus functor preserves monomorphisms. -/
#check
  (inferInstance : (J.plusFunctor (Type (max u v))).PreservesMonomorphisms)

/- Lemma 7.49.1 (5): every section of `ℱ⁺` is locally induced from `ℱ`; canonically,
this is the local surjectivity of `J.toPlus ℱ`. -/
recall Presheaf.isLocallySurjective_toPlus :
  Presheaf.IsLocallySurjective J (J.toPlus ℱ)

end

end CategoryTheory.GrothendieckTopology

/-! ### Definition_7_49_2 (from Chap07) -/
open CategoryTheory Opposite

universe w v u

namespace CategoryTheory.Presheaf

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C) (F : Cᵒᵖ ⥤ Type w)

/- Domain-style sampling for Definition 7.49.2:
- primary domain: separated presheaves of sets on a Grothendieck site;
- sampled canonical declarations:
  `Presieve.IsSeparatedFor`,
  `Presieve.IsSeparated`,
  `Presieve.IsSheaf.isSeparated`,
  `Presheaf.IsSeparated`;
- best owner abstraction: `Presieve.IsSeparated J F`, already adopted earlier in
  Definition 7.10.9;
- primitive data: only the site `(C, J)` and the set-valued presheaf `F`;
- derived API: coverwise injectivity criteria and the sheaf-to-separated implication.

Source/core/bridge triage:
- `core/canonical`: `Presieve.IsSeparated J F`;
- `bridge/view`: concrete coverwise injectivity reformulations and consequences such as the plus
  construction lemmas.

This numbered item introduces no new source-facing data beyond the canonical separatedness
predicate itself, so keeping a second chapter-local wrapper would only duplicate the owner already
used upstream in Definition 7.10.9.
-/

/- Definition 7.49.2: for a category `C` with Grothendieck topology `J`, the chapter-facing
owner notion that a set-valued presheaf `F` is separated is `CategoryTheory.Presieve.IsSeparated
J F`. This is already the canonical declaration reused earlier in Definition 7.10.9. -/
recall Presieve.IsSeparated

/- Source-facing specialization: separatedness of `F` on `(C, J)` is expressed directly as the
proposition `Presieve.IsSeparated J F`. -/
#check (Presieve.IsSeparated J F : Prop)

end CategoryTheory.Presheaf

/-! ### Theorem_7_49_3 (from Chap07) -/
/- Domain-style sampling for Theorem 7.49.3:
- primary domain: the plus construction and sheafification for set-valued presheaves on a
  Grothendieck site;
- sampled owner API:
  `plusObj_isSeparated`,
  `plusObj_isSheaf_of_isSeparated`,
  `toPlus_injective_of_isSeparated`,
  `GrothendieckTopology.isIso_toPlus_of_isSheaf`,
  `GrothendieckTopology.Plus.isSheaf_plus_plus`;
- source-facing layer: the textbook assertions about `L F`, `F ⟶ L F`, and `L (L F)`;
- core/canonical owner: the plus-construction/sheafification API on `GrothendieckTopology`;
- bridge/view: the monomorphism reformulation `toPlus_mono_of_isSeparated`, obtained from the
  source-facing objectwise injectivity statement through `Presheaf.mono_iff_injective`.

Primitive data are only the site `J` and the presheaf `F`. The map `J.toPlus F`, the iterated plus
object, and sheafification are canonical constructions of the Grothendieck-topology owner, so this
file should recall those owners directly rather than keep parallel restatements.
-/

open CategoryTheory Opposite
open GrothendieckTopology
open scoped CategoryTheory.GrothendieckTopology.PlusNotation

universe u v

section

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C)
variable (F : Cᵒᵖ ⥤ Type (max u v))

/- Theorem 7.49.3 (1): the plus construction `L F` is separated. This is the same statement as
Theorem 7.10.10 (1), already recorded in the chapter API. -/
recall plusObj_isSeparated :
  Presieve.IsSeparated J F⁺

/- Theorem 7.49.3 (2), first assertion: if `F` is separated, then `L F` is a sheaf. This is the
same statement as Theorem 7.10.10 (2), first assertion. -/
recall plusObj_isSheaf_of_isSeparated (hF : Presieve.IsSeparated J F) :
  Presheaf.IsSheaf J F⁺

/- Theorem 7.49.3 (2), second assertion: if `F` is separated, then the canonical map
`F ⟶ L F` is injective on sections over every object. This is the same statement as
Theorem 7.10.10 (2), second assertion. -/
recall toPlus_injective_of_isSeparated (hF : Presieve.IsSeparated J F) :
  ∀ U : C, Function.Injective ((J.toPlus F).app (op U))

/- Companion bridge for Theorem 7.49.3 (2), second assertion: via Definition 7.3.1 and
Lemma 7.3.2, the same map is a monomorphism. -/
recall toPlus_mono_of_isSeparated (hF : Presieve.IsSeparated J F) :
  Mono (J.toPlus F)

/- Theorem 7.49.3 (3): if `F` is a sheaf, then the canonical map `F ⟶ L F` is an isomorphism.
This is the same statement as Theorem 7.10.10 (3), now exposed by direct recall of the canonical
owner theorem. -/
recall isIso_toPlus_of_isSheaf

/- Theorem 7.49.3 (4): the iterated plus construction `L (L F)` is a sheaf. This is the same
statement as Theorem 7.10.10 (4), now exposed by direct recall of the canonical owner theorem. -/
recall Plus.isSheaf_plus_plus

/- Companion reformulation of Theorem 7.49.3 (4): since `J.sheafify F = F⁺⁺`,
the sheafification `J.sheafify F` is a sheaf. The canonical library-facing companion is the
theorem `sheafify_isSheaf`. -/
recall sheafify_isSheaf

end

/-! ### Definition_7_49_4 (from Chap07) -/
open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable (P : Cᵒᵖ ⥤ Type (max u v))

/- Domain-style sampling for Definition 7.49.4:
- primary domain: sheafification of set-valued presheaves on a Grothendieck site;
- sampled owner API:
  `presheafToSheaf`,
  `GrothendieckTopology.sheafify`,
  `GrothendieckTopology.toSheafify`,
  `sheafificationAdjunction`;
- source-facing layer: the repeated textbook item defining the associated sheaf `P^#` of a
  presheaf `P`;
- core/canonical owner: `presheafToSheaf J (Type (max u v))`;
- bridge/view: the underlying presheaf `J.sheafify P` and the unit `J.toSheafify P`, already
  recorded in `Definition_7_10_11`.

Primitive data are only the site `(C, J)` and the presheaf `P`. The associated sheaf, its
underlying presheaf, and its unit map are derived from the owner sheafification functor, so this
repeated item should expose only that owner directly. The derived bridge/view API is reused from
the earlier chapter owner file rather than recopied here.
-/

/- Definition 7.49.4: the associated sheaf `P^#` of a set-valued presheaf `P` on `(C, J)` is
again the bundled sheaf obtained by applying the canonical sheafification functor
`presheafToSheaf J (Type (max u v))` to `P`. This repeats Definition 7.10.11, so this file keeps
only the source-facing recall of that owner and leaves the companion views upstream. -/
recall presheafToSheaf

/- Source-facing specialization: `P^#` is the bundled sheaf obtained by sheafifying `P`. -/
#check (presheafToSheaf J (Type (max u v))).obj P

/-! ### Proposition_7_49_5 (from Chap07) -/
open CategoryTheory Opposite

universe u v

section

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C) [HasWeakSheafify J (Type (max u v))]
variable (F : Cᵒᵖ ⥤ Type (max u v)) (𝒢 : Sheaf J (Type (max u v)))

/- Domain-style sampling for Proposition 7.49.5:
- primary domain: sheafification on a site and its adjunction with the inclusion of sheaves into
  presheaves;
- sampled owner API:
  `presheafToSheaf`,
  `sheafificationAdjunction`,
  `CategoryTheory.toSheafify`,
  `CategoryTheory.sheafifyLift`;
- source-facing layer: the universal property of the sheafification unit `J.toSheafify F`;
- core/canonical owner: the adjunction `sheafificationAdjunction J (Type (max u v))`;
- bridge/view: the specialized Hom-set equivalence for the given presheaf `F` and sheaf `𝒢`.

Primitive data are the site `(C, J)`, the weak sheafification instance, the presheaf `F`, and the
target sheaf `𝒢`. The universal morphism and its uniqueness are derived API of the owner
adjunction, so this item should expose the specialized `homEquiv` directly rather than introduce a
parallel local wrapper for the same bijection.
-/

/- Proposition 7.49.5: the sheafification unit `J.toSheafify F : F ⟶ J.sheafify F` is universal
for maps from `F` to sheaves of sets; equivalently, precomposition with `J.toSheafify F`
induces a bijection from morphisms out of the sheafification to morphisms from `F`.
The canonical library-facing form is the sheafification adjunction hom-equivalence below. -/
recall sheafificationAdjunction

#check (((sheafificationAdjunction J (Type (max u v))).homEquiv F 𝒢) :
  ((presheafToSheaf J _).obj F ⟶ 𝒢) ≃
    (F ⟶ (sheafToPresheaf J _).obj 𝒢))

end
