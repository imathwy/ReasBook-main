import Mathlib
import Mathlib.Tactic.Recall

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Sheaf

universe u v

variable {C : Type u} [Category.{u} C]
variable {K : Type v} [Category.{v} K] [Small.{u} K]
variable (J : GrothendieckTopology C) (U : C)

/- Domain-style sampling for Lemma 18.3.2:
- primary domain: limits, colimits, and exact filtered colimits in the sheaf category
  `Sheaf J AddCommGrpCat.{u}`;
- inspected owner declarations:
  `CategoryTheory.sheafToPresheaf`,
  `Sheaf.createsLimitsOfShape`,
  `Sheaf.isColimitSheafifyCocone`,
  `AB5`;
- best owner abstraction: the canonical sheaf-category owners in mathlib, centered on
  `Sheaf J AddCommGrpCat.{u}` together with the forgetful functor
  `sheafToPresheaf J AddCommGrpCat.{u}`;
- primitive-vs-derived split:
  primitive data are only a Grothendieck topology `J`, an object `U : C`, a small diagram shape
  `K`, and, for the explicit colimit comparison companion, a diagram
  `F : K ⥤ Sheaf J AddCommGrpCat.{u}`;
  all sheafification, limit/colimit existence, sectionwise preservation, and exact
  filtered-colimit statements are derived owner API from the sheaf category and its forgetful
  functor, so this file should not keep parallel wrapper declarations;
- source/core/bridge triage:
  `source-facing`: abelian sheaves admit the stated limits and colimits, sections preserve limits,
  and colimits are computed by sheafifying presheaf colimits;
  `core/canonical`: the unconditional `HasWeakSheafify` / `HasSheafify` owners for abelian
  presheaves on a small site, the mathlib instances for `sheafToPresheaf`, the theorem
  `Sheaf.isColimitSheafifyCocone`, and the `AB5` owner on sheaves;
  `bridge/view`: the specialization of those owners to `AddCommGrpCat`.

There is no extra source-facing mathematical content beyond these owner statements, so the file is
best refined as direct canonical recall/use rather than as a family of local wrapper instances and
renamed duplicates.
-/

/- Lemma 18.3.2: the forgetful functor from abelian sheaves on a site to abelian presheaves
creates `K`-shaped limits for every small shape `K`. -/
#check (inferInstance : CreatesLimitsOfShape K (sheafToPresheaf J AddCommGrpCat.{u}))

/- Core/canonical owner recall behind the limit statement above. -/
recall Sheaf.createsLimitsOfShape

/- Taking sections over `U` is evaluation after forgetting to presheaves, so it preserves
`K`-shaped limits for every small shape `K`. -/
#check
  (inferInstance :
    PreservesLimitsOfShape K
      (sheafToPresheaf J AddCommGrpCat.{u} ⋙
        (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)))

/- The forgetful functor to abelian presheaves preserves finite products. -/
#check
  (inferInstance :
    PreservesFiniteProducts (sheafToPresheaf J AddCommGrpCat.{u}))

/- Abelian presheaves on a small site admit unconditional sheafification in `AddCommGrpCat`. -/
#check
  (show HasWeakSheafify J AddCommGrpCat.{u} from inferInstance)

/- Abelian sheaves on a site admit `K`-shaped colimits for every small shape `K`. -/
section

variable (F : K ⥤ Sheaf J AddCommGrpCat.{u})

#check
  (show HasColimitsOfShape K (Sheaf J AddCommGrpCat.{u}) from by
    let _ : HasWeakSheafify J AddCommGrpCat.{u} := inferInstance
    infer_instance)

/- The colimit of a diagram of abelian sheaves is obtained by sheafifying the colimit cocone of
the underlying abelian presheaf diagram. -/
recall Sheaf.isColimitSheafifyCocone

#check
  (isColimitSheafifyCocone
    (colimit.cocone (F ⋙ sheafToPresheaf J AddCommGrpCat.{u}))
    (colimit.isColimit (F ⋙ sheafToPresheaf J AddCommGrpCat.{u})))

end

/- Abelian presheaves on a small site admit unconditional sheafification in `AddCommGrpCat`. -/
#check
  (show HasSheafify J AddCommGrpCat.{u} from inferInstance)

/- Filtered colimits of abelian sheaves are exact. In canonical mathlib form, this says that
`Sheaf J AddCommGrpCat` satisfies `AB5`. -/
section

#check
  (show AB5 (Sheaf J AddCommGrpCat.{u}) from by
    let _ : HasSheafify J AddCommGrpCat.{u} := inferInstance
    infer_instance)

end
