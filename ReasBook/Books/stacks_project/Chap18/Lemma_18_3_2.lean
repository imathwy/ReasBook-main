import Mathlib
import Mathlib.Tactic.Recall

open CategoryTheory CategoryTheory.Limits Opposite

universe u

variable {C : Type u} [Category.{u} C]
variable {K : Type u} [Category.{u} K]
variable (J : GrothendieckTopology C) (U : C)

/- Domain-style sampling for Lemma 18.3.2:
- primary domain: limits, colimits, and exact filtered colimits in the sheaf category
  `Sheaf J AddCommGrpCat.{u}`;
- inspected owner declarations:
  `CategoryTheory.sheafToPresheaf`,
  `Sheaf.isColimitSheafifyCocone`,
  `Sheaf.hasExactColimitsOfShape`;
- best owner abstraction: the canonical sheaf-category owners in mathlib, centered on
  `Sheaf J AddCommGrpCat.{u}` together with the forgetful functor
  `sheafToPresheaf J AddCommGrpCat.{u}`;
- primitive-vs-derived split:
  primitive data are only a Grothendieck topology `J`, a shape category `K`, and a diagram
  `F : K ⥤ Sheaf J AddCommGrpCat.{u}`;
  all limit/colimit existence, sectionwise preservation, and exact filtered-colimit statements are
  derived owner API from the sheaf category and its forgetful functor, so this file should not
  keep parallel wrapper declarations;
- source/core/bridge triage:
  `source-facing`: abelian sheaves admit the stated limits and colimits, sections preserve limits,
  and colimits are computed by sheafifying presheaf colimits;
  `core/canonical`: the mathlib instances for `sheafToPresheaf`, the theorem
  `Sheaf.isColimitSheafifyCocone`, and the Grothendieck-axiom exact-colimit instance on sheaves;
  `bridge/view`: the specialization of those owners to `AddCommGrpCat`.

There is no extra source-facing mathematical content beyond these owner statements, so the file is
best refined as direct canonical recall/use rather than as a family of local wrapper instances and
renamed duplicates.
-/

/- Lemma 18.3.2: the forgetful functor from abelian sheaves on a site to abelian presheaves
creates `K`-shaped limits. -/
#check
  (inferInstance :
    CreatesLimitsOfShape K (sheafToPresheaf J AddCommGrpCat.{u}))

/- Taking sections over `U` is evaluation after forgetting to presheaves, so it preserves
`K`-shaped limits. -/
#check
  (inferInstance :
    PreservesLimitsOfShape K
      (sheafToPresheaf J AddCommGrpCat.{u} ⋙
        (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)))

/- The forgetful functor to abelian presheaves preserves finite products. -/
#check
  (inferInstance :
    PreservesFiniteProducts (sheafToPresheaf J AddCommGrpCat.{u}))

/- Abelian sheaves on a site admit `K`-shaped colimits as soon as abelian presheaves can be
sheafified. -/
section

variable [HasWeakSheafify J AddCommGrpCat.{u}]

#check
  (inferInstance :
    HasColimitsOfShape K (Sheaf J AddCommGrpCat.{u}))

/- The colimit of a diagram of abelian sheaves is obtained by sheafifying the colimit cocone of
the underlying abelian presheaf diagram. -/
recall Sheaf.isColimitSheafifyCocone

#check
  ((fun F : K ⥤ Sheaf J AddCommGrpCat.{u} ↦
      Sheaf.isColimitSheafifyCocone
        (colimit.cocone (F ⋙ sheafToPresheaf J AddCommGrpCat.{u}))
        (colimit.isColimit (F ⋙ sheafToPresheaf J AddCommGrpCat.{u}))) :
    ∀ F : K ⥤ Sheaf J AddCommGrpCat.{u},
      IsColimit
        (Sheaf.sheafifyCocone (colimit.cocone (F ⋙ sheafToPresheaf J AddCommGrpCat.{u}))))

end

/- Filtered colimits of abelian sheaves are exact. -/
section

variable [HasSheafify J AddCommGrpCat.{u}] [IsFiltered K]

#check
  (inferInstance :
    HasExactColimitsOfShape K (Sheaf J AddCommGrpCat.{u}))

end
