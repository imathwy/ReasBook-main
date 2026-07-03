import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_18_3_1 (from Chap18) -/
open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/- Domain-style sampling for Lemma 18.3.1:
- primary domain: abelian sheaves on a Grothendieck site, together with the owner local
  injective/surjective criteria for sheaf morphisms and the kernel/cokernel comparison maps for
  sheafification and forgetting to presheaves;
- sampled owner API:
  `PreservesKernel.iso`,
  `PreservesCokernel.iso`,
  `Sheaf.isLocallyInjective_iff_injective`,
  `Sheaf.isLocallySurjective_iff_epi'`;
- best owner abstraction: the abelian sheaf category `Sheaf J AddCommGrpCat.{max u v}` together
  with the forgetful functor `sheafToPresheaf J AddCommGrpCat.{max u v}` and the sheafification
  functor `presheafToSheaf J AddCommGrpCat.{max u v}`;
- source/core/bridge triage:
  `source-facing`: the sectionwise injectivity criterion, the sectionwise local exactness criterion,
  and the cokernel/sheafification comparison;
  `core/canonical`: the preserved-kernel comparison and the owner local
  injective/surjective criteria for sheaf morphisms;
  `bridge/view`: the reformulation from objects of `Cᵒᵖ` to objects of `C` via `op`.

Primitive data are only a morphism of abelian sheaves or a short complex of abelian sheaves. The
kernel and local surjectivity owners already live upstream, so this file should not keep parallel
public aliases for them. The source-facing bridge statements belong under the owner namespaces
`Sheaf` and `ShortComplex`, and the genuinely new cokernel comparison belongs under `Sheaf`.
-/

/- Lemma 18.3.1 (1): the category of abelian sheaves on a site is an abelian category. -/
#check (inferInstance : Abelian (Sheaf J AddCommGrpCat.{max u v}))

/- Lemma 18.3.1 (2): the underlying abelian presheaf of the kernel sheaf of `φ` is the kernel of
the underlying morphism of abelian presheaves. This is exactly the preserved-kernel comparison
`PreservesKernel.iso` for `sheafToPresheaf J AddCommGrpCat.{max u v}`. -/
#check PreservesKernel.iso (sheafToPresheaf J AddCommGrpCat.{max u v})

namespace Sheaf

/-- Lemma 18.3.1 (3): a morphism of abelian sheaves is injective in the abelian-category sense if
and only if it is injective on every section of the underlying abelian presheaf. -/
-- Proof sketch: monomorphisms in the sheaf category are detected by the fully faithful inclusion
-- into presheaves, and monomorphisms in `AddCommGrpCat` are exactly injective group homomorphisms.
theorem mono_iff_app_injective
    {F G : Sheaf J AddCommGrpCat.{max u v}} (φ : F ⟶ G) :
    Mono φ ↔
      ∀ U : C, Function.Injective (φ.hom.app (op U)) := sorry

/-- Lemma 18.3.1 (4): injectivity on every section is equivalent to local injectivity as a
morphism of sheaves. -/
-- Proof sketch: rewrite `Sheaf.IsLocallyInjective φ` using the standard equivalence with
-- componentwise injectivity, then pass between objects of `Cᵒᵖ` and objects of `C`.
theorem isLocallyInjective_iff_app_injective
    {F G : Sheaf J AddCommGrpCat.{max u v}} (φ : F ⟶ G) :
    Sheaf.IsLocallyInjective φ ↔
      ∀ U : C, Function.Injective (φ.hom.app (op U)) := sorry

/-- Lemma 18.3.1 (5): the cokernel sheaf of `φ` is the sheafification of the cokernel of the
underlying abelian presheaf morphism. -/
noncomputable abbrev cokernelSheafificationIso
    {F G : Sheaf J AddCommGrpCat.{max u v}} (φ : F ⟶ G) :
    cokernel φ ≅
      (presheafToSheaf J AddCommGrpCat.{max u v}).obj
        (cokernel ((sheafToPresheaf J AddCommGrpCat.{max u v}).map φ)) :=
  (cokernel.mapIso φ
      ((presheafToSheaf J AddCommGrpCat.{max u v}).map
        ((sheafToPresheaf J AddCommGrpCat.{max u v}).map φ))
      (sheafificationIso F)
      (sheafificationIso G)
      (by
        simpa using
          (sheafificationNatIso J AddCommGrpCat.{max u v}).hom.naturality φ)) ≪≫
    (PreservesCokernel.iso (presheafToSheaf J AddCommGrpCat.{max u v})
      ((sheafToPresheaf J AddCommGrpCat.{max u v}).map φ)).symm

end Sheaf

/- Lemma 18.3.1 (6): a morphism of abelian sheaves is surjective in the abelian-category sense if
and only if it is locally surjective as a morphism of sheaves. This is the canonical owner theorem
`Sheaf.isLocallySurjective_iff_epi'`, specialized to abelian sheaves. -/
recall Sheaf.isLocallySurjective_iff_epi'

/-- Lemma 18.3.1 (7): a short complex of abelian sheaves is exact at the middle term exactly when
every section killed by the right map becomes locally a section in the image of the left map. -/
-- Proof sketch: exactness in an abelian category is equivalent to the canonical map to the kernel
-- being epi; then translate epi to local surjectivity in the sheaf category and unpack the image
-- sieve condition objectwise over coverings.
theorem ShortComplex.exact_iff_locally_surjective_sections
    (S : ShortComplex (Sheaf J AddCommGrpCat.{max u v})) :
    let F₁ := S.X₁.obj
    let F₂ := S.X₂.obj
    let f := S.f.hom
    let g := S.g.hom
    S.Exact ↔
      ∀ (U : C) (s : F₂.obj (Opposite.op U)), g.app (Opposite.op U) s = 0 →
        ∃ T : J.Cover U, ∀ I : T.Arrow,
          ∃ t : F₁.obj (Opposite.op I.Y),
            f.app (Opposite.op I.Y) t = F₂.map I.f.op s := sorry

end CategoryTheory

/-! ### Lemma_18_3_2 (from Chap18) -/
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
