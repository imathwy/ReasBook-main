import StacksProject_2024.stacks_project.Chap21.Lemma_21_10_3

open CategoryTheory Limits

noncomputable section

universe u

namespace CategoryTheory

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [HasProducts AddCommGrpCat]
variable [HasWeakSheafify J AddCommGrpCat]
variable [HasSheafify J AddCommGrpCat]
variable [EnoughInjectives (Sheaf J AddCommGrpCat)]
variable [IsGrothendieckAbelian (Sheaf J AddCommGrpCat)]

variable {U : C} {ι : Type u}
variable [HasFiniteProducts (Over U)]

/- Domain-style sampling for Lemma 21.10.4:
- primary domain: the degree-one Čech-to-site cohomology comparison for abelian sheaves on a site,
  viewed through the torsor interpretation of `H¹`;
- sampled owner declarations:
  `IsCechCohomologyToSiteCohomologySucc`,
  `cechCohomologyOnSheaves`,
  `Sheaf.H'`,
  `abelianSheafTorsor_isoClasses_equiv_H1`;
- best owner abstraction:
  `source-facing`: injectivity of the degree-one comparison map for a fixed covering family
    `V : ι → Over U`;
  `core/canonical`: `cechCohomologyOnSheaves`, `Sheaf.H'`, and the degree-one comparison
    predicate `IsCechCohomologyToSiteCohomologySucc J U V 0 G f`;
  `bridge/view`: a morphism `f : Čech H¹(V, G) ⟶ H¹(U, G)` together with
    `IsCechCohomologyToSiteCohomologySucc J U V 0 G f`, and Lemma `21.4.3`, which identifies
    `H¹(U, G)` with torsor isomorphism classes and explains the source-faithful
    site-cohomology interpretation.
- primitive data: the covering family `V`, the covering proof `hV`, and the abelian sheaf `G`;
- derived API: injectivity of any degree-one comparison morphism
  `f : Čech H¹(V, G) ⟶ H¹(U, G)` satisfying
  `IsCechCohomologyToSiteCohomologySucc J U V 0 G f`, with the torsor description used only as
  bridge/view data.
-/

-- Proof sketch: use Lemma `21.4.3` on the slice site `(C / U, J.over U)` to identify the target
-- `H¹(U, G)` with torsor classes under `G.over U`. A Čech `1`-cocycle on `V` glues the trivial
-- torsor on the members of `V`, so its image in `H¹(U, G)` is represented by a torsor trivial on
-- the covering. Equality of the induced torsor classes then forces equality of the original Čech
-- classes, yielding injectivity for any degree-one comparison map of Lemma `21.10.3`.
/-- Lemma 21.10.4: for a covering family `V : ι → Over U`, any degree-one comparison morphism
`f : Čech H¹(V, G) ⟶ H¹(U, G)` satisfying
`IsCechCohomologyToSiteCohomologySucc J U V 0 G f` is injective. -/
@[stacks 0A6G]
theorem cechCohomologyToSiteCohomology_injective_degree_one
    (V : ι → Over U) (hV : (J.over U).CoversTop V)
    (G : Sheaf J AddCommGrpCat)
    (f : ((cechCohomologyOnSheaves J V 1).obj G) ⟶ G.H' 1 U)
    (hf : IsCechCohomologyToSiteCohomologySucc J U V 0 G f) :
    Function.Injective f := by
  sorry

/-- Companion API: a degree-one Čech-to-site comparison morphism is injective once its covering
family covers `U`. -/
theorem IsCechCohomologyToSiteCohomologySucc.injective_degree_one
    {V : ι → Over U} {G : Sheaf J AddCommGrpCat}
    {f : ((cechCohomologyOnSheaves J V 1).obj G) ⟶ G.H' 1 U}
    (hf : IsCechCohomologyToSiteCohomologySucc J U V 0 G f)
    (hV : (J.over U).CoversTop V) :
    Function.Injective f := by
  exact cechCohomologyToSiteCohomology_injective_degree_one V hV G f hf

/-- Companion API: a degree-one Čech-to-site comparison morphism is a monomorphism once its
covering family covers `U`. -/
theorem IsCechCohomologyToSiteCohomologySucc.mono_degree_one
    {V : ι → Over U} {G : Sheaf J AddCommGrpCat}
    {f : ((cechCohomologyOnSheaves J V 1).obj G) ⟶ G.H' 1 U}
    (hf : IsCechCohomologyToSiteCohomologySucc J U V 0 G f)
    (hV : (J.over U).CoversTop V) :
    Mono f := by
  exact (AddCommGrpCat.mono_iff_injective f).2 (hf.injective_degree_one hV)

/-- Canonical instance companion: a degree-one Čech-to-site comparison morphism is a monomorphism
whenever its covering family covers `U`. -/
instance IsCechCohomologyToSiteCohomologySucc.instMonoDegreeOne
    {V : ι → Over U} {G : Sheaf J AddCommGrpCat}
    {f : ((cechCohomologyOnSheaves J V 1).obj G) ⟶ G.H' 1 U}
    (hf : IsCechCohomologyToSiteCohomologySucc J U V 0 G f)
    (hV : (J.over U).CoversTop V) :
    Mono f :=
  hf.mono_degree_one hV

end CategoryTheory
