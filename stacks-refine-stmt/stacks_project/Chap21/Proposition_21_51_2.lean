import Mathlib
import stacks_project.Chap13.Remark_13_34_5
import stacks_project.Chap07.Lemma_7_40_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open Opposite
open DerivedCategory

noncomputable section

universe w v u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

/-- The abelian category `\mathrm{Mod}(\mathcal O)` of sheaves of modules over the sheaf of rings
`\mathcal O` on a site. -/
abbrev siteModuleCat {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (𝒪 : Sheaf J RingCat.{max u v}) :=
  SheafOfModules 𝒪

/-- The sections functor `\Gamma(U,-)` on sheaves of `\mathcal O`-modules over a fixed object
`U` of the site. -/
abbrev siteModuleSectionsFunctor {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (𝒪 : Sheaf J RingCat.{max u v}) (U : C) :
    siteModuleCat 𝒪 ⥤ AddCommGrpCat.{max u v} :=
  SheafOfModules.toSheaf 𝒪 ⋙
    sheafToPresheaf J AddCommGrpCat.{max u v} ⋙
      (evaluation Cᵒᵖ AddCommGrpCat.{max u v}).obj (op U)

/-- The category of `\mathbf Z`-indexed cochain complexes of sheaves of `\mathcal O`-modules. -/
abbrev siteModuleComplex {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (𝒪 : Sheaf J RingCat.{max u v}) [Abelian (siteModuleCat 𝒪)] :=
  CochainComplex (siteModuleCat 𝒪) ℤ

section

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable (𝒪 : Sheaf J RingCat.{max u v})

local notation "ModO" => siteModuleCat 𝒪

-- Proof sketch: on each `U ∈ B`, weak contractibility makes the sections functor exact on short
-- complexes. The forward implication maps an exact short complex along that exact functor. For
-- the converse, exactness of sheaf-module morphisms can be checked after restricting to a
-- covering by basis objects in `B`.
/-- Proposition 21.51.2 (1): if `B` is a covering family of weakly contractible objects of the
site `(\mathcal C, J)`, then a short complex of `\mathcal O`-modules is exact if and only if its
section sequence over every `U ∈ B` is exact. -/
theorem shortComplex_exact_iff_exact_on_basis_sections
    [Abelian ModO]
    (B : Set C)
    (hweak : ∀ ⦃U : C⦄, U ∈ B → J.IsWeaklyContractible U)
    (hcover : ∀ U : C, ∃ S : J.Cover U, ∀ I : S.Arrow, I.Y ∈ B)
    (S : ShortComplex ModO) :
    S.Exact ↔
      ∀ ⦃U : C⦄, U ∈ B →
        (S.map (siteModuleSectionsFunctor 𝒪 U)).Exact := sorry

-- Proof sketch: the weakly contractible basis gives the vanishing criterion needed for the
-- canonical truncation map `K ⟶ R lim_n τ_{\ge -n} K`. Applying the truncation-tower Milnor
-- criterion to any compatible comparison map yields that comparison as an isomorphism.
/-- Proposition 21.51.2 (2): if `B` is a covering family of weakly contractible objects of the
site `(\mathcal C, J)`, then every compatible comparison map from `K` to a chosen derived limit
of the truncation tower `(\tau_{\ge -n} K)_n` is an isomorphism. This is the Lean form of the
statement `K = R\!\varprojlim_n \tau_{\ge -n} K`. -/
theorem truncationComparison_isIso_of_basis_weaklyContractible
    [Abelian ModO]
    (B : Set C)
    (hweak : ∀ ⦃U : C⦄, U ∈ B → J.IsWeaklyContractible U)
    (hcover : ∀ U : C, ∃ S : J.Cover U, ∀ I : S.Arrow, I.Y ∈ B)
    (K L : DerivedCategory ModO) (c : K ⟶ L)
    (hc : IsTruncationDerivedLimitComparison K L c) :
    IsIso c := sorry

-- Proof sketch: evaluating on each weakly contractible basis object reduces the statement to the
-- corresponding surjectivity statement for inverse limits of towers of abelian groups with
-- surjective transition maps. Local surjectivity on a covering by objects of `B` then promotes to
-- surjectivity of the sheaf-module map.
/-- Proposition 21.51.2 (3): if `B` is a covering family of weakly contractible objects of the
site `(\mathcal C, J)` and `(\mathcal F_n)_n` is an inverse system of `\mathcal O`-modules with
surjective transition maps, then the projection `\varprojlim_n \mathcal F_n \to \mathcal F_1` is
surjective. In Lean, the first stage is indexed by `0`. -/
theorem limit_projectionToFirst_epi_of_surjective_transitions
    [Abelian ModO] [HasLimitsOfShape ℕᵒᵖ ModO]
    (B : Set C)
    (hweak : ∀ ⦃U : C⦄, U ∈ B → J.IsWeaklyContractible U)
    (hcover : ∀ U : C, ∃ S : J.Cover U, ∀ I : S.Arrow, I.Y ∈ B)
    (Fsys : ℕᵒᵖ ⥤ ModO)
    (hsurj : ∀ n : ℕ, Epi (Fsys.map ((homOfLE (Nat.le_succ n)).op))) :
    Epi (limit.π Fsys (op 0)) := sorry

-- Proof sketch: use part `(1)` to test exactness of a product short complex on sections over the
-- basis objects. Products in `AddCommGrpCat` are exact, so the product short complex is exact on
-- every basis object, hence exact in `\mathrm{Mod}(\mathcal O)` by the same criterion.
/-- Proposition 21.51.2 (4): products are exact in the abelian category
`\mathrm{Mod}(\mathcal O)`. -/
instance siteModuleCat_ab4Star_of_basis_weaklyContractible
    [Abelian ModO] [HasProducts ModO]
    (B : Set C)
    (hweak : ∀ ⦃U : C⦄, U ∈ B → J.IsWeaklyContractible U)
    (hcover : ∀ U : C, ∃ S : J.Cover U, ∀ I : S.Arrow, I.Y ∈ B) :
    AB4Star ModO := sorry

-- Proof sketch: once products are exact in `\mathrm{Mod}(\mathcal O)`, termwise products of
-- representative complexes preserve quasi-isomorphisms, so the product complex represents the
-- categorical product in the derived category.
/-- Proposition 21.51.2 (5): if `B` is a covering family of weakly contractible objects of the
site `(\mathcal C, J)`, then products exist in `D(\mathcal O)`. This is the derived-category
product consequence used to compute products from representative complexes. -/
theorem derived_products_exist_of_basis_weaklyContractible
    [Abelian ModO]
    (B : Set C)
    (hweak : ∀ ⦃U : C⦄, U ∈ B → J.IsWeaklyContractible U)
    (hcover : ∀ U : C, ∃ S : J.Cover U, ∀ I : S.Arrow, I.Y ∈ B)
    {α : Type w}
    (X' : α → DerivedCategory ModO) :
    HasProduct X' := sorry

-- Proof sketch: the degree-zero tower `(\mathcal F_n[0])_n` has a Milnor triangle. Exactness of
-- products from part `(4)` collapses the long exact cohomology sequence of that triangle above
-- degree `1`, so all higher derived inverse-limit objects vanish.
/-- Proposition 21.51.2 (6): if `B` is a covering family of weakly contractible objects of the
site `(\mathcal C, J)` and `K = R\!\varprojlim_n \mathcal F_n[0]` is a chosen derived limit of a
tower of `\mathcal O`-modules, then `R^p \!\varprojlim_n \mathcal F_n = 0` for every `p > 1`.
In Lean, this is the vanishing of the cohomology objects `H^p(K)` for `p > 1`. -/
theorem moduleTower_derivedLimit_higherHomology_isZero
    [Abelian ModO] [HasProducts ModO]
    (B : Set C)
    (hweak : ∀ ⦃U : C⦄, U ∈ B → J.IsWeaklyContractible U)
    (hcover : ∀ U : C, ∃ S : J.Cover U, ∀ I : S.Arrow, I.Y ∈ B)
    (Fsys : ℕᵒᵖ ⥤ ModO)
    (K : DerivedCategory ModO)
    (hK : IsDerivedLimit (Fsys ⋙ DerivedCategory.singleFunctor ModO (0 : ℤ)) K)
    (p : ℤ) (hp : 1 < p) :
    IsZero ((DerivedCategory.homologyFunctor ModO p).obj K) := sorry

-- Proof sketch: for the same degree-zero tower, the degree-one piece of the Milnor long exact
-- sequence identifies the first derived inverse-limit object with the cokernel of the Milnor
-- difference map on the product of the stages.
/-- Proposition 21.51.2 (7): if `B` is a covering family of weakly contractible objects of the
site `(\mathcal C, J)` and `K = R\!\varprojlim_n \mathcal F_n[0]` is a chosen derived limit of a
tower of `\mathcal O`-modules, then `R^1 \!\varprojlim_n \mathcal F_n` is represented by the
cokernel of the Milnor difference map on the product of the stages. -/
theorem moduleTower_firstDerivedLimit_iso_cokernel
    [Abelian ModO] [HasProducts ModO]
    (B : Set C)
    (hweak : ∀ ⦃U : C⦄, U ∈ B → J.IsWeaklyContractible U)
    (hcover : ∀ U : C, ∃ S : J.Cover U, ∀ I : S.Arrow, I.Y ∈ B)
    (Fsys : ℕᵒᵖ ⥤ ModO)
    (K : DerivedCategory ModO)
    (hK : IsDerivedLimit (Fsys ⋙ DerivedCategory.singleFunctor ModO (0 : ℤ)) K) :
    Nonempty
      (((DerivedCategory.homologyFunctor ModO (1 : ℤ)).obj K) ≅
        cokernel (derivedLimitDifferenceMap Fsys)) := sorry

-- Proof sketch: apply the Milnor distinguished triangle for a chosen derived limit
-- `K = R\!\varprojlim_n K_n` and take the long exact sequence of cohomology objects. Part `(4)`
-- identifies cohomology of products with products of cohomology objects, leaving the standard
-- Milnor short exact sequence.
/-- Proposition 21.51.2 (8): if `B` is a covering family of weakly contractible objects of the
site `(\mathcal C, J)`, then every chosen derived limit `K = R\!\varprojlim_n K_n` of a
sequential inverse system in `D(\mathcal O)` fits into the Milnor short exact sequence
`0 \to R^1 \!\varprojlim_n H^{p-1}(K_n) \to H^p(K) \to \varprojlim_n H^p(K_n) \to 0`. In Lean,
the left term is modeled by the cokernel of the Milnor difference map on the tower of cohomology
objects. -/
theorem derivedLimit_milnor_shortExact
    [Abelian ModO] [HasProducts ModO] [HasLimitsOfShape ℕᵒᵖ ModO]
    (B : Set C)
    (hweak : ∀ ⦃U : C⦄, U ∈ B → J.IsWeaklyContractible U)
    (hcover : ∀ U : C, ∃ S : J.Cover U, ∀ I : S.Arrow, I.Y ∈ B)
    (Ksys : ℕᵒᵖ ⥤ DerivedCategory ModO)
    (K : DerivedCategory ModO)
    (hK : IsDerivedLimit Ksys K)
    (p : ℤ) :
    ∃ (ι :
        cokernel (derivedLimitDifferenceMap
          (Ksys ⋙ DerivedCategory.homologyFunctor ModO (p - 1))) ⟶
          (DerivedCategory.homologyFunctor ModO p).obj K)
      (π :
        (DerivedCategory.homologyFunctor ModO p).obj K ⟶
          limit (Ksys ⋙ DerivedCategory.homologyFunctor ModO p))
      (hιπ : ι ≫ π = 0),
      (ShortComplex.mk ι π hιπ).ShortExact := sorry

end

end CategoryTheory
