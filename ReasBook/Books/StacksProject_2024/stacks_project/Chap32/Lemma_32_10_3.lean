import StacksProject_2024.stacks_project.Chap32.Lemma_32_10_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced the canonical sheaf-module finite-presentation
-- and pullback APIs, while local inspection found the project owners
-- `Functor.IsEquivalence (tensorRight -)` and `Scheme.IdealSheafData` with its concrete
-- affine-open ideal data. The finite-locally-free module condition is stated directly through
-- finite-free local trivializations to avoid importing a heavier local owner.

/-- Lemma 32.10.3 (1): let `S = lim_i S_i` be the limit of a directed inverse system of
quasi-compact and quasi-separated schemes with affine transition morphisms. Any finite locally
free `\mathcal O_S`-module descends, after passing to some stage `i`, to a finite locally free
`\mathcal O_{S_i}`-module whose pullback to `S` is isomorphic to the original module. -/
@[stacks 0B8W]
theorem exists_finiteLocallyFree_module_stage_of_limit
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ j, CompactSpace (D.obj j)]
    [∀ j, QuasiSeparatedSpace (D.obj j)]
    [∀ {j j' : I} (hjj' : j ≤ j'), IsAffineHom (D.map (homOfLE hjj'))]
    (ℱ : c.pt.Modules)
    (hℱ : ∀ x : c.pt,
      ∃ (U : TopologicalSpace.Opens c.pt) (_ : x ∈ U) (J : Type u) (_ : Finite J),
        Nonempty
          (ℱ.over U ≅
            (SheafOfModules.free.{u} J : SheafOfModules ((Scheme.ringCatSheaf c.pt).over U)))) :
    ∃ (i : I) (ℱi : (D.obj i).Modules),
      (∀ x : D.obj i,
        ∃ (U : TopologicalSpace.Opens (D.obj i)) (_ : x ∈ U) (J : Type u) (_ : Finite J),
          Nonempty
            (ℱi.over U ≅
              (SheafOfModules.free.{u} J :
                SheafOfModules ((Scheme.ringCatSheaf (D.obj i)).over U)))) ∧
        Nonempty ((Scheme.Modules.pullback (c.π.app i)).obj ℱi ≅ ℱ) := sorry

/-- Lemma 32.10.3 (2): in the same directed inverse-limit setup, any invertible
`\mathcal O_S`-module descends, after passing to some stage `i`, to an invertible
`\mathcal O_{S_i}`-module whose pullback to `S` is isomorphic to the original module. -/
@[stacks 0B8W]
theorem exists_invertible_module_stage_of_limit
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [MonoidalCategory c.pt.Modules]
    [∀ j, MonoidalCategory (D.obj j).Modules]
    [∀ j, CompactSpace (D.obj j)]
    [∀ j, QuasiSeparatedSpace (D.obj j)]
    [∀ {j j' : I} (hjj' : j ≤ j'), IsAffineHom (D.map (homOfLE hjj'))]
    (ℒ : c.pt.Modules) [Functor.IsEquivalence (MonoidalCategory.tensorRight ℒ)] :
    ∃ (i : I) (ℒi : (D.obj i).Modules)
      (_ : Functor.IsEquivalence (MonoidalCategory.tensorRight ℒi)),
      Nonempty ((Scheme.Modules.pullback (c.π.app i)).obj ℒi ≅ ℒ) := sorry

/-- Lemma 32.10.3 (3): in the same directed inverse-limit setup, any finite type
quasi-coherent ideal sheaf `\mathcal I ⊂ \mathcal O_S` is the extension of a finite type
quasi-coherent ideal sheaf on some stage `S_i`. In the `IdealSheafData` API this uses the
concrete affine-open ideals `\mathcal I(U)` and the extension is the pullback ideal sheaf
`\mathcal I_i.comap (S ⟶ S_i)`. -/
@[stacks 0B8W]
theorem exists_finiteType_idealSheaf_stage_of_limit
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ j, CompactSpace (D.obj j)]
    [∀ j, QuasiSeparatedSpace (D.obj j)]
    [∀ {j j' : I} (hjj' : j ≤ j'), IsAffineHom (D.map (homOfLE hjj'))]
    (𝓘 : c.pt.IdealSheafData)
    (h𝓘 : ∀ U : c.pt.affineOpens, (𝓘.ideal U).FG) :
    ∃ (i : I) (𝓘i : (D.obj i).IdealSheafData),
      (∀ U : (D.obj i).affineOpens, (𝓘i.ideal U).FG) ∧
        𝓘i.comap (c.π.app i) = 𝓘 := sorry

end AlgebraicGeometry
