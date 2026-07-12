import Mathlib
import Mathlib.CategoryTheory.Sites.Monoidal
import StacksProject_2024.Chap06.Definition_6_26_1
import StacksProject_2024.Chap17.ModuleRestrictionAndStalks
import StacksProject_2024.Chap17.Lemma_17_4_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits Opposite TopologicalSpace
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}
variable [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [MonoidalCategory X.Modules]

local notation "ModX" => X.Modules

/- 
Domain-style sampling for Lemma 17.16.1:
- primary domain: sheaves of modules on a ringed space, their sheaf tensor product, and stalks
- inspected canonical owner declarations:
  `RingedSpace.stalkModuleCat`,
  `tensor_product_stalk_iso_local`,
  `tensor_section_germ_eq_tmul`,
  `RingedSpace.moduleStalkHom`
- best owner abstraction:
  the earlier chapter-level theorem `tensor_product_stalk_iso_local`, which already packages the
  canonical tensor/stalk comparison on the correct owner objects
- primitive data:
  two `\mathcal O_X`-modules `\mathcal F`, `\mathcal G` and a point `x : X`
- derived API:
  the public canonical isomorphism for this item and its still-pending bifunctoriality square

Layer triage:
- `source-facing`: the stalkwise tensor-product comparison from the source
- `core/canonical`: `(RingedSpace.Modules X)`, `(⊗)`, and `RingedSpace.stalkModuleCat`
- `bridge/view`: the earlier local comparison owner from `Lemma_17_4_3`, reused here instead of
  rebuilding a second sheafification-level model
-/

/-- Lemma 17.16.1: the stalk of the sheaf tensor product `\mathcal F \otimes_{\mathcal O_X}
\mathcal G` is canonically isomorphic to the tensor product of the stalks
`\mathcal F_x \otimes_{\mathcal O_{X, x}} \mathcal G_x`. -/
noncomputable def tensorProductStalkIso (ℱ 𝒢 : ModX) (x : X) :
    stalkModuleCat (ℱ ⊗ 𝒢) x ≅ stalkModuleCat ℱ x ⊗ stalkModuleCat 𝒢 x := by
  -- Route correction: this file previously rebuilt the stalk comparison from a local
  -- sheafification model, but the earlier canonical owner `tensor_product_stalk_iso_local`
  -- already provides the required source-faithful tensor/stalk comparison.
  simpa using tensor_product_stalk_iso_local (ℱ := ℱ) (𝒢 := 𝒢) x

/-- Helper for Lemma 17.16.1: an inverse-side naturality identity for two isomorphisms yields the
corresponding `CommSq` for their forward maps. -/
private theorem commSq_of_inv_naturality
    {C : Type*} [Category C] {A B A' B' : C}
    (e : A ≅ B) (e' : A' ≅ B')
    {f : A ⟶ A'} {g : B ⟶ B'}
    (h : e.inv ≫ f = g ≫ e'.inv) :
    CommSq f e.hom e'.hom g := by
  -- Proof comment: whisker the inverse-side identity by the two isomorphism homs and simplify
  -- using the triangle identities.
  refine CommSq.mk ?_
  calc
    f ≫ e'.hom = (𝟙 _) ≫ f ≫ e'.hom := by simp
    _ = (e.hom ≫ e.inv) ≫ f ≫ e'.hom := by rw [e.hom_inv_id]
    _ = e.hom ≫ (e.inv ≫ f) ≫ e'.hom := by simp [Category.assoc]
    _ = e.hom ≫ (g ≫ e'.inv) ≫ e'.hom := by rw [h]
    _ = e.hom ≫ g ≫ (e'.inv ≫ e'.hom) := by simp [Category.assoc]
    _ = e.hom ≫ g := by simp

/-- Helper for Lemma 17.16.1: sections of the restricted module `ℱ.over U` are canonically the
same as ambient sections of `ℱ` on `U`. -/
private noncomputable def restrict_section_equiv
    (ℱ : ModX) (U : Opens X) :
    (ℱ.over U).sections ≃ ℱ.val.obj (op U) where
  toFun s := s.1 (op (Over.mk (𝟙 U)))
  invFun m :=
    (ℱ.over U).val.sectionsMk
      (fun V ↦ (ℱ.over U).val.map ((Over.mkIdTerminal.from V.unop).op) m)
      (fun V W f ↦ by
        -- Proof comment: every object of `Over U` has a unique map to the terminal object, so
        -- the reconstructed section is compatible under restriction.
        have h :
            (Over.mkIdTerminal.from V.unop).op ≫ f = (Over.mkIdTerminal.from W.unop).op := by
          apply Quiver.Hom.unop_inj
          simp only [Quiver.Hom.unop_op]
          exact Over.mkIdTerminal.hom_ext
            (f.unop ≫ Over.mkIdTerminal.from V.unop)
            (Over.mkIdTerminal.from W.unop)
        rw [← PresheafOfModules.map_comp_apply, h])
  left_inv s := by
    -- Proof comment: a section on the slice is determined by restricting its terminal value.
    ext V
    simpa using PresheafOfModules.sections_property s ((Over.mkIdTerminal.from V.unop).op)
  right_inv m := by
    -- Proof comment: evaluating the reconstructed section at the terminal object recovers `m`.
    change (ℱ.over U).val.map ((Over.mkIdTerminal.from (Over.mk (𝟙 U))).op) m = m
    have h : Over.mkIdTerminal.from (Over.mk (𝟙 U)) = 𝟙 (Over.mk (𝟙 U)) :=
      Over.mkIdTerminal.hom_ext _ _
    simpa using (ℱ.over U).val.congr_map_apply (congrArg Quiver.Hom.op h) m

/-- Helper for Lemma 17.16.1: view an ambient section on `U` as a section of the restricted
module `ℱ.over U`. -/
private noncomputable abbrev ambient_section_to_restrict_section
    (ℱ : ModX) (U : Opens X) (s : ℱ.val.obj (op U)) :
    (ℱ.over U).sections :=
  (restrict_section_equiv ℱ U).symm s

/-- Helper for Lemma 17.16.1: transporting an ambient `U`-section to `ℱ.over U` and back is the
identity. -/
private theorem restrict_section_transport_roundtrip
    (ℱ : ModX) (U : Opens X) (s : ℱ.val.obj (op U)) :
    restrict_section_equiv ℱ U (ambient_section_to_restrict_section ℱ U s) = s := by
  -- Proof comment: this is the `apply_symm_apply` identity for the section equivalence.
  exact Equiv.apply_symm_apply (restrict_section_equiv ℱ U) s

/-- Helper for Lemma 17.16.1: transporting a restricted section back to the ambient open and then
reconstructing it is the identity. -/
private theorem ambient_section_transport_roundtrip
    (ℱ : ModX) (U : Opens X) (s : (ℱ.over U).sections) :
    ambient_section_to_restrict_section ℱ U (restrict_section_equiv ℱ U s) = s := by
  -- Proof comment: this is the converse `symm_apply_apply` identity for the same equivalence.
  exact Equiv.symm_apply_apply (restrict_section_equiv ℱ U) s

/-- Helper for Lemma 17.16.1: the transported section of `ℱ.over U` evaluates to the original
ambient section at the terminal object of `Over U`. -/
private theorem ambient_section_to_restrict_section_terminal
    (ℱ : ModX) (U : Opens X) (s : ℱ.val.obj (op U)) :
    (ambient_section_to_restrict_section ℱ U s).1 (op (Over.mk (𝟙 U))) = s := by
  -- Proof comment: the terminal object restricts to itself by the identity map, so the explicit
  -- transported section formula collapses to `s`.
  change (ℱ.over U).val.map ((Over.mkIdTerminal.from (Over.mk (𝟙 U))).op) s = s
  have h : Over.mkIdTerminal.from (Over.mk (𝟙 U)) = 𝟙 (Over.mk (𝟙 U)) :=
    Over.mkIdTerminal.hom_ext _ _
  simpa using (ℱ.over U).val.congr_map_apply (congrArg Quiver.Hom.op h) s

/-- Helper for Lemma 17.16.1: the restriction of a module morphism to `U` evaluates at the
terminal object of `Over U` as the original component on `U`. -/
private theorem moduleRestrictionMap_terminal_app
    {ℱ 𝒢 : ModX} (U : Opens X) (φ : ℱ ⟶ 𝒢) :
    (RingedSpace.moduleRestrictionMap U φ).val.app (op (Over.mk (𝟙 U))) = φ.val.app (op U) := by
  -- Proof comment: at the terminal object, restricting along `U ⟶ U` is definitionally the
  -- original component of `φ`.
  rfl

/-- Helper for Lemma 17.16.1: transporting an ambient section to the restricted module and then
applying a restricted morphism agrees with first applying the ambient morphism on `U`. -/
private theorem restrict_section_equiv_sectionsMap
    {ℱ 𝒢 : ModX} (U : Opens X) (φ : ℱ ⟶ 𝒢) (s : ℱ.val.obj (op U)) :
    restrict_section_equiv 𝒢 U
        (SheafOfModules.sectionsMap (RingedSpace.moduleRestrictionMap U φ)
          (ambient_section_to_restrict_section ℱ U s)) =
      (φ.val.app (op U)) s := by
  -- Proof comment: evaluate the restricted section map at the terminal object of `Over U`; the
  -- transported section is `s` there, and the restricted morphism is the ambient map on `U`.
  change
      (((RingedSpace.moduleRestrictionMap U φ).val.app (op (Over.mk (𝟙 U))))
          ((ambient_section_to_restrict_section ℱ U s).1 (op (Over.mk (𝟙 U))))) =
        (φ.val.app (op U)) s
  rw [ambient_section_to_restrict_section_terminal]
  rw [moduleRestrictionMap_terminal_app]
  rfl

/-- Helper for Lemma 17.16.1: the open inclusion `U ↪ X` sends the point `⟨x, hx⟩` back to the
ambient point `x`. -/
private theorem open_restriction_base_apply
    (U : Opens X) (x : X) (hx : x ∈ U) :
    (X.ofRestrict U.isOpenEmbedding).hom.base ⟨x, hx⟩ = x := rfl

/-- Helper for Lemma 17.16.1: the canonical owner-level tensor/stalk comparison should first be
proved natural on inverse maps, where the domain is already the tensor product of stalks. -/
private theorem tensor_product_stalk_iso_local_inv_naturality
    {ℱ ℱ' 𝒢 𝒢' : ModX} (f : ℱ ⟶ ℱ') (g : 𝒢 ⟶ 𝒢') (x : X) :
    (tensor_product_stalk_iso_local (ℱ := ℱ) (𝒢 := 𝒢) x).inv ≫
        moduleStalkHom x (f ⊗ₘ g) =
      (moduleStalkHom x f ⊗ₘ moduleStalkHom x g) ≫
        (tensor_product_stalk_iso_local (ℱ := ℱ') (𝒢 := 𝒢') x).inv := by
  -- Route correction: the source-side square out of `stalkModuleCat (ℱ ⊗ 𝒢) x` is the wrong
  -- domain for generator arguments. The source proof should instead compare inverse maps on
  -- `stalkModuleCat ℱ x ⊗ stalkModuleCat 𝒢 x`, where `TensorProduct.ext` and `germ_exist`
  -- reduce the problem to local pure tensors on a common neighborhood.
  -- Proof skeleton:
  -- 1. Represent each tensor factor by a germ on some open neighborhood and refine to the common
  --    neighborhood `W = U ⊓ V`.
  -- 2. Transport the restricted-space tensor-stalk theorem along the Chapter 6 open-inclusion
  --    pullback-stalk comparison to obtain the ambient local pure-tensor formula on `W`.
  -- 3. Rewrite the left composite by `RingedSpace.moduleStalkMap_germ` and the right composite by
  --    `ModuleCat.MonoidalCategory.tensorHom_tmul`, then close by the transported inverse formula.
  -- TODO: the section-level transport step is now packaged by
  -- `restrict_section_equiv_sectionsMap`, and the remaining blocker is the stalk-side
  -- pure-tensor/germ transport from the restricted theorem back to the ambient stalk. Concretely,
  -- we need both the comparison between the restriction owner `ℱ.over U` and the open-inclusion
  -- pullback object `((X.ofRestrict U.isOpenEmbedding)^*).obj ℱ`, and the stalk-level transport
  -- theorem from Chapter 6. In the current workspace state that owner route is unavailable here
  -- because importing `stacks_project.Chap06.Lemma_6_26_4` requires the missing object file for
  -- `stacks_project.Chap06.Lemma_6_21_5`.
  sorry

/-- Helper for Lemma 17.16.1: the imported owner-level tensor/stalk comparison is natural in both
module arguments. -/
private theorem tensor_product_stalk_iso_local_naturality
    {ℱ ℱ' 𝒢 𝒢' : ModX} (f : ℱ ⟶ ℱ') (g : 𝒢 ⟶ 𝒢') (x : X) :
    CommSq
      (moduleStalkHom x (f ⊗ₘ g))
      (tensor_product_stalk_iso_local (ℱ := ℱ) (𝒢 := 𝒢) x).hom
      (tensor_product_stalk_iso_local (ℱ := ℱ') (𝒢 := 𝒢') x).hom
      (moduleStalkHom x f ⊗ₘ moduleStalkHom x g) := by
  -- Proof comment: once inverse-side naturality is available, the forward square is the formal
  -- transport of that identity across the two isomorphisms.
  exact commSq_of_inv_naturality
    (tensor_product_stalk_iso_local (ℱ := ℱ) (𝒢 := 𝒢) x)
    (tensor_product_stalk_iso_local (ℱ := ℱ') (𝒢 := 𝒢') x)
    (tensor_product_stalk_iso_local_inv_naturality (f := f) (g := g) (x := x))

/-- Lemma 17.16.1 is functorial in both module variables: a morphism
`f : \mathcal F \to \mathcal F'` and `g : \mathcal G \to \mathcal G'` induces a commutative
square between the canonical stalk tensor-product isomorphisms. -/
theorem tensorProductStalkIso_naturality
    {ℱ ℱ' 𝒢 𝒢' : ModX} (f : ℱ ⟶ ℱ') (g : 𝒢 ⟶ 𝒢') (x : X) :
    CommSq
      (moduleStalkHom x (f ⊗ₘ g))
      (tensorProductStalkIso ℱ 𝒢 x).hom
      (tensorProductStalkIso ℱ' 𝒢' x).hom
      (moduleStalkHom x f ⊗ₘ moduleStalkHom x g) := by
  -- Proof comment: reduce the public theorem to the canonical owner-level naturality square and
  -- transport across the wrapper isomorphism introduced above.
  simpa [tensorProductStalkIso] using
    tensor_product_stalk_iso_local_naturality (f := f) (g := g) (x := x)

end AlgebraicGeometry.RingedSpace
