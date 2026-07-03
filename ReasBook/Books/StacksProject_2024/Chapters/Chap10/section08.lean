import Mathlib
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Colimit.Module
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_10_8_1 (from Chap10) -/
universe u v

namespace CategoryTheory

section

variable {I : Type u} [Preorder I]
variable {R : Type v} [Ring R]

/- Definition 10.8.1: a system of `R`-modules over a preordered set `I` is exactly a functor
`I ⥤ ModuleCat R`, i.e. the specialization of Categories, Definition 4.21.2 to the category of
`R`-modules. The primitive data are the objects `F.obj i` and transition maps
`F.map (homOfLE hij)`; the identity and composition compatibilities are derived directly from the
owner abstraction's functor laws. When `I` is a directed set, this is a directed system in the
usual sense. -/
#check (I ⥤ ModuleCat R)

end

end CategoryTheory

/-! ### Lemma_10_8_2 (from Chap10) -/
open CategoryTheory CategoryTheory.Limits ModuleCat

universe u v

noncomputable section

section

variable {I : Type u} [Preorder I]
variable {R : Type v} [Ring R]
variable (F : I ⥤ ModuleCat.{u} R)

/-
Layering for this item:
* `source-facing`: the textbook quotient-model direct limit attached to a module-valued functor on a
  preorder, viewed as a cocone over `F`;
* `core/canonical`: `ModuleCat.directLimitDiagram`, `ModuleCat.directLimitCocone`, and
  `ModuleCat.directLimitIsColimit`;
* `bridge/view`: the objectwise identification of `F` with the canonical direct-limit diagram.
-/

local instance module_system_decidableEqIndex : DecidableEq I := Classical.decEq I

local notation "M" => fun i : I ↦ F.obj i

private abbrev moduleSystemMap (i j : I) (h : i ≤ j) :
    F.obj i →ₗ[R] F.obj j :=
  (F.map (homOfLE h)).hom

local notation "μ" => fun i j h ↦ moduleSystemMap F i j h

private instance : DirectedSystem (fun i ↦ F.obj i) (fun i j h ↦ moduleSystemMap F i j h) where
  map_self i x := by
    change ((F.map (𝟙 _)).hom) x = x
    exact congr(($((F.map_id _)) x))
  map_map := by
    intro i j k hij hjk x
    change ((F.map (homOfLE hjk)).hom) (((F.map (homOfLE hij)).hom) x) =
      ((F.map (homOfLE (hij.trans hjk))).hom) x
    simpa using congr(($((F.map_comp (homOfLE hij) (homOfLE hjk)).symm) x))

private def moduleSystemDiagramIso :
    F ≅ ModuleCat.directLimitDiagram M μ :=
  NatIso.ofComponents
    (fun _ ↦ Iso.refl _)
    (fun f ↦ by
      simpa using congrArg F.map (homOfLE_leOfHom f).symm)

local notation "M∞" => Module.DirectLimit M μ

local notation "of∞" => Module.DirectLimit.of R I M μ

/-- Lemma 10.8.2: the textbook quotient-model direct limit `(⨁ i, M_i) / Q`, implemented by
`Module.DirectLimit`, carries the canonical cocone over `F`. -/
noncomputable def module_system_cocone : Cocone F :=
  (Cocone.precompose (moduleSystemDiagramIso F).hom).obj
    (ModuleCat.directLimitCocone M μ)

/-- The structure map from stage `i` into the quotient-model direct limit is the canonical map
`Module.DirectLimit.of`. -/
@[simp] theorem module_system_cocone_ι_app (i : I) :
    (module_system_cocone F).ι.app i = ModuleCat.ofHom (of∞ i) := by
  rfl

/-- Lemma 10.8.2: the explicit quotient-model cocone `module_system_cocone F` is a colimit cocone,
so it has the universal property of the direct limit described in the source. -/
noncomputable def module_system_isColimit : IsColimit (module_system_cocone F) :=
  (IsColimit.precomposeHomEquiv (moduleSystemDiagramIso F) (ModuleCat.directLimitCocone M μ)).1
    (ModuleCat.directLimitIsColimit M μ)

/-- Companion bridge: the chosen categorical colimit `colimit F` is canonically isomorphic to the
explicit quotient-model direct limit `Module.DirectLimit`. -/
noncomputable def module_system_colimit_iso_moduleDirectLimit :
    colimit F ≅ ModuleCat.of R M∞ :=
  IsColimit.coconePointsIsoOfNatIso (colimit.isColimit F) (ModuleCat.directLimitIsColimit M μ)
    (moduleSystemDiagramIso F)

/-- Under `module_system_colimit_iso_moduleDirectLimit`, the chosen colimit structure map from
stage `i` identifies with the canonical map into `Module.DirectLimit`. -/
theorem module_system_colimit_iso_moduleDirectLimit_ι (i : I) :
    colimit.ι F i ≫ (module_system_colimit_iso_moduleDirectLimit F).hom =
      ModuleCat.ofHom (of∞ i) := by
  simpa using
    IsColimit.comp_coconePointsIsoOfNatIso_hom (colimit.isColimit F)
      (ModuleCat.directLimitIsColimit M μ) (moduleSystemDiagramIso F) i

end

/-! ### Lemma_10_8_3 (from Chap10) -/
open CategoryTheory CategoryTheory.Limits ModuleCat

universe u v

noncomputable section

section

variable {R : Type u} [Ring R]
variable {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
variable (M : I → Type v) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
variable (μ : ∀ i j, i ≤ j → M i →ₗ[R] M j)
variable [DirectedSystem M (μ · · ·)]

/-
Layering for this item:
* source-facing: the explicit eventual-equality model of the directed colimit.
* core/canonical owners: `directLimitDiagram`, `directLimitCocone`, `directLimitIsColimit`, and
  `Module.DirectLimit.linearEquiv`.
* bridge/view: identify the chosen categorical colimit with the textbook quotient-of-the-disjoint-
  union model.
-/
local notation "M∞" => DirectLimit M μ
local notation "of∞" => DirectLimit.Module.of R I M μ

local instance directLimit_eventualEq_decidableEqIndex : DecidableEq I := Classical.decEq I

/-- Lemma 10.8.3 (1): in the quotient-of-the-disjoint-union model of the direct limit, two stage
elements agree exactly when they become equal in some later stage of the directed system. -/
theorem directLimit_stageMap_eq_iff {i j : I} {x : M i} {y : M j} :
    of∞ i x = of∞ j y ↔ ∃ k, ∃ hik : i ≤ k, ∃ hjk : j ≤ k, μ i k hik x = μ j k hjk y := by
  change (⟦⟨i, x⟩⟧ : M∞) = ⟦⟨j, y⟩⟧ ↔ _
  exact Quotient.eq

/-- Lemma 10.8.3 (2): the categorical colimit of a directed system of modules is canonically
isomorphic to the textbook quotient of the disjoint union by eventual equality. -/
noncomputable def colimit_iso_eventualEqQuotient :
    colimit (directLimitDiagram M μ) ≅ ModuleCat.of R M∞ :=
  colimit.isoColimitCocone
      (⟨directLimitCocone M μ, directLimitIsColimit M μ⟩ :
        ColimitCocone (directLimitDiagram M μ)) ≪≫
    (Module.DirectLimit.linearEquiv M μ).toModuleIso

/-- Lemma 10.8.3 (3): under `colimit_iso_eventualEqQuotient`, the colimit structure map from stage `i` is the
canonical map from `M i` to the quotient of the disjoint union. -/
theorem colimit_iso_eventualEqQuotient_ι (i : I) :
    colimit.ι (directLimitDiagram M μ) i ≫ (colimit_iso_eventualEqQuotient M μ).hom =
      ModuleCat.ofHom (of∞ i) := by
  change
    colimit.ι (directLimitDiagram M μ) i ≫
        (colimit.isoColimitCocone
          (⟨directLimitCocone M μ, directLimitIsColimit M μ⟩ :
            ColimitCocone (directLimitDiagram M μ))).hom ≫
        (Module.DirectLimit.linearEquiv M μ).toModuleIso.hom =
      ModuleCat.ofHom (of∞ i)
  rw [← Category.assoc, colimit.isoColimitCocone_ι_hom]
  ext x
  simpa [DirectLimit.Module.of] using
    (Module.DirectLimit.linearEquiv_of M μ :
      (Module.DirectLimit.linearEquiv M μ) ((Module.DirectLimit.of R I M μ i) x) =
        DirectLimit.Module.of R I M μ i x)

end

/-! ### Lemma_10_8_4 (from Chap10) -/
open Module.DirectLimit

universe u v

noncomputable section

section

variable {R : Type u} [Ring R]
variable {I : Type v} [Preorder I] [IsDirectedOrder I]
variable (M : I → Type v) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
variable (μ : ∀ i j, i ≤ j → M i →ₗ[R] M j)
variable [DirectedSystem M (μ · · ·)]

local instance directLimit_zero_decidableEqIndex : DecidableEq I := Classical.decEq I

/-- Lemma 10.8.4: an element of a stage of a directed system of modules maps to zero in the
direct limit if and only if it becomes zero in some later stage. -/
-- Proof sketch: the forward implication is the canonical exactness statement
-- `Module.DirectLimit.of.zero_exact`; the reverse implication uses compatibility of the structure
-- maps with the colimit map via `Module.DirectLimit.of_f`.
theorem directLimit_stageMap_eq_zero_iff {i : I} {x : M i} :
    of R I M μ i x = 0 ↔ ∃ (j : I) (hij : i ≤ j), μ i j hij x = 0 := by
  constructor
  · -- The direct-limit exactness criterion gives the eventual vanishing stage.
    intro hx
    exact of.zero_exact hx
  · -- Rewrite the colimit class through the witness stage and then simplify using the zero witness.
    rintro ⟨j, hij, hxj⟩
    have hstage : of R I M μ j (μ i j hij x) = of R I M μ j 0 := by
      exact congrArg (of R I M μ j) hxj
    simpa [of_f] using hstage

end

/-! ### Example_10_8_5 (from Chap10) -/
open CategoryTheory CategoryTheory.Limits ModuleCat

universe u v

section

variable {R : Type u} [Ring R]
variable {Ma : Type v} [AddCommGroup Ma] [Module R Ma]
variable {Mb : Type v} [AddCommGroup Mb] [Module R Mb]
variable {Mc : Type v} [AddCommGroup Mc] [Module R Mc]

/-
Layering for Example 10.8.5:
* source-facing: the explicit quotient model for the colimit of the fork-shaped system
  `{a, b, c}` with `a < b` and `a < c`.
* core/canonical owner: `span (ModuleCat.ofHom μab) (ModuleCat.ofHom μac)`.
* bridge/view: the explicit quotient model `Coker(μab ⊕ -μac)` computing the colimit of that
  system.
-/

/-- The map `Ma → Mb × Mc` whose cokernel computes the colimit of the fork system from
Example 10.8.5. -/
def example_10_8_5_difference_map (μab : Ma →ₗ[R] Mb) (μac : Ma →ₗ[R] Mc) :
    Ma →ₗ[R] Mb × Mc :=
  μab.prod (-μac)

/-- The explicit quotient model computing the colimit in Example 10.8.5. -/
abbrev example_10_8_5_colimit_model (μab : Ma →ₗ[R] Mb) (μac : Ma →ₗ[R] Mc) :=
  (Mb × Mc) ⧸ LinearMap.range (example_10_8_5_difference_map μab μac)

/-- The canonical map from stage `b` into the explicit colimit model of Example 10.8.5. -/
def example_10_8_5_from_b (μab : Ma →ₗ[R] Mb) (μac : Ma →ₗ[R] Mc) :
    Mb →ₗ[R] example_10_8_5_colimit_model μab μac :=
  (LinearMap.range (example_10_8_5_difference_map μab μac)).mkQ.comp (LinearMap.inl R Mb Mc)

/-- The canonical map from stage `c` into the explicit colimit model of Example 10.8.5. -/
def example_10_8_5_from_c (μab : Ma →ₗ[R] Mb) (μac : Ma →ₗ[R] Mc) :
    Mc →ₗ[R] example_10_8_5_colimit_model μab μac :=
  (LinearMap.range (example_10_8_5_difference_map μab μac)).mkQ.comp (LinearMap.inr R Mb Mc)

/-- The canonical map from stage `a` into the explicit colimit model of Example 10.8.5. -/
def example_10_8_5_from_a (μab : Ma →ₗ[R] Mb) (μac : Ma →ₗ[R] Mc) :
    Ma →ₗ[R] example_10_8_5_colimit_model μab μac :=
  (example_10_8_5_from_b μab μac).comp μab

/-- The explicit quotient model of Example 10.8.5 gives a pushout cocone on
`Ma ⟶ Mb`, `Ma ⟶ Mc`. -/
private theorem example_10_8_5_comm
    (μab : Ma →ₗ[R] Mb) (μac : Ma →ₗ[R] Mc) :
    CommSq (ModuleCat.ofHom μab) (ModuleCat.ofHom μac)
      (ModuleCat.ofHom (example_10_8_5_from_b μab μac))
      (ModuleCat.ofHom (example_10_8_5_from_c μab μac)) := by
  refine ⟨?_⟩
  apply ModuleCat.hom_ext
  ext x
  change Submodule.Quotient.mk
      (((LinearMap.inl R Mb Mc).comp μab) x : Mb × Mc) =
    Submodule.Quotient.mk (((LinearMap.inr R Mb Mc).comp μac) x : Mb × Mc)
  exact (Submodule.Quotient.eq _).2 ⟨x, by
    simp [example_10_8_5_difference_map]⟩

/-- The explicit quotient cocone over the fork system from Example 10.8.5. -/
def example_10_8_5_cocone (μab : Ma →ₗ[R] Mb) (μac : Ma →ₗ[R] Mc) :
    PushoutCocone (ModuleCat.ofHom μab) (ModuleCat.ofHom μac) :=
  PushoutCocone.mk
    (ModuleCat.ofHom (example_10_8_5_from_b μab μac))
    (ModuleCat.ofHom (example_10_8_5_from_c μab μac))
    (example_10_8_5_comm μab μac).w

section Desc

variable {P : Type v} [AddCommGroup P] [Module R P]

/-- The unique factorization through the explicit colimit model induced by compatible maps out of
stages `b` and `c`. -/
private def example_10_8_5_desc
    (μab : Ma →ₗ[R] Mb) (μac : Ma →ₗ[R] Mc)
    (β : Mb →ₗ[R] P) (γ : Mc →ₗ[R] P) (hβγ : β.comp μab = γ.comp μac) :
    example_10_8_5_colimit_model μab μac →ₗ[R] P :=
  (LinearMap.range (example_10_8_5_difference_map μab μac)).liftQ (LinearMap.coprod β γ) <| by
    rw [LinearMap.range_le_ker_iff]
    ext x
    have hx : β (μab x) = γ (μac x) := LinearMap.congr_fun hβγ x
    simpa [example_10_8_5_difference_map, sub_eq_add_neg] using sub_eq_zero.mpr hx

@[simp] private theorem example_10_8_5_inl_desc
    (μab : Ma →ₗ[R] Mb) (μac : Ma →ₗ[R] Mc)
    (β : Mb →ₗ[R] P) (γ : Mc →ₗ[R] P) (hβγ : β.comp μab = γ.comp μac) :
    (example_10_8_5_desc μab μac β γ hβγ).comp (example_10_8_5_from_b μab μac) = β := by
  rw [example_10_8_5_desc, example_10_8_5_from_b, ← LinearMap.comp_assoc, Submodule.liftQ_mkQ,
    LinearMap.coprod_inl]

@[simp] private theorem example_10_8_5_inr_desc
    (μab : Ma →ₗ[R] Mb) (μac : Ma →ₗ[R] Mc)
    (β : Mb →ₗ[R] P) (γ : Mc →ₗ[R] P) (hβγ : β.comp μab = γ.comp μac) :
    (example_10_8_5_desc μab μac β γ hβγ).comp (example_10_8_5_from_c μab μac) = γ := by
  rw [example_10_8_5_desc, example_10_8_5_from_c, ← LinearMap.comp_assoc, Submodule.liftQ_mkQ,
    LinearMap.coprod_inr]

private theorem example_10_8_5_desc_unique
    (μab : Ma →ₗ[R] Mb) (μac : Ma →ₗ[R] Mc)
    (β : Mb →ₗ[R] P) (γ : Mc →ₗ[R] P) (hβγ : β.comp μab = γ.comp μac)
    {δ : example_10_8_5_colimit_model μab μac →ₗ[R] P}
    (hδB : δ.comp (example_10_8_5_from_b μab μac) = β)
    (hδC : δ.comp (example_10_8_5_from_c μab μac) = γ) :
    δ = example_10_8_5_desc μab μac β γ hβγ := by
  apply LinearMap.ext
  intro q
  refine
    Submodule.Quotient.induction_on (LinearMap.range (example_10_8_5_difference_map μab μac)) q
      ?_
  intro z
  rcases z with ⟨x, y⟩
  have hxy : (Submodule.Quotient.mk (x, y) : example_10_8_5_colimit_model μab μac) =
      Submodule.Quotient.mk (x, 0) + Submodule.Quotient.mk (0, y) := by
    simpa using
      (Submodule.Quotient.mk_add
        (LinearMap.range (example_10_8_5_difference_map μab μac)) :
        (Submodule.Quotient.mk
            ((((x, (0 : Mc)) : Mb × Mc) + (((0 : Mb), y) : Mb × Mc)) :
              Mb × Mc) :
          example_10_8_5_colimit_model μab μac) =
      Submodule.Quotient.mk (((x, (0 : Mc)) : Mb × Mc)) +
            Submodule.Quotient.mk (((0 : Mb), y) : Mb × Mc))
  have hxB : δ (Submodule.Quotient.mk (x, 0) : example_10_8_5_colimit_model μab μac) = β x := by
    simpa [example_10_8_5_from_b] using LinearMap.congr_fun hδB x
  have hyC : δ (Submodule.Quotient.mk (0, y) : example_10_8_5_colimit_model μab μac) = γ y := by
    simpa [example_10_8_5_from_c] using LinearMap.congr_fun hδC y
  have hxB' :
      example_10_8_5_desc μab μac β γ hβγ
          (Submodule.Quotient.mk (x, 0) : example_10_8_5_colimit_model μab μac) =
        β x := by
    simpa [example_10_8_5_from_b] using
      LinearMap.congr_fun (example_10_8_5_inl_desc μab μac β γ hβγ) x
  have hyC' :
      example_10_8_5_desc μab μac β γ hβγ
          (Submodule.Quotient.mk (0, y) : example_10_8_5_colimit_model μab μac) =
        γ y := by
    simpa [example_10_8_5_from_c] using
      LinearMap.congr_fun (example_10_8_5_inr_desc μab μac β γ hβγ) y
  rw [hxy, map_add, map_add, hxB, hyC, hxB', hyC']

end Desc

/-- Example 10.8.5: the explicit quotient cocone computes the colimit of the fork-shaped system
`a < b`, `a < c`. -/
def example_10_8_5_isColimit (μab : Ma →ₗ[R] Mb) (μac : Ma →ₗ[R] Mc) :
    IsColimit (example_10_8_5_cocone μab μac) := by
  exact
    PushoutCocone.IsColimit.mk (example_10_8_5_comm μab μac).w
      (fun s ↦ ModuleCat.ofHom <|
        example_10_8_5_desc μab μac s.inl.hom s.inr.hom
          (congrArg ModuleCat.Hom.hom s.condition))
      (fun s ↦ by
        apply ModuleCat.hom_ext
        exact
          (example_10_8_5_inl_desc μab μac s.inl.hom s.inr.hom
            (congrArg ModuleCat.Hom.hom s.condition)))
      (fun s ↦ by
        apply ModuleCat.hom_ext
        exact
          (example_10_8_5_inr_desc μab μac s.inl.hom s.inr.hom
            (congrArg ModuleCat.Hom.hom s.condition)))
      (fun s m hmB hmC ↦ by
        apply ModuleCat.hom_ext
        exact example_10_8_5_desc_unique μab μac s.inl.hom s.inr.hom
          (congrArg ModuleCat.Hom.hom s.condition)
          (congrArg ModuleCat.Hom.hom <| by simpa using hmB)
          (congrArg ModuleCat.Hom.hom <| by simpa using hmC))

/-- Helper for Example 10.8.5: an element of stage `b` dies in the explicit quotient colimit
exactly when it comes from `ker μac` through `μab`. -/
private lemma example_10_8_5_from_b_mem_ker_iff
    (μab : Ma →ₗ[R] Mb) (μac : Ma →ₗ[R] Mc) (x : Mb) :
    x ∈ LinearMap.ker (example_10_8_5_from_b μab μac) ↔
      x ∈ Submodule.map μab (LinearMap.ker μac) := by
  -- Convert vanishing in the quotient into a witness in the range of the difference map.
  rw [LinearMap.mem_ker]
  change
    (Submodule.Quotient.mk ((x, 0) : Mb × Mc) :
      example_10_8_5_colimit_model μab μac) = 0 ↔
      x ∈ Submodule.map μab (LinearMap.ker μac)
  rw [Submodule.Quotient.mk_eq_zero]
  constructor
  · intro hx
    rw [LinearMap.mem_range] at hx
    rcases hx with ⟨y, hy⟩
    rw [Submodule.mem_map]
    refine ⟨y, ?_, ?_⟩
    · -- The second coordinate of the range witness says `μac y = 0`.
      rw [LinearMap.mem_ker]
      have hy₂ : (example_10_8_5_difference_map μab μac y).2 = 0 := by
        simpa using congrArg Prod.snd hy
      simpa [example_10_8_5_difference_map] using hy₂
    · -- The first coordinate records that `x = μab y`.
      have hy₁ : (example_10_8_5_difference_map μab μac y).1 = x := by
        simpa using congrArg Prod.fst hy
      simpa [example_10_8_5_difference_map] using hy₁
  · intro hx
    rw [Submodule.mem_map] at hx
    rcases hx with ⟨y, hy, rfl⟩
    rw [LinearMap.mem_ker] at hy
    rw [LinearMap.mem_range]
    refine ⟨y, ?_⟩
    -- A witness from `ker μac` maps to `(μab y, 0)` under the difference map.
    ext <;> simp [example_10_8_5_difference_map, hy]

/-- Helper for Example 10.8.5: an element of stage `a` dies in the explicit quotient colimit
exactly when it decomposes as a sum of something in `ker μab` and something in `ker μac`. -/
private lemma example_10_8_5_from_a_mem_ker_iff
    (μab : Ma →ₗ[R] Mb) (μac : Ma →ₗ[R] Mc) (x : Ma) :
    x ∈ LinearMap.ker (example_10_8_5_from_a μab μac) ↔
      x ∈ LinearMap.ker μab ⊔ LinearMap.ker μac := by
  -- Convert the quotient equation into a decomposition coming from the difference-map witness.
  rw [LinearMap.mem_ker]
  change
    (Submodule.Quotient.mk ((μab x, 0) : Mb × Mc) :
      example_10_8_5_colimit_model μab μac) = 0 ↔
      x ∈ LinearMap.ker μab ⊔ LinearMap.ker μac
  rw [Submodule.Quotient.mk_eq_zero]
  constructor
  · intro hx
    rw [LinearMap.mem_range] at hx
    rcases hx with ⟨y, hy⟩
    rw [Submodule.mem_sup]
    refine ⟨x - y, ?_, y, ?_, by abel⟩
    · -- The first coordinate identifies `μab (x - y)` with `0`.
      rw [LinearMap.mem_ker]
      have hy₁ : μab y = μab x := by
        simpa [example_10_8_5_difference_map] using congrArg Prod.fst hy
      calc
        μab (x - y) = μab x - μab y := by simp
        _ = 0 := by simp [hy₁]
    · -- The second coordinate identifies `y` as lying in `ker μac`.
      rw [LinearMap.mem_ker]
      have hy₂ : -(μac y) = 0 := by
        simpa [example_10_8_5_difference_map] using congrArg Prod.snd hy
      have hy₂' : μac y = 0 := by
        simpa using congrArg Neg.neg hy₂
      exact hy₂'
  · intro hx
    rw [Submodule.mem_sup] at hx
    rcases hx with ⟨u, hu, v, hv, huv⟩
    rw [LinearMap.mem_ker] at hu hv
    change ∃ y : Ma,
        example_10_8_5_difference_map μab μac y = ((μab x, 0) : Mb × Mc)
    refine ⟨v, ?_⟩
    -- A decomposition `x = u + v` with `u` in `ker μab` and `v` in `ker μac`
    -- produces the required range witness.
    apply Prod.ext
    · calc
        μab v = μab u + μab v := by simp [hu]
        _ = μab (u + v) := by rw [LinearMap.map_add]
        _ = μab x := by rw [huv]
    · simp [example_10_8_5_difference_map, hv]

/-- Example 10.8.5: in the explicit colimit model of the fork system, the kernel of the map from
stage `a` is `ker μab + ker μac`, and the kernel of the map from stage `b` is the image of
`ker μac` under `μab`. -/
theorem example_10_8_5_kernels
    (μab : Ma →ₗ[R] Mb) (μac : Ma →ₗ[R] Mc) :
    LinearMap.ker (example_10_8_5_from_a μab μac) = LinearMap.ker μab ⊔ LinearMap.ker μac ∧
      LinearMap.ker (example_10_8_5_from_b μab μac) =
        Submodule.map μab (LinearMap.ker μac) := by
  constructor
  · -- The stage-`a` kernel is exactly the sum of the two source kernels.
    ext x
    simpa using example_10_8_5_from_a_mem_ker_iff μab μac x
  · -- The stage-`b` kernel is the image of `ker μac` under `μab`.
    ext x
    simpa using example_10_8_5_from_b_mem_ker_iff μab μac x

/-- If `μab (ker μac)` is nonzero, then some nonzero element of stage `b` dies in the explicit
colimit model of Example 10.8.5. -/
private theorem example_10_8_5_nonzero_from_b_maps_to_zero
    (μab : Ma →ₗ[R] Mb) (μac : Ma →ₗ[R] Mc)
    (hker : Submodule.map μab (LinearMap.ker μac) ≠ ⊥) :
    ∃ x : Mb, example_10_8_5_from_b μab μac x = 0 ∧ x ≠ 0 := by
  obtain ⟨_, hfrom_b⟩ := example_10_8_5_kernels μab μac
  obtain ⟨x, hx, hx_ne⟩ := (Submodule.ne_bot_iff _).mp hker
  refine ⟨x, ?_, hx_ne⟩
  -- Translate the nonzero kernel element through the explicit kernel computation.
  have hxker : x ∈ LinearMap.ker (example_10_8_5_from_b μab μac) := by
    simpa [hfrom_b] using hx
  exact LinearMap.mem_ker.mp hxker

/-- Example 10.8.5 gives the direct failure of Lemma 10.8.4 without directedness: if
`μab (ker μac)` is nonzero, then some nonzero element of stage `b` maps to `0` in the colimit of
the fork-shaped system, but it cannot become `0` in any later stage of that system. -/
theorem example_10_8_5_counterexample_to_lemma_10_8_4
    (μab : Ma →ₗ[R] Mb) (μac : Ma →ₗ[R] Mc)
    (hker : Submodule.map μab (LinearMap.ker μac) ≠ ⊥) :
    ∃ x : Mb,
      example_10_8_5_from_b μab μac x = 0 ∧
        ¬ ∃ j : WalkingSpan, ∃ f : WalkingSpan.left ⟶ j,
          ((span (ModuleCat.ofHom μab) (ModuleCat.ofHom μac)).map f).hom x = 0 := by
  obtain ⟨x, hx, hx_ne⟩ := example_10_8_5_nonzero_from_b_maps_to_zero μab μac hker
  refine ⟨x, hx, ?_⟩
  rintro ⟨j, f, hf⟩
  cases j with
  | none =>
      nomatch f
  | some val =>
      cases val with
      | left =>
          have hf_id : f = 𝟙 WalkingSpan.left := Subsingleton.elim _ _
          subst f
          exact hx_ne <| by simpa using hf
      | right =>
          nomatch f

end

/-! ### Definition_10_8_6 (from Chap10) -/
universe u v

namespace CategoryTheory

section

variable {R : Type u} [Ring R]
variable {I : Type v} [Preorder I]
variable {M N : I ⥤ ModuleCat R}

/- Definition 10.8.6: a homomorphism of systems of `R`-modules over the same preordered set `I`
is exactly a natural transformation `M ⟶ N`, i.e. the specialization of Categories,
Definition 4.2.15 to the functor category from the preorder `I` to `ModuleCat R`. Its primitive
data are the component morphisms `Φ.app i : M.obj i ⟶ N.obj i`; compatibility with transition maps
is derived from naturality. -/
#check (M ⟶ N)

/-- Companion bridge: the components of a morphism of module systems commute with the transition
maps. This is the naturality square of `Φ` specialized to the unique morphism `homOfLE h : i ⟶ j`
in the preorder category `I`. -/
-- Proof sketch: unfold `CommSq` and apply the naturality identity of the natural transformation
-- `Φ` at the preorder morphism `homOfLE h`.
theorem module_system_hom_naturality
    (Φ : M ⟶ N) {i j : I} (h : i ≤ j) :
    CommSq (M.map (homOfLE h)) (Φ.app i) (Φ.app j) (N.map (homOfLE h)) := sorry

end

end CategoryTheory

/-! ### Lemma_10_8_7 (from Chap10) -/
open CategoryTheory CategoryTheory.Limits

universe u v

namespace CategoryTheory

section

variable {R : Type u} [Ring R]
variable {I : Type v} [Preorder I]
variable {M N : I ⥤ ModuleCat R} [HasColimit M] [HasColimit N]
variable (Φ : M ⟶ N)

/- Lemma 10.8.7 is a `bridge/view` item in the colimit-of-module-systems domain: a morphism of
systems `Φ : M ⟶ N` over the same preordered set induces the canonical morphism on direct limits.
The owner abstraction is the colimit functor, so the source-facing specialization is the induced
map `colim.map Φ`, while the Chapter 4 theorem supplies its universal-property characterization. -/
#check (colim.map Φ : colimit M ⟶ colimit N)

/- Companion recall: the Chapter 4 owner theorem specializes to the uniqueness statement for the
induced map on colimits of module systems over the same preorder. -/
#check (show ∃! θ : colimit M ⟶ colimit N,
    ∀ i : I, colimit.ι M i ≫ θ = Φ.app i ≫ colimit.ι N i from
  by
    refine ⟨colim.map Φ, ?_, ?_⟩
    · intro i
      exact colimit.ι_map Φ i
    · intro θ hθ
      refine colimit.hom_ext (fun i ↦ ?_)
      calc
        colimit.ι M i ≫ θ = Φ.app i ≫ colimit.ι N i := hθ i
        _ = colimit.ι M i ≫ colim.map Φ := (colimit.ι_map Φ i).symm)

end

end CategoryTheory

/-! ### Lemma_10_8_8 (from Chap10) -/
open CategoryTheory CategoryTheory.Limits
open ShortComplex

universe u v

noncomputable section

section

variable {R : Type u} [Ring R]
variable {I : Type v} [Preorder I]
variable {L M N : I ⥤ ModuleCat R}
variable {φ : L ⟶ M} {ψ : M ⟶ N}

-- Proof sketch: use `NatTrans.ext` and check equality objectwise; the hypothesis says exactly that
-- each component of `φ ≫ ψ` is zero.
private theorem module_system_comp_eq_zero
    (hcomp : ∀ i : I, φ.app i ≫ ψ.app i = 0) :
    φ ≫ ψ = 0 := by
  -- Check the composite natural transformation objectwise, where the hypothesis gives the vanishing.
  ext i x
  change ((φ.app i ≫ ψ.app i).hom) x = 0
  simpa using LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (hcomp i)) x

/-- The short complex in the functor category attached to the composable system
`L ⟶ M ⟶ N`. This is the owner object from which the stagewise short complexes and their
homology are derived. -/
noncomputable def module_system_shortComplex
    (hcomp : ∀ i : I, φ.app i ≫ ψ.app i = 0) :
    ShortComplex (I ⥤ ModuleCat R) :=
  .mk φ ψ (module_system_comp_eq_zero hcomp)

/-- Lemma 10.8.8 (1): if each stage `L_i ⟶ M_i ⟶ N_i` is a complex, then their homology modules
assemble into a system over `I`; in the directed case this is the system from the statement of
the lemma. -/
noncomputable def module_system_homology
    (hcomp : ∀ i : I, φ.app i ≫ ψ.app i = 0) :
    I ⥤ ModuleCat R :=
  (ShortComplex.functorEquivalence I (ModuleCat R)).functor.obj
      (module_system_shortComplex hcomp) ⋙
    homologyFunctor (ModuleCat R)

-- Proof sketch: first rewrite `colim.map φ ≫ colim.map ψ` as `colim.map (φ ≫ ψ)` using
-- `colim.map_comp`, then substitute the vanishing natural transformation from
-- `module_system_comp_eq_zero`.
/-- Lemma 10.8.8 (2): the induced sequence on colimits
`colim L_i ⟶ colim M_i ⟶ colim N_i` is again a complex. -/
theorem colimit_module_system_isComplex
    (hcomp : ∀ i : I, φ.app i ≫ ψ.app i = 0) :
    colim.map φ ≫ colim.map ψ = 0 := by
  have h :=
    congrArg (fun α ↦ colim.map α)
      (module_system_comp_eq_zero hcomp)
  simpa only [Functor.map_comp, Functor.map_zero] using h

/-- The canonical comparison morphism from the colimit of the stagewise homology system to the
homology of the colimit short complex attached to `L ⟶ M ⟶ N`. -/
noncomputable def module_system_homology_comparison
    (hcomp : ∀ i : I, φ.app i ≫ ψ.app i = 0) :=
  colimit.post
    ((ShortComplex.functorEquivalence I (ModuleCat R)).functor.obj
      (module_system_shortComplex hcomp))
    (homologyFunctor (ModuleCat R))

/-- Helper for Lemma 10.8.8: the transition maps in the stagewise homology system are literally
the homology maps induced by the corresponding morphisms of stage short complexes. -/
@[simp]
theorem module_system_homology_map_eq
    (hcomp : ∀ i : I, φ.app i ≫ ψ.app i = 0) {i j : I} (f : i ⟶ j) :
    (module_system_homology (R := R) (I := I) (L := L) (M := M) (N := N) hcomp).map f =
      (homologyFunctor (ModuleCat R)).map
        ((module_system_shortComplex hcomp).mapNatTrans
          ((evaluation I (ModuleCat R)).map f)) := by
  rfl

/-- Helper for Lemma 10.8.8: the universal stage map `X_i ⟶ colim X` is natural in the diagram
`X`. -/
private theorem evaluation_to_colim_naturality
    (i : I) {F G : I ⥤ ModuleCat R} (α : F ⟶ G) :
    α.app i ≫ colimit.ι G i = colimit.ι F i ≫ colim.map α := by
  simpa using (colimit.ι_map α i).symm

/-- Helper for Lemma 10.8.8: the natural transformation from evaluation at `i` to the colimit
functor whose component on `F` is the canonical map `F.obj i ⟶ colimit F`. -/
noncomputable def evaluation_to_colim
    (i : I) :
    (evaluation I (ModuleCat R)).obj i ⟶ colim (J := I) (C := ModuleCat R) where
  app F := colimit.ι F i
  naturality _ _ α := evaluation_to_colim_naturality (R := R) (I := I) i α

/-- Helper for Lemma 10.8.8: the colimit of an empty module diagram is a zero object. -/
private theorem module_colimit_isZero_of_isEmpty
    [IsEmpty I] (F : I ⥤ ModuleCat R) :
    IsZero (colimit F : ModuleCat R) := by
  -- Compare the empty colimit with the zero module, which is also initial in `ModuleCat`.
  have hinitial : IsInitial (colimit F : ModuleCat R) :=
    (isColimitEquivIsInitialOfIsEmpty (ModuleCat R) (colimit.cocone F))
      (colimit.isColimit F)
  have hzeroModule : IsZero (ModuleCat.of R PUnit) :=
    ModuleCat.isZero_of_subsingleton (ModuleCat.of R PUnit)
  let e : (colimit F : ModuleCat R) ≅ ModuleCat.of R PUnit :=
    hinitial.coconePointUniqueUpToIso hzeroModule.isInitial
  exact IsZero.of_iso hzeroModule e

/-- Helper for Lemma 10.8.8: the categorical colimit of the stage short-complex diagram agrees
with the short complex obtained by taking colimits componentwise. -/
noncomputable def shortComplex_colimit_iso_map_colim
    (S : ShortComplex (I ⥤ ModuleCat R)) :
    colimit ((ShortComplex.functorEquivalence I (ModuleCat R)).functor.obj S) ≅
      S.map (colim (J := I) (C := ModuleCat R)) :=
  IsColimit.coconePointUniqueUpToIso
    (colimit.isColimit ((ShortComplex.functorEquivalence I (ModuleCat R)).functor.obj S))
    (ShortComplex.isColimitColimitCocone
      ((ShortComplex.functorEquivalence I (ModuleCat R)).functor.obj S))

/-- Helper for Lemma 10.8.8: the comparison isomorphism from the categorical colimit to the
componentwise colimit short complex matches the canonical cocone legs. -/
theorem shortComplex_colimit_iso_map_colim_ι
    (S : ShortComplex (I ⥤ ModuleCat R)) (i : I) :
    colimit.ι ((ShortComplex.functorEquivalence I (ModuleCat R)).functor.obj S) i ≫
        (shortComplex_colimit_iso_map_colim (R := R) (I := I) S).hom =
      (ShortComplex.colimitCocone
        ((ShortComplex.functorEquivalence I (ModuleCat R)).functor.obj S)).ι.app i := by
  -- Both cocones are colimiting, so the unique comparison iso intertwines the cocone maps.
  exact
    IsColimit.comp_coconePointUniqueUpToIso_hom
      (colimit.isColimit ((ShortComplex.functorEquivalence I (ModuleCat R)).functor.obj S))
      (ShortComplex.isColimitColimitCocone
        ((ShortComplex.functorEquivalence I (ModuleCat R)).functor.obj S))
      i

/-- Helper for Lemma 10.8.8: the stage cocone map into the pointwise-colimit short complex is the
map induced by the natural transformation `evaluation i ⟶ colim`. -/
@[simp]
theorem shortComplex_colimitCocone_ι_eq_mapNatTrans_colimit_ι
    (S : ShortComplex (I ⥤ ModuleCat R)) (i : I) :
    (ShortComplex.colimitCocone
      ((ShortComplex.functorEquivalence I (ModuleCat R)).functor.obj S)).ι.app i =
      S.mapNatTrans (evaluation_to_colim (R := R) (I := I) i) := by
  -- This is the componentwise definition of `ShortComplex.colimitCocone`.
  ext <;> rfl

variable [IsDirectedOrder I]

/-- Helper for Lemma 10.8.8: on the `i`-th cocone leg, the comparison map followed by the
transport to the pointwise-colimit short complex is the homology map induced by the stage-to-
colimit morphism of short complexes. This is the first source-faithful bridge from the abstract
comparison map to the representative chase on stages. -/
theorem module_system_homology_comparison_comp_pointwise_colimit_ι
    (hcomp : ∀ i : I, φ.app i ≫ ψ.app i = 0) (i : I) :
    colimit.ι (module_system_homology hcomp) i ≫
    module_system_homology_comparison hcomp ≫
        (homologyFunctor (ModuleCat R)).map
          (shortComplex_colimit_iso_map_colim (R := R) (I := I)
            (module_system_shortComplex hcomp)).hom =
      (homologyFunctor (ModuleCat R)).map
        ((module_system_shortComplex hcomp).mapNatTrans
          (evaluation_to_colim (R := R) (I := I) i)) := by
  -- Expand the universal comparison on the `i`-th cocone leg, then rewrite the short-complex
  -- cocone map into the pointwise colimit by the explicit `evaluation_to_colim` morphism.
  dsimp [module_system_homology, module_system_homology_comparison]
  let F :=
    ((ShortComplex.functorEquivalence I (ModuleCat R)).functor.obj
      (module_system_shortComplex hcomp))
  have hpost :
      colimit.ι (F ⋙ homologyFunctor (ModuleCat R)) i ≫
            colimit.post F (homologyFunctor (ModuleCat R)) ≫
          homologyMap
            (shortComplex_colimit_iso_map_colim (R := R) (I := I)
              (module_system_shortComplex hcomp)).hom =
        homologyMap
          (colimit.ι F i ≫
            (shortComplex_colimit_iso_map_colim (R := R) (I := I)
              (module_system_shortComplex hcomp)).hom) := by
    simpa [← Functor.map_comp] using
      congrArg
        (fun ζ ↦ ζ ≫
          homologyMap
            (shortComplex_colimit_iso_map_colim (R := R) (I := I)
              (module_system_shortComplex hcomp)).hom)
        (colimit.ι_post (F := F) (G := homologyFunctor (ModuleCat R)) i)
  have hpost' :
      colimit.ι
            (((ShortComplex.functorEquivalence I (ModuleCat R)).functor.obj
              (module_system_shortComplex hcomp)) ⋙ homologyFunctor (ModuleCat R))
            i ≫
          colimit.post
            (((ShortComplex.functorEquivalence I (ModuleCat R)).functor.obj
              (module_system_shortComplex hcomp)))
            (homologyFunctor (ModuleCat R)) ≫
            homologyMap
              (shortComplex_colimit_iso_map_colim (R := R) (I := I)
                (module_system_shortComplex hcomp)).hom =
        homologyMap
          (colimit.ι
              (((ShortComplex.functorEquivalence I (ModuleCat R)).functor.obj
                (module_system_shortComplex hcomp)))
              i ≫
            (shortComplex_colimit_iso_map_colim (R := R) (I := I)
              (module_system_shortComplex hcomp)).hom) := by
    simpa [F] using hpost
  refine hpost'.trans ?_
  congr 1
  rw [shortComplex_colimit_iso_map_colim_ι,
    shortComplex_colimitCocone_ι_eq_mapNatTrans_colimit_ι]

/-- Helper for Lemma 10.8.8: in the nonempty directed case, the homology comparison morphism is
an isomorphism. -/
theorem module_system_homology_comparison_isIso_of_nonempty
    [Nonempty I]
    (hcomp : ∀ i : I, φ.app i ≫ ψ.app i = 0) :
    IsIso (module_system_homology_comparison hcomp) := by
  -- Route correction: the preserved-homology route asked for a global exactness instance that the
  -- source proof never uses. The remaining work is the source-faithful direct-limit chase: prove
  -- surjectivity and injectivity on representatives using Lemma 10.8.3 and Lemma 10.8.4, starting
  -- from `module_system_homology_comparison_comp_pointwise_colimit_ι`.
  -- TODO: transport the target through `ShortComplex.moduleCatHomologyIso`, identify the image of
  -- a stage class with the class of `colimit.ι M i m`, and finish by the explicit representative
  -- chase from the natural-language proof.
  sorry

/-- Helper for Lemma 10.8.8: in the empty-index case, both sides of the comparison are zero
modules, so the comparison morphism is an isomorphism. -/
theorem module_system_homology_comparison_isIso_of_isEmpty
    [IsEmpty I]
    (hcomp : ∀ i : I, φ.app i ≫ ψ.app i = 0) :
    IsIso (module_system_homology_comparison hcomp) := by
  -- The source is the colimit of an empty diagram of homology modules, hence zero.
  let hsource : IsZero (colimit (module_system_homology hcomp) : ModuleCat R) :=
    module_colimit_isZero_of_isEmpty
      (R := R) (I := I) (F := module_system_homology hcomp)
  -- The pointwise-colimit short complex has zero middle object, so its homology is zero.
  let Sinf := (module_system_shortComplex hcomp).map (colim (J := I) (C := ModuleCat R))
  have hpointwise : IsZero Sinf.homology := by
    -- The middle module is `colimit M`, which vanishes because the index category is empty.
    exact ShortComplex.isZero_homology_of_isZero_X₂
      (S := Sinf)
      (module_colimit_isZero_of_isEmpty (R := R) (I := I) (F := M))
  -- Transport that zero object back across the canonical iso from the categorical colimit short
  -- complex to the pointwise-colimit short complex.
  let htarget :
      IsZero
        (((homologyFunctor (ModuleCat R)).obj
          (colimit ((ShortComplex.functorEquivalence I (ModuleCat R)).functor.obj
            (module_system_shortComplex hcomp)))) : ModuleCat R) :=
    IsZero.of_iso hpointwise
      ((homologyFunctor (ModuleCat R)).mapIso
        (shortComplex_colimit_iso_map_colim (R := R) (I := I)
          (module_system_shortComplex hcomp)))
  -- Any morphism between zero objects is automatically an isomorphism.
  exact IsZero.isIso hsource htarget (module_system_homology_comparison hcomp)

/-- Lemma 10.8.8 (3): the canonical comparison morphism from the colimit of the stagewise homology
modules `H_i` to the homology of the colimit complex is an isomorphism. This formalizes the
textbook equality `H = colim_i H_i`. -/
theorem module_system_homology_comparison_isIso
    (hcomp : ∀ i : I, φ.app i ≫ ψ.app i = 0) :
    IsIso (module_system_homology_comparison hcomp) := by
  -- Route correction: compare the categorical colimit short complex with the pointwise colimit
  -- short complex, then dispatch to the standard `mapHomologyIso` argument in the nonempty case.
  rcases isEmpty_or_nonempty I with hI | hI
  · letI : IsEmpty I := hI
    exact module_system_homology_comparison_isIso_of_isEmpty
      (R := R) (I := I) (L := L) (M := M) (N := N) hcomp
  · letI : Nonempty I := hI
    exact module_system_homology_comparison_isIso_of_nonempty
      (R := R) (I := I) (L := L) (M := M) (N := N) hcomp

noncomputable instance (hcomp : ∀ i : I, φ.app i ≫ ψ.app i = 0) :
    IsIso (module_system_homology_comparison hcomp) :=
  module_system_homology_comparison_isIso hcomp

end

/-! ### Example_10_8_9 (from Chap10) -/
open CategoryTheory
open CategoryTheory.Limits
open scoped ZeroObject

/-
Lemma 10.8.8 (1): for a directed system of complexes of `R`-modules, the stagewise homology
modules form a system over the directed set. This is formalized by `module_system_homology`.
-/
recall module_system_homology

/- Lemma 10.8.8 (2): the induced sequence on colimits is again a complex. -/
recall colimit_module_system_isComplex

/- Lemma 10.8.8 (3): the canonical comparison from the colimit of the stagewise homology modules
to the homology of the colimit complex is an isomorphism. -/
recall module_system_homology_comparison_isIso

noncomputable section

/-- The zero map `0 → ℤ` used at the source vertex of the counterexample span. -/
private abbrev forkZeroToInt : PUnit →ₗ[ℤ] ℤ :=
  0

/-- The identity map `ℤ → ℤ` used at the target vertices of the counterexample span. -/
private abbrev forkIntId : ℤ →ₗ[ℤ] ℤ :=
  LinearMap.id

/-- The source system `(0, \mathbf{Z}, \mathbf{Z}, 0, 0)` on the fork-shaped preorder used in
Example 10.8.9, written as the canonical walking-span diagram. -/
def forkColimitExactnessSource : WalkingSpan ⥤ ModuleCat ℤ :=
  span (ModuleCat.ofHom forkZeroToInt) (ModuleCat.ofHom forkZeroToInt)

/-- The constant target system `(\mathbf{Z}, \mathbf{Z}, \mathbf{Z}, 1, 1)` on the fork-shaped
preorder used in Example 10.8.9. -/
def forkColimitExactnessTarget : WalkingSpan ⥤ ModuleCat ℤ :=
  span (ModuleCat.ofHom forkIntId) (ModuleCat.ofHom forkIntId)

private instance : Subsingleton ↑(forkColimitExactnessSource.obj WalkingSpan.zero) := by
  change Subsingleton PUnit
  infer_instance

/-- The morphism of systems
`(0, \mathbf{Z}, \mathbf{Z}, 0, 0) → (\mathbf{Z}, \mathbf{Z}, \mathbf{Z}, 1, 1)` from
Example 10.8.9. -/
def forkColimitExactnessHom : forkColimitExactnessSource ⟶ forkColimitExactnessTarget :=
  spanHomMk 0 (𝟙 _) (𝟙 _)

private theorem forkColimitExactnessHom_app_mono (i : WalkingSpan) :
    Mono (forkColimitExactnessHom.app i) := by
  rcases i with _ | (_ | _)
  · exact (ModuleCat.mono_iff_injective _).2 <| by
      intro x y h
      exact Subsingleton.elim _ _
  · simpa [forkColimitExactnessSource, forkColimitExactnessTarget, forkColimitExactnessHom,
      forkZeroToInt, forkIntId] using
      (show Mono (𝟙 (ModuleCat.of ℤ ℤ)) from inferInstance)
  · simpa [forkColimitExactnessSource, forkColimitExactnessTarget, forkColimitExactnessHom,
      forkZeroToInt, forkIntId] using
      (show Mono (𝟙 (ModuleCat.of ℤ ℤ)) from inferInstance)

private theorem forkColimitExactnessHom_colimit_not_injective :
    ¬ Function.Injective (colim.map forkColimitExactnessHom).hom := sorry

private theorem forkColimitExactnessHom_colimit_not_mono :
    ¬ Mono (colim.map forkColimitExactnessHom) := by
  intro h
  exact forkColimitExactnessHom_colimit_not_injective ((ModuleCat.mono_iff_injective _).1 h)

private theorem forkColimitExactnessHom_mono : Mono forkColimitExactnessHom := by
  rw [NatTrans.mono_iff_mono_app]
  exact forkColimitExactnessHom_app_mono

/-- Example 10.8.9: on the fork-shaped preorder `a < b`, `a < c`, the morphism of systems
`(0, \mathbf{Z}, \mathbf{Z}, 0, 0) → (\mathbf{Z}, \mathbf{Z}, \mathbf{Z}, 1, 1)` is a
monomorphism, but the induced map on colimits is not. Hence the result of Lemma 10.8.8 is false
for general systems. -/
theorem fork_colimit_counterexample_to_exactness :
    Mono forkColimitExactnessHom ∧ ¬ Mono (colim.map forkColimitExactnessHom) := by
  constructor
  · exact forkColimitExactnessHom_mono
  · exact forkColimitExactnessHom_colimit_not_mono

/-- Textbook injectivity formulation of Example 10.8.9. -/
theorem fork_colimit_counterexample_to_exactness_injective :
    (∀ i : WalkingSpan, Function.Injective (forkColimitExactnessHom.app i).hom) ∧
      ¬ Function.Injective (colim.map forkColimitExactnessHom).hom := by
  refine ⟨?_, forkColimitExactnessHom_colimit_not_injective⟩
  intro i
  exact (ModuleCat.mono_iff_injective _).1 (forkColimitExactnessHom_app_mono i)

end

/-! ### Lemma_10_8_10 (from Chap10) -/
open CategoryTheory CategoryTheory.Limits

universe u v

noncomputable section

section

variable {I : Type u} [Category.{v} I] [Small.{v} I]
variable [HasSpanCocones I]

/-- Helper for Lemma 10.8.10: the quotient indexing the connected components of a `v`-small
category is itself `v`-small. -/
private instance connected_components_small :
    Small.{v} (CategoryTheory.ConnectedComponents I) := by
  dsimp [CategoryTheory.ConnectedComponents]
  infer_instance

-- Proof sketch: the source statement is about abelian groups, whose owner category in mathlib is
-- `AddCommGrpCat`. By `hasExactColimitsOfShape_of_preservesMono`, it is enough to show that
-- `colim : (I ⥤ AddCommGrpCat) ⥤ AddCommGrpCat` preserves monomorphisms. Decompose `I` into
-- connected components using Lemma `4.19.8`, each of which is filtered, apply filtered exactness
-- in `AddCommGrpCat` componentwise, and reassemble the result using exactness of coproducts.

/-- Helper for Lemma 10.8.10: the canonical legs from a decomposed diagram into the coproduct of
the componentwise colimits are natural in the decomposed index. -/
private lemma decomposed_component_cocone_naturality
    (F : CategoryTheory.Decomposed I ⥤ AddCommGrpCat)
    {X Y : CategoryTheory.Decomposed I} (f : X ⟶ Y) :
    F.map f ≫ colimit.ι (CategoryTheory.inclusion Y.1 ⋙ F) Y.2 ≫
          Limits.Sigma.ι
            (fun j : CategoryTheory.ConnectedComponents I =>
              colimit (CategoryTheory.inclusion j ⋙ F))
            Y.1 =
      (colimit.ι (CategoryTheory.inclusion X.1 ⋙ F) X.2 ≫
          Limits.Sigma.ι
            (fun j : CategoryTheory.ConnectedComponents I =>
              colimit (CategoryTheory.inclusion j ⋙ F))
            X.1) ≫
        ((Functor.const (CategoryTheory.Decomposed I)).obj
          (∐ fun j : CategoryTheory.ConnectedComponents I =>
            colimit (CategoryTheory.inclusion j ⋙ F))).map f := by
  -- Destruct the sigma-category morphism so the goal becomes the `colimit.w` relation on the
  -- relevant connected component, followed by the fixed coproduct injection.
  rcases X with ⟨j, X⟩
  rcases Y with ⟨_, Y⟩
  rcases f with ⟨f⟩
  simpa [Functor.const_obj_map] using
    (colimit.w_assoc (F := CategoryTheory.inclusion j ⋙ F) f
      (Limits.Sigma.ι
        (fun j : CategoryTheory.ConnectedComponents I =>
          colimit (CategoryTheory.inclusion j ⋙ F))
        j))

/-- Helper for Lemma 10.8.10: the chosen `Sigma.desc` map agrees with the legs of any cocone over
the decomposed diagram after restricting to one connected component. -/
private lemma decomposed_component_cocone_desc_fac
    (F : CategoryTheory.Decomposed I ⥤ AddCommGrpCat) (s : Cocone F)
    (j : CategoryTheory.ConnectedComponents I) (X : j.Component) :
    colimit.ι (CategoryTheory.inclusion j ⋙ F) X ≫
        Limits.Sigma.ι
          (fun k : CategoryTheory.ConnectedComponents I =>
            colimit (CategoryTheory.inclusion k ⋙ F))
          j ≫
        Limits.Sigma.desc
        (fun k : CategoryTheory.ConnectedComponents I =>
          colimit.desc (CategoryTheory.inclusion k ⋙ F)
            (Cocone.whisker (CategoryTheory.inclusion k) s)) =
        s.ι.app ⟨j, X⟩ := by
  -- First descend out of the coproduct of componentwise colimits, then out of the colimit on the
  -- chosen connected component.
  rw [Limits.Sigma.ι_desc]
  simpa using colimit.ι_desc (Cocone.whisker (CategoryTheory.inclusion j) s) X

/-- Helper for Lemma 10.8.10: a diagram on the decomposed category has a canonical cocone whose
vertex is the coproduct of the colimits over the connected components. -/
private def decomposed_component_cocone
    (F : CategoryTheory.Decomposed I ⥤ AddCommGrpCat) :
    Cocone F where
  pt := ∐ fun j : CategoryTheory.ConnectedComponents I =>
    colimit (CategoryTheory.inclusion j ⋙ F)
  ι :=
    { app := fun X =>
        colimit.ι (CategoryTheory.inclusion X.1 ⋙ F) X.2 ≫
          Limits.Sigma.ι
            (fun j : CategoryTheory.ConnectedComponents I =>
              colimit (CategoryTheory.inclusion j ⋙ F))
            X.1
      naturality := fun _ _ f => decomposed_component_cocone_naturality F f }

/-- Helper for Lemma 10.8.10: the coproduct of the componentwise colimits is a colimit of the
whole decomposed diagram. -/
private def decomposed_component_cocone_isColimit
    (F : CategoryTheory.Decomposed I ⥤ AddCommGrpCat) :
    IsColimit (decomposed_component_cocone F) := by
  -- Route correction: define the desc morphism by assembling the componentwise colimit desc maps,
  -- then prove uniqueness by extensionality on the coproduct and on each component colimit.
  refine
    { desc := fun s =>
        Limits.Sigma.desc
          (fun j : CategoryTheory.ConnectedComponents I =>
            colimit.desc (CategoryTheory.inclusion j ⋙ F)
              (Cocone.whisker (CategoryTheory.inclusion j) s))
      fac := ?_
      uniq := ?_ }
  · intro s X
    cases X with
    | mk j X =>
        simpa [decomposed_component_cocone] using decomposed_component_cocone_desc_fac F s j X
  · intro s m hm
    apply Limits.Sigma.hom_ext
    intro j
    apply colimit.hom_ext
    intro X
    simpa [decomposed_component_cocone, Category.assoc] using
      (hm ⟨j, X⟩).trans (decomposed_component_cocone_desc_fac F s j X).symm

/-- Helper for Lemma 10.8.10: the colimit of a decomposed diagram is canonically the coproduct of
the colimits over its connected components. -/
private def decomposed_colimit_iso_component_coproduct
    (F : CategoryTheory.Decomposed I ⥤ AddCommGrpCat) :
    (∐ fun j : CategoryTheory.ConnectedComponents I =>
      colimit (CategoryTheory.inclusion j ⋙ F)) ≅ colimit F :=
  IsColimit.coconePointUniqueUpToIso
    (decomposed_component_cocone_isColimit F) (colimit.isColimit F)

/-- Helper for Lemma 10.8.10: under the componentwise colimit decomposition, the canonical
inclusion of an object in the decomposed diagram is the component colimit leg followed by the
corresponding coproduct injection. -/
@[reassoc (attr := simp)]
private lemma decomposed_colimit_iso_component_coproduct_ι
    (F : CategoryTheory.Decomposed I ⥤ AddCommGrpCat)
    (j : CategoryTheory.ConnectedComponents I) (X : j.Component) :
    colimit.ι (CategoryTheory.inclusion j ⋙ F) X ≫
        Limits.Sigma.ι
          (fun k : CategoryTheory.ConnectedComponents I =>
            colimit (CategoryTheory.inclusion k ⋙ F))
          j ≫
      (decomposed_colimit_iso_component_coproduct F).hom =
        colimit.ι F ⟨j, X⟩ := by
  -- The comparison isomorphism between the two colimit cocones is determined by its effect on
  -- each cocone leg.
  simpa [decomposed_component_cocone, decomposed_colimit_iso_component_coproduct] using
    IsColimit.comp_coconePointUniqueUpToIso_hom
      (decomposed_component_cocone_isColimit F) (colimit.isColimit F) ⟨j, X⟩

/-- Helper for Lemma 10.8.10: the inverse of the componentwise colimit decomposition sends the
canonical colimit leg of the decomposed diagram to the matching coproduct summand. -/
@[reassoc (attr := simp)]
private lemma decomposed_colimit_iso_component_coproduct_inv_ι
    (F : CategoryTheory.Decomposed I ⥤ AddCommGrpCat)
    (j : CategoryTheory.ConnectedComponents I) (X : j.Component) :
    colimit.ι F ⟨j, X⟩ ≫ (decomposed_colimit_iso_component_coproduct F).inv =
      colimit.ι (CategoryTheory.inclusion j ⋙ F) X ≫
        Limits.Sigma.ι
          (fun k : CategoryTheory.ConnectedComponents I =>
            colimit (CategoryTheory.inclusion k ⋙ F))
          j := by
  -- Postcompose the forward leg formula with the inverse comparison isomorphism and cancel the
  -- resulting isomorphism.
  apply (cancel_mono ((decomposed_colimit_iso_component_coproduct F).hom)).1
  -- After postcomposing with the comparison isomorphism, both sides become the forward leg
  -- formula proved above.
  simp only [Category.assoc]
  simpa using (decomposed_colimit_iso_component_coproduct_ι F j X).symm

/-- Helper for Lemma 10.8.10: postcomposing the inverse decomposition leg with the fixed coproduct
comparison map preserves the componentwise leg formula. -/
private lemma decomposed_colimit_iso_component_coproduct_inv_postcompose
    {F G : CategoryTheory.Decomposed I ⥤ AddCommGrpCat} (α : F ⟶ G)
    (j : CategoryTheory.ConnectedComponents I) (X : j.Component) :
    colimit.ι F ⟨j, X⟩ ≫ (decomposed_colimit_iso_component_coproduct F).inv ≫
        (Limits.Sigma.map
          (fun j : CategoryTheory.ConnectedComponents I =>
            colim.map (Functor.whiskerLeft (CategoryTheory.inclusion j) α)) ≫
          (decomposed_colimit_iso_component_coproduct G).hom) =
      (colimit.ι (CategoryTheory.inclusion j ⋙ F) X ≫
          Limits.Sigma.ι
            (fun k : CategoryTheory.ConnectedComponents I =>
              colimit (CategoryTheory.inclusion k ⋙ F))
            j) ≫
        (Limits.Sigma.map
          (fun j : CategoryTheory.ConnectedComponents I =>
            colim.map (Functor.whiskerLeft (CategoryTheory.inclusion j) α)) ≫
          (decomposed_colimit_iso_component_coproduct G).hom) := by
  -- Freeze the inverse-leg rewrite before entering the coproduct comparison. This isolates the
  -- stable source-faithful transport step needed in the main comparison proof.
  simpa [Category.assoc] using
    congrArg
      (fun k =>
        k ≫
          (Limits.Sigma.map
            (fun j : CategoryTheory.ConnectedComponents I =>
              colim.map (Functor.whiskerLeft (CategoryTheory.inclusion j) α)) ≫
            (decomposed_colimit_iso_component_coproduct G).hom))
      (decomposed_colimit_iso_component_coproduct_inv_ι F j X)

/-- Helper for Lemma 10.8.10: after identifying a decomposed colimit with the coproduct of the
componentwise colimits, precomposing the transported coproduct map with a decomposed colimit leg
recovers the corresponding stagewise map into the target colimit. -/
private lemma decomposed_colim_map_eq_sigma_map_leg
    {F G : CategoryTheory.Decomposed I ⥤ AddCommGrpCat} (α : F ⟶ G)
    (j : CategoryTheory.ConnectedComponents I) (X : j.Component) :
    colimit.ι F ⟨j, X⟩ ≫
        ((decomposed_colimit_iso_component_coproduct F).inv ≫
          Limits.Sigma.map
            (fun k : CategoryTheory.ConnectedComponents I =>
              colim.map (Functor.whiskerLeft (CategoryTheory.inclusion k) α)) ≫
          (decomposed_colimit_iso_component_coproduct G).hom) =
      α.app ⟨j, X⟩ ≫ colimit.ι G ⟨j, X⟩ := by
  -- Route correction: compare at codomain `colim.obj G` directly so the final proof only uses the
  -- fixed decomposition rewrites, not any extra definitional transport.
  rw [decomposed_colimit_iso_component_coproduct_inv_postcompose]
  -- The coproduct comparison now reduces to the componentwise colimit map relation.
  calc
    colimit.ι (CategoryTheory.inclusion j ⋙ F) X ≫
        Limits.Sigma.ι
          (fun k : CategoryTheory.ConnectedComponents I =>
            colimit (CategoryTheory.inclusion k ⋙ F))
          j ≫
        Limits.Sigma.map
          (fun k : CategoryTheory.ConnectedComponents I =>
            colim.map (Functor.whiskerLeft (CategoryTheory.inclusion k) α)) ≫
        (decomposed_colimit_iso_component_coproduct G).hom =
      colimit.ι (CategoryTheory.inclusion j ⋙ F) X ≫
        colim.map (Functor.whiskerLeft (CategoryTheory.inclusion j) α) ≫
        Limits.Sigma.ι
          (fun k : CategoryTheory.ConnectedComponents I =>
            colimit (CategoryTheory.inclusion k ⋙ G))
          j ≫
        (decomposed_colimit_iso_component_coproduct G).hom := by
          simpa [Category.assoc] using
            (Limits.Sigma.ι_map_assoc
              (fun k : CategoryTheory.ConnectedComponents I =>
                colim.map (Functor.whiskerLeft (CategoryTheory.inclusion k) α))
              j
              (decomposed_colimit_iso_component_coproduct G).hom)
    _ =
      (Functor.whiskerLeft (CategoryTheory.inclusion j) α).app X ≫
        colimit.ι (CategoryTheory.inclusion j ⋙ G) X ≫
        Limits.Sigma.ι
          (fun k : CategoryTheory.ConnectedComponents I =>
            colimit (CategoryTheory.inclusion k ⋙ G))
          j ≫
        (decomposed_colimit_iso_component_coproduct G).hom := by
          simpa [Category.assoc] using
            congrArg
              (fun k =>
                k ≫
                  Limits.Sigma.ι
                    (fun t : CategoryTheory.ConnectedComponents I =>
                      colimit (CategoryTheory.inclusion t ⋙ G))
                    j ≫
                  (decomposed_colimit_iso_component_coproduct G).hom)
              (ι_colimMap (Functor.whiskerLeft (CategoryTheory.inclusion j) α) X)
    _ = α.app ⟨j, X⟩ ≫ colimit.ι G ⟨j, X⟩ := by
          simpa [Functor.whiskerLeft_app, Category.assoc] using
            congrArg
              (fun k => α.app ⟨j, X⟩ ≫ k)
              (decomposed_colimit_iso_component_coproduct_ι G j X)

/-- Helper for Lemma 10.8.10: after identifying a decomposed colimit with the coproduct of the
componentwise colimits, the induced map on colimits is the coproduct of the componentwise colimit
maps. -/
private lemma decomposed_colim_map_eq_sigma_map
    {F G : CategoryTheory.Decomposed I ⥤ AddCommGrpCat} (α : F ⟶ G) :
    colim.map α =
      (decomposed_colimit_iso_component_coproduct F).inv ≫
        Limits.Sigma.map
          (fun j : CategoryTheory.ConnectedComponents I =>
            colim.map (Functor.whiskerLeft (CategoryTheory.inclusion j) α)) ≫
        (decomposed_colimit_iso_component_coproduct G).hom := by
  -- Route correction: the only remaining work is to compare both candidates on every colimit leg
  -- and reuse the dedicated codomain-stable leg lemma proved just above.
  apply colimit.hom_ext
  intro X
  cases X with
  | mk j X =>
      simpa using (decomposed_colim_map_eq_sigma_map_leg α j X).symm

/-- Helper for Lemma 10.8.10: each connected component inherits exact colimits from AB5 exactness
of filtered colimits in `AddCommGrpCat`. -/
private lemma component_exact_colimits_of_shape
    (hMap : ∀ ⦃X Y : I⦄ (f g : X ⟶ Y), ∃ (Z : I) (h : Y ⟶ Z), f ≫ h = g ≫ h)
    (j : CategoryTheory.ConnectedComponents I) :
    HasExactColimitsOfShape j.Component AddCommGrpCat.{v} := by
  -- Replace the connected component by a final directed-poset model, then invoke exactness of
  -- directed colimits in `AddCommGrpCat` on that small source and push exactness forward.
  letI : IsFiltered j.Component := connected_components_are_filtered hMap j
  letI : EssentiallySmall.{v} j.Component := by infer_instance
  letI : FinallySmall.{v} j.Component :=
    CategoryTheory.finallySmall_of_essentiallySmall (J := j.Component)
  obtain ⟨K, _, _, _, x, hx⟩ := CategoryTheory.exists_final_from_directed (𝓘 := j.Component)
  letI : PartialOrder K := inferInstance
  letI : Nonempty K := inferInstance
  letI : IsDirectedOrder K := inferInstance
  letI : x.Final := hx
  letI : AB5OfSize.{0, v} AddCommGrpCat.{v} := by
    simpa using (AB5OfSize_shrink AddCommGrpCat.{v})
  letI : HasExactColimitsOfShape K AddCommGrpCat.{v} := inferInstance
  exact hasExactColimitsOfShape_of_final AddCommGrpCat.{v} x

/-- Helper for Lemma 10.8.10: exactness of coproducts over connected components is obtained by
shrinking the component index and transporting the AB4 instance back along the discrete
equivalence. -/
private lemma connected_components_discrete_exact_colimits :
    HasExactColimitsOfShape (Discrete (CategoryTheory.ConnectedComponents I))
      AddCommGrpCat.{v} := by
  -- The source proof reduces the remaining exactness step to coproducts indexed by the set of
  -- connected components; we realize that exactness via `AB4OfSize_shrink`.
  letI : AB4OfSize.{v} AddCommGrpCat.{v} := by
    simpa using (AB4OfSize_shrink AddCommGrpCat.{v})
  exact HasExactColimitsOfShape.of_domain_equivalence AddCommGrpCat.{v}
    (Discrete.equivalence (equivShrink.{v} (CategoryTheory.ConnectedComponents I)).symm)

/-- Helper for Lemma 10.8.10: on each connected component, filtered exactness in
`AddCommGrpCat` shows that the colimit map of a monomorphism remains a monomorphism. -/
private lemma component_colim_map_mono
    (hMap : ∀ ⦃X Y : I⦄ (f g : X ⟶ Y), ∃ (Z : I) (h : Y ⟶ Z), f ≫ h = g ≫ h)
    (j : CategoryTheory.ConnectedComponents I)
    {F G : j.Component ⥤ AddCommGrpCat} (β : F ⟶ G) [Mono β] :
    Mono (colim.map β) := by
  -- Insert the exact filtered-colimit instance explicitly, then let the standard exactness-to-mono
  -- bridge prove that the componentwise colimit functor preserves monomorphisms.
  letI : HasExactColimitsOfShape j.Component AddCommGrpCat :=
    by simpa using (component_exact_colimits_of_shape (hMap := hMap) j)
  let hExact :
      ∀ (S : ShortComplex (j.Component ⥤ AddCommGrpCat)), S.Exact →
        (S.map (colim : (j.Component ⥤ AddCommGrpCat) ⥤ AddCommGrpCat)).Exact :=
    fun S hS ↦ by
      -- Read exactness of the colimit functor through the chosen colimit cocones.
      simpa using
        (Limits.colim.exact_mapShortComplex (S := S) hS
          (hc₁ := colimit.isColimit S.X₁)
          (c₂ := colimit.cocone S.X₂) (hc₂ := colimit.isColimit S.X₂)
          (c₃ := colimit.cocone S.X₃) (hc₃ := colimit.isColimit S.X₃)
          (f := colim.map S.f) (g := colim.map S.g)
          (fun X ↦ colimit.ι_map S.f X) (fun X ↦ colimit.ι_map S.g X))
  letI :
      (colim : (j.Component ⥤ AddCommGrpCat) ⥤ AddCommGrpCat).PreservesMonomorphisms :=
    Functor.preservesMonomorphisms_of_map_exact _ hExact
  infer_instance

/-- Helper for Lemma 10.8.10: the coproduct of componentwise monomorphisms in `AddCommGrpCat`
is again a monomorphism. -/
private lemma sigma_map_mono_via_ab4
    {A B : CategoryTheory.ConnectedComponents I → AddCommGrpCat}
    (p : ∀ j : CategoryTheory.ConnectedComponents I, A j ⟶ B j)
    [∀ j, Mono (p j)] :
    Mono (Limits.Sigma.map p) := by
  -- Transport exactness of coproducts to the discrete connected-component index and then apply
  -- the same exactness-to-mono bridge to the discrete-shape colimit functor.
  letI : HasExactColimitsOfShape (Discrete (CategoryTheory.ConnectedComponents I)) AddCommGrpCat :=
    by simpa using (connected_components_discrete_exact_colimits (I := I))
  let hExact :
      ∀ (S : ShortComplex (Discrete (CategoryTheory.ConnectedComponents I) ⥤ AddCommGrpCat)),
        S.Exact →
          (S.map (colim :
            (Discrete (CategoryTheory.ConnectedComponents I) ⥤ AddCommGrpCat) ⥤
              AddCommGrpCat)).Exact :=
    fun S hS ↦ by
      -- Exactness of coproducts is exactness of colimits over the discrete index.
      simpa using
        (Limits.colim.exact_mapShortComplex (S := S) hS
          (hc₁ := colimit.isColimit S.X₁)
          (c₂ := colimit.cocone S.X₂) (hc₂ := colimit.isColimit S.X₂)
          (c₃ := colimit.cocone S.X₃) (hc₃ := colimit.isColimit S.X₃)
          (f := colim.map S.f) (g := colim.map S.g)
          (fun X ↦ colimit.ι_map S.f X) (fun X ↦ colimit.ι_map S.g X))
  letI :
      (colim :
        (Discrete (CategoryTheory.ConnectedComponents I) ⥤ AddCommGrpCat) ⥤
          AddCommGrpCat).PreservesMonomorphisms :=
    Functor.preservesMonomorphisms_of_map_exact _ hExact
  let φ : Discrete (CategoryTheory.ConnectedComponents I) ⥤ AddCommGrpCat :=
    Discrete.functor A
  let ψ : Discrete (CategoryTheory.ConnectedComponents I) ⥤ AddCommGrpCat :=
    Discrete.functor B
  let η : φ ⟶ ψ := Discrete.natTrans fun j => p j.as
  letI : ∀ X, Mono (η.app X) := fun j ↦ by
    change Mono (p j.as)
    infer_instance
  letI : Mono η := by
    exact NatTrans.mono_of_mono_app η
  -- Compute the sigma map as the discrete-shape colimit map between the standard coproduct
  -- cocones.
  exact Limits.colim.map_mono' η
    (Limits.coproductIsCoproduct' φ)
    (Limits.coproductIsCoproduct' ψ)
    (Limits.Sigma.map p)
    (fun j ↦ by simpa [η, φ, ψ] using Limits.Sigma.ι_map p j.as)

/-- Lemma 10.8.10: if the index category `I` satisfies the hypotheses of Categories, Lemma 4.19.8,
then taking colimits of diagrams of abelian groups over `I` is exact. The owner abstraction is the
instance `HasExactColimitsOfShape I AddCommGrpCat`. -/
instance abelian_group_colimits_exact
    (hMap : ∀ ⦃X Y : I⦄ (f g : X ⟶ Y), ∃ (Z : I) (h : Y ⟶ Z), f ≫ h = g ≫ h) :
    HasExactColimitsOfShape I AddCommGrpCat := by
  -- Route correction: keep the source decomposition route, but now the only work is to prove that
  -- the decomposed colimit functor preserves monomorphisms by factoring it through the component
  -- colimits and the coproduct over connected components.
  letI :
      (colim : (CategoryTheory.Decomposed I ⥤ AddCommGrpCat) ⥤ AddCommGrpCat).PreservesMonomorphisms := by
    refine ⟨?_⟩
    intro F G α hα
    have hComponent :
        ∀ j : CategoryTheory.ConnectedComponents I,
          Mono (colim.map (Functor.whiskerLeft (CategoryTheory.inclusion j) α)) := by
      intro j
      letI : ∀ X, Mono ((Functor.whiskerLeft (CategoryTheory.inclusion j) α).app X) := fun X ↦ by
        change Mono (α.app ⟨j, X⟩)
        infer_instance
      letI : Mono (Functor.whiskerLeft (CategoryTheory.inclusion j) α) := by
        exact NatTrans.mono_of_mono_app (Functor.whiskerLeft (CategoryTheory.inclusion j) α)
      exact component_colim_map_mono hMap j (Functor.whiskerLeft (CategoryTheory.inclusion j) α)
    letI :
        ∀ j : CategoryTheory.ConnectedComponents I,
          Mono (colim.map (Functor.whiskerLeft (CategoryTheory.inclusion j) α)) := hComponent
    have hSigma :
        Mono
          (Limits.Sigma.map
            (fun j : CategoryTheory.ConnectedComponents I =>
              colim.map (Functor.whiskerLeft (CategoryTheory.inclusion j) α))) :=
      sigma_map_mono_via_ab4
        (fun j : CategoryTheory.ConnectedComponents I =>
          colim.map (Functor.whiskerLeft (CategoryTheory.inclusion j) α))
    letI :
        Mono
          (Limits.Sigma.map
            (fun j : CategoryTheory.ConnectedComponents I =>
              colim.map (Functor.whiskerLeft (CategoryTheory.inclusion j) α))) := hSigma
    haveI : Mono ((decomposed_colimit_iso_component_coproduct F).inv) := by infer_instance
    have hInvSigma :
        Mono
          ((decomposed_colimit_iso_component_coproduct F).inv ≫
            Limits.Sigma.map
              (fun j : CategoryTheory.ConnectedComponents I =>
                colim.map (Functor.whiskerLeft (CategoryTheory.inclusion j) α))) :=
      by
        constructor
        intro Z u v huv
        apply (cancel_mono ((decomposed_colimit_iso_component_coproduct F).inv)).1
        apply (cancel_mono
          (Limits.Sigma.map
            (fun j : CategoryTheory.ConnectedComponents I =>
              colim.map (Functor.whiskerLeft (CategoryTheory.inclusion j) α)))).1
        simpa [Category.assoc] using huv
    haveI :
        Mono
          ((decomposed_colimit_iso_component_coproduct F).inv ≫
            Limits.Sigma.map
              (fun j : CategoryTheory.ConnectedComponents I =>
                colim.map (Functor.whiskerLeft (CategoryTheory.inclusion j) α))) := hInvSigma
    have hComp :
        Mono
          (((decomposed_colimit_iso_component_coproduct F).inv ≫
              Limits.Sigma.map
                (fun j : CategoryTheory.ConnectedComponents I =>
                  colim.map (Functor.whiskerLeft (CategoryTheory.inclusion j) α))) ≫
            (decomposed_colimit_iso_component_coproduct G).hom) :=
      by
        constructor
        intro Z u v huv
        apply (cancel_mono
          ((decomposed_colimit_iso_component_coproduct F).inv ≫
            Limits.Sigma.map
              (fun j : CategoryTheory.ConnectedComponents I =>
                colim.map (Functor.whiskerLeft (CategoryTheory.inclusion j) α)))).1
        apply (cancel_mono ((decomposed_colimit_iso_component_coproduct G).hom)).1
        simpa [Category.assoc] using huv
    rw [decomposed_colim_map_eq_sigma_map α]
    simpa [Category.assoc] using hComp
  letI : HasExactColimitsOfShape (CategoryTheory.Decomposed I) AddCommGrpCat :=
    hasExactColimitsOfShape_of_preservesMono AddCommGrpCat (CategoryTheory.Decomposed I)
  -- Transport exactness back along the canonical decomposition equivalence.
  exact
    (HasExactColimitsOfShape.of_domain_equivalence
      (C := AddCommGrpCat)
      (J := CategoryTheory.Decomposed I)
      (J' := I)
      (CategoryTheory.decomposedEquiv (J := I)))

end
