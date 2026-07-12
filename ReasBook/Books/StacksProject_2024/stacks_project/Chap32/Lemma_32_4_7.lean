import Mathlib

open CategoryTheory Limits Opposite AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced the affine-transition limit owner
-- `AlgebraicGeometry.nonempty_isColimit_Γ_mapCocone`; for the present item the source-facing
-- statement is the quasi-coherent-module analogue on global sections of pullbacks along the
-- over-category of the distinguished stage.

section

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
variable (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
variable [∀ j : OrderDual I, CompactSpace ↥(D.obj j)]
variable [∀ j : OrderDual I, QuasiSeparatedSpace ↥(D.obj j)]
variable [∀ {j j' : OrderDual I} (f : j ⟶ j'), IsAffineHom (D.map f)]

/-- The underlying type of global sections of a scheme module over the whole scheme. -/
private abbrev moduleGlobalSections {X : Scheme.{u}} (M : X.Modules) : Type u :=
  Γ(M, ⊤)

/-- The global-sections map obtained by first pulling back along `g` and then along `f`. -/
private noncomputable def iteratedPullbackModuleGlobalSectionsMap
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (ℱ : Z.Modules) :
    moduleGlobalSections ((Scheme.Modules.pullback g).obj ℱ) →
      moduleGlobalSections ((Scheme.Modules.pullback (f ≫ g)).obj ℱ) :=
  let η :=
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
      ((Scheme.Modules.pullback g).obj ℱ)).app ⊤
  let e := (Scheme.Modules.pullbackComp f g).hom.app ℱ
  fun s ↦ (e.app ⊤) (cast (by simp) (η s))

/-- An over-category morphism identifies the corresponding iterated pullback module sections with
the direct pullback module sections. -/
private theorem overPullbackModuleGlobalSections_eq
    (i₀ : OrderDual I) (ℱ₀ : (D.obj i₀).Modules)
    {A B : Over i₀} (φ : A ⟶ B) :
    moduleGlobalSections ((Scheme.Modules.pullback (D.map (φ.left ≫ B.hom))).obj ℱ₀) =
      moduleGlobalSections ((Scheme.Modules.pullback (D.map A.hom)).obj ℱ₀) := by
  exact congrArg
    (fun f : A.left ⟶ i₀ ↦ moduleGlobalSections ((Scheme.Modules.pullback (D.map f)).obj ℱ₀))
    (Over.w φ)

/-- The transition map on global sections of pullback modules along a morphism in `Over i₀`. -/
private noncomputable def overPullbackModuleGlobalSectionsMap
    (i₀ : OrderDual I) (ℱ₀ : (D.obj i₀).Modules)
    {A B : Over i₀} (φ : A ⟶ B) :
    moduleGlobalSections ((Scheme.Modules.pullback (D.map B.hom)).obj ℱ₀) →
      moduleGlobalSections ((Scheme.Modules.pullback (D.map A.hom)).obj ℱ₀) :=
  let h :
      moduleGlobalSections ((Scheme.Modules.pullback (D.map φ.left ≫ D.map B.hom)).obj ℱ₀) =
        moduleGlobalSections ((Scheme.Modules.pullback (D.map A.hom)).obj ℱ₀) := by
    trans moduleGlobalSections ((Scheme.Modules.pullback (D.map (φ.left ≫ B.hom))).obj ℱ₀)
    · simp [Functor.map_comp]
    · exact overPullbackModuleGlobalSections_eq D i₀ ℱ₀ φ
  fun s ↦
    cast h (iteratedPullbackModuleGlobalSectionsMap (D.map φ.left) (D.map B.hom) ℱ₀ s)

/-- Identity compatibility for the over-category pullback-module global-sections maps. -/
private theorem overPullbackModuleGlobalSectionsMap_id
    (i₀ : OrderDual I) (ℱ₀ : (D.obj i₀).Modules) (A : Over i₀) :
    overPullbackModuleGlobalSectionsMap D i₀ ℱ₀ (𝟙 A) = id := sorry

/-- Composition compatibility for the over-category pullback-module global-sections maps. -/
private theorem overPullbackModuleGlobalSectionsMap_comp
    (i₀ : OrderDual I) (ℱ₀ : (D.obj i₀).Modules)
    {A B C : Over i₀} (φ : A ⟶ B) (ψ : B ⟶ C) :
    overPullbackModuleGlobalSectionsMap D i₀ ℱ₀ (φ ≫ ψ) =
      overPullbackModuleGlobalSectionsMap D i₀ ℱ₀ φ ∘
        overPullbackModuleGlobalSectionsMap D i₀ ℱ₀ ψ := sorry

/-- The over-category diagram of global sections of the pullback modules `f_a^* \mathcal F_0`. -/
private noncomputable def limitPullbackModuleGlobalSectionsDiagram
    (i₀ : OrderDual I) (ℱ₀ : (D.obj i₀).Modules) :
    (Over i₀)ᵒᵖ ⥤ Type u where
  obj A := moduleGlobalSections ((Scheme.Modules.pullback (D.map A.unop.hom)).obj ℱ₀)
  map φ := overPullbackModuleGlobalSectionsMap D i₀ ℱ₀ φ.unop
  map_id := by
    intro A
    simpa using overPullbackModuleGlobalSectionsMap_id D i₀ ℱ₀ A.unop
  map_comp := by
    intro A B C φ ψ
    simpa using overPullbackModuleGlobalSectionsMap_comp D i₀ ℱ₀ ψ.unop φ.unop

/-- Pulling back to the limit through an object of `Over i₀` agrees with pulling back along the
projection `c.π.app i₀`. -/
private theorem limitPullbackModuleGlobalSections_eq
    (i₀ : OrderDual I) (ℱ₀ : (D.obj i₀).Modules) (A : Over i₀) :
    moduleGlobalSections ((Scheme.Modules.pullback (c.π.app A.left ≫ D.map A.hom)).obj ℱ₀) =
      moduleGlobalSections ((Scheme.Modules.pullback (c.π.app i₀)).obj ℱ₀) := by
  exact congrArg
    (fun f : c.pt ⟶ D.obj i₀ ↦ moduleGlobalSections ((Scheme.Modules.pullback f).obj ℱ₀))
    (c.w A.hom)

/-- The map from stagewise pullback-module global sections to the pullback-module global sections
on the limit scheme. -/
private noncomputable def pullbackModuleGlobalSectionsToLimitMap
    (i₀ : OrderDual I) (ℱ₀ : (D.obj i₀).Modules) (A : Over i₀) :
    moduleGlobalSections ((Scheme.Modules.pullback (D.map A.hom)).obj ℱ₀) →
      moduleGlobalSections ((Scheme.Modules.pullback (c.π.app i₀)).obj ℱ₀) :=
  let h :
      moduleGlobalSections ((Scheme.Modules.pullback (c.π.app A.left ≫ D.map A.hom)).obj ℱ₀) =
        moduleGlobalSections ((Scheme.Modules.pullback (c.π.app i₀)).obj ℱ₀) :=
    limitPullbackModuleGlobalSections_eq D c i₀ ℱ₀ A
  fun s ↦
    cast h (iteratedPullbackModuleGlobalSectionsMap (c.π.app A.left) (D.map A.hom) ℱ₀ s)

/-- The comparison maps to the limit are natural with respect to the over-category transitions. -/
private theorem pullbackModuleGlobalSectionsToLimitMap_naturality
    (i₀ : OrderDual I) (ℱ₀ : (D.obj i₀).Modules)
    {A B : Over i₀} (φ : A ⟶ B) :
    pullbackModuleGlobalSectionsToLimitMap D c i₀ ℱ₀ B =
      (pullbackModuleGlobalSectionsToLimitMap D c i₀ ℱ₀ A) ∘
        (overPullbackModuleGlobalSectionsMap D i₀ ℱ₀ φ) := sorry

/-- The cocone from the over-category diagram of pullback-module global sections to the limit
pullback-module global sections. -/
private noncomputable def limitPullbackModuleGlobalSectionsCocone
    (i₀ : OrderDual I) (ℱ₀ : (D.obj i₀).Modules) :
    Cocone (limitPullbackModuleGlobalSectionsDiagram D i₀ ℱ₀) where
  pt := moduleGlobalSections ((Scheme.Modules.pullback (c.π.app i₀)).obj ℱ₀)
  ι :=
    { app := fun A ↦ pullbackModuleGlobalSectionsToLimitMap D c i₀ ℱ₀ A.unop
      naturality := by
        intro A B φ
        simpa [Function.comp] using
          (pullbackModuleGlobalSectionsToLimitMap_naturality D c i₀ ℱ₀ φ.unop).symm }

/-- The canonical comparison map from the colimit of stagewise pullback-module global sections to
the global sections of the pullback module on the limit scheme. -/
noncomputable def limitPullbackModuleGlobalSectionsColimitMap
    (i₀ : OrderDual I) (ℱ₀ : (D.obj i₀).Modules) :
    colimit (limitPullbackModuleGlobalSectionsDiagram D i₀ ℱ₀) ⟶
      moduleGlobalSections ((Scheme.Modules.pullback (c.π.app i₀)).obj ℱ₀) :=
  colimit.desc (limitPullbackModuleGlobalSectionsDiagram D i₀ ℱ₀)
    (limitPullbackModuleGlobalSectionsCocone D c i₀ ℱ₀)

/-- Lemma 32.4.7: in Situation 32.4.5, if `\mathcal F_0` is a quasi-coherent sheaf on the
distinguished stage `S_0 = D.obj i₀`, then the canonical comparison map from the colimit of the
global sections `\Gamma(S_i, f_{i0}^* \mathcal F_0)` over objects of `Over i₀` to the global
sections `\Gamma(S, f_0^* \mathcal F_0)` on the limit scheme is an isomorphism. -/
@[stacks 01Z0]
theorem limitPullbackModuleGlobalSectionsColimitMap_isIso
    (i₀ : OrderDual I) (ℱ₀ : (D.obj i₀).Modules) [ℱ₀.IsQuasicoherent] :
    IsIso (limitPullbackModuleGlobalSectionsColimitMap D c i₀ ℱ₀) := sorry

end

end AlgebraicGeometry
