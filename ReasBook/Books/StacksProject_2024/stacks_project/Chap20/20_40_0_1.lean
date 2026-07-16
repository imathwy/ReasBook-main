import Mathlib.CategoryTheory.Sites.GlobalSections
import Mathlib.Algebra.Homology.TotalComplex
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.Topology.Sheaves.AddCommGrpCat
import StacksProject_2024.stacks_project.Chap12.Lemma_12_25_4
import StacksProject_2024.stacks_project.Chap20.Definition_20_23_1
import StacksProject_2024.stacks_project.Chap20.OpensInstances

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopologicalSpace ComplexShape HomologicalComplex₂
open CategoryTheory.Limits
open CategoryTheory.Sheaf (Γ ΓRes ΓNatIsoLim)

noncomputable section

universe u

namespace TopCat.Sheaf

section

variable {X : TopCat.{u}} {ι : Type u}
variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]

private instance weakSheafify_of_hasSheafify :
    HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  HasSheafify.isRightAdjoint

private instance sheafAddCommGrp_preadditive :
    Preadditive (X.Sheaf AddCommGrpCat.{u}) :=
  inferInstanceAs
    (Preadditive
      (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}))

private abbrev underlyingPresheafFunctor (X : TopCat.{u}) :
    X.Sheaf AddCommGrpCat.{u} ⥤ X.Presheaf AddCommGrpCat.{u} :=
  sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}

/- Domain-style sampling for 20.40.0.1:
- primary domain: the global-sections-to-extended alternating Čech comparison for unbounded
  cochain complexes of abelian sheaves on a topological space;
- sampled owner declarations:
  `Sheaf.Γ`,
  `Sheaf.ΓRes`,
  `alternatingCechComplex`,
  `alternatingCechComplexFunctor`,
  `HomologicalComplex₂.totalFunctor`,
  `ComplexShape.embeddingUpNat.extendFunctor`,
  `Functor.mapHomologicalComplex`;
- best owner abstraction: the public comparison should be built from the canonical global-sections
  owner `Sheaf.Γ (Opens.grothendieckTopology X) AddCommGrpCat` and the canonical restriction maps
  `Sheaf.ΓRes`; the rowwise construction should pass through the source-facing alternating Čech
  owner `alternatingCechComplex 𝒰` from Definition `20.23.1`, functorially packaged by
  `alternatingCechComplexFunctor 𝒰`, and then extended along `embeddingUpNat`;
- primitive data: only the space `X`, the indexed family of opens `𝒰`, and the unbounded sheaf
  complex `ℱ`;
- derived API: the extended rowwise Čech bicomplex underlying the alternating comparison, its total
  complex, the canonical comparison morphism from the global-sections complex, and the row
  identification with the alternating owner from Definition `20.23.1`.

Source/core/bridge triage:
- `source-facing`: the source-facing existence-and-uniqueness theorem
  `existsUnique_globalSectionsToAlternatingCechTotalMap`;
- `core/canonical`: `Sheaf.Γ`, `Sheaf.ΓRes`, `alternatingCechComplexFunctor`,
  `embeddingUpNat.extendFunctor`, `Functor.mapHomologicalComplex`,
  `HomologicalComplex₂.totalFunctor`, and the total-complex injections `ιTotal`;
  `alternatingCechComplexFunctor`, together with the private concrete bicomplex, the private
  row-zero comparison map, and the private support data used to build the public total-complex
  comparison morphism.

This file therefore reuses the canonical global-sections owner `Sheaf.Γ` and the restriction maps
`Sheaf.ΓRes`, instead of keeping a raw evaluation-at-`⊤` presentation of global sections. It also
keeps the rowwise alternating Čech owner from Definition `20.23.1` visible through theorem-level
source-facing API, while leaving only the internal bicomplex and zero-row support data private. -/

private instance sheafToPresheaf_additive (X : TopCat.{u}) :
    (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).Additive := by
  constructor
  intro F G f g
  ext U x
  rfl

private instance abelianPresheafLimit_additive :
    (lim : ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u}).Additive := by
  constructor
  intro F G f g
  apply limit.hom_ext
  intro j
  change limMap (f + g) ≫ limit.π G j = (limMap f + limMap g) ≫ limit.π G j
  rw [limMap_π, Preadditive.add_comp, limMap_π, limMap_π]
  simp

private instance sheafGamma_additive (X : TopCat.{u}) :
    (Sheaf.Γ (Opens.grothendieckTopology X) AddCommGrpCat.{u}).Additive := by
  exact Functor.additive_of_iso
    (ΓNatIsoLim (Opens.grothendieckTopology X) AddCommGrpCat.{u}).symm

private instance sheafGamma_preservesZeroMorphisms (X : TopCat.{u}) :
    (Sheaf.Γ (Opens.grothendieckTopology X) AddCommGrpCat.{u}).PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_additive _

/-- The cochain complex of global sections of an unbounded complex of abelian sheaves on `X`. -/
abbrev globalSectionsComplexFunctor (X : TopCat.{u}) :
    CochainComplex (X.Sheaf AddCommGrpCat.{u}) ℤ ⥤
      CochainComplex AddCommGrpCat.{u} ℤ :=
  (Γ (Opens.grothendieckTopology X) AddCommGrpCat.{u}).mapHomologicalComplex (up ℤ)

/-- The global-sections complex of an unbounded complex of abelian sheaves on `X`. -/
abbrev globalSectionsComplex (X : TopCat.{u})
    (ℱ : CochainComplex (X.Sheaf AddCommGrpCat.{u}) ℤ) :
    CochainComplex AddCommGrpCat.{u} ℤ :=
  (globalSectionsComplexFunctor X).obj ℱ

private abbrev alternatingCechRowFunctor (X : TopCat.{u}) (𝒰 : ι → Opens X) :
    X.Sheaf AddCommGrpCat.{u} ⥤ CochainComplex AddCommGrpCat.{u} ℤ :=
  underlyingPresheafFunctor X ⋙
    alternatingCechComplexFunctor 𝒰 ⋙
      embeddingUpNat.extendFunctor AddCommGrpCat.{u}

private instance alternatingCechComplexFunctor_preservesZeroMorphisms (𝒰 : ι → Opens X) :
    (alternatingCechComplexFunctor 𝒰).PreservesZeroMorphisms where
  map_zero F G := by
    apply HomologicalComplex.hom_ext
    intro p
    ext s
    rfl

private instance alternatingCechRowFunctor_preservesZeroMorphisms
    (X : TopCat.{u}) (𝒰 : ι → Opens X) :
    (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
      alternatingCechComplexFunctor 𝒰 ⋙
      embeddingUpNat.extendFunctor AddCommGrpCat.{u}).PreservesZeroMorphisms where
  map_zero F G := by
    change
      HomologicalComplex.extendMap
          ((alternatingCechComplexFunctor 𝒰).map
            ((underlyingPresheafFunctor X).map (0 : F ⟶ G)))
          embeddingUpNat =
        0
    have hzero :
        (underlyingPresheafFunctor X).map (0 : F ⟶ G) =
          0 := by
      ext U x
      rfl
    rw [hzero]
    have hzero' :
        (alternatingCechComplexFunctor 𝒰).map
            (0 :
              (underlyingPresheafFunctor X).obj F ⟶
                (underlyingPresheafFunctor X).obj G) =
          0 :=
      Functor.map_zero (alternatingCechComplexFunctor 𝒰) _ _
    rw [hzero']
    simpa using
      (Functor.map_zero (embeddingUpNat.extendFunctor AddCommGrpCat.{u})
        (alternatingCechComplex 𝒰 ((underlyingPresheafFunctor X).obj F))
        (alternatingCechComplex 𝒰 ((underlyingPresheafFunctor X).obj G)))

private instance alternatingCechRowFunctor_abbrev_preservesZeroMorphisms
    (X : TopCat.{u}) (𝒰 : ι → Opens X) :
    (alternatingCechRowFunctor X 𝒰).PreservesZeroMorphisms := by
  simpa [alternatingCechRowFunctor, underlyingPresheafFunctor] using
    (alternatingCechRowFunctor_preservesZeroMorphisms X 𝒰)

/-- The rowwise alternating Čech bicomplex attached to an unbounded complex of abelian sheaves. -/
private abbrev alternatingCechDoubleComplexFunctor (X : TopCat.{u}) (𝒰 : ι → Opens X) :
    CochainComplex (X.Sheaf AddCommGrpCat.{u}) ℤ ⥤
      HomologicalComplex₂ AddCommGrpCat.{u}
        (up ℤ) (up ℤ) :=
  (alternatingCechRowFunctor X 𝒰).mapHomologicalComplex (up ℤ)

/-- The total alternating Čech complex functor attached to the indexed family `𝒰`. -/
abbrev alternatingCechTotalComplexFunctor (X : TopCat.{u}) (𝒰 : ι → Opens X) :
    CochainComplex (X.Sheaf AddCommGrpCat.{u}) ℤ ⥤
      CochainComplex AddCommGrpCat.{u} ℤ :=
  alternatingCechDoubleComplexFunctor X 𝒰 ⋙
    HomologicalComplex₂.totalFunctor AddCommGrpCat.{u} (up ℤ) (up ℤ) (up ℤ)

private abbrev underlyingAdditivePresheaf (X : TopCat.{u})
    (ℱ : X.Sheaf AddCommGrpCat.{u}) :
    X.Presheaf AddCommGrpCat.{u} :=
  ℱ.obj

private abbrev alternatingCechRowComplex (X : TopCat.{u}) (𝒰 : ι → Opens X)
    (ℱ : X.Sheaf AddCommGrpCat.{u}) :
    CochainComplex AddCommGrpCat.{u} ℕ :=
  alternatingCechComplex 𝒰 (underlyingAdditivePresheaf X ℱ)

private abbrev alternatingCechRowComplexXIso (X : TopCat.{u}) (𝒰 : ι → Opens X)
    (ℱ : CochainComplex (X.Sheaf AddCommGrpCat.{u}) ℤ) (n : ℤ) (p : ℕ) :
    (((alternatingCechDoubleComplexFunctor X 𝒰).obj ℱ).X n).X (p : ℤ) ≅
      (alternatingCechRowComplex X 𝒰 (ℱ.X n)).X p :=
  by
    simpa [alternatingCechDoubleComplexFunctor, alternatingCechRowFunctor,
      alternatingCechRowComplex, underlyingAdditivePresheaf, underlyingPresheafFunctor] using
      (alternatingCechRowComplex X 𝒰 (ℱ.X n)).extendXIso embeddingUpNat rfl

-- Proof sketch: in degree `0` there are no repeated indices and the only permutation of `Fin 1`
-- is the identity, so the usual restriction family is automatically alternating.
/-- The degree-zero restriction family cut out by a global section is an alternating Čech
cochain. -/
theorem globalSectionsRestriction_isAlternatingCechCochain_zero
    (X : TopCat.{u}) (𝒰 : ι → Opens X)
    (ℱ : CochainComplex (X.Sheaf AddCommGrpCat.{u}) ℤ) (n : ℤ)
    (s : (globalSectionsComplex X ℱ).X n) :
    IsAlternatingCechCochain 𝒰 (ℱ.X n).obj 0
      (fun σ : Fin 1 → ι ↦
        ΓRes (ℱ.X n) (op (cechIntersection 𝒰 σ)) s) := by
  constructor
  · intro σ hσ
    exfalso
    apply hσ
    intro a b hab
    fin_cases a
    fin_cases b
    rfl
  · intro σ τ
    have hτ : τ = 1 := by
      ext i
      fin_cases i
      simp
    subst hτ
    simp
    rfl

/-- The underlying degree-zero global-sections comparison map into the alternating Čech row. -/
private def globalSectionsToAlternatingCechZeroToFun (X : TopCat.{u}) (𝒰 : ι → Opens X)
    (ℱ : CochainComplex (X.Sheaf AddCommGrpCat.{u}) ℤ) (n : ℤ) :
    (globalSectionsComplex X ℱ).X n →
      (alternatingCechRowComplex X 𝒰 (ℱ.X n)).X 0 :=
  fun s ↦
    ⟨(fun σ : Fin 1 → ι ↦
        ΓRes (ℱ.X n) (op (cechIntersection 𝒰 σ)) s),
      globalSectionsRestriction_isAlternatingCechCochain_zero X 𝒰 ℱ n s⟩

-- Proof sketch: the degree-zero alternating comparison is defined componentwise by restriction
-- maps of sheaves, hence it is additive.
/-- The degree-zero global-sections comparison into the alternating Čech row is additive. -/
private theorem globalSectionsToAlternatingCechZeroToFun_map_add
    (X : TopCat.{u}) (𝒰 : ι → Opens X)
    (ℱ : CochainComplex (X.Sheaf AddCommGrpCat.{u}) ℤ) (n : ℤ)
    (s t : (globalSectionsComplex X ℱ).X n) :
    globalSectionsToAlternatingCechZeroToFun X 𝒰 ℱ n (s + t) =
      globalSectionsToAlternatingCechZeroToFun X 𝒰 ℱ n s +
        globalSectionsToAlternatingCechZeroToFun X 𝒰 ℱ n t := by
  apply Subtype.ext
  ext σ
  change
    AddCommGrpCat.Hom.hom (ΓRes (ℱ.X n) (op (cechIntersection 𝒰 σ))) (s + t) =
      AddCommGrpCat.Hom.hom (ΓRes (ℱ.X n) (op (cechIntersection 𝒰 σ))) s +
        AddCommGrpCat.Hom.hom (ΓRes (ℱ.X n) (op (cechIntersection 𝒰 σ))) t
  exact (AddCommGrpCat.Hom.hom (ΓRes (ℱ.X n) (op (cechIntersection 𝒰 σ)))).map_add s t

/-- The Čech-degree-zero row of the alternating Čech bicomplex attached to `ℱ`. -/
private abbrev alternatingCechZeroRowComplex (X : TopCat.{u}) (𝒰 : ι → Opens X)
    (ℱ : CochainComplex (X.Sheaf AddCommGrpCat.{u}) ℤ) :
    CochainComplex AddCommGrpCat.{u} ℤ :=
  ((HomologicalComplex.eval AddCommGrpCat.{u} (up ℤ) (0 : ℤ)).mapHomologicalComplex
    (up ℤ)).obj ((alternatingCechDoubleComplexFunctor X 𝒰).obj ℱ)

-- Proof sketch: the row-zero comparison is defined degreewise by restriction maps of sheaves;
-- compatibility with the horizontal differential is therefore naturality of these restriction maps.
/-- The degreewise global-sections comparison into the Čech-degree-zero row is a chain map. -/
private theorem globalSectionsToAlternatingCechZeroComponent_comm
    (X : TopCat.{u}) (𝒰 : ι → Opens X)
    (ℱ : CochainComplex (X.Sheaf AddCommGrpCat.{u}) ℤ) {n n' : ℤ}
    (_ : (up ℤ).Rel n n') :
    (AddCommGrpCat.ofHom
        (AddMonoidHom.mk' (globalSectionsToAlternatingCechZeroToFun X 𝒰 ℱ n)
          (globalSectionsToAlternatingCechZeroToFun_map_add X 𝒰 ℱ n)) ≫
      (alternatingCechRowComplexXIso X 𝒰 ℱ n 0).inv) ≫
        (((alternatingCechDoubleComplexFunctor X 𝒰).obj ℱ).d n n').f 0 =
      (globalSectionsComplex X ℱ).d n n' ≫
        AddCommGrpCat.ofHom
          (AddMonoidHom.mk' (globalSectionsToAlternatingCechZeroToFun X 𝒰 ℱ n')
            (globalSectionsToAlternatingCechZeroToFun_map_add X 𝒰 ℱ n')) ≫
          (alternatingCechRowComplexXIso X 𝒰 ℱ n' 0).inv := by
  let α : underlyingAdditivePresheaf X (ℱ.X n) ⟶ underlyingAdditivePresheaf X (ℱ.X n') :=
    (underlyingPresheafFunctor X).map (ℱ.d n n')
  let e₀ := alternatingCechRowComplexXIso X 𝒰 ℱ n 0
  let e₀' := alternatingCechRowComplexXIso X 𝒰 ℱ n' 0
  have hrow :
      (((alternatingCechDoubleComplexFunctor X 𝒰).obj ℱ).d n n').f 0 =
        e₀.hom ≫ ((alternatingCechComplexFunctor 𝒰).map α).f 0 ≫ e₀'.inv := by
    simpa [α, alternatingCechDoubleComplexFunctor, alternatingCechRowFunctor,
      alternatingCechRowComplexXIso, alternatingCechRowComplex, underlyingAdditivePresheaf,
      underlyingPresheafFunctor, Functor.mapHomologicalComplex_obj_d] using
      (HomologicalComplex.extendMap_f
        ((alternatingCechComplexFunctor 𝒰).map α) embeddingUpNat rfl)
  have hbase :
      AddCommGrpCat.ofHom
          (AddMonoidHom.mk' (globalSectionsToAlternatingCechZeroToFun X 𝒰 ℱ n)
            (globalSectionsToAlternatingCechZeroToFun_map_add X 𝒰 ℱ n)) ≫
          ((alternatingCechComplexFunctor 𝒰).map α).f 0 =
        (globalSectionsComplex X ℱ).d n n' ≫
          AddCommGrpCat.ofHom
            (AddMonoidHom.mk' (globalSectionsToAlternatingCechZeroToFun X 𝒰 ℱ n')
              (globalSectionsToAlternatingCechZeroToFun_map_add X 𝒰 ℱ n')) := by
    ext s
    apply Subtype.ext
    ext σ
    change
      AddCommGrpCat.Hom.hom (α.app (op (cechIntersection 𝒰 σ)))
          (AddCommGrpCat.Hom.hom
            (ΓRes (ℱ.X n) (op (cechIntersection 𝒰 σ))) s) =
        AddCommGrpCat.Hom.hom
          (ΓRes (ℱ.X n') (op (cechIntersection 𝒰 σ)))
          (AddCommGrpCat.Hom.hom ((globalSectionsComplex X ℱ).d n n') s)
    have hΓRes :
        ΓRes (ℱ.X n) (op (cechIntersection 𝒰 σ)) ≫ α.app (op (cechIntersection 𝒰 σ)) =
          (globalSectionsComplex X ℱ).d n n' ≫
            ΓRes (ℱ.X n') (op (cechIntersection 𝒰 σ)) := by
      simpa [α, globalSectionsComplex, globalSectionsComplexFunctor, underlyingPresheafFunctor,
        Functor.mapHomologicalComplex_obj_d] using
        (Sheaf.ΓRes_naturality
          (ℱ.d n n') (op (cechIntersection 𝒰 σ))).symm
    exact congrArg (fun k ↦ AddCommGrpCat.Hom.hom k s) hΓRes
  calc
    (AddCommGrpCat.ofHom
          (AddMonoidHom.mk' (globalSectionsToAlternatingCechZeroToFun X 𝒰 ℱ n)
            (globalSectionsToAlternatingCechZeroToFun_map_add X 𝒰 ℱ n)) ≫
        (alternatingCechRowComplexXIso X 𝒰 ℱ n 0).inv) ≫
          (((alternatingCechDoubleComplexFunctor X 𝒰).obj ℱ).d n n').f 0 =
        (AddCommGrpCat.ofHom
          (AddMonoidHom.mk' (globalSectionsToAlternatingCechZeroToFun X 𝒰 ℱ n)
            (globalSectionsToAlternatingCechZeroToFun_map_add X 𝒰 ℱ n)) ≫
          ((alternatingCechComplexFunctor 𝒰).map α).f 0) ≫
            e₀'.inv := by
      rw [hrow]
      simp [e₀, alternatingCechRowComplexXIso, Category.assoc]
    _ =
        ((globalSectionsComplex X ℱ).d n n' ≫
          AddCommGrpCat.ofHom
            (AddMonoidHom.mk' (globalSectionsToAlternatingCechZeroToFun X 𝒰 ℱ n')
              (globalSectionsToAlternatingCechZeroToFun_map_add X 𝒰 ℱ n'))) ≫
            e₀'.inv := by
      exact congrArg (fun k ↦ k ≫ e₀'.inv) hbase
    _ =
        (globalSectionsComplex X ℱ).d n n' ≫
          AddCommGrpCat.ofHom
            (AddMonoidHom.mk' (globalSectionsToAlternatingCechZeroToFun X 𝒰 ℱ n')
              (globalSectionsToAlternatingCechZeroToFun_map_add X 𝒰 ℱ n')) ≫
            (alternatingCechRowComplexXIso X 𝒰 ℱ n' 0).inv := by
      rfl

-- Proof sketch: each degreewise map lands in Čech degree `0`, and the corresponding vertical
-- alternating Čech differential vanishes on these restriction families.
/-- The degreewise global-sections comparison into the Čech-degree-zero row lands in column
cycles. -/
private theorem globalSectionsToAlternatingCechZeroComponent_vertical
    (X : TopCat.{u}) (𝒰 : ι → Opens X)
    (ℱ : CochainComplex (X.Sheaf AddCommGrpCat.{u}) ℤ) (n : ℤ) :
    (AddCommGrpCat.ofHom
        (AddMonoidHom.mk' (globalSectionsToAlternatingCechZeroToFun X 𝒰 ℱ n)
          (globalSectionsToAlternatingCechZeroToFun_map_add X 𝒰 ℱ n)) ≫
      (alternatingCechRowComplexXIso X 𝒰 ℱ n 0).inv) ≫
        (((alternatingCechDoubleComplexFunctor X 𝒰).obj ℱ).X n).d 0 1 =
      0 := by
  let e₀ := alternatingCechRowComplexXIso X 𝒰 ℱ n 0
  let e₁ := alternatingCechRowComplexXIso X 𝒰 ℱ n 1
  have hrow :
      (((alternatingCechDoubleComplexFunctor X 𝒰).obj ℱ).X n).d 0 1 =
        e₀.hom ≫ (alternatingCechRowComplex X 𝒰 (ℱ.X n)).d 0 1 ≫ e₁.inv := by
    simpa [alternatingCechDoubleComplexFunctor, alternatingCechRowFunctor,
      alternatingCechRowComplexXIso, alternatingCechRowComplex, underlyingAdditivePresheaf,
      underlyingPresheafFunctor] using
      ((alternatingCechRowComplex X 𝒰 (ℱ.X n)).extend_d_eq embeddingUpNat rfl rfl)
  have hbase :
      AddCommGrpCat.ofHom
          (AddMonoidHom.mk' (globalSectionsToAlternatingCechZeroToFun X 𝒰 ℱ n)
            (globalSectionsToAlternatingCechZeroToFun_map_add X 𝒰 ℱ n)) ≫
          (alternatingCechRowComplex X 𝒰 (ℱ.X n)).d 0 1 =
        0 := by
    ext s
    apply Subtype.ext
    ext σ
    have hface (j : Fin 2) :
        cechRestriction 𝒰 (underlyingAdditivePresheaf X (ℱ.X n)) σ j
            ((globalSectionsToAlternatingCechZeroToFun X 𝒰 ℱ n s).1 (σ ∘ j.succAboveEmb)) =
          AddCommGrpCat.Hom.hom (ΓRes (ℱ.X n) (op (cechIntersection 𝒰 σ))) s := by
        have hΓRes :
            ΓRes (ℱ.X n) (op (cechIntersection 𝒰 (σ ∘ j.succAboveEmb))) ≫
                (underlyingAdditivePresheaf X (ℱ.X n)).map
                  (homOfLE (cechIntersection_le_succAbove 𝒰 σ j)).op =
              ΓRes (ℱ.X n) (op (cechIntersection 𝒰 σ)) := by
          simp [underlyingAdditivePresheaf]
        exact congrArg (fun k ↦ AddCommGrpCat.Hom.hom k s) hΓRes
    change
      ∑ j : Fin 2,
          (-1 : ℤ) ^ (j : ℕ) •
            cechRestriction 𝒰 (underlyingAdditivePresheaf X (ℱ.X n)) σ j
              ((globalSectionsToAlternatingCechZeroToFun X 𝒰 ℱ n s).1
                (σ ∘ j.succAboveEmb)) = 0
    let x : ((underlyingAdditivePresheaf X (ℱ.X n)).obj (op (cechIntersection 𝒰 σ))) :=
      AddCommGrpCat.Hom.hom (ΓRes (ℱ.X n) (op (cechIntersection 𝒰 σ))) s
    have h0 :
        (ConcreteCategory.hom (cechRestriction 𝒰 (underlyingAdditivePresheaf X (ℱ.X n)) σ 0))
            ((globalSectionsToAlternatingCechZeroToFun X 𝒰 ℱ n s).1
              (σ ∘ Fin.succAboveEmb 0)) =
          x := by
      simpa [x] using hface (0 : Fin 2)
    have h1 :
        (ConcreteCategory.hom (cechRestriction 𝒰 (underlyingAdditivePresheaf X (ℱ.X n)) σ 1))
            ((globalSectionsToAlternatingCechZeroToFun X 𝒰 ℱ n s).1
              (σ ∘ Fin.succAboveEmb 1)) =
          x := by
      simpa [x] using hface (1 : Fin 2)
    rw [Fin.sum_univ_two, h0, h1]
    simp [x]
  calc
    (AddCommGrpCat.ofHom
          (AddMonoidHom.mk' (globalSectionsToAlternatingCechZeroToFun X 𝒰 ℱ n)
            (globalSectionsToAlternatingCechZeroToFun_map_add X 𝒰 ℱ n)) ≫
        (alternatingCechRowComplexXIso X 𝒰 ℱ n 0).inv) ≫
          (((alternatingCechDoubleComplexFunctor X 𝒰).obj ℱ).X n).d 0 1 =
        (AddCommGrpCat.ofHom
          (AddMonoidHom.mk' (globalSectionsToAlternatingCechZeroToFun X 𝒰 ℱ n)
            (globalSectionsToAlternatingCechZeroToFun_map_add X 𝒰 ℱ n)) ≫
          (alternatingCechRowComplex X 𝒰 (ℱ.X n)).d 0 1) ≫
            e₁.inv := by
      rw [hrow]
      simp [e₀, alternatingCechRowComplexXIso, Category.assoc]
    _ =
        0 ≫ e₁.inv := by
      exact congrArg (fun k ↦ k ≫ e₁.inv) hbase
    _ = 0 := by rw [zero_comp]

/-- The degreewise global-sections comparison assembles to the row-zero morphism of the
alternating Čech bicomplex. -/
private noncomputable def globalSectionsToAlternatingCechZeroRowMap
    (X : TopCat.{u}) (𝒰 : ι → Opens X)
    (ℱ : CochainComplex (X.Sheaf AddCommGrpCat.{u}) ℤ) :
    globalSectionsComplex X ℱ ⟶ alternatingCechZeroRowComplex X 𝒰 ℱ where
  f := fun n ↦
    AddCommGrpCat.ofHom
        (AddMonoidHom.mk' (globalSectionsToAlternatingCechZeroToFun X 𝒰 ℱ n)
          (globalSectionsToAlternatingCechZeroToFun_map_add X 𝒰 ℱ n)) ≫
      (alternatingCechRowComplexXIso X 𝒰 ℱ n 0).inv
  comm' := fun _ _ h ↦
    globalSectionsToAlternatingCechZeroComponent_comm X 𝒰 ℱ h

/-- The row-zero global-sections comparison lands in the column cycles of the alternating Čech
bicomplex. -/
private theorem globalSectionsToAlternatingCechZeroRowMap_cycles
    (X : TopCat.{u}) (𝒰 : ι → Opens X)
    (ℱ : CochainComplex (X.Sheaf AddCommGrpCat.{u}) ℤ) :
    ∀ n : ℤ,
      (globalSectionsToAlternatingCechZeroRowMap X 𝒰 ℱ).f n ≫
        (((alternatingCechDoubleComplexFunctor X 𝒰).obj ℱ).X n).d 0 1 = 0 := by
  intro n
  exact globalSectionsToAlternatingCechZeroComponent_vertical X 𝒰 ℱ n

/-- The source-facing specification for the comparison morphism of `20.40.0.1` from the
global-sections complex of `ℱ` to the total alternating Čech complex attached to `𝒰`. -/
def IsGlobalSectionsToAlternatingCechTotalMap
    (X : TopCat.{u}) (𝒰 : ι → Opens X)
    (ℱ : CochainComplex (X.Sheaf AddCommGrpCat.{u}) ℤ) :
    (globalSectionsComplex X ℱ ⟶ (alternatingCechTotalComplexFunctor X 𝒰).obj ℱ) → Prop :=
  fun α ↦
    ∀ n (s : (globalSectionsComplex X ℱ).X n),
      let A : HomologicalComplex₂ AddCommGrpCat.{u} (up ℤ) (up ℤ) :=
        (alternatingCechDoubleComplexFunctor X 𝒰).obj ℱ
      let e :
          (A.X n).X 0 ≅ (alternatingCechComplex 𝒰 (ℱ.X n).obj).X 0 :=
        alternatingCechRowComplexXIso X 𝒰 ℱ n 0
      ∃ t : (alternatingCechComplex 𝒰 (ℱ.X n).obj).X 0,
        t.1 = (fun σ : Fin 1 → ι ↦
          ΓRes (ℱ.X n) (op (cechIntersection 𝒰 σ)) s) ∧
        AddCommGrpCat.Hom.hom (α.f n) s =
          AddCommGrpCat.Hom.hom
            (A.ιTotal (up ℤ) n 0 n (Int.add_zero n))
            (AddCommGrpCat.Hom.hom e.inv t)

/-- The canonical comparison morphism of `20.40.0.1`. -/
noncomputable def globalSectionsToAlternatingCechTotalMap
    (X : TopCat.{u}) (𝒰 : ι → Opens X)
    (ℱ : CochainComplex (X.Sheaf AddCommGrpCat.{u}) ℤ) :
    globalSectionsComplex X ℱ ⟶ (alternatingCechTotalComplexFunctor X 𝒰).obj ℱ :=
  doubleComplexZeroRowToTotal
    (globalSectionsToAlternatingCechZeroRowMap X 𝒰 ℱ)
    (globalSectionsToAlternatingCechZeroRowMap_cycles X 𝒰 ℱ)

/-- The canonical comparison morphism of `20.40.0.1` satisfies the source-facing component
formula. -/
theorem globalSectionsToAlternatingCechTotalMap_spec
    (X : TopCat.{u}) (𝒰 : ι → Opens X)
    (ℱ : CochainComplex (X.Sheaf AddCommGrpCat.{u}) ℤ)
    : IsGlobalSectionsToAlternatingCechTotalMap X 𝒰 ℱ
        (globalSectionsToAlternatingCechTotalMap X 𝒰 ℱ) := by
  intro n s
  refine ⟨⟨(fun σ : Fin 1 → ι ↦
      ΓRes (ℱ.X n) (op (cechIntersection 𝒰 σ)) s),
    globalSectionsRestriction_isAlternatingCechCochain_zero X 𝒰 ℱ n s⟩, rfl, rfl⟩

/-- The degree-`n` component of `globalSectionsToAlternatingCechTotalMap` sends a global section
to its degree-zero alternating restriction family in the `(n, 0)` summand of the total
alternating Čech complex. -/
theorem globalSectionsToAlternatingCechTotalMap_f
    (X : TopCat.{u}) (𝒰 : ι → Opens X)
    (ℱ : CochainComplex (X.Sheaf AddCommGrpCat.{u}) ℤ) (n : ℤ)
    (s : (globalSectionsComplex X ℱ).X n) :
    let A : HomologicalComplex₂ AddCommGrpCat.{u} (up ℤ) (up ℤ) :=
      (((sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
          alternatingCechComplexFunctor 𝒰 ⋙
          embeddingUpNat.extendFunctor AddCommGrpCat.{u}).mapHomologicalComplex
        (up ℤ)).obj ℱ)
    let t : (alternatingCechComplex 𝒰 (ℱ.X n).obj).X 0 :=
      ⟨(fun σ : Fin 1 → ι ↦ ΓRes (ℱ.X n) (op (cechIntersection 𝒰 σ)) s),
        globalSectionsRestriction_isAlternatingCechCochain_zero X 𝒰 ℱ n s⟩
    AddCommGrpCat.Hom.hom ((globalSectionsToAlternatingCechTotalMap X 𝒰 ℱ).f n) s =
      AddCommGrpCat.Hom.hom
        (A.ιTotal (up ℤ) n 0 n (Int.add_zero n))
        (AddCommGrpCat.Hom.hom
          (((alternatingCechComplex 𝒰 (ℱ.X n).obj).extendXIso embeddingUpNat rfl).inv)
          t) := by
  dsimp
  let t : (alternatingCechComplex 𝒰 (ℱ.X n).obj).X 0 :=
    ⟨(fun σ : Fin 1 → ι ↦ ΓRes (ℱ.X n) (op (cechIntersection 𝒰 σ)) s),
      globalSectionsRestriction_isAlternatingCechCochain_zero X 𝒰 ℱ n s⟩
  rcases globalSectionsToAlternatingCechTotalMap_spec X 𝒰 ℱ n s with ⟨t', ht', hmap⟩
  have htt : t' = t := by
    apply Subtype.ext
    simpa [t] using ht'
  simpa [t, htt, alternatingCechRowComplexXIso, alternatingCechRowComplex,
    underlyingAdditivePresheaf, underlyingPresheafFunctor] using hmap

/- 20.40.0.1: there is a unique morphism from the global-sections complex of `ℱ` to the total
alternating Čech complex of the indexed family `𝒰` whose degree-`n` component sends a global
section to its degree-zero alternating restriction family in the `(n, 0)` summand. -/
@[stacks 08C0]
theorem existsUnique_globalSectionsToAlternatingCechTotalMap
    (X : TopCat.{u}) (𝒰 : ι → Opens X)
    (ℱ : CochainComplex (X.Sheaf AddCommGrpCat.{u}) ℤ) :
    ∃! α : globalSectionsComplex X ℱ ⟶ (alternatingCechTotalComplexFunctor X 𝒰).obj ℱ,
      IsGlobalSectionsToAlternatingCechTotalMap X 𝒰 ℱ α := by
  refine ⟨globalSectionsToAlternatingCechTotalMap X 𝒰 ℱ, ?_, ?_⟩
  · exact globalSectionsToAlternatingCechTotalMap_spec X 𝒰 ℱ
  · intro β hβ
    ext n s
    rcases hβ n s with ⟨t, ht, hβt⟩
    rcases globalSectionsToAlternatingCechTotalMap_spec X 𝒰 ℱ n s with
      ⟨t₀, ht₀, hchosen⟩
    have htt₀ : t = t₀ := by
      apply Subtype.ext
      simpa [ht₀] using ht
    exact hβt.trans (by
      rw [htt₀]
      symm
      exact hchosen)

/-- The source-facing specification characterizes the canonical comparison morphism of
`20.40.0.1` uniquely. -/
theorem globalSectionsToAlternatingCechTotalMap_unique
    (X : TopCat.{u}) (𝒰 : ι → Opens X)
    (ℱ : CochainComplex (X.Sheaf AddCommGrpCat.{u}) ℤ)
    {β : globalSectionsComplex X ℱ ⟶ (alternatingCechTotalComplexFunctor X 𝒰).obj ℱ}
    (hβ : IsGlobalSectionsToAlternatingCechTotalMap X 𝒰 ℱ β) :
    β = globalSectionsToAlternatingCechTotalMap X 𝒰 ℱ :=
  (existsUnique_globalSectionsToAlternatingCechTotalMap X 𝒰 ℱ).unique hβ
    (globalSectionsToAlternatingCechTotalMap_spec X 𝒰 ℱ)

end

end TopCat.Sheaf
