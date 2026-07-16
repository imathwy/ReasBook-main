import stacks_proof.stacks_project.Chap07.Lemma_7_26_4.DirectSourceComparison.DirectSourceReindexing

open CategoryTheory

universe u v w

namespace CategoryTheory
namespace GrothendieckTopology

section

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C} {U : C}
variable [univLE : UnivLE.{max u v, w}]

omit [UnivLE.{max u v, w}] in
private theorem fun_app_heq_of_type_eqs {α α' : Sort _} {β β' : Sort _}
    (hα : α = α') (hβ : β = β')
    {f : α → β} {g : α' → β'} (hf : HEq f g)
    {x : α} {y : α'} (hxy : HEq x y) :
    HEq (f x) (g y) := by
  subst hα
  subst hβ
  cases hxy
  cases hf
  rfl

omit [UnivLE.{max u v, w}] in
/-- Helper for Lemma 7.26.4: the inverse direct-source normalization component is an identity
transport on terminal sections, up to heterogeneous equality. -/
private theorem localized_cover_descent_pullbackDatum_over_direct_source_iso_inv_app_heq
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category.{u, v, w} (J := J) (U := U) 𝒰)
    (I : 𝒰.Arrow)
    (T : Over I.Y)
    (K : ((𝒰.pullback I.f).pullback T.hom).Arrow)
    (x : (((localized_cover_descent_pullbackDatum_over_direct_source
      (J := J) (U := U) 𝒰 D I T).obj K).1.obj
        (Opposite.op (Over.mk (𝟙 K.Y))))) :
    HEq
      (((localized_cover_descent_pullbackDatum_over_direct_source_iso
        (J := J) (U := U) 𝒰 D I T).inv.hom K).hom.app
          (Opposite.op (Over.mk (𝟙 K.Y))) x)
      x := by
  simpa [localized_cover_descent_pullbackDatum_over_direct_source_iso,
    localized_cover_descent_pullbackDatum, localized_cover_descent_pullbackDatum_over_direct_source,
    Cover.Arrow.base, Pseudofunctor.DescentData.pullFunctorObjHom, Category.assoc] using
    (pf_mapComp'_hom_component_apply_heq
      (J := J)
      (f := (𝟙 K.Y).op.toLoc)
      (g' := (𝟙 K.Y).op.toLoc)
      (k := (𝟙 K.Y).op.toLoc)
      (hk := by simp)
      (D.obj K.base.base)
      (Opposite.op (Over.mk (𝟙 K.Y))) x)

omit [UnivLE.{max u v, w}] in
private theorem toDescentDataCompPullFunctorIso_hom_app_heq
    {S : C}
    (𝒱 : J.Cover S)
    (M : Sheaf (J.over S) (Type w))
    (T : Over S)
    (K : (𝒱.pullback T.hom).Arrow)
    (x : ((((Pseudofunctor.DescentData.pullFunctor (J.pseudofunctorOver (Type w))
      (f := fun I : 𝒱.Arrow ↦ I.f)
      (p := T.hom)
      (f' := fun K : (𝒱.pullback T.hom).Arrow ↦ K.f)
      (α := fun K ↦ K.base)
      (p' := fun _ ↦ 𝟙 _)
      (w := localized_cover_descent_pullbackDatum_w (J := J) (U := S) 𝒱 T)).obj
        (((J.pseudofunctorOver (Type w)).toDescentData
          (fun I : 𝒱.Arrow ↦ I.f)).obj M)).obj K).1.obj
        (Opposite.op (Over.mk (𝟙 K.Y))))) :
    HEq
      ((((Pseudofunctor.DescentData.toDescentDataCompPullFunctorIso
        (J.pseudofunctorOver (Type w))
        (f := fun I : 𝒱.Arrow ↦ I.f)
        (p := T.hom)
        (f' := fun K : (𝒱.pullback T.hom).Arrow ↦ K.f)
        (α := fun K ↦ K.base)
        (p' := fun _ ↦ 𝟙 _)
        (w := localized_cover_descent_pullbackDatum_w (J := J) (U := S) 𝒱 T)).hom.app M).hom K).hom.app
          (Opposite.op (Over.mk (𝟙 K.Y))) x)
      x := by
  let X : (Over K.Y)ᵒᵖ := Opposite.op (Over.mk (𝟙 K.Y))
  let A :=
    ((J.pseudofunctorOver (Type w)).mapComp'
      (T.hom.op.toLoc ≫ K.f.op.toLoc) (𝟙 K.Y).op.toLoc
      (T.hom.op.toLoc ≫ K.f.op.toLoc) (by simp)).inv.toNatTrans.app M
  let B :=
    ((J.pseudofunctorOver (Type w)).mapComp
      T.hom.op.toLoc K.f.op.toLoc).hom.toNatTrans.app M
  have hA : HEq (A.hom.app X x) x := by
    simpa [A, X, Pseudofunctor.toDescentData] using
      (pf_mapComp'_inv_component_apply_heq
        (J := J)
        (f := T.hom.op.toLoc ≫ K.f.op.toLoc)
        (g' := (𝟙 K.Y).op.toLoc)
        (k := T.hom.op.toLoc ≫ K.f.op.toLoc)
        (hk := by simp)
        M X x)
  have hB : HEq (B.hom.app X (A.hom.app X x)) (A.hom.app X x) := by
    simpa [B, X, Pseudofunctor.toDescentData] using
      (pf_mapComp_hom_component_apply_heq
        (J := J)
        (f := T.hom.op.toLoc)
        (g' := K.f.op.toLoc)
        M X (A.hom.app X x))
  simpa [A, B, X, Pseudofunctor.DescentData.toDescentDataCompPullFunctorIso,
    Pseudofunctor.toDescentData, Pseudofunctor.isoMapOfCommSq,
    Pseudofunctor.mapComp'_eq_mapComp, Category.assoc] using hB.trans hA

omit [UnivLE.{max u v, w}] in
private theorem pullFunctor_map_id_app_heq
    {S : C}
    (𝒱 : J.Cover S)
    {D₁ D₂ : (J.pseudofunctorOver (Type w)).DescentData
      (fun I : 𝒱.Arrow ↦ I.f)}
    (φ : D₁ ⟶ D₂)
    (T : Over S)
    (K : (𝒱.pullback T.hom).Arrow)
    (x : ((((Pseudofunctor.DescentData.pullFunctor (J.pseudofunctorOver (Type w))
      (f := fun I : 𝒱.Arrow ↦ I.f)
      (p := T.hom)
      (f' := fun K : (𝒱.pullback T.hom).Arrow ↦ K.f)
      (α := fun K ↦ K.base)
      (p' := fun _ ↦ 𝟙 _)
      (w := localized_cover_descent_pullbackDatum_w (J := J) (U := S) 𝒱 T)).obj
        D₁).obj K).1.obj (Opposite.op (Over.mk (𝟙 K.Y))))) :
    HEq
      ((((Pseudofunctor.DescentData.pullFunctor (J.pseudofunctorOver (Type w))
        (f := fun I : 𝒱.Arrow ↦ I.f)
        (p := T.hom)
        (f' := fun K : (𝒱.pullback T.hom).Arrow ↦ K.f)
        (α := fun K ↦ K.base)
        (p' := fun _ ↦ 𝟙 _)
        (w := localized_cover_descent_pullbackDatum_w (J := J) (U := S) 𝒱 T)).map
          φ).hom K).hom.app (Opposite.op (Over.mk (𝟙 K.Y))) x)
      ((φ.hom K.base).hom.app
        (Opposite.op ((Over.map (𝟙 K.Y)).obj (Over.mk (𝟙 K.Y)))) x) := by
  simp [Pseudofunctor.DescentData.pullFunctor]

omit [UnivLE.{max u v, w}] in
/-- Helper for Lemma 7.26.4: the direct-source terminal-section comparison with the pulled-back
component sheaf is stable under reindexing a pullback-cover arrow along a slice morphism. -/
private theorem localized_cover_descent_pullbackDatum_over_direct_section_equiv_component_arrow_map_heq
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category.{u, v, w} (J := J) (U := U) 𝒰)
    (I : 𝒰.Arrow)
    {T₁ T₂ : Over I.Y}
    (g : T₂ ⟶ T₁)
    (K : ((𝒰.pullback I.f).pullback T₂.hom).Arrow)
    {x : (((localized_cover_descent_pullbackDatum_over_direct_source
      (J := J) (U := U) 𝒰 D I T₂).obj K).1.obj
        (Opposite.op (Over.mk (𝟙 K.Y))))}
    {y : (((localized_cover_descent_pullbackDatum_over_direct_source
      (J := J) (U := U) 𝒰 D I T₁).obj
        (localized_cover_descent_pullback_arrow_map
          (J := J) (U := I.Y) (𝒰.pullback I.f) g K)).1.obj
        (Opposite.op (Over.mk (𝟙 K.Y))))}
    (hxy : HEq x y) :
    HEq
      (localized_cover_descent_pullbackDatum_over_direct_section_equiv_component
        (J := J) (U := U) 𝒰 D I T₂ K x)
      (localized_cover_descent_pullbackDatum_over_direct_section_equiv_component
        (J := J) (U := U) 𝒰 D I T₁
        (localized_cover_descent_pullback_arrow_map
          (J := J) (U := I.Y) (𝒰.pullback I.f) g K) y) := by
  cases T₁
  cases T₂
  rename_i T₁Y T₁pt hT₁ T₂Y T₂pt hT₂
  cases T₁pt
  cases T₂pt
  rename_i a₁ a₂
  cases a₁
  cases a₂
  obtain ⟨gleft, hg, rfl⟩ := Over.homMk_surjective g
  change T₁Y ⟶ I.Y at hT₁
  change T₂Y ⟶ I.Y at hT₂
  change T₂Y ⟶ T₁Y at gleft
  have hg' : hT₂ = gleft ≫ hT₁ := by
    simpa using hg.symm
  revert K x y hxy
  cases hg'
  let T₂o : Over I.Y := { left := T₂Y, right := { as := PUnit.unit }, hom := gleft ≫ hT₁ }
  let T₁o : Over I.Y := { left := T₁Y, right := { as := PUnit.unit }, hom := hT₁ }
  let g' : T₂o ⟶ T₁o := Over.homMk gleft (by simp [T₁o, T₂o])
  intro K x y hxy
  let K' :=
    localized_cover_descent_pullback_arrow_map
      (J := J) (U := I.Y) (𝒰.pullback I.f) g' K
  change
    HEq
      (localized_cover_descent_pullbackDatum_over_direct_section_equiv_component
        (J := J) (U := U) 𝒰 D I T₂o K x)
      (localized_cover_descent_pullbackDatum_over_direct_section_equiv_component
        (J := J) (U := U) 𝒰 D I T₁o K' y)
  have hsourceType :
      (((localized_cover_descent_pullbackDatum_over_direct_source
        (J := J) (U := U) 𝒰 D I
        T₂o).obj K).1.obj
          (Opposite.op (Over.mk (𝟙 K.Y)))) =
        (((localized_cover_descent_pullbackDatum_over_direct_source
          (J := J) (U := U) 𝒰 D I
          T₁o).obj K').1.obj
            (Opposite.op (Over.mk (𝟙 K'.Y)))) := by
    rcases K with ⟨Y, f, hf⟩
    simp [K', g', T₁o, T₂o, localized_cover_descent_pullbackDatum_over_direct_source,
      localized_cover_descent_pullback_arrow_map, Cover.Arrow.base, Category.assoc]
    congr 2
    exact eq_of_heq (congr_arg_heq D.obj (by
      ext <;> simp [Category.assoc]))
  have htargetType :
      ((((J.overMapPullback (Type w)
        T₂o.hom).obj
          (D.obj I)).1).obj (Opposite.op (Over.mk K.f))) =
        ((((J.overMapPullback (Type w)
          T₁o.hom).obj
            (D.obj I)).1).obj (Opposite.op (Over.mk K'.f))) := by
    have hObj :
        (Over.map T₂o.hom).obj (Over.mk K.f) =
          (Over.map T₁o.hom).obj (Over.mk K'.f) := by
      rcases K with ⟨Y, f, hf⟩
      apply over_mk_hext (𝒞 := C) (B := I.Y) (hY := rfl)
      exact heq_of_eq (by simp [K', g', T₁o, T₂o, localized_cover_descent_pullback_arrow_map,
        Category.assoc])
    simpa [GrothendieckTopology.overMapPullback] using
      congrArg (fun X : Over I.Y => (D.obj I).1.obj (Opposite.op X)) hObj
  let φ₂ :=
    (localized_cover_descent_pullbackDatum_over_direct_to_component_iso
      (J := J) (U := U) 𝒰 D I T₂o).hom.hom K
  let φ₁ :=
    (localized_cover_descent_pullbackDatum_over_direct_to_component_iso
      (J := J) (U := U) 𝒰 D I T₁o).hom.hom K'
  let X₂ : (Over K.Y)ᵒᵖ := Opposite.op (Over.mk (𝟙 K.Y))
  let X₁ : (Over K'.Y)ᵒᵖ := Opposite.op (Over.mk (𝟙 K'.Y))
  let Q₂ :=
    (((J.pseudofunctorOver (Type w)).toDescentData
      (fun L : ((𝒰.pullback I.f).pullback T₂o.hom).Arrow ↦ L.f)).obj
        ((J.overMapPullback (Type w) T₂o.hom).obj (D.obj I)))
  let Q₁ :=
    (((J.pseudofunctorOver (Type w)).toDescentData
      (fun L : ((𝒰.pullback I.f).pullback T₁o.hom).Arrow ↦ L.f)).obj
        ((J.overMapPullback (Type w) T₁o.hom).obj (D.obj I)))
  have hcodType : (Q₂.obj K).1.obj X₂ = (Q₁.obj K').1.obj X₁ := by
    simpa [Q₂, Q₁, X₂, X₁, Pseudofunctor.toDescentData,
      localized_cover_descent_overMap_terminal_obj] using htargetType
  have happ : HEq (φ₂.hom.app X₂ x) (φ₁.hom.app X₁ y) := by
    let η₂ :=
      (localized_cover_descent_pullbackDatum_over_direct_source_iso
        (J := J) (U := U) 𝒰 D I T₂o).inv.hom K
    let η₁ :=
      (localized_cover_descent_pullbackDatum_over_direct_source_iso
        (J := J) (U := U) 𝒰 D I T₁o).inv.hom K'
    let μ₂ :=
      ((Pseudofunctor.DescentData.pullFunctor (J.pseudofunctorOver (Type w))
        (f := fun K : (𝒰.pullback I.f).Arrow ↦ K.f)
        (p := T₂o.hom)
        (f' := fun K : ((𝒰.pullback I.f).pullback T₂o.hom).Arrow ↦ K.f)
        (α := fun K ↦ K.base)
        (p' := fun _ ↦ 𝟙 _)
        (w := localized_cover_descent_pullbackDatum_w (J := J) (U := I.Y)
          (𝒰.pullback I.f) T₂o)).map
          (localized_cover_descent_pullbackDatum_toDescentData_obj
            (J := J) (U := U) 𝒰 D I).hom).hom K
    let μ₁ :=
      ((Pseudofunctor.DescentData.pullFunctor (J.pseudofunctorOver (Type w))
        (f := fun K : (𝒰.pullback I.f).Arrow ↦ K.f)
        (p := T₁o.hom)
        (f' := fun K : ((𝒰.pullback I.f).pullback T₁o.hom).Arrow ↦ K.f)
        (α := fun K ↦ K.base)
        (p' := fun _ ↦ 𝟙 _)
        (w := localized_cover_descent_pullbackDatum_w (J := J) (U := I.Y)
          (𝒰.pullback I.f) T₁o)).map
          (localized_cover_descent_pullbackDatum_toDescentData_obj
            (J := J) (U := U) 𝒰 D I).hom).hom K'
    let ν₂ :=
      ((Pseudofunctor.DescentData.toDescentDataCompPullFunctorIso
        (J.pseudofunctorOver (Type w))
        (f := fun K : (𝒰.pullback I.f).Arrow ↦ K.f)
        (p := T₂o.hom)
        (f' := fun K : ((𝒰.pullback I.f).pullback T₂o.hom).Arrow ↦ K.f)
        (α := fun K ↦ K.base)
        (p' := fun _ ↦ 𝟙 _)
        (w := localized_cover_descent_pullbackDatum_w (J := J) (U := I.Y)
          (𝒰.pullback I.f) T₂o)).hom.app (D.obj I)).hom K
    let ν₁ :=
      ((Pseudofunctor.DescentData.toDescentDataCompPullFunctorIso
        (J.pseudofunctorOver (Type w))
        (f := fun K : (𝒰.pullback I.f).Arrow ↦ K.f)
        (p := T₁o.hom)
        (f' := fun K : ((𝒰.pullback I.f).pullback T₁o.hom).Arrow ↦ K.f)
        (α := fun K ↦ K.base)
        (p' := fun _ ↦ 𝟙 _)
        (w := localized_cover_descent_pullbackDatum_w (J := J) (U := I.Y)
          (𝒰.pullback I.f) T₁o)).hom.app (D.obj I)).hom K'
    let ξ₂ : (((localized_cover_descent_pullbackDatum_over_source
        (J := J) (U := U) 𝒰 D I T₂o).obj K).1.obj X₂) :=
      ((localized_cover_descent_pullbackDatum_over_direct_source_iso
        (J := J) (U := U) 𝒰 D I T₂o).inv.hom K).hom.app X₂ x
    let ξ₁ : (((localized_cover_descent_pullbackDatum_over_source
        (J := J) (U := U) 𝒰 D I T₁o).obj K').1.obj X₁) :=
      ((localized_cover_descent_pullbackDatum_over_direct_source_iso
        (J := J) (U := U) 𝒰 D I T₁o).inv.hom K').hom.app X₁ y
    have hη₂ : HEq ξ₂ x := by
      simpa [ξ₂, X₂] using
        localized_cover_descent_pullbackDatum_over_direct_source_iso_inv_app_heq
          (J := J) (U := U) 𝒰 D I T₂o K x
    have hη₁ : HEq ξ₁ y := by
      simpa [ξ₁, X₁] using
        localized_cover_descent_pullbackDatum_over_direct_source_iso_inv_app_heq
          (J := J) (U := U) 𝒰 D I T₁o K' y
    have hη : HEq ξ₂ ξ₁ :=
      hη₂.trans (hxy.trans hη₁.symm)
    have hsourceOverType :
        (((localized_cover_descent_pullbackDatum_over_source
          (J := J) (U := U) 𝒰 D I T₂o).obj K).1.obj X₂) =
          (((localized_cover_descent_pullbackDatum_over_source
            (J := J) (U := U) 𝒰 D I T₁o).obj K').1.obj X₁) := by
      rcases K with ⟨Y, f, hf⟩
      simp [X₂, X₁, K', g', T₁o, T₂o,
        localized_cover_descent_pullbackDatum_over_source,
        localized_cover_descent_pullbackDatum,
        localized_cover_descent_pullback_arrow_map, Cover.Arrow.base]
      congr 2
      exact eq_of_heq (congr_arg_heq D.obj (by
        ext <;> simp [Category.assoc]))
    let R₂ :=
      (Pseudofunctor.DescentData.pullFunctor (J.pseudofunctorOver (Type w))
        (f := fun K : (𝒰.pullback I.f).Arrow ↦ K.f)
        (p := T₂o.hom)
        (f' := fun K : ((𝒰.pullback I.f).pullback T₂o.hom).Arrow ↦ K.f)
        (α := fun K ↦ K.base)
        (p' := fun _ ↦ 𝟙 _)
        (w := localized_cover_descent_pullbackDatum_w (J := J) (U := I.Y)
          (𝒰.pullback I.f) T₂o)).obj
          (((J.pseudofunctorOver (Type w)).toDescentData
            (fun K : (𝒰.pullback I.f).Arrow ↦ K.f)).obj (D.obj I))
    let R₁ :=
      (Pseudofunctor.DescentData.pullFunctor (J.pseudofunctorOver (Type w))
        (f := fun K : (𝒰.pullback I.f).Arrow ↦ K.f)
        (p := T₁o.hom)
        (f' := fun K : ((𝒰.pullback I.f).pullback T₁o.hom).Arrow ↦ K.f)
        (α := fun K ↦ K.base)
        (p' := fun _ ↦ 𝟙 _)
        (w := localized_cover_descent_pullbackDatum_w (J := J) (U := I.Y)
          (𝒰.pullback I.f) T₁o)).obj
          (((J.pseudofunctorOver (Type w)).toDescentData
            (fun K : (𝒰.pullback I.f).Arrow ↦ K.f)).obj (D.obj I))
    have hmiddleCodType : (R₂.obj K).1.obj X₂ = (R₁.obj K').1.obj X₁ := by
      rcases K with ⟨Y, f, hf⟩
      simp [R₂, R₁, X₂, X₁, K', g', T₁o, T₂o,
        Pseudofunctor.toDescentData,
        localized_cover_descent_pullback_arrow_map, Cover.Arrow.base,
        Category.assoc]
    let θ := (localized_cover_descent_pullbackDatum_toDescentData_obj
      (J := J) (U := U) 𝒰 D I).hom
    have hμ₂ : HEq
        (μ₂.hom.app X₂ (ξ₂))
        ((θ.hom K.base).hom.app
          (Opposite.op ((Over.map (𝟙 K.Y)).obj (Over.mk (𝟙 K.Y))))
          (ξ₂)) := by
      simpa only [μ₂, θ, X₂] using
        pullFunctor_map_id_app_heq
          (J := J) (𝒱 := 𝒰.pullback I.f)
          (φ := (localized_cover_descent_pullbackDatum_toDescentData_obj
            (J := J) (U := U) 𝒰 D I).hom)
          T₂o K (ξ₂)
    have hμ₁ : HEq
        (μ₁.hom.app X₁ (ξ₁))
        ((θ.hom K'.base).hom.app
          (Opposite.op ((Over.map (𝟙 K'.Y)).obj (Over.mk (𝟙 K'.Y))))
          (ξ₁)) := by
      simpa only [μ₁, θ, X₁] using
        pullFunctor_map_id_app_heq
          (J := J) (𝒱 := 𝒰.pullback I.f)
          (φ := (localized_cover_descent_pullbackDatum_toDescentData_obj
            (J := J) (U := U) 𝒰 D I).hom)
          T₁o K' (ξ₁)
    have hμmid : HEq
        ((θ.hom K.base).hom.app
          (Opposite.op ((Over.map (𝟙 K.Y)).obj (Over.mk (𝟙 K.Y))))
          (ξ₂))
        ((θ.hom K'.base).hom.app
          (Opposite.op ((Over.map (𝟙 K'.Y)).obj (Over.mk (𝟙 K'.Y))))
          (ξ₁)) :=
      by
        apply fun_app_heq_of_type_eqs hsourceOverType hmiddleCodType ?_ hη
        have hbase : K.base = K'.base := by
          exact (localized_cover_descent_pullback_arrow_map_base
            (J := J) (U := I.Y) (𝒰.pullback I.f) g' K).symm
        exact congr_arg_heq
          (fun L : (𝒰.pullback I.f).Arrow =>
            (θ.hom L).hom.app
              (Opposite.op ((Over.map (𝟙 L.Y)).obj (Over.mk (𝟙 L.Y)))))
          hbase
    have hμ : HEq
        (μ₂.hom.app X₂ (ξ₂))
        (μ₁.hom.app X₁ (ξ₁)) :=
      hμ₂.trans (hμmid.trans hμ₁.symm)
    have hν₂ : HEq
        (ν₂.hom.app X₂ (μ₂.hom.app X₂ (ξ₂)))
        (μ₂.hom.app X₂ (ξ₂)) := by
      simpa [ν₂, R₂, X₂] using
        toDescentDataCompPullFunctorIso_hom_app_heq
          (J := J) (𝒱 := 𝒰.pullback I.f) (M := D.obj I) T₂o K
          (μ₂.hom.app X₂ (ξ₂))
    have hν₁ : HEq
        (ν₁.hom.app X₁ (μ₁.hom.app X₁ (ξ₁)))
        (μ₁.hom.app X₁ (ξ₁)) := by
      simpa [ν₁, R₁, X₁] using
        toDescentDataCompPullFunctorIso_hom_app_heq
          (J := J) (𝒱 := 𝒰.pullback I.f) (M := D.obj I) T₁o K'
          (μ₁.hom.app X₁ (ξ₁))
    simpa [φ₂, φ₁, η₂, η₁, μ₂, μ₁, ν₂, ν₁,
      localized_cover_descent_pullbackDatum_over_direct_to_component_iso,
      Category.assoc] using hν₂.trans (hμ.trans hν₁.symm)
  have hleft :
      HEq
        (localized_cover_descent_pullbackDatum_over_direct_section_equiv_component
          (J := J) (U := U) 𝒰 D I T₂o K x)
        (φ₂.hom.app X₂ x) := by
    have h :=
      localized_cover_descent_pullbackDatum_over_direct_to_component_iso_apply
        (J := J) (U := U) 𝒰 D I T₂o K x
    exact (heq_of_eq h).symm.trans (cast_heq _ _)
  have hright :
      HEq (φ₁.hom.app X₁ y)
        (localized_cover_descent_pullbackDatum_over_direct_section_equiv_component
          (J := J) (U := U) 𝒰 D I T₁o K' y) := by
    have h :=
      localized_cover_descent_pullbackDatum_over_direct_to_component_iso_apply
        (J := J) (U := U) 𝒰 D I T₁o K' y
    exact (cast_heq _ _).symm.trans (heq_of_eq h)
  exact hleft.trans (happ.trans hright)

end

end GrothendieckTopology
end CategoryTheory
