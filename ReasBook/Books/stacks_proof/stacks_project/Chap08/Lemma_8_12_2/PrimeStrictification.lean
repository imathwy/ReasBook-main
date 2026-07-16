import stacks_proof.stacks_project.Chap08.Lemma_8_12_2.PullHomConjugation
import stacks_proof.stacks_project.Chap08.Lemma_8_12_2.ChosenOverlaps

open CategoryTheory.Limits
open CategoryTheory.GrothendieckTopology.Cover

universe uC uD uS vC vD vS

namespace CategoryTheory

section

variable {C : Type uC} {D : Type uD} {S : Type uS}
variable [Category.{vC} C] [Category.{vD} D] [Category.{vS} S]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable (u : C ⥤ D)

/-- Helper for Chap08 Lemma 8 12 2: the component morphisms of a prime descent-data
isomorphism compose to the identity in one direction. -/
theorem descentDataPrimeComponentIso_hom_inv_id
    {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{vS, uS}}
    {ι : Type*} {U : C} {X : ι → C} {f : ∀ i, X i ⟶ U}
    {sq : ∀ i j, ChosenPullback (f i) (f j)}
    {sq₃ : ∀ (i₁ i₂ i₃ : ι), ChosenPullback₃ (sq i₁ i₂) (sq i₂ i₃) (sq i₁ i₃)}
    {D₁ D₂ : F.DescentData' sq sq₃} (e : D₁ ≅ D₂) (i : ι) :
    e.hom.hom i ≫ e.inv.hom i = 𝟙 (D₁.obj i) := by
  -- The owner lemma records the same component identity with the equality reversed.
  simpa using (Pseudofunctor.DescentData'.comp_hom e.hom e.inv i).symm

/-- Helper for Chap08 Lemma 8 12 2: the component morphisms of a prime descent-data
isomorphism compose to the identity in the other direction. -/
theorem descentDataPrimeComponentIso_inv_hom_id
    {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{vS, uS}}
    {ι : Type*} {U : C} {X : ι → C} {f : ∀ i, X i ⟶ U}
    {sq : ∀ i j, ChosenPullback (f i) (f j)}
    {sq₃ : ∀ (i₁ i₂ i₃ : ι), ChosenPullback₃ (sq i₁ i₂) (sq i₂ i₃) (sq i₁ i₃)}
    {D₁ D₂ : F.DescentData' sq sq₃} (e : D₁ ≅ D₂) (i : ι) :
    e.inv.hom i ≫ e.hom.hom i = 𝟙 (D₂.obj i) := by
  -- The owner lemma records the same component identity with the equality reversed.
  simpa using (Pseudofunctor.DescentData'.comp_hom e.inv e.hom i).symm

/-- Helper for Chap08 Lemma 8 12 2: take the component isomorphism of an isomorphism of
prime descent data. -/
def descentDataPrimeComponentIso
    {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{vS, uS}}
    {ι : Type*} {U : C} {X : ι → C} {f : ∀ i, X i ⟶ U}
    {sq : ∀ i j, ChosenPullback (f i) (f j)}
    {sq₃ : ∀ (i₁ i₂ i₃ : ι), ChosenPullback₃ (sq i₁ i₂) (sq i₂ i₃) (sq i₁ i₃)}
    {D₁ D₂ : F.DescentData' sq sq₃} (e : D₁ ≅ D₂) (i : ι) :
    D₁.obj i ≅ D₂.obj i where
  hom := e.hom.hom i
  inv := e.inv.hom i
  hom_inv_id := descentDataPrimeComponentIso_hom_inv_id e i
  inv_hom_id := descentDataPrimeComponentIso_inv_hom_id e i

/-- Helper for Chap08 Lemma 8 12 2: the target-side chosen-overlap morphism obtained by
strictifying the components of a source prime descent datum. -/
noncomputable def pullbackProjection_targetDescentDataPrimeHom
    [HasPullbacks C] [PreservesLimitsOfShape WalkingCospan u]
    (p : S ⥤ D) [p.IsFibered] {U : C} (T : J.Cover U)
    (Dsrc : (canonicalFiberPseudofunctor (CategoricalPullback.π₁ u p)).DescentData'
      (coverSourceChosenPullback T) (coverSourceChosenPullback₃ T))
    (I L : T.Arrow) :
    ((canonicalFiberPseudofunctor p).map (coverImageChosenPullback u T I L).p₁.op.toLoc).toFunctor.obj
        (pullbackProjection_targetFiberObj u p (Dsrc.obj I)) ⟶
      ((canonicalFiberPseudofunctor p).map (coverImageChosenPullback u T I L).p₂.op.toLoc).toFunctor.obj
        (pullbackProjection_targetFiberObj u p (Dsrc.obj L)) :=
  (pullbackProjection_targetRestrictionIso u p (coverSourceChosenPullback T I L).p₁
      (Dsrc.obj I)).inv ≫
    (pullbackProjection_targetFiberFunctor u p (coverSourceChosenPullback T I L).pullback).map
      (Dsrc.hom I L) ≫
    (pullbackProjection_targetRestrictionIso u p (coverSourceChosenPullback T I L).p₂
      (Dsrc.obj L)).hom

/-- Helper for Chap08 Lemma 8 12 2: target prime pullback of strictified transition maps is the
strictification of the corresponding source prime pullback. -/
theorem pullbackProjection_targetDescentDataPrimeHom_pullHom'
    [HasPullbacks C] [PreservesLimitsOfShape WalkingCospan u]
    (p : S ⥤ D) [p.IsFibered] {U Y : C} (T : J.Cover U)
    (Dsrc : (canonicalFiberPseudofunctor (CategoricalPullback.π₁ u p)).DescentData'
      (coverSourceChosenPullback T) (coverSourceChosenPullback₃ T))
    {I L : T.Arrow} (q : Y ⟶ U) (f₁ : Y ⟶ I.Y) (f₂ : Y ⟶ L.Y)
    (hf₁ : f₁ ≫ I.f = q) (hf₂ : f₂ ≫ L.f = q)
    (hf₁t : u.map f₁ ≫ u.map I.f = u.map q)
    (hf₂t : u.map f₂ ≫ u.map L.f = u.map q) :
    Pseudofunctor.DescentData'.pullHom'
      (F := canonicalFiberPseudofunctor p)
      (sq := coverImageChosenPullback u T)
      (pullbackProjection_targetDescentDataPrimeHom u p T Dsrc)
      (u.map q) (u.map f₁) (u.map f₂) hf₁t hf₂t =
    (pullbackProjection_targetRestrictionIso u p f₁ (Dsrc.obj I)).inv ≫
      (pullbackProjection_targetFiberFunctor u p Y).map
        (Pseudofunctor.DescentData'.pullHom'
          (F := canonicalFiberPseudofunctor (CategoricalPullback.π₁ u p))
          (sq := coverSourceChosenPullback T) Dsrc.hom q f₁ f₂ hf₁ hf₂) ≫
      (pullbackProjection_targetRestrictionIso u p f₂ (Dsrc.obj L)).hom := by
  -- Rewrite both chosen-pullback variants to the same lifted source overlap and then apply the
  -- target-restriction conjugation theorem.
  let srcSq := coverSourceChosenPullback T I L
  have hw : f₁ ≫ I.f = f₂ ≫ L.f := hf₁.trans hf₂.symm
  let k := srcSq.isPullback.lift f₁ f₂ hw
  have hk₁ : k ≫ srcSq.p₁ = f₁ := by
    simpa [k] using srcSq.isPullback.lift_fst f₁ f₂ hw
  have hk₂ : k ≫ srcSq.p₂ = f₂ := by
    simpa [k] using srcSq.isPullback.lift_snd f₁ f₂ hw
  have hkTarget₁ : u.map k ≫ u.map srcSq.p₁ = u.map f₁ := by
    rw [← u.map_comp, hk₁]
  have hkTarget₂ : u.map k ≫ u.map srcSq.p₂ = u.map f₂ := by
    rw [← u.map_comp, hk₂]
  have htarget₁ : u.map k ≫ (coverImageChosenPullback u T I L).p₁ = u.map f₁ := by
    simpa [srcSq, coverImageChosenPullback, imageChosenPullback] using hkTarget₁
  have htarget₂ : u.map k ≫ (coverImageChosenPullback u T I L).p₂ = u.map f₂ := by
    simpa [srcSq, coverImageChosenPullback, imageChosenPullback] using hkTarget₂
  have htarget :
      Pseudofunctor.DescentData'.pullHom'
          (F := canonicalFiberPseudofunctor p)
          (sq := coverImageChosenPullback u T)
          (pullbackProjection_targetDescentDataPrimeHom u p T Dsrc)
          (u.map q) (u.map f₁) (u.map f₂) hf₁t hf₂t =
        Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (pullbackProjection_targetDescentDataPrimeHom u p T Dsrc I L)
          (u.map k) (u.map f₁) (u.map f₂) hkTarget₁ hkTarget₂ := by
    exact
      Pseudofunctor.DescentData'.pullHom'_eq_pullHom
        (F := canonicalFiberPseudofunctor p)
        (sq := coverImageChosenPullback u T)
        (hom := pullbackProjection_targetDescentDataPrimeHom u p T Dsrc)
        (q := u.map q) (f₁ := u.map f₁) (f₂ := u.map f₂)
        (p := u.map k) hf₁t hf₂t htarget₁ htarget₂
  have hsource :
      Pseudofunctor.DescentData'.pullHom'
          (F := canonicalFiberPseudofunctor (CategoricalPullback.π₁ u p))
          (sq := coverSourceChosenPullback T) Dsrc.hom q f₁ f₂ hf₁ hf₂ =
        Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (Dsrc.hom I L) k f₁ f₂ hk₁ hk₂ := by
    exact
      Pseudofunctor.DescentData'.pullHom'_eq_pullHom
        (F := canonicalFiberPseudofunctor (CategoricalPullback.π₁ u p))
        (sq := coverSourceChosenPullback T) (hom := Dsrc.hom)
        (q := q) (f₁ := f₁) (f₂ := f₂) (p := k) hf₁ hf₂ hk₁ hk₂
  have hconj :=
    pullbackProjection_targetRestrictionIso_pullHom_conjugation_pair u p
      srcSq.p₁ srcSq.p₂ k f₁ f₂ hk₁ hk₂ hkTarget₁ hkTarget₂
      (Dsrc.obj I) (Dsrc.obj L) (Dsrc.hom I L)
  calc
    Pseudofunctor.DescentData'.pullHom'
        (F := canonicalFiberPseudofunctor p)
        (sq := coverImageChosenPullback u T)
        (pullbackProjection_targetDescentDataPrimeHom u p T Dsrc)
        (u.map q) (u.map f₁) (u.map f₂) hf₁t hf₂t =
        Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (pullbackProjection_targetDescentDataPrimeHom u p T Dsrc I L)
          (u.map k) (u.map f₁) (u.map f₂) hkTarget₁ hkTarget₂ := htarget
    _ =
        (pullbackProjection_targetRestrictionIso u p f₁ (Dsrc.obj I)).inv ≫
          (pullbackProjection_targetFiberFunctor u p Y).map
            (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
              (Dsrc.hom I L) k f₁ f₂ hk₁ hk₂) ≫
          (pullbackProjection_targetRestrictionIso u p f₂ (Dsrc.obj L)).hom := by
          simpa [pullbackProjection_targetDescentDataPrimeHom, srcSq] using hconj.symm
    _ =
        (pullbackProjection_targetRestrictionIso u p f₁ (Dsrc.obj I)).inv ≫
          (pullbackProjection_targetFiberFunctor u p Y).map
            (Pseudofunctor.DescentData'.pullHom'
              (F := canonicalFiberPseudofunctor (CategoricalPullback.π₁ u p))
              (sq := coverSourceChosenPullback T) Dsrc.hom q f₁ f₂ hf₁ hf₂) ≫
          (pullbackProjection_targetRestrictionIso u p f₂ (Dsrc.obj L)).hom := by
          rw [hsource]

/-- Helper for Chap08 Lemma 8 12 2: the strictified target prime descent morphism is the
identity on a repeated cover index. -/
theorem pullbackProjection_targetDescentDataPrime_hom_self
    [HasPullbacks C] [PreservesLimitsOfShape WalkingCospan u]
    (p : S ⥤ D) [p.IsFibered] {U : C} (T : J.Cover U)
    (Dsrc : (canonicalFiberPseudofunctor (CategoricalPullback.π₁ u p)).DescentData'
      (coverSourceChosenPullback T) (coverSourceChosenPullback₃ T))
    (I : T.Arrow) :
    Pseudofunctor.DescentData'.pullHom'
      (F := canonicalFiberPseudofunctor p)
      (sq := coverImageChosenPullback u T)
      (pullbackProjection_targetDescentDataPrimeHom u p T Dsrc)
      (u.map I.f) (𝟙 (u.obj I.Y)) (𝟙 (u.obj I.Y)) = 𝟙 _ := by
  -- The general pullHom comparison reduces the target identity condition to the source one.
  have hf : 𝟙 I.Y ≫ I.f = I.f := by simp
  have hfTarget : u.map (𝟙 I.Y) ≫ u.map I.f = u.map I.f := by simp
  have h := pullbackProjection_targetDescentDataPrimeHom_pullHom' u p T Dsrc I.f
    (𝟙 I.Y) (𝟙 I.Y) hf hf hfTarget hfTarget
  have hsrc := Pseudofunctor.DescentData'.pullHom'_self Dsrc I.f (𝟙 I.Y) hf
  rw [hsrc] at h
  have htargetAtMap :
      Pseudofunctor.DescentData'.pullHom'
        (F := canonicalFiberPseudofunctor p)
        (sq := coverImageChosenPullback u T)
        (pullbackProjection_targetDescentDataPrimeHom u p T Dsrc)
        (u.map I.f) (u.map (𝟙 I.Y)) (u.map (𝟙 I.Y)) hfTarget hfTarget = 𝟙 _ := by
    let eI := pullbackProjection_targetRestrictionIso u p (𝟙 I.Y) (Dsrc.obj I)
    calc
      Pseudofunctor.DescentData'.pullHom'
          (F := canonicalFiberPseudofunctor p)
          (sq := coverImageChosenPullback u T)
          (pullbackProjection_targetDescentDataPrimeHom u p T Dsrc)
          (u.map I.f) (u.map (𝟙 I.Y)) (u.map (𝟙 I.Y)) hfTarget hfTarget =
          eI.inv ≫
            pullbackProjection_targetFiberHom u p
              (𝟙 (((canonicalFiberPseudofunctor (CategoricalPullback.π₁ u p)).map
                (𝟙 I.Y).op.toLoc).toFunctor.obj (Dsrc.obj I))) ≫
            eI.hom := by
            simpa [eI] using h
      _ = eI.inv ≫ 𝟙 _ ≫ eI.hom := by
            have hId := pullbackProjection_targetFiberHom_id u p
              (((canonicalFiberPseudofunctor (CategoricalPullback.π₁ u p)).map
                (𝟙 I.Y).op.toLoc).toFunctor.obj (Dsrc.obj I))
            simpa [Category.assoc] using
              congrArg (fun t ↦ eI.inv ≫ t ≫ eI.hom) hId
      _ = 𝟙 _ := by
            simp
  convert htargetAtMap using 2
  all_goals simp [Functor.map_id]

/-- Helper for Chap08 Lemma 8 12 2: the strictified target prime descent morphisms satisfy the
cocycle identity on chosen triple overlaps. -/
theorem pullbackProjection_targetDescentDataPrime_hom_comp
    [HasPullbacks C] [PreservesLimitsOfShape WalkingCospan u]
    (p : S ⥤ D) [p.IsFibered] {U : C} (T : J.Cover U)
    (Dsrc : (canonicalFiberPseudofunctor (CategoricalPullback.π₁ u p)).DescentData'
      (coverSourceChosenPullback T) (coverSourceChosenPullback₃ T))
    (I J₁ L : T.Arrow) :
    Pseudofunctor.DescentData'.pullHom'
      (F := canonicalFiberPseudofunctor p)
      (sq := coverImageChosenPullback u T)
      (pullbackProjection_targetDescentDataPrimeHom u p T Dsrc)
      (coverImageChosenPullback₃ u T I J₁ L).p
      (coverImageChosenPullback₃ u T I J₁ L).p₁
      (coverImageChosenPullback₃ u T I J₁ L).p₂ ≫
    Pseudofunctor.DescentData'.pullHom'
      (F := canonicalFiberPseudofunctor p)
      (sq := coverImageChosenPullback u T)
      (pullbackProjection_targetDescentDataPrimeHom u p T Dsrc)
      (coverImageChosenPullback₃ u T I J₁ L).p
      (coverImageChosenPullback₃ u T I J₁ L).p₂
      (coverImageChosenPullback₃ u T I J₁ L).p₃ =
    Pseudofunctor.DescentData'.pullHom'
      (F := canonicalFiberPseudofunctor p)
      (sq := coverImageChosenPullback u T)
      (pullbackProjection_targetDescentDataPrimeHom u p T Dsrc)
      (coverImageChosenPullback₃ u T I J₁ L).p
      (coverImageChosenPullback₃ u T I J₁ L).p₁
      (coverImageChosenPullback₃ u T I J₁ L).p₃ := by
  -- Rewrite the three target prime pullbacks to strictified source pullbacks and use the source
  -- cocycle condition.
  let srcTri := coverSourceChosenPullback₃ T I J₁ L
  have hf₁ : srcTri.p₁ ≫ I.f = srcTri.p := srcTri.w₁
  have hf₂ : srcTri.p₂ ≫ J₁.f = srcTri.p := srcTri.w₂
  have hf₃ : srcTri.p₃ ≫ L.f = srcTri.p := srcTri.w₃
  have hf₁t : u.map srcTri.p₁ ≫ u.map I.f = u.map srcTri.p := by
    rw [← u.map_comp, hf₁]
  have hf₂t : u.map srcTri.p₂ ≫ u.map J₁.f = u.map srcTri.p := by
    rw [← u.map_comp, hf₂]
  have hf₃t : u.map srcTri.p₃ ≫ u.map L.f = u.map srcTri.p := by
    rw [← u.map_comp, hf₃]
  have h₁₂ :=
    pullbackProjection_targetDescentDataPrimeHom_pullHom' u p T Dsrc srcTri.p
      srcTri.p₁ srcTri.p₂ hf₁ hf₂ hf₁t hf₂t
  have h₂₃ :=
    pullbackProjection_targetDescentDataPrimeHom_pullHom' u p T Dsrc srcTri.p
      srcTri.p₂ srcTri.p₃ hf₂ hf₃ hf₂t hf₃t
  have h₁₃ :=
    pullbackProjection_targetDescentDataPrimeHom_pullHom' u p T Dsrc srcTri.p
      srcTri.p₁ srcTri.p₃ hf₁ hf₃ hf₁t hf₃t
  have hsource :
      Pseudofunctor.DescentData'.pullHom'
          (F := canonicalFiberPseudofunctor (CategoricalPullback.π₁ u p))
          (sq := coverSourceChosenPullback T) Dsrc.hom srcTri.p srcTri.p₁ srcTri.p₂ hf₁ hf₂ ≫
        Pseudofunctor.DescentData'.pullHom'
          (F := canonicalFiberPseudofunctor (CategoricalPullback.π₁ u p))
          (sq := coverSourceChosenPullback T) Dsrc.hom srcTri.p srcTri.p₂ srcTri.p₃ hf₂ hf₃ =
        Pseudofunctor.DescentData'.pullHom'
          (F := canonicalFiberPseudofunctor (CategoricalPullback.π₁ u p))
          (sq := coverSourceChosenPullback T) Dsrc.hom srcTri.p srcTri.p₁ srcTri.p₃ hf₁ hf₃ :=
    Pseudofunctor.DescentData'.comp_pullHom' Dsrc srcTri.p srcTri.p₁ srcTri.p₂ srcTri.p₃
      hf₁ hf₂ hf₃
  suffices htarget :
      Pseudofunctor.DescentData'.pullHom'
          (F := canonicalFiberPseudofunctor p)
          (sq := coverImageChosenPullback u T)
          (pullbackProjection_targetDescentDataPrimeHom u p T Dsrc)
          (u.map srcTri.p) (u.map srcTri.p₁) (u.map srcTri.p₂) hf₁t hf₂t ≫
        Pseudofunctor.DescentData'.pullHom'
          (F := canonicalFiberPseudofunctor p)
          (sq := coverImageChosenPullback u T)
          (pullbackProjection_targetDescentDataPrimeHom u p T Dsrc)
          (u.map srcTri.p) (u.map srcTri.p₂) (u.map srcTri.p₃) hf₂t hf₃t =
        Pseudofunctor.DescentData'.pullHom'
          (F := canonicalFiberPseudofunctor p)
          (sq := coverImageChosenPullback u T)
          (pullbackProjection_targetDescentDataPrimeHom u p T Dsrc)
          (u.map srcTri.p) (u.map srcTri.p₁) (u.map srcTri.p₃) hf₁t hf₃t by
    convert htarget using 1
  let Fsrc := pullbackProjection_targetFiberFunctor u p srcTri.chosenPullback.pullback
  let e₁ := pullbackProjection_targetRestrictionIso u p srcTri.p₁ (Dsrc.obj I)
  let e₂ := pullbackProjection_targetRestrictionIso u p srcTri.p₂ (Dsrc.obj J₁)
  let e₃ := pullbackProjection_targetRestrictionIso u p srcTri.p₃ (Dsrc.obj L)
  let τ₁₂ :=
    Pseudofunctor.DescentData'.pullHom'
      (F := canonicalFiberPseudofunctor (CategoricalPullback.π₁ u p))
      (sq := coverSourceChosenPullback T) Dsrc.hom srcTri.p srcTri.p₁ srcTri.p₂ hf₁ hf₂
  let τ₂₃ :=
    Pseudofunctor.DescentData'.pullHom'
      (F := canonicalFiberPseudofunctor (CategoricalPullback.π₁ u p))
      (sq := coverSourceChosenPullback T) Dsrc.hom srcTri.p srcTri.p₂ srcTri.p₃ hf₂ hf₃
  let τ₁₃ :=
    Pseudofunctor.DescentData'.pullHom'
      (F := canonicalFiberPseudofunctor (CategoricalPullback.π₁ u p))
      (sq := coverSourceChosenPullback T) Dsrc.hom srcTri.p srcTri.p₁ srcTri.p₃ hf₁ hf₃
  have hsourceMap : Fsrc.map τ₁₂ ≫ Fsrc.map τ₂₃ = Fsrc.map τ₁₃ := by
    rw [← Functor.map_comp]
    exact congrArg (fun t ↦ Fsrc.map t) hsource
  rw [h₁₂, h₂₃, h₁₃]
  change (e₁.inv ≫ Fsrc.map τ₁₂ ≫ e₂.hom) ≫
      e₂.inv ≫ Fsrc.map τ₂₃ ≫ e₃.hom =
    e₁.inv ≫ Fsrc.map τ₁₃ ≫ e₃.hom
  calc
    (e₁.inv ≫ Fsrc.map τ₁₂ ≫ e₂.hom) ≫
        e₂.inv ≫ Fsrc.map τ₂₃ ≫ e₃.hom =
      e₁.inv ≫ Fsrc.map τ₁₂ ≫ (e₂.hom ≫ e₂.inv) ≫
        Fsrc.map τ₂₃ ≫ e₃.hom := by
        simp only [Category.assoc]
    _ = e₁.inv ≫ Fsrc.map τ₁₂ ≫ Fsrc.map τ₂₃ ≫ e₃.hom := by
        calc
          e₁.inv ≫ Fsrc.map τ₁₂ ≫ (e₂.hom ≫ e₂.inv) ≫ Fsrc.map τ₂₃ ≫
              e₃.hom =
            e₁.inv ≫ Fsrc.map τ₁₂ ≫ 𝟙 _ ≫ Fsrc.map τ₂₃ ≫ e₃.hom := by
              exact congrArg
                (fun t ↦ e₁.inv ≫ Fsrc.map τ₁₂ ≫ t ≫ Fsrc.map τ₂₃ ≫ e₃.hom)
                e₂.hom_inv_id
          _ = e₁.inv ≫ Fsrc.map τ₁₂ ≫ Fsrc.map τ₂₃ ≫ e₃.hom := by
              simp only [Category.id_comp]
    _ = e₁.inv ≫ (Fsrc.map τ₁₂ ≫ Fsrc.map τ₂₃) ≫ e₃.hom := by
        simp only [Category.assoc]
    _ = e₁.inv ≫ Fsrc.map τ₁₃ ≫ e₃.hom := by
        exact congrArg (fun t ↦ e₁.inv ≫ t ≫ e₃.hom) hsourceMap

/-- Helper for Chap08 Lemma 8 12 2: strictifying a source prime descent datum gives a target
prime descent datum for the image cover. -/
noncomputable def pullbackProjection_targetDescentDataPrime
    [HasPullbacks C] [PreservesLimitsOfShape WalkingCospan u]
    (p : S ⥤ D) [p.IsFibered] {U : C} (T : J.Cover U)
    (Dsrc : (canonicalFiberPseudofunctor (CategoricalPullback.π₁ u p)).DescentData'
      (coverSourceChosenPullback T) (coverSourceChosenPullback₃ T)) :
    (canonicalFiberPseudofunctor p).DescentData'
      (coverImageChosenPullback u T) (coverImageChosenPullback₃ u T) where
  obj I := pullbackProjection_targetFiberObj u p (Dsrc.obj I)
  hom := pullbackProjection_targetDescentDataPrimeHom u p T Dsrc
  pullHom'_hom_self := pullbackProjection_targetDescentDataPrime_hom_self u p T Dsrc
  pullHom'_hom_comp := pullbackProjection_targetDescentDataPrime_hom_comp u p T Dsrc

/-- Helper for Chap08 Lemma 8 12 2: the target stack descent functor followed by the prime
descent equivalence. -/
noncomputable def pullbackProjection_targetPrimeDescentFunctor
    [HasPullbacks C] [PreservesLimitsOfShape WalkingCospan u]
    (p : S ⥤ D) [p.IsFibered] {U : C} (T : J.Cover U) :
    p.Fiber (u.obj U) ⥤
      (canonicalFiberPseudofunctor p).DescentData'
        (coverImageChosenPullback u T) (coverImageChosenPullback₃ u T) :=
  (canonicalFiberPseudofunctor p).toDescentData (fun I : T.Arrow ↦ u.map I.f) ⋙
    Pseudofunctor.DescentData'.fromDescentDataFunctor
      (canonicalFiberPseudofunctor p) (coverImageChosenPullback u T)
      (coverImageChosenPullback₃ u T)

/-- Helper for Chap08 Lemma 8 12 2: the source stack descent functor followed by the prime
descent equivalence. -/
noncomputable def pullbackProjection_sourcePrimeDescentFunctor
    [HasPullbacks C]
    (p : S ⥤ D) [p.IsFibered] {U : C} (T : J.Cover U) :
    (CategoricalPullback.π₁ u p).Fiber U ⥤
      (canonicalFiberPseudofunctor (CategoricalPullback.π₁ u p)).DescentData'
        (coverSourceChosenPullback T) (coverSourceChosenPullback₃ T) :=
  (canonicalFiberPseudofunctor (CategoricalPullback.π₁ u p)).toDescentData
      (fun I : T.Arrow ↦ I.f) ⋙
    Pseudofunctor.DescentData'.fromDescentDataFunctor
      (canonicalFiberPseudofunctor (CategoricalPullback.π₁ u p))
      (coverSourceChosenPullback T) (coverSourceChosenPullback₃ T)

/-- Helper for Chap08 Lemma 8 12 2: the target-fiber component comparison induced by a target
prime descent isomorphism. -/
noncomputable def pullbackProjection_targetStrictComponentIso
    [HasPullbacks C] [PreservesLimitsOfShape WalkingCospan u]
    (p : S ⥤ D) [p.IsFibered] {U : C} (T : J.Cover U)
    (Dsrc : (canonicalFiberPseudofunctor (CategoricalPullback.π₁ u p)).DescentData'
      (coverSourceChosenPullback T) (coverSourceChosenPullback₃ T))
    (A : p.Fiber (u.obj U))
    (e : (pullbackProjection_targetPrimeDescentFunctor u p T).obj A ≅
      pullbackProjection_targetDescentDataPrime u p T Dsrc)
    (I : T.Arrow) :
    pullbackProjection_targetFiberObj u p
      ((pullbackProjection_sourcePrimeDescentFunctor u p T).obj
        (pullbackProjection_ofTargetFiberObj u p A) |>.obj I) ≅
      pullbackProjection_targetFiberObj u p (Dsrc.obj I) :=
  pullbackProjection_targetRestrictionIso u p I.f (pullbackProjection_ofTargetFiberObj u p A) ≪≫
    (((canonicalFiberPseudofunctor p).map (u.map I.f).op.toLoc).toFunctor.mapIso
      (pullbackProjection_targetFiberCounitIso u p A)) ≪≫
    descentDataPrimeComponentIso e I

/-- Helper for Chap08 Lemma 8 12 2: lift the target-fiber component comparison back through the
source fiber equivalence. -/
noncomputable def pullbackProjection_sourcePrimeComponentIso
    [HasPullbacks C] [PreservesLimitsOfShape WalkingCospan u]
    (p : S ⥤ D) [p.IsFibered] {U : C} (T : J.Cover U)
    (Dsrc : (canonicalFiberPseudofunctor (CategoricalPullback.π₁ u p)).DescentData'
      (coverSourceChosenPullback T) (coverSourceChosenPullback₃ T))
    (A : p.Fiber (u.obj U))
    (e : (pullbackProjection_targetPrimeDescentFunctor u p T).obj A ≅
      pullbackProjection_targetDescentDataPrime u p T Dsrc)
    (I : T.Arrow) :
    ((pullbackProjection_sourcePrimeDescentFunctor u p T).obj
        (pullbackProjection_ofTargetFiberObj u p A)).obj I ≅
      Dsrc.obj I :=
  let FsrcI := pullbackProjection_targetFiberFunctor u p I.Y
  letI : FsrcI.IsEquivalence := pullbackProjection_targetFiberFunctor_isEquivalence u p I.Y
  let hFsrcI : FsrcI.FullyFaithful := Functor.FullyFaithful.ofFullyFaithful FsrcI
  hFsrcI.preimageIso (pullbackProjection_targetStrictComponentIso u p T Dsrc A e I)

end

end CategoryTheory
