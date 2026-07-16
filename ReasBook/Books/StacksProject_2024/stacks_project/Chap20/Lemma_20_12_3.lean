import StacksProject_2024.stacks_project.Chap12.Lemma_12_29_1
import StacksProject_2024.stacks_project.Chap13.Lemma_13_15_2
import StacksProject_2024.stacks_project.Chap13.Lemma_13_15_6
import StacksProject_2024.stacks_project.Chap13.Lemma_13_16_4
import StacksProject_2024.stacks_project.Chap20.«20_2_0_3»
import StacksProject_2024.stacks_project.Chap20.«20_11_0_1»

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry

noncomputable section

universe u

/- Domain-style sampling for Lemma 20.12.3:
- primary domain: higher sheaf cohomology of abelian sheaves on a topological space, together
  with the flasqueness criterion for vanishing;
- sampled owner declarations:
  `CategoryTheory.Sheaf.H'`,
  `TopCat.Sheaf.IsFlasque`,
  `moduleUnderlyingSheaf X`,
  `CategoryTheory.Sheaf.cohomologyAtObject_isomorphic_to_homology_sections_of_injectiveResolution`;
- best owner abstraction: the canonical sheaf-cohomology object `F.H' p U`, with
  `TopCat.Sheaf.IsFlasque F` as the flasqueness owner on the same abelian sheaf;
- primitive data: a topological space `X`, an abelian sheaf `F : X.Sheaf AddCommGrpCat`, an open
  subset `U`, a positive degree `p`, and the flasqueness hypothesis on `F`;
- derived API: the ringed-space module specialization obtained by applying this theorem to
  `((moduleUnderlyingSheaf X).obj ℱ)`.

Source/core/bridge triage:
- `source-facing`: vanishing of the positive cohomology objects `H^p(U, F)` for a flasque
  abelian sheaf `F`;
- `core/canonical`: `CategoryTheory.Sheaf.H'` and `TopCat.Sheaf.IsFlasque`;
- `bridge/view`: the ringed-space specialization along `moduleUnderlyingSheaf X`.

This file should therefore keep the source-facing cohomology-vanishing statement as the main
public API at the sheaf level, with the module statement only as a specialization through the
canonical forgetful bridge `moduleUnderlyingSheaf X`. -/

namespace CategoryTheory.Sheaf

variable {X : TopCat.{u}}
variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [HasExt.{u} (X.Sheaf AddCommGrpCat.{u})]

local notation "JX" => Opens.grothendieckTopology X

/-- Helper for Lemma 20.12.3: the sections functor over a fixed open subset. -/
private abbrev sectionsAtOpenFunctor (U : Opens X) :
    X.Sheaf AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u} :=
  (sheafSections JX AddCommGrpCat.{u}).obj (op U)

/-- Helper for Lemma 20.12.3: sections over a fixed open subset form an additive functor on
abelian sheaves. -/
private instance sectionsAtOpen_additive (U : Opens X) :
    (sectionsAtOpenFunctor U).Additive := by
  -- Rewrite sections as evaluation on the underlying presheaf, where additivity is already
  -- available by instance search.
  simpa [sheafSections] using
    (inferInstance :
      ((sheafToPresheaf JX AddCommGrpCat.{u}) ⋙
        (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op U)).Additive)

/-- Helper for Lemma 20.12.3: sections over a fixed open subset preserve zero morphisms. -/
private instance sectionsAtOpen_preservesZeroMorphisms (U : Opens X) :
    (sectionsAtOpenFunctor U).PreservesZeroMorphisms := by
  refine ⟨fun A B ↦ ?_⟩
  rfl

/-- Helper for Lemma 20.12.3: morphisms from the free abelian representable presheaf on `U`
identify with sections over `U`. -/
private noncomputable def freeAbelianRepresentableHomEquivSections
    (U : Opens X) (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) :
    (((yoneda.obj U) ⋙ AddCommGrpCat.free) ⟶ P) ≃ P.obj (op U) :=
  ((AddCommGrpCat.adj.whiskerRight (Opens X)ᵒᵖ).homEquiv _ _).trans yonedaEquiv

omit [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [HasExt.{u} (X.Sheaf AddCommGrpCat.{u})] in
/-- Helper for Lemma 20.12.3: precomposition with the free abelian representable map induced by
an inclusion of opens matches restriction on sections. -/
private theorem freeAbelianRepresentableHomEquivSections_naturality
    {U V : Opens X} (i : V ⟶ U) (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u})
    (f : ((yoneda.obj U) ⋙ AddCommGrpCat.free) ⟶ P) :
    freeAbelianRepresentableHomEquivSections V P
        ((Functor.whiskerRight (yoneda.map i) AddCommGrpCat.free) ≫ f) =
      P.map i.op (freeAbelianRepresentableHomEquivSections U P f) := by
  -- Unfolding the comparison shows that both sides are just evaluation at the identity section.
  change
    yonedaEquiv
        (((AddCommGrpCat.adj.whiskerRight (Opens X)ᵒᵖ).homEquiv _ _)
          ((Functor.whiskerRight (yoneda.map i) AddCommGrpCat.free) ≫ f)) =
      P.map i.op
        (yonedaEquiv (((AddCommGrpCat.adj.whiskerRight (Opens X)ᵒᵖ).homEquiv _ _) f))
  have hpre :
      ((AddCommGrpCat.adj.whiskerRight (Opens X)ᵒᵖ).homEquiv _ _)
          ((Functor.whiskerRight (yoneda.map i) AddCommGrpCat.free) ≫ f) =
        yoneda.map i ≫
          (((AddCommGrpCat.adj.whiskerRight (Opens X)ᵒᵖ).homEquiv _ _) f) := by
    simpa using
      (AddCommGrpCat.adj.whiskerRight (Opens X)ᵒᵖ).homEquiv_naturality_left (yoneda.map i) f
  rw [hpre]
  simpa using
    (yonedaEquiv_naturality
      (((AddCommGrpCat.adj.whiskerRight (Opens X)ᵒᵖ).homEquiv _ _) f) i).symm

omit [HasExt.{u} (X.Sheaf AddCommGrpCat.{u})] in
/-- Helper for Lemma 20.12.3: forgetting an injective abelian sheaf to its underlying abelian
presheaf preserves injectivity because sheafification is an exact left adjoint. -/
private theorem injective_presheaf_of_injective_sheaf
    {F : X.Sheaf AddCommGrpCat.{u}} (hF : Injective F) :
    Injective ((sheafToPresheaf JX AddCommGrpCat.{u}).obj F) := by
  let G := sheafToPresheaf JX AddCommGrpCat.{u}
  let _ : G.PreservesInjectiveObjects :=
    CategoryTheory.preservesInjectiveObjects_of_exact_leftAdjoint
      (sheafificationAdjunction JX AddCommGrpCat.{u})
      ((exactFunctor_iff (presheafToSheaf JX AddCommGrpCat.{u})).2
        ⟨inferInstance, inferInstance⟩)
  -- Push injectivity through the sheafification adjunction once and keep the presheaf statement
  -- available for the final flasque-extension step.
  simpa [G] using G.injective_obj_of_injective hF

omit [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [HasExt.{u} (X.Sheaf AddCommGrpCat.{u})] in
/-- Helper for Lemma 20.12.3: the free-abelian Yoneda map induced by an inclusion of opens is
monic. -/
private theorem freeAbelianRepresentable_map_mono_of_open_inclusion
    {U V : Opens X} (i : V ⟶ U) :
    Mono ((Functor.whiskerRight (yoneda.map i) AddCommGrpCat.free :
      ((yoneda.obj V) ⋙ AddCommGrpCat.free) ⟶ ((yoneda.obj U) ⋙ AddCommGrpCat.free))) := by
  -- Check monomorphy objectwise and reduce the additive-group statement to injectivity of the
  -- corresponding map of free abelian groups.
  classical
  refine (NatTrans.mono_iff_mono_app _).2 ?_
  intro W
  rw [AddCommGrpCat.mono_iff_injective]
  let f : (W.unop ⟶ V) → (W.unop ⟶ U) := fun g ↦ g ≫ i
  have hf : Function.Injective f := by
    intro g g' hgg'
    exact (cancel_mono i).1 hgg'
  -- The free functor preserves this injectivity because `FreeAbelianGroup.map` admits the
  -- left inverse induced by a chosen retraction on generators.
  intro x y hxy
  let r : (W.unop ⟶ U) → FreeAbelianGroup (W.unop ⟶ V) := fun h ↦
    if hh : ∃ g : W.unop ⟶ V, f g = h then FreeAbelianGroup.of (Classical.choose hh) else 0
  have hr : ∀ g : W.unop ⟶ V, r (f g) = FreeAbelianGroup.of g := by
    intro g
    dsimp [r]
    split_ifs with hh
    · apply congrArg FreeAbelianGroup.of
      exact hf (Classical.choose_spec hh)
    · exact (hh ⟨g, rfl⟩).elim
  have hmap :
      Function.LeftInverse (FreeAbelianGroup.lift r) (AddCommGrpCat.free.map f) := by
    intro z
    change FreeAbelianGroup.lift r (FreeAbelianGroup.map f z) = z
    rw [← FreeAbelianGroup.lift_comp f r z]
    have hrf : r ∘ f = FreeAbelianGroup.of := by
      ext g
      exact hr g
    rw [hrf]
    simpa [FreeAbelianGroup.map]
      using (FreeAbelianGroup.map_id_apply z)
  exact hmap.injective hxy

omit [HasExt.{u} (X.Sheaf AddCommGrpCat.{u})] in
/-- Injective abelian sheaves on a topological space are flasque. -/
theorem isFlasque_of_injective
    {F : X.Sheaf AddCommGrpCat.{u}} (hF : Injective F) :
    TopCat.Sheaf.IsFlasque F := by
  let P := (sheafToPresheaf JX AddCommGrpCat.{u}).obj F
  have hP : Injective P := injective_presheaf_of_injective_sheaf hF
  let _ : Injective P := hP
  refine ⟨fun {U V} i ↦ ?_⟩
  -- Route correction: extend the section by factoring its free-representable avatar through the
  -- mono attached to the inclusion `i.unop : V.unop ⟶ U.unop`, exactly as in the source proof.
  refine (AddCommGrpCat.epi_iff_surjective _).2 ?_
  intro s
  let m :
      ((yoneda.obj V.unop) ⋙ AddCommGrpCat.free) ⟶
        ((yoneda.obj U.unop) ⋙ AddCommGrpCat.free) :=
    Functor.whiskerRight (yoneda.map i.unop) AddCommGrpCat.free
  let _ : Mono m := freeAbelianRepresentable_map_mono_of_open_inclusion i.unop
  let fs :
      ((yoneda.obj V.unop) ⋙ AddCommGrpCat.free) ⟶ P :=
    (freeAbelianRepresentableHomEquivSections V.unop P).symm s
  let t :
      ((yoneda.obj U.unop) ⋙ AddCommGrpCat.free) ⟶ P :=
    Injective.factorThru fs m
  refine ⟨freeAbelianRepresentableHomEquivSections U.unop P t, ?_⟩
  -- Naturality converts the factorization identity back into the desired restriction equation.
  calc
    P.map i (freeAbelianRepresentableHomEquivSections U.unop P t) =
        freeAbelianRepresentableHomEquivSections V.unop P (m ≫ t) := by
          symm
          simpa [m] using
            freeAbelianRepresentableHomEquivSections_naturality i.unop P t
    _ = freeAbelianRepresentableHomEquivSections V.unop P fs := by
          simpa [t] using (Injective.comp_factorThru fs m)
    _ = s := by
          simp [fs]

/-- Helper for Lemma 20.12.3: every abelian sheaf admits a monomorphism into a flasque sheaf. -/
private instance flasque_hasMonoEmbedding :
    ObjectProperty.HasMonoEmbedding
      (fun A : X.Sheaf AddCommGrpCat.{u} ↦ TopCat.Sheaf.IsFlasque A) where
  exists_mono A := by
    -- Use an injective envelope and then convert injectivity to flasqueness.
    let p := (EnoughInjectives.presentation A).some
    refine ⟨p.J, isFlasque_of_injective p.injective, p.f, inferInstance⟩

omit [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [HasExt.{u} (X.Sheaf AddCommGrpCat.{u})] in
/-- Helper for Lemma 20.12.3: flasqueness is invariant under isomorphism. -/
private theorem isFlasque_of_iso
    {F G : X.Sheaf AddCommGrpCat.{u}} (e : F ≅ G)
    (hF : TopCat.Sheaf.IsFlasque F) :
    TopCat.Sheaf.IsFlasque G := by
  let eInv := e.inv.hom
  let eHom := e.hom.hom
  refine ⟨fun {U V} i ↦ (AddCommGrpCat.epi_iff_surjective _).2 ?_⟩
  intro s
  obtain ⟨t, ht⟩ :=
    (AddCommGrpCat.epi_iff_surjective _).1 (hF.epi i) ((eInv.app V) s)
  refine ⟨(eHom.app U) t, ?_⟩
  calc
    G.presheaf.map i ((eHom.app U) t) = (eHom.app V) (F.presheaf.map i t) := by
      simpa using congrFun (NatTrans.naturality eHom i) t
    _ = (eHom.app V) ((eInv.app V) s) := by rw [ht]
    _ = ((e.inv ≫ e.hom).hom.app V) s := by rfl
    _ = s := by
      have happ := congrArg (fun α ↦ α.hom.app V) e.inv_hom_id
      change ((fun α : G ⟶ G ↦ α.hom.app V) (e.inv ≫ e.hom)) s = s
      rw [happ]
      rfl

/-- Helper for Lemma 20.12.3: the image inclusion of the left map factors through the image of
the right map in any short complex. -/
private theorem imageCompFactorThruImage_eq_zero
    {A : Type*} [Category A] [Abelian A] (S : ShortComplex A) :
    Abelian.image.ι S.f ≫ Abelian.factorThruImage S.g = 0 := by
  apply (cancel_mono (Abelian.image.ι S.g)).1
  simpa [Category.assoc, Abelian.image.fac] using S.zero

/-- Helper for Lemma 20.12.3: after applying a zero-morphism-preserving functor, the image-factor
row still has zero composite. -/
private theorem mapImageCompFactorThruImage_eq_zero
    {A B : Type*} [Category A] [Abelian A] [Category B] [HasZeroMorphisms B]
    {Φ : A ⥤ B} [Φ.PreservesZeroMorphisms] (S : ShortComplex A) :
    Φ.map (Abelian.image.ι S.f) ≫ Φ.map (Abelian.factorThruImage S.g) = 0 := by
  rw [← Φ.map_comp, imageCompFactorThruImage_eq_zero, Functor.map_zero]

/-- Helper for Lemma 20.12.3: after applying a zero-morphism-preserving functor, the left map of
the short complex still factors through the image of the right map. -/
private theorem mapCompFactorThruImage_eq_zero
    {A B : Type*} [Category A] [Abelian A] [Category B] [HasZeroMorphisms B]
    {Φ : A ⥤ B} [Φ.PreservesZeroMorphisms] (S : ShortComplex A) :
    Φ.map S.f ≫ Φ.map (Abelian.factorThruImage S.g) = 0 := by
  have h :
      S.f ≫ Abelian.factorThruImage S.g = 0 := by
    calc
      S.f ≫ Abelian.factorThruImage S.g =
          Abelian.factorThruImage S.f ≫
            (Abelian.image.ι S.f ≫ Abelian.factorThruImage S.g) := by
              simp
      _ = 0 := by
        simp [imageCompFactorThruImage_eq_zero]
  simpa [Functor.map_comp] using congrArg Φ.map h

/-- Helper for Lemma 20.12.3: exactness of a short complex transports to the row
`im(f) ⟶ X₂ ⟶ im(g)`. -/
private theorem exactImageFactorRowOfExact
    {A : Type*} [Category A] [Abelian A]
    (S : ShortComplex A) (hS : S.Exact) :
    (ShortComplex.mk
      (Abelian.image.ι S.f)
      (Abelian.factorThruImage S.g)
      (imageCompFactorThruImage_eq_zero S)).Exact := by
  let T : ShortComplex A :=
    ShortComplex.mk
      (Abelian.image.ι S.f)
      S.g
      (Abelian.image_ι_comp_eq_zero S.zero)
  let U : ShortComplex A :=
    ShortComplex.mk
      (Abelian.image.ι S.f)
      (Abelian.factorThruImage S.g)
      (imageCompFactorThruImage_eq_zero S)
  have hT : T.Exact := by
    simpa [T] using (ShortComplex.exact_iff_exact_image_ι S).1 hS
  let φ : U ⟶ T :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := Abelian.image.ι S.g
      comm₁₂ := by simp [T, U]
      comm₂₃ := by simpa [T, U] using (Abelian.image.fac S.g).symm }
  haveI : Epi φ.τ₁ := by
    dsimp [φ]
    infer_instance
  haveI : IsIso φ.τ₂ := by
    dsimp [φ]
    infer_instance
  haveI : Mono φ.τ₃ := by
    dsimp [φ]
    infer_instance
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).2 hT

/-- Helper for Lemma 20.12.3: exactness of a mapped image-factor row transports back to
exactness of the original mapped short complex. -/
private theorem exactOfMappedImageFactorRow
    {A B : Type*} [Category A] [Abelian A] [Category B] [HasZeroMorphisms B]
    {Φ : A ⥤ B} [Φ.PreservesZeroMorphisms]
    (S : ShortComplex A)
    (hU :
      (ShortComplex.mk
        (Φ.map (Abelian.image.ι S.f))
        (Φ.map (Abelian.factorThruImage S.g))
        (mapImageCompFactorThruImage_eq_zero S)).Exact)
    [Epi (Φ.map (Abelian.factorThruImage S.f))]
    [Mono (Φ.map (Abelian.image.ι S.g))] :
    (S.map Φ).Exact := by
  let U : ShortComplex B :=
    ShortComplex.mk
      (Φ.map (Abelian.image.ι S.f))
      (Φ.map (Abelian.factorThruImage S.g))
      (mapImageCompFactorThruImage_eq_zero S)
  let W : ShortComplex B :=
    ShortComplex.mk
      (Φ.map S.f)
      (Φ.map (Abelian.factorThruImage S.g))
      (mapCompFactorThruImage_eq_zero S)
  let D : ShortComplex B := S.map Φ
  let φ : W ⟶ U :=
    { τ₁ := Φ.map (Abelian.factorThruImage S.f)
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      comm₁₂ := by
        rw [Category.comp_id, ← Φ.map_comp]
        simpa [W, U] using Abelian.image.fac S.f
      comm₂₃ := by simp [W, U] }
  haveI : Epi φ.τ₁ := by
    dsimp [φ]
    infer_instance
  haveI : IsIso φ.τ₂ := by
    dsimp [φ]
    infer_instance
  haveI : Mono φ.τ₃ := by
    dsimp [φ]
    infer_instance
  have hW : W.Exact := by
    exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).2 (by simpa [U] using hU)
  let ψ : W ⟶ D :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := Φ.map (Abelian.image.ι S.g)
      comm₁₂ := by simp [W, D]
      comm₂₃ := by
        dsimp [W, D]
        simp only [Category.id_comp]
        rw [← Φ.map_comp]
        exact congrArg Φ.map (Abelian.image.fac S.g).symm }
  haveI : Epi ψ.τ₁ := by
    change Epi (𝟙 W.X₁)
    infer_instance
  haveI : IsIso ψ.τ₂ := by
    change IsIso (𝟙 W.X₂)
    infer_instance
  haveI : Mono ψ.τ₃ := by
    simpa [ψ] using (inferInstance : Mono (Φ.map (Abelian.image.ι S.g)))
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono ψ).1 hW

open CategoryTheory.Sheaf.Hom TopCat.Sheaf.IsFlasque in
omit [HasExt.{u} (X.Sheaf AddCommGrpCat.{u})] in
/-- Helper for Lemma 20.12.3: if the left and middle terms of a short exact sequence of abelian
sheaves are flasque, then taking sections over any open subset remains short exact. -/
private theorem sections_map_shortExact_of_isFlasque
    {U : Opens X} {S : ShortComplex (X.Sheaf AddCommGrpCat.{u})}
    (hS : S.ShortExact)
    (h₁ : TopCat.Sheaf.IsFlasque S.X₁)
    (h₂ : TopCat.Sheaf.IsFlasque S.X₂) :
    (S.map (sectionsAtOpenFunctor U)).ShortExact := by
  let fHom := S.f.hom
  let _ : TopCat.Sheaf.IsFlasque S.X₁ := h₁
  let _ : TopCat.Sheaf.IsFlasque S.X₂ := h₂
  have hmono_app : Mono (fHom.app (op U)) := by
    -- Monomorphisms of sheaves are detected on each section group.
    have hmono_nat : Mono fHom := (mono_iff_presheaf_mono JX AddCommGrpCat.{u} S.f).mp hS.mono_f
    exact ((NatTrans.mono_iff_mono_app _).mp hmono_nat) (op U)
  have hmono_map : Mono (S.map (sectionsAtOpenFunctor U)).f := by
    -- Rewrite the mapped left arrow as the sectionwise map at `U`.
    simpa [sectionsAtOpenFunctor, sheafSections] using hmono_app
  refine ShortComplex.ShortExact.mk' ?_ hmono_map ?_
  · -- Exactness on sections is the left-exact part together with the explicit element lift.
    rw [ShortComplex.ab_exact_iff]
    intro s hs
    exact TopCat.Sheaf.sections_exact_of_left_exact hS.exact hS.mono_f s hs
  · -- The right map is surjective because flasqueness makes local lifts global.
    exact epi_of_shortExact hS

open TopCat.Sheaf.IsFlasque in
omit [HasExt.{u} (X.Sheaf AddCommGrpCat.{u})] in
/-- Helper for Lemma 20.12.3: the quotient term of a short exact sequence of flasque abelian
sheaves is again flasque. -/
private theorem quotient_isFlasque_of_shortExact
    {S : ShortComplex (X.Sheaf AddCommGrpCat.{u})}
    (hS : S.ShortExact)
    (h₁ : TopCat.Sheaf.IsFlasque S.X₁)
    (h₂ : TopCat.Sheaf.IsFlasque S.X₂) :
    TopCat.Sheaf.IsFlasque S.X₃ := by
  refine ⟨fun {U V} i ↦ ?_⟩
  -- Start from a section on the smaller open and lift it through the short exact sequence there.
  refine (AddCommGrpCat.epi_iff_surjective _).2 ?_
  intro s
  let gHom := S.g.hom
  let _ : TopCat.Sheaf.IsFlasque S.X₁ := h₁
  let _ : TopCat.Sheaf.IsFlasque S.X₂ := h₂
  have hV :
      (S.map (sectionsAtOpenFunctor V.unop)).ShortExact :=
    sections_map_shortExact_of_isFlasque hS h₁ h₂
  have hsurj_g :
      Function.Surjective ((S.map (sectionsAtOpenFunctor V.unop)).g) :=
    (AddCommGrpCat.epi_iff_surjective _).1 hV.epi_g
  rcases hsurj_g s with ⟨tV, htV⟩
  -- Extend the middle-term lift across the inclusion by flasqueness of `S.X₂`.
  have hsurj_restr : Function.Surjective ((S.X₂).presheaf.map i) :=
    (AddCommGrpCat.epi_iff_surjective _).1 (h₂.epi i)
  rcases hsurj_restr tV with ⟨tU, htU⟩
  refine ⟨(gHom.app U) tU, ?_⟩
  -- Naturality of the quotient map identifies the restriction of the extended lift with `s`.
  calc
    (S.X₃).presheaf.map i ((gHom.app U) tU) = (gHom.app V) (((S.X₂).presheaf.map i) tU) := by
      simpa using congrFun (NatTrans.naturality gHom i) tU
    _ = (gHom.app V) tV := by simpa [htU]
    _ = s := htV

omit [HasExt.{u} (X.Sheaf AddCommGrpCat.{u})] in
/-- Helper for Lemma 20.12.3: the image row at degree `0`,
`im(ι₀) ⟶ I⁰ ⟶ im(d₀)`, is short exact. -/
private theorem injectiveResolution_image_shortExact_zero
    (F : X.Sheaf AddCommGrpCat.{u}) :
    let I : InjectiveResolution F := injectiveResolution F
    (ShortComplex.mk
      (Abelian.image.ι (I.ι.f 0))
      (Abelian.factorThruImage (I.cocomplex.d 0 1))
      (imageCompFactorThruImage_eq_zero
        (ShortComplex.mk
          (I.ι.f 0)
          (I.cocomplex.d 0 1)
          (by simpa using I.ι.comm 0 1)))).ShortExact := by
  let I : InjectiveResolution F := injectiveResolution F
  let S : ShortComplex (X.Sheaf AddCommGrpCat.{u}) :=
    ShortComplex.mk
      (I.ι.f 0)
      (I.cocomplex.d 0 1)
      (by simpa using I.ι.comm 0 1)
  have hExact : S.Exact := by
    simpa [S] using I.exact₀
  simpa [S] using
    (ShortComplex.ShortExact.mk'
      (exactImageFactorRowOfExact S hExact) inferInstance inferInstance :
      (ShortComplex.mk
        (Abelian.image.ι S.f)
        (Abelian.factorThruImage S.g)
        (imageCompFactorThruImage_eq_zero S)).ShortExact)

omit [HasExt.{u} (X.Sheaf AddCommGrpCat.{u})] in
/-- Helper for Lemma 20.12.3: the image row at degree `n + 1`,
`im(dₙ) ⟶ Iⁿ⁺¹ ⟶ im(dₙ₊₁)`, is short exact. -/
private theorem injectiveResolution_image_shortExact_succ
    (F : X.Sheaf AddCommGrpCat.{u}) (n : ℕ) :
    let I : InjectiveResolution F := injectiveResolution F
    (ShortComplex.mk
      (Abelian.image.ι (I.cocomplex.d n (n + 1)))
      (Abelian.factorThruImage (I.cocomplex.d (n + 1) (n + 2)))
      (imageCompFactorThruImage_eq_zero
        (ShortComplex.mk
          (I.cocomplex.d n (n + 1))
          (I.cocomplex.d (n + 1) (n + 2))
          (by simpa using I.cocomplex.d_comp_d n)))).ShortExact := by
  let I : InjectiveResolution F := injectiveResolution F
  let S : ShortComplex (X.Sheaf AddCommGrpCat.{u}) :=
    ShortComplex.mk
      (I.cocomplex.d n (n + 1))
      (I.cocomplex.d (n + 1) (n + 2))
      (by simpa using I.cocomplex.d_comp_d n)
  have hExact : S.Exact := by
    simpa [S] using I.exact_succ n
  simpa [S] using
    (ShortComplex.ShortExact.mk'
      (exactImageFactorRowOfExact S hExact) inferInstance inferInstance :
      (ShortComplex.mk
        (Abelian.image.ι S.f)
        (Abelian.factorThruImage S.g)
        (imageCompFactorThruImage_eq_zero S)).ShortExact)

open CategoryTheory.Sheaf.Hom in
omit [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [HasExt.{u} (X.Sheaf AddCommGrpCat.{u})] in
/-- Helper for Lemma 20.12.3: sections over `U` preserve monomorphisms of abelian sheaves. -/
private theorem sectionsAtOpen_map_mono
    (U : Opens X) {A B : X.Sheaf AddCommGrpCat.{u}} (f : A ⟶ B) [Mono f] :
    Mono ((sectionsAtOpenFunctor U).map f) := by
  have hf : Mono f := inferInstance
  have hmono_nat : Mono f.hom := (mono_iff_presheaf_mono JX AddCommGrpCat.{u} f).mp hf
  simpa [sectionsAtOpenFunctor, sheafSections] using
    ((NatTrans.mono_iff_mono_app _).mp hmono_nat) (op U)

omit [HasExt.{u} (X.Sheaf AddCommGrpCat.{u})] in
/-- Helper for Lemma 20.12.3: each differential image in an injective resolution of a flasque
sheaf is flasque. -/
private theorem injectiveResolution_image_isFlasque
    (F : X.Sheaf AddCommGrpCat.{u}) (hF : TopCat.Sheaf.IsFlasque F) :
    ∀ n : ℕ,
      TopCat.Sheaf.IsFlasque
        (Abelian.image ((injectiveResolution F).cocomplex.d n (n + 1))) := by
  let I : InjectiveResolution F := injectiveResolution F
  intro n
  induction n with
  | zero =>
      have hShortExact := injectiveResolution_image_shortExact_zero F
      have hLeft : TopCat.Sheaf.IsFlasque (Abelian.image (I.ι.f 0)) := by
        let e : Abelian.image (I.ι.f 0) ≅ F :=
          (Abelian.imageIsoImage (I.ι.f 0)) ≪≫ imageMonoIsoSource (I.ι.f 0)
        exact isFlasque_of_iso e.symm hF
      have hMid : TopCat.Sheaf.IsFlasque (I.cocomplex.X 0) :=
        isFlasque_of_injective (I.injective 0)
      simpa [I] using quotient_isFlasque_of_shortExact hShortExact hLeft hMid
  | succ n ihn =>
      have hShortExact := injectiveResolution_image_shortExact_succ F n
      have hMid : TopCat.Sheaf.IsFlasque (I.cocomplex.X (n + 1)) :=
        isFlasque_of_injective (I.injective (n + 1))
      simpa [I] using quotient_isFlasque_of_shortExact hShortExact ihn hMid

omit [HasExt.{u} (X.Sheaf AddCommGrpCat.{u})] in
/-- Helper for Lemma 20.12.3: after taking sections over `U`, every factor-through-image map in an
injective resolution of a flasque sheaf is epi. -/
private theorem sections_factorThruImage_epi_of_injectiveResolution
    (F : X.Sheaf AddCommGrpCat.{u}) (hF : TopCat.Sheaf.IsFlasque F) (U : Opens X) :
    ∀ n : ℕ,
      Epi ((sectionsAtOpenFunctor U).map
        (Abelian.factorThruImage ((injectiveResolution F).cocomplex.d n (n + 1)))) := by
  let I : InjectiveResolution F := injectiveResolution F
  intro n
  induction n with
  | zero =>
      let T : ShortComplex (X.Sheaf AddCommGrpCat.{u}) :=
        ShortComplex.mk
          (Abelian.image.ι (I.ι.f 0))
          (Abelian.factorThruImage (I.cocomplex.d 0 1))
          (imageCompFactorThruImage_eq_zero
            (ShortComplex.mk
              (I.ι.f 0)
              (I.cocomplex.d 0 1)
              (by simpa using I.ι.comm 0 1)))
      have hShortExact : T.ShortExact := by
        simpa [I, T] using injectiveResolution_image_shortExact_zero F
      have hLeft : TopCat.Sheaf.IsFlasque (Abelian.image (I.ι.f 0)) := by
        let e : Abelian.image (I.ι.f 0) ≅ F :=
          (Abelian.imageIsoImage (I.ι.f 0)) ≪≫ imageMonoIsoSource (I.ι.f 0)
        exact isFlasque_of_iso e.symm hF
      have hMid : TopCat.Sheaf.IsFlasque (I.cocomplex.X 0) :=
        isFlasque_of_injective (I.injective 0)
      have hMapped : (T.map (sectionsAtOpenFunctor U)).ShortExact := by
        exact sections_map_shortExact_of_isFlasque hShortExact hLeft hMid
      simpa [I, T] using hMapped.epi_g
  | succ n ihn =>
      let T : ShortComplex (X.Sheaf AddCommGrpCat.{u}) :=
        ShortComplex.mk
          (Abelian.image.ι (I.cocomplex.d n (n + 1)))
          (Abelian.factorThruImage (I.cocomplex.d (n + 1) (n + 2)))
          (imageCompFactorThruImage_eq_zero
            (ShortComplex.mk
              (I.cocomplex.d n (n + 1))
              (I.cocomplex.d (n + 1) (n + 2))
              (by simpa using I.cocomplex.d_comp_d n)))
      have hShortExact : T.ShortExact := by
        simpa [I, T] using injectiveResolution_image_shortExact_succ F n
      have hLeft :
          TopCat.Sheaf.IsFlasque (Abelian.image (I.cocomplex.d n (n + 1))) := by
        simpa [I] using injectiveResolution_image_isFlasque F hF n
      have hMid : TopCat.Sheaf.IsFlasque (I.cocomplex.X (n + 1)) :=
        isFlasque_of_injective (I.injective (n + 1))
      have hMapped : (T.map (sectionsAtOpenFunctor U)).ShortExact := by
        exact sections_map_shortExact_of_isFlasque hShortExact hLeft hMid
      simpa [I, T] using hMapped.epi_g

/-- Helper for Lemma 20.12.3: applying sections over a fixed open subset to the chosen injective
resolution of `F` gives the complex that computes both right-derived sections and sheaf
cohomology over `U`. -/
private abbrev sections_injectiveResolution_complex
    (F : X.Sheaf AddCommGrpCat.{u}) (U : Opens X) :
    HomologicalComplex AddCommGrpCat.{u} (ComplexShape.up ℕ) :=
  (((sectionsAtOpenFunctor U).mapHomologicalComplex (ComplexShape.up ℕ)).obj
    (injectiveResolution F).cocomplex)

omit [HasExt.{u} (X.Sheaf AddCommGrpCat.{u})] in
/-- Helper for Lemma 20.12.3: the public cohomology object `F.H' i U` is computed by the
homology of the sections complex of an injective resolution of `F`. -/
private theorem cohomologyAtObject_isomorphic_to_sections_injectiveResolution_homology
    (F : X.Sheaf AddCommGrpCat.{u}) (U : Opens X) (i : ℕ) :
    IsIsomorphic
      (F.H' i U)
      ((sections_injectiveResolution_complex F U).homology i) := by
  simpa [sections_injectiveResolution_complex] using
    cohomologyAtObject_isomorphic_to_homology_sections_of_injectiveResolution
      JX (injectiveResolution F) i

omit [HasExt.{u} (X.Sheaf AddCommGrpCat.{u})] in
/-- Helper for Lemma 20.12.3: the chosen injective resolution is exact at every successor degree
before taking sections. -/
private theorem injectiveResolution_shortComplex_exact_succ
    (F : X.Sheaf AddCommGrpCat.{u}) (n : ℕ) :
    (ShortComplex.mk
      ((injectiveResolution F).cocomplex.d n (n + 1))
      ((injectiveResolution F).cocomplex.d (n + 1) (n + 2))
      (by simpa using (injectiveResolution F).cocomplex.d_comp_d n)).Exact := by
  let I : InjectiveResolution F := injectiveResolution F
  -- The injective-resolution owner already records exactness at every positive degree.
  simpa [I] using I.exact_succ n

omit [HasExt.{u} (X.Sheaf AddCommGrpCat.{u})] in
/-- Helper for Lemma 20.12.3: exactness of the mapped successor short complex is exactly the
`ExactAt` statement needed for the sections complex. -/
private theorem sections_exactAt_of_mapped_injectiveResolution_shortComplex
    (F : X.Sheaf AddCommGrpCat.{u}) (U : Opens X) (n : ℕ)
    (hExact :
      ((ShortComplex.mk
        ((injectiveResolution F).cocomplex.d n (n + 1))
        ((injectiveResolution F).cocomplex.d (n + 1) (n + 2))
        (by simpa using (injectiveResolution F).cocomplex.d_comp_d n)).map
          (sectionsAtOpenFunctor U)).Exact) :
    (sections_injectiveResolution_complex F U).ExactAt (n + 1) := by
  -- Unfold `ExactAt` for `Γ(U, injectiveResolution F)` and identify the resulting short complex
  -- with the image of the successor short complex under `sectionsAtOpenFunctor U`.
  simpa [sections_injectiveResolution_complex, HomologicalComplex.exactAt_iff,
    HomologicalComplex.sc, HomologicalComplex.shortComplexFunctor] using hExact

omit [HasExt.{u} (X.Sheaf AddCommGrpCat.{u})] in
/-- Helper for Lemma 20.12.3: once the sections complex of an injective resolution is exact in
positive degrees, the positive cohomology over `U` vanishes. -/
private theorem higherCohomology_isZero_of_isFlasque_from_resolution_exactness
    (F : X.Sheaf AddCommGrpCat.{u}) (U : Opens X) (n : ℕ)
    (hExact : ∀ m : ℕ, (sections_injectiveResolution_complex F U).ExactAt (m + 1)) :
    IsZero (F.H' (n + 1) U) := by
  have hHomology :
      IsZero ((sections_injectiveResolution_complex F U).homology (n + 1)) := by
    rw [← HomologicalComplex.exactAt_iff_isZero_homology]
    exact hExact n
  rcases cohomologyAtObject_isomorphic_to_sections_injectiveResolution_homology F U (n + 1) with
    ⟨e⟩
  refine e.isZero_iff.2 ?_
  simpa using hHomology

-- Proof sketch: follow the source route on the injective resolution of `F`. The short exact
-- image rows `im(dₙ) ⟶ Iⁿ⁺¹ ⟶ im(dₙ₊₁)` propagate flasqueness along the resolution and keep the
-- mapped image rows short exact after taking sections, which is enough to recover exactness of
-- `Γ(U, I^•)` in every positive degree.
omit [HasExt.{u} (X.Sheaf AddCommGrpCat.{u})] in
private theorem sections_injectiveResolution_exactAt_succ_of_isFlasque
    (F : X.Sheaf AddCommGrpCat.{u}) (hF : TopCat.Sheaf.IsFlasque F) (U : Opens X) :
    ∀ n : ℕ, (sections_injectiveResolution_complex F U).ExactAt (n + 1) := by
  let I : InjectiveResolution F := injectiveResolution F
  intro n
  let S : ShortComplex (X.Sheaf AddCommGrpCat.{u}) :=
    ShortComplex.mk
      (I.cocomplex.d n (n + 1))
      (I.cocomplex.d (n + 1) (n + 2))
      (by simpa using I.cocomplex.d_comp_d n)
  let T : ShortComplex (X.Sheaf AddCommGrpCat.{u}) :=
    ShortComplex.mk
      (Abelian.image.ι (I.cocomplex.d n (n + 1)))
      (Abelian.factorThruImage (I.cocomplex.d (n + 1) (n + 2)))
      (imageCompFactorThruImage_eq_zero S)
  have hTShortExact : T.ShortExact := by
    simpa [I, S, T] using injectiveResolution_image_shortExact_succ F n
  have hLeft :
      TopCat.Sheaf.IsFlasque (Abelian.image (I.cocomplex.d n (n + 1))) := by
    simpa [I] using injectiveResolution_image_isFlasque F hF n
  have hMid : TopCat.Sheaf.IsFlasque (I.cocomplex.X (n + 1)) :=
    isFlasque_of_injective (I.injective (n + 1))
  have hMappedT : (T.map (sectionsAtOpenFunctor U)).Exact := by
    exact (sections_map_shortExact_of_isFlasque hTShortExact hLeft hMid).exact
  have hEpi :
      Epi ((sectionsAtOpenFunctor U).map
        (Abelian.factorThruImage (I.cocomplex.d n (n + 1)))) := by
    simpa [I] using sections_factorThruImage_epi_of_injectiveResolution F hF U n
  have hMono :
      Mono ((sectionsAtOpenFunctor U).map
        (Abelian.image.ι (I.cocomplex.d (n + 1) (n + 2)))) := by
    simpa [I] using
      sectionsAtOpen_map_mono U (Abelian.image.ι (I.cocomplex.d (n + 1) (n + 2)))
  have hExact : (S.map (sectionsAtOpenFunctor U)).Exact := by
    exact exactOfMappedImageFactorRow S (by simpa [T] using hMappedT)
  exact
    sections_exactAt_of_mapped_injectiveResolution_shortComplex F U n
      (by simpa [I, S] using hExact)

-- Proof sketch: compare `H^p(U, F)` with the degree-`p` homology of the sections
-- complex of an injective resolution via
-- `CategoryTheory.Sheaf.cohomologyAtObject_isomorphic_to_homology_sections_of_injectiveResolution`.
-- Flasque sheaves are acyclic for sections over every open subset, so the sections complex is
-- acyclic in positive degrees. Transport that vanishing back across the canonical comparison.
omit [HasExt.{u} (X.Sheaf AddCommGrpCat.{u})] in
/-- Lemma 20.12.3: if an abelian sheaf on a topological space is flasque, then its higher
cohomology over every open subset vanishes. -/
@[stacks 09SY]
theorem higherCohomology_isZero_of_isFlasque
    (F : X.Sheaf AddCommGrpCat.{u}) (hF : TopCat.Sheaf.IsFlasque F)
    (U : Opens X) (p : ℕ) (hp : 0 < p) :
    IsZero (F.H' p U) := by
  -- Route correction: abandon the over-strong Chapter `13` quotient interface and instead compare
  -- `H^p(U, F)` directly with the homology of the sections complex `Γ(U, I^•)`, then kill that
  -- homology by exactness of the mapped injective resolution in positive degrees.
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_lt hp
  -- The remaining source-faithful work is concentrated in the exactness package for
  -- `Γ(U, injectiveResolution(F))`.
  simpa [Nat.zero_add, Nat.add_assoc] using
    higherCohomology_isZero_of_isFlasque_from_resolution_exactness F U n
      (sections_injectiveResolution_exactAt_succ_of_isFlasque F hF U)

end CategoryTheory.Sheaf

namespace AlgebraicGeometry.RingedSpace

-- Proof sketch: apply the sheaf-level vanishing theorem to the underlying abelian sheaf of the
-- module via the canonical bridge `moduleUnderlyingSheaf X`.
/-- Ringed-space specialization of Lemma 20.12.3 for `𝒪_X`-modules. -/
theorem higherCohomology_isZero_of_module_isFlasque
    {X : RingedSpace.{u}}
    [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
    (ℱ : RingedSpace.Modules X)
    (hℱ : TopCat.Sheaf.IsFlasque ((moduleUnderlyingSheaf X).obj ℱ))
    (U : Opens X.carrier) (p : ℕ) (hp : 0 < p) :
    IsZero (((moduleUnderlyingSheaf X).obj ℱ).H' p U) := by
  simpa using
    CategoryTheory.Sheaf.higherCohomology_isZero_of_isFlasque ((moduleUnderlyingSheaf X).obj ℱ)
      hℱ U p hp

end AlgebraicGeometry.RingedSpace
