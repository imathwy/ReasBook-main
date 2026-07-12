import StacksProject_2024.Chap08.Definition_8_5_5
import StacksProject_2024.Chap08.Lemma_8_10_5.PullbackNaturality

universe uC uX vC vX

namespace CategoryTheory

open FibredCategoryMor
open Functor IsStronglyCartesian
open StackInGroupoidsOver.Hom

section

variable {C : Type uC} [Category.{vC} C]
variable {J : GrothendieckTopology C}
variable {Xₛ Yₛ : StackInGroupoidsOver J}

/-- Helper for Lemma 8.10.5: composing in `Yₛ.S` and then passing to the locally discrete
opposite is the same as composing the corresponding `toLoc` arrows in the owner order used by
`pullHom`. -/
private theorem inherited_comp_toLoc_eq
    {A B D : Yₛ.S} (f : B ⟶ D) (g : A ⟶ B) (gf : A ⟶ D) (hgf : g ≫ f = gf) :
    f.op.toLoc ≫ g.op.toLoc = gf.op.toLoc := by
  -- Translate the composite equality to `LocallyDiscrete Yₛ.Sᵒᵖ`.
  simpa [← Quiver.Hom.comp_toLoc, ← op_comp] using
    congrArg Quiver.Hom.toLoc (congrArg Quiver.Hom.op hgf)

/-- Helper for Lemma 8.10.5: the same `toLoc` composition translation on the base site `C`. -/
theorem base_comp_toLoc_eq
    {A B D : C} (f : B ⟶ D) (g : A ⟶ B) (gf : A ⟶ D) (hgf : g ≫ f = gf) :
    f.op.toLoc ≫ g.op.toLoc = gf.op.toLoc := by
  simpa [← Quiver.Hom.comp_toLoc, ← op_comp] using
    congrArg Quiver.Hom.toLoc (congrArg Quiver.Hom.op hgf)

/-- Helper for Lemma 8.10.5: name the corrected comparison-conjugated overlap map obtained by
forgetting one `G F` descent-datum overlap morphism to `Xₛ`. -/
noncomputable abbrev inherited_basis_descent_hom
    (F : Xₛ ⟶ Yₛ)
    [IsFibredInGroupoids (G F)]
    {ι : Type*} {y : Yₛ.S} {Y : ι → Yₛ.S} {g : ∀ i, Y i ⟶ y}
    (D : ((canonicalFiberPseudofunctor (G F)).DescentData g))
    {Z : Yₛ.S} (q : Z ⟶ y) {i₁ i₂ : ι} (f₁ : Z ⟶ Y i₁) (f₂ : Z ⟶ Y i₂)
    (hf₁ : f₁ ≫ g i₁ = q := by cat_disch) (hf₂ : f₂ ≫ g i₂ = q := by cat_disch) :
    (((canonicalFiberPseudofunctor Xₛ.p).map (Yₛ.p.map f₁).op.toLoc).toFunctor.obj
        (inherited_source_fiber_obj (F := F) (D.obj i₁))) ⟶
      (((canonicalFiberPseudofunctor Xₛ.p).map (Yₛ.p.map f₂).op.toLoc).toFunctor.obj
        (inherited_source_fiber_obj (F := F) (D.obj i₂))) :=
  let e₁ :=
    inherited_source_pullback_comparison
      (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) f₁ (D.obj i₁)
  let e₂ :=
    inherited_source_pullback_comparison
      (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) f₂ (D.obj i₂)
  -- Route correction: the comparison iso goes from the forgotten `G F` pullback to the
  -- canonical `Xₛ` pullback, so the descent morphism must be conjugated by `inv ... hom`.
  e₁.inv ≫ (inherited_source_fiber_forget (F := F) _).map (D.hom q f₁ f₂ hf₁ hf₂) ≫ e₂.hom

/-- Helper for Lemma 8.10.5: after forgetting to `Xₛ`, the self-overlap morphism normalizes to
the identity once the corrected comparison shell is fixed. -/
theorem inherited_basis_descent_hom_self_normalize
    (F : Xₛ ⟶ Yₛ)
    [IsFibredInGroupoids (G F)]
    {ι : Type*} {y : Yₛ.S} {Y : ι → Yₛ.S} {g : ∀ i, Y i ⟶ y}
    (D : ((canonicalFiberPseudofunctor (G F)).DescentData g))
    {Z : Yₛ.S} (q : Z ⟶ y) {i : ι} (f : Z ⟶ Y i)
    (hf : f ≫ g i = q := by cat_disch) :
    inherited_basis_descent_hom (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F D q f f hf hf = 𝟙 _ := by
  let e :=
    inherited_source_pullback_comparison
      (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) f (D.obj i)
  have hself :
      (inherited_source_fiber_forget (F := F) Z).map (D.hom q f f hf hf) =
        𝟙 (inherited_source_fiber_obj (F := F)
          ((((canonicalFiberPseudofunctor (G F)).map f.op.toLoc).toFunctor.obj (D.obj i)))) := by
    -- Rewrite the forgotten middle term to the mapped identity before canceling the comparison.
    calc
      (inherited_source_fiber_forget (F := F) Z).map (D.hom q f f hf hf)
          =
            (inherited_source_fiber_forget (F := F) Z).map
              (𝟙
                ((((canonicalFiberPseudofunctor (G F)).map f.op.toLoc).toFunctor.obj
                  (D.obj i)))) := by
                simpa using
                  congrArg (fun k ↦ (inherited_source_fiber_forget (F := F) Z).map k)
                    (D.hom_self q f hf)
      _ =
          𝟙 (inherited_source_fiber_obj (F := F)
            ((((canonicalFiberPseudofunctor (G F)).map f.op.toLoc).toFunctor.obj
              (D.obj i)))) := by
            exact (inherited_source_fiber_forget (F := F) Z).map_id _
  -- Reduce to the literal `comparison.inv ≫ 𝟙 ≫ comparison.hom` cancellation shape.
  change e.inv ≫ (inherited_source_fiber_forget (F := F) Z).map (D.hom q f f hf hf) ≫ e.hom = 𝟙 _
  rw [hself]
  calc
    e.inv ≫ 𝟙 _ ≫ e.hom = e.inv ≫ e.hom := by simp
    _ = 𝟙 _ := e.inv_hom_id

/-- Helper for Lemma 8.10.5: after forgetting the source descent datum to the overlap fiber of
`Xₛ`, the source cocycle identity still holds before any pullback-comparison conjugation. -/
private theorem inherited_basis_descent_hom_mapped_source_cocycle
    (F : Xₛ ⟶ Yₛ)
    [IsFibredInGroupoids (G F)]
    {ι : Type*} {y : Yₛ.S} {Y : ι → Yₛ.S} {g : ∀ i, Y i ⟶ y}
    (D : ((canonicalFiberPseudofunctor (G F)).DescentData g))
    {Z : Yₛ.S} (q : Z ⟶ y) {i₁ i₂ i₃ : ι}
    (f₁ : Z ⟶ Y i₁) (f₂ : Z ⟶ Y i₂) (f₃ : Z ⟶ Y i₃)
    (hf₁ : f₁ ≫ g i₁ = q := by cat_disch) (hf₂ : f₂ ≫ g i₂ = q := by cat_disch)
    (hf₃ : f₃ ≫ g i₃ = q := by cat_disch) :
    (inherited_source_fiber_forget (F := F) Z).map (D.hom q f₁ f₂ hf₁ hf₂) ≫
        (inherited_source_fiber_forget (F := F) Z).map (D.hom q f₂ f₃ hf₂ hf₃) =
      (inherited_source_fiber_forget (F := F) Z).map (D.hom q f₁ f₃ hf₁ hf₃) := by
  -- Map the source cocycle relation through the fixed forgetting functor on the overlap fiber.
  calc
    (inherited_source_fiber_forget (F := F) Z).map (D.hom q f₁ f₂ hf₁ hf₂) ≫
        (inherited_source_fiber_forget (F := F) Z).map (D.hom q f₂ f₃ hf₂ hf₃) =
      (inherited_source_fiber_forget (F := F) Z).map
        (D.hom q f₁ f₂ hf₁ hf₂ ≫ D.hom q f₂ f₃ hf₂ hf₃) := by
          rw [(inherited_source_fiber_forget (F := F) Z).map_comp]
    _ =
      (inherited_source_fiber_forget (F := F) Z).map (D.hom q f₁ f₃ hf₁ hf₃) := by
        exact congrArg
          (fun k ↦ (inherited_source_fiber_forget (F := F) Z).map k)
          (D.hom_comp q f₁ f₂ f₃ hf₁ hf₂ hf₃)

theorem inherited_basis_descent_hom_comp_normalize
    (F : Xₛ ⟶ Yₛ)
    [IsFibredInGroupoids (G F)]
    {ι : Type*} {y : Yₛ.S} {Y : ι → Yₛ.S} {g : ∀ i, Y i ⟶ y}
    (D : ((canonicalFiberPseudofunctor (G F)).DescentData g))
    {Z : Yₛ.S} (q : Z ⟶ y) {i₁ i₂ i₃ : ι}
    (f₁ : Z ⟶ Y i₁) (f₂ : Z ⟶ Y i₂) (f₃ : Z ⟶ Y i₃)
    (hf₁ : f₁ ≫ g i₁ = q := by cat_disch) (hf₂ : f₂ ≫ g i₂ = q := by cat_disch)
    (hf₃ : f₃ ≫ g i₃ = q := by cat_disch) :
    inherited_basis_descent_hom
        (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F D q f₁ f₂ hf₁ hf₂ ≫
      inherited_basis_descent_hom
        (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F D q f₂ f₃ hf₂ hf₃ =
    inherited_basis_descent_hom
        (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F D q f₁ f₃ hf₁ hf₃ := by
  let e₁ :=
    inherited_source_pullback_comparison
      (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) f₁ (D.obj i₁)
  let e₂ :=
    inherited_source_pullback_comparison
      (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) f₂ (D.obj i₂)
  let e₃ :=
    inherited_source_pullback_comparison
      (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) f₃ (D.obj i₃)
  let m₁₂ := (inherited_source_fiber_forget (F := F) Z).map (D.hom q f₁ f₂ hf₁ hf₂)
  let m₂₃ := (inherited_source_fiber_forget (F := F) Z).map (D.hom q f₂ f₃ hf₂ hf₃)
  let m₁₃ := (inherited_source_fiber_forget (F := F) Z).map (D.hom q f₁ f₃ hf₁ hf₃)
  have hmid : m₁₂ ≫ m₂₃ = m₁₃ :=
    inherited_basis_descent_hom_mapped_source_cocycle
      (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F D q f₁ f₂ f₃ hf₁ hf₂ hf₃
  have h1 :
      inherited_basis_descent_hom
          (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F D q f₁ f₂ hf₁ hf₂ ≫
        inherited_basis_descent_hom
          (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F D q f₂ f₃ hf₂ hf₃ =
      e₁.inv ≫ m₁₂ ≫ e₂.hom ≫ e₂.inv ≫ m₂₃ ≫ e₃.hom := by
    simp only [inherited_basis_descent_hom, e₁, e₂, e₃, m₁₂, m₂₃, Category.assoc]
    rfl
  have h2 : e₂.hom ≫ e₂.inv ≫ m₂₃ ≫ e₃.hom = m₂₃ ≫ e₃.hom :=
    Iso.hom_inv_id_assoc e₂ (m₂₃ ≫ e₃.hom)
  have h3 := congrArg (fun k ↦ e₁.inv ≫ m₁₂ ≫ k) h2
  have h4 := congrArg (fun k ↦ e₁.inv ≫ k)
    ((Category.assoc m₁₂ m₂₃ e₃.hom).symm.trans
      (congrArg (fun k ↦ k ≫ e₃.hom) hmid))
  have h5 :
      e₁.inv ≫ m₁₃ ≫ e₃.hom =
        inherited_basis_descent_hom
          (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F D q f₁ f₃ hf₁ hf₃ := by
    simp only [inherited_basis_descent_hom, e₁, e₃, m₁₃, Category.assoc]
    rfl
  exact h1.trans (h3.trans (h4.trans h5))

/-- Helper for Lemma 8.10.5: after postcomposing the raw left comparison shell and the
normalized left comparison shell with the `k`- and `f`-pullback arrows, both sides reduce to the
same composite-leg pullback arrow in the source stack. -/
theorem inherited_source_pullback_comparison_comp_inv_left_boundary_postcompose_k_then_f
    (F : Xₛ ⟶ Yₛ)
    [IsFibredInGroupoids (G F)]
    {U V V' : Yₛ.S} (f : V ⟶ U) (k : V' ⟶ V) (kf : V' ⟶ U)
    (hkf : k ≫ f = kf := by cat_disch) (x : (G F).Fiber U) :
    let TX := ((canonicalFiberPseudofunctor Xₛ.p).map (Yₛ.p.map k).op.toLoc).toFunctor
    let raw :=
      (((canonicalFiberPseudofunctor Xₛ.p).mapComp'
          (Yₛ.p.map f).op.toLoc (Yₛ.p.map k).op.toLoc (Yₛ.p.map kf).op.toLoc
          (base_comp_toLoc_eq (f := Yₛ.p.map f) (g := Yₛ.p.map k)
            (gf := Yₛ.p.map kf) (by rw [← Functor.map_comp, hkf]))).hom.toNatTrans.app
        (inherited_source_fiber_obj (F := F) x)) ≫
        TX.map
          (inherited_source_pullback_comparison
            (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) f x).inv
    let strict :=
      (inherited_source_pullback_comparison
          (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) kf x).inv ≫
        (inherited_source_fiber_forget (F := F) V').map
          (((canonicalFiberPseudofunctor (G F)).mapComp'
              f.op.toLoc k.op.toLoc kf.op.toLoc
              (inherited_comp_toLoc_eq (Yₛ := Yₛ) f k kf hkf)).hom.toNatTrans.app x) ≫
        (inherited_source_pullback_comparison
          (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) k
          (((canonicalFiberPseudofunctor (G F)).map f.op.toLoc).toFunctor.obj x)).hom
    let tail :=
      (canonicalPullbackChoice Xₛ.p).map (Yₛ.p.map k)
        (inherited_source_fiber_obj (F := F)
          (((canonicalFiberPseudofunctor (G F)).map f.op.toLoc).toFunctor.obj x))
    (raw.1 ≫ tail) ≫ (canonicalPullbackChoice (G F)).map f x =
      (strict.1 ≫ tail) ≫ (canonicalPullbackChoice (G F)).map f x := by
  let TX := ((canonicalFiberPseudofunctor Xₛ.p).map (Yₛ.p.map k).op.toLoc).toFunctor
  let raw :=
    (((canonicalFiberPseudofunctor Xₛ.p).mapComp'
        (Yₛ.p.map f).op.toLoc (Yₛ.p.map k).op.toLoc (Yₛ.p.map kf).op.toLoc
        (base_comp_toLoc_eq (f := Yₛ.p.map f) (g := Yₛ.p.map k)
          (gf := Yₛ.p.map kf) (by rw [← Functor.map_comp, hkf]))).hom.toNatTrans.app
      (inherited_source_fiber_obj (F := F) x)) ≫
      TX.map
        (inherited_source_pullback_comparison
          (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) f x).inv
  let strict :=
    (inherited_source_pullback_comparison
        (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) kf x).inv ≫
      (inherited_source_fiber_forget (F := F) V').map
        (((canonicalFiberPseudofunctor (G F)).mapComp'
            f.op.toLoc k.op.toLoc kf.op.toLoc
            (inherited_comp_toLoc_eq (Yₛ := Yₛ) f k kf hkf)).hom.toNatTrans.app x) ≫
      (inherited_source_pullback_comparison
        (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) k
        (((canonicalFiberPseudofunctor (G F)).map f.op.toLoc).toFunctor.obj x)).hom
  let tail :=
    (canonicalPullbackChoice Xₛ.p).map (Yₛ.p.map k)
      (inherited_source_fiber_obj (F := F)
        (((canonicalFiberPseudofunctor (G F)).map f.op.toLoc).toFunctor.obj x))
  let leftX :=
    (((canonicalFiberPseudofunctor Xₛ.p).mapComp'
        (Yₛ.p.map f).op.toLoc (Yₛ.p.map k).op.toLoc (Yₛ.p.map kf).op.toLoc
        (base_comp_toLoc_eq (f := Yₛ.p.map f) (g := Yₛ.p.map k)
          (gf := Yₛ.p.map kf) (by rw [← Functor.map_comp, hkf]))).hom.toNatTrans.app
      (inherited_source_fiber_obj (F := F) x))
  let leftGF :=
    (((canonicalFiberPseudofunctor (G F)).mapComp'
        f.op.toLoc k.op.toLoc kf.op.toLoc
        (inherited_comp_toLoc_eq (Yₛ := Yₛ) f k kf hkf)).hom.toNatTrans.app x)
  let ef :=
    inherited_source_pullback_comparison
      (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) f x
  let ekf :=
    inherited_source_pullback_comparison
      (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) kf x
  let ck :=
    inherited_source_pullback_comparison
      (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) k
      (((canonicalFiberPseudofunctor (G F)).map f.op.toLoc).toFunctor.obj x)
  let tailSource :=
    (canonicalPullbackChoice Xₛ.p).map (Yₛ.p.map k)
      (((canonicalFiberPseudofunctor Xₛ.p).map (Yₛ.p.map f).op.toLoc).toFunctor.obj
        (inherited_source_fiber_obj (F := F) x))
  let tailF :=
    (canonicalPullbackChoice (G F)).map f x
  let tailXf :=
    (canonicalPullbackChoice Xₛ.p).map (Yₛ.p.map f) (inherited_source_fiber_obj (F := F) x)
  let tailXkf :=
    (canonicalPullbackChoice Xₛ.p).map (Yₛ.p.map kf) (inherited_source_fiber_obj (F := F) x)
  let tailGFk :=
    (canonicalPullbackChoice (G F)).map k
      (((canonicalFiberPseudofunctor (G F)).map f.op.toLoc).toFunctor.obj x)
  let tailGFkf :=
    (canonicalPullbackChoice (G F)).map kf x
  have hmapInv :
      (TX.map ef.inv).1 ≫ tail = tailSource ≫ ef.inv.1 := by
    -- Move the inverse comparison through the canonical pullback functor over `k`.
    simpa only [TX, ef, tail, tailSource] using
      canonical_pullbackFunctor_map_fac_owner
        (p := Xₛ.p) (f := Yₛ.p.map k) (φ := ef.inv)
  have hef :
      ef.inv.1 ≫ tailF = tailXf := by
    -- The inverse comparison for the `f`-pullback postcomposes to the source pullback arrow.
    simpa only [ef, tailF, tailXf] using
      inherited_source_pullback_comparison_inv_postcompose_owner
        (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) f x
  have hleftFac :
      leftX.1 ≫ tailSource ≫ tailXf = tailXkf := by
    -- The `Xₛ` map-composition hom component factors through the composite pullback arrow.
    simpa only [leftX, tailSource, tailXf, tailXkf] using
      FibredCategoryMor.canonicalFiberPseudofunctor_mapComp'_hom_app_fac
        (p := Xₛ.p) (f := Yₛ.p.map f) (g := Yₛ.p.map k)
        (gf := Yₛ.p.map kf)
        (hgf := by rw [← Functor.map_comp, hkf])
        (inherited_source_fiber_obj (F := F) x)
  have hck :
      ck.hom.1 ≫ tail = tailGFk := by
    -- The comparison for the `k`-pullback postcomposes to the chosen `(G F)` pullback arrow.
    simpa only [ck, tail, tailGFk] using
      inherited_source_pullback_comparison_hom_postcompose
        (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) k
        (((canonicalFiberPseudofunctor (G F)).map f.op.toLoc).toFunctor.obj x)
  have hleftGFFac :
      leftGF.1 ≫ tailGFk ≫ tailF = tailGFkf := by
    -- The `(G F)` map-composition hom component factors through the composite pullback arrow.
    simpa only [leftGF, tailGFk, tailF, tailGFkf] using
      FibredCategoryMor.canonicalFiberPseudofunctor_mapComp'_hom_app_fac
        (p := G F) (f := f) (g := k) (gf := kf) (hgf := hkf) x
  have hekf :
      ekf.inv.1 ≫ tailGFkf = tailXkf := by
    -- The inverse comparison for the composite leg postcomposes to the source composite pullback.
    simpa only [ekf, tailGFkf, tailXkf] using
      inherited_source_pullback_comparison_inv_postcompose_owner
        (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) kf x
  have hraw :
      (raw.1 ≫ tail) ≫ tailF = tailXkf := by
    have hraw_pre :
        (raw.1 ≫ tail) ≫ tailF = leftX.1 ≫ tailSource ≫ tailXf := by
      calc
        (raw.1 ≫ tail) ≫ tailF =
          ((leftX.1 ≫ (TX.map ef.inv).1) ≫ tail) ≫ tailF := by
            rfl
        _ = (leftX.1 ≫ ((TX.map ef.inv).1 ≫ tail)) ≫ tailF := by
            simp only [Category.assoc]
        _ = (leftX.1 ≫ (tailSource ≫ ef.inv.1)) ≫ tailF := by
            exact congrArg (fun a ↦ (leftX.1 ≫ a) ≫ tailF) hmapInv
        _ = leftX.1 ≫ tailSource ≫ (ef.inv.1 ≫ tailF) := by
            simp only [Category.assoc]
        _ = leftX.1 ≫ tailSource ≫ tailXf := by
            exact congrArg (fun a ↦ leftX.1 ≫ tailSource ≫ a) hef
    exact hraw_pre.trans (by simpa only [Category.assoc] using hleftFac)
  have hstrict :
      (strict.1 ≫ tail) ≫ tailF = tailXkf := by
    calc
      (strict.1 ≫ tail) ≫ tailF =
          ((ekf.inv.1 ≫ ((inherited_source_fiber_forget (F := F) V').map leftGF).1 ≫
              ck.hom.1) ≫ tail) ≫ tailF := by
            rfl
      _ =
          ekf.inv.1 ≫ ((inherited_source_fiber_forget (F := F) V').map leftGF).1 ≫
            (ck.hom.1 ≫ tail) ≫ tailF := by
            simp only [Category.assoc]
      _ =
          ekf.inv.1 ≫ ((inherited_source_fiber_forget (F := F) V').map leftGF).1 ≫
            tailGFk ≫ tailF := by
            exact congrArg
              (fun a ↦ ekf.inv.1 ≫
                ((inherited_source_fiber_forget (F := F) V').map leftGF).1 ≫ a ≫ tailF)
              hck
      _ = ekf.inv.1 ≫ leftGF.1 ≫ tailGFk ≫ tailF := by
            rfl
      _ = ekf.inv.1 ≫ (leftGF.1 ≫ tailGFk ≫ tailF) := by
            simp only [Category.assoc]
      _ = ekf.inv.1 ≫ tailGFkf := by
            exact congrArg (fun a ↦ ekf.inv.1 ≫ a) hleftGFFac
      _ = tailXkf := hekf
  -- Both postcomposed shells have been reduced to the same composite-leg pullback arrow.
  exact hraw.trans hstrict.symm

/-- Helper for Lemma 8.10.5: the left composition boundary for the inherited source pullback
comparison rewrites the iterated `Xₛ` pullback shell to the corresponding forgotten `(G F)`
shell, before the middle refinement morphism is moved across `k`. -/
theorem inherited_source_pullback_comparison_comp_inv_left_boundary
    (F : Xₛ ⟶ Yₛ)
    [IsFibredInGroupoids (G F)]
    {U V V' : Yₛ.S} (f : V ⟶ U) (k : V' ⟶ V) (kf : V' ⟶ U)
    (hkf : k ≫ f = kf := by cat_disch) (x : (G F).Fiber U) :
    let TX := ((canonicalFiberPseudofunctor Xₛ.p).map (Yₛ.p.map k).op.toLoc).toFunctor
    let leftX :=
      (((canonicalFiberPseudofunctor Xₛ.p).mapComp'
          (Yₛ.p.map f).op.toLoc (Yₛ.p.map k).op.toLoc (Yₛ.p.map kf).op.toLoc
          (base_comp_toLoc_eq (f := Yₛ.p.map f) (g := Yₛ.p.map k)
            (gf := Yₛ.p.map kf) (by rw [← Functor.map_comp, hkf]))).hom.toNatTrans.app
        (inherited_source_fiber_obj (F := F) x))
    let leftGF :=
      (((canonicalFiberPseudofunctor (G F)).mapComp'
          f.op.toLoc k.op.toLoc kf.op.toLoc
          (inherited_comp_toLoc_eq (Yₛ := Yₛ) f k kf hkf)).hom.toNatTrans.app x)
    let ef := inherited_source_pullback_comparison
      (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) f x
    let ekf := inherited_source_pullback_comparison
      (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) kf x
    let ck := inherited_source_pullback_comparison
      (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) k
      (((canonicalFiberPseudofunctor (G F)).map f.op.toLoc).toFunctor.obj x)
    leftX ≫ TX.map ef.inv =
      ekf.inv ≫ (inherited_source_fiber_forget (F := F) V').map leftGF ≫ ck.hom := by
  let TX := ((canonicalFiberPseudofunctor Xₛ.p).map (Yₛ.p.map k).op.toLoc).toFunctor
  let leftX :=
    (((canonicalFiberPseudofunctor Xₛ.p).mapComp'
        (Yₛ.p.map f).op.toLoc (Yₛ.p.map k).op.toLoc (Yₛ.p.map kf).op.toLoc
        (base_comp_toLoc_eq (f := Yₛ.p.map f) (g := Yₛ.p.map k)
          (gf := Yₛ.p.map kf) (by rw [← Functor.map_comp, hkf]))).hom.toNatTrans.app
      (inherited_source_fiber_obj (F := F) x))
  let leftGF :=
    (((canonicalFiberPseudofunctor (G F)).mapComp'
        f.op.toLoc k.op.toLoc kf.op.toLoc
        (inherited_comp_toLoc_eq (Yₛ := Yₛ) f k kf hkf)).hom.toNatTrans.app x)
  let ef := inherited_source_pullback_comparison
    (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) f x
  let ekf := inherited_source_pullback_comparison
    (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) kf x
  let ck := inherited_source_pullback_comparison
    (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) k
    (((canonicalFiberPseudofunctor (G F)).map f.op.toLoc).toFunctor.obj x)
  let raw := leftX ≫ TX.map ef.inv
  let strict := ekf.inv ≫ (inherited_source_fiber_forget (F := F) V').map leftGF ≫ ck.hom
  let tail :=
    (canonicalPullbackChoice Xₛ.p).map (Yₛ.p.map k)
      (inherited_source_fiber_obj (F := F)
        (((canonicalFiberPseudofunctor (G F)).map f.op.toLoc).toFunctor.obj x))
  let tailF := (canonicalPullbackChoice (G F)).map f x
  have htail :
      Xₛ.p.IsStronglyCartesian (Yₛ.p.map k) tail := by
    -- The first cancellation uses the canonical source pullback over the refinement leg `k`.
    exact
      (canonicalPullbackChoice Xₛ.p).isStronglyCartesian (Yₛ.p.map k)
        (inherited_source_fiber_obj (F := F)
          (((canonicalFiberPseudofunctor (G F)).map f.op.toLoc).toFunctor.obj x))
  have htailF :
      Xₛ.p.IsStronglyCartesian (Yₛ.p.map f) tailF := by
    -- The second cancellation uses that the forgotten `(G F)` pullback arrow is strongly
    -- cartesian for the source projection.
    exact
      inherited_source_pullback_lift_isStronglyCartesian
        (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) f x
  have hraw_tail :
      Xₛ.p.IsHomLift (Yₛ.p.map k) (raw.1 ≫ tail) := by
    -- A vertical fiber morphism followed by the chosen `k`-pullback arrow is a lift over `k`.
    exact @IsHomLift.comp_lift_id_left' _ _ _ _ Xₛ.p _ _ _
      (Yₛ.p.obj V') raw.1 raw.2 _ _ (Yₛ.p.map k) tail htail.toIsHomLift
  have hstrict_tail :
      Xₛ.p.IsHomLift (Yₛ.p.map k) (strict.1 ≫ tail) := by
    -- The same lift calculation applies to the normalized shell.
    exact @IsHomLift.comp_lift_id_left' _ _ _ _ Xₛ.p _ _ _
      (Yₛ.p.obj V') strict.1 strict.2 _ _ (Yₛ.p.map k) tail htail.toIsHomLift
  have hpost₂ :
      (raw.1 ≫ tail) ≫ tailF = (strict.1 ≫ tail) ≫ tailF := by
    -- After one more postcomposition by the `f`-pullback arrow, both shells reduce to the same
    -- composite-leg pullback arrow.
    simpa only [raw, strict, tail, tailF, TX, leftX, leftGF, ef, ekf, ck] using
      inherited_source_pullback_comparison_comp_inv_left_boundary_postcompose_k_then_f
        (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F f k kf hkf x
  have hpost :
      raw.1 ≫ tail = strict.1 ≫ tail := by
    -- Cancel the common strongly cartesian `f`-pullback arrow.
    exact
      @Functor.IsStronglyCartesian.ext _ _ _ _ Xₛ.p _ _ _ _
        (Yₛ.p.map f) tailF htailF _ _ (Yₛ.p.map k)
        (raw.1 ≫ tail) (strict.1 ≫ tail) hraw_tail hstrict_tail hpost₂
  -- Cancel the common strongly cartesian `k`-pullback arrow to recover equality in the fiber.
  apply Functor.Fiber.hom_ext
  change raw.1 = strict.1
  exact
    @Functor.IsStronglyCartesian.ext _ _ _ _ Xₛ.p _ _ _ _
      (Yₛ.p.map k) tail htail _ _ (𝟙 (Yₛ.p.obj V'))
      raw.1 strict.1 raw.2 strict.2 hpost

/-- Helper for Lemma 8.10.5: after postcomposing the raw right comparison shell and the
normalized right comparison shell with the composite-leg pullback arrow, both sides reduce to the
same iterated `(G F)` pullback factorization. -/
theorem inherited_source_pullback_comparison_comp_hom_right_boundary_postcompose_kf
    (F : Xₛ ⟶ Yₛ)
    [IsFibredInGroupoids (G F)]
    {U V V' : Yₛ.S} (f : V ⟶ U) (k : V' ⟶ V) (kf : V' ⟶ U)
    (hkf : k ≫ f = kf := by cat_disch) (x : (G F).Fiber U) :
    let TX := ((canonicalFiberPseudofunctor Xₛ.p).map (Yₛ.p.map k).op.toLoc).toFunctor
    let raw :=
      (inherited_source_pullback_comparison
          (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) k
          (((canonicalFiberPseudofunctor (G F)).map f.op.toLoc).toFunctor.obj x)).hom ≫
        TX.map
          (inherited_source_pullback_comparison
            (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) f x).hom ≫
        (((canonicalFiberPseudofunctor Xₛ.p).mapComp'
          (Yₛ.p.map f).op.toLoc (Yₛ.p.map k).op.toLoc (Yₛ.p.map kf).op.toLoc
          (base_comp_toLoc_eq (f := Yₛ.p.map f) (g := Yₛ.p.map k)
            (gf := Yₛ.p.map kf) (by rw [← Functor.map_comp, hkf]))).inv.toNatTrans.app
        (inherited_source_fiber_obj (F := F) x))
    let strict :=
      (inherited_source_fiber_forget (F := F) V').map
          (((canonicalFiberPseudofunctor (G F)).mapComp'
              f.op.toLoc k.op.toLoc kf.op.toLoc
              (inherited_comp_toLoc_eq (Yₛ := Yₛ) f k kf hkf)).inv.toNatTrans.app x) ≫
        (inherited_source_pullback_comparison
          (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) kf x).hom
    let tail :=
      (canonicalPullbackChoice Xₛ.p).map (Yₛ.p.map kf)
        (inherited_source_fiber_obj (F := F) x)
    raw.1 ≫ tail = strict.1 ≫ tail := by
  let TX := ((canonicalFiberPseudofunctor Xₛ.p).map (Yₛ.p.map k).op.toLoc).toFunctor
  let ck := inherited_source_pullback_comparison
    (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) k
    (((canonicalFiberPseudofunctor (G F)).map f.op.toLoc).toFunctor.obj x)
  let ef := inherited_source_pullback_comparison
    (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) f x
  let ekf := inherited_source_pullback_comparison
    (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) kf x
  let rightX :=
    (((canonicalFiberPseudofunctor Xₛ.p).mapComp'
      (Yₛ.p.map f).op.toLoc (Yₛ.p.map k).op.toLoc (Yₛ.p.map kf).op.toLoc
      (base_comp_toLoc_eq (f := Yₛ.p.map f) (g := Yₛ.p.map k)
        (gf := Yₛ.p.map kf) (by rw [← Functor.map_comp, hkf]))).inv.toNatTrans.app
      (inherited_source_fiber_obj (F := F) x))
  let rightGF :=
    (((canonicalFiberPseudofunctor (G F)).mapComp'
      f.op.toLoc k.op.toLoc kf.op.toLoc
      (inherited_comp_toLoc_eq (Yₛ := Yₛ) f k kf hkf)).inv.toNatTrans.app x)
  let raw := ck.hom ≫ TX.map ef.hom ≫ rightX
  let strict := (inherited_source_fiber_forget (F := F) V').map rightGF ≫ ekf.hom
  let tail :=
    (canonicalPullbackChoice Xₛ.p).map (Yₛ.p.map kf)
      (inherited_source_fiber_obj (F := F) x)
  let tailKSource :=
    (canonicalPullbackChoice Xₛ.p).map (Yₛ.p.map k)
      (((canonicalFiberPseudofunctor Xₛ.p).map (Yₛ.p.map f).op.toLoc).toFunctor.obj
        (inherited_source_fiber_obj (F := F) x))
  let tailKTarget :=
    (canonicalPullbackChoice Xₛ.p).map (Yₛ.p.map k)
      (inherited_source_fiber_obj (F := F)
        (((canonicalFiberPseudofunctor (G F)).map f.op.toLoc).toFunctor.obj x))
  let tailXf :=
    (canonicalPullbackChoice Xₛ.p).map (Yₛ.p.map f) (inherited_source_fiber_obj (F := F) x)
  let tailGFk :=
    (canonicalPullbackChoice (G F)).map k
      (((canonicalFiberPseudofunctor (G F)).map f.op.toLoc).toFunctor.obj x)
  let tailGFf := (canonicalPullbackChoice (G F)).map f x
  let tailGFkf := (canonicalPullbackChoice (G F)).map kf x
  have hrightX :
      rightX.1 ≫ tail = tailKSource ≫ tailXf := by
    -- The inverse `Xₛ` map-composition component factors the composite pullback arrow.
    simpa only [rightX, tail, tailKSource, tailXf] using
      FibredCategoryMor.canonicalFiberPseudofunctor_mapComp'_inv_app_fac
        (p := Xₛ.p) (f := Yₛ.p.map f) (g := Yₛ.p.map k)
        (gf := Yₛ.p.map kf)
        (hgf := by rw [← Functor.map_comp, hkf])
        (inherited_source_fiber_obj (F := F) x)
  have hmapHom :
      (TX.map ef.hom).1 ≫ tailKSource = tailKTarget ≫ ef.hom.1 := by
    -- Move the direct comparison through the canonical pullback functor over `k`.
    simpa only [TX, ef, tailKSource, tailKTarget] using
      canonical_pullbackFunctor_map_fac_owner
        (p := Xₛ.p) (f := Yₛ.p.map k) (φ := ef.hom)
  have hck :
      ck.hom.1 ≫ tailKTarget = tailGFk := by
    -- The comparison for the `k`-pullback postcomposes to the chosen `(G F)` pullback arrow.
    simpa only [ck, tailKTarget, tailGFk] using
      inherited_source_pullback_comparison_hom_postcompose
        (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) k
        (((canonicalFiberPseudofunctor (G F)).map f.op.toLoc).toFunctor.obj x)
  have hef :
      ef.hom.1 ≫ tailXf = tailGFf := by
    -- The comparison for the `f`-pullback postcomposes to the chosen `(G F)` pullback arrow.
    simpa only [ef, tailXf, tailGFf] using
      inherited_source_pullback_comparison_hom_postcompose
        (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) f x
  have hrightGF :
      rightGF.1 ≫ tailGFkf = tailGFk ≫ tailGFf := by
    -- The inverse `(G F)` map-composition component factors the composite pullback arrow.
    simpa only [rightGF, tailGFkf, tailGFk, tailGFf] using
      FibredCategoryMor.canonicalFiberPseudofunctor_mapComp'_inv_app_fac
        (p := G F) (f := f) (g := k) (gf := kf) (hgf := hkf) x
  have hekf :
      ekf.hom.1 ≫ tail = tailGFkf := by
    -- The comparison for the composite leg postcomposes to the chosen `(G F)` pullback arrow.
    simpa only [ekf, tail, tailGFkf] using
      inherited_source_pullback_comparison_hom_postcompose
        (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) kf x
  have hraw :
      raw.1 ≫ tail = tailGFk ≫ tailGFf := by
    have hraw_pre :
        raw.1 ≫ tail = tailGFk ≫ (ef.hom.1 ≫ tailXf) := by
      calc
        raw.1 ≫ tail =
          (ck.hom.1 ≫ (TX.map ef.hom).1 ≫ rightX.1) ≫ tail := by
            rfl
        _ = ck.hom.1 ≫ (TX.map ef.hom).1 ≫ (rightX.1 ≫ tail) := by
            simp only [Category.assoc]
        _ = ck.hom.1 ≫ (TX.map ef.hom).1 ≫ (tailKSource ≫ tailXf) := by
            exact congrArg (fun a ↦ ck.hom.1 ≫ (TX.map ef.hom).1 ≫ a) hrightX
        _ = ck.hom.1 ≫ ((TX.map ef.hom).1 ≫ tailKSource) ≫ tailXf := by
            simp only [Category.assoc]
        _ = ck.hom.1 ≫ (tailKTarget ≫ ef.hom.1) ≫ tailXf := by
            exact congrArg (fun a ↦ ck.hom.1 ≫ a ≫ tailXf) hmapHom
        _ = (ck.hom.1 ≫ tailKTarget) ≫ (ef.hom.1 ≫ tailXf) := by
            simp only [Category.assoc]
        _ = tailGFk ≫ (ef.hom.1 ≫ tailXf) := by
            exact congrArg (fun a ↦ a ≫ (ef.hom.1 ≫ tailXf)) hck
    exact hraw_pre.trans (congrArg (fun a ↦ tailGFk ≫ a) hef)
  have hstrict :
      strict.1 ≫ tail = tailGFk ≫ tailGFf := by
    have hforget :
        ((inherited_source_fiber_forget (F := F) V').map rightGF).1 = rightGF.1 := by
      rfl
    have hstrict_pre :
        strict.1 ≫ tail =
          ((inherited_source_fiber_forget (F := F) V').map rightGF).1 ≫ tailGFkf := by
      calc
        strict.1 ≫ tail =
          (((inherited_source_fiber_forget (F := F) V').map rightGF).1 ≫
              ekf.hom.1) ≫ tail := by
            rfl
        _ = ((inherited_source_fiber_forget (F := F) V').map rightGF).1 ≫
            (ekf.hom.1 ≫ tail) := by
            simp only [Category.assoc]
        _ = ((inherited_source_fiber_forget (F := F) V').map rightGF).1 ≫
            tailGFkf := by
            exact congrArg
              (fun a ↦ ((inherited_source_fiber_forget (F := F) V').map rightGF).1 ≫ a)
              hekf
    have hstrict_mid :
        strict.1 ≫ tail = rightGF.1 ≫ tailGFkf :=
      hstrict_pre.trans (congrArg (fun a ↦ a ≫ tailGFkf) hforget)
    exact hstrict_mid.trans hrightGF
  -- Both postcomposed right shells are the same iterated `(G F)` pullback factorization.
  exact hraw.trans hstrict.symm

/-- Helper for Lemma 8.10.5: the right composition boundary for the inherited source pullback
comparison rewrites the iterated `Xₛ` pullback shell back to the composite-leg comparison after
the middle refinement morphism has been transported across `k`. -/
theorem inherited_source_pullback_comparison_comp_hom_right_boundary
    (F : Xₛ ⟶ Yₛ)
    [IsFibredInGroupoids (G F)]
    {U V V' : Yₛ.S} (f : V ⟶ U) (k : V' ⟶ V) (kf : V' ⟶ U)
    (hkf : k ≫ f = kf := by cat_disch) (x : (G F).Fiber U) :
    let TX := ((canonicalFiberPseudofunctor Xₛ.p).map (Yₛ.p.map k).op.toLoc).toFunctor
    let rightX :=
      (((canonicalFiberPseudofunctor Xₛ.p).mapComp'
          (Yₛ.p.map f).op.toLoc (Yₛ.p.map k).op.toLoc (Yₛ.p.map kf).op.toLoc
          (base_comp_toLoc_eq (f := Yₛ.p.map f) (g := Yₛ.p.map k)
            (gf := Yₛ.p.map kf) (by rw [← Functor.map_comp, hkf]))).inv.toNatTrans.app
        (inherited_source_fiber_obj (F := F) x))
    let rightGF :=
      (((canonicalFiberPseudofunctor (G F)).mapComp'
          f.op.toLoc k.op.toLoc kf.op.toLoc
          (inherited_comp_toLoc_eq (Yₛ := Yₛ) f k kf hkf)).inv.toNatTrans.app x)
    let ef := inherited_source_pullback_comparison
      (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) f x
    let ekf := inherited_source_pullback_comparison
      (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) kf x
    let ck := inherited_source_pullback_comparison
      (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) k
      (((canonicalFiberPseudofunctor (G F)).map f.op.toLoc).toFunctor.obj x)
    ck.hom ≫ TX.map ef.hom ≫ rightX =
      (inherited_source_fiber_forget (F := F) V').map rightGF ≫ ekf.hom := by
  let TX := ((canonicalFiberPseudofunctor Xₛ.p).map (Yₛ.p.map k).op.toLoc).toFunctor
  let rightX :=
    (((canonicalFiberPseudofunctor Xₛ.p).mapComp'
        (Yₛ.p.map f).op.toLoc (Yₛ.p.map k).op.toLoc (Yₛ.p.map kf).op.toLoc
        (base_comp_toLoc_eq (f := Yₛ.p.map f) (g := Yₛ.p.map k)
          (gf := Yₛ.p.map kf) (by rw [← Functor.map_comp, hkf]))).inv.toNatTrans.app
      (inherited_source_fiber_obj (F := F) x))
  let rightGF :=
    (((canonicalFiberPseudofunctor (G F)).mapComp'
        f.op.toLoc k.op.toLoc kf.op.toLoc
        (inherited_comp_toLoc_eq (Yₛ := Yₛ) f k kf hkf)).inv.toNatTrans.app x)
  let ef := inherited_source_pullback_comparison
    (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) f x
  let ekf := inherited_source_pullback_comparison
    (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) kf x
  let ck := inherited_source_pullback_comparison
    (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) k
    (((canonicalFiberPseudofunctor (G F)).map f.op.toLoc).toFunctor.obj x)
  let raw := ck.hom ≫ TX.map ef.hom ≫ rightX
  let strict := (inherited_source_fiber_forget (F := F) V').map rightGF ≫ ekf.hom
  let tail :=
    (canonicalPullbackChoice Xₛ.p).map (Yₛ.p.map kf)
      (inherited_source_fiber_obj (F := F) x)
  have htail :
      Xₛ.p.IsStronglyCartesian (Yₛ.p.map kf) tail := by
    -- The right boundary is canceled against the canonical source pullback over the composite leg.
    exact
      (canonicalPullbackChoice Xₛ.p).isStronglyCartesian (Yₛ.p.map kf)
        (inherited_source_fiber_obj (F := F) x)
  have hpost :
      raw.1 ≫ tail = strict.1 ≫ tail := by
    -- The postcomposed shells were normalized in the preceding helper.
    simpa only [raw, strict, tail, TX, rightX, rightGF, ef, ekf, ck] using
      inherited_source_pullback_comparison_comp_hom_right_boundary_postcompose_kf
        (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F f k kf hkf x
  -- Cancel the common strongly cartesian composite-leg pullback arrow.
  apply Functor.Fiber.hom_ext
  change raw.1 = strict.1
  exact
    @Functor.IsStronglyCartesian.ext _ _ _ _ Xₛ.p _ _ _ _
      (Yₛ.p.map kf) tail htail _ _ (𝟙 (Yₛ.p.obj V'))
      raw.1 strict.1 raw.2 strict.2 hpost

/-- Helper for Lemma 8.10.5: after the two comparison boundaries are normalized, the three
forgotten `(G F)` refinement pieces fold back to the source-side `pullHom` shell. -/
theorem inherited_source_fiber_forget_pullHom_source_shell_map
    (F : Xₛ ⟶ Yₛ)
    [IsFibredInGroupoids (G F)]
    {ι : Type*} {y : Yₛ.S} {Y : ι → Yₛ.S} {g : ∀ i, Y i ⟶ y}
    (D : ((canonicalFiberPseudofunctor (G F)).DescentData g))
    {Z' Z : Yₛ.S} (k : Z' ⟶ Z) (q : Z ⟶ y)
    {i₁ i₂ : ι} (f₁ : Z ⟶ Y i₁) (f₂ : Z ⟶ Y i₂)
    (hf₁ : f₁ ≫ g i₁ = q := by cat_disch) (hf₂ : f₂ ≫ g i₂ = q := by cat_disch)
    (kf₁ : Z' ⟶ Y i₁) (kf₂ : Z' ⟶ Y i₂)
    (hkf₁ : k ≫ f₁ = kf₁ := by cat_disch) (hkf₂ : k ≫ f₂ = kf₂ := by cat_disch) :
    let leftGF :=
      (((canonicalFiberPseudofunctor (G F)).mapComp'
          f₁.op.toLoc k.op.toLoc kf₁.op.toLoc
          (inherited_comp_toLoc_eq (Yₛ := Yₛ) f₁ k kf₁ hkf₁)).hom.toNatTrans.app
        (D.obj i₁))
    let rightGF :=
      (((canonicalFiberPseudofunctor (G F)).mapComp'
          f₂.op.toLoc k.op.toLoc kf₂.op.toLoc
          (inherited_comp_toLoc_eq (Yₛ := Yₛ) f₂ k kf₂ hkf₂)).inv.toNatTrans.app
        (D.obj i₂))
    (inherited_source_fiber_forget (F := F) Z').map leftGF ≫
        (inherited_source_fiber_forget (F := F) Z').map
          ((((canonicalFiberPseudofunctor (G F)).map k.op.toLoc).toFunctor.map
            (D.hom q f₁ f₂ hf₁ hf₂))) ≫
        (inherited_source_fiber_forget (F := F) Z').map rightGF =
      (inherited_source_fiber_forget (F := F) Z').map
        (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (D.hom q f₁ f₂ hf₁ hf₂) k kf₁ kf₂ hkf₁ hkf₂) := by
  let leftGF :=
    (((canonicalFiberPseudofunctor (G F)).mapComp'
        f₁.op.toLoc k.op.toLoc kf₁.op.toLoc
        (inherited_comp_toLoc_eq (Yₛ := Yₛ) f₁ k kf₁ hkf₁)).hom.toNatTrans.app
      (D.obj i₁))
  let rightGF :=
    (((canonicalFiberPseudofunctor (G F)).mapComp'
        f₂.op.toLoc k.op.toLoc kf₂.op.toLoc
        (inherited_comp_toLoc_eq (Yₛ := Yₛ) f₂ k kf₂ hkf₂)).inv.toNatTrans.app
      (D.obj i₂))
  -- Unfold the source-side `pullHom` once and fold the visible threefold composite through the
  -- fixed forgetting functor over `Z'`.
  rw [Pseudofunctor.LocallyDiscreteOpToCat.pullHom]
  change
    (inherited_source_fiber_forget (F := F) Z').map leftGF ≫
        (inherited_source_fiber_forget (F := F) Z').map
          ((((canonicalFiberPseudofunctor (G F)).map k.op.toLoc).toFunctor.map
            (D.hom q f₁ f₂ hf₁ hf₂))) ≫
        (inherited_source_fiber_forget (F := F) Z').map rightGF =
      (inherited_source_fiber_forget (F := F) Z').map
        (leftGF ≫
          ((((canonicalFiberPseudofunctor (G F)).map k.op.toLoc).toFunctor.map
            (D.hom q f₁ f₂ hf₁ hf₂)) ≫ rightGF))
  rw [functor_map_threefold_comp]

/-- Helper for Lemma 8.10.5: before the literal-base counit shell is reintroduced, the forgotten
source overlap morphism is compatible with pulling back along an actual upstairs refinement. -/
theorem inherited_basis_descent_hom_pullHom_refinement
    (F : Xₛ ⟶ Yₛ)
    [IsFibredInGroupoids (G F)]
    {ι : Type*} {y : Yₛ.S} {Y : ι → Yₛ.S} {g : ∀ i, Y i ⟶ y}
    (D : ((canonicalFiberPseudofunctor (G F)).DescentData g))
    {Z' Z : Yₛ.S} (k : Z' ⟶ Z) (q : Z ⟶ y) (q' : Z' ⟶ y)
    (hq : k ≫ q = q')
    {i₁ i₂ : ι} (f₁ : Z ⟶ Y i₁) (f₂ : Z ⟶ Y i₂)
    (hf₁ : f₁ ≫ g i₁ = q := by cat_disch) (hf₂ : f₂ ≫ g i₂ = q := by cat_disch)
    (kf₁ : Z' ⟶ Y i₁) (kf₂ : Z' ⟶ Y i₂)
    (hkf₁ : k ≫ f₁ = kf₁ := by cat_disch) (hkf₂ : k ≫ f₂ = kf₂ := by cat_disch) :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (inherited_basis_descent_hom
          (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F D q f₁ f₂ hf₁ hf₂)
        (Yₛ.p.map k) (Yₛ.p.map kf₁) (Yₛ.p.map kf₂)
        (by rw [← Functor.map_comp, hkf₁])
        (by rw [← Functor.map_comp, hkf₂]) =
      inherited_basis_descent_hom
        (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F D q' kf₁ kf₂
        (by rw [← hq, ← hkf₁, Category.assoc, hf₁])
        (by rw [← hq, ← hkf₂, Category.assoc, hf₂]) := by
  let e₁ :=
    inherited_source_pullback_comparison
      (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) f₁ (D.obj i₁)
  let e₂ :=
    inherited_source_pullback_comparison
      (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) f₂ (D.obj i₂)
  let ek₁ :=
    inherited_source_pullback_comparison
      (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) kf₁ (D.obj i₁)
  let ek₂ :=
    inherited_source_pullback_comparison
      (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) kf₂ (D.obj i₂)
  let T := ((canonicalFiberPseudofunctor Xₛ.p).map (Yₛ.p.map k).op.toLoc).toFunctor
  let d :=
    (inherited_source_fiber_forget (F := F) Z).map (D.hom q f₁ f₂ hf₁ hf₂)
  let dk :=
    (inherited_source_fiber_forget (F := F) Z').map
      (D.hom q' kf₁ kf₂
        (by rw [← hq, ← hkf₁, Category.assoc, hf₁])
        (by rw [← hq, ← hkf₂, Category.assoc, hf₂]))
  -- First normalize the middle descent morphism with the source descent pullback law.
  have hD :
      (inherited_source_fiber_forget (F := F) Z').map
          (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
            (D.hom q f₁ f₂ hf₁ hf₂) k kf₁ kf₂ hkf₁ hkf₂) =
        dk := by
    exact congrArg
      (fun φ ↦ (inherited_source_fiber_forget (F := F) Z').map φ)
      (D.pullHom_hom k q q' hq f₁ f₂ hf₁ hf₂ kf₁ kf₂ hkf₁ hkf₂)
  let ck₁ :=
    inherited_source_pullback_comparison
      (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) k
      (((canonicalFiberPseudofunctor (G F)).map f₁.op.toLoc).toFunctor.obj (D.obj i₁))
  let ck₂ :=
    inherited_source_pullback_comparison
      (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) k
      (((canonicalFiberPseudofunctor (G F)).map f₂.op.toLoc).toFunctor.obj (D.obj i₂))
  let leftX :=
    (((canonicalFiberPseudofunctor Xₛ.p).mapComp'
        (Yₛ.p.map f₁).op.toLoc (Yₛ.p.map k).op.toLoc (Yₛ.p.map kf₁).op.toLoc
        (base_comp_toLoc_eq (f := Yₛ.p.map f₁) (g := Yₛ.p.map k)
          (gf := Yₛ.p.map kf₁) (by rw [← Functor.map_comp, hkf₁]))).hom.toNatTrans.app
      (inherited_source_fiber_obj (F := F) (D.obj i₁)))
  let rightX :=
    (((canonicalFiberPseudofunctor Xₛ.p).mapComp'
        (Yₛ.p.map f₂).op.toLoc (Yₛ.p.map k).op.toLoc (Yₛ.p.map kf₂).op.toLoc
        (base_comp_toLoc_eq (f := Yₛ.p.map f₂) (g := Yₛ.p.map k)
          (gf := Yₛ.p.map kf₂) (by rw [← Functor.map_comp, hkf₂]))).inv.toNatTrans.app
      (inherited_source_fiber_obj (F := F) (D.obj i₂)))
  let leftGF :=
    (((canonicalFiberPseudofunctor (G F)).mapComp'
        f₁.op.toLoc k.op.toLoc kf₁.op.toLoc
        (inherited_comp_toLoc_eq (Yₛ := Yₛ) f₁ k kf₁ hkf₁)).hom.toNatTrans.app
      (D.obj i₁))
  let rightGF :=
    (((canonicalFiberPseudofunctor (G F)).mapComp'
        f₂.op.toLoc k.op.toLoc kf₂.op.toLoc
        (inherited_comp_toLoc_eq (Yₛ := Yₛ) f₂ k kf₂ hkf₂)).inv.toNatTrans.app
      (D.obj i₂))
  let midGF :=
    (inherited_source_fiber_forget (F := F) Z').map
      ((((canonicalFiberPseudofunctor (G F)).map k.op.toLoc).toFunctor.map
        (D.hom q f₁ f₂ hf₁ hf₂)))
  have hleft :
      leftX ≫ T.map e₁.inv =
        ek₁.inv ≫ (inherited_source_fiber_forget (F := F) Z').map leftGF ≫ ck₁.hom := by
    -- Normalize the left composition-comparison boundary to the common refinement leg.
    simpa only [leftX, T, e₁, ek₁, leftGF, ck₁] using
      inherited_source_pullback_comparison_comp_inv_left_boundary
        (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F f₁ k kf₁ hkf₁ (D.obj i₁)
  have hmid :
      ck₁.hom ≫ T.map d = midGF ≫ ck₂.hom := by
    -- Move the forgotten middle overlap morphism across the `k`-comparison square.
    simpa only [ck₁, ck₂, T, d, midGF] using
      (inherited_source_pullback_comparison_naturality_over_vertical
        (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F)
        (f := k) (φ := D.hom q f₁ f₂ hf₁ hf₂)).symm
  have hright :
      ck₂.hom ≫ T.map e₂.hom ≫ rightX =
        (inherited_source_fiber_forget (F := F) Z').map rightGF ≫ ek₂.hom := by
    -- Normalize the right composition-comparison boundary to the common refinement leg.
    simpa only [rightX, T, e₂, ek₂, rightGF, ck₂] using
      inherited_source_pullback_comparison_comp_hom_right_boundary
        (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F f₂ k kf₂ hkf₂ (D.obj i₂)
  have hfold :
      (inherited_source_fiber_forget (F := F) Z').map leftGF ≫ midGF ≫
          (inherited_source_fiber_forget (F := F) Z').map rightGF =
        (inherited_source_fiber_forget (F := F) Z').map
          (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
            (D.hom q f₁ f₂ hf₁ hf₂) k kf₁ kf₂ hkf₁ hkf₂) := by
    -- Fold the three normalized source-side pieces back into the source `pullHom` shell.
    simpa only [leftGF, rightGF, midGF] using
      inherited_source_fiber_forget_pullHom_source_shell_map
        (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F D k q f₁ f₂ hf₁ hf₂
        kf₁ kf₂ hkf₁ hkf₂
  have hcalc :
      leftX ≫ T.map e₁.inv ≫ T.map d ≫ T.map e₂.hom ≫ rightX =
        ek₁.inv ≫ dk ≫ ek₂.hom := by
    calc
      leftX ≫ T.map e₁.inv ≫ T.map d ≫ T.map e₂.hom ≫ rightX =
          ek₁.inv ≫ (inherited_source_fiber_forget (F := F) Z').map leftGF ≫ ck₁.hom ≫
            T.map d ≫ T.map e₂.hom ≫ rightX := by
            calc
              leftX ≫ T.map e₁.inv ≫ T.map d ≫ T.map e₂.hom ≫ rightX =
                  (leftX ≫ T.map e₁.inv) ≫ T.map d ≫ T.map e₂.hom ≫ rightX := by
                    simp only [Category.assoc]
              _ =
                  (ek₁.inv ≫ (inherited_source_fiber_forget (F := F) Z').map leftGF ≫
                    ck₁.hom) ≫ T.map d ≫ T.map e₂.hom ≫ rightX := by
                    exact congrArg (fun a ↦ a ≫ T.map d ≫ T.map e₂.hom ≫ rightX) hleft
              _ =
                  ek₁.inv ≫ (inherited_source_fiber_forget (F := F) Z').map leftGF ≫
                    ck₁.hom ≫ T.map d ≫ T.map e₂.hom ≫ rightX := by
                    simp only [Category.assoc]
      _ =
          ek₁.inv ≫ (inherited_source_fiber_forget (F := F) Z').map leftGF ≫
            (ck₁.hom ≫ T.map d) ≫ T.map e₂.hom ≫ rightX := by
            simp only [Category.assoc]
      _ =
          ek₁.inv ≫ (inherited_source_fiber_forget (F := F) Z').map leftGF ≫
            (midGF ≫ ck₂.hom) ≫ T.map e₂.hom ≫ rightX := by
            exact congrArg
              (fun a ↦ ek₁.inv ≫ (inherited_source_fiber_forget (F := F) Z').map leftGF ≫
                a ≫ T.map e₂.hom ≫ rightX)
              hmid
      _ =
          ek₁.inv ≫ (inherited_source_fiber_forget (F := F) Z').map leftGF ≫ midGF ≫
            (ck₂.hom ≫ T.map e₂.hom ≫ rightX) := by
            simp only [Category.assoc]
      _ =
          ek₁.inv ≫ (inherited_source_fiber_forget (F := F) Z').map leftGF ≫ midGF ≫
            ((inherited_source_fiber_forget (F := F) Z').map rightGF ≫ ek₂.hom) := by
            exact congrArg
              (fun a ↦ ek₁.inv ≫ (inherited_source_fiber_forget (F := F) Z').map leftGF ≫
                midGF ≫ a)
              hright
      _ =
          ek₁.inv ≫
            ((inherited_source_fiber_forget (F := F) Z').map leftGF ≫ midGF ≫
              (inherited_source_fiber_forget (F := F) Z').map rightGF) ≫ ek₂.hom := by
            simp only [Category.assoc]
      _ =
          ek₁.inv ≫
            (inherited_source_fiber_forget (F := F) Z').map
              (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
                (D.hom q f₁ f₂ hf₁ hf₂) k kf₁ kf₂ hkf₁ hkf₂) ≫
            ek₂.hom := by
            exact congrArg (fun a ↦ ek₁.inv ≫ a ≫ ek₂.hom) hfold
      _ = ek₁.inv ≫ dk ≫ ek₂.hom := by
            exact congrArg (fun a ↦ ek₁.inv ≫ a ≫ ek₂.hom) hD
  have hcalc_assoc :
      leftX ≫ (T.map e₁.inv ≫ (T.map d ≫ T.map e₂.hom)) ≫ rightX =
        ek₁.inv ≫ dk ≫ ek₂.hom := by
    -- Reassociate the expanded `pullHom` shell into the normalized calculation shape.
    simpa only [Category.assoc] using hcalc
  -- Expand both `pullHom` shells and consume the normalized boundary calculation.
  rw [inherited_basis_descent_hom]
  simp only [Pseudofunctor.LocallyDiscreteOpToCat.pullHom, Functor.map_comp]
  simpa only [inherited_basis_descent_hom, T, d, dk, e₁, e₂, ek₁, ek₂, leftX, rightX] using
    hcalc_assoc

end

end CategoryTheory
