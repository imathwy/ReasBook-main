import StacksProject_2024.Chap08.Lemma_8_10_5.TargetOverlap

universe uC uX vC vX

namespace CategoryTheory

open FibredCategoryMor
open Functor IsStronglyCartesian
open StackInGroupoidsOver.Hom
open Opposite

section

variable {C : Type uC} [Category.{vC} C]
variable {J : GrothendieckTopology C}
variable {Xₛ Yₛ : StackInGroupoidsOver J}

/-- Helper for Lemma 8.10.5: two morphisms in the same target fiber are equal if they agree after
postcomposition with a cartesian arrow out of that fiber. -/
theorem target_fiber_hom_ext_of_cartesian_postcompose
    {Z U : C} {A B : Yₛ.p.Fiber Z} {T : Yₛ.S} {tail : B.1 ⟶ T}
    (q : Z ⟶ U) [Yₛ.p.IsStronglyCartesian q tail]
    (φ ψ : A ⟶ B) (h : φ.1 ≫ tail = ψ.1 ≫ tail) : φ = ψ := by
  -- Push the fiber equality to total-category morphisms and use the cartesian uniqueness
  -- principle with the identity lift over the overlap base.
  letI : Yₛ.p.IsHomLift (𝟙 Z) φ.1 := φ.2
  letI : Yₛ.p.IsHomLift (𝟙 Z) ψ.1 := ψ.2
  apply Functor.Fiber.hom_ext
  change φ.1 = ψ.1
  exact Functor.IsStronglyCartesian.ext Yₛ.p q tail (𝟙 Z) h

/-- Helper for Lemma 8.10.5: after fixing a reconstructed target object, the source-forgotten
component morphisms satisfy the same overlap equation once both sides are postcomposed with the
chosen comparison back to `D.obj i₂`. -/
theorem inherited_basis_reconstructed_component_postcancel
    (F : Xₛ ⟶ Yₛ) [IsFibredInGroupoids (G F)]
    {ι : Type*} {y : Yₛ.S} {Y : ι → Yₛ.S} {g : ∀ i, Y i ⟶ y}
    (D : ((canonicalFiberPseudofunctor (G F)).DescentData g))
    (x : Xₛ.p.Fiber (Yₛ.p.obj y))
    (ε :
      ((canonicalFiberPseudofunctor Xₛ.p).toDescentData
        (fun i ↦ Yₛ.p.map (g i))).obj x ≅
      (inherited_basis_simple_forget_to_source_descent_functor
        (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (Y := Y) (g := g) F).obj D)
    (A : (G F).Fiber y)
    (αX : inherited_source_fiber_obj (F := F) A ⟶ x)
    (componentHom :
      ∀ i,
        (((canonicalFiberPseudofunctor (G F)).map (g i).op.toLoc).toFunctor.obj A) ⟶
          D.obj i)
    (hcomponentHom :
      ∀ i,
        (inherited_source_fiber_forget (F := F) (Y i)).map (componentHom i) =
          (inherited_source_pullback_comparison
              (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) (g i) A).hom ≫
            (((canonicalFiberPseudofunctor Xₛ.p).map
                (Yₛ.p.map (g i)).op.toLoc).toFunctor.map αX) ≫
              ε.hom.hom i)
    {Z : Yₛ.S} (q : Z ⟶ y) {i₁ i₂ : ι}
    (f₁ : Z ⟶ Y i₁) (f₂ : Z ⟶ Y i₂)
    (hf₁ : f₁ ≫ g i₁ = q := by cat_disch)
    (hf₂ : f₂ ≫ g i₂ = q := by cat_disch) :
    let DA := (((canonicalFiberPseudofunctor (G F)).toDescentData g).obj A)
    let T₁G := ((canonicalFiberPseudofunctor (G F)).map f₁.op.toLoc).toFunctor
    let T₂G := ((canonicalFiberPseudofunctor (G F)).map f₂.op.toLoc).toFunctor
    let eD₂ :=
      inherited_source_pullback_comparison
        (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) f₂ (D.obj i₂)
    (inherited_source_fiber_forget (F := F) Z).map
        (T₁G.map (componentHom i₁) ≫ D.hom q f₁ f₂ hf₁ hf₂) ≫ eD₂.hom =
      (inherited_source_fiber_forget (F := F) Z).map
        (DA.hom q f₁ f₂ hf₁ hf₂ ≫ T₂G.map (componentHom i₂)) ≫ eD₂.hom := by
  intro DA T₁G T₂G eD₂
  let eD₁ :=
    inherited_source_pullback_comparison
      (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) f₁ (D.obj i₁)
  let AG₁ :=
    (((canonicalFiberPseudofunctor (G F)).map (g i₁).op.toLoc).toFunctor.obj A)
  let AG₂ :=
    (((canonicalFiberPseudofunctor (G F)).map (g i₂).op.toLoc).toFunctor.obj A)
  let eA₁ :=
    inherited_source_pullback_comparison
      (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) f₁ AG₁
  let eA₂ :=
    inherited_source_pullback_comparison
      (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) f₂ AG₂
  let eG₁ :=
    inherited_source_pullback_comparison
      (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) (g i₁) A
  let eG₂ :=
    inherited_source_pullback_comparison
      (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) (g i₂) A
  let sourceA := inherited_source_fiber_obj (F := F) A
  let SX :=
    ((canonicalFiberPseudofunctor Xₛ.p).toDescentData
      (fun i ↦ Yₛ.p.map (g i)))
  let T₁X :=
    ((canonicalFiberPseudofunctor Xₛ.p).map (Yₛ.p.map f₁).op.toLoc).toFunctor
  let T₂X :=
    ((canonicalFiberPseudofunctor Xₛ.p).map (Yₛ.p.map f₂).op.toLoc).toFunctor
  let sourceMap₁ :=
    ((canonicalFiberPseudofunctor Xₛ.p).map (Yₛ.p.map (g i₁)).op.toLoc).toFunctor
  let sourceMap₂ :=
    ((canonicalFiberPseudofunctor Xₛ.p).map (Yₛ.p.map (g i₂)).op.toLoc).toFunctor
  have hf₁base : Yₛ.p.map f₁ ≫ Yₛ.p.map (g i₁) = Yₛ.p.map q := by
    rw [← Functor.map_comp, hf₁]
  have hf₂base : Yₛ.p.map f₂ ≫ Yₛ.p.map (g i₂) = Yₛ.p.map q := by
    rw [← Functor.map_comp, hf₂]
  let dD :=
    inherited_basis_descent_hom
      (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F D q f₁ f₂ hf₁ hf₂
  let dA :=
    inherited_basis_descent_hom
      (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F DA q f₁ f₂ hf₁ hf₂
  let simpleD :=
    inherited_basis_simple_forget_to_source_descent_hom
      (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F D
      (Yₛ.p.map q) (Yₛ.p.map f₁) (Yₛ.p.map f₂) hf₁base hf₂base
  let simpleA :=
    inherited_basis_simple_forget_to_source_descent_hom
      (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F DA
      (Yₛ.p.map q) (Yₛ.p.map f₁) (Yₛ.p.map f₂) hf₁base hf₂base
  let canX :=
    (SX.obj x).hom (Yₛ.p.map q) (Yₛ.p.map f₁) (Yₛ.p.map f₂) hf₁base hf₂base
  let canA :=
    (SX.obj sourceA).hom (Yₛ.p.map q) (Yₛ.p.map f₁) (Yₛ.p.map f₂)
      hf₁base hf₂base
  have hDmid :
      (inherited_source_fiber_forget (F := F) Z).map (D.hom q f₁ f₂ hf₁ hf₂) ≫
          eD₂.hom =
        eD₁.hom ≫ dD := by
    change
      (inherited_source_fiber_forget (F := F) Z).map (D.hom q f₁ f₂ hf₁ hf₂) ≫
          eD₂.hom =
        eD₁.hom ≫
          (eD₁.inv ≫
            (inherited_source_fiber_forget (F := F) Z).map (D.hom q f₁ f₂ hf₁ hf₂) ≫
              eD₂.hom)
    calc
      (inherited_source_fiber_forget (F := F) Z).map (D.hom q f₁ f₂ hf₁ hf₂) ≫
          eD₂.hom =
          (eD₁.hom ≫ eD₁.inv) ≫
            (inherited_source_fiber_forget (F := F) Z).map (D.hom q f₁ f₂ hf₁ hf₂) ≫
              eD₂.hom := by
            rw [eD₁.hom_inv_id]
            simp only [Category.id_comp]
            rfl
      _ =
          eD₁.hom ≫
            (eD₁.inv ≫
              (inherited_source_fiber_forget (F := F) Z).map (D.hom q f₁ f₂ hf₁ hf₂) ≫
                eD₂.hom) := by
            simp only [Category.assoc]
  have hAmid :
      (inherited_source_fiber_forget (F := F) Z).map (DA.hom q f₁ f₂ hf₁ hf₂) ≫
          eA₂.hom =
        eA₁.hom ≫ dA := by
    change
      (inherited_source_fiber_forget (F := F) Z).map (DA.hom q f₁ f₂ hf₁ hf₂) ≫
          eA₂.hom =
        eA₁.hom ≫
          (eA₁.inv ≫
            (inherited_source_fiber_forget (F := F) Z).map (DA.hom q f₁ f₂ hf₁ hf₂) ≫
              eA₂.hom)
    calc
      (inherited_source_fiber_forget (F := F) Z).map (DA.hom q f₁ f₂ hf₁ hf₂) ≫
          eA₂.hom =
          (eA₁.hom ≫ eA₁.inv) ≫
            (inherited_source_fiber_forget (F := F) Z).map (DA.hom q f₁ f₂ hf₁ hf₂) ≫
              eA₂.hom := by
            rw [eA₁.hom_inv_id]
            simp only [Category.id_comp]
            rfl
      _ =
          eA₁.hom ≫
            (eA₁.inv ≫
              (inherited_source_fiber_forget (F := F) Z).map (DA.hom q f₁ f₂ hf₁ hf₂) ≫
                eA₂.hom) := by
            simp only [Category.assoc]
  have hnat₁ :
      (inherited_source_fiber_forget (F := F) Z).map (T₁G.map (componentHom i₁)) ≫
          eD₁.hom =
        eA₁.hom ≫
          T₁X.map ((inherited_source_fiber_forget (F := F) (Y i₁)).map
            (componentHom i₁)) := by
    simpa [T₁G, T₁X, eA₁, eD₁, AG₁] using
      inherited_source_pullback_comparison_naturality_over_vertical
        (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F)
        (f := f₁) (x := AG₁) (y := D.obj i₁) (componentHom i₁)
  have hnat₂ :
      (inherited_source_fiber_forget (F := F) Z).map (T₂G.map (componentHom i₂)) ≫
          eD₂.hom =
        eA₂.hom ≫
          T₂X.map ((inherited_source_fiber_forget (F := F) (Y i₂)).map
            (componentHom i₂)) := by
    simpa [T₂G, T₂X, eA₂, eD₂, AG₂] using
      inherited_source_pullback_comparison_naturality_over_vertical
        (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F)
        (f := f₂) (x := AG₂) (y := D.obj i₂) (componentHom i₂)
  have hsimpleD : simpleD = dD := by
    simpa [simpleD, dD] using
      inherited_basis_simple_forget_to_source_descent_hom_actual
        (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F D q f₁ f₂ hf₁ hf₂
  have hsimpleA : simpleA = dA := by
    simpa [simpleA, dA, DA] using
      inherited_basis_simple_forget_to_source_descent_hom_actual
        (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F DA q f₁ f₂ hf₁ hf₂
  have hε :
      T₁X.map (ε.hom.hom i₁) ≫ simpleD =
        canX ≫ T₂X.map (ε.hom.hom i₂) := by
    simpa [T₁X, T₂X, SX, canX, simpleD, hf₁base, hf₂base] using
      ε.hom.comm (Yₛ.p.map q) (Yₛ.p.map f₁) (Yₛ.p.map f₂) hf₁base hf₂base
  have hα :
      T₁X.map (sourceMap₁.map αX) ≫ canX =
        canA ≫ T₂X.map (sourceMap₂.map αX) := by
    have h :=
      (SX.map αX).comm
        (Yₛ.p.map q) (Yₛ.p.map f₁) (Yₛ.p.map f₂) hf₁base hf₂base
    simpa [SX, T₁X, T₂X, sourceMap₁, sourceMap₂, canX, canA, sourceA,
      hf₁base, hf₂base] using h
  have hAofObj :
      T₁X.map eG₁.hom ≫ canA =
        simpleA ≫ T₂X.map eG₂.hom := by
    change
      (((canonicalFiberPseudofunctor Xₛ.p).map (Yₛ.p.map f₁).op.toLoc).toFunctor.map
          (inherited_source_pullback_comparison
            (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) (g i₁) A).hom) ≫
        (((canonicalFiberPseudofunctor Xₛ.p).toDescentData
            (fun i ↦ Yₛ.p.map (g i))).obj sourceA).hom
          (Yₛ.p.map q) (Yₛ.p.map f₁) (Yₛ.p.map f₂) hf₁base hf₂base =
      inherited_basis_simple_forget_to_source_descent_hom
          (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F DA
          (Yₛ.p.map q) (Yₛ.p.map f₁) (Yₛ.p.map f₂) hf₁base hf₂base ≫
        (((canonicalFiberPseudofunctor Xₛ.p).map (Yₛ.p.map f₂).op.toLoc).toFunctor.map
          (inherited_source_pullback_comparison
            (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) (g i₂) A).hom)
    exact
      inherited_basis_simple_ofObj_source_overlap_comm
        (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F A
        (Yₛ.p.map q) (Yₛ.p.map f₁) (Yₛ.p.map f₂) hf₁base hf₂base
  have hsourceComm :
      T₁X.map ((inherited_source_fiber_forget (F := F) (Y i₁)).map (componentHom i₁)) ≫
          dD =
        dA ≫
          T₂X.map ((inherited_source_fiber_forget (F := F) (Y i₂)).map
            (componentHom i₂)) := by
    have hcomponentHom₁ :
        T₁X.map ((inherited_source_fiber_forget (F := F) (Y i₁)).map (componentHom i₁)) =
          T₁X.map (eG₁.hom ≫ sourceMap₁.map αX ≫ ε.hom.hom i₁) := by
      exact congrArg (fun t ↦ T₁X.map t) (hcomponentHom i₁)
    have hcomponentHom₂ :
        T₂X.map ((inherited_source_fiber_forget (F := F) (Y i₂)).map (componentHom i₂)) =
          T₂X.map (eG₂.hom ≫ sourceMap₂.map αX ≫ ε.hom.hom i₂) := by
      exact congrArg (fun t ↦ T₂X.map t) (hcomponentHom i₂)
    have hmap₁ :
        T₁X.map (eG₁.hom ≫ sourceMap₁.map αX ≫ ε.hom.hom i₁) =
          T₁X.map eG₁.hom ≫ T₁X.map (sourceMap₁.map αX) ≫
            T₁X.map (ε.hom.hom i₁) := by
      simp only [Functor.map_comp]
    have hmap₂ :
        T₂X.map (eG₂.hom ≫ sourceMap₂.map αX ≫ ε.hom.hom i₂) =
          T₂X.map eG₂.hom ≫ T₂X.map (sourceMap₂.map αX) ≫
            T₂X.map (ε.hom.hom i₂) := by
      simp only [Functor.map_comp]
    have hεstep :
        (T₁X.map eG₁.hom ≫ T₁X.map (sourceMap₁.map αX) ≫
            T₁X.map (ε.hom.hom i₁)) ≫ simpleD =
          T₁X.map eG₁.hom ≫
            (T₁X.map (sourceMap₁.map αX) ≫ canX) ≫
              T₂X.map (ε.hom.hom i₂) := by
      simpa only [Category.assoc] using
        congrArg
          (fun t ↦ (T₁X.map eG₁.hom ≫ T₁X.map (sourceMap₁.map αX)) ≫ t) hε
    have hαstep :
        T₁X.map eG₁.hom ≫
            (T₁X.map (sourceMap₁.map αX) ≫ canX) ≫
              T₂X.map (ε.hom.hom i₂) =
          T₁X.map eG₁.hom ≫
            (canA ≫ T₂X.map (sourceMap₂.map αX)) ≫
              T₂X.map (ε.hom.hom i₂) := by
      exact congrArg
        (fun t ↦ T₁X.map eG₁.hom ≫ t ≫ T₂X.map (ε.hom.hom i₂)) hα
    have hαassoc :
        T₁X.map eG₁.hom ≫
            (canA ≫ T₂X.map (sourceMap₂.map αX)) ≫
              T₂X.map (ε.hom.hom i₂) =
          (T₁X.map eG₁.hom ≫ canA) ≫ T₂X.map (sourceMap₂.map αX) ≫
              T₂X.map (ε.hom.hom i₂) := by
      simp only [Category.assoc]
    have hAstep :
        (T₁X.map eG₁.hom ≫ canA) ≫ T₂X.map (sourceMap₂.map αX) ≫
            T₂X.map (ε.hom.hom i₂) =
          (simpleA ≫ T₂X.map eG₂.hom) ≫ T₂X.map (sourceMap₂.map αX) ≫
            T₂X.map (ε.hom.hom i₂) := by
      exact congrArg
        (fun t ↦ t ≫ T₂X.map (sourceMap₂.map αX) ≫ T₂X.map (ε.hom.hom i₂))
        hAofObj
    have h0 :
        T₁X.map ((inherited_source_fiber_forget (F := F) (Y i₁)).map
              (componentHom i₁)) ≫ dD =
          T₁X.map (eG₁.hom ≫ sourceMap₁.map αX ≫ ε.hom.hom i₁) ≫ dD := by
      exact congrArg (fun t ↦ t ≫ dD) hcomponentHom₁
    have h1 :
        T₁X.map (eG₁.hom ≫ sourceMap₁.map αX ≫ ε.hom.hom i₁) ≫ dD =
          (T₁X.map eG₁.hom ≫ T₁X.map (sourceMap₁.map αX) ≫
            T₁X.map (ε.hom.hom i₁)) ≫ dD := by
      exact congrArg (fun t ↦ t ≫ dD) hmap₁
    have h2 :
        (T₁X.map eG₁.hom ≫ T₁X.map (sourceMap₁.map αX) ≫
            T₁X.map (ε.hom.hom i₁)) ≫ dD =
          (T₁X.map eG₁.hom ≫ T₁X.map (sourceMap₁.map αX) ≫
            T₁X.map (ε.hom.hom i₁)) ≫ simpleD := by
      exact congrArg
        (fun t ↦ (T₁X.map eG₁.hom ≫ T₁X.map (sourceMap₁.map αX) ≫
          T₁X.map (ε.hom.hom i₁)) ≫ t) hsimpleD.symm
    have h7 :
        (simpleA ≫ T₂X.map eG₂.hom) ≫ T₂X.map (sourceMap₂.map αX) ≫
            T₂X.map (ε.hom.hom i₂) =
          (dA ≫ T₂X.map eG₂.hom) ≫ T₂X.map (sourceMap₂.map αX) ≫
            T₂X.map (ε.hom.hom i₂) := by
      exact congrArg
        (fun t ↦ (t ≫ T₂X.map eG₂.hom) ≫ T₂X.map (sourceMap₂.map αX) ≫
          T₂X.map (ε.hom.hom i₂))
        hsimpleA
    have h8 :
        (dA ≫ T₂X.map eG₂.hom) ≫ T₂X.map (sourceMap₂.map αX) ≫
            T₂X.map (ε.hom.hom i₂) =
          dA ≫ T₂X.map (eG₂.hom ≫ sourceMap₂.map αX ≫ ε.hom.hom i₂) := by
      simpa only [Category.assoc] using congrArg (fun t ↦ dA ≫ t) hmap₂.symm
    have h9 :
        dA ≫ T₂X.map (eG₂.hom ≫ sourceMap₂.map αX ≫ ε.hom.hom i₂) =
          dA ≫ T₂X.map ((inherited_source_fiber_forget (F := F) (Y i₂)).map
            (componentHom i₂)) := by
      exact congrArg (fun t ↦ dA ≫ t) hcomponentHom₂.symm
    exact h0.trans (h1.trans (h2.trans
      (hεstep.trans (hαstep.trans (hαassoc.trans (hAstep.trans (h7.trans (h8.trans h9))))))))
  have hleft :
      (inherited_source_fiber_forget (F := F) Z).map
          (T₁G.map (componentHom i₁) ≫ D.hom q f₁ f₂ hf₁ hf₂) ≫ eD₂.hom =
        eA₁.hom ≫
          T₁X.map ((inherited_source_fiber_forget (F := F) (Y i₁)).map
            (componentHom i₁)) ≫ dD := by
    calc
      (inherited_source_fiber_forget (F := F) Z).map
          (T₁G.map (componentHom i₁) ≫ D.hom q f₁ f₂ hf₁ hf₂) ≫ eD₂.hom =
          (inherited_source_fiber_forget (F := F) Z).map (T₁G.map (componentHom i₁)) ≫
            (inherited_source_fiber_forget (F := F) Z).map (D.hom q f₁ f₂ hf₁ hf₂) ≫
              eD₂.hom := by
            simp only [Functor.map_comp, Category.assoc]
      _ = (inherited_source_fiber_forget (F := F) Z).map (T₁G.map (componentHom i₁)) ≫
            (eD₁.hom ≫ dD) := by
            exact congrArg
              (fun t ↦ (inherited_source_fiber_forget (F := F) Z).map
                (T₁G.map (componentHom i₁)) ≫ t) hDmid
      _ = ((inherited_source_fiber_forget (F := F) Z).map (T₁G.map (componentHom i₁)) ≫
            eD₁.hom) ≫ dD := by
            simp only [Category.assoc]
      _ = (eA₁.hom ≫
            T₁X.map ((inherited_source_fiber_forget (F := F) (Y i₁)).map
              (componentHom i₁))) ≫ dD := by
            exact congrArg (fun t ↦ t ≫ dD) hnat₁
      _ = eA₁.hom ≫
            T₁X.map ((inherited_source_fiber_forget (F := F) (Y i₁)).map
              (componentHom i₁)) ≫ dD := by
            simp only [Category.assoc]
  have hright :
      (inherited_source_fiber_forget (F := F) Z).map
          (DA.hom q f₁ f₂ hf₁ hf₂ ≫ T₂G.map (componentHom i₂)) ≫ eD₂.hom =
        eA₁.hom ≫ dA ≫
          T₂X.map ((inherited_source_fiber_forget (F := F) (Y i₂)).map
            (componentHom i₂)) := by
    have hr0 :
        (inherited_source_fiber_forget (F := F) Z).map
            (DA.hom q f₁ f₂ hf₁ hf₂ ≫ T₂G.map (componentHom i₂)) ≫ eD₂.hom =
          (inherited_source_fiber_forget (F := F) Z).map (DA.hom q f₁ f₂ hf₁ hf₂) ≫
            (inherited_source_fiber_forget (F := F) Z).map (T₂G.map (componentHom i₂)) ≫
              eD₂.hom := by
      simp only [Functor.map_comp, Category.assoc]
    have hr1 :
        (inherited_source_fiber_forget (F := F) Z).map (DA.hom q f₁ f₂ hf₁ hf₂) ≫
            (inherited_source_fiber_forget (F := F) Z).map (T₂G.map (componentHom i₂)) ≫
              eD₂.hom =
          (inherited_source_fiber_forget (F := F) Z).map (DA.hom q f₁ f₂ hf₁ hf₂) ≫
            (eA₂.hom ≫
              T₂X.map ((inherited_source_fiber_forget (F := F) (Y i₂)).map
                (componentHom i₂))) := by
      exact congrArg
        (fun t ↦ (inherited_source_fiber_forget (F := F) Z).map
          (DA.hom q f₁ f₂ hf₁ hf₂) ≫ t) hnat₂
    have hr2 :
        (inherited_source_fiber_forget (F := F) Z).map (DA.hom q f₁ f₂ hf₁ hf₂) ≫
            (eA₂.hom ≫
              T₂X.map ((inherited_source_fiber_forget (F := F) (Y i₂)).map
                (componentHom i₂))) =
          ((inherited_source_fiber_forget (F := F) Z).map (DA.hom q f₁ f₂ hf₁ hf₂) ≫
            eA₂.hom) ≫
              T₂X.map ((inherited_source_fiber_forget (F := F) (Y i₂)).map
                (componentHom i₂)) := by
      simp only [Category.assoc]
    have hr3 :
        ((inherited_source_fiber_forget (F := F) Z).map (DA.hom q f₁ f₂ hf₁ hf₂) ≫
            eA₂.hom) ≫
              T₂X.map ((inherited_source_fiber_forget (F := F) (Y i₂)).map
                (componentHom i₂)) =
          (eA₁.hom ≫ dA) ≫
              T₂X.map ((inherited_source_fiber_forget (F := F) (Y i₂)).map
                (componentHom i₂)) := by
      exact congrArg
        (fun t ↦ t ≫ T₂X.map
          ((inherited_source_fiber_forget (F := F) (Y i₂)).map (componentHom i₂)))
        hAmid
    have hr4 :
        (eA₁.hom ≫ dA) ≫
            T₂X.map ((inherited_source_fiber_forget (F := F) (Y i₂)).map
              (componentHom i₂)) =
          eA₁.hom ≫ dA ≫
            T₂X.map ((inherited_source_fiber_forget (F := F) (Y i₂)).map
              (componentHom i₂)) := by
      simp only [Category.assoc]
    exact hr0.trans (hr1.trans (hr2.trans (hr3.trans hr4)))
  have hsourceComm_pre :
      eA₁.hom ≫
          T₁X.map ((inherited_source_fiber_forget (F := F) (Y i₁)).map
            (componentHom i₁)) ≫ dD =
        eA₁.hom ≫ dA ≫
          T₂X.map ((inherited_source_fiber_forget (F := F) (Y i₂)).map
            (componentHom i₂)) := by
    simpa only [Category.assoc] using congrArg (fun t ↦ eA₁.hom ≫ t) hsourceComm
  exact hleft.trans (hsourceComm_pre.trans hright.symm)

end

end CategoryTheory
