import Mathlib
import stacks_proof.stacks_project.Chap10.Definition_10_71_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.ProjectiveResolution
open CochainComplex.HomComplex
open HomologicalComplex
open ChainComplex

noncomputable section

universe u v

section

variable {R : Type u} [Ring R]
variable {M1 M2 N : Type v}
variable [AddCommGroup M1] [Module R M1]
variable [AddCommGroup M2] [Module R M2]
variable [AddCommGroup N] [Module R N]
variable {F G : ChainComplex (ModuleCat R) ℕ}

local notation "moduleSingle[" M "]" =>
  CategoryTheory.Functor.obj (ChainComplex.single₀ (ModuleCat R)) (ModuleCat.of R M)

local notation "cochainSingle[" M "]" =>
  CategoryTheory.Functor.obj (CochainComplex.singleFunctor (ModuleCat R) 0) (ModuleCat.of R M)

local notation "freeResolution[" π "]" =>
  IsFreeResolution.toProjectiveResolution π

local notation "resolutionHomComplex[" π "]" =>
  CochainComplex.HomComplex
    (ProjectiveResolution.cochainComplex freeResolution[π])
    cochainSingle[N]

namespace ProjectiveResolution.Hom

/-- Helper for Lemma 10.71.5: the outer Hom-complex differential is definitionally the inner
`HomComplex.δ` differential on cochains. -/
lemma resolutionHomComplex_d_apply
    {M : Type v} [AddCommGroup M] [Module R M]
    {K : ChainComplex (ModuleCat R) ℕ}
    {π : K ⟶ moduleSingle[M]} [IsFreeResolution π]
    (i j : ℤ) (x : resolutionHomComplex[π].X i) :
    ((resolutionHomComplex[π].d i j) x) = δ i j x := rfl

/-- Helper for Lemma 10.71.5: degree bookkeeping for composing a degree `-1` cochain with a
degree `p` cochain. -/
lemma precomp_homotopy_comp_eq {p q : ℤ} (hpq : p + (-1) = q) :
    (-1) + p = q := by
  omega

/-- Helper for Lemma 10.71.5: the degree-`(p - 1)` precomposition map associated to a homotopy
between compatible lifts. -/
noncomputable def precomp_homotopy_component
    {πF : F ⟶ moduleSingle[M1]} {πG : G ⟶ moduleSingle[M2]}
    [IsFreeResolution πF] [IsFreeResolution πG]
    {f : ModuleCat.of R M1 ⟶ ModuleCat.of R M2}
    {γ δ : freeResolution[πF].Hom freeResolution[πG] f}
    (h : Homotopy γ.hom' δ.hom')
    (p q : ℤ) (hpq : p + (-1) = q) :
    resolutionHomComplex[πG].X p → resolutionHomComplex[πF].X q :=
  fun z ↦ p.negOnePow • (Cochain.ofHomotopy h).comp z (precomp_homotopy_comp_eq hpq)

/-- Helper for Lemma 10.71.5: the precomposition component attached to a homotopy preserves
zero. -/
lemma precomp_homotopy_component_map_zero
    {πF : F ⟶ moduleSingle[M1]} {πG : G ⟶ moduleSingle[M2]}
    [IsFreeResolution πF] [IsFreeResolution πG]
    {f : ModuleCat.of R M1 ⟶ ModuleCat.of R M2}
    {γ δ : freeResolution[πF].Hom freeResolution[πG] f}
    (h : Homotopy γ.hom' δ.hom')
    (p q : ℤ) (hpq : p + (-1) = q) :
    precomp_homotopy_component (N := N) h p q hpq 0 = 0 := by
  -- The second cochain factor is zero, so the composition and its scalar multiple both vanish.
  have hcomp :
      (Cochain.ofHomotopy h).comp (0 : resolutionHomComplex[πG].X p)
        (precomp_homotopy_comp_eq hpq) = 0 := by
    exact Cochain.comp_zero (z₁ := Cochain.ofHomotopy h) (h := precomp_homotopy_comp_eq hpq)
  simpa [precomp_homotopy_component, hcomp]

/-- Helper for Lemma 10.71.5: the precomposition component attached to a homotopy is additive. -/
lemma precomp_homotopy_component_map_add
    {πF : F ⟶ moduleSingle[M1]} {πG : G ⟶ moduleSingle[M2]}
    [IsFreeResolution πF] [IsFreeResolution πG]
    {f : ModuleCat.of R M1 ⟶ ModuleCat.of R M2}
    {γ δ : freeResolution[πF].Hom freeResolution[πG] f}
    (h : Homotopy γ.hom' δ.hom')
    (p q : ℤ) (hpq : p + (-1) = q)
    (z₁ z₂ : resolutionHomComplex[πG].X p) :
    precomp_homotopy_component (N := N) h p q hpq (z₁ + z₂) =
      precomp_homotopy_component (N := N) h p q hpq z₁ +
        precomp_homotopy_component (N := N) h p q hpq z₂ := by
  -- Additivity comes directly from additivity of `Cochain.comp` in the second factor.
  have hcomp :
      (Cochain.ofHomotopy h).comp (z₁ + z₂) (precomp_homotopy_comp_eq hpq) =
        (Cochain.ofHomotopy h).comp z₁ (precomp_homotopy_comp_eq hpq) +
          (Cochain.ofHomotopy h).comp z₂ (precomp_homotopy_comp_eq hpq) := by
    exact Cochain.comp_add (z₁ := Cochain.ofHomotopy h) (z₂ := z₁) (z₂' := z₂)
      (h := precomp_homotopy_comp_eq hpq)
  rw [precomp_homotopy_component, hcomp, smul_add,
    precomp_homotopy_component, precomp_homotopy_component]
  rfl

/-- Helper for Lemma 10.71.5: the degree `-1` cochain on the outer Hom complex induced by a
homotopy between compatible lifts. -/
noncomputable def precomp_homotopy_cochain
    {πF : F ⟶ moduleSingle[M1]} {πG : G ⟶ moduleSingle[M2]}
    [IsFreeResolution πF] [IsFreeResolution πG]
    {f : ModuleCat.of R M1 ⟶ ModuleCat.of R M2}
    {γ δ : freeResolution[πF].Hom freeResolution[πG] f}
    (h : Homotopy γ.hom' δ.hom') :
    Cochain resolutionHomComplex[πG] resolutionHomComplex[πF] (-1) :=
  Cochain.mk (fun p q hpq ↦ AddCommGrpCat.ofHom
    { toFun := precomp_homotopy_component (N := N) h p q hpq
      map_zero' := precomp_homotopy_component_map_zero (N := N) h p q hpq
      map_add' := precomp_homotopy_component_map_add (N := N) h p q hpq })

noncomputable def homComplexMap
    {πF : F ⟶ moduleSingle[M1]} {πG : G ⟶ moduleSingle[M2]}
    [IsFreeResolution πF] [IsFreeResolution πG]
    {f : ModuleCat.of R M1 ⟶ ModuleCat.of R M2}
    (γ : freeResolution[πF].Hom freeResolution[πG] f) :
    resolutionHomComplex[πG] ⟶ resolutionHomComplex[πF] := by
  exact
    { f := fun j ↦ AddCommGrpCat.ofHom
        { toFun := fun z ↦ (Cochain.ofHom γ.hom').comp z (zero_add j)
          map_zero' := by simp
          map_add' := by simp [Cochain.comp_add] }
      comm' := fun j k hjk ↦ by
        ext z
        change δ j k ((Cochain.ofHom γ.hom').comp z (zero_add j)) =
          (Cochain.ofHom γ.hom').comp (δ j k z) (zero_add k)
        exact δ_ofHom_comp γ.hom' z k }

/-- Helper for Lemma 10.71.5: after one outer `δ` expansion, the explicit precomposition
homotopy cochain becomes the inner `δ` of the source homotopy composed with the fixed input
cochain. -/
lemma precomp_homotopy_delta_comp_component
    {πF : F ⟶ moduleSingle[M1]} {πG : G ⟶ moduleSingle[M2]}
    [IsFreeResolution πF] [IsFreeResolution πG]
    {f : ModuleCat.of R M1 ⟶ ModuleCat.of R M2}
    {γ₁ γ₂ : freeResolution[πF].Hom freeResolution[πG] f}
    (h : Homotopy γ₁.hom' γ₂.hom')
    (p : ℤ) (z : resolutionHomComplex[πG].X p) :
    δ (p - 1) p ((Cochain.ofHomotopy h).comp z (show (-1) + p = p - 1 by omega)) =
      (Cochain.ofHomotopy h).comp (δ p (p + 1) z) (show (-1) + (p + 1) = p by omega) +
        p.negOnePow • (δ (-1) 0 (Cochain.ofHomotopy h)).comp z (zero_add p) := by
  -- Freeze the composite cochain and apply the standard `δ_comp` identity at this degree.
  simpa using
    (δ_comp (z₁ := Cochain.ofHomotopy h) (z₂ := z)
      (h := show (-1) + p = p - 1 by omega)
      (m₁ := 0) (m₂ := p + 1) (m₁₂ := p)
      (h₁₂ := show p - 1 + 1 = p by omega)
      (h₁ := show (-1) + 1 = 0 by omega)
      (h₂ := show p + 1 = p + 1 by rfl))

/-- Helper for Lemma 10.71.5: after specializing `δ_comp`, the remaining sign algebra collapses
the two shifted terms to the degree-zero differential of the homotopy cochain. -/
lemma precomp_homotopy_delta_cancel
    {πF : F ⟶ moduleSingle[M1]} {πG : G ⟶ moduleSingle[M2]}
    [IsFreeResolution πF] [IsFreeResolution πG]
    {f : ModuleCat.of R M1 ⟶ ModuleCat.of R M2}
    {γ₁ γ₂ : freeResolution[πF].Hom freeResolution[πG] f}
    (h : Homotopy γ₁.hom' γ₂.hom')
    (p : ℤ) (z : resolutionHomComplex[πG].X p) :
    p.negOnePow • δ (p - 1) p ((Cochain.ofHomotopy h).comp z (show (-1) + p = p - 1 by omega)) +
      (p + 1).negOnePow • (Cochain.ofHomotopy h).comp (δ p (p + 1) z)
        (show (-1) + (p + 1) = p by omega) =
      (δ (-1) 0 (Cochain.ofHomotopy h)).comp z (zero_add p) := by
  -- After the structural `δ_comp` rewrite, only sign cancellation remains.
  rw [precomp_homotopy_delta_comp_component (N := N) h p z]
  simp only [smul_add, Int.negOnePow_succ, Units.neg_smul, smul_smul, Int.units_mul_self,
    one_smul]
  abel

/-- Helper for Lemma 10.71.5: after one outer `δ` expansion, the explicit precomposition
homotopy cochain becomes the inner `δ` of the source homotopy composed with the fixed input
cochain. -/
lemma precomp_homotopy_cochain_componentwise_delta_normalized
    {πF : F ⟶ moduleSingle[M1]} {πG : G ⟶ moduleSingle[M2]}
    [IsFreeResolution πF] [IsFreeResolution πG]
    {f : ModuleCat.of R M1 ⟶ ModuleCat.of R M2}
    {γ₁ γ₂ : freeResolution[πF].Hom freeResolution[πG] f}
    (h : Homotopy γ₁.hom' γ₂.hom')
    (p : ℤ) (z : resolutionHomComplex[πG].X p) :
    ((δ (-1) 0 (precomp_homotopy_cochain (N := N) h)).v p p (add_zero p)) z =
      (δ (-1) 0 (Cochain.ofHomotopy h)).comp z (zero_add p) := by
  -- Route correction: we first expand the outer degree-zero differential, then reduce the result
  -- to the fixed-degree sign-cancellation lemma proved from `Cochain.δ_comp`.
  rw [δ_v (-1) 0 (neg_add_cancel 1) (precomp_homotopy_cochain (N := N) h) p p (add_zero p)
    (p - 1) (p + 1) rfl rfl]
  -- Rewriting the outer differentials and the explicit homotopy component exposes the exact
  -- fixed-degree expression handled by `precomp_homotopy_delta_cancel`.
  simp only [AddCommGrpCat.hom_add_apply, AddCommGrpCat.comp_apply, resolutionHomComplex_d_apply,
    Int.negOnePow_zero, one_smul]
  have hleft :
      ((precomp_homotopy_cochain (N := N) h).v p (p - 1)
        (show p + (-1) = p - 1 by omega)) z =
        precomp_homotopy_component (N := N) h p (p - 1)
          (show p + (-1) = p - 1 by omega) z := rfl
  have hright :
      ((precomp_homotopy_cochain (N := N) h).v (p + 1) p
        (show (p + 1) + (-1) = p by omega)) (δ p (p + 1) z) =
        precomp_homotopy_component (N := N) h (p + 1) p
          (show (p + 1) + (-1) = p by omega) (δ p (p + 1) z) := rfl
  rw [hleft, hright]
  simp only [precomp_homotopy_component]
  have hsmul :
      δ (p - 1) p (p.negOnePow • (Cochain.ofHomotopy h).comp z (show (-1) + p = p - 1 by omega)) =
        p.negOnePow • δ (p - 1) p ((Cochain.ofHomotopy h).comp z (show (-1) + p = p - 1 by omega)) := by
    exact δ_units_smul (n := p - 1) (m := p) (k := p.negOnePow)
      ((Cochain.ofHomotopy h).comp z (show (-1) + p = p - 1 by omega))
  rw [hsmul]
  exact precomp_homotopy_delta_cancel (N := N) h p z

/-- Helper for Lemma 10.71.5: the fixed-degree outer differential of the explicit homotopy
cochain reduces to the difference of the two precomposition maps. -/
lemma precomp_homotopy_cochain_componentwise_delta
    {πF : F ⟶ moduleSingle[M1]} {πG : G ⟶ moduleSingle[M2]}
    [IsFreeResolution πF] [IsFreeResolution πG]
    {f : ModuleCat.of R M1 ⟶ ModuleCat.of R M2}
    {γ₁ γ₂ : freeResolution[πF].Hom freeResolution[πG] f}
    (h : Homotopy γ₁.hom' γ₂.hom')
    (p : ℤ) (z : resolutionHomComplex[πG].X p) :
    ((δ (-1) 0 (precomp_homotopy_cochain (N := N) h)).v p p (add_zero p)) z =
      ((Cochain.ofHom (homComplexMap (N := N) γ₁) -
          Cochain.ofHom (homComplexMap (N := N) γ₂)).v p p (add_zero p)) z := by
  -- Route correction: the previous global `δ` proof obscured the source argument.
  -- We first freeze the outer degree `p` and the input cochain `z`, then normalize by one
  -- outer `δ_v` expansion before applying the standard `δ_ofHomotopy` identity.
  rw [precomp_homotopy_cochain_componentwise_delta_normalized (N := N) h p z]
  -- The resulting inner degree-zero cochain is exactly the difference of the two
  -- precomposition maps induced by the homotopic lifts.
  simpa only [Cochain.sub_comp, Cochain.zero_cochain_comp_v, Cochain.ofHom_v, homComplexMap] using
    congrArg (fun t => t.comp z (zero_add p)) (δ_ofHomotopy h)

/-- Helper for Lemma 10.71.5: the differential of the outer precomposition cochain is the
difference of the two induced Hom-complex maps. -/
lemma precomp_homotopy_cochain_delta
    {πF : F ⟶ moduleSingle[M1]} {πG : G ⟶ moduleSingle[M2]}
    [IsFreeResolution πF] [IsFreeResolution πG]
    {f : ModuleCat.of R M1 ⟶ ModuleCat.of R M2}
    {γ₁ γ₂ : freeResolution[πF].Hom freeResolution[πG] f}
    (h : Homotopy γ₁.hom' γ₂.hom') :
    δ (-1) 0 (precomp_homotopy_cochain (N := N) h) =
      Cochain.ofHom (homComplexMap (N := N) γ₁) - Cochain.ofHom (homComplexMap (N := N) γ₂) := by
  -- Route correction: after freezing the outer degree in the helper above, this global equality
  -- is just extensionality in the outer cochain variable and in the input cochain.
  ext p z
  exact precomp_homotopy_cochain_componentwise_delta (N := N) h p z

/-- Helper for Lemma 10.71.5: the explicit precomposition cochain witness satisfies the equation
required by `Cochain.equivHomotopy`. -/
lemma precomp_homotopy_cochain_eq
    {πF : F ⟶ moduleSingle[M1]} {πG : G ⟶ moduleSingle[M2]}
    [IsFreeResolution πF] [IsFreeResolution πG]
    {f : ModuleCat.of R M1 ⟶ ModuleCat.of R M2}
    {γ₁ γ₂ : freeResolution[πF].Hom freeResolution[πG] f}
    (h : Homotopy γ₁.hom' γ₂.hom') :
    Cochain.ofHom (homComplexMap (N := N) γ₁) =
      δ (-1) 0 (precomp_homotopy_cochain (N := N) h) +
        Cochain.ofHom (homComplexMap (N := N) γ₂) := by
  rw [precomp_homotopy_cochain_delta (N := N) h]
  abel

/-- Helper for Lemma 10.71.5: a homotopy between compatible lifts induces a homotopy between the
precomposition maps on the `Hom_R(-, N)` cochain complexes. -/
noncomputable def homComplexMap_homotopy
    {πF : F ⟶ moduleSingle[M1]} {πG : G ⟶ moduleSingle[M2]}
    [IsFreeResolution πF] [IsFreeResolution πG]
    {f : ModuleCat.of R M1 ⟶ ModuleCat.of R M2}
    {γ₁ γ₂ : freeResolution[πF].Hom freeResolution[πG] f}
    (h : Homotopy γ₁.hom' γ₂.hom') :
    Homotopy
      (homComplexMap (N := N) γ₁ : resolutionHomComplex[πG] ⟶ resolutionHomComplex[πF])
      (homComplexMap (N := N) γ₂ : resolutionHomComplex[πG] ⟶ resolutionHomComplex[πF]) :=
  (Cochain.equivHomotopy _ _).symm
    ⟨precomp_homotopy_cochain (N := N) h, precomp_homotopy_cochain_eq (N := N) h⟩

/-- Helper for Lemma 10.71.5: the packaged identity lift acts by the identity on the Hom
complex. -/
lemma homComplexMap_id
    {πF : F ⟶ moduleSingle[M1]} [IsFreeResolution πF]
    (γ : freeResolution[πF].Hom freeResolution[πF] (𝟙 (ModuleCat.of R M1)))
    (hγ : γ.hom = 𝟙 _) :
    homComplexMap (N := N) γ = 𝟙 _ := by
  -- Rewrite the lift to the literal identity chain map and simplify precomposition.
  rcases γ with ⟨γhom, γcomm⟩
  dsimp at hγ
  subst γhom
  apply HomologicalComplex.hom_ext
  intro j
  ext z
  apply Cochain.ext
  intro r s hrs
  have hz :
      (Cochain.ofHom
          (HomologicalComplex.extendMap (𝟙 freeResolution[πF].complex)
            ComplexShape.embeddingDownNat)).comp z (zero_add j) = z := by
    simpa [HomologicalComplex.extendMap_id] using (Cochain.id_comp z :
      (Cochain.ofHom (𝟙 freeResolution[πF].cochainComplex)).comp z (zero_add j) = z)
  exact Cochain.congr_v hz r s hrs

/-- Helper for Lemma 10.71.5: precomposition on the Hom complex is contravariantly functorial in
the compatible lift. -/
lemma homComplexMap_comp
    {M3 : Type v} [AddCommGroup M3] [Module R M3]
    {H : ChainComplex (ModuleCat R) ℕ}
    {πF : F ⟶ moduleSingle[M1]} {πG : G ⟶ moduleSingle[M2]} {πH : H ⟶ moduleSingle[M3]}
    [IsFreeResolution πF] [IsFreeResolution πG] [IsFreeResolution πH]
    {f : ModuleCat.of R M1 ⟶ ModuleCat.of R M2}
    {g : ModuleCat.of R M2 ⟶ ModuleCat.of R M3}
    {h : ModuleCat.of R M1 ⟶ ModuleCat.of R M3}
    (γ₁ : freeResolution[πF].Hom freeResolution[πG] f)
    (γ₂ : freeResolution[πG].Hom freeResolution[πH] g)
    (γcomp : freeResolution[πF].Hom freeResolution[πH] h)
    (hγcomp : γcomp.hom = γ₁.hom ≫ γ₂.hom) :
    homComplexMap (N := N) γcomp =
      homComplexMap (N := N) γ₂ ≫ homComplexMap (N := N) γ₁ := by
  -- Route correction: the source proof composes lifts first and only then passes to `Hom`.
  -- Here we mirror that route and use the cochain-composition associativity once.
  rcases γcomp with ⟨γhom, γcomm⟩
  dsimp at hγcomp
  subst γhom
  apply HomologicalComplex.hom_ext
  intro j
  ext z
  apply Cochain.ext
  intro r s hrs
  have hOf :
      Cochain.ofHom
          (HomologicalComplex.extendMap (γ₁.hom ≫ γ₂.hom) ComplexShape.embeddingDownNat) =
        (Cochain.ofHom (HomologicalComplex.extendMap γ₁.hom ComplexShape.embeddingDownNat)).comp
          (Cochain.ofHom (HomologicalComplex.extendMap γ₂.hom ComplexShape.embeddingDownNat))
          (zero_add 0) := by
    simpa [HomologicalComplex.extendMap_comp] using
      (Cochain.ofHom_comp
        (HomologicalComplex.extendMap γ₁.hom ComplexShape.embeddingDownNat)
        (HomologicalComplex.extendMap γ₂.hom ComplexShape.embeddingDownNat))
  have hz :
      (Cochain.ofHom
          (HomologicalComplex.extendMap (γ₁.hom ≫ γ₂.hom) ComplexShape.embeddingDownNat)).comp z
          (zero_add j) =
        (Cochain.ofHom (HomologicalComplex.extendMap γ₁.hom ComplexShape.embeddingDownNat)).comp
          ((Cochain.ofHom (HomologicalComplex.extendMap γ₂.hom ComplexShape.embeddingDownNat)).comp z
            (zero_add j))
          (zero_add j) := by
    calc
      (Cochain.ofHom
          (HomologicalComplex.extendMap (γ₁.hom ≫ γ₂.hom) ComplexShape.embeddingDownNat)).comp z
          (zero_add j) =
        (((Cochain.ofHom (HomologicalComplex.extendMap γ₁.hom ComplexShape.embeddingDownNat)).comp
            (Cochain.ofHom (HomologicalComplex.extendMap γ₂.hom ComplexShape.embeddingDownNat))
            (zero_add 0))).comp z
            (zero_add j) := by rw [hOf]
      _ =
        (Cochain.ofHom (HomologicalComplex.extendMap γ₁.hom ComplexShape.embeddingDownNat)).comp
          ((Cochain.ofHom (HomologicalComplex.extendMap γ₂.hom ComplexShape.embeddingDownNat)).comp z
            (zero_add j))
          (zero_add j) := by
            simpa using Cochain.comp_assoc_of_first_is_zero_cochain
              (Cochain.ofHom (HomologicalComplex.extendMap γ₁.hom ComplexShape.embeddingDownNat))
              (Cochain.ofHom (HomologicalComplex.extendMap γ₂.hom ComplexShape.embeddingDownNat))
              z (zero_add j)
  exact Cochain.congr_v hz r s hrs

end ProjectiveResolution.Hom

open ProjectiveResolution.Hom

/-- Helper for Lemma 10.71.5: the literal identity chain map is compatible with the identity
augmentation in degree `0`. -/
lemma identity_hom_f_zero_comp_π_f_zero
    {πF : F ⟶ moduleSingle[M1]} [IsFreeResolution πF] :
    ((𝟙 freeResolution[πF].complex :
        freeResolution[πF].complex ⟶ freeResolution[πF].complex)).f 0 ≫
        freeResolution[πF].π.f 0 =
      freeResolution[πF].π.f 0 ≫
        ((ChainComplex.single₀ (ModuleCat R)).map (𝟙 (ModuleCat.of R M1))).f 0 := by
  -- The identity chain map and the identity augmentation commute definitionally in degree `0`.
  simpa using Category.comp_id (freeResolution[πF].π.f 0)

/-- Helper for Lemma 10.71.5: the literal identity chain map packages as a compatible identity
lift. -/
noncomputable def identity_lift
    {πF : F ⟶ moduleSingle[M1]} [IsFreeResolution πF] :
    freeResolution[πF].Hom freeResolution[πF] (𝟙 (ModuleCat.of R M1)) :=
  ⟨𝟙 freeResolution[πF].complex,
    identity_hom_f_zero_comp_π_f_zero (R := R) (M1 := M1) (πF := πF)⟩

/-- Helper for Lemma 10.71.5: casting the identity lift along an equality of module maps does not
change the induced map on the `Hom` complex. -/
lemma casted_identity_lift_homComplexMap_id
    {M : Type v} [AddCommGroup M] [Module R M]
    {K : ChainComplex (ModuleCat R) ℕ}
    {π : K ⟶ moduleSingle[M]} [IsFreeResolution π]
    {g : ModuleCat.of R M ⟶ ModuleCat.of R M}
    (e : g = 𝟙 (ModuleCat.of R M)) :
    homComplexMap (N := N)
        ((e.symm ▸ (identity_lift :
          freeResolution[π].Hom freeResolution[π] (𝟙 (ModuleCat.of R M)))) :
          freeResolution[π].Hom freeResolution[π] g) = 𝟙 _ := by
  -- After substituting the equality of module maps, we reduce to the literal identity lift.
  subst e
  simpa [identity_lift] using
    (ProjectiveResolution.Hom.homComplexMap_id (N := N)
      (γ := (identity_lift :
        freeResolution[π].Hom freeResolution[π] (𝟙 (ModuleCat.of R M)))) rfl)

/-- Helper for Lemma 10.71.5: projective-resolution lifts compose to a compatible lift of the
composite module map in degree `0`. -/
lemma comp_hom_f_zero_comp_π_f_zero
    {M3 : Type v} [AddCommGroup M3] [Module R M3]
    {H : ChainComplex (ModuleCat R) ℕ}
    {πF : F ⟶ moduleSingle[M1]} {πG : G ⟶ moduleSingle[M2]} {πH : H ⟶ moduleSingle[M3]}
    [IsFreeResolution πF] [IsFreeResolution πG] [IsFreeResolution πH]
    {f : ModuleCat.of R M1 ⟶ ModuleCat.of R M2}
    {g : ModuleCat.of R M2 ⟶ ModuleCat.of R M3}
    (γ₁ : freeResolution[πF].Hom freeResolution[πG] f)
    (γ₂ : freeResolution[πG].Hom freeResolution[πH] g) :
    (γ₁.hom ≫ γ₂.hom).f 0 ≫ freeResolution[πH].π.f 0 =
      freeResolution[πF].π.f 0 ≫
        ((ChainComplex.single₀ (ModuleCat R)).map (f ≫ g)).f 0 := by
  -- The degree-`0` compatibility of the composite follows by associativity and the two given
  -- degree-`0` compatibility relations.
  calc
    (γ₁.hom ≫ γ₂.hom).f 0 ≫ freeResolution[πH].π.f 0 =
      γ₁.hom.f 0 ≫ (γ₂.hom.f 0 ≫ freeResolution[πH].π.f 0) := by simp [Category.assoc]
    _ = γ₁.hom.f 0 ≫
        (freeResolution[πG].π.f 0 ≫ ((ChainComplex.single₀ (ModuleCat R)).map g).f 0) := by
          rw [γ₂.hom_f_zero_comp_π_f_zero]
    _ = (γ₁.hom.f 0 ≫ freeResolution[πG].π.f 0) ≫
        ((ChainComplex.single₀ (ModuleCat R)).map g).f 0 := by simp [Category.assoc]
    _ = (freeResolution[πF].π.f 0 ≫ ((ChainComplex.single₀ (ModuleCat R)).map f).f 0) ≫
        ((ChainComplex.single₀ (ModuleCat R)).map g).f 0 := by
          rw [γ₁.hom_f_zero_comp_π_f_zero]
    _ = freeResolution[πF].π.f 0 ≫
        (((ChainComplex.single₀ (ModuleCat R)).map f).f 0 ≫
          ((ChainComplex.single₀ (ModuleCat R)).map g).f 0) := by simp [Category.assoc]
    _ = freeResolution[πF].π.f 0 ≫
        ((ChainComplex.single₀ (ModuleCat R)).map (f ≫ g)).f 0 := by
          simp

/-- Helper for Lemma 10.71.5: compatible lifts admit a compatible composite lift. -/
noncomputable def comp_lift
    {M3 : Type v} [AddCommGroup M3] [Module R M3]
    {H : ChainComplex (ModuleCat R) ℕ}
    {πF : F ⟶ moduleSingle[M1]} {πG : G ⟶ moduleSingle[M2]} {πH : H ⟶ moduleSingle[M3]}
    [IsFreeResolution πF] [IsFreeResolution πG] [IsFreeResolution πH]
    {f : ModuleCat.of R M1 ⟶ ModuleCat.of R M2}
    {g : ModuleCat.of R M2 ⟶ ModuleCat.of R M3}
    (γ₁ : freeResolution[πF].Hom freeResolution[πG] f)
    (γ₂ : freeResolution[πG].Hom freeResolution[πH] g) :
    freeResolution[πF].Hom freeResolution[πH] (f ≫ g) :=
  ⟨γ₁.hom ≫ γ₂.hom, comp_hom_f_zero_comp_π_f_zero (R := R) γ₁ γ₂⟩

/-- Helper for Lemma 10.71.5: the inverse of an isomorphism admits a compatible lift between the
chosen free resolutions. -/
noncomputable def inverse_lift
    (f : ModuleCat.of R M1 ⟶ ModuleCat.of R M2) [IsIso f]
    (πF : F ⟶ moduleSingle[M1]) (πG : G ⟶ moduleSingle[M2])
    [IsFreeResolution πF] [IsFreeResolution πG] :
    freeResolution[πG].Hom freeResolution[πF] (inv f) :=
  ⟨ProjectiveResolution.lift (inv f) freeResolution[πG] freeResolution[πF],
    ProjectiveResolution.lift_commutes_zero (inv f) freeResolution[πG] freeResolution[πF]⟩

/-- Lemma 10.71.5: any two compatible lifts of a module map between free resolutions induce the
same map on the cohomology of the contravariant `Hom_R(-, N)` complex. -/
-- Proof sketch: the two compatible lifts are morphisms of the associated projective resolutions,
-- hence `ProjectiveResolution.liftHomotopy` gives a homotopy between their induced cochain maps
-- `α.hom'` and `β.hom'`. Precomposition with these morphisms defines the canonical maps on the
-- `CochainComplex.HomComplex` computing `Hom_R(-, N)` cohomology, and `Homotopy.homologyMap_eq`
-- identifies the induced cohomology maps.
@[stacks 00LT]
theorem resolution_homologyMap_eq_of_compatible_lifts
    (f : ModuleCat.of R M1 ⟶ ModuleCat.of R M2)
    (πF : F ⟶ moduleSingle[M1]) (πG : G ⟶ moduleSingle[M2])
    [IsFreeResolution πF] [IsFreeResolution πG]
    (α β : freeResolution[πF].Hom freeResolution[πG] f)
    (i : ℤ) :
    homologyMap (homComplexMap β : resolutionHomComplex[πG] ⟶
      resolutionHomComplex[πF]) i =
      homologyMap (homComplexMap α : resolutionHomComplex[πG] ⟶
        resolutionHomComplex[πF]) i :=
      by
  -- Follow the source proof: compatible lifts are homotopic on the resolution side.
  let hChain :
      Homotopy (α.hom : F ⟶ G) (β.hom : F ⟶ G) :=
    ProjectiveResolution.liftHomotopy f α.hom β.hom α.hom_comp_π β.hom_comp_π
  let hCochain :
      Homotopy α.hom' β.hom' :=
    hChain.extend ComplexShape.embeddingDownNat
  -- Precomposition by homotopic maps gives homotopic maps on the `Hom` cochain complexes.
  exact (ProjectiveResolution.Hom.homComplexMap_homotopy (N := N) hCochain).homologyMap_eq i |>.symm

/-- Compatible lifts of an isomorphism induce isomorphisms on all `Hom_R(-, N)` cohomology
groups. -/
-- Proof sketch: choose a compatible lift of the inverse using the projective-resolution lifting
-- API. The two composites are compatible lifts of the identity, so the previous theorem shows
-- that the induced cohomology maps are inverse to one another.
theorem resolution_homologyMap_isIso_of_isIso
    (f : ModuleCat.of R M1 ⟶ ModuleCat.of R M2) [IsIso f]
    (πF : F ⟶ moduleSingle[M1]) (πG : G ⟶ moduleSingle[M2])
    [IsFreeResolution πF] [IsFreeResolution πG]
    (α : freeResolution[πF].Hom freeResolution[πG] f)
    (i : ℤ) :
    IsIso
      (homologyMap (homComplexMap α : resolutionHomComplex[πG] ⟶
        resolutionHomComplex[πF]) i) := by
  let β : freeResolution[πG].Hom freeResolution[πF] (inv f) :=
    inverse_lift (R := R) (M1 := M1) (M2 := M2) f πF πG
  let eF : f ≫ inv f = 𝟙 (ModuleCat.of R M1) := IsIso.hom_inv_id f
  let eG : inv f ≫ f = 𝟙 (ModuleCat.of R M2) := IsIso.inv_hom_id f
  let idLiftF : freeResolution[πF].Hom freeResolution[πF] (f ≫ inv f) :=
    eF.symm ▸ (identity_lift :
      freeResolution[πF].Hom freeResolution[πF] (𝟙 (ModuleCat.of R M1)))
  let idLiftG : freeResolution[πG].Hom freeResolution[πG] (inv f ≫ f) :=
    eG.symm ▸ (identity_lift :
      freeResolution[πG].Hom freeResolution[πG] (𝟙 (ModuleCat.of R M2)))
  have hcompF :
      homologyMap (homComplexMap (N := N) (comp_lift (R := R) α β) :
        resolutionHomComplex[πF] ⟶ resolutionHomComplex[πF]) i =
        homologyMap (homComplexMap (N := N) β) i ≫
          homologyMap (homComplexMap (N := N) α) i := by
    -- The contravariant Hom-complex map turns the composite lift into the reversed composite.
    rw [ProjectiveResolution.Hom.homComplexMap_comp (N := N) α β
      (comp_lift (R := R) α β) rfl, HomologicalComplex.homologyMap_comp]
  have hcompG :
      homologyMap (homComplexMap (N := N) (comp_lift (R := R) β α) :
        resolutionHomComplex[πG] ⟶ resolutionHomComplex[πG]) i =
        homologyMap (homComplexMap (N := N) α) i ≫
          homologyMap (homComplexMap (N := N) β) i := by
    -- The same functoriality computation for the opposite composite lift gives the other side.
    rw [ProjectiveResolution.Hom.homComplexMap_comp (N := N) β α
      (comp_lift (R := R) β α) rfl, HomologicalComplex.homologyMap_comp]
  have hidF :
      homologyMap (homComplexMap (N := N) idLiftF :
        resolutionHomComplex[πF] ⟶ resolutionHomComplex[πF]) i = 𝟙 _ := by
    -- Casting the identity lift along `f ≫ inv f = 𝟙` does not change the induced Hom-complex
    -- map, so the resulting homology map is the identity.
    have hmap :
        homComplexMap (N := N) idLiftF = 𝟙 (resolutionHomComplex[πF]) := by
      simpa [idLiftF] using
        (casted_identity_lift_homComplexMap_id (N := N)
          (π := πF) (g := f ≫ inv f) eF)
    simpa [hmap] using
      (HomologicalComplex.homologyMap_id (K := resolutionHomComplex[πF]) (i := i))
  have hidG :
      homologyMap (homComplexMap (N := N) idLiftG :
        resolutionHomComplex[πG] ⟶ resolutionHomComplex[πG]) i = 𝟙 _ := by
    -- The inverse composite is handled in the same way on the `G`-resolution.
    have hmap :
        homComplexMap (N := N) idLiftG = 𝟙 (resolutionHomComplex[πG]) := by
      simpa [idLiftG] using
        (casted_identity_lift_homComplexMap_id (N := N)
          (π := πG) (g := inv f ≫ f) eG)
    simpa [hmap] using
      (HomologicalComplex.homologyMap_id (K := resolutionHomComplex[πG]) (i := i))
  have hinv_hom_id :
      homologyMap (homComplexMap (N := N) β) i ≫
        homologyMap (homComplexMap (N := N) α) i = 𝟙 _ := by
    have hEqF :
        homologyMap (homComplexMap (N := N) (comp_lift (R := R) α β) :
          resolutionHomComplex[πF] ⟶ resolutionHomComplex[πF]) i =
          homologyMap (homComplexMap (N := N) idLiftF :
            resolutionHomComplex[πF] ⟶ resolutionHomComplex[πF]) i := by
      -- The two compatible lifts of `f ≫ inv f` induce the same homology map.
      exact (resolution_homologyMap_eq_of_compatible_lifts (N := N) (f ≫ inv f) πF πF
        (comp_lift (R := R) α β) idLiftF i).symm
    -- Compare the composite lift with the casted identity lift of `M₁`.
    calc
      homologyMap (homComplexMap (N := N) β) i ≫
          homologyMap (homComplexMap (N := N) α) i =
        homologyMap (homComplexMap (N := N) (comp_lift (R := R) α β) :
          resolutionHomComplex[πF] ⟶ resolutionHomComplex[πF]) i := by
            exact hcompF.symm
      _ = homologyMap (homComplexMap (N := N) idLiftF :
          resolutionHomComplex[πF] ⟶ resolutionHomComplex[πF]) i := hEqF
      _ = 𝟙 _ := hidF
  have hhom_inv_id :
      homologyMap (homComplexMap (N := N) α) i ≫
        homologyMap (homComplexMap (N := N) β) i = 𝟙 _ := by
    have hEqG :
        homologyMap (homComplexMap (N := N) (comp_lift (R := R) β α) :
          resolutionHomComplex[πG] ⟶ resolutionHomComplex[πG]) i =
          homologyMap (homComplexMap (N := N) idLiftG :
            resolutionHomComplex[πG] ⟶ resolutionHomComplex[πG]) i := by
      -- The two compatible lifts of `inv f ≫ f` induce the same homology map.
      exact (resolution_homologyMap_eq_of_compatible_lifts (N := N) (inv f ≫ f) πG πG
        (comp_lift (R := R) β α) idLiftG i).symm
    -- Compare the other composite lift with the casted identity lift of `M₂`.
    calc
      homologyMap (homComplexMap (N := N) α) i ≫
          homologyMap (homComplexMap (N := N) β) i =
        homologyMap (homComplexMap (N := N) (comp_lift (R := R) β α) :
          resolutionHomComplex[πG] ⟶ resolutionHomComplex[πG]) i := by
            exact hcompG.symm
      _ = homologyMap (homComplexMap (N := N) idLiftG :
          resolutionHomComplex[πG] ⟶ resolutionHomComplex[πG]) i := hEqG
      _ = 𝟙 _ := hidG
  let invMap :=
    homologyMap (homComplexMap (N := N) β :
      resolutionHomComplex[πF] ⟶ resolutionHomComplex[πG]) i
  exact ⟨⟨invMap, hhom_inv_id, hinv_hom_id⟩⟩

/-- An endomorphism lift of the identity induces the identity on the cohomology of
`Hom_R(-, N)`. -/
-- Proof sketch: apply the compatibility-independence statement to the given identity lift and the
-- identity morphism of the free resolution.
theorem resolution_homologyMap_eq_id_of_identity_lift
    (πF : F ⟶ moduleSingle[M1]) [IsFreeResolution πF]
    (α : freeResolution[πF].Hom freeResolution[πF] (𝟙 (ModuleCat.of R M1)))
    (i : ℤ) :
    homologyMap (homComplexMap α : resolutionHomComplex[πF] ⟶
      resolutionHomComplex[πF]) i = 𝟙 _ := by
  -- Compare the given compatible identity lift with the literal identity lift of the same
  -- augmentation map, then rewrite the latter side to the identity.
  let β : freeResolution[πF].Hom freeResolution[πF] (𝟙 (ModuleCat.of R M1)) :=
    identity_lift
  calc
    homologyMap (homComplexMap α : resolutionHomComplex[πF] ⟶
        resolutionHomComplex[πF]) i =
      homologyMap (homComplexMap β : resolutionHomComplex[πF] ⟶
        resolutionHomComplex[πF]) i := by
          simpa [β] using
            (resolution_homologyMap_eq_of_compatible_lifts (N := N)
              (𝟙 (ModuleCat.of R M1)) πF πF α β i).symm
    _ = 𝟙 _ := by
          have hβ :
              homComplexMap (N := N) β = 𝟙 _ := by
            simpa [β, identity_lift] using
              (ProjectiveResolution.Hom.homComplexMap_id (N := N) β rfl)
          simpa [hβ] using
            (HomologicalComplex.homologyMap_id
              (K := resolutionHomComplex[πF]) (i := i))

end
