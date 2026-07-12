import StacksProject_2024.Chap10.Lemma_10_134_12.TensorModel
open Algebra
open Algebra.Extension
open Algebra.Generators
open CategoryTheory
open CategoryTheory.Limits
open scoped NaiveCotangent TensorProduct

universe u v

noncomputable section

section

variable (A : Type u) (B : Type v) (Bg : Type v)
variable [CommRing A] [CommRing B] [CommRing Bg]
variable [Algebra A B] [Algebra A Bg] [Algebra B Bg]
variable [IsScalarTower A B Bg]
variable (g : B) [IsLocalization.Away g Bg]

attribute [local instance] SMulCommClass.of_commMonoid
attribute [local instance] TensorProduct.rightAlgebra

/-- Helper for Lemma 10.134.12: if the cotangent homology and Kähler differentials vanish, then
the cotangent-complex map is a linear equivalence. -/
noncomputable def cotangentComplexEquiv_of_subsingleton_h1_and_kaehler
    {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] [Algebra R S]
    (P : Extension R S)
    [Subsingleton P.H1Cotangent] [Subsingleton Ω[S⁄R]] :
    P.Cotangent ≃ₗ[S] P.CotangentSpace :=
  -- This is the same bijectivity argument used in Lemma 10.134.10 for localization.
  LinearEquiv.ofBijective P.cotangentComplex <| by
    refine ⟨(Extension.subsingleton_h1Cotangent P).mp inferInstance, ?_⟩
    intro x
    have hx : x ∈ LinearMap.ker P.toKaehler := by
      change P.toKaehler x = 0
      exact Subsingleton.elim _ _
    have hexact := (LinearMap.exact_iff).mp P.exact_cotangentComplex_toKaehler
    rw [hexact] at hx
    exact hx

/-- Helper for Lemma 10.134.12: if the right summand of a biproduct of chain complexes is
contractible, then the left inclusion is a homotopy equivalence. -/
noncomputable def biprod_inl_homotopyEquiv_of_right_contractible
    (X Y : ChainComplex (ModuleCat Bg) ℕ)
    (hY : Homotopy (𝟙 Y) 0) :
    HomotopyEquiv X (X ⊞ Y) := by
  refine
    { hom := biprod.inl
      inv := biprod.fst
      homotopyHomInvId := by
        -- The source composite is literally the identity on the left summand.
        exact Homotopy.ofEq (by simp)
      homotopyInvHomId := by
        -- Split the identity on the biproduct and kill the right summand with the contraction.
        let hRight :
            Homotopy (biprod.snd ≫ biprod.inr : X ⊞ Y ⟶ X ⊞ Y) 0 :=
          by
            simpa using
              (hY.compRight (biprod.inr : Y ⟶ X ⊞ Y)).compLeft (biprod.snd : X ⊞ Y ⟶ Y)
        let hSum :
            Homotopy
              ((biprod.fst : X ⊞ Y ⟶ X) ≫ (biprod.inl : X ⟶ X ⊞ Y) +
                (biprod.snd : X ⊞ Y ⟶ Y) ≫ (biprod.inr : Y ⟶ X ⊞ Y))
              ((biprod.fst : X ⊞ Y ⟶ X) ≫ (biprod.inl : X ⟶ X ⊞ Y) + 0) :=
          Homotopy.add (Homotopy.refl _) hRight
        have hId :
            (𝟙 (X ⊞ Y) : X ⊞ Y ⟶ X ⊞ Y) =
              (biprod.fst : X ⊞ Y ⟶ X) ≫ (biprod.inl : X ⟶ X ⊞ Y) +
                (biprod.snd : X ⊞ Y ⟶ Y) ≫ (biprod.inr : Y ⟶ X ⊞ Y) := by
          apply biprod.hom_ext
          · simp
          · simp
        have hLeft :
            ((biprod.fst : X ⊞ Y ⟶ X) ≫ (biprod.inl : X ⟶ X ⊞ Y) + 0) =
              (biprod.fst : X ⊞ Y ⟶ X) ≫ (biprod.inl : X ⟶ X ⊞ Y) := by
          simp
        exact ((Homotopy.ofEq hId).trans (hSum.trans (Homotopy.ofEq hLeft))).symm }

/-- Helper for Lemma 10.134.12: the explicit `ModuleCat` product comparison sends the biproduct
to the first projection. -/
theorem biprodIsoProd_hom_comp_fst (M N : ModuleCat Bg) :
    (ModuleCat.biprodIsoProd M N).hom ≫ ModuleCat.ofHom (LinearMap.fst Bg M N) = biprod.fst := by
  -- Compare the canonical biproduct and product cones on the left projection.
  simpa [ModuleCat.binaryProductLimitCone_cone_π_app_left] using
    IsLimit.conePointUniqueUpToIso_hom_comp
      (BinaryBiproduct.isLimit M N) (ModuleCat.binaryProductLimitCone M N).isLimit
      (Discrete.mk WalkingPair.left)

/-- Helper for Lemma 10.134.12: the explicit `ModuleCat` product comparison sends the biproduct
to the second projection. -/
theorem biprodIsoProd_hom_comp_snd (M N : ModuleCat Bg) :
    (ModuleCat.biprodIsoProd M N).hom ≫ ModuleCat.ofHom (LinearMap.snd Bg M N) = biprod.snd := by
  -- Compare the same two cones on the right projection.
  simpa [ModuleCat.binaryProductLimitCone_cone_π_app_right] using
    IsLimit.conePointUniqueUpToIso_hom_comp
      (BinaryBiproduct.isLimit M N) (ModuleCat.binaryProductLimitCone M N).isLimit
      (Discrete.mk WalkingPair.right)

/-- Helper for Lemma 10.134.12: under `ModuleCat.biprodIsoProd`, the left summand is the usual
product inclusion into the first factor. -/
theorem biprodIsoProd_inl_hom (M N : ModuleCat Bg) :
    biprod.inl ≫ (ModuleCat.biprodIsoProd M N).hom =
      ModuleCat.ofHom (LinearMap.inl Bg M N) := by
  -- Check the two explicit product projections separately.
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Prod.ext
  · change ((biprod.inl ≫ (ModuleCat.biprodIsoProd M N).hom ≫
        ModuleCat.ofHom (LinearMap.fst Bg M N)).hom x) = x
    simp [biprodIsoProd_hom_comp_fst]
  · change ((biprod.inl ≫ (ModuleCat.biprodIsoProd M N).hom ≫
        ModuleCat.ofHom (LinearMap.snd Bg M N)).hom x) = 0
    simp [biprodIsoProd_hom_comp_snd]

/-- Helper for Lemma 10.134.12: under `ModuleCat.biprodIsoProd`, the right summand is the usual
product inclusion into the second factor. -/
theorem biprodIsoProd_inr_hom (M N : ModuleCat Bg) :
    biprod.inr ≫ (ModuleCat.biprodIsoProd M N).hom =
      ModuleCat.ofHom (LinearMap.inr Bg M N) := by
  -- Again compare after the two explicit product projections.
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro y
  apply Prod.ext
  · change ((biprod.inr ≫ (ModuleCat.biprodIsoProd M N).hom ≫
        ModuleCat.ofHom (LinearMap.fst Bg M N)).hom y) = 0
    simp [biprodIsoProd_hom_comp_fst]
  · change ((biprod.inr ≫ (ModuleCat.biprodIsoProd M N).hom ≫
        ModuleCat.ofHom (LinearMap.snd Bg M N)).hom y) = y
    simp [biprodIsoProd_hom_comp_snd]

/-- Helper for Lemma 10.134.12: the pointwise form of `biprodIsoProd_inl_hom`. -/
theorem biprodIsoProd_hom_inl_apply (M N : ModuleCat Bg) (x : M) :
    ((ModuleCat.biprodIsoProd M N).hom.hom) ((biprod.inl : M ⟶ M ⊞ N).hom x) = (x, 0) := by
  -- Evaluate the left-inclusion morphism equality on an element of the left summand.
  simpa using congrArg
    (fun k : M ⟶ ModuleCat.of Bg (M × N) ↦ k.hom x)
    (biprodIsoProd_inl_hom (Bg := Bg) M N)

/-- Helper for Lemma 10.134.12: the pointwise form of `biprodIsoProd_inr_hom`. -/
theorem biprodIsoProd_hom_inr_apply (M N : ModuleCat Bg) (y : N) :
    ((ModuleCat.biprodIsoProd M N).hom.hom) ((biprod.inr : N ⟶ M ⊞ N).hom y) = (0, y) := by
  -- Evaluate the right-inclusion morphism equality on an element of the right summand.
  simpa using congrArg
    (fun k : N ⟶ ModuleCat.of Bg (M × N) ↦ k.hom y)
    (biprodIsoProd_inr_hom (Bg := Bg) M N)

/-- Helper for Lemma 10.134.12: in the localization-away presentation over `B`, the distinguished
cotangent class maps to `g` times the standard cotangent-space basis vector. -/
theorem localizationAway_cotangentComplex_cMulXSubOne :
    ((Generators.localizationAway Bg g).toExtension.cotangentComplex)
        (Generators.cMulXSubOneCotangent Bg g) =
      g • (Generators.localizationAway Bg g).cotangentSpaceBasis () := by
  let Q := Generators.localizationAway Bg g
  let y := Q.toExtension.cotangentComplex (Generators.cMulXSubOneCotangent Bg g)
  have hcoeff : Q.cotangentSpaceBasis.repr y () = algebraMap B Bg g := by
    -- The unique basis coordinate is the derivative of `g * X - 1`, namely `g`.
    have hrepr :=
      Q.cotangentSpaceBasis_repr_one_tmul
        (x := MvPolynomial.C g * MvPolynomial.X () - 1) (i := ())
    have hderiv :
        (MvPolynomial.aeval Q.val)
            (MvPolynomial.pderiv () (MvPolynomial.C g * MvPolynomial.X () - 1)) =
          algebraMap B Bg g := by
      simp
    simpa [Q, y, Generators.cMulXSubOneCotangent_eq, Algebra.Extension.cotangentComplex_mk] using
      hrepr.trans hderiv
  -- Expand the cotangent-space element in the canonical rank-one basis.
  calc
    y = ∑ i, Q.cotangentSpaceBasis.repr y i • Q.cotangentSpaceBasis i := by
      symm
      exact Q.cotangentSpaceBasis.sum_repr y
    _ = g • Q.cotangentSpaceBasis () := by
      simp [hcoeff]

/-- Helper for Lemma 10.134.12: under the Jacobi-Zariski cotangent-space splitting, the
base-changed `toComp` map is exactly the right summand inclusion. -/
theorem localized_self_compEquiv_apply_map_toComp
    (x : Bg ⊗[B] (selfExtension A B).CotangentSpace) :
    CotangentSpace.compEquiv
        (Generators.localizationAway Bg g)
        (Generators.self A B)
        (((Extension.CotangentSpace.map
            ((Generators.localizationAway Bg g).toComp
              (Generators.self A B)).toExtensionHom).liftBaseChange Bg) x) =
      (0, x) := by
  -- Apply the inverse description of the right summand and use injectivity of the Jacobi-Zariski
  -- splitting.
  apply (CotangentSpace.compEquiv
    (Generators.localizationAway Bg g) (Generators.self A B)).symm.injective
  simp [CotangentSpace.compEquiv_symm_zero]

/-- Helper for Lemma 10.134.12: the `ofComp` projection of the localized self differential
recovers the localization-away differential of the distinguished extra generator. -/
theorem localized_self_extra_generator_cotangent_space_fst
    (x : (localizedSelfGenerators A B Bg g).toExtension.Cotangent)
    (hx : Extension.Cotangent.map
      ((Generators.localizationAway Bg g).ofComp (Generators.self A B)).toExtensionHom x =
        Generators.cMulXSubOneCotangent Bg g) :
    (CotangentSpace.compEquiv
        (Generators.localizationAway Bg g)
        (Generators.self A B)
        ((localizedSelfGenerators A B Bg g).toExtension.cotangentComplex x)).1 =
      ((Generators.localizationAway Bg g).toExtension.cotangentComplex)
        (Generators.cMulXSubOneCotangent Bg g) := by
  -- The left projection in the Jacobi-Zariski splitting is the `ofComp` cotangent-space map,
  -- and `hx` identifies the resulting cotangent class.
  rw [CotangentSpace.fst_compEquiv_apply]
  rw [Extension.CotangentSpace.map_cotangentComplex]
  simpa [hx]

/-- Helper for Lemma 10.134.12: the tensor summand of the degree-`1` localization splitting maps
purely to the tensor summand in degree `0`. -/
theorem localized_self_tensor_component_cotangent_space_split
    (x : (localizedSelfGenerators A B Bg g).toExtension.Cotangent)
    (hx : Extension.Cotangent.map
      ((Generators.localizationAway Bg g).ofComp (Generators.self A B)).toExtensionHom x =
        Generators.cMulXSubOneCotangent Bg g)
    (a : Bg ⊗[B] (selfExtension A B).Cotangent) :
    CotangentSpace.compEquiv
        (Generators.localizationAway Bg g)
        (Generators.self A B)
        ((localizedSelfGenerators A B Bg g).toExtension.cotangentComplex
          (((Generators.self A B).cotangentCompLocalizationAwayEquiv (T := Bg) g hx).symm
            (a, 0))) =
      (0, LinearMap.baseChange Bg (selfExtension A B).cotangentComplex a) := by
  -- Rewrite the chosen tensor lift in degree `1` by the explicit `symm_inl` formula.
  rw [Generators.cotangentCompLocalizationAwayEquiv_symm_inl
    (g := g) (P := Generators.self A B) (x := x) (hx := hx)]
  -- Compute its image under the localized self differential.
  rw [tensorToLocalizedSelfPresentation_cotangentComplex_apply]
  -- The degree-`0` splitting sends this base-changed tensor term to the right summand.
  simpa using localized_self_compEquiv_apply_map_toComp A B Bg g
    (LinearMap.baseChange Bg (selfExtension A B).cotangentComplex a)

/-- Helper for Lemma 10.134.12: the canonical extra localization relation belongs to the kernel
of the localized self-presentation. -/
theorem localized_self_extra_relation_mem_ker :
    MvPolynomial.rename Sum.inr ((Generators.self A B).σ g) * MvPolynomial.X (Sum.inl ()) - 1 ∈
      (localizedSelfGenerators A B Bg g).ker := by
  let P := Generators.self A B
  let Q := Generators.localizationAway Bg g
  -- The localization-away kernel description identifies the extra relation as a generator of the
  -- second summand in the composed kernel.
  rw [show (localizedSelfGenerators A B Bg g).ker =
      Ideal.map (Q.toComp P).toAlgHom P.ker ⊔
        Ideal.span {MvPolynomial.rename Sum.inr (P.σ g) * MvPolynomial.X (Sum.inl ()) - 1} by
      simpa [localizedSelfGenerators] using
        Algebra.Generators.comp_localizationAway_ker
          (T := Bg) (P := P) (g := g) (f := P.σ g) (by simp)]
  exact
    (show Ideal.span {MvPolynomial.rename Sum.inr (P.σ g) * MvPolynomial.X (Sum.inl ()) - 1} ≤
        Ideal.map (Q.toComp P).toAlgHom P.ker ⊔
          Ideal.span {MvPolynomial.rename Sum.inr (P.σ g) * MvPolynomial.X (Sum.inl ()) - 1} from
      le_sup_right)
      (Ideal.subset_span (by simp [P, Generators.self]))

/-- Helper for Lemma 10.134.12: the canonical cotangent class of the extra localization relation
in the localized self-presentation. -/
noncomputable def localized_self_extra_generator :
    (localizedSelfGenerators A B Bg g).toExtension.Cotangent :=
  Extension.Cotangent.mk
    ⟨MvPolynomial.rename Sum.inr ((Generators.self A B).σ g) * MvPolynomial.X (Sum.inl ()) - 1,
      localized_self_extra_relation_mem_ker A B Bg g⟩

/-- Helper for Lemma 10.134.12: the `ofComp` map sends the canonical extra relation of the
localized self-presentation to the standard generator `gX - 1` of the localization-away
conormal module. -/
theorem localized_self_extra_generator_maps_to_cMulXSubOne :
    Extension.Cotangent.map
        ((Generators.localizationAway Bg g).ofComp (Generators.self A B)).toExtensionHom
        (localized_self_extra_generator A B Bg g) =
      Generators.cMulXSubOneCotangent Bg g := by
  -- This is the source proof's distinguished generator `fx - 1` rewritten through `ofComp`.
  simp_rw [localized_self_extra_generator, Extension.Cotangent.map_mk,
    Generators.Hom.toExtensionHom_toAlgHom_apply, Generators.cMulXSubOneCotangent_eq]
  congr 2
  convert
    (Algebra.Generators.toAlgHom_ofComp_localizationAway
      (P := Generators.self A B) (T := Bg) g) using 1

/-- Helper for Lemma 10.134.12: the degree-`0` shear records the tensor correction coming from
the canonical extra localization relation. -/
noncomputable def localized_self_degree0_shear :
    (Generators.localizationAway Bg g).toExtension.CotangentSpace →ₗ[Bg]
      Bg ⊗[B] (selfExtension A B).CotangentSpace :=
  let P := Generators.self A B
  let Q := Generators.localizationAway Bg g
  let C := localizedSelfGenerators A B Bg g
  let t :=
    (CotangentSpace.compEquiv Q P
      (C.toExtension.cotangentComplex (localized_self_extra_generator A B Bg g))).2
  (Generators.localizationAway Bg g).cotangentSpaceBasis.constr Bg
    (fun _ ↦ (IsLocalization.Away.invSelf (S := Bg) g : Bg) • t)

/-- Helper for Lemma 10.134.12: the degree-`0` shear sends the localization differential of
`gX - 1` to the tensor correction term of the canonical extra relation. -/
theorem localized_self_degree0_shear_cotangentComplex_cMulXSubOne :
    localized_self_degree0_shear A B Bg g
      (((Generators.localizationAway Bg g).toExtension.cotangentComplex)
        (Generators.cMulXSubOneCotangent Bg g)) =
      (CotangentSpace.compEquiv
          (Generators.localizationAway Bg g)
          (Generators.self A B)
          ((localizedSelfGenerators A B Bg g).toExtension.cotangentComplex
            (localized_self_extra_generator A B Bg g))).2 := by
  let P := Generators.self A B
  let Q := Generators.localizationAway Bg g
  let C := localizedSelfGenerators A B Bg g
  let t :=
    (CotangentSpace.compEquiv Q P
      (C.toExtension.cotangentComplex (localized_self_extra_generator A B Bg g))).2
  -- Evaluate the rank-one `Q`-basis construction on the distinguished generator `gX - 1`.
  rw [localized_self_degree0_shear, localizationAway_cotangentComplex_cMulXSubOne]
  change
    ((Q.cotangentSpaceBasis.constr Bg
        fun _ ↦ (IsLocalization.Away.invSelf (S := Bg) g : Bg) • t)
      (g • Q.cotangentSpaceBasis ())) = t
  rw [show g • Q.cotangentSpaceBasis () = (algebraMap B Bg g) • Q.cotangentSpaceBasis () by
    simpa [Algebra.smul_def]]
  rw [map_smul, Module.Basis.constr_basis]
  -- The only remaining input is the localization identity `g * g⁻¹ = 1`.
  calc
    algebraMap B Bg g • ((IsLocalization.Away.invSelf (S := Bg) g : Bg) • t) =
        (algebraMap B Bg g * IsLocalization.Away.invSelf (S := Bg) g) • t := by
          simp [smul_smul]
    _ = t := by
          simpa using congrArg (fun s : Bg ↦ s • t)
            (IsLocalization.Away.mul_invSelf (S := Bg) g)

/-- Helper for Lemma 10.134.12: after correcting degree `0` by the canonical shear, the right
summand of the localization splitting is a chain-level copy of the localization-away complex. -/
theorem localized_self_compEquiv_cotangentComplex_symm_inr
    (y : (Generators.localizationAway Bg g).toExtension.Cotangent) :
    CotangentSpace.compEquiv
        (Generators.localizationAway Bg g)
        (Generators.self A B)
        ((localizedSelfGenerators A B Bg g).toExtension.cotangentComplex
          ((((Generators.self A B).cotangentCompLocalizationAwayEquiv (T := Bg) g
              (localized_self_extra_generator_maps_to_cMulXSubOne A B Bg g)).symm) (0, y))) =
      (((Generators.localizationAway Bg g).toExtension.cotangentComplex) y,
        localized_self_degree0_shear A B Bg g
          (((Generators.localizationAway Bg g).toExtension.cotangentComplex) y)) := by
  let P := Generators.self A B
  let Q := Generators.localizationAway Bg g
  let C := localizedSelfGenerators A B Bg g
  let e₁ := P.cotangentCompLocalizationAwayEquiv (T := Bg) g
    (localized_self_extra_generator_maps_to_cMulXSubOne A B Bg g)
  let c := (Generators.basisCotangentAway Bg g).repr y ()
  have hy :
      c • Generators.cMulXSubOneCotangent Bg g = y := by
    -- The localization-away cotangent module is rank one on `gX - 1`.
    simpa [c, Generators.basisCotangentAway_apply] using
      (Generators.basisCotangentAway Bg g).sum_repr y
  have hgen :
      CotangentSpace.compEquiv Q P
        (C.toExtension.cotangentComplex (e₁.symm (0, Generators.cMulXSubOneCotangent Bg g))) =
          (Q.toExtension.cotangentComplex (Generators.cMulXSubOneCotangent Bg g),
            localized_self_degree0_shear A B Bg g
              (Q.toExtension.cotangentComplex (Generators.cMulXSubOneCotangent Bg g))) := by
    -- Compare the two components on the distinguished generator supplied by the source proof.
    have hfst :
        (CotangentSpace.compEquiv Q P
          (C.toExtension.cotangentComplex (e₁.symm (0, Generators.cMulXSubOneCotangent Bg g)))).1 =
            Q.toExtension.cotangentComplex (Generators.cMulXSubOneCotangent Bg g) := by
          rw [Generators.cotangentCompLocalizationAwayEquiv_symm_inr
            (g := g) (P := P)
            (x := localized_self_extra_generator A B Bg g)
            (hx := localized_self_extra_generator_maps_to_cMulXSubOne A B Bg g)]
          exact localized_self_extra_generator_cotangent_space_fst A B Bg g
            (x := localized_self_extra_generator A B Bg g)
            (localized_self_extra_generator_maps_to_cMulXSubOne A B Bg g)
    have hsnd :
        (CotangentSpace.compEquiv Q P
          (C.toExtension.cotangentComplex (e₁.symm (0, Generators.cMulXSubOneCotangent Bg g)))).2 =
            localized_self_degree0_shear A B Bg g
              (Q.toExtension.cotangentComplex (Generators.cMulXSubOneCotangent Bg g)) := by
          rw [Generators.cotangentCompLocalizationAwayEquiv_symm_inr
            (g := g) (P := P)
            (x := localized_self_extra_generator A B Bg g)
            (hx := localized_self_extra_generator_maps_to_cMulXSubOne A B Bg g)]
          exact (localized_self_degree0_shear_cotangentComplex_cMulXSubOne A B Bg g).symm
    exact Prod.ext hfst hsnd
  -- Rewrite an arbitrary cotangent element through the rank-one basis and scale the generator case.
  rw [← hy]
  let y₀ : Q.toExtension.Cotangent := Generators.cMulXSubOneCotangent Bg g
  have hscaled : c •
      CotangentSpace.compEquiv Q P (C.toExtension.cotangentComplex (e₁.symm (0, y₀))) =
        c •
          (Q.toExtension.cotangentComplex y₀,
            localized_self_degree0_shear A B Bg g (Q.toExtension.cotangentComplex y₀)) :=
    by rw [hgen]
  have hleft :
      CotangentSpace.compEquiv Q P
          (C.toExtension.cotangentComplex (e₁.symm (0, c • y₀))) =
        c • CotangentSpace.compEquiv Q P
          (C.toExtension.cotangentComplex (e₁.symm (0, y₀))) := by
      have hpair :
          ((0 : Bg ⊗[B] (selfExtension A B).Cotangent), c • y₀) =
            c • ((0 : Bg ⊗[B] (selfExtension A B).Cotangent), y₀) := by
        ext <;> simp
      rw [hpair, map_smul, map_smul, map_smul]
  have hright :
      c •
          (Q.toExtension.cotangentComplex y₀,
            localized_self_degree0_shear A B Bg g (Q.toExtension.cotangentComplex y₀)) =
        (Q.toExtension.cotangentComplex (c • y₀),
          localized_self_degree0_shear A B Bg g (Q.toExtension.cotangentComplex (c • y₀))) := by
      ext <;> simp [map_smul]
  rw [hleft, hscaled, hright]

/-- Helper for Lemma 10.134.12: the degree-`0` shear on the product cotangent-space term is
inverted by adding back the same correction. -/
theorem localized_self_degree0_shear_equiv_left_inv :
    Function.LeftInverse
      (fun z :
          (Generators.localizationAway Bg g).toExtension.CotangentSpace ×
            (Bg ⊗[B] (selfExtension A B).CotangentSpace) ↦
        (z.1, z.2 - localized_self_degree0_shear A B Bg g z.1))
      (fun z :
          (Generators.localizationAway Bg g).toExtension.CotangentSpace ×
            (Bg ⊗[B] (selfExtension A B).CotangentSpace) ↦
        (z.1, z.2 + localized_self_degree0_shear A B Bg g z.1)) := by
  -- The source-faithful shear only changes the tensor component, so the inverse cancels there.
  intro z
  ext <;> simp [sub_eq_add_neg, add_assoc]

/-- Helper for Lemma 10.134.12: the same degree-`0` shear is also right-inverted by subtracting
the correction once more. -/
theorem localized_self_degree0_shear_equiv_right_inv :
    Function.RightInverse
      (fun z :
          (Generators.localizationAway Bg g).toExtension.CotangentSpace ×
            (Bg ⊗[B] (selfExtension A B).CotangentSpace) ↦
        (z.1, z.2 - localized_self_degree0_shear A B Bg g z.1))
      (fun z :
          (Generators.localizationAway Bg g).toExtension.CotangentSpace ×
            (Bg ⊗[B] (selfExtension A B).CotangentSpace) ↦
        (z.1, z.2 + localized_self_degree0_shear A B Bg g z.1)) := by
  -- The same cancellation identity proves the reverse composite is the identity as well.
  intro z
  ext <;> simp [sub_eq_add_neg, add_assoc]

/-- Helper for Lemma 10.134.12: the degree-`0` shear automorphism is additive. -/
theorem localized_self_degree0_shear_equiv_map_add
    (z z' :
      (Generators.localizationAway Bg g).toExtension.CotangentSpace ×
        (Bg ⊗[B] (selfExtension A B).CotangentSpace)) :
    (z + z').2 - localized_self_degree0_shear A B Bg g (z + z').1 =
      (z.2 - localized_self_degree0_shear A B Bg g z.1) +
        (z'.2 - localized_self_degree0_shear A B Bg g z'.1) := by
  -- Additivity reduces immediately to the linearity of `localized_self_degree0_shear`.
  simp [map_add, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

/-- Helper for Lemma 10.134.12: the degree-`0` shear automorphism is `Bg`-linear. -/
theorem localized_self_degree0_shear_equiv_map_smul
    (a : Bg)
    (z :
      (Generators.localizationAway Bg g).toExtension.CotangentSpace ×
        (Bg ⊗[B] (selfExtension A B).CotangentSpace)) :
    (a • z.2) - localized_self_degree0_shear A B Bg g (a • z.1) =
      a • (z.2 - localized_self_degree0_shear A B Bg g z.1) := by
  -- The shear term is linear in the localization component, so scalars factor out.
  rw [map_smul]
  simp [sub_eq_add_neg, smul_add]

/-- Helper for Lemma 10.134.12: the canonical degree-`0` shear is packaged as a product
automorphism before building the chain-level biproduct comparison. -/
noncomputable def localized_self_degree0_shear_equiv_on_product :
    ((Generators.localizationAway Bg g).toExtension.CotangentSpace ×
        (Bg ⊗[B] (selfExtension A B).CotangentSpace)) ≃ₗ[Bg]
      ((Generators.localizationAway Bg g).toExtension.CotangentSpace ×
        (Bg ⊗[B] (selfExtension A B).CotangentSpace)) :=
  -- The source proof uses exactly a lower-triangular shear that fixes the localization term and
  -- subtracts the correction from the tensor term.
  (LinearEquiv.refl Bg _).skewProd (LinearEquiv.refl Bg _)
    (-localized_self_degree0_shear A B Bg g)

/-- Helper for Lemma 10.134.12: the pointwise formula for the degree-`0` shear automorphism. -/
theorem localized_self_degree0_shear_equiv_on_product_apply
    (z :
      (Generators.localizationAway Bg g).toExtension.CotangentSpace ×
        (Bg ⊗[B] (selfExtension A B).CotangentSpace)) :
    localized_self_degree0_shear_equiv_on_product A B Bg g z =
      (z.1, z.2 - localized_self_degree0_shear A B Bg g z.1) := by
  -- Unfold the triangular product automorphism and simplify the inserted negation.
  simp [localized_self_degree0_shear_equiv_on_product, sub_eq_add_neg]

/-- Helper for Lemma 10.134.12: the inverse pointwise formula for the degree-`0` shear
automorphism. -/
theorem localized_self_degree0_shear_equiv_on_product_symm_apply
    (z :
      (Generators.localizationAway Bg g).toExtension.CotangentSpace ×
        (Bg ⊗[B] (selfExtension A B).CotangentSpace)) :
    (localized_self_degree0_shear_equiv_on_product A B Bg g).symm z =
      (z.1, z.2 + localized_self_degree0_shear A B Bg g z.1) := by
  -- The inverse of a lower-triangular shear adds back the same correction on the second factor.
  simp [localized_self_degree0_shear_equiv_on_product]

/-- Helper for Lemma 10.134.12: the tensor summand already lands in normalized degree `0` after
applying the isolated shear automorphism. -/
theorem localized_self_degree0_shear_equiv_normalizes_tensor
    (a : Bg ⊗[B] (selfExtension A B).Cotangent) :
    localized_self_degree0_shear_equiv_on_product A B Bg g
      (CotangentSpace.compEquiv
        (Generators.localizationAway Bg g)
        (Generators.self A B)
        ((localizedSelfGenerators A B Bg g).toExtension.cotangentComplex
          ((((Generators.self A B).cotangentCompLocalizationAwayEquiv (T := Bg) g
            (localized_self_extra_generator_maps_to_cMulXSubOne A B Bg g)).symm) (a, 0)))) =
      (0, LinearMap.baseChange Bg (selfExtension A B).cotangentComplex a) := by
  -- The tensor lift already lands purely in the tensor factor before the shear, so the shear acts
  -- trivially after rewriting by the source-faithful degree-`0` split.
  rw [localized_self_tensor_component_cotangent_space_split]
  rw [localized_self_degree0_shear_equiv_on_product_apply]
  simp

/-- Helper for Lemma 10.134.12: the localization summand becomes a pure copy of the
localization-away complex after applying the isolated shear automorphism. -/
theorem localized_self_degree0_shear_equiv_normalizes_localization
    (y : (Generators.localizationAway Bg g).toExtension.Cotangent) :
    localized_self_degree0_shear_equiv_on_product A B Bg g
      (CotangentSpace.compEquiv
        (Generators.localizationAway Bg g)
        (Generators.self A B)
        ((localizedSelfGenerators A B Bg g).toExtension.cotangentComplex
          ((((Generators.self A B).cotangentCompLocalizationAwayEquiv (T := Bg) g
            (localized_self_extra_generator_maps_to_cMulXSubOne A B Bg g)).symm) (0, y)))) =
      (((Generators.localizationAway Bg g).toExtension.cotangentComplex) y, 0) := by
  -- The localization lift carries exactly the shear correction in the tensor slot, and the
  -- forward shear subtracts that correction back to zero.
  rw [localized_self_compEquiv_cotangentComplex_symm_inr]
  rw [localized_self_degree0_shear_equiv_on_product_apply]
  simp

/-- Helper for Lemma 10.134.12: higher terms of any naive cotangent complex are canonically the
zero `PUnit` module. -/
noncomputable def extension_naiveCotangentChainComplex_X_succ_succ_iso_punit
    {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] [Algebra R S]
    (P : Extension R S) (n : ℕ) :
    P.naiveCotangentChainComplex.X (n + 2) ≅ ModuleCat.of S PUnit :=
  let succZero :
      ∀ {X₀ X₁ : ModuleCat S} (f : X₁ ⟶ X₀),
        Σ' (X₂ : ModuleCat S) (d : X₂ ⟶ X₁), d ≫ f = 0 :=
    fun {_ _} _ ↦ ⟨ModuleCat.of S PUnit, 0, zero_comp⟩
  -- `ChainComplex.mk'` identifies every term above degree `1` with the chosen zero object.
  (ChainComplex.mk'XIso
      (ModuleCat.of S P.CotangentSpace)
      (ModuleCat.of S (ULift P.Cotangent))
      (ModuleCat.ofHom (P.cotangentComplex.comp ULift.moduleEquiv.toLinearMap))
      succZero n) ≪≫
    eqToIso rfl

/-- Helper for Lemma 10.134.12: the normalized tensor model also has `PUnit` in every degree
above `1`. -/
noncomputable def tensorNaiveCotangentAwayModel_X_succ_succ_iso_punit
    (n : ℕ) :
    (tensorNaiveCotangentAwayModel A B Bg).X (n + 2) ≅ ModuleCat.of Bg PUnit :=
  let P := selfExtension A B
  let succZero :
      ∀ {X₀ X₁ : ModuleCat Bg} (f : X₁ ⟶ X₀),
        Σ' (X₂ : ModuleCat Bg) (d : X₂ ⟶ X₁), d ≫ f = 0 :=
    fun {_ _} _ ↦ ⟨ModuleCat.of Bg PUnit, 0, zero_comp⟩
  -- The private tensor model was defined with the same `mk'` zero tail.
  (ChainComplex.mk'XIso
      (ModuleCat.of Bg (Bg ⊗[B] P.CotangentSpace))
      (ModuleCat.of Bg (Bg ⊗[B] P.Cotangent))
      (ModuleCat.ofHom (LinearMap.baseChange Bg P.cotangentComplex))
      succZero n) ≪≫
    eqToIso rfl

/-- Helper for Lemma 10.134.12: the degree-`≥ 2` term of the localized self-presentation is also
subsingleton, again because it is canonically the zero `PUnit` module. -/
theorem localized_self_X_succ_succ_subsingleton
    (n : ℕ) :
    Subsingleton
      ((localizedSelfGenerators A B Bg g).toExtension.naiveCotangentChainComplex.X (n + 2)) := by
  -- The standard `mk'` description of the naive cotangent complex makes every higher term
  -- canonically equivalent to `PUnit`.
  let e :=
    extension_naiveCotangentChainComplex_X_succ_succ_iso_punit
      ((localizedSelfGenerators A B Bg g).toExtension) n
  refine ⟨fun x y ↦ ?_⟩
  have hxy : e.hom.hom x = e.hom.hom y := Subsingleton.elim _ _
  simpa using congrArg e.inv.hom hxy

omit [Algebra A Bg] [IsScalarTower A B Bg]

/-- Helper for Lemma 10.134.12: every degree `n + 2` term of the normalized tensor model is
subsingleton. -/
theorem tensorNaiveCotangentAwayModel_X_succ_succ_subsingleton
    (n : ℕ) :
    Subsingleton ((tensorNaiveCotangentAwayModel A B Bg).X (n + 2)) := by
  -- Transport the unique element of `PUnit` back through the explicit high-degree identification.
  let e := tensorNaiveCotangentAwayModel_X_succ_succ_iso_punit A B Bg n
  refine ⟨fun x y ↦ ?_⟩
  have hxy : e.hom.hom x = e.hom.hom y := Subsingleton.elim _ _
  simpa using congrArg e.inv.hom hxy

omit [CommRing A] [Algebra A B]

/-- Helper for Lemma 10.134.12: every degree `n + 2` term of the canonical localization-away
naive cotangent complex is also subsingleton. -/
theorem localizationAway_reindex_X_succ_succ_subsingleton
    (n : ℕ) :
    Subsingleton
      ((localizationAwayGenerators B Bg g).toExtension.naiveCotangentChainComplex.X (n + 2)) := by
  -- This is the same `PUnit` tail coming from the standard `mk'` presentation model.
  let e :=
    extension_naiveCotangentChainComplex_X_succ_succ_iso_punit
      ((localizationAwayGenerators B Bg g).toExtension) n
  refine ⟨fun x y ↦ ?_⟩
  have hxy : e.hom.hom x = e.hom.hom y := Subsingleton.elim _ _
  simpa using congrArg e.inv.hom hxy

/-- Helper for Lemma 10.134.12: the forward basis map from the reindexed degree-`0` term to the
standard localization-away degree-`0` term. -/
noncomputable def localizationAway_reindex_cotangentSpace_forward :
    (localizationAwayGenerators B Bg g).toExtension.CotangentSpace →ₗ[Bg]
      (Generators.localizationAway Bg g).toExtension.CotangentSpace :=
  (localizationAwayGenerators B Bg g).cotangentSpaceBasis.constr Bg
    (fun _ ↦ (Generators.localizationAway Bg g).cotangentSpaceBasis ())

/-- Helper for Lemma 10.134.12: the backward basis map from the standard localization-away
degree-`0` term to the reindexed one. -/
noncomputable def localizationAway_reindex_cotangentSpace_backward :
    (Generators.localizationAway Bg g).toExtension.CotangentSpace →ₗ[Bg]
      (localizationAwayGenerators B Bg g).toExtension.CotangentSpace :=
  (Generators.localizationAway Bg g).cotangentSpaceBasis.constr Bg
    (fun _ ↦ (localizationAwayGenerators B Bg g).cotangentSpaceBasis (ULift.up ()))

end
