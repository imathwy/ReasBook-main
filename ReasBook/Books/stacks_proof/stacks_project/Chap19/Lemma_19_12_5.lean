import Mathlib
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
import StacksProject_2024.Chap12.Definition_12_27_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits
open CochainComplex.HomComplex

noncomputable section

universe w v u

namespace CochainComplex

section LocalOwnerFallback

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Helper for Lemma 19.12.5: a file-local fallback copy of the Chapter 19 owner packaging for a
functorial monomorphic quasi-isomorphic enlargement of cochain complexes. -/
structure FunctorialComplexApproximation (C : Type u) [Category.{v} C] [Abelian C] where
  /-- The underlying endofunctor on cochain complexes. -/
  toFunctor : CochainComplex C ℤ ⥤ CochainComplex C ℤ
  /-- The natural comparison map from a complex to its chosen enlargement. -/
  ι : 𝟭 (CochainComplex C ℤ) ⟶ toFunctor
  /-- The comparison natural transformation is monomorphic. -/
  mono_ι : Mono ι
  /-- Each comparison map is a quasi-isomorphism. -/
  quasiIso_app (M : CochainComplex C ℤ) : QuasiIso (ι.app M)

namespace FunctorialComplexApproximation

variable {C : Type u} [Category.{v} C] [Abelian C]

instance (J : FunctorialComplexApproximation C) : Mono J.ι :=
  J.mono_ι

/-- Helper for Lemma 19.12.5: every component of the comparison map in a functorial complex
approximation is mono. -/
theorem mono_app (J : FunctorialComplexApproximation C) (M : CochainComplex C ℤ) :
    Mono (J.ι.app M) := by
  -- Proof comment: monomorphy of a natural transformation is detected objectwise.
  exact (NatTrans.mono_iff_mono_app J.ι).1 J.mono_ι M

end FunctorialComplexApproximation

end LocalOwnerFallback

section AuxiliaryConstruction

variable {C : Type u} [Category.{v} C] [HasFunctorialInjectiveEmbeddings C]

/-- Helper for Lemma 19.12.5: the identity subobject of the chosen injective target `I(X)` is
again injective. -/
theorem identity_subobject_injective_of_functorial_embedding
    (X : C) :
    Injective
      ((((Subobject.mk (𝟙 (HasFunctorialInjectiveEmbeddings.under X))) :
          Subobject (HasFunctorialInjectiveEmbeddings.under X)) : Subobject
            (HasFunctorialInjectiveEmbeddings.under X)) : C) := by
  exact
    Injective.of_iso
      (Subobject.underlyingIso (𝟙 (HasFunctorialInjectiveEmbeddings.under X))).symm
      inferInstance

/-- Helper for Lemma 19.12.5: the chosen embedding `X ⟶ I(X)` already factors through an
injective subobject of `I(X)`, namely the identity subobject. -/
theorem functorial_embedding_factors_through_injective_subobject
    (X : C) :
    ∃ I : Subobject (HasFunctorialInjectiveEmbeddings.under X),
      Injective (I : C) ∧ I.Factors (HasFunctorialInjectiveEmbeddings.ι X) := by
  refine ⟨⊤, ?_, ?_⟩
  · -- The top subobject is the identity subobject after rewriting with `Subobject.top_eq_id`.
    simpa [Subobject.top_eq_id] using
      identity_subobject_injective_of_functorial_embedding (C := C) X
  · -- Every morphism factors through the top subobject.
    simpa [Subobject.top_eq_id] using
      (Subobject.top_factors (HasFunctorialInjectiveEmbeddings.ι X))

end AuxiliaryConstruction

section AuxiliaryBiproductComplex

variable {C : Type u} [Category.{v} C] [Abelian C] [HasFunctorialInjectiveEmbeddings C]

/-- Helper for Lemma 19.12.5: the source-proof auxiliary object
`J(M)^n = I(M^n) ⊞ I(M^{n + 1})` assembled degreewise into a cochain complex. -/
noncomputable def injective_biproduct_complex_obj
    (M : CochainComplex C ℤ) : CochainComplex C ℤ :=
  CochainComplex.of
    (fun n ↦ HasFunctorialInjectiveEmbeddings.under (M.X n) ⊞
      HasFunctorialInjectiveEmbeddings.under (M.X (n + 1)))
    (fun n ↦ Limits.biprod.snd ≫ Limits.biprod.inl)
    (fun n ↦ by
      simp)

/-- Helper for Lemma 19.12.5: every term of the auxiliary complex `J(M)` is injective. -/
theorem injective_biproduct_complex_obj_term_injective
    (M : CochainComplex C ℤ) (n : ℤ) :
    Injective ((injective_biproduct_complex_obj (C := C) M).X n) := by
  -- Each term is a binary biproduct of the chosen injective envelopes in consecutive degrees.
  change Injective
    (HasFunctorialInjectiveEmbeddings.under (M.X n) ⊞
      HasFunctorialInjectiveEmbeddings.under (M.X (n + 1)))
  infer_instance

/-- Helper for Lemma 19.12.5: the successor differential on `J(M)` is the fixed map
`snd ≫ inl`. -/
theorem injective_biproduct_complex_obj_d_succ
    (M : CochainComplex C ℤ) (i : ℤ) :
    (injective_biproduct_complex_obj (C := C) M).d i (i + 1) =
      Limits.biprod.snd ≫ Limits.biprod.inl := by
  -- This is the canonical `CochainComplex.of_d` computation for the source auxiliary complex.
  simpa [injective_biproduct_complex_obj] using
    (CochainComplex.of_d
      (fun n ↦ HasFunctorialInjectiveEmbeddings.under (M.X n) ⊞
        HasFunctorialInjectiveEmbeddings.under (M.X (n + 1)))
      (fun n ↦ Limits.biprod.snd ≫ Limits.biprod.inl)
      (fun n ↦ by simp)
      i)

/-- Helper for Lemma 19.12.5: the degreewise maps on `J(M)` commute with the fixed differential
`snd ≫ inl`. -/
theorem injective_biproduct_complex_map_comm
    {M N : CochainComplex C ℤ} (f : M ⟶ N) (i j : ℤ) (hij : (ComplexShape.up ℤ).Rel i j) :
    Limits.biprod.map
        (HasFunctorialInjectiveEmbeddings.underMap (f.f i))
        (HasFunctorialInjectiveEmbeddings.underMap (f.f (i + 1))) ≫
      (injective_biproduct_complex_obj (C := C) N).d i j =
        (injective_biproduct_complex_obj (C := C) M).d i j ≫
          Limits.biprod.map
            (HasFunctorialInjectiveEmbeddings.underMap (f.f j))
            (HasFunctorialInjectiveEmbeddings.underMap (f.f (j + 1))) := by
  -- Reduce the shape relation to the successor case, then expose the fixed `snd ≫ inl`
  -- differential from `CochainComplex.of`.
  rcases hij with rfl
  rw [injective_biproduct_complex_obj_d_succ (C := C) N i]
  rw [injective_biproduct_complex_obj_d_succ (C := C) M i]
  -- Both sides are the same projection/inclusion composite through the second summand.
  calc
    Limits.biprod.map
        (HasFunctorialInjectiveEmbeddings.underMap (f.f i))
        (HasFunctorialInjectiveEmbeddings.underMap (f.f (i + 1))) ≫
      Limits.biprod.snd ≫ Limits.biprod.inl =
        Limits.biprod.snd ≫ HasFunctorialInjectiveEmbeddings.underMap (f.f (i + 1)) ≫
          Limits.biprod.inl := by
            simpa [Category.assoc] using
              congrArg
                (fun k ↦ k ≫ Limits.biprod.inl)
                (Limits.biprod.map_snd
                  (HasFunctorialInjectiveEmbeddings.underMap (f.f i))
                  (HasFunctorialInjectiveEmbeddings.underMap (f.f (i + 1))))
    _ =
      Limits.biprod.snd ≫ Limits.biprod.inl ≫
        Limits.biprod.map
          (HasFunctorialInjectiveEmbeddings.underMap (f.f (i + 1)))
          (HasFunctorialInjectiveEmbeddings.underMap (f.f (i + 1 + 1))) := by
            simpa [Category.assoc] using
              congrArg
                (fun k ↦ Limits.biprod.snd ≫ k)
                (Limits.biprod.inl_map
                  (HasFunctorialInjectiveEmbeddings.underMap (f.f (i + 1)))
                  (HasFunctorialInjectiveEmbeddings.underMap (f.f (i + 1 + 1)))).symm
    _ = (Limits.biprod.snd ≫ Limits.biprod.inl) ≫
        Limits.biprod.map
          (HasFunctorialInjectiveEmbeddings.underMap (f.f (i + 1)))
          (HasFunctorialInjectiveEmbeddings.underMap (f.f (i + 1 + 1))) := by
            rw [Category.assoc]

/-- Helper for Lemma 19.12.5: the auxiliary biproduct complex sends identity maps to identity
chain maps. -/
theorem injective_biproduct_complex_map_id
    (M : CochainComplex C ℤ) :
    HomologicalComplex.Hom.mk
        (fun n ↦
          Limits.biprod.map
            (HasFunctorialInjectiveEmbeddings.underMap (𝟙 (M.X n)))
            (HasFunctorialInjectiveEmbeddings.underMap (𝟙 (M.X (n + 1)))))
        (fun i j hij ↦ injective_biproduct_complex_map_comm (C := C) (𝟙 M) i j hij) =
      𝟙 (injective_biproduct_complex_obj (C := C) M) := by
  -- Compare degreewise components and then compare the two biproduct projections.
  ext n
  change
    Limits.biprod.map
        (HasFunctorialInjectiveEmbeddings.underMap (𝟙 (M.X n)))
        (HasFunctorialInjectiveEmbeddings.underMap (𝟙 (M.X (n + 1)))) =
      𝟙
        (HasFunctorialInjectiveEmbeddings.under (M.X n) ⊞
          HasFunctorialInjectiveEmbeddings.under (M.X (n + 1)))
  apply Limits.biprod.hom_ext
  · simp [HasFunctorialInjectiveEmbeddings.underMap]
  · simp [HasFunctorialInjectiveEmbeddings.underMap]

noncomputable def injective_biproduct_complex : CochainComplex C ℤ ⥤ CochainComplex C ℤ where
  obj M := injective_biproduct_complex_obj (C := C) M
  map {M N} f :=
    HomologicalComplex.Hom.mk
      (fun n ↦
        Limits.biprod.map
          (HasFunctorialInjectiveEmbeddings.underMap (f.f n))
          (HasFunctorialInjectiveEmbeddings.underMap (f.f (n + 1))))
      (fun i j hij ↦ injective_biproduct_complex_map_comm (C := C) f i j hij)
  map_id M := injective_biproduct_complex_map_id (C := C) M
  map_comp f g := by
    -- Compare degreewise components and use functoriality of the chosen injective targets.
    ext n
    change
      Limits.biprod.map
          (HasFunctorialInjectiveEmbeddings.underMap (f.f n ≫ g.f n))
          (HasFunctorialInjectiveEmbeddings.underMap (f.f (n + 1) ≫ g.f (n + 1))) =
        Limits.biprod.map
            (HasFunctorialInjectiveEmbeddings.underMap (f.f n))
            (HasFunctorialInjectiveEmbeddings.underMap (f.f (n + 1))) ≫
          Limits.biprod.map
            (HasFunctorialInjectiveEmbeddings.underMap (g.f n))
            (HasFunctorialInjectiveEmbeddings.underMap (g.f (n + 1)))
    apply Limits.biprod.hom_ext
    · simp [HasFunctorialInjectiveEmbeddings.underMap, Category.assoc]
    · simp [HasFunctorialInjectiveEmbeddings.underMap, Category.assoc]

/-- Helper for Lemma 19.12.5: the degreewise textbook inclusion defines a chain map
`M ⟶ J(M)`. -/
theorem injective_biproduct_inclusion_second_projection
    {A B : C} (f : A ⟶ B) :
    Limits.biprod.lift
        (HasFunctorialInjectiveEmbeddings.ι A)
        (f ≫ HasFunctorialInjectiveEmbeddings.ι B) ≫
      Limits.biprod.snd =
        HasFunctorialInjectiveEmbeddings.ι A ≫
          HasFunctorialInjectiveEmbeddings.underMap f := by
  -- Projecting to the second summand exposes the naturality square for the chosen embeddings.
  rw [Limits.biprod.lift_snd]
  simpa [Category.assoc] using
    (HasFunctorialInjectiveEmbeddings.ι_naturality_w f)

/-- Helper for Lemma 19.12.5: precomposing the textbook inclusion and then projecting to the
second summand is the canonical `ι ≫ underMap` normal form. -/
theorem injective_biproduct_inclusion_second_projection_assoc
    {X A B : C} (g : X ⟶ A) (f : A ⟶ B) :
    g ≫
        Limits.biprod.lift
          (HasFunctorialInjectiveEmbeddings.ι A)
          (f ≫ HasFunctorialInjectiveEmbeddings.ι B) ≫
      Limits.biprod.snd =
        g ≫ HasFunctorialInjectiveEmbeddings.ι A ≫
          HasFunctorialInjectiveEmbeddings.underMap f := by
  -- Reassociate the already verified second-projection formula into the precomposed normal form.
  simpa [Category.assoc] using
    congrArg (fun k ↦ g ≫ k)
      (injective_biproduct_inclusion_second_projection (C := C) f)

/-- Helper for Lemma 19.12.5: if `g ≫ f = 0`, then the corresponding composite into the chosen
injective targets also vanishes. -/
theorem comp_functorial_embedding_underMap_eq_zero_of_comp_zero
    {X A B : C} (g : X ⟶ A) (f : A ⟶ B) (hgf : g ≫ f = 0) :
    g ≫ HasFunctorialInjectiveEmbeddings.ι A ≫
      HasFunctorialInjectiveEmbeddings.underMap f = 0 := by
  -- Proof comment: precompose the owner naturality square with `g` and then rewrite the vanishing
  -- composite `g ≫ f = 0`.
  simpa [Category.assoc, hgf] using
    congrArg (fun k ↦ g ≫ k) (HasFunctorialInjectiveEmbeddings.ι_naturality_w f)

/-- Helper for Lemma 19.12.5: the degreewise textbook inclusion defines a chain map
`M ⟶ J(M)`. -/
theorem injective_biproduct_inclusion_app_comm
    (M : CochainComplex C ℤ) (i j : ℤ) (hij : (ComplexShape.up ℤ).Rel i j) :
    Limits.biprod.lift
        (HasFunctorialInjectiveEmbeddings.ι (M.X i))
        (M.d i (i + 1) ≫ HasFunctorialInjectiveEmbeddings.ι (M.X (i + 1))) ≫
      (injective_biproduct_complex_obj (C := C) M).d i j =
        M.d i j ≫
          Limits.biprod.lift
            (HasFunctorialInjectiveEmbeddings.ι (M.X j))
            (M.d j (j + 1) ≫ HasFunctorialInjectiveEmbeddings.ι (M.X (j + 1))) := by
  -- Route correction: normalize the successor differential and then compare the two projections,
  -- exactly as in the source proof for `u_M : M ⟶ J(M)`.
  rcases hij with rfl
  rw [injective_biproduct_complex_obj_d_succ (C := C) M i]
  apply Limits.biprod.hom_ext
  · -- The first projection records the degree-`i + 1` embedding on both sides.
    calc
      (Limits.biprod.lift
            (HasFunctorialInjectiveEmbeddings.ι (M.X i))
            (M.d i (i + 1) ≫ HasFunctorialInjectiveEmbeddings.ι (M.X (i + 1))) ≫
          Limits.biprod.snd ≫ Limits.biprod.inl) ≫
        Limits.biprod.fst =
          Limits.biprod.lift
            (HasFunctorialInjectiveEmbeddings.ι (M.X i))
            (M.d i (i + 1) ≫ HasFunctorialInjectiveEmbeddings.ι (M.X (i + 1))) ≫
              Limits.biprod.snd := by
                simp [Category.assoc]
      _ =
        HasFunctorialInjectiveEmbeddings.ι (M.X i) ≫
          HasFunctorialInjectiveEmbeddings.underMap (M.d i (i + 1)) :=
            injective_biproduct_inclusion_second_projection (C := C) (M.d i (i + 1))
      _ =
        M.d i (i + 1) ≫ HasFunctorialInjectiveEmbeddings.ι (M.X (i + 1)) := by
          simpa [Category.assoc] using
            (HasFunctorialInjectiveEmbeddings.ι_naturality_w (M.d i (i + 1))).symm
      _ =
        (M.d i (i + 1) ≫
            Limits.biprod.lift
              (HasFunctorialInjectiveEmbeddings.ι (M.X (i + 1)))
              (M.d (i + 1) (i + 1 + 1) ≫
                HasFunctorialInjectiveEmbeddings.ι (M.X (i + 1 + 1)))) ≫
          Limits.biprod.fst := by
            simp [Category.assoc]
  · -- The second projection vanishes because `d^{i+1} ∘ d^i = 0`, transported through `ι`.
    calc
      (Limits.biprod.lift
            (HasFunctorialInjectiveEmbeddings.ι (M.X i))
            (M.d i (i + 1) ≫ HasFunctorialInjectiveEmbeddings.ι (M.X (i + 1))) ≫
          Limits.biprod.snd ≫ Limits.biprod.inl) ≫
        Limits.biprod.snd = 0 := by
          simp [Category.assoc]
      _ =
        (M.d i (i + 1) ≫
            Limits.biprod.lift
              (HasFunctorialInjectiveEmbeddings.ι (M.X (i + 1)))
              (M.d (i + 1) (i + 1 + 1) ≫
                HasFunctorialInjectiveEmbeddings.ι (M.X (i + 1 + 1)))) ≫
          Limits.biprod.snd := by
            symm
            calc
              (M.d i (i + 1) ≫
                    Limits.biprod.lift
                      (HasFunctorialInjectiveEmbeddings.ι (M.X (i + 1)))
                      (M.d (i + 1) (i + 1 + 1) ≫
                        HasFunctorialInjectiveEmbeddings.ι (M.X (i + 1 + 1)))) ≫
                  Limits.biprod.snd =
                M.d i (i + 1) ≫
                  HasFunctorialInjectiveEmbeddings.ι (M.X (i + 1)) ≫
                    HasFunctorialInjectiveEmbeddings.underMap (M.d (i + 1) (i + 1 + 1)) := by
                      rw [Category.assoc]
                      rw [injective_biproduct_inclusion_second_projection_assoc (C := C)
                        (g := M.d i (i + 1)) (f := M.d (i + 1) (i + 1 + 1))]
              _ = 0 := comp_functorial_embedding_underMap_eq_zero_of_comp_zero (C := C)
                (g := M.d i (i + 1)) (f := M.d (i + 1) (i + 1 + 1))
                (M.d_comp_d i (i + 1) (i + 1 + 1))

noncomputable def injective_biproduct_inclusion_app
    (M : CochainComplex C ℤ) :
    M ⟶ injective_biproduct_complex_obj (C := C) M :=
  HomologicalComplex.Hom.mk
    (fun n ↦
      Limits.biprod.lift
        (HasFunctorialInjectiveEmbeddings.ι (M.X n))
        (M.d n (n + 1) ≫ HasFunctorialInjectiveEmbeddings.ι (M.X (n + 1))))
    (fun i j hij ↦ injective_biproduct_inclusion_app_comm (C := C) M i j hij)

/-- Helper for Lemma 19.12.5: the inclusion maps `u_M : M ⟶ J(M)` are natural in the complex
`M`, so they package into a natural transformation `𝟭 ⟶ J`. -/
theorem injective_biproduct_inclusion_naturality
    {M N : CochainComplex C ℤ} (f : M ⟶ N) :
    f ≫ injective_biproduct_inclusion_app (C := C) N =
      injective_biproduct_inclusion_app (C := C) M ≫
        (injective_biproduct_complex (C := C)).map f := by
  -- Proof comment: compare the degreewise components and then compare the two biproduct
  -- projections separately.
  ext n
  apply Limits.biprod.hom_ext
  · -- The first projection is exactly the owner naturality square in degree `n`.
    calc
      (f ≫ injective_biproduct_inclusion_app (C := C) N).f n ≫ Limits.biprod.fst =
          f.f n ≫ HasFunctorialInjectiveEmbeddings.ι (N.X n) := by
            simp [injective_biproduct_inclusion_app, Category.assoc]
      _ =
          HasFunctorialInjectiveEmbeddings.ι (M.X n) ≫
            HasFunctorialInjectiveEmbeddings.underMap (f.f n) := by
              simpa [Category.assoc] using
                (HasFunctorialInjectiveEmbeddings.ι_naturality_w (f.f n))
      _ =
          (injective_biproduct_inclusion_app (C := C) M ≫
              (injective_biproduct_complex (C := C)).map f).f n ≫
            Limits.biprod.fst := by
              simp [injective_biproduct_inclusion_app, injective_biproduct_complex,
                Category.assoc]
  · -- The second projection uses the chain-map relation for `f` and then owner naturality in
    -- degree `n + 1`.
    calc
      (f ≫ injective_biproduct_inclusion_app (C := C) N).f n ≫ Limits.biprod.snd =
          f.f n ≫ N.d n (n + 1) ≫
            HasFunctorialInjectiveEmbeddings.ι (N.X (n + 1)) := by
              simp [injective_biproduct_inclusion_app, Category.assoc]
      _ =
          M.d n (n + 1) ≫ f.f (n + 1) ≫
            HasFunctorialInjectiveEmbeddings.ι (N.X (n + 1)) := by
              simpa [Category.assoc] using
                congrArg
                  (fun k ↦ k ≫ HasFunctorialInjectiveEmbeddings.ι (N.X (n + 1)))
                  (f.comm n (n + 1))
      _ =
          M.d n (n + 1) ≫ HasFunctorialInjectiveEmbeddings.ι (M.X (n + 1)) ≫
            HasFunctorialInjectiveEmbeddings.underMap (f.f (n + 1)) := by
              rw [Category.assoc]
              simpa [Category.assoc] using
                (HasFunctorialInjectiveEmbeddings.ι_naturality_w (f.f (n + 1)))
      _ =
          (injective_biproduct_inclusion_app (C := C) M ≫
              (injective_biproduct_complex (C := C)).map f).f n ≫
            Limits.biprod.snd := by
              simp [injective_biproduct_inclusion_app, injective_biproduct_complex,
                Category.assoc]

/-- Helper for Lemma 19.12.5: each textbook inclusion `u_M : M ⟶ J(M)` is degreewise split mono,
hence mono as a morphism of cochain complexes. -/
theorem injective_biproduct_inclusion_app_mono
    (M : CochainComplex C ℤ) :
    Mono (injective_biproduct_inclusion_app (C := C) M) := by
  -- Proof comment: each degree component becomes mono after postcomposing with the first
  -- biproduct projection, which recovers the chosen embedding `ι`.
  refine HomologicalComplex.mono_of_mono_f _ ?_
  intro n
  have hcomp :
      (injective_biproduct_inclusion_app (C := C) M).f n ≫ Limits.biprod.fst =
        HasFunctorialInjectiveEmbeddings.ι (M.X n) := by
    simp [injective_biproduct_inclusion_app, Category.assoc]
  exact mono_of_mono_fac hcomp

/-- Helper for Lemma 19.12.5: the canonical cokernel row attached to the textbook inclusion
`u_M : M ⟶ J(M)` is short exact. -/
theorem injectiveBiproductInclusionShortExact
    (M : CochainComplex C ℤ) :
    (ShortComplex.cokernelSequence (injective_biproduct_inclusion_app (C := C) M)).ShortExact := by
  -- Combine the canonical cokernel exactness with the split-monomorphism just established.
  exact
    ShortComplex.ShortExact.mk'
      (ShortComplex.cokernelSequence_exact (injective_biproduct_inclusion_app (C := C) M))
      (injective_biproduct_inclusion_app_mono (C := C) M)
      inferInstance

noncomputable def injective_biproduct_inclusion :
    𝟭 (CochainComplex C ℤ) ⟶ injective_biproduct_complex (C := C) where
  app M := injective_biproduct_inclusion_app (C := C) M
  naturality {_ _} f := injective_biproduct_inclusion_naturality (C := C) f

/-- Helper for Lemma 19.12.5: the objectwise quotient of the textbook inclusion
`u_M : M ⟶ J(M)`. -/
noncomputable abbrev injectiveBiproductQuotientObj
    (M : CochainComplex C ℤ) : CochainComplex C ℤ :=
  cokernel (injective_biproduct_inclusion_app (C := C) M)

/-- Helper for Lemma 19.12.5: the quotient map induced by a morphism of complexes under the
natural textbook inclusion `u`. -/
noncomputable def injectiveBiproductQuotientMap
    {M N : CochainComplex C ℤ} (f : M ⟶ N) :
    injectiveBiproductQuotientObj (C := C) M ⟶
      injectiveBiproductQuotientObj (C := C) N :=
  let _ : Mono (injective_biproduct_inclusion_app (C := C) M) :=
    injective_biproduct_inclusion_app_mono (C := C) M
  let _ : Mono (injective_biproduct_inclusion_app (C := C) N) :=
    injective_biproduct_inclusion_app_mono (C := C) N
  cokernel.map
    (injective_biproduct_inclusion_app (C := C) M)
    (injective_biproduct_inclusion_app (C := C) N)
    f
    ((injective_biproduct_complex (C := C)).map f)
    (injective_biproduct_inclusion_naturality (C := C) f).symm

/-- Helper for Lemma 19.12.5: the canonical quotient projection is natural with respect to the
maps induced by `injectiveBiproductQuotientMap`. -/
theorem injectiveBiproductQuotient_projection_naturality
    {M N : CochainComplex C ℤ} (f : M ⟶ N) :
    cokernel.π (injective_biproduct_inclusion_app (C := C) M) ≫
        injectiveBiproductQuotientMap (C := C) f =
      ((injective_biproduct_complex (C := C)).map f) ≫
        cokernel.π (injective_biproduct_inclusion_app (C := C) N) := by
  -- Proof comment: the induced quotient map is defined by `cokernel.map`, so the projection
  -- naturality is exactly the owner computation rule `cokernel.π_desc`.
  dsimp [injectiveBiproductQuotientMap]
  rw [cokernel.π_desc]

/-- Helper for Lemma 19.12.5: the quotient maps induced from the textbook inclusion compose
functorially. -/
theorem injectiveBiproductQuotientMap_comp
    {L M N : CochainComplex C ℤ} (f : L ⟶ M) (g : M ⟶ N) :
    injectiveBiproductQuotientMap (C := C) (f ≫ g) =
      injectiveBiproductQuotientMap (C := C) f ≫
        injectiveBiproductQuotientMap (C := C) g := by
  -- Proof comment: compare both quotient maps after precomposing with the cokernel projection of
  -- `u_L`, then rewrite the two quotient squares into the same functorial normal form.
  apply (cancel_epi (cokernel.π (injective_biproduct_inclusion_app (C := C) L))).1
  calc
    cokernel.π (injective_biproduct_inclusion_app (C := C) L) ≫
        injectiveBiproductQuotientMap (C := C) (f ≫ g) =
      (injective_biproduct_complex (C := C)).map (f ≫ g) ≫
        cokernel.π (injective_biproduct_inclusion_app (C := C) N) := by
          rw [injectiveBiproductQuotient_projection_naturality]
    _ =
      ((injective_biproduct_complex (C := C)).map f ≫
          (injective_biproduct_complex (C := C)).map g) ≫
        cokernel.π (injective_biproduct_inclusion_app (C := C) N) := by
          rw [Functor.map_comp]
    _ =
      (injective_biproduct_complex (C := C)).map f ≫
        ((injective_biproduct_complex (C := C)).map g ≫
          cokernel.π (injective_biproduct_inclusion_app (C := C) N)) := by
            simp [Category.assoc]
    _ =
      (injective_biproduct_complex (C := C)).map f ≫
        (cokernel.π (injective_biproduct_inclusion_app (C := C) M) ≫
          injectiveBiproductQuotientMap (C := C) g) := by
            rw [injectiveBiproductQuotient_projection_naturality]
    _ =
      ((injective_biproduct_complex (C := C)).map f ≫
          cokernel.π (injective_biproduct_inclusion_app (C := C) M)) ≫
        injectiveBiproductQuotientMap (C := C) g := by
          simp [Category.assoc]
    _ =
      (cokernel.π (injective_biproduct_inclusion_app (C := C) L) ≫
          injectiveBiproductQuotientMap (C := C) f) ≫
        injectiveBiproductQuotientMap (C := C) g := by
          rw [injectiveBiproductQuotient_projection_naturality]
    _ =
      cokernel.π (injective_biproduct_inclusion_app (C := C) L) ≫
        injectiveBiproductQuotientMap (C := C) f ≫
          injectiveBiproductQuotientMap (C := C) g := by
            simp [Category.assoc]

/-- Helper for Lemma 19.12.5: the canonical comparison map
`M ⟶ mappingCocone(cokernel.π u_M)` obtained from the zero `(-1)`-cochain. -/
noncomputable def injectiveBiproductApproximationApp
    (M : CochainComplex C ℤ) :
    M ⟶
      CochainComplex.mappingCocone
        (cokernel.π (injective_biproduct_inclusion_app (C := C) M)) :=
  CochainComplex.mappingCocone.lift
    (cokernel.π (injective_biproduct_inclusion_app (C := C) M))
    (injective_biproduct_inclusion_app (C := C) M)
    (0 : Cochain M (injectiveBiproductQuotientObj (C := C) M) (-1))
    (by
      -- The zero `(-1)`-cochain is admissible because `u_M` followed by the quotient projection is
      -- exactly zero.
      simpa using
        (cokernel.condition (injective_biproduct_inclusion_app (C := C) M)))

/-- Helper for Lemma 19.12.5: the canonical comparison into the mapping cocone projects back to
the textbook inclusion `u_M`. -/
theorem injectiveBiproductApproximation_app_fst
    (M : CochainComplex C ℤ) :
    injectiveBiproductApproximationApp (C := C) M ≫
        CochainComplex.mappingCocone.fst
          (cokernel.π (injective_biproduct_inclusion_app (C := C) M)) =
      injective_biproduct_inclusion_app (C := C) M := by
  -- The defining computation rule for `mappingCocone.lift` recovers the left map.
  simp [injectiveBiproductApproximationApp]

/-- Helper for Lemma 19.12.5: each comparison map `j_M : M ⟶ N(M)` is mono because its
composition with the standard projection to `J(M)` is the already-monic inclusion `u_M`. -/
theorem injectiveBiproductApproximation_app_mono
    (M : CochainComplex C ℤ) :
    Mono (injectiveBiproductApproximationApp (C := C) M) := by
  let j := injectiveBiproductApproximationApp (C := C) M
  let _ : Mono (injective_biproduct_inclusion_app (C := C) M) :=
    injective_biproduct_inclusion_app_mono (C := C) M
  have hcomp :
      j ≫ CochainComplex.mappingCocone.fst
          (cokernel.π (injective_biproduct_inclusion_app (C := C) M)) =
        injective_biproduct_inclusion_app (C := C) M := by
    -- Proof comment: `j_M` was defined by `mappingCocone.lift`, so its first projection is
    -- exactly the textbook inclusion `u_M`.
    simpa [j] using injectiveBiproductApproximation_app_fst (C := C) M
  -- Proof comment: a morphism is mono once it factors through a mono map on the right.
  simpa [j] using (show Mono j from mono_of_mono_fac hcomp)

/-- Helper for Lemma 19.12.5: the morphism on mapping cocones induced by a morphism of
complexes under the functorial quotient square. -/
noncomputable def injectiveBiproductApproximationMap
    {M N : CochainComplex C ℤ} (f : M ⟶ N) :
    CochainComplex.mappingCocone
        (cokernel.π (injective_biproduct_inclusion_app (C := C) M)) ⟶
      CochainComplex.mappingCocone
        (cokernel.π (injective_biproduct_inclusion_app (C := C) N)) :=
  (CochainComplex.mappingCone.map
      (cokernel.π (injective_biproduct_inclusion_app (C := C) M))
      (cokernel.π (injective_biproduct_inclusion_app (C := C) N))
      ((injective_biproduct_complex (C := C)).map f)
      (injectiveBiproductQuotientMap (C := C) f)
      (injectiveBiproductQuotient_projection_naturality (C := C) f))⟦(-1 : ℤ)⟧'

/-- Helper for Lemma 19.12.5: the textbook mapping-cocone construction is functorial in the
complex. -/
noncomputable def injectiveBiproductApproximationFunctor :
    CochainComplex C ℤ ⥤ CochainComplex C ℤ :=
  { obj := fun M ↦
      CochainComplex.mappingCocone
        (cokernel.π (injective_biproduct_inclusion_app (C := C) M))
    map := fun {_ _} f ↦ injectiveBiproductApproximationMap (C := C) f
    map_id := by
      intro M
      have hq :
          injectiveBiproductQuotientMap (C := C) (𝟙 M) =
            𝟙 (injectiveBiproductQuotientObj (C := C) M) := by
        -- Proof comment: compare the quotient identity map after precomposing with the cokernel
        -- projection, where the defining `cokernel.map` equation reduces to the identity square.
        apply (cancel_epi (cokernel.π (injective_biproduct_inclusion_app (C := C) M))).1
        rw [Category.comp_id, injectiveBiproductQuotient_projection_naturality]
        simp
      -- Proof comment: once the quotient identity is normalized, the owner `mappingCone.map_id`
      -- gives the identity morphism on the shifted mapping cone.
      simpa [injectiveBiproductApproximationMap, hq] using
        congrArg
          (fun k ↦ k⟦(-1 : ℤ)⟧')
          (CochainComplex.mappingCone.map_id
            (φ := cokernel.π (injective_biproduct_inclusion_app (C := C) M)))
    map_comp := by
      intro L M N f g
      -- Proof comment: rewrite the quotient map and the auxiliary complex map into composite
      -- normal form, then apply the owner composition law for `mappingCone.map`.
      simpa [injectiveBiproductApproximationMap, injectiveBiproductQuotientMap_comp,
        Category.assoc] using
        congrArg
          (fun k ↦ k⟦(-1 : ℤ)⟧')
          (CochainComplex.mappingCone.map_comp
            (φ₁ := cokernel.π (injective_biproduct_inclusion_app (C := C) L))
            (φ₂ := cokernel.π (injective_biproduct_inclusion_app (C := C) M))
            (φ₃ := cokernel.π (injective_biproduct_inclusion_app (C := C) N))
            (a := (injective_biproduct_complex (C := C)).map f)
            (b := injectiveBiproductQuotientMap (C := C) f)
            (a' := (injective_biproduct_complex (C := C)).map g)
            (b' := injectiveBiproductQuotientMap (C := C) g)
            (comm := injectiveBiproductQuotient_projection_naturality (C := C) f)
            (comm' := injectiveBiproductQuotient_projection_naturality (C := C) g)) }

/-- Helper for Lemma 19.12.5: the component of `j_M` in degree `n` factors through the visible
`J(M)^n` summand of the mapping cocone term, and that summand is injective. -/
theorem injectiveBiproductApproximation_component_factors
    (M : CochainComplex C ℤ) (n : ℤ) :
    ∃ I :
        Subobject
          ((CochainComplex.mappingCocone
            (cokernel.π (injective_biproduct_inclusion_app (C := C) M))).X n),
      Injective (I : C) ∧
        I.Factors ((injectiveBiproductApproximationApp (C := C) M).f n) := by
  let π := cokernel.π (injective_biproduct_inclusion_app (C := C) M)
  let i :
      (injective_biproduct_complex_obj (C := C) M).X n ⟶
        (CochainComplex.mappingCocone π).X n :=
    (CochainComplex.mappingCocone.inl π).v n n (add_zero n)
  have hi_mono : Mono i := by
    -- Proof comment: the visible inclusion has `mappingCocone.fst` as a right inverse in degree
    -- `n`, so it is mono.
    exact mono_of_mono_fac (CochainComplex.mappingCocone.inl_v_fst_f (φ := π) n)
  refine ⟨Subobject.mk i, ?_, ?_⟩
  · -- Proof comment: `Subobject.mk i` has the same underlying object as the visible injective
    -- summand `J(M)^n`.
    dsimp [i]
    exact
      Injective.of_iso
        (Subobject.underlyingIso
          ((CochainComplex.mappingCocone.inl π).v n n (add_zero n))).symm
        (injective_biproduct_complex_obj_term_injective (C := C) M n)
  · have hfst :
        (injectiveBiproductApproximationApp (C := C) M).f n ≫
            (CochainComplex.mappingCocone.fst π).f n =
          (injective_biproduct_inclusion_app (C := C) M).f n := by
      -- Proof comment: the first projection of `j_M` is exactly the textbook inclusion `u_M`.
      simpa [π] using
        congrArg (fun k ↦ k.f n) (injectiveBiproductApproximation_app_fst (C := C) M)
    have hsnd :
        (injectiveBiproductApproximationApp (C := C) M).f n ≫
            (CochainComplex.mappingCocone.snd π).v n (n - 1) (by omega) =
          0 := by
      -- Proof comment: the defining `(-1)`-cochain of `j_M` is zero, so the second cocone
      -- component vanishes degreewise.
      simpa [injectiveBiproductApproximationApp, π] using
        (CochainComplex.mappingCocone.lift_f_snd_v
          (φ := π)
          (α := injective_biproduct_inclusion_app (C := C) M)
          (β := (0 : Cochain M (injectiveBiproductQuotientObj (C := C) M) (-1)))
          (hαβ := by
            simpa using (cokernel.condition (injective_biproduct_inclusion_app (C := C) M)))
          n (n - 1) (by omega))
    have hid :
        (injectiveBiproductApproximationApp (C := C) M).f n ≫
            (CochainComplex.mappingCocone.fst π).f n ≫ i =
          (injectiveBiproductApproximationApp (C := C) M).f n := by
      -- Proof comment: `mappingCocone.id_X` decomposes the identity into the visible `inl`
      -- summand plus the `snd`/`inr` branch, and the latter vanishes by `hsnd`.
      simpa [i, Category.assoc, hsnd] using
        congrArg
          (fun k ↦ (injectiveBiproductApproximationApp (C := C) M).f n ≫ k)
          (CochainComplex.mappingCocone.id_X (φ := π) n (n - 1) (by omega))
    have hfactor :
        (injective_biproduct_inclusion_app (C := C) M).f n ≫ i =
          (injectiveBiproductApproximationApp (C := C) M).f n := by
      -- Proof comment: replace the first projection of `j_M` by `u_M`, then collapse the
      -- identity decomposition from `hid`.
      calc
        (injective_biproduct_inclusion_app (C := C) M).f n ≫ i =
            (injectiveBiproductApproximationApp (C := C) M).f n ≫
              (CochainComplex.mappingCocone.fst π).f n ≫ i := by
                rw [hfst]
        _ = (injectiveBiproductApproximationApp (C := C) M).f n := hid
    -- Proof comment: the visible summand therefore supplies the required subobject factorization.
    exact
      (Subobject.mk_factors_iff i
        ((injectiveBiproductApproximationApp (C := C) M).f n)).2
        ⟨(injective_biproduct_inclusion_app (C := C) M).f n, hfactor⟩

end AuxiliaryBiproductComplex

/-
Domain-style sampling for Lemma 19.12.5:
- primary domain: functorial cochain-complex approximations in a Grothendieck abelian category,
  upgraded by degreewise factorization through injective subobjects;
- sampled owner declarations:
  `FunctorialComplexApproximation`,
  `HasFunctorialInjectiveEmbeddings`,
  `hasFunctorialInjectiveEmbeddings_of_isGrothendieckAbelian`,
  `Subobject.Factors`;
- best owner abstraction: the core owner remains `FunctorialComplexApproximation C` from
  Lemma 19.12.4, while the injective-subobject factorization is derived theorem-level data about
  its degreewise comparison maps rather than a second packaged owner;
- primitive data: a functorial complex approximation;
- derived API: for each degreewise component `(J.ι.app M).f n`, an injective subobject of
  `(J.toFunctor.obj M).X n` together with the canonical factorization property
  `I.Factors ((J.ι.app M).f n)`.

Source/core/bridge triage:
- `source-facing`: the existence statement that the comparison maps factor through injective
  subobjects degreewise;
- `core/canonical`: `FunctorialComplexApproximation C`;
- `bridge/view`: the degreewise factorization witnesses for the comparison morphism.
-/

/-- Lemma 19.12.5: in a Grothendieck abelian category there exists a functorial cochain-complex
replacement `M ↦ N(M)` together with a natural map `j_M : M ⟶ N(M)` that is termwise injective
and a quasi-isomorphism, and whose degreewise components factor through injective subobjects of the
corresponding terms of `N(M)` in the canonical `Subobject.Factors` sense. -/
-- Proof sketch: apply Theorem 19.11.7 termwise to obtain functorial monomorphisms
-- `Mⁿ ⟶ I(Mⁿ)`, assemble these into the standard auxiliary complex `J(M)`, and form the shifted
-- mapping cone of the quotient map `J(M) ⟶ Q(M)`. The induced map `j_M : M ⟶ N(M)` is termwise
-- mono, each component lands in an injective subobject by construction, and the long exact
-- cohomology sequence for the defining short exact sequence gives that `j_M` is a quasi-isomorphism.
theorem exists_functorial_injective_subobject_complex_approximation
    (C : Type u) [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C] :
    ∃ J : FunctorialComplexApproximation C,
      ∀ (M : CochainComplex C ℤ) (n : ℤ),
        ∃ I : Subobject ((J.toFunctor.obj M).X n),
          Injective (I : C) ∧ I.Factors ((J.ι.app M).f n) := by
  letI : HasFunctorialInjectiveEmbeddings C :=
    CategoryTheory.hasFunctorialInjectiveEmbeddings_of_isGrothendieckAbelian
  -- The verified source-proof prefix now includes the actual endofunctor `J` and the natural
  -- inclusion `u : 𝟭 ⟶ J` from the textbook construction.
  -- Route correction: the remaining blocker is no longer the chain-map packaging; it is the
  -- functorial cokernel/mapping-cocone step and the comparison quasi-isomorphism for
  -- `M ⟶ J(M) ⟶ Q(M)`.
  let _J := injective_biproduct_complex (C := C)
  let _u := injective_biproduct_inclusion (C := C)
  -- TODO: the quotient layer is now normalized by
  -- `injectiveBiproductQuotient_projection_naturality`, and the comparison component is fixed by
  -- `injectiveBiproductApproximationApp` together with
  -- `injectiveBiproductApproximation_app_fst`. The remaining work is to package the objectwise
  -- mapping-cocone construction into a functor and compare its canonical map with
  -- `mappingCone.descShortComplex` in order to import the owner theorem
  -- `mappingCone.quasiIso_descShortComplex`.
  sorry

end CochainComplex
