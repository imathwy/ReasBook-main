import Mathlib
import StacksProject_2024.Chap10.Lemma_10_127_5
import StacksProject_2024.Chap10.Lemma_10_131_5
import StacksProject_2024.Chap10.Lemma_10_131_9
import StacksProject_2024.Chap10.Lemma_10_131_14
import StacksProject_2024.Chap10.Lemma_10_151_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits
open scoped TensorProduct

universe u v

section

/-
Domain-style sampling:
- primary domain: descent of unramified tensor-product base change along filtered colimits of
  commutative algebras;
- sampled owner declarations:
  `RingHom.FormallyUnramified`,
  `Algebra.FormallyUnramified.base_change`,
  `Algebra.FiniteType.baseChange`,
  `Algebra.Unramified`,
  `Algebra.unramified_iff_formallyUnramified_and_finiteType`;
- best owner abstraction:
  - `source-facing`: the filtered-colimit descent theorem below
  - `core/canonical`: the tensor-product base-change hom
    `Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ R)` together with the induced algebra structure on
    the target tensor product and its owner predicate `Algebra.Unramified`
  - `bridge/view`: the owner-level formally-unramified descent theorem below, which supplies the
    primitive part of the canonical unramified owner while finite type is recovered separately by
    base change
- primitive vs. derived:
  - primitive data: the filtered diagram `F`, the map `φ₀ : B₀ →ₐ[A₀] C₀`, and the formal
    unramifiedness of its colimit base-change hom
  - derived API: finite type of each base-changed hom, obtained from `hφ₀ : φ₀.FiniteType` by
    base change; the public source-facing theorem should therefore conclude in the canonical owner
    `Algebra.Unramified`, with the decomposition into formal unramifiedness and finite type kept
    only as a bridge.
-/

variable {A₀ : Type u} [CommRing A₀]
variable {J : Type v} [SmallCategory J] [IsFiltered J]
variable (F : J ⥤ CommAlgCat.{u} A₀) [HasColimit F]
variable {B₀ C₀ : Type u} [CommRing B₀] [CommRing C₀]
variable [Algebra A₀ B₀] [Algebra A₀ C₀]

/-- Helper for Lemma 10.168.5: the stage tensor-product base-change hom of a finite-type map is
again of finite type. -/
theorem tensor_base_change_hom_finiteType
    (φ₀ : B₀ →ₐ[A₀] C₀) (hφ₀ : φ₀.FiniteType) (j : J) :
    (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ ↑(F.obj j))).FiniteType := by
  letI : Algebra B₀ C₀ := φ₀.toRingHom.toAlgebra
  let S := B₀ ⊗[A₀] ↑(F.obj j)
  let e :=
    (Algebra.TensorProduct.comm (R := B₀) (A := S) (B := C₀)).toRingEquiv.trans
      (Algebra.TensorProduct.cancelBaseChange
        (R := A₀) (S := B₀) (T := C₀) (A := C₀) (B := ↑(F.obj j))).toRingEquiv
  let fbase : S →+* (S ⊗[B₀] C₀) :=
    (Algebra.TensorProduct.includeLeft : S →ₐ[B₀] (S ⊗[B₀] C₀)).toRingHom
  -- Finite type is stable under the literal base change along `B₀ → S`.
  have hbaseAlg : Algebra.FiniteType S (S ⊗[B₀] C₀) := by
    letI : Algebra.FiniteType B₀ C₀ := by
      simpa [AlgHom.FiniteType, RingHom.FiniteType] using hφ₀
    exact Algebra.FiniteType.baseChange (R := B₀) (A := C₀) (B := S)
  have hfbase : @RingHom.FiniteType S (S ⊗[B₀] C₀) inferInstance inferInstance fbase := by
    -- Package the base-changed algebra structure as the corresponding finite-type ring map.
    unfold fbase
    exact RingHom.finiteType_algebraMap.mpr hbaseAlg
  have he :
      e.toRingHom.comp fbase =
        (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ ↑(F.obj j))).toRingHom := by
    -- The standard `comm` plus `cancelBaseChange` transport rewrites the literal base change
    -- into the tensor-product map appearing in the statement.
    ext b
    · -- On the `B₀`-generator, the composite sends `b ⊗ 1` to `φ₀ b ⊗ 1`.
      change
        (Algebra.TensorProduct.cancelBaseChange
          (R := A₀) (S := B₀) (T := C₀) (A := C₀) (B := ↑(F.obj j)))
          ((Algebra.TensorProduct.comm (R := B₀) (A := S) (B := C₀))
            ((((b ⊗ₜ[A₀] (1 : ↑(F.obj j))) : S) ⊗ₜ[B₀] (1 : C₀)))) =
          φ₀ b ⊗ₜ[A₀] (1 : ↑(F.obj j))
      simp [S, Algebra.smul_def]
      simpa using
        (show (algebraMap B₀ C₀) b ⊗ₜ[A₀] (1 : ↑(F.obj j)) = φ₀ b ⊗ₜ[A₀] (1 : ↑(F.obj j)) from
          rfl)
    · -- On the stage-ring generator, the composite fixes `1 ⊗ a`.
      simpa [e, fbase, S] using
        (show
          ((e.toRingHom.comp fbase).comp Algebra.TensorProduct.includeRight.toRingHom) b =
            ((Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ ↑(F.obj j))).comp
              Algebra.TensorProduct.includeRight.toRingHom) b from
          rfl)
  have hcomp : (e.toRingHom.comp fbase).FiniteType :=
    RingHom.finiteType_respectsIso.1 _ e hfbase
  -- After rewriting the transported base-change map, this is exactly the desired finite-type
  -- statement for the tensor-product hom.
  rw [AlgHom.FiniteType]
  rw [← he]
  exact hcomp

/-- Helper for Lemma 10.168.5: if a finite family generates an algebra, then the differentials of
that family span the Kähler differentials. -/
theorem kaehler_generators_span_top_of_adjoin_eq_top
    {R : Type u} {S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    {n : ℕ} (x : Fin n → S) (hx : Algebra.adjoin R (Set.range x) = ⊤) :
    Submodule.span S (Set.range fun i : Fin n ↦ KaehlerDifferential.D R S (x i)) = ⊤ := by
  let f : MvPolynomial (Fin n) R →ₐ[R] S := MvPolynomial.aeval x
  have hsurj : Function.Surjective f := by
    -- Proof comment: the chosen family generates exactly when the corresponding polynomial
    -- evaluation map is surjective.
    rw [← AlgHom.range_eq_top, ← Algebra.adjoin_range_eq_range_aeval]
    simpa [f] using hx
  let P : Algebra.Generators R S (Fin n) := Algebra.Generators.ofAlgHom f hsurj
  have hval : P.val = x := by
    -- Proof comment: the generator family attached to `aeval x` is exactly the original family.
    ext i
    change f (MvPolynomial.X i) = x i
    simp [f]
  have himage :
      P.toExtension.toKaehler '' Set.range P.cotangentSpaceBasis =
        Set.range fun i : Fin n ↦ KaehlerDifferential.D R S (x i) := by
    -- Proof comment: the canonical cotangent basis maps to the universal differentials of the
    -- chosen generators.
    ext y
    constructor
    · rintro ⟨z, ⟨i, rfl⟩, rfl⟩
      refine ⟨i, ?_⟩
      rw [← hval]
      simp
    · rintro ⟨i, rfl⟩
      refine ⟨P.cotangentSpaceBasis i, ⟨i, rfl⟩, ?_⟩
      rw [← hval]
      simp
  have hbasis :
      Submodule.span S (Set.range P.cotangentSpaceBasis) =
        (⊤ : Submodule S P.toExtension.CotangentSpace) := by
    simpa using (Module.Basis.span_eq P.cotangentSpaceBasis)
  calc
    Submodule.span S (Set.range fun i : Fin n ↦ KaehlerDifferential.D R S (x i)) =
      Submodule.map P.toExtension.toKaehler
        (Submodule.span S (Set.range P.cotangentSpaceBasis)) := by
          rw [Submodule.map_span, himage]
    _ = Submodule.map P.toExtension.toKaehler (⊤ : Submodule S P.toExtension.CotangentSpace) := by
          rw [hbasis]
    _ = ⊤ := by
          rw [Submodule.map_top, LinearMap.range_eq_top.2 P.toExtension.toKaehler_surjective]

/-- Helper for Lemma 10.168.5: if `c` lies in the `B₀`-subalgebra generated by `x`, then the pure
tensor `c ⊗ 1` lies in the `(B₀ ⊗[A₀] R)`-subalgebra generated by the pure tensors `x i ⊗ 1`. -/
theorem tensor_base_change_pure_tensor_mem_adjoin
    (φ₀ : B₀ →ₐ[A₀] C₀) {n : ℕ} (x : Fin n → C₀)
    (R : Type u) [CommRing R] [Algebra A₀ R] {c : C₀}
    (hc :
      letI : Algebra B₀ C₀ := φ₀.toRingHom.toAlgebra
      c ∈ Algebra.adjoin B₀ (Set.range x)) :
    letI : Algebra (B₀ ⊗[A₀] R) (C₀ ⊗[A₀] R) :=
      (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ R)).toRingHom.toAlgebra
    c ⊗ₜ[A₀] (1 : R) ∈
      Algebra.adjoin (B₀ ⊗[A₀] R)
        (Set.range fun i : Fin n ↦ x i ⊗ₜ[A₀] (1 : R)) := by
  letI : Algebra B₀ C₀ := φ₀.toRingHom.toAlgebra
  let S := B₀ ⊗[A₀] R
  letI : Algebra S (C₀ ⊗[A₀] R) :=
    (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ R)).toRingHom.toAlgebra
  -- Proof comment: build `c ⊗ 1` inside the tensor-base-change adjoin by induction on the
  -- original proof that `c` lies in the `B₀`-adjoin of the family `x`.
  refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ hc
  · intro y hy
    rcases hy with ⟨i, rfl⟩
    exact Algebra.subset_adjoin ⟨i, rfl⟩
  · intro b
    -- Proof comment: coefficients from `B₀` become scalars coming from the base algebra
    -- `B₀ ⊗[A₀] R`.
    change algebraMap S (C₀ ⊗[A₀] R) ((b : B₀) ⊗ₜ[A₀] (1 : R)) ∈
      Algebra.adjoin S (Set.range fun i : Fin n ↦ x i ⊗ₜ[A₀] (1 : R))
    exact Subalgebra.algebraMap_mem _ _
  · intro y z _ _ hy hz
    simpa [TensorProduct.add_tmul] using Subalgebra.add_mem
      (Algebra.adjoin S (Set.range fun i : Fin n ↦ x i ⊗ₜ[A₀] (1 : R))) hy hz
  · intro y z _ _ hy hz
    simpa [Algebra.TensorProduct.tmul_mul_tmul] using
      Subalgebra.mul_mem
        (Algebra.adjoin S (Set.range fun i : Fin n ↦ x i ⊗ₜ[A₀] (1 : R))) hy hz

/-- Helper for Lemma 10.168.5: the pure tensors `x i ⊗ 1` still generate the base-changed target
algebra over `B₀ ⊗[A₀] R`. -/
theorem tensor_base_change_comm_cancel_adjoin_eq_top
    (φ₀ : B₀ →ₐ[A₀] C₀) {n : ℕ} (x : Fin n → C₀)
    (hx :
      letI : Algebra B₀ C₀ := φ₀.toRingHom.toAlgebra
      Algebra.adjoin B₀ (Set.range x) = ⊤)
    (R : Type u) [CommRing R] [Algebra A₀ R] :
    letI : Algebra (B₀ ⊗[A₀] R) (C₀ ⊗[A₀] R) :=
      (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ R)).toRingHom.toAlgebra
    Algebra.adjoin (B₀ ⊗[A₀] R)
      (Set.range fun i : Fin n ↦ x i ⊗ₜ[A₀] (1 : R)) = ⊤ := by
  letI : Algebra B₀ C₀ := φ₀.toRingHom.toAlgebra
  let S := B₀ ⊗[A₀] R
  letI : Algebra S (C₀ ⊗[A₀] R) :=
    (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ R)).toRingHom.toAlgebra
  apply top_unique
  intro z hz
  -- Proof comment: every element of the tensor product is built from pure tensors, and each pure
  -- tensor `c ⊗ r` is a scalar multiple of the already-controlled tensor `c ⊗ 1`.
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · exact Subalgebra.zero_mem _ 
  · intro c r
    have hc : c ∈ Algebra.adjoin B₀ (Set.range x) := by
      simpa [hx] using (show c ∈ (⊤ : Subalgebra B₀ C₀) from trivial)
    have hc' :
        c ⊗ₜ[A₀] (1 : R) ∈
          Algebra.adjoin S (Set.range fun i : Fin n ↦ x i ⊗ₜ[A₀] (1 : R)) :=
      tensor_base_change_pure_tensor_mem_adjoin (φ₀ := φ₀) x R hc
    have hs :
        algebraMap S (C₀ ⊗[A₀] R) ((1 : B₀) ⊗ₜ[A₀] r) ∈
          Algebra.adjoin S (Set.range fun i : Fin n ↦ x i ⊗ₜ[A₀] (1 : R)) :=
      Subalgebra.algebraMap_mem _ _
    have hmul :
        algebraMap S (C₀ ⊗[A₀] R) ((1 : B₀) ⊗ₜ[A₀] r) * (c ⊗ₜ[A₀] (1 : R)) ∈
          Algebra.adjoin S (Set.range fun i : Fin n ↦ x i ⊗ₜ[A₀] (1 : R)) :=
      Subalgebra.mul_mem _ hs hc'
    have hEq :
        algebraMap S (C₀ ⊗[A₀] R) ((1 : B₀) ⊗ₜ[A₀] r) * (c ⊗ₜ[A₀] (1 : R)) =
          c ⊗ₜ[A₀] r := by
      change
        (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ R)) ((1 : B₀) ⊗ₜ[A₀] r) *
            (c ⊗ₜ[A₀] (1 : R)) =
          c ⊗ₜ[A₀] r
      rw [Algebra.TensorProduct.map_tmul]
      simp [Algebra.TensorProduct.tmul_mul_tmul]
    rw [hEq] at hmul
    exact hmul
  · intro z₁ z₂ hz₁ hz₂
    exact Subalgebra.add_mem _ hz₁ hz₂

/-- Helper for Lemma 10.168.5: the same finite generating family still spans the Kähler
differentials after tensoring with any `A₀`-algebra. -/
theorem tensor_base_change_kaehler_generators_span_top
    (φ₀ : B₀ →ₐ[A₀] C₀) {n : ℕ} (x : Fin n → C₀)
    (hx :
      letI : Algebra B₀ C₀ := φ₀.toRingHom.toAlgebra
      Algebra.adjoin B₀ (Set.range x) = ⊤)
    (R : Type u) [CommRing R] [Algebra A₀ R] :
    letI : Algebra (B₀ ⊗[A₀] R) (C₀ ⊗[A₀] R) :=
      (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ R)).toRingHom.toAlgebra
    Submodule.span (C₀ ⊗[A₀] R)
      (Set.range fun i : Fin n ↦
        KaehlerDifferential.D (B₀ ⊗[A₀] R) (C₀ ⊗[A₀] R) (x i ⊗ₜ[A₀] (1 : R))) = ⊤ := by
  letI : Algebra (B₀ ⊗[A₀] R) (C₀ ⊗[A₀] R) :=
    (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ R)).toRingHom.toAlgebra
  -- Proof comment: once the pure tensors still generate the base-changed algebra, the standard
  -- finite-generation statement for Kähler differentials applies verbatim.
  simpa using
    kaehler_generators_span_top_of_adjoin_eq_top
      (R := B₀ ⊗[A₀] R) (S := C₀ ⊗[A₀] R)
      (x := fun i : Fin n ↦ x i ⊗ₜ[A₀] (1 : R))
      (tensor_base_change_comm_cancel_adjoin_eq_top (φ₀ := φ₀) x hx R)

/-- Helper for Lemma 10.168.5: formal unramifiedness of the tensor-base-changed map makes the
target Kähler differential module a subsingleton. -/
theorem tensor_base_change_subsingleton_kaehlerDifferential
    (φ₀ : B₀ →ₐ[A₀] C₀)
    (R : Type u) [CommRing R] [Algebra A₀ R]
    (hfu : (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ R)).FormallyUnramified) :
    letI : Algebra (B₀ ⊗[A₀] R) (C₀ ⊗[A₀] R) :=
      (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ R)).toRingHom.toAlgebra
    Subsingleton (KaehlerDifferential (B₀ ⊗[A₀] R) (C₀ ⊗[A₀] R)) := by
  letI : Algebra (B₀ ⊗[A₀] R) (C₀ ⊗[A₀] R) :=
    (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ R)).toRingHom.toAlgebra
  letI : Algebra.FormallyUnramified (B₀ ⊗[A₀] R) (C₀ ⊗[A₀] R) := hfu
  -- Proof comment: this is exactly the canonical `FormallyUnramified` owner instance on
  -- Kähler differentials.
  infer_instance

/-- Helper for Lemma 10.168.5: under formal unramifiedness after tensor base change, every
distinguished differential `d(x ⊗ 1)` vanishes in the target Kähler differential module. -/
theorem tensor_base_change_D_tmul_one_eq_zero
    (φ₀ : B₀ →ₐ[A₀] C₀)
    (R : Type u) [CommRing R] [Algebra A₀ R]
    (hfu : (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ R)).FormallyUnramified)
    (x : C₀) :
    letI : Algebra (B₀ ⊗[A₀] R) (C₀ ⊗[A₀] R) :=
      (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ R)).toRingHom.toAlgebra
    KaehlerDifferential.D (B₀ ⊗[A₀] R) (C₀ ⊗[A₀] R) (x ⊗ₜ[A₀] (1 : R)) = 0 := by
  -- Proof comment: once the target differential module is subsingleton, every generator equals
  -- `0`.
  let hsub :=
    tensor_base_change_subsingleton_kaehlerDifferential (φ₀ := φ₀) R hfu
  exact @Subsingleton.elim _ hsub _ _

/-- Helper for Lemma 10.168.5: forgetting a filtered colimit cocone of `A₀`-algebras to
`CommRingCat` preserves its colimit property. -/
noncomputable def commAlg_forget_commRing_mapCocone_isColimit
    {I : Type v} [SmallCategory I] [IsFiltered I]
    (G : I ⥤ CommAlgCat.{u} A₀) (c : ColimitCocone G) :
    IsColimit ((forget₂ (CommAlgCat.{u} A₀) CommRingCat).mapCocone c.cocone) := by
  let E := commAlgCatEquivUnder (CommRingCat.of A₀)
  have hUnder : IsColimit (E.functor.mapCocone c.cocone) := by
    -- Proof comment: transport the colimit cocone across the standard equivalence
    -- `CommAlgCat A₀ ≌ Under (CommRingCat.of A₀)`.
    exact isColimitOfPreserves E.functor c.isColimit
  -- Proof comment: the forgetful functor from the under-category preserves filtered colimits, so
  -- the underlying commutative-ring cocone is still colimiting.
  simpa [E, commAlgCatEquivUnder] using
    (isColimitOfPreserves (CategoryTheory.Under.forget (CommRingCat.of A₀)) hUnder)

/-- Helper for Lemma 10.168.5: the base-changed stage rings are obtained by pushing out the
diagram of `A₀`-algebras along `A₀ → R₀` and then forgetting to `CommRingCat`. -/
noncomputable abbrev tensor_base_change_underlying_cocone
    {I : Type v} [SmallCategory I] [IsFiltered I]
    (G : I ⥤ CommAlgCat.{u} A₀) (c : ColimitCocone G)
    (R₀ : Type u) [CommRing R₀] [Algebra A₀ R₀] :
    Cocone
      (G ⋙ (commAlgCatEquivUnder (CommRingCat.of A₀)).functor ⋙
        Under.pushout (CommRingCat.ofHom (algebraMap A₀ R₀)) ⋙
        CategoryTheory.Under.forget (CommRingCat.of R₀)) :=
  ((CategoryTheory.Under.forget (CommRingCat.of R₀)).mapCocone
    ((Under.pushout (CommRingCat.ofHom (algebraMap A₀ R₀))).mapCocone
      ((commAlgCatEquivUnder (CommRingCat.of A₀)).functor.mapCocone c.cocone)))

/-- Helper for Lemma 10.168.5: after base change along `A₀ → R₀`, the resulting cocone of stage
rings remains colimiting after forgetting to `CommRingCat`. -/
noncomputable def tensor_base_change_underlying_cocone_isColimit
    {I : Type v} [SmallCategory I] [IsFiltered I]
    (G : I ⥤ CommAlgCat.{u} A₀) (c : ColimitCocone G)
    (R₀ : Type u) [CommRing R₀] [Algebra A₀ R₀] :
    IsColimit (tensor_base_change_underlying_cocone (A₀ := A₀) G c R₀) := by
  let E := commAlgCatEquivUnder (CommRingCat.of A₀)
  let P := Under.pushout (CommRingCat.ofHom (algebraMap A₀ R₀))
  have hUnder : IsColimit (E.functor.mapCocone c.cocone) := by
    -- Proof comment: first move the colimit cocone for `G` into the under-category over `A₀`.
    exact isColimitOfPreserves E.functor c.isColimit
  have hPush : IsColimit (P.mapCocone (E.functor.mapCocone c.cocone)) := by
    -- Proof comment: pushout in the under-category is a left adjoint, hence preserves colimits.
    exact isColimitOfPreserves P hUnder
  -- Proof comment: the forgetful functor from `Under (CommRingCat.of R₀)` preserves filtered
  -- colimits, so the base-changed cocone of underlying rings is colimiting.
  simpa [tensor_base_change_underlying_cocone, P, E, commAlgCatEquivUnder] using
    (isColimitOfPreserves (CategoryTheory.Under.forget (CommRingCat.of R₀)) hPush)

/-- Helper for Lemma 10.168.5: the underlying stage rings of a directed diagram of `A₀`-algebras
form a directed system under the transition ring maps. -/
theorem directed_commAlg_underlying_directedSystem
    {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (G : I ⥤ CommAlgCat.{u} A₀) (c : ColimitCocone G) :
    DirectedSystem
      (fun i ↦ ↑(G.obj i))
      (fun i j h ↦ (G.map (homOfLE h)).hom) := by
  let A : I → Type u := fun i ↦ ↑(G.obj i)
  let ρ : ∀ i j, i ≤ j → A i →+* A j := fun i j h ↦ (G.map (homOfLE h)).hom
  refine
    { map_self := ?_
      map_map := ?_ }
  · intro i x
    -- Proof comment: the transition map along the identity morphism is the identity by
    -- functoriality of `G`.
    change ((G.map (𝟙 i)).hom) x = x
    simpa using congrArg (fun f : G.obj i ⟶ G.obj i ↦ f x) (G.map_id i)
  · intro k j i hij hjk x
    -- Proof comment: composing two transition maps agrees with the transition along the composite
    -- order relation because `G` is a functor on the preorder category.
    change ((G.map (homOfLE hjk)).hom) (((G.map (homOfLE hij)).hom) x) =
      ((G.map (homOfLE (hij.trans hjk))).hom) x
    simpa using
      congrArg (fun f : G.obj i ⟶ G.obj k ↦ f x)
        (G.map_comp (homOfLE hij) (homOfLE hjk)).symm

/-- Helper for Lemma 10.168.5: the `CommRingCat` universe-lift functor preserves identities on
the nose after applying `RingHom.ulift`. -/
lemma entry_commRingCat_uliftFunctor_map_id (R : CommRingCat.{u}) :
    CommRingCat.ofHom
        (RingHom.ulift (RingHom.id R) : ULift.{v} R →+* ULift.{v} R) =
      𝟙 (CommRingCat.of (ULift.{v} R)) := by
  -- Proof comment: on elements, the lifted identity is literally the identity function.
  ext x
  simp [RingHom.ulift_apply]

/-- Helper for Lemma 10.168.5: the `CommRingCat` universe-lift functor sends compositions to
compositions after applying `RingHom.ulift`. -/
lemma entry_commRingCat_uliftFunctor_map_comp
    {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) :
    CommRingCat.ofHom
        (RingHom.ulift (g.hom.comp f.hom) : ULift.{v} R →+* ULift.{v} T) =
      CommRingCat.ofHom
          (RingHom.ulift f.hom : ULift.{v} R →+* ULift.{v} S) ≫
        CommRingCat.ofHom
          (RingHom.ulift g.hom : ULift.{v} S →+* ULift.{v} T) := by
  -- Proof comment: both composites act by `x ↦ ULift.up (g (f x.down))`.
  ext x
  simp [RingHom.ulift_apply]

/-- Helper for Lemma 10.168.5: the literal universe-lift functor on `CommRingCat` needed for the
explicit direct-limit cocone. -/
abbrev entry_commRingCat_uliftFunctor : CommRingCat.{u} ⥤ CommRingCat.{max u v} where
  obj R := CommRingCat.of (ULift.{v} R)
  map f := CommRingCat.ofHom (RingHom.ulift f.hom)
  map_id := entry_commRingCat_uliftFunctor_map_id
  map_comp := entry_commRingCat_uliftFunctor_map_comp

/-- Helper for Lemma 10.168.5: the universe-safe ring diagram for a directed system of
`A₀`-algebras is obtained by forgetting to `CommRingCat` and then applying the chapter's
`CommRingCat` universe-lift functor. -/
abbrev directed_commAlg_toULiftCommRing
    {I : Type v} [Preorder I]
    (G : I ⥤ CommAlgCat.{u} A₀) :
    I ⥤ CommRingCat.{max u v} :=
  G ⋙ forget₂ (CommAlgCat.{u} A₀) CommRingCat ⋙ entry_commRingCat_uliftFunctor

/-- Helper for Lemma 10.168.5: on an order morphism, the lifted ring diagram uses the universe
lift of the underlying transition ring hom. -/
@[simp]
theorem directed_commAlg_toULiftCommRing_map_homOfLE
    {I : Type v} [Preorder I]
    (G : I ⥤ CommAlgCat.{u} A₀) {i j : I} (h : i ≤ j) :
    (directed_commAlg_toULiftCommRing (A₀ := A₀) G).map (homOfLE h) =
      CommRingCat.ofHom
        ((RingHom.ulift (G.map (homOfLE h)).hom) :
          ULift.{v} ↑(G.obj i) →+* ULift.{v} ↑(G.obj j)) := by
  rfl

/-- Helper for Lemma 10.168.5: the explicit ring direct limit of a directed system of
`A₀`-algebras carries the tautological cocone in `CommRingCat`. -/
noncomputable def directed_commRing_directLimitCocone
    {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (G : I ⥤ CommAlgCat.{u} A₀) :
    Cocone (directed_commAlg_toULiftCommRing (A₀ := A₀) G) where
  pt := CommRingCat.of <|
    ULift.{v} <|
      Ring.DirectLimit
      (fun i ↦ ↑(G.obj i))
      (fun i j h ↦ (G.map (homOfLE h)).hom)
  ι :=
    { app := fun i ↦
        CommRingCat.ofHom <|
          ((RingHom.ulift <|
            Ring.DirectLimit.of
              (fun i ↦ ↑(G.obj i))
              (fun i j h ↦ (G.map (homOfLE h)).hom) i) :
            ULift.{v} ↑(G.obj i) →+*
              ULift.{v}
                (Ring.DirectLimit
                  (fun i ↦ ↑(G.obj i))
                  (fun i j h ↦ (G.map (homOfLE h)).hom)))
      naturality := by
        intro i j f
        -- Proof comment: the direct-limit structure maps satisfy the directed-system relation
        -- `of_j ∘ f_ij = of_i`, and `RingHom.ulift` preserves that identity on the nose.
        apply CommRingCat.hom_ext
        ext x
        cases x using ULift.casesOn
        rename_i x
        change
          ULift.up
              ((Ring.DirectLimit.of
                  (fun i ↦ ↑(G.obj i))
                  (fun i j h ↦ (G.map (homOfLE h)).hom) j)
                (((G.map f).hom) x)) =
            ULift.up
              ((Ring.DirectLimit.of
                  (fun i ↦ ↑(G.obj i))
                  (fun i j h ↦ (G.map (homOfLE h)).hom) i) x)
        exact congrArg ULift.up <|
          by
            simpa only [homOfLE_leOfHom] using
              (Ring.DirectLimit.of_f
                (G := fun i ↦ ↑(G.obj i))
                (f := fun i j h ↦ (G.map (homOfLE h)).hom)
                (leOfHom f) x) }

/-- Helper for Lemma 10.168.5: the explicit `ULift`ed `Ring.DirectLimit` cocone is already a
colimit cocone in `CommRingCat`. -/
noncomputable def directed_commRing_directLimitCocone_isColimit
    {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (G : I ⥤ CommAlgCat.{u} A₀) :
    IsColimit (directed_commRing_directLimitCocone (A₀ := A₀) G) := by
  classical
  let descAux :
      ∀ s : Cocone (directed_commAlg_toULiftCommRing (A₀ := A₀) G),
        Ring.DirectLimit
            (fun i ↦ ↑(G.obj i))
            (fun i j h ↦ (G.map (homOfLE h)).hom) →+* ↑s.pt :=
    fun s ↦
      Ring.DirectLimit.lift
        (fun i ↦ ↑(G.obj i))
        (fun i j h ↦ (G.map (homOfLE h)).hom)
        ↑s.pt
        (fun i ↦ (s.ι.app i).hom.comp
          (ULift.ringEquiv.symm : ↑(G.obj i) ≃+* ULift.{v} ↑(G.obj i)).toRingHom)
        (fun i j h x ↦ by
          -- Proof comment: cocone naturality on the lifted stage `ULift.up x` is exactly the
          -- compatibility relation needed by `Ring.DirectLimit.lift`.
          have hs :
              (((directed_commAlg_toULiftCommRing (A₀ := A₀) G).map (homOfLE h)) ≫
                  s.ι.app j).hom (ULift.up x) =
                (s.ι.app i).hom (ULift.up x) := by
            simpa using congrArg
              (fun f : (directed_commAlg_toULiftCommRing (A₀ := A₀) G).obj i ⟶ s.pt ↦
                f.hom (ULift.up x))
              (s.w (homOfLE h))
          simpa [directed_commAlg_toULiftCommRing_map_homOfLE, RingHom.comp_apply,
            RingHom.ulift_apply] using hs)
  refine
    { desc := fun s ↦
        CommRingCat.ofHom ((descAux s).comp
          (ULift.ringEquiv : ULift.{v}
            (Ring.DirectLimit
              (fun i ↦ ↑(G.obj i))
              (fun i j h ↦ (G.map (homOfLE h)).hom)) ≃+*
                Ring.DirectLimit
                  (fun i ↦ ↑(G.obj i))
                  (fun i j h ↦ (G.map (homOfLE h)).hom)).toRingHom)
      fac := ?_
      uniq := ?_ }
  · intro s i
    apply CommRingCat.hom_ext
    ext x
    cases x using ULift.casesOn
    rename_i x
    change
      (descAux s)
          (Ring.DirectLimit.of
            (fun i ↦ ↑(G.obj i))
            (fun i j h ↦ (G.map (homOfLE h)).hom)
            i x) =
        (s.ι.app i).hom (ULift.up x)
    simp only [descAux, RingHom.comp_apply, Ring.DirectLimit.lift_of]
    rfl
  · intro s m hm
    apply CommRingCat.hom_ext
    ext x
    cases x using ULift.casesOn
    rename_i x
    induction x using Ring.DirectLimit.induction_on with
    | ih i x =>
        -- Proof comment: every direct-limit class is represented at some stage, and the cocone
        -- relation fixes the value of any candidate desc map on that representative.
        have hm' :
            (((directed_commRing_directLimitCocone (A₀ := A₀) G).ι.app i) ≫ m).hom
                (ULift.up x) =
              (s.ι.app i).hom (ULift.up x) := by
          simpa using congrArg
            (fun f : (directed_commAlg_toULiftCommRing (A₀ := A₀) G).obj i ⟶ s.pt ↦
              f.hom (ULift.up x))
            (hm i)
        change
          (m.hom)
              (ULift.up
                (Ring.DirectLimit.of
                  (fun i ↦ ↑(G.obj i))
                  (fun i j h ↦ (G.map (homOfLE h)).hom)
                  i x)) =
            (descAux s)
              (Ring.DirectLimit.of
                (fun i ↦ ↑(G.obj i))
                (fun i j h ↦ (G.map (homOfLE h)).hom)
                i x)
        simpa [descAux, Ring.DirectLimit.lift_of] using hm'

/-- Helper for Lemma 10.168.5: the stage maps from the explicit ring direct limit to the cocone
point agree with the given cocone legs. -/
theorem directed_commAlg_ringDirectLimit_leg_compatible
    {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (G : I ⥤ CommAlgCat.{u} A₀) (c : ColimitCocone G)
    {i j : I} (h : i ≤ j) :
    ((c.cocone.ι.app j).hom.toRingHom : G.obj j →+* c.cocone.pt).comp
        (G.map (homOfLE h)).hom.toRingHom =
      (c.cocone.ι.app i).hom.toRingHom := by
  -- Proof comment: this is exactly the cocone naturality relation, read on the underlying ring
  -- homomorphisms.
  exact congrArg (fun f : G.obj i ⟶ c.cocone.pt ↦ f.hom.toRingHom) (c.cocone.w (homOfLE h))

/-- Helper for Lemma 10.168.5: the explicit ring direct limit maps canonically to the chosen
colimit point by the cocone legs. -/
noncomputable def directed_commAlg_ringDirectLimitToCoconePoint
    {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (G : I ⥤ CommAlgCat.{u} A₀) (c : ColimitCocone G) :
    Ring.DirectLimit
        (fun i ↦ ↑(G.obj i))
        (fun i j h ↦ (G.map (homOfLE h)).hom) →+* ↑c.cocone.pt :=
  Ring.DirectLimit.lift
    (fun i ↦ ↑(G.obj i))
    (fun i j h ↦ (G.map (homOfLE h)).hom)
    ↑c.cocone.pt
    (fun i ↦ (c.cocone.ι.app i).hom.toRingHom)
    (fun _ _ h x ↦
      DFunLike.congr_fun (directed_commAlg_ringDirectLimit_leg_compatible (G := G) (c := c) h) x)

/-- Helper for Lemma 10.168.5: the canonical map from the explicit ring direct limit to the
cocone point agrees with the stage cocone legs. -/
theorem directed_commAlg_ringDirectLimitToCoconePoint_comp_of
    {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (G : I ⥤ CommAlgCat.{u} A₀) (c : ColimitCocone G) (i : I) :
    (directed_commAlg_ringDirectLimitToCoconePoint (G := G) c).comp
        (Ring.DirectLimit.of
          (fun i ↦ ↑(G.obj i))
          (fun i j h ↦ (G.map (homOfLE h)).hom) i) =
      (c.cocone.ι.app i).hom.toRingHom := by
  -- Proof comment: evaluate the direct-limit lift on the class of a stage element.
  ext x
  simp [directed_commAlg_ringDirectLimitToCoconePoint, RingHom.comp_apply, Ring.DirectLimit.lift_of]

/-- Helper for Lemma 10.168.5: the explicit ring direct limit of a directed diagram of
`A₀`-algebras. -/
abbrev directed_commAlg_ringDirectLimit
    {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (G : I ⥤ CommAlgCat.{u} A₀) :=
  Ring.DirectLimit
    (fun i ↦ ↑(G.obj i))
    (fun i j h ↦ (G.map (homOfLE h)).hom)

/-- Helper for Lemma 10.168.5: the explicit ring direct limit carries the canonical `A₀`-algebra
structure induced from an arbitrary stage. -/
@[reducible]
noncomputable instance directed_commAlg_ringDirectLimitAlgebra
    {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (G : I ⥤ CommAlgCat.{u} A₀) :
    Algebra A₀ (directed_commAlg_ringDirectLimit (A₀ := A₀) G) :=
  let i : I := Classical.arbitrary I
  ((Ring.DirectLimit.of
      (fun i ↦ ↑(G.obj i))
      (fun i j h ↦ (G.map (homOfLE h)).hom)
      i).comp
    (algebraMap A₀ ↑(G.obj i))).toAlgebra

/-- Helper for Lemma 10.168.5: the canonical algebra map into the explicit ring direct limit agrees
with the map induced from any fixed stage. -/
theorem directed_ringDirectLimit_algebraMap_eq_of
    {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (G : I ⥤ CommAlgCat.{u} A₀) (i : I) (a : A₀) :
    algebraMap A₀ (directed_commAlg_ringDirectLimit (A₀ := A₀) G) a =
      Ring.DirectLimit.of
        (fun i ↦ ↑(G.obj i))
        (fun i j h ↦ (G.map (homOfLE h)).hom)
        i (algebraMap A₀ ↑(G.obj i) a) := by
  classical
  let i₀ : I := Classical.arbitrary I
  obtain ⟨j, hi₀j, hij⟩ := exists_ge_ge i₀ i
  change
    Ring.DirectLimit.of
        (fun i ↦ ↑(G.obj i))
        (fun i j h ↦ (G.map (homOfLE h)).hom)
        i₀ (algebraMap A₀ ↑(G.obj i₀) a) =
      Ring.DirectLimit.of
        (fun i ↦ ↑(G.obj i))
        (fun i j h ↦ (G.map (homOfLE h)).hom)
        i (algebraMap A₀ ↑(G.obj i) a)
  calc
    Ring.DirectLimit.of
        (fun i ↦ ↑(G.obj i))
        (fun i j h ↦ (G.map (homOfLE h)).hom)
        i₀ (algebraMap A₀ ↑(G.obj i₀) a) =
      Ring.DirectLimit.of
        (fun i ↦ ↑(G.obj i))
        (fun i j h ↦ (G.map (homOfLE h)).hom)
        j (((G.map (homOfLE hi₀j)).hom) (algebraMap A₀ ↑(G.obj i₀) a)) := by
          symm
          exact Ring.DirectLimit.of_f
            (G := fun i ↦ ↑(G.obj i))
            (f := fun i j h ↦ (G.map (homOfLE h)).hom)
            (i := i₀) (j := j) (hij := hi₀j) (x := algebraMap A₀ ↑(G.obj i₀) a)
    _ =
      Ring.DirectLimit.of
        (fun i ↦ ↑(G.obj i))
        (fun i j h ↦ (G.map (homOfLE h)).hom)
        j (algebraMap A₀ ↑(G.obj j) a) := by
          rw [(G.map (homOfLE hi₀j)).hom.commutes]
    _ =
      Ring.DirectLimit.of
        (fun i ↦ ↑(G.obj i))
        (fun i j h ↦ (G.map (homOfLE h)).hom)
        j (((G.map (homOfLE hij)).hom) (algebraMap A₀ ↑(G.obj i) a)) := by
          rw [← (G.map (homOfLE hij)).hom.commutes]
    _ =
      Ring.DirectLimit.of
        (fun i ↦ ↑(G.obj i))
        (fun i j h ↦ (G.map (homOfLE h)).hom)
        i (algebraMap A₀ ↑(G.obj i) a) := by
          exact Ring.DirectLimit.of_f
            (G := fun i ↦ ↑(G.obj i))
            (f := fun i j h ↦ (G.map (homOfLE h)).hom)
            (i := i) (j := j) (hij := hij) (x := algebraMap A₀ ↑(G.obj i) a)

/-- Helper for Lemma 10.168.5: each stage maps canonically to the explicit ring direct limit as an
`A₀`-algebra. -/
noncomputable abbrev directed_commAlg_stageToRingDirectLimitAlgHom
    {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (G : I ⥤ CommAlgCat.{u} A₀) (i : I) :
    ↑(G.obj i) →ₐ[A₀] directed_commAlg_ringDirectLimit (A₀ := A₀) G :=
  { toRingHom :=
      Ring.DirectLimit.of
        (fun i ↦ ↑(G.obj i))
        (fun i j h ↦ (G.map (homOfLE h)).hom)
        i
    commutes' := fun a ↦ (directed_ringDirectLimit_algebraMap_eq_of (A₀ := A₀) G i a).symm }

/-- Helper for Lemma 10.168.5: the canonical map from the explicit ring direct limit to the cocone
point is an `A₀`-algebra map. -/
noncomputable abbrev directed_commAlg_ringDirectLimitToCoconePointAlgHom
    {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (G : I ⥤ CommAlgCat.{u} A₀) (c : ColimitCocone G) :
    directed_commAlg_ringDirectLimit (A₀ := A₀) G →ₐ[A₀] ↑c.cocone.pt :=
  { toRingHom := directed_commAlg_ringDirectLimitToCoconePoint (A₀ := A₀) G c
    commutes' := fun a ↦ by
      classical
      let i : I := Classical.arbitrary I
      have hstage :
          directed_commAlg_ringDirectLimitToCoconePoint (A₀ := A₀) G c
              (algebraMap A₀ (directed_commAlg_ringDirectLimit (A₀ := A₀) G) a) =
            (c.cocone.ι.app i).hom (algebraMap A₀ ↑(G.obj i) a) := by
        rw [directed_ringDirectLimit_algebraMap_eq_of (A₀ := A₀) G i]
        simpa [RingHom.comp_apply] using congrArg
          (fun f : ↑(G.obj i) →+* ↑c.cocone.pt ↦
            f (algebraMap A₀ ↑(G.obj i) a))
          (directed_commAlg_ringDirectLimitToCoconePoint_comp_of (A₀ := A₀) G c i)
      exact hstage.trans <| by
        simpa using (c.cocone.ι.app i).hom.commutes a }

/-- Helper for Lemma 10.168.5: the canonical map from the explicit ring direct limit to the chosen
cocone point agrees with the given cocone leg on every stage class. -/
theorem directed_commAlg_ringDirectLimitToCoconePointAlgHom_comp_of
    {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (G : I ⥤ CommAlgCat.{u} A₀) (c : ColimitCocone G) (i : I) (x : ↑(G.obj i)) :
    directed_commAlg_ringDirectLimitToCoconePointAlgHom (A₀ := A₀) G c
        (Ring.DirectLimit.of
          (fun i ↦ ↑(G.obj i))
          (fun i j h ↦ (G.map (homOfLE h)).hom)
          i x) =
      (c.cocone.ι.app i).hom x := by
  -- Proof comment: evaluate the direct-limit lift on the class represented at stage `i`.
  exact congrArg (fun f : _ →+* ↑c.cocone.pt ↦ f x)
    (directed_commAlg_ringDirectLimitToCoconePoint_comp_of (A₀ := A₀) G c i)

/- Helper for Lemma 10.168.5: if the distinguished differentials of a finite generating family
span the stage Kähler differential module and all vanish, then the stage map is formally
unramified. -/
theorem tensor_base_change_formallyUnramified_of_generator_zero
    (φ₀ : B₀ →ₐ[A₀] C₀) {n : ℕ} (x : Fin n → C₀)
    (hx :
      letI : Algebra B₀ C₀ := φ₀.toRingHom.toAlgebra
      Algebra.adjoin B₀ (Set.range x) = ⊤)
    (R : Type u) [CommRing R] [Algebra A₀ R]
    (hz :
      ∀ k : Fin n,
        letI : Algebra (B₀ ⊗[A₀] R) (C₀ ⊗[A₀] R) :=
          (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ R)).toRingHom.toAlgebra
        KaehlerDifferential.D (B₀ ⊗[A₀] R) (C₀ ⊗[A₀] R) (x k ⊗ₜ[A₀] (1 : R)) = 0) :
    (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ R)).FormallyUnramified := by
  letI : Algebra (B₀ ⊗[A₀] R) (C₀ ⊗[A₀] R) :=
    (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ R)).toRingHom.toAlgebra
  let Ω := KaehlerDifferential (B₀ ⊗[A₀] R) (C₀ ⊗[A₀] R)
  have hspan :
      Submodule.span (C₀ ⊗[A₀] R)
        (Set.range fun i : Fin n ↦
          KaehlerDifferential.D (B₀ ⊗[A₀] R) (C₀ ⊗[A₀] R) (x i ⊗ₜ[A₀] (1 : R))) = ⊤ :=
    tensor_base_change_kaehler_generators_span_top (φ₀ := φ₀) x hx R
  have hzero_all : ∀ z : Ω, z = 0 := by
    intro z
    have hzmem :
        z ∈ Submodule.span (C₀ ⊗[A₀] R)
          (Set.range fun i : Fin n ↦
            KaehlerDifferential.D (B₀ ⊗[A₀] R) (C₀ ⊗[A₀] R) (x i ⊗ₜ[A₀] (1 : R))) := by
      simpa [hspan] using (show z ∈ (⊤ : Submodule (C₀ ⊗[A₀] R) Ω) from trivial)
    -- Proof comment: span induction reduces every differential to the chosen vanishing family.
    refine Submodule.span_induction (p := fun y _ ↦ y = 0) ?_ ?_ ?_ ?_ hzmem
    · intro y hy
      rcases hy with ⟨i, rfl⟩
      exact hz i
    · simp
    · intro y z _ _ hy hz'
      rw [hy, hz', add_zero]
    · intro a y _ hy
      rw [hy, smul_zero]
  -- Proof comment: `Ω = 0` is exactly the Kähler criterion for formal unramifiedness.
  refine (Algebra.formallyUnramified_iff (B₀ ⊗[A₀] R) (C₀ ⊗[A₀] R)).2 ?_
  exact ⟨fun y z ↦ (hzero_all y).trans (hzero_all z).symm⟩

/-- Helper for Lemma 10.168.5: a finite family of indices in a directed preorder has a common
upper bound. -/
theorem directed_finset_common_upper_bound
    {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (s : Finset I) :
    ∃ i : I, ∀ j ∈ s, j ≤ i := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨Classical.arbitrary I, ?_⟩
      intro j hj
      exact False.elim (Finset.notMem_empty j hj)
  | insert a s ha hs =>
      rcases hs with ⟨i, hi⟩
      rcases exists_ge_ge a i with ⟨k, hak, hik⟩
      refine ⟨k, ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj'
      · exact hak
      · exact (hi j hj').trans hik

/-- Helper for Lemma 10.168.5: a finite indexed family of stage witnesses can be merged to one
common stage. -/
theorem directed_fin_common_upper_bound
    {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    {n : ℕ} (u : Fin n → I) :
    ∃ i : I, ∀ k : Fin n, u k ≤ i := by
  classical
  obtain ⟨i, hi⟩ := directed_finset_common_upper_bound (s := Finset.univ.image u)
  refine ⟨i, ?_⟩
  intro k
  exact hi (u k) (Finset.mem_image_of_mem u (Finset.mem_univ k))

/-- Helper for Lemma 10.168.5: after pushing out a directed system of `A₀`-algebras along
`A₀ → R₀`, the resulting diagram in `CommAlgCat R₀` is the canonical tensor-base-change
diagram. -/
noncomputable abbrev tensor_base_change_commAlgDiagram
    {I : Type v} [Preorder I]
    (G : I ⥤ CommAlgCat.{u} A₀)
    (R₀ : Type u) [CommRing R₀] [Algebra A₀ R₀] :
    I ⥤ CommAlgCat.{u} R₀ :=
  G ⋙ (commAlgCatEquivUnder (CommRingCat.of A₀)).functor ⋙
    Under.pushout (CommRingCat.ofHom (algebraMap A₀ R₀)) ⋙
    (commAlgCatEquivUnder (CommRingCat.of R₀)).inverse

/-- Helper for Lemma 10.168.5: the tensor-base-changed colimit cocone in `CommAlgCat R₀`. -/
noncomputable abbrev tensor_base_change_commAlgCocone
    {I : Type v} [Preorder I]
    (G : I ⥤ CommAlgCat.{u} A₀) (c : ColimitCocone G)
    (R₀ : Type u) [CommRing R₀] [Algebra A₀ R₀] :
    Cocone (tensor_base_change_commAlgDiagram (A₀ := A₀) G R₀) :=
  ((commAlgCatEquivUnder (CommRingCat.of R₀)).inverse.mapCocone
    ((Under.pushout (CommRingCat.ofHom (algebraMap A₀ R₀))).mapCocone
      ((commAlgCatEquivUnder (CommRingCat.of A₀)).functor.mapCocone c.cocone)))

/-- Helper for Lemma 10.168.5: the tensor-base-changed cocone is colimiting already in
`CommAlgCat R₀`. -/
noncomputable def tensor_base_change_commAlgCocone_isColimit
    {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (G : I ⥤ CommAlgCat.{u} A₀) (c : ColimitCocone G)
    (R₀ : Type u) [CommRing R₀] [Algebra A₀ R₀] :
    IsColimit (tensor_base_change_commAlgCocone (A₀ := A₀) G c R₀) := by
  let E₀ := commAlgCatEquivUnder (CommRingCat.of A₀)
  let P := Under.pushout (CommRingCat.ofHom (algebraMap A₀ R₀))
  let E₁ := commAlgCatEquivUnder (CommRingCat.of R₀)
  have hUnder : IsColimit (E₀.functor.mapCocone c.cocone) := by
    -- Proof comment: first move the original colimit cocone to the under-category over `A₀`.
    exact isColimitOfPreserves E₀.functor c.isColimit
  have hPush : IsColimit (P.mapCocone (E₀.functor.mapCocone c.cocone)) := by
    -- Proof comment: pushout along `A₀ → R₀` preserves colimits because it is a left adjoint.
    exact isColimitOfPreserves P hUnder
  -- Proof comment: transport the pushed-out colimit cocone back across the equivalence with
  -- `CommAlgCat R₀`.
  simpa [tensor_base_change_commAlgCocone, tensor_base_change_commAlgDiagram, E₀, E₁, P,
    commAlgCatEquivUnder] using
    (isColimitOfPreserves E₁.inverse hPush)

/-- Helper for Lemma 10.168.5: the legs of any cocone over a directed diagram of `A₀`-algebras
commute with the transition maps on the underlying rings. -/
theorem directed_commAlg_cocone_leg_compatible
    {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (G : I ⥤ CommAlgCat.{u} A₀) (t : Cocone G)
    {i j : I} (h : i ≤ j) :
    ((t.ι.app j).hom.toRingHom : ↑(G.obj j) →+* ↑t.pt).comp (G.map (homOfLE h)).hom.toRingHom =
      (t.ι.app i).hom.toRingHom := by
  -- Proof comment: this is just cocone naturality read on the underlying ring homomorphisms.
  exact congrArg (fun f : G.obj i ⟶ t.pt ↦ f.hom.toRingHom) (t.w (homOfLE h))

/-- Helper for Lemma 10.168.5: every cocone over a directed diagram of `A₀`-algebras receives the
canonical algebra map from the explicit `Ring.DirectLimit`. -/
noncomputable abbrev directed_commAlg_ringDirectLimitDescAlgHom
    {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (G : I ⥤ CommAlgCat.{u} A₀) (t : Cocone G) :
    directed_commAlg_ringDirectLimit (A₀ := A₀) G →ₐ[A₀] ↑t.pt :=
  { toRingHom :=
      Ring.DirectLimit.lift
        (fun i ↦ ↑(G.obj i))
        (fun i j h ↦ (G.map (homOfLE h)).hom)
        ↑t.pt
        (fun i ↦ (t.ι.app i).hom.toRingHom)
        (fun _ _ h x ↦
          DFunLike.congr_fun (directed_commAlg_cocone_leg_compatible (A₀ := A₀) G t h) x)
    commutes' := fun a ↦ by
      classical
      let i : I := Classical.arbitrary I
      -- Proof comment: check the `A₀`-algebra structure on one stage representative and then
      -- descend it to the direct limit.
      rw [directed_ringDirectLimit_algebraMap_eq_of (A₀ := A₀) G i]
      change
        Ring.DirectLimit.lift
            (fun i ↦ ↑(G.obj i))
            (fun i j h ↦ (G.map (homOfLE h)).hom)
            ↑t.pt
            (fun i ↦ (t.ι.app i).hom.toRingHom)
            (fun _ _ h x ↦
              DFunLike.congr_fun
                (directed_commAlg_cocone_leg_compatible (A₀ := A₀) G t h) x)
            (Ring.DirectLimit.of
              (fun i ↦ ↑(G.obj i))
              (fun i j h ↦ (G.map (homOfLE h)).hom)
              i (algebraMap A₀ ↑(G.obj i) a)) =
          algebraMap A₀ ↑t.pt a
      simpa [RingHom.comp_apply, Ring.DirectLimit.lift_of] using (t.ι.app i).hom.commutes a }

/-- Helper for Lemma 10.168.5: the canonical desc map from the explicit `Ring.DirectLimit`
evaluates on a stage class by the corresponding cocone leg. -/
@[simp]
theorem directed_commAlg_ringDirectLimitDescAlgHom_comp_of
    {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (G : I ⥤ CommAlgCat.{u} A₀) (t : Cocone G) (i : I) (x : ↑(G.obj i)) :
    directed_commAlg_ringDirectLimitDescAlgHom (A₀ := A₀) G t
        (Ring.DirectLimit.of
          (fun i ↦ ↑(G.obj i))
          (fun i j h ↦ (G.map (homOfLE h)).hom)
          i x) =
      (t.ι.app i).hom x := by
  -- Proof comment: this is exactly the defining evaluation formula of `Ring.DirectLimit.lift`.
  change
    Ring.DirectLimit.lift
        (fun i ↦ ↑(G.obj i))
        (fun i j h ↦ (G.map (homOfLE h)).hom)
        ↑t.pt
        (fun i ↦ (t.ι.app i).hom.toRingHom)
        (fun _ _ h x ↦
          DFunLike.congr_fun
            (directed_commAlg_cocone_leg_compatible (A₀ := A₀) G t h) x)
        (Ring.DirectLimit.of
          (fun i ↦ ↑(G.obj i))
          (fun i j h ↦ (G.map (homOfLE h)).hom)
          i x) =
      (t.ι.app i).hom x
  simp only [Ring.DirectLimit.lift_of]
  rfl

/-- Helper for Lemma 10.168.5: after forgetting the tensor-base-change cocone to types, applying
the usual `Type`-level `uliftFunctor` preserves any already-available small-universe colimit
witness in the larger universe. -/
noncomputable def tensor_base_change_underlying_cocone_small_ulift_isColimit
    {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (G : I ⥤ CommAlgCat.{u} A₀) (c : ColimitCocone G)
    (R₀ : Type u) [CommRing R₀] [Algebra A₀ R₀]
    (hsmall :
      IsColimit ((forget CommRingCat).mapCocone
        (tensor_base_change_underlying_cocone (A₀ := A₀) G c R₀))) :
    IsColimit
      (((forget CommRingCat) ⋙ CategoryTheory.uliftFunctor.{max u v, u}).mapCocone
        (tensor_base_change_underlying_cocone (A₀ := A₀) G c R₀)) := by
  -- Proof comment: once the underlying commutative-ring cocone is colimiting in the small
  -- universe, the ordinary `Type`-level `uliftFunctor` transports that witness to the larger
  -- universe where the explicit direct-limit representatives live.
  exact isColimitOfPreserves CategoryTheory.uliftFunctor.{max u v, u} hsmall

/-- Helper for Lemma 10.168.5: the canonical algebra map from the explicit tensor-stage direct
limit to the tensor-base-changed cocone point. -/
noncomputable abbrev tensor_base_change_ringDirectLimitToCoconePointAlgHom
    {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (G : I ⥤ CommAlgCat.{u} A₀) (c : ColimitCocone G)
    (R₀ : Type u) [CommRing R₀] [Algebra A₀ R₀] :
    directed_commAlg_ringDirectLimit
        (A₀ := R₀) (tensor_base_change_commAlgDiagram (A₀ := A₀) G R₀) →ₐ[R₀]
      ↑((tensor_base_change_commAlgCocone (A₀ := A₀) G c R₀).pt) :=
  directed_commAlg_ringDirectLimitDescAlgHom
    (A₀ := R₀) (tensor_base_change_commAlgDiagram (A₀ := A₀) G R₀)
    (tensor_base_change_commAlgCocone (A₀ := A₀) G c R₀)

/-- Helper for Lemma 10.168.5: the canonical tensor-base-change desc map evaluates on a stage
class by the corresponding tensor-base-change cocone leg. -/
@[simp]
theorem tensor_base_change_ringDirectLimitToCoconePointAlgHom_comp_of
    {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (G : I ⥤ CommAlgCat.{u} A₀) (c : ColimitCocone G)
    (R₀ : Type u) [CommRing R₀] [Algebra A₀ R₀]
    (i : I) (z : ↑((tensor_base_change_commAlgDiagram (A₀ := A₀) G R₀).obj i)) :
    tensor_base_change_ringDirectLimitToCoconePointAlgHom (A₀ := A₀) G c R₀
        (Ring.DirectLimit.of
          (fun i ↦ ↑((tensor_base_change_commAlgDiagram (A₀ := A₀) G R₀).obj i))
          (fun i j h ↦
            ((tensor_base_change_commAlgDiagram (A₀ := A₀) G R₀).map (homOfLE h)).hom)
          i z) =
      (tensor_base_change_commAlgCocone (A₀ := A₀) G c R₀).ι.app i z := by
  -- Proof comment: this is just the general direct-limit desc evaluation formula specialized to
  -- the tensor-base-change diagram and cocone.
  exact directed_commAlg_ringDirectLimitDescAlgHom_comp_of
    (A₀ := R₀) (tensor_base_change_commAlgDiagram (A₀ := A₀) G R₀)
    (tensor_base_change_commAlgCocone (A₀ := A₀) G c R₀) i z

/-- Helper for Lemma 10.168.5: the canonical stage maps into the explicit tensor-stage ring direct
limit are compatible with the transition maps of the tensor-base-change diagram. -/
theorem tensor_base_change_ringDirectLimit_of_homOfLE
    {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (G : I ⥤ CommAlgCat.{u} A₀)
    (R₀ : Type u) [CommRing R₀] [Algebra A₀ R₀]
    {i j : I} (h : i ≤ j) :
    (Ring.DirectLimit.of
        (fun i ↦ ↑((tensor_base_change_commAlgDiagram (A₀ := A₀) G R₀).obj i))
        (fun i j h ↦
          ((tensor_base_change_commAlgDiagram (A₀ := A₀) G R₀).map (homOfLE h)).hom)
        j).comp (((tensor_base_change_commAlgDiagram (A₀ := A₀) G R₀).map (homOfLE h)).hom) =
      Ring.DirectLimit.of
        (fun i ↦ ↑((tensor_base_change_commAlgDiagram (A₀ := A₀) G R₀).obj i))
        (fun i j h ↦
          ((tensor_base_change_commAlgDiagram (A₀ := A₀) G R₀).map (homOfLE h)).hom)
        i := by
  ext x
  change
    Ring.DirectLimit.of
        (fun i ↦ ↑((tensor_base_change_commAlgDiagram (A₀ := A₀) G R₀).obj i))
        (fun i j h ↦
          ((tensor_base_change_commAlgDiagram (A₀ := A₀) G R₀).map (homOfLE h)).hom)
        j (((tensor_base_change_commAlgDiagram (A₀ := A₀) G R₀).map (homOfLE h)).hom x) =
      Ring.DirectLimit.of
        (fun i ↦ ↑((tensor_base_change_commAlgDiagram (A₀ := A₀) G R₀).obj i))
        (fun i j h ↦
          ((tensor_base_change_commAlgDiagram (A₀ := A₀) G R₀).map (homOfLE h)).hom)
        i x
  simpa using
    (Ring.DirectLimit.of_f
      (G := fun i ↦ ↑((tensor_base_change_commAlgDiagram (A₀ := A₀) G R₀).obj i))
      (f := fun i j h ↦
        ((tensor_base_change_commAlgDiagram (A₀ := A₀) G R₀).map (homOfLE h)).hom)
      (hij := h) (x := x))

/-- Helper for Lemma 10.168.5: after passing to the large-universe underlying types, the canonical
inverse map from the tensor-base-changed cocone point to the explicit tensor-stage direct limit. -/
noncomputable def tensor_base_change_ringDirectLimit_inverse_large_ulift
    {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (G : I ⥤ CommAlgCat.{u} A₀) (c : ColimitCocone G)
    (R₀ : Type u) [CommRing R₀] [Algebra A₀ R₀] :
    ULift ↑((tensor_base_change_commAlgCocone (A₀ := A₀) G c R₀).pt) →
      ULift
        (directed_commAlg_ringDirectLimit
          (A₀ := R₀) (tensor_base_change_commAlgDiagram (A₀ := A₀) G R₀)) := sorry

/-- Helper for Lemma 10.168.5: the large-universe inverse map sends the cocone leg of a stage
element to its explicit `Ring.DirectLimit.of` class. -/
theorem tensor_base_change_ringDirectLimit_inverse_large_ulift_comp_of
    {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (G : I ⥤ CommAlgCat.{u} A₀) (c : ColimitCocone G)
    (R₀ : Type u) [CommRing R₀] [Algebra A₀ R₀]
    (i : I) (z : ↑((tensor_base_change_commAlgDiagram (A₀ := A₀) G R₀).obj i)) :
    tensor_base_change_ringDirectLimit_inverse_large_ulift (A₀ := A₀) G c R₀
        (ULift.up ((tensor_base_change_commAlgCocone (A₀ := A₀) G c R₀).ι.app i z)) =
      ULift.up
        (Ring.DirectLimit.of
          (fun i ↦ ↑((tensor_base_change_commAlgDiagram (A₀ := A₀) G R₀).obj i))
          (fun i j h ↦
            ((tensor_base_change_commAlgDiagram (A₀ := A₀) G R₀).map (homOfLE h)).hom)
          i z) := by
  -- TODO: evaluate the ulifted colimit desc map on the stage cocone leg once the large-universe
  -- comparison cocone is packaged with the exact underlying diagram expected by `hulift.fac`.
  sorry

/-- Helper for Lemma 10.168.5: forgetting the auxiliary `ULift`, the inverse map from the
tensor-base-changed cocone point to the explicit tensor-stage direct limit. -/
noncomputable def tensor_base_change_ringDirectLimit_inverse_large
    {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (G : I ⥤ CommAlgCat.{u} A₀) (c : ColimitCocone G)
    (R₀ : Type u) [CommRing R₀] [Algebra A₀ R₀] :
    ↑((tensor_base_change_commAlgCocone (A₀ := A₀) G c R₀).pt) →
      directed_commAlg_ringDirectLimit
        (A₀ := R₀) (tensor_base_change_commAlgDiagram (A₀ := A₀) G R₀) := sorry

/-- Helper for Lemma 10.168.5: the plain inverse map sends the cocone leg of a stage element to
its explicit `Ring.DirectLimit.of` class. -/
theorem tensor_base_change_ringDirectLimit_inverse_large_comp_of
    {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (G : I ⥤ CommAlgCat.{u} A₀) (c : ColimitCocone G)
    (R₀ : Type u) [CommRing R₀] [Algebra A₀ R₀]
    (i : I) (z : ↑((tensor_base_change_commAlgDiagram (A₀ := A₀) G R₀).obj i)) :
    tensor_base_change_ringDirectLimit_inverse_large (A₀ := A₀) G c R₀
        ((tensor_base_change_commAlgCocone (A₀ := A₀) G c R₀).ι.app i z) =
      Ring.DirectLimit.of
        (fun i ↦ ↑((tensor_base_change_commAlgDiagram (A₀ := A₀) G R₀).obj i))
        (fun i j h ↦
          ((tensor_base_change_commAlgDiagram (A₀ := A₀) G R₀).map (homOfLE h)).hom)
        i z := by
  -- TODO: once the plain inverse is defined by stripping `ULift` from the large inverse map, this
  -- is the direct `ULift.down` image of the preceding stage formula.
  sorry

/-- Helper for Lemma 10.168.5: the canonical desc map composed with the large-universe inverse is
the identity on the tensor-base-changed cocone point. -/
theorem tensor_base_change_ringDirectLimitToCoconePoint_inverse_large_apply
    {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (G : I ⥤ CommAlgCat.{u} A₀) (c : ColimitCocone G)
    (R₀ : Type u) [CommRing R₀] [Algebra A₀ R₀]
    (y : ↑((tensor_base_change_commAlgCocone (A₀ := A₀) G c R₀).pt)) :
    tensor_base_change_ringDirectLimitToCoconePointAlgHom (A₀ := A₀) G c R₀
        (tensor_base_change_ringDirectLimit_inverse_large (A₀ := A₀) G c R₀ y) =
      y := by
  -- TODO: compare the identity map on the ulifted cocone point with the composite of the desc map
  -- and the large-universe inverse by `hulift.hom_ext` on stage legs.
  sorry

/-- Helper for Lemma 10.168.5: after passing to the large-universe underlying types, the canonical
map from the explicit tensor-stage direct limit to the tensor-base-changed cocone point is
bijective. -/
theorem tensor_base_change_ringDirectLimitToCoconePoint_bijective
    {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (G : I ⥤ CommAlgCat.{u} A₀) (c : ColimitCocone G)
    (R₀ : Type u) [CommRing R₀] [Algebra A₀ R₀] :
    Function.Bijective
      (tensor_base_change_ringDirectLimitToCoconePointAlgHom (A₀ := A₀) G c R₀) := by
  refine ⟨?_, ?_⟩
  · intro x y hxy
    -- Proof comment: the explicit inverse is a left inverse on stage representatives, hence on
    -- the whole direct limit by `Ring.DirectLimit.induction_on`.
    have hleft :
        ∀ z,
          tensor_base_change_ringDirectLimit_inverse_large (A₀ := A₀) G c R₀
              (tensor_base_change_ringDirectLimitToCoconePointAlgHom (A₀ := A₀) G c R₀ z) = z := by
      intro z
      induction z using Ring.DirectLimit.induction_on with
      | ih i x =>
          rw [tensor_base_change_ringDirectLimitToCoconePointAlgHom_comp_of
              (A₀ := A₀) G c R₀ i x]
          rw [tensor_base_change_ringDirectLimit_inverse_large_comp_of
              (A₀ := A₀) G c R₀ i x]
    calc
      x = tensor_base_change_ringDirectLimit_inverse_large (A₀ := A₀) G c R₀
            (tensor_base_change_ringDirectLimitToCoconePointAlgHom (A₀ := A₀) G c R₀ x) := by
              symm
              exact hleft x
      _ = tensor_base_change_ringDirectLimit_inverse_large (A₀ := A₀) G c R₀
            (tensor_base_change_ringDirectLimitToCoconePointAlgHom (A₀ := A₀) G c R₀ y) := by
              rw [hxy]
      _ = y := hleft y
  · intro y
    refine ⟨tensor_base_change_ringDirectLimit_inverse_large (A₀ := A₀) G c R₀ y, ?_⟩
    exact tensor_base_change_ringDirectLimitToCoconePoint_inverse_large_apply
      (A₀ := A₀) G c R₀ y

/-- Helper for Lemma 10.168.5: the explicit tensor-stage direct limit identifies with the
tensor-base-changed cocone point as an `R₀`-algebra. -/
noncomputable def tensor_base_change_ringDirectLimit_algEquiv
    {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (G : I ⥤ CommAlgCat.{u} A₀) (c : ColimitCocone G)
    (R₀ : Type u) [CommRing R₀] [Algebra A₀ R₀] :
    directed_commAlg_ringDirectLimit
        (A₀ := R₀) (tensor_base_change_commAlgDiagram (A₀ := A₀) G R₀) ≃ₐ[R₀]
      ↑((tensor_base_change_commAlgCocone (A₀ := A₀) G c R₀).pt) :=
  AlgEquiv.ofBijective
    (tensor_base_change_ringDirectLimitToCoconePointAlgHom (A₀ := A₀) G c R₀)
    (tensor_base_change_ringDirectLimitToCoconePoint_bijective
      (A₀ := A₀) G c R₀)

/-- Helper for Lemma 10.168.5: under the tensor-stage direct-limit identification, the class of a
stage element is sent to the corresponding cocone leg value. -/
@[simp]
theorem tensor_base_change_ringDirectLimit_algEquiv_comp_of
    {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (G : I ⥤ CommAlgCat.{u} A₀) (c : ColimitCocone G)
    (R₀ : Type u) [CommRing R₀] [Algebra A₀ R₀]
    (i : I) (z : ↑((tensor_base_change_commAlgDiagram (A₀ := A₀) G R₀).obj i)) :
    tensor_base_change_ringDirectLimit_algEquiv (A₀ := A₀) G c R₀
        (Ring.DirectLimit.of
          (fun i ↦ ↑((tensor_base_change_commAlgDiagram (A₀ := A₀) G R₀).obj i))
          (fun i j h ↦
            ((tensor_base_change_commAlgDiagram (A₀ := A₀) G R₀).map (homOfLE h)).hom)
          i z) =
      (tensor_base_change_commAlgCocone (A₀ := A₀) G c R₀).ι.app i z := by
  -- Proof comment: `AlgEquiv.ofBijective` keeps the forward map unchanged, so the stage formula is
  -- exactly the one for the canonical desc algebra hom.
  simpa [tensor_base_change_ringDirectLimit_algEquiv, AlgEquiv.ofBijective_apply] using
    tensor_base_change_ringDirectLimitToCoconePointAlgHom_comp_of
      (A₀ := A₀) G c R₀ i z

/-- Helper for Lemma 10.168.5: vanishing of the finitely many tensor-generator differentials on
the canonical tensor colimit descends to one stage. -/
theorem tensor_base_change_coconePoint_generator_zero_descends
    {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (G : I ⥤ CommAlgCat.{u} A₀) (c : ColimitCocone G)
    (φ₀ : B₀ →ₐ[A₀] C₀) {n : ℕ} (x : Fin n → C₀)
    (hz :
      ∀ k : Fin n,
        letI : Algebra (B₀ ⊗[A₀] ↑c.cocone.pt) (C₀ ⊗[A₀] ↑c.cocone.pt) :=
          (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ ↑c.cocone.pt)).toRingHom.toAlgebra
        KaehlerDifferential.D (B₀ ⊗[A₀] ↑c.cocone.pt) (C₀ ⊗[A₀] ↑c.cocone.pt)
          (x k ⊗ₜ[A₀] (1 : ↑c.cocone.pt)) = 0) :
    ∃ i : I,
      ∀ k : Fin n,
        letI : Algebra (B₀ ⊗[A₀] ↑(G.obj i)) (C₀ ⊗[A₀] ↑(G.obj i)) :=
          (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ ↑(G.obj i))).toRingHom.toAlgebra
        KaehlerDifferential.D (B₀ ⊗[A₀] ↑(G.obj i)) (C₀ ⊗[A₀] ↑(G.obj i))
          (x k ⊗ₜ[A₀] (1 : ↑(G.obj i))) = 0 := by
  -- Route correction: follow the source proof directly through
  -- `Ω_{C/B} = colim_i Ω_{Cᵢ/Bᵢ}`. The remaining missing bridges are:
  -- 1. the stagewise direct-limit/cocone-point algebra equivalence and its `Ring.DirectLimit.of`
  --    evaluation formula from the preceding two helpers;
  -- 2. a transport-stable specialization of `kaehlerDifferential_directLimitComparison` sending
  --    the direct-limit class of `1 ⊗ d(x_k ⊗ 1)` to the cocone-point differential
  --    `d(x_k ⊗ 1)`.
  --
  -- Once those are in place, each zero from `hz` descends by
  -- `Module.DirectLimit.of.zero_exact`, and `directed_fin_common_upper_bound` merges the finitely
  -- many witness stages exactly as in the textbook proof.
  sorry

-- Proof sketch: formal unramifiedness of the colimit base-change hom is the primitive owner
-- input. Interpreting it via Kähler differentials, finite type of `φ₀` gives finitely many
-- generators whose images vanish after tensoring to the colimit, so filtered-colimit finiteness
-- forces those generators to vanish already at some stage. That yields formal unramifiedness of
-- the stage base-change hom; finite type of the same stage hom is then recovered separately from
-- `hφ₀` by base change.
/-- Helper for Lemma 10.168.5: after reindexing a filtered diagram by a final directed poset, the
remaining source-faithful task is the directed-index proof that descends the vanishing of a finite
family of Kähler generators along the explicit direct-limit presentation. -/
theorem finite_type_formallyUnramified_baseChangeHom_descends_to_directed_reindex
    {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (G : I ⥤ CommAlgCat.{u} A₀) (c : ColimitCocone G)
    (φ₀ : B₀ →ₐ[A₀] C₀) (hφ₀ : φ₀.FiniteType)
    (hfu : (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ ↑c.cocone.pt)).FormallyUnramified) :
    ∃ i : I, (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ ↑(G.obj i))).FormallyUnramified := by
  letI : Algebra B₀ C₀ := φ₀.toRingHom.toAlgebra
  letI : Algebra.FiniteType B₀ C₀ := by
    simpa [AlgHom.FiniteType, RingHom.FiniteType] using hφ₀
  obtain ⟨n, f, hsurj⟩ :=
    (Algebra.FiniteType.iff_quotient_mvPolynomial'' (R := B₀) (S := C₀)).1 inferInstance
  let x : Fin n → C₀ := fun i ↦ f (MvPolynomial.X i)
  have haeval : MvPolynomial.aeval (R := B₀) x = f := by
    ext i
    simp [x]
  have hx : Algebra.adjoin B₀ (Set.range x) = ⊤ := by
    have hrange : AlgHom.range (MvPolynomial.aeval (R := B₀) x) = ⊤ := by
      rw [AlgHom.range_eq_top]
      rw [haeval]
      exact hsurj
    rwa [← Algebra.adjoin_range_eq_range_aeval (R := B₀) (f := x)] at hrange
  have hz :
      ∀ k : Fin n,
        letI : Algebra (B₀ ⊗[A₀] ↑c.cocone.pt) (C₀ ⊗[A₀] ↑c.cocone.pt) :=
          (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ ↑c.cocone.pt)).toRingHom.toAlgebra
        KaehlerDifferential.D (B₀ ⊗[A₀] ↑c.cocone.pt) (C₀ ⊗[A₀] ↑c.cocone.pt)
          (x k ⊗ₜ[A₀] (1 : ↑c.cocone.pt)) = 0 := by
    intro k
    -- Proof comment: the tensor target over the chosen colimit is formally unramified, so every
    -- distinguished differential vanishes there.
    simpa using
      tensor_base_change_D_tmul_one_eq_zero
        (φ₀ := φ₀) (R := ↑c.cocone.pt) hfu (x := x k)
  obtain ⟨i, hi⟩ :=
    tensor_base_change_coconePoint_generator_zero_descends
      (A₀ := A₀) (G := G) c (φ₀ := φ₀) x hz
  refine ⟨i, ?_⟩
  -- Proof comment: once the descended generator family vanishes at stage `i`, the stage Kähler
  -- differential module is zero by the spanning result from the source proof.
  exact tensor_base_change_formallyUnramified_of_generator_zero
    (φ₀ := φ₀) x hx ↑(G.obj i) hi

/-
The public theorem first reduces the arbitrary filtered index category to the canonical
directed-poset presentation from `IsFiltered.exists_directed`. Finality keeps the original colimit
point, so the formally-unramified hypothesis is unchanged; only the index category becomes
directed, which is the exact setting needed for the remaining source-faithful direct-limit proof.
-/
/-- Owner-level form of Lemma 10.168.5: if the colimit tensor-product base-change hom of
`φ₀ : B₀ →ₐ[A₀] C₀` is formally unramified, then some stage base-change hom is already formally
unramified. The finite-type input is kept separate because it is primitive data of `φ₀`, not of
the colimit base change. -/
theorem finite_type_formallyUnramified_baseChangeHom_descends_to_stage
    (φ₀ : B₀ →ₐ[A₀] C₀) (hφ₀ : φ₀.FiniteType)
    (hfu : (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ ↑(colimit F))).FormallyUnramified) :
    ∃ j : J, (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ ↑(F.obj j))).FormallyUnramified := by
  classical
  obtain ⟨I, hIord, hIdir, hInonempty, x, hx⟩ := CategoryTheory.IsFiltered.exists_directed J
  let _ : PartialOrder I := hIord
  let _ : Nonempty I := hInonempty
  let _ : IsDirectedOrder I := hIdir
  let G : I ⥤ CommAlgCat.{u} A₀ := x ⋙ F
  let cG : ColimitCocone G :=
    Functor.Final.colimitCoconeComp x (getColimitCocone F)
  -- Proof comment: the final reindex keeps the original colimit point, so the colimit-stage
  -- formal unramifiedness hypothesis is the same after reindexing.
  obtain ⟨i, hi⟩ :=
    finite_type_formallyUnramified_baseChangeHom_descends_to_directed_reindex
      (G := G) cG φ₀ hφ₀ (by simpa [G, cG] using hfu)
  -- Proof comment: a stage of the reindexed directed system is literally an original stage of `F`.
  exact ⟨x.obj i, by simpa [G] using hi⟩

/-- Lemma 10.168.5: let `A = colim_i Aᵢ` be a directed colimit of `A₀`-algebras. If the base
change `B₀ ⊗[A₀] A → C₀ ⊗[A₀] A` of a map `φ₀ : B₀ →ₐ[A₀] C₀` is formally unramified and `φ₀`
is of finite type, then for some stage `Aᵢ` the base-changed map
`B₀ ⊗[A₀] Aᵢ → C₀ ⊗[A₀] Aᵢ` is already unramified. This is stated on the canonical base-change
hom through the canonical owner `Algebra.Unramified`; Lemma `10.151.2` supplies the bridge from
this owner to the pair of formal unramifiedness and finite type. -/
theorem finite_type_unramified_baseChange_descends_to_stage
    (φ₀ : B₀ →ₐ[A₀] C₀) (hφ₀ : φ₀.FiniteType)
    (hfu : (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ ↑(colimit F))).FormallyUnramified) :
    ∃ j : J,
      letI :=
        (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ ↑(F.obj j))).toRingHom.toAlgebra
      Algebra.Unramified (B₀ ⊗[A₀] ↑(F.obj j)) (C₀ ⊗[A₀] ↑(F.obj j)) := by
  -- First descend the formally-unramified part, which is the primitive content of the source
  -- proof.
  obtain ⟨j, hj⟩ := finite_type_formallyUnramified_baseChangeHom_descends_to_stage
    (F := F) φ₀ hφ₀ hfu
  refine ⟨j, ?_⟩
  letI := (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ ↑(F.obj j))).toRingHom.toAlgebra
  -- Finite type then follows by ordinary base change from the original finite-type hypothesis.
  have hft :
      Algebra.FiniteType (B₀ ⊗[A₀] ↑(F.obj j)) (C₀ ⊗[A₀] ↑(F.obj j)) := by
    letI : Algebra B₀ C₀ := φ₀.toRingHom.toAlgebra
    simpa [AlgHom.FiniteType, RingHom.FiniteType] using
      tensor_base_change_hom_finiteType (F := F) φ₀ hφ₀ j
  -- The canonical owner characterization of unramified combines the two ingredients.
  exact (Algebra.unramified_iff_formallyUnramified_and_finiteType).2 ⟨hj, hft⟩

end
