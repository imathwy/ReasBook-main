import Mathlib
import Mathlib.Analysis.Matrix.PosDef

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_16_16_3_1 (from Chap16) -/
noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped MonoidAlgebra Representation TensorProduct ZeroObject

namespace Representation

section ProjectivePositiveSubset

variable {A : Type u} [CommRing A] [IsLocalRing A]
variable {G : Type u} [Group G] [Finite G]

local notation "k" => IsLocalRing.ResidueField A

/-- Helper for Lemma 16-16.3-1: the tensor-product residue-field reduction carries the restricted
`A[G]`-action coming from `A[G] → k[G]`. -/
local instance residueTensorModule
    (P : FiniteProjectiveGroupAlgebraModule A G) :
    Module A[G] (k ⊗[A] P.V) :=
  Module.compHom (k ⊗[A] P.V) (MonoidAlgebra.mapRingHom G (algebraMap A k))

/-- Helper for Lemma 16-16.3-1: the restricted tensor-product action is compatible with the scalar
tower `A → A[G]`. -/
local instance residueTensorIsScalarTower
    (P : FiniteProjectiveGroupAlgebraModule A G) :
    IsScalarTower A A[G] (k ⊗[A] P.V) :=
  IsScalarTower.of_algebraMap_smul fun a x ↦ by
    change
      (MonoidAlgebra.mapRingHom G (algebraMap A k)) (MonoidAlgebra.single (1 : G) a) • x =
        a • x
    rw [MonoidAlgebra.mapRingHom_single]
    have hsingle :
        MonoidAlgebra.single (1 : G) (IsLocalRing.residue A a) =
          algebraMap k (k[G]) (IsLocalRing.residue A a) := by
      rw [MonoidAlgebra.single_eq_algebraMap_mul_of]
      simp
    calc
      MonoidAlgebra.single (1 : G) (IsLocalRing.residue A a) • x
          = (IsLocalRing.residue A a) • x := by
              simpa only [hsingle] using
                (IsScalarTower.algebraMap_smul (k[G]) (IsLocalRing.residue A a) x)
      _ = a • x := by
            simpa [IsLocalRing.ResidueField.algebraMap_eq] using
              (IsScalarTower.algebraMap_smul k a x)

/-- Helper for Lemma 16-16.3-1: the binary product of two actual finite projective `R[G]`-modules
again represents the sum of their Grothendieck classes. -/
private theorem exists_product_projective_module_class_eq_add
    {R : Type u} [CommRing R] {G : Type u} [Group G]
    (P Q : FiniteProjectiveGroupAlgebraModule R G) :
    ∃ W : FiniteProjectiveGroupAlgebraModule R G,
      Nonempty (W.V ≃ₗ[R[G]] (P.V × Q.V)) ∧
      [W]ₚ₀ = [P]ₚ₀ + [Q]ₚ₀ := by
  let W0 : ModuleCat R[G] := ModuleCat.of R[G] (P.V × Q.V)
  have hfinite : Module.Finite R[G] W0 := by
    -- Finite generation is inherited by the binary product module.
    change Module.Finite R[G] (P.V × Q.V)
    infer_instance
  let Wfg : FGModuleCat R[G] := ⟨W0, hfinite⟩
  have hproj : Module.Projective R[G] Wfg := by
    -- Projectivity is likewise preserved by finite products.
    change Module.Projective R[G] (P.V × Q.V)
    infer_instance
  let W : FiniteProjectiveGroupAlgebraModule R G := ⟨Wfg, hproj⟩
  let f : P ⟶ W :=
    ObjectProperty.homMk (ConcreteCategory.ofHom (LinearMap.inl R[G] P.V Q.V))
  let g : W ⟶ Q :=
    ObjectProperty.homMk (ConcreteCategory.ofHom (LinearMap.snd R[G] P.V Q.V))
  let r : W ⟶ P :=
    ObjectProperty.homMk (ConcreteCategory.ofHom (LinearMap.fst R[G] P.V Q.V))
  let s : Q ⟶ W :=
    ObjectProperty.homMk (ConcreteCategory.ofHom (LinearMap.inr R[G] P.V Q.V))
  let T : ShortComplex (FiniteProjectiveGroupAlgebraModule R G) :=
    ShortComplex.mk f g (by ext x <;> rfl)
  have hsplit : T.Splitting := by
    -- The standard inclusions and projections split the product short complex.
    refine
      { r := r
        s := s
        f_r := ?_
        s_g := ?_
        id := ?_ }
    · apply ObjectProperty.hom_ext
      apply ObjectProperty.hom_ext
      apply ModuleCat.hom_ext
      ext x
      change (LinearMap.fst R[G] P.V Q.V) ((LinearMap.inl R[G] P.V Q.V) x) = x
      simp
    · apply ObjectProperty.hom_ext
      apply ObjectProperty.hom_ext
      apply ModuleCat.hom_ext
      ext x
      change (LinearMap.snd R[G] P.V Q.V) ((LinearMap.inr R[G] P.V Q.V) x) = x
      simp
    · apply ObjectProperty.hom_ext
      apply ObjectProperty.hom_ext
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      rintro ⟨x, y⟩
      change
        (LinearMap.inl R[G] P.V Q.V ((LinearMap.fst R[G] P.V Q.V) (x, y)) +
            LinearMap.inr R[G] P.V Q.V ((LinearMap.snd R[G] P.V Q.V) (x, y))) =
          (x, y)
      simp
  -- Translate the split short exact sequence into the Grothendieck relation.
  refine ⟨W, ⟨⟨LinearEquiv.refl R[G] (P.V × Q.V)⟩, ?_⟩⟩
  simpa [T, W, Wfg, W0] using
    finiteProjectiveGroupAlgebraGrothendieckClass_middle_eq_left_add_right
      (A := R) (G := G) T hsplit.shortExact

/-- Helper for Lemma 16-16.3-1: every class in `P₀[A](G)` can be written as a difference of two
actual finite projective classes. -/
private theorem exists_projective_class_difference_rep_local
    (x : P₀[A](G)) :
    ∃ P Q : FiniteProjectiveGroupAlgebraModule A G, x = [P]ₚ₀ - [Q]ₚ₀ := by
  refine QuotientAddGroup.induction_on x ?_
  intro a
  refine FreeAbelianGroup.induction_on a ?_ ?_ ?_ ?_
  · -- The zero class is represented by the zero module minus itself.
    refine
      ⟨(0 : FiniteProjectiveGroupAlgebraModule A G),
        (0 : FiniteProjectiveGroupAlgebraModule A G), ?_⟩
    simp
  · intro P
    -- A generator class is already a difference with zero.
    refine ⟨P, (0 : FiniteProjectiveGroupAlgebraModule A G), ?_⟩
    change [P]ₚ₀ = [P]ₚ₀ - [0]ₚ₀
    rw [finiteProjectiveGroupAlgebraGrothendieckClass_zero (A := A) (G := G)]
    exact (sub_zero [P]ₚ₀).symm
  · intro a ha
    rcases ha with ⟨P, Q, hPQ⟩
    -- Negation swaps the two witnesses.
    refine ⟨Q, P, ?_⟩
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using congrArg Neg.neg hPQ
  · intro a b ha hb
    rcases ha with ⟨P, Q, hPQ⟩
    rcases hb with ⟨P', Q', hP'Q'⟩
    obtain ⟨W, -, hW⟩ :=
      exists_product_projective_module_class_eq_add (R := A) (G := G) P P'
    obtain ⟨Z, -, hZ⟩ :=
      exists_product_projective_module_class_eq_add (R := A) (G := G) Q Q'
    -- Add the two difference presentations and compress the positive parts again.
    refine ⟨W, Z, ?_⟩
    calc
      QuotientAddGroup.mk' (finiteProjectiveGroupAlgebraGrothendieckRelations A G) (a + b)
          =
            QuotientAddGroup.mk' (finiteProjectiveGroupAlgebraGrothendieckRelations A G) a +
              QuotientAddGroup.mk' (finiteProjectiveGroupAlgebraGrothendieckRelations A G) b := by
                rfl
      _ = ([P]ₚ₀ - [Q]ₚ₀) + ([P']ₚ₀ - [Q']ₚ₀) := by
            simp [hPQ, hP'Q']
      _ = [W]ₚ₀ - [Z]ₚ₀ := by
            simp [hW, hZ, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

/-- Helper for Lemma 16-16.3-1: the canonical reduction map `P → k ⊗[A] P` is `A[G]`-linear when
the reduced module is viewed by restriction of scalars. -/
private noncomputable def reduction_groupAlgebraLinear
    (P : FiniteProjectiveGroupAlgebraModule A G) :
    P.V →ₗ[A[G]] (k ⊗[A] P.V) := by
  refine
    { toFun := TensorProduct.mk A k P.V 1
      map_add' := by
        intro x y
        simpa using (TensorProduct.mk A k P.V 1).map_add x y
      map_smul' := ?_ }
  intro a x
  refine MonoidAlgebra.induction_on (p := fun a : A[G] =>
      (TensorProduct.mk A k P.V 1) (a • x) = a • (TensorProduct.mk A k P.V 1 x)) a ?_ ?_ ?_
  · intro g
    -- Check equivariance first on group elements, then extend linearly.
    change (TensorProduct.mk A k P.V 1) (MonoidAlgebra.of A G g • x) =
      (MonoidAlgebra.mapRingHom G (algebraMap A k) (MonoidAlgebra.of A G g)) •
        (TensorProduct.mk A k P.V 1 x)
    simpa [MonoidAlgebra.of_apply] using
      (MonoidAlgebra.tensorProduct_mk_map_monoidAlgebra_of
        (Λ := A) (G := G) (P := P.V) g x)
  · intro a b ha hb
    rw [add_smul, map_add, ha, hb, add_smul]
  · intro c a ha
    simpa [smul_smul, ha] using congrArg (fun z => c • z) ha

/-- Helper for Lemma 16-16.3-1: the canonical reduction map onto `k ⊗[A] P` is surjective. -/
private theorem reduction_groupAlgebraLinear_surjective
    (P : FiniteProjectiveGroupAlgebraModule A G) :
    Function.Surjective (reduction_groupAlgebraLinear (A := A) (G := G) P) := by
  -- This is the standard tensor-product surjectivity of reduction modulo the maximal ideal.
  simpa [reduction_groupAlgebraLinear, IsLocalRing.ResidueField.algebraMap_eq] using
    (TensorProduct.mk_surjective (R := A) (M := P.V) (S := k) IsLocalRing.residue_surjective)

/-- Helper for Lemma 16-16.3-1: a reduced `k[G]`-linear map can be viewed as an `A[G]`-linear map
after restricting scalars along `A[G] → k[G]`. -/
private noncomputable def restrictReducedGroupAlgebraLinear
    {P Q : FiniteProjectiveGroupAlgebraModule A G}
    (g : (k ⊗[A] P.V) →ₗ[k[G]] (k ⊗[A] Q.V)) :
    (k ⊗[A] P.V) →ₗ[A[G]] (k ⊗[A] Q.V) := by
  refine
    { toFun := g
      map_add' := g.map_add
      map_smul' := ?_ }
  intro a x
  change g ((MonoidAlgebra.mapRingHom G (algebraMap A k)) a • x) =
      (MonoidAlgebra.mapRingHom G (algebraMap A k)) a • g x
  simpa using g.map_smul ((MonoidAlgebra.mapRingHom G (algebraMap A k)) a) x

/-- Helper for Lemma 16-16.3-1: an idempotent range inside a finite projective `A[G]`-module is
again a finite projective `A[G]`-module. -/
private noncomputable def rangeFiniteProjectiveGroupAlgebraModule
    (P : FiniteProjectiveGroupAlgebraModule A G)
    (e : Module.End A[G] P.V) (he : IsIdempotentElem e) :
    FiniteProjectiveGroupAlgebraModule A G := by
  let W0 : ModuleCat A[G] := ModuleCat.of A[G] (LinearMap.range e)
  have hfinite : Module.Finite A[G] W0 := by
    -- Finite generation passes to the range of an endomorphism.
    change Module.Finite A[G] (LinearMap.range e)
    infer_instance
  let Wfg : FGModuleCat A[G] := ⟨W0, hfinite⟩
  have hproj : Module.Projective A[G] Wfg := by
    -- The range of an idempotent on a projective module is a split summand.
    change Module.Projective A[G] (LinearMap.range e)
    exact
      LinearMap.IsResidueFieldReduction.projective_range_of_idempotent_endomorphism_general
        e he
  exact ⟨Wfg, hproj⟩

/-- Helper for Lemma 16-16.3-1: if a residue-field class difference is actual, then the larger
projective module already surjects onto the smaller one. -/
private theorem surjective_map_of_positive_projective_difference_residueField
    {Pbar Qbar : FiniteProjectiveGroupAlgebraModule k G}
    (hPQ : [Pbar]ₚ₀ - [Qbar]ₚ₀ ∈ P⁺[k](G)) :
    ∃ f : Pbar.V →ₗ[k[G]] Qbar.V, Function.Surjective f := by
  rcases (mem_projectivePositiveSubset_iff k G).1 hPQ with ⟨Wbar, hWbar⟩
  obtain ⟨Ubar, hUbar_equiv, hUbar_class⟩ :=
    exists_product_projective_module_class_eq_add (R := k) (G := G) Wbar Qbar
  have hPclass : [Pbar]ₚ₀ = [Ubar]ₚ₀ := by
    -- Rewrite the positive difference as an actual summand decomposition of `Pbar`.
    calc
      [Pbar]ₚ₀ = [Wbar]ₚ₀ + [Qbar]ₚ₀ := by
        simpa [hWbar, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
          congrArg (fun z : P₀[k](G) => z + [Qbar]ₚ₀) hWbar
      _ = [Ubar]ₚ₀ := hUbar_class.symm
  obtain ⟨ePU⟩ :=
    (finiteProjectiveGroupAlgebraGrothendieckClass_eq_iff_nonempty_linearEquiv
      (A := k) (G := G) Pbar Ubar).1 hPclass
  rcases hUbar_equiv with ⟨eUprod⟩
  let f : Pbar.V →ₗ[k[G]] Qbar.V :=
    (LinearMap.snd k[G] Wbar.V Qbar.V).comp (eUprod.toLinearMap.comp ePU.toLinearMap)
  refine ⟨f, ?_⟩
  intro q
  -- Transport the obvious projection `Wbar.V × Qbar.V → Qbar.V` back to `Pbar`.
  refine ⟨ePU.symm (eUprod.symm (0, q)), ?_⟩
  simp [f]

/-- Helper for Lemma 16-16.3-1: a surjective reduced map between projective residue-field
reductions lifts to a surjective `A[G]`-linear map upstairs. -/
private theorem lift_surjective_reduction_map_local
    {P Q : FiniteProjectiveGroupAlgebraModule A G}
    (fbar : P.residueFieldReduction.V →ₗ[k[G]] Q.residueFieldReduction.V)
    (hbar : Function.Surjective fbar) :
    ∃ f : P.V →ₗ[A[G]] Q.V, Function.Surjective f := by
  let fbarTensor : (k ⊗[A] P.V) →ₗ[k[G]] (k ⊗[A] Q.V) := by
    simpa [FiniteProjectiveGroupAlgebraModule.residueFieldReduction,
      FiniteProjectiveGroupAlgebraModule.V] using fbar
  have hbarTensor : Function.Surjective fbarTensor := by
    simpa [fbarTensor] using hbar
  let qP : P.V →ₗ[A[G]] (k ⊗[A] P.V) :=
    reduction_groupAlgebraLinear (A := A) (G := G) P
  let qQ : Q.V →ₗ[A[G]] (k ⊗[A] Q.V) :=
    reduction_groupAlgebraLinear (A := A) (G := G) Q
  let h : P.V →ₗ[A[G]] (k ⊗[A] Q.V) :=
    (restrictReducedGroupAlgebraLinear (A := A) (G := G) fbarTensor).comp qP
  have hqQ : Function.Surjective qQ :=
    reduction_groupAlgebraLinear_surjective (A := A) (G := G) Q
  obtain ⟨f, hf⟩ := Module.projective_lifting_property qQ h hqQ
  have hh : Function.Surjective h := by
    -- The lifted target map remains surjective because both reduction and `fbar` are surjective.
    intro z
    obtain ⟨y, hy⟩ := hbarTensor z
    obtain ⟨x, hx⟩ := reduction_groupAlgebraLinear_surjective (A := A) (G := G) P y
    refine ⟨x, ?_⟩
    simpa [h, qP, hx] using hy
  have hbase : Function.Surjective (baseChange_groupAlgebraLinear (A := A) (G := G) f) := by
    -- Surjectivity on the base change is read off from the surjective composite `qQ ∘ f`.
    intro z
    obtain ⟨x, hx⟩ := hh z
    refine ⟨(1 : k) ⊗ₜ[A] x, ?_⟩
    calc
      baseChange_groupAlgebraLinear (A := A) (G := G) f ((1 : k) ⊗ₜ[A] x)
          = (1 : k) ⊗ₜ[A] f x := by
              simp
      _ = qQ (f x) := rfl
      _ = h x := LinearMap.congr_fun hf x
      _ = z := hx
  let e : P ⟶ Q := ObjectProperty.homMk (ConcreteCategory.ofHom f)
  have hsurj : Function.Surjective f := by
    -- Local Nakayama upgrades surjectivity of the reduced map to surjectivity upstairs.
    simpa [e, baseChange_groupAlgebraLinear] using
      finiteProjective_underlying_surjective_of_reduction_surjective
        (A := A) (G := G) e hbase
  exact ⟨f, hsurj⟩

/-- Helper for Lemma 16-16.3-1: a split surjection of finite projective `A[G]`-modules identifies
the source class as the target class plus the class of an actual complement. -/
private theorem mem_projectivePositiveSubset_of_surjective_map_difference
    {P Q : FiniteProjectiveGroupAlgebraModule A G}
    (hf : ∃ f : P.V →ₗ[A[G]] Q.V, Function.Surjective f) :
    [P]ₚ₀ - [Q]ₚ₀ ∈ P⁺[A](G) := by
  rcases hf with ⟨f, hsurj⟩
  obtain ⟨i, hi⟩ := (Module.Projective.iff_split_of_projective f hsurj).1 inferInstance
  let T : Module.End A[G] P.V := i.comp f
  have hT_idem : IsIdempotentElem T := by
    -- The splitting relation `f ∘ i = id` makes `T = i ∘ f` into a projector.
    ext x
    simpa [T, LinearMap.comp_apply] using congrArg i (LinearMap.congr_fun hi (f x))
  let TRange :=
    rangeFiniteProjectiveGroupAlgebraModule (A := A) (G := G) P T hT_idem
  let TWitness :=
    rangeFiniteProjectiveGroupAlgebraModule (A := A) (G := G) P (1 - T) hT_idem.one_sub
  let toRange : Q.V →ₗ[A[G]] LinearMap.range T :=
    { toFun := fun q ↦ ⟨i q, ⟨i q, by
        simpa [T, LinearMap.comp_apply] using congrArg i (LinearMap.congr_fun hi q)⟩⟩
      map_add' := by
        intro x y
        ext <;> simp
      map_smul' := by
        intro a x
        ext <;> simp }
  let toQ : LinearMap.range T →ₗ[A[G]] Q.V :=
    f.comp (LinearMap.range T).subtype
  let eRangeQ : LinearMap.range T ≃ₗ[A[G]] Q.V :=
    { toFun := toQ
      invFun := toRange
      left_inv := by
        intro x
        apply Subtype.ext
        -- Every point in the range of an idempotent projector is fixed by that projector.
        simpa [toQ, toRange, T] using
          congrArg Subtype.val
            (LinearMap.IsResidueFieldReduction.range_element_fixed_of_isIdempotentElem
              T hT_idem x)
      right_inv := by
        intro q
        simpa [toQ, toRange, T, LinearMap.comp_apply] using LinearMap.congr_fun hi q
      map_add' := by
        intro x y
        simpa [toQ] using toQ.map_add x y
      map_smul' := by
        intro a x
        simpa [toQ] using toQ.map_smul a x }
  have hcompl :
      IsCompl (LinearMap.range T) (LinearMap.range (1 - T)) := by
    -- For an idempotent projector, the complementary summand is the range of `1 - T`.
    simpa [LinearMap.IsIdempotentElem.ker_eq_range_one_sub (p := T) hT_idem] using
      (LinearMap.IsIdempotentElem.isCompl hT_idem :
        IsCompl (LinearMap.range T) (LinearMap.ker T))
  let eProd :=
    Submodule.prodEquivOfIsCompl (LinearMap.range T) (LinearMap.range (1 - T)) hcompl
  obtain ⟨Wprod, hWprod_equiv, hWprod_class⟩ :=
    exists_product_projective_module_class_eq_add (R := A) (G := G) TRange TWitness
  have hPclass : [P]ₚ₀ = [Wprod]ₚ₀ := by
    -- Compare `P` with the explicit product of the image and complementary image of `T`.
    rcases hWprod_equiv with ⟨eWprod⟩
    exact
      (finiteProjectiveGroupAlgebraGrothendieckClass_eq_iff_nonempty_linearEquiv
        (A := A) (G := G) P Wprod).2
        ⟨eProd.symm.trans eWprod.symm⟩
  have hRangeClass : [TRange]ₚ₀ = [Q]ₚ₀ := by
    -- The projector image is exactly the split copy of `Q`.
    exact
      (finiteProjectiveGroupAlgebraGrothendieckClass_eq_iff_nonempty_linearEquiv
        (A := A) (G := G) TRange Q).2
        ⟨eRangeQ⟩
  refine (mem_projectivePositiveSubset_iff A G).2 ?_
  refine ⟨TWitness, ?_⟩
  -- Rewrite the source class through the product decomposition and cancel the split copy of `Q`.
  apply (eq_sub_iff_add_eq'.2 ?_)
  calc
    [Q]ₚ₀ + [TWitness]ₚ₀ = [TRange]ₚ₀ + [TWitness]ₚ₀ := by rw [hRangeClass]
    _ = [Wprod]ₚ₀ := hWprod_class.symm
    _ = [P]ₚ₀ := hPclass.symm

-- Proof sketch: write `x` as a difference `[P]ₚ₀ - [Q]ₚ₀`, show that positivity of the reduced
-- difference gives a surjection `P_k → Q_k`, lift that surjection upstairs, and then read the
-- split complement back as an actual positive witness for `x`.
/-- Helper for Lemma 16-16.3-1: if the reduction of a projective Grothendieck class is actual over
the residue field, then the original class is already actual over `A`. -/
private theorem mem_projectivePositiveSubset_of_reduction_mem
    {x : P₀[A](G)}
    (hx : projectiveGrothendieckReductionHom (A := A) (G := G) x ∈ P⁺[k](G)) :
    x ∈ P⁺[A](G) := by
  obtain ⟨P, Q, hxPQ⟩ := exists_projective_class_difference_rep_local (A := A) (G := G) x
  have hred :
      [P.residueFieldReduction]ₚ₀ - [Q.residueFieldReduction]ₚ₀ ∈ P⁺[k](G) := by
    -- Rewrite the reduction of `x` through the chosen difference presentation.
    simpa [hxPQ, map_sub] using hx
  obtain ⟨fbar, hfbar⟩ :=
    surjective_map_of_positive_projective_difference_residueField
      (A := A) (G := G) hred
  obtain ⟨f, hf⟩ :=
    lift_surjective_reduction_map_local (A := A) (G := G) fbar hfbar
  have hpos : [P]ₚ₀ - [Q]ₚ₀ ∈ P⁺[A](G) :=
    mem_projectivePositiveSubset_of_surjective_map_difference
      (A := A) (G := G) ⟨f, hf⟩
  simpa [hxPQ] using hpos

-- Proof sketch: transport the projective class `x` to `P_k(G)` using the canonical reduction
-- homomorphism. Over the residue field the projective-envelope basis identifies actual projective
-- classes with a positive cone, so the field-case lemma shows that the reduced class is actual.
-- The previous local-ring reflection lemma then transports that positivity back upstairs.
/-- Lemma 16-16.3-1: if a positive multiple of a class in `P_A(G)` is the class of an actual
finite projective `A[G]`-module, then the class itself already belongs to the source-facing
positive subset `P_A^+(G)`, written here as `P⁺[A](G)`. -/
theorem mem_projectivePositiveSubset_of_nsmul_mem
    {x : P₀[A](G)} {n : ℕ} (hn : 1 ≤ n)
    (hx : n • x ∈ P⁺[A](G)) :
    x ∈ P⁺[A](G) := by
  let red : P₀[A](G) →+ P₀[k](G) :=
    projectiveGrothendieckReductionHom (A := A) (G := G)
  have hxk : n • red x ∈ P⁺[k](G) :=
    reduction_nsmul_mem_projectivePositiveSubset (A := A) (G := G) (x := x) (n := n) hx
  have hxk' : red x ∈ P⁺[k](G) :=
    @mem_projectivePositiveSubset_of_nsmul_mem_residueField
      k inferInstance G inferInstance inferInstance (red x) n hn hxk
  -- The remaining local-ring input is positivity reflection along reduction.
  exact mem_projectivePositiveSubset_of_reduction_mem (A := A) (G := G) hxk'

end ProjectivePositiveSubset

end Representation

/-! ### Proposition_16_16_3_2 (from Chap16) -/
noncomputable section

open scoped Representation

universe u

namespace Representation

section

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A]
variable {A' : Type u} [CommRing A'] [IsLocalRing A']
  [Algebra A A'] [Module.Finite A A']
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {K' : Type u} [Field K'] [Algebra A' K'] [Algebra A K'] [IsFractionRing A' K']
variable [Algebra K K'] [IsScalarTower A A' K'] [IsScalarTower A K K'] [FiniteDimensional K K']
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]
variable [CharP (IsLocalRing.ResidueField A) p]
variable [HasEnoughRootsOfUnity K (Monoid.exponent G)]

local notation "k" => IsLocalRing.ResidueField A
local notation "k'" => IsLocalRing.ResidueField A'
local notation:max "P_k(" G ")" => finiteProjectiveGroupAlgebraGrothendieckGroup k G
local notation:max "P_k'(" G ")" => finiteProjectiveGroupAlgebraGrothendieckGroup k' G
local notation "eA" => (projectiveGrothendieckBaseChangeHom K' : P₀[A](G) →+ R₀[K'](G))
local notation "eA'" => (projectiveGrothendieckBaseChangeHom K' : P₀[A'](G) →+ R₀[K'](G))

/- Domain-style sampling for Proposition 16-16.3-2:
* primary domain: projective Grothendieck classes under scalar extension to the common fraction
  field `K'`, with LinearRepresentations_Serre_1977's source-facing actual-projective images over the finite local extension
  `A ⟶ A'`;
* relevant owner declarations inspected in this domain:
  `FiniteProjectiveGroupAlgebraModule`,
  `projectivePositiveSubset`,
  `projectiveGrothendieckScalarExtensionHom`,
  `projectiveGrothendieckBaseChangeHom`,
  `projectiveGrothendieckReductionEquiv`;
* best owner abstraction: the Chapter `16` scalar-extension owners
  `projectiveGrothendieckScalarExtensionHom A K' : P₀[k](G) →+ R₀[K'](G)` and
  `projectiveGrothendieckScalarExtensionHom A' K' : P₀[k'](G) →+ R₀[K'](G)`, with the
  source-facing actual projective images over `A` and `A'` mapped into them through the reduction
  equivalences `P₀[A](G) ≃+ P₀[k](G)` and `P₀[A'](G) ≃+ P₀[k'](G)`.
* source/core/bridge triage:
  source-facing: LinearRepresentations_Serre_1977's conclusion that `x` comes from an actual projective `A[G]`-module;
  core/canonical: the scalar-extension maps
    `projectiveGrothendieckScalarExtensionHom A K'`,
    `projectiveGrothendieckScalarExtensionHom A' K'`, and the positive subsets
    `P⁺[k](G)`, `P⁺[k'](G)`;
  bridge/view: this proposition, which keeps the source-facing image statements
    `eA '' P⁺[A](G)` and `eA' '' P⁺[A'](G)` as the public surface while treating the residue-field
    scalar-extension owners as the underlying canonical layer.
Primitive data vs derived API:
* primitive data: membership in the canonical scalar-extension positive images
  `(projectiveGrothendieckScalarExtensionHom A K' : P₀[k](G) →+ R₀[K'](G)) '' P⁺[k](G)` and
  `(projectiveGrothendieckScalarExtensionHom A' K' : P₀[k'](G) →+ R₀[K'](G)) '' P⁺[k'](G)`;
* derived API: the source-facing projective `A[G]`- and `A'[G]`-module witnesses extracted via
  `mem_projectivePositiveSubset_iff` and the reduction equivalences.
This file therefore keeps the image-membership theorem as the main entry and does not introduce a
parallel existential/uniqueness owner.
-/

-- Proof sketch: the helper theorem below sends the source-facing positive-image hypothesis
-- `n • x ∈ eA' '' P⁺[A'](G)` into the canonical residue-field scalar-extension positive image over
-- `A'`. Theorem `16-16.2-2` then forces the character of `x` to vanish on `p`-singular
-- elements, and the `K`-valuedness hypothesis descends `x` from `R_K'(G)` to the corresponding
-- projective scalar-extension range over `A`. Lemma `16-16.3-1` is the source-facing bridge that
-- turns the resulting canonical positivity back into the image `eA '' P⁺[A](G)`.
variable (K)

/-- The source-facing image of actual projective `A[G]`-classes in `R_K'(G)` lies in the canonical
residue-field scalar-extension positive image. -/
theorem projectivePositiveImage_subset_scalarExtensionPositiveImage
    [HenselianLocalRing A] :
    eA '' P⁺[A](G) ⊆
      (projectiveGrothendieckScalarExtensionHom A K' : P_k(G) →+ R₀[K'](G)) '' P⁺[k](G) := by
  rintro x ⟨y, hy, rfl⟩
  rcases (mem_projectivePositiveSubset_iff A G).1 hy with ⟨P, rfl⟩
  refine ⟨[P.residueFieldReduction]ₚ₀, ?_, ?_⟩
  · exact (mem_projectivePositiveSubset_iff k G).2 ⟨P.residueFieldReduction, rfl⟩
  · have hred' :
        projectiveGrothendieckReductionEquiv (A := A) (G := G) [P]ₚ₀ =
          [P.residueFieldReduction]ₚ₀ := by
      -- On generators, reduction identifies an actual projective class with its residue-field
      -- reduction class.
      change
        projectiveGrothendieckReductionHom (A := A) (G := G) [P]ₚ₀ =
          [P.residueFieldReduction]ₚ₀
      exact projectiveGrothendieckReductionHom_projectiveClass_eq (A := A) (G := G) P
    have hred :
        (projectiveGrothendieckReductionEquiv (A := A) (G := G)).symm
            [P.residueFieldReduction]ₚ₀ = [P]ₚ₀ := by
      rw [← hred']
      exact
        (projectiveGrothendieckReductionEquiv (A := A) (G := G)).symm_apply_apply [P]ₚ₀
    simp [projectiveGrothendieckScalarExtensionHom_apply,
      projectiveGrothendieckBaseChangeHom_projectiveClass_eq, hred]

/-- Helper for Proposition 16-16.3-2: the residue field of the finite local extension `A → A'`
still has characteristic `p`. -/
private theorem charP_residueField_of_local_extension
    {A : Type u} [CommRing A] [IsLocalRing A]
    {A' : Type u} [CommRing A'] [IsLocalRing A'] [Algebra A A'] [Module.Finite A A']
    {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
    {K' : Type u} [Field K'] [Algebra A' K'] [Algebra A K'] [IsFractionRing A' K']
    [Algebra K K'] [IsScalarTower A A' K'] [IsScalarTower A K K'] [FiniteDimensional K K']
    {p : ℕ} [Fact p.Prime] [CharP (IsLocalRing.ResidueField A) p] :
    CharP (IsLocalRing.ResidueField A') p := by
  -- Embed `A` into `A'` by composing with the injective maps into the common fraction field `K'`.
  have hAK : Function.Injective (algebraMap A K) := by
    simpa [faithfulSMul_iff_algebraMap_injective] using
      (inferInstance : FaithfulSMul A K)
  have hKK' : Function.Injective (algebraMap K K') := RingHom.injective _
  have hAK' : Function.Injective (algebraMap A K') := by
    simpa [IsScalarTower.algebraMap_eq A K K'] using hKK'.comp hAK
  have hcomp : Function.Injective ((algebraMap A' K') ∘ (algebraMap A A')) := by
    simpa [IsScalarTower.algebraMap_eq A A' K'] using hAK'
  have hAA' : Function.Injective (algebraMap A A') := Function.Injective.of_comp hcomp
  -- The integral finite extension `A → A'` is therefore a local ring homomorphism, so it induces
  -- an injective map on residue fields.
  let _ : FaithfulSMul A A' :=
    (faithfulSMul_iff_algebraMap_injective A A').2 hAA'
  let _ : IsLocalHom (algebraMap A A') := by
    infer_instance
  let f : IsLocalRing.ResidueField A →+* IsLocalRing.ResidueField A' :=
    IsLocalRing.ResidueField.map (algebraMap A A')
  exact charP_of_injective_ringHom f.injective p

/-- Helper for Proposition 16-16.3-2: on an actual projective generator, scalar extension from
`K` to `K'` after base change agrees with direct base change to `K'`. -/
private theorem finiteRepGrothendieckScalarExtension_projectiveClass_eq_direct
    (P : FiniteProjectiveGroupAlgebraModule A G) :
    finiteRepGrothendieckScalarExtensionHom K K' G [P.scalarExtension K]₀ =
      [P.scalarExtension K']₀ := by
  -- Reassociate the iterated tensor product and collapse the redundant middle `K`-factor.
  rw [finiteRepGrothendieckScalarExtensionHom_class_eq]
  refine finiteRepGrothendieckClass_eq_of_nonempty_iso ?_
  refine ⟨Representation.Equiv.toFDRepIso ?_⟩
  refine Representation.Equiv.mk
    ((TensorProduct.AlgebraTensorModule.assoc A K K' K' K P.V).symm.trans
      (TensorProduct.AlgebraTensorModule.congr
        (TensorProduct.AlgebraTensorModule.rid K K' K')
        (LinearEquiv.refl A P.V))) ?_
  intro g
  ext x
  rfl

/-- Helper for Proposition 16-16.3-2: further scalar extension commutes with the source-facing
projective base-change map. -/
private theorem finiteRepGrothendieckScalarExtension_comp_projectiveGrothendieckBaseChangeHom_eq :
    (finiteRepGrothendieckScalarExtensionHom K K' G).comp
      (projectiveGrothendieckBaseChangeHom (A := A) (G := G) K) =
        projectiveGrothendieckBaseChangeHom (A := A) (G := G) K' := by
  -- Check the identity on projective generators before extending additively to the quotient.
  apply AddMonoidHom.ext
  intro x
  refine Quotient.inductionOn x ?_
  intro y
  refine FreeAbelianGroup.induction_on y ?_ ?_ ?_ ?_
  · simp [projectiveGrothendieckBaseChangeHom]
  · intro P
    -- On generators, reuse the direct scalar-extension comparison before descending additively.
    simp [projectiveGrothendieckBaseChangeHom,
      finiteRepGrothendieckScalarExtension_projectiveClass_eq_direct
        (A := A) (K := K) (K' := K') (G := G) P]
  · intro y' hy'
    simpa using congrArg Neg.neg hy'
  · intro y₁ y₂ hy₁ hy₂
    simp [map_add, hy₁, hy₂]

/-- Helper for Proposition 16-16.3-2: if a positive multiple of `x` already comes from an actual
projective `A'[G]`-module, then the character of `x` vanishes on `p`-singular elements. -/
private theorem character_eq_zero_on_pSingular_of_nsmul_mem_projectivePositiveImage
    {A : Type u} [CommRing A] [IsLocalRing A]
    {A' : Type u} [CommRing A'] [IsLocalRing A'] [Algebra A A'] [Module.Finite A A']
    {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
    {K' : Type u} [Field K'] [Algebra A' K'] [Algebra A K'] [IsFractionRing A' K']
    [Algebra K K'] [IsScalarTower A A' K'] [IsScalarTower A K K'] [FiniteDimensional K K']
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] [CharP (IsLocalRing.ResidueField A) p]
    [HenselianLocalRing A']
    {x : R₀[K'](G)} {n : ℕ} (hn : 1 ≤ n)
    (hx :
      n • x ∈
        (projectiveGrothendieckBaseChangeHom (A := A') (G := G) K') '' P⁺[A'](G)) :
    ∀ g : G, ¬ IsPRegular p g → finiteRepGrothendieckCharacter K' G x g = 0 := by
  -- Route correction: the residue-field characteristic bridge is now available, so the only
  -- remaining work is the source-faithful cancellation from the vanishing of `χ_(n • x)` to the
  -- vanishing of `χ_x`.
  let _ := hn
  let _ := hx
  let _ : CharP (IsLocalRing.ResidueField A') p :=
    charP_residueField_of_local_extension (A := A) (A' := A') (K := K) (K' := K') (p := p)
  sorry

/-- Helper for Proposition 16-16.3-2: the source-facing base-change map over the actual fraction
field `K` is injective. -/
private theorem projective_baseChange_injective
    [HenselianLocalRing A] :
    Function.Injective (projectiveGrothendieckBaseChangeHom (A := A) (G := G) K) := by
  -- Reflect equality of source-facing base-change classes through the split injectivity of the
  -- residue-field scalar-extension map and then back across the reduction equivalence.
  obtain ⟨s, hs⟩ :=
    projectiveGrothendieckScalarExtensionHom_split_injective
      (A := A) (K := K) (G := G)
  intro x y hxy
  have hred :
      projectiveGrothendieckReductionEquiv (A := A) (G := G) x =
        projectiveGrothendieckReductionEquiv (A := A) (G := G) y := by
    apply hs.injective
    simpa [projectiveGrothendieckScalarExtensionHom_apply] using hxy
  exact (projectiveGrothendieckReductionEquiv (A := A) (G := G)).injective hred

/-- Helper for Proposition 16-16.3-2: restricting a projective `A'[G]`-module along
`A[G] → A'[G]` and comparing characters produces the expected
`[K' : K]`-multiple in `R_K'(G)`. -/
private theorem restricted_projective_witness_class_eq_extension_degree_nsmul
    (x : R₀[K'](G))
    (hchar : IsValuedInBaseField K (finiteRepGrothendieckCharacter K' G x))
    {n : ℕ} (P' : FiniteProjectiveGroupAlgebraModule A' G)
    (hP' : projectiveGrothendieckBaseChangeHom (A := A') (G := G) K' [P']ₚ₀ = n • x) :
    ∃ E : FiniteProjectiveGroupAlgebraModule A G,
      projectiveGrothendieckBaseChangeHom (A := A) (G := G) K' [E]ₚ₀ =
        ((n * Module.finrank K K' : ℕ) • x) := by
  -- Route correction: the remaining gap is exactly LinearRepresentations_Serre_1977's restricted-witness comparison over the
  -- actual fraction field `K`; the K'-level placeholder route was discarded.
  let _ := x
  let _ := hchar
  let _ := P'
  let _ := hP'
  sorry

/-- Proposition 16-16.3-2: if `K' / K` is finite, the ordinary character of
`x ∈ R_K'(G)` is `K`-valued, and some positive multiple of `x` lies in the image
`eA' '' P⁺[A'](G)`, then `x` itself lies in the source-facing positive image
`eA '' P⁺[A](G)`. This is the bridge form of the canonical Chapter `16` scalar-extension
criterion. -/
theorem mem_projectivePositiveImage_of_character_valuedInBaseField
    (x : R₀[K'](G))
    (hchar : IsValuedInBaseField K (finiteRepGrothendieckCharacter K' G x))
    (hnsmul : ∃ n : ℕ, 1 ≤ n ∧ n • x ∈ eA' '' P⁺[A'](G))
    : x ∈ eA '' P⁺[A](G) := by
  -- Route correction: the injectivity bridge is now in place. The remaining source-faithful work
  -- is to descend from the `A'`-witness by proving p-singular vanishing for `x` itself and then
  -- comparing the restricted witness over `K`.
  let _ := x
  let _ := hchar
  let _ := hnsmul
  sorry

end

end Representation

/-! ### Proposition_16_16_3_3 (from Chap16) -/
noncomputable section

universe u

open scoped Representation

namespace Representation

section

variable {K : Type u} [Field K]
variable {G : Type u} [Group G]

/- Domain-style sampling for Proposition 16-16.3-3:
* primary domain: Grothendieck groups in modular representation theory, with actual
  finite-dimensional and finite-projective representation classes tracked through scalar extension
  and reduction;
* relevant owner declarations inspected in this domain:
  `finiteRepGrothendieckClass`,
  `projectivePositiveSubset`,
  `projectiveGrothendieckScalarExtensionHom`,
  `decompositionHom`;
* best owner abstraction: the canonical additive homomorphisms on Grothendieck groups, with this
  file owning only the source-facing actual subset `R⁺[K](G)` and condition `(R)`;
* primitive data: actual finite-dimensional `K[G]`-representations through
  `finiteRepGrothendieckClass`;
* derived API: the bridge theorem identifying the source-facing image `e '' P⁺[k](G)` with the
  canonical range owner `e.range` intersected with `R⁺[K](G)`.

Source/core/bridge triage:
* source-facing: `R⁺[K](G)` and `SatisfiesConditionR`;
* core/canonical: `projectiveGrothendieckScalarExtensionHom` and `decompositionHom`;
* bridge/view: Proposition `16-16.3-3`, which compares the source-facing positive projective image
  with the canonical scalar-extension range inside `R₀[K](G)`.
-/

section FiniteRepPositiveSubset

/-- LinearRepresentations_Serre_1977's actual positive subset `R_K^+(G)`, written here as `R⁺[K](G)`, consists of the classes
in `R_K(G)` represented by actual finite-dimensional `K[G]`-representations. -/
def finiteRepPositiveSubset
    (K : Type u) [Field K] (G : Type u) [Group G] :
    Set (R₀[K](G)) :=
  Set.range (finiteRepGrothendieckClass K G)

scoped[Representation] notation:max "R⁺[" K "](" G ")" =>
  finiteRepPositiveSubset K G

/-- Membership in `R_K^+(G)` means being the class of some actual finite-dimensional
`K[G]`-representation. -/
@[simp] theorem mem_finiteRepPositiveSubset_iff
    {x : R₀[K](G)} :
    x ∈ R⁺[K](G) ↔
      ∃ V : FDRep K G, [V]₀ = x :=
  Iff.rfl

end FiniteRepPositiveSubset

variable [Finite G]

/-- LinearRepresentations_Serre_1977's condition `(R)` for a subset `RKplus ⊆ R_K(G)` is the existence of a finite local
overring `A'` of `A` with fraction field `K'`, such that the scalar-extension map
`R_K(G) → R_K'(G)` identifies `RKplus` with the preimage of the actual positive cone in
`R_K'(G)`, and the decomposition map `R_K'(G) → R_k'(G)` sends that actual positive cone onto the
actual positive cone over the residue field `k' = IsLocalRing.ResidueField A'`. -/
def SatisfiesConditionR
    (RKplus : Set (R₀[K](G))) (A : Type u) [CommRing A] [IsLocalRing A]
    [Algebra A K] [IsFractionRing A K] : Prop :=
  ∃ (A' : Type u) (_ : CommRing A') (_ : IsLocalRing A') (_ : Algebra A A')
      (_ : Module.Finite A A') (K' : Type u) (_ : Field K') (_ : Algebra A' K')
      (_ : Algebra A K') (_ : IsFractionRing A' K') (_ : Algebra K K')
      (_ : IsScalarTower A A' K') (_ : IsScalarTower A K K')
      (_ : FiniteDimensional K K'),
    RKplus = (finiteRepGrothendieckScalarExtensionHom K K' G) ⁻¹' R⁺[K'](G) ∧
      decompositionHom A' K' G '' R⁺[K'](G) = R⁺[IsLocalRing.ResidueField A'](G)

variable {A : Type u} [CommRing A] [IsLocalRing A] [Algebra A K] [IsFractionRing A K]

local notation "k" => IsLocalRing.ResidueField A
local notation "e" =>
  (projectiveGrothendieckScalarExtensionHom A K : P₀[k](G) →+ R₀[K](G))

-- Proof sketch: use Proposition `16-16.3-2` to descend positive projective classes from a finite
-- extension satisfying condition `(R)`. Through the canonical reduction equivalence
-- `P_A(G) ≃ P_k(G)`, this identifies the image of the source-facing positive subset `P_k^+(G)`
-- under LinearRepresentations_Serre_1977's scalar-extension owner `e` with the intersection of the full scalar-extension
-- range of `e` and the actual positive subset `R⁺[K](G)`.
/-- Proposition 16-16.3-3: if condition `(R)` holds for the positive subset `R_K^+(G)`, then the
image of the source-facing positive subset `P_k^+(G)`, under LinearRepresentations_Serre_1977's canonical scalar-extension
homomorphism `e : P_k(G) → R_K(G)`, is exactly the intersection of the range of `e` with
`R_K^+(G)`. Here `k = IsLocalRing.ResidueField A`. -/
theorem SatisfiesConditionR.image_eq_range_inter_positive
    (hR : SatisfiesConditionR (R⁺[K](G)) A) :
    e '' P⁺[k](G) =
      ((e).range : Set (R₀[K](G))) ∩ R⁺[K](G) := sorry

end

end Representation

/-! ### Remark_16_16_3_5 (from Chap16) -/
noncomputable section

open CategoryTheory

universe u

namespace Representation

namespace FDRep

variable {A : Type u} [CommRing A] [IsLocalRing A]
variable {G : Type u} [Group G]

/-- A residue-field finite-dimensional representation has an `(R')`-lift for the fraction-field
setting `K/A` if it is obtained, up to equivariant isomorphism, by reducing a stable `A`-lattice
inside a simple finite-dimensional `K[G]`-representation. This is the per-object owner on the
canonical residue-field object `S : FDRep (IsLocalRing.ResidueField A) G` behind LinearRepresentations_Serre_1977's
condition `(R')`. -/
def HasRPrimeLift (S : FDRep (IsLocalRing.ResidueField A) G)
    (K : Type u) [Field K] [Algebra A K] [IsFractionRing A K] : Prop :=
  ∃ X : FDRep K G, Simple X ∧
    ∃ L : StableLattice A X.ρ, Nonempty (FDRep.of L.reductionRepresentation ≅ S)

end FDRep

section

variable (A : Type u) [CommRing A] [IsLocalRing A]
variable (K : Type u) [Field K] [Algebra A K] [IsFractionRing A K]
variable (G : Type u) [Group G]

local notation "k" => IsLocalRing.ResidueField A

/- Domain-style sampling for this item:
* primary domain: modular lifting of simple residue-field representations through stable lattices
  inside simple finite-dimensional fraction-field representations;
* relevant owner declarations inspected before refining:
  `StableLattice.reductionRepresentation`,
  `Representation.exists_stableLattice`,
  `decompositionHom_finiteRepClass_eq`;
* best owner abstraction here is the per-object predicate `FDRep.HasRPrimeLift` on the canonical
  owner `S : FDRep k G`, with the global condition `(R')` obtained by quantifying over simple
  objects;
* source/core/bridge triage:
  source-facing: LinearRepresentations_Serre_1977's condition `(R')` for the fixed fraction-field setting `K/A`;
  core/canonical: the owner `FDRep.HasRPrimeLift` on residue-field objects together with the
  fraction-field owner `FDRep` for lifts;
  bridge/view: the canonical reduction `FDRep.of L.reductionRepresentation`.

Primitive data vs derived API:
* primitive data: a simple finite-dimensional `K[G]`-representation and a stable lattice in it;
* derived API: the bundled reduction `FDRep.of L.reductionRepresentation` and the global
  quantification forming `SatisfiesConditionRPrime`.
-/

/-- LinearRepresentations_Serre_1977's condition `(R')` for the fraction-field setting `K/A`: every simple finite-dimensional
representation over the residue field `k = IsLocalRing.ResidueField A` is obtained, up to
equivariant isomorphism, by reducing a stable `A`-lattice inside a simple finite-dimensional
`K[G]`-representation. -/
def SatisfiesConditionRPrime : Prop :=
  ∀ S : FDRep k G, Simple S →
    FDRep.HasRPrimeLift S K

-- Proof sketch: under LinearRepresentations_Serre_1977's sufficiently-large-field hypothesis, the decomposition map is
-- surjective on simple modular classes; realize a chosen lift by a stable `A`-lattice in a
-- finite-dimensional `K[G]`-module, and use the standard rigidity of simple reductions to arrange
-- the lifted representation to be irreducible.
/-- Remark 16-16.3-5: if `K` is sufficiently large, then the fraction-field setting `K/A`
satisfies LinearRepresentations_Serre_1977's condition `(R')`. Equivalently, every simple `k[G]`-module is the reduction
modulo the maximal ideal of a stable lattice in an irreducible finite-dimensional
`K[G]`-representation. -/
theorem satisfiesConditionRPrime_of_sufficiently_large
    [Finite G]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)] :
    SatisfiesConditionRPrime A K G := sorry

end

end Representation

/-! ### Theorem_16_16_3_6 (from Chap16) -/
noncomputable section

universe u

open scoped Representation

namespace Representation

section

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable [CharP (IsLocalRing.ResidueField A) p]

/- Domain-style sampling for Theorem 16-16.3-6:
* primary domain: modular representation-theoretic lifting criteria for finite `p`-solvable
  groups, expressed through the Chapter `16` owner predicates `SatisfiesConditionR` and
  `SatisfiesConditionRPrime`;
* relevant owner declarations inspected in this domain:
  `IsPSolvableOfHeight`,
  `SatisfiesConditionR`,
  `FDRep.HasRPrimeLift`,
  `SatisfiesConditionRPrime`,
  `IsPSolvable`;
* best owner abstraction: the source-facing conjunction asserting that the fixed
  fraction-field/local-ring setting `K/A` satisfies LinearRepresentations_Serre_1977's conditions `(R)` and `(R')` under the
  canonical group-theoretic owner predicate `IsPSolvable p G`;
* primitive data: the owner predicates `IsPSolvable p G`, `SatisfiesConditionR (R⁺[K](G)) A`, and
  `SatisfiesConditionRPrime A K G`;
* derived API: the two projection theorems below extracting `(R)` and `(R')` separately from the
  source-facing Fong-Swan conjunction.

Source/core/bridge triage:
* source-facing: `fong_swan_of_isPSolvable`;
* core/canonical: `IsPSolvable`, `SatisfiesConditionR`, and `SatisfiesConditionRPrime`;
* bridge/view: the two projection lemmas, which do not introduce any new owner data.
-/

-- Proof sketch: argue by induction on a `p`-solvable height witness for `G`; the induction step
-- combines the recursive normal-subgroup structure with the Chapter 16 descent criteria for
-- condition `(R)` and the lattice-lifting statement `(R')`.
/-- Theorem 16-16.3-6: if the finite group `G` is `p`-solvable, then it satisfies LinearRepresentations_Serre_1977's
conditions `(R)` and `(R')`: the actual positive cone `R_K^+(G)` satisfies condition `(R)`, and
every simple finite-dimensional representation over the residue field of `A` lifts from a stable
lattice in an irreducible finite-dimensional `K`-representation of `G`. -/
theorem fong_swan_of_isPSolvable
    (hp : Nat.Prime p) (hG : IsPSolvable p G) :
    SatisfiesConditionR (R⁺[K](G)) A ∧
      SatisfiesConditionRPrime A K G := sorry

/-- The `(R')` half of Theorem `16-16.3-6`, obtained by projecting the Fong-Swan conjunction. -/
theorem satisfiesConditionRPrime_of_isPSolvable
    (hp : Nat.Prime p) (hG : IsPSolvable p G) :
    SatisfiesConditionRPrime A K G :=
  (fong_swan_of_isPSolvable hp hG).2

/-- The `(R)` half of Theorem `16-16.3-6`, obtained by projecting the Fong-Swan conjunction: a
`p`-solvable finite group satisfies LinearRepresentations_Serre_1977's condition `(R)` for actual `K[G]`-representation
classes. -/
theorem satisfiesConditionR_of_isPSolvable
    (hp : Nat.Prime p) (hG : IsPSolvable p G) :
    SatisfiesConditionR (R⁺[K](G)) A :=
  (fong_swan_of_isPSolvable hp hG).1

end

end Representation

/-! ### Corollary_16_16_4_2 (from Chap16) -/
noncomputable section

open scoped MonoidAlgebra
open Representation

universe u

namespace Representation

section

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [IsDomain A] [IsDiscreteValuationRing A]
local notation "k" => IsLocalRing.ResidueField A
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]

/-- Helper for Corollary 16-16.4-2: a stable lattice whose `A[G]`-module is projective yields an
actual finite projective `A[G]`-owner whose generic fiber is the original representation. -/
lemma projective_lift_iso_of_stable_lattice
    (V : FDRep K G) (L : StableLattice A V.ρ)
    (hproj : Module.Projective A[G] L.toRepresentation.asModule) :
    ∃ Q : FiniteProjectiveGroupAlgebraModule A G, Nonempty (Q.scalarExtension K ≅ V) := by
  -- Package the lattice as the canonical finite-projective `A[G]` owner.
  let Qfg : FGModuleCat A[G] := ⟨ModuleCat.of A[G] L.toSubmodule, by infer_instance⟩
  let Q : FiniteProjectiveGroupAlgebraModule A G := ⟨Qfg, by
    simpa using hproj⟩
  refine ⟨Q, ?_⟩
  -- The stable-lattice base-change equivalence is exactly the desired generic-fiber isomorphism.
  refine ⟨Representation.Equiv.toFDRepIso ?_⟩
  refine Representation.Equiv.mk (L.toSubmodule_subtype_isBaseChange.equiv) ?_
  intro g
  ext x
  simp [FiniteProjectiveGroupAlgebraModule.scalarExtension, Representation.ofModule']

/-- Helper for Corollary 16-16.4-2: defect zero produces an actual finite projective `A[G]`-lift
whose scalar-extension class is `[V]₀`. -/
lemma projective_scalar_extension_class_of_defect_zero
    [Fact p.Prime] [CharP k p]
    (V : FDRep K G) (hdefect : Representation.HasDefectZero V.ρ p) :
    ∃ Q : FiniteProjectiveGroupAlgebraModule A G, [Q.scalarExtension K]₀ = [V]₀ := by
  -- Choose a stable lattice and apply Proposition `16-16.4-1 (1)` to make it projective.
  obtain ⟨L⟩ := Representation.exists_stableLattice A V.ρ
  have hproj : Module.Projective A[G] L.toRepresentation.asModule :=
    L.projective_of_defect_zero hdefect
  -- Repackage that projective lattice as an actual finite projective owner.
  obtain ⟨Q, hQ⟩ :=
    projective_lift_iso_of_stable_lattice (A := A) (K := K) (G := G) V L hproj
  refine ⟨Q, ?_⟩
  -- Isomorphic finite-dimensional representations define the same Grothendieck class.
  exact finiteRepGrothendieckClass_eq_of_nonempty_iso (L := K) (G := G) hQ

/-- Helper for Corollary 16-16.4-2: an actual projective scalar-extension lift gives the exact
range witness needed by Theorem `16-16.2-1`. -/
lemma mem_projectiveGrothendieckScalarExtension_range_of_projective_scalar_extension_class
    (V : FDRep K G)
    (hV : ∃ Q : FiniteProjectiveGroupAlgebraModule A G, [Q.scalarExtension K]₀ = [V]₀) :
    [V]₀ ∈ (projectiveGrothendieckScalarExtensionHom A K : P₀[k](G) →+ R₀[K](G)).range := by
  rcases hV with ⟨Q, hQ⟩
  refine ⟨projectiveGrothendieckReductionEquiv (A := A) (G := G) [Q]ₚ₀, ?_⟩
  -- Evaluate LinearRepresentations_Serre_1977's scalar-extension map on the explicit projective witness.
  calc
    projectiveGrothendieckScalarExtensionHom A K
        ((projectiveGrothendieckReductionEquiv (A := A) (G := G)) [Q]ₚ₀) =
        [Q.scalarExtension K]₀ := by
          have hred :
              (projectiveGrothendieckReductionEquiv (A := A) (G := G)).symm
                  ((projectiveGrothendieckReductionEquiv (A := A) (G := G)) [Q]ₚ₀) = [Q]ₚ₀ := by
            exact
              (projectiveGrothendieckReductionEquiv (A := A) (G := G)).symm_apply_apply [Q]ₚ₀
          rw [projectiveGrothendieckScalarExtensionHom_apply]
          rw [hred]
          exact projectiveGrothendieckBaseChangeHom_projectiveClass_eq (K := K) Q
    _ = [V]₀ := hQ

/-- Corollary 16-16.4-2: for a defect-zero irreducible finite-dimensional `K`-representation, the
ordinary character is zero on `p`-singular elements of `G`. -/
theorem character_eq_zero_of_not_isPRegular_of_defect_zero
    [Fact p.Prime] [CharP k p]
    (V : FDRep K G) (hdefect : Representation.HasDefectZero V.ρ p)
    (g : G) (hg : ¬ IsPRegular p g) :
    V.character g = 0 := by
  -- Follow LinearRepresentations_Serre_1977's source route: defect zero gives an actual projective lattice lift.
  have hclass :
      ∃ Q : FiniteProjectiveGroupAlgebraModule A G, [Q.scalarExtension K]₀ = [V]₀ :=
    projective_scalar_extension_class_of_defect_zero
      (A := A) (K := K) (G := G) (p := p) V hdefect
  -- Convert that actual lift into the canonical range hypothesis of Theorem `16-16.2-1`.
  have hrange :
      [V]₀ ∈ (projectiveGrothendieckScalarExtensionHom A K : P₀[k](G) →+ R₀[K](G)).range :=
    mem_projectiveGrothendieckScalarExtension_range_of_projective_scalar_extension_class
      (A := A) (K := K) (G := G) V hclass
  -- The forward character-vanishing theorem now applies directly to the actual class `[V]₀`.
  have hvanish :=
    character_eq_zero_on_pSingular_of_mem_projectiveGrothendieckScalarExtension_range
      (A := A) (K := K) (G := G) (p := p) hrange g hg
  simpa [finiteRepGrothendieckCharacter_class] using hvanish

end

end Representation

/-! ### Exercise_16_16_4_4 (from Chap16) -/
noncomputable section

open Representation

local notation "A4" => alternatingGroup (Fin 4)
local notation "S4" => Equiv.Perm (Fin 4)

local instance fact_prime_two : Fact (Nat.Prime 2) := ⟨by decide⟩
local instance fact_prime_three : Fact (Nat.Prime 3) := ⟨by decide⟩

namespace Representation

/-- Helper for Exercise 16-16.4-4: an irreducible finite-dimensional complex representation of a
finite group has defect zero at `p` when the `p`-part of the group order divides its degree. -/
class HasDefectZero {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) [FiniteDimensional k V] (p : ℕ) [Finite G] [Fact p.Prime] :
    Prop where
  isIrreducible : ρ.IsIrreducible
  dvd_finrank : p ^ Nat.factorization (Nat.card G) p ∣ Module.finrank k ρ.asModule

end Representation

/-- Helper for Exercise 16-16.4-4: an irreducible complex representation has a nontrivial
underlying vector space. -/
lemma nontrivial_of_isIrreducible
    {G : Type} [Monoid G] {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) [ρ.IsIrreducible] : Nontrivial V := by
  -- If the space were trivial, the zero and whole subrepresentations would coincide.
  by_contra hV
  letI : Subsingleton V := not_nontrivial_iff_subsingleton.mp hV
  have hbot_top : (⊥ : Subrepresentation ρ) = ⊤ := by
    apply Subrepresentation.toSubmodule_injective
    ext x
    constructor
    · intro _
      trivial
    · intro _
      simpa using (Subsingleton.elim x 0)
  exact IsSimpleOrder.bot_ne_top hbot_top

/-- Helper for Exercise 16-16.4-4: a doubly pretransitive finite action has irreducible complex
augmentation representation. -/
lemma permutation_augmentation_isIrreducible_of_two_pretransitive
    {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X] [Nontrivial X]
    (h2 : MulAction.IsMultiplyPretransitive G X 2) :
    (Representation.permutationAugmentationRepresentation ℂ G X).IsIrreducible := by
  -- Chapter 7 turns double transitivity into the character criterion for augmentation
  -- irreducibility.
  letI : MulAction.IsMultiplyPretransitive G X 2 := h2
  letI : MulAction.IsPretransitive G X :=
    MulAction.isPretransitive_of_is_two_pretransitive (G := G) (α := X)
  have hpair :=
    (Representation.isTwoPretransitive_iff_pairActionHasDiagonalOrbits
      (G := G) (X := X)).mp h2
  have hsq :=
    (Representation.pairActionHasDiagonalOrbits_iff_character_square_pairing_eq_two
      (G := G) (X := X)).mp hpair
  exact
    (Representation.character_square_pairing_eq_two_iff_augmentation_isIrreducible
      (G := G) (X := X)).mp hsq

/-- Helper for Exercise 16-16.4-4: the augmentation constituent of the natural action on four
letters has degree `3`. -/
lemma fin_four_permutation_augmentation_finrank_three
    {G : Type} [Group G] [MulAction G (Fin 4)] :
    Module.finrank ℂ
      (Representation.permutationAugmentationSubrepresentation ℂ G (Fin 4)).toSubmodule = 3 := by
  letI : Invertible (Nat.card (Fin 4) : ℂ) := invertibleOfNonzero (by norm_num)
  -- Evaluate the permutation/augmentation character splitting at the identity.
  have hχ :=
    Representation.permutation_character_eq_trivial_add_augmentation
      (k := ℂ) (G := G) (X := Fin 4)
  have h1 : (4 : ℂ) = 1 + Representation.permutationAugmentationCharacter ℂ G (Fin 4) 1 := by
    simpa [Representation.char_one] using congrFun hχ 1
  have h2 := congrArg (fun z : ℂ => z - 1) h1
  norm_num at h2
  have hchar :
      (Representation.permutationAugmentationRepresentation ℂ G (Fin 4)).character 1 = 3 := by
    simpa [Representation.permutationAugmentationCharacter] using h2.symm
  -- The identity character value is the dimension of the representation.
  have hone :=
    Representation.char_one
      (ρ := Representation.permutationAugmentationRepresentation ℂ G (Fin 4))
  rw [hchar] at hone
  exact_mod_cast hone.symm

/-- Helper for Exercise 16-16.4-4: an irreducible finite-dimensional complex representation has
degree at most `√|G|`. -/
lemma fdrep_finrank_sq_le_card
    {G : Type} [Group G] [Finite G] (V : FDRep ℂ G)
    (hirr : Representation.IsIrreducible V.ρ) :
    Module.finrank ℂ V.V ^ 2 ≤ Nat.card G := by
  -- Turn the character orthogonality relation into a sum of nonnegative norm squares.
  letI : Representation.IsIrreducible V.ρ := hirr
  letI : CategoryTheory.Simple V := FDRep.simple_of_isIrreducible V
  letI : Fintype G := Fintype.ofFinite G
  letI : DecidableEq G := Classical.decEq G
  have hsum : ∑ g : G, Complex.normSq (V.character g) = Nat.card G := by
    have hterm :
        Finset.univ.sum (fun g : G ↦ (Complex.normSq (V.character g) : ℂ)) =
          Finset.univ.sum (fun g : G ↦ V.character g * V.character g⁻¹) := by
      refine Finset.sum_congr rfl fun g _ ↦ ?_
      calc
        (Complex.normSq (V.character g) : ℂ) = V.character g * star (V.character g) := by
          simpa [Complex.normSq_eq_norm_sq] using (Complex.mul_conj' (V.character g)).symm
        _ = V.character g * V.character g⁻¹ := by
          have hstar : star (V.character g) = V.character g⁻¹ := by
            simpa using
              (Representation.char_inv_eq_star_of_isOfFinOrder
                (ρ := V.ρ) g (isOfFinOrder_of_finite g)).symm
          rw [hstar]
    apply Complex.ofReal_injective
    calc
      ((∑ g : G, Complex.normSq (V.character g) : ℝ) : ℂ)
          = ∑ g : G, V.character g * V.character g⁻¹ := by
              simpa using hterm
      _ = Nat.card G := (FDRep.simple_iff_char_is_norm_one (k := ℂ) V).mp inferInstance
  have hle_real : (Module.finrank ℂ V.V ^ 2 : ℝ) ≤ Nat.card G := by
    have hnonneg :
        0 ≤ (Finset.univ.erase (1 : G)).sum (fun g : G ↦ Complex.normSq (V.character g)) := by
      exact Finset.sum_nonneg fun g _ ↦ Complex.normSq_nonneg (V.character g)
    have hsplit :=
      Finset.sum_erase_add (a := (1 : G)) (s := Finset.univ)
        (f := fun g : G ↦ Complex.normSq (V.character g)) (by simp)
    have hone : V.character 1 = Module.finrank ℂ V.V := by
      exact Representation.char_one (ρ := V.ρ)
    have hchar_one : Complex.normSq (V.character 1) = Module.finrank ℂ V.V ^ 2 := by
      rw [hone, Complex.normSq_eq_norm_sq]
      norm_num
    calc
      (Module.finrank ℂ V.V ^ 2 : ℝ) = Complex.normSq (V.character 1) := by
        symm
        exact hchar_one
      _ ≤ Complex.normSq (V.character 1) +
            (Finset.univ.erase (1 : G)).sum (fun g : G ↦ Complex.normSq (V.character g)) := by
          exact le_add_of_nonneg_right hnonneg
      _ = ∑ g : G, Complex.normSq (V.character g) := by
          calc
            Complex.normSq (V.character 1) +
                (Finset.univ.erase (1 : G)).sum (fun g : G ↦ Complex.normSq (V.character g)) =
              (Finset.univ.erase (1 : G)).sum (fun g : G ↦ Complex.normSq (V.character g)) +
                Complex.normSq (V.character 1) := by
                  rw [add_comm]
            _ = ∑ g : G, Complex.normSq (V.character g) := hsplit
      _ = Nat.card G := hsum
  exact_mod_cast hle_real

/- Domain-style sampling for this item:
* primary domain: defect-zero finite-dimensional complex representations of the finite groups
  `A₄` and `S₄`;
* relevant owner declarations inspected in this domain:
  `Representation.HasDefectZero`,
  `StableLattice.reduction_irreducible_of_defect_zero`,
  `character_eq_zero_of_not_isPRegular_of_defect_zero`,
  `simple_finiteRep_projective_defect_zero_and_cartan_tfae`;
* best owner abstraction: the bundled owner `FDRep ℂ G` together with the chapter-level owner
  predicate `HasDefectZero (V.ρ) p` on the underlying irreducible representation of `V`;
* source/core/bridge triage:
  source-facing: these four existence and nonexistence assertions for the concrete groups `A₄`
    and `S₄`;
  core/canonical: `FDRep ℂ G`, `Simple V`, and `Representation.HasDefectZero`;
  bridge/view: the passage from a bundled `FDRep` object `V` to its underlying representation
    `V.ρ`.

Primitive data vs derived API:
* primitive data: an actual finite-dimensional complex representation `V : FDRep ℂ G`;
* derived API: simplicity of `V`, already encoded inside the defect-zero owner
  `HasDefectZero (V.ρ) p`.

No new owner or wrapper is needed here: the exercise should stay source-facing, stated directly
in terms of the existing chapter owner `HasDefectZero (V.ρ) p` rather than through a parallel
local alias or package.
-/

-- Proof sketch: use the character table of `A₄`, whose irreducible complex degrees are
-- `1, 1, 1, 3`; none of these is divisible by the `2`-part `4` of `|A₄| = 12`.
/-- Exercise 16-16.4-4 (1): for `A₄`, there is no irreducible complex representation of the type
described by Proposition `16-16.4-1` when `p = 2`, i.e. no simple object of the canonical owner
`FDRep ℂ A₄` has defect zero at `2`. -/
theorem alternatingGroup_four_not_exists_irreducible_complex_representation_of_defect_zero_at_two :
    ¬ ∃ V : FDRep ℂ A4, HasDefectZero (V.ρ) 2 := by
  rintro ⟨V, hdefect⟩
  let n := Module.finrank ℂ (Representation.asModule V.ρ)
  letI : Representation.IsIrreducible V.ρ := hdefect.isIrreducible
  letI : Nontrivial V.V := nontrivial_of_isIrreducible (ρ := V.ρ)
  -- Character orthogonality gives the generic bound `n² ≤ |A₄| = 12`.
  have hbound : n ^ 2 ≤ 12 := by
    have hsq := fdrep_finrank_sq_le_card V hdefect.isIrreducible
    simpa [n, alternatingGroup.card_of_card_eq_four (α := Fin 4) (by simp)] using hsq
  -- Defect zero at `2` forces the `2`-part `4` of `|A₄|` to divide `n`.
  have hdvd : 4 ∣ n := by
    have hdvd' := hdefect.dvd_finrank
    rw [show Nat.card A4 = 12 by
      simpa using alternatingGroup.card_of_card_eq_four (α := Fin 4) (by simp)] at hdvd'
    have hpow : 2 ^ Nat.factorization 12 2 = 4 := by
      native_decide
    rw [hpow] at hdvd'
    simpa [n] using hdvd'
  have hpos : 0 < n := by
    simpa [n] using (Module.finrank_pos (R := ℂ) (M := V.V))
  rcases hdvd with ⟨k, hk⟩
  rw [hk] at hbound hpos
  have hkpos : 0 < k := by
    omega
  nlinarith [hbound, hkpos]

-- Proof sketch: use the standard degree-three irreducible representation of `A₄`, for example
-- the tetrahedral representation, and note that `3` is exactly the `3`-part of `|A₄| = 12`.
/-- Exercise 16-16.4-4 (2): for `A₄`, there is an irreducible complex representation of the type
described by Proposition `16-16.4-1` when `p = 3`, i.e. a simple object of the canonical owner
`FDRep ℂ A₄` with defect zero at `3`. -/
theorem alternatingGroup_four_exists_irreducible_complex_representation_of_defect_zero_at_three :
    ∃ V : FDRep ℂ A4, HasDefectZero (V.ρ) 3 := by
  let ρ := Representation.permutationAugmentationRepresentation ℂ A4 (Fin 4)
  let V : FDRep ℂ A4 := FDRep.of ρ
  have h2 : MulAction.IsMultiplyPretransitive A4 (Fin 4) 2 := by
    simpa using alternatingGroup.isMultiplyPretransitive (α := Fin 4)
  have hirr : ρ.IsIrreducible :=
    permutation_augmentation_isIrreducible_of_two_pretransitive h2
  have hdim :
      Module.finrank ℂ
        (Representation.permutationAugmentationSubrepresentation ℂ A4 (Fin 4)).toSubmodule = 3 :=
    fin_four_permutation_augmentation_finrank_three
  refine ⟨V, ?_⟩
  -- The standard augmentation representation has degree `3`, exactly the `3`-part of `|A₄|`.
  refine ⟨?_, ?_⟩
  · simpa [V, ρ] using hirr
  · rw [show Nat.card A4 = 12 by
      simpa using alternatingGroup.card_of_card_eq_four (α := Fin 4) (by simp)]
    have hpow : 3 ^ Nat.factorization 12 3 = 3 := by
      native_decide
    have hdimV : Module.finrank ℂ (Representation.asModule V.ρ) = 3 := by
      simpa [V, ρ] using hdim
    rw [hpow, hdimV]

-- Proof sketch: use the character table of `S₄`, whose irreducible complex degrees are
-- `1, 1, 2, 3, 3`; none of these is divisible by the `2`-part `8` of `|S₄| = 24`.
/-- Exercise 16-16.4-4 (3): for `S₄`, there is no irreducible complex representation of the type
described by Proposition `16-16.4-1` when `p = 2`, i.e. no simple object of the canonical owner
`FDRep ℂ S₄` has defect zero at `2`. -/
theorem symmetricGroup_four_not_exists_irreducible_complex_representation_of_defect_zero_at_two :
    ¬ ∃ V : FDRep ℂ S4, HasDefectZero (V.ρ) 2 := by
  rintro ⟨V, hdefect⟩
  let n := Module.finrank ℂ (Representation.asModule V.ρ)
  letI : Representation.IsIrreducible V.ρ := hdefect.isIrreducible
  letI : Nontrivial V.V := nontrivial_of_isIrreducible (ρ := V.ρ)
  have hcard : Nat.card S4 = 24 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm]
    norm_num
  -- The same orthogonality bound now gives `n² ≤ |S₄| = 24`.
  have hbound : n ^ 2 ≤ 24 := by
    have hsq := fdrep_finrank_sq_le_card V hdefect.isIrreducible
    simpa [n, hcard] using hsq
  -- Defect zero at `2` forces the `2`-part `8` of `|S₄|` to divide `n`.
  have hdvd : 8 ∣ n := by
    have hdvd' := hdefect.dvd_finrank
    rw [hcard] at hdvd'
    have hpow : 2 ^ Nat.factorization 24 2 = 8 := by
      native_decide
    rw [hpow] at hdvd'
    simpa [n] using hdvd'
  have hpos : 0 < n := by
    simpa [n] using (Module.finrank_pos (R := ℂ) (M := V.V))
  rcases hdvd with ⟨k, hk⟩
  rw [hk] at hbound hpos
  have hkpos : 0 < k := by
    omega
  nlinarith [hbound, hkpos]

-- Proof sketch: use either of the standard degree-three irreducible representations of `S₄`,
-- such as the quotient of the permutation representation by the diagonal line; its degree is
-- divisible by the `3`-part of `|S₄| = 24`.
/-- Exercise 16-16.4-4 (4): for `S₄`, there is an irreducible complex representation of the type
described by Proposition `16-16.4-1` when `p = 3`, i.e. a simple object of the canonical owner
`FDRep ℂ S₄` with defect zero at `3`. -/
theorem symmetricGroup_four_exists_irreducible_complex_representation_of_defect_zero_at_three :
    ∃ V : FDRep ℂ S4, HasDefectZero (V.ρ) 3 := by
  let ρ := Representation.permutationAugmentationRepresentation ℂ S4 (Fin 4)
  let V : FDRep ℂ S4 := FDRep.of ρ
  have h2 : MulAction.IsMultiplyPretransitive S4 (Fin 4) 2 := by
    simpa using Equiv.Perm.isMultiplyPretransitive (α := Fin 4) 2
  have hirr : ρ.IsIrreducible :=
    permutation_augmentation_isIrreducible_of_two_pretransitive h2
  have hdim :
      Module.finrank ℂ
        (Representation.permutationAugmentationSubrepresentation ℂ S4 (Fin 4)).toSubmodule = 3 :=
    fin_four_permutation_augmentation_finrank_three
  have hcard : Nat.card S4 = 24 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm]
    norm_num
  refine ⟨V, ?_⟩
  -- The same standard augmentation constituent has degree `3`, the `3`-part of `|S₄|`.
  refine ⟨?_, ?_⟩
  · simpa [V, ρ] using hirr
  · rw [hcard]
    have hpow : 3 ^ Nat.factorization 24 3 = 3 := by
      native_decide
    have hdimV : Module.finrank ℂ (Representation.asModule V.ρ) = 3 := by
      simpa [V, ρ] using hdim
    rw [hpow, hdimV]
