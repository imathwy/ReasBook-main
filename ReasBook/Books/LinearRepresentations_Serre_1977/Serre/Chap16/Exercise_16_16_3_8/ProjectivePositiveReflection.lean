import LinearRepresentations_Serre_1977.Serre.Chap14.Exercise_14_14_4_6.ProjectorRangeBridge
import LinearRepresentations_Serre_1977.Serre.Chap14.Corollary_14_14_4_3
import LinearRepresentations_Serre_1977.Serre.Chap14.Corollary_14_14_4_4

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped MonoidAlgebra TensorProduct ZeroObject
open scoped Representation

namespace Representation

section

variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {G : Type u} [Group G] [Finite G]

local notation "k" => IsLocalRing.ResidueField A
local notation:max "P⁺[" R "](" G ")" =>
  Set.range fun P : FiniteProjectiveGroupAlgebraModule R G ↦ [P]ₚ₀

/-- Helper for Exercise 16-16.3-8: the tensor-product residue-field reduction carries the
restricted `A[G]`-action coming from `A[G] → k[G]`. -/
local instance residueTensorModuleForPositiveReflection
    (P : FiniteProjectiveGroupAlgebraModule A G) :
    Module A[G] (k ⊗[A] P.V) :=
  Module.compHom (k ⊗[A] P.V) (MonoidAlgebra.mapRingHom G (algebraMap A k))

/-- Helper for Exercise 16-16.3-8: the restricted tensor-product action is compatible with the
scalar tower `A → A[G]`. -/
local instance residueTensorIsScalarTowerForPositiveReflection
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
      MonoidAlgebra.single (1 : G) (IsLocalRing.residue A a) • x =
          (IsLocalRing.residue A a) • x := by
            simpa only [hsingle] using
              (IsScalarTower.algebraMap_smul (k[G]) (IsLocalRing.residue A a) x)
      _ = a • x := by
            simpa [IsLocalRing.ResidueField.algebraMap_eq] using
              (IsScalarTower.algebraMap_smul k a x)

/-- Helper for Exercise 16-16.3-8: the binary product of two actual finite projective
`R[G]`-modules again represents the sum of their Grothendieck classes. -/
private theorem exists_product_projective_module_class_eq_add_local
    {R : Type u} [CommRing R] {G : Type u} [Group G]
    (P Q : FiniteProjectiveGroupAlgebraModule R G) :
    ∃ W : FiniteProjectiveGroupAlgebraModule R G,
      Nonempty (W.V ≃ₗ[R[G]] (P.V × Q.V)) ∧
      [W]ₚ₀ = [P]ₚ₀ + [Q]ₚ₀ := by
  -- Use the product module and the split product short exact sequence to read the relation.
  let W0 : ModuleCat R[G] := ModuleCat.of R[G] (P.V × Q.V)
  have hfinite : Module.Finite R[G] W0 := by
    change Module.Finite R[G] (P.V × Q.V)
    infer_instance
  let Wfg : FGModuleCat R[G] := ⟨W0, hfinite⟩
  have hproj : Module.Projective R[G] Wfg := by
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
  refine ⟨W, ⟨⟨LinearEquiv.refl R[G] (P.V × Q.V)⟩, ?_⟩⟩
  simpa [T, W, Wfg, W0] using
    finiteProjectiveGroupAlgebraGrothendieckClass_middle_eq_left_add_right
      (A := R) (G := G) T ⟨LinearEquiv.refl R[G] (P.V × Q.V)⟩

/-- Helper for Exercise 16-16.3-8: every class in `P_A(G)` is a difference of two actual
projective generator classes. -/
private theorem exists_projective_class_difference_rep_local
    (x : P₀[A](G)) :
    ∃ P Q : FiniteProjectiveGroupAlgebraModule A G, x = [P]ₚ₀ - [Q]ₚ₀ := by
  -- Descend the difference presentation through the free presentation of the Grothendieck group.
  refine QuotientAddGroup.induction_on x ?_
  intro a
  refine FreeAbelianGroup.induction_on a ?_ ?_ ?_ ?_
  · refine
      ⟨(0 : FiniteProjectiveGroupAlgebraModule A G),
        (0 : FiniteProjectiveGroupAlgebraModule A G), ?_⟩
    simp
  · intro P
    refine ⟨P, (0 : FiniteProjectiveGroupAlgebraModule A G), ?_⟩
    change [P]ₚ₀ = [P]ₚ₀ - [0]ₚ₀
    rw [finiteProjectiveGroupAlgebraGrothendieckClass_zero (A := A) (G := G)]
    exact (sub_zero [P]ₚ₀).symm
  · intro a ha
    rcases ha with ⟨P, Q, hPQ⟩
    refine ⟨Q, P, ?_⟩
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using congrArg Neg.neg hPQ
  · intro a b ha hb
    rcases ha with ⟨P, Q, hPQ⟩
    rcases hb with ⟨P', Q', hP'Q'⟩
    obtain ⟨W, -, hW⟩ :=
      exists_product_projective_module_class_eq_add_local (R := A) (G := G) P P'
    obtain ⟨Z, -, hZ⟩ :=
      exists_product_projective_module_class_eq_add_local (R := A) (G := G) Q Q'
    refine ⟨W, Z, ?_⟩
    calc
      QuotientAddGroup.mk' (finiteProjectiveGroupAlgebraGrothendieckRelations A G) (a + b) =
          QuotientAddGroup.mk' (finiteProjectiveGroupAlgebraGrothendieckRelations A G) a +
            QuotientAddGroup.mk' (finiteProjectiveGroupAlgebraGrothendieckRelations A G) b := by
            rfl
      _ = ([P]ₚ₀ - [Q]ₚ₀) + ([P']ₚ₀ - [Q']ₚ₀) := by
            simp [hPQ, hP'Q']
      _ = [W]ₚ₀ - [Z]ₚ₀ := by
            simp [hW, hZ, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

/-- Helper for Exercise 16-16.3-8: the canonical reduction map `P → k ⊗[A] P` is
`A[G]`-linear when the reduced module is viewed by restriction of scalars. -/
private noncomputable def reduction_groupAlgebraLinear_local
    (P : FiniteProjectiveGroupAlgebraModule A G) :
    P.V →ₗ[A[G]] (k ⊗[A] P.V) :=
  { toFun := TensorProduct.mk A k P.V 1
    map_add' := fun x y ↦ by
      simpa using (TensorProduct.mk A k P.V 1).map_add x y
    map_smul' := fun a x ↦ by
      -- Equivariance is checked on monoid-algebra generators and extended linearly.
      refine MonoidAlgebra.induction_on (p := fun a : A[G] =>
        (TensorProduct.mk A k P.V 1) (a • x) =
          a • (TensorProduct.mk A k P.V 1 x)) a ?_ ?_ ?_
      · intro g
        change (TensorProduct.mk A k P.V 1) (MonoidAlgebra.of A G g • x) =
          (MonoidAlgebra.mapRingHom G (algebraMap A k) (MonoidAlgebra.of A G g)) •
            (TensorProduct.mk A k P.V 1 x)
        simpa [MonoidAlgebra.of_apply] using
          (MonoidAlgebra.tensorProduct_mk_map_monoidAlgebra_of
            (Λ := A) (G := G) (P := P.V) g x)
      · intro a b ha hb
        rw [add_smul, map_add, ha, hb, add_smul]
      · intro c a ha
        simpa [smul_smul, ha] using congrArg (fun z ↦ c • z) ha }

/-- Helper for Exercise 16-16.3-8: the canonical reduction map onto `k ⊗[A] P` is surjective. -/
private theorem reduction_groupAlgebraLinear_surjective_local
    (P : FiniteProjectiveGroupAlgebraModule A G) :
    Function.Surjective (reduction_groupAlgebraLinear_local (A := A) (G := G) P) := by
  -- This is the standard tensor-product surjectivity of reduction modulo the maximal ideal.
  simpa [reduction_groupAlgebraLinear_local, IsLocalRing.ResidueField.algebraMap_eq] using
    (TensorProduct.mk_surjective (R := A) (M := P.V) (S := k) IsLocalRing.residue_surjective)

/-- Helper for Exercise 16-16.3-8: a reduced `k[G]`-linear map can be viewed as an
`A[G]`-linear map after restricting scalars along `A[G] → k[G]`. -/
private noncomputable def restrictReducedGroupAlgebraLinear_local
    {P Q : FiniteProjectiveGroupAlgebraModule A G}
    (g : (k ⊗[A] P.V) →ₗ[k[G]] (k ⊗[A] Q.V)) :
    (k ⊗[A] P.V) →ₗ[A[G]] (k ⊗[A] Q.V) :=
  { toFun := g
    map_add' := g.map_add
    map_smul' := fun a x ↦ by
      change g ((MonoidAlgebra.mapRingHom G (algebraMap A k)) a • x) =
          (MonoidAlgebra.mapRingHom G (algebraMap A k)) a • g x
      simpa using g.map_smul ((MonoidAlgebra.mapRingHom G (algebraMap A k)) a) x }

/-- Helper for Exercise 16-16.3-8: an idempotent range inside a finite projective
`A[G]`-module is again a finite projective `A[G]`-module. -/
private noncomputable def rangeFiniteProjectiveGroupAlgebraModule_local
    (P : FiniteProjectiveGroupAlgebraModule A G)
    (e : Module.End A[G] P.V) (he : IsIdempotentElem e) :
    FiniteProjectiveGroupAlgebraModule A G :=
  let W0 : ModuleCat A[G] := ModuleCat.of A[G] (LinearMap.range e)
  let hfinite : Module.Finite A[G] W0 := by
    change Module.Finite A[G] (LinearMap.range e)
    infer_instance
  let Wfg : FGModuleCat A[G] := ⟨W0, hfinite⟩
  let hproj : Module.Projective A[G] Wfg := by
    change Module.Projective A[G] (LinearMap.range e)
    exact
      LinearMap.IsResidueFieldReduction.projective_range_of_idempotent_endomorphism_general
        e he
  ⟨Wfg, hproj⟩

/-- Helper for Exercise 16-16.3-8: if a residue-field class difference is actual, then the
larger projective module already surjects onto the smaller one. -/
private theorem surjective_map_of_positive_projective_difference_residueField_local
    {Pbar Qbar : FiniteProjectiveGroupAlgebraModule k G}
    (hPQ : [Pbar]ₚ₀ - [Qbar]ₚ₀ ∈ P⁺[k](G)) :
    ∃ f : Pbar.V →ₗ[k[G]] Qbar.V, Function.Surjective f := by
  -- Rewrite the positive difference as a product decomposition and project to the second factor.
  rcases hPQ with ⟨Wbar, hWbar⟩
  obtain ⟨Ubar, hUbar_equiv, hUbar_class⟩ :=
    exists_product_projective_module_class_eq_add_local (R := k) (G := G) Wbar Qbar
  have hPclass : [Pbar]ₚ₀ = [Ubar]ₚ₀ := by
    calc
      [Pbar]ₚ₀ = [Wbar]ₚ₀ + [Qbar]ₚ₀ := by
        simpa [hWbar, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
          congrArg (fun z : P₀[k](G) ↦ z + [Qbar]ₚ₀) hWbar
      _ = [Ubar]ₚ₀ := hUbar_class.symm
  obtain ⟨ePU⟩ :=
    (finiteProjectiveGroupAlgebraGrothendieckClass_eq_iff_nonempty_linearEquiv
      (A := k) (G := G) Pbar Ubar).1 hPclass
  rcases hUbar_equiv with ⟨eUprod⟩
  let f : Pbar.V →ₗ[k[G]] Qbar.V :=
    (LinearMap.snd k[G] Wbar.V Qbar.V).comp (eUprod.toLinearMap.comp ePU.toLinearMap)
  refine ⟨f, ?_⟩
  intro q
  refine ⟨ePU.symm (eUprod.symm (0, q)), ?_⟩
  simp [f]

/-- Helper for Exercise 16-16.3-8: a surjective reduced map between projective residue-field
reductions lifts to a surjective `A[G]`-linear map upstairs. -/
private theorem lift_surjective_reduction_map_local
    {P Q : FiniteProjectiveGroupAlgebraModule A G}
    (fbar : P.residueFieldReduction.V →ₗ[k[G]] Q.residueFieldReduction.V)
    (hbar : Function.Surjective fbar) :
    ∃ f : P.V →ₗ[A[G]] Q.V, Function.Surjective f := by
  -- Lift across the projective target after viewing reduction as an `A[G]`-linear quotient.
  let fbarTensor : (k ⊗[A] P.V) →ₗ[k[G]] (k ⊗[A] Q.V) := by
    simpa [FiniteProjectiveGroupAlgebraModule.residueFieldReduction,
      FiniteProjectiveGroupAlgebraModule.V] using fbar
  have hbarTensor : Function.Surjective fbarTensor := by
    simpa [fbarTensor] using hbar
  let qP : P.V →ₗ[A[G]] (k ⊗[A] P.V) :=
    reduction_groupAlgebraLinear_local (A := A) (G := G) P
  let qQ : Q.V →ₗ[A[G]] (k ⊗[A] Q.V) :=
    reduction_groupAlgebraLinear_local (A := A) (G := G) Q
  let h : P.V →ₗ[A[G]] (k ⊗[A] Q.V) :=
    (restrictReducedGroupAlgebraLinear_local (A := A) (G := G) fbarTensor).comp qP
  have hqQ : Function.Surjective qQ :=
    reduction_groupAlgebraLinear_surjective_local (A := A) (G := G) Q
  obtain ⟨f, hf⟩ := Module.projective_lifting_property qQ h hqQ
  have hh : Function.Surjective h := by
    intro z
    obtain ⟨y, hy⟩ := hbarTensor z
    obtain ⟨x, hx⟩ := reduction_groupAlgebraLinear_surjective_local (A := A) (G := G) P y
    refine ⟨x, ?_⟩
    simpa [h, qP, hx] using hy
  have hbase : Function.Surjective (baseChange_groupAlgebraLinear (A := A) (G := G) f) := by
    -- Surjectivity on the base change is read off from the surjective composite `qQ ∘ f`.
    intro z
    obtain ⟨x, hx⟩ := hh z
    refine ⟨(1 : k) ⊗ₜ[A] x, ?_⟩
    calc
      baseChange_groupAlgebraLinear (A := A) (G := G) f ((1 : k) ⊗ₜ[A] x) =
          (1 : k) ⊗ₜ[A] f x := by
            simp
      _ = qQ (f x) := rfl
      _ = h x := LinearMap.congr_fun hf x
      _ = z := hx
  let e : P ⟶ Q := ObjectProperty.homMk (ConcreteCategory.ofHom f)
  have hsurj : Function.Surjective f := by
    -- Nakayama upgrades surjectivity of the reduced map to surjectivity upstairs.
    simpa [e, baseChange_groupAlgebraLinear] using
      finiteProjective_underlying_surjective_of_reduction_surjective
        (A := A) (G := G) e hbase
  exact ⟨f, hsurj⟩

/-- Helper for Exercise 16-16.3-8: a split surjection of finite projective `A[G]`-modules
identifies the source class as the target class plus the class of an actual complement. -/
private theorem mem_projectivePositiveSubset_of_surjective_map_difference_local
    {P Q : FiniteProjectiveGroupAlgebraModule A G}
    (hf : ∃ f : P.V →ₗ[A[G]] Q.V, Function.Surjective f) :
    [P]ₚ₀ - [Q]ₚ₀ ∈ P⁺[A](G) := by
  -- Split the surjection, take the complementary idempotent range, and read the class relation.
  rcases hf with ⟨f, hsurj⟩
  obtain ⟨i, hi⟩ := (Module.Projective.iff_split_of_projective f hsurj).1 inferInstance
  let T : Module.End A[G] P.V := i.comp f
  have hT_idem : IsIdempotentElem T := by
    ext x
    simpa [T, LinearMap.comp_apply] using congrArg i (LinearMap.congr_fun hi (f x))
  let TRange :=
    rangeFiniteProjectiveGroupAlgebraModule_local (A := A) (G := G) P T hT_idem
  let TWitness :=
    rangeFiniteProjectiveGroupAlgebraModule_local (A := A) (G := G) P (1 - T) hT_idem.one_sub
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
    simpa [LinearMap.IsIdempotentElem.ker_eq_range_one_sub (p := T) hT_idem] using
      (LinearMap.IsIdempotentElem.isCompl hT_idem :
        IsCompl (LinearMap.range T) (LinearMap.ker T))
  let eProd :=
    Submodule.prodEquivOfIsCompl (LinearMap.range T) (LinearMap.range (1 - T)) hcompl
  obtain ⟨Wprod, hWprod_equiv, hWprod_class⟩ :=
    exists_product_projective_module_class_eq_add_local (R := A) (G := G) TRange TWitness
  have hPclass : [P]ₚ₀ = [Wprod]ₚ₀ := by
    rcases hWprod_equiv with ⟨eWprod⟩
    exact
      (finiteProjectiveGroupAlgebraGrothendieckClass_eq_iff_nonempty_linearEquiv
        (A := A) (G := G) P Wprod).2
        ⟨eProd.symm.trans eWprod.symm⟩
  have hRangeClass : [TRange]ₚ₀ = [Q]ₚ₀ :=
    (finiteProjectiveGroupAlgebraGrothendieckClass_eq_iff_nonempty_linearEquiv
      (A := A) (G := G) TRange Q).2
      ⟨eRangeQ⟩
  refine ⟨TWitness, ?_⟩
  apply (eq_sub_iff_add_eq'.2 ?_)
  calc
    [Q]ₚ₀ + [TWitness]ₚ₀ = [TRange]ₚ₀ + [TWitness]ₚ₀ := by rw [hRangeClass]
    _ = [Wprod]ₚ₀ := hWprod_class.symm
    _ = [P]ₚ₀ := hPclass.symm

/-- Helper for Exercise 16-16.3-8: if the reduction of a projective Grothendieck class is
actual over the residue field, then the original class is already actual over `A`. -/
theorem mem_projectivePositiveSubset_of_reductionHom_mem_noComplete
    {x : P₀[A](G)}
    (hx : projectiveGrothendieckReductionHom (A := A) (G := G) x ∈ P⁺[k](G)) :
    x ∈ P⁺[A](G) := by
  -- Write `x` as a difference and turn positivity of the reduced difference into a surjection.
  obtain ⟨P, Q, hxPQ⟩ := exists_projective_class_difference_rep_local (A := A) (G := G) x
  have hred :
      [P.residueFieldReduction]ₚ₀ - [Q.residueFieldReduction]ₚ₀ ∈ P⁺[k](G) := by
    simpa [hxPQ, map_sub] using hx
  obtain ⟨fbar, hfbar⟩ :=
    surjective_map_of_positive_projective_difference_residueField_local
      (A := A) (G := G) hred
  obtain ⟨f, hf⟩ :=
    lift_surjective_reduction_map_local (A := A) (G := G) fbar hfbar
  have hpos : [P]ₚ₀ - [Q]ₚ₀ ∈ P⁺[A](G) :=
    mem_projectivePositiveSubset_of_surjective_map_difference_local
      (A := A) (G := G) ⟨f, hf⟩
  simpa [hxPQ] using hpos

/-- Helper for Exercise 16-16.3-8: positivity of a projective class should reflect back along the
reduction homomorphism `P₀[A](G) → P₀[k](G)`. -/
theorem mem_projectivePositiveSubset_of_reduction_mem_local
    [IsNoetherianRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {x : P₀[A](G)}
    (hx : projectiveGrothendieckReductionEquiv (A := A) (G := G) x ∈ P⁺[k](G)) :
    x ∈ P⁺[A](G) := by
  -- The no-completion reflection theorem consumes the hom-shaped reduction hypothesis.
  exact mem_projectivePositiveSubset_of_reductionHom_mem_noComplete (A := A) (G := G) (by
    simpa [projectiveGrothendieckReductionEquiv] using hx)

/-- Helper for Exercise 16-16.3-8: the same positivity reflection stated on the reduction
homomorphism surface. -/
theorem mem_projectivePositiveSubset_of_reductionHom_mem_local
    {x : P₀[A](G)}
    (hx : projectiveGrothendieckReductionHom (A := A) (G := G) x ∈ P⁺[k](G)) :
    x ∈ P⁺[A](G) := by
  -- Keep the older local name as a thin adapter for existing target-file calls.
  exact mem_projectivePositiveSubset_of_reductionHom_mem_noComplete (A := A) (G := G) hx

end

end Representation
