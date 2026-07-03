import Mathlib
import LinearRepresentations_Serre_1977.Chap11.Proposition_11_11_4_1.Index
import LinearRepresentations_Serre_1977.Chap14.Exercise_14_14_4_5
import LinearRepresentations_Serre_1977.Chap16.Corollary_16_16_1_7
import LinearRepresentations_Serre_1977.Chap16.Exercise_16_16_1_12
import LinearRepresentations_Serre_1977.Chap02.Exercise_2_2_4_5
import LinearRepresentations_Serre_1977.Chap02.Proposition_2_2_4_1
import LinearRepresentations_Serre_1977.Chap06.Proposition_6_6_2_1

noncomputable section

universe u

open scoped MonoidAlgebra Representation

namespace Representation

section SwanExercise

namespace FiniteProjectiveGroupAlgebraModule

/-- Helper for Exercise 16-16.2-3: restricting a finite projective `A[G]`-owner to a subgroup
keeps the owner projective over the subgroup algebra. -/
theorem projective_restrictScalars_of_free_hom
    {R : Type u} [Semiring R]
    {S : Type u} [Semiring S] (σ : R →+* S)
    {M : Type*} [AddCommMonoid M] [Module S M]
    [Module R S] [Module R M] [IsScalarTower R S M]
    (hsmulS : ∀ (r : R) (s : S), (r • s : S) = σ r * s)
    [Module.Free R S] [Module.Projective S M] :
    Module.Projective R M := by
  -- Restrict the splitting of the projective `S`-module along `σ : R → S`.
  obtain ⟨P, _instAddCommMonoid, _instModule, _instFree, i, s, hs⟩ :=
    (Module.Projective.iff_split (R := S) (P := M)).mp inferInstance
  let _ : Module R P := Module.compHom P σ
  let _ : IsScalarTower R S P := by
    -- The restricted `R`-action on the free summand is the one induced by `σ`.
    refine ⟨?_⟩
    intro r s x
    calc
      (r • s) • x = (σ r * s) • x := by rw [hsmulS]
      _ = (σ r) • (s • x) := by simpa using (mul_smul (σ r) s x)
  let _ : Module.Free R P :=
    Module.Free.of_basis
      ((Module.Free.chooseBasis R S).smulTower (Module.Free.chooseBasis S P))
  exact Module.Projective.of_split (i.restrictScalars R) (s.restrictScalars R) <| by
    -- The restricted splitting identity is the same pointwise identity as before.
    ext x
    exact LinearMap.congr_fun hs x

/-- Helper for Exercise 16-16.2-3: a representation equivalence induces an equivalence of the
corresponding owner modules over the group algebra. -/
theorem nonempty_asModuleLinearEquiv_of_repEquiv
    {A : Type u} [CommRing A]
    {H : Type u} [Group H]
    {V W : Type u} [AddCommGroup V] [AddCommGroup W]
    [Module A V] [Module A W]
    (ρ : Representation A H V) (σ : Representation A H W) (e : ρ.Equiv σ) :
    Nonempty (ρ.asModule ≃ₗ[A[H]] σ.asModule) := by
  -- Compare the owner modules through the underlying linear equivalence and then check
  -- compatibility one group-algebra basis element at a time.
  refine ⟨
    { toFun := fun x => σ.asModuleEquiv.symm (e.toLinearEquiv (ρ.asModuleEquiv x))
      invFun := fun y => ρ.asModuleEquiv.symm (e.symm.toLinearEquiv (σ.asModuleEquiv y))
      left_inv := by
        intro x
        simp
      right_inv := by
        intro y
        simp
      map_add' := by
        intro x y
        simp
      map_smul' := by
        intro r x
        apply σ.asModuleEquiv.injective
        rw [σ.asModuleEquiv_map_smul, ρ.asModuleEquiv_map_smul]
        change e.toLinearEquiv ((ρ.asAlgebraHom r) (ρ.asModuleEquiv x)) =
          (σ.asAlgebraHom r) (e.toLinearEquiv (ρ.asModuleEquiv x))
        refine MonoidAlgebra.induction_on
          (p := fun s : A[H] =>
            e.toLinearEquiv ((ρ.asAlgebraHom s) (ρ.asModuleEquiv x)) =
              (σ.asAlgebraHom s) (e.toLinearEquiv (ρ.asModuleEquiv x))) r ?_ ?_ ?_
        · intro h
          simpa [Representation.asAlgebraHom, MonoidAlgebra.of] using
            (Representation.IntertwiningMap.isIntertwining ρ σ e.toIntertwiningMap h
              (ρ.asModuleEquiv x))
        · intro a b ha hb
          simp [map_add, ha, hb]
        · intro a b hb
          simp [hb] }⟩

/-- Helper for Exercise 16-16.2-3: the owner module of `Representation.ofModule' M` is
canonically the original `A[G]`-module `M`. -/
theorem ofModule'_asAlgebraHom_apply
    {A : Type u} [CommRing A]
    {G : Type u} [Group G]
    (M : Type*) [AddCommGroup M] [Module A M] [Module A[G] M] [IsScalarTower A A[G] M]
    (r : A[G]) (m : M) :
    ((Representation.ofModule' (k := A) (G := G) M).asAlgebraHom r) m = r • m := by
  -- Expand the group-algebra element linearly and check the claim on monomials.
  refine MonoidAlgebra.induction_on
    (p := fun s : A[G] =>
      ((Representation.ofModule' (k := A) (G := G) M).asAlgebraHom s) m = s • m) r ?_ ?_ ?_
  · intro g
    simp [Representation.ofModule', MonoidAlgebra.of]
  · intro a b ha hb
    simp [ha, hb, add_smul]
  · intro a b hb
    simp [hb]

/-- Helper for Exercise 16-16.2-3: the owner module of `Representation.ofModule' M` is
canonically the original `A[G]`-module `M`. -/
theorem nonempty_ofModule'_asModuleLinearEquiv
    {A : Type u} [CommRing A]
    {G : Type u} [Group G]
    (M : Type*) [AddCommGroup M] [Module A M] [Module A[G] M] [IsScalarTower A A[G] M] :
    Nonempty ((Representation.ofModule' (k := A) (G := G) M).asModule ≃ₗ[A[G]] M) := by
  -- Use the standard `asModuleEquiv` and verify that it respects the original `A[G]`-action.
  let toFun : (Representation.ofModule' (k := A) (G := G) M).asModule → M :=
    fun x => (Representation.ofModule' (k := A) (G := G) M).asModuleEquiv x
  let invFun : M → (Representation.ofModule' (k := A) (G := G) M).asModule :=
    fun x => (Representation.ofModule' (k := A) (G := G) M).asModuleEquiv.symm x
  have hleft : Function.LeftInverse invFun toFun := by
    intro x
    simp [toFun, invFun]
  have hright : Function.RightInverse invFun toFun := by
    intro x
    simp [toFun, invFun]
  have hadd : ∀ x y, toFun (x + y) = toFun x + toFun y := by
    intro x y
    rfl
  have hsmul : ∀ (r : A[G]) x, toFun (r • x) = r • toFun x := by
    intro r x
    calc
      (Representation.ofModule' (k := A) (G := G) M).asModuleEquiv (r • x)
          = ((Representation.ofModule' (k := A) (G := G) M).asAlgebraHom r)
              ((Representation.ofModule' (k := A) (G := G) M).asModuleEquiv x) := by
                simpa using
                  (Representation.asModuleEquiv_map_smul
                    (ρ := Representation.ofModule' (k := A) (G := G) M) r x)
      _ = r • (Representation.ofModule' (k := A) (G := G) M).asModuleEquiv x := by
            simpa [toFun] using
              (ofModule'_asAlgebraHom_apply (A := A) (G := G) M r
                ((Representation.ofModule' (k := A) (G := G) M).asModuleEquiv x))
  refine ⟨
    { toFun := toFun
      invFun := invFun
      left_inv := hleft
      right_inv := hright
      map_add' := hadd
      map_smul' := hsmul }⟩

/-- Helper for Exercise 16-16.2-3: restricting the ambient `A[G]`-action along `A[H] → A[G]`
still makes the owner into an `A`-scalar tower. -/
theorem subgroup_compHom_isScalarTower
    {A : Type u} [CommRing A]
    {G : Type u} [Group G]
    (H : Subgroup G) (M : Type*) [AddCommGroup M] [Module A M] [Module A[G] M]
    [IsScalarTower A A[G] M] :
    let σ : A[↥H] →+* A[G] := MonoidAlgebra.mapDomainRingHom A H.subtype
    let _ : Module A[↥H] M := Module.compHom M σ
    IsScalarTower A A[↥H] M := by
  let σ : A[↥H] →+* A[G] := MonoidAlgebra.mapDomainRingHom A H.subtype
  let _ : Module A[↥H] M := Module.compHom M σ
  -- The subgroup-algebra scalar action factors through the ambient group-algebra action.
  exact IsScalarTower.of_algebraMap_smul fun a x ↦ by
    have hσalg : σ ((algebraMap A A[↥H]) a) = algebraMap A A[G] a := by
      simpa [σ] using
        congrArg (fun f : A →+* A[G] => f a)
          (MonoidAlgebra.mapDomainRingHom_comp_algebraMap
            (R := A) (A := A) H.subtype)
    change (σ ((algebraMap A A[↥H]) a)) • x = a • x
    rw [hσalg]
    change (algebraMap A A[G] a) • x = a • x
    exact IsScalarTower.algebraMap_smul (A := A[G]) (M := M) a x

/-- Helper for Exercise 16-16.2-3: forgetting the `RestrictScalars A A[G]` wrapper on the owner
of `Q.toRep` gives the canonical `A`-linear equivalence back to `Q.V`. -/
noncomputable def restrictScalars_owner_linearEquiv
    {A : Type u} [CommRing A]
    {G : Type u} [Group G]
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    Q.toRep.V ≃ₗ[A] Q.V := by
  let e : RestrictScalars A A[G] Q.V ≃ₗ[A] Q.V :=
    { toFun := RestrictScalars.addEquiv A A[G] Q.V
      invFun := (RestrictScalars.addEquiv A A[G] Q.V).symm
      left_inv := by
        intro x
        rfl
      right_inv := by
        intro x
        rfl
      map_add' := by
        intro x y
        rfl
      map_smul' := by
        intro a x
        calc
          RestrictScalars.addEquiv A A[G] Q.V (a • x)
              = MonoidAlgebra.single (1 : G) a • RestrictScalars.addEquiv A A[G] Q.V x := by
                  simp
          _ = a • RestrictScalars.addEquiv A A[G] Q.V x := by
                calc
                  MonoidAlgebra.single (1 : G) a • RestrictScalars.addEquiv A A[G] Q.V x
                      = (a • (1 : A[G])) • RestrictScalars.addEquiv A A[G] Q.V x := by
                          simp [Algebra.smul_def]
                  _ = a • ((1 : A[G]) • RestrictScalars.addEquiv A A[G] Q.V x) := by
                        rw [smul_assoc]
                  _ = a • RestrictScalars.addEquiv A A[G] Q.V x := by
                        simp }
  exact
    (by
      simpa [FiniteProjectiveGroupAlgebraModule.toRep, Rep.ofModuleMonoidAlgebra_obj_coe] using e)

/-- Helper for Exercise 16-16.2-3: the underlying `A`-linear identification of the restricted
owner with `Q.V` already intertwines the subgroup action with the `ofModule'` model. -/
theorem restrictScalars_owner_isIntertwining_restricted_ofModule'
    {A : Type u} [CommRing A]
    {G : Type u} [Group G]
    (H : Subgroup G) (Q : FiniteProjectiveGroupAlgebraModule A G) :
    let σ : A[↥H] →+* A[G] := MonoidAlgebra.mapDomainRingHom A H.subtype
    let _ : Module A[↥H] Q.V := Module.compHom Q.V σ
    let _ : IsScalarTower A A[↥H] Q.V :=
      subgroup_compHom_isScalarTower (A := A) (G := G) H Q.V
    Representation.IsIntertwiningMap
      (ρ := (Rep.res H.subtype Q.toRep).ρ)
      (σ := Representation.ofModule' (k := A) (G := H) Q.V)
      (restrictScalars_owner_linearEquiv (A := A) (G := G) Q).toLinearMap := by
  let σ : A[↥H] →+* A[G] := MonoidAlgebra.mapDomainRingHom A H.subtype
  let _ : Module A[↥H] Q.V := Module.compHom Q.V σ
  let _ : IsScalarTower A A[↥H] Q.V :=
    subgroup_compHom_isScalarTower (A := A) (G := G) H Q.V
  -- Both subgroup actions are the original `G`-action evaluated at `h.1`.
  refine Representation.IsIntertwiningMap.mk ?_
  intro h x
  calc
    (restrictScalars_owner_linearEquiv (A := A) (G := G) Q)
        (((Rep.res H.subtype Q.toRep).ρ h) x)
        =
      (restrictScalars_owner_linearEquiv (A := A) (G := G) Q)
        ((Q.toRep.ρ.asAlgebraHom (MonoidAlgebra.of A G h.1))
          (Q.toRep.ρ.asModuleEquiv (Q.toRep.ρ.asModuleEquiv.symm x))) := by
            simp [Rep.res_obj_ρ]
    _ =
      (MonoidAlgebra.single h.1 (1 : A) : A[G]) •
          ((restrictScalars_owner_linearEquiv (A := A) (G := G) Q) x) := by
            simpa [FiniteProjectiveGroupAlgebraModule.toRep,
              Rep.ofModuleMonoidAlgebra_obj_ρ, restrictScalars_owner_linearEquiv] using
              (Representation.smul_ofModule_asModule
                (k := A) (G := G) (M := ModuleCat.of A[G] Q.V)
                (r := MonoidAlgebra.of A G h.1)
                (m := Q.toRep.ρ.asModuleEquiv.symm x))
    _ =
      (MonoidAlgebra.single h (1 : A) : A[↥H]) •
        ((restrictScalars_owner_linearEquiv (A := A) (G := G) Q) x) := by
          show (MonoidAlgebra.single h.1 (1 : A) : A[G]) •
              ((restrictScalars_owner_linearEquiv (A := A) (G := G) Q) x) =
            σ (MonoidAlgebra.single h (1 : A)) •
              ((restrictScalars_owner_linearEquiv (A := A) (G := G) Q) x)
          simp [σ]
    _ = ((Representation.ofModule' (k := A) (G := H) Q.V) h)
          ((restrictScalars_owner_linearEquiv (A := A) (G := G) Q) x) := by
            simp [Representation.ofModule', MonoidAlgebra.of]

/-- Helper for Exercise 16-16.2-3: the restricted representation is equivalent to the
`Representation.ofModule'` model on the same restricted owner module. -/
theorem restricted_nonempty_equiv_ofModule'_compHom_owner
    {A : Type u} [CommRing A]
    {G : Type u} [Group G]
    (H : Subgroup G) (Q : FiniteProjectiveGroupAlgebraModule A G) :
    let σ : A[↥H] →+* A[G] := MonoidAlgebra.mapDomainRingHom A H.subtype
    let _ : Module A[↥H] Q.V := Module.compHom Q.V σ
    let _ : IsScalarTower A A[↥H] Q.V :=
      subgroup_compHom_isScalarTower (A := A) (G := G) H Q.V
    Nonempty ((Rep.res H.subtype Q.toRep).ρ.Equiv
      (Representation.ofModule' (k := A) (G := H) Q.V)) := by
  let σ : A[↥H] →+* A[G] := MonoidAlgebra.mapDomainRingHom A H.subtype
  let _ : Module A[↥H] Q.V := Module.compHom Q.V σ
  let _ : IsScalarTower A A[↥H] Q.V :=
    subgroup_compHom_isScalarTower (A := A) (G := G) H Q.V
  -- Package the carrier identity as a representation equivalence once equivariance is known.
  refine ⟨Representation.Equiv.mk
    (restrictScalars_owner_linearEquiv (A := A) (G := G) Q) ?_⟩
  intro h
  ext x
  exact
    (restrictScalars_owner_isIntertwining_restricted_ofModule'
      (A := A) (G := G) H Q).isIntertwining h x

/-- Helper for Exercise 16-16.2-3: the owner of the restricted representation is canonically the
same `A[H]`-module as the ambient owner with scalar action restricted along `A[H] → A[G]`. -/
theorem restricted_asModuleLinearEquiv_compHom_owner
    {A : Type u} [CommRing A]
    {G : Type u} [Group G]
    (H : Subgroup G) (Q : FiniteProjectiveGroupAlgebraModule A G) :
    let σ : A[↥H] →+* A[G] := MonoidAlgebra.mapDomainRingHom A H.subtype
    let _ : Module A[↥H] Q.V := Module.compHom Q.V σ
    let _ : IsScalarTower A A[↥H] Q.V :=
      subgroup_compHom_isScalarTower (A := A) (G := G) H Q.V
    Nonempty (((Rep.res H.subtype Q.toRep).ρ.asModule) ≃ₗ[A[↥H]] Q.V) := by
  let σ : A[↥H] →+* A[G] := MonoidAlgebra.mapDomainRingHom A H.subtype
  let _ : Module A[↥H] Q.V := Module.compHom Q.V σ
  let _ : IsScalarTower A A[↥H] Q.V :=
    subgroup_compHom_isScalarTower (A := A) (G := G) H Q.V
  obtain ⟨eρ⟩ :=
    restricted_nonempty_equiv_ofModule'_compHom_owner
      (A := A) (G := G) H Q
  let f :
      ((Rep.res H.subtype Q.toRep).ρ.asModule) →ₗ[A[↥H]]
        (Representation.ofModule' (k := A) (G := H) Q.V).asModule :=
    (Representation.IntertwiningMap.equivLinearMapAsModule
      (ρ := (Rep.res H.subtype Q.toRep).ρ)
      (σ := Representation.ofModule' (k := A) (G := H) Q.V))
      eρ.toIntertwiningMap
  have hf_bij : Function.Bijective f := by
    constructor
    · intro x y hxy
      exact eρ.injective hxy
    · intro w
      refine ⟨(Rep.res H.subtype Q.toRep).ρ.asModuleEquiv.symm
        (eρ.symm ((Representation.ofModule' (k := A) (G := H) Q.V).asModuleEquiv w)), ?_⟩
      change eρ ((Rep.res H.subtype Q.toRep).ρ.asModuleEquiv
        ((Rep.res H.subtype Q.toRep).ρ.asModuleEquiv.symm
          (eρ.symm ((Representation.ofModule' (k := A) (G := H) Q.V).asModuleEquiv w)))) =
        (Representation.ofModule' (k := A) (G := H) Q.V).asModuleEquiv w
      simp
  obtain ⟨eM⟩ := nonempty_ofModule'_asModuleLinearEquiv (A := A) (G := H) Q.V
  -- First identify the restricted owner with the `ofModule'` owner, then forget back to `Q.V`.
  refine ⟨(LinearEquiv.ofBijective f hf_bij).trans eM⟩

/-- Helper for Exercise 16-16.2-3: a right-transversal decomposition of `G` exhibits `A[G]` as a
free `A[H]`-module. -/
theorem rightTransversal_freeModel_map_single_smul
    {A : Type u} [CommRing A]
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) (T : H.RightTransversal) (h : H) (g : G) (r : A) :
    let e : G ≃ (↥(T : Set G) × H) :=
      T.2.equiv.trans (Equiv.prodComm H ↥(T : Set G))
    let Φ : (G →₀ A) ≃ₗ[A] (↥(T : Set G) →₀ H →₀ A) :=
      Finsupp.domLCongr e ≪≫ₗ Finsupp.curryLinearEquiv A
    Φ (Finsupp.single (h.1 * g) r) =
      (Representation.free A H ↥(T : Set G) h) (Φ (Finsupp.single g r)) := by
  dsimp
  have he :
      (T.2.equiv.trans (Equiv.prodComm H ↥(T : Set G))) (h.1 * g) =
        ((T.2.equiv.trans (Equiv.prodComm H ↥(T : Set G)) g).1,
          h * (T.2.equiv.trans (Equiv.prodComm H ↥(T : Set G)) g).2) := by
    -- The complement equivalence records that left multiplication only changes the subgroup part.
    simpa using
      congrArg (Equiv.prodComm H ↥(T : Set G))
        (T.2.equiv_mul_left_of_mem (g := g) h.2)
  -- Both sides reduce to the same singleton in the free model indexed by the transversal.
  simp [he]

/-- Helper for Exercise 16-16.2-3: restricting the left-regular representation to `H` is the
free representation on any right transversal of `H`. -/
theorem right_transversal_restricted_leftRegular_equiv_free
    {A : Type u} [CommRing A]
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) (T : H.RightTransversal) :
    Nonempty (Representation.Equiv
      ((Representation.leftRegular A G).comp H.subtype)
      (Representation.free A H ↥(T : Set G))) := by
  let e : G ≃ (↥(T : Set G) × H) :=
    T.2.equiv.trans (Equiv.prodComm H ↥(T : Set G))
  let Φ : (G →₀ A) ≃ₗ[A] (↥(T : Set G) →₀ H →₀ A) :=
    Finsupp.domLCongr e ≪≫ₗ Finsupp.curryLinearEquiv A
  refine ⟨Representation.Equiv.mk Φ ?_⟩
  intro h
  -- Check the intertwining identity on singleton basis vectors of the regular representation.
  apply Finsupp.lhom_ext'
  intro g
  apply LinearMap.ext
  intro r
  simpa [Φ, e] using
    rightTransversal_freeModel_map_single_smul (A := A) (G := G) H T h g r

/-- Helper for Exercise 16-16.2-3: the restricted left-regular owner is literally the group
algebra `A[G]` with scalars restricted along `A[H] → A[G]`. -/
theorem restricted_leftRegular_asModuleLinearEquiv_compHom_groupAlgebra
    {A : Type u} [CommRing A]
    {G : Type u} [Group G]
    (H : Subgroup G) :
    let σ : A[↥H] →+* A[G] := MonoidAlgebra.mapDomainRingHom A H.subtype
    let _ : Module A[↥H] A[G] := Module.compHom A[G] σ
    Nonempty (Representation.asModule ((Representation.leftRegular A G).comp H.subtype) ≃ₗ[A[↥H]]
      A[G]) :=
by
  let σ : A[↥H] →+* A[G] := MonoidAlgebra.mapDomainRingHom A H.subtype
  let _ : Module A[↥H] A[G] := Module.compHom A[G] σ
  -- Route correction: keep the literal carrier `A[G]` and compare the restricted regular action
  -- directly with the `Module.compHom` scalar action along `A[H] → A[G]`.
  refine ⟨
    { (Representation.asModuleEquiv ((Representation.leftRegular A G).comp H.subtype)) with
      map_smul' := ?_ }⟩
  intro r x
  let y : A[G] :=
    (Representation.asModuleEquiv ((Representation.leftRegular A G).comp H.subtype)) x
  calc
    (Representation.asModuleEquiv ((Representation.leftRegular A G).comp H.subtype)) (r • x) =
        (Representation.asAlgebraHom ((Representation.leftRegular A G).comp H.subtype) r) y := by
          simpa [y] using
            (Representation.asModuleEquiv_map_smul
              (ρ := ((Representation.leftRegular A G).comp H.subtype)) r x)
    _ = σ r * y := by
          refine MonoidAlgebra.induction_on
            (p := fun s : A[↥H] =>
              (Representation.asAlgebraHom ((Representation.leftRegular A G).comp H.subtype) s) y =
                σ s * y) r ?_ ?_ ?_
          · intro h
            ext g
            simpa [σ, Algebra.smul_def] using
              (Finsupp.mapDomain_equiv_apply (f := Equiv.mulLeft h.1) y g)
          · intro a b ha hb
            calc
              ((Representation.asAlgebraHom ((Representation.leftRegular A G).comp H.subtype))
                  (a + b)) y
                  =
              ((Representation.asAlgebraHom ((Representation.leftRegular A G).comp H.subtype))
                  a) y +
                ((Representation.asAlgebraHom ((Representation.leftRegular A G).comp H.subtype))
                  b) y := by
                    simp
              _ = σ a * y + σ b * y := by
                    rw [ha, hb]
                    rfl
              _ = (σ a + σ b) * y := by rw [add_mul]
              _ = σ (a + b) * y := by rw [map_add]
          · intro a b hb
            calc
              ((Representation.asAlgebraHom ((Representation.leftRegular A G).comp H.subtype))
                  (a • b)) y
                  =
                ((Representation.asAlgebraHom ((Representation.leftRegular A G).comp H.subtype))
                  ((algebraMap A A[↥H]) a))
                    (((Representation.asAlgebraHom
                      ((Representation.leftRegular A G).comp H.subtype)) b) y) := by
                        rw [Algebra.smul_def, map_mul, Module.End.mul_apply]
              _ = a •
                  (((Representation.asAlgebraHom
                    ((Representation.leftRegular A G).comp H.subtype)) b) y) := by
                      simp [Representation.asAlgebraHom_single]
              _ = a • (σ b * y) := by
                    exact congrArg (fun z => a • z) hb
              _ = σ ((algebraMap A A[↥H]) a * b) * y := by
                    calc
                      a • (σ b * y) = σ ((algebraMap A A[↥H]) a) * (σ b * y) := by
                        simp [Algebra.smul_def, σ]
                      _ = (σ ((algebraMap A A[↥H]) a) * σ b) * y := by
                            rw [mul_assoc]
                      _ = σ ((algebraMap A A[↥H]) a * b) * y := by
                            rw [← map_mul]
              _ = σ (a • b) * y := by
                    simp [Algebra.smul_def]
    _ = r • y := by
          rfl

/-- Helper for Exercise 16-16.2-3: a right-transversal decomposition of `G` exhibits `A[G]` as a
free `A[H]`-module. -/
theorem subgroup_groupAlgebra_free_of_transversal
    {A : Type u} [CommRing A]
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) :
    let σ : A[↥H] →+* A[G] := MonoidAlgebra.mapDomainRingHom A H.subtype
    let _ : Module A[↥H] A[G] := Module.compHom A[G] σ
    Module.Free A[↥H] A[G] := by
  let σ : A[↥H] →+* A[G] := MonoidAlgebra.mapDomainRingHom A H.subtype
  let _ : Module A[↥H] A[G] := Module.compHom A[G] σ
  -- Route correction: follow LinearRepresentations_Serre_1977's transversal argument first, then transport the resulting
  -- free `A[H]`-basis from the restricted regular owner to the literal `A[G]` owner.
  let T : H.RightTransversal := default
  obtain ⟨eρ⟩ :=
    right_transversal_restricted_leftRegular_equiv_free (A := A) (G := G) H T
  obtain ⟨eM⟩ :=
    nonempty_asModuleLinearEquiv_of_repEquiv
      (A := A)
      (H := ↥H)
      (V := G →₀ A)
      (W := ↥(T : Set G) →₀ H →₀ A)
      ((Representation.leftRegular A G).comp H.subtype)
      (Representation.free A H ↥(T : Set G))
      eρ
  let _ : Module.Free A[↥H] (Representation.free A H ↥(T : Set G)).asModule := by
    simpa using
      (Representation.free_asModule_free (k := A) (G := ↥H) (α := ↥(T : Set G)))
  -- Transport the canonical free basis of `Rep.free` back to the restricted regular owner.
  let hfreeReg :
      Module.Free A[↥H]
        (Representation.asModule ((Representation.leftRegular A G).comp H.subtype)) :=
    Module.Free.of_equiv eM.symm
  obtain ⟨eOwner⟩ :=
    restricted_leftRegular_asModuleLinearEquiv_compHom_groupAlgebra
      (A := A) (G := G) H
  let _ :
      Module.Free A[↥H]
        (Representation.asModule ((Representation.leftRegular A G).comp H.subtype)) :=
    hfreeReg
  let hfreeOwner : Module.Free A[↥H] A[G] := Module.Free.of_equiv eOwner
  simpa using hfreeOwner

/-- Helper for Exercise 16-16.2-3: the ambient owner with subgroup-restricted scalars is already
projective over `A[H]`. -/
theorem subgroup_compHom_owner_projective
    {A : Type u} [CommRing A]
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) (Q : FiniteProjectiveGroupAlgebraModule A G) :
    let σ : A[↥H] →+* A[G] := MonoidAlgebra.mapDomainRingHom A H.subtype
    let _ : Module A[↥H] Q.V := Module.compHom Q.V σ
    let _ : IsScalarTower A A[↥H] Q.V :=
      subgroup_compHom_isScalarTower (A := A) (G := G) H Q.V
    Module.Projective A[↥H] Q.V := by
  let σ : A[↥H] →+* A[G] := MonoidAlgebra.mapDomainRingHom A H.subtype
  let _ : Module A[↥H] A[G] := Module.compHom A[G] σ
  let _ : Module.Free A[↥H] A[G] :=
    subgroup_groupAlgebra_free_of_transversal (A := A) (G := G) H
  let _ : Module A[↥H] Q.V := Module.compHom Q.V σ
  let _ : IsScalarTower A A[↥H] Q.V :=
    subgroup_compHom_isScalarTower (A := A) (G := G) H Q.V
  let _ : IsScalarTower A[↥H] A[G] Q.V := by
    -- The restricted scalar action on `Q.V` is induced by the same homomorphism `σ`.
    refine ⟨?_⟩
    intro r s x
    simpa [σ, Module.compHom] using (mul_smul (σ r) s x)
  -- Apply the generic free-restriction lemma on the literal `Module.compHom` owner.
  exact projective_restrictScalars_of_free_hom
    (R := A[↥H]) (S := A[G]) (σ := σ) (M := Q.V)
    (fun (r : A[↥H]) (s : A[G]) => rfl)

/-- Helper for Exercise 16-16.2-3: restricting a finite projective `A[G]`-owner to a subgroup
keeps the owner projective over the subgroup algebra. -/
theorem subgroupRestriction_projective
    {A : Type u} [CommRing A]
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) (Q : FiniteProjectiveGroupAlgebraModule A G) :
    Module.Projective A[H] ((Rep.res H.subtype Q.toRep).ρ.asModule) := by
  let σ : A[↥H] →+* A[G] := MonoidAlgebra.mapDomainRingHom A H.subtype
  let _ : Module A[↥H] Q.V := Module.compHom Q.V σ
  let _ : IsScalarTower A A[↥H] Q.V :=
    subgroup_compHom_isScalarTower (A := A) (G := G) H Q.V
  have hprojective : Module.Projective A[↥H] Q.V := by
    simpa [σ] using subgroup_compHom_owner_projective (A := A) (G := G) H Q
  obtain ⟨eOwner⟩ :=
    restricted_asModuleLinearEquiv_compHom_owner (A := A) (G := G) (H := H) Q
  let _ : Module.Projective A[↥H] Q.V := hprojective
  -- Transport projectivity once across the explicit owner equivalence.
  simpa using
    (Module.Projective.of_equiv' eOwner.symm :
      Module.Projective A[↥H] ((Rep.res H.subtype Q.toRep).ρ.asModule))

/-- Helper for Exercise 16-16.2-3: package subgroup restriction as an actual finite projective
owner on the same carrier `Q.V`. -/
def restrictedToSubgroup
    {A : Type u} [CommRing A]
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) (Q : FiniteProjectiveGroupAlgebraModule A G) :
    FiniteProjectiveGroupAlgebraModule A H :=
  let σ : A[↥H] →+* A[G] := MonoidAlgebra.mapDomainRingHom A H.subtype
  let _ : Module A[↥H] Q.V := Module.compHom Q.V σ
  let _ : IsScalarTower A A[↥H] Q.V :=
    subgroup_compHom_isScalarTower (A := A) (G := G) H Q.V
  let _ : Module.Finite A Q.V := Q.finite
  let _ : Module.Finite A[↥H] Q.V := Module.Finite.of_restrictScalars_finite A A[↥H] Q.V
  -- Package the restricted owner on the literal `Module.compHom` carrier `Q.V`.
  ⟨FGModuleCat.of A[↥H] Q.V, subgroup_compHom_owner_projective (A := A) (G := G) H Q⟩

end FiniteProjectiveGroupAlgebraModule

end SwanExercise

end Representation
