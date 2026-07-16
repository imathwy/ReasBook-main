import Mathlib
import Mathlib.RepresentationTheory.Intertwining
import LinearRepresentations_Serre_1977.Serre.Chap14.Corollary_14_14_4_3

open scoped BigOperators MonoidAlgebra Representation TensorProduct
open CategoryTheory
open Representation
open FiniteProjectiveGroupAlgebraModule

universe u v w

noncomputable section

variable {A : Type u} [CommRing A] [IsLocalRing A]
variable {G : Type v} [Group G]

/-- Helper for Exercise 14-14.4-6: a finite projective `A[G]`-module is free over the local base
ring `A`. -/
theorem free_of_projective_groupAlgebra_over_local
    {G : Type v} [Group G] {P : Type w} [AddCommGroup P] [Module A P]
    [Module A[G] P] [IsScalarTower A A[G] P] [Module.Projective A[G] P]
    [Module.Finite A P] :
    Module.Free A P := by
  obtain ⟨M, _instAddCommGroup, _instModuleAG, _instFree, i, s, hs⟩ :=
    Module.Projective.iff_split.mp (inferInstance : Module.Projective A[G] P)
  let _ : Module A M := Module.compHom M (algebraMap A A[G])
  let _ : IsScalarTower A A[G] M := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let _ : Module.Free A M :=
    Module.Free.of_basis
      ((MonoidAlgebra.basis G A).smulTower (Module.Free.chooseBasis (A[G]) M))
  let _ : Module.Projective A P := by
    refine Module.Projective.of_split (i.restrictScalars A) (s.restrictScalars A) ?_
    ext x
    exact LinearMap.congr_fun hs x
  let _ : Module.Flat A P := Module.Flat.of_projective
  exact Module.free_of_flat_of_isLocalRing

/-- Helper for Exercise 14-14.4-6: for `Representation.ofModule'`, the induced `A[G]`-action on
the carrier is the original scalar multiplication. -/
theorem ofModule'_asAlgebraHom_apply
    (A : Type*) [CommRing A] (M : Type*) [AddCommGroup M] [Module A M] [Module A[G] M]
    [IsScalarTower A A[G] M]
    (r : A[G]) (m : M) :
    ((Representation.ofModule' (k := A) (G := G) M).asAlgebraHom r) m = r • m := by
  refine MonoidAlgebra.induction_on
    (p := fun s : A[G] =>
      ((Representation.ofModule' (k := A) (G := G) M).asAlgebraHom s) m = s • m) r ?_ ?_ ?_
  · intro g
    simp [Representation.ofModule', MonoidAlgebra.of]
  · intro a b ha hb
    simp [ha, hb, add_smul]
  · intro a b hb
    simp [hb]

/-- Helper for Exercise 14-14.4-6: the module underlying `Representation.ofModule' M` is
canonically the original `A[G]`-module `M`. -/
theorem nonempty_ofModule'_asModuleLinearEquiv
    (A : Type*) [CommRing A] (M : Type*) [AddCommGroup M] [Module A M] [Module A[G] M]
    [IsScalarTower A A[G] M] :
    Nonempty ((Representation.ofModule' (k := A) (G := G) M).asModule ≃ₗ[A[G]] M) := by
  let toFun : (Representation.ofModule' (k := A) (G := G) M).asModule → M :=
    fun x ↦ (Representation.ofModule' (k := A) (G := G) M).asModuleEquiv x
  let invFun : M → (Representation.ofModule' (k := A) (G := G) M).asModule :=
    fun x ↦ (Representation.ofModule' (k := A) (G := G) M).asModuleEquiv.symm x
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
              (ofModule'_asAlgebraHom_apply (G := G) A M r
                ((Representation.ofModule' (k := A) (G := G) M).asModuleEquiv x))
  exact ⟨
    { toFun := toFun
      invFun := invFun
      left_inv := hleft
      right_inv := hright
      map_add' := hadd
      map_smul' := hsmul }⟩

/-- Helper for Exercise 14-14.4-6: the `Representation.ofModule'` carrier identification can be
used as an actual `A[G]`-linear equivalence. -/
noncomputable def ofModule'_asModuleLinearEquiv
    (A : Type*) [CommRing A] (M : Type*) [AddCommGroup M] [Module A M] [Module A[G] M]
    [IsScalarTower A A[G] M] :
    (Representation.ofModule' (k := A) (G := G) M).asModule ≃ₗ[A[G]] M :=
  let toFun : (Representation.ofModule' (k := A) (G := G) M).asModule → M :=
    fun x ↦ (Representation.ofModule' (k := A) (G := G) M).asModuleEquiv x
  let invFun : M → (Representation.ofModule' (k := A) (G := G) M).asModule :=
    fun x ↦ (Representation.ofModule' (k := A) (G := G) M).asModuleEquiv.symm x
  { toFun := toFun
    invFun := invFun
    left_inv := by
      intro x
      simp [toFun, invFun]
    right_inv := by
      intro x
      simp [toFun, invFun]
    map_add' := by
      intro x y
      rfl
    map_smul' := by
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
                (ofModule'_asAlgebraHom_apply (G := G) A M r
                  ((Representation.ofModule' (k := A) (G := G) M).asModuleEquiv x)) }

/-- Helper for Exercise 14-14.4-6: after identifying `Representation.ofModule' M` with `M`, an
equivariant endomorphism is exactly an `A[G]`-linear endomorphism of `M`. -/
noncomputable def ofModule'_equivAlgEnd
    (A : Type*) [CommRing A] (M : Type*) [AddCommGroup M] [Module A M] [Module A[G] M]
    [IsScalarTower A A[G] M] :
    Representation.IntertwiningMap (Representation.ofModule' M : Representation A G M)
      (Representation.ofModule' M : Representation A G M) ≃ₐ[A] Module.End A[G] M :=
  (Representation.IntertwiningMap.equivAlgEnd
      (ρ := (Representation.ofModule' M : Representation A G M))).trans
    (LinearEquiv.conjAlgEquiv A (ofModule'_asModuleLinearEquiv (G := G) A M))

/-- Helper for Exercise 14-14.4-6: the transported `A[G]`-linear endomorphism acts by the same
formula as the original intertwining endomorphism. -/
theorem ofModule'_equivAlgEnd_apply_apply
    (A : Type*) [CommRing A] (M : Type*) [AddCommGroup M] [Module A M] [Module A[G] M]
    [IsScalarTower A A[G] M]
    (u : Representation.IntertwiningMap (Representation.ofModule' M : Representation A G M)
      (Representation.ofModule' M : Representation A G M))
    (x : M) :
    ofModule'_equivAlgEnd (G := G) A M u x = u x := by
  simp [ofModule'_equivAlgEnd, ofModule'_asModuleLinearEquiv,
    LinearEquiv.conjAlgEquiv_apply,
    Representation.IntertwiningMap.equivAlgEnd,
    Representation.IntertwiningMap.equivLinearMapAsModule]
  rfl

/-- Helper for Exercise 14-14.4-6: the ordinary `A[G]`-linear endomorphism module of a finite
projective `A[G]`-module is free over the local base ring `A`. -/
theorem groupAlgebra_endomorphismModule_free
    (P : Type w) [AddCommGroup P] [Module A P] [Module A[G] P] [IsScalarTower A A[G] P]
    [Module.Projective A[G] P] [Module.Finite A P] :
    Module.Free A (P →ₗ[A[G]] P) := by
  letI : Module.Free A P := free_of_projective_groupAlgebra_over_local (A := A) (G := G) (P := P)
  letI : Module.Finite A[G] P := Module.Finite.of_restrictScalars_finite A A[G] P
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin' (A[G]) P
  letI : Module.Free A[G] (Fin n → A[G]) :=
    Module.Free.of_basis (Pi.basisFun (A[G]) (Fin n))
  letI : Module.Finite A[G] (Fin n → A[G]) :=
    Module.Finite.of_basis (Pi.basisFun (A[G]) (Fin n))
  obtain ⟨i, hi⟩ := (Module.Projective.iff_split_of_projective s hs).1
    (inferInstance : Module.Projective A[G] P)
  let toAmbient : (P →ₗ[A[G]] P) →ₗ[A] ((Fin n → A[G]) →ₗ[A[G]] P) :=
    { toFun := fun u ↦ u.comp s
      map_add' := by
        intro u v
        rfl
      map_smul' := by
        intro a u
        rfl }
  let fromAmbient : ((Fin n → A[G]) →ₗ[A[G]] P) →ₗ[A] (P →ₗ[A[G]] P) :=
    { toFun := fun φ ↦ φ.comp i
      map_add' := by
        intro φ ψ
        rfl
      map_smul' := by
        intro a φ
        rfl }
  have hsplit : fromAmbient.comp toAmbient = LinearMap.id := by
    ext u x
    change (u.comp s).comp i x = u x
    simp [LinearMap.comp_assoc, hi]
  letI : Module.Projective A (P →ₗ[A[G]] P) :=
    Module.Projective.of_split toAmbient fromAmbient hsplit
  letI : Module.Flat A (P →ₗ[A[G]] P) := Module.Flat.of_projective
  letI : Module.Finite A (P →ₗ[A[G]] P) := Module.Finite.of_surjective fromAmbient <| by
    intro u
    refine ⟨toAmbient u, ?_⟩
    exact LinearMap.congr_fun hsplit u
  exact Module.free_of_flat_of_isLocalRing

/-- Helper for Exercise 14-14.4-6: the equivariant endomorphism algebra of a finite projective
`A[G]`-module is finite over `A`. -/
theorem equivariantEndomorphismAlgebra_finite
    (P : Type w) [AddCommGroup P] [Module A P] [Module A[G] P] [IsScalarTower A A[G] P]
    [Module.Projective A[G] P] [Module.Finite A P] :
    Module.Finite A
      (Representation.IntertwiningMap
        (Representation.ofModule' P : Representation A G P)
        (Representation.ofModule' P : Representation A G P)) := by
  letI : Module.Free A P := free_of_projective_groupAlgebra_over_local (A := A) (G := G) (P := P)
  letI : Module.Finite A[G] P := Module.Finite.of_restrictScalars_finite A A[G] P
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin' (A[G]) P
  letI : Module.Free A[G] (Fin n → A[G]) :=
    Module.Free.of_basis (Pi.basisFun (A[G]) (Fin n))
  letI : Module.Finite A[G] (Fin n → A[G]) :=
    Module.Finite.of_basis (Pi.basisFun (A[G]) (Fin n))
  obtain ⟨i, hi⟩ := (Module.Projective.iff_split_of_projective s hs).1
    (inferInstance : Module.Projective A[G] P)
  let toAmbient : (P →ₗ[A[G]] P) →ₗ[A] ((Fin n → A[G]) →ₗ[A[G]] P) :=
    { toFun := fun u ↦ u.comp s
      map_add' := by
        intro u v
        rfl
      map_smul' := by
        intro a u
        rfl }
  let fromAmbient : ((Fin n → A[G]) →ₗ[A[G]] P) →ₗ[A] (P →ₗ[A[G]] P) :=
    { toFun := fun φ ↦ φ.comp i
      map_add' := by
        intro φ ψ
        rfl
      map_smul' := by
        intro a φ
        rfl }
  have hsplit : fromAmbient.comp toAmbient = LinearMap.id := by
    ext u x
    change (u.comp s).comp i x = u x
    simp [LinearMap.comp_assoc, hi]
  letI : Module.Finite A ((Fin n → A[G]) →ₗ[A[G]] P) :=
    Module.Finite.linearMap (R := A[G]) (S := A) (M := Fin n → A[G]) (N := P)
  letI : Module.Finite A (P →ₗ[A[G]] P) := Module.Finite.of_surjective fromAmbient <| by
    intro u
    refine ⟨toAmbient u, ?_⟩
    exact LinearMap.congr_fun hsplit u
  let endEquiv :
      Representation.IntertwiningMap
          (Representation.ofModule' P : Representation A G P)
          (Representation.ofModule' P : Representation A G P) ≃ₗ[A]
        (P →ₗ[A[G]] P) :=
    (ofModule'_equivAlgEnd (G := G) A P).toLinearEquiv
  exact Module.Finite.of_surjective endEquiv.symm.toLinearMap endEquiv.symm.surjective

end
