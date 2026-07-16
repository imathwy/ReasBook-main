import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap14.Proposition_14_14_3_1
import LinearRepresentations_Serre_1977.Serre.Chap14.Corollary_14_14_4_3.ProjectiveModules
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.FieldTransport

noncomputable section

open CategoryTheory
open scoped MonoidAlgebra Representation TensorProduct

universe u x

namespace Representation

section RingEquivTransfer

/-- Helper for Exercise 18-18.3-2: finite generation is preserved by restriction of scalars along a
ring isomorphism. -/
theorem moduleFinite_of_compHom_ringEquiv
    {R S : Type*} [Ring R] [Ring S] (φ : R ≃+* S)
    {M : Type*} [AddCommGroup M] [Module S M] [Module.Finite S M] :
    letI : Module R M := Module.compHom M φ.toRingHom
    Module.Finite R M := by
  letI : Module R M := Module.compHom M φ.toRingHom
  letI : Module R S := Module.compHom S φ.toRingHom
  haveI : Module.Finite R S := Module.Finite.equiv (Module.compHom.toLinearEquiv φ)
  haveI : IsScalarTower R S M := ⟨fun r s m => smul_assoc (φ r) s m⟩
  exact Module.Finite.trans S M

/-- Helper for Exercise 18-18.3-2: projectivity is preserved by restriction of scalars along a ring
isomorphism. -/
theorem moduleProjective_of_compHom_ringEquiv
    {R S : Type*} [Ring R] [Ring S] (φ : R ≃+* S)
    {M : Type*} [AddCommGroup M] [Module S M] [Module.Projective S M] :
    letI : Module R M := Module.compHom M φ.toRingHom
    Module.Projective R M := by
  classical
  letI : Module R M := Module.compHom M φ.toRingHom
  obtain ⟨W, _instAdd, _instModW, _instFreeW, i, s, hs⟩ :=
    Module.Projective.iff_split.mp (inferInstance : Module.Projective S M)
  letI : Module R S := Module.compHom S φ.toRingHom
  letI : Module R W := Module.compHom W φ.toRingHom
  haveI : IsScalarTower R S M := ⟨fun r s m => smul_assoc (φ r) s m⟩
  haveI : IsScalarTower R S W := ⟨fun r s w => smul_assoc (φ r) s w⟩
  -- `W` is free over `R` by transporting its `S`-basis along `φ`.
  letI : Module.Free R W :=
    Module.Free.of_basis
      ((Module.Free.chooseBasis S W).mapCoeffs φ.symm (by
        intro c x
        change φ (φ.symm c) • x = c • x
        simp))
  haveI : Module.Projective R W := inferInstance
  refine Module.Projective.of_split (i.restrictScalars R) (s.restrictScalars R) ?_
  ext m
  exact LinearMap.congr_fun hs m

end RingEquivTransfer

section MapRingEquiv

variable {F K : Type u} [Field F] [Field K]

/-- Helper for Exercise 18-18.3-2: the ring homomorphism `F[G] →+* K[G]` induced on group algebras
by a ring homomorphism `e : F →+* K` of coefficient fields, sending `single g c ↦ single g (e c)`.
-/
def mapMonoidAlgebraRingHom (e : F →+* K) (G : Type*) [Monoid G] :
    MonoidAlgebra F G →+* MonoidAlgebra K G :=
  MonoidAlgebra.liftNCRingHom ((MonoidAlgebra.singleOneRingHom).comp e) (MonoidAlgebra.of K G)
    (fun c g => by
      show (MonoidAlgebra.single (1 : G) (e c)) * (MonoidAlgebra.single g 1)
        = (MonoidAlgebra.single g 1) * (MonoidAlgebra.single (1 : G) (e c))
      rw [MonoidAlgebra.single_mul_single, MonoidAlgebra.single_mul_single, one_mul, mul_one,
        one_mul, mul_one])

@[simp]
theorem mapMonoidAlgebraRingHom_single (e : F →+* K) {G : Type*} [Monoid G] (a : G) (b : F) :
    mapMonoidAlgebraRingHom e G (MonoidAlgebra.single a b) = MonoidAlgebra.single a (e b) := by
  show MonoidAlgebra.liftNC ((MonoidAlgebra.singleOneRingHom.comp e : F →+* MonoidAlgebra K G) :
      F →+ MonoidAlgebra K G) (MonoidAlgebra.of K G) (MonoidAlgebra.single a b)
      = MonoidAlgebra.single a (e b)
  rw [MonoidAlgebra.liftNC_single]
  show (MonoidAlgebra.single (1 : G) (e b)) * (MonoidAlgebra.single a 1)
    = MonoidAlgebra.single a (e b)
  rw [MonoidAlgebra.single_mul_single, one_mul, mul_one]

/-- Helper for Exercise 18-18.3-2: the ring isomorphism `F[G] ≃+* K[G]` induced on group algebras by
a ring isomorphism `e : F ≃+* K` of coefficient fields, sending `single g c ↦ single g (e c)`. -/
def mapMonoidAlgebraRingEquiv (e : F ≃+* K) (G : Type*) [Monoid G] :
    MonoidAlgebra F G ≃+* MonoidAlgebra K G :=
  RingEquiv.ofRingHom (mapMonoidAlgebraRingHom (e : F →+* K) G)
    (mapMonoidAlgebraRingHom (e.symm : K →+* F) G)
    (by
      apply MonoidAlgebra.ringHom_ext
      · intro r
        simp
      · intro a
        simp)
    (by
      apply MonoidAlgebra.ringHom_ext
      · intro r
        simp
      · intro a
        simp)

@[simp]
theorem mapMonoidAlgebraRingEquiv_single (e : F ≃+* K) {G : Type*} [Monoid G] (a : G) (b : F) :
    mapMonoidAlgebraRingEquiv e G (MonoidAlgebra.single a b) = MonoidAlgebra.single a (e b) :=
  mapMonoidAlgebraRingHom_single (e : F →+* K) a b

theorem mapMonoidAlgebraRingEquiv_algebraMap (e : F ≃+* K) {G : Type*} [Monoid G] (c : F) :
    mapMonoidAlgebraRingEquiv e G (algebraMap F (MonoidAlgebra F G) c)
      = algebraMap K (MonoidAlgebra K G) (e c) := by
  simp only [MonoidAlgebra.coe_algebraMap, Function.comp_apply, Algebra.algebraMap_self,
    RingHom.id_apply, mapMonoidAlgebraRingEquiv_single]

end MapRingEquiv

section OfModuleAction

/-- Helper for Exercise 18-18.3-2: the `G`-action of the representation `Representation.ofModule M`
attached to a `k[G]`-module `M` is given by multiplication by `single g 1`. -/
theorem ofModule_act {k : Type u} [Field k] {H : Type u} [Group H]
    (M : ModuleCat k[H]) (g : H) (m : RestrictScalars k k[H] M) :
    Representation.ofModule M g m
      = (RestrictScalars.addEquiv k k[H] M).symm
          (MonoidAlgebra.single g (1 : k) • RestrictScalars.addEquiv k k[H] M m) := by
  rw [← Representation.asAlgebraHom_single_one]
  exact Representation.ofModule_asAlgebraHom_apply_apply M (MonoidAlgebra.single g 1) m

end OfModuleAction

section TransProj

variable {F K : Type u} [Field F] [Field K] (e : F ≃+* K)
variable {G : Type u} [Group G] [Finite G]

open FiniteProjectiveGroupAlgebraModule

/-- Exercise 18-18.3-2: transport a finitely generated projective `K[G]`-module to an isomorphic
coefficient field `F`, by restriction of scalars along the induced ring isomorphism
`mapMonoidAlgebraRingEquiv e G : F[G] ≃+* K[G]`. The underlying additive group is unchanged. -/
def transProj (P : FiniteProjectiveGroupAlgebraModule K G) :
    FiniteProjectiveGroupAlgebraModule F G := by
  letI : Module (MonoidAlgebra F G) P.V :=
    Module.compHom P.V (mapMonoidAlgebraRingEquiv e G).toRingHom
  haveI hfin : Module.Finite (MonoidAlgebra F G) P.V :=
    moduleFinite_of_compHom_ringEquiv (mapMonoidAlgebraRingEquiv e G)
  haveI hproj : Module.Projective (MonoidAlgebra F G) P.V :=
    moduleProjective_of_compHom_ringEquiv (mapMonoidAlgebraRingEquiv e G)
  exact ⟨⟨ModuleCat.of (MonoidAlgebra F G) P.V, by exact hfin⟩, by exact hproj⟩

/-- The underlying `F`-linear identity equivalence between the finite representation attached to
`transProj e P` and the field-transport of the finite representation attached to `P`. -/
def transProjLinearEquiv (P : FiniteProjectiveGroupAlgebraModule K G) :
    (↥((transProj e P).toFiniteRep.V)) ≃ₗ[F] (↥((fdRepOverRingEquiv e P.toFiniteRep).V)) where
  toFun x := x
  invFun x := x
  map_add' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl
  map_smul' c x := by
    let y : (P.V : Type u) := x
    show mapMonoidAlgebraRingEquiv e G (algebraMap F (MonoidAlgebra F G) c) • y
      = algebraMap K (MonoidAlgebra K G) (e c) • y
    rw [mapMonoidAlgebraRingEquiv_algebraMap]

/-- The `G`-action on `transProj e P`, transported to `single g 1` multiplication on `P.V`. -/
theorem transProj_toRep_act (P : FiniteProjectiveGroupAlgebraModule K G) (g : G)
    (x : (P.V : Type u)) :
    Representation.ofModule (k := F) (G := G) (transProj e P).V g x
      = MonoidAlgebra.single g (1 : K) • x := by
  rw [ofModule_act (k := F) (H := G) (transProj e P).V g x]
  show mapMonoidAlgebraRingEquiv e G (MonoidAlgebra.single g (1 : F)) • x
    = MonoidAlgebra.single g (1 : K) • x
  rw [mapMonoidAlgebraRingEquiv_single, map_one]

/-- The `G`-action on `P`, written as `single g 1` multiplication on `P.V`. -/
theorem toRep_act (P : FiniteProjectiveGroupAlgebraModule K G) (g : G) (x : (P.V : Type u)) :
    Representation.ofModule (k := K) (G := G) P.V g x = MonoidAlgebra.single g (1 : K) • x := by
  rw [ofModule_act P.V g x]; rfl

/-- The isomorphism of underlying `FGModuleCat F` objects built from `transProjLinearEquiv`. -/
def transProjCarrierIso (P : FiniteProjectiveGroupAlgebraModule K G) :
    (transProj e P).toFiniteRep.V ≅ (fdRepOverRingEquiv e P.toFiniteRep).V where
  hom := ConcreteCategory.ofHom (transProjLinearEquiv e P).toLinearMap
  inv := ConcreteCategory.ofHom (transProjLinearEquiv e P).symm.toLinearMap
  hom_inv_id := by ext x; rfl
  inv_hom_id := by ext x; rfl

/-- Deliverable 2: the finite representation attached to `transProj e P` is isomorphic to the
field-transport of the finite representation attached to `P`. -/
def transProj_toFiniteRep_iso (P : FiniteProjectiveGroupAlgebraModule K G) :
    (transProj e P).toFiniteRep ≅ fdRepOverRingEquiv e (P.toFiniteRep) :=
  Action.mkIso (transProjCarrierIso e P) (by
    intro g
    ext x
    show Representation.ofModule (k := F) (G := G) (transProj e P).V g x
       = Representation.ofModule (k := K) (G := G) P.V g x
    rw [transProj_toRep_act, toRep_act])

/-- Helper: the `k[H]`-module action on `asModule ρ` is given by `asAlgebraHom`. -/
theorem asModule_smul_eq {k H W : Type*} [CommRing k] [Monoid H] [AddCommGroup W] [Module k W]
    (ρ : Representation k H W) (r : k[H]) (x : asModule ρ) :
    (r • x : asModule ρ) = ρ.asAlgebraHom r x := rfl

/-- Helper for Exercise 18-18.3-2: the `F[G]`-action on `asModule (fdRepOverRingEquiv e π).ρ` agrees,
along `mapMonoidAlgebraRingEquiv e G`, with the `K[G]`-action on `asModule π.ρ`. -/
theorem asModule_smul_transport {π : FDRep K G} (a : MonoidAlgebra F G)
    (w' : asModule (fdRepOverRingEquiv e π).ρ) (w : asModule π.ρ) (hw : (w' : (π.V : Type u)) = w) :
    ((a • w' : asModule (fdRepOverRingEquiv e π).ρ) : (π.V : Type u))
      = ((mapMonoidAlgebraRingEquiv e G a • w : asModule π.ρ) : (π.V : Type u)) := by
  let L : MonoidAlgebra F G →+ (π.V : Type u) :=
    { toFun := fun a => ((a • w' : asModule (fdRepOverRingEquiv e π).ρ) : (π.V : Type u))
      map_zero' := zero_smul _ w'
      map_add' := fun a b => add_smul a b w' }
  let R : MonoidAlgebra F G →+ (π.V : Type u) :=
    { toFun := fun a => ((mapMonoidAlgebraRingEquiv e G a • w : asModule π.ρ) : (π.V : Type u))
      map_zero' := by rw [map_zero]; exact zero_smul _ w
      map_add' := by intro a b; rw [map_add]; exact add_smul _ _ w }
  have hLR : L = R := by
    apply Finsupp.addHom_ext
    intro g c
    show ((MonoidAlgebra.single g c • w' : asModule (fdRepOverRingEquiv e π).ρ) : (π.V : Type u))
      = ((mapMonoidAlgebraRingEquiv e G (MonoidAlgebra.single g c) • w : asModule π.ρ)
          : (π.V : Type u))
    rw [asModule_smul_eq, asModule_smul_eq, mapMonoidAlgebraRingEquiv_single,
      Representation.asAlgebraHom_single, Representation.asAlgebraHom_single,
      LinearMap.smul_apply, LinearMap.smul_apply]
    show c • ((fdRepOverRingEquiv e π).ρ g w') = e c • (π.ρ g w)
    rw [← hw]
    rfl
  exact congrArg (fun (h : MonoidAlgebra F G →+ (π.V : Type u)) => h a) hLR

/-- Deliverable 3 for Exercise 18-18.3-2: transport a projective envelope across the ring
isomorphism `e`. -/
theorem transProj_envelope {π : FDRep K G}
    (P : FiniteProjectiveGroupAlgebraModule K G)
    (f : P.V →ₗ[K[G]] asModule π.ρ) (hf : f.IsProjectiveEnvelope) :
    ∃ f' : (transProj e P).V →ₗ[F[G]] asModule (fdRepOverRingEquiv e π).ρ,
      f'.IsProjectiveEnvelope := by
  classical
  let f' : (transProj e P).V →ₗ[F[G]] asModule (fdRepOverRingEquiv e π).ρ :=
    { toFun := fun x => (f x : asModule (fdRepOverRingEquiv e π).ρ)
      map_add' := fun x y => f.map_add x y
      map_smul' := by
        intro a x
        let xv : (P.V : Type u) := x
        let fxv : asModule (fdRepOverRingEquiv e π).ρ := f xv
        have key :
            (f ((mapMonoidAlgebraRingEquiv e G a) • xv) :
                asModule (fdRepOverRingEquiv e π).ρ)
              = a • fxv := by
          rw [f.map_smul]
          exact (asModule_smul_transport e a fxv (f xv) rfl).symm
        exact key }
  refine ⟨f', ?_⟩
  have hsurj : Function.Surjective f' := by
    intro y
    obtain ⟨x, hx⟩ := hf.surjective y
    exact ⟨x, hx⟩
  haveI hProj : Module.Projective (MonoidAlgebra F G) ((transProj e P).V) := inferInstance
  have hEss' : f'.IsEssential := by
    refine ⟨fun N hN => ?_⟩
    let N' : Submodule (K[G]) (P.V : Type u) :=
      { carrier := {x | x ∈ N}
        zero_mem' := N.zero_mem
        add_mem' := fun ha hb => N.add_mem ha hb
        smul_mem' := fun b x hx => by
          have hb := N.smul_mem ((mapMonoidAlgebraRingEquiv e G).symm b) hx
          have hbb : b = mapMonoidAlgebraRingEquiv e G ((mapMonoidAlgebraRingEquiv e G).symm b) :=
            (RingEquiv.apply_symm_apply _ _).symm
          rw [hbb]
          exact hb }
    have hmap : N'.map f = ⊤ := by
      rw [Submodule.eq_top_iff']
      intro y
      let yρ' : asModule (fdRepOverRingEquiv e π).ρ := y
      have hy : yρ' ∈ N.map f' := by rw [hN]; exact Submodule.mem_top
      rcases hy with ⟨x, hxN, hfx⟩
      exact ⟨x, hxN, hfx⟩
    have hN'top : N' = ⊤ := hf.toIsEssential.eq_top_of_map_eq_top N' hmap
    rw [Submodule.eq_top_iff']
    intro x
    let xP : (P.V : Type u) := x
    have hx' : xP ∈ N' := by rw [hN'top]; exact Submodule.mem_top
    exact hx'
  exact { surjective := hsurj }

end TransProj

end Representation
