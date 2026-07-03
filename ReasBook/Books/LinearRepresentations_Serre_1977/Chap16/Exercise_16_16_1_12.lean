import Mathlib
import LinearRepresentations_Serre_1977.Chap14.Corollary_14_14_4_3
import LinearRepresentations_Serre_1977.Chap08.Corollary_8_8_3_8
import LinearRepresentations_Serre_1977.Chap15.Definition_15_15_1_1
import LinearRepresentations_Serre_1977.Chap16.Exercise_16_16_1_12.Index

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open CategoryTheory
open scoped MonoidalCategory Representation MonoidAlgebra

namespace Representation

section

variable (k : Type u) [Field k]
variable (G : Type u) [Group G]

private abbrev finiteRepDimensionLift :
    FreeAbelianGroup (FDRep k G) →+ ℤ :=
  FreeAbelianGroup.lift fun V : FDRep k G ↦
    Int.ofNat (Module.finrank k V.1)

-- Proof sketch: the defining relations of `R_k(G)` come from short exact sequences, and
-- `Module.finrank` is additive on short exact sequences of finite-dimensional `k`-vector spaces.
private theorem finiteRepGrothendieckRelations_le_dimensionLift_ker :
    finiteRepGrothendieckRelations k G ≤
      (finiteRepDimensionLift k G).ker := by
  -- It suffices to kill the defining short-exact-sequence generators of `R_k(G)`.
  rw [finiteRepGrothendieckRelations, AddSubgroup.closure_le]
  rintro _ ⟨⟨S, hS⟩, rfl⟩
  let F : FDRep k G ⥤ ModuleCat k :=
    (forget₂ (FDRep k G) (Rep k G)) ⋙ (forget₂ (Rep k G) (ModuleCat k))
  have hSF : (S.map F).ShortExact := by
    -- Forgetting to `k`-vector spaces preserves the given short exact sequence.
    simpa [F] using hS.map_of_exact F
  let f : S.X₁.V →ₗ[k] S.X₂.V := (F.map S.f).hom
  let g : S.X₂.V →ₗ[k] S.X₃.V := (F.map S.g).hom
  have hExact : Function.Exact f g := by
    -- In `ModuleCat k`, short exactness is the usual exactness of linear maps.
    simpa [f, g] using
      (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact (S.map F)).mp hSF.exact
  have hf : Function.Injective f := by
    -- The left map of a short exact sequence is mono, hence injective on underlying vectors.
    exact (ModuleCat.mono_iff_injective _).1 hSF.mono_f
  have hg : Function.Surjective g := by
    -- The right map of a short exact sequence is epi, hence surjective on underlying vectors.
    exact (ModuleCat.epi_iff_surjective _).1 hSF.epi_g
  have hdim :
      Module.finrank k S.X₂.V = Module.finrank k S.X₁.V + Module.finrank k S.X₃.V := by
    -- Rank-nullity for the right map identifies the middle dimension with the sum of the kernel
    -- and quotient dimensions, and exactness identifies that kernel with the image of the left map.
    calc
      Module.finrank k S.X₂.V
          = Module.finrank k (LinearMap.range g) +
              Module.finrank k (LinearMap.ker g) := by
              symm
              exact LinearMap.finrank_range_add_finrank_ker g
      _ = Module.finrank k S.X₃.V + Module.finrank k (LinearMap.range f) := by
            rw [hExact.linearMap_ker_eq, LinearMap.range_eq_top.2 hg]
            simp
      _ = Module.finrank k S.X₃.V + Module.finrank k S.X₁.V := by
            rw [LinearMap.finrank_range_of_inj hf]
      _ = Module.finrank k S.X₁.V + Module.finrank k S.X₃.V := by
            rw [add_comm]
  change
    finiteRepDimensionLift k G
        (FreeAbelianGroup.of S.X₂ - FreeAbelianGroup.of S.X₁ - FreeAbelianGroup.of S.X₃) = 0
  -- After evaluating the lift on generators, the dimension identity cancels the defining relation.
  simp only [finiteRepDimensionLift, map_sub, FreeAbelianGroup.lift_apply_of, Int.ofNat_eq_natCast]
  rw [hdim, Int.natCast_add]
  abel

/-- The dimension homomorphism on LinearRepresentations_Serre_1977's Grothendieck group `R_k(G)`. -/
def finiteRepGrothendieckDimension :
    R₀[k](G) →+ ℤ :=
  QuotientAddGroup.lift
    (finiteRepGrothendieckRelations k G)
    (finiteRepDimensionLift k G)
    (finiteRepGrothendieckRelations_le_dimensionLift_ker k G)

/-- Reducing the Grothendieck-group dimension homomorphism modulo `p ^ n`. -/
def finiteRepGrothendieckDimensionMod (p n : ℕ) :
    R₀[k](G) →+ ZMod (p ^ n) :=
  (Int.castAddHom (ZMod (p ^ n))).comp
    (finiteRepGrothendieckDimension k G)

end

section

variable {p : ℕ}
variable {k : Type u} [Field k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

/-- Helper for Exercise 16-16.1-12: if `S` is free as an `R`-module, then restricting scalars
turns a projective `S`-module into a projective `R`-module. -/
private theorem projective_restrictScalars_of_free_hom
    {R : Type u} [Semiring R]
    {S : Type u} [Semiring S] (σ : R →+* S)
    {M : Type*} [AddCommMonoid M] [Module S M]
    [Module R S] [Module R M] [IsScalarTower R S M]
    (hsmulS : ∀ (r : R) (s : S), (r • s : S) = σ r * s)
    [Module.Free R S] [Module.Projective S M] :
    Module.Projective R M := by
  -- Split the projective `S`-module off a free `S`-module, then restrict the splitting to `R`.
  obtain ⟨P, _instAddCommGroup, _instModule, _instFree, i, s, hs⟩ :=
    (Module.Projective.iff_split (R := S) (P := M)).mp inferInstance
  let _ : Module R P := Module.compHom P σ
  let _ : IsScalarTower R S P := by
    -- The restricted `R`-action is the one induced by the ring homomorphism `σ`.
    refine ⟨?_⟩
    intro r s x
    calc
      (r • s) • x = (σ r * s) • x := by rw [hsmulS]
      _ = (σ r) • (s • x) := by simpa using (mul_smul (σ r) s x)
  let _ : Module.Free R P :=
    Module.Free.of_basis
      ((Module.Free.chooseBasis R S).smulTower (Module.Free.chooseBasis S P))
  exact Module.Projective.of_split (i.restrictScalars R) (s.restrictScalars R) <| by
    -- The restricted maps still split exactly as they did over `S`.
    ext x
    exact LinearMap.congr_fun hs x

omit [Finite G] in
/-- Helper for Exercise 16-16.1-12: once `k[G]` is known to be free over `k[H]`, restriction
of scalars along `k[H] → k[G]` carries a projective `k[G]`-module to a projective
`k[H]`-module. -/
private theorem projective_restrictScalars_of_subgroup_groupAlgebra
    (H : Subgroup G)
    (E : FiniteProjectiveGroupAlgebraModule k G)
    (hfree :
      let σ : k[↥H] →+* k[G] := MonoidAlgebra.mapDomainRingHom k H.subtype
      let _ : Module k[↥H] k[G] := Module.compHom k[G] σ
      Module.Free k[↥H] k[G]) :
    let σ : k[↥H] →+* k[G] := MonoidAlgebra.mapDomainRingHom k H.subtype
    let _ : Module k[↥H] E.V := Module.compHom E.V σ
    Module.Projective k[↥H] E.V := by
  let σ : k[↥H] →+* k[G] := MonoidAlgebra.mapDomainRingHom k H.subtype
  let _ : Module k[↥H] k[G] := Module.compHom k[G] σ
  let _ : Module.Free k[↥H] k[G] := hfree
  let _ : Module k[↥H] E.V := Module.compHom E.V σ
  let _ : IsScalarTower k[↥H] k[G] E.V := by
    -- The restricted subgroup action is compatible with the ambient `k[G]`-action by associativity.
    refine ⟨?_⟩
    intro r s x
    simpa [σ, Module.compHom] using (mul_smul (σ r) s x)
  -- The generic free-restriction lemma now applies to the underlying `k[G]`-module `E.V`.
  exact projective_restrictScalars_of_free_hom (R := k[↥H]) (S := k[G])
    (σ := σ) (M := E.V) (fun (r : k[↥H]) (s : k[G]) => rfl)

omit [Finite G] in
/-- Helper for Exercise 16-16.1-12: restricting a representation along `H ≤ G` keeps the same
underlying carrier, and only changes the scalar action to the restricted `k[H]`-action. -/
private theorem restricted_asModule_eq
    (H : Subgroup G) (E : FiniteProjectiveGroupAlgebraModule k G) :
    let σ : k[↥H] →+* k[G] := MonoidAlgebra.mapDomainRingHom k H.subtype
    let _ : Module k[↥H] E.V := Module.compHom E.V σ
    ((Rep.res H.subtype E.toRep).ρ.asModule) = E.V := by
  -- Restriction does not change the underlying type; it only swaps in the subgroup action.
  rfl

omit [Finite G] [CharP k p] [Fact p.Prime] in
/-- Helper for Exercise 16-16.1-12: on the restricted owner module, the basis element
`single h 1` acts by the original `G`-action evaluated at `h`. -/
private theorem restricted_single_smul_eq_apply
    (H : Subgroup G) (E : FiniteProjectiveGroupAlgebraModule k G) (h : H)
    (x : (Rep.res H.subtype E.toRep).ρ.asModule) :
    (MonoidAlgebra.single h (1 : k)) • x =
      E.toRep.ρ h.1 ((Rep.res H.subtype E.toRep).ρ.asModuleEquiv x) := by
  -- `Representation.single_smul` computes the action of a monoid-algebra basis element.
  simp [Representation.single_smul]

omit [Finite G] [CharP k p] [Fact p.Prime] in
/-- Helper for Exercise 16-16.1-12: for `Representation.ofModule'`, the induced `k[H]`-action is
the original scalar action on the owner module. -/
private theorem ofModule'_asAlgebraHom_apply
    {H : Type u} [Group H]
    (M : Type u) [AddCommGroup M] [Module k M] [Module k[H] M] [IsScalarTower k k[H] M]
    (r : k[H]) (m : M) :
    ((Representation.ofModule' (k := k) (G := H) M).asAlgebraHom r) m = r • m := by
  -- Expand the group-algebra element linearly and check the identity on monomials.
  refine MonoidAlgebra.induction_on
    (p := fun s : k[H] =>
      ((Representation.ofModule' (k := k) (G := H) M).asAlgebraHom s) m = s • m) r ?_ ?_ ?_
  · intro g
    simp [Representation.ofModule', MonoidAlgebra.of]
  · intro a b ha hb
    simp [ha, hb, add_smul]
  · intro a b hb
    simp [hb]

omit [Finite G] [CharP k p] [Fact p.Prime] in
/-- Helper for Exercise 16-16.1-12: the owner module of `Representation.ofModule' M` is
canonically the original `k[H]`-module `M`. -/
private theorem nonempty_ofModule'_asModuleLinearEquiv
    {H : Type u} [Group H]
    (M : Type u) [AddCommGroup M] [Module k M] [Module k[H] M] [IsScalarTower k k[H] M] :
    Nonempty ((Representation.ofModule' (k := k) (G := H) M).asModule ≃ₗ[k[H]] M) := by
  -- Use the standard `asModuleEquiv` and then verify that it respects the original `k[H]`-action.
  let toFun : (Representation.ofModule' (k := k) (G := H) M).asModule → M :=
    fun x => (Representation.ofModule' (k := k) (G := H) M).asModuleEquiv x
  let invFun : M → (Representation.ofModule' (k := k) (G := H) M).asModule :=
    fun x => (Representation.ofModule' (k := k) (G := H) M).asModuleEquiv.symm x
  have hleft : Function.LeftInverse invFun toFun := by
    intro x
    simp [toFun, invFun]
  have hright : Function.RightInverse invFun toFun := by
    intro x
    simp [toFun, invFun]
  have hadd : ∀ x y, toFun (x + y) = toFun x + toFun y := by
    intro x y
    rfl
  have hsmul : ∀ (r : k[H]) x, toFun (r • x) = r • toFun x := by
    intro r x
    -- Rewrite the transported action through `asModuleEquiv`, then identify it with the
    -- original `k[H]`-action on `M`.
    calc
      (Representation.ofModule' (k := k) (G := H) M).asModuleEquiv (r • x)
          = ((Representation.ofModule' (k := k) (G := H) M).asAlgebraHom r)
              ((Representation.ofModule' (k := k) (G := H) M).asModuleEquiv x) := by
                simp
      _ = r • (Representation.ofModule' (k := k) (G := H) M).asModuleEquiv x := by
            simpa [toFun] using
              (ofModule'_asAlgebraHom_apply (k := k) (H := H) M r
                ((Representation.ofModule' (k := k) (G := H) M).asModuleEquiv x))
  refine ⟨
    { toFun := toFun
      invFun := invFun
      left_inv := hleft
      right_inv := hright
      map_add' := hadd
      map_smul' := hsmul }⟩

omit [Finite G] [CharP k p] [Fact p.Prime] in
/-- Helper for Exercise 16-16.1-12: forgetting the `RestrictScalars k k[G]` wrapper on the owner
of `E.toRep` gives a canonical `k`-linear equivalence back to `E.V`. -/
private noncomputable def restrictScalars_owner_linearEquiv
    (E : FiniteProjectiveGroupAlgebraModule k G) :
    E.toRep.V ≃ₗ[k] E.V := by
  let e : RestrictScalars k k[G] E.V ≃ₗ[k] E.V :=
    { toFun := RestrictScalars.addEquiv k k[G] E.V
      invFun := (RestrictScalars.addEquiv k k[G] E.V).symm
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
        -- Normalize the restricted scalar action through the basis element `single 1 a`.
        calc
          RestrictScalars.addEquiv k k[G] E.V (a • x)
              = MonoidAlgebra.single (1 : G) a • RestrictScalars.addEquiv k k[G] E.V x := by
                  simp
          _ = a • RestrictScalars.addEquiv k k[G] E.V x := by
                calc
                  MonoidAlgebra.single (1 : G) a • RestrictScalars.addEquiv k k[G] E.V x
                      = (a • (1 : k[G])) • RestrictScalars.addEquiv k k[G] E.V x := by
                          simp [Algebra.smul_def]
                  _ = a • ((1 : k[G]) • RestrictScalars.addEquiv k k[G] E.V x) := by
                        rw [smul_assoc]
                  _ = a • RestrictScalars.addEquiv k k[G] E.V x := by
                        simp }
  simpa [FiniteProjectiveGroupAlgebraModule.toRep, Rep.ofModuleMonoidAlgebra_obj_coe] using e

omit [Finite G] [CharP k p] [Fact p.Prime] in
/-- Helper for Exercise 16-16.1-12: the underlying `k`-linear identification of the restricted
owner with `E.V` already intertwines the restricted `H`-action with the
`Representation.ofModule'` action on the restricted `k[H]`-module structure. -/
private theorem restrictScalars_owner_isIntertwining_restricted_ofModule'
    (H : Subgroup G) (E : FiniteProjectiveGroupAlgebraModule k G) :
    let σ : k[↥H] →+* k[G] := MonoidAlgebra.mapDomainRingHom k H.subtype
    let _ : Module k[↥H] E.V := Module.compHom E.V σ
    let _ : IsScalarTower k k[↥H] E.V := by
      refine ⟨?_⟩
      intro a r x
      change (σ (a • r)) • x = a • ((σ r) • x)
      have hσalg : σ ((algebraMap k k[↥H]) a) = algebraMap k k[G] a := by
        simpa [σ] using
          congrArg (fun f : k →+* k[G] => f a)
            (MonoidAlgebra.mapDomainRingHom_comp_algebraMap
              (R := k) (A := k) H.subtype)
      rw [Algebra.smul_def, map_mul, hσalg]
      simpa [Algebra.smul_def] using (mul_smul (algebraMap k k[G] a) (σ r) x)
    Representation.IsIntertwiningMap
      (ρ := (Rep.res H.subtype E.toRep).ρ)
      (σ := Representation.ofModule' (k := k) (G := H) E.V)
      (restrictScalars_owner_linearEquiv (k := k) (G := G) E).toLinearMap := by
  let σ : k[↥H] →+* k[G] := MonoidAlgebra.mapDomainRingHom k H.subtype
  let _ : Module k[↥H] E.V := Module.compHom E.V σ
  let _ : IsScalarTower k k[↥H] E.V := by
    refine ⟨?_⟩
    intro a r x
    change (σ (a • r)) • x = a • ((σ r) • x)
    have hσalg : σ ((algebraMap k k[↥H]) a) = algebraMap k k[G] a := by
      simpa [σ] using
        congrArg (fun f : k →+* k[G] => f a)
          (MonoidAlgebra.mapDomainRingHom_comp_algebraMap
            (R := k) (A := k) H.subtype)
    rw [Algebra.smul_def, map_mul, hσalg]
    simpa [Algebra.smul_def] using (mul_smul (algebraMap k k[G] a) (σ r) x)
  -- Compare the two `H`-actions on generators `h : H`; both are given by the original action of
  -- `h.1 : G` once the restricted scalar structure is unfolded.
  refine Representation.IsIntertwiningMap.mk ?_
  intro h x
  -- Route correction: prove equivariance at the representation level first, then upgrade it to
  -- the owner-level `k[H]`-linear equivalence below.
  calc
    (restrictScalars_owner_linearEquiv (k := k) (G := G) E)
        (((Rep.res H.subtype E.toRep).ρ h) x)
        =
      (restrictScalars_owner_linearEquiv (k := k) (G := G) E)
        ((E.toRep.ρ.asAlgebraHom (MonoidAlgebra.of k G h.1))
          (E.toRep.ρ.asModuleEquiv (E.toRep.ρ.asModuleEquiv.symm x))) := by
            simp
    _ =
      (MonoidAlgebra.single h.1 (1 : k) : k[G]) •
          ((restrictScalars_owner_linearEquiv (k := k) (G := G) E) x) := by
            simpa [FiniteProjectiveGroupAlgebraModule.toRep,
              Rep.ofModuleMonoidAlgebra_obj_ρ, restrictScalars_owner_linearEquiv] using
              (Representation.smul_ofModule_asModule
                (k := k) (G := G) (M := ModuleCat.of k[G] E.V)
                (r := MonoidAlgebra.of k G h.1)
                (m := E.toRep.ρ.asModuleEquiv.symm x))
    _ =
      (MonoidAlgebra.single h (1 : k) : k[↥H]) •
        ((restrictScalars_owner_linearEquiv (k := k) (G := G) E) x) := by
          show (MonoidAlgebra.single h.1 (1 : k) : k[G]) •
              ((restrictScalars_owner_linearEquiv (k := k) (G := G) E) x) =
            σ (MonoidAlgebra.single h (1 : k)) •
              ((restrictScalars_owner_linearEquiv (k := k) (G := G) E) x)
          simp [σ]
    _ = ((Representation.ofModule' (k := k) (G := H) E.V) h)
          ((restrictScalars_owner_linearEquiv (k := k) (G := G) E) x) := by
            simp [Representation.ofModule']

omit [Finite G] [CharP k p] [Fact p.Prime] in
/-- Helper for Exercise 16-16.1-12: the restricted representation is equivalent to the
`Representation.ofModule'` model on the same restricted owner module. -/
private theorem restricted_nonempty_equiv_ofModule'_compHom_owner
    (H : Subgroup G) (E : FiniteProjectiveGroupAlgebraModule k G) :
    let σ : k[↥H] →+* k[G] := MonoidAlgebra.mapDomainRingHom k H.subtype
    let _ : Module k[↥H] E.V := Module.compHom E.V σ
    let _ : IsScalarTower k k[↥H] E.V := by
      refine ⟨?_⟩
      intro a r x
      change (σ (a • r)) • x = a • ((σ r) • x)
      have hσalg : σ ((algebraMap k k[↥H]) a) = algebraMap k k[G] a := by
        simpa [σ] using
          congrArg (fun f : k →+* k[G] => f a)
            (MonoidAlgebra.mapDomainRingHom_comp_algebraMap
              (R := k) (A := k) H.subtype)
      rw [Algebra.smul_def, map_mul, hσalg]
      simpa [Algebra.smul_def] using (mul_smul (algebraMap k k[G] a) (σ r) x)
    Nonempty ((Rep.res H.subtype E.toRep).ρ.Equiv
      (Representation.ofModule' (k := k) (G := H) E.V)) := by
  let σ : k[↥H] →+* k[G] := MonoidAlgebra.mapDomainRingHom k H.subtype
  let _ : Module k[↥H] E.V := Module.compHom E.V σ
  let _ : IsScalarTower k k[↥H] E.V := by
    refine ⟨?_⟩
    intro a r x
    change (σ (a • r)) • x = a • ((σ r) • x)
    have hσalg : σ ((algebraMap k k[↥H]) a) = algebraMap k k[G] a := by
      simpa [σ] using
        congrArg (fun f : k →+* k[G] => f a)
          (MonoidAlgebra.mapDomainRingHom_comp_algebraMap
            (R := k) (A := k) H.subtype)
    rw [Algebra.smul_def, map_mul, hσalg]
    simpa [Algebra.smul_def] using (mul_smul (algebraMap k k[G] a) (σ r) x)
  -- Package the carrier-level identity as a representation equivalence once equivariance is known.
  refine ⟨Representation.Equiv.mk
    (restrictScalars_owner_linearEquiv (k := k) (G := G) E) ?_⟩
  intro h
  ext x
  exact
    (restrictScalars_owner_isIntertwining_restricted_ofModule'
      (k := k) (G := G) (H := H) E).isIntertwining h x

omit [Finite G] [CharP k p] [Fact p.Prime] in
/-- Helper for Exercise 16-16.1-12: the owner of the restricted representation is canonically the
same `k[H]`-module as the ambient owner with scalar action restricted along `k[H] → k[G]`. -/
private theorem restricted_asModuleLinearEquiv_compHom_owner
    (H : Subgroup G) (E : FiniteProjectiveGroupAlgebraModule k G) :
    let σ : k[↥H] →+* k[G] := MonoidAlgebra.mapDomainRingHom k H.subtype
    let _ : Module k[↥H] E.V := Module.compHom E.V σ
    let _ : IsScalarTower k k[↥H] E.V := by
      refine ⟨?_⟩
      intro a r x
      change (σ (a • r)) • x = a • ((σ r) • x)
      have hσalg : σ ((algebraMap k k[↥H]) a) = algebraMap k k[G] a := by
        simpa [σ] using
          congrArg (fun f : k →+* k[G] => f a)
            (MonoidAlgebra.mapDomainRingHom_comp_algebraMap
              (R := k) (A := k) H.subtype)
      rw [Algebra.smul_def, map_mul, hσalg]
      simpa [Algebra.smul_def] using (mul_smul (algebraMap k k[G] a) (σ r) x)
    Nonempty (((Rep.res H.subtype E.toRep).ρ.asModule) ≃ₗ[k[↥H]] E.V) := by
  let σ : k[↥H] →+* k[G] := MonoidAlgebra.mapDomainRingHom k H.subtype
  let _ : Module k[↥H] E.V := Module.compHom E.V σ
  let _ : IsScalarTower k k[↥H] E.V := by
    refine ⟨?_⟩
    intro a r x
    change (σ (a • r)) • x = a • ((σ r) • x)
    have hσalg : σ ((algebraMap k k[↥H]) a) = algebraMap k k[G] a := by
      simpa [σ] using
        congrArg (fun f : k →+* k[G] => f a)
          (MonoidAlgebra.mapDomainRingHom_comp_algebraMap
            (R := k) (A := k) H.subtype)
    rw [Algebra.smul_def, map_mul, hσalg]
    simpa [Algebra.smul_def] using (mul_smul (algebraMap k k[G] a) (σ r) x)
  obtain ⟨eρ⟩ :=
    restricted_nonempty_equiv_ofModule'_compHom_owner
      (k := k) (G := G) (H := H) E
  let f :
      ((Rep.res H.subtype E.toRep).ρ.asModule) →ₗ[k[↥H]]
        (Representation.ofModule' (k := k) (G := H) E.V).asModule :=
    (Representation.IntertwiningMap.equivLinearMapAsModule
      (ρ := (Rep.res H.subtype E.toRep).ρ)
      (σ := Representation.ofModule' (k := k) (G := H) E.V))
      eρ.toIntertwiningMap
  have hf_bij : Function.Bijective f := by
    constructor
    · intro x y hxy
      exact eρ.injective hxy
    · intro w
      refine ⟨(Rep.res H.subtype E.toRep).ρ.asModuleEquiv.symm
        (eρ.symm ((Representation.ofModule' (k := k) (G := H) E.V).asModuleEquiv w)), ?_⟩
      -- Move the owner equality back to the underlying `k`-vector-space picture.
      change eρ ((Rep.res H.subtype E.toRep).ρ.asModuleEquiv
        ((Rep.res H.subtype E.toRep).ρ.asModuleEquiv.symm
          (eρ.symm ((Representation.ofModule' (k := k) (G := H) E.V).asModuleEquiv w)))) =
        (Representation.ofModule' (k := k) (G := H) E.V).asModuleEquiv w
      simp
  obtain ⟨eM⟩ := nonempty_ofModule'_asModuleLinearEquiv (k := k) (H := H) E.V
  -- First identify the restricted owner with the `ofModule'` owner, then forget the latter back
  -- to the original restricted `k[H]`-module `E.V`.
  refine ⟨(LinearEquiv.ofBijective f hf_bij).trans eM⟩

omit [Finite G] [CharP k p] [Fact p.Prime] in
/-- Helper for Exercise 16-16.1-12: a simple `k[H]`-module viewed through
`Representation.ofModule'` is irreducible. -/
private theorem ofModule'_isIrreducible_of_isSimpleModule
    {H : Type u} [Group H]
    (M : Type u) [AddCommGroup M] [Module k M] [Module k[H] M] [IsScalarTower k k[H] M]
    [IsSimpleModule k[H] M] :
    (Representation.ofModule' (k := k) (G := H) M).IsIrreducible := by
  -- Transfer simplicity across the canonical owner-module equivalence and then use the
  -- irreducibility/simple-module bridge.
  rcases nonempty_ofModule'_asModuleLinearEquiv (k := k) (H := H) M with ⟨eM⟩
  exact
    (Representation.irreducible_iff_isSimpleModule_asModule
      (Representation.ofModule' (k := k) (G := H) M)).2
      (@IsSimpleModule.congr (k[H]) inferInstance
        ((Representation.ofModule' (k := k) (G := H) M).asModule)
        (Representation.ofModule' (k := k) (G := H) M).instAddCommGroupAsModule
        (Representation.ofModule' (k := k) (G := H) M).instModuleMonoidAlgebraAsModule
        M inferInstance inferInstance eM inferInstance)

omit [Finite G] [CharP k p] [Fact p.Prime] in
/-- Helper for Exercise 16-16.1-12: an isomorphism of finite-dimensional representations induces
an equivalence of the underlying `k[H]`-modules. -/
private theorem nonempty_asModuleLinearEquiv_of_nonempty_fdRepIso
    {H : Type u} [Group H]
    (τ σ : FDRep k H) (hτσ : Nonempty (τ ≅ σ)) :
    Nonempty (asModule τ.ρ ≃ₗ[k[H]] asModule σ.ρ) := by
  -- Forget the `FDRep` isomorphism to `Rep`, then read its image in `ModuleCat k[H]` as the
  -- required owner-module equivalence.
  rcases hτσ with ⟨e⟩
  exact ⟨by
    simpa using
      (((forget₂ (FDRep k H) (Rep k H)) ⋙ Rep.toModuleMonoidAlgebra
        (k := k) (G := H)).mapIso e).toLinearEquiv⟩

omit [CharP k p] [Fact p.Prime] in
/-- Helper for Exercise 16-16.1-12: a simple trivial finite-dimensional representation is
one-dimensional over the coefficient field. -/
private theorem finrank_eq_one_of_simple_of_isTrivial
    {H : Type u} [Group H]
    (W : FDRep k H) [Simple W] [Representation.IsTrivial W.ρ] :
    Module.finrank k W = 1 := by
  letI : Representation.IsIrreducible W.ρ := FDRep.isIrreducible_of_simple W
  have hW_nontrivial : Nontrivial W := by
    -- A simple object in `FDRep` cannot have a subsingleton carrier.
    have hW_not_subsingleton : ¬ Subsingleton W := by
      intro hW
      letI : Subsingleton W := hW
      have hzero : (𝟙 W : W ⟶ W) = 0 := by
        ext x
        exact Subsingleton.elim _ _
      exact CategoryTheory.id_nonzero W hzero
    exact not_subsingleton_iff_nontrivial.mp hW_not_subsingleton
  letI : Nontrivial W := hW_nontrivial
  obtain ⟨w, hw0⟩ := exists_ne (0 : W)
  let U : Subrepresentation W.ρ :=
    { toSubmodule := Submodule.span k {w}
      apply_mem_toSubmodule := by
        intro g x hx
        rw [Submodule.mem_span_singleton] at hx ⊢
        rcases hx with ⟨c, rfl⟩
        refine ⟨c, ?_⟩
        simp }
  have hU_ne_bot : U ≠ ⊥ := by
    -- The chosen nonzero vector survives in the generated line.
    intro hU
    have hw_mem : w ∈ U.toSubmodule := by
      exact Submodule.subset_span (by simp)
    have hw_bot : w ∈ (⊥ : Subrepresentation W.ρ).toSubmodule := by
      simpa [hU] using hw_mem
    have : w = 0 := by
      simpa using hw_bot
    exact hw0 this
  have hU_top : U = ⊤ := (IsSimpleOrder.eq_bot_or_eq_top U).resolve_left hU_ne_bot
  have hspan : Submodule.span k {w} = ⊤ := by
    -- Simplicity forces the nonzero invariant line to be the whole module.
    simpa [U] using congrArg Subrepresentation.toSubmodule hU_top
  exact (finrank_eq_one_iff_of_nonzero' w hw0).2 fun x ↦ by
    have hx : x ∈ Submodule.span k {w} := by
      simp [hspan]
    simpa [Submodule.mem_span_singleton] using hx

omit [CharP k p] [Fact p.Prime] in
/-- Helper for Exercise 16-16.1-12: a simple trivial finite-dimensional representation is
isomorphic to the one-dimensional trivial representation. -/
private theorem nonempty_iso_trivial_of_simple_of_isTrivial
    {H : Type u} [Group H]
    (W : FDRep k H) [Simple W] [Representation.IsTrivial W.ρ] :
    Nonempty (W ≅ FDRep.of (Representation.trivial k H k)) := by
  -- First reduce to the one-dimensional case forced by simplicity and triviality.
  have hdim :
      Module.finrank k W = 1 :=
    finrank_eq_one_of_simple_of_isTrivial (k := k) W
  rcases Module.nonempty_linearEquiv_of_finrank_eq_one hdim with ⟨e⟩
  have hWrho : W ≅ FDRep.of W.ρ :=
    Action.mkIso (Iso.refl _) fun g => by
      ext x
      rfl
  let hEquiv : Representation.Equiv W.ρ (Representation.trivial k H k) :=
    Representation.Equiv.mk e.symm <| by
      intro g
      ext z
      simp
  exact ⟨hWrho.trans (Representation.Equiv.toFDRepIso hEquiv)⟩

/-- Helper for Exercise 16-16.1-12: every simple finite-dimensional representation of a finite
`p`-group over a field of characteristic `p` is isomorphic to the trivial one-dimensional
representation. -/
private theorem simple_fdRep_nonempty_iso_trivial_of_isPGroup
    {H : Type u} [Group H] [Finite H]
    (hH : IsPGroup p H) (W : FDRep k H) [Simple W] :
    Nonempty (W ≅ FDRep.of (Representation.trivial k H k)) := by
  letI : Representation.IsIrreducible W.ρ := FDRep.isIrreducible_of_simple W
  letI : Representation.IsTrivial W.ρ :=
    isTrivial_of_isIrreducible_of_isPGroup_charP (ρ := W.ρ) hH
  -- Once irreducibility gives triviality in characteristic `p`, the simple-object argument above
  -- identifies the module with the one-dimensional trivial representation.
  exact nonempty_iso_trivial_of_simple_of_isTrivial (k := k) W

/-- Helper for Exercise 16-16.1-12: every simple `k[H]`-module for a finite `p`-group is the
trivial module. -/
private theorem simple_groupAlgebraModule_nonempty_linearEquiv_trivial_of_isPGroup
    {H : Type u} [Group H] [Finite H]
    (hH : IsPGroup p H) {M : Type u}
    [AddCommGroup M] [Module k M] [Module k[H] M] [IsScalarTower k k[H] M]
    [IsSimpleModule k[H] M] [Module.Finite k M] :
    Nonempty (M ≃ₗ[k[H]] (Representation.trivial k H k).asModule) := by
  let τ : FDRep k H := FDRep.of (Representation.ofModule' (k := k) (G := H) M)
  letI : Representation.IsIrreducible τ.ρ :=
    ofModule'_isIrreducible_of_isSimpleModule (k := k) (H := H) M
  letI : Simple τ := FDRep.simple_of_isIrreducible τ
  obtain ⟨eτ⟩ :=
    nonempty_asModuleLinearEquiv_of_nonempty_fdRepIso (k := k) (H := H) τ
      (FDRep.of (Representation.trivial k H k))
      (simple_fdRep_nonempty_iso_trivial_of_isPGroup (p := p) (k := k) hH τ)
  obtain ⟨eM⟩ := nonempty_ofModule'_asModuleLinearEquiv (k := k) (H := H) M
  -- First identify `M` with the owner module of `τ`, then apply the simple `FDRep` classification.
  refine ⟨?_⟩
  let eM' : M ≃ₗ[k[H]] asModule τ.ρ := by
    simpa [τ] using eM.symm
  exact eM'.trans eτ

/-- Helper for Exercise 16-16.1-12: a `k[H]`-submodule inherits the ambient `k`-module structure
by restriction of scalars. -/
private instance groupAlgebra_submodule_module_over_field
    {H : Type u} [Group H] {M : Type u}
    [AddCommGroup M] [Module k M] [Module k[H] M] [IsScalarTower k k[H] M]
    (N : Submodule k[H] M) :
    Module k N := by
  let N' : Submodule k M := Submodule.restrictScalars k N
  change Module k N'
  infer_instance

/-- Helper for Exercise 16-16.1-12: a `k[H]`-submodule also inherits the scalar-tower structure
from the ambient module. -/
private instance groupAlgebra_submodule_isScalarTower
    {H : Type u} [Group H] {M : Type u}
    [AddCommGroup M] [Module k M] [Module k[H] M] [IsScalarTower k k[H] M]
    (N : Submodule k[H] M) :
    IsScalarTower k k[H] N := by
  let N' : Submodule k M := Submodule.restrictScalars k N
  change IsScalarTower k k[H] N'
  infer_instance

/-- Helper for Exercise 16-16.1-12: the carrier of the trivial representation comes with the
canonical `k[H]`-module structure used by `asModule`. -/
private instance trivial_asModule_module
    {H : Type u} [Group H] :
    Module k[H] ((Representation.trivial k H k).asModule) :=
  Representation.instModuleMonoidAlgebraAsModule (ρ := Representation.trivial k H k)

/-- Helper for Exercise 16-16.1-12: over a finite group algebra, a finite projective module is
determined by the largest semisimple quotient of its projective envelope. -/
private theorem projective_linearEquiv_of_largestSemisimpleQuotient_linearEquiv
    {H : Type u} [Group H] [Finite H]
    {P Q : Type u} [AddCommGroup P] [AddCommGroup Q]
    [Module k[H] P] [Module k[H] Q]
    [Module.Projective k[H] P] [Module.Projective k[H] Q]
    [Module.Finite k[H] P] [Module.Finite k[H] Q]
    (hPQ : Nonempty ((P ⧸ Module.jacobson k[H] P) ≃ₗ[k[H]]
      (Q ⧸ Module.jacobson k[H] Q))) :
    Nonempty (P ≃ₗ[k[H]] Q) := by
  let kH : Type u := k[H]
  let _ : Module.Finite k kH := MonoidAlgebra.moduleFinite
  let _ : IsArtinianRing kH := IsArtinianRing.of_finite k kH
  let _ : IsArtinian kH P := by infer_instance
  let _ : IsArtinian kH Q := by infer_instance
  obtain ⟨eQuot⟩ := hPQ
  let qP : P →ₗ[kH] (P ⧸ Module.jacobson kH P) := (Module.jacobson kH P).mkQ
  let qQ : Q →ₗ[kH] (Q ⧸ Module.jacobson kH Q) := (Module.jacobson kH Q).mkQ
  have hqP : qP.IsProjectiveEnvelope := by
    -- The canonical Jacobson-quotient map is the projective envelope of a projective source.
    simpa [qP] using
      (show ((Module.jacobson kH P).mkQ : P →ₗ[kH] P ⧸ Module.jacobson kH P).IsProjectiveEnvelope
        from LinearMap.largestSemisimpleQuotientMk_isProjectiveEnvelope)
  have hqQ : qQ.IsProjectiveEnvelope := by
    simpa [qQ] using
      (show ((Module.jacobson kH Q).mkQ : Q →ₗ[kH] Q ⧸ Module.jacobson kH Q).IsProjectiveEnvelope
        from LinearMap.largestSemisimpleQuotientMk_isProjectiveEnvelope)
  let qQ' : Q →ₗ[kH] (P ⧸ Module.jacobson kH P) :=
    eQuot.symm.toLinearMap.comp qQ
  have hqQ' : qQ'.IsProjectiveEnvelope := by
    -- Transport the second envelope so both projective envelopes have the same target.
    simpa [qQ', qQ] using
      (LinearMap.isProjectiveEnvelope_iff_conj (R := kH)
        (LinearEquiv.refl kH Q) eQuot.symm).2 hqQ
  obtain ⟨eSrc, _⟩ := LinearMap.isProjectiveEnvelope_unique hqP hqQ'
  exact ⟨eSrc⟩

/-- Helper for Exercise 16-16.1-12: Jacobson quotients of finite-dimensional `k[H]`-modules stay
finite-dimensional over the coefficient field `k`. -/
private theorem largestSemisimpleQuotient_moduleFinite
    {H : Type u} [Group H] [Finite H]
    {M : Type u} [AddCommGroup M] [Module k M] [Module k[H] M] [IsScalarTower k k[H] M]
    [Module.Finite k M] :
    Module.Finite k (M ⧸ Module.jacobson k[H] M) := by
  -- Finite generation descends along the Jacobson-quotient map.
  exact
    Module.Finite.of_surjective
      ((Module.jacobson k[H] M).mkQ.restrictScalars k)
      (by
        intro x
        rcases Submodule.mkQ_surjective (Module.jacobson k[H] M) x with ⟨y, rfl⟩
        exact ⟨y, rfl⟩)

/-- Helper for Exercise 16-16.1-12: every semisimple `k[H]`-module for a finite `p`-group is a
finite product of trivial modules. -/
private theorem semisimple_groupAlgebraModule_nonempty_linearEquiv_trivial_pi_of_isPGroup
    {H : Type u} [Group H] [Finite H]
    (hH : IsPGroup p H) {Q : Type u}
    [AddCommGroup Q] [Module k Q] [Module k[H] Q] [IsScalarTower k k[H] Q]
    [IsSemisimpleModule k[H] Q] [Module.Finite k Q] :
    ∃ r : ℕ, Nonempty (Q ≃ₗ[k[H]]
      ((i : Fin r) → (Representation.trivial k H k).asModule)) := by
  let _ : Module.Finite (MonoidAlgebra k H) Q :=
    Module.Finite.of_restrictScalars_finite k (MonoidAlgebra k H) Q
  obtain ⟨r, S, eS, hSsimple⟩ :=
    IsSemisimpleModule.exists_linearEquiv_fin_dfinsupp (MonoidAlgebra k H) Q
  have htriv :
      ∀ i : Fin r,
        Nonempty (↥(S i) ≃ₗ[MonoidAlgebra k H] (Representation.trivial k H k).asModule) := by
    intro i
    let hModule : Module k ↥(S i) :=
      groupAlgebra_submodule_module_over_field (k := k) (H := H) (M := Q) (S i)
    letI : Module k ↥(S i) := hModule
    let hTower : IsScalarTower k k[H] ↥(S i) := by
      refine IsScalarTower.of_algebraMap_smul fun a x ↦ ?_
      ext
      change (((algebraMap k k[H]) a) • (x : Q) : Q) = a • (x : Q)
      exact IsScalarTower.algebraMap_smul (R := k) (A := k[H]) a (x : Q)
    letI : IsScalarTower k k[H] ↥(S i) := hTower
    let hFiniteDimensional : FiniteDimensional k ↥(S i) := by
      let N' : Submodule k Q := Submodule.restrictScalars k (S i)
      change FiniteDimensional k N'
      exact FiniteDimensional.of_injective N'.subtype (Submodule.injective_subtype N')
    letI : FiniteDimensional k ↥(S i) := hFiniteDimensional
    let hFinite : Module.Finite k ↥(S i) := Module.Finite.of_basis (Module.Free.chooseBasis k ↥(S i))
    letI : Module.Finite k ↥(S i) := hFinite
    let hSimple : IsSimpleModule k[H] ↥(S i) := hSsimple i
    letI : IsSimpleModule k[H] ↥(S i) := hSimple
    exact
      @simple_groupAlgebraModule_nonempty_linearEquiv_trivial_of_isPGroup
        p k inferInstance inferInstance inferInstance H inferInstance inferInstance hH
        ↥(S i) inferInstance hModule inferInstance hTower hSimple hFinite
  let eTriv :
      (Π₀ i : Fin r, ↥(S i)) ≃ₗ[MonoidAlgebra k H]
        Π₀ i : Fin r, (Representation.trivial k H k).asModule :=
    DFinsupp.mapRange.linearEquiv fun i ↦ Classical.choice (htriv i)
  refine ⟨r, ?_⟩
  exact ⟨eS.trans (eTriv.trans DFinsupp.linearEquivFunOnFintype)⟩

/-- Helper for Exercise 16-16.1-12: the one-dimensional trivial representation is irreducible. -/
private theorem trivial_representation_isIrreducible
    {H : Type u} [Group H] :
    (Representation.trivial k H k).IsIrreducible := by
  let ρ : Representation k H k := Representation.trivial k H k
  letI : Nontrivial (Subrepresentation ρ) :=
    ⟨⊥, ⊤, fun h ↦
      bot_ne_top <| by simpa using congrArg Subrepresentation.toSubmodule h⟩
  letI : IsSimpleOrder (Submodule k k) :=
    (isSimpleModule_iff k k).1 ((isSimpleModule_iff_finrank_eq_one).2 (by simp))
  refine IsSimpleOrder.of_forall_eq_top fun σ hσ ↦ ?_
  have hσtop : σ.toSubmodule = ⊤ := by
    rcases eq_bot_or_eq_top σ.toSubmodule with hσbot | hσtop
    · exact False.elim <| hσ <|
        Subrepresentation.toSubmodule_injective (by simpa using hσbot)
    · exact hσtop
  exact Subrepresentation.toSubmodule_injective (by simpa using hσtop)

/-- Helper for Exercise 16-16.1-12: the `k[H]`-action on a finite product of trivial modules
collapses to scalar multiplication by an element of `k`. -/
private theorem groupAlgebra_smul_eq_field_smul_on_trivial_pi
    {H : Type u} [Group H] {ι : Type*}
    (a : k[H]) (v : ι → (Representation.trivial k H k).asModule) :
    ∃ c : k, a • v = c • v := by
  refine MonoidAlgebra.induction_on
    (p := fun b : k[H] => ∃ c : k, b • v = c • v) a ?_ ?_ ?_
  · intro h
    refine ⟨1, ?_⟩
    ext i
    change (MonoidAlgebra.single h (1 : k)) • v i = (1 : k) • v i
    rw [Representation.single_smul]
    rfl
  · intro a b ha hb
    rcases ha with ⟨c, hc⟩
    rcases hb with ⟨d, hd⟩
    refine ⟨c + d, ?_⟩
    rw [add_smul, hc, hd, add_smul]
  · intro t b hb
    rcases hb with ⟨c, hc⟩
    refine ⟨t * c, ?_⟩
    calc
      (t • b) • v = ((algebraMap k k[H]) t * b) • v := by
        rw [Algebra.smul_def]
      _ = t • (b • v) := by
        simpa [Algebra.smul_def] using (smul_assoc t b v)
      _ = t • (c • v) := by rw [hc]
      _ = (t * c) • v := by rw [smul_smul]

/-- Helper for Exercise 16-16.1-12: the largest semisimple quotient of the regular `k[H]`-module
is the one-dimensional trivial module. -/
private theorem regular_largestSemisimpleQuotient_nonempty_linearEquiv_trivial_of_isPGroup
    {H : Type u} [Group H] [Finite H]
    (hH : IsPGroup p H) :
    Nonempty ((k[H] ⧸ Module.jacobson k[H] k[H]) ≃ₗ[k[H]]
      (Representation.trivial k H k).asModule) := by
  let kH : Type u := k[H]
  let Q : Type u := kH ⧸ Module.jacobson kH kH
  let _ : Module.Finite k Q := largestSemisimpleQuotient_moduleFinite (k := k) (H := H) (M := kH)
  let _ : IsArtinianRing kH := IsArtinianRing.of_finite k kH
  let _ : IsArtinian kH kH := by infer_instance
  let _ : IsSemisimpleModule kH Q := by
    simpa [Q] using
      (largestSemisimpleQuotient_isSemisimple (R := kH) (M := kH))
  obtain ⟨r, ⟨eQ⟩⟩ :=
    semisimple_groupAlgebraModule_nonempty_linearEquiv_trivial_pi_of_isPGroup
      (p := p) (k := k) hH (Q := Q)
  let q : kH →ₗ[kH] Q := (Module.jacobson kH kH).mkQ
  let q1 : Q := q 1
  have hq1_ne_zero : q1 ≠ 0 := by
    intro hq1
    have h1mem : (1 : kH) ∈ Module.jacobson kH kH := by
      have hq1' : q 1 = 0 := by
        simpa [q1] using hq1
      have h1ker :
          (Module.jacobson kH kH).mkQ (1 : kH) = 0 := by
        change q 1 = 0
        exact hq1'
      exact (Submodule.Quotient.mk_eq_zero (Module.jacobson kH kH)).1 h1ker
    have hjacobson_top : Module.jacobson kH kH = ⊤ := by
      apply top_unique
      intro y _
      have hy1 : y * (1 : kH) ∈ Module.jacobson kH kH := by
        simpa using (Module.jacobson kH kH).smul_mem y h1mem
      simpa using hy1
    exact (Module.jacobson_lt_top kH kH).ne hjacobson_top
  have hcyclic :
      ∀ x : Q, ∃ a : kH, x = a • q1 := by
    intro x
    have hq_surj : Function.Surjective q := by
      simpa [q] using (Submodule.mkQ_surjective (Module.jacobson kH kH))
    rcases hq_surj x with ⟨a, rfl⟩
    refine ⟨a, ?_⟩
    simpa [q, q1] using (q.map_smul a (1 : kH))
  let v : (i : Fin r) → (Representation.trivial k H k).asModule := eQ q1
  have hv_ne_zero : v ≠ 0 := by
    intro hv
    exact hq1_ne_zero (eQ.injective <| by simpa [v] using hv)
  have hspan :
      ∀ y : (i : Fin r) → (Representation.trivial k H k).asModule, ∃ c : k, c • v = y := by
    intro y
    obtain ⟨a, ha⟩ := hcyclic (eQ.symm y)
    rcases groupAlgebra_smul_eq_field_smul_on_trivial_pi
        (k := k) (H := H) (ι := Fin r) a v with ⟨c, hc⟩
    refine ⟨c, ?_⟩
    calc
      c • v = a • v := hc.symm
      _ = eQ (a • q1) := by simp [v]
      _ = eQ (eQ.symm y) := by rw [ha]
      _ = y := by simp
  have hdim_one :
      Module.finrank k ((i : Fin r) → (Representation.trivial k H k).asModule) = 1 :=
    (finrank_eq_one_iff_of_nonzero' v hv_ne_zero).2 hspan
  let eTk :
      ((i : Fin r) → (Representation.trivial k H k).asModule) ≃ₗ[k] (Fin r → k) :=
    LinearEquiv.piCongrRight fun _ => (Representation.trivial k H k).asModuleEquiv
  have hdim_target :
      Module.finrank k ((i : Fin r) → (Representation.trivial k H k).asModule) = r := by
    calc
      Module.finrank k ((i : Fin r) → (Representation.trivial k H k).asModule) =
          Module.finrank k (Fin r → k) := eTk.finrank_eq
      _ = r := by
            simp
  have hr : r = 1 := by
    simpa [hdim_target] using hdim_one
  subst hr
  -- Cyclicity forces the semisimple quotient to collapse to a single trivial factor.
  exact ⟨eQ.trans
    (LinearEquiv.funUnique (Fin 1) kH ((Representation.trivial k H k).asModule))⟩

/-- Helper for Exercise 16-16.1-12: the largest semisimple quotient of a finite free `k[H]`-module
of rank `r` is the rank-`r` product of trivial modules. -/
private theorem free_groupAlgebra_largestSemisimpleQuotient_nonempty_linearEquiv_trivial_pi_of_isPGroup
    {H : Type u} [Group H] [Finite H]
    (hH : IsPGroup p H) (r : ℕ) :
    Nonempty ((((i : Fin r) → k[H]) ⧸ Module.jacobson k[H] ((i : Fin r) → k[H])) ≃ₗ[k[H]]
      ((i : Fin r) → asModule (Representation.trivial k H k))) := by
  let kH : Type u := k[H]
  let Tmod : Type u := (Representation.trivial k H k).asModule
  let _ : Module.Finite k kH := MonoidAlgebra.moduleFinite
  let _ : IsArtinianRing kH := IsArtinianRing.of_finite k kH
  induction r with
  | zero =>
      let hLeft :
          Subsingleton ((((i : Fin 0) → kH) ⧸ Module.jacobson kH ((i : Fin 0) → kH))) := by
        infer_instance
      let hRight : Subsingleton ((i : Fin 0) → Tmod) := by
        infer_instance
      letI := hLeft
      letI := hRight
      -- Both sides are zero modules for the empty free module.
      exact ⟨LinearEquiv.ofSubsingleton _ _⟩
  | succ r ih =>
      let eSplit : ((i : Fin (r + 1)) → kH) ≃ₗ[kH] (kH × ((i : Fin r) → kH)) := by
        -- Reindex the free module into a head factor and a tail free module.
        let eReindex : ((o : Option (Fin r)) → kH) ≃ₗ[kH] ((i : Fin (r + 1)) → kH) :=
          LinearEquiv.piCongrLeft kH (fun _ : Fin (r + 1) => kH) (finSuccEquiv r).symm
        simpa using eReindex.symm.trans (LinearEquiv.piOptionEquivProd kH)
      have hmapJac :
          Submodule.map eSplit.toLinearMap (Module.jacobson kH ((i : Fin (r + 1)) → kH)) =
            Module.jacobson kH (kH × ((i : Fin r) → kH)) := by
        -- The head-tail splitting is a linear equivalence, so it transports the Jacobson radical.
        simpa [eSplit] using
          (Module.map_jacobson_of_bijective (R := kH) (f := eSplit.toLinearMap) eSplit.bijective)
      obtain ⟨eQuotSplit⟩ :
          Nonempty ((((i : Fin (r + 1)) → kH) ⧸ Module.jacobson kH ((i : Fin (r + 1)) → kH))
            ≃ₗ[kH]
              ((kH × ((i : Fin r) → kH)) ⧸ Module.jacobson kH (kH × ((i : Fin r) → kH)))) := by
        exact ⟨Submodule.Quotient.equiv _ _ eSplit hmapJac⟩
      let _ : Module.Free kH ((i : Fin r) → kH) := Module.Free.of_basis (Pi.basisFun kH (Fin r))
      let _ : Module.Finite kH ((i : Fin r) → kH) := Module.Finite.of_basis (Pi.basisFun kH (Fin r))
      let _ : Module.Projective kH ((i : Fin r) → kH) := by infer_instance
      let _ : IsArtinian kH kH := by infer_instance
      let _ : IsArtinian kH ((i : Fin r) → kH) := by infer_instance
      obtain ⟨eProd⟩ :=
        largestSemisimpleQuotient_prod_linearEquiv
          (R := kH) (P := kH) (Q := (i : Fin r) → kH)
      obtain ⟨eHead⟩ :=
        regular_largestSemisimpleQuotient_nonempty_linearEquiv_trivial_of_isPGroup
          (p := p) (k := k) hH
      obtain ⟨eTail⟩ := ih
      let eProdTail :
          (((kH ⧸ Module.jacobson kH kH) ×
              (((i : Fin r) → kH) ⧸ Module.jacobson kH ((i : Fin r) → kH))) ≃ₗ[kH]
            (Tmod × ((i : Fin r) → Tmod))) :=
        LinearEquiv.prodCongr eHead eTail
      let eAsOption :
          (((o : Option (Fin r)) → Tmod) ≃ₗ[kH] (Tmod × ((i : Fin r) → Tmod))) := by
        -- Repackage the head trivial factor and the tail trivial factors into one product.
        simpa using
          (LinearEquiv.piOptionEquivProd kH :
            ((o : Option (Fin r)) → Tmod) ≃ₗ[kH]
              (Tmod × ((i : Fin r) → Tmod)))
      let eQuotReindex :
          (((o : Option (Fin r)) → Tmod) ≃ₗ[kH] ((i : Fin (r + 1)) → Tmod)) :=
        LinearEquiv.piCongrLeft kH (fun _ : Fin (r + 1) => Tmod) (finSuccEquiv r).symm
      -- Compose the head-tail quotient bridge with the induction hypothesis on the tail.
      exact ⟨eQuotSplit.trans (eProd.trans (eProdTail.trans (eAsOption.symm.trans eQuotReindex)))⟩

/-- Helper for Exercise 16-16.1-12: over a local ring, every finite projective module is free. -/
private theorem free_of_finite_projective_over_local_ring
    {R : Type u} [CommRing R] [IsLocalRing R]
    {M : Type*} [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M] :
    Module.Free R M := by
  -- Projective modules are flat, and finite flat modules over a local ring are free.
  let _ : Module.Flat R M := Module.Flat.of_projective
  exact Module.free_of_flat_of_isLocalRing

/-- Helper for Exercise 16-16.1-12: LinearRepresentations_Serre_1977's `15.6` route should identify every finite projective
`k[H]`-module for a finite `p`-group `H` with a free module. -/
private theorem finite_projective_groupAlgebra_free_of_isPGroup
    {H : Type u} [Group H] [Finite H]
    (hH : IsPGroup p H) {M : Type u}
    [AddCommGroup M] [Module k M] [Module k[H] M] [IsScalarTower k k[H] M]
    [Module.Projective k[H] M] [Module.Finite k M] :
    Module.Free k[H] M := by
  let kH : Type u := k[H]
  let Q : Type u := M ⧸ Module.jacobson kH M
  let _ : Module.Finite kH M := Module.Finite.of_restrictScalars_finite k kH M
  let _ : Module.Finite k Q :=
    largestSemisimpleQuotient_moduleFinite (k := k) (H := H) (M := M)
  let _ : IsArtinianRing kH := IsArtinianRing.of_finite k kH
  let _ : IsArtinian kH M := by infer_instance
  let _ : IsSemisimpleModule kH Q := by
    -- The Jacobson quotient is the canonical semisimple quotient of `M`.
    simpa [Q] using largestSemisimpleQuotient_isSemisimple (R := kH) (M := M)
  -- Route correction: `k[H]` is generally noncommutative, so the commutative local-ring shortcut
  -- does not apply. Instead, compare `M` with a free module through their Jacobson quotients.
  obtain ⟨r, ⟨eQ⟩⟩ :=
    semisimple_groupAlgebraModule_nonempty_linearEquiv_trivial_pi_of_isPGroup
      (p := p) (k := k) hH (Q := Q)
  obtain ⟨eFreeQ⟩ :=
    free_groupAlgebra_largestSemisimpleQuotient_nonempty_linearEquiv_trivial_pi_of_isPGroup
      (p := p) (k := k) hH r
  let F : Type u := (i : Fin r) → kH
  let _ : Module.Free kH F := Module.Free.of_basis (Pi.basisFun kH (Fin r))
  let _ : Module.Finite kH F := Module.Finite.of_basis (Pi.basisFun kH (Fin r))
  let _ : Module.Projective kH F := by infer_instance
  obtain ⟨eMF⟩ :=
    projective_linearEquiv_of_largestSemisimpleQuotient_linearEquiv
      (k := k) (H := H) (P := M) (Q := F) ⟨eQ.trans eFreeQ.symm⟩
  -- Transport the explicit free structure on the rank-`r` free module back across the equivalence.
  exact Module.Free.of_equiv eMF.symm

-- Proof sketch: restrict the projective `k[G]`-representation to the Sylow subgroup; over the group
-- algebra of a finite `p`-group in characteristic `p`, every projective module is free.
private theorem finiteProjectiveRep_restrict_sylow_free
    (P : Sylow p G) (n : ℕ) (hcard : Nat.card (P : Subgroup G) = p ^ n)
    (E : FiniteProjectiveGroupAlgebraModule k G) :
    Module.Free k[↥(P : Subgroup G)]
      ((Rep.res (P : Subgroup G).subtype E.toRep).ρ.asModule) := by
  let _ := hcard
  let H : Type u := ↥(P : Subgroup G)
  let M := ((Rep.res (P : Subgroup G).subtype E.toRep).ρ.asModule)
  letI : Fintype H := Fintype.ofFinite H
  have hPGroup : IsPGroup p H := P.isPGroup'
  let σ : k[H] →+* k[G] := MonoidAlgebra.mapDomainRingHom k (P : Subgroup G).subtype
  letI : Module k[H] k[G] := Module.compHom k[G] σ
  letI : Module k[H] E.V := Module.compHom E.V σ
  letI : IsScalarTower k k[H] E.V := by
    -- The `k`-action factors through `k[H]` exactly as it already does through `k[G]`.
    refine ⟨?_⟩
    intro a r x
    change (σ (a • r)) • x = a • ((σ r) • x)
    have hσalg : σ ((algebraMap k k[H]) a) = algebraMap k k[G] a := by
      simpa [σ] using
        congrArg (fun f : k →+* k[G] => f a)
          (MonoidAlgebra.mapDomainRingHom_comp_algebraMap
            (R := k) (A := k) ((P : Subgroup G).subtype))
    rw [Algebra.smul_def, map_mul]
    rw [hσalg]
    simpa [Algebra.smul_def] using (mul_smul (algebraMap k k[G] a) (σ r) x)
  have hfreeAmbient : Module.Free k[H] k[G] := by
    -- The ambient group algebra should first be rewritten as free over the subgroup algebra.
    simpa [H, σ] using
      (subgroup_groupAlgebra_free_of_transversal
        (k := k) (G := G) (H := (P : Subgroup G)))
  have hprojectiveRestricted : Module.Projective k[H] E.V := by
    -- Once the ambient algebra is free, restriction of scalars preserves projectivity.
    simpa [H, σ] using
      (projective_restrictScalars_of_subgroup_groupAlgebra
        (k := k) (G := G) (H := (P : Subgroup G)) E hfreeAmbient)
  letI : Module.Projective k[H] E.V := hprojectiveRestricted
  letI : Module.Finite k E.V := E.finite
  have hfreeRestricted : Module.Free k[H] E.V :=
    finite_projective_groupAlgebra_free_of_isPGroup
      (p := p) (k := k) (H := H) hPGroup
  obtain ⟨eRestricted⟩ :=
    restricted_asModuleLinearEquiv_compHom_owner
      (k := k) (G := G) (H := (P : Subgroup G)) E
  -- Transport freeness across the explicit owner equivalence, keeping the source-faithful proof
  -- focused on the subgroup-freeness and `p`-group projective-to-free steps above.
  let hfreeM : Module.Free k[H] M := by
    let _ : Module.Free k[H] E.V := hfreeRestricted
    exact Module.Free.of_equiv eRestricted.symm
  simpa [M, H] using hfreeM

-- Proof sketch: by the previous theorem the restriction to the Sylow subgroup is free of some
-- rank `r`, so its `k`-dimension is `r * |P| = r * p ^ n`.
private theorem finiteProjectiveRep_finrank_dvd_p_pow_of_sylow
    (P : Sylow p G) (n : ℕ) (hcard : Nat.card (P : Subgroup G) = p ^ n)
    (E : FiniteProjectiveGroupAlgebraModule k G) :
    p ^ n ∣ Module.finrank k E.toRep := by
  classical
  let H : Type u := ↥(P : Subgroup G)
  let M := ((Rep.res (P : Subgroup G).subtype E.toRep).ρ.asModule)
  letI : Fintype H := Fintype.ofFinite H
  letI : Module.Free k[H] M := finiteProjectiveRep_restrict_sylow_free P n hcard E
  letI : Module.Finite k[H] M := Module.Finite.of_restrictScalars_finite k k[H] M
  let bH : Module.Basis H k k[H] := MonoidAlgebra.basis H k
  let bM : Module.Basis (Module.Free.ChooseBasisIndex k[H] M) k[H] M :=
    Module.Free.chooseBasis k[H] M
  letI : Finite (Module.Free.ChooseBasisIndex k[H] M) := Module.Finite.finite_basis bM
  letI : Fintype (Module.Free.ChooseBasisIndex k[H] M) :=
    Fintype.ofFinite (Module.Free.ChooseBasisIndex k[H] M)
  let r : ℕ := Fintype.card (Module.Free.ChooseBasisIndex k[H] M)
  refine ⟨r, ?_⟩
  -- The free `k[H]`-basis of the restriction lifts, via the group-algebra basis, to a `k`-basis.
  have hdim :
      Module.finrank k M =
        Fintype.card H * Fintype.card (Module.Free.ChooseBasisIndex k[H] M) := by
    rw [Module.finrank_eq_card_basis (bH.smulTower bM), Fintype.card_prod]
  -- Rewriting the subgroup cardinality as `p ^ n` yields the desired divisibility witness.
  have hcardH : Fintype.card H = p ^ n := by
    simpa [H, Nat.card_eq_fintype_card] using hcard
  calc
    Module.finrank k E.toRep = Module.finrank k M := by rfl
    _ = Fintype.card H * r := by simpa [r] using hdim
    _ = p ^ n * r := by rw [hcardH]

/-- The dimension homomorphism modulo `p ^ n` on `R_k(G)` descends to the Cartan cokernel as soon
as it vanishes on the range of the Cartan homomorphism. -/
def cartanCokernelDimensionMod
    (n : ℕ)
    (hker : (cartanHom k G).range ≤
      (finiteRepGrothendieckDimensionMod k G p n).ker) :
    cartanCokernel k G →+ ZMod (p ^ n) :=
  QuotientAddGroup.lift
    (cartanHom k G).range
    (finiteRepGrothendieckDimensionMod k G p n)
    hker

-- Proof sketch: every element in the range of `cartanHom k G` is generated by classes of
-- projective modules, and the previous divisibility statement shows that each such class has
-- dimension congruent to `0` modulo `p ^ n`.
/-- If a Sylow `p`-subgroup has order `p ^ n`, then the dimension homomorphism modulo `p ^ n`
vanishes on the range of the Cartan homomorphism. -/
theorem cartanHom_range_le_dimensionMod_ker_of_sylow
    (P : Sylow p G) (n : ℕ) (hcard : Nat.card (P : Subgroup G) = p ^ n) :
    (cartanHom k G).range ≤
      (finiteRepGrothendieckDimensionMod k G p n).ker := by
  intro y hy
  rcases hy with ⟨x, rfl⟩
  change finiteRepGrothendieckDimensionMod k G p n (cartanHom k G x) = 0
  -- Pass to representatives in `P₀[k](G)` and then to the free abelian group on projectives.
  have hfree :
      ∀ a : FreeAbelianGroup (FiniteProjectiveGroupAlgebraModule k G),
        finiteRepGrothendieckDimensionMod k G p n
            (cartanHom k G
              (QuotientAddGroup.mk'
                (finiteProjectiveGroupAlgebraGrothendieckRelations k G) a)) = 0 := by
    intro a
    refine FreeAbelianGroup.induction_on a ?_ ?_ ?_ ?_
    · -- The zero class maps to zero under the composed dimension map.
      simp [finiteRepGrothendieckDimensionMod, finiteRepGrothendieckDimension, finiteRepDimensionLift]
    · intro E
      -- On a generator `[E]ₚ₀`, the Cartan map is just the class `[E.toFiniteRep]₀`.
      change finiteRepGrothendieckDimensionMod k G p n (cartanHom k G [E]ₚ₀) = 0
      rw [cartanHom_projectiveClass_eq]
      -- The previous divisibility theorem says that this class has dimension `0` modulo `p ^ n`.
      change ((finiteRepGrothendieckDimension k G [E.toFiniteRep]₀ : ℤ) : ZMod (p ^ n)) = 0
      change (Int.ofNat (Module.finrank k E.toRep) : ZMod (p ^ n)) = 0
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact Int.ofNat_dvd.mpr
        (finiteProjectiveRep_finrank_dvd_p_pow_of_sylow (P := P) (n := n) (hcard := hcard)
          (E := E))
    · intro E hE
      -- The composed dimension map is additive, so it also vanishes on negative generators.
      simpa [map_neg, hE]
    · intro a b ha hb
      -- Additivity of the Grothendieck-group dimension map propagates the vanishing statement.
      change (finiteRepGrothendieckDimensionMod k G p n)
          ((cartanHom k G)
            ((QuotientAddGroup.mk'
                (finiteProjectiveGroupAlgebraGrothendieckRelations k G) a) +
              (QuotientAddGroup.mk'
                (finiteProjectiveGroupAlgebraGrothendieckRelations k G) b))) = 0
      rw [(cartanHom k G).map_add, (finiteRepGrothendieckDimensionMod k G p n).map_add, ha, hb]
      simp
  exact QuotientAddGroup.induction_on
    (α := FreeAbelianGroup (FiniteProjectiveGroupAlgebraModule k G)) x hfree

variable (k)

/-- The source-facing descended dimension map modulo `p ^ n` on the Cartan cokernel under the
Sylow-order hypothesis `|P| = p ^ n`. -/
def cartanCokernelDimensionModOfSylow
    (P : Sylow p G) (n : ℕ) (hcard : Nat.card (P : Subgroup G) = p ^ n) :
    cartanCokernel k G →+ ZMod (p ^ n) :=
  cartanCokernelDimensionMod n
    (cartanHom_range_le_dimensionMod_ker_of_sylow P n hcard)

/-- Helper for Exercise 16-16.1-12: the descended dimension map sends the trivial class in the
Cartan cokernel to `1` in `ZMod (p ^ n)`. -/
private theorem trivial_class_dimensionModOfSylow_eq_one
    (P : Sylow p G) (n : ℕ) (hcard : Nat.card (P : Subgroup G) = p ^ n) :
    cartanCokernelDimensionModOfSylow k P n hcard
        (QuotientAddGroup.mk' (cartanHom k G).range ([𝟙_ (FDRep k G)]₀)) =
      (1 : ZMod (p ^ n)) := by
  -- Evaluate the quotient lift on the trivial generator and reduce to the one-dimensional
  -- `k`-vector-space dimension of the trivial representation.
  change (Int.ofNat (Module.finrank k k) : ZMod (p ^ n)) = 1
  simp

-- Proof sketch: the class of the one-dimensional trivial representation maps to `1` under the
-- dimension homomorphism, so its image in the cokernel maps to the generator of `ZMod (p ^ n)`.
/-- Exercise 16-16.1-12: if `P` is a Sylow `p`-subgroup of `G` with order `p ^ n`, then the
canonical cokernel-dimension map modulo `p ^ n` is surjective. -/
theorem cartanCokernelDimensionMod_surjective_of_sylow
    (P : Sylow p G) (n : ℕ) (hcard : Nat.card (P : Subgroup G) = p ^ n) :
    Function.Surjective (cartanCokernelDimensionModOfSylow k P n hcard) := by
  intro y
  rcases ZMod.intCast_surjective y with ⟨m, rfl⟩
  refine ⟨m • QuotientAddGroup.mk' (cartanHom k G).range ([𝟙_ (FDRep k G)]₀), ?_⟩
  -- The trivial class already maps to `1`, so its integer multiples realize every residue class.
  rw [map_zsmul, trivial_class_dimensionModOfSylow_eq_one]
  simp

variable {k}

-- Proof sketch: apply the surjective cokernel-dimension map to the multiple
-- `p ^ (n - 1) • [1]`; its image is the nonzero class `p ^ (n - 1)` in `ZMod (p ^ n)` when
-- `n > 0`, so this multiple cannot come from the image of `cartanHom k G`.
/-- The multiple `p ^ (n - 1)` of the trivial class does not lie in the image of the Cartan
homomorphism. -/
theorem trivial_class_p_pow_pred_not_in_cartan_range
    (P : Sylow p G) (n : ℕ) (hn : 0 < n)
    (hcard : Nat.card (P : Subgroup G) = p ^ n) :
    (Int.ofNat (p ^ (n - 1))) • ([𝟙_ (FDRep k G)]₀ : R₀[k](G)) ∉
      (cartanHom k G).range := by
  intro hmem
  let q : cartanCokernel k G :=
    QuotientAddGroup.mk' (cartanHom k G).range
      ((Int.ofNat (p ^ (n - 1))) • ([𝟙_ (FDRep k G)]₀ : R₀[k](G)))
  -- Membership in the Cartan range means that the corresponding cokernel class is zero.
  have hq : q = 0 := by
    exact (QuotientAddGroup.eq_zero_iff _).2 hmem
  have himage :
      cartanCokernelDimensionModOfSylow k P n hcard q =
        (Int.ofNat (p ^ (n - 1)) : ZMod (p ^ n)) := by
    -- The descended dimension map sends this multiple of the trivial class to the same residue.
    rw [show q =
        (Int.ofNat (p ^ (n - 1))) • QuotientAddGroup.mk' (cartanHom k G).range
          ([𝟙_ (FDRep k G)]₀ : R₀[k](G)) by
          rfl]
    rw [map_zsmul, trivial_class_dimensionModOfSylow_eq_one]
    simp
  have hnonzero : (Int.ofNat (p ^ (n - 1)) : ZMod (p ^ n)) ≠ 0 := by
    -- Since `n > 0`, the residue class of `p^(n-1)` is nonzero modulo `p^n`.
    intro hzero
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hzero
    have hnat : p ^ n ∣ p ^ (n - 1) := by
      exact Int.ofNat_dvd_natCast.mp hzero
    have hp1 : 1 < p := (Fact.out : Nat.Prime p).one_lt
    have hlt : p ^ (n - 1) < p ^ n := by
      exact Nat.pow_lt_pow_right hp1 (Nat.sub_lt (Nat.succ_le_of_lt hn) (by decide : 0 < 1))
    exact Nat.not_dvd_of_pos_of_lt (pow_pos (Nat.Prime.pos (Fact.out : Nat.Prime p)) _) hlt hnat
  exact hnonzero <| by simpa [hq] using himage.symm

/-- If `G` is a finite `p`-group and `Q` is a finite projective `k[G]`-module in characteristic
`p`, then the underlying `k[G]`-module of `Q` is free. This is the owner-level wrapper around the
source-faithful freeness step proved earlier in the exercise. -/
theorem FiniteProjectiveGroupAlgebraModule.free_of_charP_of_isPGroup
    (Q : FiniteProjectiveGroupAlgebraModule k G)
    (hG : IsPGroup p G) :
    Module.Free k[G] Q.V := by
  let _ : Module.Projective k[G] Q.V := Q.projective
  let _ : Module.Finite k Q.V := Q.finite
  -- This is exactly the source-faithful projective-implies-free step for finite `p`-groups.
  exact
    finite_projective_groupAlgebra_free_of_isPGroup
      (p := p) (k := k) (H := G) hG

end

end Representation
