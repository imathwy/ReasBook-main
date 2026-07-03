import Mathlib

noncomputable section

universe u

open CategoryTheory
open scoped MonoidalCategory Representation MonoidAlgebra

namespace Representation

section

variable {p : ℕ}
variable {k : Type u} [Field k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

omit [Finite G] [CharP k p] [Fact p.Prime] in
/-- Helper for Exercise 16-16.1-12: a representation equivalence induces an equivalence of the
corresponding owner `k[H]`-modules. -/
theorem nonempty_asModuleLinearEquiv_of_repEquiv
    {H : Type u} [Group H]
    {V W : Type u} [AddCommGroup V] [AddCommGroup W]
    [Module k V] [Module k W]
    (ρ : Representation k H V) (σ : Representation k H W) (e : ρ.Equiv σ) :
    Nonempty (ρ.asModule ≃ₗ[k[H]] σ.asModule) := by
  -- First identify the owner modules with their underlying `k`-vector spaces, then transport the
  -- `k[H]`-action across the representation equivalence.
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
        -- Check the compatibility one monoid-algebra basis vector at a time.
        refine MonoidAlgebra.induction_on
          (p := fun s : k[H] =>
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

omit [Finite G] in
/-- Helper for Exercise 16-16.1-12: after fixing a right transversal, left multiplication by
`h : H` on `G` matches the free `H`-action on the corresponding free model. -/
theorem rightTransversal_freeModel_map_single_smul
    (H : Subgroup G) (T : H.RightTransversal) (h : H) (g : G) (r : k) :
    let e : G ≃ (↥(T : Set G) × H) :=
      T.2.equiv.trans (Equiv.prodComm H ↥(T : Set G))
    let Φ : (G →₀ k) ≃ₗ[k] (↥(T : Set G) →₀ H →₀ k) :=
      Finsupp.domLCongr e ≪≫ₗ Finsupp.curryLinearEquiv k
    Φ (Finsupp.single (h.1 * g) r) =
      (Representation.free k H ↥(T : Set G) h) (Φ (Finsupp.single g r)) := by
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

omit [Finite G] in
/-- Helper for Exercise 16-16.1-12: restricting the left-regular representation to `H` is the
free representation on any right transversal of `H`. -/
theorem right_transversal_restricted_leftRegular_equiv_free
    (H : Subgroup G) (T : H.RightTransversal) :
    Nonempty (Representation.Equiv
      ((Representation.leftRegular k G).comp H.subtype)
      (Representation.free k H ↥(T : Set G))) := by
  let e : G ≃ (↥(T : Set G) × H) :=
    T.2.equiv.trans (Equiv.prodComm H ↥(T : Set G))
  let Φ : (G →₀ k) ≃ₗ[k] (↥(T : Set G) →₀ H →₀ k) :=
    Finsupp.domLCongr e ≪≫ₗ Finsupp.curryLinearEquiv k
  refine ⟨Representation.Equiv.mk Φ ?_⟩
  intro h
  -- Check the intertwining identity on singleton basis vectors of the regular representation.
  apply Finsupp.lhom_ext'
  intro g
  apply LinearMap.ext
  intro r
  simpa [Φ, e] using
    rightTransversal_freeModel_map_single_smul (k := k) (G := G) H T h g r

omit [Finite G] [CharP k p] [Fact p.Prime] in
/-- Helper for Exercise 16-16.1-12: the restricted left-regular owner is literally the group
algebra `k[G]` with scalars restricted along `k[H] → k[G]`. -/
theorem restricted_leftRegular_asModuleLinearEquiv_compHom_groupAlgebra
    (H : Subgroup G) :
    let σ : k[↥H] →+* k[G] := MonoidAlgebra.mapDomainRingHom k H.subtype
    let _ : Module k[↥H] k[G] := Module.compHom k[G] σ
    Nonempty (Representation.asModule ((Representation.leftRegular k G).comp H.subtype) ≃ₗ[k[↥H]]
      k[G]) := by
  let σ : k[↥H] →+* k[G] := MonoidAlgebra.mapDomainRingHom k H.subtype
  let _ : Module k[↥H] k[G] := Module.compHom k[G] σ
  -- Keep the literal carrier `k[G]` and compare the restricted regular action directly with the
  -- `Module.compHom` scalar action along `k[H] → k[G]`.
  refine ⟨
    { (Representation.asModuleEquiv ((Representation.leftRegular k G).comp H.subtype)) with
      map_smul' := ?_ }⟩
  intro r x
  let y : k[G] :=
    (Representation.asModuleEquiv ((Representation.leftRegular k G).comp H.subtype)) x
  calc
    (Representation.asModuleEquiv ((Representation.leftRegular k G).comp H.subtype)) (r • x) =
        (Representation.asAlgebraHom ((Representation.leftRegular k G).comp H.subtype) r) y := by
          simpa [y] using
            (Representation.asModuleEquiv_map_smul
              (ρ := ((Representation.leftRegular k G).comp H.subtype)) r x)
    _ = σ r * y := by
          refine MonoidAlgebra.induction_on
            (p := fun s : k[↥H] =>
              (Representation.asAlgebraHom ((Representation.leftRegular k G).comp H.subtype) s) y =
                σ s * y) r ?_ ?_ ?_
          · intro h
            ext g
            simpa [σ, Algebra.smul_def] using
              (Finsupp.mapDomain_equiv_apply (f := Equiv.mulLeft h.1) y g)
          · intro a b ha hb
            calc
              ((Representation.asAlgebraHom ((Representation.leftRegular k G).comp H.subtype))
                  (a + b)) y
                  =
              ((Representation.asAlgebraHom ((Representation.leftRegular k G).comp H.subtype))
                  a) y +
                ((Representation.asAlgebraHom ((Representation.leftRegular k G).comp H.subtype))
                  b) y := by
                    simp
              _ = σ a * y + σ b * y := by
                    rw [ha, hb]
                    rfl
              _ = (σ a + σ b) * y := by rw [add_mul]
              _ = σ (a + b) * y := by
                    rw [map_add]
          · intro a b hb
            calc
              ((Representation.asAlgebraHom ((Representation.leftRegular k G).comp H.subtype))
                  (a • b)) y
                  =
                ((Representation.asAlgebraHom ((Representation.leftRegular k G).comp H.subtype))
                  ((algebraMap k k[↥H]) a))
                    (((Representation.asAlgebraHom
                      ((Representation.leftRegular k G).comp H.subtype)) b) y) := by
                        rw [Algebra.smul_def, map_mul, Module.End.mul_apply]
              _ = a •
                  (((Representation.asAlgebraHom
                    ((Representation.leftRegular k G).comp H.subtype)) b) y) := by
                      simp [Representation.asAlgebraHom_single]
              _ = a • (σ b * y) := by
                    exact congrArg (fun z => a • z) hb
              _ = σ ((algebraMap k k[↥H]) a * b) * y := by
                    calc
                      a • (σ b * y) = σ ((algebraMap k k[↥H]) a) * (σ b * y) := by
                        simp [Algebra.smul_def, σ]
                      _ = (σ ((algebraMap k k[↥H]) a) * σ b) * y := by
                            rw [mul_assoc]
                      _ = σ ((algebraMap k k[↥H]) a * b) * y := by
                            rw [← map_mul]
              _ = σ (a • b) * y := by
                    simp [Algebra.smul_def]
    _ = r • y := by
          rfl

/-- Helper for Exercise 16-16.1-12: a right-transversal decomposition of `G` should exhibit
`k[G]` as a free `k[H]`-module. -/
theorem subgroup_groupAlgebra_free_of_transversal
    (H : Subgroup G) :
    let σ : k[↥H] →+* k[G] := MonoidAlgebra.mapDomainRingHom k H.subtype
    let _ : Module k[↥H] k[G] := Module.compHom k[G] σ
    Module.Free k[↥H] k[G] := by
  let σ : k[↥H] →+* k[G] := MonoidAlgebra.mapDomainRingHom k H.subtype
  let _ : Module k[↥H] k[G] := Module.compHom k[G] σ
  -- Follow LinearRepresentations_Serre_1977's transversal argument first, then transport the resulting free `k[H]`-basis
  -- from the restricted regular owner to the literal `k[G]` owner.
  let T : H.RightTransversal := default
  obtain ⟨eρ⟩ :=
    right_transversal_restricted_leftRegular_equiv_free (k := k) (G := G) H T
  obtain ⟨eM⟩ :=
    nonempty_asModuleLinearEquiv_of_repEquiv
      (k := k)
      (H := ↥H)
      (V := G →₀ k)
      (W := ↥(T : Set G) →₀ H →₀ k)
      ((Representation.leftRegular k G).comp H.subtype)
      (Representation.free k H ↥(T : Set G))
      eρ
  let _ : Module.Free k[↥H] (Representation.free k H ↥(T : Set G)).asModule := by
    simpa using
      (Representation.free_asModule_free (k := k) (G := ↥H) (α := ↥(T : Set G)))
  -- Transport the canonical free basis of `Rep.free` back to the restricted regular owner.
  let hfreeReg :
      Module.Free k[↥H]
        (Representation.asModule ((Representation.leftRegular k G).comp H.subtype)) :=
    Module.Free.of_equiv eM.symm
  obtain ⟨eOwner⟩ :=
    restricted_leftRegular_asModuleLinearEquiv_compHom_groupAlgebra
      (k := k) (G := G) H
  let _ :
      Module.Free k[↥H]
        (Representation.asModule ((Representation.leftRegular k G).comp H.subtype)) :=
    hfreeReg
  let hfreeOwner : Module.Free k[↥H] k[G] := Module.Free.of_equiv eOwner
  simpa using hfreeOwner

end

end Representation
