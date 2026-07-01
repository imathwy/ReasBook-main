import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- Owner-form criterion for Lemma 10.36.2: if a finitely generated `R`-submodule `M` of `S`
contains `1` and is stable under multiplication by `y`, then `y` is integral over `R`. -/
theorem isIntegral_of_stable_fg_submodule {y : S} {M : Submodule R S}
    (hfg : M.FG) (h1 : (1 : S) ∈ M) (hy : ∀ m ∈ M, y * m ∈ M) :
    IsIntegral R y := by
  haveI : Module.Finite R M := Module.Finite.of_fg hfg
  let T : Subalgebra R S :=
    { carrier := {z : S | ∀ m ∈ M, z * m ∈ M}
      zero_mem' := by
        intro m hm
        simp
      add_mem' := by
        intro a b ha hb m hm
        simpa [add_mul] using M.add_mem (ha m hm) (hb m hm)
      one_mem' := by
        intro m hm
        simpa using hm
      mul_mem' := by
        intro a b ha hb m hm
        simpa [mul_assoc] using ha (b * m) (hb m hm)
      algebraMap_mem' := by
        intro r m hm
        simpa [Algebra.smul_def] using M.smul_mem r hm }
  let act : T →ₐ[R] Module.End R M :=
    AlgHom.ofLinearMap
      { toFun := fun z ↦
          { toFun := fun m ↦ ⟨z * m, z.2 m m.2⟩
            map_add' := by
              intro a b
              ext
              simp [mul_add]
            map_smul' := by
              intro r m
              ext
              simp [Algebra.smul_def, mul_assoc, mul_comm] }
        map_add' := by
          intro a b
          ext m
          simp [add_mul]
        map_smul' := by
          intro r z
          ext m
          simp [Algebra.smul_def, mul_assoc] }
      (by
        ext m
        simp)
      (by
        intro a b
        ext m
        simp [mul_assoc])
  let oneM : M := ⟨1, h1⟩
  have hact_inj : Function.Injective act := by
    intro a b hab
    ext
    simpa [act, oneM] using congrArg Subtype.val (congrArg (fun f : Module.End R M ↦ f oneM) hab)
  have hT : Algebra.IsIntegral R T := Algebra.IsIntegral.of_injective act hact_inj
  letI : Algebra.IsIntegral R T := hT
  exact (Algebra.IsIntegral.isIntegral (⟨y, hy⟩ : T)).map T.val

/-- Lemma 10.36.2: if there exists a finitely generated `R`-submodule `M` of `S` containing `1`
and stable under multiplication by `y`, then `y` is integral over `R`. This is the thin
source-facing corollary of `isIntegral_of_stable_fg_submodule`. -/
theorem isIntegral_of_exists_fg_submodule_of_one_mem_of_mul_mem {y : S}
    (hM : ∃ M : Submodule R S, M.FG ∧ (1 : S) ∈ M ∧ ∀ m ∈ M, y * m ∈ M) :
    IsIntegral R y := by
  rcases hM with ⟨M, hfg, h1, hy⟩
  exact isIntegral_of_stable_fg_submodule hfg h1 hy

end
