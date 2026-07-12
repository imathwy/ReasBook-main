import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u

section

variable {A : Type u} [CommRing A]

local notation "ModuleInverseSystem" => OrderDual ℕ+ ⥤ ModuleCat A

/- Domain triage:
* `source-facing`: Lemma `10.98.1` says that a sequential inverse system of `A`-modules whose
  `n`th stage is annihilated by `I ^ n` has `I`-adically complete inverse limit.
* `core/canonical` owners: the inverse system owner `OrderDual ℕ+ ⥤ ModuleCat A`, the inverse
  limit owner `limit M_`, the canonical projections `limit.π`, and the adic-completeness owner
  `IsAdicComplete` together with `AdicCompletion.isAdicComplete`.
* `bridge/view`: the factorization of each projection `limit M_ → M_n` through
  `(limit M_) ⧸ I ^ n (limit M_)`, then the induced retraction
  `AdicCompletion I (limit M_) → limit M_`.

Relevant owner declarations sampled for this refinement:
* `IsAdicComplete`
* `AdicCompletion.of_bijective_iff`
* `AdicCompletion.isAdicComplete`
* `CategoryTheory.Limits.limit.π`

Primitive data are only the inverse system `M_` and the stagewise annihilation hypothesis `I^n M_n
= 0`; the inverse limit module and its projections are canonical derived API from `limit M_`. -/

-- Proof sketch: for each positive integer `n`, the projection `M := lim M_n → M_n` factors through
-- `M ⧸ I ^ n M` because `I ^ n M_n = 0`. Passing to the inverse limit of these factorizations gives
-- a retraction `AdicCompletion I M → M` of the canonical map `M → AdicCompletion I M`. Since
-- `AdicCompletion I M` is `I`-adically complete by Lemma `10.96.3`, the retract `M` is also
-- `I`-adically complete.
/-- Helper for Lemma 10.98.1: the `n`th limit projection kills `I ^ n` on the inverse limit. -/
lemma limit_projection_pow_smul_top_le_ker
    (I : Ideal A) (M_ : ModuleInverseSystem)
    (hM_ :
      ∀ n : ℕ+, I ^ (n : ℕ) • (⊤ : Submodule A (M_.obj (OrderDual.toDual n))) = ⊥)
    (n : ℕ+) :
    I ^ (n : ℕ) • (⊤ : Submodule A (limit M_ : ModuleCat A)) ≤
      LinearMap.ker ((limit.π M_ (OrderDual.toDual n)).hom) := by
  -- Map `I ^ n` times the whole limit into the `n`th stage and use the stagewise annihilation.
  have hmaple :
      Submodule.map ((limit.π M_ (OrderDual.toDual n)).hom)
          (I ^ (n : ℕ) • (⊤ : Submodule A (limit M_ : ModuleCat A))) ≤
        I ^ (n : ℕ) • (⊤ : Submodule A (M_.obj (OrderDual.toDual n))) := by
    rw [Submodule.map_smul'']
    exact smul_mono_right _ <| by
      rw [Submodule.map_top]
      exact le_top
  have hmapbot :
      Submodule.map ((limit.π M_ (OrderDual.toDual n)).hom)
          (I ^ (n : ℕ) • (⊤ : Submodule A (limit M_ : ModuleCat A))) ≤
        ⊥ := by
    simpa [hM_ n] using le_trans hmaple (le_of_eq (hM_ n))
  simpa [Submodule.comap_bot] using
    (Submodule.map_le_iff_le_comap.mp hmapbot)

/-- Helper for Lemma 10.98.1: the `n`th limit projection descends through
`(\varprojlim M_n) / I ^ n (\varprojlim M_n)`. -/
def limit_projection_quotient_desc
    (I : Ideal A) (M_ : ModuleInverseSystem)
    (hM_ :
      ∀ n : ℕ+, I ^ (n : ℕ) • (⊤ : Submodule A (M_.obj (OrderDual.toDual n))) = ⊥)
    (n : ℕ+) :
    ((limit M_ : ModuleCat A) ⧸ I ^ (n : ℕ) •
        (⊤ : Submodule A (limit M_ : ModuleCat A))) →ₗ[A]
      M_.obj (OrderDual.toDual n) :=
  (I ^ (n : ℕ) • (⊤ : Submodule A (limit M_ : ModuleCat A))).liftQ
    ((limit.π M_ (OrderDual.toDual n)).hom)
    (limit_projection_pow_smul_top_le_ker I M_ hM_ n)

/-- Helper for Lemma 10.98.1: the descended `n`th stage map recovers the original limit
projection on representatives. -/
lemma limit_projection_quotient_desc_comp_mkQ
    (I : Ideal A) (M_ : ModuleInverseSystem)
    (hM_ :
      ∀ n : ℕ+, I ^ (n : ℕ) • (⊤ : Submodule A (M_.obj (OrderDual.toDual n))) = ⊥)
    (n : ℕ+) :
    (limit_projection_quotient_desc I M_ hM_ n).comp
        (Submodule.mkQ
          (I ^ (n : ℕ) • (⊤ : Submodule A (limit M_ : ModuleCat A)))) =
      (limit.π M_ (OrderDual.toDual n)).hom := by
  -- The quotient lift is defined exactly to extend the stage projection.
  simpa [limit_projection_quotient_desc] using
    (Submodule.liftQ_mkQ
      (p := I ^ (n : ℕ) • (⊤ : Submodule A (limit M_ : ModuleCat A)))
      ((limit.π M_ (OrderDual.toDual n)).hom)
      (limit_projection_pow_smul_top_le_ker I M_ hM_ n))

/-- Helper for Lemma 10.98.1: the descended stage maps are compatible with the transition maps
of the inverse system. -/
lemma limit_projection_quotient_desc_compat
    (I : Ideal A) (M_ : ModuleInverseSystem)
    (hM_ :
      ∀ n : ℕ+, I ^ (n : ℕ) • (⊤ : Submodule A (M_.obj (OrderDual.toDual n))) = ⊥)
    {i j : OrderDual ℕ+} (f : i ⟶ j) :
    (M_.map f).hom ∘ₗ
        limit_projection_quotient_desc I M_ hM_ (OrderDual.ofDual i) =
      limit_projection_quotient_desc I M_ hM_ (OrderDual.ofDual j) ∘ₗ
          AdicCompletion.transitionMap I (limit M_ : ModuleCat A)
          (show ((OrderDual.ofDual j : ℕ+) : ℕ) ≤ ((OrderDual.ofDual i : ℕ+) : ℕ) from
            (show OrderDual.ofDual j ≤ OrderDual.ofDual i from leOfHom f)) := by
  -- It suffices to compare both descended maps on quotient representatives.
  apply DFunLike.ext
  intro x
  refine Quotient.inductionOn' x ?_
  intro y
  have hi :
      (limit_projection_quotient_desc I M_ hM_ (OrderDual.ofDual i))
          (Submodule.Quotient.mk y) =
        (limit.π M_ i).hom y := by
    simpa using
      congrArg (fun g ↦ g y)
        (limit_projection_quotient_desc_comp_mkQ I M_ hM_ (OrderDual.ofDual i))
  have hj :
      (limit_projection_quotient_desc I M_ hM_ (OrderDual.ofDual j))
          (Submodule.Quotient.mk y) =
        (limit.π M_ j).hom y := by
    simpa using
      congrArg (fun g ↦ g y)
        (limit_projection_quotient_desc_comp_mkQ I M_ hM_ (OrderDual.ofDual j))
  calc
    (M_.map f).hom
        ((limit_projection_quotient_desc I M_ hM_ (OrderDual.ofDual i))
          (Submodule.Quotient.mk y))
      = (M_.map f).hom ((limit.π M_ i).hom y) := by rw [hi]
    _ = (limit.π M_ j).hom y := by
          simpa using congrArg (fun g ↦ g.hom y) (limit.w M_ f)
    _ = (limit_projection_quotient_desc I M_ hM_ (OrderDual.ofDual j))
          (Submodule.Quotient.mk y) := by rw [hj]

/-- Helper for Lemma 10.98.1: the adic completion of the inverse limit, viewed as an object of
`ModuleCat A`. -/
abbrev inverse_limit_completion_obj
    (I : Ideal A) (M_ : ModuleInverseSystem) : ModuleCat A :=
  ModuleCat.of A (AdicCompletion I (limit M_ : ModuleCat A))

/-- Helper for Lemma 10.98.1: the cone from the adic completion of the inverse limit to the
inverse system, built from the descended stage projections. -/
lemma completion_to_inverse_limit_cone_naturality
    (I : Ideal A) (M_ : ModuleInverseSystem)
    (hM_ :
      ∀ n : ℕ+, I ^ (n : ℕ) • (⊤ : Submodule A (M_.obj (OrderDual.toDual n))) = ⊥)
    {i j : OrderDual ℕ+} (f : i ⟶ j) :
    ((Functor.const (OrderDual ℕ+) ).obj (inverse_limit_completion_obj I M_)).map f ≫
        ModuleCat.ofHom
          (limit_projection_quotient_desc I M_ hM_ (OrderDual.ofDual j) ∘ₗ
            AdicCompletion.eval I (limit M_ : ModuleCat A)
              (((OrderDual.ofDual j : ℕ+) : ℕ))) =
      ModuleCat.ofHom
          (limit_projection_quotient_desc I M_ hM_ (OrderDual.ofDual i) ∘ₗ
            AdicCompletion.eval I (limit M_ : ModuleCat A)
              (((OrderDual.ofDual i : ℕ+) : ℕ))) ≫
        M_.map f := by
  -- The completion coordinates satisfy the same transition relation as the system.
  apply ModuleCat.hom_ext
  apply DFunLike.ext
  intro x
  let hle :
      ((OrderDual.ofDual j : ℕ+) : ℕ) ≤ ((OrderDual.ofDual i : ℕ+) : ℕ) :=
    show ((OrderDual.ofDual j : ℕ+) : ℕ) ≤ ((OrderDual.ofDual i : ℕ+) : ℕ) from
      (show OrderDual.ofDual j ≤ OrderDual.ofDual i from leOfHom f)
  let xi :=
    AdicCompletion.eval I (limit M_ : ModuleCat A)
      (((OrderDual.ofDual i : ℕ+) : ℕ)) x
  have hcompat :
      (M_.map f).hom
          ((limit_projection_quotient_desc I M_ hM_ (OrderDual.ofDual i)) xi) =
        (limit_projection_quotient_desc I M_ hM_ (OrderDual.ofDual j))
          (AdicCompletion.transitionMap I (limit M_ : ModuleCat A) hle xi) := by
    exact congrArg (fun g ↦ g xi) (limit_projection_quotient_desc_compat I M_ hM_ f)
  exact (congrArg
      (limit_projection_quotient_desc I M_ hM_ (OrderDual.ofDual j)) (x.property hle)).symm.trans
    hcompat.symm

/-- Helper for Lemma 10.98.1: the naturality family used to build the completion-to-limit cone. -/
lemma completion_to_inverse_limit_cone_naturality_family
    (I : Ideal A) (M_ : ModuleInverseSystem)
    (hM_ :
      ∀ n : ℕ+, I ^ (n : ℕ) • (⊤ : Submodule A (M_.obj (OrderDual.toDual n))) = ⊥) :
    ∀ ⦃X Y : OrderDual ℕ+⦄ (f : X ⟶ Y),
      ((Functor.const (OrderDual ℕ+) ).obj (inverse_limit_completion_obj I M_)).map f ≫
          ModuleCat.ofHom
            (limit_projection_quotient_desc I M_ hM_ (OrderDual.ofDual Y) ∘ₗ
              AdicCompletion.eval I (limit M_ : ModuleCat A)
                (((OrderDual.ofDual Y : ℕ+) : ℕ))) =
        ModuleCat.ofHom
            (limit_projection_quotient_desc I M_ hM_ (OrderDual.ofDual X) ∘ₗ
              AdicCompletion.eval I (limit M_ : ModuleCat A)
                (((OrderDual.ofDual X : ℕ+) : ℕ))) ≫
          M_.map f := by
  intro X Y f
  exact completion_to_inverse_limit_cone_naturality I M_ hM_ f

/-- Helper for Lemma 10.98.1: taking the limit of the descended stage maps gives a canonical
retraction from the adic completion back to the inverse limit. -/
abbrev completion_to_inverse_limit_hom
    (I : Ideal A) (M_ : ModuleInverseSystem)
    (hM_ :
      ∀ n : ℕ+, I ^ (n : ℕ) • (⊤ : Submodule A (M_.obj (OrderDual.toDual n))) = ⊥) :=
  limit.lift M_
    { pt := inverse_limit_completion_obj I M_
      π :=
        { app := fun n ↦
            ModuleCat.ofHom
              (limit_projection_quotient_desc I M_ hM_ (OrderDual.ofDual n) ∘ₗ
                AdicCompletion.eval I (limit M_ : ModuleCat A)
                  (((OrderDual.ofDual n : ℕ+) : ℕ)))
          naturality := completion_to_inverse_limit_cone_naturality_family I M_ hM_ } }

/-- Helper for Lemma 10.98.1: the limit-lift map has the expected formula after projecting to
any stage. -/
lemma completion_to_inverse_limit_π_apply
    (I : Ideal A) (M_ : ModuleInverseSystem)
    (hM_ :
      ∀ n : ℕ+, I ^ (n : ℕ) • (⊤ : Submodule A (M_.obj (OrderDual.toDual n))) = ⊥)
    (n : ℕ+) (x : inverse_limit_completion_obj I M_) :
    (limit.π M_ (OrderDual.toDual n)).hom
        ((completion_to_inverse_limit_hom I M_ hM_).hom x) =
      limit_projection_quotient_desc I M_ hM_ n
        (AdicCompletion.eval I (limit M_ : ModuleCat A) (n : ℕ) x) := by
  -- The `limit.lift` stage formula identifies each projection with the defining cone leg.
  change
    (((limit.lift M_
        { pt := inverse_limit_completion_obj I M_
          π :=
            { app := fun m ↦
              ModuleCat.ofHom
                  (limit_projection_quotient_desc I M_ hM_ (OrderDual.ofDual m) ∘ₗ
                    AdicCompletion.eval I (limit M_ : ModuleCat A)
                      (((OrderDual.ofDual m : ℕ+) : ℕ)))
              naturality := completion_to_inverse_limit_cone_naturality_family I M_ hM_ } }) ≫
        limit.π M_ (OrderDual.toDual n)).hom x) =
      limit_projection_quotient_desc I M_ hM_ n
        (AdicCompletion.eval I (limit M_ : ModuleCat A) (n : ℕ) x)
  rw [limit.lift_π]
  rfl

/-- Helper for Lemma 10.98.1: the completion-to-limit comparison is a left inverse to the
canonical completion map. -/
lemma completion_to_inverse_limit_leftInverse
    (I : Ideal A) (M_ : ModuleInverseSystem)
    (hM_ :
      ∀ n : ℕ+, I ^ (n : ℕ) • (⊤ : Submodule A (M_.obj (OrderDual.toDual n))) = ⊥) :
    ModuleCat.ofHom (AdicCompletion.of I (limit M_ : ModuleCat A)) ≫
        completion_to_inverse_limit_hom I M_ hM_ =
      𝟙 (limit M_) := by
  -- Compare the candidate splitting after every stage projection of the inverse limit.
  apply limit.hom_ext
  intro n
  apply ModuleCat.hom_ext
  ext x
  change
    (limit.π M_ (OrderDual.toDual n)).hom
        ((completion_to_inverse_limit_hom I M_ hM_).hom
          (AdicCompletion.of I (limit M_ : ModuleCat A) x)) =
      (limit.π M_ (OrderDual.toDual n)).hom x
  rw [completion_to_inverse_limit_π_apply]
  rw [AdicCompletion.eval_of]
  simpa using congrArg (fun g ↦ g x) (limit_projection_quotient_desc_comp_mkQ I M_ hM_ n)

/-- Helper for Lemma 10.98.1: the underlying linear map of the completion-to-limit comparison. -/
abbrev completion_to_inverse_limit
    (I : Ideal A) (M_ : ModuleInverseSystem)
    (hM_ :
      ∀ n : ℕ+, I ^ (n : ℕ) • (⊤ : Submodule A (M_.obj (OrderDual.toDual n))) = ⊥) :
    AdicCompletion I (limit M_ : ModuleCat A) →ₗ[A] (limit M_ : ModuleCat A) :=
  (completion_to_inverse_limit_hom I M_ hM_).hom

/-- Helper for Lemma 10.98.1: forgetting the categorical splitting yields a linear left inverse
for the completion map. -/
lemma completion_to_inverse_limit_leftInverse_linear
    (I : Ideal A) (M_ : ModuleInverseSystem)
    (hM_ :
      ∀ n : ℕ+, I ^ (n : ℕ) • (⊤ : Submodule A (M_.obj (OrderDual.toDual n))) = ⊥) :
    (completion_to_inverse_limit I M_ hM_).comp
        (AdicCompletion.of I (limit M_ : ModuleCat A)) =
      LinearMap.id := by
  -- Forgetting the category structure turns the split identity into a linear-map identity.
  simpa [completion_to_inverse_limit] using
    congrArg ModuleCat.Hom.hom (completion_to_inverse_limit_leftInverse I M_ hM_)

/-- Helper for Lemma 10.98.1: a linear retract of an `I`-adically complete module is again
`I`-adically complete. -/
lemma isAdicComplete_of_leftInverse
    (I : Ideal A)
    {M : Type*} [AddCommGroup M] [Module A M]
    {N : Type*} [AddCommGroup N] [Module A N]
    (f : M →ₗ[A] N) (g : N →ₗ[A] M) (hgf : g.comp f = LinearMap.id)
    (hN : IsAdicComplete I N) :
    IsAdicComplete I M := by
  let _ : IsAdicComplete I N := hN
  -- Show that `M → M^` is bijective by transporting points through the retraction.
  rw [← AdicCompletion.of_bijective_iff]
  refine ⟨?_, ?_⟩
  · intro x y hxy
    -- Injectivity descends because the completion map on `N` is injective.
    have hfy :
        AdicCompletion.of I N (f x) = AdicCompletion.of I N (f y) := by
      simpa [AdicCompletion.map_of] using congrArg (AdicCompletion.map I f) hxy
    have hfxy : f x = f y :=
      (AdicCompletion.of_injective (I := I) (M := N)) hfy
    have hleft : ∀ z : M, g (f z) = z := by
      intro z
      simpa [LinearMap.comp_apply] using congrArg (fun k ↦ k z) hgf
    calc
      x = g (f x) := by symm; exact hleft x
      _ = g (f y) := by simpa using congrArg g hfxy
      _ = y := hleft y
  · intro x
    -- Surjectivity descends by lifting into the completion of `N` and retracting back.
    obtain ⟨y, hy⟩ := AdicCompletion.of_surjective I N (AdicCompletion.map I f x)
    refine ⟨g y, ?_⟩
    calc
      AdicCompletion.of I M (g y)
          = AdicCompletion.map I g (AdicCompletion.of I N y) := by
              simp [AdicCompletion.map_of]
      _ = AdicCompletion.map I g (AdicCompletion.map I f x) := by rw [hy]
      _ = AdicCompletion.map I (g.comp f) x := by
            simpa using congrArg (fun F ↦ F x) (AdicCompletion.map_comp (I := I) f g)
      _ = AdicCompletion.map I (LinearMap.id : M →ₗ[A] M) x := by rw [hgf]
      _ = x := by
            simpa using congrArg (fun F ↦ F x) (AdicCompletion.map_id (I := I) (M := M))

/-- Lemma 10.98.1: if `I` is a finitely generated ideal and `(M_n)` is an inverse system of
`A`-modules over `ℕ+` with `I ^ n M_n = 0` for every stage `n`, then the inverse limit
`\varprojlim M_n` is `I`-adically complete. -/
@[stacks 0G1Q]
theorem isAdicComplete_inverseLimit_of_stagewise_pow_smul_top_eq_bot
    (I : Ideal A) (hI : I.FG) (M_ : ModuleInverseSystem)
    (hM_ :
      ∀ n : ℕ+, I ^ (n : ℕ) • (⊤ : Submodule A (M_.obj (OrderDual.toDual n))) = ⊥) :
    IsAdicComplete I (limit M_ : ModuleCat A) := by
  -- Route correction: close via the textbook retract argument instead of unfolding completeness.
  exact isAdicComplete_of_leftInverse I
    (AdicCompletion.of I (limit M_ : ModuleCat A))
    (completion_to_inverse_limit I M_ hM_)
    (completion_to_inverse_limit_leftInverse_linear I M_ hM_)
    (AdicCompletion.isAdicComplete (I := I) (M := (limit M_ : ModuleCat A)) hI)

end
