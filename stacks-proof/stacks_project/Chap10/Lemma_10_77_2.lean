import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe u v

section

variable {R : Type u} [Ring R] [Small.{v} R]
variable {P : Type v} [AddCommGroup P] [Module R P]

/-- Helper for Lemma 10.77.2: a module is projective exactly when it splits off from a free
module whose ambient additive structure is recorded as an `AddCommGroup`. -/
lemma projective_iff_split_free_addCommGroup :
    Module.Projective R P ↔
      ∃ (F : Type v) (_ : AddCommGroup F) (_ : Module R F) (_ : Module.Free R F)
        (i : P →ₗ[R] F) (s : F →ₗ[R] P), s.comp i = LinearMap.id := by
  constructor
  · intro hP
    -- Translate mathlib's split characterization to the additive-group ambient module used here.
    rcases (Module.Projective.iff_split' (R := R) (P := P)).1 hP with
      ⟨F, hFAdd, hFModule, hFFree, i, s, hs⟩
    letI : AddCommMonoid F := hFAdd
    letI : Module R F := hFModule
    letI : Module.Free R F := hFFree
    letI : AddCommGroup F := Module.addCommMonoidToAddCommGroup R (M := F)
    exact ⟨F, inferInstance, inferInstance, inferInstance, i, s, hs⟩
  · rintro ⟨F, hFAdd, hFModule, hFFree, i, s, hs⟩
    -- A split summand of a free module is projective.
    letI : AddCommGroup F := hFAdd
    letI : Module R F := hFModule
    letI : Module.Free R F := hFFree
    exact Module.Projective.of_split i s hs

/-- Helper for Lemma 10.77.2: the source-facing quantification over all unbundled modules is
equivalent to quantifying over all bundled objects of `ModuleCat R`. -/
lemma extOne_subsingleton_forall_moduleCat_iff :
    (∀ (M : Type v) (_ : AddCommGroup M) (_ : Module R M),
      Subsingleton (Abelian.Ext (ModuleCat.of R P) (ModuleCat.of R M) 1)) ↔
      ∀ (Y : ModuleCat.{v} R), Subsingleton (Abelian.Ext (ModuleCat.of R P) Y 1) := by
  constructor
  · intro hExt Y
    -- Rebundle the target module and simplify `ModuleCat.of` back to the original object.
    simpa using hExt Y inferInstance inferInstance
  · intro hExt M hMAdd hMModule
    -- Evaluate the bundled statement on the module object associated to `M`.
    letI : AddCommGroup M := hMAdd
    letI : Module R M := hMModule
    simpa using hExt (ModuleCat.of R M)

/-- Helper for Lemma 10.77.2: projectivity is equivalent to vanishing of all `Ext¹` classes out
of the module. -/
lemma module_projective_iff_extOne_subsingleton :
    Module.Projective R P ↔
      ∀ (M : Type v) (_ : AddCommGroup M) (_ : Module R M),
        Subsingleton (Abelian.Ext (ModuleCat.of R P) (ModuleCat.of R M) 1) := by
  constructor
  · intro hP
    -- Move from the module-theoretic notion of projective to the categorical one in `ModuleCat`.
    have hProjective : Projective (ModuleCat.of R P) :=
      (IsProjective.iff_projective (R := R) (P := P)).1 hP
    have hExtCat : ∀ (Y : ModuleCat.{v} R),
        Subsingleton (Abelian.Ext (ModuleCat.of R P) Y 1) :=
      (CategoryTheory.projective_iff_subsingleton_ext_one (X := ModuleCat.of R P)).1 hProjective
    exact (extOne_subsingleton_forall_moduleCat_iff (R := R) (P := P)).2 hExtCat
  · intro hExt
    -- Convert the source-facing statement to the bundled form required by the categorical API.
    have hExtCat : ∀ (Y : ModuleCat.{v} R),
        Subsingleton (Abelian.Ext (ModuleCat.of R P) Y 1) :=
      (extOne_subsingleton_forall_moduleCat_iff (R := R) (P := P)).1 hExt
    have hProjective : Projective (ModuleCat.of R P) :=
      (CategoryTheory.projective_iff_subsingleton_ext_one (X := ModuleCat.of R P)).2 hExtCat
    exact (IsProjective.iff_projective (R := R) (P := P)).2 hProjective

/-- Lemma 10.77.2: for an `R`-module `P`, the following are equivalent: `P` is projective, `P`
is a direct summand of a free `R`-module, and `Ext^1_R(P, M) = 0` for every `R`-module `M`. -/
-- Proof sketch: use `Module.Projective.iff_split'` for the direct-summand characterization and
-- `IsProjective.iff_projective` to compare module-theoretic projectivity with projectivity in
-- `ModuleCat R`; then identify vanishing of every class in `Ext^1(P, M)` with the
-- `Subsingleton` criterion `projective_iff_subsingleton_ext_one`.
theorem module_projective_direct_summand_free_extOne_tfae :
    List.TFAE [
      Module.Projective R P,
      ∃ (F : Type v) (_ : AddCommGroup F) (_ : Module R F) (_ : Module.Free R F)
        (i : P →ₗ[R] F) (s : F →ₗ[R] P), s.comp i = LinearMap.id,
      ∀ (M : Type v) (_ : AddCommGroup M) (_ : Module R M),
        Subsingleton (Abelian.Ext (ModuleCat.of R P) (ModuleCat.of R M) 1)
    ] := by
  -- Use clause (1) as the hub: compare it separately with the split-free and `Ext¹` conditions.
  tfae_have 1 ↔ 2 := projective_iff_split_free_addCommGroup (R := R) (P := P)
  tfae_have 1 ↔ 3 := module_projective_iff_extOne_subsingleton (R := R) (P := P)
  tfae_finish

end
