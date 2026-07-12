import StacksProject_2024.Chap10.Lemma_10_13_2
import StacksProject_2024.Chap17.Lemma_17_3_1
import StacksProject_2024.Chap17.Lemma_17_21_1
import StacksProject_2024.Chap17.ModuleRestrictionAndStalks
import Mathlib.Tactic.StacksAttribute

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.RingedSpace
open scoped AlgebraicGeometry
open scoped TensorProduct

noncomputable section

namespace CategoryTheory.ShortComplex

variable {X : RingedSpace}

local notation "ModX" => X.Modules

/- Domain-style sampling for Lemma 17.21.4:
- primary domain: symmetric and exterior power exact sequences of `\mathcal O_X`-modules on a
  ringed space;
- inspected owner declarations:
  `RingedSpace.symmetricPowerLeftTensorMap`,
  `RingedSpace.exteriorPowerLeftTensorMap`,
  `RingedSpace.symmetricPowerMap`,
  `RingedSpace.exteriorPowerMap`,
  `CategoryTheory.ShortComplex.ShortExact.stalkShortComplex`,
  `symmetric_power_exact_of_exact`,
  `exterior_power_exact_of_exact`;
- best owner abstraction:
  the source-facing sequences belong on the ambient owner `S : ShortComplex (X.Modules)`, while
  the short-exact consequences belong on the canonical owner namespace
  `CategoryTheory.ShortComplex.ShortExact`; the ringed-space power-operation maps are primitive
  data from Lemma `17.21.1`, and the module-valued exactness theorems from Lemma `10.13.2` are a
  bridge used after passing to stalks;
- primitive-vs-derived split:
  primitive data are a short complex `S : ShortComplex ModX` and a degree `n : ℕ`;
  derived API consists of the induced power-operation maps and the resulting short-exact
  sequences.

Source/core/bridge triage:
- `source-facing`: the canonical symmetric- and exterior-power sequences attached to a short
  complex of `\mathcal O_X`-modules;
- `core/canonical`: `ShortComplex (X.Modules)`, `ShortComplex.ShortExact`,
  `symmetricPowerLeftTensorMap`, `exteriorPowerLeftTensorMap`, `symmetricPowerMap`,
  and `exteriorPowerMap`;
- `bridge/view`: the stalkwise comparison with the module-theoretic exactness owners
  `symmetric_power_exact_of_exact` and `exterior_power_exact_of_exact`. -/

section

variable (S : ShortComplex ModX) (n : ℕ)

/-- Helper for Lemma 17.21.4: the symmetric-power sequence has zero composite. -/
private theorem symmetricPowerSequenceCompEqZero :
    (symmetricPowerLeftTensorMap n S.f) ≫ (symmetricPowerMap (n + 1) S.g) = 0 := by
  -- Proof comment: unfold the sheaf-level maps and push the vanishing back to the underlying
  -- sheafification functor; the remaining composite is induced by `S.g ≫ S.f = 0`.
  simp [AlgebraicGeometry.RingedSpace.symmetricPowerLeftTensorMap,
    AlgebraicGeometry.RingedSpace.symmetricPowerMap, Category.assoc, Functor.map_comp, S.zero]

/-- The canonical symmetric-power short complex attached to a short complex of
`\mathcal O_X`-modules in degree `n + 1`. -/
def symmetricPowerSequence :
    ShortComplex ModX :=
  ShortComplex.mk
    (symmetricPowerLeftTensorMap n S.f)
    (symmetricPowerMap (n + 1) S.g)
    (symmetricPowerSequenceCompEqZero (S := S) (n := n))

/-- Helper for Lemma 17.21.4: the exterior-power sequence has zero composite. -/
private theorem exteriorPowerSequenceCompEqZero :
    (exteriorPowerLeftTensorMap n S.f) ≫ (exteriorPowerMap (n + 1) S.g) = 0 := by
  -- Proof comment: after unfolding the two sheafified power maps, the composite is induced from
  -- the sectionwise exterior-power composite attached to `S.g ≫ S.f = 0`.
  simp [AlgebraicGeometry.RingedSpace.exteriorPowerLeftTensorMap,
    AlgebraicGeometry.RingedSpace.exteriorPowerMap, Category.assoc, Functor.map_comp, S.zero]

/-- The canonical exterior-power short complex attached to a short complex of
`\mathcal O_X`-modules in degree `n + 1`. -/
def exteriorPowerSequence :
    ShortComplex ModX :=
  ShortComplex.mk
    (exteriorPowerLeftTensorMap n S.f)
    (exteriorPowerMap (n + 1) S.g)
    (exteriorPowerSequenceCompEqZero (S := S) (n := n))

end

end CategoryTheory.ShortComplex

namespace CategoryTheory.ShortComplex.ShortExact

open AlgebraicGeometry.RingedSpace

variable {X : RingedSpace}

local notation "ModX" => X.Modules

section

variable {S : ShortComplex ModX}

/-- Helper for Lemma 17.21.4: the commutative ring of sections over an open set. -/
private abbrev sectionRing (X : RingedSpace) (U : (Opens X)ᵒᵖ) :=
  X.presheaf.obj U

/-- Helper for Lemma 17.21.4: after restricting scalars along an algebra map, the target exterior
power carries the source scalar action. -/
private local instance exteriorPowerModule
    {R S M : Type _} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [Module S M] (n : ℕ) :
    Module R ↥(⋀[S]^n M) :=
  Module.compHom _ (algebraMap R S)

/-- Helper for Lemma 17.21.4: after restricting scalars along an algebra map, the target symmetric
power carries the source scalar action. -/
private local instance symmetricPowerModule
    {R S M : Type _} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [Module S M] (n : ℕ) :
    Module R (Sym[S] (SymmetricPower.UFin n) M) :=
  Module.compHom _ (algebraMap R S)

/-- Helper for Lemma 17.21.4: a linear map into a scalar-restricted target induces the
corresponding map on fixed-degree exterior powers. -/
private noncomputable def exteriorPowerRestrict
    {R S M N : Type _} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    (n : ℕ) (f : M →ₗ[R] N) :
    ⋀[R]^n M →ₗ[R] ⋀[S]^n N := by
  letI : Module R ↥(⋀[S]^n N) := exteriorPowerModule n
  letI : IsScalarTower R S ↥(⋀[S]^n N) := IsScalarTower.of_compHom R S ↥(⋀[S]^n N)
  let ιN : N [⋀^Fin n]→ₗ[S] ↥(⋀[S]^n N) := exteriorPower.ιMulti S n
  let ιN' : N [⋀^Fin n]→ₗ[R] ↥(⋀[S]^n N) :=
    { toMultilinearMap :=
        { toFun := ιN
          map_update_add' := by
            intro _ m i x y
            simpa using ιN.map_update_add m i x y
          map_update_smul' := by
            intro _ m i r x
            simpa only [algebraMap_smul S] using ιN.map_update_smul m i (algebraMap R S r) x }
      map_eq_zero_of_eq' := by
        intro m i j hij hne
        exact ιN.map_eq_zero_of_eq m hij hne }
  -- Proof comment: the alternating universal property packages the scalar-restricted target as
  -- the correct exterior-power recipient.
  exact show ⋀[R]^n M →ₗ[R] ⋀[S]^n N from
    exteriorPower.alternatingMapLinearEquiv (ιN'.compLinearMap f)

/-- Helper for Lemma 17.21.4: a linear map into a scalar-restricted target induces the
corresponding map on fixed-degree symmetric powers. -/
private noncomputable def symmetricPowerRestrict
    {R S M N : Type _} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    (n : ℕ) (f : M →ₗ[R] N) :
    Sym[R] (SymmetricPower.UFin n) M →ₗ[R] Sym[S] (SymmetricPower.UFin n) N := by
  letI : Module R (Sym[S] (SymmetricPower.UFin n) N) := symmetricPowerModule n
  letI : IsScalarTower R S (Sym[S] (SymmetricPower.UFin n) N) :=
    IsScalarTower.of_compHom R S (Sym[S] (SymmetricPower.UFin n) N)
  let tprodN :
      MultilinearMap S (fun _ : SymmetricPower.UFin n ↦ N)
        (Sym[S] (SymmetricPower.UFin n) N) :=
    SymmetricPower.tprod S
  let tprodN' :
      MultilinearMap R (fun _ : SymmetricPower.UFin n ↦ N)
        (Sym[S] (SymmetricPower.UFin n) N) :=
    { toFun := tprodN
      map_update_add' := by
        intro _ m i x y
        simpa using tprodN.map_update_add m i x y
      map_update_smul' := by
        intro _ m i r x
        simpa only [algebraMap_smul S] using tprodN.map_update_smul m i (algebraMap R S r) x }
  let tensorLift :
      (⨂[R] (_ : SymmetricPower.UFin n), M) →ₗ[R] Sym[S] (SymmetricPower.UFin n) N :=
    PiTensorProduct.lift
      (tprodN'.compLinearMap fun _ ↦ f)
  have hrel :
      addConGen (SymmetricPower.Rel R (SymmetricPower.UFin n) M) ≤
        AddCon.ker tensorLift.toAddMonoidHom := by
    intro x y h
    induction h with
    | of _ _ hrel =>
        cases hrel with
        | perm e m =>
            change tensorLift (PiTensorProduct.tprod R (fun i ↦ m i)) =
              tensorLift (PiTensorProduct.tprod R (fun i ↦ m (e i)))
            simp only [tensorLift, PiTensorProduct.lift.tprod]
            exact (SymmetricPower.tprod_equiv e (f ∘ m)).symm
    | refl => rfl
    | symm hxy ih => exact ih.symm
    | trans hxy hyz ihxy ihyz => exact ihxy.trans ihyz
    | add hxy hyz ihxy ihyz => simpa using congrArg₂ (· + ·) ihxy ihyz
  let g : Sym[R] (SymmetricPower.UFin n) M →+ Sym[S] (SymmetricPower.UFin n) N :=
    AddCon.lift _ tensorLift.toAddMonoidHom hrel
  -- Proof comment: descend the tensor-level map across the symmetric quotient and then check
  -- `R`-linearity on representatives.
  exact
    { toFun := g
      map_add' := g.map_add
      map_smul' := by
        intro r q
        refine AddCon.induction_on q ?_
        intro x
        change tensorLift (r • x) = r • tensorLift x
        simp [tensorLift] }

/-- Helper for Lemma 17.21.4: a section over `U` determines a semilinear germ in the stalk
module at `x`. -/
private def stalkGermLinear
    (ℱ : ModX) (x : X) (U : Opens X) (hx : x ∈ U) :
    ℱ.val.obj (op U) →ₛₗ[(X.presheaf.germ U x hx).hom] ↑(stalkModuleCat ℱ x) where
  toFun s := TopCat.Presheaf.germ ℱ.val.presheaf U x hx s
  map_add' := by
    intro s t
    -- Proof comment: the stalk germ map is additive on sections.
    simpa using (TopCat.Presheaf.germ ℱ.val.presheaf U x hx).hom.map_add s t
  map_smul' := by
    intro r s
    -- Proof comment: `PresheafOfModules.germ_smul` identifies the germ of a scalar multiple with
    -- the scalar multiple of the germ.
    simpa using PresheafOfModules.germ_smul ℱ.val x U hx r s

/-- Helper for Lemma 17.21.4: the ordinary stalk map induced by a morphism of module presheaves. -/
private noncomputable def presheafStalkMap
    {P Q : PresheafOfModules X.ringCatSheaf.obj} (x : X) (φ : P ⟶ Q) :
    TopCat.Presheaf.stalk P.presheaf x ⟶ TopCat.Presheaf.stalk Q.presheaf x :=
  (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
    ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map φ)

/-- Helper for Lemma 17.21.4: the sheafification unit is bijective on stalks of module
presheaves. -/
private theorem sheafificationUnitStalkMap_bijective
    (P : PresheafOfModules X.ringCatSheaf.obj) (x : X) :
    Function.Bijective
      (presheafStalkMap (X := X) x
        ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app P)) := by
  let η := ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app P)
  have hη :
      (PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map η =
        CategoryTheory.toSheafify (Opens.grothendieckTopology X) P.presheaf := by
    -- Proof comment: forgetting the module structure turns the module sheafification unit into
    -- the additive sheafification unit.
    simpa [η] using
      PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app
        (𝟙 X.ringCatSheaf.obj) P
  have hη_iso :
      IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
        ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map η)) := by
    -- Proof comment: stalks do not change under additive sheafification.
    rw [hη]
    simpa using
      TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat P.presheaf
  let fη :
      TopCat.Presheaf.stalk P.presheaf x ⟶
        TopCat.Presheaf.stalk
          (((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj P).val.presheaf) x :=
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
      ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map η)
  have hη_iso' : IsIso fη := by
    simpa [fη] using hη_iso
  have hη_bijective : Function.Bijective fη :=
    (CategoryTheory.isIso_iff_bijective fη).1 hη_iso'
  simpa [presheafStalkMap, η, fη] using hη_bijective

/-- Helper for Lemma 17.21.4: the stalk of a sheafified module presheaf agrees with the stalk of
the underlying presheaf as a type-level equivalence. -/
private noncomputable def presheafSheafificationStalkEquiv
    (P : PresheafOfModules X.ringCatSheaf.obj) (x : X) :
    ↑(stalkModuleCat ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj P) x) ≃
      ↑(TopCat.Presheaf.stalk P.presheaf x) :=
  Equiv.ofBijective
    (presheafStalkMap (X := X) x
      ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app P))
    (sheafificationUnitStalkMap_bijective (X := X) P x)

/-- Helper for Lemma 17.21.4: a morphism of `\mathcal O_X`-modules is mono once all of its stalk
maps are injective. -/
private theorem monoOfStalkwiseInjective
    {ℱ 𝒢 : ModX} (φ : ℱ ⟶ 𝒢)
    (hφ : ∀ x : X, Function.Injective (RingedSpace.moduleStalkMap x φ)) :
    Mono φ := by
  let toAbelianSheaf : ModX ⥤ TopCat.Sheaf AddCommGrpCat X :=
    SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X)
  have hmonoUnderlying : Mono (toAbelianSheaf.map φ) := by
    refine (TopCat.Presheaf.mono_iff_stalk_mono (toAbelianSheaf.map φ)).2 ?_
    intro x
    -- Proof comment: the module-valued stalk map is the same underlying additive map after
    -- forgetting scalars.
    exact (AddCommGrpCat.mono_iff_injective _).2 <| by
      simpa [RingedSpace.moduleStalkMap, toAbelianSheaf] using hφ x
  let _ : Mono (toAbelianSheaf.map φ) := hmonoUnderlying
  refine ⟨?_⟩
  intro Z g h hcomp
  -- Proof comment: cancel the mono after forgetting to additive sheaves and then reflect the
  -- equality of morphisms back to module sheaves.
  have hmapEq : toAbelianSheaf.map g = toAbelianSheaf.map h :=
    (cancel_mono (toAbelianSheaf.map φ)).1 <| by
      simpa using congrArg (fun k ↦ toAbelianSheaf.map k) hcomp
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  ext s
  simpa [toAbelianSheaf, PresheafOfModules.toPresheaf] using
    congrArg (fun k ↦ (k.hom.app U) s) hmapEq

/-- Helper for Lemma 17.21.4: an additive-sheaf morphism is epic exactly when all induced stalk
maps are surjective. -/
private theorem addCommGrpSheafEpiIffStalkSurjective
    {A B : TopCat.Sheaf AddCommGrpCat X} (φ : A ⟶ B) :
    Epi φ ↔
      ∀ x : X,
        Function.Surjective (((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map φ.hom).hom) := by
  -- Proof comment: for sheaves of abelian groups, epimorphy is the same as local surjectivity,
  -- and that local condition is detected on stalks.
  rw [← TopCat.Sheaf.isLocallySurjective_iff_epi φ]
  simpa using TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks φ.hom

/-- Helper for Lemma 17.21.4: if every stalk map has full range, then the sheaf morphism is
epic. -/
private theorem moduleMapEpiOfStalkRangeEqTop
    {𝒢 ℱ : ModX} (φ : 𝒢 ⟶ ℱ) :
    (∀ x : X, (RingedSpace.moduleStalkHom x φ).hom.range = ⊤) → Epi φ := by
  intro hφ
  have htoSheaf :
      Epi ((SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X)).map φ) := by
    -- Proof comment: `range = ⊤` is exactly surjectivity of the corresponding additive stalk
    -- map after forgetting scalars.
    refine (addCommGrpSheafEpiIffStalkSurjective (X := X)
      ((SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X)).map φ)).2 ?_
    intro x
    have hsurj :
        Function.Surjective ((RingedSpace.moduleStalkHom x φ).hom) := by
      rw [← LinearMap.range_eq_top]
      exact hφ x
    simpa [RingedSpace.moduleStalkHom, RingedSpace.moduleStalkMap] using hsurj
  let toAbelianSheaf : ModX ⥤ TopCat.Sheaf AddCommGrpCat X :=
    SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X)
  let _ : Epi (toAbelianSheaf.map φ) := htoSheaf
  refine ⟨?_⟩
  intro Z g h hcomp
  -- Proof comment: cancel the epimorphism after forgetting to additive sheaves and reflect the
  -- resulting equality of morphisms back to `\mathcal O_X`-modules.
  have hmapComp : toAbelianSheaf.map φ ≫ toAbelianSheaf.map g =
      toAbelianSheaf.map φ ≫ toAbelianSheaf.map h := by
    simpa using congrArg (fun f ↦ toAbelianSheaf.map f) hcomp
  have hmapEq : toAbelianSheaf.map g = toAbelianSheaf.map h :=
    (cancel_epi (toAbelianSheaf.map φ)).1 hmapComp
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  ext s
  simpa [toAbelianSheaf, PresheafOfModules.toPresheaf] using
    congrArg (fun k ↦ (k.hom.app U) s) hmapEq

/-- Helper for Lemma 17.21.4: stalkwise short exactness upgrades to short exactness for sheaves of
`\mathcal O_X`-modules. -/
private theorem shortExactOfStalkwiseShortExact
    (T : ShortComplex ModX)
    (hT : ∀ x : X, (RingedSpace.stalkShortComplex T x).ShortExact) :
    T.ShortExact := by
  refine
    { mono_f := monoOfStalkwiseInjective (X := X) T.f ?_
      exact :=
        (RingedSpace.ringedSpaceModule_exact_iff_stalkwise_exact T).2
          (fun x ↦ (hT x).exact)
      epi_g :=
        moduleMapEpiOfStalkRangeEqTop (X := X) (φ := T.g) ?_ }
  · intro x
    -- Proof comment: the first map in the stalk short complex is exactly the stalk map of `T.f`.
    simpa [RingedSpace.moduleStalkMap, RingedSpace.stalkShortComplex] using
      (hT x).moduleCat_injective_f
  · intro x
    -- Proof comment: surjectivity of the second stalk map is equivalent to its range being `⊤`.
    rw [← LinearMap.range_eq_top]
    simpa [RingedSpace.stalkShortComplex] using
      (LinearMap.range_eq_top.2 (hT x).moduleCat_surjective_g)

/-- Helper for Lemma 17.21.4: a short exact sequence of `\mathcal O_X`-modules induces a short
exact sequence on each stalk module. -/
private theorem stalkModuleShortExact
    (hS : S.ShortExact) (x : X) :
    (RingedSpace.stalkShortComplex S x).ShortExact := by
  let toAbelianSheaf := SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X)
  letI : toAbelianSheaf.PreservesZeroMorphisms := by
    change (SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X)).PreservesZeroMorphisms
    exact { map_zero _ _ := by rfl }
  -- Proof comment: exactness is detected stalkwise, while mono/epi are tested on the underlying
  -- additive stalk maps.
  refine ModuleCat.shortComplex_shortExact (RingedSpace.stalkShortComplex S x)
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
      ((RingedSpace.ringedSpaceModule_exact_iff_stalkwise_exact S).1 hS.exact x))
    ?_ ?_
  · have hmono :
        Mono ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
          (toAbelianSheaf.map S.f).hom) := by
      letI : Mono S.f := hS.mono_f
      exact (TopCat.Presheaf.mono_iff_stalk_mono (toAbelianSheaf.map S.f)).1
        (Functor.map_mono toAbelianSheaf S.f) x
    -- Proof comment: the stalk map of `S.f` is the same additive map after forgetting scalars.
    simpa [RingedSpace.moduleStalkMap] using (AddCommGrpCat.mono_iff_injective _).1 hmono
  · have hsurj :
        Function.Surjective
          (((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
            (toAbelianSheaf.map S.g).hom).hom) := by
      letI : Epi S.g := hS.epi_g
      have hloc :
          TopCat.Presheaf.IsLocallySurjective (toAbelianSheaf.map S.g).hom := by
        exact (TopCat.Sheaf.isLocallySurjective_iff_epi (toAbelianSheaf.map S.g)).2
          (Functor.map_epi toAbelianSheaf S.g)
      exact (TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks
        (toAbelianSheaf.map S.g).hom).1 hloc x
    -- Proof comment: surjectivity of the additive stalk map is exactly surjectivity of the
    -- packaged module stalk map.
    simpa [RingedSpace.moduleStalkMap] using hsurj

/-- Helper for Lemma 17.21.4: after passing to a fixed stalk, Lemma `10.13.2` gives the
module-theoretic symmetric-power exact sequence. -/
private theorem symmetricPowerExactOnStalkModules
    (hS : S.ShortExact) (n : ℕ) (x : X) :
    Function.Exact
        (SymmetricPower.leftTensorMap n (RingedSpace.moduleStalkHom x S.f).hom)
        (SymmetricPower.map (n + 1) (RingedSpace.moduleStalkHom x S.g).hom) ∧
      Function.Surjective
        (SymmetricPower.map (n + 1) (RingedSpace.moduleStalkHom x S.g).hom) := by
  -- Proof comment: the powered stalk sequence is exactly the module-valued sequence from Lemma
  -- `10.13.2`, applied to the stalk short complex.
  simpa using symmetric_power_exact_of_exact
    (S := RingedSpace.stalkShortComplex S x)
    (hS := stalkModuleShortExact (X := X) (S := S) hS x) n

/-- Helper for Lemma 17.21.4: after passing to a fixed stalk, Lemma `10.13.2` gives the
module-theoretic exterior-power exact sequence. -/
private theorem exteriorPowerExactOnStalkModules
    (hS : S.ShortExact) (n : ℕ) (x : X) :
    Function.Exact
        (exteriorPower.leftTensorMap n (RingedSpace.moduleStalkHom x S.f).hom)
        (exteriorPower.map (n + 1) (RingedSpace.moduleStalkHom x S.g).hom) ∧
      Function.Surjective
        (exteriorPower.map (n + 1) (RingedSpace.moduleStalkHom x S.g).hom) := by
  -- Proof comment: this is the exterior analogue of the previous stalkwise module computation.
  simpa using exterior_power_exact_of_exact
    (S := RingedSpace.stalkShortComplex S x)
    (hS := stalkModuleShortExact (X := X) (S := S) hS x) n

-- Proof sketch: after passing to the stalk at each point, the sequence identifies with the
-- module-theoretic symmetric-power exact sequence from Lemma `10.13.2`; exactness of sheaves of
-- modules is detected stalkwise via `stalkShortComplex`.
/-- Lemma 17.21.4 (1), stated in degree `n + 1`: for a short exact sequence
`0 ⟶ S.X₁ ⟶ S.X₂ ⟶ S.X₃ ⟶ 0` of `\mathcal O_X`-modules, the canonical sequence
`S.X₁ ⊗ Symm[n] S.X₂ ⟶ Symm[n + 1] S.X₂ ⟶ Symm[n + 1] S.X₃ ⟶ 0`
is short exact in `X.Modules`. -/
@[stacks 01CJ]
theorem symmetricPowerSequence
    (hS : S.ShortExact) (n : ℕ) :
    (ShortComplex.symmetricPowerSequence S n).ShortExact := by
  -- Route correction: the global sheaf packaging is no longer the blocker. The only remaining
  -- task is to identify each stalk of the symmetric-power sequence with the module-theoretic
  -- powered stalk sequence from Lemma `10.13.2`.
  refine shortExactOfStalkwiseShortExact (X := X) (T := ShortComplex.symmetricPowerSequence S n) ?_
  intro x
  -- TODO: the sheafification-unit reduction is now packaged by
  -- `presheafSheafificationStalkEquiv`; the remaining target-local blocker is the bijective
  -- comparison from the ordinary stalk of `symmetricPowerPresheaf _ _` to
  -- `Sym[X.presheaf.stalk x] (SymmetricPower.UFin _) (stalkModuleCat _ x)`, together with its
  -- compatibility with `tensorProductStalkIso` and the two powered differentials.
  sorry

-- Proof sketch: the same stalkwise reduction identifies the exterior-power sequence with the
-- module-theoretic exact sequence from Lemma `10.13.2`.
/-- Lemma 17.21.4 (2), stated in degree `n + 1`: for a short exact sequence
`0 ⟶ S.X₁ ⟶ S.X₂ ⟶ S.X₃ ⟶ 0` of `\mathcal O_X`-modules, the canonical sequence
`S.X₁ ⊗ Λ^[n] S.X₂ ⟶ Λ^[n + 1] S.X₂ ⟶ Λ^[n + 1] S.X₃ ⟶ 0`
is short exact in `X.Modules`. -/
@[stacks 01CJ]
theorem exteriorPowerSequence
    (hS : S.ShortExact) (n : ℕ) :
    (ShortComplex.exteriorPowerSequence S n).ShortExact := by
  -- Route correction: as in the symmetric case, the sheaf-level exactness packaging is settled;
  -- the unresolved step is the stalkwise comparison with the module-theoretic exterior-power
  -- sequence.
  refine shortExactOfStalkwiseShortExact (X := X) (T := ShortComplex.exteriorPowerSequence S n) ?_
  intro x
  -- TODO: after the already-added sheafification-unit stalk equivalence, the remaining blocker is
  -- the bijective comparison from the ordinary stalk of `exteriorPowerPresheaf _ _` to
  -- `⋀[X.presheaf.stalk x]^_ (stalkModuleCat _ x)`, plus the corresponding compatibility with
  -- `tensorProductStalkIso` and the powered sequence maps on generators.
  sorry

end

end CategoryTheory.ShortComplex.ShortExact
