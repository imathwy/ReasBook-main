import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w w₁ w₂ w₃ w₄

section

namespace LinearMap

variable {R : Type u} [Semiring R]
variable {P : Type v} {M : Type w} [AddCommMonoid P] [Module R P]
variable [AddCommMonoid M] [Module R M]

/-- An essential epimorphism of modules is a linear map whose only submodule mapping onto the whole
target is the whole source. -/
class IsEssential (f : P →ₗ[R] M) : Prop where
  eq_top_of_map_eq_top (N : Submodule R P) (hN : N.map f = ⊤) : N = ⊤

/-- A projective envelope is a surjective essential homomorphism with projective source. -/
class IsProjectiveEnvelope (f : P →ₗ[R] M) : Prop extends Module.Projective R P, f.IsEssential
    where
  surjective : Function.Surjective f

end LinearMap

section GroupAlgebraProjectiveEnvelope

variable {k : Type u} [Field k]
variable {G : Type u} [Group G] [Finite G]

open Module

local notation "kG" => MonoidAlgebra k G

/-- Helper for Proposition 14-14.3-1: a nontrivial `k[G]`-module forces `k[G]` to be small in the
module universe, which lets the explicit free cover live in that same universe. -/
private theorem small_groupAlgebra_of_nontrivial_module
    (M : Type w) [AddCommGroup M] [Module kG M] [Nontrivial M] : Small.{w} kG := by
  classical
  let _ : Module k M := Module.compHom M (algebraMap k kG)
  let m : M := Classical.choose (exists_ne (0 : M))
  have hm : m ≠ 0 := Classical.choose_spec (exists_ne (0 : M))
  have _ : Small.{w} k := small_of_injective (smul_left_injective k hm)
  let e : kG ≃ (G → k) := Finsupp.equivFunOnFinite
  exact small_map e

/-- Helper for Proposition 14-14.3-1: every `k[G]`-module admits a projective presentation whose
underlying linear map is surjective. In the nontrivial case we use the explicit free cover
`M →₀ Shrink k[G]`, so the source already lives in the target universe. -/
private theorem exists_projective_presentation_surjective
    (M : ModuleCat.{w} kG) :
    ∃ (F : ModuleCat.{w} kG) (π : F ⟶ M),
      Module.Projective kG F ∧ Function.Surjective π.hom := by
  classical
  by_cases hM : Subsingleton M
  · let Z := ULift.{w} PUnit
    -- In the trivial case, the zero module already gives a surjective projective presentation.
    refine ⟨ModuleCat.of kG Z, ModuleCat.ofHom (0 : Z →ₗ[kG] M), ?_, ?_⟩
    · infer_instance
    · intro y
      refine ⟨0, ?_⟩
      exact hM.elim _ _
  · let _ : Nontrivial M := not_subsingleton_iff_nontrivial.mp hM
    have _ : Small.{w} kG := small_groupAlgebra_of_nontrivial_module (k := k) (G := G) M
    let e : Basis M kG (M →₀ Shrink.{w} kG) :=
      ⟨Finsupp.mapRange.linearEquiv (Shrink.linearEquiv kG kG)⟩
    -- Use the same-universe free cover from `ModuleCat.enoughProjectives` directly.
    refine ⟨ModuleCat.of kG (M →₀ Shrink.{w} kG), ModuleCat.ofHom (e.constr ℕ _root_.id), ?_, ?_⟩
    · exact Module.Projective.of_basis e
    · intro m
      -- The basis vector at `m` maps to `m`, so the cover is surjective.
      refine ⟨Finsupp.single m 1, ?_⟩
      have hsingle :
          ((let e' : Basis M kG (M →₀ Shrink.{w} kG) :=
              ⟨Finsupp.mapRange.linearEquiv (Shrink.linearEquiv kG kG)⟩
            ; e'.constr ℕ _root_.id) (Finsupp.single m 1)) = m := by
        simp [Basis.constr_apply]
      simpa [e] using hsingle

/-- Helper for Proposition 14-14.3-1: a surjective linear map remains surjective after reducing
both source and target modulo `I • ⊤`. -/
private theorem jacobson_quotient_surjective_of_surjective
    {R : Type u} [Ring R] {P : Type v} [AddCommGroup P] [Module R P]
    {M : Type w} [AddCommGroup M] [Module R M] (I : Ideal R) {f : P →ₗ[R] M}
    (hf : Function.Surjective f) :
    Function.Surjective
      (Submodule.mapQ (I • (⊤ : Submodule R P)) (I • (⊤ : Submodule R M)) f
        (Submodule.smul_top_le_comap_smul_top I f)) := by
  intro y
  -- Lift a quotient class to the target, then lift that representative through `f`.
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (I • (⊤ : Submodule R M)) y
  obtain ⟨p, rfl⟩ := hf x
  exact ⟨Submodule.Quotient.mk p, rfl⟩

/-- Helper for Proposition 14-14.3-1: the quotient map induced by a linear map is compatible with
the quotient-ring scalar action. -/
private theorem quotient_map_linear_map_smul
    {R : Type u} [Ring R] (I : Ideal R) [I.IsTwoSided] {P : Type v} [AddCommGroup P] [Module R P]
    {M : Type w} [AddCommGroup M] [Module R M] (f : P →ₗ[R] M) (a : R ⧸ I)
    (x : P ⧸ (I • (⊤ : Submodule R P))) :
    (Submodule.mapQ (I • (⊤ : Submodule R P)) (I • (⊤ : Submodule R M)) f
      (Submodule.smul_top_le_comap_smul_top I f)) (a • x) =
      a • (Submodule.mapQ (I • (⊤ : Submodule R P)) (I • (⊤ : Submodule R M)) f
        (Submodule.smul_top_le_comap_smul_top I f)) x := by
  -- Unwrap both the quotient scalar and the quotient class to reduce to the ordinary `R`-linearity
  -- of `Submodule.mapQ`.
  rcases Ideal.Quotient.mk_surjective a with ⟨r, rfl⟩
  rcases Submodule.mkQ_surjective (I • (⊤ : Submodule R P)) x with ⟨p, rfl⟩
  simp

/-- Helper for Proposition 14-14.3-1: package reduction modulo `I • ⊤` as an
`R ⧸ I`-linear map. -/
private noncomputable def quotient_map_linear
    {R : Type u} [Ring R] (I : Ideal R) [I.IsTwoSided] {P : Type v} [AddCommGroup P] [Module R P]
    {M : Type w} [AddCommGroup M] [Module R M] (f : P →ₗ[R] M) :
    P ⧸ (I • (⊤ : Submodule R P)) →ₗ[R ⧸ I] M ⧸ (I • (⊤ : Submodule R M)) :=
  { toFun := fun x =>
      (Submodule.mapQ (I • (⊤ : Submodule R P)) (I • (⊤ : Submodule R M)) f
        (Submodule.smul_top_le_comap_smul_top I f)) x
    map_add' := by
      intro x y
      simp
    map_smul' := by
      intro a x
      exact quotient_map_linear_map_smul I f a x }

/-- Helper for Proposition 14-14.3-1: the quotient-ring-linear reduction map is surjective
whenever the original linear map is surjective. -/
private theorem quotient_map_linear_surjective_of_surjective
    {R : Type u} [Ring R] (I : Ideal R) [I.IsTwoSided] {P : Type v} [AddCommGroup P] [Module R P]
    {M : Type w} [AddCommGroup M] [Module R M] {f : P →ₗ[R] M}
    (hf : Function.Surjective f) :
    Function.Surjective (quotient_map_linear I f) := by
  -- The quotient-ring-linear map has the same underlying function as the already proved `mapQ`.
  intro y
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (I • (⊤ : Submodule R M)) y
  obtain ⟨p, rfl⟩ := hf x
  exact ⟨Submodule.Quotient.mk p, rfl⟩

/-- Helper for Proposition 14-14.3-1: reduction modulo `Ring.jacobson k[G] • ⊤` packages into a
ring hom on endomorphism rings. -/
private noncomputable def jacobson_quotient_end_ringHom
    {F : Type w} [AddCommGroup F] [Module kG F] :
    Module.End kG F →+* Module.End kG (F ⧸ (Ring.jacobson kG • (⊤ : Submodule kG F))) := by
  let J : Ideal kG := Ring.jacobson kG
  let JF : Submodule kG F := J • (⊤ : Submodule kG F)
  refine
    { toFun := fun u =>
        Submodule.mapQ JF JF u (Submodule.smul_top_le_comap_smul_top J u)
      map_zero' := by
        -- Reduction sends the zero endomorphism to zero on the quotient.
        simpa [J, JF] using
          (Submodule.mapQ_zero
            (p := JF) (q := JF)
            (h := Submodule.smul_top_le_comap_smul_top J (0 : Module.End kG F)))
      map_one' := by
        -- Reduction preserves the identity endomorphism.
        simpa [J, JF, Module.End.one_eq_id] using
          (Submodule.mapQ_id
            (p := JF)
            (h := by
              simpa [J, JF] using
                (show JF ≤ Submodule.comap (LinearMap.id : F →ₗ[kG] F) JF by
                  simpa)))
      map_add' := by
        intro u v
        -- The quotient map is defined pointwise, so addition is preserved pointwise as well.
        ext x
        rfl
      map_mul' := by
        intro u v
        -- Composition descends compatibly to the quotient endomorphism ring.
        simpa [J, JF, Module.End.mul_eq_comp] using
          (Submodule.mapQ_comp (p := JF) (p₂ := JF) (p₃ := JF) v u
            (Submodule.smul_top_le_comap_smul_top J v)
            (Submodule.smul_top_le_comap_smul_top J u)) }

/-- Helper for Proposition 14-14.3-1: projective modules lift endomorphisms from their Jacobson
quotients. -/
private theorem jacobson_quotient_end_surjective_of_projective
    {F : Type w} [AddCommGroup F] [Module kG F] [Module.Projective kG F] :
    Function.Surjective
      (fun u : Module.End kG F =>
        Submodule.mapQ (Ring.jacobson kG • (⊤ : Submodule kG F))
          (Ring.jacobson kG • (⊤ : Submodule kG F)) u
          (Submodule.smul_top_le_comap_smul_top (Ring.jacobson kG) u)) := by
  intro uBar
  let JF : Submodule kG F := Ring.jacobson kG • (⊤ : Submodule kG F)
  let q : F →ₗ[kG] F ⧸ JF := JF.mkQ
  have hqsurj : Function.Surjective q := JF.mkQ_surjective
  obtain ⟨u, hu⟩ := Module.projective_lifting_property q (uBar.comp q) hqsurj
  refine ⟨u, ?_⟩
  -- The lift is determined after composing with the quotient map, and `q` is surjective.
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := hqsurj x
  have hcomp :
      (Submodule.mapQ JF JF u (Submodule.smul_top_le_comap_smul_top (Ring.jacobson kG) u)).comp q =
        uBar.comp q := by
    -- This is exactly the compatibility relation defining `Submodule.mapQ`.
    rw [Submodule.mapQ_mkQ, hu]
  simpa [q, JF] using
    congrArg (fun f : F →ₗ[kG] F ⧸ JF => f y) hcomp

/-- Helper for Proposition 14-14.3-1: an endomorphism acting trivially on the Jacobson quotient is
nilpotent because each iterate gains one Jacobson-radical factor. -/
private theorem jacobson_quotient_end_mapQ_ker_isNilpotent
    {F : Type w} [AddCommGroup F] [Module kG F] (u : Module.End kG F)
    (hu :
      Submodule.mapQ (Ring.jacobson kG • (⊤ : Submodule kG F))
          (Ring.jacobson kG • (⊤ : Submodule kG F)) u
          (Submodule.smul_top_le_comap_smul_top (Ring.jacobson kG) u) = 0) :
    IsNilpotent u := by
  let _ : Module.Finite k kG := MonoidAlgebra.moduleFinite
  let _ : IsArtinianRing kG := IsArtinianRing.of_finite k kG
  let _ : IsSemiprimaryRing kG := inferInstance
  let J : Ideal kG := Ring.jacobson kG
  let JF : Submodule kG F := J • (⊤ : Submodule kG F)
  have hu_mem : ∀ x : F, u x ∈ JF := by
    intro x
    -- Evaluate the vanishing quotient endomorphism on the class of `x`.
    have hx :=
      congrArg (fun f : Module.End kG (F ⧸ JF) => f (Submodule.Quotient.mk x)) hu
    exact (Submodule.Quotient.mk_eq_zero JF).1 (by simpa using hx)
  have hu_map_pow :
      ∀ n : ℕ, Submodule.map u (J ^ n • (⊤ : Submodule kG F)) ≤ J ^ (n + 1) • (⊤ : Submodule kG F) :=
      by
    intro n
    -- One more application of `u` contributes one more Jacobson factor.
    calc
      Submodule.map u (J ^ n • (⊤ : Submodule kG F)) =
          J ^ n • Submodule.map u (⊤ : Submodule kG F) := by
            simpa using (Submodule.map_smul'' (J ^ n) (⊤ : Submodule kG F) u)
      _ ≤ J ^ n • JF := by
            gcongr
            intro y hy
            rcases (Submodule.mem_map).1 hy with ⟨x, -, rfl⟩
            exact hu_mem x
      _ = J ^ (n + 1) • (⊤ : Submodule kG F) := by
            change J ^ n • (J • (⊤ : Submodule kG F)) = J ^ (n + 1) • (⊤ : Submodule kG F)
            rw [← Submodule.mul_smul]
            exact congrArg (fun I : Ideal kG => I • (⊤ : Submodule kG F)) (J.pow_succ (n := n)).symm
  have hu_pow_mem : ∀ n : ℕ, ∀ x : F, (u ^ n) x ∈ J ^ n • (⊤ : Submodule kG F) := by
    intro n
    induction n with
    | zero =>
        intro x
        simpa [J.pow_zero] using (Submodule.mem_top (x := x) : x ∈ (⊤ : Submodule kG F))
    | succ n ih =>
        intro x
        have hx : (u ^ n) x ∈ J ^ n • (⊤ : Submodule kG F) := ih x
        have hx_map : u ((u ^ n) x) ∈ Submodule.map u (J ^ n • (⊤ : Submodule kG F)) := by
          exact (Submodule.mem_map).2 ⟨(u ^ n) x, hx, rfl⟩
        simpa [pow_succ', Module.End.mul_eq_comp] using hu_map_pow n hx_map
  rcases (IsSemiprimaryRing.isNilpotent (R := kG) : IsNilpotent J) with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  -- Once the Jacobson power vanishes, the corresponding iterate of `u` is zero.
  ext x
  have hx : (u ^ n) x ∈ J ^ n • (⊤ : Submodule kG F) := hu_pow_mem n x
  rw [hn] at hx
  simpa using hx

/-- Helper for Proposition 14-14.3-1: kernel elements of the quotient-endomorphism ring hom are
nilpotent. -/
private theorem jacobson_quotient_end_ringHom_ker_isNilpotent
    {F : Type w} [AddCommGroup F] [Module kG F] (u : Module.End kG F)
    (hu : jacobson_quotient_end_ringHom (k := k) (G := G) u = 0) :
    IsNilpotent u := by
  -- The ring-hom packaging has the same underlying quotient action as the original `mapQ`.
  simpa [jacobson_quotient_end_ringHom] using
    jacobson_quotient_end_mapQ_ker_isNilpotent (k := k) (G := G) u hu

/-- Helper for Proposition 14-14.3-1: the range of an idempotent endomorphism of a projective
module is projective. -/
private theorem lifted_projector_range_projective
    {F : Type w} [AddCommGroup F] [Module kG F] [Module.Projective kG F]
    (e : Module.End kG F) (he : IsIdempotentElem e) :
    Module.Projective kG (LinearMap.range e) := by
  -- The idempotent endomorphism is a projection onto its range, so the range is a split summand.
  have hsplit : e.rangeRestrict.comp (LinearMap.range e).subtype = LinearMap.id := by
    ext x
    obtain ⟨y, hy⟩ := x.property
    calc
      ↑((e.rangeRestrict.comp (LinearMap.range e).subtype) x) = e (e y) := by
        simpa [LinearMap.comp_apply, hy]
      _ = e y := by
        simpa [Module.End.mul_apply] using congrArg (fun f : Module.End kG F => f y) he
      _ = ↑x := hy
  exact Module.Projective.of_split (LinearMap.range e).subtype e.rangeRestrict hsplit

/-- Helper for Proposition 14-14.3-1: bundle the range of an endomorphism as a `k[G]`-module
object. -/
private noncomputable abbrev lifted_projector_range_module
    {F : Type w} [AddCommGroup F] [Module kG F] (e : Module.End kG F) :
    ModuleCat.{w} kG :=
  ModuleCat.of kG (LinearMap.range e)

/-- Helper for Proposition 14-14.3-1: the canonical map from the range of an endomorphism into a
target module induced by a linear map on the ambient module. -/
private noncomputable abbrev lifted_projector_range_hom
    {F : Type w} [AddCommGroup F] [Module kG F]
    (e : Module.End kG F) {M : ModuleCat.{w} kG} (π : F →ₗ[kG] M) :
    lifted_projector_range_module (k := k) (G := G) e ⟶ M :=
  ModuleCat.ofHom (π.comp (LinearMap.range e).subtype)

/-- Helper for Proposition 14-14.3-1: every element of the range of an idempotent projector is
fixed by that projector. -/
private theorem lifted_projector_range_fixed
    {F : Type w} [AddCommGroup F] [Module kG F] (e : Module.End kG F)
    (he : IsIdempotentElem e) (x : LinearMap.range e) :
    e ((LinearMap.range e).subtype x) = (LinearMap.range e).subtype x := by
  -- Unpack the range witness and apply idempotence once.
  obtain ⟨y, hy⟩ := x.property
  calc
    e ((LinearMap.range e).subtype x) = e (e y) := by
      simpa using (congrArg e hy).symm
    _ = e y := by
      simpa [Module.End.mul_apply] using congrArg (fun u : Module.End kG F => u y) he
    _ = (LinearMap.range e).subtype x := hy

/-- Helper for Proposition 14-14.3-1: a kernel element of the lifted map has zero class in the
Jacobson quotient of the ambient projective module. -/
private theorem lifted_projector_range_mkQ_eq_zero_of_mem_ker
    {F : Type w₁} [AddCommGroup F] [Module kG F]
    {M : Type w₂} [AddCommGroup M] [Module kG M]
    (J : Ideal kG) [J.IsTwoSided] (e : Module.End kG F) (π : F →ₗ[kG] M)
    (sBar : M ⧸ (J • (⊤ : Submodule kG M)) →ₗ[kG ⧸ J] F ⧸ (J • (⊤ : Submodule kG F)))
    (πBar : F ⧸ (J • (⊤ : Submodule kG F)) →ₗ[kG ⧸ J] M ⧸ (J • (⊤ : Submodule kG M)))
    (eBarR : Module.End kG (F ⧸ (J • (⊤ : Submodule kG F))))
    (he_idem : IsIdempotentElem e)
    (he_map :
      Submodule.mapQ (J • (⊤ : Submodule kG F)) (J • (⊤ : Submodule kG F)) e
        (Submodule.smul_top_le_comap_smul_top J e) = eBarR)
    (hπBar_mk : ∀ y : F,
      πBar (Submodule.Quotient.mk y) =
        (Submodule.Quotient.mk (π y) : M ⧸ (J • (⊤ : Submodule kG M))))
    (heBarR_apply : ∀ z, eBarR z = sBar (πBar z))
    {x : LinearMap.range e}
    (hx : (π.comp (LinearMap.range e).subtype) x = 0) :
    (Submodule.Quotient.mk (((LinearMap.range e).subtype x : F)) :
      F ⧸ (J • (⊤ : Submodule kG F))) = 0 := by
  let z : F ⧸ (J • (⊤ : Submodule kG F)) :=
    Submodule.Quotient.mk (((LinearMap.range e).subtype x : F))
  have hfix_class : eBarR z = z := by
    -- The lifted idempotent fixes the quotient class of any point already in `range e`.
    calc
      eBarR z = (Submodule.mapQ (J • (⊤ : Submodule kG F)) (J • (⊤ : Submodule kG F)) e
          (Submodule.smul_top_le_comap_smul_top J e)) z := by
            simpa using
              congrArg
                (fun u : Module.End kG (F ⧸ (J • (⊤ : Submodule kG F))) => u z)
                he_map.symm
      _ = Submodule.Quotient.mk (e (((LinearMap.range e).subtype x : F))) := by
            rfl
      _ = (Submodule.Quotient.mk (((LinearMap.range e).subtype x : F)) :
            F ⧸ (J • (⊤ : Submodule kG F))) := by
            rw [lifted_projector_range_fixed (k := k) (G := G) e he_idem x]
  have hπ_zero : πBar z = 0 := by
    -- The quotient class is killed because `x` lies in the kernel of `π ∘ subtype`.
    rw [show z = Submodule.Quotient.mk (((LinearMap.range e).subtype x : F)) by rfl]
    rw [hπBar_mk]
    simpa using congrArg (Submodule.Quotient.mk (p := J • (⊤ : Submodule kG M))) hx
  -- The class is both fixed by the lifted projector and mapped to zero, so it must itself vanish.
  calc
    z = eBarR z := by
      symm
      exact hfix_class
    _ = sBar (πBar z) := heBarR_apply z
    _ = 0 := by
      rw [hπ_zero]
      simp

/-- Helper for Proposition 14-14.3-1: Jacobson-radical membership in the ambient module restricts
to Jacobson-radical membership in the lifted range. -/
private theorem lifted_projector_range_mem_jacobson_of_ambient_mem
    {F : Type w} [AddCommGroup F] [Module kG F]
    (J : Ideal kG) (e : Module.End kG F) (he_idem : IsIdempotentElem e)
    {x : LinearMap.range e}
    (hx : (((LinearMap.range e).subtype x : F)) ∈ J • (⊤ : Submodule kG F)) :
    x ∈ J • (⊤ : Submodule kG (LinearMap.range e)) := by
  let i : LinearMap.range e →ₗ[kG] F := (LinearMap.range e).subtype
  let r : F →ₗ[kG] LinearMap.range e := e.rangeRestrict
  have hri : r (i x) = x := by
    exact Subtype.ext (lifted_projector_range_fixed (k := k) (G := G) e he_idem x)
  have hr_surj : Function.Surjective r := by
    -- Every point of the range is hit by its own inclusion into `F`.
    intro y
    exact ⟨i y, Subtype.ext (lifted_projector_range_fixed (k := k) (G := G) e he_idem y)⟩
  have hr_range_top : LinearMap.range r = ⊤ := LinearMap.range_eq_top.2 hr_surj
  have hmap :
      Submodule.map r (J • (⊤ : Submodule kG F)) = J • (⊤ : Submodule kG (LinearMap.range e)) := by
    -- Mapping the ambient Jacobson piece through the retraction yields the Jacobson piece on the
    -- range because `r` is already surjective.
    rw [Submodule.map_smul'', Submodule.map_top, hr_range_top]
  have hx_map : r (i x) ∈ Submodule.map r (J • (⊤ : Submodule kG F)) := by
    exact (Submodule.mem_map).2 ⟨i x, hx, rfl⟩
  simpa [hri, hmap] using hx_map

/-- Helper for Proposition 14-14.3-1: the kernel of the map from the lifted range to `M` lies in
the Jacobson-radical part of that range. -/
private theorem lifted_projector_range_kernel_le_jacobson
    {F : Type w₁} [AddCommGroup F] [Module kG F]
    {M : Type w₂} [AddCommGroup M] [Module kG M]
    (J : Ideal kG) [J.IsTwoSided] (e : Module.End kG F) (π : F →ₗ[kG] M)
    (sBar : M ⧸ (J • (⊤ : Submodule kG M)) →ₗ[kG ⧸ J] F ⧸ (J • (⊤ : Submodule kG F)))
    (πBar : F ⧸ (J • (⊤ : Submodule kG F)) →ₗ[kG ⧸ J] M ⧸ (J • (⊤ : Submodule kG M)))
    (eBarR : Module.End kG (F ⧸ (J • (⊤ : Submodule kG F))))
    (he_idem : IsIdempotentElem e)
    (he_map :
      Submodule.mapQ (J • (⊤ : Submodule kG F)) (J • (⊤ : Submodule kG F)) e
        (Submodule.smul_top_le_comap_smul_top J e) = eBarR)
    (hπBar_mk : ∀ y : F,
      πBar (Submodule.Quotient.mk y) =
        (Submodule.Quotient.mk (π y) : M ⧸ (J • (⊤ : Submodule kG M))))
    (heBarR_apply : ∀ z, eBarR z = sBar (πBar z)) :
    LinearMap.ker (π.comp (LinearMap.range e).subtype) ≤
      J • (⊤ : Submodule kG (LinearMap.range e)) := by
  intro x hx
  have hmk_zero :=
    lifted_projector_range_mkQ_eq_zero_of_mem_ker (k := k) (G := G) J e π sBar πBar eBarR
      he_idem he_map hπBar_mk heBarR_apply hx
  have hi_mem : (((LinearMap.range e).subtype x : F)) ∈ J • (⊤ : Submodule kG F) := by
    simpa using
      (Submodule.Quotient.mk_eq_zero
        (p := J • (⊤ : Submodule kG F))
        (x := (((LinearMap.range e).subtype x : F)))).1 hmk_zero
  exact lifted_projector_range_mem_jacobson_of_ambient_mem (k := k) (G := G) J e he_idem hi_mem

/-- Helper for Proposition 14-14.3-1: once the lifted-range map is known to be surjective,
essential, and projective on its source, it is a projective envelope. -/
private theorem lifted_projector_range_isProjectiveEnvelope
    {F : Type w₁} [AddCommGroup F] [Module kG F]
    {M : ModuleCat.{w₁} kG} (e : Module.End kG F) (π : F →ₗ[kG] M)
    (hproj : Module.Projective kG (LinearMap.range e))
    (hsurj : Function.Surjective (π.comp (LinearMap.range e).subtype))
    (hess : (π.comp (LinearMap.range e).subtype).IsEssential) :
    (lifted_projector_range_hom (k := k) (G := G) e π).hom.IsProjectiveEnvelope := by
  -- The bundled morphism is definitionally the raw map `π ∘ subtype`.
  change (π.comp (LinearMap.range e).subtype).IsProjectiveEnvelope
  letI : Module.Projective kG (LinearMap.range e) := hproj
  letI : (π.comp (LinearMap.range e).subtype).IsEssential := hess
  exact LinearMap.IsProjectiveEnvelope.mk hsurj

/-- Helper for Proposition 14-14.3-1: package the lifted range and its canonical map as a
projective-envelope witness once the raw map data are verified. -/
private theorem exists_lifted_projector_range_isProjectiveEnvelope
    {F : Type w₁} [AddCommGroup F] [Module kG F]
    {M : ModuleCat.{w₁} kG} (e : Module.End kG F) (π : F →ₗ[kG] M)
    (hproj : Module.Projective kG (LinearMap.range e))
    (hsurj : Function.Surjective (π.comp (LinearMap.range e).subtype))
    (hess : (π.comp (LinearMap.range e).subtype).IsEssential) :
    ∃ (P : ModuleCat.{w₁} kG) (f : P ⟶ M), f.hom.IsProjectiveEnvelope := by
  exact ⟨lifted_projector_range_module (k := k) (G := G) e,
    lifted_projector_range_hom (k := k) (G := G) e π,
    lifted_projector_range_isProjectiveEnvelope (k := k) (G := G) e π hproj hsurj hess⟩

/-- Helper for Proposition 14-14.3-1: over `k[G]`, a submodule whose image generates the
Jacobson quotient is already the whole module. -/
private theorem eq_top_of_sup_jacobson_smul_top_eq_top_local
    {X : Type w} [AddCommGroup X] [Module kG X] [IsSemiprimaryRing kG] (N : Submodule kG X)
    (hN : N ⊔ Ring.jacobson kG • (⊤ : Submodule kG X) = ⊤) : N = ⊤ := by
  have hmap : Submodule.map N.mkQ (Ring.jacobson kG • (⊤ : Submodule kG X)) = ⊤ := by
    -- Pass to the quotient by `N` so the generation hypothesis becomes a Jacobson-radical action.
    exact (Submodule.map_mkQ_eq_top N (Ring.jacobson kG • (⊤ : Submodule kG X))).2 hN
  have hJtop : Ring.jacobson kG • (⊤ : Submodule kG (X ⧸ N)) = ⊤ := by
    -- The quotient identifies the image of `J • ⊤` with the Jacobson action on `X ⧸ N`.
    simpa [Submodule.map_smul'', Submodule.map_top] using hmap
  rcases (IsSemiprimaryRing.isNilpotent (R := kG) : IsNilpotent (Ring.jacobson kG)) with ⟨n, hn⟩
  have hpow : ∀ m : ℕ, (Ring.jacobson kG ^ m) • (⊤ : Submodule kG (X ⧸ N)) = ⊤ := by
    intro m
    induction m with
    | zero =>
        -- The unit ideal acts trivially on the whole quotient.
        change ((1 : Ideal kG) • (⊤ : Submodule kG (X ⧸ N))) = ⊤
        simp
    | succ m ih =>
        -- Iterating the Jacobson action preserves the whole quotient.
        calc
          (Ring.jacobson kG ^ (m + 1)) • (⊤ : Submodule kG (X ⧸ N)) =
              Ring.jacobson kG • (Ring.jacobson kG ^ m • (⊤ : Submodule kG (X ⧸ N))) := by
                rw [Ideal.IsTwoSided.pow_succ (I := Ring.jacobson kG), Submodule.mul_smul]
          _ = Ring.jacobson kG • (⊤ : Submodule kG (X ⧸ N)) := by rw [ih]
          _ = ⊤ := hJtop
  have htopbot : (⊤ : Submodule kG (X ⧸ N)) = ⊥ := by
    -- Nilpotence of the Jacobson radical forces the quotient itself to vanish.
    calc
      (⊤ : Submodule kG (X ⧸ N)) = (Ring.jacobson kG ^ n) • (⊤ : Submodule kG (X ⧸ N)) :=
        (hpow n).symm
      _ = (0 : Ideal kG) • (⊤ : Submodule kG (X ⧸ N)) := by rw [hn]
      _ = ⊥ := by simp
  have hsubmod : Subsingleton (Submodule kG (X ⧸ N)) := (subsingleton_iff_top_eq_bot).mp htopbot
  have hsub : Subsingleton (X ⧸ N) := (Submodule.subsingleton_iff kG).1 hsubmod
  exact (Submodule.Quotient.subsingleton_iff).1 hsub

/-- Helper for Proposition 14-14.3-1: over `k[G]`, a surjective map with kernel inside
`Ring.jacobson k[G] • ⊤` is essential. -/
private theorem isEssential_of_ker_le_jacobson_smul_top_local
    [IsSemiprimaryRing kG] {P : Type w₁} [AddCommGroup P] [Module kG P]
    {M : Type w₂} [AddCommGroup M] [Module kG M] {f : P →ₗ[kG] M}
    (hf : Function.Surjective f)
    (hker : LinearMap.ker f ≤ Ring.jacobson kG • (⊤ : Submodule kG P)) : f.IsEssential := by
  refine ⟨fun N hN ↦ ?_⟩
  have hsurjN : Function.Surjective (f.domRestrict N) := by
    -- Surjectivity of the restricted map is exactly the hypothesis that `N` maps onto the target.
    rw [← LinearMap.range_eq_top, LinearMap.range_domRestrict]
    exact hN
  have hsup : N ⊔ LinearMap.ker f = ⊤ := (LinearMap.surjective_domRestrict_iff hf).1 hsurjN
  have hsup' : N ⊔ Ring.jacobson kG • (⊤ : Submodule kG P) = ⊤ := by
    -- Enlarge the kernel bound from `ker f` to the Jacobson-radical piece.
    apply top_unique
    have hle : N ⊔ LinearMap.ker f ≤ N ⊔ Ring.jacobson kG • (⊤ : Submodule kG P) :=
      sup_le_sup_left hker N
    exact hsup ▸ hle
  exact eq_top_of_sup_jacobson_smul_top_eq_top_local (k := k) (G := G) N hsup'

-- Source-faithful public surface: LinearRepresentations_Serre_1977's proposition is about `k[G]`-modules. The broader
-- Artinian-ring formulation is kept for internal helper infrastructure below, but the public
-- existence theorem is recorded only in the group-algebra setting actually used downstream.
/-- Proposition 14-14.3-1 (1): (a) every `k[G]`-module admits a projective envelope. -/
theorem exists_isProjectiveEnvelope (M : ModuleCat.{w} kG) :
    ∃ (P : ModuleCat.{w} kG) (f : P ⟶ M), f.hom.IsProjectiveEnvelope := by
  classical
  let _ : Module.Finite k kG := MonoidAlgebra.moduleFinite
  let _ : IsArtinianRing kG := IsArtinianRing.of_finite k kG
  let _ : IsSemiprimaryRing kG := inferInstance
  obtain ⟨F, π, hFproj, hπsurj⟩ :=
    exists_projective_presentation_surjective (k := k) (G := G) M
  let J : Ideal kG := Ring.jacobson kG
  let JF : Submodule kG F := J • (⊤ : Submodule kG F)
  let JM : Submodule kG M := J • (⊤ : Submodule kG M)
  let πBar : F ⧸ JF →ₗ[kG ⧸ J] M ⧸ JM := quotient_map_linear J π.hom
  have hπBar_surj : Function.Surjective πBar :=
    quotient_map_linear_surjective_of_surjective J hπsurj
  let _ : IsSemisimpleRing (kG ⧸ J) := IsSemiprimaryRing.isSemisimpleRing (R := kG)
  let _ : Module.Projective (kG ⧸ J) (M ⧸ JM) :=
    Module.projective_of_isSemisimpleRing (kG ⧸ J) (M ⧸ JM)
  obtain ⟨sBar, hsBar⟩ :=
    Module.projective_lifting_property πBar
      (LinearMap.id : M ⧸ JM →ₗ[kG ⧸ J] M ⧸ JM) hπBar_surj
  let eBarR : Module.End kG (F ⧸ JF) :=
    (sBar.restrictScalars kG).comp (πBar.restrictScalars kG)
  have hπBar_sBar_apply : ∀ y : M ⧸ JM, πBar (sBar y) = y := by
    intro y
    simpa using congrArg (fun f : M ⧸ JM →ₗ[kG ⧸ J] M ⧸ JM => f y) hsBar
  have heBarR_idem : IsIdempotentElem eBarR := by
    -- The lifted projector on the Jacobson quotient is the usual `section ∘ projection`.
    rw [IsIdempotentElem, Module.End.mul_eq_comp]
    ext z
    simp [eBarR, hπBar_sBar_apply]
  let _ : Module.Projective kG F := hFproj
  have heBarR_mem_range :
      eBarR ∈ (jacobson_quotient_end_ringHom (k := k) (G := G) (F := F)).range := by
    -- Surjectivity on quotient endomorphisms gives a preimage of the quotient projector.
    obtain ⟨u, hu⟩ :=
      jacobson_quotient_end_surjective_of_projective (k := k) (G := G) (F := F) eBarR
    exact ⟨u, by simpa [JF, jacobson_quotient_end_ringHom] using hu⟩
  have hker_nil :
      ∀ u ∈ RingHom.ker (jacobson_quotient_end_ringHom (k := k) (G := G) (F := F)),
        IsNilpotent u := by
    intro u hu
    exact jacobson_quotient_end_ringHom_ker_isNilpotent (k := k) (G := G) (F := F) u hu
  obtain ⟨e, he_idem, he_map⟩ :=
    exists_isIdempotentElem_eq_of_ker_isNilpotent
      (jacobson_quotient_end_ringHom (k := k) (G := G) (F := F))
      hker_nil eBarR heBarR_mem_range heBarR_idem
  have he_mapQ :
      Submodule.mapQ JF JF e (Submodule.smul_top_le_comap_smul_top J e) = eBarR := by
    simpa [JF, jacobson_quotient_end_ringHom] using he_map
  let P0 := LinearMap.range e
  let i : P0 →ₗ[kG] F := (LinearMap.range e).subtype
  let f0 : P0 →ₗ[kG] M := π.hom.comp i
  have hP0proj : Module.Projective kG P0 :=
    lifted_projector_range_projective (k := k) (G := G) e he_idem
  have hπBar_mk : ∀ y : F,
      πBar (Submodule.Quotient.mk y) =
        (Submodule.Quotient.mk (π.hom y) : M ⧸ JM) := by
    intro y
    rfl
  have hf0_surj : Function.Surjective f0 := by
    let N : Submodule kG M := LinearMap.range f0
    have hNmap : Submodule.map JM.mkQ N = ⊤ := by
      -- Every quotient class comes from an element in the lifted idempotent range.
      apply top_le_iff.mp
      intro y hy
      obtain ⟨q, hq⟩ := Submodule.mkQ_surjective JF (sBar y)
      let x0 : P0 := ⟨e q, ⟨q, rfl⟩⟩
      have hclass : (Submodule.Quotient.mk (e q) : F ⧸ JF) = sBar y := by
        calc
          (Submodule.Quotient.mk (e q) : F ⧸ JF) =
              (Submodule.mapQ JF JF e (Submodule.smul_top_le_comap_smul_top J e))
                (Submodule.Quotient.mk q) := by
                  rfl
          _ = eBarR (Submodule.Quotient.mk q) := by
                simpa using
                  congrArg
                    (fun u : Module.End kG (F ⧸ JF) => u (Submodule.Quotient.mk q))
                    he_mapQ
          _ = eBarR (sBar y) := by simpa using congrArg eBarR hq
          _ = sBar (πBar (sBar y)) := by rfl
          _ = sBar y := by rw [hπBar_sBar_apply y]
      have hy0 : JM.mkQ (f0 x0) = y := by
        calc
          JM.mkQ (f0 x0) = πBar (Submodule.Quotient.mk (e q)) := by
            simpa [f0, i, x0] using (hπBar_mk (e q)).symm
          _ = πBar (sBar y) := by rw [hclass]
          _ = y := hπBar_sBar_apply y
      refine (Submodule.mem_map).2 ?_
      exact ⟨f0 x0, ⟨x0, rfl⟩, hy0⟩
    have hNsup : N ⊔ JM = ⊤ := by
      simpa [sup_comm] using (Submodule.map_mkQ_eq_top JM N).mp hNmap
    have hNtop : N = ⊤ :=
      eq_top_of_sup_jacobson_smul_top_eq_top_local (k := k) (G := G) N hNsup
    apply LinearMap.range_eq_top.1
    simpa [N] using hNtop
  have heBarR_apply : ∀ z, eBarR z = sBar (πBar z) := by
    intro z
    rfl
  have hker :
      LinearMap.ker f0 ≤ J • (⊤ : Submodule kG P0) :=
    lifted_projector_range_kernel_le_jacobson (k := k) (G := G) J e π.hom sBar πBar eBarR
      he_idem he_mapQ hπBar_mk heBarR_apply
  have hess : f0.IsEssential :=
    isEssential_of_ker_le_jacobson_smul_top_local (k := k) (G := G) hf0_surj hker
  -- The remaining packaging step is delegated to the dedicated helper theorem.
  exact exists_lifted_projector_range_isProjectiveEnvelope (k := k) (G := G) e π.hom
    hP0proj hf0_surj hess

end GroupAlgebraProjectiveEnvelope

variable {R : Type u} [Ring R]

variable {M : Type v} [AddCommGroup M] [Module R M]

namespace LinearMap

variable {P : Type w₁} [AddCommGroup P] [Module R P]
variable {Q : Type w₂} [AddCommGroup Q] [Module R Q]

-- Proof sketch: composing with an essential epimorphism preserves the condition that only the top
-- submodule can map onto the whole target.
/-- Helper for Proposition 14-14.3-1: essential maps are closed under composition. -/
theorem IsEssential.comp
    {N : Type w₃} [AddCommGroup N] [Module R N] {f : P →ₗ[R] Q} {g : Q →ₗ[R] N}
    (hf : f.IsEssential) (hg : g.IsEssential) : (g.comp f).IsEssential := by
  refine ⟨fun S hS ↦ ?_⟩
  -- First push the image of `S` through the second essential map.
  apply hf.eq_top_of_map_eq_top
  apply hg.eq_top_of_map_eq_top
  simpa using (Submodule.map_comp f g S ▸ hS)

-- Proof sketch: once the lift `u` is known to be surjective by essentiality of `g`, projectivity
-- of `Q` splits `u`; essentiality of `f` then forces the splitting to be surjective, which kills
-- the kernel of `u`.
/-- Helper for Proposition 14-14.3-1: a lift between two projective envelopes is bijective. -/
theorem lift_between_projective_envelopes_bijective
    {f : P →ₗ[R] M} {g : Q →ₗ[R] M} (hf : f.IsProjectiveEnvelope)
    (hg : g.IsProjectiveEnvelope) {u : P →ₗ[R] Q} (hu : g.comp u = f) :
    Function.Bijective u := by
  letI : f.IsProjectiveEnvelope := hf
  letI : g.IsProjectiveEnvelope := hg
  have hu_surj : Function.Surjective u := by
    have hmap : (LinearMap.range u).map g = ⊤ := by
      rw [← LinearMap.range_comp]
      have hsurj_comp : Function.Surjective (g.comp u) := by
        simpa [hu] using hf.surjective
      simpa using (LinearMap.range_eq_top.2 hsurj_comp : LinearMap.range (g.comp u) = ⊤)
    -- Essentiality of `g` upgrades surjectivity on the image to surjectivity on the source.
    have htop : LinearMap.range u = ⊤ := hg.toIsEssential.eq_top_of_map_eq_top _ hmap
    exact LinearMap.range_eq_top.1 htop
  have hQproj : Module.Projective R Q := by infer_instance
  obtain ⟨i, hi⟩ := (Module.Projective.iff_split_of_projective u hu_surj).1 hQproj
  have hui : ∀ q : Q, u (i q) = q := by
    intro q
    simpa [LinearMap.comp_apply] using congrArg (fun e : Q →ₗ[R] Q => e q) hi
  have hcomp : f.comp i = g := by
    calc
      f.comp i = (g.comp u).comp i := by rw [hu]
      _ = g.comp (u.comp i) := by rw [LinearMap.comp_assoc]
      _ = g.comp LinearMap.id := by rw [hi]
      _ = g := by rw [LinearMap.comp_id]
  have hi_surj : Function.Surjective i := by
    have hmap : (LinearMap.range i).map f = ⊤ := by
      rw [← LinearMap.range_comp]
      have hsurj_comp : Function.Surjective (f.comp i) := by
        simpa [hcomp] using hg.surjective
      simpa using (LinearMap.range_eq_top.2 hsurj_comp : LinearMap.range (f.comp i) = ⊤)
    -- Essentiality of `f` forces the chosen splitting to have full range.
    have htop : LinearMap.range i = ⊤ := hf.toIsEssential.eq_top_of_map_eq_top _ hmap
    exact LinearMap.range_eq_top.1 htop
  refine ⟨?_, hu_surj⟩
  intro x y hxy
  have hzero : u (x - y) = 0 := by
    simp [map_sub, hxy]
  obtain ⟨q, hq⟩ := hi_surj (x - y)
  have hq_zero : q = 0 := by
    rw [← hui q, hq, hzero]
  have hxy' : x - y = 0 := by
    rw [← hq, hq_zero, map_zero]
  exact sub_eq_zero.mp hxy'

-- Proof sketch: use projectivity of one envelope to lift through the other surjection; essentiality
-- forces the lift to be surjective, and projectivity splits it, so the kernel must vanish.
/-- Proposition 14-14.3-1 (2): (a) any two projective envelopes of the same module are isomorphic
through an isomorphism commuting with the quotient maps. -/
theorem isProjectiveEnvelope_unique
    {P : Type w} [AddCommGroup P] [Module R P] {Q : Type w} [AddCommGroup Q] [Module R Q]
    {f : P →ₗ[R] M} {g : Q →ₗ[R] M} (hf : f.IsProjectiveEnvelope)
    (hg : g.IsProjectiveEnvelope) :
    ∃ e : P ≃ₗ[R] Q, g.comp e.toLinearMap = f := by
  letI : f.IsProjectiveEnvelope := hf
  -- Lift `f` across the envelope map `g`.
  obtain ⟨u, hu⟩ := Module.projective_lifting_property g f hg.surjective
  have hu_bij : Function.Bijective u := lift_between_projective_envelopes_bijective hf hg hu
  -- The bijective lift upgrades to the desired linear equivalence.
  refine ⟨LinearEquiv.ofBijective u hu_bij, hu⟩

end LinearMap

-- Proof sketch: the Jacobson quotient of an Artinian module has zero Jacobson radical, hence it is
-- semisimple by the Artinian semisimplicity criterion.
/-- The quotient by the Jacobson radical is semisimple for an Artinian module. -/
theorem largestSemisimpleQuotient_isSemisimple [IsArtinian R M] :
    IsSemisimpleModule R (M ⧸ Module.jacobson R M) :=
  by
    simpa using
      (IsArtinian.isSemisimpleModule_iff_jacobson R (M ⧸ Module.jacobson R M)).2
        (Module.jacobson_quotient_jacobson R M)

/-- Helper for Proposition 14-14.3-1: over a semiprimary ring, a submodule whose image generates
the Jacobson quotient is already the whole module. -/
theorem eq_top_of_sup_jacobson_smul_top_eq_top
    {X : Type w₁} [AddCommGroup X] [Module R X] [IsSemiprimaryRing R] (N : Submodule R X)
    (hN : N ⊔ Ring.jacobson R • (⊤ : Submodule R X) = ⊤) : N = ⊤ := by
  have hmap : Submodule.map N.mkQ (Ring.jacobson R • (⊤ : Submodule R X)) = ⊤ := by
    -- Pass to the quotient by `N` to rewrite the generation hypothesis as a statement about the
    -- Jacobson radical action on `X ⧸ N`.
    exact (Submodule.map_mkQ_eq_top N (Ring.jacobson R • (⊤ : Submodule R X))).2 hN
  have hJtop : Ring.jacobson R • (⊤ : Submodule R (X ⧸ N)) = ⊤ := by
    -- The quotient identifies the image of `Ring.jacobson R • ⊤` with the Jacobson action on the
    -- whole quotient module.
    simpa [Submodule.map_smul'', Submodule.map_top] using hmap
  rcases (IsSemiprimaryRing.isNilpotent (R := R) : IsNilpotent (Ring.jacobson R)) with ⟨n, hn⟩
  have hpow : ∀ m : ℕ, (Ring.jacobson R ^ m) • (⊤ : Submodule R (X ⧸ N)) = ⊤ := by
    intro m
    induction m with
    | zero =>
        -- The zeroth power is the unit ideal, so it acts trivially.
        change ((1 : Ideal R) • (⊤ : Submodule R (X ⧸ N))) = ⊤
        simp
    | succ m ih =>
        -- Iterate the hypothesis through powers of the Jacobson radical.
        calc
          (Ring.jacobson R ^ (m + 1)) • (⊤ : Submodule R (X ⧸ N)) =
              Ring.jacobson R • (Ring.jacobson R ^ m • (⊤ : Submodule R (X ⧸ N))) := by
                rw [Ideal.IsTwoSided.pow_succ (I := Ring.jacobson R), Submodule.mul_smul]
          _ = Ring.jacobson R • (⊤ : Submodule R (X ⧸ N)) := by rw [ih]
          _ = ⊤ := hJtop
  have htopbot : (⊤ : Submodule R (X ⧸ N)) = ⊥ := by
    -- Nilpotence of `Ring.jacobson R` forces the whole quotient to vanish.
    calc
      (⊤ : Submodule R (X ⧸ N)) = (Ring.jacobson R ^ n) • (⊤ : Submodule R (X ⧸ N)) :=
        (hpow n).symm
      _ = (0 : Ideal R) • (⊤ : Submodule R (X ⧸ N)) := by rw [hn]
      _ = ⊥ := by simp
  have hsubmod : Subsingleton (Submodule R (X ⧸ N)) := (subsingleton_iff_top_eq_bot).mp htopbot
  have hsub : Subsingleton (X ⧸ N) := (Submodule.subsingleton_iff R).1 hsubmod
  exact (Submodule.Quotient.subsingleton_iff).1 hsub

namespace LinearMap

variable {P₁ : Type w₁} {P₂ : Type w₂} {M₁ : Type w₃} {M₂ : Type w₄}
variable [AddCommGroup P₁] [Module R P₁] [AddCommGroup P₂] [Module R P₂]
variable [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]

/-- Helper for Proposition 14-14.3-1: every linear equivalence is an essential map. -/
theorem equiv_isEssential (e : P₁ ≃ₗ[R] P₂) : (e : P₁ →ₗ[R] P₂).IsEssential := by
  refine ⟨fun N hN ↦ ?_⟩
  -- Mapping onto `⊤` through an equivalence already forces the original submodule to be `⊤`.
  exact (Submodule.map_eq_top_iff (p := N) (e := e)).1 hN

-- Proof sketch: conjugating by equivalences amounts to composing with essential maps on both
-- sides, so the essentiality predicate can be transported through the two inverses.
/-- Helper for Proposition 14-14.3-1: conjugating by linear equivalences preserves essentiality. -/
theorem isEssential_iff_conj
    (eP : P₁ ≃ₗ[R] P₂) (eM : M₁ ≃ₗ[R] M₂) {f : P₁ →ₗ[R] M₁} :
    ((((eM : M₁ →ₗ[R] M₂).comp f).comp (eP.symm : P₂ →ₗ[R] P₁)).IsEssential) ↔
      f.IsEssential := by
  constructor
  · intro h
    -- Undo the conjugation on the target, then on the source.
    have h' :
        (((eM.symm : M₂ →ₗ[R] M₁).comp
          (((eM : M₁ →ₗ[R] M₂).comp f).comp (eP.symm : P₂ →ₗ[R] P₁))).IsEssential) :=
      IsEssential.comp h (equiv_isEssential (R := R) eM.symm)
    simpa [LinearMap.comp_assoc] using
      (IsEssential.comp (equiv_isEssential (R := R) eP) h')
  · intro h
    -- Reapply the source and target equivalences to recover the conjugated map.
    have h' : (((eM : M₁ →ₗ[R] M₂).comp f).IsEssential) :=
      IsEssential.comp h (equiv_isEssential (R := R) eM)
    simpa [LinearMap.comp_assoc] using
      (IsEssential.comp (equiv_isEssential (R := R) eP.symm) h')

-- Proof sketch: a linear equivalence transports projectivity and surjectivity directly, while the
-- essentiality condition is pulled across the induced order isomorphism on submodules.
/-- Helper for Proposition 14-14.3-1: conjugating by linear equivalences preserves the
projective-envelope property. -/
theorem isProjectiveEnvelope_iff_conj
    (eP : P₁ ≃ₗ[R] P₂) (eM : M₁ ≃ₗ[R] M₂) {f : P₁ →ₗ[R] M₁} :
    ((((eM : M₁ →ₗ[R] M₂).comp f).comp (eP.symm : P₂ →ₗ[R] P₁)).IsProjectiveEnvelope) ↔
      f.IsProjectiveEnvelope := by
  constructor
  · intro h
    letI : (((eM : M₁ →ₗ[R] M₂).comp f).comp (eP.symm : P₂ →ₗ[R] P₁)).IsProjectiveEnvelope := h
    -- Transport projectivity and essentiality back through the two equivalences.
    letI : Module.Projective R P₁ := Module.Projective.of_equiv' eP.symm
    letI : f.IsEssential := (isEssential_iff_conj (R := R) eP eM).mp h.toIsEssential
    have hsurj : Function.Surjective f := by
      -- A surjective conjugate gives a surjective original map after undoing the source change.
      intro y
      obtain ⟨x, hx⟩ := h.surjective (eM y)
      refine ⟨eP.symm x, ?_⟩
      apply eM.injective
      simpa [LinearMap.comp_apply] using hx
    exact LinearMap.IsProjectiveEnvelope.mk hsurj
  · intro h
    letI : f.IsProjectiveEnvelope := h
    -- Transport projectivity and essentiality forward through the two equivalences.
    letI : Module.Projective R P₂ := Module.Projective.of_equiv' eP
    letI :
        ((((eM : M₁ →ₗ[R] M₂).comp f).comp (eP.symm : P₂ →ₗ[R] P₁))).IsEssential :=
      (isEssential_iff_conj (R := R) eP eM).mpr h.toIsEssential
    have hsurj :
        Function.Surjective (((eM : M₁ →ₗ[R] M₂).comp f).comp (eP.symm : P₂ →ₗ[R] P₁)) := by
      -- Surjectivity is witnessed by applying the inverse target equivalence first.
      intro y
      obtain ⟨x, hx⟩ := h.surjective (eM.symm y)
      refine ⟨eP x, ?_⟩
      simp [LinearMap.comp_apply, hx]
    exact LinearMap.IsProjectiveEnvelope.mk hsurj

/-- Helper for Proposition 14-14.3-1: over a semiprimary ring, a surjective map with kernel inside
`Ring.jacobson R • ⊤` is essential. -/
theorem isEssential_of_ker_le_jacobson_smul_top
    [IsSemiprimaryRing R] {P : Type w₁} [AddCommGroup P] [Module R P]
    {M : Type w₂} [AddCommGroup M] [Module R M] {f : P →ₗ[R] M} (hf : Function.Surjective f)
    (hker : LinearMap.ker f ≤ Ring.jacobson R • (⊤ : Submodule R P)) : f.IsEssential := by
  refine ⟨fun N hN ↦ ?_⟩
  have hsurjN : Function.Surjective (f.domRestrict N) := by
    -- Surjectivity of the restricted map is exactly the hypothesis that `N` maps onto the target.
    rw [← LinearMap.range_eq_top, LinearMap.range_domRestrict]
    exact hN
  have hsup : N ⊔ LinearMap.ker f = ⊤ := (LinearMap.surjective_domRestrict_iff hf).1 hsurjN
  have hsup' : N ⊔ Ring.jacobson R • (⊤ : Submodule R P) = ⊤ := by
    -- Enlarge the kernel bound from `ker f` to the whole Jacobson radical piece.
    apply top_unique
    have hle : N ⊔ LinearMap.ker f ≤ N ⊔ Ring.jacobson R • (⊤ : Submodule R P) :=
      sup_le_sup_left hker N
    exact hsup ▸ hle
  exact eq_top_of_sup_jacobson_smul_top_eq_top (R := R) N hsup'

/-- Helper for Proposition 14-14.3-1: the kernel of a surjective essential map lies in the
Jacobson radical of the source module. -/
theorem IsEssential.ker_le_jacobson
    {P : Type w₁} [AddCommGroup P] [Module R P]
    {M : Type w₂} [AddCommGroup M] [Module R M]
    {f : P →ₗ[R] M} (hf : f.IsEssential) (hsurj : Function.Surjective f) :
    LinearMap.ker f ≤ Module.jacobson R P := by
  rw [Module.jacobson]
  refine le_sInf ?_
  intro S hS
  by_contra hker
  have hsup : S ⊔ LinearMap.ker f = ⊤ := by
    have hlt : S < S ⊔ LinearMap.ker f := by
      refine lt_of_le_of_ne le_sup_left ?_
      intro hEq
      exact hker (hEq ▸ le_sup_right)
    exact (hS.lt_iff).1 hlt
  have hmap : S.map f = ⊤ := by
    apply top_le_iff.mp
    intro y hy
    rcases hsurj y with ⟨x, rfl⟩
    have hx : x ∈ S ⊔ LinearMap.ker f := by
      simp [hsup]
    rcases Submodule.mem_sup.1 hx with ⟨xS, hxS, xK, hxK, rfl⟩
    refine (Submodule.mem_map).2 ?_
    refine ⟨xS, hxS, ?_⟩
    simp [LinearMap.mem_ker] at hxK
    simp [hxK]
  exact hS.ne_top (hf.eq_top_of_map_eq_top S hmap)

/-- Helper for Proposition 14-14.3-1: a projective envelope over a projective target identifies
its source with that target. -/
theorem IsProjectiveEnvelope.nonempty_linearEquiv_target
    {P : Type w₁} [AddCommGroup P] [Module R P]
    {M : Type w₂} [AddCommGroup M] [Module R M]
    {f : P →ₗ[R] M} (hf : f.IsProjectiveEnvelope) [Module.Projective R M] :
    Nonempty (P ≃ₗ[R] M) := by
  letI : (LinearMap.id : M →ₗ[R] M).IsEssential :=
    equiv_isEssential (R := R) (LinearEquiv.refl R M)
  letI : (LinearMap.id : M →ₗ[R] M).IsProjectiveEnvelope :=
    LinearMap.IsProjectiveEnvelope.mk (f := LinearMap.id) (fun x ↦ ⟨x, rfl⟩)
  have hid : (LinearMap.id : M →ₗ[R] M).IsProjectiveEnvelope := inferInstance
  obtain ⟨u, hu⟩ := Module.projective_lifting_property (LinearMap.id : M →ₗ[R] M) f
    (Function.surjective_id)
  have hu_bij : Function.Bijective u :=
    lift_between_projective_envelopes_bijective hf hid hu
  exact ⟨LinearEquiv.ofBijective u hu_bij⟩

-- Proof sketch: a submodule inside the graph of a linear equivalence is already determined by its
-- first projection, so surjectivity on the first factor upgrades to surjectivity on the second.
/-- Helper for Proposition 14-14.3-1: a submodule of the graph of a linear equivalence has full
second projection as soon as its first projection is full. -/
theorem graph_second_map_eq_top_of_first_map_eq_top
    {Q₁ : Type w₁} {Q₂ : Type w₂} [AddCommGroup Q₁] [Module R Q₁]
    [AddCommGroup Q₂] [Module R Q₂] {e : Q₁ ≃ₗ[R] Q₂} {W : Submodule R (Q₁ × Q₂)}
    (hW : W ≤ e.toLinearMap.graph) (hfst : W.map (LinearMap.fst R Q₁ Q₂) = ⊤) :
    W.map (LinearMap.snd R Q₁ Q₂) = ⊤ := by
  -- Choose a preimage of `e.symm y` under the first projection and use the graph relation.
  apply top_le_iff.mp
  intro y hy
  let x : Q₁ := e.symm y
  have hx : x ∈ W.map (LinearMap.fst R Q₁ Q₂) := by
    simp [hfst, x]
  rcases (Submodule.mem_map).1 hx with ⟨z, hzW, hzfst⟩
  refine (Submodule.mem_map).2 ?_
  refine ⟨z, hzW, ?_⟩
  have hzgraph : z ∈ e.toLinearMap.graph := hW hzW
  have hz2 : z.2 = e z.1 := by
    simpa [LinearMap.mem_graph_iff] using hzgraph
  have hz1 : z.1 = x := by
    simpa using hzfst
  simp [hz2, hz1, x]

-- Proof sketch: if the image of a submodule under a product map is all of `M₁ × M₂`, then its
-- first-coordinate image maps onto `M₁`.
/-- Helper for Proposition 14-14.3-1: fullness of the image under a product map forces fullness on
the first coordinate image. -/
theorem left_map_eq_top_of_prodMap_eq_top {f : P₁ →ₗ[R] M₁} {g : P₂ →ₗ[R] M₂}
    {S : Submodule R (P₁ × P₂)} (hS : S.map (LinearMap.prodMap f g) = ⊤) :
    (S.map (LinearMap.fst R P₁ P₂)).map f = ⊤ := by
  -- Realize every `(x, 0)` in the image of `S` and then project to the first factor.
  apply top_le_iff.mp
  intro x hx
  have hx' : (x, 0) ∈ S.map (LinearMap.prodMap f g) := by
    simpa [hS]
  rcases (Submodule.mem_map).1 hx' with ⟨z, hzS, hzmap⟩
  refine (Submodule.mem_map).2 ?_
  refine ⟨z.1, ?_, ?_⟩
  · refine (Submodule.mem_map).2 ?_
    exact ⟨z, hzS, rfl⟩
  · simpa using congrArg Prod.fst hzmap

-- Proof sketch: the same argument on the second coordinate realizes every `(0, y)` in the image.
/-- Helper for Proposition 14-14.3-1: fullness of the image under a product map forces fullness on
the second coordinate image. -/
theorem right_map_eq_top_of_prodMap_eq_top {f : P₁ →ₗ[R] M₁} {g : P₂ →ₗ[R] M₂}
    {S : Submodule R (P₁ × P₂)} (hS : S.map (LinearMap.prodMap f g) = ⊤) :
    (S.map (LinearMap.snd R P₁ P₂)).map g = ⊤ := by
  -- Realize every `(0, y)` in the image of `S` and then project to the second factor.
  apply top_le_iff.mp
  intro y hy
  have hy' : (0, y) ∈ S.map (LinearMap.prodMap f g) := by
    simpa [hS]
  rcases (Submodule.mem_map).1 hy' with ⟨z, hzS, hzmap⟩
  refine (Submodule.mem_map).2 ?_
  refine ⟨z.2, ?_, ?_⟩
  · refine (Submodule.mem_map).2 ?_
    exact ⟨z, hzS, rfl⟩
  · simpa using congrArg Prod.snd hzmap

-- Route correction: the earlier coordinate chase was too weak. The stable route is Goursat on the
-- submodule in `P₁ × P₂`, then a kernel-fiber argument on the second quotient factor.
/-- Helper for Proposition 14-14.3-1: the product of an essential map with a surjective essential
map is again essential. -/
theorem prodMap_isEssential {f : P₁ →ₗ[R] M₁} {g : P₂ →ₗ[R] M₂}
    (hg_surj : Function.Surjective g) (hf : f.IsEssential) (hg : g.IsEssential) :
    (LinearMap.prodMap f g).IsEssential := by
  refine ⟨fun S hS ↦ ?_⟩
  let L₁ : Submodule R P₁ := S.map (LinearMap.fst R P₁ P₂)
  let L₂ : Submodule R P₂ := S.map (LinearMap.snd R P₁ P₂)
  have hL₁map : L₁.map f = ⊤ := by
    simpa [L₁] using left_map_eq_top_of_prodMap_eq_top hS
  have hL₂map : L₂.map g = ⊤ := by
    simpa [L₂] using right_map_eq_top_of_prodMap_eq_top hS
  have hL₁ : L₁ = ⊤ := hf.eq_top_of_map_eq_top L₁ hL₁map
  have hL₂ : L₂ = ⊤ := hg.eq_top_of_map_eq_top L₂ hL₂map
  have hfst_surj : Function.Surjective (Prod.fst ∘ S.subtype) := by
    -- Full image on the first coordinate is exactly surjectivity of the first projection.
    intro x
    have hx : x ∈ L₁ := by
      simpa [hL₁, L₁]
    rcases (Submodule.mem_map).1 hx with ⟨z, hzS, rfl⟩
    exact ⟨⟨z, hzS⟩, rfl⟩
  have hsnd_surj : Function.Surjective (Prod.snd ∘ S.subtype) := by
    -- The same argument gives surjectivity of the second projection.
    intro y
    have hy : y ∈ L₂ := by
      simpa [hL₂, L₂]
    rcases (Submodule.mem_map).1 hy with ⟨z, hzS, rfl⟩
    exact ⟨⟨z, hzS⟩, rfl⟩
  obtain ⟨e, he⟩ := Submodule.goursat_surjective (L := S) hfst_surj hsnd_surj
  let A : Submodule R P₁ := S.goursatFst
  let B : Submodule R P₂ := S.goursatSnd
  let U : Submodule R (P₁ × P₂) := S ⊓ (⊤ : Submodule R P₁).prod (LinearMap.ker g)
  have hUfst_map : (U.map (LinearMap.fst R P₁ P₂)).map f = ⊤ := by
    -- Use the points of `S` mapping to `(x, 0)` to force fullness after quotienting by `ker g`.
    apply top_le_iff.mp
    intro x hx
    have hx' : (x, 0) ∈ S.map (LinearMap.prodMap f g) := by
      simpa [hS]
    rcases (Submodule.mem_map).1 hx' with ⟨z, hzS, hzmap⟩
    have hzU : z ∈ U := by
      refine ⟨hzS, ?_⟩
      refine ⟨by simp, ?_⟩
      simpa [LinearMap.mem_ker] using congrArg Prod.snd hzmap
    refine (Submodule.mem_map).2 ?_
    refine ⟨z.1, ?_, ?_⟩
    · exact (Submodule.mem_map).2 ⟨z, hzU, rfl⟩
    · simpa using congrArg Prod.fst hzmap
  have hUfst : U.map (LinearMap.fst R P₁ P₂) = ⊤ := hf.eq_top_of_map_eq_top _ hUfst_map
  let q : P₁ × P₂ →ₗ[R] (P₁ ⧸ A) × (P₂ ⧸ B) := A.mkQ.prodMap B.mkQ
  let W : Submodule R ((P₁ ⧸ A) × (P₂ ⧸ B)) := U.map q
  have hWle : W ≤ e.toLinearMap.graph := by
    -- The quotient image of `U` sits inside the quotient image of `S`, which is Goursat's graph.
    intro z hz
    have hz' : z ∈ S.map q := Submodule.map_mono inf_le_left hz
    rw [show S.map q = LinearMap.range (q.comp S.subtype) by
      rw [LinearMap.range_comp, Submodule.range_subtype]] at hz'
    rw [he] at hz'
    simpa [W] using hz'
  have hWfst : W.map (LinearMap.fst R (P₁ ⧸ A) (P₂ ⧸ B)) = ⊤ := by
    -- Every quotient class on the first factor has a representative coming from `U`.
    apply top_le_iff.mp
    intro x hx
    obtain ⟨x0, rfl⟩ := Quotient.mk_surjective x
    have hx0 : x0 ∈ U.map (LinearMap.fst R P₁ P₂) := by
      simpa [hUfst]
    rcases (Submodule.mem_map).1 hx0 with ⟨z, hzU, hzfst⟩
    refine (Submodule.mem_map).2 ?_
    refine ⟨q z, ?_, ?_⟩
    · exact (Submodule.mem_map).2 ⟨z, hzU, rfl⟩
    · simpa [q] using congrArg (Submodule.Quotient.mk (p := A)) hzfst
  have hWsnd : W.map (LinearMap.snd R (P₁ ⧸ A) (P₂ ⧸ B)) = ⊤ :=
    graph_second_map_eq_top_of_first_map_eq_top hWle hWfst
  have hkerB : (LinearMap.ker g).map B.mkQ = ⊤ := by
    -- The second quotient factor is already generated by classes coming from `ker g`.
    apply top_le_iff.mp
    intro y hy
    have hyW : y ∈ W.map (LinearMap.snd R (P₁ ⧸ A) (P₂ ⧸ B)) := by
      simpa [hWsnd]
    rcases (Submodule.mem_map).1 hyW with ⟨w, hwW, hwsnd⟩
    rcases (Submodule.mem_map).1 hwW with ⟨z, hzU, rfl⟩
    refine (Submodule.mem_map).2 ?_
    refine ⟨z.2, hzU.2.2, ?_⟩
    simpa [q] using hwsnd
  have hsupB : (LinearMap.ker g) ⊔ B = ⊤ := by
    simpa [sup_comm] using (Submodule.map_mkQ_eq_top B (LinearMap.ker g)).mp hkerB
  have hBmap : B.map g = ⊤ := by
    -- Once `ker g ⊔ B = ⊤`, surjectivity of `g` promotes `B` to a full image.
    have htop : ((LinearMap.ker g) ⊔ B).map g = ⊤ := by
      rw [hsupB]
      simpa using (LinearMap.range_eq_top.2 hg_surj : LinearMap.range g = ⊤)
    have hmapker : (LinearMap.ker g).map g = ⊥ := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        simp [LinearMap.mem_ker] at hx
        simpa [hx]
      · intro hy
        have hy0 : y = 0 := by
          simpa using hy
        refine (Submodule.mem_map).2 ?_
        refine ⟨0, by simp [LinearMap.mem_ker], ?_⟩
        simpa [hy0]
    rw [Submodule.map_sup, hmapker] at htop
    simpa [sup_comm] using htop
  have hB : B = ⊤ := hg.eq_top_of_map_eq_top B hBmap
  have hAmap : A.map f = ⊤ := by
    -- After `B = ⊤`, subtract the vertical element `(0, z₂)` to land in `A = S.goursatFst`.
    apply top_le_iff.mp
    intro x hx
    have hx' : (x, 0) ∈ S.map (LinearMap.prodMap f g) := by
      simpa [hS]
    rcases (Submodule.mem_map).1 hx' with ⟨z, hzS, hzmap⟩
    have hz0 : (0, z.2) ∈ S := by
      have hz2B : z.2 ∈ B := by
        simpa [B, hB]
      simpa [B, Submodule.goursatSnd] using hz2B
    have hzA0 : (z.1, 0) ∈ S := by
      convert sub_mem hzS hz0 using 1 <;> ext <;> simp
    have hzA : z.1 ∈ A := by
      simpa [A, Submodule.goursatFst] using hzA0
    exact (Submodule.mem_map).2 ⟨z.1, hzA, by simpa using congrArg Prod.fst hzmap⟩
  have hA : A = ⊤ := hf.eq_top_of_map_eq_top A hAmap
  have htop : (⊤ : Submodule R (P₁ × P₂)) ≤ S := by
    simpa [A, hA, B, hB] using (Submodule.goursatFst_prod_goursatSnd_le S)
  exact top_le_iff.mp htop

-- Proof sketch: projectivity is stable under binary products, surjectivity is coordinatewise, and
-- the essentiality part is exactly `prodMap_isEssential`.
/-- Helper for Proposition 14-14.3-1: the product of two projective envelopes is a projective
envelope. -/
theorem prodMap_isProjectiveEnvelope {f : P₁ →ₗ[R] M₁} {g : P₂ →ₗ[R] M₂}
    (hf : f.IsProjectiveEnvelope) (hg : g.IsProjectiveEnvelope) :
    (LinearMap.prodMap f g).IsProjectiveEnvelope := by
  -- Assemble the structure one field at a time.
  letI : Module.Projective R (P₁ × P₂) := by
    infer_instance
  letI : (LinearMap.prodMap f g).IsEssential :=
    prodMap_isEssential hg.surjective hf.toIsEssential hg.toIsEssential
  exact LinearMap.IsProjectiveEnvelope.mk
    (Function.Surjective.prodMap hf.surjective hg.surjective)

end LinearMap

namespace DirectSum

/-- Helper for Proposition 14-14.3-1: separating the `none` summand conjugates `DirectSum.lmap`
to the corresponding binary product map. -/
theorem lmap_option_eq_conj_prodMap
    {ι : Type v} {P : Option ι → Type w} {M : Option ι → Type w}
    [∀ i, AddCommGroup (P i)] [∀ i, Module R (P i)] [∀ i, AddCommGroup (M i)]
    [∀ i, Module R (M i)] (f : ∀ i, P i →ₗ[R] M i) :
    let eP : (⨁ i, P i) ≃ₗ[R] P none × ⨁ i, P (some i) :=
      DirectSum.lequivProdDirectSum (R := R) (α := P)
    let eM : (⨁ i, M i) ≃ₗ[R] M none × ⨁ i, M (some i) :=
      DirectSum.lequivProdDirectSum (R := R) (α := M)
    (eM.toLinearMap.comp (DirectSum.lmap f)).comp eP.symm.toLinearMap =
      LinearMap.prodMap (f none) (DirectSum.lmap fun i => f (some i)) := by
  -- Evaluate both sides on a pair and compare the two coordinates directly.
  dsimp [DirectSum.lequivProdDirectSum, DirectSum.addEquivProdDirectSum]
  apply DFunLike.ext
  rintro ⟨x, y⟩
  ext
  · rfl
  · rfl

/-- Helper for Proposition 14-14.3-1: reindexing a direct sum conjugates `DirectSum.lmap` to the
same family written over the new index type. -/
theorem lmap_congrLeft_eq_conj
    {α β : Type v} (e : α ≃ β) {P : α → Type w} {M : α → Type w}
    [∀ i, AddCommGroup (P i)] [∀ i, Module R (P i)] [∀ i, AddCommGroup (M i)]
    [∀ i, Module R (M i)] (f : ∀ i, P i →ₗ[R] M i) :
    let eP : (⨁ i, P i) ≃ₗ[R] ⨁ j, P (e.symm j) :=
      DirectSum.lequivCongrLeft (R := R) e
    let eM : (⨁ i, M i) ≃ₗ[R] ⨁ j, M (e.symm j) :=
      DirectSum.lequivCongrLeft (R := R) e
    (eM.toLinearMap.comp (DirectSum.lmap f)).comp eP.symm.toLinearMap =
      DirectSum.lmap (fun j => f (e.symm j)) := by
  -- Evaluate on each reindexed coordinate and use the explicit formula for `lequivCongrLeft`.
  dsimp
  apply DFunLike.ext
  intro z
  ext b
  have hz : ((DirectSum.lequivCongrLeft (R := R) e).symm z) (e.symm b) = z b := by
    simpa using
      (DirectSum.lequivCongrLeft_apply (R := R) (h := e)
        ((DirectSum.lequivCongrLeft (R := R) e).symm z) b).symm
  simp [DirectSum.lmap_apply, hz]

/-- Proposition 14-14.3-1 (3): (b) for a finite family of projective envelopes, the induced map on
the direct sums is again a projective envelope. Here the direct sum is the finitely supported family
module `Π₀ i, -`. -/
theorem lmap_isProjectiveEnvelope
    {ι : Type v} [Finite ι] {P : ι → Type w} {M : ι → Type w}
    [∀ i, AddCommGroup (P i)] [∀ i, Module R (P i)] [∀ i, AddCommGroup (M i)]
    [∀ i, Module R (M i)] (f : ∀ i, P i →ₗ[R] M i)
    (hf : ∀ i, (f i).IsProjectiveEnvelope) :
    (lmap f).IsProjectiveEnvelope := by
  classical
  revert P M f hf
  induction ι using Finite.induction_empty_option with
  | of_equiv e ih =>
      intro P M _ _ _ _ f hf
      -- Route correction: the old reindexing attempt got stuck on dependent transports. Reindex the
      -- current family by `e`, then conjugate the target map to the already-proved smaller index set.
      let P' : _ → Type w := fun i ↦ P (e i)
      let M' : _ → Type w := fun i ↦ M (e i)
      let f' : ∀ i, P' i →ₗ[R] M' i := fun i ↦ f (e i)
      have hf' : ∀ i, (f' i).IsProjectiveEnvelope := fun i ↦ hf (e i)
      have h' : (DirectSum.lmap f').IsProjectiveEnvelope :=
        ih (P := P') (M := M') f' hf'
      let eP' : (⨁ j, P j) ≃ₗ[R] ⨁ i, P (e i) :=
        DirectSum.lequivCongrLeft (R := R) e.symm
      let eM' : (⨁ j, M j) ≃ₗ[R] ⨁ i, M (e i) :=
        DirectSum.lequivCongrLeft (R := R) e.symm
      have hconj :
          (eM'.toLinearMap.comp (DirectSum.lmap f)).comp eP'.symm.toLinearMap =
            DirectSum.lmap f' := by
        -- The canonical reindexing equivalence rewrites the target direct sum into the inductive one.
        simpa [P', M', eP', eM', f'] using
          DirectSum.lmap_congrLeft_eq_conj (R := R) e.symm f
      have hconj' :
          ((eM'.toLinearMap.comp (DirectSum.lmap f)).comp
            eP'.symm.toLinearMap).IsProjectiveEnvelope := by
        rw [hconj]
        exact h'
      exact (LinearMap.isProjectiveEnvelope_iff_conj (R := R) eP' eM').mp hconj'
  | h_empty =>
      intro P M _ _ _ _ f hf
      letI : Module.Projective R (⨁ i, P i) := by
        infer_instance
      letI : (DirectSum.lmap f).IsEssential := by
        refine ⟨fun N hN ↦ ?_⟩
        -- On the empty index set, every submodule is equal because the source direct sum is trivial.
        exact Subsingleton.elim _ _
      -- The empty direct sum map is the unique map from the zero module to itself.
      exact LinearMap.IsProjectiveEnvelope.mk (fun y ↦ ⟨0, Subsingleton.elim _ _⟩)
  | h_option ih =>
      intro P M _ _ _ _ f hf
      let P' : _ → Type w := fun i ↦ P (some i)
      let M' : _ → Type w := fun i ↦ M (some i)
      let f' : ∀ i, P' i →ₗ[R] M' i := fun i ↦ f (some i)
      have hf' : ∀ i, (f' i).IsProjectiveEnvelope := fun i ↦ hf (some i)
      have htail : (DirectSum.lmap f').IsProjectiveEnvelope :=
        ih (P := P') (M := M') f' hf'
      let eP' : (⨁ i, P i) ≃ₗ[R] P none × ⨁ i, P (some i) :=
        DirectSum.lequivProdDirectSum (R := R) (α := P)
      let eM' : (⨁ i, M i) ≃ₗ[R] M none × ⨁ i, M (some i) :=
        DirectSum.lequivProdDirectSum (R := R) (α := M)
      have hprod :
          (LinearMap.prodMap (f none) (DirectSum.lmap f')).IsProjectiveEnvelope :=
        -- Split off the `none` summand and apply the binary product theorem.
        LinearMap.prodMap_isProjectiveEnvelope (hf none) htail
      have hconj :
          (eM'.toLinearMap.comp (DirectSum.lmap f)).comp eP'.symm.toLinearMap =
            LinearMap.prodMap (f none) (DirectSum.lmap f') := by
        -- The direct sum over `Option α` is conjugate to the binary product of the head and tail.
        simpa [eP', eM', f'] using DirectSum.lmap_option_eq_conj_prodMap (R := R) f
      have hconj' :
          ((eM'.toLinearMap.comp (DirectSum.lmap f)).comp
            eP'.symm.toLinearMap).IsProjectiveEnvelope := by
        rw [hconj]
        exact hprod
      exact (LinearMap.isProjectiveEnvelope_iff_conj (R := R) eP' eM').mp hconj'

end DirectSum

namespace LinearMap

/-- Helper for Proposition 14-14.3-1: Artinian modules have coatomic submodule lattices because
every proper submodule lies below a minimal proper supermodule, hence below a coatom. -/
theorem isCoatomic_submodule_of_isArtinian
    {P : Type w} [AddCommGroup P] [Module R P] [IsArtinianRing R] [IsArtinian R P] :
    IsCoatomic (Submodule R P) := by
  -- Route correction: the earlier ring-free claim was too strong. Over an Artinian ring, Hopkins-
  -- Levitzki makes an Artinian module finite, and finite modules are already known to be coatomic.
  let _ : Module.Finite R P := IsSemiprimaryRing.finite_of_isArtinian R R P
  infer_instance

/-- Helper for Proposition 14-14.3-1: over an Artinian ring, an Artinian module has a coatomic
submodule lattice. -/
theorem isCoatomic_submodule_of_isArtinianRing_and_isArtinian
    {P : Type w} [AddCommGroup P] [Module R P] [IsArtinianRing R] [IsArtinian R P] :
    IsCoatomic (Submodule R P) := by
  let _ : IsSemiprimaryRing R := inferInstance
  -- Hopkins-Levitzki upgrades an Artinian module over an Artinian ring to a finite module.
  let _ : Module.Finite R P := IsSemiprimaryRing.finite_of_isArtinian R R P
  -- Finite modules have coatomic submodule lattices.
  infer_instance

/-- Helper for Proposition 14-14.3-1: on a coatomic submodule lattice, the quotient by the
Jacobson radical is an essential epimorphism. -/
theorem jacobson_mkQ_isEssential_of_isCoatomic
    {P : Type w} [AddCommGroup P] [Module R P] [IsCoatomic (Submodule R P)] :
    (((Module.jacobson R P).mkQ) : P →ₗ[R] P ⧸ Module.jacobson R P).IsEssential := by
  refine ⟨fun N hN ↦ ?_⟩
  -- Rewrite surjectivity on the quotient into a statement that `N` together with the radical
  -- generates the whole lattice, then invoke `Order.radical_nongenerating`.
  have hsup : Module.jacobson R P ⊔ N = ⊤ := by
    exact (Submodule.map_mkQ_eq_top (Module.jacobson R P) N).1 hN
  have hjac : Module.jacobson R P = Order.radical (Submodule R P) := by
    rw [Module.jacobson, Order.radical, sInf_eq_iInf]
  have hsup' : N ⊔ Order.radical (Submodule R P) = ⊤ := by
    rw [sup_comm, ← hjac]
    exact hsup
  exact Order.radical_nongenerating hsup'

/-- Helper for Proposition 14-14.3-1: Artinian modules have essential Jacobson-quotient maps
because their submodule lattices are coatomic. -/
theorem jacobson_mkQ_isEssential_of_isArtinian
    {P : Type w} [AddCommGroup P] [Module R P] [IsArtinianRing R] [IsArtinian R P] :
    (((Module.jacobson R P).mkQ) : P →ₗ[R] P ⧸ Module.jacobson R P).IsEssential := by
  -- Convert Artinianity directly into coatomicity of the submodule lattice.
  letI : IsCoatomic (Submodule R P) := isCoatomic_submodule_of_isArtinian (R := R) (P := P)
  exact jacobson_mkQ_isEssential_of_isCoatomic (R := R) (P := P)

/-- Helper for Proposition 14-14.3-1: over an Artinian ring, an Artinian module has an essential
Jacobson-quotient map. -/
theorem jacobson_mkQ_isEssential_of_isArtinianRing_and_isArtinian
    {P : Type w} [AddCommGroup P] [Module R P] [IsArtinianRing R] [IsArtinian R P] :
    (((Module.jacobson R P).mkQ) : P →ₗ[R] P ⧸ Module.jacobson R P).IsEssential := by
  letI : IsCoatomic (Submodule R P) :=
    isCoatomic_submodule_of_isArtinianRing_and_isArtinian (R := R) (P := P)
  -- The coatomic-lattice argument now applies without the missing generic step.
  exact jacobson_mkQ_isEssential_of_isCoatomic (R := R) (P := P)

-- Proof sketch: the canonical quotient map `P → P / jacobson(P)` is surjective, the quotient is
-- semisimple by the previous theorem, and projectivity plus maximality of the semisimple quotient
-- identifies this map as the projective envelope.
/-- Proposition 14-14.3-1 (4): (c) if `P` is projective, then the canonical map onto its largest
semisimple quotient is a projective envelope. -/
theorem largestSemisimpleQuotientMk_isProjectiveEnvelope
    {P : Type w} [AddCommGroup P] [Module R P] [Module.Projective R P]
    [IsArtinianRing R] [IsArtinian R P] :
    ((Module.jacobson R P).mkQ).IsProjectiveEnvelope := by
  -- The source is already projective; only essentiality and surjectivity of the quotient map
  -- remain.
  letI :
      (((Module.jacobson R P).mkQ) : P →ₗ[R] P ⧸ Module.jacobson R P).IsEssential :=
    jacobson_mkQ_isEssential_of_isArtinian (R := R) (P := P)
  exact LinearMap.IsProjectiveEnvelope.mk (Module.jacobson R P).mkQ_surjective

end LinearMap

/-- Helper for Corollary 14-14.3-2: the largest semisimple quotient of a binary product is the
product of the two largest semisimple quotients. -/
theorem largestSemisimpleQuotient_prod_linearEquiv
    {P : Type v} [AddCommGroup P] [Module R P] [Module.Projective R P]
    [IsArtinianRing R] [IsArtinian R P]
    {Q : Type w} [AddCommGroup Q] [Module R Q] [Module.Projective R Q] [IsArtinian R Q] :
    Nonempty (((P × Q) ⧸ Module.jacobson R (P × Q)) ≃ₗ[R]
      (P ⧸ Module.jacobson R P) × (Q ⧸ Module.jacobson R Q)) := by
  let qP : P →ₗ[R] P ⧸ Module.jacobson R P := (Module.jacobson R P).mkQ
  let qQ : Q →ₗ[R] Q ⧸ Module.jacobson R Q := (Module.jacobson R Q).mkQ
  let q : P × Q →ₗ[R] (P ⧸ Module.jacobson R P) × (Q ⧸ Module.jacobson R Q) :=
    qP.prodMap qQ
  let _ : IsArtinian R (P × Q) := by infer_instance
  have hqP : qP.IsProjectiveEnvelope := by
    simpa [qP] using
      (LinearMap.largestSemisimpleQuotientMk_isProjectiveEnvelope (R := R) (P := P))
  have hqQ : qQ.IsProjectiveEnvelope := by
    simpa [qQ] using
      (LinearMap.largestSemisimpleQuotientMk_isProjectiveEnvelope (R := R) (P := Q))
  have hq : q.IsProjectiveEnvelope := by
    simpa [q] using LinearMap.prodMap_isProjectiveEnvelope hqP hqQ
  have hjac_le_prod :
      Module.jacobson R (P × Q) ≤ (Module.jacobson R P).prod (Module.jacobson R Q) := by
    rw [← inf_top_eq (Module.jacobson R P), ← top_inf_eq (Module.jacobson R Q),
      ← Submodule.prod_inf_prod]
    refine le_inf ?_ ?_
    · simpa [Submodule.comap_fst] using
        (Module.le_comap_jacobson (f := LinearMap.fst R P Q))
    · simpa [Submodule.comap_snd] using
        (Module.le_comap_jacobson (f := LinearMap.snd R P Q))
  have hjac_le : Module.jacobson R (P × Q) ≤ LinearMap.ker q := by
    simpa [q, qP, qQ, LinearMap.ker_prodMap] using hjac_le_prod
  have hsurj : Function.Surjective q := by
    intro y
    rcases (Module.jacobson R P).mkQ_surjective y.1 with ⟨x, hx⟩
    rcases (Module.jacobson R Q).mkQ_surjective y.2 with ⟨x', hx'⟩
    refine ⟨(x, x'), ?_⟩
    simp [q, qP, qQ, hx, hx']
  have hker_le : LinearMap.ker q ≤ Module.jacobson R (P × Q) := by
    exact hq.toIsEssential.ker_le_jacobson hsurj
  have hker : Module.jacobson R (P × Q) = LinearMap.ker q := le_antisymm hjac_le hker_le
  refine ⟨?_⟩
  rw [hker]
  simpa [q] using (LinearMap.quotKerEquivOfSurjective q hsurj)

end
