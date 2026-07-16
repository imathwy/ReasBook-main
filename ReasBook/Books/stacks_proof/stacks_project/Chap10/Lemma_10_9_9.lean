import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Limits
import stacks_proof.stacks_project.Chap10.Lemma_10_24_1
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open LocalizedModule

universe u v

noncomputable section

namespace Submonoid

variable {R : Type u} [CommMonoid R]

/-- The elements of a submonoid, viewed as a separate preorder by divisibility. -/
structure Divisibility (S : Submonoid R) where
  val : S

instance (S : Submonoid R) : CoeTC S.Divisibility S := ⟨Divisibility.val⟩

instance (S : Submonoid R) : CoeTC S.Divisibility R := ⟨fun f ↦ (f.val : R)⟩

instance (S : Submonoid R) : CoeTC S S.Divisibility := ⟨Divisibility.mk⟩

@[simp] theorem divisibility_val_mk {S : Submonoid R} (s : S) :
    ((Divisibility.mk s : S.Divisibility) : S) = s := rfl

@[simp] theorem divisibility_coe_mk {S : Submonoid R} (s : S) :
    ((Divisibility.mk s : S.Divisibility) : R) = s := rfl

instance divisibilityLE (S : Submonoid R) : LE S.Divisibility where
  le f g := (f : R) ∣ (g : R)

instance divisibilityPreorder (S : Submonoid R) : Preorder S.Divisibility where
  le := (· ≤ ·)
  le_refl _ := dvd_rfl
  le_trans _ _ _ := dvd_trans

end Submonoid

section

variable {R : Type u} [CommRing R]
variable (S : Submonoid R)
variable (M : Type v) [AddCommGroup M] [Module R M]

/-- If `r` divides `x`, then scalar multiplication by `r` is invertible on `M_x`. -/
private theorem away_moduleEnd_isUnit_of_dvd
    (x r : R) (h : r ∣ x) :
    IsUnit (algebraMap R (Module.End R (LocalizedModule.Away x M)) r) := by
  -- First move the unit statement to the ring localization away from `x`.
  have h' : IsUnit (algebraMap R (Localization.Away x) r) :=
    IsLocalization.Away.isUnit_of_dvd x h
  -- Then transport that unit along the scalar action on the localized module.
  let lsmulAway : Localization.Away x →ₐ[R] Module.End R (LocalizedModule.Away x M) :=
    Algebra.lsmul R R (LocalizedModule.Away x M)
  simpa [Algebra.smul_def] using h'.map lsmulAway

/-- Every element of `powers f` acts invertibly on `M_g` when `f ∣ g`. -/
private theorem away_moduleEnd_isUnit_of_mem_powers_of_dvd
    {f g : S.Divisibility} (h : f ≤ g) (x : Submonoid.powers (f : R)) :
    IsUnit (algebraMap R (Module.End R (LocalizedModule.Away (g : R) M)) x) := by
  -- Reduce to the generator `f`, then take the appropriate power.
  rcases x with ⟨x, ⟨n, rfl⟩⟩
  simpa [map_pow] using
    (away_moduleEnd_isUnit_of_dvd (M := M) (g : R) (f : R) h).pow n

/-- Helper for Lemma 10.9.9: maps out of an away localization are determined by their restriction
to the original module, provided the relevant powers act invertibly on the codomain. -/
private theorem away_linearMap_ext
    {N : Type (max u v)} [AddCommGroup N] [Module R N] (f : S.Divisibility)
    (hN : ∀ x : Submonoid.powers (f : R), IsUnit (algebraMap R (Module.End R N) x))
    {g h : LocalizedModule.Away (f : R) M →ₗ[R] N}
    (hcomp :
      g.comp (LocalizedModule.mkLinearMap (Submonoid.powers (f : R)) M) =
        h.comp (LocalizedModule.mkLinearMap (Submonoid.powers (f : R)) M)) :
    g = h := by
  -- Apply the localization uniqueness principle for maps out of `M_f`.
  exact IsLocalizedModule.ext
    (S := Submonoid.powers (f : R))
    (f := LocalizedModule.mkLinearMap (Submonoid.powers (f : R)) M)
    (M'' := N) hN hcomp

/-- The canonical transition map `M_f → M_g` attached to a divisibility relation `f ≤ g`,
equivalently to a factorization `g = fr`. -/
private noncomputable def away_localization_map {f g : S.Divisibility} (h : f ≤ g) :
    LocalizedModule.Away (f : R) M →ₗ[R] LocalizedModule.Away (g : R) M :=
  LocalizedModule.lift (Submonoid.powers (f : R))
    (LocalizedModule.mkLinearMap (Submonoid.powers (g : R)) M)
    (fun x ↦ away_moduleEnd_isUnit_of_mem_powers_of_dvd (S := S) (M := M) h x)

/-- Identity morphisms in the away-localization diagram act by the identity map. -/
-- Proof sketch: both sides are maps `M_f → M_f` that agree after precomposition with the canonical
-- localization map, so uniqueness in the universal property of `M_f` identifies them.
private theorem away_localization_diagram_map_id (f : S.Divisibility) :
    ModuleCat.ofHom (away_localization_map S M (leOfHom (𝟙 f))) =
      𝟙 (ModuleCat.of R (LocalizedModule.Away (f : R) M)) := by
  apply ModuleCat.hom_ext
  change away_localization_map S M (leOfHom (𝟙 f)) = LinearMap.id
  -- Both maps are determined by their restriction along the canonical map from `M`.
  exact away_linearMap_ext (S := S) (M := M) f
    (fun x ↦ by
      simpa using away_moduleEnd_isUnit_of_mem_powers_of_dvd
        (S := S) (M := M) (leOfHom (𝟙 f)) x)
    (N := LocalizedModule.Away (f : R) M)
    (g := away_localization_map S M (leOfHom (𝟙 f)))
    (h := LinearMap.id) <| by
      -- On generators, both sides are the canonical localization map `M → M_f`.
      simpa [away_localization_map] using
        (LocalizedModule.lift_comp (Submonoid.powers (f : R))
          (LocalizedModule.mkLinearMap (Submonoid.powers (f : R)) M)
          (fun x ↦ away_moduleEnd_isUnit_of_mem_powers_of_dvd
            (S := S) (M := M) (leOfHom (𝟙 f)) x)).trans
            (LinearMap.id_comp _).symm

/-- Composition in the away-localization diagram is given by composition of transition maps. -/
-- Proof sketch: both composites are the unique maps extending the same canonical map out of `M_f`,
-- so the universal property of localization gives the equality.
private theorem away_localization_diagram_map_comp
    {f g h : S.Divisibility} (h₁ : f ⟶ g) (h₂ : g ⟶ h) :
    ModuleCat.ofHom (away_localization_map S M (leOfHom (h₁ ≫ h₂))) =
      ModuleCat.ofHom (away_localization_map S M (leOfHom h₁)) ≫
        ModuleCat.ofHom (away_localization_map S M (leOfHom h₂)) := by
  apply ModuleCat.hom_ext
  change away_localization_map S M (leOfHom (h₁ ≫ h₂)) =
    (away_localization_map S M (leOfHom h₂)).comp (away_localization_map S M (leOfHom h₁))
  -- Again, it is enough to compare the two maps after precomposition with `M → M_f`.
  exact away_linearMap_ext (S := S) (M := M) f
    (fun x ↦ by
      simpa using away_moduleEnd_isUnit_of_mem_powers_of_dvd
        (S := S) (M := M) (leOfHom (h₁ ≫ h₂)) x)
    (N := LocalizedModule.Away (h : R) M)
    (g := away_localization_map S M (leOfHom (h₁ ≫ h₂)))
    (h := (away_localization_map S M (leOfHom h₂)).comp
      (away_localization_map S M (leOfHom h₁))) <| by
      -- Both composites extend the same canonical map `M → M_h`.
      rw [away_localization_map, LinearMap.comp_assoc, away_localization_map, away_localization_map]
      rw [LocalizedModule.lift_comp, LocalizedModule.lift_comp, LocalizedModule.lift_comp]

/-- The diagram `f ↦ M_f` indexed by the divisibility preorder on `S`, where `f ≤ g` means
`f ∣ g`, equivalently `g = fr` for some `r : R`. -/
noncomputable def away_localization_diagram : S.Divisibility ⥤ ModuleCat R :=
  { obj := fun f ↦ ModuleCat.of R (LocalizedModule.Away (f : R) M)
    map := fun {_ _} h ↦
      ModuleCat.ofHom (away_localization_map S M (leOfHom h))
    map_id := fun f ↦ away_localization_diagram_map_id S M f
    map_comp := fun h₁ h₂ ↦ away_localization_diagram_map_comp S M h₁ h₂ }

/-- The canonical map from the away localization `M_f` to the full localization `S⁻¹M`. -/
private noncomputable abbrev away_localization_to_localizedModule (f : S.Divisibility) :
    LocalizedModule.Away (f : R) M →ₗ[R] LocalizedModule S M :=
  LocalizedModule.liftOfLE (Submonoid.powers (f : R)) S
    (Submonoid.powers_le.2 (show (f : R) ∈ S from (f : S).2))

/-- The maps `M_f → S⁻¹M` are compatible with the transition maps of the away-localization diagram. -/
-- Proof sketch: both sides are maps `M_f → S⁻¹M` extending the same map from `M`, so the universal
-- property of `M_f` forces them to agree.
@[reassoc]
private theorem away_localization_to_total_naturality {f g : S.Divisibility} (h : f ⟶ g) :
    (away_localization_diagram S M).map h ≫
        ModuleCat.ofHom (away_localization_to_localizedModule S M g) =
      ModuleCat.ofHom (away_localization_to_localizedModule S M f) := by
  apply ModuleCat.hom_ext
  change (away_localization_to_localizedModule S M g).comp
      (away_localization_map S M (leOfHom h)) =
    away_localization_to_localizedModule S M f
  -- Compare the two maps `M_f → S⁻¹M` on the dense image of `M`.
  exact away_linearMap_ext (S := S) (M := M) f
    (fun x ↦ by
      simpa using IsLocalizedModule.map_units
        (S := S)
        (f := LocalizedModule.mkLinearMap S M)
        ⟨x.1, Submonoid.powers_le.2 (show (f : R) ∈ S from (f : S).2) x.2⟩)
    (N := LocalizedModule S M)
    (g := (away_localization_to_localizedModule S M g).comp
      (away_localization_map S M (leOfHom h)))
    (h := away_localization_to_localizedModule S M f) <| by
      -- Both maps restrict to the same canonical localization map from `M`.
      rw [LinearMap.comp_assoc, away_localization_map, LocalizedModule.lift_comp]
      rw [away_localization_to_localizedModule]
      erw [IsLocalizedModule.liftOfLE_comp]
      rw [away_localization_to_localizedModule]
      erw [IsLocalizedModule.liftOfLE_comp]

/-- The cocone on the diagram `f ↦ M_f` with vertex the full localization `S⁻¹M`. -/
noncomputable def away_localization_cocone :
    Cocone (away_localization_diagram S M) where
  pt := ModuleCat.of R (LocalizedModule S M)
  ι :=
    { app := fun f ↦ ModuleCat.ofHom (away_localization_to_localizedModule S M f)
      naturality := fun _ _ h ↦ away_localization_to_total_naturality S M h }

/-- Helper for Lemma 10.9.9: the transition map along a divisibility relation sends the basic
generator `m / f` to the transported basic generator `(r • m) / g` whenever `g = fr`. -/
private theorem away_localization_map_mk_pow_one
    {f g : S.Divisibility} (h : f ≤ g) {r : R} (hr : (g : R) = (f : R) * r) (m : M) :
    away_localization_map S M h (LocalizedModule.mk m (Submonoid.pow (f : R) 1)) =
      LocalizedModule.mk (r • m) (Submonoid.pow (g : R) 1) := by
  -- Evaluate the localization lift on the basic generator `m / f`.
  rw [away_localization_map, LocalizedModule.lift_mk]
  -- Identify the inverse action with the expected transported fraction.
  apply (Module.End.algebraMap_isUnit_inv_apply_eq_iff
    (R := R)
    (S := R)
    (M := LocalizedModule.Away (g : R) M)
    (x := (((Submonoid.pow (f : R) 1 : Submonoid.powers (f : R)) : R)))
    (away_moduleEnd_isUnit_of_mem_powers_of_dvd (S := S) (M := M) h
      (Submonoid.pow (f : R) 1))
    _ _).2
  -- Multiplying by `f` turns the target fraction back into `m / 1`.
  simp only [LocalizedModule.mkLinearMap_apply]
  rw [hr]
  simpa [LocalizedModule.smul'_mk, Submonoid.smul_def, mul_smul] using
    (LocalizedModule.mk_cancel (s := Submonoid.pow ((f : R) * r) 1) (m := m)).symm

/-- Helper for Lemma 10.9.9: cocone naturality transports the basic generator `m / f` to the
basic generator `(r • m) / g` in the target component whenever `g = fr`. -/
private theorem cocone_app_mk_pow_one_transport
    (c : Cocone (away_localization_diagram S M)) {f g : S.Divisibility} (h : f ≤ g)
    {r : R} (hr : (g : R) = (f : R) * r) (m : M) :
    c.ι.app f (LocalizedModule.mk m (Submonoid.pow (f : R) 1)) =
      c.ι.app g (LocalizedModule.mk (r • m) (Submonoid.pow (g : R) 1)) := by
  -- Move along the cocone edge, then rewrite the diagram map on the basic generator.
  have hw := ConcreteCategory.congr_hom (c.w (homOfLE h))
    (LocalizedModule.mk m (Submonoid.pow (f : R) 1))
  change c.ι.app g
      (away_localization_map S M h (LocalizedModule.mk m (Submonoid.pow (f : R) 1))) =
    c.ι.app f (LocalizedModule.mk m (Submonoid.pow (f : R) 1)) at hw
  rw [away_localization_map_mk_pow_one (S := S) (M := M) h hr] at hw
  exact hw.symm

/-- Helper for Lemma 10.9.9: transition maps preserve fractions whose denominator is `1`. -/
private theorem away_localization_map_mk_one
    {f g : S.Divisibility} (h : f ≤ g) (m : M) :
    away_localization_map S M h (LocalizedModule.mk m (1 : Submonoid.powers (f : R))) =
      LocalizedModule.mk m (1 : Submonoid.powers (g : R)) := by
  -- Evaluate the localization lift on the generator `m / 1`.
  rw [away_localization_map, LocalizedModule.lift_mk_one]
  rfl

/-- Helper for Lemma 10.9.9: cocone naturality transports fractions with denominator `1`. -/
private theorem cocone_app_mk_one_transport
    (c : Cocone (away_localization_diagram S M)) {f g : S.Divisibility} (h : f ≤ g) (m : M) :
    c.ι.app f (LocalizedModule.mk m (1 : Submonoid.powers (f : R))) =
      c.ι.app g (LocalizedModule.mk m (1 : Submonoid.powers (g : R))) := by
  -- Move along the cocone edge, then rewrite the diagram map on the denominator-`1` fraction.
  have hw := ConcreteCategory.congr_hom (c.w (homOfLE h))
    (LocalizedModule.mk m (1 : Submonoid.powers (f : R)))
  change c.ι.app g
      (away_localization_map S M h (LocalizedModule.mk m (1 : Submonoid.powers (f : R)))) =
    c.ι.app f (LocalizedModule.mk m (1 : Submonoid.powers (f : R))) at hw
  rw [away_localization_map_mk_one (S := S) (M := M) h] at hw
  exact hw.symm

/-- Helper for Lemma 10.9.9: if the target index is the actual denominator `f^(n+1)`, then the
transition map sends `m / f^(n+1)` to the basic generator `m / g`. -/
private theorem away_localization_map_mk_power_denominator
    {f : S.Divisibility} {g : S} (h : f ≤ (g : S.Divisibility))
    {n : ℕ} (hg : (g : R) = (f : R) ^ (n + 1)) (m : M) :
    away_localization_map S M h (LocalizedModule.mk m (Submonoid.pow (f : R) (n + 1))) =
      LocalizedModule.mk m (Submonoid.pow (g : R) 1) := by
  -- Evaluate the localization lift on `m / f^(n+1)` and cancel the matching denominator `g`.
  rw [away_localization_map, LocalizedModule.lift_mk]
  apply (Module.End.algebraMap_isUnit_inv_apply_eq_iff
    (R := R)
    (S := R)
    (M := LocalizedModule.Away (g : R) M)
    (x := (((Submonoid.pow (f : R) (n + 1) : Submonoid.powers (f : R)) : R)))
    (away_moduleEnd_isUnit_of_mem_powers_of_dvd (S := S) (M := M) h
      (Submonoid.pow (f : R) (n + 1)))
    _ _).2
  simp only [LocalizedModule.mkLinearMap_apply, LocalizedModule.smul'_mk]
  convert (LocalizedModule.mk_cancel (s := Submonoid.pow (g : R) 1) (m := m)).symm using 1
  simp [Submonoid.smul_def, hg]

/-- Helper for Lemma 10.9.9: cocone naturality transports `m / f^(n+1)` to the matching basic
generator in the denominator component. -/
private theorem cocone_app_mk_power_denominator_transport
    (c : Cocone (away_localization_diagram S M)) {f : S.Divisibility} {g : S}
    (h : f ≤ (g : S.Divisibility)) {n : ℕ} (hg : (g : R) = (f : R) ^ (n + 1)) (m : M) :
    c.ι.app f (LocalizedModule.mk m (Submonoid.pow (f : R) (n + 1))) =
      c.ι.app g (LocalizedModule.mk m (Submonoid.pow (g : R) 1)) := by
  -- Move along the cocone edge, then rewrite the diagram map on the chosen denominator.
  have hw := ConcreteCategory.congr_hom (c.w (homOfLE h))
    (LocalizedModule.mk m (Submonoid.pow (f : R) (n + 1)))
  change c.ι.app g
      (away_localization_map S M h (LocalizedModule.mk m (Submonoid.pow (f : R) (n + 1)))) =
    c.ι.app f (LocalizedModule.mk m (Submonoid.pow (f : R) (n + 1))) at hw
  rw [away_localization_map_mk_power_denominator (S := S) (M := M) h hg] at hw
  exact hw.symm

/-- Helper for Lemma 10.9.9: fractions in `M_f` with the same denominator `f` add by adding their
numerators. -/
private theorem away_mk_pow_one_add (f : S.Divisibility) (m₁ m₂ : M) :
    LocalizedModule.mk (m₁ + m₂) (Submonoid.pow (f : R) 1) =
      LocalizedModule.mk m₁ (Submonoid.pow (f : R) 1) +
        LocalizedModule.mk m₂ (Submonoid.pow (f : R) 1) := by
  -- Reuse the standard same-denominator addition formula for localized modules.
  simpa [IsLocalizedModule.mk_eq_mk'] using
    (IsLocalizedModule.mk'_add
      (S := Submonoid.powers (f : R))
      (f := LocalizedModule.mkLinearMap (Submonoid.powers (f : R)) M)
      m₁ m₂ (Submonoid.pow (f : R) 1))

/-- Equivalent representatives in the localization define the same cocone evaluation. -/
private theorem localized_module_desc_wd (c : Cocone (away_localization_diagram S M))
    (p p' : M × S) (h : p ≈ p') :
    c.ι.app p.2 (LocalizedModule.mk p.1 (Submonoid.pow (p.2 : R) 1)) =
      c.ι.app p'.2 (LocalizedModule.mk p'.1 (Submonoid.pow (p'.2 : R) 1)) := by
  -- Route correction: transport both representatives to one common away-localization component.
  rcases h with ⟨u, hu⟩
  let q : S.Divisibility := (p.2 * p'.2 * u : S)
  have hpq : (p.2 : R) ∣ (q : R) := by
    refine ⟨((p'.2 * u : S) : R), ?_⟩
    simpa [q, mul_assoc]
  have hp'q : (p'.2 : R) ∣ (q : R) := by
    refine ⟨((p.2 * u : S) : R), ?_⟩
    simpa [q, mul_assoc, mul_left_comm, mul_comm]
  -- Cocone naturality identifies both sides with basic generators in the `q`-component.
  rw [cocone_app_mk_pow_one_transport (S := S) (M := M) (c := c) (f := p.2) (g := q) hpq
      (r := ((p'.2 * u : S) : R))
      (by simpa [q, mul_assoc]),
    cocone_app_mk_pow_one_transport (S := S) (M := M) (c := c) (f := p'.2) (g := q) hp'q
      (r := ((p.2 * u : S) : R))
      (by simp [q, mul_left_comm, mul_comm])]
  -- The original localization relation is exactly the equality of transported numerators.
  exact congrArg
    (fun x ↦ c.ι.app q (LocalizedModule.mk x (Submonoid.pow (q : R) 1)))
    (by simpa [Submonoid.smul_def, mul_smul, mul_assoc, mul_left_comm, mul_comm] using hu)

/-- The universal map from the total localization to the vertex of a cocone on the away
localization diagram, defined on a fraction `m / s` by evaluating the `s`-component of the cocone
on the corresponding element of `M_s`. -/
private noncomputable def localized_module_desc_fun (c : Cocone (away_localization_diagram S M)) :
    LocalizedModule S M → c.pt :=
  fun x ↦
    x.liftOn
      (fun p ↦ c.ι.app p.2 (LocalizedModule.mk p.1 (Submonoid.pow (p.2 : R) 1)))
      (localized_module_desc_wd S M c)

@[simp]
private theorem localized_module_desc_fun_mk (c : Cocone (away_localization_diagram S M))
    (m : M) (s : S) :
    localized_module_desc_fun S M c (LocalizedModule.mk m s) =
      c.ι.app s (LocalizedModule.mk m (Submonoid.pow (s : R) 1)) := by
  -- Evaluate the quotient-descended function on the canonical representative `(m, s)`.
  simp [localized_module_desc_fun, LocalizedModule.liftOn_mk]

/-- The cocone-descending map out of `S⁻¹M` preserves addition. -/
private theorem localized_module_desc_fun_map_add
    (c : Cocone (away_localization_diagram S M)) (x y : LocalizedModule S M) :
    localized_module_desc_fun S M c (x + y) =
      localized_module_desc_fun S M c x + localized_module_desc_fun S M c y := by
  -- Reduce to two explicit fractions and transport them to the common component `M_(ss')`.
  refine LocalizedModule.induction_on₂ ?_ x y
  intro m m' s s'
  let q : S.Divisibility := (s * s' : S)
  have hsq : (s : R) ∣ (q : R) := by
    refine ⟨(s' : R), ?_⟩
    simpa [q]
  have hs'q : (s' : R) ∣ (q : R) := by
    refine ⟨(s : R), ?_⟩
    simpa [q, mul_comm]
  have hs :
      c.ι.app s (LocalizedModule.mk m (Submonoid.pow (s : R) 1)) =
        c.ι.app q (LocalizedModule.mk ((s' : R) • m) (Submonoid.pow (q : R) 1)) :=
    cocone_app_mk_pow_one_transport (S := S) (M := M) (c := c) (f := s) (g := q) hsq
      (r := (s' : R)) (by simpa [q]) m
  have hs' :
      c.ι.app s' (LocalizedModule.mk m' (Submonoid.pow (s' : R) 1)) =
        c.ι.app q (LocalizedModule.mk ((s : R) • m') (Submonoid.pow (q : R) 1)) :=
    cocone_app_mk_pow_one_transport (S := S) (M := M) (c := c) (f := s') (g := q) hs'q
      (r := (s : R)) (by simpa [q, mul_comm]) m'
  rw [LocalizedModule.mk_add_mk, localized_module_desc_fun_mk, localized_module_desc_fun_mk,
    localized_module_desc_fun_mk]
  -- Once both summands live in the same away localization, additivity is ordinary linearity.
  let z1 : ↥c.pt := c.ι.app s (LocalizedModule.mk m (Submonoid.pow (s : R) 1))
  let z2 : ↥c.pt := c.ι.app s' (LocalizedModule.mk m' (Submonoid.pow (s' : R) 1))
  have hsum :
      c.ι.app q (LocalizedModule.mk ((s' : R) • m + (s : R) • m')
        (Submonoid.pow (q : R) 1)) = z1 + z2 := by
    calc
      c.ι.app q (LocalizedModule.mk ((s' : R) • m + (s : R) • m')
          (Submonoid.pow (q : R) 1)) =
        ModuleCat.Hom.hom (c.ι.app q)
          (LocalizedModule.mk ((s' : R) • m) (Submonoid.pow (q : R) 1)) +
            ModuleCat.Hom.hom (c.ι.app q)
              (LocalizedModule.mk ((s : R) • m') (Submonoid.pow (q : R) 1)) := by
          rw [away_mk_pow_one_add (S := S) (M := M) q]
          exact (ModuleCat.Hom.hom (c.ι.app q)).map_add
            (LocalizedModule.mk ((s' : R) • m) (Submonoid.pow (q : R) 1))
            (LocalizedModule.mk ((s : R) • m') (Submonoid.pow (q : R) 1))
      _ = (ConcreteCategory.hom (c.ι.app q))
            (LocalizedModule.mk ((s' : R) • m) (Submonoid.pow (q : R) 1)) +
          (ConcreteCategory.hom (c.ι.app q))
            (LocalizedModule.mk ((s : R) • m') (Submonoid.pow (q : R) 1)) := by
          rfl
      _ = z1 + z2 := by
        rw [← hs, ← hs']
        change z1 + z2 = z1 + z2
        rfl
  simpa [q, z1, z2] using hsum

/-- The cocone-descending map out of `S⁻¹M` preserves scalar multiplication. -/
private theorem localized_module_desc_fun_map_smul
    (c : Cocone (away_localization_diagram S M)) (r : R) (x : LocalizedModule S M) :
    localized_module_desc_fun S M c (r • x) =
      r • localized_module_desc_fun S M c x := by
  -- Reduce to one fraction and use linearity in the chosen cocone component.
  refine LocalizedModule.induction_on ?_ x
  intro m s
  rw [LocalizedModule.smul'_mk, localized_module_desc_fun_mk, localized_module_desc_fun_mk]
  simpa [LocalizedModule.smul'_mk] using
    map_smul (ConcreteCategory.hom (c.ι.app s)) r
      (LocalizedModule.mk m (Submonoid.pow (s : R) 1))

/-- The universal morphism from the total localization cocone to an arbitrary cocone on the away
localization diagram. -/
private noncomputable def localized_module_desc (c : Cocone (away_localization_diagram S M)) :
    LocalizedModule S M →ₗ[R] c.pt where
  toFun := localized_module_desc_fun S M c
  map_add' := localized_module_desc_fun_map_add S M c
  map_smul' := localized_module_desc_fun_map_smul S M c

@[simp]
private theorem localized_module_desc_mk (c : Cocone (away_localization_diagram S M))
    (m : M) (s : S) :
    localized_module_desc S M c (LocalizedModule.mk m s) =
      c.ι.app s (LocalizedModule.mk m (Submonoid.pow (s : R) 1)) := by
  -- The linear desc map agrees with its underlying function on generators.
  simpa [localized_module_desc] using localized_module_desc_fun_mk (S := S) (M := M) c m s

/-- Helper for Lemma 10.9.9: the canonical map `M_f → S⁻¹M` preserves denominator-`1` fractions. -/
private theorem away_localization_to_localizedModule_mk_one
    (f : S.Divisibility) (m : M) :
    away_localization_to_localizedModule S M f
      (LocalizedModule.mk m (1 : Submonoid.powers (f : R))) =
    LocalizedModule.mk m (1 : S) := by
  -- Route correction: compute the total-localization map directly on the image of `m : M`.
  change
    IsLocalizedModule.liftOfLE
        (Submonoid.powers (f : R)) S
        (Submonoid.powers_le.2 (show (f : R) ∈ S from (f : S).2))
        (LocalizedModule.mkLinearMap (Submonoid.powers (f : R)) M)
        (LocalizedModule.mkLinearMap S M)
        ((LocalizedModule.mkLinearMap (Submonoid.powers (f : R)) M) m) =
      LocalizedModule.mk m (1 : S)
  -- The universal property says that `liftOfLE` agrees with the canonical map on `M`.
  simpa [LocalizedModule.mkLinearMap_apply] using
    (IsLocalizedModule.liftOfLE_apply
      (S₁ := Submonoid.powers (f : R))
      (S₂ := S)
      (h := Submonoid.powers_le.2 (show (f : R) ∈ S from (f : S).2))
      (f₁ := LocalizedModule.mkLinearMap (Submonoid.powers (f : R)) M)
      (f₂ := LocalizedModule.mkLinearMap S M) m)

/-- Helper for Lemma 10.9.9: the canonical map `M_f → S⁻¹M` sends `m / f^(n+1)` to the total
localization fraction with the same denominator index `g = f^(n+1)`. -/
private theorem away_localization_to_localizedModule_mk_power_denominator
    {f : S.Divisibility} {g : S} {n : ℕ} (hg : (g : R) = (f : R) ^ (n + 1)) (m : M) :
    away_localization_to_localizedModule S M f
      (LocalizedModule.mk m (Submonoid.pow (f : R) (n + 1))) =
    LocalizedModule.mk m g := by
  -- Rewrite both sides into the `mk'` normal form expected by `liftOfLE_mk'`.
  rw [IsLocalizedModule.mk_eq_mk', IsLocalizedModule.mk_eq_mk']
  -- The lift preserves the numerator and embeds the denominator into `S`.
  let g' : S :=
    ⟨(f : R) ^ (n + 1),
      Submonoid.powers_le.2 (show (f : R) ∈ S from (f : S).2) ⟨n + 1, rfl⟩⟩
  have hg' : g' = g := Subtype.ext <| by simpa [g'] using hg.symm
  -- After identifying the embedded denominator with `g`, the computation is immediate.
  rw [← hg']
  simpa [away_localization_to_localizedModule, g'] using
    (IsLocalizedModule.liftOfLE_mk'
      (S₁ := Submonoid.powers (f : R))
      (S₂ := S)
      (h := Submonoid.powers_le.2 (show (f : R) ∈ S from (f : S).2))
      (f₁ := LocalizedModule.mkLinearMap (Submonoid.powers (f : R)) M)
      (f₂ := LocalizedModule.mkLinearMap S M)
      m (Submonoid.pow (f : R) (n + 1)))

/-- The universal map from `S⁻¹M` to a cocone vertex factors the canonical cocone maps. -/
private theorem localized_module_desc_fac
    (c : Cocone (away_localization_diagram S M)) (f : S.Divisibility) :
    ModuleCat.ofHom (away_localization_to_localizedModule S M f) ≫
        ModuleCat.ofHom (localized_module_desc S M c) =
      c.ι.app f := by
  apply ModuleCat.hom_ext
  ext x
  -- Route correction: once the total-localization map is computed on generators, factorization is
  -- a denominator split inside `M_f`.
  refine LocalizedModule.induction_on ?_ x
  intro m s
  rcases s.2 with ⟨n, hn⟩
  have hs : s = Submonoid.pow (f : R) n := by
    apply Subtype.ext
    simpa [hn]
  subst s
  cases n with
  | zero =>
      -- The denominator-`1` branch lands in the `1`-component of the cocone.
      change
        localized_module_desc S M c
            (away_localization_to_localizedModule S M f
              (LocalizedModule.mk m (Submonoid.pow (f : R) 0))) =
          c.ι.app f (LocalizedModule.mk m (Submonoid.pow (f : R) 0))
      rw [show Submonoid.pow (f : R) 0 = (1 : Submonoid.powers (f : R)) by
        ext
        simp]
      rw [away_localization_to_localizedModule_mk_one, localized_module_desc_mk]
      rw [show Submonoid.pow ((1 : S) : R) 1 = (1 : Submonoid.powers ((1 : S) : R)) by
        ext
        simp]
      simpa using
        (cocone_app_mk_one_transport (S := S) (M := M) (c := c)
          (f := (1 : S)) (g := f) (show (1 : R) ∣ (f : R) from one_dvd _) m)
  | succ n =>
      -- For a positive power denominator, choose the actual denominator component in `S`.
      let g : S :=
        ⟨(f : R) ^ (n + 1),
          Submonoid.powers_le.2 (show (f : R) ∈ S from (f : S).2) ⟨n + 1, rfl⟩⟩
      have hg : (g : R) = (f : R) ^ (n + 1) := rfl
      have hfg : f ≤ (g : S.Divisibility) := by
        refine ⟨(f : R) ^ n, ?_⟩
        simp [g, pow_succ, mul_comm]
      change
        localized_module_desc S M c
            (away_localization_to_localizedModule S M f
              (LocalizedModule.mk m (Submonoid.pow (f : R) (n + 1)))) =
          c.ι.app f (LocalizedModule.mk m (Submonoid.pow (f : R) (n + 1)))
      rw [away_localization_to_localizedModule_mk_power_denominator (S := S) (M := M)
          (f := f) (g := g) (n := n) hg, localized_module_desc_mk]
      simpa [g] using
        (cocone_app_mk_power_denominator_transport (S := S) (M := M) (c := c)
          (f := f) (g := g) hfg (n := n) hg m).symm

/-- Any cocone on the away-localization diagram receives a unique morphism from the canonical
localization cocone. -/
private theorem away_localization_cocone_existsUnique_desc
    (c : Cocone (away_localization_diagram S M)) :
    ∃! t : (away_localization_cocone S M).pt ⟶ c.pt,
      ∀ f : S.Divisibility, (away_localization_cocone S M).ι.app f ≫ t = c.ι.app f := by
  refine ⟨ModuleCat.ofHom (localized_module_desc S M c), ?_, ?_⟩
  · -- The descended map is compatible with every cocone leg by the factorization lemma.
    exact localized_module_desc_fac (S := S) (M := M) c
  · intro t ht
    apply ModuleCat.hom_ext
    ext x
    -- The full localization is generated by basic fractions `m / s`.
    refine LocalizedModule.induction_on ?_ x
    intro m s
    have hs := LinearMap.congr_fun (ModuleCat.hom_ext_iff.mp (ht s))
      (LocalizedModule.mk m (Submonoid.pow (s : R) 1))
    change
      t
          (away_localization_to_localizedModule S M s
            (LocalizedModule.mk m (Submonoid.pow (s : R) 1))) =
        c.ι.app s (LocalizedModule.mk m (Submonoid.pow (s : R) 1)) at hs
    rw [away_localization_to_localizedModule_mk_power_denominator
      (S := S) (M := M) (f := s) (g := s) (n := 0) (by simp)] at hs
    simpa [localized_module_desc_mk] using hs

/-- Lemma 10.9.9: the localization `LocalizedModule S M` is the colimit of the diagram
`f ↦ LocalizedModule.Away f M` indexed by `S`, where `f ≤ g` means `g = fr` for some `r : R` and
the transition map is the canonical map sending `m / f^n` to `r^n m / g^n`. -/
@[stacks 00CR]
noncomputable def localized_module_is_colimit_away_localization_diagram :
    IsColimit (away_localization_cocone S M) :=
  IsColimit.ofExistsUnique (away_localization_cocone_existsUnique_desc S M)

/-- The universal morphism from the canonical localization cocone restricts to the given cocone
on each away localization. -/
-- Proof sketch: this is the `fac` field of
-- `localized_module_is_colimit_away_localization_diagram`.
@[reassoc, simp]
theorem localized_module_is_colimit_away_localization_diagram_fac
    (s : Cocone (away_localization_diagram S M)) (f : S.Divisibility) :
    (away_localization_cocone S M).ι.app f ≫
      (localized_module_is_colimit_away_localization_diagram S M).desc s =
        s.ι.app f := by
  -- This is the `fac` field of the colimit structure just constructed.
  simpa using (localized_module_is_colimit_away_localization_diagram S M).fac s f

end
