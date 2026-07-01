import stacks_project.Chap10.Lemma_10_24_1

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

/-- The canonical transition map `M_f → M_g` attached to a divisibility relation `f ≤ g`,
equivalently to a factorization `g = fr`. -/
private noncomputable def away_localization_map {f g : S.Divisibility} (h : f ≤ g) :
    LocalizedModule.Away (f : R) M →ₗ[R] LocalizedModule.Away (g : R) M :=
  LocalizedModule.liftOfLE (Submonoid.powers (f : R)) (Submonoid.powers (g : R))
    (Submonoid.powers_le.mpr h)

/-- Identity morphisms in the away-localization diagram act by the identity map. -/
-- Proof sketch: both sides are maps `M_f → M_f` that agree after precomposition with the canonical
-- localization map, so uniqueness in the universal property of `M_f` identifies them.
private theorem away_localization_diagram_map_id (f : S.Divisibility) :
    ModuleCat.ofHom (away_localization_map S M (leOfHom (𝟙 f))) =
      𝟙 (ModuleCat.of R (LocalizedModule.Away (f : R) M)) := sorry

/-- Composition in the away-localization diagram is given by composition of transition maps. -/
-- Proof sketch: both composites are the unique maps extending the same canonical map out of `M_f`,
-- so the universal property of localization gives the equality.
private theorem away_localization_diagram_map_comp
    {f g h : S.Divisibility} (h₁ : f ⟶ g) (h₂ : g ⟶ h) :
    ModuleCat.ofHom (away_localization_map S M (leOfHom (h₁ ≫ h₂))) =
      ModuleCat.ofHom (away_localization_map S M (leOfHom h₁)) ≫
        ModuleCat.ofHom (away_localization_map S M (leOfHom h₂)) := sorry

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
      ModuleCat.ofHom (away_localization_to_localizedModule S M f) := sorry

/-- The cocone on the diagram `f ↦ M_f` with vertex the full localization `S⁻¹M`. -/
noncomputable def away_localization_cocone :
    Cocone (away_localization_diagram S M) where
  pt := ModuleCat.of R (LocalizedModule S M)
  ι :=
    { app := fun f ↦ ModuleCat.ofHom (away_localization_to_localizedModule S M f)
      naturality := fun _ _ h ↦ by
        simpa using away_localization_to_total_naturality S M h }

private theorem localized_module_desc_wd (c : Cocone (away_localization_diagram S M))
    (p p' : M × S) (h : p ≈ p') :
    c.ι.app p.2 (LocalizedModule.mk p.1 (Submonoid.pow (p.2 : R) 1)) =
      c.ι.app p'.2 (LocalizedModule.mk p'.1 (Submonoid.pow (p'.2 : R) 1)) := by
  sorry

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
  exact LocalizedModule.liftOn_mk (localized_module_desc_wd S M c) m s

private theorem localized_module_desc_fun_map_add
    (c : Cocone (away_localization_diagram S M)) (x y : LocalizedModule S M) :
    localized_module_desc_fun S M c (x + y) =
      localized_module_desc_fun S M c x + localized_module_desc_fun S M c y := by
  sorry

private theorem localized_module_desc_fun_map_smul
    (c : Cocone (away_localization_diagram S M)) (r : R) (x : LocalizedModule S M) :
    localized_module_desc_fun S M c (r • x) =
      r • localized_module_desc_fun S M c x := by
  sorry

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
      c.ι.app s (LocalizedModule.mk m (Submonoid.pow (s : R) 1)) :=
  localized_module_desc_fun_mk S M c m s

private theorem localized_module_desc_fac
    (c : Cocone (away_localization_diagram S M)) (f : S.Divisibility) :
    ModuleCat.ofHom (away_localization_to_localizedModule S M f) ≫
        ModuleCat.ofHom (localized_module_desc S M c) =
      c.ι.app f := by
  sorry

/-- Any cocone on the away-localization diagram receives a unique morphism from the canonical
localization cocone. -/
private theorem away_localization_cocone_existsUnique_desc
    (c : Cocone (away_localization_diagram S M)) :
    ∃! t : (away_localization_cocone S M).pt ⟶ c.pt,
      ∀ f : S.Divisibility, (away_localization_cocone S M).ι.app f ≫ t = c.ι.app f := by
  sorry

/-- Lemma 10.9.9: the localization `LocalizedModule S M` is the colimit of the diagram
`f ↦ LocalizedModule.Away f M` indexed by `S`, where `f ≤ g` means `g = fr` for some `r : R` and
the transition map is the canonical map sending `m / f^n` to `r^n m / g^n`. -/
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
        s.ι.app f :=
  (localized_module_is_colimit_away_localization_diagram S M).fac s f

end
