import Mathlib.RingTheory.LocalProperties.Exactness

-- Declarations for this item will be appended below by the statement pipeline.

open LinearMap LocalizedModule

universe u v w

noncomputable section

section

variable {R : Type u} [CommSemiring R]
variable {ι : Type w}

/- Domain-style sampling:
- primary domain: commutative algebra of localization exactness on a standard principal-open cover;
- sampled owner declarations:
  `LocalizedModule.mkLinearMap`,
  `LocalizedModule.lift`,
  `injective_of_localized_span`,
  `exact_of_localized_span`;
- best owner abstraction: the localization-exactness owner theorems on a span-cover, with the
  family map and overlap-difference map as the source-facing bridge data for this particular
  two-step Cech complex;
- source/core/bridge triage:
  `source-facing`: the two explicit maps `α` and `β` in the localization glueing sequence;
  `core/canonical`: `injective_of_localized_span` and `exact_of_localized_span`;
  `bridge/view`: the canonical comparison maps built from `mkLinearMap` and `lift`;
- primitive data: the family `f : ι → R` and the canonical maps obtained from localization away
  from the elements `f i`;
- derived API: the injectivity and exactness statement `away_localization_glueing_exact`.
-/

local notation "Away" => LocalizedModule.Away

/-- The canonical map from `M` to the finite family of away localizations `M_(f_i)`. -/
abbrev awayLocalizationFamilyMap
    (M : Type v) [AddCommGroup M] [Module R M] (f : ι → R) :
    M →ₗ[R] ∀ i : ι, Away (f i) M :=
  LinearMap.pi fun i ↦ mkLinearMap (.powers (f i)) M

private theorem awayModuleEnd_isUnit_of_dvd
    (M : Type v) [AddCommGroup M] [Module R M] (x r : R) (h : r ∣ x) :
    IsUnit (algebraMap R (Module.End R (Away x M)) r) := by
  have h' : IsUnit (algebraMap R (Localization.Away x) r) :=
    IsLocalization.Away.isUnit_of_dvd x h
  let lsmulAway : Localization.Away x →ₐ[R] Module.End R (Away x M) :=
    Algebra.lsmul R R (Away x M)
  simpa [Algebra.smul_def] using
    h'.map lsmulAway

/-- The pairwise compatibility map for a finite family of away localizations. -/
def awayLocalizationCompatibilityMap
    (M : Type v) [AddCommGroup M] [Module R M] (f : ι → R) :
    (∀ i : ι, Away (f i) M) →ₗ[R] ∀ i : ι, ∀ j : ι, Away (f i * f j) M :=
  LinearMap.pi fun i ↦ LinearMap.pi fun j ↦
    (LocalizedModule.lift (.powers (f i))
      (mkLinearMap (.powers (f i * f j)) M)
      (fun x ↦ by
        rcases (Submonoid.mem_powers_iff x.1 (f i)).mp x.2 with ⟨n, hn⟩
        have hfi :
            IsUnit (algebraMap R (Module.End R (Away (f i * f j) M)) (f i)) :=
          awayModuleEnd_isUnit_of_dvd M (f i * f j) (f i) (dvd_mul_right _ _)
        simpa [← hn] using hfi.pow n)).comp (LinearMap.proj i) -
    (LocalizedModule.lift (.powers (f j))
      (mkLinearMap (.powers (f i * f j)) M)
      (fun x ↦ by
        rcases (Submonoid.mem_powers_iff x.1 (f j)).mp x.2 with ⟨n, hn⟩
        have hfj :
            IsUnit (algebraMap R (Module.End R (Away (f i * f j) M)) (f j)) :=
          awayModuleEnd_isUnit_of_dvd M (f i * f j) (f j) (dvd_mul_left _ _)
        simpa [← hn] using hfj.pow n)).comp (LinearMap.proj j)

end

section

variable {R : Type u} [CommSemiring R]
variable {ι : Type w} [Finite ι]

-- Proof sketch: apply `injective_of_localized_span` and `exact_of_localized_span` to the canonical
-- maps `α` and `β` from the statement using the covering hypothesis
-- `Ideal.span (Set.range f) = ⊤`. After localizing at each `f i`, the statement reduces via the
-- canonical comparison maps for iterated localizations to the trivial case where one generator is
-- a unit, exactly as in the Stacks proof after passing to a localization where some `f i` becomes
-- `1`.
/-- Lemma 10.24.1: if the finite family `f : ι → R` generates the unit ideal, then the
sequence `0 → M → ∏ i, M_(f_i) → ∏ i j, M_(f_i f_j)` with `α(m) = (m/1)_i` and
`β((m_i)_i) = (m_i|_(f_i f_j) - m_j|_(f_i f_j))_(i,j)` is exact. Because the indexing sets are
finite, this is the finite-product translation of the source's direct-sum exact sequence. -/
theorem away_localization_glueing_exact
    (M : Type v) [AddCommGroup M] [Module R M] (f : ι → R) (hf : Ideal.span (Set.range f) = ⊤) :
    Function.Injective (awayLocalizationFamilyMap M f) ∧
      Function.Exact (awayLocalizationFamilyMap M f) (awayLocalizationCompatibilityMap M f) := sorry

end
