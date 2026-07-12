import Mathlib
import StacksProject_2024.Chap10.Lemma_10_17_6
import StacksProject_2024.Chap10.Lemma_10_17_7
import StacksProject_2024.Chap10.Lemma_10_68_6
import StacksProject_2024.Chap10.Lemma_10_106_3
import StacksProject_2024.Chap10.Lemma_10_106_4
import StacksProject_2024.Chap10.Lemma_10_106_7
import StacksProject_2024.Chap15.Lemma_15_47_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open PrimeSpectrum
open RingTheory Sequence IsLocalRing
open scoped PrimeSpectrum

section

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/-- Helper for Lemma 15.47.3: an open subset of `Spec (R ⧸ p)` whose image points are already
regular in `Spec R` yields an ambient open trace on `V(p)` contained in the regular locus. -/
lemma exists_nonempty_open_regular_subset_zeroLocus_of_homeomorph_image
    (p : PrimeSpectrum R)
    {V : Set (PrimeSpectrum (R ⧸ p.asIdeal))}
    (hV_open : IsOpen V) (hV_nonempty : V.Nonempty)
    (hV_reg :
    ∀ x ∈ V,
        ((Ideal.primeSpectrum_quotient_homeomorph_zeroLocus p.asIdeal x).1) ∈ Reg(Spec R)) :
    ∃ U : Set (PrimeSpectrum R), IsOpen U ∧ (U ∩ zeroLocus p.asIdeal).Nonempty ∧
      U ∩ zeroLocus p.asIdeal ⊆ Reg(Spec R) := by
  let e := Ideal.primeSpectrum_quotient_homeomorph_zeroLocus p.asIdeal
  let W : Set (V((p.asIdeal : Set R))) := e '' V
  have hW_open : IsOpen W := by
    -- First rewrite the transported image as a preimage along the inverse homeomorphism.
    have hW_preimage : W = e.symm ⁻¹' V := by
      ext z
      constructor
      · rintro ⟨x, hxV, rfl⟩
        simpa using hxV
      · intro hz
        refine ⟨e.symm z, hz, ?_⟩
        simp [W]
    rw [hW_preimage]
    exact hV_open.preimage e.symm.continuous
  rcases (isOpen_induced_iff.mp hW_open) with ⟨U, hU_open, hW_eq⟩
  refine ⟨U, hU_open, ?_, ?_⟩
  · rcases hV_nonempty with ⟨x, hxV⟩
    refine ⟨(e x).1, ?_, (e x).2⟩
    -- A point of the transported open subset gives a point of the ambient trace on `V(p)`.
    have hxW : e x ∈ W := ⟨x, hxV, rfl⟩
    have hxU : e x ∈ Subtype.val ⁻¹' U := by
      rw [hW_eq]
      exact hxW
    exact hxU
  · intro x hx
    let xV : V((p.asIdeal : Set R)) := ⟨x, hx.2⟩
    have hxW : xV ∈ W := by
      -- Use the ambient-open presentation of the subspace-open set inside `V(p)`.
      have hxU : xV ∈ Subtype.val ⁻¹' U := hx.1
      rw [hW_eq] at hxU
      exact hxU
    rcases hxW with ⟨y, hyV, hyx⟩
    -- Unpack the transported point and read regularity from the quotient-side hypothesis.
    have hyreg : ((Ideal.primeSpectrum_quotient_homeomorph_zeroLocus p.asIdeal y).1) ∈ Reg(Spec R) :=
      hV_reg y hyV
    have hxy : ((Ideal.primeSpectrum_quotient_homeomorph_zeroLocus p.asIdeal y).1) = x := by
      exact congrArg Subtype.val hyx
    simpa [hxy] using hyreg

/-- Helper for Lemma 15.47.3: every nonempty open subset of `Spec (R ⧸ p)` contains the generic
point of the quotient domain. -/
lemma genericPoint_mem_of_nonempty_open_quotient
    (p : PrimeSpectrum R)
    {V : Set (PrimeSpectrum (R ⧸ p.asIdeal))}
    (hV_open : IsOpen V) (hV_nonempty : V.Nonempty) :
    (⟨⊥, inferInstance⟩ : PrimeSpectrum (R ⧸ p.asIdeal)) ∈ V := by
  rcases hV_nonempty with ⟨x, hxV⟩
  -- The generic point specializes to every point of the quotient spectrum, so openness forces it
  -- into every nonempty open subset.
  exact
    ((PrimeSpectrum.le_iff_specializes (⊥ : PrimeSpectrum (R ⧸ p.asIdeal)) x).mp bot_le).mem_open
      hV_open hxV

/-- Helper for Lemma 15.47.3: a nonempty open subset of `Spec (R ⧸ p)` contains a quotient-side
principal basic open defined by an element of `R` not lying in `p`. -/
lemma exists_basicOpen_subset_of_nonempty_open_quotient
    (p : PrimeSpectrum R)
    {V : Set (PrimeSpectrum (R ⧸ p.asIdeal))}
    (hV_open : IsOpen V) (hV_nonempty : V.Nonempty) :
    ∃ g0 : R, g0 ∉ p.asIdeal ∧
      (basicOpen (Ideal.Quotient.mk p.asIdeal g0) : Set (PrimeSpectrum (R ⧸ p.asIdeal))) ⊆ V := by
  have hgeneric_mem : (⟨⊥, inferInstance⟩ : PrimeSpectrum (R ⧸ p.asIdeal)) ∈ V :=
    genericPoint_mem_of_nonempty_open_quotient (p := p) hV_open hV_nonempty
  obtain ⟨_, ⟨_, ⟨gbar, rfl⟩, rfl⟩, hbasic, hbasic_subset⟩ :=
    isBasis_basic_opens.exists_subset_of_mem_open hgeneric_mem hV_open
  obtain ⟨g0, rfl⟩ := Ideal.Quotient.mk_surjective gbar
  have hg0bar : Ideal.Quotient.mk p.asIdeal g0 ≠ 0 := by
    -- The generic point lies in the chosen basic open, so its defining function is nonzero.
    exact (PrimeSpectrum.mem_basicOpen _ ⟨⊥, inferInstance⟩).1 hbasic
  have hg0 : g0 ∉ p.asIdeal := by
    intro hg0p
    exact hg0bar ((Ideal.Quotient.eq_zero_iff_mem).2 hg0p)
  exact ⟨g0, hg0, hbasic_subset⟩

/-- Helper for Lemma 15.47.3: the prime of the quotient spectrum is obtained by mapping the image
prime of `Spec R` along the quotient map. -/
lemma quotientPoint_asIdeal_eq_map_image_asIdeal
    (p : PrimeSpectrum R) (x : PrimeSpectrum (R ⧸ p.asIdeal)) :
    x.asIdeal =
      ((Ideal.primeSpectrum_quotient_homeomorph_zeroLocus p.asIdeal x).1.asIdeal).map
        (Ideal.Quotient.mk p.asIdeal) := by
  -- Rewrite the quotient-side prime ideal by evaluating the inverse homeomorphism on its image.
  simpa using
    (Ideal.primeSpectrum_quotient_homeomorph_zeroLocus_symm_asIdeal
      (I := p.asIdeal)
      (x := Ideal.primeSpectrum_quotient_homeomorph_zeroLocus p.asIdeal x))

/-- Helper for Lemma 15.47.3: the image prime of a quotient point lies over the defining prime
`p`. -/
lemma quotientPoint_asIdeal_le
    (p : PrimeSpectrum R) (x : PrimeSpectrum (R ⧸ p.asIdeal)) :
    p.asIdeal ≤ ((Ideal.primeSpectrum_quotient_homeomorph_zeroLocus p.asIdeal x).1).asIdeal := by
  -- The quotient-spectrum homeomorphism lands in the closed subset `V(p)`, which is exactly the
  -- containment condition `p ≤ q` on prime ideals.
  exact
    (PrimeSpectrum.mem_zeroLocus
      ((Ideal.primeSpectrum_quotient_homeomorph_zeroLocus p.asIdeal x).1)
      (p.asIdeal : Set R)).1
      (Ideal.primeSpectrum_quotient_homeomorph_zeroLocus p.asIdeal x).2

/-- Helper for Lemma 15.47.3: a quotient-side principal basic open maps to the corresponding
principal basic open upstairs in `Spec R`. -/
lemma image_mem_basicOpen_of_mem_basicOpen_quotient
    (p : PrimeSpectrum R) {g : R} {x : PrimeSpectrum (R ⧸ p.asIdeal)}
    (hx :
      x ∈ (basicOpen (Ideal.Quotient.mk p.asIdeal g) : Set (PrimeSpectrum (R ⧸ p.asIdeal)))) :
    ((Ideal.primeSpectrum_quotient_homeomorph_zeroLocus p.asIdeal x).1) ∈
      (basicOpen g : Set (PrimeSpectrum R)) := by
  -- Unpack the basic-open condition and rewrite the image prime as the comap along the quotient.
  have hx' : Ideal.Quotient.mk p.asIdeal g ∉ x.asIdeal := by
    simpa [PrimeSpectrum.mem_basicOpen] using hx
  simpa [PrimeSpectrum.mem_basicOpen, Ideal.primeSpectrum_quotient_homeomorph_zeroLocus_apply] using
    hx'

/-- Helper for Lemma 15.47.3: after fixing the quotient basic open `D(g0 mod p)`, one further
principal shrink `D((g0 * h) mod p)` carries a regular sequence whose away-localized ideal agrees
with `p`. -/
lemma exists_principal_shrink_with_regular_sequence_and_ideal_eq
    (p : PrimeSpectrum R) (hp : p ∈ Reg(Spec R)) (g0 : R) (hg0 : g0 ∉ p.asIdeal) :
    ∃ h : R, ∃ fs : List R,
      g0 * h ∉ p.asIdeal ∧
        Ideal.ofList fs ≤ p.asIdeal ∧
        IsRegular (Localization.Away (g0 * h))
          (fs.map (algebraMap R (Localization.Away (g0 * h)))) ∧
        Ideal.map (algebraMap R (Localization.Away (g0 * h))) (Ideal.ofList fs) =
          Ideal.map (algebraMap R (Localization.Away (g0 * h))) p.asIdeal := by
  -- TODO: follow the source route in the fixed neighborhood `D(g0)` by first producing regular
  -- generators of `pR_p`, then spreading them away from one element `h ∉ p`, and finally killing
  -- the finite quotient `p / (fs)` after inverting that same `h`.
  let _ := hp
  let _ := hg0
  sorry

/-- Helper for Lemma 15.47.3: regularity of the quotient local ring at `x` transports to the
corresponding quotient of the ambient localization at the image prime. -/
lemma isRegularLocalRing_localizationAtPrime_quotientPoint_quotient
    (p : PrimeSpectrum R) (x : PrimeSpectrum (R ⧸ p.asIdeal))
    (hx_regular : IsRegularLocalRing (Localization.AtPrime x.asIdeal)) :
    IsRegularLocalRing
      ((Localization.AtPrime
          ((Ideal.primeSpectrum_quotient_homeomorph_zeroLocus p.asIdeal x).1).asIdeal) ⧸
        Ideal.map
          (algebraMap R
            (Localization.AtPrime
              ((Ideal.primeSpectrum_quotient_homeomorph_zeroLocus p.asIdeal x).1).asIdeal))
          p.asIdeal) := by
  -- TODO: identify `Localization.AtPrime x.asIdeal` with the quotient
  -- `Localization.AtPrime q.asIdeal / p Localization.AtPrime q.asIdeal` at the image prime
  -- `q`, then transport the regular-local instance across that ring equivalence.
  let _ := hx_regular
  let _ := quotientPoint_asIdeal_le (p := p) (x := x)
  sorry

/-- Helper for Lemma 15.47.3: regularity of a sequence on an away localization survives when one
localizes further at a prime inside the same basic open. -/
lemma isRegular_atPrime_of_regular_away_of_mem_basicOpen
    (q : PrimeSpectrum R) {g : R} {fs : List R}
    (hqg : q ∈ (basicOpen g : Set (PrimeSpectrum R)))
    (hfs :
      IsRegular (Localization.Away g)
        (fs.map (algebraMap R (Localization.Away g)))) :
    IsRegular (Localization.AtPrime q.asIdeal)
      (fs.map (algebraMap R (Localization.AtPrime q.asIdeal))) := by
  -- TODO: identify `Localization.AtPrime q.asIdeal` with the iterated localization
  -- `(Localization.Away g)_{qg}` for `qg = (primeSpectrum_localizationAway_homeomorph_D g).symm ⟨q, hqg⟩`,
  -- then transport `hfs` by the flat-local base-change theorem of Lemma `10.68.5`.
  let _ := hqg
  let _ := hfs
  sorry

/-- Helper for Lemma 15.47.3: if the spread ideal agrees with `p` on `R_g`, then the same ideal
agreement holds after localizing further at any prime in `D(g)`. -/
lemma map_ofList_eq_map_prime_at_away_prime_of_away_eq
    (p : PrimeSpectrum R) {g : R} {fs : List R}
    (qg : PrimeSpectrum (Localization.Away g))
    (hfs_eq :
      Ideal.map (algebraMap R (Localization.Away g)) (Ideal.ofList fs) =
        Ideal.map (algebraMap R (Localization.Away g)) p.asIdeal) :
    Ideal.map (algebraMap R (Localization.AtPrime qg.asIdeal)) (Ideal.ofList fs) =
      Ideal.map (algebraMap R (Localization.AtPrime qg.asIdeal)) p.asIdeal := by
  -- First localize the away-level ideal equality at the prime `qg` of `R_g`.
  calc
    Ideal.map (algebraMap R (Localization.AtPrime qg.asIdeal)) (Ideal.ofList fs)
      = Ideal.map (algebraMap (Localization.Away g) (Localization.AtPrime qg.asIdeal))
          (Ideal.map (algebraMap R (Localization.Away g)) (Ideal.ofList fs)) := by
            simp [Ideal.map_map,
              IsScalarTower.algebraMap_eq R (Localization.Away g)
                (Localization.AtPrime qg.asIdeal)]
    _ = Ideal.map (algebraMap (Localization.Away g) (Localization.AtPrime qg.asIdeal))
          (Ideal.map (algebraMap R (Localization.Away g)) p.asIdeal) := by
            -- Apply the given equality after extending both ideals to `(R_g)_{qg}`.
            exact congrArg
              (Ideal.map (algebraMap (Localization.Away g) (Localization.AtPrime qg.asIdeal)))
              hfs_eq
    _ = Ideal.map (algebraMap R (Localization.AtPrime qg.asIdeal)) p.asIdeal := by
          simp [Ideal.map_map,
            IsScalarTower.algebraMap_eq R (Localization.Away g)
              (Localization.AtPrime qg.asIdeal)]

/-- Helper for Lemma 15.47.3: if the spread ideal agrees with `p` on `R_g`, then the same ideal
agreement holds after localizing further at any prime in `D(g)`. -/
lemma map_ofList_eq_map_prime_atPrime_of_away_eq
    (p q : PrimeSpectrum R) {g : R} {fs : List R}
    (hqg : q ∈ (basicOpen g : Set (PrimeSpectrum R)))
    (hfs_eq :
      Ideal.map (algebraMap R (Localization.Away g)) (Ideal.ofList fs) =
        Ideal.map (algebraMap R (Localization.Away g)) p.asIdeal) :
    Ideal.map (algebraMap R (Localization.AtPrime q.asIdeal)) (Ideal.ofList fs) =
      Ideal.map (algebraMap R (Localization.AtPrime q.asIdeal)) p.asIdeal := by
  -- Route correction: first pass through the prime `qg` of `R_g`, and only then rewrite from
  -- the iterated localization `(R_g)_{qg}` to the ambient local ring `R_q`.
  let qg : PrimeSpectrum (Localization.Away g) :=
    (primeSpectrum_localizationAway_homeomorph_D g).symm ⟨q, hqg⟩
  have hqg_eq :
      Ideal.map (algebraMap R (Localization.AtPrime qg.asIdeal)) (Ideal.ofList fs) =
        Ideal.map (algebraMap R (Localization.AtPrime qg.asIdeal)) p.asIdeal := by
    -- This is the source-faithful first half of the transport: localize the away-level equality
    -- once more at the corresponding prime of `R_g`.
    exact map_ofList_eq_map_prime_at_away_prime_of_away_eq (p := p) (g := g) (fs := fs) qg hfs_eq
  -- TODO: transport `hqg_eq` across the canonical iterated-localization equivalence
  -- `Localization.AtPrime q.asIdeal ≃ₐ[R] Localization.AtPrime qg.asIdeal`, obtained from
  -- `IsLocalization.localizationLocalizationAtPrimeIsoLocalization`, and rewrite the two ideal
  -- maps along that equivalence.
  let _ := hqg
  let _ := qg
  let _ := hqg_eq
  let _ := hfs_eq
  sorry

/-- Helper for Lemma 15.47.3: once the fixed principal shrink provides a regular sequence whose
localized ideal equals `p`, any regular quotient point maps to a regular ambient prime. -/
lemma image_regular_of_fixed_principal_shrink
    (p : PrimeSpectrum R) {g : R} {fs : List R} {x : PrimeSpectrum (R ⧸ p.asIdeal)}
    (hx_basic :
      x ∈ (basicOpen (Ideal.Quotient.mk p.asIdeal g) : Set (PrimeSpectrum (R ⧸ p.asIdeal))))
    (hfs_le : Ideal.ofList fs ≤ p.asIdeal)
    (hfs_reg :
      IsRegular (Localization.Away g)
        (fs.map (algebraMap R (Localization.Away g))))
    (hfs_eq :
      Ideal.map (algebraMap R (Localization.Away g)) (Ideal.ofList fs) =
        Ideal.map (algebraMap R (Localization.Away g)) p.asIdeal)
    (hx_regular : IsRegularLocalRing (Localization.AtPrime x.asIdeal)) :
    ((Ideal.primeSpectrum_quotient_homeomorph_zeroLocus p.asIdeal x).1) ∈ Reg(Spec R) := by
  let q : PrimeSpectrum R := (Ideal.primeSpectrum_quotient_homeomorph_zeroLocus p.asIdeal x).1
  have hq_basic : q ∈ basicOpen g := by
    -- The quotient-side basic-open condition already says that the image prime lies in `D(g)`.
    exact image_mem_basicOpen_of_mem_basicOpen_quotient (p := p) hx_basic
  have hquot_p :
      IsRegularLocalRing
        ((Localization.AtPrime q.asIdeal) ⧸
          Ideal.map (algebraMap R (Localization.AtPrime q.asIdeal)) p.asIdeal) := by
    -- Transport regularity from the quotient local ring `R_x` to `R_q / pR_q`.
    simpa [q] using
      isRegularLocalRing_localizationAtPrime_quotientPoint_quotient
        (p := p) (x := x) hx_regular
  have hq_regseq :
      IsRegular (Localization.AtPrime q.asIdeal)
        (fs.map (algebraMap R (Localization.AtPrime q.asIdeal))) := by
    -- Localize the away-regular sequence once more at the image prime `q`.
    exact isRegular_atPrime_of_regular_away_of_mem_basicOpen (q := q) hq_basic hfs_reg
  have hq_ideal_eq :
      Ideal.map (algebraMap R (Localization.AtPrime q.asIdeal)) (Ideal.ofList fs) =
        Ideal.map (algebraMap R (Localization.AtPrime q.asIdeal)) p.asIdeal := by
    -- The away-level equality of ideals remains true after localizing at `q`.
    exact map_ofList_eq_map_prime_atPrime_of_away_eq (p := p) (q := q) hq_basic hfs_eq
  -- TODO: replace the quotient by `pR_q` with the quotient by the spread ideal via `hq_ideal_eq`,
  -- then apply Lemma `10.106.7` in the local ring `R_q` to deduce that `R_q` is regular.
  let _ := hfs_le
  let _ := hquot_p
  let _ := hq_regseq
  let _ := hq_ideal_eq
  sorry

/-- Helper for Lemma 15.47.3: isolate the nonempty branch after freezing a quotient-side basic
open and keeping its generic point. The remaining gap is purely the algebraic spread/localization
argument on this fixed principal neighborhood. -/
lemma exists_basicOpen_on_quotient_with_regular_image_of_nonempty
    (p : PrimeSpectrum R) (hp : p ∈ Reg(Spec R))
    {V : Set (PrimeSpectrum (R ⧸ p.asIdeal))}
    (hV_open : IsOpen V) (hV_nonempty : V.Nonempty)
    (hV_reg : ∀ x ∈ V, IsRegularLocalRing (Localization.AtPrime x.asIdeal)) :
    ∃ g : R, g ∉ p.asIdeal ∧
      ∀ x ∈ V ∩ (basicOpen (Ideal.Quotient.mk p.asIdeal g) :
        Set (PrimeSpectrum (R ⧸ p.asIdeal))),
        ((Ideal.primeSpectrum_quotient_homeomorph_zeroLocus p.asIdeal x).1) ∈ Reg(Spec R) := by
  obtain ⟨g0, hg0, hbasic0_subset⟩ :=
    exists_basicOpen_subset_of_nonempty_open_quotient (p := p) hV_open hV_nonempty
  have hgeneric_mem : (⟨⊥, inferInstance⟩ : PrimeSpectrum (R ⧸ p.asIdeal)) ∈ V :=
    genericPoint_mem_of_nonempty_open_quotient (p := p) hV_open hV_nonempty
  have hgeneric_basic :
      (⟨⊥, inferInstance⟩ : PrimeSpectrum (R ⧸ p.asIdeal)) ∈
        (basicOpen (Ideal.Quotient.mk p.asIdeal g0) : Set (PrimeSpectrum (R ⧸ p.asIdeal))) := by
    have hg0bar : Ideal.Quotient.mk p.asIdeal g0 ≠ 0 := by
      intro hg0bar
      exact hg0 ((Ideal.Quotient.eq_zero_iff_mem).1 hg0bar)
    exact (PrimeSpectrum.mem_basicOpen _ ⟨⊥, inferInstance⟩).2 hg0bar
  have hV0_nonempty :
      (V ∩ (basicOpen (Ideal.Quotient.mk p.asIdeal g0) :
        Set (PrimeSpectrum (R ⧸ p.asIdeal)))).Nonempty := by
    exact ⟨⟨⊥, inferInstance⟩, hgeneric_mem, hgeneric_basic⟩
  -- Route correction: the topology is now frozen at the fixed neighborhood `D(g0 mod p) ⊆ V`.
  obtain ⟨h, fs, hgh, hfs_le, hfs_reg, hfs_eq⟩ :=
    exists_principal_shrink_with_regular_sequence_and_ideal_eq
      (p := p) (hp := hp) g0 hg0
  refine ⟨g0 * h, hgh, ?_⟩
  intro x hx
  have hxV : x ∈ V := hx.1
  have hx_basic :
      x ∈ (basicOpen (Ideal.Quotient.mk p.asIdeal (g0 * h)) :
        Set (PrimeSpectrum (R ⧸ p.asIdeal))) := hx.2
  have hx_regular : IsRegularLocalRing (Localization.AtPrime x.asIdeal) := hV_reg x hxV
  -- The pointwise endgame is now isolated: apply the shrink data and the quotient/localization
  -- comparison to the chosen quotient point `x`.
  let _ := hbasic0_subset
  let _ := hV0_nonempty
  exact
    image_regular_of_fixed_principal_shrink
      (p := p) (g := g0 * h) (fs := fs) hx_basic hfs_le hfs_reg hfs_eq hx_regular

/-- Helper for Lemma 15.47.3: near a regular prime `p`, a nonempty open subset of regular points
of `Spec (R ⧸ p)` yields a nonempty open trace on `V(p)` inside the regular locus of `Spec R`. -/
lemma exists_basicOpen_on_quotient_with_regular_image
    (p : PrimeSpectrum R) (hp : p ∈ Reg(Spec R))
    {V : Set (PrimeSpectrum (R ⧸ p.asIdeal))}
    (hV_open : IsOpen V)
    (hV_reg : ∀ x ∈ V, IsRegularLocalRing (Localization.AtPrime x.asIdeal)) :
    ∃ g : R, g ∉ p.asIdeal ∧
      ∀ x ∈ V ∩ (basicOpen (Ideal.Quotient.mk p.asIdeal g) :
        Set (PrimeSpectrum (R ⧸ p.asIdeal))),
        ((Ideal.primeSpectrum_quotient_homeomorph_zeroLocus p.asIdeal x).1) ∈ Reg(Spec R) := by
  by_cases hV_nonempty : V.Nonempty
  · exact
      exists_basicOpen_on_quotient_with_regular_image_of_nonempty
        (p := p) (hp := hp) hV_open hV_nonempty hV_reg
  · refine ⟨1, ?_, ?_⟩
    · intro h1
      exact p.2.ne_top (p.asIdeal.eq_top_of_isUnit_mem h1 isUnit_one)
    · intro x hx
      exact False.elim (hV_nonempty ⟨x, hx.1⟩)

/-- Helper for Lemma 15.47.3: shrinking by a quotient-side basic open keeps the regular-point
image construction nonempty. -/
lemma exists_nonempty_open_regular_subset_zeroLocus_of_regular_quotient_open
    (p : PrimeSpectrum R) (hp : p ∈ Reg(Spec R))
    {V : Set (PrimeSpectrum (R ⧸ p.asIdeal))}
    (hV_open : IsOpen V) (hV_nonempty : V.Nonempty)
    (hV_reg : ∀ x ∈ V, IsRegularLocalRing (Localization.AtPrime x.asIdeal)) :
    ∃ U : Set (PrimeSpectrum R), IsOpen U ∧ (U ∩ zeroLocus p.asIdeal).Nonempty ∧
      U ∩ zeroLocus p.asIdeal ⊆ Reg(Spec R) := by
  obtain ⟨g, hg, hg_reg⟩ :=
    exists_basicOpen_on_quotient_with_regular_image
      (p := p) (hp := hp) hV_open hV_reg
  let V' : Set (PrimeSpectrum (R ⧸ p.asIdeal)) :=
    V ∩ (basicOpen (Ideal.Quotient.mk p.asIdeal g) : Set (PrimeSpectrum (R ⧸ p.asIdeal)))
  have hV'_open : IsOpen V' := by
    -- After the algebraic shrink, the quotient-side set is still open.
    change IsOpen (V ∩ (basicOpen (Ideal.Quotient.mk p.asIdeal g) :
      Set (PrimeSpectrum (R ⧸ p.asIdeal))))
    exact hV_open.inter isOpen_basicOpen
  have hgeneric_mem : (⟨⊥, inferInstance⟩ : PrimeSpectrum (R ⧸ p.asIdeal)) ∈ V := by
    exact genericPoint_mem_of_nonempty_open_quotient (p := p) hV_open hV_nonempty
  have hgeneric_basic :
      (⟨⊥, inferInstance⟩ : PrimeSpectrum (R ⧸ p.asIdeal)) ∈
        (basicOpen (Ideal.Quotient.mk p.asIdeal g) : Set (PrimeSpectrum (R ⧸ p.asIdeal))) := by
    have hgbar : Ideal.Quotient.mk p.asIdeal g ≠ 0 := by
      intro hgbar
      exact hg ((Ideal.Quotient.eq_zero_iff_mem).1 hgbar)
    exact (PrimeSpectrum.mem_basicOpen _ ⟨⊥, inferInstance⟩).2 hgbar
  have hV'_nonempty : V'.Nonempty := by
    -- The generic point survives the shrink because `g ∉ p`.
    exact ⟨⟨⊥, inferInstance⟩, hgeneric_mem, hgeneric_basic⟩
  have hV'_reg :
      ∀ x ∈ V',
        ((Ideal.primeSpectrum_quotient_homeomorph_zeroLocus p.asIdeal x).1) ∈ Reg(Spec R) := by
    intro x hx
    exact hg_reg x hx
  -- The remaining transport from the quotient spectrum back to an ambient open subset of `Spec R`
  -- is purely topological and already isolated in the previous helper.
  exact
    exists_nonempty_open_regular_subset_zeroLocus_of_homeomorph_image
      (p := p) hV'_open hV'_nonempty hV'_reg

/- Domain-style sampling:
- primary domain: the regular locus on `PrimeSpectrum R` and the chapter owners `IsJ0Ring` and
  `IsJ1Ring`;
- sampled owner declarations of the same kind:
  `PrimeSpectrum.regularLocus`,
  `isJ0Ring_iff_exists_nonempty_open_subset_regularLocus`,
  `isJ1Ring_iff_forall_regularPoint_zeroLocus_contains_nonempty_open_regular_subset`,
  `Ideal.primeSpectrum_quotient_homeomorph_zeroLocus`;
- best owner abstraction: the source-facing criterion from Lemma `15.47.2` is the canonical owner
  bridge for proving `IsJ1Ring R`, while the hypotheses `IsJ0Ring (R ⧸ p.asIdeal)` are derived
  input on the quotient spectra `Spec (R ⧸ p) ≃ V(p)`;
- primitive vs. derived: the primitive public data are just the ring `R` and the owner hypothesis
  that each prime quotient is `J-0`. The required open subsets of `V(p)` are derived via the
  quotient-spectrum owner bridge, so they should not be packaged as a separate local wrapper API.

Source/core/bridge triage:
- `source-facing`: the chapter lemma asserting that `J-0` prime quotients force `R` to be `J-1`;
- `core/canonical`: `Reg(Spec R)`, `IsJ0Ring`, and `IsJ1Ring`;
- `bridge/view`: the homeomorphism `Spec (R ⧸ p) ≃ V(p)` transporting the quotient regular locus
  back to the closed subset `V(p)`.
-/

-- Proof sketch: apply the criterion of Lemma `15.47.2`. For a regular prime `p`, choose a
-- regular sequence generating `p` after localizing and then after shrinking to a principal open.
-- For any prime `q ⊇ p` whose image in `Spec (R ⧸ p)` is regular, the quotient local ring
-- `R_q / p R_q` is regular; the regular-sequence criterion for regular local rings then implies
-- that `R_q` is regular. Since `R ⧸ p` is `J-0`, this yields the required nonempty open subset of
-- `V(p)` contained in the regular locus, so Lemma `15.47.2` gives that `R` is `J-1`.
/-- Lemma 15.47.3: if `R` is a Noetherian ring and for every prime `p` of `R` the quotient
ring `R ⧸ p` is `J-0`, then `R` is `J-1`. -/
theorem isJ1Ring_of_isJ0Ring_quotient_by_prime
    (hquot : ∀ p : PrimeSpectrum R, IsJ0Ring (R ⧸ p.asIdeal)) :
    IsJ1Ring R := by
  rw [isJ1Ring_iff_forall_regularPoint_zeroLocus_contains_nonempty_open_regular_subset]
  intro p hp
  obtain ⟨V, hV_open, hV_nonempty, hV_reg⟩ :=
    (isJ0Ring_iff_exists_nonempty_open_subset_regularLocus).mp (hquot p)
  -- First extract the regular-local content of the quotient-side regular locus witness.
  have hV_reg_local :
      ∀ x ∈ V, IsRegularLocalRing (Localization.AtPrime x.asIdeal) := by
    intro x hx
    simpa using hV_reg hx
  -- The remaining source-faithful step is the local regular-sequence bridge from regularity on
  -- `Spec (R ⧸ p)` back to regularity on a nonempty open trace inside `V(p)`.
  exact
    exists_nonempty_open_regular_subset_zeroLocus_of_regular_quotient_open
      (p := p) (hp := hp) hV_open hV_nonempty hV_reg_local

end
