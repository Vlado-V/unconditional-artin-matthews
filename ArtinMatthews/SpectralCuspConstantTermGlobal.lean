module

public import ArtinMatthews.SpectralCuspConstantTermHeights
public import ArtinMatthews.SpectralCuspWeightedGluing


set_option backward.privateInPublic true
@[expose] public section

/-! Actual globally locally-integrable cusp constant terms and their physical
vertical derivative representatives, glued from the compatible genuine
weighted L² restrictions at all positive heights. -/

noncomputable section
open Set MeasureTheory Filter
open scoped MatrixGroups

namespace ArtinMatthews

theorem spectralCuspGluingHeight_antitone {m n : ℕ} (h : m ≤ n) :
    spectralCuspGluingHeight n ≤ spectralCuspGluingHeight m := by
  unfold spectralCuspGluingHeight
  apply one_div_le_one_div_of_le (by positivity)
  exact_mod_cast Nat.add_le_add_right h 1

def gamma0CuspConstantTermDerivativeLp (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (u : gamma0EnergySpace N) : CuspVerticalL2 (N : ℝ) Y :=
  (gamma0CuspConstantTermDerivative_memLp N r Y hY u).toLp
    (gamma0CuspConstantTermDerivative N r Y hY u)

theorem gamma0CuspConstantTermDerivativeLp_ae (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (u : gamma0EnergySpace N) :
    gamma0CuspConstantTermDerivativeLp N r Y hY u
      =ᵐ[(cuspHorizontalMeasure (N : ℝ) univ) • cuspVerticalMeasure Y]
        gamma0CuspConstantTermDerivative N r Y hY u :=
  (gamma0CuspConstantTermDerivative_memLp N r Y hY u).coeFn_toLp

def gamma0CuspConstantTermFamily (N : ℕ) [NeZero N] (r : SL(2, ℤ))
    (f : Gamma0RegionL2 N) (n : ℕ) : CuspVerticalL2 (N : ℝ) (spectralCuspGluingHeight n) :=
  gamma0CuspConstantTerm N r (spectralCuspGluingHeight n) (spectralCuspGluingHeight_pos n) f

def gamma0CuspDerivativeFamily (N : ℕ) [NeZero N] (r : SL(2, ℤ))
    (u : gamma0EnergySpace N) (n : ℕ) : CuspVerticalL2 (N : ℝ) (spectralCuspGluingHeight n) :=
  gamma0CuspConstantTermDerivativeLp N r (spectralCuspGluingHeight n) (spectralCuspGluingHeight_pos n) u

theorem gamma0CuspConstantTermFamily_compatible (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (f : Gamma0RegionL2 N) (m n : ℕ) (h : m ≤ n) :
    gamma0CuspConstantTermFamily N r f m
      =ᵐ[(cuspHorizontalMeasure (N : ℝ) univ) • cuspVerticalMeasure (spectralCuspGluingHeight m)]
        gamma0CuspConstantTermFamily N r f n :=
  (gamma0CuspConstantTerm_height_ae N r _ _ (spectralCuspGluingHeight_pos n)
    (spectralCuspGluingHeight_pos m) (spectralCuspGluingHeight_antitone h) f).symm

theorem gamma0CuspDerivativeFamily_compatible (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (u : gamma0EnergySpace N) (m n : ℕ) (h : m ≤ n) :
    gamma0CuspDerivativeFamily N r u m
      =ᵐ[(cuspHorizontalMeasure (N : ℝ) univ) • cuspVerticalMeasure (spectralCuspGluingHeight m)]
        gamma0CuspDerivativeFamily N r u n := by
  have hm := gamma0CuspConstantTermDerivativeLp_ae N r _ (spectralCuspGluingHeight_pos m) u
  have hn := gamma0CuspConstantTermDerivativeLp_ae N r _ (spectralCuspGluingHeight_pos n) u
  have hn' := (Measure.absolutelyContinuous_of_le
    (cuspWeightedVerticalMeasure_mono (N : ℝ) (spectralCuspGluingHeight_antitone h))).ae_eq hn
  exact hm.trans ((gamma0CuspConstantTermDerivative_height_ae N r _ _
    (spectralCuspGluingHeight_pos n) (spectralCuspGluingHeight_pos m)
      (spectralCuspGluingHeight_antitone h) u).symm.trans hn'.symm)

def gamma0GlobalCuspConstantTerm (N : ℕ) [NeZero N] (r : SL(2, ℤ))
    (f : Gamma0RegionL2 N) : ℝ → ℂ :=
  spectralCuspGluedRepresentative (N : ℝ) (gamma0CuspConstantTermFamily N r f)

def gamma0GlobalCuspConstantTermDerivative (N : ℕ) [NeZero N] (r : SL(2, ℤ))
    (u : gamma0EnergySpace N) : ℝ → ℂ :=
  spectralCuspGluedRepresentative (N : ℝ) (gamma0CuspDerivativeFamily N r u)

theorem gamma0GlobalCuspConstantTerm_locallyIntegrable (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (f : Gamma0RegionL2 N) :
    LocallyIntegrableOn (gamma0GlobalCuspConstantTerm N r f) (Ioi 0) volume :=
  spectralCuspGluedRepresentative_locallyIntegrableOn (Nat.cast_pos.mpr (NeZero.pos N))
    _ (gamma0CuspConstantTermFamily_compatible N r f)

theorem gamma0GlobalCuspConstantTermDerivative_locallyIntegrable (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (u : gamma0EnergySpace N) :
    LocallyIntegrableOn (gamma0GlobalCuspConstantTermDerivative N r u) (Ioi 0) volume :=
  spectralCuspGluedRepresentative_locallyIntegrableOn (Nat.cast_pos.mpr (NeZero.pos N))
    _ (gamma0CuspDerivativeFamily_compatible N r u)

theorem gamma0GlobalCuspConstantTerm_ae (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (f : Gamma0RegionL2 N) (Y : ℝ) (hY : 0 < Y) :
    gamma0GlobalCuspConstantTerm N r f
      =ᵐ[(cuspHorizontalMeasure (N : ℝ) univ) • cuspVerticalMeasure Y]
        gamma0CuspConstantTerm N r Y hY f := by
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hY
  have hh : spectralCuspGluingHeight n ≤ Y := hn.le
  have hg := spectralCuspGluedRepresentative_ae (Nat.cast_pos.mpr (NeZero.pos N))
    (gamma0CuspConstantTermFamily N r f) (gamma0CuspConstantTermFamily_compatible N r f) n
  exact ((Measure.absolutelyContinuous_of_le (cuspWeightedVerticalMeasure_mono (N : ℝ) hh)).ae_eq hg).trans
    (gamma0CuspConstantTerm_height_ae N r _ Y (spectralCuspGluingHeight_pos n) hY hh f)

theorem gamma0GlobalCuspConstantTermDerivative_ae (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (u : gamma0EnergySpace N) (Y : ℝ) (hY : 0 < Y) :
    gamma0GlobalCuspConstantTermDerivative N r u
      =ᵐ[(cuspHorizontalMeasure (N : ℝ) univ) • cuspVerticalMeasure Y]
        gamma0CuspConstantTermDerivative N r Y hY u := by
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hY
  have hh : spectralCuspGluingHeight n ≤ Y := hn.le
  have hg := spectralCuspGluedRepresentative_ae (Nat.cast_pos.mpr (NeZero.pos N))
    (gamma0CuspDerivativeFamily N r u) (gamma0CuspDerivativeFamily_compatible N r u) n
  have hg' := (Measure.absolutelyContinuous_of_le (cuspWeightedVerticalMeasure_mono (N : ℝ) hh)).ae_eq hg
  have hn := gamma0CuspConstantTermDerivativeLp_ae N r _ (spectralCuspGluingHeight_pos n) u
  have hn' := (Measure.absolutelyContinuous_of_le (cuspWeightedVerticalMeasure_mono (N : ℝ) hh)).ae_eq hn
  exact hg'.trans (hn'.trans
    (gamma0CuspConstantTermDerivative_height_ae N r _ Y (spectralCuspGluingHeight_pos n) hY hh u))

theorem mem_gamma0AllHeightCuspidalMassSpace_iff_globalConstantTerm (N : ℕ) [NeZero N]
    (f : Gamma0RegionL2 N) :
    f ∈ gamma0AllHeightCuspidalMassSpace N ↔
      ∀ r : SL(2, ℤ), gamma0GlobalCuspConstantTerm N r f =ᵐ[volume.restrict (Ioi 0)] 0 := by
  rw [mem_gamma0AllHeightCuspidalMassSpace_iff_constantTerm]
  constructor
  · intro h r
    apply spectralCuspWeightedGluing_unique (Nat.cast_pos.mpr (NeZero.pos N))
    intro n
    have hg := gamma0GlobalCuspConstantTerm_ae N r f _ (spectralCuspGluingHeight_pos n)
    rw [h r _ (spectralCuspGluingHeight_pos n)] at hg
    exact hg.trans (Lp.coeFn_zero ℂ 2 _)
  · intro h r Y hY
    have hv : gamma0GlobalCuspConstantTerm N r f =ᵐ[volume.restrict (Ioi Y)] 0 :=
      ae_restrict_of_ae_restrict_of_subset (fun y hy => hY.trans hy) (h r)
    have hz := (spectralCuspVerticalL2_ae_iff (Nat.cast_pos.mpr (NeZero.pos N)) hY).mpr hv
    apply Lp.ext
    filter_upwards [gamma0GlobalCuspConstantTerm_ae N r f Y hY, hz, Lp.coeFn_zero ℂ 2
      ((cuspHorizontalMeasure (N : ℝ) univ) • cuspVerticalMeasure Y)] with y he hz hzero
    exact he.symm.trans (hz.trans hzero.symm)

end ArtinMatthews
