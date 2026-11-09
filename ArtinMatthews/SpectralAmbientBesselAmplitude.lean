module

public import ArtinMatthews.SpectralAmbientFourierBessel
public import ArtinMatthews.SpectralAmbientFourierHeights
public import ArtinMatthews.SpectralGamma0PoincareBessel


set_option backward.privateInPublic true
@[expose] public section

/-! One actual Bessel amplitude serves every positive base height, including
for residual eigenvectors, and gives the original Poincare pairing. -/

noncomputable section
open Set MeasureTheory Filter
open scoped MatrixGroups ContDiff InnerProductSpace

namespace ArtinMatthews

theorem gamma0CuspBessel_coefficient_unique (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (n : ℤ) (m : Gamma0RegionL2 N)
    (ν : ℂ) (hν : -1 / 2 < ν.re) (q : ℝ) (hq : 0 < q)
    (Y₁ Y₂ : ℝ) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂) (a b : ℂ)
    (ha : gamma0CuspFourierCoefficient N r Y₁ hY₁ n m =ᵐ[volume.restrict (Ioi Y₁)]
      fun y => a * cuspBesselKernel ν q y)
    (hb : gamma0CuspFourierCoefficient N r Y₂ hY₂ n m =ᵐ[volume.restrict (Ioi Y₂)]
      fun y => b * cuspBesselKernel ν q y) : a = b := by
  let Y := max Y₁ Y₂
  have hY : 0 < Y := hY₁.trans_le (le_max_left _ _)
  have hle₁ : Y₁ ≤ Y := le_max_left _ _
  have hle₂ : Y₂ ≤ Y := le_max_right _ _
  have hm₁ : volume.restrict (Ioi Y) ≤ volume.restrict (Ioi Y₁) :=
    Measure.restrict_mono_set _ (fun _ hy => hle₁.trans_lt hy)
  have hm₂ : volume.restrict (Ioi Y) ≤ volume.restrict (Ioi Y₂) :=
    Measure.restrict_mono_set _ (fun _ hy => hle₂.trans_lt hy)
  have ha' := (Measure.absolutelyContinuous_of_le hm₁).ae_eq ha
  have hb' := (Measure.absolutelyContinuous_of_le hm₂).ae_eq hb
  have hc₁ := gamma0CuspFourierCoefficient_height_ae N r Y₁ Y hY₁ hY hle₁ n m
  have hc₂ := gamma0CuspFourierCoefficient_height_ae N r Y₂ Y hY₂ hY hle₂ n m
  have he : (fun y => a * cuspBesselKernel ν q y) =ᵐ[volume.restrict (Ioi Y)]
      fun y => b * cuspBesselKernel ν q y :=
    ha'.symm.trans (hc₁.trans (hc₂.symm.trans hb'))
  have hcont : ContinuousOn (cuspBesselKernel ν q) (Ioi Y) :=
    fun y hy => (cuspBesselKernel_continuousAt ν hq (hY.trans hy)).continuousWithinAt
  have heq := Measure.eqOn_open_of_ae_eq (μ := volume) he isOpen_Ioi
    (continuousOn_const.mul hcont) (continuousOn_const.mul hcont)
  obtain ⟨y, hy₀, hy, hne⟩ := spectralKBesselWhittaker_exists_ne_zero_above ν hν q Y hq
  have hk : cuspBesselKernel ν q y ≠ 0 := by
    simpa only [cuspBesselKernel, spectralKBesselWhittaker_eq_sqrt ν q y hy₀.le] using hne
  exact mul_right_cancel₀ hk (heq hy)

def gamma0AmbientBesselAmplitude (N : ℕ) [NeZero N] (eig : ℝ) (hl : 0 ≤ eig)
    (m : Gamma0RegionL2 N) (hG : gamma0Green N m = (((eig + 1)⁻¹ : ℝ) : ℂ) • m)
    (r : SL(2, ℤ)) (n : ℤ) (hn : n ≠ 0) : ℂ :=
  Classical.choose (gamma0AmbientEigen_fourier_bessel_ae N eig hl m hG r 1 zero_lt_one n hn)

theorem gamma0AmbientBesselAmplitude_fourier_ae (N : ℕ) [NeZero N]
    (eig : ℝ) (hl : 0 ≤ eig) (m : Gamma0RegionL2 N)
    (hG : gamma0Green N m = (((eig + 1)⁻¹ : ℝ) : ℂ) • m)
    (r : SL(2, ℤ)) (n : ℤ) (hn : n ≠ 0) (Y : ℝ) (hY : 0 < Y) :
    gamma0CuspFourierCoefficient N r Y hY n m =ᵐ[volume.restrict (Ioi Y)]
      fun y => gamma0AmbientBesselAmplitude N eig hl m hG r n hn *
        cuspBesselKernel (Complex.sqrt (1 / 4 - (eig : ℂ)))
          (|cuspFourierFrequency (N : ℝ) n|) y := by
  obtain ⟨a, ha⟩ := gamma0AmbientEigen_fourier_bessel_ae N eig hl m hG r Y hY n hn
  have hb := Classical.choose_spec
    (gamma0AmbientEigen_fourier_bessel_ae N eig hl m hG r 1 zero_lt_one n hn)
  have hq : 0 < |cuspFourierFrequency (N : ℝ) n| := abs_pos.mpr
    (cuspFourierFrequency_ne_zero (N : ℝ) (Nat.cast_pos.mpr (NeZero.pos N)) n hn)
  have hν : -1 / 2 < (Complex.sqrt (1 / 4 - (eig : ℂ))).re :=
    lt_of_lt_of_le (by norm_num) (spectralComplexSqrt_re_nonneg _)
  have he := gamma0CuspBessel_coefficient_unique N r n m _ hν _ hq Y 1 hY zero_lt_one a
    (gamma0AmbientBesselAmplitude N eig hl m hG r n hn) ha hb
  simpa only [he] using ha

theorem gamma0AmbientOperatorEigen_fourier_all_heights (N : ℕ) [NeZero N]
    (eig : ℝ) (hl : 0 ≤ eig) (m : Gamma0RegionL2 N)
    (hm : (m, (((eig + 1 : ℝ) : ℂ) • m)) ∈ (gamma0MassEnergyOperator N).graph)
    (r : SL(2, ℤ)) (n : ℤ) (hn : n ≠ 0) :
    ∃ a : ℂ, ∀ (Y : ℝ) (hY : 0 < Y),
      gamma0CuspFourierCoefficient N r Y hY n m =ᵐ[volume.restrict (Ioi Y)]
        fun y => a * cuspBesselKernel (Complex.sqrt (1 / 4 - (eig : ℂ)))
          (|cuspFourierFrequency (N : ℝ) n|) y := by
  have hG := (gamma0AmbientEigen_operator_iff_green N eig hl m).mp hm
  exact ⟨gamma0AmbientBesselAmplitude N eig hl m hG r n hn,
    fun Y hY => gamma0AmbientBesselAmplitude_fourier_ae N eig hl m hG r n hn Y hY⟩

theorem gamma0FourierPoincareTest_ambient_inner (N : ℕ) [NeZero N]
    (eig : ℝ) (hl : 0 ≤ eig) (m : Gamma0RegionL2 N)
    (hG : gamma0Green N m = (((eig + 1)⁻¹ : ℝ) : ℂ) • m)
    (r : SL(2, ℤ)) (n : ℤ) (hn : n ≠ 0) (Y : ℝ) (hY : 0 < Y)
    (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hpos : tsupport ρ ⊆ Ioi (0 : ℝ)) (hs : tsupport ρ ⊆ Ioi Y) :
    inner ℂ (gamma0FourierPoincareTest N r n ρ hρ hcρ hpos) m =
      (2 * (N : ℂ)) * gamma0AmbientBesselAmplitude N eig hl m hG r n hn *
        cuspBesselTransform (Complex.sqrt (1 / 4 - (eig : ℂ)))
          (|cuspFourierFrequency (N : ℝ) n|) Y ρ :=
  gamma0FourierPoincareTest_inner_of_bessel N r Y hY n m _ _ _
    (gamma0AmbientBesselAmplitude_fourier_ae N eig hl m hG r n hn Y hY)
    ρ hρ hcρ hpos hs

end ArtinMatthews
