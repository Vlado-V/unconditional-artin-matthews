module

public import ArtinMatthews.SpectralGamma0Localization
public import ArtinMatthews.SpectralGamma0EnergyGraph
public import ArtinMatthews.SpectralCompactChartEnergy
public import ArtinMatthews.SpectralCoreLocalizationChartCompact
public import ArtinMatthews.SpectralCoreLocalizationSmoothEnergy
public import ArtinMatthews.SpectralHyperbolicL2
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Uniform global energy control and genuine local compactness of the actual core. -/

noncomputable section
open Set MeasureTheory

namespace ArtinMatthews

variable (φ : SchwartzMap (ℝ × ℝ) ℂ) {A a b : ℝ}
  (ha : 0 < a) (hab : a ≤ b) (hφ : tsupport φ ⊆ spectralPlaneRectangle A a b)

theorem gamma0LocalizedSeedLp_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N] (ψ : h2SmoothCompactSeeds),
      ‖gamma0LocalizedSeedLp φ ha hab hφ N ψ‖ ≤ C * ‖gamma0EnergyTest N ψ‖ := by
  obtain ⟨Cφ,hCφ,hlocal⟩ := spectralCoreLocalization_energy_bound_smooth φ ha hφ
  obtain ⟨CK,hCK,hchart⟩ := compact_chart_gamma0_energy_bound
    (spectralCoreChart_compact A a b ha)
  let C := (1 / a^2) * (Cφ * CK)
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨Real.sqrt C, Real.sqrt_pos.2 hC, fun N _ ψ => ?_⟩
  let G := spectralCoreLocalization φ ha hφ (gamma0PoincareSeed N ψ.val)
    (gamma0SmoothSeed_representative_smooth N ψ)
  have hs : tsupport G ⊆ spectralPlaneRectangle A a b :=
    spectralCoreLocalization_support φ ha hφ _ _
  have hc : HasCompactSupport (G : ℝ × ℝ → ℂ) :=
    (spectralPlaneRectangle_compact A a b).of_isClosed_subset (isClosed_tsupport _) hs
  have hband := (hyperbolic_L2_band_transfer G.continuous.measurable
    (spectral_plane_normsq_integrable G.continuous hc) ha hab
    (spectral_rectangle_height_band hs)).2.2
  have hn : ‖gamma0LocalizedSeedLp φ ha hab hφ N ψ‖^2 =
      ∫ z : UpperHalfPlane, ‖G (z.re,z.im)‖^2 := by
    rw [← real_inner_self_eq_norm_sq,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [spectralHyperbolicRectangleLp_ae ha hab G hs] with z hz
    rw [real_inner_self_eq_norm_sq]
    change ‖(spectralHyperbolicRectangleLp ha hab G hs) z‖^2 = _
    rw [hz]
  have hnonneg : 0 ≤ ∫ p, h2DirichletDensity G G p := by
    apply integral_nonneg
    intro p
    simp only [h2DirichletDensity,real_inner_self_eq_norm_sq]
    positivity
  have hmain : ‖gamma0LocalizedSeedLp φ ha hab hφ N ψ‖^2 ≤ C * ‖gamma0EnergyTest N ψ‖^2 := by
    rw [hn]
    calc
      _ ≤ (1 / a^2) * ∫ p, ‖G p‖^2 := hband
      _ ≤ (1 / a^2) * ((∫ p, ‖G p‖^2)+(∫ p, h2DirichletDensity G G p)) :=
        mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hnonneg) (by positivity)
      _ ≤ (1 / a^2) * (Cφ * (∫ z : UpperHalfPlane in
          {z | (z.re,z.im) ∈ spectralPlaneRectangle A a b},
          ‖gamma0PoincareSeed N ψ.val z‖^2+h2SectionEnergy (gamma0PoincareSeed N ψ.val) z)) :=
        mul_le_mul_of_nonneg_left (hlocal _ (gamma0SmoothSeed_representative_smooth N ψ))
          (by positivity)
      _ ≤ (1 / a^2) * (Cφ * (CK * ‖gamma0EnergyTest N ψ‖^2)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (hchart N ψ) hCφ.le) (by positivity)
      _ = C * ‖gamma0EnergyTest N ψ‖^2 := by dsimp only [C]; ring
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow,Real.sq_sqrt hC.le]
  exact hmain

/-- Any family of genuine smooth core vectors with bounded global energy
has compact closure after fixed compact localization. -/
theorem gamma0LocalizedSeedLp_rellich {J : Type*} (N : ℕ) [NeZero N]
    (ψ : J → h2SmoothCompactSeeds) {B : ℝ} (hB : 0 ≤ B)
    (henergy : ∀ j, ‖gamma0EnergyTest N (ψ j)‖^2 ≤ B) :
    IsCompact (closure (range (fun j => gamma0LocalizedSeedLp φ ha hab hφ N (ψ j)))) := by
  obtain ⟨CK,hCK,hchart⟩ := compact_chart_gamma0_energy_bound
    (spectralCoreChart_compact A a b ha)
  exact spectralCoreLocalization_rellich_hyperbolic_smooth φ ha hab hφ
    (fun j => gamma0PoincareSeed N (ψ j).val)
    (fun j => gamma0SmoothSeed_representative_smooth N (ψ j))
    (mul_nonneg hCK.le hB) (fun j => (hchart N (ψ j)).trans
      (mul_le_mul_of_nonneg_left (henergy j) hCK.le))

end ArtinMatthews
