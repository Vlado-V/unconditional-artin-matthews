module

public import ArtinMatthews.SpectralGamma0AllHeightMeanZero
public import ArtinMatthews.SpectralCuspHyperbolicProjectionRepresentative
public import ArtinMatthews.SpectralGamma0GradientCuspBound
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.IsFormallyReal
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

/-! The actual gradient seminorm controls all positive-height cusp residuals. -/
noncomputable section
open Set MeasureTheory Filter
open scoped MatrixGroups
namespace ArtinMatthews

theorem gamma0CuspHeightSeed_residual_eq (N : ℕ) [NeZero N]
    (ψ : h2SmoothCompactSeeds) (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y)
    (henergy : IntegrableOn (h2SectionEnergy (gamma0CuspSection N ψ r))
      (hyperbolicCuspStrip (N : ℝ) Y)) :
    let G := spectralSectionCuspSmoothCore (gamma0CuspSection N ψ r)
      (gamma0CuspSection_smooth N ψ r) (Nat.cast_pos.mpr (NeZero.pos N)) hY henergy
    gamma0CuspHeightSeedLp N r Y hY ψ -
      cuspHyperbolicAverageProjection (N : ℝ) Y hY (gamma0CuspHeightSeedLp N r Y hY ψ) =
      spectralCuspProjectedLp G.smooth (Nat.cast_pos.mpr (NeZero.pos N)) hY
        G.energy_integrable := by
  dsimp only
  let G := spectralSectionCuspSmoothCore (gamma0CuspSection N ψ r)
    (gamma0CuspSection_smooth N ψ r) (Nat.cast_pos.mpr (NeZero.pos N)) hY henergy
  have hstrip : MeasurableSet (hyperbolicCuspStrip (N : ℝ) Y) :=
    (measurableSet_Ioc.preimage UpperHalfPlane.continuous_re.measurable).inter
      (measurableSet_Ioi.preimage UpperHalfPlane.continuous_im.measurable)
  have he : (fun z : UpperHalfPlane => G.toFun (z.re,z.im))
      =ᵐ[volume.restrict (hyperbolicCuspStrip (N : ℝ) Y)] gamma0CuspSection N ψ r := by
    filter_upwards [ae_restrict_mem hstrip] with z hz
    exact spectralSectionSmoothExtension_at_upper hY (gamma0CuspSection N ψ r) z hz.2.le
  have hm := (memLp_congr_ae he).mpr (gamma0CuspSection_memLp_positive_height N ψ r Y hY)
  have hlp : hm.toLp (fun z : UpperHalfPlane => G.toFun (z.re,z.im)) =
      gamma0CuspHeightSeedLp N r Y hY ψ := by
    apply Lp.ext
    exact hm.coeFn_toLp.trans (he.trans (gamma0CuspHeightSeedLp_ae N r Y hY ψ).symm)
  have hp := cuspHyperbolicMeanZero_ae_representative (N : ℝ) Y
    (Nat.cast_pos.mpr (NeZero.pos N)) hY G.toFun G.smooth.continuous hm
  rw [hlp] at hp
  apply Lp.ext
  exact hp.trans (spectralCuspProjectedLp_ae G.smooth
    (Nat.cast_pos.mpr (NeZero.pos N)) hY G.energy_integrable).symm

theorem gamma0CuspHeightSeed_residual_gradient_bound (N : ℕ) [NeZero N]
    (Y : ℝ) (hY : 0 < Y) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ψ : h2SmoothCompactSeeds) (r : SL(2, ℤ)),
      ‖gamma0CuspHeightSeedLp N r Y hY ψ -
        cuspHyperbolicAverageProjection (N : ℝ) Y hY
          (gamma0CuspHeightSeedLp N r Y hY ψ)‖^2 ≤ C*‖gamma0SeedGradient N ψ‖^2 := by
  obtain ⟨C,hC,hb⟩ := gamma0_cusp_positive_height_gradient_bound N Y hY
  have hw : 0 < (N : ℝ) := Nat.cast_pos.mpr (NeZero.pos N)
  refine ⟨((N:ℝ)/Y)^2*C,mul_pos (sq_pos_of_pos (div_pos hw hY)) hC,?_⟩
  intro ψ r
  let G := spectralSectionCuspSmoothCore (gamma0CuspSection N ψ r)
    (gamma0CuspSection_smooth N ψ r) hw hY (hb ψ r).1
  have hn := spectralCuspProjectedLp_norm_le G.smooth hw hY G.energy_integrable
  have hs := (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (div_nonneg hw.le hY.le) (norm_nonneg _))).mpr hn
  rw [mul_pow,spectralCuspDerivativeLp_norm_square] at hs
  have he : (∫ y in Ioi Y, cuspHorizontalEnergy G.toFun (N:ℝ) y) ≤
      C*‖gamma0SeedGradient N ψ‖^2 :=
    (spectralSectionSmoothExtension_cusp_energy (gamma0CuspSection N ψ r)
      (gamma0CuspSection_smooth N ψ r) hw hY (hb ψ r).1).2.trans (hb ψ r).2
  rw [gamma0CuspHeightSeed_residual_eq N ψ r Y hY (hb ψ r).1]
  exact hs.trans ((mul_le_mul_of_nonneg_left he (sq_nonneg _)).trans_eq (by ring))

theorem gamma0CuspHeightRestriction_residual_gradient_bound (N : ℕ) [NeZero N]
    (Y : ℝ) (hY : 0 < Y) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : gamma0EnergySpace N) (r : SL(2, ℤ)),
      ‖gamma0CuspHeightRestriction N r Y hY u -
        cuspHyperbolicAverageProjection (N : ℝ) Y hY
          (gamma0CuspHeightRestriction N r Y hY u)‖^2 ≤ C*‖gamma0EnergyGradient N u‖^2 := by
  obtain ⟨C,hC,hb⟩ := gamma0CuspHeightSeed_residual_gradient_bound N Y hY
  refine ⟨C,hC,?_⟩
  intro u r
  let R := gamma0CuspHeightRestriction N r Y hY -
    (cuspHyperbolicAverageProjection (N : ℝ) Y hY).comp (gamma0CuspHeightRestriction N r Y hY)
  change ‖R u‖^2 ≤ C*‖gamma0EnergyGradient N u‖^2
  apply isClosed_property (gamma0EnergyTest_dense N)
    (isClosed_le (R.continuous.norm.pow 2)
      (continuous_const.mul ((gamma0EnergyGradient N).continuous.norm.pow 2)))
  intro ψ
  change ‖gamma0CuspHeightRestriction N r Y hY (gamma0EnergyTest N ψ) -
    cuspHyperbolicAverageProjection (N : ℝ) Y hY
      (gamma0CuspHeightRestriction N r Y hY (gamma0EnergyTest N ψ))‖^2 ≤
        C*‖gamma0EnergyGradient N (gamma0EnergyTest N ψ)‖^2
  rw [gamma0CuspHeightRestriction_apply,gamma0EnergyGradient_test]
  exact hb ψ r

theorem gamma0AllHeightMeanZeroEnergy_restriction_eq_zero_of_gradient_eq_zero
    (N : ℕ) [NeZero N] (u : gamma0AllHeightMeanZeroEnergy N)
    (hu : gamma0EnergyGradient N u.val = 0)
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) :
    gamma0CuspHeightRestriction N r Y hY u.val = 0 := by
  obtain ⟨C,_,hb⟩ := gamma0CuspHeightRestriction_residual_gradient_bound N Y hY
  have h := hb u.val r
  have hm := (mem_gamma0AllHeightMeanZeroEnergy_iff N u.val).mp u.property r Y hY
  rw [hm,sub_zero,hu,norm_zero,zero_pow (by norm_num : (2:ℕ) ≠ 0),mul_zero] at h
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp (le_antisymm h (sq_nonneg _)))

end ArtinMatthews
