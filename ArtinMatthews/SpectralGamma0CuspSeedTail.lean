module

public import ArtinMatthews.SpectralGamma0CuspGraphCore
public import ArtinMatthews.SpectralCuspProjectedTail
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

/-! Actual mean-zero cusp mass of genuine arithmetic compact seeds. -/

noncomputable section
open Set MeasureTheory Filter
open scoped MatrixGroups ContDiff

namespace ArtinMatthews

theorem spectralSection_extension_residual {Y : ℝ} (hY : 0 < Y)
    (F : UpperHalfPlane → ℂ) (w : ℝ) {p : ℝ × ℝ} (hp : Y ≤ p.2) :
    cuspMeanZeroRepresentative w (spectralSectionSmoothExtension Y F) p =
      cuspMeanZeroRepresentative w (spectralSectionPlane F) p := by
  have he : (fun x => spectralSectionSmoothExtension Y F (x,p.2)) =
      (fun x => spectralSectionPlane F (x,p.2)) :=
    funext (fun _ => spectralSectionSmoothExtension_eq hY F hp)
  unfold cuspMeanZeroRepresentative cuspAverageRepresentative cuspHorizontalMean
  rw [spectralSectionSmoothExtension_eq hY F hp,he]

/-- After subtracting the literal horizontal average, every actual compact
seed has quadratic cusp escape-of-mass decay in the global energy norm. -/
theorem gamma0CuspSeed_projected_tail_bound (N : ℕ) [NeZero N]
    (ψ : h2SmoothCompactSeeds) (r : SL(2, ℤ)) {Y : ℝ} (hY : 1 ≤ Y) :
    (∫ z in hyperbolicCuspStrip (N : ℝ) Y,
      ‖cuspMeanZeroRepresentative (N : ℝ)
        (spectralSectionPlane (gamma0CuspSection N ψ r)) (z.re,z.im)‖^2) ≤
      ((N : ℝ)^2/Y^2) * (((N : ℝ)+1)*‖gamma0EnergyTest N ψ‖^2) := by
  let G := gamma0CuspSmoothCore N ψ r
  have hw : 0 < (N : ℝ) := Nat.cast_pos.mpr (NeZero.pos N)
  have hYpos : 0 < Y := zero_lt_one.trans_le hY
  have hi : IntegrableOn (cuspHorizontalEnergy G.toFun (N : ℝ)) (Ioi Y) :=
    G.energy_integrable.mono_set (fun _ hy => hY.trans_lt hy)
  have ht := hyperbolic_cusp_projected_tail_bound G.smooth.continuous hw hYpos
    (fun _ _ => G.smooth.comp (contDiff_id.prodMk contDiff_const)) hi
  have he : (∫ z in hyperbolicCuspStrip (N : ℝ) Y,
      ‖cuspMeanZeroRepresentative (N : ℝ) G.toFun (z.re,z.im)‖^2) =
      (∫ z in hyperbolicCuspStrip (N : ℝ) Y,
      ‖cuspMeanZeroRepresentative (N : ℝ)
        (spectralSectionPlane (gamma0CuspSection N ψ r)) (z.re,z.im)‖^2) := by
    apply setIntegral_congr_fun
      ((measurableSet_Ioc.preimage UpperHalfPlane.continuous_re.measurable).inter
        (measurableSet_Ioi.preimage UpperHalfPlane.continuous_im.measurable))
    intro z hz
    change ‖cuspMeanZeroRepresentative (N : ℝ)
      (spectralSectionSmoothExtension 1 (gamma0CuspSection N ψ r)) (z.re,z.im)‖^2 = _
    rw [spectralSection_extension_residual zero_lt_one _ _ (hY.trans hz.2.le)]
  rw [he] at ht
  apply ht.trans
  apply mul_le_mul_of_nonneg_left _ (div_nonneg (sq_nonneg _) (sq_nonneg _))
  calc
    _ ≤ ∫ y in Ioi (1 : ℝ), cuspHorizontalEnergy G.toFun (N : ℝ) y :=
      setIntegral_mono_set G.energy_integrable
        (Eventually.of_forall (fun y => cuspHorizontalEnergy_nonneg _ hw.le y))
        (Eventually.of_forall (fun _ hy => hY.trans_lt hy))
    _ ≤ ((N : ℝ)+1)*‖gamma0EnergyTest N ψ‖^2 := gamma0CuspSmoothCore_energy_bound N ψ r

end ArtinMatthews
