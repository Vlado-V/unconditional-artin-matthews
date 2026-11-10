module

public import ArtinMatthews.SpectralWeylHeightCutoff
public import Mathlib.Analysis.RCLike.Sqrt
public import ArtinMatthews.SpectralKLPowerAnalysis
public import ArtinMatthews.SpectralNativeEigenOrder
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Literal height cutoffs pass through the actual K-order integral
throughout the closed ambient eigenvalue strip. -/

noncomputable section
open Set MeasureTheory Filter OAI.CubicEisenstein
open scoped Topology
namespace ArtinMatthews

theorem spectralKLPower_order_cutoff_tendsto (f : ℝ → ℂ) (hf : Measurable f)
    {a M B β : ℝ} (ha : 0 < a) (hM : 0 ≤ M) (hβ : 0 ≤ β) (hβB : β < B)
    (hpower : ∀ x, 0 < x → ‖f x‖ ≤ M*x^B) (ν : ℂ) (hν : |ν.re| ≤ β) :
    Tendsto (fun K : ℕ => ∫ x in Ioi (0 : ℝ), schlafliBesselK ν x*
      (spectralWeylProfileCutoff a K f x/(x : ℂ))) atTop
      (𝓝 (∫ x in Ioi (0 : ℝ), schlafliBesselK ν x*(f x/(x : ℂ)))) := by
  have hi := spectralKLPower_analysis_integrable f hf M B β hM hβ hβB hpower ν hν
  have hik (K : ℕ) := spectralKLPower_analysis_integrable (spectralWeylProfileCutoff a K f)
    (spectralWeylProfileCutoff_measurable a K f hf) M B β hM hβ hβB
    (fun x hx => (spectralWeylProfileCutoff_norm_le a K f x).trans (hpower x hx)) ν hν
  apply tendsto_integral_of_dominated_convergence
    (fun x => ‖schlafliBesselK ν x*(f x/(x : ℂ))‖)
  · exact fun K => (hik K).aestronglyMeasurable
  · exact hi.norm
  · intro K
    filter_upwards with x
    change ‖schlafliBesselK ν x*(spectralWeylProfileCutoff a K f x/(x : ℂ))‖ ≤
      ‖schlafliBesselK ν x*(f x/(x : ℂ))‖
    have he : schlafliBesselK ν x*(spectralWeylProfileCutoff a K f x/(x : ℂ)) =
        (spectralHeightAnnularPartial K (a*x) : ℂ)*(schlafliBesselK ν x*(f x/(x : ℂ))) := by
      unfold spectralWeylProfileCutoff
      ring
    rw [he,norm_mul,Complex.norm_real,
      Real.norm_of_nonneg (spectralHeightAnnularPartial_bounds K (a*x)).1]
    exact mul_le_of_le_one_left (norm_nonneg _) (spectralHeightAnnularPartial_bounds K (a*x)).2
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    apply tendsto_const_nhds.congr'
    filter_upwards [spectralHeightAnnularPartial_eventually_one (mul_pos ha hx)] with K hK
    simp only [spectralWeylProfileCutoff,hK,Complex.ofReal_one,one_mul]

theorem spectralKLPower_eigen_order_integrable (f : ℝ → ℂ) (hf : Measurable f)
    {M B : ℝ} (hM : 0 ≤ M) (hB : 1/2 < B)
    (hpower : ∀ x, 0 < x → ‖f x‖ ≤ M*x^B) (eig : ℝ) (heig : 0 ≤ eig) :
    IntegrableOn (fun x : ℝ => schlafliBesselK (Complex.sqrt (1/4-(eig : ℂ))) x*
      (f x/(x : ℂ))) (Ioi (0 : ℝ)) :=
  spectralKLPower_analysis_integrable f hf M B (1/2) hM (by norm_num) hB hpower _
    (spectralNonnegativeEnergy_order_abs_re_le eig heig)

end ArtinMatthews
