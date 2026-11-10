module

public import ArtinMatthews.SpectralLpTestMultiplier
public import ArtinMatthews.SpectralEnergyTest
public import ArtinMatthews.SpectralEisensteinKernelLocalization
public import ArtinMatthews.SpectralEisensteinChannelSurjectivity
public import ArtinMatthews.SpectralEisensteinGreenIntertwining
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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

/-! Actual arbitrary-test multiplication on all Eisenstein channels,
transported through the proved unitary synthesis. -/
noncomputable section
open Set Filter MeasureTheory
open scoped InnerProductSpace BoundedContinuousFunction
namespace ArtinMatthews

def gamma0EisensteinTestMultiplier (N : ℕ) [NeZero N] (h : SpectralEnergyTest) :
    Gamma0EisensteinSpectralSpace N →L[ℂ] Gamma0EisensteinSpectralSpace N :=
  (PiLp.continuousLinearEquiv 2 ℂ
    (fun _ : Gamma0EisensteinCuspClasses N => Lp ℂ 2 gamma0EisensteinSpectralMeasure)).symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.pi (fun i =>
      (spectralLpTestMultiplier gamma0EisensteinSpectralMeasure (spectralContinuousTestSymbol h)).comp
        (ContinuousLinearMap.proj i))).comp
      (PiLp.continuousLinearEquiv 2 ℂ
        (fun _ : Gamma0EisensteinCuspClasses N => Lp ℂ 2 gamma0EisensteinSpectralMeasure)).toContinuousLinearMap)

theorem gamma0EisensteinTestMultiplier_apply (N : ℕ) [NeZero N] (h : SpectralEnergyTest)
    (f : Gamma0EisensteinSpectralSpace N) (i : Gamma0EisensteinCuspClasses N) :
    gamma0EisensteinTestMultiplier N h f i=
      spectralLpTestMultiplier gamma0EisensteinSpectralMeasure (spectralContinuousTestSymbol h) (f i) := rfl

theorem gamma0EisensteinTestMultiplier_norm (N : ℕ) [NeZero N] (h : SpectralEnergyTest)
    (f : Gamma0EisensteinSpectralSpace N) : ‖gamma0EisensteinTestMultiplier N h f‖≤‖h‖*‖f‖ := by
  have hb (i : Gamma0EisensteinCuspClasses N) :
      ‖spectralLpTestValue gamma0EisensteinSpectralMeasure (spectralContinuousTestSymbol h) (f i)‖≤‖h‖*‖f i‖ :=
    (spectralLpTestValue_norm _ _ _).trans
      (mul_le_mul_of_nonneg_right (spectralContinuousTestSymbol_norm h) (norm_nonneg _))
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  rw [PiLp.norm_sq_eq_of_L2,mul_pow,PiLp.norm_sq_eq_of_L2,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  change ‖spectralLpTestValue gamma0EisensteinSpectralMeasure (spectralContinuousTestSymbol h) (f i)‖^2≤‖h‖^2*‖f i‖^2
  have hh := pow_le_pow_left₀ (norm_nonneg _) (hb i) 2
  simpa only [mul_pow] using hh

theorem gamma0EisensteinTestMultiplier_pair_integrable (N : ℕ) [NeZero N] (h : SpectralEnergyTest)
    (f g : Gamma0EisensteinSpectralSpace N) :
    Integrable (fun t => spectralContinuousTestSymbol h t*gamma0EisensteinChannelPair N f g t)
      gamma0EisensteinSpectralMeasure := by
  have hi := integrable_finsetSum Finset.univ (fun i _ =>
    spectralLpTestMultiplier_integrable gamma0EisensteinSpectralMeasure (spectralContinuousTestSymbol h) (f i) (g i))
  apply hi.congr
  exact ae_of_all _ (fun t => by
    change (∑ i,spectralContinuousTestSymbol h t*inner ℂ (f i t) (g i t))=_
    rw [← Finset.mul_sum]
    rfl)

theorem gamma0EisensteinTestMultiplier_inner (N : ℕ) [NeZero N] (h : SpectralEnergyTest)
    (f g : Gamma0EisensteinSpectralSpace N) :
    inner ℂ f (gamma0EisensteinTestMultiplier N h g)=
      ∫ t,spectralContinuousTestSymbol h t*gamma0EisensteinChannelPair N f g t
        ∂gamma0EisensteinSpectralMeasure := by
  change (∑ i,inner ℂ (f i) (spectralLpTestMultiplier gamma0EisensteinSpectralMeasure
    (spectralContinuousTestSymbol h) (g i)))=_
  simp_rw [spectralLpTestMultiplier_inner]
  rw [← integral_finsetSum Finset.univ (fun i _ => spectralLpTestMultiplier_integrable
    gamma0EisensteinSpectralMeasure (spectralContinuousTestSymbol h) (f i) (g i))]
  apply integral_congr_ae
  exact ae_of_all _ (fun t => by
    change (∑ i,spectralContinuousTestSymbol h t*inner ℂ (f i t) (g i t))=
      spectralContinuousTestSymbol h t*(∑ i,inner ℂ (f i t) (g i t))
    exact (Finset.mul_sum _ _ _).symm)

def gamma0ContinuousTestOperator (N : ℕ) [NeZero N] (h : SpectralEnergyTest) :
    Gamma0RegionL2 N →L[ℂ] Gamma0RegionL2 N :=
  (gamma0EisensteinAnalysis N).adjoint.comp
    ((gamma0EisensteinTestMultiplier N h).comp (gamma0EisensteinAnalysis N))

theorem gamma0ContinuousTestOperator_pair (N : ℕ) [NeZero N] (h : SpectralEnergyTest)
    (u v : Gamma0RegionL2 N) :
    inner ℂ u (gamma0ContinuousTestOperator N h v)=
      ∫ t,spectralContinuousTestSymbol h t*
        gamma0EisensteinChannelPair N (gamma0EisensteinAnalysis N u) (gamma0EisensteinAnalysis N v) t
          ∂gamma0EisensteinSpectralMeasure := by
  change inner ℂ u ((gamma0EisensteinAnalysis N).adjoint
    (gamma0EisensteinTestMultiplier N h (gamma0EisensteinAnalysis N v)))=_
  rw [ContinuousLinearMap.adjoint_inner_right,gamma0EisensteinTestMultiplier_inner]

theorem gamma0ContinuousTestOperator_norm (N : ℕ) [NeZero N] (h : SpectralEnergyTest)
    (u : Gamma0RegionL2 N) : ‖gamma0ContinuousTestOperator N h u‖≤‖h‖*‖u‖ := by
  change ‖(gamma0EisensteinAnalysis N).adjoint
    (gamma0EisensteinTestMultiplier N h (gamma0EisensteinAnalysis N u))‖≤_
  rw [gamma0EisensteinSynthesis_norm]
  exact (gamma0EisensteinTestMultiplier_norm N h _).trans
    (mul_le_mul_of_nonneg_left (gamma0EisensteinAnalysis_norm_le N u) (norm_nonneg _))

theorem gamma0ContinuousTestOperator_analysis (N : ℕ) [NeZero N] (h : SpectralEnergyTest)
    (u : Gamma0RegionL2 N) :
    gamma0EisensteinAnalysis N (gamma0ContinuousTestOperator N h u)=
      gamma0EisensteinTestMultiplier N h (gamma0EisensteinAnalysis N u) :=
  gamma0EisensteinAnalysis_synthesis N _

theorem gamma0EisensteinTest_synthesis_pair (N : ℕ) [NeZero N] (h : SpectralEnergyTest)
    (f g : Gamma0EisensteinSpectralSpace N) :
    inner ℂ ((gamma0EisensteinAnalysis N).adjoint f)
      (gamma0ContinuousTestOperator N h ((gamma0EisensteinAnalysis N).adjoint g))=
      ∫ t,spectralContinuousTestSymbol h t*gamma0EisensteinChannelPair N f g t
        ∂gamma0EisensteinSpectralMeasure := by
  rw [gamma0ContinuousTestOperator_pair,gamma0EisensteinAnalysis_synthesis,gamma0EisensteinAnalysis_synthesis]


theorem gamma0EisensteinTestMultiplier_one (N : ℕ) [NeZero N] :
    gamma0EisensteinTestMultiplier N 1=ContinuousLinearMap.id ℂ _ := by
  apply ContinuousLinearMap.ext
  intro f
  apply PiLp.ext
  intro i
  change spectralLpTestMultiplier gamma0EisensteinSpectralMeasure (spectralContinuousTestSymbol 1) (f i)=f i
  rw [show spectralContinuousTestSymbol 1=(1:ℝ →ᵇ ℂ) from rfl,spectralLpTestMultiplier_one]
  rfl

theorem gamma0EisensteinTestMultiplier_green (N : ℕ) [NeZero N] :
    gamma0EisensteinTestMultiplier N spectralGreenEnergyTest=gamma0EisensteinGreenMultiplier N := by
  apply ContinuousLinearMap.ext
  intro f
  apply PiLp.ext
  intro i
  apply Lp.ext
  filter_upwards [spectralLpTestMultiplier_ae gamma0EisensteinSpectralMeasure
      (spectralContinuousTestSymbol spectralGreenEnergyTest) (f i),gamma0EisensteinGreenMultiply_ae (f i)] with t ht hg
  change (spectralLpTestMultiplier gamma0EisensteinSpectralMeasure
    (spectralContinuousTestSymbol spectralGreenEnergyTest) (f i)) t=gamma0EisensteinGreenMultiply (f i) t
  rw [ht,hg,spectralContinuousTestSymbol_green]

theorem gamma0ContinuousTestOperator_one (N : ℕ) [NeZero N] (u : Gamma0RegionL2 N) :
    gamma0ContinuousTestOperator N 1 u=(gamma0EisensteinAnalysis N).adjoint (gamma0EisensteinAnalysis N u) := by
  change (gamma0EisensteinAnalysis N).adjoint (gamma0EisensteinTestMultiplier N 1 (gamma0EisensteinAnalysis N u))=_
  rw [gamma0EisensteinTestMultiplier_one]
  rfl

theorem gamma0ContinuousTestOperator_green (N : ℕ) [NeZero N] (u : Gamma0RegionL2 N) :
    gamma0ContinuousTestOperator N spectralGreenEnergyTest u=
      gamma0Green N ((gamma0EisensteinAnalysis N).adjoint (gamma0EisensteinAnalysis N u)) := by
  change (gamma0EisensteinAnalysis N).adjoint
    (gamma0EisensteinTestMultiplier N spectralGreenEnergyTest (gamma0EisensteinAnalysis N u))=_
  rw [gamma0EisensteinTestMultiplier_green]
  exact gamma0EisensteinSynthesis_green_intertwines N _

end ArtinMatthews
