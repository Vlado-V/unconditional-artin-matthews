module

public import ArtinMatthews.SpectralGreenWeightLocalization
public import ArtinMatthews.SpectralEisensteinAnalysisCompletion
public import ArtinMatthews.SpectralEisensteinGreenMultiplier
public import ArtinMatthews.SpectralEisensteinGreenIntertwining
public import ArtinMatthews.SpectralEisensteinGreenMoments
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

/-! Actual synthesis-kernel vectors are fiberwise orthogonal to every
completed Eisenstein coefficient vector. This follows from the proved
Green intertwining and separation by the positive Green coordinate. -/
noncomputable section
open Set Filter MeasureTheory
open scoped InnerProductSpace
namespace ArtinMatthews

def gamma0EisensteinChannelPair (N : ℕ) [NeZero N]
    (u v : Gamma0EisensteinSpectralSpace N) (t : ℝ) : ℂ :=
  ∑ i : Gamma0EisensteinCuspClasses N,inner ℂ (u i t) (v i t)

theorem gamma0EisensteinChannelPair_integrable (N : ℕ) [NeZero N]
    (u v : Gamma0EisensteinSpectralSpace N) : Integrable (gamma0EisensteinChannelPair N u v)
      gamma0EisensteinSpectralMeasure :=
  integrable_finsetSum Finset.univ (fun i _ => L2.integrable_inner (u i) (v i))

theorem gamma0EisensteinChannelPair_inner (N : ℕ) [NeZero N]
    (u v : Gamma0EisensteinSpectralSpace N) :
    inner ℂ u v=∫ t,gamma0EisensteinChannelPair N u v t ∂gamma0EisensteinSpectralMeasure := by
  change (∑ i,inner ℂ (u i) (v i))=_
  simp_rw [L2.inner_def]
  exact (integral_finsetSum Finset.univ (fun i _ => L2.integrable_inner (u i) (v i))).symm

theorem gamma0EisensteinGreenWeight_eq_coordinate (t : ℝ) :
    gamma0EisensteinGreenWeight t=(spectralPositiveGreenCoordinate t:ℂ) := by
  rw [gamma0EisensteinGreenWeight,gamma0EnergyGreenWeight_eq_real]
  change (((1/4+t^2+1)⁻¹:ℝ):ℂ)=(((5/4+t^2)⁻¹:ℝ):ℂ)
  congr 2
  ring

theorem gamma0EisensteinChannelPair_power_ae (N : ℕ) [NeZero N]
    (u v : Gamma0EisensteinSpectralSpace N) (n : ℕ) :
    (fun t => gamma0EisensteinChannelPair N u (((gamma0EisensteinGreenMultiplier N)^n) v) t)
      =ᵐ[gamma0EisensteinSpectralMeasure]
        fun t => (spectralPositiveGreenCoordinate t)^n • gamma0EisensteinChannelPair N u v t := by
  have hp : ∀ᵐ t ∂gamma0EisensteinSpectralMeasure,∀ i : Gamma0EisensteinCuspClasses N,
      ((((gamma0EisensteinGreenMultiplier N)^n) v) i) t=gamma0EisensteinGreenWeight t^n*(v i t) := by
    apply ae_all_iff.mpr
    intro i
    rw [gamma0EisensteinGreenMultiplier_power_apply]
    exact gamma0EisensteinGreenScalarOperator_power_ae (v i) n
  filter_upwards [hp] with t ht
  rw [gamma0EisensteinChannelPair,gamma0EisensteinChannelPair,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [ht i,gamma0EisensteinGreenWeight_eq_coordinate,RCLike.inner_apply,RCLike.inner_apply,
    Complex.real_smul,Complex.ofReal_pow]
  ring

theorem gamma0EisensteinSynthesis_kernel_power (N : ℕ) [NeZero N]
    (v : Gamma0EisensteinSpectralSpace N) (hv : (gamma0EisensteinAnalysis N).adjoint v=0) (n : ℕ) :
    (gamma0EisensteinAnalysis N).adjoint (((gamma0EisensteinGreenMultiplier N)^n) v)=0 := by
  induction n with
  | zero => simpa using hv
  | succ n ih =>
    rw [pow_succ',mul_apply_eq_comp]
    exact gamma0EisensteinSynthesis_kernel_green_invariant N _ ih

theorem gamma0EisensteinSynthesis_kernel_moments (N : ℕ) [NeZero N]
    (v : Gamma0EisensteinSpectralSpace N) (hv : (gamma0EisensteinAnalysis N).adjoint v=0)
    (u : Gamma0RegionL2 N) (n : ℕ) :
    (∫ t,(spectralPositiveGreenCoordinate t)^n •
      gamma0EisensteinChannelPair N (gamma0EisensteinAnalysis N u) v t ∂gamma0EisensteinSpectralMeasure)=0 := by
  rw [← integral_congr_ae (gamma0EisensteinChannelPair_power_ae N (gamma0EisensteinAnalysis N u) v n),
    ← gamma0EisensteinChannelPair_inner,← ContinuousLinearMap.adjoint_inner_right,
    gamma0EisensteinSynthesis_kernel_power N v hv n,inner_zero_right]

theorem gamma0EisensteinSynthesis_kernel_fiber (N : ℕ) [NeZero N]
    (v : Gamma0EisensteinSpectralSpace N) (hv : (gamma0EisensteinAnalysis N).adjoint v=0)
    (u : Gamma0RegionL2 N) :
    gamma0EisensteinChannelPair N (gamma0EisensteinAnalysis N u) v=ᵐ[gamma0EisensteinSpectralMeasure] 0 := by
  apply spectralPositiveGreen_moment_unique (gamma0EisensteinChannelPair_integrable N _ v) _
    (gamma0EisensteinSynthesis_kernel_moments N v hv u)
  change ∀ᵐ t ∂(ENNReal.ofReal ((2*Real.pi)⁻¹) • volume.restrict (Ioi 0)),0≤t
  apply Measure.ae_smul_measure
  exact (ae_restrict_mem measurableSet_Ioi).mono (fun t ht => ht.le)

end ArtinMatthews
