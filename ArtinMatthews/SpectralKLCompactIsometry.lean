module

public import ArtinMatthews.SpectralKLSynthesis
public import ArtinMatthews.SpectralKLSynthesisEnergy
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
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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

/-! The genuine KL synthesis isometry for compact positive spectral data.
The measure density is literally 2/pi^2*t*sinh(pi*t). No completeness or
surjectivity is asserted here. -/

noncomputable section
open Set MeasureTheory Filter
open OAI.CubicEisenstein
open scoped Topology ContDiff

namespace ArtinMatthews

def spectralKLPlancherelWeight (t : ℝ) : ℝ := (2/Real.pi^2)*t*Real.sinh (Real.pi*t)

def spectralKLWeightedSynthesis (g : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ t in Ioi (0 : ℝ), schlafliBesselK ((t : ℂ)*Complex.I) x*g t*(spectralKLPlancherelWeight t : ℂ)

theorem spectralKLPlancherelWeight_continuous : Continuous spectralKLPlancherelWeight := by
  unfold spectralKLPlancherelWeight
  fun_prop

theorem spectralKLPlancherelWeight_pos {t : ℝ} (ht : 0 < t) : 0 < spectralKLPlancherelWeight t := by
  unfold spectralKLPlancherelWeight
  exact mul_pos (mul_pos (div_pos two_pos (sq_pos_of_pos Real.pi_pos)) ht)
    (Real.sinh_pos_iff.mpr (mul_pos Real.pi_pos ht))

theorem spectralKLCompact_spectral_energy_integrable (g : ℝ → ℂ) (hg : Continuous g)
    (hgc : HasCompactSupport g) :
    Integrable (fun t : ℝ => spectralKLPlancherelWeight t*‖g t‖^2) := by
  have hc : HasCompactSupport (fun t : ℝ => ‖g t‖^2) :=
    hgc.comp_left (g := fun z : ℂ => ‖z‖^2) (by simp)
  exact (spectralKLPlancherelWeight_continuous.mul (hg.norm.pow 2)).integrable_of_hasCompactSupport hc.mul_left

theorem spectralKLWeightedSynthesis_eq (g : ℝ → ℂ) (hgp : tsupport g ⊆ Ioi (0 : ℝ))
    {x : ℝ} (hx : 0 < x) :
    spectralKLWeightedSynthesis g x =
      spectralKLSynthesis (fun t => (spectralKLPlancherelWeight t : ℂ)*g t) x := by
  have hp : tsupport (fun t => (spectralKLPlancherelWeight t : ℂ)*g t) ⊆ Ioi (0 : ℝ) :=
    tsupport_mul_subset_right.trans hgp
  rw [spectralKLSynthesis_actual _ hp hx]
  unfold spectralKLWeightedSynthesis
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _
  dsimp only
  ring

theorem spectralKLCompact_synthesis_isometry (g : ℝ → ℂ) (hg : Continuous g)
    (hgc : HasCompactSupport g) (hgp : tsupport g ⊆ Ioi (0 : ℝ)) :
    IntegrableOn (fun x : ℝ => ‖spectralKLWeightedSynthesis g x‖^2/x) (Ioi 0) ∧
      (∫ x in Ioi (0 : ℝ), ‖spectralKLWeightedSynthesis g x‖^2/x) =
        ∫ t in Ioi (0 : ℝ), spectralKLPlancherelWeight t*‖g t‖^2 := by
  let f : ℝ → ℂ := fun t => (spectralKLPlancherelWeight t : ℂ)*g t
  have hf : Continuous f := (Complex.continuous_ofReal.comp spectralKLPlancherelWeight_continuous).mul hg
  have hfc : HasCompactSupport f := hgc.mul_left
  have hfp : tsupport f ⊆ Ioi (0 : ℝ) := tsupport_mul_subset_right.trans hgp
  obtain ⟨hi,heq⟩ := spectralKLSynthesis_energy f hf hfc hfp
  have hxpoint (x : ℝ) (hx : 0 < x) :
      x^(-1 : ℝ)*‖spectralKLSynthesis f x‖^2 = ‖spectralKLWeightedSynthesis g x‖^2/x := by
    rw [spectralKLWeightedSynthesis_eq g hgp hx]
    simp only [Real.rpow_neg_one]
    ring
  have his : IntegrableOn (fun x : ℝ => ‖spectralKLWeightedSynthesis g x‖^2/x) (Ioi 0) := by
    apply hi.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact hxpoint x hx
  refine ⟨his,?_⟩
  calc
    _ = ∫ x in Ioi (0 : ℝ), x^(-1 : ℝ)*‖spectralKLSynthesis f x‖^2 := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      exact (hxpoint x hx).symm
    _ = ∫ t : ℝ, (Real.pi^2/(2*t*Real.sinh (Real.pi*t)))*‖f t‖^2 := heq
    _ = ∫ t : ℝ, spectralKLPlancherelWeight t*‖g t‖^2 := by
      apply integral_congr_ae
      filter_upwards with t
      by_cases ht : t ∈ tsupport g
      · have htp := hgp ht
        have hμ := spectralKLPlancherelWeight_pos htp
        dsimp [f]
        rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg hμ.le,mul_pow]
        unfold spectralKLPlancherelWeight
        have ht0 : t ≠ 0 := htp.ne'
        have hs0 : Real.sinh (Real.pi*t) ≠ 0 := (Real.sinh_pos_iff.mpr (mul_pos Real.pi_pos htp)).ne'
        field_simp
      · simp [f,image_eq_zero_of_notMem_tsupport ht]
    _ = _ := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro t ht
      have hn : t ∉ tsupport g := fun h => ht (hgp h)
      simp [image_eq_zero_of_notMem_tsupport hn]

theorem spectralKLCompact_smooth_synthesis_isometry (g : ℝ → ℂ)
    (hg : ContDiffOn ℝ ∞ g (Ioi (0 : ℝ))) (hgc : HasCompactSupport g)
    (hgp : tsupport g ⊆ Ioi (0 : ℝ)) :
    IntegrableOn (fun x : ℝ => ‖spectralKLWeightedSynthesis g x‖^2/x) (Ioi 0) ∧
      (∫ x in Ioi (0 : ℝ), ‖spectralKLWeightedSynthesis g x‖^2/x) =
        ∫ t in Ioi (0 : ℝ), spectralKLPlancherelWeight t*‖g t‖^2 := by
  exact spectralKLCompact_synthesis_isometry g
    (hg.continuousOn.continuous_of_tsupport_subset isOpen_Ioi hgp) hgc hgp

end ArtinMatthews
