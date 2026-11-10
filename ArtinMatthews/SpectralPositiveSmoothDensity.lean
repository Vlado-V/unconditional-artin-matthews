module

public import ArtinMatthews.SpectralKLPositiveSmoothDensity
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Normed.Lp.SmoothApprox
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

/-! Positive compact smooth density for an actual locally finite measure
supported on the open positive half-line, including restricted Lebesgue. -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff

namespace ArtinMatthews

theorem spectral_positive_measure_memLp_compact (μ : Measure ℝ) [IsFiniteMeasureOnCompacts μ]
    (g : ℝ → ℂ) (hg : Continuous g) (hgc : HasCompactSupport g) : MemLp g 2 μ :=
  hg.memLp_of_hasCompactSupport hgc

theorem spectral_positive_cutoff_toLp_tendsto (μ : Measure ℝ) [IsFiniteMeasureOnCompacts μ]
    (hμ : ∀ᵐ t ∂μ, 0 < t) (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) :
    Tendsto (fun n : ℕ => (spectral_positive_measure_memLp_compact μ
      (fun t => (spectralKLPositiveCutoff n t : ℂ)*g t)
      ((spectralKLPositiveCutoff_contDiff n).mul hg).continuous hgc.mul_left).toLp
        (fun t => (spectralKLPositiveCutoff n t : ℂ)*g t)) atTop
      (𝓝 ((spectral_positive_measure_memLp_compact μ g hg.continuous hgc).toLp g)) := by
  have hgm := spectral_positive_measure_memLp_compact μ g hg.continuous hgc
  apply spectral_L2_toLp_tendsto_of_dominated _ _ g hgm (fun t => 4*‖g t‖^2)
    (((memLp_two_iff_integrable_sq_norm hgm.aestronglyMeasurable).mp hgm).const_mul 4)
  · intro n
    filter_upwards with t
    have hm : ‖(spectralKLPositiveCutoff n t : ℂ)*g t-g t‖ ≤ 2*‖g t‖ := by
      calc
        _ ≤ ‖(spectralKLPositiveCutoff n t : ℂ)*g t‖+‖g t‖ := norm_sub_le _ _
        _ ≤ ‖g t‖+‖g t‖ := by
          rw [norm_mul]
          exact add_le_add (mul_le_of_le_one_left (norm_nonneg (g t)) (spectralKLPositiveCutoff_norm_le_one n t)) le_rfl
        _ = _ := by ring
    nlinarith [norm_nonneg ((spectralKLPositiveCutoff n t : ℂ)*g t-g t),norm_nonneg (g t)]
  · filter_upwards [hμ] with t ht
    apply tendsto_const_nhds.congr'
    filter_upwards [spectralKLPositiveCutoff_eventually_one ht] with n hn
    simp [hn]

theorem spectral_positive_measure_dense_smooth (μ : Measure ℝ) [IsFiniteMeasureOnCompacts μ]
    (hμ : ∀ᵐ t ∂μ, 0 < t) :
    Dense {u : Lp ℂ 2 μ | ∃ g : ℝ → ℂ, u =ᵐ[μ] g ∧ HasCompactSupport g ∧
      ContDiff ℝ ∞ g ∧ tsupport g ⊆ Ioi (0 : ℝ)} := by
  have hd : Dense {u : Lp ℂ 2 μ | ∃ g : ℝ → ℂ,
      u =ᵐ[μ] g ∧ HasCompactSupport g ∧ ContDiff ℝ ∞ g} :=
    Lp.dense_hasCompactSupport_contDiff (by norm_num)
  have hs : {u : Lp ℂ 2 μ | ∃ g : ℝ → ℂ, u =ᵐ[μ] g ∧ HasCompactSupport g ∧ ContDiff ℝ ∞ g} ⊆
      closure {u : Lp ℂ 2 μ | ∃ g : ℝ → ℂ, u =ᵐ[μ] g ∧ HasCompactSupport g ∧
        ContDiff ℝ ∞ g ∧ tsupport g ⊆ Ioi (0 : ℝ)} := by
    intro u hu
    obtain ⟨g,hug,hgc,hg⟩ := hu
    have hmeq : (spectral_positive_measure_memLp_compact μ g hg.continuous hgc).toLp g = u := by
      apply Lp.ext
      exact (MemLp.coeFn_toLp _).trans hug.symm
    rw [← hmeq]
    apply mem_closure_of_tendsto (spectral_positive_cutoff_toLp_tendsto μ hμ g hg hgc)
    apply Filter.Eventually.of_forall
    intro n
    obtain ⟨hc,hdiff,hpos⟩ := spectralKLPositiveCutoff_mul_properties g hg hgc n
    exact ⟨_,MemLp.coeFn_toLp _,hc,hdiff,hpos⟩
  intro u
  exact (closure_minimal hs isClosed_closure) (hd u)

def spectralKLPositiveLebesgueMeasure : Measure ℝ := volume.restrict (Ioi 0)

instance spectralKLPositiveLebesgueMeasure_locallyFinite : IsLocallyFiniteMeasure spectralKLPositiveLebesgueMeasure := by
  unfold spectralKLPositiveLebesgueMeasure
  infer_instance

theorem spectralKLPositiveLebesgue_dense_smooth :
    Dense {u : Lp ℂ 2 spectralKLPositiveLebesgueMeasure | ∃ g : ℝ → ℂ,
      u =ᵐ[spectralKLPositiveLebesgueMeasure] g ∧ HasCompactSupport g ∧
        ContDiff ℝ ∞ g ∧ tsupport g ⊆ Ioi (0 : ℝ)} :=
  spectral_positive_measure_dense_smooth _ (ae_restrict_mem measurableSet_Ioi)

end ArtinMatthews
