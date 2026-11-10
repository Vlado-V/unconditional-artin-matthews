module

public import ArtinMatthews.SpectralCuspFourierODEHorizontal
public import ArtinMatthews.CuspAverageProjectionOperator
public import ArtinMatthews.SpectralCuspFourierODEDifferentiation
public import ArtinMatthews.CuspAverageProjectionIntegral
public import ArtinMatthews.SpectralCuspHyperbolicProjectionRepresentative
public import ArtinMatthews.SpectralCuspVerticalEnergy
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! A bounded phase-weighted horizontal projection in the actual strip L²
spaces.  The strip width and phase period are separate parameters. -/

noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal

namespace ArtinMatthews

theorem cuspFourierPhase_norm (T : ℝ) (n : ℤ) (x : ℝ) :
    ‖cuspFourierPhase T n x‖ = 1 := by
  rw [cuspFourierPhase, Complex.norm_exp]
  have hr : (-((cuspFourierFrequency T n : ℝ) : ℂ) * Complex.I * x).re = 0 := by
    simp
  rw [hr, Real.exp_zero]

theorem cuspFourierMultiply_memLp (w Y T : ℝ) (n : ℤ) (f : CuspStripL2 w Y) :
    MemLp (fun p : ℝ × ℝ => cuspFourierPhase T n p.1 * f p) 2 (cuspStripMeasure w Y) := by
  apply (Lp.memLp f).congr_norm
  · exact (((cuspFourierPhase_contDiff T n).continuous.comp continuous_fst).aestronglyMeasurable).mul
      (Lp.aestronglyMeasurable f)
  · exact Eventually.of_forall fun p => by rw [norm_mul, cuspFourierPhase_norm, one_mul]

def cuspFourierMultiplyLp (w Y T : ℝ) (n : ℤ) (f : CuspStripL2 w Y) : CuspStripL2 w Y :=
  (cuspFourierMultiply_memLp w Y T n f).toLp (fun p => cuspFourierPhase T n p.1 * f p)

theorem cuspFourierMultiplyLp_ae (w Y T : ℝ) (n : ℤ) (f : CuspStripL2 w Y) :
    cuspFourierMultiplyLp w Y T n f =ᵐ[cuspStripMeasure w Y]
      fun p => cuspFourierPhase T n p.1 * f p :=
  (cuspFourierMultiply_memLp w Y T n f).coeFn_toLp

def cuspFourierMultiplier (w Y T : ℝ) (n : ℤ) :
    CuspStripL2 w Y →ₗᵢ[ℂ] CuspStripL2 w Y where
  toFun := cuspFourierMultiplyLp w Y T n
  map_add' f g := by
    apply Lp.ext
    filter_upwards [cuspFourierMultiplyLp_ae w Y T n (f + g),
      cuspFourierMultiplyLp_ae w Y T n f, cuspFourierMultiplyLp_ae w Y T n g,
      Lp.coeFn_add f g, Lp.coeFn_add (cuspFourierMultiplyLp w Y T n f)
        (cuspFourierMultiplyLp w Y T n g)] with p hfg hf hg hadd hsum
    rw [hfg, hsum]
    change _ = cuspFourierMultiplyLp w Y T n f p + cuspFourierMultiplyLp w Y T n g p
    rw [hf, hg]
    rw [hadd]
    simp only [Pi.add_apply]
    ring
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [cuspFourierMultiplyLp_ae w Y T n (c • f),
      cuspFourierMultiplyLp_ae w Y T n f, Lp.coeFn_smul c f,
      Lp.coeFn_smul c (cuspFourierMultiplyLp w Y T n f)] with p hcf hf hsmul hresult
    simp only [RingHom.id_apply]
    rw [hcf, hresult]
    change _ = c * cuspFourierMultiplyLp w Y T n f p
    rw [hf]
    rw [hsmul]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  norm_map' f := by
    change ‖cuspFourierMultiplyLp w Y T n f‖ = ‖f‖
    apply le_antisymm
    · apply Lp.norm_le_norm_of_ae_le
      filter_upwards [cuspFourierMultiplyLp_ae w Y T n f] with p hp
      rw [hp, norm_mul, cuspFourierPhase_norm, one_mul]
    · apply Lp.norm_le_norm_of_ae_le
      filter_upwards [cuspFourierMultiplyLp_ae w Y T n f] with p hp
      rw [hp, norm_mul, cuspFourierPhase_norm, one_mul]

def cuspFourierProjection (w Y T : ℝ) (n : ℤ) :
    CuspStripL2 w Y →L[ℂ] CuspVerticalL2 w Y :=
  (cuspVerticalPullback w Y).toContinuousLinearMap.adjoint.comp
    (cuspFourierMultiplier w Y T n).toContinuousLinearMap

theorem cuspFourierProjection_norm_apply (w Y T : ℝ) (n : ℤ) (f : CuspStripL2 w Y) :
    ‖cuspFourierProjection w Y T n f‖ ≤ ‖f‖ := by
  have hV := (cuspVerticalPullback w Y).norm_toContinuousLinearMap_le
  have hVa : ‖(cuspVerticalPullback w Y).toContinuousLinearMap.adjoint‖ ≤ 1 := by
    simpa only [ContinuousLinearMap.adjoint.norm_map] using hV
  exact ((cuspVerticalPullback w Y).toContinuousLinearMap.adjoint.le_opNorm _).trans
    (by
        change ‖(cuspVerticalPullback w Y).toContinuousLinearMap.adjoint‖ *
          ‖cuspFourierMultiplier w Y T n f‖ ≤ ‖f‖
        rw [(cuspFourierMultiplier w Y T n).norm_map]
        exact mul_le_of_le_one_left (norm_nonneg f) hVa)

theorem cuspFourierProjection_ae (w Y T : ℝ) (hw : 0 < w) (n : ℤ) (f : CuspStripL2 w Y) :
    cuspFourierProjection w Y T n f =ᵐ[cuspVerticalMeasure Y]
      cuspHorizontalWeightedMean w (cuspFourierPhase T n) f := by
  have h := cuspVerticalAdjoint_ae_horizontalMean w Y hw (cuspFourierMultiplyLp w Y T n f)
  have he := cuspHorizontalMean_congr_ae w Y (cuspFourierMultiplyLp_ae w Y T n f)
  exact h.trans he

theorem cuspFourierProjection_integrable_energy (w Y T : ℝ)
    (hw : 0 < w) (hY : 0 < Y) (n : ℤ) (f : CuspStripL2 w Y) :
    IntegrableOn (fun y : ℝ => ‖cuspFourierProjection w Y T n f y‖ ^ 2 / y ^ 2) (Ioi Y) :=
  cuspVerticalL2_integrable_energy hw hY _

end ArtinMatthews
