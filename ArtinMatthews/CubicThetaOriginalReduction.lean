module

public import ArtinMatthews.CubicThetaShiftedCorrelation
public import ArtinMatthews.ShiftedSourceNormalization
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

/-! Instantiate the circle reduction at the original source g(n), with its
actual normalized Schwartz functions and explicit finite support cutoffs. -/

noncomputable section
open Complex UpperHalfPlane Set OAI
open scoped MatrixGroups ContDiff BigOperators
namespace ArtinMatthews

theorem thetaShiftedCorrelation_nonzero_error
    (N : ℕ) [NeZero N] (hN : 3 ∣ N) (f : CuspForm (cubicThetaKernel N) 1)
    (χ : SevenEighths.HeckeFamily.Character)
    (hcoeff : ∀ n, (qExpansion 1 f).coeff n = idealThetaCoeff χ n)
    (m1 m2 L : ℕ) (hL : 0 < L)
    (hm1 : 0 < m1) (hm2 : 0 < m2) (hne : m1 ≠ m2)
    (hsq1 : Squarefree m1) (hsq2 : Squarefree m2)
    (T : ℝ) (hT : 1 ≤ T) (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g)
    (hgs : Function.support g ⊆ Icc T (2*T)) :
    let K1 := (m1 : ℝ)*T
    let K2 := (m2 : ℝ)*T
    let W1 := shiftedSourceTranslate
      (normalizedSourceSchwartz g hg T (by linarith) hgs) (1/K1)
    let W2 := shiftedSourceTranslate sourcePlateauSchwartz (1/K2)
    let T1 := ⌈1 + 2*K1⌉₊
    let T2 := ⌈1 + 5*K2/2⌉₊
    let D := shiftedCommonPrimePart m1 m2
    let m3 := m1 / m1.gcd m2
    let m4 := m2 / m1.gcd m2
    ‖thetaShiftedCorrelation χ m1 m2 g -
      thetaDualNonzeroCircleAverage χ W1 W2 K1 K2 D m3 m4 (N*D^2) (m3*m4) L‖ ≤
      circleThetaSourceError χ m1 m2 T1 T2 (shiftedSourceTest g m1) (shiftedSourceMajorant m2 T)
        (N*D^2) (m3*m4) L +
      ‖thetaDualZeroCircleAverage χ W1 W2 K1 K2 D m3 m4 (N*D^2) (m3*m4) L‖ := by
  intro K1 K2 W1 W2 T1 T2 D m3 m4
  have hm1R : (0 : ℝ) < m1 := by exact_mod_cast hm1
  have hm2R : (0 : ℝ) < m2 := by exact_mod_cast hm2
  have hTp : 0 < T := by linarith
  have hK1 : 0 < K1 := mul_pos hm1R hTp
  have hK2 : 0 < K2 := mul_pos hm2R hTp
  have hscale1 : 1 ≤ K1 := by
    dsimp [K1]
    have hm : (1 : ℝ) ≤ m1 := by exact_mod_cast hm1
    nlinarith [mul_nonneg (sub_nonneg.mpr hm) (sub_nonneg.mpr hT)]
  have hscale2 : 1 ≤ K2 := by
    dsimp [K2]
    have hm : (1 : ℝ) ≤ m2 := by exact_mod_cast hm2
    nlinarith [mul_nonneg (sub_nonneg.mpr hm) (sub_nonneg.mpr hT)]
  have hH1 : (fun x => W1 (x/K1)) = shiftedSourceTest g m1 := by
    funext x
    exact (shiftedSourceTest_eq_normalized g hg T m1 hTp hm1R hgs x).symm
  have hH2 : (fun x => W2 (x/K2)) = shiftedSourceMajorant m2 T := by
    funext x
    exact (shiftedSourceMajorant_eq_normalized m2 T x).symm
  have hv1 : 1 + 2*(m1 : ℝ)*T ≤ T1 := by
    simpa only [mul_assoc] using Nat.le_ceil (1 + 2*K1)
  have hv2 : 1 + 5*(m2 : ℝ)*T/2 ≤ T2 := by
    simpa only [mul_assoc] using Nat.le_ceil (1 + 5*K2/2)
  have hfinite := thetaShiftedCorrelation_eq_finite χ m1 m2 T1 T2 hm1 hm2 T hTp g hgs hv1
    (show 1 + 2*(m2 : ℝ)*T ≤ T2 by nlinarith)
  have hred := thetaShiftedFiniteSum_nonzero_error N hN f χ hcoeff
    m1 m2 T1 T2 L hL hm1 hm2 hne hsq1 hsq2 W1 W2 K1 K2 hK1 hK2 3 (7/2)
    (by norm_num) (by norm_num)
    (shiftedSourceTest_normalized_support g hg T m1 hTp hgs hscale1)
    (shiftedSourceMajorant_normalized_support m2 T hscale2)
    (by rw [hH1]; exact shiftedSourceTest_smooth g hg m1)
    (by rw [hH2]; exact shiftedSourceMajorant_smooth m2 T)
    (1+(m1 : ℝ)*T) (1+2*(m1 : ℝ)*T) (1+(m2 : ℝ)*T/2) (1+5*(m2 : ℝ)*T/2)
    (by positivity) (by positivity) hv1 hv2
    (by rw [hH1]; exact shiftedSourceTest_support g T m1 hm1R hgs)
    (by rw [hH2]; exact shiftedSourceMajorant_support m2 T hm2R hTp)
  dsimp only at hred
  rw [hH1, hH2, ← hfinite] at hred
  exact hred

end ArtinMatthews
