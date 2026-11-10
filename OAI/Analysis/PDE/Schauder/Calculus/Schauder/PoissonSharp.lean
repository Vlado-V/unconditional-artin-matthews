module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.Analysis.PDE.Schauder.Calculus.Schauder.PoissonInverse
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
public import Mathlib.Order.CompletePartialOrder
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
public import OAI.Analysis.PDE.Schauder.Calculus.Schauder.Bilinear


set_option backward.privateInPublic true
@[expose] public section

/-! Exponent-preserving Schauder estimate for the genuine inverse Laplacian. -/

noncomputable section
open _root_.MeasureTheory Set Metric InnerProductSpace Laplacian
namespace OAI.Analysis.PDE.Schauder

theorem second_fderiv_const_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (hf : ContDiff ℝ 2 f) (c : ℝ) (x : E) :
    fderiv ℝ (fderiv ℝ (c • f)) x = c • fderiv ℝ (fderiv ℝ f) x := by
  have hDf : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have he : fderiv ℝ (c • f) = c • fderiv ℝ f := by
    funext y
    exact fderiv_const_smul (hf.differentiable (by norm_num) y) c
  rw [he]
  exact fderiv_const_smul (hDf.differentiable one_ne_zero x) c

theorem poissonPotential_hessian_holder {m : ℕ} (hm : 3 ≤ m)
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    ∃ C > 0, ∀ (f : EuclideanSpace ℝ (Fin m) → ℝ),
      ContDiff ℝ 2 f → HasCompactSupport f → ∀ H, 0 ≤ H →
      (∀ x y, |f x - f y| ≤ H * ‖x - y‖ ^ α) → ∀ x z,
      ‖fderiv ℝ (fderiv ℝ (poissonPotential f)) z -
        fderiv ℝ (fderiv ℝ (poissonPotential f)) x‖ ≤ C * H * ‖z - x‖ ^ α := by
  obtain ⟨C, hC, hb⟩ := newtonianPotential_hessian_holder (show 2 ≤ m by omega) hα hα1
  have hn : 0 < |(poissonNormalization m)⁻¹| := abs_pos.mpr (inv_ne_zero (poissonNormalization_ne_zero hm))
  refine ⟨|(poissonNormalization m)⁻¹| * C, mul_pos hn hC, ?_⟩
  intro f hf hfc H hH hh x z
  have hu := contDiff_newtonianPotential (show 1 ≤ m by omega) f hf hfc
  simp only [poissonPotential, second_fderiv_const_smul _ hu]
  have h := mul_le_mul_of_nonneg_left (hb f hf hfc H hH hh x z) hn.le
  have hs (A : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) :
      ‖(poissonNormalization m)⁻¹ • A‖ ≤ |(poissonNormalization m)⁻¹| * ‖A‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro v
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro w
    change ‖(poissonNormalization m)⁻¹ * A v w‖ ≤ _
    rw [norm_mul, Real.norm_eq_abs]
    calc
      _ ≤ |(poissonNormalization m)⁻¹| * (‖A v‖ * ‖w‖) :=
        mul_le_mul_of_nonneg_left ((A v).le_opNorm w) (abs_nonneg _)
      _ ≤ |(poissonNormalization m)⁻¹| * ((‖A‖ * ‖v‖) * ‖w‖) := by
        gcongr
        exact A.le_opNorm v
      _ = _ := by ring
  have hsub (A B : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) :
      (poissonNormalization m)⁻¹ • A - (poissonNormalization m)⁻¹ • B =
        (poissonNormalization m)⁻¹ • (A - B) := by
    ext v w
    change (poissonNormalization m)⁻¹ * A v w - (poissonNormalization m)⁻¹ * B v w =
      (poissonNormalization m)⁻¹ * (A v w - B v w)
    ring
  rw [hsub]
  exact (hs _).trans (by simpa only [mul_assoc] using h)

end OAI.Analysis.PDE.Schauder
