module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.Analysis.PDE.Schauder.Calculus.Schauder.RadialMoments
public import Mathlib.MeasureTheory.Integral.IntegrableOn
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

/-! Integrability on annuli and radial-weighted second moments. -/

noncomputable section
open _root_.MeasureTheory Set Metric
namespace OAI.Analysis.PDE.Schauder

def normAnnulus {E : Type*} [NormedAddCommGroup E] (r R : ℝ) : Set E :=
  {y | r < ‖y‖ ∧ ‖y‖ < R}

theorem measurableSet_normAnnulus {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] (r R : ℝ) : MeasurableSet (normAnnulus (E := E) r R) :=
  (measurableSet_lt measurable_const continuous_norm.measurable).inter
    (measurableSet_lt continuous_norm.measurable measurable_const)

theorem integrableOn_normAnnulus {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E] [IsFiniteMeasureOnCompacts (volume : Measure E)]
    (f : E → ℝ) (hf : ∀ y ≠ 0, ContinuousAt f y) {r : ℝ} (hr : 0 < r) (R : ℝ) :
    IntegrableOn f (normAnnulus r R) := by
  let K : Set E := closedBall 0 R ∩ {y | r ≤ ‖y‖}
  have hK : IsCompact K := (isCompact_closedBall (0 : E) R).inter_right
    (isClosed_le continuous_const continuous_norm)
  have hc : ContinuousOn f K := by
    intro y hy
    exact (hf y (norm_pos_iff.mp (hr.trans_le hy.2))).continuousWithinAt
  apply (hc.integrableOn_compact hK).mono_set
  intro y hy
  exact ⟨by simpa using hy.2.le, hy.1.le⟩

def annularWeight (p r R : ℝ) (t : ℝ) : ℝ :=
  (Ioo r R).indicator (fun t => t ^ p) t

variable {m : ℕ}

theorem annularWeight_integral (p r R : ℝ) (f : EuclideanSpace ℝ (Fin m) → ℝ) :
    (∫ y, annularWeight p r R ‖y‖ * f y) =
      ∫ y in normAnnulus r R, ‖y‖ ^ p * f y := by
  rw [← integral_indicator (measurableSet_normAnnulus r R)]
  congr 1
  funext y
  by_cases hy : r < ‖y‖ ∧ ‖y‖ < R <;> simp [annularWeight, normAnnulus, hy]

theorem integrable_annularWeight_moment (p : ℝ) {r : ℝ} (hr : 0 < r) (R : ℝ)
    (i j : Fin m) :
    Integrable (fun y : EuclideanSpace ℝ (Fin m) => annularWeight p r R ‖y‖ * y i * y j) := by
  have h := integrableOn_normAnnulus
    (fun y : EuclideanSpace ℝ (Fin m) => ‖y‖ ^ p * y i * y j) (fun y hy =>
      ((continuous_norm.continuousAt.rpow_const (Or.inl (norm_ne_zero_iff.mpr hy))).mul
        (PiLp.continuous_apply 2 (fun _ : Fin m => ℝ) i).continuousAt).mul
          (PiLp.continuous_apply 2 (fun _ : Fin m => ℝ) j).continuousAt) hr R
  have hi := h.integrable_indicator (measurableSet_normAnnulus r R)
  convert! hi using 1
  funext y
  by_cases hy : r < ‖y‖ ∧ ‖y‖ < R <;> simp [annularWeight, normAnnulus, hy]

theorem annularMoment_offDiagonal (p : ℝ) (r R : ℝ) (i j : Fin m) (hij : i ≠ j) :
    (∫ y in normAnnulus r R, (‖y‖ : ℝ) ^ p * (y : EuclideanSpace ℝ (Fin m)) i * y j) = 0 := by
  have h := radialMoment_offDiagonal (annularWeight p r R) i j hij
  simpa only [radialMoment, mul_assoc, annularWeight_integral] using h

theorem annularMoment_trace (p : ℝ) {r : ℝ} (hr : 0 < r) (R : ℝ) (i : Fin m) :
    (m : ℝ) * (∫ y in normAnnulus r R,
      (‖y‖ : ℝ) ^ p * (y : EuclideanSpace ℝ (Fin m)) i * y i) =
      ∫ y in normAnnulus r R, (‖y‖ : ℝ) ^ p * ‖(y : EuclideanSpace ℝ (Fin m))‖ ^ 2 := by
  have h := radialMoment_trace (annularWeight p r R)
    (fun j => integrable_annularWeight_moment p hr R j j) i
  simpa only [radialMoment, mul_assoc, annularWeight_integral] using h

end OAI.Analysis.PDE.Schauder
