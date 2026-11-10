module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.Analysis.PDE.Weak.Boundary.H1Translation
public import Mathlib.MeasureTheory.Function.L2Space
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
public import OAI.Analysis.PDE.Weak.Boundary.Weak.Test
public import OAI.Analysis.PDE.Weak.Elliptic.Adjoint
public import OAI.Analysis.PDE.Weak.Elliptic.Energy


set_option backward.privateInPublic true
@[expose] public section

noncomputable section
open Set _root_.MeasureTheory InnerProductSpace
namespace OAI.Analysis.PDE.Weak

open OAI.Analysis.PDE.Variational

variable {m : ℕ}

/-- The discrete integration-by-parts identity for completed, rather than
only smooth, admissible test functions. -/
theorem WeakDivergenceEquation.shifted_h1Zero_test
    {Ω : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)}
    {H : Lp (OAI.Analysis.PDE.Variational.CellVectors m) 2 (volume : Measure (OAI.Analysis.PDE.Variational.CellCoordinates m))}
    {f : Lp ℝ 2 (volume : Measure (OAI.Analysis.PDE.Variational.CellCoordinates m))}
    (hweak : WeakDivergenceEquation Ω H f)
    (v : OAI.Analysis.PDE.Variational.CellCoordinates m) (h : ℝ) (q : H1Pair m)
    (hq : differenceH1Pair v (-h) q ∈ H1Zero Ω) :
    inner ℝ (differenceQuotientL2 volume v h H) q.2 =
      -inner ℝ f (differenceQuotientL2 volume v (-h) q.1) := by
  have he := hweak.h1Zero_test hq
  change inner ℝ H (differenceQuotientL2 volume v (-h) q.2) =
    inner ℝ f (differenceQuotientL2 volume v (-h) q.1) at he
  rw [inner_differenceQuotientL2, he]

/-- The forcing term is uniformly controlled by the gradient of the
completed test, with no reciprocal-step loss. -/
theorem WeakDivergenceEquation.shifted_h1Zero_test_bound
    {Ω Ω' : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)}
    {H : Lp (OAI.Analysis.PDE.Variational.CellVectors m) 2 (volume : Measure (OAI.Analysis.PDE.Variational.CellCoordinates m))}
    {f : Lp ℝ 2 (volume : Measure (OAI.Analysis.PDE.Variational.CellCoordinates m))}
    (hweak : WeakDivergenceEquation Ω H f)
    (j : Fin (m + 1)) {h : ℝ} (hh : h ≠ 0) {q : H1Pair m}
    (hq : q ∈ H1Zero Ω')
    (hback : differenceH1Pair (Pi.single j 1) (-h) q ∈ H1Zero Ω) :
    |inner ℝ (differenceQuotientL2 volume (Pi.single j 1) h H) q.2| ≤
      ‖f‖ * ‖q.2‖ := by
  rw [hweak.shifted_h1Zero_test (Pi.single j 1) h q hback, abs_neg]
  exact (abs_real_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_left (OAI.Analysis.PDE.Weak.H1Zero.difference_bound hq j (neg_ne_zero.mpr hh)) (norm_nonneg _))

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The coercive algebra after the actual cutoff test is inserted.  The
commutator and the forcing are measured explicitly, not assumed small. -/
theorem coercive_cutoff_energy_bound (A : E →L[ℝ] E) (P U Q R : E)
    {lam Λ F : ℝ} (hlam : 0 < lam) (_ : 0 ≤ Λ) (hF : 0 ≤ F)
    (hA : ‖A‖ ≤ Λ)
    (hell : lam * ‖P‖ ^ 2 ≤ inner ℝ (A P) P)
    (hQ : ‖Q‖ ≤ ‖P‖ + 2 * ‖U‖)
    (heq : |inner ℝ (A P) (P + (2 : ℝ) • U) + inner ℝ R Q| ≤ F * ‖Q‖) :
    ‖P‖ ^ 2 ≤
      ((F + ‖R‖ + 2 * Λ * ‖U‖) ^ 2 / lam +
        4 * (F + ‖R‖) * ‖U‖) / lam := by
  have hcross : |inner ℝ (A P) U| ≤ Λ * ‖P‖ * ‖U‖ :=
    (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right
      ((A.le_opNorm P).trans (mul_le_mul_of_nonneg_right hA (norm_nonneg _)))
      (norm_nonneg _))
  have hr := abs_real_inner_le_norm R Q
  have he := (le_abs_self _).trans heq
  have hl := neg_abs_le (inner ℝ R Q)
  have hc := neg_abs_le (inner ℝ (A P) U)
  have hqmul := mul_le_mul_of_nonneg_left hQ (show 0 ≤ F + ‖R‖ by positivity)
  have hmain : lam * ‖P‖ ^ 2 ≤
      (F + ‖R‖ + 2 * Λ * ‖U‖) * ‖P‖ + 2 * (F + ‖R‖) * ‖U‖ := by
    simp only [inner_add_right, real_inner_smul_right] at he
    nlinarith
  have hy := weightedYoung hlam ‖P‖ (F + ‖R‖ + 2 * Λ * ‖U‖)
  apply (le_div_iff₀ hlam).mpr
  have hi : (F + ‖R‖ + 2 * Λ * ‖U‖) ^ 2 / lam =
      lam⁻¹ * (F + ‖R‖ + 2 * Λ * ‖U‖) ^ 2 := by ring
  rw [hi]
  nlinarith

end OAI.Analysis.PDE.Weak
