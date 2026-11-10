module

public import ArtinMatthews.VaryingKummerAnalyticPeriodicTheta
public import ArtinMatthews.VaryingKummerAnalyticMixedTraceDualMatrix
public import ArtinMatthews.VaryingKummerAnalyticMixedTraceDualTheta
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

/-! Exact arithmetic identification of the finite Fourier phases occurring
in mixed ideal-lattice Poisson summation. No principal-ideal or signature
assumption is imposed on the fractional ideal. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open Module NumberField
open ArtinMatthews.ReusedTheta
open scoped NumberField nonZeroDivisors Classical BigOperators
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)

theorem mixedDualIntegerEquiv_trace_coordinates
    (a : I.val) (z : MixedIdealIndex K I → ℤ) :
    (Algebra.trace ℚ K ((a : K) * (mixedDualIntegerEquiv K I z : K)) : ℝ) =
      ∑ i, (((fractionalIdealBasis K I.val).equivFun a) i : ℝ) * (z i : ℝ) := by
  rw [← mixedTraceTransform_inner_eq_trace, mixedDualIntegerEquiv_embedding]
  change inner ℝ (mixedIdealEmbedding K I a) (mixedDualMatrixVector K I z) = _
  have ha := mixedIdealEuclideanBasis_integer_apply K I
    ((fractionalIdealBasis K I.val).equivFun a)
  rw [LinearEquiv.symm_apply_apply] at ha
  rw [← ha, Basis.equivFun_symm_apply, sum_inner]
  simp only [inner_smul_left, RCLike.conj_to_real, mixedDualMatrixVector_pair]

theorem mixedDualIntegerEquiv_trace_int
    (a : I.val) (z : MixedIdealIndex K I → ℤ) :
    Algebra.trace ℚ K ((a : K) * (mixedDualIntegerEquiv K I z : K)) =
      ((∑ i, ((fractionalIdealBasis K I.val).equivFun a) i * z i : ℤ) : ℚ) := by
  exact_mod_cast mixedDualIntegerEquiv_trace_coordinates K I a z

def mixedResidueRepresentative (N : ℕ) (r : MixedIdealIndex K I → Fin N) : I.val :=
  (fractionalIdealBasis K I.val).equivFun.symm (fun i => (r i : ℤ))

theorem mixedResidueRepresentative_trace (N : ℕ)
    (r : MixedIdealIndex K I → Fin N) (z : MixedIdealIndex K I → ℤ) :
    (Algebra.trace ℚ K ((mixedResidueRepresentative K I N r : K) *
      (mixedDualIntegerEquiv K I z : K)) : ℝ) =
      ∑ i, (r i : ℝ) * (z i : ℝ) := by
  rw [mixedDualIntegerEquiv_trace_coordinates]
  simp only [mixedResidueRepresentative, LinearEquiv.apply_symm_apply, Int.cast_natCast]

theorem mixedResidueFourier_phase (N : ℕ)
    (r : MixedIdealIndex K I → Fin N) (z : MixedIdealIndex K I → ℤ) :
    UnitAddTorus.mFourier z (torusProjection (congruencePoint N r)) =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
        ((Algebra.trace ℚ K ((mixedResidueRepresentative K I N r : K) *
          (mixedDualIntegerEquiv K I z : K)) : ℚ) : ℂ) / (N : ℂ)) := by
  have ht := congrArg (fun x : ℝ => (x : ℂ))
    (mixedResidueRepresentative_trace K I N r z)
  push_cast at ht
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, torusProjection,
    fourier_coe_apply, Complex.ofReal_one, div_one]
  rw [← Complex.exp_sum]
  congr 1
  rw [ht, Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  simp only [congruencePoint, Complex.ofReal_div, Complex.ofReal_natCast]
  ring

theorem mixedPeriodicDualWeight_eq_trace_sum (N : ℕ)
    (w : (MixedIdealIndex K I → Fin N) → ℂ) (z : MixedIdealIndex K I → ℤ) :
    periodicDualWeight N w z =
      ∑ r, w r * Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
        ((Algebra.trace ℚ K ((mixedResidueRepresentative K I N r : K) *
          (mixedDualIntegerEquiv K I z : K)) : ℚ) : ℂ) / (N : ℂ)) := by
  unfold periodicDualWeight congruenceThetaFourierWeight
  simp_rw [mixedResidueFourier_phase K I N]

end
end ArtinMatthews.VaryingKummerAnalytic
