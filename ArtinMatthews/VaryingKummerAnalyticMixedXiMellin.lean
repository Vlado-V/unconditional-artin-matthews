module

public import ArtinMatthews.VaryingKummerAnalyticMixedComplexMellin
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The previously constructed entire unit-averaged xi is the actual iterated
Mellin integral of the fractional-ideal theta in the convergence half-plane. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField MeasureTheory Set
open NumberField.Units NumberField.Units.dirichletUnitTheorem
open ArtinMatthews.ReusedTheta
open scoped NumberField nonZeroDivisors Classical BigOperators
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)

def mixedUnitThetaMellin (s : ℂ) : ℂ :=
  ∫ u in mixedUnitLogDomain K, ∫ t in Ioi 0, mixedThetaMellinKernel K I s (t,u)

theorem mixedIdealUnitXi_eq_unitMellin {s : ℂ} (hs : 1 < s.re) :
    mixedIdealUnitXi K I s =
      ((Module.finrank ℚ K : ℂ)*s/2) *
        ((Module.finrank ℚ K : ℂ)*s/2 - (Module.finrank ℚ K : ℂ)/2) *
          mixedUnitThetaMellin K I s := by
  let n : ℝ := Module.finrank ℚ K
  let z : ℂ := (Module.finrank ℚ K : ℂ)*s/2
  have hn : 0 < n := Nat.cast_pos.mpr Module.finrank_pos
  have hz : n/2 < z.re := by
    dsimp [n, z]
    simp only [Complex.div_ofNat_re, Complex.mul_re, Complex.natCast_re,
      Complex.natCast_im, zero_mul, sub_zero]
    dsimp [n] at hn
    nlinarith
  have hz0 : z ≠ 0 := by
    intro h
    have H := congrArg Complex.re h
    simp only [Complex.zero_re] at H
    rw [H] at hz
    linarith
  have hzn : z ≠ (Module.finrank ℚ K : ℂ)/2 := by
    intro h
    have H := congrArg Complex.re h
    simp only [Complex.div_ofNat_re, Complex.natCast_re] at H
    change z.re = n/2 at H
    linarith
  have he (u : logSpace K) :
      thetaMellinXi (logScaledLattice (mixedIdealMatrix K I) (mixedIdealLogScale K I u)) z =
        z*(z-(Module.finrank ℚ K : ℂ)/2)*
          ∫ t in Ioi 0, mixedThetaMellinKernel K I s (t,u) := by
    let B := logScaledLattice (mixedIdealMatrix K I) (mixedIdealLogScale K I u)
    have hm := normalizedTheta_hasMellin B (s := z) (by
      simpa only [mixedIdealIndex_card] using hz)
    rw [thetaMellinXi_eq B hz0 (by simpa only [mixedIdealIndex_card] using hzn),
      mixedIdealIndex_card, ← hm.2]
    congr 1
    unfold mellin mixedThetaMellinKernel
    simp_rw [mixedIdealFlowTheta_eq_normalizedTheta, smul_eq_mul]
    rfl
  unfold mixedIdealUnitXi mixedUnitThetaMellin
  change (∫ u in mixedUnitLogDomain K,
    thetaMellinXi (logScaledLattice (mixedIdealMatrix K I) (mixedIdealLogScale K I u)) z) =
      z*(z-(Module.finrank ℚ K : ℂ)/2)*
        ∫ u in mixedUnitLogDomain K, ∫ t in Ioi 0, mixedThetaMellinKernel K I s (t,u)
  simp_rw [he]
  exact integral_const_mul _ _

end
end ArtinMatthews.VaryingKummerAnalytic
