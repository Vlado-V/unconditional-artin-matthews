module

public import ArtinMatthews.GiantTwoSidedPatternKernel
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

/-! The adjoint reverses the signed dilation and conjugates the
coefficient and frequency. The auxiliary law and both physical
normalizations agree exactly in the reverse direction. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators ComplexConjugate
noncomputable section

theorem giantTwoSidedPatternPhysicalCoefficient_conj {J : Type*} [Fintype J]
    {P : J → Finset ℕ} (hP : ∀ j p,p∈P j → p.Prime)
    {k ell : ℕ} {C : J → Finset (Fin k)} (step : ℤ) (q ζ : ℝ)
    (K : GiantTwoSidedPatternCoefficient P C ell) {Z Z' : Finset ℕ}
    (s : GiantTwoSidedEndpointState P (k+ell) Z) (t : GiantTwoSidedEndpointState P (k+ell) Z')
    (a : GiantTwoSidedPatternAuxiliary P C) :
    conj (giantTwoSidedPatternPhysicalCoefficient step q ζ K s t a) =
      giantTwoSidedPatternPhysicalCoefficient (-step) q (-ζ) (fun b c a => conj (K c b a)) t s a := by
  classical
  have hr : GiantTwoSidedPatternCondition C step s t a ↔ GiantTwoSidedPatternCondition C (-step) t s a := by
    constructor
    · exact giantTwoSidedPatternCondition_reverse C step s t a
    · intro h
      simpa only [neg_neg] using giantTwoSidedPatternCondition_reverse C (-step) t s a h
  unfold giantTwoSidedPatternPhysicalCoefficient
  by_cases hs : GiantTwoSidedPatternCondition C step s t a
  · rw [ite_eq_left hs,ite_eq_left (hr.mp hs)]
    have hd := giantTwoSidedPatternCopiedProduct_eq hs.1
    let D := giantTwoSidedPatternCopiedProduct C s.val.2*giantTwoSidedPatternAuxiliaryProduct a
    have hD : 0 < D := Nat.mul_pos
      (prod_pos fun j _ => prod_pos fun i _ => (hP j _ (s.val.2 j (Fin.castAdd ell i)).property).pos)
      (prod_pos fun j _ => prod_pos fun i _ => (hP j _ (a j i).property).pos)
    have harg : (D:ℂ).arg≠Real.pi := by
      rw [← Complex.ofReal_natCast,Complex.arg_ofReal_of_nonneg (Nat.cast_pos.mpr hD).le]
      exact ne_of_lt Real.pi_pos
    have hphase : conj ((D:ℂ)^((ζ:ℂ)*Complex.I)) = (D:ℂ)^(((-ζ):ℂ)*Complex.I) := by
      have he := (Complex.cpow_conj (D:ℂ) ((ζ:ℂ)*Complex.I) harg).symm
      simpa only [map_mul,Complex.conj_natCast,Complex.conj_ofReal,Complex.conj_I,
        map_neg,mul_neg,neg_mul] using he
    rw [hd]
    simp only [map_mul,Complex.conj_ofReal]
    rw [hphase]
    simp only [Complex.ofReal_neg]
    ring
  · rw [ite_eq_right hs,ite_eq_right (fun h => hs (hr.mpr h)),map_zero]

theorem giantTwoSidedPatternTransition_conj {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset ℕ} (hP : ∀ j p,p∈P j → p.Prime)
    {k ell : ℕ} {C : J → Finset (Fin k)} (step : ℤ) (q ζ : ℝ)
    (K : GiantTwoSidedPatternCoefficient P C ell) {Z Z' : Finset ℕ}
    (s : GiantTwoSidedEndpointState P (k+ell) Z) (t : GiantTwoSidedEndpointState P (k+ell) Z') :
    conj (∑ a : GiantTwoSidedPatternAuxiliary P C,giantTwoSidedPatternPhysicalCoefficient step q ζ K s t a) =
      ∑ a : GiantTwoSidedPatternAuxiliary P C,
        giantTwoSidedPatternPhysicalCoefficient (-step) q (-ζ) (fun b c a => conj (K c b a)) t s a := by
  rw [map_sum]
  exact sum_congr rfl fun a _ => giantTwoSidedPatternPhysicalCoefficient_conj hP step q ζ K s t a

end
end ArtinMatthews
