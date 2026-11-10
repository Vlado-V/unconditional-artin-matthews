module

public import ArtinMatthews.GiantTwoSidedPatternKernel
public import ArtinMatthews.PrimeExtractionMellinProfile
public import ArtinMatthews.GiantPhysicalMellin
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The Fourier variable shifts the actual dilation frequency in each
physical coefficient, including its auxiliary-prime product. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section

theorem giantPhysicalMellin_cpow_shift (ζ v : ℝ) {D : ℕ} (hD : 0 < D) :
    (D : ℂ) ^ (((ζ - 2 * Real.pi * v : ℝ) : ℂ) * Complex.I) =
      (D : ℂ) ^ ((ζ : ℂ) * Complex.I) * primeExtractionMellinPhase (-v) D := by
  rw [giantPhysicalMellinPhase_nat_cpow (-v) hD]
  have he : (((ζ - 2 * Real.pi * v : ℝ) : ℂ) * Complex.I) =
      (ζ : ℂ) * Complex.I + (((2 * Real.pi * (-v) : ℝ) : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [he, Complex.cpow_add _ _ (by exact_mod_cast hD.ne')]

theorem giantTwoSidedPatternPhysicalCoefficient_mellin {J : Type*} [Fintype J]
    {P : J → Finset ℕ} (hP : ∀ j p, p ∈ P j → p.Prime)
    {k ell : ℕ} {C : J → Finset (Fin k)} (step : ℤ) (q ζ v : ℝ)
    (K : GiantTwoSidedPatternCoefficient P C ell) {Z Z' : Finset ℕ}
    (s : GiantTwoSidedEndpointState P (k + ell) Z)
    (t : GiantTwoSidedEndpointState P (k + ell) Z')
    (aux : GiantTwoSidedPatternAuxiliary P C) :
    giantTwoSidedPatternPhysicalCoefficient step q (ζ - 2 * Real.pi * v) K s t aux =
      giantTwoSidedPatternPhysicalCoefficient step q ζ K s t aux *
        primeExtractionMellinPhase (-v)
          (giantTwoSidedPatternCopiedProduct C s.val.2 * giantTwoSidedPatternAuxiliaryProduct aux) := by
  have hD : 0 < giantTwoSidedPatternCopiedProduct C s.val.2 *
      giantTwoSidedPatternAuxiliaryProduct aux := Nat.mul_pos
    (prod_pos fun j _ => prod_pos fun i _ => (hP j _ (s.val.2 j (Fin.castAdd ell i)).property).pos)
    (prod_pos fun j _ => prod_pos fun i _ => (hP j _ (aux j i).property).pos)
  unfold giantTwoSidedPatternPhysicalCoefficient
  split_ifs
  · rw [giantPhysicalMellin_cpow_shift ζ v hD]
    simp only [Nat.cast_mul]
    ring
  · exact (zero_mul _).symm

end
end ArtinMatthews
