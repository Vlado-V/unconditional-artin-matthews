module

public import ArtinMatthews.SpectralCuspEisensteinZeroRows
public import ArtinMatthews.SpectralGeometricSignSectors
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Set
open scoped MatrixGroups Classical
noncomputable section

/-- An actual correspondence between inequivalent cusps has nonzero lower entry. -/
theorem gamma0CuspCorrespondence_lower_ne_zero_of_inequivalent
    (N : ℕ) (r s : SL(2, ℤ)) (h : ¬ gamma0EisensteinCuspsEquivalent N r s)
    (M : gamma0CuspCorrespondence N r s) : M.val 1 0 ≠ 0 := by
  intro hM
  exact h ((gamma0EisensteinCuspsEquivalent_iff N r s).mpr ⟨M, hM⟩)

/-- The literal zero-lower-entry matrix fibre is empty for inequivalent cusps. -/
theorem gamma0ZeroGeometricFibre_isEmpty_of_inequivalent
    (N : ℕ) (r s : SL(2, ℤ)) (h : ¬ gamma0EisensteinCuspsEquivalent N r s) :
    IsEmpty {M : gamma0CuspCorrespondence N r s // M.val 1 0 = 0} :=
  ⟨fun M => gamma0CuspCorrespondence_lower_ne_zero_of_inequivalent N r s h M.val M.property⟩

/-- The zero sector of the actual correspondence has empty support. -/
theorem gamma0ZeroGeometricFibre_eq_empty_of_inequivalent
    (N : ℕ) (r s : SL(2, ℤ)) (h : ¬ gamma0EisensteinCuspsEquivalent N r s) :
    {M : gamma0CuspCorrespondence N r s | M.val 1 0 = 0} = ∅ := by
  ext M
  simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  exact gamma0CuspCorrespondence_lower_ne_zero_of_inequivalent N r s h M

/-- The literal zero geometric sum vanishes for inequivalent Gamma0 cusps. -/
theorem gamma0ZeroGeometricSum_eq_zero_of_inequivalent
    (N : ℕ) (r s : SL(2, ℤ)) (h : ¬ gamma0EisensteinCuspsEquivalent N r s)
    (ψ φ : h2SmoothCompactSeeds) : gamma0ZeroGeometricSum N r s ψ φ = 0 := by
  unfold gamma0ZeroGeometricSum
  have hz (M : gamma0CuspCorrespondence N r s) :
      (if M.val 1 0 = 0 then compactPoincareGeometricKernel ψ φ M.val else 0) = 0 := by
    rw [ite_eq_right (gamma0CuspCorrespondence_lower_ne_zero_of_inequivalent N r s h M)]
  simp only [hz, finsum_zero]

end
end ArtinMatthews
