module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.RepresentationTheory.Weil.Local.GaussianSquareCharacter
public import OAI.RepresentationTheory.Weil.Local.TransposeSubstitution
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
public import OAI.RepresentationTheory.Weil.Local.FourierLinearSubstitution
public import OAI.RepresentationTheory.Weil.Local.LinearOscillatorHom


set_option backward.privateInPublic true
@[expose] public section

/-! # Gaussian Normal Form Factors -/

namespace OAI.RepresentationTheory.Weil.Local.GaussianNormalFormFactors.Construction

noncomputable section

/-! Determinant character factors in a Fourier normal form product. -/

variable {k : Type} [NormedField k] [CompleteSpace k] [LocallyCompactSpace k]
  [NonarchimedeanAddGroup k] [CharZero k] [MeasurableSpace k] [BorelSpace k]
  (hnd : ¬ DiscreteTopology k) (ψ : AddChar k ℂ) (hu : ∀ t : k, ‖ψ t‖ = 1)
  (hc : Continuous (fun t => ψ t)) (hn : ∃ t : k, ψ t ≠ 1)
  (hns : ¬ ∃ t : k, t ^ 2 = -1)

theorem gaussianSquareCharacter_inv (a : kˣ) :
    GaussianSquareCharacter.Construction.nonarchimedeanGaussianSquareCharacter hnd ψ hu hc hn hns a⁻¹ =
      GaussianSquareCharacter.Construction.nonarchimedeanGaussianSquareCharacter hnd ψ hu hc hn hns a := by
  rw [map_inv]
  have h := GaussianSquareCharacter.Construction.nonarchimedeanGaussianSquareCharacter_square hnd ψ hu hc hn hns a
  rw [pow_two] at h
  exact inv_eq_of_mul_eq_one_left h

theorem gaussianSquareCharacter_normalForm_product {n : ℕ} (B B' N : FunctionsMetaplectic.Construction.GeneralLinear k n) :
    let χ := GaussianSquareCharacter.Construction.nonarchimedeanGaussianSquareCharacter hnd ψ hu hc hn hns
    χ (FunctionsMetaplectic.Construction.determinantUnit k N) *
      χ (FunctionsMetaplectic.Construction.determinantUnit k (B * (TransposeSubstitution.Construction.transposeGeneralLinear B')⁻¹ * N)) =
        χ (FunctionsMetaplectic.Construction.determinantUnit k B) * χ (FunctionsMetaplectic.Construction.determinantUnit k B') := by
  dsimp only
  rw [LinearOscillatorHom.Construction.determinantUnit_mul, LinearOscillatorHom.Construction.determinantUnit_mul, FourierLinearSubstitution.Construction.determinantUnit_inv, TransposeSubstitution.Construction.determinantUnit_transpose,
    map_mul, map_mul, gaussianSquareCharacter_inv]
  have h := GaussianSquareCharacter.Construction.nonarchimedeanGaussianSquareCharacter_square hnd ψ hu hc hn hns (FunctionsMetaplectic.Construction.determinantUnit k N)
  rw [pow_two] at h
  rw [mul_comm _ (_ * _), mul_assoc, h, mul_one]

end

end OAI.RepresentationTheory.Weil.Local.GaussianNormalFormFactors.Construction
