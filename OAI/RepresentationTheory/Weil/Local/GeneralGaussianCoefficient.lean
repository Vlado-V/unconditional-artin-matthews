module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.RepresentationTheory.Weil.Local.DiagonalQuadratic
public import OAI.RepresentationTheory.Weil.Local.GaussianSquareCharacter
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
public import OAI.RepresentationTheory.Weil.Local.GaussianDeterminantSquare
public import OAI.RepresentationTheory.Weil.Local.GeneralFresnelPairing
public import OAI.RepresentationTheory.Weil.Local.SymmetricCongruenceDiagonal
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! # General Gaussian Coefficient -/

namespace OAI.RepresentationTheory.Weil.Local.GeneralGaussianCoefficient.Construction

noncomputable section

/-! A general Fresnel coefficient with a checked square, using the actual normalized scalar Gaussian index. -/

open _root_.Matrix _root_.MeasureTheory

variable {k : Type} [NormedField k] [CompleteSpace k] [LocallyCompactSpace k]
  [NonarchimedeanAddGroup k] [CharZero k] [MeasurableSpace k] [BorelSpace k]
  (hnd : ¬ DiscreteTopology k) (ψ : AddChar k ℂ) (hu : ∀ t : k, ‖ψ t‖ = 1)
  (hc : Continuous (fun t => ψ t)) (hn : ∃ t : k, ψ t ≠ 1)
  (hns : ¬ ∃ t : k, t ^ 2 = -1)

theorem generalGaussianCoefficient_square {n : ℕ} (M A : FunctionsMetaplectic.Construction.GeneralLinear k n) (a : Fin n → kˣ)
    (h : A.val.transpose * M.val * A.val = diagonal (fun i => (a i).val)) :
    ((FunctionsMetaplectic.Construction.localModulus k (FunctionsMetaplectic.Construction.determinantUnit k A) : ℂ) * DiagonalQuadratic.Construction.diagonalGaussianCoefficient ψ a) ^ 2 =
      (FunctionsMetaplectic.Construction.gaussianIndex k ψ 1 ^ (2 * n) *
        (GaussianSquareCharacter.Construction.nonarchimedeanGaussianSquareCharacter hnd ψ hu hc hn hns (FunctionsMetaplectic.Construction.determinantUnit k M)).val) /
          (FunctionsMetaplectic.Construction.localModulus k (FunctionsMetaplectic.Construction.determinantUnit k M) : ℂ) := by
  have hA0 : (FunctionsMetaplectic.Construction.localModulus k (FunctionsMetaplectic.Construction.determinantUnit k A) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (FunctionsMetaplectic.Construction.localModulus_pos k _).ne'
  have hM0 : (FunctionsMetaplectic.Construction.localModulus k (FunctionsMetaplectic.Construction.determinantUnit k M) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (FunctionsMetaplectic.Construction.localModulus_pos k _).ne'
  rw [mul_pow, GaussianDeterminantSquare.Construction.diagonalGaussianCoefficient_square hnd ψ hu hc hn hns a,
    GaussianDeterminantSquare.Construction.gaussianSquareCharacter_congruence hnd ψ hu hc hn hns M A a h,
    GaussianDeterminantSquare.Construction.localModulus_congruence M A a h, Complex.ofReal_mul, Complex.ofReal_pow]
  field_simp

theorem exists_nonarchimedean_general_fresnel_coefficient {n : ℕ}
    (M : FunctionsMetaplectic.Construction.GeneralLinear k n) (hM : M.val.IsSymm) :
    ∃ c : ℂ,
      c ^ 2 = (FunctionsMetaplectic.Construction.gaussianIndex k ψ 1 ^ (2 * n) *
        (GaussianSquareCharacter.Construction.nonarchimedeanGaussianSquareCharacter hnd ψ hu hc hn hns (FunctionsMetaplectic.Construction.determinantUnit k M)).val) /
          (FunctionsMetaplectic.Construction.localModulus k (FunctionsMetaplectic.Construction.determinantUnit k M) : ℂ) ∧
      ∀ f : FunctionsMetaplectic.Construction.schwartzBruhat k n,
        (∫ x, FunctionsMetaplectic.Construction.fourierIntegral ψ (FunctionsMetaplectic.Construction.positionMeasure k n ψ) f.val x * ψ (FunctionsMetaplectic.Construction.quadratic M.val x)
          ∂ FunctionsMetaplectic.Construction.positionMeasure k n ψ) =
          c * ∫ x, f.val x * ψ (-FunctionsMetaplectic.Construction.quadratic M⁻¹.val x) ∂ FunctionsMetaplectic.Construction.positionMeasure k n ψ := by
  obtain ⟨A, a, ha⟩ := SymmetricCongruenceDiagonal.Construction.symmetric_generalLinear_congruence_diagonal M hM
  exact ⟨(FunctionsMetaplectic.Construction.localModulus k (FunctionsMetaplectic.Construction.determinantUnit k A) : ℂ) * DiagonalQuadratic.Construction.diagonalGaussianCoefficient ψ a,
    generalGaussianCoefficient_square hnd ψ hu hc hn hns M A a ha,
    GeneralFresnelPairing.Construction.nonarchimedean_general_fresnel_pairing_of_diagonalization hnd ψ hu hc hn M A a ha⟩

end

end OAI.RepresentationTheory.Weil.Local.GeneralGaussianCoefficient.Construction
