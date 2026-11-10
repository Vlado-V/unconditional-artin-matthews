module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.RepresentationTheory.Weil.Local.DiagonalQuadratic
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
public import OAI.RepresentationTheory.Weil.Local.FresnelChangeCoordinates
public import OAI.RepresentationTheory.Weil.Local.NonarchimedeanHaar
public import OAI.RepresentationTheory.Weil.Local.QuadraticDiagonalData


set_option backward.privateInPublic true
@[expose] public section

/-! # General Fresnel Pairing -/

namespace OAI.RepresentationTheory.Weil.Local.GeneralFresnelPairing.Construction

noncomputable section

/-! The actual nonarchimedean Fresnel pairing for a general nonsingular symmetric form. -/

open _root_.Matrix _root_.MeasureTheory

theorem integral_fourier_transpose_substitution_phase
    {k : Type} [NormedField k] [LocallyCompactSpace k]
    [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k] {n : ℕ}
    (ψ : AddChar k ℂ) (μ : Measure k) [μ.IsAddHaarMeasure]
    (A : FunctionsMetaplectic.Construction.GeneralLinear k n) (f P Q : FunctionsMetaplectic.Construction.Position k n → ℂ)
    (hPQ : ∀ x, P (A⁻¹.val *ᵥ x) = Q x) :
    (∫ x, FunctionsMetaplectic.Construction.fourierIntegral ψ (Measure.pi (fun _ : Fin n => μ))
      (FunctionsMetaplectic.Construction.substitutionOperator (TransposeSubstitution.Construction.transposeGeneralLinear A) f) x * P x
      ∂Measure.pi (fun _ : Fin n => μ)) =
      ∫ x, FunctionsMetaplectic.Construction.fourierIntegral ψ (Measure.pi (fun _ : Fin n => μ)) f x * Q x
        ∂Measure.pi (fun _ : Fin n => μ) := by
  let d := FunctionsMetaplectic.Construction.localModulus k (FunctionsMetaplectic.Construction.determinantUnit k A)
  let g := fun x => FunctionsMetaplectic.Construction.fourierIntegral ψ (Measure.pi (fun _ : Fin n => μ)) f (A.val *ᵥ x) * P x
  calc
    _ = d • ∫ x, g x ∂Measure.pi (fun _ : Fin n => μ) := by
      rw [← integral_smul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        dsimp only
        rw [TransposeSubstitution.Construction.fourierIntegral_transpose_substitution, TransposeSubstitution.Construction.determinantUnit_transpose]
        change ((FunctionsMetaplectic.Construction.localModulus k (FunctionsMetaplectic.Construction.determinantUnit k A) : ℝ) •
          FunctionsMetaplectic.Construction.fourierIntegral ψ (Measure.pi (fun _ : Fin n => μ)) f (A.val.transpose.transpose *ᵥ x)) * P x = _
        rw [Matrix.transpose_transpose]
        dsimp only [g, d]
        simp only [Complex.real_smul]
        ring
    _ = ∫ x, g (A⁻¹.val *ᵥ x) ∂Measure.pi (fun _ : Fin n => μ) :=
      (FourierLinearSubstitution.Construction.integral_matrix_inverse μ A g).symm
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        dsimp only [g]
        rw [hPQ, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]

theorem nonarchimedean_general_fresnel_pairing_of_diagonalization
    {k : Type} [NormedField k] [LocallyCompactSpace k] [NonarchimedeanAddGroup k] [CharZero k]
    [MeasurableSpace k] [BorelSpace k]
    (hnd : ¬ DiscreteTopology k) {n : ℕ}
    (ψ : AddChar k ℂ) (hu : ∀ t : k, ‖ψ t‖ = 1) (hc : Continuous (fun t => ψ t))
    (hn : ∃ t : k, ψ t ≠ 1) (M A : FunctionsMetaplectic.Construction.GeneralLinear k n) (a : Fin n → kˣ)
    (hdiag : A.val.transpose * M.val * A.val = diagonal (fun i => (a i).val))
    (f : FunctionsMetaplectic.Construction.schwartzBruhat k n) :
    (∫ x, FunctionsMetaplectic.Construction.fourierIntegral ψ (FunctionsMetaplectic.Construction.positionMeasure k n ψ) f.val x * ψ (FunctionsMetaplectic.Construction.quadratic M.val x)
      ∂ FunctionsMetaplectic.Construction.positionMeasure k n ψ) =
      ((FunctionsMetaplectic.Construction.localModulus k (FunctionsMetaplectic.Construction.determinantUnit k A) : ℂ) * DiagonalQuadratic.Construction.diagonalGaussianCoefficient ψ a) *
        ∫ x, f.val x * ψ (-FunctionsMetaplectic.Construction.quadratic M⁻¹.val x) ∂ FunctionsMetaplectic.Construction.positionMeasure k n ψ := by
  let : SecondCountableTopology k := FunctionsMetaplectic.Construction.localField_secondCountable k hnd
  let μ := FunctionsMetaplectic.Construction.selfDualMeasure k ψ
  let : μ.IsAddHaarMeasure := NonarchimedeanHaar.Construction.nonarchimedean_selfDualMeasure_isAddHaarMeasure hnd ψ hu hc hn
  have hp := DiagonalQuadratic.Construction.nonarchimedean_diagonal_fresnel_pairing hnd ψ hu hc hn a
    (LinearSubstitution.Construction.testSubstitution (TransposeSubstitution.Construction.transposeGeneralLinear A) f)
  have hleft := integral_fourier_transpose_substitution_phase ψ μ A f.val
    (fun x => ψ (FunctionsMetaplectic.Construction.quadratic (diagonal fun i => (a i).val) x)) (fun x => ψ (FunctionsMetaplectic.Construction.quadratic M.val x))
    (fun x => congrArg ψ (QuadraticDiagonalData.Construction.quadratic_diagonal_inverse_coordinates M A a hdiag x))
  have hright := FresnelChangeCoordinates.Construction.integral_substitution_mul_phase μ (TransposeSubstitution.Construction.transposeGeneralLinear A) f.val
    (fun x => ψ (-FunctionsMetaplectic.Construction.quadratic (diagonal fun i => (a i).val⁻¹) x)) (fun x => ψ (-FunctionsMetaplectic.Construction.quadratic M⁻¹.val x))
    (fun x => congrArg ψ (congrArg Neg.neg (QuadraticDiagonalData.Construction.quadratic_inverse_diagonal_coordinates M A a hdiag x)))
  change (∫ x, FunctionsMetaplectic.Construction.fourierIntegral ψ (FunctionsMetaplectic.Construction.positionMeasure k n ψ)
      (FunctionsMetaplectic.Construction.substitutionOperator (TransposeSubstitution.Construction.transposeGeneralLinear A) f.val) x *
        ψ (FunctionsMetaplectic.Construction.quadratic (diagonal fun i => (a i).val) x) ∂ FunctionsMetaplectic.Construction.positionMeasure k n ψ) =
    DiagonalQuadratic.Construction.diagonalGaussianCoefficient ψ a *
      ∫ x, FunctionsMetaplectic.Construction.substitutionOperator (TransposeSubstitution.Construction.transposeGeneralLinear A) f.val x *
        ψ (-FunctionsMetaplectic.Construction.quadratic (diagonal fun i => (a i).val⁻¹) x) ∂ FunctionsMetaplectic.Construction.positionMeasure k n ψ at hp
  dsimp only [μ, FunctionsMetaplectic.Construction.positionMeasure] at hp hleft hright ⊢
  rw [hleft, hright, TransposeSubstitution.Construction.determinantUnit_transpose, Complex.real_smul] at hp
  exact hp.trans (by ring)

end

end OAI.RepresentationTheory.Weil.Local.GeneralFresnelPairing.Construction
