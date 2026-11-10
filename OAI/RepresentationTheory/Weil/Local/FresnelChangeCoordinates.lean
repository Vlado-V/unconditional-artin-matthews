module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.RepresentationTheory.Weil.Local.DiagonalQuadratic
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
public import Mathlib.RingTheory.SimpleRing.Principal
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
public import OAI.RepresentationTheory.Weil.Local.NonarchimedeanHaar


set_option backward.privateInPublic true
@[expose] public section

/-! # Fresnel Change Coordinates -/

namespace OAI.RepresentationTheory.Weil.Local.FresnelChangeCoordinates.Construction

noncomputable section

/-! Recovering Gaussian coefficient congruence from the actual Fourier pairing and Haar substitution. -/

open _root_.Matrix _root_.MeasureTheory

section Substitution
variable {k : Type} [NormedField k] [LocallyCompactSpace k]
  [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k] {n : ℕ}
  (μ : Measure k) [μ.IsAddHaarMeasure]

theorem integral_substitution_mul_phase (A : FunctionsMetaplectic.Construction.GeneralLinear k n)
    (f P Q : FunctionsMetaplectic.Construction.Position k n → ℂ) (hPQ : ∀ x, P (A.val *ᵥ x) = Q x) :
    (∫ x, FunctionsMetaplectic.Construction.substitutionOperator A f x * P x ∂Measure.pi (fun _ : Fin n => μ)) =
      (FunctionsMetaplectic.Construction.localModulus k (FunctionsMetaplectic.Construction.determinantUnit k A) : ℝ) •
        ∫ x, f x * Q x ∂Measure.pi (fun _ : Fin n => μ) := by
  have hi := FourierLinearSubstitution.Construction.integral_matrix_inverse μ A (fun x => f x * Q x)
  rw [← hi]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    dsimp only
    rw [FunctionsMetaplectic.Construction.substitutionOperator_apply, ← hPQ]
    have hcancel : A.val *ᵥ (A⁻¹.val *ᵥ x) = x := by
      rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
    rw [hcancel]

theorem integral_fourier_substitution_phase (ψ : AddChar k ℂ)
    (A : FunctionsMetaplectic.Construction.GeneralLinear k n) (hA : A.val.IsSymm) (f P Q : FunctionsMetaplectic.Construction.Position k n → ℂ)
    (hPQ : ∀ x, P (A⁻¹.val *ᵥ x) = Q x) :
    (∫ x, FunctionsMetaplectic.Construction.fourierIntegral ψ (Measure.pi (fun _ : Fin n => μ)) (FunctionsMetaplectic.Construction.substitutionOperator A f) x * P x
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
        rw [FourierLinearSubstitution.Construction.fourierIntegral_symmetric_substitution ψ μ A hA]
        dsimp only [g, d]
        simp only [Complex.real_smul]
        ring
    _ = ∫ x, g (A⁻¹.val *ᵥ x) ∂Measure.pi (fun _ : Fin n => μ) :=
      (FourierLinearSubstitution.Construction.integral_matrix_inverse μ A g).symm
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        dsimp only [g]
        rw [hPQ]
        have hcancel : A.val *ᵥ (A⁻¹.val *ᵥ x) = x := by
          rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
        rw [hcancel]

end Substitution

theorem nonarchimedean_diagonalGaussianCoefficient_congruence
    {k : Type} [NormedField k] [LocallyCompactSpace k] [NonarchimedeanAddGroup k] [CharZero k]
    [MeasurableSpace k] [BorelSpace k]
    (hnd : ¬ DiscreteTopology k) {n : ℕ}
    (ψ : AddChar k ℂ) (hu : ∀ t : k, ‖ψ t‖ = 1) (hc : Continuous (fun t => ψ t))
    (hn : ∃ t : k, ψ t ≠ 1) (a b : Fin n → kˣ) (A : FunctionsMetaplectic.Construction.GeneralLinear k n) (hA : A.val.IsSymm)
    (hq : ∀ x, FunctionsMetaplectic.Construction.quadratic (diagonal fun i => (a i).val) (A⁻¹.val *ᵥ x) =
      FunctionsMetaplectic.Construction.quadratic (diagonal fun i => (b i).val) x)
    (hqi : ∀ x, FunctionsMetaplectic.Construction.quadratic (diagonal fun i => (a i).val⁻¹) (A.val *ᵥ x) =
      FunctionsMetaplectic.Construction.quadratic (diagonal fun i => (b i).val⁻¹) x) :
    DiagonalQuadratic.Construction.diagonalGaussianCoefficient ψ b =
      (FunctionsMetaplectic.Construction.localModulus k (FunctionsMetaplectic.Construction.determinantUnit k A) : ℂ) * DiagonalQuadratic.Construction.diagonalGaussianCoefficient ψ a := by
  let : SecondCountableTopology k := FunctionsMetaplectic.Construction.localField_secondCountable k hnd
  let μ := FunctionsMetaplectic.Construction.selfDualMeasure k ψ
  let : μ.IsAddHaarMeasure := NonarchimedeanHaar.Construction.nonarchimedean_selfDualMeasure_isAddHaarMeasure hnd ψ hu hc hn
  let μn := FunctionsMetaplectic.Construction.positionMeasure k n ψ
  let : μn.IsAddHaarMeasure := by dsimp [μn, FunctionsMetaplectic.Construction.positionMeasure]; infer_instance
  obtain ⟨f, hf⟩ := DiagonalQuadratic.Construction.exists_nonarchimedean_quadratic_pairing_ne_zero hnd ψ hu hc μn
    (diagonal fun i => (b i).val⁻¹)
  have hfa := DiagonalQuadratic.Construction.nonarchimedean_diagonal_fresnel_pairing hnd ψ hu hc hn a (LinearSubstitution.Construction.testSubstitution A f)
  have hfb := DiagonalQuadratic.Construction.nonarchimedean_diagonal_fresnel_pairing hnd ψ hu hc hn b f
  have hleft := integral_fourier_substitution_phase μ ψ A hA f.val
    (fun x => ψ (FunctionsMetaplectic.Construction.quadratic (diagonal fun i => (a i).val) x))
    (fun x => ψ (FunctionsMetaplectic.Construction.quadratic (diagonal fun i => (b i).val) x)) (fun x => congrArg ψ (hq x))
  have hright := integral_substitution_mul_phase μ A f.val
    (fun x => ψ (-FunctionsMetaplectic.Construction.quadratic (diagonal fun i => (a i).val⁻¹) x))
    (fun x => ψ (-FunctionsMetaplectic.Construction.quadratic (diagonal fun i => (b i).val⁻¹) x))
    (fun x => congrArg ψ (congrArg Neg.neg (hqi x)))
  change (∫ x, FunctionsMetaplectic.Construction.fourierIntegral ψ μn (FunctionsMetaplectic.Construction.substitutionOperator A f.val) x *
      ψ (FunctionsMetaplectic.Construction.quadratic (diagonal fun i => (a i).val) x) ∂μn) =
    DiagonalQuadratic.Construction.diagonalGaussianCoefficient ψ a * ∫ x, FunctionsMetaplectic.Construction.substitutionOperator A f.val x *
      ψ (-FunctionsMetaplectic.Construction.quadratic (diagonal fun i => (a i).val⁻¹) x) ∂μn at hfa
  dsimp only [μn, μ, FunctionsMetaplectic.Construction.positionMeasure] at hfa hleft hright hfb hf
  rw [hleft, hright, hfb, Complex.real_smul] at hfa
  apply mul_right_cancel₀ hf
  calc
    _ = _ := hfa
    _ = _ := by ring

end

end OAI.RepresentationTheory.Weil.Local.FresnelChangeCoordinates.Construction
