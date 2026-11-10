module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.RepresentationTheory.Weil.Local.TestFourierNormalForm
public import OAI.RepresentationTheory.Weil.Local.FourierNormalForm
public import OAI.RepresentationTheory.Weil.Local.GaussianSquareCharacter
public import OAI.RepresentationTheory.Weil.Local.NonarchimedeanTestSpace
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
public import OAI.RepresentationTheory.Weil.Local.FourierNormalFormMultiplication
public import OAI.RepresentationTheory.Weil.Local.GaussianNormalFormFactors
public import OAI.RepresentationTheory.Weil.Local.GeneralFresnelOperator
public import OAI.RepresentationTheory.Weil.Local.NonarchimedeanHaar


set_option backward.privateInPublic true
@[expose] public section

/-! # Nonarchimedean Normal Form Product -/

namespace OAI.RepresentationTheory.Weil.Local.NonarchimedeanNormalFormProduct.Construction

noncomputable section

/-! Exact products of normalized Fourier operators, with the Gaussian determinant factor. -/

open _root_.Matrix _root_.MeasureTheory

variable {k : Type} [NormedField k] [CompleteSpace k] [LocallyCompactSpace k]
  [NonarchimedeanAddGroup k] [CharZero k] [MeasurableSpace k] [BorelSpace k]
  [SecondCountableTopology k]
  (hnd : ¬ DiscreteTopology k) (ψ : AddChar k ℂ) (hu : ∀ t : k, ‖ψ t‖ = 1)
  (hc : Continuous (fun t => ψ t)) (hn : ∃ t : k, ψ t ≠ 1)
  (hns : ¬ ∃ t : k, t ^ 2 = -1)

theorem exists_nonarchimedean_normalForm_product {n : ℕ}
    (F : FunctionsMetaplectic.Construction.schwartzBruhat k n ≃ₗ[ℂ] FunctionsMetaplectic.Construction.schwartzBruhat k n)
    (hF : ∀ f x, (F f).val x = FunctionsMetaplectic.Construction.fourierIntegral ψ (FunctionsMetaplectic.Construction.positionMeasure k n ψ) f.val x)
    (P Q P' Q' : FunctionsMetaplectic.Construction.SymmetricMatrix k n) (B B' : FunctionsMetaplectic.Construction.GeneralLinear k n)
    (hprod : FourierNormalForm.Construction.fourierNormalForm P B Q * FourierNormalForm.Construction.fourierNormalForm P' B' Q' ∈ FourierBigCell.Construction.fourierBigCell k n) :
    let χ := GaussianSquareCharacter.Construction.nonarchimedeanGaussianSquareCharacter hnd ψ hu hc hn hns
    let R := TestFourierNormalForm.Construction.testFourierNormalForm ψ (NonarchimedeanTestSpace.Construction.nonarchimedean_quadratic_mem ψ hu hc) F
    ∃ (P'' Q'' : FunctionsMetaplectic.Construction.SymmetricMatrix k n) (B'' : FunctionsMetaplectic.Construction.GeneralLinear k n) (Γ : ℂ),
      FourierNormalForm.Construction.fourierNormalForm P B Q * FourierNormalForm.Construction.fourierNormalForm P' B' Q' = FourierNormalForm.Construction.fourierNormalForm P'' B'' Q'' ∧
      Γ ^ 2 * (χ (FunctionsMetaplectic.Construction.determinantUnit k B'')).val =
        FunctionsMetaplectic.Construction.gaussianIndex k ψ 1 ^ (2 * n) *
          (χ (FunctionsMetaplectic.Construction.determinantUnit k B)).val * (χ (FunctionsMetaplectic.Construction.determinantUnit k B')).val ∧
      ∀ f : FunctionsMetaplectic.Construction.schwartzBruhat k n, R P.val B Q.val (R P'.val B' Q'.val f) =
        Γ • R P''.val B'' Q''.val f := by
  let χ := GaussianSquareCharacter.Construction.nonarchimedeanGaussianSquareCharacter hnd ψ hu hc hn hns
  let R := TestFourierNormalForm.Construction.testFourierNormalForm ψ (NonarchimedeanTestSpace.Construction.nonarchimedean_quadratic_mem ψ hu hc) F
  have hm := FourierNormalForm.Construction.fourierNormalForm_product_middle_nonsingular P Q P' Q' B B' hprod
  obtain ⟨M, hM⟩ := (Matrix.isUnit_iff_isUnit_det (Q.val + P'.val)).mpr (isUnit_iff_ne_zero.mpr hm)
  let N := TransposeSubstitution.Construction.transposeGeneralLinear B' * M * B'
  have hN : N.val = B'.val.transpose * (Q.val + P'.val) * B'.val := by
    change B'.val.transpose * M.val * B'.val = _
    rw [hM]
  have hNs : N.val.IsSymm := by
    rw [hN]
    exact (SymmetricMatrixOperations.Construction.symmetricCongruence B'.val (SymmetricMatrixOperations.Construction.symmetricAdd Q P')).property
  obtain ⟨Γ, hΓ, hrel⟩ := GeneralFresnelOperator.Construction.exists_nonarchimedean_general_fourier_relation hnd ψ hu hc hn hns N hNs F hF
  let C := B * (TransposeSubstitution.Construction.transposeGeneralLinear B')⁻¹
  let S := SymmetricMatrixOperations.Construction.symmetricNegativeInverse N hNs
  refine ⟨SymmetricMatrixOperations.Construction.symmetricAdd P (SymmetricMatrixOperations.Construction.symmetricCongruence C⁻¹.val S), SymmetricMatrixOperations.Construction.symmetricAdd S Q', C * N, Γ,
    FourierNormalFormMultiplication.Construction.fourierNormalForm_product_formula P Q P' Q' B B' N hN hNs, ?_, ?_⟩
  · change Γ ^ 2 * (χ (FunctionsMetaplectic.Construction.determinantUnit k (C * N))).val = _
    rw [hΓ, mul_assoc, ← Units.val_mul]
    have he := GaussianNormalFormFactors.Construction.gaussianSquareCharacter_normalForm_product hnd ψ hu hc hn hns B B' N
    change χ (FunctionsMetaplectic.Construction.determinantUnit k N) * χ (FunctionsMetaplectic.Construction.determinantUnit k (C * N)) =
      χ (FunctionsMetaplectic.Construction.determinantUnit k B) * χ (FunctionsMetaplectic.Construction.determinantUnit k B') at he
    rw [he, Units.val_mul, ← mul_assoc]
  · let : (FunctionsMetaplectic.Construction.selfDualMeasure k ψ).IsAddHaarMeasure :=
      NonarchimedeanHaar.Construction.nonarchimedean_selfDualMeasure_isAddHaarMeasure hnd ψ hu hc hn
    intro f
    exact TestFourierNormalForm.Construction.testFourierNormalForm_product ψ (NonarchimedeanTestSpace.Construction.nonarchimedean_quadratic_mem ψ hu hc) F
      (FunctionsMetaplectic.Construction.selfDualMeasure k ψ) hF P.val Q.val P'.val Q'.val B B' N hN Γ hrel f

end

end OAI.RepresentationTheory.Weil.Local.NonarchimedeanNormalFormProduct.Construction
