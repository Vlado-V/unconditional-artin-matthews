module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.RepresentationTheory.Weil.Local.ComplexNormalization
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
public import OAI.RepresentationTheory.Weil.Local.CharacterScaling
public import OAI.RepresentationTheory.Weil.Local.ComplexFresnelPairing


set_option backward.privateInPublic true
@[expose] public section

/-! # Complex Fresnel Normalization -/

namespace OAI.RepresentationTheory.Weil.Local.ComplexFresnelNormalization.Construction

noncomputable section

/-! Transport of complex Fresnel pairing through the square root of the character parameter. -/

open _root_.MeasureTheory
open scoped NNReal

theorem integral_complex_square_character {n : ℕ} (s : ℂ) (hs : s ≠ 0)
    (f : FunctionsMetaplectic.Construction.Position ℂ n → ℂ) :
    (∫ x, f x ∂ FunctionsMetaplectic.Construction.positionMeasure ℂ n (ComplexNormalization.Construction.complexCharacter (s ^ 2))) = ∫ x, f (s⁻¹ • x) := by
  rw [ComplexNormalization.Construction.positionMeasure_complex n (s ^ 2) (pow_ne_zero _ hs), integral_smul_measure,
    ENNReal.toReal_ofReal (by positivity)]
  have hm : Real.sqrt (DeterminantMeasure.Construction.haarModulus ℂ (s ^ 2) : ℝ) = (DeterminantMeasure.Construction.haarModulus ℂ s : ℝ) := by
    rw [map_pow, NNReal.coe_pow, Real.sqrt_sq (NNReal.coe_nonneg _)]
  rw [hm]
  have h := CharacterScaling.Construction.integral_scalar_position n s⁻¹ (inv_ne_zero hs) volume f
  simp only [map_inv₀, NNReal.coe_inv, inv_pow, inv_inv] at h
  exact h.symm

theorem fourier_complex_square_character {n : ℕ} (s : ℂ) (hs : s ≠ 0)
    (f : FunctionsMetaplectic.Construction.Position ℂ n → ℂ) (x : FunctionsMetaplectic.Construction.Position ℂ n) :
    FunctionsMetaplectic.Construction.fourierIntegral (ComplexNormalization.Construction.complexCharacter (s ^ 2)) (FunctionsMetaplectic.Construction.positionMeasure ℂ n (ComplexNormalization.Construction.complexCharacter (s ^ 2))) f x =
      FunctionsMetaplectic.Construction.fourierIntegral ArchimedeanTestSpace.Construction.complexStandardCharacter volume (fun z => f (s⁻¹ • z)) (s • x) := by
  unfold FunctionsMetaplectic.Construction.fourierIntegral
  rw [integral_complex_square_character s hs]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun z => by
    dsimp only
    congr 1
    change ArchimedeanTestSpace.Construction.complexStandardCharacter (s ^ 2 * -FunctionsMetaplectic.Construction.dot x (s⁻¹ • z)) =
      ArchimedeanTestSpace.Construction.complexStandardCharacter (-FunctionsMetaplectic.Construction.dot (s • x) z)
    congr 1
    simp only [FunctionsMetaplectic.Construction.dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    field_simp

theorem complex_square_character_quadratic {n : ℕ} (s : ℂ) (hs : s ≠ 0) (x : FunctionsMetaplectic.Construction.Position ℂ n) :
    ComplexNormalization.Construction.complexCharacter (s ^ 2) (FunctionsMetaplectic.Construction.quadratic 1 (s⁻¹ • x)) = ArchimedeanTestSpace.Construction.complexStandardCharacter (FunctionsMetaplectic.Construction.quadratic 1 x) := by
  change ArchimedeanTestSpace.Construction.complexStandardCharacter (s ^ 2 * FunctionsMetaplectic.Construction.quadratic 1 (s⁻¹ • x)) = _
  rw [QuadraticIntertwiner.Construction.quadratic_smul_vector]
  congr 1
  field_simp

theorem complex_fresnel_pairing_square {n : ℕ} (s : ℂ) (hs : s ≠ 0)
    (f : FunctionsMetaplectic.Construction.schwartzBruhat ℂ n) :
    (∫ x, FunctionsMetaplectic.Construction.fourierIntegral (ComplexNormalization.Construction.complexCharacter (s ^ 2)) (FunctionsMetaplectic.Construction.positionMeasure ℂ n (ComplexNormalization.Construction.complexCharacter (s ^ 2))) f.val x *
      ComplexNormalization.Construction.complexCharacter (s ^ 2) (FunctionsMetaplectic.Construction.quadratic 1 x) ∂ FunctionsMetaplectic.Construction.positionMeasure ℂ n (ComplexNormalization.Construction.complexCharacter (s ^ 2))) =
      ∫ x, f.val x * ComplexNormalization.Construction.complexCharacter (s ^ 2) (-FunctionsMetaplectic.Construction.quadratic 1 x)
        ∂ FunctionsMetaplectic.Construction.positionMeasure ℂ n (ComplexNormalization.Construction.complexCharacter (s ^ 2)) := by
  let g := FunctionsMetaplectic.Construction.schwartzBruhat_coordinateEquiv
    (CharacterScaling.Construction.scalarPositionEquiv n s⁻¹ (inv_ne_zero hs)).toContinuousAddEquiv f
  have hg (x : FunctionsMetaplectic.Construction.Position ℂ n) : g.val x = f.val (s⁻¹ • x) := rfl
  have hpair := ComplexFresnelPairing.Construction.complex_fresnel_pairing_standard g
  rw [integral_complex_square_character s hs, integral_complex_square_character s hs]
  calc
    _ = ∫ x, FunctionsMetaplectic.Construction.fourierIntegral ArchimedeanTestSpace.Construction.complexStandardCharacter volume g.val x * ArchimedeanTestSpace.Construction.complexStandardCharacter (FunctionsMetaplectic.Construction.quadratic 1 x) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        dsimp only
        rw [fourier_complex_square_character s hs, complex_square_character_quadratic s hs,
          smul_smul, mul_inv_cancel₀ hs, one_smul]
        rfl
    _ = ∫ x, g.val x * ArchimedeanTestSpace.Construction.complexStandardCharacter (-FunctionsMetaplectic.Construction.quadratic 1 x) := hpair
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        dsimp only
        rw [hg]
        congr 1
        simp_rw [AddChar.map_neg_eq_inv]
        rw [complex_square_character_quadratic s hs]

theorem complex_fresnel_pairing {n : ℕ}
    (ψ : AddChar ℂ ℂ) (hc : Continuous (fun z => ψ z))
    (hu : ∀ z, ‖ψ z‖ = 1) (hn : ∃ z, ψ z ≠ 1) (f : FunctionsMetaplectic.Construction.schwartzBruhat ℂ n) :
    (∫ x, FunctionsMetaplectic.Construction.fourierIntegral ψ (FunctionsMetaplectic.Construction.positionMeasure ℂ n ψ) f.val x * ψ (FunctionsMetaplectic.Construction.quadratic 1 x) ∂ FunctionsMetaplectic.Construction.positionMeasure ℂ n ψ) =
      FunctionsMetaplectic.Construction.gaussianIndex ℂ ψ 1 ^ n * ∫ x, f.val x * ψ (-FunctionsMetaplectic.Construction.quadratic 1 x) ∂ FunctionsMetaplectic.Construction.positionMeasure ℂ n ψ := by
  rw [(ArchimedeanTestSpace.Construction.complex_gaussian_normalization ψ hc hu hn 1 one_ne_zero).2.2, one_pow, one_mul]
  obtain ⟨b, hb, rfl⟩ := ComplexNormalization.Construction.continuous_nontrivial_unitary_complex_character ψ hc hu hn
  let s : ℂ := b ^ (1 / 2 : ℂ)
  have hs : s ^ (2 : ℕ) = b := by simp [s, one_div]
  have hs0 : s ≠ 0 := by
    intro h
    rw [h, zero_pow (by decide)] at hs
    exact hb hs.symm
  rw [← hs]
  exact complex_fresnel_pairing_square s hs0 f

end

end OAI.RepresentationTheory.Weil.Local.ComplexFresnelNormalization.Construction
