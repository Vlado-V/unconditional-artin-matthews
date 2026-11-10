module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.RepresentationTheory.Weil.AdelicSplitting.DeterminantMeasure
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
public import OAI.RepresentationTheory.Weil.AdelicSplitting.OneCoordinate


set_option backward.privateInPublic true
@[expose] public section

/-! # Character Scaling -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.CharacterScaling.LocalAnalysis

noncomputable section

/-! Character rescaling with the actual Haar modulus and reference compact. -/

open _root_.MeasureTheory
open scoped NNReal ENNReal

variable {k : Type} [NormedField k] [LocallyCompactSpace k]
  [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k]

def scalarPositionEquiv (n : ℕ) (b : k) (hb : b ≠ 0) : Local.FunctionsMetaplectic.Construction.Position k n ≃L[k] Local.FunctionsMetaplectic.Construction.Position k n where
  __ := LinearEquiv.smulOfNeZero k (Local.FunctionsMetaplectic.Construction.Position k n) b hb
  continuous_toFun := continuous_const.smul continuous_id
  continuous_invFun := continuous_const.smul continuous_id

theorem integral_scalar_position (n : ℕ) (b : k) (hb : b ≠ 0)
    (μ : Measure k) [μ.IsAddHaarMeasure]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : Local.FunctionsMetaplectic.Construction.Position k n → E) :
    (∫ x, f (b • x) ∂Measure.pi (fun _ : Fin n => μ)) =
      (((DeterminantMeasure.LocalAnalysis.haarModulus k b : ℝ) ^ n)⁻¹ : ℝ) • ∫ x, f x ∂Measure.pi (fun _ : Fin n => μ) := by
  let e := scalarPositionEquiv n b hb
  have hdet : Matrix.det (Matrix.diagonal (fun _ : Fin n => b)) ≠ 0 := by
    simpa only [Matrix.det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      using pow_ne_zero n hb
  have hm := DeterminantMeasure.LocalAnalysis.map_matrix_haar_eq_smul μ hdet
  have he : (Matrix.toLin' (Matrix.diagonal (fun _ : Fin n => b)) : Local.FunctionsMetaplectic.Construction.Position k n → Local.FunctionsMetaplectic.Construction.Position k n) = e := by
    funext x
    ext i
    change (Matrix.diagonal (fun _ : Fin n => b)).mulVec x i = b * x i
    simp
  rw [he] at hm
  simp only [Matrix.det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    map_inv₀, map_pow] at hm
  have hi := integral_map_equiv (μ := Measure.pi (fun _ : Fin n => μ))
    e.toHomeomorph.toMeasurableEquiv f
  change (∫ x, f x ∂Measure.map e (Measure.pi (fun _ : Fin n => μ))) =
    ∫ x, f (b • x) ∂Measure.pi (fun _ : Fin n => μ) at hi
  rw [← hi, hm, integral_smul_measure]
  simp only [ENNReal.coe_toReal, NNReal.coe_inv, NNReal.coe_pow]

theorem integral_scalar_field (b : k) (hb : b ≠ 0)
    (μ : Measure k) [μ.IsAddHaarMeasure]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : k → E) :
    (∫ x, f (b * x) ∂μ) = (DeterminantMeasure.LocalAnalysis.haarModulus k b : ℝ)⁻¹ • ∫ x, f x ∂μ := by
  have h := integral_scalar_position 1 b hb μ (fun x => f (x 0))
  change (∫ x, (fun t => f (b * t)) (x 0) ∂Measure.pi (fun _ : Fin 1 => μ)) = _ at h
  rw [OneCoordinate.LocalAnalysis.integral_one_coordinate μ (fun t => f (b * t)), OneCoordinate.LocalAnalysis.integral_one_coordinate μ f, pow_one] at h
  exact h

omit [SecondCountableTopology k] in
theorem referenceFourier_mulShift (ψ : AddChar k ℂ) (b ξ : k) :
    Local.FunctionsMetaplectic.Construction.referenceFourier k (ψ.mulShift b) ξ = Local.FunctionsMetaplectic.Construction.referenceFourier k ψ (b * ξ) := by
  unfold Local.FunctionsMetaplectic.Construction.referenceFourier
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    dsimp only
    change ψ (b * -(ξ * x)) = ψ (-((b * ξ) * x))
    congr 1
    ring

theorem fourierHaarScaleSquared_mulShift (ψ : AddChar k ℂ) (b : k) (hb : b ≠ 0) :
    Local.FunctionsMetaplectic.Construction.fourierHaarScaleSquared k (ψ.mulShift b) =
      Local.FunctionsMetaplectic.Construction.fourierHaarScaleSquared k ψ / (DeterminantMeasure.LocalAnalysis.haarModulus k b : ℝ) := by
  unfold Local.FunctionsMetaplectic.Construction.fourierHaarScaleSquared
  simp_rw [referenceFourier_mulShift]
  rw [integral_scalar_field b hb (Measure.addHaar : Measure k)
    (fun ξ => ‖Local.FunctionsMetaplectic.Construction.referenceFourier k ψ ξ‖ ^ 2), smul_eq_mul]
  ring

omit [LocallyCompactSpace k] [BorelSpace k] [SecondCountableTopology k] in
theorem fourierIntegral_mulShift (n : ℕ) (ψ : AddChar k ℂ) (b : k)
    (μ : Measure (Local.FunctionsMetaplectic.Construction.Position k n)) (f : Local.FunctionsMetaplectic.Construction.Position k n → ℂ) (x : Local.FunctionsMetaplectic.Construction.Position k n) :
    Local.FunctionsMetaplectic.Construction.fourierIntegral (ψ.mulShift b) μ f x = Local.FunctionsMetaplectic.Construction.fourierIntegral ψ μ f (b • x) := by
  unfold Local.FunctionsMetaplectic.Construction.fourierIntegral
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y => by
    dsimp only
    congr 1
    change ψ (b * -Local.FunctionsMetaplectic.Construction.dot x y) = ψ (-Local.FunctionsMetaplectic.Construction.dot (b • x) y)
    congr 1
    simp [Local.FunctionsMetaplectic.Construction.dot, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, mul_assoc]

theorem fourierIntegral_mulShift_scaled_input (n : ℕ)
    (ψ : AddChar k ℂ) (b : k) (hb : b ≠ 0) (μ : Measure k) [μ.IsAddHaarMeasure]
    (f : Local.FunctionsMetaplectic.Construction.Position k n → ℂ) (x : Local.FunctionsMetaplectic.Construction.Position k n) :
    Local.FunctionsMetaplectic.Construction.fourierIntegral (ψ.mulShift b) (Measure.pi (fun _ : Fin n => μ)) (fun y => f (b • y)) x =
      (((DeterminantMeasure.LocalAnalysis.haarModulus k b : ℝ) ^ n)⁻¹ : ℝ) •
        Local.FunctionsMetaplectic.Construction.fourierIntegral ψ (Measure.pi (fun _ : Fin n => μ)) f x := by
  have h := integral_scalar_position n b hb μ (fun y => f y * ψ (-Local.FunctionsMetaplectic.Construction.dot x y))
  unfold Local.FunctionsMetaplectic.Construction.fourierIntegral
  rw [← h]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y => by
    dsimp only
    congr 1
    change ψ (b * -Local.FunctionsMetaplectic.Construction.dot x y) = ψ (-Local.FunctionsMetaplectic.Construction.dot x (b • y))
    congr 1
    simp [Local.FunctionsMetaplectic.Construction.dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_left_comm]

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.CharacterScaling.LocalAnalysis
