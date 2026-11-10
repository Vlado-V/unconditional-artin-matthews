module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.RepresentationTheory.Weil.AdelicSplitting.RealCharacters
public import OAI.RepresentationTheory.Weil.AdelicSplitting.FourierIntertwiner
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Ring.IsFormallyReal
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
public import OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanCharacters


set_option backward.privateInPublic true
@[expose] public section

/-! # Real Normalization -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.RealNormalization.LocalAnalysis

noncomputable section

/-! Exact self-dual Fourier normalization for every continuous nontrivial unitary real character. -/

open _root_.MeasureTheory Filter
open scoped _root_.Topology ENNReal

theorem real_fourier_frequency {n : ℕ} (c : ℝ) (f : Local.FunctionsMetaplectic.Construction.Position ℝ n → ℂ)
    (x : Local.FunctionsMetaplectic.Construction.Position ℝ n) :
    Local.FunctionsMetaplectic.Construction.fourierIntegral (RealCharacters.LocalAnalysis.realCharacter c) volume f x =
      Local.FunctionsMetaplectic.Construction.fourierIntegral (RealCharacters.LocalAnalysis.realCharacter 1) volume f (c • x) := by
  unfold Local.FunctionsMetaplectic.Construction.fourierIntegral
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y => by
    dsimp only
    congr 1
    change (Real.fourierChar (c * -Local.FunctionsMetaplectic.Construction.dot x y) : ℂ) =
      (Real.fourierChar (1 * -Local.FunctionsMetaplectic.Construction.dot (c • x) y) : ℂ)
    congr 2
    simp [Local.FunctionsMetaplectic.Construction.dot, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, mul_assoc]

theorem real_fourier_scaled_input {n : ℕ} (c : ℝ) (g : Local.FunctionsMetaplectic.Construction.Position ℝ n → ℂ)
    (x : Local.FunctionsMetaplectic.Construction.Position ℝ n) :
    Local.FunctionsMetaplectic.Construction.fourierIntegral (RealCharacters.LocalAnalysis.realCharacter c) volume (fun y => g (c • y)) x =
      ((|c| ^ n)⁻¹ : ℝ) • Local.FunctionsMetaplectic.Construction.fourierIntegral (RealCharacters.LocalAnalysis.realCharacter 1) volume g x := by
  have h := Measure.integral_comp_smul (volume : Measure (Local.FunctionsMetaplectic.Construction.Position ℝ n))
    (fun y => g y * RealCharacters.LocalAnalysis.realCharacter 1 (-Local.FunctionsMetaplectic.Construction.dot x y)) c
  simp only [Module.finrank_pi, Fintype.card_fin, abs_inv, abs_pow] at h
  unfold Local.FunctionsMetaplectic.Construction.fourierIntegral
  rw [← h]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y => by
    dsimp only
    congr 1
    change (Real.fourierChar (c * -Local.FunctionsMetaplectic.Construction.dot x y) : ℂ) =
      (Real.fourierChar (1 * -Local.FunctionsMetaplectic.Construction.dot x (c • y)) : ℂ)
    congr 2
    simp [Local.FunctionsMetaplectic.Construction.dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_left_comm]

theorem real_fourier_square_volume {n : ℕ} (c : ℝ)
    (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ n) (x : Local.FunctionsMetaplectic.Construction.Position ℝ n) :
    Local.FunctionsMetaplectic.Construction.fourierIntegral (RealCharacters.LocalAnalysis.realCharacter c) volume
      (Local.FunctionsMetaplectic.Construction.fourierIntegral (RealCharacters.LocalAnalysis.realCharacter c) volume f.val) x =
      ((|c| ^ n)⁻¹ : ℝ) • f.val (-x) := by
  have hf : Local.FunctionsMetaplectic.Construction.fourierIntegral (RealCharacters.LocalAnalysis.realCharacter c) volume f.val =
      fun y => Local.FunctionsMetaplectic.Construction.fourierIntegral (RealCharacters.LocalAnalysis.realCharacter 1) volume f.val (c • y) :=
    funext (real_fourier_frequency c f.val)
  rw [hf, real_fourier_scaled_input, RealCharacters.LocalAnalysis.real_fourier_inversion_standard]

theorem positionMeasure_real (n : ℕ) (c : ℝ) (hc : c ≠ 0) :
    Local.FunctionsMetaplectic.Construction.positionMeasure ℝ n (RealCharacters.LocalAnalysis.realCharacter c) =
      ENNReal.ofReal (Real.sqrt |c| ^ n) • volume := by
  unfold Local.FunctionsMetaplectic.Construction.positionMeasure
  simp_rw [RealCharacters.LocalAnalysis.selfDualMeasure_real c hc]
  let : (ENNReal.ofReal (Real.sqrt |c|) • (volume : Measure ℝ)).IsAddHaarMeasure := by
    apply Measure.IsAddHaarMeasure.smul
    · exact (ENNReal.ofReal_pos.mpr (Real.sqrt_pos.mpr (abs_pos.mpr hc))).ne'
    · exact ENNReal.ofReal_ne_top
  refine Measure.pi_eq (μ := fun _ : Fin n =>
    ENNReal.ofReal (Real.sqrt |c|) • (volume : Measure ℝ)) fun s _ => ?_
  rw [Measure.smul_apply, volume_pi_pi]
  simp only [Measure.smul_apply, smul_eq_mul, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [ENNReal.ofReal_pow (Real.sqrt_nonneg _)]

theorem fourierIntegral_real_normalized {n : ℕ} (c : ℝ) (hc : c ≠ 0)
    (f : Local.FunctionsMetaplectic.Construction.Position ℝ n → ℂ) (x : Local.FunctionsMetaplectic.Construction.Position ℝ n) :
    Local.FunctionsMetaplectic.Construction.fourierIntegral (RealCharacters.LocalAnalysis.realCharacter c) (Local.FunctionsMetaplectic.Construction.positionMeasure ℝ n (RealCharacters.LocalAnalysis.realCharacter c)) f x =
      (Real.sqrt |c| ^ n : ℝ) • Local.FunctionsMetaplectic.Construction.fourierIntegral (RealCharacters.LocalAnalysis.realCharacter c) volume f x := by
  rw [positionMeasure_real n c hc, Local.FunctionsMetaplectic.Construction.fourierIntegral, integral_smul_measure]
  rw [ENNReal.toReal_ofReal (by positivity)]
  rfl

theorem real_fourier_inversion {n : ℕ} (c : ℝ) (hc : c ≠ 0)
    (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ n) (x : Local.FunctionsMetaplectic.Construction.Position ℝ n) :
    Local.FunctionsMetaplectic.Construction.fourierIntegral (RealCharacters.LocalAnalysis.realCharacter c) (Local.FunctionsMetaplectic.Construction.positionMeasure ℝ n (RealCharacters.LocalAnalysis.realCharacter c))
      (Local.FunctionsMetaplectic.Construction.fourierIntegral (RealCharacters.LocalAnalysis.realCharacter c) (Local.FunctionsMetaplectic.Construction.positionMeasure ℝ n (RealCharacters.LocalAnalysis.realCharacter c)) f.val) x =
        f.val (-x) := by
  have hf : Local.FunctionsMetaplectic.Construction.fourierIntegral (RealCharacters.LocalAnalysis.realCharacter c) (Local.FunctionsMetaplectic.Construction.positionMeasure ℝ n (RealCharacters.LocalAnalysis.realCharacter c)) f.val =
      (Real.sqrt |c| ^ n : ℂ) • Local.FunctionsMetaplectic.Construction.fourierIntegral (RealCharacters.LocalAnalysis.realCharacter c) volume f.val := by
    funext y
    rw [fourierIntegral_real_normalized c hc]
    simp only [Complex.real_smul, Pi.smul_apply, smul_eq_mul, Complex.ofReal_pow]
  rw [fourierIntegral_real_normalized c hc, hf, Local.FunctionsMetaplectic.Construction.fourierIntegral_smul,
    Pi.smul_apply, real_fourier_square_volume]
  simp only [Complex.real_smul, smul_eq_mul]
  have hcoef : (Real.sqrt |c| ^ n) * (Real.sqrt |c| ^ n) * (|c| ^ n)⁻¹ = 1 := by
    rw [← mul_pow, Real.mul_self_sqrt (abs_nonneg _), mul_inv_cancel₀ (pow_ne_zero _ (abs_ne_zero.mpr hc))]
  have hcoefC : (Real.sqrt |c| ^ n : ℂ) * (Real.sqrt |c| ^ n : ℂ) * (((|c| ^ n)⁻¹ : ℝ) : ℂ) = 1 := by
    exact_mod_cast hcoef
  calc
    _ = ((Real.sqrt |c| ^ n : ℂ) * (Real.sqrt |c| ^ n : ℂ) *
        (((|c| ^ n)⁻¹ : ℝ) : ℂ)) * f.val (-x) := by push_cast; ring
    _ = _ := by rw [hcoefC, one_mul]

theorem real_fourier_mem {n : ℕ} (c : ℝ) (hc : c ≠ 0)
    (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ n) :
    Local.FunctionsMetaplectic.Construction.fourierIntegral (RealCharacters.LocalAnalysis.realCharacter c) (Local.FunctionsMetaplectic.Construction.positionMeasure ℝ n (RealCharacters.LocalAnalysis.realCharacter c)) f.val ∈
      Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ n := by
  let e : Local.FunctionsMetaplectic.Construction.Position ℝ n ≃L[ℝ] Local.FunctionsMetaplectic.Construction.Position ℝ n :=
    { __ := LinearEquiv.smulOfNeZero ℝ (Local.FunctionsMetaplectic.Construction.Position ℝ n) c hc
      continuous_toFun := continuous_const.smul continuous_id
      continuous_invFun := continuous_const.smul continuous_id }
  let φ := (RealCharacters.LocalAnalysis.realSchwartzEquiv n).symm (RealCharacters.LocalAnalysis.realBruhatFourier n f)
  let χ := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e φ
  refine ArchimedeanCharacters.LocalAnalysis.schwartzBruhat_archimedean_iff.mpr ⟨(Real.sqrt |c| ^ n : ℂ) • χ, ?_⟩
  funext x
  rw [fourierIntegral_real_normalized c hc, real_fourier_frequency]
  change (Real.sqrt |c| ^ n : ℝ) • Local.FunctionsMetaplectic.Construction.fourierIntegral (RealCharacters.LocalAnalysis.realCharacter 1) volume f.val (c • x) =
    (Real.sqrt |c| ^ n : ℂ) * φ (c • x)
  rw [RealCharacters.LocalAnalysis.realSchwartzEquiv_symm_apply, RealCharacters.LocalAnalysis.realBruhatFourier_apply]
  simp only [Complex.real_smul, Complex.ofReal_pow]

theorem real_fourier_analysis (n : ℕ)
    (ψ : AddChar ℝ ℂ) (hc : Continuous ψ) (hu : ∀ t, ‖ψ t‖ = 1)
    (hn : ∃ t, ψ t ≠ 1) :
    0 < Local.FunctionsMetaplectic.Construction.fourierHaarScaleSquared ℝ ψ ∧
    (∀ f : Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ n,
      Local.FunctionsMetaplectic.Construction.fourierIntegral ψ (Local.FunctionsMetaplectic.Construction.positionMeasure ℝ n ψ) f.val ∈ Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ n) ∧
    ∀ (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ n) x,
      Local.FunctionsMetaplectic.Construction.fourierIntegral ψ (Local.FunctionsMetaplectic.Construction.positionMeasure ℝ n ψ)
        (Local.FunctionsMetaplectic.Construction.fourierIntegral ψ (Local.FunctionsMetaplectic.Construction.positionMeasure ℝ n ψ) f.val) x = f.val (-x) := by
  obtain ⟨c, hcn, rfl⟩ := RealCharacters.LocalAnalysis.continuous_nontrivial_unitary_real_character ψ hc hu hn
  exact ⟨RealCharacters.LocalAnalysis.fourierHaarScaleSquared_real_pos c hcn, real_fourier_mem c hcn,
    real_fourier_inversion c hcn⟩

/-- The raw real Fourier lift for every character allowed by AdelicSplitting. All
normalization, stability, inversion, and unitarity obligations are proved. -/
def realRawFourierOscillator (n : ℕ)
    (ψ : AddChar ℝ ℂ) (hc : Continuous ψ) (hu : ∀ t, ‖ψ t‖ = 1)
    (hn : ∃ t, ψ t ≠ 1) : Local.FunctionsMetaplectic.Construction.Oscillator ℝ n ψ := by
  have h := real_fourier_analysis n ψ hc hu hn
  let : (Local.FunctionsMetaplectic.Construction.selfDualMeasure ℝ ψ).IsAddHaarMeasure :=
    FourierTools.LocalAnalysis.selfDualMeasure_isAddHaarMeasure_of_scale_pos ℝ ψ h.1
  let : (Local.FunctionsMetaplectic.Construction.positionMeasure ℝ n ψ).IsAddHaarMeasure := by
    unfold Local.FunctionsMetaplectic.Construction.positionMeasure
    infer_instance
  exact FourierIntertwiner.LocalAnalysis.fourierOscillator ψ hu hc (Local.FunctionsMetaplectic.Construction.positionMeasure ℝ n ψ) h.2.1 h.2.2

theorem realRawFourierOscillator_apply (n : ℕ)
    (ψ : AddChar ℝ ℂ) (hc : Continuous ψ) (hu : ∀ t, ‖ψ t‖ = 1)
    (hn : ∃ t, ψ t ≠ 1) (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ n) (x : Local.FunctionsMetaplectic.Construction.Position ℝ n) :
    ((realRawFourierOscillator n ψ hc hu hn).val.2 f).val x =
      Local.FunctionsMetaplectic.Construction.fourierIntegral ψ (Local.FunctionsMetaplectic.Construction.positionMeasure ℝ n ψ) f.val x := rfl

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.RealNormalization.LocalAnalysis
