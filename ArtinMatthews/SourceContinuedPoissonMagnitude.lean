module

public import ArtinMatthews.SourceProbeComparison
public import ArtinMatthews.SourceContinuedPoissonRowIntegral
public import ArtinMatthews.SourceRowFrequencyNorm
public import ArtinMatthews.SourceSLocalProbeVertical
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The physical source scales and the absolute integral of the actual
height majorant. The frequency power is identified with the same exterior
norm that enters the dyadic conductor bounds. -/
namespace ArtinMatthews.SourcePhysical
open MeasureTheory VaryingKummerAnalytic
noncomputable section

theorem sourcePoissonTripleScale_source_scales {Z : ℝ} (hZ : 0 < Z) (a b c : ℝ) :
    sourcePoissonTripleScale (Z^(9/10 : ℝ)) (Z^(133/1000 : ℝ)) Z a b c =
      Z^(sourceContourExponent a b c)*Real.exp ((a+c-1)^2) := by
  unfold sourcePoissonTripleScale sourceContourExponent
  rw [← Real.rpow_mul hZ.le, ← Real.rpow_mul hZ.le, ← Real.rpow_add hZ, ← Real.rpow_add hZ]
  congr 1
  congr 1
  ring

def sourcePoissonInverseQuadraticMass : ℝ :=
  ∫ p : SourcePoissonHeights,
    (sourceContourHeightWeight p.1.1*sourceContourHeightWeight p.1.2)*
      Real.exp (-((p.2+p.1.2)^2)) ∂sourcePoissonHeightMeasure

theorem sourcePoissonInverseQuadraticMass_nonneg : 0 ≤ sourcePoissonInverseQuadraticMass :=
  integral_nonneg (fun p => mul_nonneg (mul_nonneg (sourceContourHeightWeight_nonneg p.1.1)
    (sourceContourHeightWeight_nonneg p.1.2)) (Real.exp_nonneg _))

theorem sourcePoissonHeightIntegral_norm_le_of_majorant (f : SourcePoissonHeights → ℂ)
    (hf : Integrable f sourcePoissonHeightMeasure) (C : ℝ)
    (hC : ∀ p, ‖f p‖ ≤ C*(sourceContourHeightWeight p.1.1*sourceContourHeightWeight p.1.2)*
      Real.exp (-((p.2+p.1.2)^2))) :
    ‖∫ p, f p ∂sourcePoissonHeightMeasure‖ ≤ C*sourcePoissonInverseQuadraticMass := by
  apply (norm_integral_le_integral_norm f).trans
  unfold sourcePoissonInverseQuadraticMass
  rw [← integral_const_mul]
  exact integral_mono hf.norm (sourcePoissonHeightWeightProduct_integrable.const_mul C)
    (fun p => (hC p).trans_eq (by ring))

end
end ArtinMatthews.SourcePhysical

namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain AllowedGenerators MeasureTheory
open VaryingKummerAnalytic SourcePhysical
open scoped NumberField Classical BigOperators
noncomputable section
variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable {J : Ideal (𝓞 F)} (η : EvenIdealRayCharacter F J) (hJ : J ≠ ⊥)
local notation "S" => sourceHilbertSet F S₀
local notation "R" => sourceRing F S₀

omit [IsTotallyComplex F] in
include hζ in
theorem sourcePoissonFrequencyNorm_eq_exterior (u : {a : R // a ≠ 0}) :
    sourcePoissonFrequencyNorm F S₀ u =
      (sourcePrimeExponentNorm F S₀ (sourceElementExponents F S₀ u.val u.property) : ℝ) :=
  sourceRowFieldNorm_eq_frequencyNorm F S₀ hζ u.val u.property

omit [IsTotallyComplex F] in
theorem exists_sourceProbeContourWeights_inverse_quadratic
    (v : InfinitePlace F) (b c : ℝ) (hc : 0 < c) (m : ℕ) :
    ∃ D : ℝ, 0 < D ∧ ∀ y t : ℝ,
      ((|y|+2)^m*‖sourceProbeW1Mellin (sourcePoissonVertical b y)‖)*
        ‖sourceSLocalProbeMellin F hζ S v (sourcePoissonVertical c t)‖ ≤
        D*(sourceContourHeightWeight y*sourceContourHeightWeight t) := by
  obtain ⟨C, hC, hW⟩ := sourceProbeW1Mellin_strip_decay b b (m+2)
  obtain ⟨B, hB, hM⟩ := sourceSLocalProbeMellin_vertical_rapid F hζ S v 2 c c hc
  refine ⟨((2 : ℝ)^m*C)*(B+1), by positivity, ?_⟩
  intro y t
  have hw' := hW (sourcePoissonVertical b y)
    (by rw [sourcePoissonVertical_re]) (by rw [sourcePoissonVertical_re])
  rw [sourcePoissonVertical_im] at hw'
  have hw := sourceContourHeightWeight_of_rapid m y C _ (norm_nonneg _) hw'
  have hm' := hM (sourcePoissonVertical c t)
    (by rw [sourcePoissonVertical_re]) (by rw [sourcePoissonVertical_re])
  rw [sourcePoissonVertical_im] at hm'
  have hm := sourceContourHeightWeight_of_rapid 0 t B _ (norm_nonneg _) hm'
  simp only [pow_zero, one_mul] at hm
  have hm₁ := hm.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one)
    (sourceContourHeightWeight_nonneg t))
  exact (mul_le_mul hw hm₁ (norm_nonneg _)
    (mul_nonneg (by positivity) (sourceContourHeightWeight_nonneg y))).trans_eq (by ring)

theorem sourceContinuedPoissonRowIntegral_norm_le_of_amplitude
    (hcut : principalAngularCutoff F J ⊆ S) (v : InfinitePlace F) (u : {a : R // a ≠ 0})
    (hu : ¬ ∃ x : F, x^6 = (u.val : F))
    {X Y Z : ℝ} (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z)
    (a b c : ℝ) (ha : 1 < a) (hb : 3/1000 ≤ b) (hc : 2/5 ≤ c)
    (m : ℕ) (B D : ℝ) (hB : 0 ≤ B)
    (hW : ∀ y t : ℝ, ((|y|+2)^m*‖sourceProbeW1Mellin (sourcePoissonVertical b y)‖)*
        ‖sourceSLocalProbeMellin F hζ S v (sourcePoissonVertical c t)‖ ≤
        D*(sourceContourHeightWeight y*sourceContourHeightWeight t))
    (hA : ∀ p : SourcePoissonHeights,
      let ξ := sourcePoissonVertical a p.2
      let w := sourcePoissonVertical b p.1.1
      let z := sourcePoissonVertical c p.1.2
      ‖(sourcePoissonFrequencyNorm F S₀ u : ℂ)^(-z)*
        sourceRowEulerContinuation F hζ S₀ u.val u.property η hJ (ξ,w,z)‖ ≤ B*(|p.1.1|+2)^m) :
    ‖sourceContinuedPoissonRowIntegral F S₀ hζ η hJ v u X Y Z a b c‖ ≤
      ‖(1/(2*Real.pi) : ℂ)^3‖ * (sourcePoissonTripleScale X Y Z a b c * B * D) *
        sourcePoissonInverseQuadraticMass := by
  have hi := sourceContinuedPoissonRowOnLines_integrable_right F S₀ hζ η hJ v u hcut hu hX hY hZ a b c ha hb hc
  let T := sourcePoissonTripleScale X Y Z a b c
  have hT : 0 ≤ T := by dsimp [T, sourcePoissonTripleScale]; positivity
  have h := sourcePoissonHeightIntegral_norm_le_of_majorant _ hi (T*B*D) (by
    intro p
    rw [sourceContinuedPoissonRowOnLines, sourceContinuedPoissonRowKernel_vertical_norm F S₀ hζ η hJ v u hX hY hZ]
    calc
      _ ≤ (T*(B*(|p.1.1|+2)^m))*
          ((‖sourceProbeW1Mellin (sourcePoissonVertical b p.1.1)‖*
            ‖sourceSLocalProbeMellin F hζ S v (sourcePoissonVertical c p.1.2)‖)*
              Real.exp (-((p.2+p.1.2)^2))) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hA p) hT) (by positivity)
      _ = (T*B)*(((|p.1.1|+2)^m*‖sourceProbeW1Mellin (sourcePoissonVertical b p.1.1)‖)*
          ‖sourceSLocalProbeMellin F hζ S v (sourcePoissonVertical c p.1.2)‖)*
            Real.exp (-((p.2+p.1.2)^2)) := by ring
      _ ≤ _ := (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hW p.1.1 p.1.2) (mul_nonneg hT hB)) (Real.exp_nonneg _)).trans_eq (by ring))
  rw [sourceContinuedPoissonRowIntegral, norm_mul]
  exact (mul_le_mul_of_nonneg_left h (norm_nonneg _)).trans_eq (by dsimp only [T]; ring)

end
end ArtinMatthews.SourceEulerAssembly
