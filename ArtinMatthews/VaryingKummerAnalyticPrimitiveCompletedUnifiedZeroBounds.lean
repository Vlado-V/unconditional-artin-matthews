module

public import ArtinMatthews.VaryingKummerAnalyticPrimitiveCompletedUnifiedPair
public import ArtinMatthews.VaryingKummerAnalyticComplexZeroPole
public import ArtinMatthews.VaryingKummerAnalyticZeroHeightWindow
public import ArtinMatthews.VaryingKummerAnalyticComplexZeroCount
public import ArtinMatthews.VaryingKummerAnalyticPrimitiveCompletedUnifiedLogDerivative
public import ArtinMatthews.VaryingKummerAnalyticWeightedZeroSum
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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

/-! Quantitative zero bounds for the actual unified inverse-character
product. All constants come from the proved Gamma and ideal Euler estimates;
boundary nonvanishing remains an explicit arithmetic input. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField OAI.PrimeDegreePackets.AnalyticGrowth
open scoped NumberField nonZeroDivisors Classical BigOperators
noncomputable section
namespace EvenIdealRayCharacter
variable {K : Type*} [Field K] [NumberField K] {M : Ideal (𝓞 K)}
variable (ψ : EvenIdealRayCharacter K M) (hM : M ≠ ⊥)
variable (hprim : OAI.SevenEighths.FiniteFourier.IsPrimitiveOnIdeals ψ.residue)
variable (hnp : ψ.IsNonprincipal)
include hprim hnp

theorem primitiveCompletedUnifiedPair_logDeriv_eq_primitive {s : ℂ} (hs : 1 < s.re) :
    logDeriv (ψ.primitiveCompletedUnifiedPair hM) s =
      2*(Real.log (mixedConductorScale K (integralIdealFractionalUnit M hM)):ℂ) +
        2*logDeriv (mixedGammaFactor K) s +
          logDeriv (ψ.primitiveContinued hM hprim) s +
            logDeriv (ψ.inverse.primitiveContinued hM (ψ.inverse_isPrimitive hM hprim)) s := by
  rw [ψ.primitiveCompletedUnifiedPair_logDeriv hM hprim hnp hs,
    ψ.primitiveCompletedUnified_logDeriv hM hprim hnp hs,
    ψ.inverse.primitiveCompletedUnified_logDeriv hM
      (ψ.inverse_isPrimitive hM hprim) (ψ.inverse_isNonprincipal hnp) hs]
  ring

theorem primitiveCompletedUnifiedPair_hasSum_complexZeroPole
    (h0 : ψ.primitiveCompletedUnifiedPair hM 0 ≠ 0) {s : ℂ} (hs : 1 < s.re) :
    HasSum (complexZeroPole (ψ.primitiveCompletedUnifiedPair hM) s)
      (logDeriv (ψ.primitiveCompletedUnifiedPair hM) s).re :=
  hasSum_complexZeroPole (ψ.primitiveCompletedUnifiedPair_entire hM hprim) h0
    (ψ.primitiveCompletedUnifiedPair_hasSubquadraticGrowth hM hprim)
    (ψ.primitiveCompletedUnifiedPair_functionalEquation hM hprim hnp)
    (fun _ h => (ψ.primitiveCompletedUnifiedPair_zero_strip hM hprim hnp h).2) hs

theorem primitiveCompletedUnifiedPair_finite_zero_height_window_bound
    (h0 : ψ.primitiveCompletedUnifiedPair hM 0 ≠ 0)
    (S : Finset ℂ) (T : ℝ) (hT : ∀ ρ ∈ S, |T-ρ.im| ≤ 1) :
    (∑ ρ ∈ S, (zeroMultiplicity (ψ.primitiveCompletedUnifiedPair hM) ρ : ℝ)) ≤
      5*(logDeriv (ψ.primitiveCompletedUnifiedPair hM) (⟨2,T⟩ : ℂ)).re :=
  finite_zero_height_window_bound (ψ.primitiveCompletedUnifiedPair_entire hM hprim) h0
    (ψ.primitiveCompletedUnifiedPair_hasSubquadraticGrowth hM hprim)
    (ψ.primitiveCompletedUnifiedPair_functionalEquation hM hprim hnp)
    (fun _ h => (ψ.primitiveCompletedUnifiedPair_zero_strip hM hprim hnp h).2) S T hT

theorem primitiveCompletedUnifiedPair_zeroHeightCount_le_logDeriv
    (h0 : ψ.primitiveCompletedUnifiedPair hM 0 ≠ 0) (T : ℝ) :
    zeroHeightCount (ψ.primitiveCompletedUnifiedPair hM) T ≤
      5*(logDeriv (ψ.primitiveCompletedUnifiedPair hM) (⟨2,T⟩ : ℂ)).re :=
  zeroHeightCount_le_logDeriv (ψ.primitiveCompletedUnifiedPair_entire hM hprim) h0
    (ψ.primitiveCompletedUnifiedPair_hasSubquadraticGrowth hM hprim)
    (ψ.primitiveCompletedUnifiedPair_functionalEquation hM hprim hnp)
    (fun _ h => (ψ.primitiveCompletedUnifiedPair_zero_strip hM hprim hnp h).2) T

theorem primitiveCompletedUnifiedPair_weighted_zero_summable_and_bound
    (h0 : ψ.primitiveCompletedUnifiedPair hM 0 ≠ 0) {Φ : ℂ → ℂ} {C : ℝ}
    (hC : 0 ≤ C)
    (hΦ : ∀ ρ, ψ.primitiveCompletedUnifiedPair hM ρ = 0 → ‖Φ ρ‖ ≤ C/(1+|ρ.im|)^2) :
    Summable (fun ρ => (zeroMultiplicity (ψ.primitiveCompletedUnifiedPair hM) ρ : ℂ)*Φ ρ) ∧
      (∑' ρ, ‖(zeroMultiplicity (ψ.primitiveCompletedUnifiedPair hM) ρ : ℂ)*Φ ρ‖) ≤
        4*C*(logDeriv (ψ.primitiveCompletedUnifiedPair hM) 2).re :=
  weighted_zero_summable_and_bound (ψ.primitiveCompletedUnifiedPair_entire hM hprim) h0
    (ψ.primitiveCompletedUnifiedPair_hasSubquadraticGrowth hM hprim)
    (ψ.primitiveCompletedUnifiedPair_functionalEquation hM hprim hnp) hC
    (fun _ => ψ.primitiveCompletedUnifiedPair_zero_strip hM hprim hnp) hΦ

end EvenIdealRayCharacter

universe u

theorem exists_primitiveCompletedUnifiedPair_logDeriv_conductor_bound :
    ∃ B : ℝ, 0 < B ∧ ∀ (K : Type u) [Field K] [NumberField K]
      (M : Ideal (𝓞 K)) (hM : M ≠ ⊥) (ψ : EvenIdealRayCharacter K M)
      (_hprim : OAI.SevenEighths.FiniteFourier.IsPrimitiveOnIdeals ψ.residue)
      (_hnp : ψ.IsNonprincipal) (s : ℂ), 3/2 ≤ s.re → s.re ≤ 2 →
      ‖logDeriv (ψ.primitiveCompletedUnifiedPair hM) s‖ ≤
        Real.log |(discr K:ℝ)| + Real.log (Ideal.absNorm M:ℝ) +
          B*(Module.finrank ℚ K:ℝ)*Real.log (|s.im|+2) := by
  obtain ⟨B,hB,HB⟩ := exists_primitiveCompletedUnified_logDeriv_conductor_bound
  refine ⟨2*B,by positivity,?_⟩
  intro K _ _ M hM ψ hprim hnp s hs hs'
  have hF := HB K M hM ψ hprim hnp s hs hs'
  have hG := HB K M hM ψ.inverse (ψ.inverse_isPrimitive hM hprim)
    (ψ.inverse_isNonprincipal hnp) s hs hs'
  rw [ψ.primitiveCompletedUnifiedPair_logDeriv hM hprim hnp (by linarith)]
  calc
    _ ≤ ‖logDeriv (ψ.primitiveCompletedUnified hM) s‖ +
        ‖logDeriv (ψ.inverse.primitiveCompletedUnified hM) s‖ := norm_add_le _ _
    _ ≤ _ := by nlinarith

theorem exists_primitiveCompletedUnifiedPair_finite_height_bound :
    ∃ B : ℝ, 0 < B ∧ ∀ (K : Type u) [Field K] [NumberField K]
      (M : Ideal (𝓞 K)) (hM : M ≠ ⊥) (ψ : EvenIdealRayCharacter K M)
      (_hprim : OAI.SevenEighths.FiniteFourier.IsPrimitiveOnIdeals ψ.residue)
      (_hnp : ψ.IsNonprincipal) (_h0 : ψ.primitiveCompletedUnifiedPair hM 0 ≠ 0)
      (S : Finset ℂ) (T : ℝ), (∀ ρ ∈ S, |T-ρ.im| ≤ 1) →
      (∑ ρ ∈ S, (zeroMultiplicity (ψ.primitiveCompletedUnifiedPair hM) ρ : ℝ)) ≤
        5*Real.log |(discr K:ℝ)| + 5*Real.log (Ideal.absNorm M:ℝ) +
          B*(Module.finrank ℚ K:ℝ)*Real.log (|T|+2) := by
  obtain ⟨B,hB,HB⟩ := exists_primitiveCompletedUnifiedPair_logDeriv_conductor_bound
  refine ⟨5*B,by positivity,?_⟩
  intro K _ _ M hM ψ hprim hnp h0 S T hT
  have H := ψ.primitiveCompletedUnifiedPair_finite_zero_height_window_bound
    hM hprim hnp h0 S T hT
  have hB := (Complex.re_le_norm _).trans
    (HB K M hM ψ hprim hnp (⟨2,T⟩ : ℂ) (by norm_num) (by norm_num))
  change (logDeriv (ψ.primitiveCompletedUnifiedPair hM) (⟨2,T⟩ : ℂ)).re ≤
    Real.log |(discr K:ℝ)| + Real.log (Ideal.absNorm M:ℝ) +
      B*(Module.finrank ℚ K:ℝ)*Real.log (|T|+2) at hB
  nlinarith

theorem exists_primitiveCompletedUnifiedPair_zeroHeight_bound :
    ∃ B : ℝ, 0 < B ∧ ∀ (K : Type u) [Field K] [NumberField K]
      (M : Ideal (𝓞 K)) (hM : M ≠ ⊥) (ψ : EvenIdealRayCharacter K M)
      (_hprim : OAI.SevenEighths.FiniteFourier.IsPrimitiveOnIdeals ψ.residue)
      (_hnp : ψ.IsNonprincipal) (_h0 : ψ.primitiveCompletedUnifiedPair hM 0 ≠ 0) (T : ℝ),
      zeroHeightCount (ψ.primitiveCompletedUnifiedPair hM) T ≤
        5*Real.log |(discr K:ℝ)| + 5*Real.log (Ideal.absNorm M:ℝ) +
          B*(Module.finrank ℚ K:ℝ)*Real.log (|T|+2) := by
  obtain ⟨B,hB,HB⟩ := exists_primitiveCompletedUnifiedPair_finite_height_bound
  refine ⟨B,hB,?_⟩
  intro K _ _ M hM ψ hprim hnp h0 T
  apply HB K M hM ψ hprim hnp h0 (zeroHeightWindow (ψ.primitiveCompletedUnifiedPair hM) T) T
  intro ρ hρ
  exact (Finset.mem_filter.mp hρ).2

theorem exists_primitiveContinuedPair_finite_height_bound :
    ∃ B : ℝ, 0 < B ∧ ∀ (K : Type u) [Field K] [NumberField K]
      (M : Ideal (𝓞 K)) (hM : M ≠ ⊥) (ψ : EvenIdealRayCharacter K M)
      (hprim : OAI.SevenEighths.FiniteFourier.IsPrimitiveOnIdeals ψ.residue)
      (_hnp : ψ.IsNonprincipal) (_h0 : ψ.primitiveCompletedUnifiedPair hM 0 ≠ 0)
      (S : Finset ℂ) (T : ℝ), (∀ ρ ∈ S, 0 < ρ.re) → (∀ ρ ∈ S, |T-ρ.im| ≤ 1) →
      (∑ ρ ∈ S, ((zeroMultiplicity (ψ.primitiveContinued hM hprim) ρ : ℝ) +
        (zeroMultiplicity (ψ.inverse.primitiveContinued hM (ψ.inverse_isPrimitive hM hprim)) ρ : ℝ))) ≤
        5*Real.log |(discr K:ℝ)| + 5*Real.log (Ideal.absNorm M:ℝ) +
          B*(Module.finrank ℚ K:ℝ)*Real.log (|T|+2) := by
  obtain ⟨B,hB,HB⟩ := exists_primitiveCompletedUnifiedPair_finite_height_bound
  refine ⟨B,hB,?_⟩
  intro K _ _ M hM ψ hprim hnp h0 S T hpos hT
  have H := HB K M hM ψ hprim hnp h0 S T hT
  have he : (∑ ρ ∈ S, (zeroMultiplicity (ψ.primitiveCompletedUnifiedPair hM) ρ : ℝ)) =
      ∑ ρ ∈ S, ((zeroMultiplicity (ψ.primitiveContinued hM hprim) ρ : ℝ) +
        (zeroMultiplicity (ψ.inverse.primitiveContinued hM (ψ.inverse_isPrimitive hM hprim)) ρ : ℝ)) := by
    apply Finset.sum_congr rfl
    intro ρ hρ
    rw [ψ.primitiveCompletedUnifiedPair_zeroMultiplicity_eq_primitive hM hprim hnp h0 (hpos ρ hρ),
      Int.cast_add]
  rwa [he] at H

theorem exists_primitiveCompletedUnifiedPair_weighted_zero_bound :
    ∃ B : ℝ, 0 < B ∧ ∀ (K : Type u) [Field K] [NumberField K]
      (M : Ideal (𝓞 K)) (hM : M ≠ ⊥) (ψ : EvenIdealRayCharacter K M)
      (_hprim : OAI.SevenEighths.FiniteFourier.IsPrimitiveOnIdeals ψ.residue)
      (_hnp : ψ.IsNonprincipal) (_h0 : ψ.primitiveCompletedUnifiedPair hM 0 ≠ 0)
      (Φ : ℂ → ℂ) (C : ℝ), 0 ≤ C →
      (∀ ρ, ψ.primitiveCompletedUnifiedPair hM ρ = 0 → ‖Φ ρ‖ ≤ C/(1+|ρ.im|)^2) →
      Summable (fun ρ => (zeroMultiplicity (ψ.primitiveCompletedUnifiedPair hM) ρ : ℂ)*Φ ρ) ∧
        (∑' ρ, ‖(zeroMultiplicity (ψ.primitiveCompletedUnifiedPair hM) ρ : ℂ)*Φ ρ‖) ≤
          4*C*(Real.log |(discr K:ℝ)| + Real.log (Ideal.absNorm M:ℝ) +
            B*(Module.finrank ℚ K:ℝ)) := by
  obtain ⟨B,hB,HB⟩ := exists_primitiveCompletedUnifiedPair_logDeriv_conductor_bound
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨B*Real.log 2,by positivity,?_⟩
  intro K _ _ M hM ψ hprim hnp h0 Φ C hC hΦ
  obtain ⟨hS,H⟩ := ψ.primitiveCompletedUnifiedPair_weighted_zero_summable_and_bound
    hM hprim hnp h0 hC hΦ
  refine ⟨hS,H.trans ?_⟩
  have hB := (Complex.re_le_norm _).trans
    (HB K M hM ψ hprim hnp (2 : ℂ) (by norm_num) (by norm_num))
  have he : B*(Module.finrank ℚ K:ℝ)*Real.log (|(2 : ℂ).im|+2) =
      (B*Real.log 2)*(Module.finrank ℚ K:ℝ) := by norm_num; ring
  rw [he] at hB
  exact mul_le_mul_of_nonneg_left hB (by positivity : 0 ≤ 4*C)

end
end ArtinMatthews.VaryingKummerAnalytic
