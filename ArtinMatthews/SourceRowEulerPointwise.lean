module

public import ArtinMatthews.SourceRowContinuedEuler
public import ArtinMatthews.SourceExteriorZetaBounds
public import ArtinMatthews.SourceGlobalCorrectionAnalytic
public import ArtinMatthews.SourcePrimeNormSummability
public import ArtinMatthews.SourceRowAnalyticBounds
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


set_option backward.privateInPublic true
@[expose] public section

/-! Pointwise bounds on the literal source Euler continuation. The
low-w estimate leaves the actual reciprocal as a separate factor so that
it applies on both the right line and the finite good-row box. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain AllowedGenerators VaryingKummerAnalytic
open scoped NumberField Classical BigOperators nonZeroDivisors
noncomputable section
variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
variable {M : Ideal (𝓞 F)} (η : EvenIdealRayCharacter F M) (hM : M ≠ ⊥)
local notation "S" => sourceHilbertSet F S₀
local notation "R" => sourceRing F S₀

theorem sourceRowEulerContinuation_norm (u : R) (hu : u ≠ 0) (p : ProbeCoordinates) :
    ‖sourceRowEulerContinuation F hζ S₀ u hu η hM p‖ =
      ‖principalExteriorZeta S (6*p.2.2)‖ * ‖sourceRowNumeratorContinued F hζ S₀ u hu p.2.1‖ *
      ‖sourceRowTwistReciprocal F hζ S₀ u hu η hM p.1‖ *
      ‖sourceGlobalCorrection F hζ S₀ η u hu p‖ := by
  simp only [sourceRowEulerContinuation, norm_mul]

theorem exists_sourceRowEulerContinuation_low_w_bound
    (hcut : principalAngularCutoff F M ⊆ S) (b : ℝ) (hb : 1/6 < b) :
    ∃ m : ℕ, ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ (u : R) (hu : u ≠ 0), (¬ ∃ x : F, x^6 = (u : F)) →
        ∀ p : ProbeCoordinates, p ∈ probeEulerDomain → (3/1000 : ℝ) ≤ p.2.1.re → b ≤ p.2.2.re →
        ‖sourceRowEulerContinuation F hζ S₀ u hu η hM p‖ ≤ C*
          (sourcePrimeExponentNorm F S₀ (sourceElementExponents F S₀ u hu) : ℝ)^(1/2+ε)*
          (|p.2.1.im|+2)^m*‖sourceRowTwistReciprocal F hζ S₀ u hu η hM p.1‖ := by
  obtain ⟨m, h⟩ := exists_sourceRowNumeratorContinued_source06_bound F hζ S₀
  refine ⟨m, ?_⟩
  intro ε hε
  obtain ⟨C, hC, hn⟩ := h (ε/2) (by positivity)
  obtain ⟨D, hD, hc⟩ := sourceGlobalCorrection_uniform_subpower F hζ S₀ η hM hcut (ε/2) (by positivity)
  let B := sourceRayAbsoluteEulerBound F (6*b) * (2 : ℝ)^(S).card
  have hB : 0 < B := mul_pos (sourceRayAbsoluteEulerBound_pos F _) (by positivity)
  refine ⟨B*C*D, by positivity, ?_⟩
  intro u hu hu₆ p hp hw hz
  let Q : ℝ := sourcePrimeExponentNorm F S₀ (sourceElementExponents F S₀ u hu)
  let E := ‖sourceRowTwistReciprocal F hζ S₀ u hu η hM p.1‖
  have hQ : 0 < Q := by
    dsimp only [Q]
    exact_mod_cast sourcePrimeExponentNorm_pos F S₀ (sourceElementExponents F S₀ u hu)
  have hN := hn u hu hu₆ p.2.1 hw
  have hH := hc u hu p hp
  have hZ := sourceExteriorZeta_scaled_norm_le_right F S hb hz
  rw [sourceRowEulerContinuation_norm F hζ S₀ η hM u hu p]
  calc
    _ ≤ (B*(C*Q^(1/2+ε/2)*(|p.2.1.im|+2)^m)*E)*(D*Q^(ε/2)) :=
      mul_le_mul (mul_le_mul_of_nonneg_right
        (mul_le_mul hZ hN (norm_nonneg _) hB.le) (norm_nonneg _)) hH (norm_nonneg _) (by positivity)
    _ = (B*C*D)*(Q^(1/2+ε/2)*Q^(ε/2))*(|p.2.1.im|+2)^m*E := by ring
    _ = _ := by rw [← Real.rpow_add hQ, show 1/2+ε/2+ε/2 = 1/2+ε by ring]

theorem exists_sourceRowEulerContinuation_right_bound
    (hcut : principalAngularCutoff F M ⊆ S) (a b : ℝ) (ha : 1 < a) (hb : 1/6 < b)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : R) (hu : u ≠ 0) (p : ProbeCoordinates), p ∈ probeEulerDomain →
      a ≤ p.1.re → a ≤ p.2.1.re → b ≤ p.2.2.re →
      ‖sourceRowEulerContinuation F hζ S₀ u hu η hM p‖ ≤ C*
        (sourcePrimeExponentNorm F S₀ (sourceElementExponents F S₀ u hu) : ℝ)^ε := by
  obtain ⟨D, hD, hc⟩ := sourceGlobalCorrection_uniform_subpower F hζ S₀ η hM hcut ε hε
  let A := sourceRayAbsoluteEulerBound F a
  let B := sourceRayAbsoluteEulerBound F (6*b) * (2 : ℝ)^(S).card
  have hA : 0 < A := sourceRayAbsoluteEulerBound_pos F a
  have hB : 0 < B := mul_pos (sourceRayAbsoluteEulerBound_pos F _) (by positivity)
  refine ⟨B*A*A*D, by positivity, ?_⟩
  intro u hu p hp hξ hw hz
  let Q : ℝ := sourcePrimeExponentNorm F S₀ (sourceElementExponents F S₀ u hu)
  have hZ := sourceExteriorZeta_scaled_norm_le_right F S hb hz
  have hN := sourceRowNumeratorContinued_norm_le_right F hζ S₀ u hu ha hw
  have hR := sourceRowTwistReciprocal_norm_le_right F hζ S₀ η hM u hu ha hξ
  have hH := hc u hu p hp
  rw [sourceRowEulerContinuation_norm F hζ S₀ η hM u hu p]
  calc
    _ ≤ B*A*A*(D*Q^ε) :=
      mul_le_mul (mul_le_mul (mul_le_mul hZ hN (norm_nonneg _) hB.le) hR
        (norm_nonneg _) (mul_nonneg hB.le hA.le)) hH (norm_nonneg _) (by positivity)
    _ = _ := by dsimp only [Q]; ring

end
end ArtinMatthews.SourceEulerAssembly
