module

public import ArtinMatthews.SourceRowContinuedEuler
public import ArtinMatthews.SourceRowEulerPointwise
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

/-! Preserve the physical frequency power on a dyad. This gives the
source06 low-w exponent `1/2 - Re(z) + ε` and the far exponent
`-Re(z) + ε` before the number of rows is counted. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain AllowedGenerators VaryingKummerAnalytic
open scoped NumberField Classical BigOperators nonZeroDivisors
noncomputable section

theorem sourceDyadicFrequency_mul_bound {Q U a B : ℝ} {z L : ℂ}
    (hU : 0 < U) (hlo : U ≤ Q) (hhi : Q ≤ 2*U) (ha : 0 ≤ a) (hz : 0 ≤ z.re)
    (hB : 0 ≤ B) (hL : ‖L‖ ≤ B*Q^a) :
    ‖(Q : ℂ)^(-z)*L‖ ≤ (B*(2 : ℝ)^a)*U^(a-z.re) := by
  have hQ : 0 < Q := hU.trans_le hlo
  have hqa := Real.rpow_le_rpow hQ.le hhi ha
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hU.le] at hqa
  have hqz := Real.rpow_le_rpow_of_nonpos hU hlo (neg_nonpos.mpr hz)
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hQ, Complex.neg_re]
  calc
    _ ≤ U^(-z.re)*(B*((2 : ℝ)^a*U^a)) :=
      mul_le_mul hqz (hL.trans (mul_le_mul_of_nonneg_left hqa hB)) (norm_nonneg _) (by positivity)
    _ = (B*(2 : ℝ)^a)*(U^a*U^(-z.re)) := by ring
    _ = _ := by rw [← Real.rpow_add hU, sub_eq_add_neg]

variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
variable {M : Ideal (𝓞 F)} (η : EvenIdealRayCharacter F M) (hM : M ≠ ⊥)
local notation "S" => sourceHilbertSet F S₀
local notation "R" => sourceRing F S₀

theorem exists_sourceRowEulerContinuation_dyadic_low_w_bound
    (hcut : principalAngularCutoff F M ⊆ S) (b : ℝ) (hb : 1/6 < b) :
    ∃ m : ℕ, ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ (u : R) (hu : u ≠ 0), (¬ ∃ x : F, x^6 = (u : F)) →
        ∀ (U : ℝ), 0 < U →
        let Q := sourcePrimeExponentNorm F S₀ (sourceElementExponents F S₀ u hu)
        U ≤ (Q : ℝ) → (Q : ℝ) ≤ 2*U →
        ∀ p : ProbeCoordinates, p ∈ probeEulerDomain → (3/1000 : ℝ) ≤ p.2.1.re → b ≤ p.2.2.re →
        ‖(Q : ℂ)^(-p.2.2)*sourceRowEulerContinuation F hζ S₀ u hu η hM p‖ ≤
          C*U^(1/2-p.2.2.re+ε)*(|p.2.1.im|+2)^m*
            ‖sourceRowTwistReciprocal F hζ S₀ u hu η hM p.1‖ := by
  obtain ⟨m, h⟩ := exists_sourceRowEulerContinuation_low_w_bound F hζ S₀ η hM hcut b hb
  refine ⟨m, ?_⟩
  intro ε hε
  obtain ⟨C, hC, hbnd⟩ := h ε hε
  refine ⟨C*(2 : ℝ)^(1/2+ε), by positivity, ?_⟩
  intro u hu hu₆ U hU Q hlo hhi p hp hw hz
  let H := (|p.2.1.im|+2)^m
  let D := ‖sourceRowTwistReciprocal F hζ S₀ u hu η hM p.1‖
  have hL : ‖sourceRowEulerContinuation F hζ S₀ u hu η hM p‖ ≤ (C*H*D)*(Q : ℝ)^(1/2+ε) :=
    (hbnd u hu hu₆ p hp hw hz).trans_eq (by dsimp only [H,D,Q]; ring)
  have h := sourceDyadicFrequency_mul_bound hU hlo hhi (by positivity : 0 ≤ 1/2+ε)
    (by linarith : 0 ≤ p.2.2.re) (by dsimp [H,D]; positivity : 0 ≤ C*H*D) hL
  rw [← Complex.ofReal_natCast]
  refine h.trans_eq ?_
  rw [show 1/2+ε-p.2.2.re = 1/2-p.2.2.re+ε by ring]
  dsimp only [H,D]
  ring

theorem exists_sourceRowEulerContinuation_dyadic_right_bound
    (hcut : principalAngularCutoff F M ⊆ S) (a b : ℝ) (ha : 1 < a) (hb : 1/6 < b)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : R) (hu : u ≠ 0) (U : ℝ), 0 < U →
      let Q := sourcePrimeExponentNorm F S₀ (sourceElementExponents F S₀ u hu)
      U ≤ (Q : ℝ) → (Q : ℝ) ≤ 2*U →
      ∀ p : ProbeCoordinates, p ∈ probeEulerDomain →
        a ≤ p.1.re → a ≤ p.2.1.re → b ≤ p.2.2.re →
        ‖(Q : ℂ)^(-p.2.2)*sourceRowEulerContinuation F hζ S₀ u hu η hM p‖ ≤ C*U^(ε-p.2.2.re) := by
  obtain ⟨C, hC, h⟩ := exists_sourceRowEulerContinuation_right_bound F hζ S₀ η hM hcut a b ha hb ε hε
  refine ⟨C*(2 : ℝ)^ε, by positivity, ?_⟩
  intro u hu U hU Q hlo hhi p hp hξ hw hz
  rw [← Complex.ofReal_natCast]
  exact sourceDyadicFrequency_mul_bound hU hlo hhi hε.le (by linarith) hC.le (h u hu p hp hξ hw hz)

end
end ArtinMatthews.SourceEulerAssembly
