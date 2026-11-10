module

public import ArtinMatthews.QuadraticHeckeScaleOptimizer
public import ArtinMatthews.SourceQuadraticB3PoissonBound
public import ArtinMatthews.QuadraticB2DescentIteration
public import ArtinMatthews.QuadraticB2NearScale
public import ArtinMatthews.SourceQuadraticB2BallStep
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

/-! Theorem 4.3 from the actual annular Proposition 5.2. The cutoff
remains fixed, column lengths descend to one, and the near range uses
E_alpha directly. All growing-scale losses are included in the budget. -/
namespace ArtinMatthews.SourceEulerAssembly

open NumberField IsDedekindDomain StandardAdelic QuadraticScale
open scoped NumberField Classical BigOperators

noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable {G : Type} [Fintype G] [DecidableEq G]
local notation "E" => SourcePrimeExponents F S₀
local notation "energy" => sourceQuadraticDyadicEnergy F S₀ hζ

theorem sourceQuadraticPoissonScaleBound_of_B3 (label : E → G) {a : ℝ} (ha : 1 < a)
    (hE : QuadraticHeckeSieveExponentBound energy a)
    (hpoisson : SourceQuadraticB3PoissonBound F S₀ hζ label a) :
    QuadraticHeckePoissonScaleBound energy a := by
  intro ε hε
  obtain ⟨r, δ, hr, hδ, hbudget, hnearBudget⟩ := exists_descent_precision a ε ha hε
  obtain ⟨A, hA, hstep⟩ := exists_sourceQuadraticB2_ball_step F S₀ hζ label ha.le hδ hpoisson
  obtain ⟨C, hC, hbase⟩ := sourceQuadraticSmoothedB2Norm_crude F S₀ hζ
  obtain ⟨D, hD, hnear⟩ := hE (ε / 2) (half_pos hε)
  have hA0 : 0 < A := zero_lt_one.trans_le hA
  let C₀ := max 1 C
  let far := ((r : ℝ) + 1) * A ^ r * C₀
  let near := D * (1 + (2 : ℝ) ^ (a - 1))
  have hC₀ : 1 ≤ C₀ := le_max_left _ _
  have hfar : 0 < far := by dsimp [far]; positivity
  have hnear0 : 0 < near := by dsimp [near]; positivity
  refine ⟨max far near, lt_of_lt_of_le hfar (le_max_left _ _), ?_⟩
  intro M N hM hN
  let T := M * N
  let main := poissonMainScale M N a
  have hM0 := zero_lt_one.trans_le hM
  have hN0 := zero_lt_one.trans_le hN
  have hT : 1 ≤ T := one_le_mul_of_one_le_of_one_le hM hN
  have hT0 := zero_lt_one.trans_le hT
  have hmain : 0 ≤ main := poissonMainScale_nonneg hM0.le hN0.le a
  by_cases hsep : 2 * N * T ^ δ ≤ M
  · let K := poissonCutoff M N δ
    let H := N ^ (r : ℝ)⁻¹
    let X (i : ℕ) := sourceQuadraticSmoothedB2Norm F S₀ hζ M K (descentColumn N H i)
    let β := δ * (a + 3 / 2)
    let step := A * T ^ β
    let target := C₀ * H ^ 5 * main
    have hH : 1 ≤ H := descentRatio_one_le hN r
    have hH0 := zero_lt_one.trans_le hH
    have htarget : 0 ≤ target := by dsimp [target]; positivity
    have hSmallTarget : H ^ (5 : ℕ) * main ≤ target := by
      simpa only [target, mul_assoc] using le_mul_of_one_le_left
        (mul_nonneg (pow_nonneg hH0.le 5) hmain) hC₀
    have hstep1 : 1 ≤ step := one_le_mul_of_one_le_of_one_le hA
      (Real.one_le_rpow hT (mul_nonneg hδ.le (by linarith)))
    have hmainM : M ≤ main := by
      change M ≤ M + N + N ^ (2 * a - 1) * M ^ (1 - a)
      have hp : 0 ≤ N ^ (2 * a - 1) * M ^ (1 - a) := by positivity
      linarith
    have hXbase : X r ≤ target := by
      change sourceQuadraticSmoothedB2Norm F S₀ hζ M K (descentColumn N H r) ≤ _
      rw [show descentColumn N H r = 1 from descentColumn_final hN hr]
      calc
        _ ≤ C * M * 1 := hbase M K 1 hM le_rfl
        _ ≤ C₀ * M := by
          rw [mul_one]
          exact mul_le_mul_of_nonneg_right (le_max_right _ _) hM0.le
        _ ≤ _ := by
          simpa only [target, mul_assoc] using mul_le_mul_of_nonneg_left
            (hmainM.trans (le_mul_of_one_le_left hmain
              (one_le_pow₀ hH : 1 ≤ H ^ (5 : ℕ)))) (zero_le_one.trans hC₀)
    have hXstep (i : ℕ) (hi : i < r) : X i ≤ step * (X (i + 1) + target) := by
      have hLi := descentColumn_bounds hN hr hi.le
      have hh := hstep M N (descentColumn N H i) H hM hN hLi.1 hLi.2 hH hsep
      change X i ≤ _ at hh
      rw [← descentColumn_succ N H i] at hh
      refine hh.trans ?_
      change step * (X (i + 1) + H ^ 5 * main) ≤ _
      apply mul_le_mul_of_nonneg_left _ (zero_le_one.trans hstep1)
      exact add_le_add_right hSmallTarget _
    have hiter := descent_iterate X r hstep1 htarget hXbase hXstep
    have hK := poissonCutoff_range hM hN hδ.le hsep hN le_rfl
    have hentry : energy M N ≤ X 0 := by
      rw [show X 0 = sourceQuadraticSmoothedB2Norm F S₀ hζ M K N by simp [X, descentColumn]]
      exact sourceQuadraticDyadicEnergy_le_smoothedB2 F S₀ hζ hM0 hK.2.1 hN0.le
    have hH5 : H ^ (5 : ℕ) ≤ T ^ (5 / (r : ℝ)) := by
      have hr0 : 0 < (r : ℝ) := by exact_mod_cast hr
      have he : H ^ (5 : ℕ) = N ^ (5 / (r : ℝ)) := by
        dsimp [H]
        rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
        congr 1
        field_simp
        norm_num
      rw [he]
      exact Real.rpow_le_rpow hN0.le (le_mul_of_one_le_left hN0.le hM) (by positivity)
    have hpower : (T ^ β) ^ r * H ^ (5 : ℕ) ≤ T ^ ε := by
      calc
        _ ≤ (T ^ β) ^ r * T ^ (5 / (r : ℝ)) :=
          mul_le_mul_of_nonneg_left hH5 (by positivity)
        _ = T ^ (β * (r : ℝ) + 5 / (r : ℝ)) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hT0.le, ← Real.rpow_add hT0]
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hT hbudget
    calc
      energy M N ≤ X 0 := hentry
      _ ≤ ((r : ℝ) + 1) * step ^ r * target := hiter
      _ = far * ((T ^ β) ^ r * H ^ (5 : ℕ)) * main := by
        dsimp [step, target, far]
        rw [mul_pow]
        ring
      _ ≤ far * T ^ ε * main := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpower hfar.le) hmain
      _ ≤ max far near * (M * N) ^ ε *
          (M + N + N ^ (2 * a - 1) * M ^ (1 - a)) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hT0.le _)) hmain
  · have hnear' : M ≤ 2 * N * T ^ δ := (lt_of_not_ge hsep).le
    have hterm := nearScale_main_bound hM hN ha.le hδ.le hnear'
    have hbudget' : ε / 2 + δ * (a - 1) ≤ ε := by
      have h := mul_le_mul_of_nonneg_left (show a - 1 ≤ 2 * a - 1 by linarith) hδ.le
      linarith
    have hpower : T ^ (ε / 2) * T ^ (δ * (a - 1)) ≤ T ^ ε := by
      rw [← Real.rpow_add hT0]
      exact Real.rpow_le_rpow_of_exponent_le hT hbudget'
    calc
      energy M N ≤ D * T ^ (ε / 2) * (M + N ^ a) := hnear M N hM hN
      _ ≤ D * T ^ (ε / 2) *
          ((1 + (2 : ℝ) ^ (a - 1)) * T ^ (δ * (a - 1)) * main) :=
        mul_le_mul_of_nonneg_left hterm (by positivity)
      _ = near * (T ^ (ε / 2) * T ^ (δ * (a - 1))) * main := by dsimp [near]; ring
      _ ≤ near * T ^ ε * main := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpower hnear0.le) hmain
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hT0.le _)) hmain

end
end ArtinMatthews.SourceEulerAssembly
