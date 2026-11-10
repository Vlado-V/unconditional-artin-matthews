module

public import ArtinMatthews.VaryingKummerAnalyticMixedZetaContinuation
public import ArtinMatthews.VaryingKummerAnalyticDedekindLogDerivativeBound
public import ArtinMatthews.VaryingKummerAnalyticMixedFunctionalNormalization
public import ArtinMatthews.VaryingKummerAnalyticMixedGammaLeft
public import ArtinMatthews.VaryingKummerAnalyticMixedGammaVertical
public import ArtinMatthews.VaryingKummerAnalyticMixedZeroScale
public import ArtinMatthews.VaryingKummerAnalyticMixedZetaFunctionalEquation
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
public import Mathlib.Tactic.Basify
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Genuine left-contour logarithmic-derivative estimate, uniform in both
field discriminant and degree, for the actual Dedekind continuation. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField Complex
open scoped Classical BigOperators
noncomputable section
universe u
variable (K : Type u) [Field K] [NumberField K]

omit [NumberField K] in
theorem mixedGammaArguments_left_away {s : ℂ} (hs : s.re = -(1/2 : ℝ)) :
    ∀ w : InfinitePlace K, ∀ n : ℕ, (InfinitePlace.mult w : ℂ)*s/2 ≠ -(n : ℂ) := by
  intro w
  have hm₁ : (1 : ℝ) ≤ InfinitePlace.mult w := InfinitePlace.one_le_mult
  have hm₂ : (InfinitePlace.mult w : ℝ) ≤ 2 := by
    unfold InfinitePlace.mult
    split_ifs <;> norm_num
  have hre : (((InfinitePlace.mult w : ℂ)*s/2).re) = -(InfinitePlace.mult w : ℝ)/4 := by
    simp [hs]
    ring
  apply gamma_left_argument_away
  · rw [hre]; linarith
  · rw [hre]; linarith

theorem mixedDiscriminantScale_log_abs_le :
    2*|Real.log (mixedDiscriminantScale K)| ≤
      Real.log |(discr K : ℝ)| + (Module.finrank ℚ K : ℝ)*Real.log 2 := by
  rw [mixedDiscriminantScale_log]
  have hD := discr_log_nonneg K
  have hlog : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  have hc : (0 : ℝ) ≤ InfinitePlace.nrComplexPlaces K := Nat.cast_nonneg _
  have hn : 2*(InfinitePlace.nrComplexPlaces K : ℝ) ≤ (Module.finrank ℚ K : ℝ) := by
    exact_mod_cast (show 2*InfinitePlace.nrComplexPlaces K ≤ Module.finrank ℚ K by
      rw [← InfinitePlace.card_add_two_mul_card_eq_rank K]
      omega)
  have H : |-(InfinitePlace.nrComplexPlaces K : ℝ)*Real.log 2 + Real.log |(discr K : ℝ)|/2| ≤
      Real.log |(discr K : ℝ)|/2 + (InfinitePlace.nrComplexPlaces K : ℝ)*Real.log 2 := by
    apply abs_le.mpr
    constructor <;> nlinarith [mul_nonneg hc hlog]
  have Hn := mul_le_mul_of_nonneg_right hn hlog
  linarith

/-- The exact functional equation gives the required left-line estimate
without any assumed zeta continuation or assumed uniform analytic bound. -/
theorem exists_mixedDedekind_left_logarithmic_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : Type u) [Field K] [NumberField K], ∀ s : ℂ,
      s.re = -(1/2 : ℝ) →
      ‖logDeriv (mixedDedekindZetaContinuation K) s‖ ≤
        C*(Real.log |(discr K : ℝ)| +
          (Module.finrank ℚ K : ℝ)*Real.log (|s.im|+2)) := by
  obtain ⟨B,hB,hleft⟩ := exists_mixedGammaFactor_left_logarithmic_bound.{u}
  obtain ⟨A,hA,hright⟩ := exists_mixedGammaFactor_vertical_logarithmic_bound.{u}
  let E := dedekindLogDerivUniformConstant
  have hE : 0 < E := dedekindLogDerivUniformConstant_pos
  have hl2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  let C := 2+B+A+E/Real.log 2
  have hC : 1 < C := by
    have hd : 0 < E/Real.log 2 := div_pos hE hl2
    dsimp [C]
    linarith
  refine ⟨C,by linarith,?_⟩
  intro K _ _ s hs
  have ht : (1-s).re = (3/2 : ℝ) := by simp [hs]; norm_num
  have hi : |(1-s).im| = |s.im| := by simp
  have hbl := hleft K s hs
  have hbr := hright K (1-s) (by rw [ht]; norm_num) (by rw [ht]; norm_num)
  rw [hi] at hbr
  have he := dedekindZeta_logDeriv_norm_le K (s := 1-s) (by rw [ht])
  have hl : Real.log 2 ≤ Real.log (|s.im|+2) :=
    Real.log_le_log (by norm_num) (by linarith [abs_nonneg s.im])
  have hn : (0 : ℝ) ≤ Module.finrank ℚ K := Nat.cast_nonneg _
  have hdn := discr_log_nonneg K
  have hnorm : ‖logDeriv (mixedDedekindZetaContinuation K) s‖ ≤
      2*|Real.log (mixedDiscriminantScale K)| +
      B*(Module.finrank ℚ K : ℝ)*Real.log (|s.im|+2) +
      A*(Module.finrank ℚ K : ℝ)*Real.log (|s.im|+2) + E*(Module.finrank ℚ K : ℝ) := by
    rw [mixedDedekindZetaContinuation_logDeriv_left K (by rw [hs]; norm_num)
      (mixedGammaArguments_left_away K hs)]
    calc
      _ ≤ ‖-(2*(Real.log (mixedDiscriminantScale K) : ℂ))‖ +
        ‖logDeriv (mixedGammaFactor K) s‖ + ‖logDeriv (mixedGammaFactor K) (1-s)‖ +
        ‖logDeriv (dedekindZeta K) (1-s)‖ := by
          grw [norm_sub_le, norm_sub_le, norm_sub_le]
      _ ≤ _ := by
        simp only [norm_neg,norm_mul,Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs]
        exact add_le_add (add_le_add (add_le_add le_rfl hbl) hbr) he
  have hdisc := mixedDiscriminantScale_log_abs_le K
  have hlogn := mul_le_mul_of_nonneg_left hl hn
  have hEn : E*(Module.finrank ℚ K : ℝ) ≤
      (E/Real.log 2)*(Module.finrank ℚ K : ℝ)*Real.log (|s.im|+2) := by
    calc
      _ = (E/Real.log 2)*(Module.finrank ℚ K : ℝ)*Real.log 2 := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hl (by positivity)
  have hpos : 0 ≤ (Module.finrank ℚ K : ℝ)*Real.log (|s.im|+2) :=
    mul_nonneg hn (le_trans hl2.le hl)
  have hCd := mul_le_mul_of_nonneg_right hC.le hdn
  dsimp [C] at hC ⊢
  nlinarith

end
end ArtinMatthews.VaryingKummerAnalytic
