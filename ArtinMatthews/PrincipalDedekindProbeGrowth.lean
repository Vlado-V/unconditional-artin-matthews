module

public import ArtinMatthews.PrincipalDedekindReciprocal
public import ArtinMatthews.PrincipalDedekindProbeBoundary
public import ArtinMatthews.VaryingKummerAnalyticConductorConvexity
public import ArtinMatthews.VaryingKummerAnalyticMixedDedekindGrowth
public import ArtinMatthews.VaryingKummerAnalyticMixedInverseGammaStripGrowth
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Actual polynomial growth of the pole-removed principal Dedekind function.
The strip maximum principle uses proved boundary and theta/Gamma growth inputs. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField Complex Set Filter
open scoped NumberField Classical Topology
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

theorem principalDedekindRegularized_convexity_strip_growth :
    ∃ C D R : ℝ, 0 < C ∧ 0 < D ∧ ∀ σ : ℝ,
      -(1/4 : ℝ) ≤ σ → σ ≤ 5/4 → ∀ t : ℝ, R ≤ |t| →
      ‖principalDedekindRegularized K ((σ : ℂ)+(t : ℂ)*I)‖ ≤
        C*Real.exp (D*(|t|+2)^2) := by
  obtain ⟨C,D,hC,hD,hGamma⟩ := exists_mixedInverseGammaFactor_strip_growth K
  obtain ⟨R,hR⟩ := eventually_atTop.mp
    (mixedCompletedDedekindXi_hasSubquadraticGrowth K 1 zero_lt_one)
  let A := mixedDiscriminantScale K
  have hA : 0 < A := mixedDiscriminantScale_pos K
  let CA := Real.exp (2*|Real.log A|)
  refine ⟨CA*C,D+1,max 1 R,mul_pos (Real.exp_pos _) hC,by linarith,?_⟩
  intro σ hσ hσ' t ht
  have hsabs : |σ| ≤ 2 := abs_le.mpr ⟨by linarith,by linarith⟩
  have hscale : ‖(A : ℂ)^(-((σ : ℂ)+(t : ℂ)*I))‖ ≤ CA := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hA]
    simp only [neg_re,add_re,ofReal_re,mul_re,ofReal_im,I_re,I_im,mul_zero,zero_mul,sub_zero,add_zero]
    rw [Real.rpow_def_of_pos hA]
    apply Real.exp_le_exp.mpr
    calc
      Real.log A*(-σ) ≤ |Real.log A*(-σ)| := le_abs_self _
      _ = |Real.log A| * |σ| := by rw [abs_mul,abs_neg]
      _ ≤ |Real.log A| * 2 := mul_le_mul_of_nonneg_left hsabs (abs_nonneg _)
      _ = _ := by ring
  have hz : ‖(σ : ℂ)+(t : ℂ)*I‖ ≤ |t|+2 := by
    calc
      _ ≤ ‖(σ : ℂ)‖+‖(t : ℂ)*I‖ := norm_add_le _ _
      _ = |σ|+|t| := by simp
      _ ≤ _ := by linarith
  have hcomplete := hR (|t|+2) (by linarith [le_max_right (1 : ℝ) R])
    ((σ : ℂ)+(t : ℂ)*I) hz
  simp only [one_mul] at hcomplete
  have hgam := hGamma σ hσ hσ' t (by linarith [le_max_left (1 : ℝ) R])
  have hden : 1 ≤ ‖(σ : ℂ)+(t : ℂ)*I‖ := by
    have hi := Complex.abs_im_le_norm ((σ : ℂ)+(t : ℂ)*I)
    norm_num at hi
    linarith [le_max_left (1 : ℝ) R]
  have hs0 : (σ : ℂ)+(t : ℂ)*I ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le zero_lt_one hden)
  rw [principalDedekindRegularized_eq_inverseGamma K hs0, norm_div, norm_mul, norm_mul]
  calc
    _ ≤ ‖(A : ℂ)^(-((σ : ℂ)+(t : ℂ)*I))‖ *
        ‖mixedInverseGammaFactor K ((σ : ℂ)+(t : ℂ)*I)‖ *
          ‖mixedCompletedDedekindXi K ((σ : ℂ)+(t : ℂ)*I)‖ :=
      div_le_self (by positivity) hden
    _ ≤ (CA*(C*Real.exp (D*(|t|+2)^2)))*Real.exp ((|t|+2)^2) :=
      mul_le_mul (mul_le_mul hscale hgam (norm_nonneg _) (Real.exp_pos _).le)
        hcomplete (norm_nonneg _) (by positivity)
    _ = (CA*C)*(Real.exp (D*(|t|+2)^2)*Real.exp ((|t|+2)^2)) := by ring
    _ = _ := by
      rw [← Real.exp_add]
      congr 1
      congr 1
      ring

theorem exists_principalDedekindRegularized_strip_polynomial_bound :
    ∃ (C : ℝ) (m : ℕ), 0 < C ∧ 1 ≤ m ∧ ∀ z : ℂ,
      -(1/4 : ℝ) ≤ z.re → z.re ≤ 5/4 →
      ‖principalDedekindRegularized K z‖ ≤ C*(|z.im|+2)^m := by
  obtain ⟨C,m,hC,hm,hleft,hright⟩ := exists_principalDedekindRegularized_boundary_bounds K
  let B := max 1 ((mixedDiscriminantScale K)^(3/2 : ℝ))
  have hB : 1 ≤ B := le_max_left _ _
  refine ⟨C*6^m*B,m,mul_pos (mul_pos hC (by positivity)) (zero_lt_one.trans_le hB),hm,?_⟩
  intro z hza hzb
  have h := conductor_strip_convexity (mixedDiscriminantScale_pos K) hC m
    (principalDedekindRegularized_entire K) hleft hright
    (principalDedekindRegularized_convexity_strip_growth K) hza hzb
  have hp : (mixedDiscriminantScale K)^(5/4-z.re) ≤ B := by
    by_cases hD : 1 ≤ mixedDiscriminantScale K
    · exact (Real.rpow_le_rpow_of_exponent_le hD (by linarith)).trans (le_max_right _ _)
    · exact (Real.rpow_le_one (mixedDiscriminantScale_pos K).le
        (le_of_lt (lt_of_not_ge hD)) (by linarith)).trans (le_max_left _ _)
  exact h.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hp (mul_nonneg hC.le (by positivity)))
    (pow_nonneg (by positivity) m))

theorem exists_mixedDedekindZeta_strip_bound_away_pole :
    ∃ (C : ℝ) (m : ℕ), 0 < C ∧ ∀ (δ : ℝ), 0 < δ → ∀ z : ℂ,
      -(1/4 : ℝ) ≤ z.re → z.re ≤ 5/4 → δ ≤ ‖z-1‖ →
      ‖mixedDedekindZeta K z‖ ≤ (C/δ)*(|z.im|+2)^m := by
  obtain ⟨C,m,hC,_hm,hf⟩ := exists_principalDedekindRegularized_strip_polynomial_bound K
  refine ⟨C,m,hC,?_⟩
  intro δ hδ z hza hzb hz
  change ‖principalDedekindRegularized K z / (z-1)‖ ≤ _
  rw [norm_div]
  calc
    _ ≤ (C*(|z.im|+2)^m)/δ :=
      div_le_div₀ (mul_nonneg hC.le (pow_nonneg (by positivity) _)) (hf z hza hzb) hδ hz
    _ = _ := by ring

theorem exists_mixedDedekindZeta_vertical_polynomial_bound
    (a : ℝ) (ha : -(1/4 : ℝ) ≤ a) (ha' : a ≤ 5/4) (ha1 : a ≠ 1) :
    ∃ (C : ℝ) (m : ℕ), 0 < C ∧ ∀ t : ℝ,
      ‖mixedDedekindZeta K ((a : ℂ)+(t : ℂ)*I)‖ ≤ C*(|t|+2)^m := by
  obtain ⟨C,m,hC,hf⟩ := exists_mixedDedekindZeta_strip_bound_away_pole K
  have hd : 0 < |a-1| := abs_pos.mpr (sub_ne_zero.mpr ha1)
  refine ⟨C/|a-1|,m,div_pos hC hd,?_⟩
  intro t
  have hb : |a-1| ≤ ‖((a : ℂ)+(t : ℂ)*I)-1‖ := by
    simpa using Complex.abs_re_le_norm (((a : ℂ)+(t : ℂ)*I)-1)
  simpa using hf |a-1| hd ((a : ℂ)+(t : ℂ)*I) (by simpa using ha) (by simpa using ha') hb

theorem exists_principalProbe_remainder_vertical_bounds :
    ∃ (C₁ C₂ : ℝ) (m₁ m₂ : ℕ), 0 < C₁ ∧ 0 < C₂ ∧
      (∀ t : ℝ, ‖mixedDedekindZeta K ((19/20 : ℂ)+(t : ℂ)*I)‖ ≤ C₁*(|t|+2)^m₁) ∧
      ∀ t : ℝ, ‖mixedDedekindZeta K ((24/25 : ℂ)+(t : ℂ)*I)‖ ≤ C₂*(|t|+2)^m₂ := by
  obtain ⟨C₁,m₁,hC₁,h₁⟩ := exists_mixedDedekindZeta_vertical_polynomial_bound K
    (19/20) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨C₂,m₂,hC₂,h₂⟩ := exists_mixedDedekindZeta_vertical_polynomial_bound K
    (24/25) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨C₁,C₂,m₁,m₂,hC₁,hC₂,by simpa using h₁,by simpa using h₂⟩

end
end ArtinMatthews.VaryingKummerAnalytic
