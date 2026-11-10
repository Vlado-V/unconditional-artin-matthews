module

public import ArtinMatthews.CubicTheta
public import ArtinMatthews.CircleShiftedFrequency
public import ArtinMatthews.ShiftedDoubleVoronoiFubini
public import ArtinMatthews.CircleShiftedApproximation
public import ArtinMatthews.QuadraticIdealNormCountGlobal
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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

/-! A completely explicit polynomial error envelope for the actual ideal
theta coefficients. This uses the proved divisor bound, not a spectral input. -/

noncomputable section
open scoped BigOperators
namespace ArtinMatthews

local instance : FunLike (UpperHalfPlane → ℂ) UpperHalfPlane ℂ :=
  ⟨id, Function.injective_id⟩

theorem circleTheta_source_norm_le (χ : OAI.SevenEighths.HeckeFamily.Character)
    (H1 H2 : ℝ → ℂ) (K1 K2 : ℕ) (B1 B2 : ℝ) (hB1 : 0≤B1) (_hB2 : 0≤B2)
    (hw1 : ∀ n∈Finset.Icc 1 K1, ‖H1 n‖≤B1)
    (hw2 : ∀ n∈Finset.Icc 1 K2, ‖H2 n‖≤B2)
    (k : ℕ×ℕ) (hk : k∈(Finset.Icc 1 K1) ×ˢ (Finset.Icc 1 K2)) :
    ‖cuspSourcePair (heckeTheta χ) H1 H2 k‖ ≤ (K1 : ℝ)*K2*B1*B2 := by
  obtain ⟨hk1,hk2⟩ := Finset.mem_product.mp hk
  have hc1 : ‖idealThetaCoeff χ k.1‖≤(K1 : ℝ) := by
    apply (idealThetaCoeff_norm_le_divisors_card χ k.1).trans
    exact_mod_cast (Nat.card_divisors_le_self k.1).trans (Finset.mem_Icc.mp hk1).2
  have hc2 : ‖idealThetaCoeff χ k.2‖≤(K2 : ℝ) := by
    apply (idealThetaCoeff_norm_le_divisors_card χ k.2).trans
    exact_mod_cast (Nat.card_divisors_le_self k.2).trans (Finset.mem_Icc.mp hk2).2
  change ‖(UpperHalfPlane.qExpansion 1 (heckeTheta χ)).coeff k.1 *
    (UpperHalfPlane.qExpansion 1 (heckeTheta χ)).coeff k.2 * H1 k.1 * H2 k.2‖ ≤ _
  rw [heckeTheta_qExpansion_coeff,heckeTheta_qExpansion_coeff]
  simp only [norm_mul]
  exact mul_le_mul (mul_le_mul (mul_le_mul hc1 hc2 (norm_nonneg _) (Nat.cast_nonneg _))
    (hw1 _ hk1) (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))
    (hw2 _ hk2) (norm_nonneg _) (mul_nonneg
      (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hB1)

theorem circleTheta_original_approximation (χ : OAI.SevenEighths.HeckeFamily.Character)
    (m1 m2 K1 K2 : ℕ) (hm1 : 0 < m1) (hs1 : Squarefree m1)
    (H1 H2 : ℝ → ℂ) (B1 B2 : ℝ) (hB1 : 0≤B1) (hB2 : 0≤B2)
    (hw1 : ∀ n∈Finset.Icc 1 K1, ‖H1 n‖≤B1)
    (hw2 : ∀ n∈Finset.Icc 1 K2, ‖H2 n‖≤B2)
    (Q : Finset ℕ) (ω : ℕ → ℝ)
    (hω : ∀ q∈Q, 0≤ω q) (hΛ : 0<circleNormalizer Q ω) :
    let d := m1.gcd m2
    let m3 := m1/d
    let m4 := m2/d
    let A := cuspSourcePair (heckeTheta χ) H1 H2
    ‖(∑ k∈((Finset.Icc 1 K1) ×ˢ (Finset.Icc 1 K2)).filter
        (fun k => (d : ℤ)∣((k.1 : ℤ)-1)),
        A k*circleDetector Q ω (circleShiftedFrequency m3 m4 k)) -
      (∑ n∈(Finset.range (K1+1)).filter (fun n => m1*n+1≤K1 ∧ m2*n+1≤K2),
        A (m1*n+1,m2*n+1))‖ ≤
      ((K1 : ℝ)*K2)^2*B1*B2 *
        (circleWeightMass Q ω*((m4*K1+m3*K2 : ℕ) : ℝ)^2/circleNormalizer Q ω) := by
  intro d m3 m4 A
  apply (circleShifted_original_approximation m1 m2 K1 K2 hm1 hs1 A Q ω hω hΛ).trans
  apply mul_le_mul_of_nonneg_right
  · calc
      _ ≤ ∑ _k∈(Finset.Icc 1 K1) ×ˢ (Finset.Icc 1 K2), (K1 : ℝ)*K2*B1*B2 :=
        Finset.sum_le_sum (circleTheta_source_norm_le χ H1 H2 K1 K2 B1 B2 hB1 hB2 hw1 hw2)
      _ = _ := by
        simp only [Finset.sum_const,nsmul_eq_mul,Finset.card_product,
          Nat.card_Icc,Nat.add_one_sub_one,Nat.cast_mul]
        ring
  · exact div_nonneg (mul_nonneg (circleWeightMass_nonneg Q ω hω) (sq_nonneg _)) hΛ.le

end ArtinMatthews
