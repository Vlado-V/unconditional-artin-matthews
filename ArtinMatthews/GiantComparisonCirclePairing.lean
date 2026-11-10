module

public import ArtinMatthews.MarkedMinorArcProductFourier
public import ArtinMatthews.MarkedMinorArcCircle
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
public import Mathlib.Topology.Separation.CompletelyRegular
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The negative shift phase on the actual normalized circle selects
exactly the positive product shift in the finite endpoint pairing. -/
namespace ArtinMatthews
open MeasureTheory AddCircle
open scoped BigOperators ComplexConjugate
noncomputable section
local instance : Fact (0 < (1:ℝ)) := ⟨by norm_num⟩

local notation "Circle1" => AddCircle (1:ℝ)
local notation "haar" => @AddCircle.haarAddCircle (1:ℝ) _

def giantComparisonCircleMultiplier {A B : Type*} [Fintype A] [Fintype B]
    (μ : A → ℝ) (ν : B → ℝ) (p : A → ℕ) (q : B → ℕ)
    (f : A → ℂ) (g : B → ℂ) (θ : Circle1) : ℂ :=
  ∑ a, (μ a:ℂ)*f a*∑ b, (ν b:ℂ)*g b*fourier (-((p a*q b:ℕ):ℤ)) θ

theorem giantComparisonCircleMultiplier_continuous {A B : Type*} [Fintype A] [Fintype B]
    (μ : A → ℝ) (ν : B → ℝ) (p : A → ℕ) (q : B → ℕ)
    (f : A → ℂ) (g : B → ℂ) :
    Continuous (giantComparisonCircleMultiplier μ ν p q f g) := by
  unfold giantComparisonCircleMultiplier
  fun_prop

private theorem comparisonCircle_monomial_integral (j : ℤ) :
    (∫ θ : Circle1, fourier j θ ∂haar) = if j=0 then 1 else 0 := by
  have h := congrFun (fourierCoeff_fourier (T := (1:ℝ)) j) 0
  simpa only [fourierCoeff,neg_zero,fourier_zero,ContinuousMap.one_apply,one_smul,
    Pi.single_apply,eq_comm] using h

private theorem comparisonCircle_polynomial_apply (S : Finset ℤ) (U : S → ℂ) (θ : Circle1) :
    markedProductFourierPolynomial S U θ = ∑ u : S, U u*fourier u.val θ := by
  simp only [markedProductFourierPolynomial,ContinuousMap.sum_apply,ContinuousMap.smul_apply,smul_eq_mul]

private theorem comparisonCircle_integrable_of_continuous {F : Circle1 → ℂ}
    (hF : Continuous F) : Integrable F haar :=
  hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem giantComparisonCircle_singleShift (S T : Finset ℤ) (U : S → ℂ) (V : T → ℂ) (D : ℕ) :
    (∫ θ : Circle1, fourier (-(D:ℤ)) θ*conj (markedProductFourierPolynomial S U θ)*
      markedProductFourierPolynomial T V θ ∂haar) =
      ∑ u : S, ∑ v : T, if v.val=u.val+(D:ℤ) then conj (U u)*V v else 0 := by
  let F (u : S) (v : T) (θ : Circle1) :=
    (conj (U u)*V v)*fourier (v.val-u.val-(D:ℤ)) θ
  have he (θ : Circle1) : fourier (-(D:ℤ)) θ*conj (markedProductFourierPolynomial S U θ)*
      markedProductFourierPolynomial T V θ = ∑ u : S, ∑ v : T, F u v θ := by
    simp only [comparisonCircle_polynomial_apply,map_sum,map_mul,← fourier_neg,
      Finset.mul_sum,Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro u _
    apply Finset.sum_congr rfl
    intro v _
    dsimp only [F]
    rw [show v.val-u.val-(D:ℤ) = -(D:ℤ)+(-u.val)+v.val by ring,fourier_add,fourier_add]
    ring
  have hi (u : S) (v : T) : Integrable (F u v) haar :=
    comparisonCircle_integrable_of_continuous (continuous_const.mul (fourier _).continuous)
  simp_rw [he]
  rw [integral_finsetSum Finset.univ (fun u _ => integrable_finsetSum Finset.univ (fun v _ => hi u v))]
  apply Finset.sum_congr rfl
  intro u _
  rw [integral_finsetSum Finset.univ (fun v _ => hi u v)]
  apply Finset.sum_congr rfl
  intro v _
  dsimp only [F]
  rw [integral_const_mul,comparisonCircle_monomial_integral]
  have hindex : (v.val-u.val-(D:ℤ)=0) ↔ v.val=u.val+(D:ℤ) := by omega
  by_cases hshift : v.val=u.val+(D:ℤ)
  · rw [if_pos (hindex.mpr hshift), if_pos hshift, mul_one]
  · rw [if_neg ((not_congr hindex).mpr hshift), if_neg hshift, mul_zero]

theorem giantComparisonCircle_pairing {A B : Type*} [Fintype A] [Fintype B]
    (μ : A → ℝ) (ν : B → ℝ) (p : A → ℕ) (q : B → ℕ)
    (f : A → ℂ) (g : B → ℂ) (S T : Finset ℤ) (U : S → ℂ) (V : T → ℂ) :
    (∫ θ : Circle1, giantComparisonCircleMultiplier μ ν p q f g θ*
      conj (markedProductFourierPolynomial S U θ)*markedProductFourierPolynomial T V θ ∂haar) =
      ∑ a, (μ a:ℂ)*f a*∑ b, (ν b:ℂ)*g b*
        ∑ u : S, ∑ v : T, if v.val=u.val+((p a*q b:ℕ):ℤ) then conj (U u)*V v else 0 := by
  let K (D : ℕ) (θ : Circle1) :=
    fourier (-(D:ℤ)) θ*conj (markedProductFourierPolynomial S U θ)*markedProductFourierPolynomial T V θ
  have he (θ : Circle1) : giantComparisonCircleMultiplier μ ν p q f g θ*
      conj (markedProductFourierPolynomial S U θ)*markedProductFourierPolynomial T V θ =
      ∑ a, (μ a:ℂ)*f a*∑ b, (ν b:ℂ)*g b*K (p a*q b) θ := by
    simp only [giantComparisonCircleMultiplier,K,Finset.mul_sum,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring
  have hi (D : ℕ) : Integrable (K D) haar :=
    comparisonCircle_integrable_of_continuous
      (((fourier _).continuous.mul (markedProductFourierPolynomial S U).continuous.star).mul
        (markedProductFourierPolynomial T V).continuous)
  simp_rw [he]
  rw [integral_finsetSum Finset.univ (fun a _ =>
    (integrable_finsetSum Finset.univ (fun b _ => (hi (p a*q b)).const_mul _)).const_mul _)]
  apply Finset.sum_congr rfl
  intro a _
  rw [integral_const_mul,integral_finsetSum Finset.univ (fun b _ => (hi (p a*q b)).const_mul _)]
  congr 1
  apply Finset.sum_congr rfl
  intro b _
  rw [integral_const_mul]
  exact congrArg (fun z : ℂ => (ν b:ℂ)*g b*z) (giantComparisonCircle_singleShift S T U V (p a*q b))

end
end ArtinMatthews
