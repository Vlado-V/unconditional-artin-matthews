module

public import ArtinMatthews.MarkedMajorMellinConstructed
public import ArtinMatthews.MarkedMajorFourierSeparationExp
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Finset MeasureTheory Complex
noncomputable section

def markedMajorEndpointPolynomial {α : Type*} (S : Finset α) (A : α → ℂ) (w : α → ℝ)
    (t : ℝ) : ℂ := ∑ i ∈ S, A i*Complex.exp (I*(t : ℂ)*(Real.log (w i) : ℂ))

theorem markedMajorEndpointPolynomial_product {α β : Type*} (S : Finset α) (T : Finset β)
    (A : α → ℂ) (B : β → ℂ) (w : α → ℝ) (w' : β → ℝ) (t s : ℝ) (F : ℂ) :
    F*(markedMajorEndpointPolynomial S A w t * markedMajorEndpointPolynomial T B w' (s-t)) =
      ∑ i ∈ S, ∑ j ∈ T, (A i*B j)*(F*(Complex.exp (I*(t : ℂ)*(Real.log (w i) : ℂ))*
        Complex.exp (I*((s-t : ℝ) : ℂ)*(Real.log (w' j) : ℂ)))) := by
  unfold markedMajorEndpointPolynomial
  rw [sum_mul_sum]
  simp_rw [mul_sum]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  ring

theorem markedMajor_mellin_endpoint_integrable {α β : Type*} (S : Finset α) (T : Finset β)
    (A : α → ℂ) (B : β → ℂ) (w : α → ℝ) (w' : β → ℝ)
    (hw : ∀ i ∈ S, 0 < w i) (hw' : ∀ j ∈ T, 0 < w' j)
    (g : SchwartzMap (ℝ × ℝ) ℂ) {X : ℝ} (hX : 0 < X) :
    Integrable (fun p : ℝ × ℝ => markedMajorFourierCoefficient g (p.1/X,p.2)*
      (markedMajorEndpointPolynomial S A w p.1 * markedMajorEndpointPolynomial T B w' (p.2-p.1))) := by
  simp_rw [markedMajorEndpointPolynomial_product]
  exact integrable_finsetSum S (fun i hi => integrable_finsetSum T (fun j hj =>
    (markedMajor_mellin_separated_exp_integrable g hX (hw i hi) (hw' j hj)).const_mul (A i*B j)))

theorem markedMajor_mellin_finite_endpoints {α β : Type*} (S : Finset α) (T : Finset β)
    (A : α → ℂ) (B : β → ℂ) (w : α → ℝ) (w' : β → ℝ)
    (hw : ∀ i ∈ S, 0 < w i) (hw' : ∀ j ∈ T, 0 < w' j)
    (g : SchwartzMap (ℝ × ℝ) ℂ) {X : ℝ} (hX : 0 < X) :
    (∑ i ∈ S, ∑ j ∈ T, (A i*B j)*g (X*(Real.log (w i)-Real.log (w' j)),Real.log (w' j))) =
      (X : ℂ)⁻¹ * ∫ p : ℝ × ℝ, markedMajorFourierCoefficient g (p.1/X,p.2)*
        (markedMajorEndpointPolynomial S A w p.1 * markedMajorEndpointPolynomial T B w' (p.2-p.1)) := by
  let H := fun i j (p : ℝ × ℝ) => (A i*B j)*(markedMajorFourierCoefficient g (p.1/X,p.2)*
    (Complex.exp (I*(p.1 : ℂ)*(Real.log (w i) : ℂ))*
      Complex.exp (I*((p.2-p.1 : ℝ) : ℂ)*(Real.log (w' j) : ℂ))))
  have hH : ∀ i ∈ S, ∀ j ∈ T, Integrable (H i j) := fun i hi j hj =>
    (markedMajor_mellin_separated_exp_integrable g hX (hw i hi) (hw' j hj)).const_mul (A i*B j)
  calc
    _ = ∑ i ∈ S, ∑ j ∈ T, (X : ℂ)⁻¹ * ∫ p : ℝ × ℝ, H i j p := by
      apply sum_congr rfl
      intro i hi
      apply sum_congr rfl
      intro j hj
      rw [markedMajor_mellin_separation_exp g hX (hw i hi) (hw' j hj)]
      rw [integral_integral (markedMajor_mellin_separated_exp_integrable g hX (hw i hi) (hw' j hj))]
      simp only [H,integral_const_mul,← Measure.volume_eq_prod]
      ring
    _ = (X : ℂ)⁻¹ * (∑ i ∈ S, ∑ j ∈ T, ∫ p : ℝ × ℝ, H i j p) := by simp only [mul_sum]
    _ = (X : ℂ)⁻¹ * ∫ p : ℝ × ℝ, ∑ i ∈ S, ∑ j ∈ T, H i j p := by
      congr 1
      rw [integral_finsetSum S (fun i hi => integrable_finsetSum T (fun j hj => hH i hi j hj))]
      apply sum_congr rfl
      intro i hi
      exact (integral_finsetSum T (fun j hj => hH i hi j hj)).symm
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards with p
      exact (markedMajorEndpointPolynomial_product S T A B w w' p.1 p.2 _).symm

theorem markedMajor_constructed_finite_endpoints {α β : Type*} (S : Finset α) (T : Finset β)
    (A : α → ℂ) (B : β → ℂ) (w : α → ℝ) (w' : β → ℝ)
    (ψ : SchwartzMap ℝ ℂ) {a b R X : ℝ} (ha : 0 < a) (hab : a < b)
    (hψ : tsupport ψ ⊆ Set.Icc (-R) R) (hX : 0 < X) (theta : ℝ)
    (hw : ∀ i ∈ S, w i ∈ Set.Icc a b) (hw' : ∀ j ∈ T, w' j ∈ Set.Icc a b) :
    (∑ i ∈ S, ∑ j ∈ T, (A i*B j)*(ψ (X*(w i-w' j))*
      OAI.Problem337.RealPhase.phase (theta*(X*(w i-w' j))))) =
      (X : ℂ)⁻¹ * ∫ p : ℝ × ℝ, markedMajorConstructedCoefficient ψ ha hab hψ hX theta (p.1/X,p.2)*
        (markedMajorEndpointPolynomial S A w p.1 * markedMajorEndpointPolynomial T B w' (p.2-p.1)) := by
  unfold markedMajorConstructedCoefficient
  rw [← markedMajor_mellin_finite_endpoints S T A B w w'
    (fun i hi => ha.trans_le (hw i hi).1) (fun j hj => ha.trans_le (hw' j hj).1)
    (markedMajorConstructedKernel ψ ha hab hψ hX theta) hX]
  apply sum_congr rfl
  intro i hi
  apply sum_congr rfl
  intro j hj
  congr 1
  exact (markedMajorMellinKernel_on_source _ _ ψ hX.ne'
    (ha.trans_le (hw i hi).1) (ha.trans_le (hw' j hj).1)
    (majorMellinPositiveCutoff_plateau a b ha hab (hw i hi))
    (majorMellinPositiveCutoff_plateau a b ha hab (hw' j hj)) theta).symm

end
end ArtinMatthews
