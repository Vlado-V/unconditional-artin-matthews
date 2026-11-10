module

public import ArtinMatthews.VaryingKummerAnalyticGrowth
public import OAI.NumberTheory.PrimePackets.AnalyticLogarithms
public import ArtinMatthews.VaryingKummerAnalyticZeroReflection
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

/-! Generic near-one zero multiplicity and uniqueness bounds, extracted from
OpenAI PrimePackets/SubquadraticGrowth.lean. -/
namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical ArithmeticFunction.Moebius
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
open Filter Set Topology
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix
open MeasureTheory Filter Set Module TopologicalSpace
open MeasureTheory Filter Set
open scoped BigOperators Topology ENNReal
open scoped BigOperators Topology ENNReal Classical
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix
open MeasureTheory ProbabilityTheory Filter Set
open Set Filter
open scoped Topology
open scoped Classical
open scoped Topology ENNReal Classical
open scoped ENNReal Classical
open MeasureTheory Set Topology UniformSpace TopologicalSpace
open scoped ENNReal Topology
open MeasureTheory Filter Set Matrix
open scoped Topology Classical
open scoped Matrix Classical
open scoped Topology Classical Matrix
open scoped Classical Pointwise
open scoped Topology Classical ENNReal
open scoped Matrix Topology Classical
open MeasureTheory ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal ProbabilityTheory
open scoped ENNReal ProbabilityTheory
open Set Filter Topology
open Set Filter Topology MeasureTheory
open MeasureTheory Set Filter Topology
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Matrix ENNReal NNReal ProbabilityTheory
open MeasureTheory
open scoped BigOperators ENNReal
open NumberField Finset
open NumberField Filter Set Topology
open MeasureTheory ProbabilityTheory Matrix
open scoped Classical BigOperators ENNReal
open MeasureTheory Set Filter Topology Module
open scoped BigOperators SchwartzMap
open MeasureTheory Set Filter Topology Module WithLp
open scoped BigOperators SchwartzMap ZeroAtInfty
open scoped FourierTransform
open scoped BigOperators SchwartzMap FourierTransform
open scoped BigOperators FourierTransform
open MeasureTheory Set Filter Topology Module WithLp Asymptotics
open Module WithLp MeasureTheory
open scoped BigOperators Matrix
open Module MeasureTheory
open MeasureTheory Module WithLp
open scoped BigOperators NumberField nonZeroDivisors ENNReal
open Complex Set Metric Filter
open Complex Set Metric Filter MeromorphicOn
open scoped Topology ComplexConjugate
open MeasureTheory Set Filter
open ArtinMatthews.ReusedGrowth
namespace PrimeDegreePackets.AnalyticGrowth

lemma near_one_kernel_lower {a b : ℝ} (ha : 1 ≤ a) (ha' : a ≤ 5/4)
    (hb : |b| ≤ 1/4) : (10/13:ℝ) ≤ a/(a^2+b^2) := by
  have hb' := abs_le.mp hb
  have hbs : b^2 ≤ 1/16 := by nlinarith
  have hd : 0 < a^2+b^2 := by nlinarith [sq_nonneg b]
  apply (le_div_iff₀ hd).mpr
  have Hp : 0 ≤ (5/4-a)*(10*a-1/2) := mul_nonneg (by linarith) (by linarith)
  nlinarith

lemma real_inverse_pole_scaled {L h : ℝ} (hL : L ≠ 0) (ρ : ℂ) :
    (1/(((1+h:ℝ):ℂ)-ρ)).re =
      L*((L*(1-ρ.re)+L*h)/((L*(1-ρ.re)+L*h)^2+(L*ρ.im)^2)) := by
  simp only [one_div, Complex.inv_re, Complex.sub_re, Complex.ofReal_re,
    Complex.normSq_apply, Complex.sub_im, Complex.ofReal_im, zero_sub]
  have HE : L*(1-ρ.re)+L*h = L*(1+h-ρ.re) := by ring
  rw [HE]
  simp only [mul_pow, neg_mul_neg]
  rw [← mul_add, ← mul_div_assoc, ← mul_assoc, ← pow_two]
  rw [show L*L = L^2 by ring]
  rw [mul_div_mul_left _ _ (pow_ne_zero 2 hL)]
  congr 1; ring

 

lemma near_one_complex_pole_lower {L : ℝ} (hL : 0 < L) {ρ : ℂ}
    (hβ : ρ.re ≤ 1) (hβ' : 1-1/(4*L) ≤ ρ.re) (hγ : |ρ.im| ≤ 1/(4*L)) :
    (10/13)*L ≤ (1/(((1+1/L:ℝ):ℂ)-ρ)).re := by
  have hX : 0 ≤ L*(1-ρ.re) := mul_nonneg hL.le (by linarith)
  have hX' : L*(1-ρ.re) ≤ 1/4 := by
    have H := mul_le_mul_of_nonneg_left (show 1-ρ.re ≤ 1/(4*L) by linarith) hL.le
    have HE : L*(1/(4*L)) = (1/4:ℝ) := by field_simp
    rwa [HE] at H
  have hY : |L*ρ.im| ≤ 1/4 := by
    rw [abs_mul, abs_of_pos hL]
    have H := mul_le_mul_of_nonneg_left hγ hL.le
    have HE : L*(1/(4*L)) = (1/4:ℝ) := by field_simp
    rwa [HE] at H
  have H := near_one_kernel_lower (a := L*(1-ρ.re)+1) (by linarith) (by linarith) hY
  rw [real_inverse_pole_scaled hL.ne', mul_one_div_cancel hL.ne']
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left H hL.le

end PrimeDegreePackets.AnalyticGrowth

open Complex Set Filter
namespace PrimeDegreePackets.AnalyticGrowth

 

def InNearOneBox (L : ℝ) (ρ : ℂ) : Prop :=
  1-1/(4*L) ≤ ρ.re ∧ |ρ.im| ≤ 1/(4*L)

lemma nearOneBox_multiplicity_sum_le_one {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0) (hg : HasSubquadraticGrowth f)
    (hfe : ∀ z, f (1-z) = f z) (hstrip : ∀ ρ, f ρ = 0 → ρ.re ≤ 1)
    {L A : ℝ} (hL : 0 < L) (hA : 26*A < L)
    (hbound : (logDeriv f (((1+1/L:ℝ)):ℂ)).re ≤ (3/2)*L+A)
    (t : Finset ℂ) (ht : ∀ ρ ∈ t, f ρ = 0 ∧ InNearOneBox L ρ) :
    ∑ ρ ∈ t, zeroMultiplicity f ρ ≤ 1 := by
  have hs : 1 < 1+1/L := by have H := one_div_pos.mpr hL; linarith
  have HS := hasSum_realZeroPole hf h0 hg hfe hstrip hs
  have Hlower : (10/13)*L*(∑ ρ ∈ t, (zeroMultiplicity f ρ : ℝ)) ≤
      ∑ ρ ∈ t, realZeroPole f (1+1/L) ρ := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro ρ hρ
    have H := near_one_complex_pole_lower hL (hstrip ρ (ht ρ hρ).1)
      (ht ρ hρ).2.1 (ht ρ hρ).2.2
    simpa only [realZeroPole, mul_comm] using mul_le_mul_of_nonneg_left H
      (show (0:ℝ) ≤ zeroMultiplicity f ρ by exact_mod_cast zeroMultiplicity_nonneg hf ρ)
  have Hupper := (HS.summable.sum_le_tsum t
    (fun ρ _ => realZeroPole_nonneg hf h0 hstrip hs ρ)).trans_eq HS.tsum_eq
  have Htotal := Hlower.trans (Hupper.trans hbound)
  by_contra h
  have Htwo : (2:ℤ) ≤ ∑ ρ ∈ t, zeroMultiplicity f ρ := by omega
  have Htwo' : (2:ℝ) ≤ ∑ ρ ∈ t, (zeroMultiplicity f ρ : ℝ) := by exact_mod_cast Htwo
  have HH := mul_le_mul_of_nonneg_left Htwo' (show 0 ≤ (10/13)*L by positivity)
  nlinarith

 

theorem nearOneBox_real_simple_unique {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0) (hg : HasSubquadraticGrowth f)
    (hfe : ∀ z, f (1-z) = f z) (hconj : ∀ z, f (conj z) = conj (f z))
    (hstrip : ∀ ρ, f ρ = 0 → ρ.re ≤ 1)
    {L A : ℝ} (hL : 0 < L) (hA : 26*A < L)
    (hbound : (logDeriv f (((1+1/L:ℝ)):ℂ)).re ≤ (3/2)*L+A)
    {ρ : ℂ} (hρ : f ρ = 0) (hbox : InNearOneBox L ρ) :
    zeroMultiplicity f ρ = 1 ∧ ρ.im = 0 ∧
      ∀ τ, f τ = 0 → InNearOneBox L τ → τ = ρ := by
  classical
  have HP {τ : ℂ} (hτ : f τ = 0) : 1 ≤ zeroMultiplicity f τ := by
    have H := zeroMultiplicity_nonneg hf τ
    have H' := (zeroMultiplicity_ne_zero_iff hf h0 τ).mpr hτ
    omega
  have Huniq : ∀ τ, f τ = 0 → InNearOneBox L τ → τ = ρ := by
    intro τ hτ hτbox
    by_contra hne
    have H := nearOneBox_multiplicity_sum_le_one hf h0 hg hfe hstrip hL hA hbound
      {τ,ρ} (by
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl
        · exact ⟨hτ,hτbox⟩
        · exact ⟨hρ,hbox⟩)
    simp only [Finset.sum_pair hne] at H
    have Hτ := HP hτ
    have Hρ := HP hρ
    omega
  have Hsimple := nearOneBox_multiplicity_sum_le_one hf h0 hg hfe hstrip hL hA hbound
    {ρ} (by intro z hz; have H := Finset.mem_singleton.mp hz; subst z; exact ⟨hρ,hbox⟩)
  have HS : zeroMultiplicity f ρ = 1 := by
    simp only [Finset.sum_singleton] at Hsimple
    exact le_antisymm Hsimple (HP hρ)
  have Hc := Huniq (conj ρ) (by rw [hconj, hρ]; simp) (by
    simpa only [InNearOneBox, Complex.conj_re, Complex.conj_im, abs_neg] using hbox)
  have HI := congrArg Complex.im Hc
  simp only [Complex.conj_im] at HI
  exact ⟨HS, by linarith, Huniq⟩

end PrimeDegreePackets.AnalyticGrowth
end
end
end OAI
