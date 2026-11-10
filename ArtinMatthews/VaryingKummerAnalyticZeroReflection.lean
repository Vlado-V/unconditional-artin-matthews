module

public import ArtinMatthews.VaryingKummerAnalyticZeroGrowth
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
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
public import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Fourier.Notation
import Mathlib.Analysis.Matrix.Normed


set_option backward.privateInPublic true
@[expose] public section

/-! Generic functional-equation symmetry and nonnegative pole-sum identity,
extracted from OpenAI PrimePackets/ZeroReflection.lean. -/
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

lemma zeroMultiplicity_reflection {f : ℂ → ℂ} (hfe : ∀ z, f (1-z) = f z) (z : ℂ) :
    zeroMultiplicity f (1-z) = zeroMultiplicity f z := by
  have Hg : HasDerivAt (fun z : ℂ => 1-z) (-1) z := by
    apply ((hasDerivAt_id z).const_sub 1).congr_deriv
    simp
  have H := meromorphicOrderAt_comp_of_deriv_ne_zero (f := f)
    (g := fun z : ℂ => 1-z) (x := z) (analyticAt_const.sub analyticAt_id) (by rw [Hg.deriv]; norm_num)
  have HE : f ∘ (fun z : ℂ => 1-z) = f := funext hfe
  rw [HE] at H
  exact congrArg WithTop.untop₀ H.symm

lemma logDeriv_reflection {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hfe : ∀ z, f (1-z) = f z) (z : ℂ) : logDeriv f (1-z) = -logDeriv f z := by
  have Hg : HasDerivAt (fun z : ℂ => 1-z) (-1) z := by
    apply ((hasDerivAt_id z).const_sub 1).congr_deriv
    simp
  have H := ((hf (1-z)).hasDerivAt.comp z Hg)
  have HE : (fun z : ℂ => f (1-z)) = f := funext hfe
  simp only [Function.comp_def] at H
  rw [HE] at H
  have HD := H.deriv
  rw [logDeriv_apply, logDeriv_apply, hfe]
  have HD' : deriv f (1-z) = -deriv f z := by linear_combination HD
  rw [HD', neg_div]

 

lemma hasSum_of_nonneg_finite_exhaustion {α ι : Type*} {l : Filter ι} [NeBot l]
    {a : α → ℝ} (ha : ∀ x, 0 ≤ a x) (t : ι → Finset α)
    (ht : ∀ x, a x ≠ 0 → ∀ᶠ i in l, x ∈ t i) {A : ℝ}
    (hA : Tendsto (fun i => ∑ x ∈ t i, a x) l (𝓝 A)) : HasSum a A := by
  classical
  have HB : ∀ s : Finset α, ∑ x ∈ s, a x ≤ A := by
    intro s
    have H : ∀ᶠ i in l, ∀ x ∈ s, a x ≠ 0 → x ∈ t i := by
      rw [Filter.eventually_all_finset]
      intro x hx
      by_cases hx0 : a x = 0
      · exact Filter.Eventually.of_forall (by simp [hx0])
      · exact (ht x hx0).mono (fun i hi _ => hi)
    apply ge_of_tendsto hA
    filter_upwards [H] with i hi
    calc
      _ = ∑ x ∈ s.filter (fun x => a x ≠ 0), a x := by
        symm
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro x hx hn
        by_contra h
        exact hn (Finset.mem_filter.mpr ⟨hx,h⟩)
      _ ≤ ∑ x ∈ t i, a x := Finset.sum_le_sum_of_subset_of_nonneg
        (fun x hx => hi x (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hx).2)
        (fun x _ _ => ha x)
  have HS := summable_of_sum_le ha HB
  have HE : ∑' x, a x = A := le_antisymm (HS.tsum_le_of_sum_le HB)
    (le_of_tendsto hA (Filter.Eventually.of_forall (fun i => HS.sum_le_tsum (t i) (fun x _ => ha x))))
  exact HE ▸ HS.hasSum

end PrimeDegreePackets.AnalyticGrowth


namespace PrimeDegreePackets.AnalyticGrowth

 
def realZeroPole (f : ℂ → ℂ) (σ : ℝ) (ρ : ℂ) : ℝ :=
  (zeroMultiplicity f ρ : ℝ)*(1/((σ:ℂ)-ρ)).re

lemma realZeroPole_nonneg {f : ℂ → ℂ} (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0)
    (hstrip : ∀ ρ, f ρ = 0 → ρ.re ≤ 1) {σ : ℝ} (hσ : 1 < σ) (ρ : ℂ) :
    0 ≤ realZeroPole f σ ρ := by
  by_cases hm : zeroMultiplicity f ρ = 0
  · simp [realZeroPole, hm]
  have hρ := hstrip ρ ((zeroMultiplicity_ne_zero_iff hf h0 ρ).mp hm)
  unfold realZeroPole
  apply mul_nonneg (by exact_mod_cast zeroMultiplicity_nonneg hf ρ)
  simp only [one_div, Complex.inv_re, Complex.sub_re, Complex.ofReal_re]
  exact div_nonneg (by linarith) (Complex.normSq_nonneg _)

lemma realZeroPole_pair {f : ℂ → ℂ} (hfe : ∀ z, f (1-z) = f z)
    (σ : ℝ) (ρ : ℂ) :
    realZeroPole f σ ρ + realZeroPole f σ (1-ρ) =
      ((zeroMultiplicity f ρ : ℂ)*(1/((σ:ℂ)-ρ)-1/((1-(σ:ℂ))-ρ))).re := by
  have HE : (σ:ℂ)-(1-ρ) = -((1-(σ:ℂ))-ρ) := by ring
  simp only [realZeroPole, zeroMultiplicity_reflection hfe, HE, one_div, inv_neg,
    Complex.neg_re, Complex.mul_re, Complex.intCast_re, Complex.intCast_im,
    zero_mul, sub_zero, Complex.sub_re]
  ring

lemma diskPoleSum_sub_re {f : ℂ → ℂ} (hfe : ∀ z, f (1-z) = f z)
    (σ R : ℝ) :
    (diskPoleSum f R σ-diskPoleSum f R (1-(σ:ℂ))).re =
      ∑ ρ ∈ zeroDiskFinset f R, (realZeroPole f σ ρ+realZeroPole f σ (1-ρ)) := by
  classical
  simp only [diskPoleSum, ← Finset.sum_sub_distrib, ← mul_sub,
    realZeroPole_pair hfe]
  exact map_sum Complex.reAddGroupHom _ _

 

theorem hasSum_realZeroPole {f : ℂ → ℂ} (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0)
    (hg : HasSubquadraticGrowth f) (hfe : ∀ z, f (1-z) = f z)
    (hstrip : ∀ ρ, f ρ = 0 → ρ.re ≤ 1) {σ : ℝ} (hσ : 1 < σ) :
    HasSum (realZeroPole f σ) (logDeriv f σ).re := by
  classical
  have hσ0 : f (σ:ℂ) ≠ 0 := by
    intro h
    have HH := hstrip σ h
    simp only [Complex.ofReal_re] at HH
    linarith
  have hσ1 : f (1-(σ:ℂ)) ≠ 0 := by rwa [hfe]
  obtain ⟨r,hr,_,hS⟩ := exists_good_radii hf h0
  have HT := (Complex.continuous_re.tendsto _).comp (tendsto_diskPoleSum_sub hf h0 hg hr
    (Filter.Eventually.of_forall hS) hσ0 hσ1)
  have HT' : Tendsto (fun j => ∑ ρ ∈ zeroDiskFinset f (r j),
      (realZeroPole f σ ρ+realZeroPole f σ (1-ρ))) atTop (𝓝 (2*(logDeriv f σ).re)) := by
    simpa only [Function.comp_def, diskPoleSum_sub_re hfe,
      logDeriv_reflection hf hfe, Complex.sub_re, Complex.neg_re, sub_neg_eq_add, two_mul, Complex.add_re] using HT
  have HNN := realZeroPole_nonneg hf h0 hstrip hσ
  have Hsum : HasSum (fun ρ => realZeroPole f σ ρ+realZeroPole f σ (1-ρ))
      (2*(logDeriv f σ).re) := by
    apply hasSum_of_nonneg_finite_exhaustion (fun ρ => add_nonneg (HNN ρ) (HNN (1-ρ)))
      (fun j => zeroDiskFinset f (r j)) _ HT'
    intro ρ hρ
    have Hm : zeroMultiplicity f ρ ≠ 0 := by
      intro H
      apply hρ
      simp [realZeroPole, zeroMultiplicity_reflection hfe, H]
    filter_upwards [hr.eventually_ge_atTop ‖ρ‖] with j hj
    rw [mem_zeroDiskFinset, divisor_closedBall_eq_multiplicity hf hj]
    exact Hm
  have HS : Summable (realZeroPole f σ) := Hsum.summable.of_nonneg_of_le HNN
    (fun ρ => le_add_of_nonneg_right (HNN (1-ρ)))
  let e : ℂ ≃ ℂ := ⟨fun ρ => 1-ρ, fun ρ => 1-ρ, by intro ρ; ring, by intro ρ; ring⟩
  have HS' : Summable (fun ρ => realZeroPole f σ (1-ρ)) := e.summable_iff.mpr HS
  have HE : (∑' ρ, realZeroPole f σ (1-ρ)) = ∑' ρ, realZeroPole f σ ρ :=
    e.tsum_eq (realZeroPole f σ)
  have HH := Hsum.tsum_eq
  rw [HS.tsum_add HS', HE] at HH
  have HA : (∑' ρ, realZeroPole f σ ρ) = (logDeriv f σ).re := by linarith
  exact HA ▸ HS.hasSum

end PrimeDegreePackets.AnalyticGrowth


end
end
end OAI
