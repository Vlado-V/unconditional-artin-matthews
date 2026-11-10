module

public import OAI.NumberTheory.PrimePackets.AnalyticLogarithms
public import ArtinMatthews.VaryingKummerAnalyticGrowth
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Fourier.Notation
import Mathlib.Analysis.Matrix.Normed


set_option backward.privateInPublic true
@[expose] public section

/-! Generic zero-count and logarithmic-derivative estimates extracted from
OpenAI PrimePackets/MellinGrowth.lean. The mathematical proof bodies are unchanged;
the growth predicate is the separately checked generic ReusedGrowth definition. -/

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


lemma diskZeroCount_subquadratic {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (h0 : f 0 ≠ 0) (hg : HasSubquadraticGrowth f) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ R : ℝ in atTop, diskZeroCount f R ≤ ε*R^2 := by
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have HT : Tendsto (fun R : ℝ => 2*R) atTop atTop :=
    Tendsto.const_mul_atTop (by norm_num : (0:ℝ) < 2) tendsto_id
  have HB := HT.eventually (hg (ε*Real.log 2/8) (by positivity))
  have HC := (tendsto_const_mul_pow_atTop (by decide : (2:ℕ) ≠ 0)
    (by positivity : 0 < ε*Real.log 2/2)).eventually_ge_atTop (-Real.log ‖f 0‖)
  filter_upwards [HB, HC, eventually_gt_atTop (0:ℝ)] with R hB hC hR
  apply (diskZeroCount_le hf h0 hR (by positivity) hB).trans
  apply (div_le_iff₀ hL).mpr
  nlinarith

lemma diskZeroCount_div_sq_tendsto_zero {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (h0 : f 0 ≠ 0) (hg : HasSubquadraticGrowth f) :
    Tendsto (fun R : ℝ => diskZeroCount f R/R^2) atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    filter_upwards [] with R
    exact ha.trans_le (div_nonneg (diskZeroCount_nonneg hf R) (sq_nonneg R))
  · intro b hb
    filter_upwards [diskZeroCount_subquadratic hf h0 hg (half_pos hb),
      eventually_gt_atTop (0:ℝ)] with R hR hpos
    apply lt_of_le_of_lt ((div_le_iff₀ (sq_pos_of_pos hpos)).mpr hR)
    exact half_lt_self hb

end PrimeDegreePackets.AnalyticGrowth


namespace PrimeDegreePackets.AnalyticGrowth

lemma divisor_ball_eq_closedBall {f : ℂ → ℂ} {R : ℝ} (hf : Differentiable ℂ f)
    (hS : ∀ z ∈ sphere (0:ℂ) R, f z ≠ 0) :
    (divisor f (ball (0:ℂ) R) : ℂ → ℤ) = divisor f (closedBall (0:ℂ) R) := by
  ext z
  by_cases hz : z ∈ ball (0:ℂ) R
  · rw [MeromorphicOn.divisor_apply (fun z _ => (hf.analyticAt z).meromorphicAt) hz,
      MeromorphicOn.divisor_apply (fun z _ => (hf.analyticAt z).meromorphicAt)
        (ball_subset_closedBall hz)]
  · by_cases hzC : z ∈ closedBall (0:ℂ) R
    · have hzS : z ∈ sphere (0:ℂ) R := by
        rw [mem_sphere_zero_iff_norm]
        exact le_antisymm (mem_closedBall_zero_iff.mp hzC) (not_lt.mp (by simpa using hz))
      rw [MeromorphicOn.divisor_apply (fun z _ => (hf.analyticAt z).meromorphicAt) hzC,
        (hf.analyticAt z).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr (hS z hzS)]
      simp [hz]
    · simp [hz, hzC]

def zeroDiskFinset (f : ℂ → ℂ) (R : ℝ) : Finset ℂ :=
  ((divisor f (closedBall (0:ℂ) R)).finiteSupport (isCompact_closedBall 0 R)).toFinset

lemma mem_zeroDiskFinset (f : ℂ → ℂ) (R : ℝ) (z : ℂ) :
    z ∈ zeroDiskFinset f R ↔ divisor f (closedBall (0:ℂ) R) z ≠ 0 := by
  simp [zeroDiskFinset, Function.mem_support]

lemma zeroDiskFinset_norm_le {f : ℂ → ℂ} {R : ℝ} {z : ℂ}
    (hz : z ∈ zeroDiskFinset f R) : ‖z‖ ≤ R :=
  mem_closedBall_zero_iff.mp ((divisor f (closedBall (0:ℂ) R)).supportWithinDomain
    ((mem_zeroDiskFinset f R z).mp hz))

lemma divisor_closedBall_eq_multiplicity {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {R : ℝ} {z : ℂ} (hz : ‖z‖ ≤ R) :
    divisor f (closedBall (0:ℂ) R) z = zeroMultiplicity f z :=
  MeromorphicOn.divisor_apply (fun z _ => (hf.analyticAt z).meromorphicAt)
    (mem_closedBall_zero_iff.mpr hz)

lemma diskZeroCount_eq_sum {f : ℂ → ℂ} (hf : Differentiable ℂ f) (R : ℝ) :
    diskZeroCount f R = ∑ ρ ∈ zeroDiskFinset f R, (zeroMultiplicity f ρ : ℝ) := by
  classical
  rw [diskZeroCount_eq_finsum, finsum_eq_sum_of_support_subset (s := zeroDiskFinset f R) _ (by
    intro z hz
    apply (mem_zeroDiskFinset f R z).mpr
    intro H
    simp [H] at hz)]
  apply Finset.sum_congr rfl
  intro ρ hρ
  rw [divisor_closedBall_eq_multiplicity hf (zeroDiskFinset_norm_le hρ)]

def diskPoleSum (f : ℂ → ℂ) (R : ℝ) (z : ℂ) : ℂ :=
  ∑ ρ ∈ zeroDiskFinset f R, (zeroMultiplicity f ρ : ℂ) * (1/(z-ρ))

lemma ecanonical_logDeriv_finite {f g : ℂ → ℂ} {R : ℝ}
    (D : ECanonicalDecomp f g R) (hf : Differentiable ℂ f) (hR : 0 < R)
    (hS : ∀ z ∈ sphere (0:ℂ) R, f z ≠ 0) {z : ℂ}
    (hz : ‖z‖ ≤ R/2) (hfz : f z ≠ 0) :
    logDeriv f z = diskPoleSum f R z +
      (∑ ρ ∈ zeroDiskFinset f R, (zeroMultiplicity f ρ : ℂ)*canonicalCorrection R ρ z) +
      logDeriv g z := by
  classical
  rw [ecanonical_logDeriv D hf hR hS hz hfz, divisor_ball_eq_closedBall hf hS]
  rw [finsum_eq_sum_of_support_subset (s := zeroDiskFinset f R) _ (by
    intro ρ hρ
    apply (mem_zeroDiskFinset f R ρ).mpr
    intro H
    simp [H] at hρ)]
  congr 1
  simp only [diskPoleSum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ρ hρ
  rw [divisor_closedBall_eq_multiplicity hf (zeroDiskFinset_norm_le hρ), mul_add]

lemma correction_sum_sub_le {f : ℂ → ℂ} (hf : Differentiable ℂ f) {R : ℝ}
    (hR : 0 < R) {z w : ℂ} (hz : ‖z‖ ≤ R/2) (hw : ‖w‖ ≤ R/2) :
    ‖(∑ ρ ∈ zeroDiskFinset f R, (zeroMultiplicity f ρ : ℂ)*canonicalCorrection R ρ z) -
      (∑ ρ ∈ zeroDiskFinset f R, (zeroMultiplicity f ρ : ℂ)*canonicalCorrection R ρ w)‖ ≤
      (4*diskZeroCount f R/R^2)*‖z-w‖ := by
  classical
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ ρ ∈ zeroDiskFinset f R, ‖(zeroMultiplicity f ρ : ℂ)*
        canonicalCorrection R ρ z-(zeroMultiplicity f ρ : ℂ)*canonicalCorrection R ρ w‖ :=
      norm_sum_le _ _
    _ ≤ ∑ ρ ∈ zeroDiskFinset f R, (zeroMultiplicity f ρ : ℝ)*(4/R^2*‖z-w‖) := by
      apply Finset.sum_le_sum
      intro ρ hρ
      rw [← mul_sub, norm_mul, Complex.norm_intCast,
        abs_of_nonneg (show (0:ℝ) ≤ zeroMultiplicity f ρ by exact_mod_cast zeroMultiplicity_nonneg hf ρ)]
      exact mul_le_mul_of_nonneg_left
        (norm_canonicalCorrection_sub_le hR (zeroDiskFinset_norm_le hρ) hz hw)
        (by exact_mod_cast zeroMultiplicity_nonneg hf ρ)
    _ = _ := by rw [← Finset.sum_mul, ← diskZeroCount_eq_sum hf]; ring

lemma diskPoleSum_error_le {f : ℂ → ℂ} (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0)
    {R B : ℝ} (hR : 0 < R) (hS : ∀ z ∈ sphere (0:ℂ) R, f z ≠ 0)
    (hbound : ∀ z ∈ sphere (0:ℂ) R, ‖f z‖ ≤ Real.exp B)
    (hB : Real.log ‖f 0‖ < B) {z w : ℂ}
    (hz : ‖z‖ < R/4) (hw : ‖w‖ < R/4) (hfz : f z ≠ 0) (hfw : f w ≠ 0) :
    ‖(logDeriv f z-logDeriv f w)-(diskPoleSum f R z-diskPoleSum f R w)‖ ≤
      ((64*(B-Real.log ‖f 0‖)+4*diskZeroCount f R)/R^2)*‖z-w‖ := by
  obtain ⟨g,D⟩ := exists_entire_ecanonicalDecomp (R := R) hf h0
  have hz' : ‖z‖ ≤ R/2 := by linarith
  have hw' : ‖w‖ ≤ R/2 := by linarith
  have HE : (logDeriv f z-logDeriv f w)-(diskPoleSum f R z-diskPoleSum f R w) =
      ((∑ ρ ∈ zeroDiskFinset f R, (zeroMultiplicity f ρ : ℂ)*canonicalCorrection R ρ z) -
       (∑ ρ ∈ zeroDiskFinset f R, (zeroMultiplicity f ρ : ℂ)*canonicalCorrection R ρ w)) +
      (logDeriv g z-logDeriv g w) := by
    rw [ecanonical_logDeriv_finite D hf hR hS hz' hfz,
      ecanonical_logDeriv_finite D hf hR hS hw' hfw]
    ring
  rw [HE]
  apply (norm_add_le _ _).trans
  have Hg := logDeriv_sub_le_of_log_norm_le hR (sub_pos.mpr hB)
    (D.analyticOnNhd.differentiableOn.mono ball_subset_closedBall)
    (fun z hz => D.ne_zero z (ball_subset_closedBall hz))
    (fun z hz => sub_le_sub (ecanonical_log_norm_le D hf hR hS hbound (ball_subset_closedBall hz))
      (ecanonical_log_norm_zero_ge D hf hR hS h0))
    (mem_ball_zero_iff.mpr hz) (mem_ball_zero_iff.mpr hw)
  have HC := correction_sum_sub_le hf hR hz' hw'
  calc
    _ ≤ (4*diskZeroCount f R/R^2)*‖z-w‖ +
      (64*(B-Real.log ‖f 0‖)/R^2)*‖z-w‖ := add_le_add HC Hg
    _ = _ := by ring

end PrimeDegreePackets.AnalyticGrowth


namespace PrimeDegreePackets.AnalyticGrowth

 

lemma tendsto_diskPoleSum_sub {f : ℂ → ℂ} (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0)
    (hg : HasSubquadraticGrowth f) {ι : Type*} {l : Filter ι} {r : ι → ℝ}
    (hr : Tendsto r l atTop) (hS : ∀ᶠ i in l, ∀ z ∈ sphere (0:ℂ) (r i), f z ≠ 0)
    {z w : ℂ} (hfz : f z ≠ 0) (hfw : f w ≠ 0) :
    Tendsto (fun i => diskPoleSum f (r i) z-diskPoleSum f (r i) w) l
      (𝓝 (logDeriv f z-logDeriv f w)) := by
  apply Metric.tendsto_nhds.2
  intro ε hε
  let η := ε/(200*(‖z-w‖+1))
  have hη : 0 < η := by dsimp [η]; positivity
  have HP := (tendsto_const_mul_pow_atTop (by decide : (2:ℕ) ≠ 0) hη).eventually_ge_atTop
    (|Real.log ‖f 0‖|+1-Real.log ‖f 0‖)
  filter_upwards [hr.eventually (hg η hη), hr.eventually (diskZeroCount_subquadratic hf h0 hg hη),
    hr.eventually HP, hr.eventually (eventually_gt_atTop (4*(‖z‖+‖w‖+1))), hS]
    with i hG hN hP hR hS'
  have hR0 : 0 < r i := by linarith [norm_nonneg z, norm_nonneg w]
  have hz : ‖z‖ < r i/4 := by linarith [norm_nonneg w]
  have hw : ‖w‖ < r i/4 := by linarith [norm_nonneg z]
  have HB : Real.log ‖f 0‖ < η*(r i)^2+|Real.log ‖f 0‖|+1 := by
    nlinarith [le_abs_self (Real.log ‖f 0‖), sq_nonneg (r i)]
  have H := diskPoleSum_error_le hf h0 hR0 hS' (B := η*(r i)^2+|Real.log ‖f 0‖|+1)
    (fun a ha => (hG a (le_of_eq (mem_sphere_zero_iff_norm.mp ha))).trans
      (Real.exp_le_exp.mpr (by linarith [abs_nonneg (Real.log ‖f 0‖)]))) HB hz hw hfz hfw
  rw [dist_eq_norm']
  apply H.trans_lt
  have HE : (64*(η*(r i)^2+|Real.log ‖f 0‖|+1-Real.log ‖f 0‖)+4*diskZeroCount f (r i))/(r i)^2
      ≤ 132*η := by
    apply (div_le_iff₀ (sq_pos_of_pos hR0)).mpr
    nlinarith
  calc
    _ ≤ (132*η)*‖z-w‖ := mul_le_mul_of_nonneg_right HE (norm_nonneg _)
    _ < ε := by
      dsimp [η]
      have Hden : 0 < 200*(‖z-w‖+1) := by positivity
      rw [show 132*(ε/(200*(‖z-w‖+1)))*‖z-w‖ =
        ε*(132*‖z-w‖)/(200*(‖z-w‖+1)) by ring]
      apply (div_lt_iff₀ Hden).mpr
      nlinarith [norm_nonneg (z-w)]

 

lemma exists_good_radii {f : ℂ → ℂ} (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0) :
    ∃ r : ℕ → ℝ, Tendsto r atTop atTop ∧
      (∀ j : ℕ, (j:ℝ)+1 < r j ∧ r j < j+2) ∧
      ∀ j z, z ∈ sphere (0:ℂ) (r j) → f z ≠ 0 := by
  choose r hR hS using fun j : ℕ => exists_zero_free_sphere hf h0
    (show (j:ℝ)+1 < j+2 by linarith)
  refine ⟨r,?_,hR,hS⟩
  apply tendsto_atTop_mono (fun j => (hR j).1.le)
  exact tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop

end PrimeDegreePackets.AnalyticGrowth
end
end
end OAI
