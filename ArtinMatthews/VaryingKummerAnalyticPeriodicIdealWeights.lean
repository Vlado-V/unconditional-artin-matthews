module

public import ArtinMatthews.VaryingKummerAnalyticPeriodicTheta
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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
public import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.Topology.Separation.CompletelyRegular
public import Mathlib.Topology.Sheaves.Init
import Mathlib.Analysis.Matrix.Normed


set_option backward.privateInPublic true
@[expose] public section

/-! Exact generic proof extraction from OpenAI PrimePackets/IntegerEmbeddings.lean.
Only namespace/import routing changes; no signature hypotheses. -/
namespace ArtinMatthews.ReusedTheta
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
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
open scoped BigOperators Classical
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
open WithLp Asymptotics


variable {d R : Type*} [Fintype d] [CommRing R]
local instance integerEmbeddingsDecidableEq : DecidableEq d := Classical.decEq d

def moduleResidueEquiv {M : Type*} [AddCommGroup M] (b : Basis d ℤ M)
    (N : ℕ) [NeZero N] : (d → Fin N) ≃ ModN M N :=
  (Equiv.piCongrRight fun _ : d => (ZMod.finEquiv N).toEquiv).trans
    (ModN.basis b).equivFun.symm.toEquiv

lemma rationalModulus_nsmul (N : ℕ) (x : R ⧸ rationalModulusIdeal R N) :
    N • x = 0 := by
  obtain ⟨x,rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [← map_nsmul,Ideal.Quotient.eq_zero_iff_mem]
  change N • x ∈ Ideal.span {(N:R)}
  rw [nsmul_eq_mul,Ideal.mem_span_singleton]
  exact dvd_mul_right _ _

def idealModNReduction (I : Ideal R) (N : ℕ) :
    ModN I N →+ R ⧸ rationalModulusIdeal R N :=
  ModN.liftEquiv.symm ⟨(Ideal.Quotient.mk (rationalModulusIdeal R N)).toAddMonoidHom.comp
    I.subtype.toAddMonoidHom, fun _ => rationalModulus_nsmul N _⟩

lemma idealModNReduction_mk (I : Ideal R) (N : ℕ) (x : I) :
    idealModNReduction I N (ModN.mkQ N x) =
      Ideal.Quotient.mk (rationalModulusIdeal R N) x := rfl

lemma idealModNReduction_surjective (I : Ideal R) (N : ℕ)
    (hI : IsCoprime I (rationalModulusIdeal R N)) :
    Function.Surjective (idealModNReduction I N) := by
  obtain ⟨a,ha,b,hb,hab⟩ := Ideal.isCoprime_iff_exists.mp hI
  intro y
  obtain ⟨y,rfl⟩ := Ideal.Quotient.mk_surjective y
  refine ⟨ModN.mkQ N ⟨a*y,I.mul_mem_right y ha⟩, ?_⟩
  rw [idealModNReduction_mk,map_mul]
  have Ha : Ideal.Quotient.mk (rationalModulusIdeal R N) a = 1 := by
    have H := congrArg (Ideal.Quotient.mk (rationalModulusIdeal R N)) hab
    rw [map_add,Ideal.Quotient.eq_zero_iff_mem.mpr hb,add_zero,map_one] at H
    exact H
  rw [Ha,one_mul]

lemma idealModNReduction_bijective (I : Ideal R) (bI : Basis d ℤ I) (bR : Basis d ℤ R)
    (N : ℕ) [NeZero N] (hI : IsCoprime I (rationalModulusIdeal R N)) :
    Function.Bijective (idealModNReduction I N) := by
  let : Fintype (ModN I N) := Fintype.ofEquiv (d → Fin N) (moduleResidueEquiv bI N)
  let : Fintype (R ⧸ rationalModulusIdeal R N) :=
    Fintype.ofEquiv (d → Fin N) (integralResidueEquiv bR N)
  apply (Fintype.bijective_iff_surjective_and_card _).mpr
  refine ⟨idealModNReduction_surjective I N hI,?_⟩
  exact (Fintype.card_congr (moduleResidueEquiv bI N)).symm.trans
    (Fintype.card_congr (integralResidueEquiv bR N))

def idealResidueEquiv (I : Ideal R) (bI : Basis d ℤ I) (bR : Basis d ℤ R)
    (N : ℕ) [NeZero N] (hI : IsCoprime I (rationalModulusIdeal R N)) :
    (d → Fin N) ≃ R ⧸ rationalModulusIdeal R N :=
  (moduleResidueEquiv bI N).trans (Equiv.ofBijective (idealModNReduction I N)
    (idealModNReduction_bijective I bI bR N hI))

def idealCharacterWeight (I : Ideal R) (bI : Basis d ℤ I) (N : ℕ) [NeZero N]
    (χ : MulChar (R ⧸ rationalModulusIdeal R N) ℂ) : (d → Fin N) → ℂ :=
  fun r => χ (idealModNReduction I N (moduleResidueEquiv bI N r))

lemma idealCharacterWeight_sum_zero (I : Ideal R) (bI : Basis d ℤ I) (bR : Basis d ℤ R)
    (N : ℕ) [NeZero N] (hI : IsCoprime I (rationalModulusIdeal R N))
    (χ : MulChar (R ⧸ rationalModulusIdeal R N) ℂ) (hχ : χ ≠ 1) :
    ∑ r, idealCharacterWeight I bI N χ r = 0 := by
  let : Fintype (R ⧸ rationalModulusIdeal R N) :=
    Fintype.ofEquiv (d → Fin N) (integralResidueEquiv bR N)
  change (∑ r, χ (idealResidueEquiv I bI bR N hI r)) = 0
  rw [(idealResidueEquiv I bI bR N hI).sum_comp]
  exact MulChar.sum_eq_zero_of_ne_one hχ

lemma moduleResidueEquiv_zero {M : Type*} [AddCommGroup M] (b : Basis d ℤ M)
    (N : ℕ) [NeZero N] : moduleResidueEquiv b N (0 : d → Fin N) = 0 := by
  have h : (Equiv.piCongrRight fun _ : d => (ZMod.finEquiv N).toEquiv)
      (0 : d → Fin N) = (0 : d → ZMod N) := by
    funext i
    exact (ZMod.finEquiv N).map_zero
  simp only [moduleResidueEquiv,Equiv.trans_apply,h,LinearEquiv.coe_toEquiv,_root_.map_zero]

lemma idealCharacterWeight_zero (I : Ideal R) (bI : Basis d ℤ I) (N : ℕ) [NeZero N]
    (χ : MulChar (R ⧸ rationalModulusIdeal R N) ℂ) (hχ : χ ≠ 1) :
    periodicPrimalWeight N (idealCharacterWeight I bI N χ) 0 = 0 := by
  have : Nontrivial (R ⧸ rationalModulusIdeal R N) := mulChar_nontrivial_domain χ hχ
  simp only [periodicPrimalWeight,integerCongruenceEquiv_zero,idealCharacterWeight,
    moduleResidueEquiv_zero,_root_.map_zero,MulChar.map_zero]





variable {d : Type*} [Fintype d]

 

theorem thetaRemainder_uniform_positive_scale_bound (R : ℝ) (hR : 0 ≤ R)
    (k : ℝ) (hk : 0 < k) :
    ∃ a C : ℝ, 0 < a ∧ 0 ≤ C ∧
      ∀ (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d),
        ‖B.symm.toContinuousLinearMap‖ ≤ R → ∀ t : ℝ, k ≤ t →
          ‖thetaRemainder B t‖ ≤ C * Real.exp (-a*t) := by
  let c : ℝ := (R+1)⁻¹
  have hc : 0 < c := inv_pos.mpr (by linarith)
  let a : ℝ := c^2/2
  have ha : 0 < a := by dsimp [a]; positivity
  let v := fun z : NonzeroIntegerVector d => Real.exp (-(a*k)*‖euclideanInteger z.1‖^2)
  have hv : Summable v := by
    have H := (thetaRemainder_summable (ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ d)) (mul_pos ha hk)).norm
    simpa only [ContinuousLinearEquiv.refl_apply,gaussianTerm_norm] using H
  refine ⟨a,∑' z, v z,ha,tsum_nonneg (fun z => (Real.exp_pos _).le),fun B hB t ht => ?_⟩
  have hbound (z : NonzeroIntegerVector d) : c*‖euclideanInteger z.1‖ ≤ ‖B (euclideanInteger z.1)‖ := by
    have H := B.symm.toContinuousLinearMap.le_opNorm (B (euclideanInteger z.1))
    simp only [ContinuousLinearEquiv.coe_coe,ContinuousLinearEquiv.symm_apply_apply] at H
    have HR : 0 < R+1 := by linarith
    rw [show c*‖euclideanInteger z.1‖ = ‖euclideanInteger z.1‖/(R+1) by dsimp [c]; ring,
      div_le_iff₀ HR]
    calc
      ‖euclideanInteger z.1‖ ≤ ‖B.symm.toContinuousLinearMap‖ * ‖B (euclideanInteger z.1)‖ := H
      _ ≤ ‖B (euclideanInteger z.1)‖*(R+1) := by nlinarith [norm_nonneg (B (euclideanInteger z.1))]
  have ht' : 0 < t := by linarith
  calc
    ‖thetaRemainder B t‖ ≤ ∑' z : NonzeroIntegerVector d,
        ‖Complex.exp (-(t:ℂ)*‖B (euclideanInteger z.1)‖^2)‖ :=
      norm_tsum_le_tsum_norm (thetaRemainder_summable B ht').norm
    _ ≤ ∑' z, v z * Real.exp (-a*t) := by
      apply (thetaRemainder_summable B ht').norm.tsum_le_tsum _ (hv.mul_right _)
      intro z
      rw [gaussianTerm_norm]
      dsimp only [v]
      rw [←Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hx := euclideanInteger_norm_one_le z
      have hy := hbound z
      have hx2 : 1 ≤ ‖euclideanInteger z.1‖^2 := by nlinarith
      have hcsq : c^2 * ‖euclideanInteger z.1‖^2 ≤ ‖B (euclideanInteger z.1)‖^2 := by
        have H := (sq_le_sq₀ (mul_nonneg hc.le (norm_nonneg _)) (norm_nonneg _)).mpr hy
        simpa only [mul_pow] using H
      have h1 := mul_nonneg (sub_nonneg.mpr ht) (mul_nonneg (sq_nonneg c)
        (sq_nonneg ‖euclideanInteger z.1‖))
      have h2 := mul_nonneg ht'.le (sub_nonneg.mpr hcsq)
      have h3 := mul_nonneg (sq_nonneg c) (sub_nonneg.mpr hx2)
      have h4 := mul_nonneg ht'.le h3
      dsimp only [a]
      nlinarith
    _ = _ := tsum_mul_right





variable {d : Type*} [Fintype d]
variable {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
variable (B : α → EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (a : (d → ℤ) → ℂ) (k : ℝ)

omit [IsFiniteMeasure μ] in
lemma scaledWeightedThetaTail_joint_stronglyMeasurable
    (hB : ∀ z : d → ℤ, Measurable (fun x => B x (euclideanInteger z))) :
    StronglyMeasurable (fun p : α × ℝ => scaledWeightedThetaTail (B p.1) a k p.2) := by
  have HH : Measurable (fun p : α × ℝ => weightedThetaRemainder (B p.1) a (k*max p.2 1)) := by
    unfold weightedThetaRemainder
    apply Measurable.tsum
    intro z
    have HB : Measurable (fun p : α × ℝ => B p.1 (euclideanInteger z.1)) :=
      (hB z.1).comp measurable_fst
    fun_prop
  have HP : MeasurableSet {p : α × ℝ | 1 < p.2} :=
    measurableSet_lt measurable_const measurable_snd
  apply Measurable.stronglyMeasurable
  convert HH.indicator HP using 1
  ext p
  simp only [scaledWeightedThetaTail,Set.indicator_apply]
  rfl

def averagedWeightedThetaTail (t : ℝ) : ℂ := ∫ x, scaledWeightedThetaTail (B x) a k t ∂μ

omit [IsFiniteMeasure μ] in
lemma averagedWeightedThetaTail_eq_zero {t : ℝ} (ht : t ≤ 1) :
    averagedWeightedThetaTail μ B a k t = 0 := by
  simp [averagedWeightedThetaTail,scaledWeightedThetaTail,not_lt.mpr ht]

lemma averagedWeightedThetaTail_stronglyMeasurable
    (hB : StronglyMeasurable (fun p : α × ℝ => scaledWeightedThetaTail (B p.1) a k p.2)) :
    StronglyMeasurable (averagedWeightedThetaTail μ B a k) :=
  hB.integral_prod_left'

omit [IsFiniteMeasure μ] [MeasurableSpace α] in
lemma scaledWeightedThetaTail_uniform_bound (hk : 0 < k) (M : ℝ)
    (ha : ∀ z, ‖a z‖ ≤ M) (R : ℝ) (hR : 0 ≤ R)
    (hB : ∀ x, ‖(B x).symm.toContinuousLinearMap‖ ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x t, ‖scaledWeightedThetaTail (B x) a k t‖ ≤ C := by
  have hM : 0 ≤ M := (norm_nonneg (a 0)).trans (ha 0)
  obtain ⟨c,C,hc,hC,H⟩ := thetaRemainder_uniform_positive_scale_bound (d := d) R hR k hk
  refine ⟨M*C,mul_nonneg hM hC,fun x t => ?_⟩
  by_cases ht : 1 < t
  · simp only [scaledWeightedThetaTail,Set.indicator_of_mem (show t ∈ Set.Ioi 1 from ht),max_eq_left ht.le]
    have hkt : k ≤ k*t := by nlinarith
    calc
      _ ≤ M*‖thetaRemainder (B x) (k*t)‖ :=
        weightedThetaRemainder_bound (B x) a M ha (mul_pos hk (zero_lt_one.trans ht))
      _ ≤ M*(C*Real.exp (-c*(k*t))) := mul_le_mul_of_nonneg_left (H (B x) (hB x) _ hkt) hM
      _ ≤ M*C := by
        apply mul_le_mul_of_nonneg_left _ hM
        apply mul_le_of_le_one_right hC
        rw [Real.exp_le_one_iff]
        have := mul_pos hc (mul_pos hk (zero_lt_one.trans ht))
        linarith
  · simp only [scaledWeightedThetaTail,Set.indicator_of_notMem (show t ∉ Set.Ioi 1 from ht),norm_zero]
    exact mul_nonneg hM hC

lemma scaledWeightedThetaTail_integrable_average (hk : 0 < k) (M : ℝ)
    (ha : ∀ z, ‖a z‖ ≤ M) (R : ℝ) (hR : 0 ≤ R)
    (hbound : ∀ x, ‖(B x).symm.toContinuousLinearMap‖ ≤ R)
    (hB : ∀ z : d → ℤ, Measurable (fun x => B x (euclideanInteger z))) (t : ℝ) :
    Integrable (fun x => scaledWeightedThetaTail (B x) a k t) μ := by
  obtain ⟨C,hC,HC⟩ := scaledWeightedThetaTail_uniform_bound B a k hk M ha R hR hbound
  have H := scaledWeightedThetaTail_joint_stronglyMeasurable B a k hB
  exact (integrable_const C).mono'
    ((H.comp_measurable (measurable_id.prodMk measurable_const)).aestronglyMeasurable)
    (Filter.Eventually.of_forall (fun x => HC x t))

lemma averagedWeightedThetaTail_bounds (hk : 0 < k) (M : ℝ)
    (ha : ∀ z, ‖a z‖ ≤ M) (R : ℝ) (hR : 0 ≤ R)
    (hB : ∀ x, ‖(B x).symm.toContinuousLinearMap‖ ≤ R) :
    ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧
      (∀ t : ℝ, ‖averagedWeightedThetaTail μ B a k t‖ ≤ C) ∧
      ∀ t : ℝ, 1 < t → ‖averagedWeightedThetaTail μ B a k t‖ ≤ C * Real.exp (-c*t) := by
  have hM : 0 ≤ M := (norm_nonneg (a 0)).trans (ha 0)
  obtain ⟨c,C,hc,hC,hbound⟩ := thetaRemainder_uniform_positive_scale_bound (d := d) R hR k hk
  have Hb (t : ℝ) (ht : 1 < t) :
      ‖averagedWeightedThetaTail μ B a k t‖ ≤ (M*C*μ.real Set.univ) * Real.exp (-(c*k)*t) := by
    have HP : k ≤ k*t := by nlinarith
    have HB (x : α) : ‖weightedThetaRemainder (B x) a (k*t)‖ ≤
        (M*C)*Real.exp (-c*(k*t)) := by
      calc
        _ ≤ M*‖thetaRemainder (B x) (k*t)‖ :=
          weightedThetaRemainder_bound (B x) a M ha (mul_pos hk (zero_lt_one.trans ht))
        _ ≤ M*(C*Real.exp (-c*(k*t))) := mul_le_mul_of_nonneg_left (hbound (B x) (hB x) _ HP) hM
        _ = _ := by ring
    have HH := norm_integral_le_of_norm_le_const (μ := μ) (Filter.Eventually.of_forall HB)
    have HE : averagedWeightedThetaTail μ B a k t = ∫ x, weightedThetaRemainder (B x) a (k*t) ∂μ := by
      simp only [averagedWeightedThetaTail,scaledWeightedThetaTail,
        Set.indicator_of_mem (show t ∈ Set.Ioi 1 from ht),max_eq_left ht.le]
    rw [HE]
    rw [show -c*(k*t) = -(c*k)*t by ring] at HH
    simpa only [mul_assoc,mul_left_comm,mul_comm] using HH
  refine ⟨c*k,M*C*μ.real Set.univ,mul_pos hc hk,
    mul_nonneg (mul_nonneg hM hC) measureReal_nonneg,?_,Hb⟩
  intro t
  by_cases ht : 1 < t
  · apply (Hb t ht).trans
    apply mul_le_of_le_one_right (mul_nonneg (mul_nonneg hM hC) measureReal_nonneg)
    rw [Real.exp_le_one_iff]
    have := mul_pos (mul_pos hc hk) (zero_lt_one.trans ht)
    nlinarith
  · rw [averagedWeightedThetaTail_eq_zero μ B a k (not_lt.mp ht),norm_zero]
    positivity

lemma averagedWeightedThetaTail_locallyIntegrable (hk : 0 < k) (M : ℝ)
    (ha : ∀ z, ‖a z‖ ≤ M) (R : ℝ) (hR : 0 ≤ R)
    (hbound : ∀ x, ‖(B x).symm.toContinuousLinearMap‖ ≤ R)
    (hB : StronglyMeasurable (fun p : α × ℝ => scaledWeightedThetaTail (B p.1) a k p.2)) :
    LocallyIntegrable (averagedWeightedThetaTail μ B a k) := by
  obtain ⟨c,C,hc,hC,hall,_⟩ := averagedWeightedThetaTail_bounds μ B a k hk M ha R hR hbound
  rw [locallyIntegrable_iff]
  intro D hD
  have : IsFiniteMeasure (volume.restrict D) := isFiniteMeasure_restrict.mpr hD.measure_lt_top.ne
  exact (integrable_const C).mono'
    (averagedWeightedThetaTail_stronglyMeasurable μ B a k hB).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun t => hall t))

omit [IsFiniteMeasure μ] in
lemma averagedWeightedThetaTail_bigO_zero (b : ℝ) :
    averagedWeightedThetaTail μ B a k =O[𝓝[>] 0] (fun t : ℝ => t^(-b)) := by
  apply IsBigO.of_bound 0
  have H : ∀ᶠ t : ℝ in 𝓝[>] 0, t < 1 :=
    eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds zero_lt_one)
  filter_upwards [H] with t ht
  simp [averagedWeightedThetaTail_eq_zero μ B a k ht.le]

lemma averagedWeightedThetaTail_bigO_exp (hk : 0 < k) (M : ℝ)
    (ha : ∀ z, ‖a z‖ ≤ M) (R : ℝ) (hR : 0 ≤ R)
    (hbound : ∀ x, ‖(B x).symm.toContinuousLinearMap‖ ≤ R) :
    ∃ c : ℝ, 0 < c ∧ averagedWeightedThetaTail μ B a k =O[atTop] (fun t => Real.exp (-c*t)) := by
  obtain ⟨c,C,hc,_,_,hdecay⟩ := averagedWeightedThetaTail_bounds μ B a k hk M ha R hR hbound
  refine ⟨c,hc,IsBigO.of_bound C ?_⟩
  filter_upwards [eventually_gt_atTop (1:ℝ)] with t ht
  simpa only [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)] using hdecay t ht

theorem averagedWeightedThetaTail_mellin_entire (hk : 0 < k) (M : ℝ)
    (ha : ∀ z, ‖a z‖ ≤ M) (R : ℝ) (hR : 0 ≤ R)
    (hbound : ∀ x, ‖(B x).symm.toContinuousLinearMap‖ ≤ R)
    (hB : ∀ z : d → ℤ, Measurable (fun x => B x (euclideanInteger z))) :
    Differentiable ℂ (mellin (averagedWeightedThetaTail μ B a k)) := by
  obtain ⟨c,hc,hdecay⟩ := averagedWeightedThetaTail_bigO_exp μ B a k hk M ha R hR hbound
  have hmeas := scaledWeightedThetaTail_joint_stronglyMeasurable B a k hB
  intro s
  exact mellin_differentiableAt_of_isBigO_rpow_exp hc
    ((averagedWeightedThetaTail_locallyIntegrable μ B a k hk M ha R hR hbound hmeas).locallyIntegrableOn (Set.Ioi 0))
    hdecay (averagedWeightedThetaTail_bigO_zero μ B a k (s.re-1)) (by linarith)

theorem averagedWeightedThetaTail_mellin_convergent (hk : 0 < k) (M : ℝ)
    (ha : ∀ z, ‖a z‖ ≤ M) (R : ℝ) (hR : 0 ≤ R)
    (hbound : ∀ x, ‖(B x).symm.toContinuousLinearMap‖ ≤ R)
    (hB : ∀ z : d → ℤ, Measurable (fun x => B x (euclideanInteger z))) (s : ℂ) :
    MellinConvergent (averagedWeightedThetaTail μ B a k) s := by
  obtain ⟨c,hc,hdecay⟩ := averagedWeightedThetaTail_bigO_exp μ B a k hk M ha R hR hbound
  have hmeas := scaledWeightedThetaTail_joint_stronglyMeasurable B a k hB
  exact mellinConvergent_of_isBigO_rpow_exp hc
    ((averagedWeightedThetaTail_locallyIntegrable μ B a k hk M ha R hR hbound hmeas).locallyIntegrableOn (Set.Ioi 0))
    hdecay (averagedWeightedThetaTail_bigO_zero μ B a k (s.re-1)) (by linarith)


end
end ArtinMatthews.ReusedTheta
