module

public import ArtinMatthews.VaryingKummerAnalyticPeriodicThetaAverages
public import ArtinMatthews.VaryingKummerAnalyticGrowth
public import ArtinMatthews.VaryingKummerAnalyticPeriodicIdealWeights
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

/-! Genuine subquadratic growth for the full periodic theta Mellin transform.
Both tails have actual exponential estimates; their exact Poisson decomposition
supplies the left half-plane without a growth assumption. -/
namespace ArtinMatthews.ReusedTheta
open MeasureTheory Set Filter
open ArtinMatthews.ReusedGrowth
open scoped Classical BigOperators
noncomputable section
variable {d : Type*} [Fintype d]
variable {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
variable (B : α → EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)

theorem averagedWeightedThetaTail_mellin_hasSubquadraticGrowth
    (a : (d → ℤ) → ℂ) (k : ℝ) (hk : 0 < k) (M : ℝ)
    (ha : ∀ z, ‖a z‖ ≤ M) (R : ℝ) (hR : 0 ≤ R)
    (hB : ∀ x, ‖(B x).symm.toContinuousLinearMap‖ ≤ R) :
    HasSubquadraticGrowth (mellin (averagedWeightedThetaTail μ B a k)) := by
  obtain ⟨c,C,hc,hC,_,hb⟩ := averagedWeightedThetaTail_bounds μ B a k hk M ha R hR hB
  exact mellin_hasSubquadraticGrowth hc hC
    (fun _ ht => averagedWeightedThetaTail_eq_zero μ B a k ht) hb

theorem averagedNormalizedPeriodicTheta_mellin_hasSubquadraticGrowth (N : ℕ) [NeZero N]
    (w : (d → Fin N) → ℂ)
    (hzero : periodicPrimalWeight N w 0 = 0) (hsum : ∑ i, w i = 0)
    (R T : ℝ) (hR : 0 ≤ R) (hT : 0 ≤ T)
    (hB : ∀ x, ‖(B x).symm.toContinuousLinearMap‖ ≤ R)
    (hD : ∀ x, ‖(adjointEquiv (B x).symm).symm.toContinuousLinearMap‖ ≤ T)
    (hBm : ∀ z : d → ℤ, Measurable (fun x => B x (euclideanInteger z)))
    (hDm : ∀ z : d → ℤ, Measurable (fun x => adjointEquiv (B x).symm (euclideanInteger z)))
    (c : ℂ) (hc : ∀ x, ((|(LinearMap.det (B x).toLinearMap)⁻¹|:ℝ):ℂ) = c) :
    HasSubquadraticGrowth (mellin (averagedNormalizedPeriodicTheta μ B N w)) := by
  let k : ℝ := Real.pi/(N:ℝ)^2
  have hk : 0 < k := div_pos Real.pi_pos
    (sq_pos_of_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N))))
  let D := fun x => adjointEquiv (B x).symm
  let P := averagedWeightedThetaTail μ B (periodicPrimalWeight N w) k
  let Q := averagedWeightedThetaTail μ D (periodicDualWeight N w) Real.pi
  let a : ℂ := (Fintype.card d:ℂ)/2
  have hwp : ∀ z, ‖periodicPrimalWeight N w z‖ ≤ ∑ i, ‖w i‖ :=
    fun z => congruenceWeight_bound N w ((integerCongruenceEquiv N z).1)
  have hwq : ∀ z, ‖periodicDualWeight N w z‖ ≤ ∑ i, ‖w i‖ :=
    congruenceThetaFourierWeight_bound (congruencePoint N) w
  have hPe : HasSubquadraticGrowth (mellin P) :=
    averagedWeightedThetaTail_mellin_hasSubquadraticGrowth μ B _ k hk _ hwp R hR hB
  have hQe : HasSubquadraticGrowth (mellin Q) :=
    averagedWeightedThetaTail_mellin_hasSubquadraticGrowth μ D _ Real.pi Real.pi_pos _ hwq T hT hD
  have hPc (s : ℂ) : MellinConvergent P s :=
    averagedWeightedThetaTail_mellin_convergent μ B _ k hk _ hwp R hR hB hBm s
  have hQc (s : ℂ) : MellinConvergent Q s :=
    averagedWeightedThetaTail_mellin_convergent μ D _ Real.pi Real.pi_pos _ hwq T hT hD hDm s
  have hPI (t : ℝ) : Integrable (fun x => periodicPrimalTail (B x) N w t) μ :=
    scaledWeightedThetaTail_integrable_average μ B _ k hk _ hwp R hR hB hBm t
  have hQI (t : ℝ) : Integrable (fun x => periodicDualTail (B x) N w t) μ :=
    scaledWeightedThetaTail_integrable_average μ D _ Real.pi Real.pi_pos _ hwq T hT hD hDm t
  have H (t : ℝ) (ht : 0 < t) (hne : t ≠ 1) :
      averagedNormalizedPeriodicTheta μ B N w t = P t+c*(t:ℂ)^(-a)*Q t⁻¹ := by
    unfold averagedNormalizedPeriodicTheta
    simp_rw [normalizedPeriodicTheta_decomposition _ N w hzero hsum ht hne, hc]
    rw [integral_add (hPI t) ((hQI t⁻¹).const_mul _), integral_const_mul]
    rfl
  have Hne : ∀ᵐ t : ℝ ∂(volume.restrict (Set.Ioi 0)), t ≠ 1 := by
    apply ae_restrict_of_ae
    rw [ae_iff]
    simp
  have HE : averagedNormalizedPeriodicTheta μ B N w =ᵐ[volume.restrict (Ioi 0)]
      (fun t => P t+c*(t:ℂ)^(-a)*Q t⁻¹) := by
    filter_upwards [Hne,ae_restrict_mem measurableSet_Ioi] with t hne ht
    exact H t ht hne
  have HM : mellin (averagedNormalizedPeriodicTheta μ B N w) =
      (fun s => mellin P s+c*mellin Q (a-s)) := by
    funext s
    exact (hasMellin_of_add_inversion a c s (hPc s) (hQc (a-s)) HE).2
  rw [HM]
  apply (hPe.add ((hasSubquadraticGrowth_const c).mul (hQe.comp_affine (-1) a))).congr
  intro s
  simp only [neg_one_mul,sub_eq_add_neg,add_comm]


end
end ArtinMatthews.ReusedTheta
