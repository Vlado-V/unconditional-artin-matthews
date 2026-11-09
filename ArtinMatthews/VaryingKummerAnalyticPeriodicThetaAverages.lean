module

public import ArtinMatthews.VaryingKummerAnalyticPeriodicIdealWeights


set_option backward.privateInPublic true
@[expose] public section

/-! Exact generic proof extraction from OpenAI PrimePackets/GaussianMellin.lean.
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


variable {d : Type*} [Fintype d]
local instance averagedPeriodicThetaDecidableEq : DecidableEq d := Classical.decEq d

lemma hasMellin_of_add_inversion {F P Q : ℝ → ℂ} (a c s : ℂ)
    (hP : MellinConvergent P s) (hQ : MellinConvergent Q (a-s))
    (hF : F =ᵐ[volume.restrict (Ioi 0)] (fun t => P t+c*(t:ℂ)^(-a)*Q t⁻¹)) :
    HasMellin F s (mellin P s+c*mellin Q (a-s)) := by
  let q := fun t : ℝ => c • ((t:ℂ)^(-a) • Q t⁻¹)
  have hQi : MellinConvergent (fun t => (t:ℂ)^(-a) • Q t⁻¹) s := by
    apply MellinConvergent.cpow_smul.mpr
    apply mellinConvergent_inv.mpr
    convert hQ using 1
    ring
  have hq : MellinConvergent q s := hQi.const_smul c
  have HF := hasMellin_add hP hq
  have hqeq : mellin q s = c*mellin Q (a-s) := by
    calc
      mellin q s = c • mellin (fun t => (t:ℂ)^(-a) • Q t⁻¹) s := mellin_const_smul _ s c
      _ = _ := by
        rw [mellin_cpow_smul,mellin_comp_inv,smul_eq_mul]
        congr 2
        ring
  have HE : F =ᵐ[volume.restrict (Ioi 0)] (fun t => P t+q t) := by
    simpa only [q,smul_eq_mul,mul_assoc] using hF
  have HI : (fun t : ℝ => (t:ℂ)^(s-1) • F t) =ᵐ[volume.restrict (Ioi 0)]
      (fun t : ℝ => (t:ℂ)^(s-1) • (P t+q t)) := by
    filter_upwards [HE] with t ht
    rw [ht]
  refine ⟨HF.1.congr HI.symm, ?_⟩
  exact (integral_congr_ae HI).trans (HF.2.trans (by rw [hqeq]))

variable {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (B : α → EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)

def averagedNormalizedPeriodicTheta (N : ℕ) [NeZero N]
    (w : (d → Fin N) → ℂ) (t : ℝ) : ℂ := ∫ x, normalizedPeriodicTheta (B x) N w t ∂μ

 

theorem averagedNormalizedPeriodicTheta_mellin_entire (N : ℕ) [NeZero N]
    (w : (d → Fin N) → ℂ)
    (hzero : periodicPrimalWeight N w 0 = 0) (hsum : ∑ i, w i = 0)
    (R T : ℝ) (hR : 0 ≤ R) (hT : 0 ≤ T)
    (hB : ∀ x, ‖(B x).symm.toContinuousLinearMap‖ ≤ R)
    (hD : ∀ x, ‖(adjointEquiv (B x).symm).symm.toContinuousLinearMap‖ ≤ T)
    (hBm : ∀ z : d → ℤ, Measurable (fun x => B x (euclideanInteger z)))
    (hDm : ∀ z : d → ℤ, Measurable (fun x => adjointEquiv (B x).symm (euclideanInteger z)))
    (c : ℂ) (hc : ∀ x, ((|(LinearMap.det (B x).toLinearMap)⁻¹|:ℝ):ℂ) = c) :
    Differentiable ℂ (mellin (averagedNormalizedPeriodicTheta μ B N w)) := by
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
  have hPe : Differentiable ℂ (mellin P) :=
    averagedWeightedThetaTail_mellin_entire μ B _ k hk _ hwp R hR hB hBm
  have hQe : Differentiable ℂ (mellin Q) :=
    averagedWeightedThetaTail_mellin_entire μ D _ Real.pi Real.pi_pos _ hwq T hT hD hDm
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
  exact hPe.add ((hQe.comp ((differentiable_const a).sub differentiable_id)).const_mul c)


end
end ArtinMatthews.ReusedTheta
