module

public import ArtinMatthews.VaryingKummerAnalyticGaussian
public import Mathlib.Analysis.Real.Pi.Bounds


set_option backward.privateInPublic true
@[expose] public section

/-! Exact generic proof extraction from OpenAI math-main, LatticeTheta.lean
lines 232–452. Only namespace/import routing changes.
See varying-kummer-theta-stage/generic-extraction-manifest.json. -/

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
open MeasureTheory Set Filter Topology Module WithLp
open scoped BigOperators SchwartzMap ZeroAtInfty
open scoped FourierTransform
open scoped BigOperators SchwartzMap FourierTransform
open scoped BigOperators FourierTransform
open MeasureTheory Set Filter Topology Module WithLp Asymptotics
open Module WithLp MeasureTheory
open scoped BigOperators Matrix
section
variable {d : Type*} [Fintype d]

def normalizedTheta (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d) (t : ℝ) : ℂ :=
  latticeTheta B (Real.pi*t)

def normalizedThetaTail (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d) : ℝ → ℂ :=
  (Set.Ioi 1).indicator (fun t => thetaRemainder B (Real.pi*max t 1))

lemma normalizedTheta_inversion (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (t : ℝ) (ht : 0 < t) :
    normalizedTheta B t = ((|(LinearMap.det B.toLinearMap)⁻¹|:ℝ):ℂ) *
      (t:ℂ)^(-((Fintype.card d:ℂ)/2)) * normalizedTheta (adjointEquiv B.symm) t⁻¹ := by
  unfold normalizedTheta
  rw [latticeTheta_inversion B (Real.pi*t) (mul_pos Real.pi_pos ht)]
  have hπ : (Real.pi:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have ht' : (t:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have h1 : (Real.pi:ℂ) / ((Real.pi*t:ℝ):ℂ) = (t:ℂ)⁻¹ := by
    rw [Complex.ofReal_mul]; field_simp
  have h2 : Real.pi^2/(Real.pi*t) = Real.pi*t⁻¹ := by field_simp
  rw [h1,h2,Complex.inv_cpow_ofReal_nonneg ht.le,←Complex.cpow_neg]

lemma normalizedThetaTail_locallyIntegrable (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d) :
    LocallyIntegrable (normalizedThetaTail B) := by
  have hc : Continuous (fun t : ℝ => thetaRemainder B (Real.pi*max t 1)) :=
    (thetaRemainder_continuousOn B).comp_continuous
      (continuous_const.mul (continuous_id.max continuous_const))
      (fun t => mul_pos Real.pi_pos (lt_of_lt_of_le zero_lt_one (le_max_right t 1)))
  exact hc.locallyIntegrable.indicator measurableSet_Ioi

lemma normalizedThetaTail_bigO_exp (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d) :
    ∃ a : ℝ, 0 < a ∧ normalizedThetaTail B =O[atTop] (fun t => Real.exp (-a*t)) := by
  obtain ⟨a,C,ha,_,hbound⟩ := thetaRemainder_exponential_bound B
  refine ⟨a*Real.pi,mul_pos ha Real.pi_pos,IsBigO.of_bound C ?_⟩
  filter_upwards [eventually_gt_atTop (1:ℝ)] with t ht
  have hpt : 1 ≤ Real.pi*t := by nlinarith [Real.pi_gt_three]
  simpa [normalizedThetaTail,ht,max_eq_left ht.le,Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _),mul_assoc] using hbound (Real.pi*t) hpt

lemma normalizedThetaTail_bigO_zero (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (b : ℝ) : normalizedThetaTail B =O[𝓝[>] 0] (fun t : ℝ => t^(-b)) := by
  apply IsBigO.of_bound 0
  have H : ∀ᶠ t : ℝ in 𝓝[>] 0, t < 1 :=
    eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds zero_lt_one)
  filter_upwards [H] with t ht
  simp [normalizedThetaTail,not_lt.mpr ht.le]

lemma normalizedThetaTail_mellin_convergent (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (s : ℂ) : MellinConvergent (normalizedThetaTail B) s := by
  obtain ⟨a,ha,hbound⟩ := normalizedThetaTail_bigO_exp B
  exact mellinConvergent_of_isBigO_rpow_exp ha
    ((normalizedThetaTail_locallyIntegrable B).locallyIntegrableOn (Set.Ioi 0)) hbound
    (normalizedThetaTail_bigO_zero B (s.re-1)) (by linarith)

@[fun_prop] lemma normalizedThetaTail_mellin_differentiable (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d) :
    Differentiable ℂ (mellin (normalizedThetaTail B)) := by
  obtain ⟨a,ha,hbound⟩ := normalizedThetaTail_bigO_exp B
  intro s
  exact mellin_differentiableAt_of_isBigO_rpow_exp ha
    ((normalizedThetaTail_locallyIntegrable B).locallyIntegrableOn (Set.Ioi 0)) hbound
    (normalizedThetaTail_bigO_zero B (s.re-1)) (by linarith)

lemma normalizedThetaTail_eq (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    {t : ℝ} (ht : 1 < t) : normalizedThetaTail B t = normalizedTheta B t - 1 := by
  rw [normalizedThetaTail,indicator_of_mem (show t ∈ Set.Ioi 1 from ht),max_eq_left ht.le]
  exact thetaRemainder_eq B (mul_pos Real.pi_pos (zero_lt_one.trans ht))

lemma normalizedTheta_decomposition (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    {t : ℝ} (ht : 0 < t) (hne : t ≠ 1) :
    normalizedTheta B t - 1 =
      normalizedThetaTail B t +
        ((|(LinearMap.det B.toLinearMap)⁻¹|:ℝ):ℂ) * (t:ℂ)^(-((Fintype.card d:ℂ)/2)) *
          normalizedThetaTail (adjointEquiv B.symm) t⁻¹ +
        ((|(LinearMap.det B.toLinearMap)⁻¹|:ℝ):ℂ) *
          (Set.Ioc 0 1).indicator (fun x : ℝ => (x:ℂ)^(-((Fintype.card d:ℂ)/2))) t -
        (Set.Ioc 0 1).indicator (fun _ : ℝ => (1:ℂ)) t := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hinv : 1 < t⁻¹ := (one_lt_inv₀ ht).mpr hlt
    rw [normalizedThetaTail_eq _ hinv,
      show normalizedThetaTail B t = 0 by simp [normalizedThetaTail,not_lt.mpr hlt.le],
      indicator_of_mem (show t ∈ Set.Ioc 0 1 from ⟨ht,hlt.le⟩),
      indicator_of_mem (show t ∈ Set.Ioc 0 1 from ⟨ht,hlt.le⟩),normalizedTheta_inversion B t ht]
    ring
  · have hinv : t⁻¹ < 1 := (inv_lt_one₀ (zero_lt_one.trans hgt)).mpr hgt
    rw [normalizedThetaTail_eq _ hgt,
      show normalizedThetaTail (adjointEquiv B.symm) t⁻¹ = 0 by
        simp [normalizedThetaTail,not_lt.mpr hinv.le],
      indicator_of_notMem (show t ∉ Set.Ioc 0 1 from fun h => (not_le_of_gt hgt) h.2),
      indicator_of_notMem (show t ∉ Set.Ioc 0 1 from fun h => (not_le_of_gt hgt) h.2)]
    ring

def thetaMellinContinuation (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d) (s : ℂ) : ℂ :=
  mellin (normalizedThetaTail B) s + ((|(LinearMap.det B.toLinearMap)⁻¹|:ℝ):ℂ) *
    mellin (normalizedThetaTail (adjointEquiv B.symm)) ((Fintype.card d:ℂ)/2-s) +
      ((|(LinearMap.det B.toLinearMap)⁻¹|:ℝ):ℂ) / (s-(Fintype.card d:ℂ)/2) - 1/s

 

def thetaMellinXi (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d) (s : ℂ) : ℂ :=
  s*(s-(Fintype.card d:ℂ)/2) *
    (mellin (normalizedThetaTail B) s + ((|(LinearMap.det B.toLinearMap)⁻¹|:ℝ):ℂ) *
      mellin (normalizedThetaTail (adjointEquiv B.symm)) ((Fintype.card d:ℂ)/2-s)) +
    ((|(LinearMap.det B.toLinearMap)⁻¹|:ℝ):ℂ)*s - (s-(Fintype.card d:ℂ)/2)

lemma thetaMellinXi_differentiable (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d) :
    Differentiable ℂ (thetaMellinXi B) := by
  unfold thetaMellinXi
  fun_prop

lemma thetaMellinXi_eq (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    {s : ℂ} (hs : s ≠ 0) (hsa : s ≠ (Fintype.card d:ℂ)/2) :
    thetaMellinXi B s = s*(s-(Fintype.card d:ℂ)/2)*thetaMellinContinuation B s := by
  unfold thetaMellinXi thetaMellinContinuation
  generalize (Fintype.card d:ℂ)/2 = a at hsa ⊢
  field_simp [hs,sub_ne_zero.mpr hsa]

lemma mellinConvergent_inv {f : ℝ → ℂ} {s : ℂ} :
    MellinConvergent (fun t => f t⁻¹) s ↔ MellinConvergent f (-s) := by
  simpa only [Real.rpow_neg_one,Complex.ofReal_neg,Complex.ofReal_one,div_neg,_root_.div_one] using (MellinConvergent.comp_rpow (f := f) (s := s) (a := -1) (by norm_num))

 

theorem normalizedTheta_hasMellin (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    {s : ℂ} (hs : (Fintype.card d:ℝ)/2 < s.re) :
    HasMellin (fun t => normalizedTheta B t - 1) s (thetaMellinContinuation B s) := by
  let a : ℂ := (Fintype.card d:ℂ)/2
  let c : ℂ := ((|(LinearMap.det B.toLinearMap)⁻¹|:ℝ):ℂ)
  let P := normalizedThetaTail B
  let Q := normalizedThetaTail (adjointEquiv B.symm)
  let R := (Set.Ioc 0 1).indicator (fun t : ℝ => (t:ℂ)^(-a))
  let J := (Set.Ioc 0 1).indicator (fun _ : ℝ => (1:ℂ))
  let q := fun t : ℝ => c • ((t:ℂ)^(-a) • Q t⁻¹)
  have ha : a.re = (Fintype.card d:ℝ)/2 := by simp [a]
  have has : 0 < s.re + (-a).re := by rw [Complex.neg_re,ha]; linarith
  have hs0 : 0 < s.re := lt_of_le_of_lt (by positivity) hs
  have hP : MellinConvergent P s := normalizedThetaTail_mellin_convergent B s
  have hQ : MellinConvergent (fun t => (t:ℂ)^(-a) • Q t⁻¹) s := by
    apply MellinConvergent.cpow_smul.mpr
    apply mellinConvergent_inv.mpr
    exact normalizedThetaTail_mellin_convergent _ _
  have hq : MellinConvergent q s := hQ.const_smul c
  have hR : HasMellin R s (1/(s-a)) := by
    simpa only [sub_eq_add_neg] using hasMellin_cpow_Ioc (-a) has
  have hJ : HasMellin J s (1/s) := hasMellin_one_Ioc hs0
  have hPR := hasMellin_add hP hq
  have hPRR := hasMellin_add hPR.1 (hR.1.const_smul c)
  have HF := hasMellin_sub hPRR.1 hJ.1
  have hqeq : mellin q s = c * mellin Q (a-s) := by
    calc
      mellin q s = c • mellin (fun t => (t:ℂ)^(-a) • Q t⁻¹) s :=
        mellin_const_smul _ s c
      _ = c * mellin Q (a-s) := by
        rw [mellin_cpow_smul,mellin_comp_inv,smul_eq_mul]
        congr 2
        ring
  have HFval : mellin (fun t => (P t + q t) + c • R t - J t) s =
      thetaMellinContinuation B s := by
    rw [HF.2,hPRR.2,hPR.2,hqeq,mellin_const_smul,hR.2,hJ.2,smul_eq_mul]
    simp only [thetaMellinContinuation,P,Q,c,a,mul_one_div]
  have Hne : ∀ᵐ t : ℝ ∂(volume.restrict (Set.Ioi 0)), t ≠ 1 := by
    apply ae_restrict_of_ae
    rw [ae_iff]
    simp
  have HE : (fun t => normalizedTheta B t - 1) =ᵐ[volume.restrict (Set.Ioi 0)]
      (fun t => (P t + q t) + c • R t - J t) := by
    filter_upwards [Hne,ae_restrict_mem measurableSet_Ioi] with t hne ht
    simpa only [P,q,c,a,R,J,smul_eq_mul,mul_assoc] using
      normalizedTheta_decomposition B ht hne
  have HI : (fun t : ℝ => (t:ℂ)^(s-1) • (normalizedTheta B t-1))
      =ᵐ[volume.restrict (Set.Ioi 0)]
      (fun t : ℝ => (t:ℂ)^(s-1) • ((P t+q t)+c • R t-J t)) := by
    filter_upwards [HE] with t ht
    rw [ht]
  refine ⟨HF.1.congr HI.symm, ?_⟩
  exact (integral_congr_ae HI).trans HFval

lemma thetaDual_involutive (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d) :
    adjointEquiv (adjointEquiv B.symm).symm = B := by
  apply ContinuousLinearEquiv.ext
  funext x
  change B.toContinuousLinearMap.adjoint.adjoint x = B x
  rw [ContinuousLinearMap.adjoint_adjoint]
  rfl

lemma adjointEquiv_det (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d) :
    LinearMap.det (adjointEquiv B).toLinearMap = LinearMap.det B.toLinearMap := by
  classical
  change LinearMap.det B.toContinuousLinearMap.adjoint.toLinearMap = _
  rw [← ContinuousLinearMap.adjoint_toLinearMap,
    ← LinearMap.det_toMatrix (EuclideanSpace.basisFun d ℝ).toBasis,
    LinearMap.toMatrix_adjoint]
  simp only [Matrix.det_conjTranspose,star_trivial,LinearMap.det_toMatrix]
  rfl

lemma thetaDual_det (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d) :
    LinearMap.det (adjointEquiv B.symm).toLinearMap = (LinearMap.det B.toLinearMap)⁻¹ := by
  rw [adjointEquiv_det]
  exact B.toLinearEquiv.det_coe_symm

 

theorem thetaMellinXi_functional_equation (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (s : ℂ) : thetaMellinXi B s = ((|(LinearMap.det B.toLinearMap)⁻¹|:ℝ):ℂ) *
      thetaMellinXi (adjointEquiv B.symm) ((Fintype.card d:ℂ)/2-s) := by
  have hdet : LinearMap.det B.toLinearMap ≠ 0 := B.toLinearEquiv.isUnit_det'.ne_zero
  have hd : ((|(LinearMap.det (adjointEquiv B.symm).toLinearMap)⁻¹|:ℝ):ℂ) =
      (((|(LinearMap.det B.toLinearMap)⁻¹|:ℝ):ℂ))⁻¹ := by
    rw [thetaDual_det]
    simp
  have hc : ((|(LinearMap.det B.toLinearMap)⁻¹|:ℝ):ℂ) ≠ 0 := by
    simpa only [ne_eq,Complex.ofReal_eq_zero,abs_eq_zero,inv_eq_zero] using hdet
  unfold thetaMellinXi
  rw [thetaDual_involutive,hd]
  generalize (Fintype.card d:ℂ)/2 = a
  simp only [sub_sub_cancel]
  generalize ((|(LinearMap.det B.toLinearMap)⁻¹|:ℝ):ℂ) = c at hc ⊢
  field_simp [hc]
  ring

end


end
end ArtinMatthews.ReusedTheta
