module

public import ArtinMatthews.SpectralEisensteinLogGeometry
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Complex.RealDeriv


set_option backward.privateInPublic true
@[expose] public section

/-! Genuine spatial derivatives of exp(s times the logarithmic row height). -/
noncomputable section
open Set Filter
open scoped ContDiff
namespace ArtinMatthews

def eisensteinRowPower (s : ℂ) (c d : ℝ) (p : ℝ × ℝ) : ℂ :=
  Complex.exp (s*(eisensteinRowLog c d p : ℂ))

def eisensteinRowPowerX (s : ℂ) (c d : ℝ) (p : ℝ × ℝ) : ℂ :=
  s*eisensteinRowPower s c d p*(eisensteinRowLogX c d p : ℂ)

def eisensteinRowPowerY (s : ℂ) (c d : ℝ) (p : ℝ × ℝ) : ℂ :=
  s*eisensteinRowPower s c d p*(eisensteinRowLogY c d p : ℂ)

def eisensteinRowPowerXX (s : ℂ) (c d : ℝ) (p : ℝ × ℝ) : ℂ :=
  eisensteinRowPower s c d p * (s^2*(eisensteinRowLogX c d p : ℂ)^2+s*(eisensteinRowLogXX c d p : ℂ))

def eisensteinRowPowerXY (s : ℂ) (c d : ℝ) (p : ℝ × ℝ) : ℂ :=
  eisensteinRowPower s c d p * (s^2*(eisensteinRowLogX c d p : ℂ)*(eisensteinRowLogY c d p : ℂ)+
    s*(eisensteinRowLogXY c d p : ℂ))

def eisensteinRowPowerYY (s : ℂ) (c d : ℝ) (p : ℝ × ℝ) : ℂ :=
  eisensteinRowPower s c d p * (s^2*(eisensteinRowLogY c d p : ℂ)^2+s*(eisensteinRowLogYY c d p : ℂ))

theorem eisensteinRowPower_contDiffOn (s : ℂ) (c d : ℝ) (hcd : c ≠ 0 ∨ d ≠ 0) :
    ContDiffOn ℝ ∞ (eisensteinRowPower s c d) {p : ℝ × ℝ | 0 < p.2} := by
  have hlog : ContDiffOn ℝ ∞ (eisensteinRowLog c d) {p : ℝ × ℝ | 0 < p.2} := by
    intro p hp
    have hq : ContDiffAt ℝ ∞ (eisensteinRowQuadratic c d) p := by
      unfold eisensteinRowQuadratic
      fun_prop
    exact ((contDiffAt_snd.log hp.ne').sub (hq.log (eisensteinRowQuadratic_pos c d hcd p hp).ne')).contDiffWithinAt
  have hc := Complex.ofRealCLM.contDiff.comp_contDiffOn hlog
  exact (contDiffOn_const.mul hc).cexp

theorem eisensteinRowPower_hasFDerivAt (s : ℂ) (c d : ℝ) (hcd : c ≠ 0 ∨ d ≠ 0)
    (p : ℝ × ℝ) (hp : 0 < p.2) :
    HasFDerivAt (eisensteinRowPower s c d)
      (spectralPlaneDerivative (eisensteinRowPowerX s c d p) (eisensteinRowPowerY s c d p)) p := by
  have hl := eisensteinRowLog_hasFDerivAt c d hcd p hp
  have hc := Complex.ofRealCLM.hasFDerivAt.comp p hl
  have he := (hc.const_mul s).cexp
  change HasFDerivAt (fun q => Complex.exp (s*(eisensteinRowLog c d q : ℂ))) _ p
  convert! he using 1
  apply ContinuousLinearMap.ext
  intro u
  simp [spectralPlaneDerivative,eisensteinRowPowerX,eisensteinRowPowerY,eisensteinRowPower,
    Complex.real_smul]
  ring

theorem eisensteinRowPowerX_hasFDerivAt (s : ℂ) (c d : ℝ) (hcd : c ≠ 0 ∨ d ≠ 0)
    (p : ℝ × ℝ) (hp : 0 < p.2) :
    HasFDerivAt (eisensteinRowPowerX s c d)
      (spectralPlaneDerivative (eisensteinRowPowerXX s c d p) (eisensteinRowPowerXY s c d p)) p := by
  have hf := eisensteinRowPower_hasFDerivAt s c d hcd p hp
  have hl := Complex.ofRealCLM.hasFDerivAt.comp p (eisensteinRowLogX_hasFDerivAt c d hcd p hp)
  have h := (hf.const_mul s).mul hl
  change HasFDerivAt (fun q => s*eisensteinRowPower s c d q*(eisensteinRowLogX c d q : ℂ)) _ p
  convert! h using 1
  apply ContinuousLinearMap.ext
  intro u
  simp [spectralPlaneDerivative,eisensteinRowPowerXX,eisensteinRowPowerXY,
    eisensteinRowPowerX,eisensteinRowPowerY,Complex.real_smul]
  ring

theorem eisensteinRowPowerY_hasFDerivAt (s : ℂ) (c d : ℝ) (hcd : c ≠ 0 ∨ d ≠ 0)
    (p : ℝ × ℝ) (hp : 0 < p.2) :
    HasFDerivAt (eisensteinRowPowerY s c d)
      (spectralPlaneDerivative (eisensteinRowPowerXY s c d p) (eisensteinRowPowerYY s c d p)) p := by
  have hf := eisensteinRowPower_hasFDerivAt s c d hcd p hp
  have hl := Complex.ofRealCLM.hasFDerivAt.comp p (eisensteinRowLogY_hasFDerivAt c d hcd p hp)
  have h := (hf.const_mul s).mul hl
  change HasFDerivAt (fun q => s*eisensteinRowPower s c d q*(eisensteinRowLogY c d q : ℂ)) _ p
  convert! h using 1
  apply ContinuousLinearMap.ext
  intro u
  simp [spectralPlaneDerivative,eisensteinRowPowerXY,eisensteinRowPowerYY,
    eisensteinRowPowerX,eisensteinRowPowerY,Complex.real_smul]
  ring

theorem eisensteinRowPower_fderiv_eventually (s : ℂ) (c d : ℝ) (hcd : c ≠ 0 ∨ d ≠ 0)
    (p : ℝ × ℝ) (hp : 0 < p.2) :
    fderiv ℝ (eisensteinRowPower s c d) =ᶠ[nhds p]
      (fun q => spectralPlaneDerivative (eisensteinRowPowerX s c d q) (eisensteinRowPowerY s c d q)) := by
  filter_upwards [(isOpen_lt continuous_const continuous_snd).mem_nhds hp] with q hq
  exact (eisensteinRowPower_hasFDerivAt s c d hcd q hq).fderiv

theorem eisensteinRowPower_second (s : ℂ) (c d : ℝ) (hcd : c ≠ 0 ∨ d ≠ 0)
    (p : ℝ × ℝ) (hp : 0 < p.2) :
    fderiv ℝ (fderiv ℝ (eisensteinRowPower s c d)) p =
      spectralPlaneDerivativeMap.comp
        ((spectralPlaneDerivative (eisensteinRowPowerXX s c d p) (eisensteinRowPowerXY s c d p)).prod
          (spectralPlaneDerivative (eisensteinRowPowerXY s c d p) (eisensteinRowPowerYY s c d p))) := by
  rw [(eisensteinRowPower_fderiv_eventually s c d hcd p hp).fderiv_eq]
  exact (hasFDerivAt_spectralPlaneDerivative (eisensteinRowPowerX_hasFDerivAt s c d hcd p hp)
    (eisensteinRowPowerY_hasFDerivAt s c d hcd p hp)).fderiv

theorem eisensteinRowPower_hyperbolic_pde (s : ℂ) (c d : ℝ) (hcd : c ≠ 0 ∨ d ≠ 0)
    (p : ℝ × ℝ) (hp : 0 < p.2) :
    -((p.2:ℂ)^2)*(fderiv ℝ (fderiv ℝ (eisensteinRowPower s c d)) p (1,0) (1,0)+
      fderiv ℝ (fderiv ℝ (eisensteinRowPower s c d)) p (0,1) (0,1)) =
        s*(1-s)*eisensteinRowPower s c d p := by
  rw [eisensteinRowPower_second s c d hcd p hp]
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.prod_apply,
    spectralPlaneDerivativeMap_apply,spectralPlaneDerivative_apply,one_smul,zero_smul,add_zero,zero_add]
  have he := congrArg (fun r : ℝ => (r:ℂ)) (eisensteinRowLog_eikonal c d hcd p hp)
  have hl := congrArg (fun r : ℝ => (r:ℂ)) (eisensteinRowLog_laplacian c d hcd p hp)
  push_cast at he hl
  unfold eisensteinRowPowerXX eisensteinRowPowerYY
  have hpC : (p.2:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hp.ne'
  calc
    _ = -((p.2:ℂ)^2)*eisensteinRowPower s c d p*
        (s^2*((eisensteinRowLogX c d p:ℂ)^2+(eisensteinRowLogY c d p:ℂ)^2)+
          s*((eisensteinRowLogXX c d p:ℂ)+(eisensteinRowLogYY c d p:ℂ))) := by ring
    _ = _ := by rw [he,hl]; field_simp; ring

end ArtinMatthews
