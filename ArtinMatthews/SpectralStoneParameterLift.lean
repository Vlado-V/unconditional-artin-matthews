module

public import ArtinMatthews.SpectralAmbientStone
public import ArtinMatthews.SpectralEisensteinCriticalLine
public import ArtinMatthews.SpectralEisensteinCriticalPowerFlux


set_option backward.privateInPublic true
@[expose] public section

/-! Explicit continuous upper and lower energy lifts to the actual
right-hand Eisenstein resolvent domain. They have the genuine reflected
critical and common subcritical boundary values. -/
noncomputable section
open Set Filter Topology
namespace ArtinMatthews

def spectralStoneRootReal (x ε : ℝ) : ℝ :=
  Real.sqrt ((Real.sqrt ((x-1/4)^2+ε^2)-(x-1/4))/2)

def spectralStoneRootImag (x ε : ℝ) : ℝ :=
  Real.sqrt ((Real.sqrt ((x-1/4)^2+ε^2)+(x-1/4))/2)

def spectralStoneUpperParameter (x ε : ℝ) : ℂ :=
  (((1/2:ℝ)+spectralStoneRootReal x ε:ℝ):ℂ)-(spectralStoneRootImag x ε:ℂ)*Complex.I

def spectralStoneLowerParameter (x ε : ℝ) : ℂ :=
  (starRingEnd ℂ) (spectralStoneUpperParameter x ε)

theorem spectralStoneRoot_bounds (x ε : ℝ) :
    |x-1/4|≤Real.sqrt ((x-1/4)^2+ε^2) := by
  apply (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [sq_abs,Real.sq_sqrt (by positivity)]
  exact le_add_of_nonneg_right (sq_nonneg _)

theorem spectralStoneRoot_squares (x ε : ℝ) :
    (spectralStoneRootReal x ε)^2=(Real.sqrt ((x-1/4)^2+ε^2)-(x-1/4))/2 ∧
    (spectralStoneRootImag x ε)^2=(Real.sqrt ((x-1/4)^2+ε^2)+(x-1/4))/2 := by
  have h := spectralStoneRoot_bounds x ε
  constructor
  · exact Real.sq_sqrt (div_nonneg (sub_nonneg.mpr ((le_abs_self _).trans h)) (by norm_num))
  · exact Real.sq_sqrt (div_nonneg (by linarith [(neg_le_abs (x-1/4)).trans h]) (by norm_num))

theorem spectralStoneRoot_product (x ε : ℝ) (hε : 0≤ε) :
    2*spectralStoneRootReal x ε*spectralStoneRootImag x ε=ε := by
  have hU : 0 ≤ spectralStoneRootReal x ε := Real.sqrt_nonneg _
  have hV : 0 ≤ spectralStoneRootImag x ε := Real.sqrt_nonneg _
  obtain ⟨hu,hv⟩ := spectralStoneRoot_squares x ε
  apply (sq_eq_sq₀ (by positivity) hε).mp
  rw [mul_pow,mul_pow,hu,hv]
  have h := Real.sq_sqrt (show 0≤(x-1/4)^2+ε^2 by positivity)
  nlinarith only [h]

theorem spectralStoneUpperParameter_re (x ε : ℝ) :
    (spectralStoneUpperParameter x ε).re=1/2+spectralStoneRootReal x ε := by
  simp [spectralStoneUpperParameter,Complex.mul_re]

theorem spectralStoneUpperParameter_im (x ε : ℝ) :
    (spectralStoneUpperParameter x ε).im= -spectralStoneRootImag x ε := by
  simp [spectralStoneUpperParameter,Complex.mul_im]

theorem spectralStoneUpperParameter_energy (x ε : ℝ) (hε : 0≤ε) :
    spectralStoneUpperParameter x ε*(1-spectralStoneUpperParameter x ε)=spectralEnergyShift x ε := by
  obtain ⟨hu,hv⟩ := spectralStoneRoot_squares x ε
  apply Complex.ext
  · simp only [Complex.mul_re,Complex.sub_re,Complex.one_re,Complex.sub_im,Complex.one_im,zero_sub,
      spectralStoneUpperParameter_re,spectralStoneUpperParameter_im,spectralEnergyShift_re]
    nlinarith only [hu,hv]
  · simp only [Complex.mul_im,Complex.sub_re,Complex.one_re,Complex.sub_im,Complex.one_im,zero_sub,
      spectralStoneUpperParameter_re,spectralStoneUpperParameter_im,spectralEnergyShift_im]
    nlinarith only [spectralStoneRoot_product x ε hε]

theorem spectralEnergyShift_conj (x ε : ℝ) :
    (starRingEnd ℂ) (spectralEnergyShift x ε)=spectralEnergyShift x (-ε) := by
  apply Complex.ext <;> simp only [Complex.conj_re,Complex.conj_im,spectralEnergyShift_re,spectralEnergyShift_im]

theorem spectralStoneLowerParameter_energy (x ε : ℝ) (hε : 0≤ε) :
    spectralStoneLowerParameter x ε*(1-spectralStoneLowerParameter x ε)=spectralEnergyShift x (-ε) := by
  rw [spectralStoneLowerParameter,← map_one (starRingEnd ℂ),← map_sub,← map_mul,
    spectralStoneUpperParameter_energy x ε hε,spectralEnergyShift_conj]

theorem spectralStoneUpperParameter_domain (x ε : ℝ) (hε : 0<ε) :
    spectralStoneUpperParameter x ε∈gamma0EisensteinContinuationDomain := by
  refine ⟨?_,?_⟩
  · rw [spectralStoneUpperParameter_re,lt_add_iff_pos_right]
    have hU : 0 ≤ spectralStoneRootReal x ε := Real.sqrt_nonneg _
    refine lt_of_le_of_ne hU ?_
    intro h
    have hp := spectralStoneRoot_product x ε hε.le
    rw [← h,mul_zero,zero_mul] at hp
    exact hε.ne hp
  · rw [spectralStoneUpperParameter_energy x ε hε.le]
    exact spectralEnergyShift_offcut x ε hε.ne'

theorem spectralStoneLowerParameter_domain (x ε : ℝ) (hε : 0<ε) :
    spectralStoneLowerParameter x ε∈gamma0EisensteinContinuationDomain := by
  refine ⟨?_,?_⟩
  · rw [spectralStoneLowerParameter,Complex.conj_re]
    exact (spectralStoneUpperParameter_domain x ε hε).1
  · rw [spectralStoneLowerParameter_energy x ε hε.le]
    exact spectralEnergyShift_offcut x (-ε) (neg_ne_zero.mpr hε.ne')

theorem spectralStoneUpperParameter_continuous :
    Continuous (fun p : ℝ×ℝ => spectralStoneUpperParameter p.1 p.2) := by
  unfold spectralStoneUpperParameter spectralStoneRootReal spectralStoneRootImag
  fun_prop

theorem spectralStoneLowerParameter_continuous :
    Continuous (fun p : ℝ×ℝ => spectralStoneLowerParameter p.1 p.2) :=
  Complex.continuous_conj.comp spectralStoneUpperParameter_continuous

theorem spectralStoneUpperParameter_critical (x : ℝ) (hx : (1/4:ℝ)≤x) :
    spectralStoneUpperParameter x 0=1-eisensteinCriticalPoint (Real.sqrt (x-1/4)) := by
  have h : 0≤x-1/4 := sub_nonneg.mpr hx
  have hR : spectralStoneRootReal x 0=0 := by
    simp only [spectralStoneRootReal,zero_pow (by decide : (2:ℕ)≠0),add_zero,
      Real.sqrt_sq h,sub_self,zero_div,Real.sqrt_zero]
  have hI : spectralStoneRootImag x 0=Real.sqrt (x-1/4) := by
    simp only [spectralStoneRootImag,zero_pow (by decide : (2:ℕ)≠0),add_zero,Real.sqrt_sq h]
    congr 1
    ring
  apply Complex.ext
  · rw [spectralStoneUpperParameter_re,hR,add_zero,Complex.sub_re,Complex.one_re,eisensteinCriticalPoint_re]
    norm_num
  · rw [spectralStoneUpperParameter_im,hI,Complex.sub_im,Complex.one_im,eisensteinCriticalPoint_im,zero_sub]

theorem spectralStoneLowerParameter_critical (x : ℝ) (hx : (1/4:ℝ)≤x) :
    spectralStoneLowerParameter x 0=eisensteinCriticalPoint (Real.sqrt (x-1/4)) := by
  rw [spectralStoneLowerParameter,spectralStoneUpperParameter_critical x hx,
    eisensteinCriticalParameter_conj (eisensteinCriticalPoint_re _),starRingEnd_self_apply]

theorem spectralStoneUpperParameter_subcritical (x : ℝ) (hx : x≤1/4) :
    spectralStoneUpperParameter x 0=(((1/2:ℝ)+Real.sqrt (1/4-x):ℝ):ℂ) := by
  have h : 0≤1/4-x := sub_nonneg.mpr hx
  have hR : Real.sqrt ((x-1/4)^2+(0:ℝ)^2)=1/4-x := by
    rw [show x-(1/4:ℝ)= -(1/4-x) by ring,neg_pow,zero_pow (by decide : (2:ℕ)≠0),add_zero]
    norm_num
    exact Real.sqrt_sq h
  have hu : spectralStoneRootReal x 0=Real.sqrt (1/4-x) := by
    rw [spectralStoneRootReal,hR]
    congr 1
    ring
  have hv : spectralStoneRootImag x 0=0 := by
    rw [spectralStoneRootImag,hR,show (1/4-x)+(x-1/4)=(0:ℝ) by ring,zero_div,Real.sqrt_zero]
  rw [spectralStoneUpperParameter,hu,hv,Complex.ofReal_zero,zero_mul,sub_zero]

theorem spectralStoneLowerParameter_subcritical (x : ℝ) (hx : x≤1/4) :
    spectralStoneLowerParameter x 0=spectralStoneUpperParameter x 0 := by
  rw [spectralStoneLowerParameter,spectralStoneUpperParameter_subcritical x hx,Complex.conj_ofReal]

end ArtinMatthews
