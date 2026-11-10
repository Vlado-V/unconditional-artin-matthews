module

public import ArtinMatthews.SpectralContinuousAtomVector
public import Mathlib.Algebra.Order.Ring.Star


set_option backward.privateInPublic true
@[expose] public section

/-! The actual scalar spectral atom vector is the orthogonal component
in the corresponding genuine self-adjoint eigenspace. -/
noncomputable section
open Set Filter MeasureTheory
open scoped InnerProductSpace Topology ENNReal
namespace ArtinMatthews

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem spectralQuadraticAtomBump_complement_factor (T : H →L[ℂ] H) (a : ℂ) (n : ℕ) :
    let d := spectralQuadraticShiftSymbol T a
    let p := spectralQuadraticAtomBump T a n
    1-p=d*(((n:ℂ) • star d)*p) := by
  dsimp only
  ext x
  let z := (x:ℂ)-a
  let r : ℝ := 1+(n:ℝ)*‖z‖^2
  have hp : spectralQuadraticAtomBump T a n x=((r⁻¹:ℝ):ℂ) := rfl
  simp only [ContinuousMap.sub_apply,ContinuousMap.one_apply,ContinuousMap.mul_apply,ContinuousMap.smul_apply,
    ContinuousMap.star_apply,smul_eq_mul,spectralQuadraticShiftSymbol_apply,hp,Complex.ofReal_inv]
  change 1-((r:ℂ)⁻¹)=z*(((n:ℂ)*(starRingEnd ℂ) z)*(r:ℂ)⁻¹)
  have hr : (r:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (by dsimp [r]; positivity))
  have hsq : z*(starRingEnd ℂ) z=((‖z‖^2:ℝ):ℂ) := by
    rw [Complex.ofReal_pow]
    exact Complex.mul_conj' z
  have hD : z*((n:ℂ)*(starRingEnd ℂ) z)=(r:ℂ)-1 := by
    rw [mul_left_comm,hsq]
    simp only [r,Complex.ofReal_add,Complex.ofReal_one,Complex.ofReal_mul,Complex.ofReal_natCast]
    ring
  rw [← mul_assoc,hD,sub_mul,mul_inv_cancel₀ hr,one_mul]

theorem spectralQuadraticAtomVector_orthogonal (T : H →L[ℂ] H) (hT : IsSelfAdjoint T)
    (u w : H) (a : ℝ) (hw : T w=(a:ℂ) • w) :
    inner ℂ w (u-spectralQuadraticAtomVector T hT.isStarNormal u (a:ℂ))=0 := by
  let C := cfcHom (R:=ℂ) hT.isStarNormal
  let A : H →L[ℂ] H := T-(a:ℂ) • 1
  let d := spectralQuadraticShiftSymbol T (a:ℂ)
  let p := spectralQuadraticAtomBump T (a:ℂ)
  have hT' := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hT
  have hA : A.IsSymmetric := by
    intro v x
    change inner ℂ (T v-(a:ℂ) • v) x=inner ℂ v (T x-(a:ℂ) • x)
    have he : inner ℂ (T v) x=inner ℂ v (T x) := hT' v x
    rw [inner_sub_left,inner_sub_right,inner_smul_left,inner_smul_right,Complex.conj_ofReal,he]
  have hw0 : A w=0 := by
    change T w-(a:ℂ) • w=0
    rw [hw,sub_self]
  have hn (n : ℕ) : inner ℂ w (u-(C (p n)) u)=0 := by
    let q := ((n:ℂ) • star d)*p n
    have h : 1-p n=d*q := spectralQuadraticAtomBump_complement_factor T (a:ℂ) n
    have he := congrArg C h
    rw [map_sub,map_one,map_mul,spectralQuadraticShiftSymbol_cfc] at he
    have hOp : u-(C (p n)) u=A ((C q) u) := congrArg (fun L : H →L[ℂ] H => L u) he
    have hPair : inner ℂ w (A ((C q) u))=inner ℂ (A w) ((C q) u) := (hA w _).symm
    rw [hOp,hPair,hw0,inner_zero_left]
  have hCont : Continuous (fun v : H => inner ℂ w (u-v)) :=
    continuous_const.inner (continuous_const.sub continuous_id)
  have h := hCont.continuousAt.tendsto.comp (spectralQuadraticAtomVector_tendsto T hT.isStarNormal u (a:ℂ))
  have hz : Tendsto (fun n : ℕ => inner ℂ w (u-(C (p n)) u)) atTop (𝓝 0) :=
    tendsto_const_nhds.congr (fun n => (hn n).symm)
  exact tendsto_nhds_unique h hz

theorem spectralQuadraticMeasure_atom_zero_of_injective (T : H →L[ℂ] H) (hT : IsStarNormal T)
    (hi : Function.Injective T) (u : H) :
    spectralQuadraticMeasure T hT u (spectralQuadraticAtomSet T 0)=0 := by
  let v := spectralQuadraticAtomVector T hT u 0
  have he : T v=(0:ℂ) • v := spectralQuadraticAtomVector_eigen T hT u 0
  have hv : v=0 := hi (by rw [he,zero_smul,map_zero])
  rw [spectralQuadraticMeasure_atom]
  change ENNReal.ofReal (‖v‖^2)=0
  simp [hv]

end ArtinMatthews
