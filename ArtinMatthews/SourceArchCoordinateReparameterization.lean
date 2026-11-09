module

public import OAI.NumberTheory.DirichletL.MeanSquare.UnitRows
public import Mathlib.Analysis.Calculus.ContDiff.Deriv


set_option backward.privateInPublic true
@[expose] public section

/-! The native positive Laplacian in the exact right-root and
exponential-height parameters. -/
namespace ArtinMatthews.SourceArchJacquet
open Filter OAI.CubicEisenstein
open scoped ContDiff Topology BigOperators
noncomputable section

private theorem deriv2_comp_real (f : ℝ → ℂ) (g : ℝ → ℝ) (x : ℝ)
    (hf : ContDiffAt ℝ 2 f (g x)) (hg : ContDiffAt ℝ 2 g x) :
    deriv (deriv (f ∘ g)) x =
      deriv g x • (deriv g x • deriv (deriv f) (g x)) +
        deriv (deriv g) x • deriv f (g x) := by
  have hdf : ContDiffAt ℝ 1 (deriv f) (g x) := hf.derivWithin (by norm_num)
  have hdg : ContDiffAt ℝ 1 (deriv g) x := hg.derivWithin (by norm_num)
  have hchain := (hdf.differentiableAt (by norm_num)).hasDerivAt.scomp x
    (hg.differentiableAt (by norm_num)).hasDerivAt
  have hprod := (hdg.differentiableAt (by norm_num)).hasDerivAt.smul hchain
  have he : deriv (f ∘ g) =ᶠ[𝓝 x] fun t => deriv g t • deriv f (g t) := by
    filter_upwards [hg.continuousAt.eventually (hf.eventually (by simp)),
      hg.eventually (by simp)] with t ht ht'
    exact ((ht.differentiableAt (by norm_num)).hasDerivAt.scomp t
      (ht'.differentiableAt (by norm_num)).hasDerivAt).deriv
  exact (hprod.congr_of_eventuallyEq he).deriv

private theorem deriv2_affine (f : ℝ → ℂ) (a b : ℝ) (hf : ContDiffAt ℝ 2 f a) :
    deriv (deriv (fun t => f (a+b*t))) 0 = (b:ℂ)^2*deriv (deriv f) a := by
  let g : ℝ → ℝ := fun t => a+b*t
  have hg : ContDiff ℝ 2 g := by dsimp [g]; fun_prop
  have h0 : g 0 = a := by simp [g]
  have hd : deriv g = fun _ => b := by
    funext t
    have h := ((hasDerivAt_const t a).add ((hasDerivAt_id t).const_mul b)).deriv
    change deriv g t = 0+b*1 at h
    simpa only [mul_one,zero_add] using h
  have hdd : deriv (deriv g) 0 = 0 := by rw [hd,deriv_const]
  change deriv (deriv (f ∘ g)) 0 = _
  rw [deriv2_comp_real f g 0 (by rwa [h0]) hg.contDiffAt,hdd,hd,h0]
  simp only [zero_smul,add_zero,RCLike.real_smul_eq_coe_mul,pow_two,mul_assoc] <;> rfl

private theorem deriv_exponential_height (f : ℝ → ℂ) (y : ℝ)
    (hf : ContDiffAt ℝ 2 f y) :
    deriv (fun t => f (y*Real.exp t)) 0 = (y:ℂ)*deriv f y ∧
    deriv (deriv (fun t => f (y*Real.exp t))) 0 =
      (y:ℂ)^2*deriv (deriv f) y+(y:ℂ)*deriv f y := by
  let g : ℝ → ℝ := fun t => y*Real.exp t
  have hg : ContDiff ℝ 2 g := by dsimp [g]; fun_prop
  have h0 : g 0 = y := by simp [g]
  have hd : deriv g = g := funext fun t => ((Real.hasDerivAt_exp t).const_mul y).deriv
  have hdd : deriv (deriv g) 0 = y := by rw [hd,hd,h0]
  have hf' : ContDiffAt ℝ 2 f (g 0) := by rwa [h0]
  constructor
  · change deriv (f ∘ g) 0 = _
    have h := ((hf'.differentiableAt (by norm_num)).hasDerivAt.scomp 0
      (hg.differentiable (by norm_num) 0).hasDerivAt).deriv
    rw [hd,h0] at h
    exact h.trans (show y • deriv f y = (y:ℂ)*deriv f y from rfl)
  · change deriv (deriv (f ∘ g)) 0 = _
    rw [deriv2_comp_real f g 0 hf' hg.contDiffAt,hdd,hd,h0]
    simp only [RCLike.real_smul_eq_coe_mul,pow_two,mul_assoc] <;> rfl

theorem sourceArchEuclideanLaplacian_right_paths (f : EuclideanSpatial → ℂ)
    (hf : ∀ p, 0 < p 2 → ContDiffAt ℝ (∞ : ℕ∞ω) f p)
    (p : EuclideanSpatial) (hp : 0 < p 2) :
    positiveEuclideanLaplacian f p =
      -(deriv (deriv (fun t => f (euclideanAxisPath p 0 (p 0+p 2*t)))) 0+
        deriv (deriv (fun t => f (euclideanAxisPath p 1 (p 1+p 2*t)))) 0+
        deriv (deriv (fun t => f (euclideanAxisPath p 2 (p 2*Real.exp t)))) 0-
        2*deriv (fun t => f (euclideanAxisPath p 2 (p 2*Real.exp t))) 0) := by
  let A : Fin 3 → ℝ → ℂ := fun j t => f (euclideanAxisPath p j t)
  have hA (j : Fin 3) : ContDiffAt ℝ 2 (A j) (p j) := by
    have hpath : ContDiff ℝ 2 (euclideanAxisPath p j) := by
      rw [show euclideanAxisPath p j = fun t => p+(t-p j)•euclideanCoordinateVector j from
        funext (euclideanAxisPath_affine p j)]
      fun_prop
    have hfp : ContDiffAt ℝ 2 f (euclideanAxisPath p j (p j)) := by
      rw [euclideanAxisPath_self]
      exact (hf p hp).of_le (by simp)
    exact hfp.comp (p j) hpath.contDiffAt
  rw [positiveEuclideanLaplacian_eq_axis f hf p hp,axisLaplacian,Fin.sum_univ_three]
  change -((p 2:ℂ)^2*(deriv (deriv (A 0)) (p 0)+deriv (deriv (A 1)) (p 1)+
      deriv (deriv (A 2)) (p 2))-(p 2:ℂ)*deriv (A 2) (p 2)) =
    -(deriv (deriv (fun t => A 0 (p 0+p 2*t))) 0+
      deriv (deriv (fun t => A 1 (p 1+p 2*t))) 0+
      deriv (deriv (fun t => A 2 (p 2*Real.exp t))) 0-
      2*deriv (fun t => A 2 (p 2*Real.exp t)) 0)
  have hv := deriv_exponential_height (A 2) (p 2) (hA 2)
  rw [deriv2_affine (A 0) (p 0) (p 2) (hA 0),deriv2_affine (A 1) (p 1) (p 2) (hA 1),hv.1,hv.2]
  ring

end
end ArtinMatthews.SourceArchJacquet
