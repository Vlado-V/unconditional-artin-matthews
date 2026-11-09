module

public import OAI.Analysis.PDE.Weak.Elliptic.Classical.Gradient
public import OAI.Analysis.PDE.Weak.Elliptic.Linear


set_option backward.privateInPublic true
@[expose] public section

/-! Identification of quantitative weak derivatives with honest smooth derivatives. -/
noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace
open OAI.Analysis.PDE.Weak OAI.Analysis.PDE.Variational
namespace ArtinMatthews

theorem spectral_weak_scalar_derivative_classical
    {Ω : Set (Fin 2 → ℝ)} (hΩ : IsOpen Ω)
    (f g : Lp ℝ 2 (volume : Measure (Fin 2 → ℝ))) (j : Fin 2)
    (hd : HasWeakDirectionalDerivativeOn volume Ω (Pi.single j 1) f g)
    (u : (Fin 2 → ℝ) → ℝ) (hu : ContDiff ℝ 1 u)
    (heq : ∀ᵐ x ∂volume, x ∈ Ω → f x = u x) :
    ∀ᵐ x ∂volume, x ∈ Ω → g x = fderiv ℝ u x (Pi.single j 1) := by
  let du := fun x => fderiv ℝ u x (Pi.single j 1)
  have hdu : Continuous du := OAI.Analysis.PDE.Green.continuous_directional hu _
  have hlocal : LocallyIntegrableOn (fun x => g x-du x) Ω volume :=
    (((Lp.memLp g).locallyIntegrable (by norm_num)).locallyIntegrableOn Ω).sub
      (hdu.locallyIntegrable.locallyIntegrableOn Ω)
  have hz := hΩ.ae_eq_zero_of_integral_contDiff_smul_eq_zero hlocal ?_
  · filter_upwards [hz] with x hx
    exact fun hxΩ => sub_eq_zero.mp (hx hxΩ)
  intro φ hφ hs hsub
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by simp)
  have hφ2 : MemLp φ 2 volume := hφ.continuous.memLp_of_hasCompactSupport hs
  have hi : Integrable (fun x => φ x*g x) := hφ2.integrable_mul (Lp.memLp g)
  have hj : Integrable (fun x => φ x*du x) :=
    (hφ.continuous.mul hdu).integrable_of_hasCompactSupport hs.mul_right
  have hw := hd φ hφ1 hs hsub
  have hc := OAI.Analysis.PDE.Green.integral_directional_by_parts
    (μ := volume) hφ1 hu hs (Pi.single j 1)
  have he : (∫ x, fderiv ℝ φ x (Pi.single j 1)*f x) =
      ∫ x, fderiv ℝ φ x (Pi.single j 1)*u x := by
    apply integral_congr_ae
    filter_upwards [heq] with x hx
    by_cases hxs : x ∈ tsupport φ
    · rw [hx (hsub hxs)]
    · rw [fderiv_of_notMem_tsupport ℝ hxs]
      simp only [zero_apply,zero_mul]
  simp only [RCLike.inner_apply,conj_trivial] at hw
  rw [he] at hw
  simp only [smul_eq_mul,mul_sub]
  rw [integral_sub hi hj]
  have hw' : (∫ x, φ x*g x) = -(∫ x, u x*fderiv ℝ φ x (Pi.single j 1)) := by
    simpa only [mul_comm] using hw
  have hc' : (∫ x, φ x*du x) = -(∫ x, u x*fderiv ℝ φ x (Pi.single j 1)) := by
    simpa only [du,mul_comm] using hc
  rw [hw',hc',sub_self]

theorem spectral_weak_vector_derivative_classical_component
    (f g : Lp (CellVectors 1) 2 (volume : Measure (Fin 2 → ℝ))) (j k : Fin 2)
    (hd : HasWeakDirectionalDerivative volume (Pi.single j 1) f g)
    (u : (Fin 2 → ℝ) → CellVectors 1) (hu : ContDiff ℝ 1 u)
    (heq : f =ᵐ[volume] u) :
    ∀ᵐ x ∂volume, g x k = fderiv ℝ (fun y => u y k) x (Pi.single j 1) := by
  let L := EuclideanSpace.proj (𝕜 := ℝ) k
  have hs : HasWeakDirectionalDerivativeOn volume univ (Pi.single j 1)
      (L.compLp f) (L.compLp g) := hd.on.map_Lp volume L
  have hu' : ContDiff ℝ 1 (fun x => u x k) := L.contDiff.comp hu
  have heq' : ∀ᵐ x ∂volume, x ∈ (univ : Set (Fin 2 → ℝ)) → L.compLp f x = u x k := by
    filter_upwards [L.coeFn_compLp f,heq] with x hx hy
    exact fun _ => hx.trans (congrArg L hy)
  have he := spectral_weak_scalar_derivative_classical isOpen_univ
    (L.compLp f) (L.compLp g) j hs (fun x => u x k) hu' heq'
  filter_upwards [L.coeFn_compLp g,he] with x hx hy
  exact hx.symm.trans (hy (mem_univ x))

end ArtinMatthews
