module

public import ArtinMatthews.SpectralPeterssonUniform
public import ArtinMatthews.SpectralPeterssonPoincareAction
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion


set_option backward.privateInPublic true
@[expose] public section

/-! Holomorphicity of the actual Poincare sum on the upper half plane
and its literal period one in every normalized cusp chart. -/

noncomputable section
open Set Filter Matrix UpperHalfPlane
open scoped MatrixGroups UpperHalfPlane Manifold

namespace ArtinMatthews

theorem spectralHolomorphicSeedSlash_differentiableOn (k m : ℕ) (G : SL(2, ℝ)) :
    DifferentiableOn ℂ
      (spectralHolomorphicSlash k G (spectralHolomorphicCuspSeed m) ∘ ofComplex)
      upperHalfPlaneSet := by
  let A : ℂ := G 0 0
  let B : ℂ := G 0 1
  let C : ℂ := G 1 0
  let D : ℂ := G 1 1
  let u : ℂ := 2*(Real.pi : ℂ)*Complex.I*(m : ℂ)
  let P (z : ℂ) := Complex.exp (u*((A*z+B)/(C*z+D)))/(C*z+D)^k
  have hD (z : ℂ) (hz : z ∈ upperHalfPlaneSet) : C*z+D ≠ 0 := by
    have h := UpperHalfPlane.denom_ne_zero (Matrix.SpecialLinearGroup.mapGL ℝ G)
      (⟨z,hz⟩ : UpperHalfPlane)
    simpa [UpperHalfPlane.denom,C,D] using h
  have hN : Differentiable ℂ (fun z : ℂ => A*z+B) := by fun_prop
  have hL : Differentiable ℂ (fun z : ℂ => C*z+D) := by fun_prop
  have hQ := hN.differentiableOn.div hL.differentiableOn hD
  have hU : DifferentiableOn ℂ (fun _ : ℂ => u) upperHalfPlaneSet := differentiableOn_const u
  have hExp : DifferentiableOn ℂ (fun z : ℂ => Complex.exp (u*((A*z+B)/(C*z+D)))) upperHalfPlaneSet :=
    Complex.differentiable_exp.comp_differentiableOn (hU.mul hQ)
  have hP : DifferentiableOn ℂ P upperHalfPlaneSet :=
    hExp.div (hL.differentiableOn.pow k) (fun z hz => pow_ne_zero _ (hD z hz))
  refine hP.congr ?_
  intro z hz
  rw [Function.comp_apply,ofComplex_apply_of_im_pos hz,spectralHolomorphicSlash_apply,
    spectralHolomorphicCuspSeed,UpperHalfPlane.coe_specialLinearGroup_apply]
  simp only [Algebra.algebraMap_self_apply]
  rfl

theorem gamma0PeterssonPoincareChart_mdifferentiable (N : ℕ) [NeZero N] (b a : SL(2, ℤ))
    (k m : ℕ) (hk : 3 ≤ k) : MDiff (gamma0PeterssonPoincareChart N b a k m) := by
  let P := gamma0PeterssonPoincareChart N b a k m
  let F (s : Finset (Gamma0PeterssonPositiveRow N b a)) (z : UpperHalfPlane) :=
    ∑ p ∈ s, gamma0PeterssonSignedSummand N b a k m p.val z
  have hL : TendstoLocallyUniformlyOn (fun s => ↑ₕ(F s)) (↑ₕP) atTop upperHalfPlaneSet := by
    rw [← range_coe,← image_univ]
    apply TendstoLocallyUniformlyOn.comp (s := ⊤) _ _ _ (OpenPartialHomeomorph.continuousOn_symm _)
    · simp only [Set.top_eq_univ,tendstoLocallyUniformlyOn_univ]
      exact gamma0PeterssonPoincareChart_locallyUniformly N b a k m hk
    · intro z _
      exact Set.mem_univ _
  have hD : ∀ᶠ s in atTop, DifferentiableOn ℂ (↑ₕ(F s)) upperHalfPlaneSet := by
    apply Eventually.of_forall
    intro s
    change DifferentiableOn ℂ (fun z => ∑ p ∈ s,
      gamma0PeterssonSignedSummand N b a k m p.val (ofComplex z)) upperHalfPlaneSet
    classical
    induction s using Finset.induction_on with
    | empty => simpa only [Finset.sum_empty] using (differentiableOn_const (0 : ℂ))
    | @insert p s hp hs =>
      simp only [Finset.sum_insert hp]
      exact (spectralHolomorphicSeedSlash_differentiableOn k m _).add hs
  exact UpperHalfPlane.mdifferentiable_iff.mpr (hL.differentiableOn hD isOpen_upperHalfPlaneSet)

theorem gamma0PeterssonPoincareChart_periodic (N : ℕ) [NeZero N] (b a : SL(2, ℤ))
    (k m : ℕ) (hk : 3 ≤ k) (hEven : Even k) :
    Function.Periodic (gamma0PeterssonPoincareChart N b a k m ∘ ofComplex) (1 : ℂ) := by
  have h : Function.Periodic (gamma0PeterssonPoincareChart N b a k m ∘ ofComplex) ((1 : ℝ) : ℂ) := by
    apply UpperHalfPlane.periodic_comp_ofComplex
    intro z
    have hz : (1 : ℝ) +ᵥ z = realTranslation 1 • z := by
      apply UpperHalfPlane.ext
      rw [UpperHalfPlane.coe_vadd,realTranslation_coe_smul,add_comm]
    rw [hz]
    have hp := congrFun (gamma0PeterssonPoincareChart_slash_translation N b a k m hk hEven 1) z
    rw [spectralHolomorphicSlash_apply] at hp
    simpa [realTranslation] using hp
  simpa only [Complex.ofReal_one] using h

end ArtinMatthews
