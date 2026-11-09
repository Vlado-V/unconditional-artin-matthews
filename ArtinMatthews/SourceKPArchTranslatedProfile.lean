module

public import ArtinMatthews.SourceArchSphericalSection
public import OAI.NumberTheory.DirichletL.CubicSieve.TwistedProfiles
public import OAI.NumberTheory.DirichletL.MeanSquare.UnitRows


set_option backward.privateInPublic true
@[expose] public section

/-! The actual spherical section at every complex matrix in ordinary
upper-half-space coordinates, with its smooth profile and positive Laplacian. -/

namespace ArtinMatthews.SourceArchJacquet
open Matrix Matrix.GeneralLinearGroup OAI.CubicEisenstein Filter
open scoped MatrixGroups ContDiff Topology
noncomputable section

def sourceArchTranslatedRow (g : GL (Fin 2) ℂ) : Fin 2 → ℂ := fun i => g 1 i

theorem sourceArchTranslatedRow_ne_zero (g : GL (Fin 2) ℂ) : sourceArchTranslatedRow g ≠ 0 := by
  intro h
  have h₀ : g 1 0 = 0 := congrFun h 0
  have h₁ : g 1 1 = 0 := congrFun h 1
  have hp := sourceArchBottomNorm_pos g
  simp only [sourceArchBottomNorm, h₀, h₁, norm_zero, zero_pow (by decide : 2 ≠ 0), zero_add] at hp
  exact (lt_irrefl 0) hp

theorem sourceArchHeight_right_upperSection (g : GL (Fin 2) ℂ) (z : ℂ) (y : ℝ) (hy : 0 < y) :
    sourceArchHeight (g*(upperSection z y hy : GL (Fin 2) ℂ)) =
      ‖(GeneralLinearGroup.det g : ℂ)‖ * transformedHeight z y (sourceArchTranslatedRow g) := by
  have he : sourceArchBottomNorm (g*(upperSection z y hy : GL (Fin 2) ℂ)) =
      rowEnergy (rowOperator (upperSection z y hy) (sourceArchTranslatedRow g)) := by
    rfl
  rw [sourceArchHeight, map_mul, SpecialLinearGroup.coeToGL_det, mul_one, he,
    rowEnergy_upperSection]
  unfold transformedHeight
  simp only [div_eq_mul_inv, _root_.mul_inv_rev, inv_inv]

def sourceArchTranslatedProfile (s : ℂ) (g : GL (Fin 2) ℂ) (p : EuclideanSpatial) : ℂ :=
  (‖(GeneralLinearGroup.det g : ℂ)‖ : ℂ)^(2*s+1) *
    spatialHeightPower (2*s+1)
      (Complex.normSq (g 1 0)) ((g 1 0*star (g 1 1)).re)
      (-(g 1 0*star (g 1 1)).im) (Complex.normSq (g 1 1)) (p 0) (p 1) (p 2)

theorem sourceArchTranslatedProfile_eq_section (s : ℂ) (g : GL (Fin 2) ℂ)
    (p : EuclideanSpatial) (hp : 0 < p 2) :
    sourceArchSphericalGL s (g*(upperSection ((p 0 : ℂ)+(p 1 : ℂ)*Complex.I) (p 2) hp :
      GL (Fin 2) ℂ)) = sourceArchTranslatedProfile s g p := by
  have ht : 0 < transformedHeight ((p 0 : ℂ)+(p 1 : ℂ)*Complex.I) (p 2)
      (sourceArchTranslatedRow g) :=
    div_pos hp (heightDenominator_pos _ _ hp _ (sourceArchTranslatedRow_ne_zero g))
  rw [sourceArchSphericalGL, sourceArchHeight_right_upperSection, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (norm_nonneg _) ht.le]
  change _ * actualHeightPower (2*s+1) (sourceArchTranslatedRow g) (p 0) (p 1) (p 2) = _
  rw [actualHeightPower_eq_spatial _ _ (sourceArchTranslatedRow_ne_zero g) _ _ _ hp]
  rfl

theorem sourceArchTranslatedProfile_contDiffAt (s : ℂ) (g : GL (Fin 2) ℂ)
    (p : EuclideanSpatial) (hp : 0 < p 2) :
    ContDiffAt (ℝ) (∞ : ℕ∞ω) (sourceArchTranslatedProfile s g) p := by
  have hQ : ContDiff (ℝ) (∞ : ℕ∞ω) (fun q : EuclideanSpatial =>
      quadraticHeightDenominator (Complex.normSq (g 1 0)) ((g 1 0*star (g 1 1)).re)
        (-(g 1 0*star (g 1 1)).im) (Complex.normSq (g 1 1)) (q 0) (q 1) (q 2)) := by
    unfold quadraticHeightDenominator
    fun_prop
  have hQpos : 0 < quadraticHeightDenominator (Complex.normSq (g 1 0))
      ((g 1 0*star (g 1 1)).re) (-(g 1 0*star (g 1 1)).im)
      (Complex.normSq (g 1 1)) (p 0) (p 1) (p 2) := by
    have h := heightDenominator_pos ((p 0 : ℂ)+(p 1 : ℂ)*Complex.I) (p 2) hp
      (sourceArchTranslatedRow g) (sourceArchTranslatedRow_ne_zero g)
    rw [heightDenominator_eq_quadratic] at h
    simpa only [sourceArchTranslatedRow] using h
  have hy : ContDiffAt (ℝ) (∞ : ℕ∞ω) (fun q : EuclideanSpatial => q 2) p := by fun_prop
  unfold sourceArchTranslatedProfile spatialHeightPower logRatioPower
  exact contDiffAt_const.mul
    (contDiffAt_const.mul (Complex.ofRealCLM.contDiff.contDiffAt.comp p
      ((hy.log hp.ne').sub (hQ.contDiffAt.log hQpos.ne')))).cexp

theorem sourceArchTranslatedProfile_laplacian (s : ℂ) (g : GL (Fin 2) ℂ)
    (p : EuclideanSpatial) (hp : 0 < p 2) :
    positiveEuclideanLaplacian (sourceArchTranslatedProfile s g) p =
      (1-4*s^2)*sourceArchTranslatedProfile s g p := by
  rw [positiveEuclideanLaplacian_eq_axis _ (sourceArchTranslatedProfile_contDiffAt s g) p hp]
  change -axisLaplacian (fun q : SpatialCoordinates =>
    (‖(GeneralLinearGroup.det g : ℂ)‖ : ℂ)^(2*s+1) *
      spatialHeightPower (2*s+1) (Complex.normSq (g 1 0)) ((g 1 0*star (g 1 1)).re)
        (-(g 1 0*star (g 1 1)).im) (Complex.normSq (g 1 1)) (q 0) (q 1) (q 2)) p.ofLp = _
  rw [axisLaplacian_const_mul, axisLaplacian_eq_hyperbolicLaplacian,
    spatialHeightPower_eigenfunction (2*s+1) _ _ _ _ _ _ _
      (complex_row_quadratic_relation _ _) hp.ne']
  · unfold sourceArchTranslatedProfile
    ring
  · have h := (heightDenominator_pos ((p 0 : ℂ)+(p 1 : ℂ)*Complex.I) (p 2) hp
      (sourceArchTranslatedRow g) (sourceArchTranslatedRow_ne_zero g)).ne'
    rw [heightDenominator_eq_quadratic] at h
    simpa only [sourceArchTranslatedRow] using h

def sourceArchTranslatedSectionChart (s : ℂ) (g : GL (Fin 2) ℂ) (p : EuclideanSpatial) : ℂ :=
  if hp : 0 < p 2 then sourceArchSphericalGL s
    (g*(upperSection ((p 0 : ℂ)+(p 1 : ℂ)*Complex.I) (p 2) hp : GL (Fin 2) ℂ)) else 0

theorem sourceArchTranslatedSectionChart_eventually_profile (s : ℂ) (g : GL (Fin 2) ℂ)
    (p : EuclideanSpatial) (hp : 0 < p 2) :
    sourceArchTranslatedSectionChart s g =ᶠ[𝓝 p] sourceArchTranslatedProfile s g := by
  have hpos : ∀ᶠ q : EuclideanSpatial in 𝓝 p, 0 < q 2 :=
    (show ContinuousAt (fun q : EuclideanSpatial => q 2) p by fun_prop).eventually_const_lt hp
  filter_upwards [hpos] with q hq
  rw [sourceArchTranslatedSectionChart, dite_eq_left hq]
  exact sourceArchTranslatedProfile_eq_section s g q hq

theorem sourceArchTranslatedSectionChart_contDiffAt (s : ℂ) (g : GL (Fin 2) ℂ)
    (p : EuclideanSpatial) (hp : 0 < p 2) :
    ContDiffAt (ℝ) (∞ : ℕ∞ω) (sourceArchTranslatedSectionChart s g) p :=
  (sourceArchTranslatedProfile_contDiffAt s g p hp).congr_of_eventuallyEq
    (sourceArchTranslatedSectionChart_eventually_profile s g p hp)

theorem sourceArchTranslatedSectionChart_laplacian (s : ℂ) (g : GL (Fin 2) ℂ)
    (p : EuclideanSpatial) (hp : 0 < p 2) :
    positiveEuclideanLaplacian (sourceArchTranslatedSectionChart s g) p =
      (1-4*s^2)*sourceArchTranslatedSectionChart s g p := by
  have he := sourceArchTranslatedSectionChart_eventually_profile s g p hp
  rw [positiveEuclideanLaplacian_congr _ _ p he,
    sourceArchTranslatedProfile_laplacian s g p hp, he.eq_of_nhds]

end
end ArtinMatthews.SourceArchJacquet
