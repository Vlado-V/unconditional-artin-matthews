module

public import ArtinMatthews.SpectralWeylPlanarCoordinates
public import Mathlib.MeasureTheory.Measure.Lebesgue.Integral


set_option backward.privateInPublic true
@[expose] public section

/-! The two horizontal signs combine to the actual cosine orbital kernel. -/

noncomputable section
open Set MeasureTheory Filter

namespace ArtinMatthews

theorem integrable_complex_star {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {F : X → ℂ} (hF : Integrable F μ) : Integrable (fun x => star (F x)) μ :=
  Complex.conjCLE.toContinuousLinearMap.integrable_comp hF

theorem integral_reflection_pair (F : ℝ → ℂ) (hF : Integrable F)
    (hs : ∀ x, F (-x) = star (F x)) :
    (∫ x : ℝ, F x) = ∫ x in Ioi (0 : ℝ), star (F x) + F x := by
  have hneg : (∫ x in Iic (0 : ℝ), F x) = ∫ x in Ioi (0 : ℝ), star (F x) := by
    have h := integral_comp_neg_Ioi (0 : ℝ) F
    simp only [neg_zero] at h
    exact h.symm.trans (integral_congr_ae (Eventually.of_forall hs))
  have hp : IntegrableOn F (Ioi (0 : ℝ)) := hF.restrict
  rw [← intervalIntegral.integral_Iic_add_Ioi hF.restrict hp,hneg,
    ← integral_add (integrable_complex_star hp) hp]

theorem atkinPhase_add_conj (x : ℝ) :
    star (atkinPhase x) + atkinPhase x = 2*(Real.cos (2*Real.pi*x) : ℂ) := by
  have hp : 2*(Real.pi : ℂ)*Complex.I*(x : ℂ) = ((2*Real.pi*x : ℝ) : ℂ)*Complex.I := by
    push_cast
    ring
  have hn : 2*(Real.pi : ℂ)*Complex.I*((-x : ℝ) : ℂ) = -((2*Real.pi*x : ℝ) : ℂ)*Complex.I := by
    push_cast
    ring
  rw [atkinPhase_conj]
  unfold atkinPhase
  rw [hp,hn,Complex.ofReal_cos,Complex.two_cos]
  exact add_comm _ _

def weylCosineDensity (N : ℕ) (m n : ℤ) (ρ η : ℝ → ℝ)
    (c : ℝ) (p : ℝ × ℝ) : ℂ :=
  (weylPlanarAmplitude ρ η c p.1 p.2 / p.2^2 *
    Real.cos (2*Real.pi*weylPlanarPhase N m n c p.1 p.2) : ℝ)

theorem weylPlanarDensity_reflection (N : ℕ) (m n : ℤ) (ρ η : ℝ → ℝ)
    (c x y : ℝ) :
    weylPlanarDensity N m n ρ η c (-x,y) = star (weylPlanarDensity N m n ρ η c (x,y)) := by
  have he : weylPlanarPhase N m n c (-x) y = -weylPlanarPhase N m n c x y := by
    unfold weylPlanarPhase
    rw [neg_sq]
    ring
  have hs (a : ℝ) : star (a : ℂ) = (a : ℂ) := by simp
  dsimp only [weylPlanarDensity,weylPlanarIntegrand,weylPlanarAmplitude]
  rw [neg_sq,he]
  simp only [Complex.real_smul,star_mul,hs,← atkinPhase_conj]
  ring

theorem weylPlanarDensity_reflection_pair (N : ℕ) (m n : ℤ) (ρ η : ℝ → ℝ)
    (c x y : ℝ) :
    star (weylPlanarDensity N m n ρ η c (x,y)) + weylPlanarDensity N m n ρ η c (x,y) =
      2*weylCosineDensity N m n ρ η c (x,y) := by
  have hs (a : ℝ) : star (a : ℂ) = (a : ℂ) := by simp
  dsimp only [weylPlanarDensity,weylPlanarIntegrand,weylCosineDensity]
  simp only [Complex.real_smul,star_mul,hs]
  calc
    _ = (((y^2)⁻¹ : ℝ) : ℂ) * (weylPlanarAmplitude ρ η c x y : ℂ) *
        (star (atkinPhase (weylPlanarPhase N m n c x y)) +
          atkinPhase (weylPlanarPhase N m n c x y)) := by ring
    _ = _ := by
      rw [atkinPhase_add_conj]
      push_cast
      ring

theorem weylPlanar_horizontal_cosine (N : ℕ) (m n : ℤ) (ρ η : ℝ → ℝ)
    (c y : ℝ) (hI : Integrable (fun x : ℝ => weylPlanarDensity N m n ρ η c (x,y))) :
    (∫ x : ℝ, weylPlanarDensity N m n ρ η c (x,y)) =
      2 * ∫ x in Ioi (0 : ℝ), weylCosineDensity N m n ρ η c (x,y) := by
  rw [integral_reflection_pair _ hI (fun x => weylPlanarDensity_reflection N m n ρ η c x y)]
  simp_rw [weylPlanarDensity_reflection_pair]
  rw [integral_const_mul]

theorem cuspWeylOrbitalKernel_horizontal (N : ℕ) (m n : ℤ) (ρ η : ℝ → ℝ)
    (c : ℝ) (hc : c ≠ 0)
    (hI : IntegrableOn (weylPlanarDensity N m n ρ η c) {p : ℝ × ℝ | 0 < p.2}) :
    cuspWeylOrbitalKernel N m n ρ η c hc =
      ∫ y in Ioi (0 : ℝ), ∫ x : ℝ, weylPlanarDensity N m n ρ η c (x,y) := by
  rw [cuspWeylOrbitalKernel_coordinates]
  have hs : {p : ℝ × ℝ | 0 < p.2} = (univ : Set ℝ) ×ˢ Ioi (0 : ℝ) := by ext p; simp
  rw [hs] at hI ⊢
  change Integrable _ ((volume.prod volume).restrict (univ ×ˢ Ioi (0 : ℝ))) at hI
  rw [← Measure.prod_restrict,Measure.restrict_univ] at hI
  change (∫ p, _ ∂(volume.prod volume).restrict (univ ×ˢ Ioi (0 : ℝ))) = _
  rw [← Measure.prod_restrict,Measure.restrict_univ,integral_prod_symm _ hI]

theorem cuspWeylOrbitalKernel_cosine (N : ℕ) (m n : ℤ) (ρ η : ℝ → ℝ)
    (c : ℝ) (hc : c ≠ 0)
    (hI : IntegrableOn (weylPlanarDensity N m n ρ η c) {p : ℝ × ℝ | 0 < p.2}) :
    cuspWeylOrbitalKernel N m n ρ η c hc =
      2 * ∫ y in Ioi (0 : ℝ), ∫ x in Ioi (0 : ℝ), weylCosineDensity N m n ρ η c (x,y) := by
  rw [cuspWeylOrbitalKernel_horizontal N m n ρ η c hc hI,← integral_const_mul]
  have hs : {p : ℝ × ℝ | 0 < p.2} = (univ : Set ℝ) ×ˢ Ioi (0 : ℝ) := by ext p; simp
  rw [hs] at hI
  change Integrable _ ((volume.prod volume).restrict (univ ×ˢ Ioi (0 : ℝ))) at hI
  rw [← Measure.prod_restrict,Measure.restrict_univ] at hI
  apply integral_congr_ae
  filter_upwards [hI.prod_left_ae] with y hy
  exact weylPlanar_horizontal_cosine N m n ρ η c y hy

end ArtinMatthews
