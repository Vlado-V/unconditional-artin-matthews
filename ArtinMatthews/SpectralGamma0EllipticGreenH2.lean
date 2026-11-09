module

public import ArtinMatthews.SpectralGamma0EllipticActualEquation
public import ArtinMatthews.SpectralGamma0EllipticInteriorH2


set_option backward.privateInPublic true
@[expose] public section

/-! Genuine local H² regularity of the actual automorphic Green vector.
The Sobolev graph membership, second-order equation, and L² forcing are all
constructed from the completed automorphic mass-plus-energy problem. -/
noncomputable section
open Set MeasureTheory Filter
open scoped MatrixGroups ContDiff
open OAI.Analysis.PDE.Weak OAI.Analysis.PDE.Variational
namespace ArtinMatthews

variable (φ : SchwartzMap (ℝ × ℝ) ℂ) {A a b : ℝ}
  (ha : 0 < a) (hab : a ≤ b) (hφ : tsupport φ ⊆ spectralPlaneRectangle A a b)
  (r : SL(2, ℤ)) (P : ℂ →L[ℝ] ℝ)

include hab

theorem gamma0EllipticGreen_weakDivergence (N : ℕ) [NeZero N] {Y c d : ℝ}
    (hY : 0 < Y) (hc : Y < c) (hac : a ≤ c)
    (hplateau : ∀ p ∈ spectralEllipticBand (2*(N:ℝ)) c d, φ p = 1)
    (f : Gamma0RegionL2 N) {Ω : Set (Fin 2 → ℝ)}
    (hΩ : Ω ⊆ spectralEllipticCoordinates ⁻¹' spectralEllipticBand (2*(N:ℝ)) c d) :
    WeakDivergenceEquation Ω
      (gamma0EllipticPair φ ha hφ r P N (gamma0WeakSolution N f)).2
      (gamma0EllipticForcing φ ha hφ r P N f) := by
  apply spectralElliptic_weakDivergence_of_second_tests _
    (gamma0EllipticPair_mem_H1Zero φ ha hφ r P N _) _
  intro χ hχ hcχ hs
  simpa only [mul_comm] using gamma0EllipticGreen_second_weak_equation
    φ ha hab hφ r P N hY hc hac hplateau f χ hχ hcχ (hs.trans hΩ)

theorem gamma0Green_localized_gradient_hasWeakDerivative (N : ℕ) [NeZero N]
    {Y c d : ℝ} (hY : 0 < Y) (hc : Y < c) (hac : a ≤ c)
    (hplateau : ∀ p ∈ spectralEllipticBand (2*(N:ℝ)) c d, φ p = 1)
    (f : Gamma0RegionL2 N) {Ω : Set (Fin 2 → ℝ)} (hΩopen : IsOpen Ω)
    (hΩ : Ω ⊆ spectralEllipticCoordinates ⁻¹' spectralEllipticBand (2*(N:ℝ)) c d)
    (η : (Fin 2 → ℝ) → ℝ) (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
    {K L : ℝ} (hK : 0 ≤ K) (hηM : ∀ x, |η x| ≤ 1)
    (hηK : ∀ x, ‖cellGradient η x‖ ≤ K) (hηL : ∀ x, ‖fderiv ℝ η x‖ ≤ L)
    (hsη : tsupport η ⊆ Ω) (j : Fin 2) :
    let p := gamma0EllipticPair φ ha hφ r P N (gamma0WeakSolution N f)
    let q := gamma0EllipticForcing φ ha hφ r P N f
    ∃ g : Lp (CellVectors 1) 2 (volume : Measure (Fin 2 → ℝ)),
      ‖g‖ ≤ Real.sqrt ((‖q‖+2*(K*‖p.2‖))^2 + 4*‖q‖*(K*‖p.2‖)) + L*‖p.2‖ ∧
      HasWeakDirectionalDerivative volume (Pi.single j 1)
        (cutoffL2 η hη.continuous hηM p.2) g :=
  spectralElliptic_laplacian_interior_H2 _
    (gamma0EllipticPair_mem_H1Zero φ ha hφ r P N _) _ hΩopen
    (gamma0EllipticGreen_weakDivergence φ ha hab hφ r P N hY hc hac hplateau f hΩ)
    η hη hcη hK hηM hηK hηL hsη j

end ArtinMatthews
