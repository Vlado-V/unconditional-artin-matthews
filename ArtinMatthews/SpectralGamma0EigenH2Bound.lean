module

public import ArtinMatthews.SpectralGamma0EigenEnergyBounds
public import ArtinMatthews.SpectralGamma0EigenPotentialBound
public import ArtinMatthews.SpectralEllipticH2LinearBound


set_option backward.privateInPublic true
@[expose] public section

/-! Polynomial local H2 bounds for the normalized actual cuspidal eigenbasis.
The constants precede the spectral index and depend only on the fixed geometry. -/
noncomputable section
open Set MeasureTheory Filter
open scoped MatrixGroups ContDiff
open OAI.Analysis.PDE.Weak OAI.Analysis.PDE.Variational
namespace ArtinMatthews

theorem gamma0FullCuspidalSpectralBasis_local_H2_bound
    (φ : SchwartzMap (ℝ × ℝ) ℂ) {A a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hφ : tsupport φ ⊆ spectralPlaneRectangle A a b)
    (r : SL(2,ℤ)) (L0 : ℂ →L[ℝ] ℝ) (N : ℕ) [NeZero N]
    {Y c d : ℝ} (hY : 0 < Y) (hc : Y < c)
    (hplateau : ∀ p ∈ spectralEllipticBand (2*(N:ℝ)) c d, φ p = 1)
    {Ω : Set (Fin 2 → ℝ)} (hΩ : IsOpen Ω)
    (hΩband : Ω ⊆ spectralEllipticCoordinates ⁻¹' spectralEllipticBand (2*(N:ℝ)) c d)
    (η : (Fin 2 → ℝ) → ℝ) (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
    {K L : ℝ} (hK : 0 ≤ K) (hL : 0 ≤ L) (hηM : ∀ x, |η x| ≤ 1)
    (hηK : ∀ x, ‖cellGradient η x‖ ≤ K) (hηL : ∀ x, ‖fderiv ℝ η x‖ ≤ L)
    (hsη : tsupport η ⊆ Ω) :
    ∃ C : ℝ, 0 < C ∧ ∀ (i : Gamma0AllHeightSpectralIndex N) (j : Fin 2),
      ∃ g : Lp (CellVectors 1) 2 (volume : Measure (Fin 2 → ℝ)),
        ‖g‖ ≤ C*(1+gamma0AllHeightGradientSpectralValue N i) ∧
        HasWeakDirectionalDerivative volume (Pi.single j 1)
          (cutoffL2 η hη.continuous hηM
            (gamma0EllipticPair φ ha hφ r L0 N (gamma0AllHeightSpectralEnergy N i).val).2) g := by
  obtain ⟨M,hM,hMB⟩ := spectralEllipticPotentialCoefficient_uniform_linear_bound φ ha hφ
  let R := ‖gamma0EllipticMass φ ha hφ r L0 N‖
  let P := ‖gamma0EllipticPair φ ha hφ r L0 N‖
  have hR : 0 ≤ R := ContinuousLinearMap.opNorm_nonneg _
  have hP : 0 ≤ P := ContinuousLinearMap.opNorm_nonneg _
  refine ⟨M*R+(4*K+L)*P+1,by positivity,?_⟩
  intro i j
  let lam := gamma0AllHeightGradientSpectralValue N i
  have hlam : 0 ≤ lam := gamma0AllHeightGradientSpectralValue_nonneg N i
  let p := gamma0EllipticPair φ ha hφ r L0 N (gamma0AllHeightSpectralEnergy N i).val
  let B := spectralEllipticPotentialCoefficient φ ha hφ lam
  have hB := spectralEllipticPotentialCoefficient_smoothBounded φ ha hφ lam
  have hBM : ∀ x, ‖B x‖ ≤ M*|lam| := hMB lam
  let f := fieldMultiplierCLM B hB.1.continuous.aestronglyMeasurable
    (Eventually.of_forall hBM) p.1
  have he : WeakDivergenceEquation Ω p.2 f :=
    gamma0EllipticEigen_weakDivergence φ ha hab hφ r L0 N i hY hc hplateau hΩband hBM
  obtain ⟨g,hg,hd⟩ := spectralElliptic_laplacian_interior_H2_linear_bound p
    (gamma0EllipticPair_mem_H1Zero φ ha hφ r L0 N _) f hΩ he η hη hcη hK hL
    hηM hηK hηL hsη j
  have hp1 : ‖p.1‖ ≤ R := gamma0EllipticEigenPair_mass_norm_le φ ha hab hφ r L0 N i
  have hp2 : ‖p.2‖ ≤ P*(1+lam) :=
    (show ‖p.2‖ ≤ ‖p‖ from by rw [Prod.norm_def]; exact le_max_right _ _).trans
      (gamma0EllipticEigenPair_norm_le φ ha hφ r L0 N i)
  have hf0 : ‖f‖ ≤ (M*|lam|)*‖p.1‖ :=
    norm_fieldMultiplier_le B hB.1.continuous.aestronglyMeasurable
      (Eventually.of_forall hBM) p.1
  have hf : ‖f‖ ≤ (M*R)*(1+lam) := by
    calc
      ‖f‖ ≤ (M*|lam|)*R := hf0.trans
        (mul_le_mul_of_nonneg_left hp1 (mul_nonneg hM.le (abs_nonneg _)))
      _ = (M*R)*lam := by rw [abs_of_nonneg hlam]; ring
      _ ≤ (M*R)*(1+lam) := mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hM.le hR)
  refine ⟨g,hg.trans ?_,hd⟩
  calc
    ‖f‖+(4*K+L)*‖p.2‖ ≤ (M*R)*(1+lam)+(4*K+L)*(P*(1+lam)) :=
      add_le_add hf (mul_le_mul_of_nonneg_left hp2 (by positivity))
    _ ≤ (M*R+(4*K+L)*P+1)*(1+lam) := by nlinarith

end ArtinMatthews
