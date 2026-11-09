module

public import ArtinMatthews.SpectralGamma0EllipticInteriorH2


set_option backward.privateInPublic true
@[expose] public section

/-! A linear version of the genuine quantitative interior H2 estimate. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff
open OAI.Analysis.PDE.Weak OAI.Analysis.PDE.Variational
namespace ArtinMatthews

theorem spectralElliptic_laplacian_interior_H2_linear_bound
    (p : H1Pair 1) (hp : p ∈ H1Zero (univ : Set (Fin 2 → ℝ)))
    (f : Lp ℝ 2 (volume : Measure (Fin 2 → ℝ))) {Ω : Set (Fin 2 → ℝ)}
    (hΩ : IsOpen Ω) (hweak : WeakDivergenceEquation Ω p.2 f)
    (η : (Fin 2 → ℝ) → ℝ) (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
    {K L : ℝ} (hK : 0 ≤ K) (_hL : 0 ≤ L) (hηM : ∀ x, |η x| ≤ 1)
    (hηK : ∀ x, ‖cellGradient η x‖ ≤ K) (hηL : ∀ x, ‖fderiv ℝ η x‖ ≤ L)
    (hsη : tsupport η ⊆ Ω) (j : Fin 2) :
    ∃ g : Lp (CellVectors 1) 2 (volume : Measure (Fin 2 → ℝ)),
      ‖g‖ ≤ ‖f‖+(4*K+L)*‖p.2‖ ∧
      HasWeakDirectionalDerivative volume (Pi.single j 1)
        (cutoffL2 η hη.continuous hηM p.2) g := by
  obtain ⟨g,hg,hd⟩ := spectralElliptic_laplacian_interior_H2 p hp f hΩ hweak
    η hη hcη hK hηM hηK hηL hsη j
  refine ⟨g,hg.trans ?_,hd⟩
  have hroot : Real.sqrt ((‖f‖+2*(K*‖p.2‖))^2+4*‖f‖*(K*‖p.2‖)) ≤
      ‖f‖+4*K*‖p.2‖ := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · nlinarith [sq_nonneg (K*‖p.2‖)]
  nlinarith

end ArtinMatthews
