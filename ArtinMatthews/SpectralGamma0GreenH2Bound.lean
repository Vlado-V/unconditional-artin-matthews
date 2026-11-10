module

public import ArtinMatthews.SpectralGamma0EllipticBand
public import ArtinMatthews.SpectralGamma0EllipticCompletion
public import ArtinMatthews.SpectralGamma0WeakInverse
public import OAI.Analysis.PDE.Weak.Elliptic.Cutoff
public import OAI.Analysis.PDE.Weak.Elliptic.Derivative
public import ArtinMatthews.SpectralEllipticH2LinearBound
public import ArtinMatthews.SpectralGamma0EllipticGreenH2
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Uniform local H2 smoothing by the actual bounded automorphic Green operator. -/
noncomputable section
open Set MeasureTheory Filter
open scoped MatrixGroups ContDiff
open OAI.Analysis.PDE.Weak OAI.Analysis.PDE.Variational
namespace ArtinMatthews

theorem gamma0Green_local_H2_bound
    (φ : SchwartzMap (ℝ × ℝ) ℂ) {A a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hφ : tsupport φ ⊆ spectralPlaneRectangle A a b)
    (r : SL(2,ℤ)) (L0 : ℂ →L[ℝ] ℝ) (N : ℕ) [NeZero N]
    {Y c d : ℝ} (hY : 0 < Y) (hc : Y < c) (hac : a ≤ c)
    (hplateau : ∀ p ∈ spectralEllipticBand (2*(N:ℝ)) c d, φ p = 1)
    {Ω : Set (Fin 2 → ℝ)} (hΩ : IsOpen Ω)
    (hΩband : Ω ⊆ spectralEllipticCoordinates ⁻¹' spectralEllipticBand (2*(N:ℝ)) c d)
    (η : (Fin 2 → ℝ) → ℝ) (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
    {K L : ℝ} (hK : 0 ≤ K) (hL : 0 ≤ L) (hηM : ∀ x, |η x| ≤ 1)
    (hηK : ∀ x, ‖cellGradient η x‖ ≤ K) (hηL : ∀ x, ‖fderiv ℝ η x‖ ≤ L)
    (hsη : tsupport η ⊆ Ω) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : Gamma0RegionL2 N) (j : Fin 2),
      ∃ g : Lp (CellVectors 1) 2 (volume : Measure (Fin 2 → ℝ)),
        ‖g‖ ≤ C*‖f‖ ∧
        HasWeakDirectionalDerivative volume (Pi.single j 1)
          (cutoffL2 η hη.continuous hηM
            (gamma0EllipticPair φ ha hφ r L0 N (gamma0WeakSolution N f)).2) g := by
  let P := ‖gamma0EllipticPair φ ha hφ r L0 N‖
  let M := ‖gamma0EllipticMass φ ha hφ r L0 N‖
  have hP : 0 ≤ P := ContinuousLinearMap.opNorm_nonneg _
  have hM : 0 ≤ M := ContinuousLinearMap.opNorm_nonneg _
  refine ⟨(2/a^2)*M+(4*K+L)*P+1,by positivity,?_⟩
  intro f j
  let p := gamma0EllipticPair φ ha hφ r L0 N (gamma0WeakSolution N f)
  let q := gamma0EllipticForcing φ ha hφ r L0 N f
  have hpair : ‖p‖ ≤ P*‖f‖ :=
    ((gamma0EllipticPair φ ha hφ r L0 N).le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (gamma0WeakSolution_bound N f) hP)
  have hp2 : ‖p.2‖ ≤ P*‖f‖ :=
    (show ‖p.2‖ ≤ ‖p‖ from by rw [Prod.norm_def]; exact le_max_right _ _).trans hpair
  have hGf : ‖gamma0Green N f‖ ≤ ‖f‖ := by
    have h := ((gamma0Green N).le_opNorm f).trans
      (mul_le_mul_of_nonneg_right (gamma0Green_norm N) (norm_nonneg f))
    simpa only [one_mul] using h
  have hsource : ‖f-gamma0Green N f‖ ≤ 2*‖f‖ := by
    have h := (norm_sub_le f (gamma0Green N f)).trans (add_le_add le_rfl hGf)
    linarith
  have hq : ‖q‖ ≤ ((2/a^2)*M)*‖f‖ := by
    calc
      ‖q‖ ≤ (1/a^2)*‖gamma0EllipticMass φ ha hφ r L0 N (f-gamma0Green N f)‖ :=
        gamma0EllipticForcing_norm_le φ ha hφ r L0 N f
      _ ≤ (1/a^2)*(M*‖f-gamma0Green N f‖) :=
        mul_le_mul_of_nonneg_left ((gamma0EllipticMass φ ha hφ r L0 N).le_opNorm _) (by positivity)
      _ ≤ (1/a^2)*(M*(2*‖f‖)) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hsource hM) (by positivity)
      _ = _ := by ring
  obtain ⟨g,hg,hd⟩ := spectralElliptic_laplacian_interior_H2_linear_bound p
    (gamma0EllipticPair_mem_H1Zero φ ha hφ r L0 N _) q hΩ
    (gamma0EllipticGreen_weakDivergence φ ha hab hφ r L0 N hY hc hac hplateau f hΩband)
    η hη hcη hK hL hηM hηK hηL hsη j
  refine ⟨g,hg.trans ?_,hd⟩
  calc
    ‖q‖+(4*K+L)*‖p.2‖ ≤ ((2/a^2)*M)*‖f‖+(4*K+L)*(P*‖f‖) :=
      add_le_add hq (mul_le_mul_of_nonneg_left hp2 (by positivity))
    _ ≤ ((2/a^2)*M+(4*K+L)*P+1)*‖f‖ := by nlinarith [norm_nonneg f]

end ArtinMatthews
