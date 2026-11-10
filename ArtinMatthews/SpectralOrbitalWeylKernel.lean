module

public import ArtinMatthews.SpectralOrbitalIntegral
public import ArtinMatthews.SpectralCuspBruhatKernel
public import ArtinMatthews.SpectralCuspPeriodKloosterman
public import ArtinMatthews.SpectralCuspTwoCellFourier
public import ArtinMatthews.SpectralFourierBruhatKernel
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Metric
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The residue-independent Weyl orbital integral is derived from the
unwindowed actual kernel by invariant translation, with its exact phase. -/

noncomputable section
open Set MeasureTheory Filter Matrix
open scoped MatrixGroups ContDiff InnerProductSpace

namespace ArtinMatthews

theorem cuspFourierWave_realTranslation (N : ℕ) (n : ℤ) (ρ : ℝ → ℝ)
    (x : ℝ) (z : UpperHalfPlane) :
    cuspFourierWave N n ρ (realTranslation x • z) =
      star (cuspFourierPhase (N : ℝ) n x) • cuspFourierWave N n ρ z := by
  unfold cuspFourierWave
  rw [realTranslation_re_smul,realTranslation_im_smul,cuspFourierPhase_add]
  simp only [star_mul,smul_eq_mul]
  ring

def cuspWeylOrbitalIntegrand (N : ℕ) (m n : ℤ) (ρ η : ℝ → ℝ)
    (c : ℝ) (hc : c ≠ 0) (z : UpperHalfPlane) : ℂ :=
  inner ℂ (cuspFourierWave N m ρ z) (cuspFourierWave N n η (realWeylMatrix c hc • z))

def cuspWeylOrbitalKernel (N : ℕ) (m n : ℤ) (ρ η : ℝ → ℝ) (c : ℝ) (hc : c ≠ 0) : ℂ :=
  ∫ z : UpperHalfPlane, cuspWeylOrbitalIntegrand N m n ρ η c hc z

theorem cuspUnwindowedOrbitalIntegrand_bruhat (N : ℕ) (m n : ℤ) (ρ η : ℝ → ℝ)
    (R : SL(2, ℤ)) {c : ℤ} (hc : c ≠ 0) (hR : R 1 0 = c) (z : UpperHalfPlane) :
    cuspUnwindowedOrbitalIntegrand N m n ρ η R
      (realTranslation (-((R 1 1 : ℝ)/c)) • z) =
      cuspGeometricPhase N m n c R * cuspWeylOrbitalIntegrand N m n ρ η
        (c : ℝ) (by exact_mod_cast hc) z := by
  let α : ℝ := (R 0 0 : ℝ)/c
  let β : ℝ := (R 1 1 : ℝ)/c
  have hact : R • (realTranslation (-β) • z) =
      realTranslation α • (realWeylMatrix (c : ℝ) (by exact_mod_cast hc) • z) := by
    rw [← atkinRealMap_smul,integer_matrix_bruhat R hc hR]
    change (realTranslation α * realWeylMatrix (c : ℝ) (by exact_mod_cast hc) * realTranslation β) •
      (realTranslation (-β) • z) = _
    rw [mul_smul,mul_smul,← mul_smul (realTranslation β),realTranslation_mul,
      add_neg_cancel,realTranslation_zero,one_smul]
  have hp : cuspFourierPhase (N : ℝ) m (-β) * star (cuspFourierPhase (N : ℝ) n α) =
      cuspGeometricPhase N m n c R := by
    rw [cuspFourierPhase_bruhat_factor]
    unfold cuspGeometricPhase α β
    congr 1
    ring
  unfold cuspUnwindowedOrbitalIntegrand cuspWeylOrbitalIntegrand
  change inner ℂ (cuspFourierWave N m ρ (realTranslation (-β) • z))
    (cuspFourierWave N n η (R • (realTranslation (-β) • z))) = _
  rw [hact,cuspFourierWave_realTranslation,cuspFourierWave_realTranslation]
  calc
    _ = (cuspFourierPhase (N : ℝ) m (-β) * star (cuspFourierPhase (N : ℝ) n α)) *
        inner ℂ (cuspFourierWave N m ρ z)
          (cuspFourierWave N n η (realWeylMatrix (c : ℝ) (by exact_mod_cast hc) • z)) := by
      simp only [inner_smul_left,inner_smul_right,starRingEnd_apply,star_star]
      ring
    _ = _ := by rw [hp]

theorem cuspUnwindowedOrbitalKernel_bruhat (N : ℕ) (m n : ℤ) (ρ η : ℝ → ℝ)
    (R : SL(2, ℤ)) {c : ℤ} (hc : c ≠ 0) (hR : R 1 0 = c) :
    cuspUnwindowedOrbitalKernel N m n ρ η R = cuspGeometricPhase N m n c R *
      cuspWeylOrbitalKernel N m n ρ η (c : ℝ) (by exact_mod_cast hc) := by
  let g := realTranslation (-((R 1 1 : ℝ)/c))
  have he := (realTranslation_measurePreserving (-((R 1 1 : ℝ)/c))).integral_comp
    (show MeasurableEmbedding (fun z : UpperHalfPlane => g • z) from
      measurableEmbedding_const_smul g) (cuspUnwindowedOrbitalIntegrand N m n ρ η R)
  unfold cuspUnwindowedOrbitalKernel cuspWeylOrbitalKernel
  rw [← he,← integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall (cuspUnwindowedOrbitalIntegrand_bruhat N m n ρ η R hc hR)

theorem cuspWeylOrbitalIntegrand_integrable_of_matrix (N : ℕ) [NeZero N]
    (m n : ℤ) (ρ η : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hη : ContDiff ℝ ∞ η)
    (hcρ : HasCompactSupport ρ) (hcη : HasCompactSupport η)
    (hpρ : tsupport ρ ⊆ Ioi (0 : ℝ)) (hpη : tsupport η ⊆ Ioi (0 : ℝ))
    (R : SL(2, ℤ)) {c : ℤ} (hc : c ≠ 0) (hR : R 1 0 = c) :
    Integrable (cuspWeylOrbitalIntegrand N m n ρ η (c : ℝ) (by exact_mod_cast hc)) := by
  let g := realTranslation (-((R 1 1 : ℝ)/c))
  have hI := cuspUnwindowedOrbitalIntegrand_integrable N m n ρ η hρ hη hcρ hcη hpρ hpη R
    (hR ▸ hc)
  have hmp := realTranslation_measurePreserving (-((R 1 1 : ℝ)/c))
  have hme : MeasurableEmbedding (fun z : UpperHalfPlane => g • z) := measurableEmbedding_const_smul g
  have hcomp : Integrable (fun z : UpperHalfPlane =>
      cuspUnwindowedOrbitalIntegrand N m n ρ η R (g • z)) :=
    (hmp.integrable_comp_emb hme (g := cuspUnwindowedOrbitalIntegrand N m n ρ η R)).mpr hI
  have hn : cuspGeometricPhase N m n c R ≠ 0 := by
    intro hz
    have hnorm := cuspGeometricPhase_norm N m n c R
    rw [hz,norm_zero] at hnorm
    norm_num at hnorm
  apply (hcomp.const_mul (cuspGeometricPhase N m n c R)⁻¹).congr
  filter_upwards [] with z
  rw [cuspUnwindowedOrbitalIntegrand_bruhat N m n ρ η R hc hR,
    ← mul_assoc,inv_mul_cancel₀ hn,one_mul]

def cuspBasicLowerMatrix (c : ℤ) : SL(2, ℤ) :=
  ⟨!![1,0;c,1],by simp [Matrix.det_fin_two]⟩

theorem cuspWeylOrbitalIntegrand_integrable (N : ℕ) [NeZero N]
    (m n : ℤ) (ρ η : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hη : ContDiff ℝ ∞ η)
    (hcρ : HasCompactSupport ρ) (hcη : HasCompactSupport η)
    (hpρ : tsupport ρ ⊆ Ioi (0 : ℝ)) (hpη : tsupport η ⊆ Ioi (0 : ℝ))
    (c : ℤ) (hc : c ≠ 0) :
    Integrable (cuspWeylOrbitalIntegrand N m n ρ η (c : ℝ) (by exact_mod_cast hc)) :=
  cuspWeylOrbitalIntegrand_integrable_of_matrix N m n ρ η hρ hη hcρ hcη hpρ hpη
    (cuspBasicLowerMatrix c) hc rfl

end ArtinMatthews
