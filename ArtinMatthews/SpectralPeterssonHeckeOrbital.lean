module

public import ArtinMatthews.SpectralPeterssonHeckeRescale
public import ArtinMatthews.SpectralTrueWidthKloosterman
public import Mathlib.Analysis.Fourier.FourierTransform
public import ArtinMatthews.AtkinLehnerMixedWeight
public import ArtinMatthews.SpectralFourierBruhatKernel
public import ArtinMatthews.SpectralPeterssonHeckePoisson
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

/-! The literal weight-two orbital Fourier expansion after grouping by
true modulus. The normalized left and right shifts retain their phases. -/

noncomputable section
open Matrix Set UpperHalfPlane
open scoped MatrixGroups FourierTransform

namespace ArtinMatthews

def spectralPeterssonHeckeOrbital (u : ℝ) (m : ℕ+) (G : SL(2, ℝ)) (z : UpperHalfPlane) : ℂ :=
  ∑' l : ℤ, spectralHolomorphicSlash 2 (G*realTranslation (l : ℝ)) (spectralPeterssonHeckeSeed u m) z

def spectralPeterssonHeckeOrbitalAmplitude (u : ℝ) (m : ℕ+) (C y : ℝ) (n : ℤ) : ℂ :=
  ((C^(-(2+2*u))*y^(-1-u) : ℝ) : ℂ)*
    𝓕 (spectralPeterssonHeckeProfile u (spectralPeterssonHeckeLambda m C y)) ((n : ℝ)*y)

theorem spectralPeterssonHeckeOrbitalAmplitude_summable (u : ℝ) (m : ℕ+) (C y : ℝ)
    (hu : u ∈ Icc (0 : ℝ) 1) (hC : 0 < C) (hy : 0 < y) :
    Summable (fun n => ‖spectralPeterssonHeckeOrbitalAmplitude u m C y n‖) := by
  have hlam : 0 ≤ spectralPeterssonHeckeLambda m C y := by unfold spectralPeterssonHeckeLambda; positivity
  simp only [spectralPeterssonHeckeOrbitalAmplitude,norm_mul]
  exact (spectralPeterssonHeckeProfile_samples_summable u _ y hu hlam hy).mul_left _

theorem spectralPeterssonHeckeOrbital_fourier (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1)
    (m : ℕ+) (G : SL(2, ℝ)) (hC : 0 < G 1 0) (z : UpperHalfPlane) :
    spectralPeterssonHeckeOrbital u m G z =
      ∑' n : ℤ, atkinPhase (((m : ℝ)*G 0 0+(n : ℝ)*G 1 1)/(G 1 0))*
        spectralPeterssonHeckeOrbitalAmplitude u m (G 1 0) z.im n*atkinPhase ((n : ℝ)*z.re) := by
  let C := G 1 0
  let A := G 0 0
  let D := G 1 1
  let y := z.im
  let x := z.re+D/C
  let L := spectralPeterssonHeckeLambda m C y
  let H := spectralPeterssonHeckeProfile u L
  let b : ℂ := atkinPhase ((m : ℝ)*A/C)*((C^(-(2+2*u))*y^(-2-u) : ℝ) : ℂ)
  have hlam : 0 ≤ L := by dsimp only [L,spectralPeterssonHeckeLambda]; positivity
  have hpoint (l : ℤ) :
      spectralHolomorphicSlash 2 (G*realTranslation (l : ℝ)) (spectralPeterssonHeckeSeed u m) z =
        b*H ((x+(l : ℝ))/y) := by
    rw [spectralHolomorphicSlash_mul,spectralHolomorphicSlash_realTranslation,spectralPeterssonHeckeSlash_rescale u m G hC,
      realTranslation_im_smul,realTranslation_re_smul]
    dsimp only [b,H,L,x,C,A,D,y]
    rw [show z.re+(l : ℝ)+G 1 1/(G 1 0) = z.re+G 1 1/(G 1 0)+(l : ℝ) by ring]
  have hpow : y^(-2-u)*y = y^(-1-u) := by
    calc
      _ = y^(-2-u)*y^(1 : ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add z.im_pos]; congr 1; ring
  have hweight : (C^(-(2+2*u))*y^(-2-u))*y = C^(-(2+2*u))*y^(-1-u) := by
    rw [mul_assoc,hpow]
  have hsum : spectralPeterssonHeckeOrbital u m G z = b*(∑' l : ℤ, H ((x+(l : ℝ))/y)) := by
    unfold spectralPeterssonHeckeOrbital
    rw [← tsum_mul_left]
    exact tsum_congr hpoint
  rw [hsum]
  have hp : (∑' l : ℤ, H ((x+(l : ℝ))/y)) =
      (y : ℂ)*(∑' n : ℤ, 𝓕 H ((n : ℝ)*y)*atkinPhase ((n : ℝ)*x)) :=
    spectralPeterssonHeckeProfile_periodized u L y x hu hlam z.im_pos
  rw [hp,← mul_assoc,← tsum_mul_left]
  apply tsum_congr
  intro n
  change (b*(y : ℂ))*(𝓕 H ((n : ℝ)*y)*atkinPhase ((n : ℝ)*x)) =
    atkinPhase (((m : ℝ)*A+(n : ℝ)*D)/C)*spectralPeterssonHeckeOrbitalAmplitude u m C y n*
      atkinPhase ((n : ℝ)*z.re)
  have h₁ : ((m : ℝ)*A+(n : ℝ)*D)/C = (m : ℝ)*A/C+(n : ℝ)*(D/C) := by ring
  have h₂ : (n : ℝ)*x = (n : ℝ)*(D/C)+(n : ℝ)*z.re := by dsimp only [x]; ring
  have hb : b*(y : ℂ) = atkinPhase ((m : ℝ)*A/C)*((C^(-(2+2*u))*y^(-1-u) : ℝ) : ℂ) := by
    dsimp only [b]
    rw [mul_assoc,← Complex.ofReal_mul,hweight]
  rw [h₁,h₂,atkinPhase_add,atkinPhase_add,hb]
  dsimp only [spectralPeterssonHeckeOrbitalAmplitude,H,L]
  ring

def gamma0PeterssonHeckeModulus (N : ℕ) [NeZero N] (b a : SL(2, ℤ)) (u : ℝ) (m : ℕ+)
    (c : Ioi (0 : ℕ)) (z : UpperHalfPlane) : ℂ :=
  let _ : NeZero c.val := ⟨c.property.ne'⟩
  ∑ R : gamma0TrueWidthReducedMatrix N b a c.val,
    spectralPeterssonHeckeOrbital u m (gamma0TrueWidthMatrix N b a R.val) z

def gamma0PeterssonHeckeJointTerm (N : ℕ) [NeZero N] (b a : SL(2, ℤ)) (u : ℝ) (m : ℕ+)
    (c : Ioi (0 : ℕ)) (n : ℤ) (z : UpperHalfPlane) : ℂ :=
  let _ : NeZero c.val := ⟨c.property.ne'⟩
  let C := gamma0TrueWidthModulus N b a (c.val : ℝ)
  gamma0TrueWidthKloostermanSum N b a c.val n (m : ℤ)*
    spectralPeterssonHeckeOrbitalAmplitude u m C z.im n*atkinPhase ((n : ℝ)*z.re)

theorem gamma0PeterssonHeckeModulus_fourier (N : ℕ) [NeZero N] (b a : SL(2, ℤ)) (u : ℝ)
    (hu : u ∈ Icc (0 : ℝ) 1) (m : ℕ+) (c : Ioi (0 : ℕ)) (z : UpperHalfPlane) :
    gamma0PeterssonHeckeModulus N b a u m c z = ∑' n, gamma0PeterssonHeckeJointTerm N b a u m c n z := by
  let _ : NeZero c.val := ⟨c.property.ne'⟩
  let C := gamma0TrueWidthModulus N b a (c.val : ℝ)
  have hC : 0 < C := gamma0TrueWidthModulus_pos N b a (Nat.cast_pos.mpr c.property)
  let W (R : gamma0TrueWidthReducedMatrix N b a c.val) (n : ℤ) : ℂ :=
    cuspTrueWidthGeometricPhase N b a n (m : ℤ) c.val R.val*
      spectralPeterssonHeckeOrbitalAmplitude u m C z.im n*atkinPhase ((n : ℝ)*z.re)
  have hw (R : gamma0TrueWidthReducedMatrix N b a c.val) : Summable (W R) := by
    apply Summable.of_norm
    simp only [W,norm_mul,cuspTrueWidthGeometricPhase,atkinPhase_norm,one_mul,mul_one]
    exact spectralPeterssonHeckeOrbitalAmplitude_summable u m C z.im hu hC z.im_pos
  have heq (R : gamma0TrueWidthReducedMatrix N b a c.val) :
      spectralPeterssonHeckeOrbital u m (gamma0TrueWidthMatrix N b a R.val) z = ∑' n, W R n := by
    let G := gamma0TrueWidthMatrix N b a R.val
    have hg : G 1 0 = C := gamma0TrueWidthMatrix_lower N b a R.val c.val R.property.2.1
    rw [spectralPeterssonHeckeOrbital_fourier u hu m G (hg.symm ▸ hC)]
    apply tsum_congr
    intro n
    have hphase := cuspTrueWidthGeometricPhase_normalized N b a R.val n (m : ℤ) (c.val : ℤ)
      (by exact_mod_cast c.property.ne') R.property.2.1
    change cuspTrueWidthGeometricPhase N b a n (m : ℤ) (c.val : ℤ) R.val =
      atkinPhase (((n : ℝ)*G 1 1+((m : ℤ) : ℝ)*G 0 0)/(G 1 0)) at hphase
    unfold W
    rw [hphase,hg]
    push_cast
    ring_nf
  unfold gamma0PeterssonHeckeModulus
  dsimp only
  simp_rw [heq]
  rw [← Summable.tsum_finsetSum (fun R _ => hw R)]
  apply tsum_congr
  intro n
  unfold gamma0PeterssonHeckeJointTerm gamma0TrueWidthKloostermanSum
  dsimp only
  simp only [W,Finset.sum_mul]
  rfl

end ArtinMatthews
