module

public import ArtinMatthews.SpectralCompactResolventMeromorphicTest
public import ArtinMatthews.SpectralEisensteinMeromorphicTests
public import ArtinMatthews.SpectralEisensteinRegularMatching
public import ArtinMatthews.SpectralCompactResolventReflectedJump
public import ArtinMatthews.SpectralEisensteinMixedCuspFlux
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Exact diagonal jump of the actual compact-forcing ambient resolvent
across the regular critical line, in the native compact test normalization. -/
noncomputable section
open Set
open scoped MatrixGroups
namespace ArtinMatthews

theorem spectralCriticalFluxProduct (t : ℝ) (ht : t≠0) (B e : ℂ)
    (he : e=(2:ℂ)*(t:ℂ)*Complex.I*(starRingEnd ℂ) B) :
    B*e=(Complex.I/(2*(t:ℂ)))*((‖e‖^2:ℝ):ℂ) := by
  have htC : (t:ℂ)≠0 := Complex.ofReal_ne_zero.mpr ht
  have hc : (starRingEnd ℂ) e=-((2:ℂ)*(t:ℂ)*Complex.I)*B := by
    rw [he]
    simp only [map_mul,Complex.conj_ofReal,Complex.conj_I,Complex.conj_ofNat,starRingEnd_self_apply]
    ring
  rw [Complex.ofReal_pow,← Complex.mul_conj' e,hc]
  field_simp [htC]
  calc
    _ = -(B*e)*(-1) := by ring
    _ = -(B*e)*Complex.I^2 := by rw [Complex.I_sq]
    _ = _ := by ring

theorem gamma0CompactForcingResolvent_critical_jump (N : ℕ) [NeZero N]
    (ψ : h2SmoothCompactSeeds) (Y : Gamma0CompactResolventCutoff N ψ)
    (s : ℂ) (hs : s.re=1/2) (ht : s.im≠0) (hr : gamma0EisensteinMatchingRegular N s)
    (hYs : gamma0HeightMatchingRegular N Y.height Y.pos s)
    (hYq : gamma0HeightMatchingRegular N Y.height Y.pos (1-s)) :
    gamma0CompactForcingResolventMeromorphicTest N ψ ψ Y s-
      gamma0CompactForcingResolventMeromorphicTest N ψ ψ Y (1-s)=
        -((Complex.I/(2*(s.im:ℂ)))*((∑ i,
          ‖gamma0CuspEisensteinMeromorphicTest N (gamma0EisensteinCuspClassRepresentative N i) ψ s‖^2:ℝ):ℂ)) := by
  let E (i : Gamma0EisensteinCuspClasses N) :=
    gamma0CuspEisensteinMeromorphicTest N (gamma0EisensteinCuspClassRepresentative N i) ψ s
  let B := gamma0CompactForcingMatchedCoefficient N ψ Y (1-s)
  have hTerm (i : Gamma0EisensteinCuspClasses N) :
      B i*E i=(Complex.I/(2*(s.im:ℂ)))*((‖E i‖^2:ℝ):ℂ) :=
    spectralCriticalFluxProduct s.im ht (B i) (E i)
      (gamma0CompactForcingMatchedCoefficient_critical_test N ψ Y s hs hr hYq i)
  have hSum : ((∑ i,‖E i‖^2:ℝ):ℂ)=∑ i,((‖E i‖^2:ℝ):ℂ) :=
    map_sum Complex.ofRealHom _ _
  rw [gamma0CompactForcingResolventMeromorphicTest_eq_matched_of_det N ψ ψ Y s hYs.2,
    gamma0CompactForcingResolventMeromorphicTest_eq_matched_of_det N ψ ψ Y (1-s) hYq.2,
    gamma0CompactForcingMatchedTest_reflected_jump N ψ ψ Y s hr hYs hYq]
  change -(∑ i,B i*E i)= -((Complex.I/(2*(s.im:ℂ)))*((∑ i,‖E i‖^2:ℝ):ℂ))
  simp only [hTerm,← Finset.mul_sum,hSum]

theorem gamma0CompactForcingResolvent_critical_jump_im (N : ℕ) [NeZero N]
    (ψ : h2SmoothCompactSeeds) (Y : Gamma0CompactResolventCutoff N ψ)
    (s : ℂ) (hs : s.re=1/2) (ht : s.im≠0) (hr : gamma0EisensteinMatchingRegular N s)
    (hYs : gamma0HeightMatchingRegular N Y.height Y.pos s)
    (hYq : gamma0HeightMatchingRegular N Y.height Y.pos (1-s)) :
    (gamma0CompactForcingResolventMeromorphicTest N ψ ψ Y s-
      gamma0CompactForcingResolventMeromorphicTest N ψ ψ Y (1-s)).im=
        -((∑ i,‖gamma0CuspEisensteinMeromorphicTest N (gamma0EisensteinCuspClassRepresentative N i) ψ s‖^2)/
          (2*s.im)) := by
  let S : ℝ := ∑ i,‖gamma0CuspEisensteinMeromorphicTest N (gamma0EisensteinCuspClassRepresentative N i) ψ s‖^2
  have h : (Complex.I/(2*(s.im:ℂ)))*(S:ℂ)=((S/(2*s.im):ℝ):ℂ)*Complex.I := by
    push_cast
    ring
  rw [gamma0CompactForcingResolvent_critical_jump N ψ Y s hs ht hr hYs hYq]
  change (-((Complex.I/(2*(s.im:ℂ)))*(S:ℂ))).im= -(S/(2*s.im))
  rw [h]
  simp only [Complex.neg_im,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,
    Complex.I_im,mul_zero,mul_one,add_zero]

end ArtinMatthews
