module

public import ArtinMatthews.DoubleVoronoiDetection
public import ArtinMatthews.ShiftedDoubleVoronoiFubini
public import ArtinMatthews.ShiftedDoubleVoronoiDetector
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.NumberTheory.Chebyshev
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


set_option backward.privateInPublic true
@[expose] public section

/-!
# The convergent double transformation to ordinary Kloosterman sums

This joins the actual weight-one analytic summation theorem to the exact
finite arithmetic. The original linear-relation and congruence detector is
retained. No Kloosterman estimate, circle approximation, or correlation bound
is assumed or asserted here.
-/

noncomputable section
open Complex UpperHalfPlane Set Finset
open scoped MatrixGroups ContDiff
open OAI.Erdos970.ErdosKloosterman

namespace ArtinMatthews

/-- The original linear-relation and k1≡1(mod d) detector, before rescaling j. -/
def doubleVoronoiSourceDetector (H d : ℕ) (v3 v4 a : (ZMod (H*d))ˣ)
    (k1 k2 : ZMod (H*d)) (j : ZMod d) : ZMod (H*d) :=
  (a : ZMod (H*d))*((v4 : ZMod (H*d))*(k1-1)-(v3 : ZMod (H*d))*(k2-1)) +
    (H : ZMod (H*d))*(j.val : ZMod (H*d))*(k1-1)

/-- The original source detector and the rescaled numerator detector give
identical actual coefficient sums. All finite/infinite exchanges are justified. -/
theorem weightOne_source_detector_eq_primal
    (N : ℕ) [NeZero N] (f : CuspForm (cubicThetaKernel N) 1)
    (H d : ℕ) [NeZero H] [NeZero d] (hdH : d∣H)
    (v3 v4 : (ZMod (H*d))ˣ)
    (H1 H2 : ℝ → ℂ) (hs1 : ContDiff ℝ ∞ H1) (hs2 : ContDiff ℝ ∞ H2)
    (u1 v1 u2 v2 : ℝ) (hu1 : 0 < u1) (hu2 : 0 < u2)
    (hw1 : Function.support H1 ⊆ Icc u1 v1) (hw2 : Function.support H2 ⊆ Icc u2 v2) :
    (∑ a : (ZMod (H*d))ˣ, ∑ j : ZMod d, ∑' k : ℕ × ℕ,
      cuspSourcePair f H1 H2 k * ZMod.stdAddChar (doubleVoronoiSourceDetector H d v3 v4 a k.1 k.2 j)) /
        (d : ℂ) =
      (∑ a : (ZMod (H*d))ˣ, ∑ j : ZMod d, ∑' k : ℕ × ℕ,
        cuspSourcePair f H1 H2 k * ZMod.stdAddChar (doubleVoronoiPrimalPhase H d hdH v3 v4 a k.1 k.2 j)) /
          (d : ℂ) := by
  have hA := cuspSourcePair_summable N f H1 H2 hs1 hs2 u1 v1 u2 v2 hu1 hu2 hw1 hw2
  rw [doubleVoronoi_finite_average_tsum (H*d) d _ hA,
    doubleVoronoi_finite_average_tsum (H*d) d _ hA]
  apply tsum_congr
  intro k
  congr 1
  apply congrArg (fun z : ℂ ↦ z / (d : ℂ))
  apply sum_congr rfl
  intro a _
  exact doubleVoronoi_primal_detection H d hdH v3 v4 a k.1 k.2

set_option maxHeartbeats 800000 in
/-- The complete separable source-to-Kloosterman identity, with the exact
D-congruence and ψ(−m3*m4)/q² factor. The remaining assumptions on r and A0
are the arithmetic factorization supplied by the actual common-prime part. -/
theorem weightOne_double_voronoi_kloosterman
    (N : ℕ) [NeZero N] (hN : 3∣N) (f : CuspForm (cubicThetaKernel N) 1)
    (H d r : ℕ) [NeZero H] [NeZero d]
    (hdH : d∣H) (hQ : N*(d*r)^2∣H*d) (hr : r≠0)
    (m3 m4 : ℕ) (A0 : ℤ)
    (hfactor : (m3 : ℤ)-m4=(r : ℤ)*A0) (hcop : IsCoprime (d : ℤ) ((m3 : ℤ)*A0))
    (v3 v4 : (ZMod (H*d))ˣ)
    (hv3 : (v3 : ZMod (H*d))=(m3 : ZMod (H*d)))
    (hv4 : (v4 : ZMod (H*d))=(m4 : ZMod (H*d)))
    (H1 H2 : ℝ → ℂ) (hs1 : ContDiff ℝ ∞ H1) (hs2 : ContDiff ℝ ∞ H2)
    (u1 v1 u2 v2 : ℝ) (hu1 : 0 < u1) (hu2 : 0 < u2)
    (hw1 : Function.support H1 ⊆ Icc u1 v1) (hw2 : Function.support H2 ⊆ Icc u2 v2) :
    (∑ a : (ZMod (H*d))ˣ, ∑ j : ZMod d, ∑' k : ℕ × ℕ,
      cuspSourcePair f H1 H2 k * ZMod.stdAddChar (doubleVoronoiSourceDetector H d v3 v4 a k.1 k.2 j)) /
        (d : ℂ) =
      (cubicThetaNebentypus (-(m3 : ℤ)*m4) / ((H*d : ℕ) : ℂ)^2) *
        ∑' k : ℕ × ℕ, cuspBesselPair f (H*d) H1 H2 k *
          ((if Int.ModEq ((d : ℤ)*(r : ℤ)) ((m3 : ℤ)^2*k.1) ((m4 : ℤ)^2*k.2) then 1 else 0) *
            sum ZMod.stdAddChar ((v3 : ZMod (H*d))-(v4 : ZMod (H*d)))
              ((↑(v3*v4)⁻¹ : ZMod (H*d))*((v4 : ZMod (H*d))*k.2-(v3 : ZMod (H*d))*k.1))) := by
  have hD : (d*r)^2∣H*d := (show (d*r)^2∣N*(d*r)^2 from ⟨N, by ring⟩).trans hQ
  have hp (a : (ZMod (H*d))ˣ) (j : ZMod d) :=
    weightOne_double_voronoi_detector N hN f (d*r) H d hdH (dvd_mul_right d r) hQ
      m3 m4 v3 v4 hv3 hv4 a j H1 H2 hs1 hs2 u1 v1 u2 v2 hu1 hu2 hw1 hw2
  rw [weightOne_source_detector_eq_primal N f H d hdH v3 v4 H1 H2 hs1 hs2
    u1 v1 u2 v2 hu1 hu2 hw1 hw2]
  simp_rw [hp, ← Finset.mul_sum]
  rw [mul_div_assoc]
  congr 1
  exact weightOne_dual_average_kloosterman N f H d r hdH hD hr m3 m4 A0 hfactor hcop
    v3 v4 (by simpa only [Int.cast_natCast] using hv3) (by simpa only [Int.cast_natCast] using hv4)
    H1 H2 hs1 hs2 u1 v1 u2 v2 hu1 hu2 hw1 hw2

end ArtinMatthews
