module

public import ArtinMatthews.ShiftedDoubleVoronoiKloosterman
public import ArtinMatthews.ShiftedCommonPrimePartSquarefree
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

/-! The complete separable double Voronoi identity for the actual squarefree
source integers, their gcd, and their common-prime part. The level-modulus
condition supplies the detector rescaling and the required arithmetic factors. -/

noncomputable section
open Complex UpperHalfPlane Set
open scoped MatrixGroups ContDiff
open OAI.Erdos970.ErdosKloosterman

namespace ArtinMatthews

set_option maxHeartbeats 800000 in
/-- The actual squarefree-parameter version of the double transformation and
finite Kloosterman identity. There is no assumed factorization of D and no
assumed source-to-dual equality. The test remains separable and compact smooth. -/
theorem weightOne_double_voronoi_squarefree
    (N : ℕ) [NeZero N] (hN : 3∣N) (f : CuspForm (cubicThetaKernel N) 1)
    (m1 m2 H : ℕ) [NeZero H] [NeZero (m1.gcd m2)]
    (hm1 : 0<m1) (hm2 : 0<m2) (hne : m1≠m2) (hsq1 : Squarefree m1) (hsq2 : Squarefree m2)
    (hQ : N*(shiftedCommonPrimePart m1 m2)^2∣H*(m1.gcd m2))
    (hc : ((m1/(m1.gcd m2))*(m2/(m1.gcd m2))).Coprime (H*(m1.gcd m2)))
    (H1 H2 : ℝ → ℂ) (hs1 : ContDiff ℝ ∞ H1) (hs2 : ContDiff ℝ ∞ H2)
    (u1 v1 u2 v2 : ℝ) (hu1 : 0 < u1) (hu2 : 0 < u2)
    (hw1 : Function.support H1 ⊆ Icc u1 v1) (hw2 : Function.support H2 ⊆ Icc u2 v2) :
    let d := m1.gcd m2
    let v3 := ZMod.unitOfCoprime (m1/d) (Nat.coprime_mul_iff_left.mp hc).1
    let v4 := ZMod.unitOfCoprime (m2/d) (Nat.coprime_mul_iff_left.mp hc).2
    (∑ a : (ZMod (H*d))ˣ, ∑ j : ZMod d, ∑' k : ℕ × ℕ,
      cuspSourcePair f H1 H2 k * ZMod.stdAddChar (doubleVoronoiSourceDetector H d v3 v4 a k.1 k.2 j)) /
        (d : ℂ) =
      (cubicThetaNebentypus (-((m1/d : ℕ) : ℤ)*(m2/d : ℕ)) / ((H*d : ℕ) : ℂ)^2) *
        ∑' k : ℕ × ℕ, cuspBesselPair f (H*d) H1 H2 k *
          ((if Int.ModEq (shiftedCommonPrimePart m1 m2 : ℤ)
            (((m1/d : ℕ) : ℤ)^2*k.1) (((m2/d : ℕ) : ℤ)^2*k.2) then 1 else 0) *
            sum ZMod.stdAddChar ((v3 : ZMod (H*d))-(v4 : ZMod (H*d)))
              ((↑(v3*v4)⁻¹ : ZMod (H*d))*((v4 : ZMod (H*d))*k.2-(v3 : ZMod (H*d))*k.1))) := by
  intro d v3 v4
  obtain ⟨r,A0,hr,hD,hfactor,hcop,-,-⟩ := squarefree_commonPrimePart_factors hm1 hm2 hne hsq1 hsq2
  have hQ' : N*(d*r)^2∣H*d := by simpa only [hD] using hQ
  have hdd : d^2∣H*d := by
    apply (show d^2∣N*(d*r)^2 from ⟨N*r^2, by ring⟩).trans hQ'
  have hdH : d∣H := by
    have hdq : d∣H*d := dvd_mul_left d H
    have hh : d∣(H*d)/d := (Nat.dvd_div_iff_mul_dvd hdq).mpr (by simpa only [pow_two] using hdd)
    simpa only [Nat.mul_div_cancel H (NeZero.pos d)] using hh
  have hv := weightOne_double_voronoi_kloosterman N hN f H d r hdH hQ' hr
    (m1/d) (m2/d) A0 hfactor hcop v3 v4
    (by simp only [v3, ZMod.coe_unitOfCoprime]) (by simp only [v4, ZMod.coe_unitOfCoprime])
    H1 H2 hs1 hs2 u1 v1 u2 v2 hu1 hu2 hw1 hw2
  simpa only [hD, Nat.cast_mul] using hv

end ArtinMatthews
