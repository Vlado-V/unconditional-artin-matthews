module

public import ArtinMatthews.SIntegerGaussCRTPhase
public import ArtinMatthews.SIntegerLocalCOne
public import ArtinMatthews.QuotientUnitChanges
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
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

/-! Literal principal local source kernel and its exact quotient form.
Divisibility is proved equivalent to the original congruence gate. -/
namespace ArtinMatthews.SourceCRTNormalization

open NumberField IsDedekindDomain ArtinMatthews.SIntegerPrincipalization
open ArtinMatthews.SIntegerQuotient ArtinMatthews.SIntegerFourier ArtinMatthews.StandardAdelic
open scoped NumberField Classical
noncomputable section
variable {K : Type} [Field K] [NumberField K]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 K)))

def principalSourceKernel (A B : PrincipalIntegerRing S₀) (hA : A ≠ 0) (hB : B ≠ 0)
    (H : PrincipalIntegerRing S₀)
    (W : ((PrincipalIntegerRing S₀) ⧸ Ideal.span {A}) → ℂ)
    (Z : ((PrincipalIntegerRing S₀) ⧸ Ideal.span {B}) → ℂ) : ℂ :=
  quotientCongruenceKernel (Ideal.span {A}) (Ideal.span {B}) B H
    (sourceProductPhase S₀ A B hA hB) W Z

theorem principalSourceKernel_divide (A B : PrincipalIntegerRing S₀) (hA : A ≠ 0) (hB : B ≠ 0)
    (H : PrincipalIntegerRing S₀)
    (W : ((PrincipalIntegerRing S₀) ⧸ Ideal.span {A}) → ℂ)
    (Z : ((PrincipalIntegerRing S₀) ⧸ Ideal.span {B}) → ℂ) :
    principalSourceKernel S₀ A B hA hB H W Z =
      ∑' d : (PrincipalIntegerRing S₀) ⧸ Ideal.span {A},
        if hd : A ∣ H - B * Quotient.out d then
          W d * ∑' v : (PrincipalIntegerRing S₀) ⧸ Ideal.span {B},
            Z v * sIntegerQuotientPhase K (principalizingSet S₀) B hB
              (Ideal.Quotient.mk _ (principalDivide A (H - B * Quotient.out d) hd) * v)
        else 0 := by
  unfold principalSourceKernel quotientCongruenceKernel
  apply tsum_congr
  intro d
  by_cases hd : A ∣ H - B * Quotient.out d
  · have hm := Ideal.mem_span_singleton.mpr hd
    rw [dite_eq_left hd]
    simp only [ite_eq_left hm]
    rw [← tsum_mul_left]
    apply tsum_congr
    intro v
    rw [sourceProductPhase_mk]
    let q : PrincipalIntegerRing S₀ := principalDivide A (H - B * Quotient.out d) hd
    let r : PrincipalIntegerRing S₀ := Quotient.out v
    have hq : H - B * Quotient.out d = A * q := principalDivide_spec A _ hd
    have hr : Ideal.Quotient.mk (Ideal.span {B}) q * v = Ideal.Quotient.mk _ (q * r) := by
      rw [map_mul, Ideal.Quotient.mk_out]
    rw [hr, sIntegerQuotientPhase_mk]
    have hA' : (A : K) ≠ 0 := fun h => hA (Subtype.ext h)
    have hB' : (B : K) ≠ 0 := fun h => hB (Subtype.ext h)
    have he : (((H - B * Quotient.out d) * r : PrincipalIntegerRing S₀) : K) /
        ((A : K) * (B : K)) =
        ((q * r : PrincipalIntegerRing S₀) : K) /
          (B : K) := by
      calc
        _ = (((A * q) * r :
            PrincipalIntegerRing S₀) : K) / ((A : K) * (B : K)) :=
          congrArg (fun y : PrincipalIntegerRing S₀ => ((y * r : PrincipalIntegerRing S₀) : K) /
            ((A : K) * (B : K))) hq
        _ = _ := by
          change ((A : K) * (q : K) * (r : K)) /
            ((A : K) * (B : K)) =
            ((q : K) * (r : K)) / (B : K)
          field_simp
    rw [he]
    ring
  · have hm : H - B * Quotient.out d ∉ Ideal.span {A} := by
      simpa only [Ideal.mem_span_singleton] using hd
    simp only [ite_eq_right hm, dite_eq_right hd, tsum_zero]

end
end ArtinMatthews.SourceCRTNormalization
