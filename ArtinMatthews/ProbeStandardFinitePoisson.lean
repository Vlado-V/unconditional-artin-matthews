module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import Mathlib.RingTheory.Henselian
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

/-! The literal finite source F(s,A,h), with the actual global trace
exponential and the exact integral quotient forced by its congruence. -/
namespace ArtinMatthews.VaryingKummerAnalytic

open NumberField
open scoped NumberField BigOperators Classical
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

def probeFieldTraceExponential (x : K) : ℂ :=
  Complex.exp ((Algebra.trace ℚ K x : ℂ) * (2 * (Real.pi : ℂ) * Complex.I))

def probeStandardFiniteSum (I J : Ideal (𝓞 K)) (s A h : 𝓞 K)
    (f g : (𝓞 K) → ℂ) : ℂ :=
  ∑' d : (𝓞 K) ⧸ I, ∑' v : (𝓞 K) ⧸ J,
    if h - A * Quotient.out d ∈ I then
      f (Quotient.out d) * g (Quotient.out v) *
        probeFieldTraceExponential K
          ((((h - A * Quotient.out d : 𝓞 K) : K) * (Quotient.out v : 𝓞 K)) /
            ((s : K) * (A : K))) else 0

def probeStandardFiniteF (s A h : 𝓞 K) (f g : (𝓞 K) → ℂ) : ℂ :=
  probeStandardFiniteSum K (Ideal.span {s}) (Ideal.span {A}) s A h f g

def probeStandardFiniteGauss (A k : 𝓞 K) (g : (𝓞 K) → ℂ) : ℂ :=
  ∑' v : (𝓞 K) ⧸ Ideal.span {A}, g (Quotient.out v) *
    probeFieldTraceExponential K (((k : K) * (Quotient.out v : 𝓞 K)) / (A : K))

def probeFiniteExactQuotient (x s : 𝓞 K) (h : s ∣ x) : 𝓞 K := h.choose

omit [NumberField K] in
theorem probeFiniteExactQuotient_spec (x s : 𝓞 K) (h : s ∣ x) :
    x = s * probeFiniteExactQuotient K x s h := h.choose_spec

theorem probeStandardFiniteF_gauss (s A h : 𝓞 K) (hs : s ≠ 0) (hA : A ≠ 0)
    (f g : (𝓞 K) → ℂ) :
    probeStandardFiniteF K s A h f g =
      ∑' d : (𝓞 K) ⧸ Ideal.span {s},
        if hd : s ∣ h - A * Quotient.out d then f (Quotient.out d) *
          probeStandardFiniteGauss K A (probeFiniteExactQuotient K _ s hd) g else 0 := by
  have hsK : (s : K) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.mpr hs
  have hAK : (A : K) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.mpr hA
  unfold probeStandardFiniteF probeStandardFiniteSum
  apply tsum_congr
  intro d
  by_cases hd : s ∣ h - A * Quotient.out d
  · have hm : h - A * Quotient.out d ∈ Ideal.span {s} := Ideal.mem_span_singleton.mpr hd
    simp only [ite_eq_left hm, dite_eq_left hd]
    unfold probeStandardFiniteGauss
    rw [← tsum_mul_left]
    apply tsum_congr
    intro v
    have hq : ((h - A * Quotient.out d : 𝓞 K) : K) =
        (s : K) * (probeFiniteExactQuotient K (h - A * Quotient.out d) s hd : K) := by
      exact_mod_cast probeFiniteExactQuotient_spec K (h - A * Quotient.out d) s hd
    have he : (((h - A * Quotient.out d : 𝓞 K) : K) * (Quotient.out v : 𝓞 K)) /
        ((s : K) * (A : K)) =
        ((probeFiniteExactQuotient K (h - A * Quotient.out d) s hd : K) *
          (Quotient.out v : 𝓞 K)) / (A : K) := by
      rw [hq]
      field_simp
    rw [he]
    ring
  · have hm : h - A * Quotient.out d ∉ Ideal.span {s} :=
      fun hx => hd (Ideal.mem_span_singleton.mp hx)
    simp only [ite_eq_right hm, dite_eq_right hd, tsum_zero]

end
end ArtinMatthews.VaryingKummerAnalytic
