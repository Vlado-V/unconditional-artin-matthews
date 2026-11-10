module

public import ArtinMatthews.SourcePrincipalKernel
public import ArtinMatthews.QuotientKernelRepresentatives
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

/-! Equality transport for a principal modulus, retaining its actual
standard phase and transporting the residue weight canonically. -/
namespace ArtinMatthews.SourceCRTNormalization

open NumberField IsDedekindDomain ArtinMatthews.SIntegerPrincipalization
open scoped NumberField Classical
noncomputable section
variable {K : Type} [Field K] [NumberField K]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 K)))

theorem principalSourceKernel_congr_left (A A' B : PrincipalIntegerRing S₀) (h : A = A')
    (hA : A ≠ 0) (hA' : A' ≠ 0) (hB : B ≠ 0) (H : PrincipalIntegerRing S₀)
    (W : ((PrincipalIntegerRing S₀) ⧸ Ideal.span {A}) → ℂ)
    (Z : ((PrincipalIntegerRing S₀) ⧸ Ideal.span {B}) → ℂ) :
    principalSourceKernel S₀ A B hA hB H W Z =
      principalSourceKernel S₀ A' B hA' hB H
        (fun d => W ((Ideal.quotEquivOfEq (congrArg (fun x : PrincipalIntegerRing S₀ => Ideal.span {x}) h)).symm d)) Z := by
  cases h
  simp only [quotientEquivOfEq_refl, RingEquiv.symm_refl, RingEquiv.refl_apply]

end
end ArtinMatthews.SourceCRTNormalization
