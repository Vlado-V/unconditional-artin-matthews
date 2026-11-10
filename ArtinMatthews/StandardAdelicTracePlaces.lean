module

public import ArtinMatthews.StandardAdelicLocalNontrivial
public import Mathlib.Algebra.AffineMonoid.Basic
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
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.SimpleRing.Principal
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

/-! The exceptional local conductor set is exactly the prime support of
the actual different ideal. -/
namespace ArtinMatthews.StandardAdelic

open NumberField IsDedekindDomain FractionalIdeal
open scoped NumberField nonZeroDivisors Classical
noncomputable section
variable (K : Type) [Field K] [NumberField K]

theorem count_coe_ne_zero_iff_dvd (P : HeightOneSpectrum (𝓞 K)) (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) :
    FractionalIdeal.count K P I ≠ 0 ↔ P.asIdeal ∣ I := by
  rw [FractionalIdeal.count_coe K P hI, Int.natCast_ne_zero]
  exact Associates.count_ne_zero_iff_dvd hI P.irreducible

theorem mem_traceBadPlaces_iff_different (P : HeightOneSpectrum (𝓞 K)) :
    P ∈ traceBadPlaces K ↔ P.asIdeal ∣ differentIdeal ℤ (𝓞 K) := by
  have hc : FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K) =
      ((differentIdeal ℤ (𝓞 K) : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)⁻¹ := by
    rw [coeIdeal_differentIdeal ℤ ℚ K (𝓞 K), inv_inv]
  rw [mem_traceBadPlaces, hc, FractionalIdeal.count_inv, neg_ne_zero]
  exact count_coe_ne_zero_iff_dvd K P _ differentIdeal_ne_bot

end
end ArtinMatthews.StandardAdelic
