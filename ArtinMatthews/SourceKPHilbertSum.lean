module

public import ArtinMatthews.SourceFiniteKPHilbert
public import ArtinMatthews.SourceKubotaCoordinates
public import ArtinMatthews.SourceFiniteKPMultipliers
public import ArtinMatthews.SourceKubotaWeylSymbol
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
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
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

/-! The additive Steinberg identity used in the deep compact splitting.
The finite-place specialization uses the actual cubic CFT pairing. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain
open scoped NumberField
noncomputable section

theorem sourceKPHilbert_sum_trivial {F A : Type*} [Field F] [CommGroup A]
    (B : Fˣ →* (Fˣ →* A))
    (hdiag : ∀ x, B x x = 1)
    (hminus : ∀ x, B x (sourceMinusOneUnit F) = 1)
    (hsteinberg : ∀ x : Fˣ, ∀ hx : 1 - (x : F) ≠ 0, B x (Units.mk0 _ hx) = 1)
    (s a b : Fˣ) (hs : (s : F) = (a : F) + (b : F)) :
    B (s/a) (s/b) = 1 := by
  have hrel : ((b/a : Fˣ) : F) = ((s/a : Fˣ) : F) - 1 := by
    simp only [Units.val_div_eq_div_val]
    rw [hs, add_div, div_self a.ne_zero, add_sub_cancel_left]
  have hsym := sourceKubotaSymbol_steinberg_sub B hminus hsteinberg (s/a) (b/a) hrel
  have he : s/b = (s/a)/(b/a) := (div_div_div_cancel_right s b a).symm
  rw [he, map_div, hdiag, hsym, div_one]

theorem sourceFiniteKPHilbert_sum (K : Type) [Field K] [NumberField K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ 12) (P : HeightOneSpectrum (𝓞 K))
    (s a b : (P.adicCompletion K)ˣ)
    (hs : (s : P.adicCompletion K) = (a : P.adicCompletion K) + (b : P.adicCompletion K)) :
    sourceFiniteKPHilbert K hζ P (s/a) (s/b) = 1 :=
  sourceKPHilbert_sum_trivial (sourceFiniteKPHilbert K hζ P)
    (sourceFiniteKPHilbert_diag K hζ P) (sourceFiniteKPHilbert_minus_right K hζ P)
    (sourceFiniteKPHilbert_steinberg K hζ P) s a b hs

end
end ArtinMatthews
