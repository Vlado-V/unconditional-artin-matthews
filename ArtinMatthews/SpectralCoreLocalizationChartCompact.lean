module

public import ArtinMatthews.SpectralRellichRectangle
public import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
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
public import Mathlib.RingTheory.WittVector.IsPoly
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

/-! A compact positive coordinate set is an actual compact hyperbolic chart. -/

namespace ArtinMatthews
noncomputable section

open Set

theorem spectralCoreChart_compact_of_positive {S : Set (ℝ × ℝ)}
    (hS : IsCompact S) (hpositive : S ⊆ {p : ℝ × ℝ | 0 < p.2}) :
    IsCompact {z : UpperHalfPlane | (z.re,z.im) ∈ S} := by
  let lift : ℝ × ℝ → UpperHalfPlane := fun p =>
    UpperHalfPlane.ofComplex (Complex.equivRealProdCLM.symm p)
  have hpos (p : ℝ × ℝ) (hp : p ∈ S) : 0 < (Complex.equivRealProdCLM.symm p).im := by
    simpa [Complex.equivRealProdCLM_symm_apply] using hpositive hp
  have hc : ContinuousOn lift S := by
    intro p hp
    exact (ContinuousAt.comp (f := fun q : ℝ × ℝ => Complex.equivRealProdCLM.symm q)
      (UpperHalfPlane.contMDiffAt_ofComplex (n := 0) (hpos p hp)).continuousAt
      Complex.equivRealProdCLM.symm.continuous.continuousAt).continuousWithinAt
  have he : lift '' S = {z : UpperHalfPlane | (z.re,z.im) ∈ S} := by
    ext z
    constructor
    · rintro ⟨p,hp,rfl⟩
      have hpair : ((lift p).re,(lift p).im) = p := by
        change Complex.equivRealProdCLM ((lift p : UpperHalfPlane) : ℂ) = p
        simp only [lift, UpperHalfPlane.ofComplex_apply_of_im_pos (hpos p hp)]
        exact Complex.equivRealProdCLM.apply_symm_apply p
      change ((lift p).re,(lift p).im) ∈ S
      rwa [hpair]
    · intro hz
      refine ⟨(z.re,z.im),hz,?_⟩
      have hz' : Complex.equivRealProdCLM.symm (z.re,z.im) = (z : ℂ) :=
        Complex.equivRealProdCLM.symm_apply_apply (z : ℂ)
      simp only [lift,hz',UpperHalfPlane.ofComplex_apply]
  rw [← he]
  exact hS.image_of_continuousOn hc

theorem spectralCoreChart_compact (A a b : ℝ) (ha : 0 < a) :
    IsCompact {z : UpperHalfPlane | (z.re,z.im) ∈ spectralPlaneRectangle A a b} :=
  spectralCoreChart_compact_of_positive (spectralPlaneRectangle_compact A a b)
    (fun _ hp => ha.trans_le hp.2.1)

end
end ArtinMatthews
