module

public import ArtinMatthews.MarkedMajorLabelEndpointConjugateIdentity
public import ArtinMatthews.MarkedMajorLabelFiniteEnergy
public import ArtinMatthews.MarkedMajorLabelFiniteSupport
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

namespace ArtinMatthews
open MeasureTheory Set Finset
noncomputable section

/-- Exact original triple source, with no truncation or cutoff error. -/
theorem markedMajorLabel_full_source_energy {J J' : Type*} [Fintype J] [Fintype J']
    (bands : J → Finset ℕ) (bands' : J' → Finset ℕ)
    (hbands : ∀ j p,p ∈ bands j → p.Prime) (hbands' : ∀ j p,p ∈ bands' j → p.Prime)
    (cutoff : ℝ → ℂ) {lo hi : ℝ} (hlo : 0 < lo) (hinterval : lo < 4*hi)
    (hsupp : Function.support cutoff ⊆ Icc lo hi)
    {k q k' q' : ℕ} (χb : DirichletCharacter ℂ k) (χb' : DirichletCharacter ℂ k')
    (χ : DirichletCharacter ℂ q) (χ' : DirichletCharacter ℂ q')
    (θ θ' theta Y W X H u v U H' u' v' U' modulation modulation' : ℝ)
    (l r l' r' : ℕ) (β β' : ℕ → ℂ)
    (hY : 0 < Y) (hX : 0 < X) (hH : 0 < H) (hU : 0 < U) (hH' : 0 < H') (hU' : 0 < U')
    (hscale : H*U=X) (hscale' : H'*U'=X)
    (hHu : H ≤ u) (huv : u ≤ v) (hvH : v ≤ 2*H) (hl : U ≤ (l:ℝ)) (hr : (r:ℝ) ≤ 2*U)
    (hHu' : H' ≤ u') (huv' : u' ≤ v') (hvH' : v' ≤ 2*H') (hl' : U' ≤ (l':ℝ)) (hr' : (r':ℝ) ≤ 2*U')
    (ψ : SchwartzMap ℝ ℂ) {R : ℝ} (hψ : tsupport ψ ⊆ Icc (-R) R) :
    ‖(Y:ℂ)⁻¹ * ∑ z ∈ markedMajorLabelTripleSet bands u v l r,
      ∑ z' ∈ markedMajorLabelTripleSet bands' u' v' l' r',
      (markedMajorLabelTripleCoefficient bands cutoff χb θ Y χ W modulation β z*
       markedMajorLabelConjugateTripleCoefficient bands' cutoff χb' θ' Y χ' W modulation' β' z')*
      (ψ (X*(markedMajorLabelTripleValue z/(Y*X)-markedMajorLabelTripleValue z'/(Y*X)))*
       OAI.Problem337.RealPhase.phase (theta*(X*(markedMajorLabelTripleValue z/(Y*X)-markedMajorLabelTripleValue z'/(Y*X)))))‖ ≤
      (Y*X)*(∫ p : ℝ × ℝ,
        ‖markedMajorConstructedCoefficient ψ hlo hinterval hψ hX theta (p.1/X,p.2)*
          (markedMajorLabelEndpoint bands cutoff χb θ Y χ W modulation H u v U l r β p.1*
           markedMajorLabelConjugateEndpoint bands' cutoff χb' θ' Y χ' W modulation' H' u' v' U' l' r' β' (p.2-p.1))‖) := by
  have H := markedMajorLabel_finite_source_energy bands bands' hbands hbands' cutoff hlo hinterval hsupp
    χb χb' χ χ' θ θ' theta Y W X H u v U H' u' v' U' modulation modulation'
    l r l' r' β β' hY hX hH hU hH' hU' hscale hscale' hHu huv hvH hl hr hHu' huv' hvH' hl' hr' ψ hψ
  have he := markedMajorSupported_bilateral_sum bands bands' cutoff χb χb' χ χ'
    θ θ' Y W modulation modulation' u v u' v' l r l' r' β β'
    (fun z z' => ψ (X*(markedMajorLabelTripleValue z/(Y*X)-markedMajorLabelTripleValue z'/(Y*X)))*
      OAI.Problem337.RealPhase.phase (theta*(X*(markedMajorLabelTripleValue z/(Y*X)-markedMajorLabelTripleValue z'/(Y*X)))))
  rw [he] at H
  exact H

end
end ArtinMatthews
