module

public import ArtinMatthews.MarkedMajorLabelEndpointIdentity
public import ArtinMatthews.MarkedMajorLabelMeanConjugate
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

/-! The literal conjugated centered source coefficient has the same exact
endpoint normalization, with reversed logarithmic modulation. -/
namespace ArtinMatthews
open Finset ComplexConjugate

noncomputable def markedMajorLabelConjugateTripleCoefficient {J : Type*} [Fintype J]
    (bands : J → Finset ℕ) (cutoff : ℝ → ℂ) {k q : ℕ}
    (χb : DirichletCharacter ℂ k) (θ Y : ℝ) (χ : DirichletCharacter ℂ q)
    (W modulation : ℝ) (β : ℕ → ℂ) (z : ℕ×(ℕ×ℕ)) : ℂ :=
  markedMajorLabelWeight bands cutoff χb θ Y z.1*
    (conj (markedMajorCenteredCoefficient W modulation z.2.1)*χ z.2.1)*β z.2.2

theorem markedMajorLabelConjugateTripleCoefficient_eq {J : Type*} [Fintype J]
    (bands : J → Finset ℕ) (cutoff : ℝ → ℂ) {k q : ℕ}
    (χb : DirichletCharacter ℂ k) (θ Y : ℝ) (χ : DirichletCharacter ℂ q)
    (W modulation : ℝ) (β : ℕ → ℂ) :
    markedMajorLabelConjugateTripleCoefficient bands cutoff χb θ Y χ W modulation β =
      markedMajorLabelTripleCoefficient bands cutoff χb θ Y χ W (-modulation) β := by
  funext z
  simp only [markedMajorLabelConjugateTripleCoefficient,markedMajorLabelTripleCoefficient,
    marked_centered_coefficient_conj]

theorem markedMajorLabel_conjugate_endpoint_identity {J : Type*} [Fintype J]
    (bands : J → Finset ℕ) (hbands : ∀ j p,p ∈ bands j → p.Prime)
    (cutoff : ℝ → ℂ) {k q : ℕ}
    (χb : DirichletCharacter ℂ k) (θ Y : ℝ) (χ : DirichletCharacter ℂ q)
    (W modulation H u v U : ℝ) (l r : ℕ) (β : ℕ → ℂ)
    (hY : Y ≠ 0) (hH : H ≠ 0) (hU : U ≠ 0) (hl : 0 < l) (t : ℝ) :
    markedMajorEndpointPolynomial (markedMajorLabelTripleSet bands u v l r)
      (markedMajorLabelConjugateTripleCoefficient bands cutoff χb θ Y χ W modulation β)
      markedMajorLabelTripleValue t =
      ((Y*H*U:ℝ):ℂ)*markedMajorLabelConjugateEndpoint bands cutoff χb θ Y χ W modulation H u v U l r β t := by
  rw [markedMajorLabelConjugateTripleCoefficient_eq,markedMajorLabelConjugateEndpoint_eq]
  exact markedMajorLabel_endpoint_identity bands hbands cutoff χb θ Y χ W (-modulation) H u v U l r β hY hH hU hl t

theorem markedMajorLabel_conjugate_scaled_endpoint_identity {J : Type*} [Fintype J]
    (bands : J → Finset ℕ) (hbands : ∀ j p,p ∈ bands j → p.Prime)
    (cutoff : ℝ → ℂ) {k q : ℕ}
    (χb : DirichletCharacter ℂ k) (θ Y : ℝ) (χ : DirichletCharacter ℂ q)
    (W modulation H u v U : ℝ) (l r : ℕ) (β : ℕ → ℂ)
    (hY : 0 < Y) (hH : 0 < H) (hU : 0 < U) (hl : 0 < l) (t : ℝ) :
    markedMajorEndpointPolynomial (markedMajorLabelTripleSet bands u v l r)
      (markedMajorLabelConjugateTripleCoefficient bands cutoff χb θ Y χ W modulation β)
      (fun z => markedMajorLabelTripleValue z/(Y*H*U)) t =
      Complex.exp (-(Complex.I*(t:ℂ)*(Real.log (Y*H*U):ℂ)))*
        (((Y*H*U:ℝ):ℂ)*markedMajorLabelConjugateEndpoint bands cutoff χb θ Y χ W modulation H u v U l r β t) := by
  rw [markedMajorLabelConjugateTripleCoefficient_eq,markedMajorLabelConjugateEndpoint_eq]
  exact markedMajorLabel_scaled_endpoint_identity bands hbands cutoff χb θ Y χ W (-modulation) H u v U l r β hY hH hU hl t

end ArtinMatthews
