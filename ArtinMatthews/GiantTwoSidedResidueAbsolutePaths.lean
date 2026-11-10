module

public import ArtinMatthews.GiantTwoSidedResiduePathExpansion
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

/-! The fully expanded positive-length Haar path mass obeys the same
logarithmic bound as the actual absolute transition matrix. -/
namespace ArtinMatthews
open Finset Filter
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

theorem giantCandidateResidueExpandedRoot_pathMass_eventually {I : Type*} (ell m₀ : ℕ)
    {q : ℝ} (hq : 0<q) (hq1 : q<1) (C₁ : ℝ) :
    ∃ A : ℝ,0 ≤ A ∧ ∀ᶠ x : ℝ in atTop,∀ S : Finset (GiantCandidateGroupIndex x),
      let P (j : S) := giantCandidateGroup x j.val
      ∀ (nz : ∀ p : ↥(markedPhysicalBandPrimes P),NeZero p.val),
      letI : ∀ p : ↥(markedPhysicalBandPrimes P),NeZero p.val := nz
      ∀ (k n : ℕ),n≠0 →
      ∀ (patterns : Fin n → Finset I) (C : Fin n → I → S → Finset (Fin k)),
        (∀ i ν,ν∈patterns i → ∀ j,(C i ν j).card ≤ m₀) →
      ∀ (step : Fin n → ℤ) (ζ : Fin n → ℝ)
        (K : ∀ i ν,GiantTwoSidedPatternCoefficient P (C i ν) ell) (K₀ : Fin n → I → ℝ),
        (∀ i ν,ν∈patterns i → 0 ≤ K₀ i ν ∧ ∀ b c a,‖K i ν b c a‖ ≤ K₀ i ν) →
        (∀ i,(∑ ν∈patterns i,K₀ i ν) ≤ (Real.log x)^C₁) →
        giantTwoSidedResidueExpandedRootMass patterns C step q ζ K ≤ ((Real.log x)^(C₁+A))^n := by
  obtain ⟨A,hA,h⟩ := giantCandidateResidueFamily_pathMass_eventually (I:=I) ell m₀ hq hq1 C₁
  refine ⟨A,hA,?_⟩
  filter_upwards [h,giantCandidateSelectedGroups_geometry_eventually,
    giantCandidateFullPrimes_prime_upper_eventually] with x hx hgeo hprime
  intro S
  let P (j : S) := giantCandidateGroup x j.val
  dsimp only
  intro nz
  let : ∀ p : ↥(markedPhysicalBandPrimes P),NeZero p.val := nz
  intro k n hn
  cases n with
  | zero => exact (hn rfl).elim
  | succ n =>
    intro patterns C hC step ζ K K₀ hK hmass
    have hP (j : S) (p : ℕ) (hp : p∈P j) : p.Prime :=
      (hprime p (mem_giantCandidateFullPrimes.mpr ⟨j.val,hp⟩)).1
    have hV (j : S) : 0<bandReciprocalMass (P j) :=
      (div_pos (Real.log_pos (by norm_num)) (by norm_num)).trans ((hgeo S).2.1 j).1
    rw [giantTwoSidedResidueExpandedRootMass_eq hP (hgeo S).1 hV patterns C step hq.le ζ K]
    exact hx S nz k (n+1) patterns C hC step ζ K K₀ hK hmass

end
end ArtinMatthews
