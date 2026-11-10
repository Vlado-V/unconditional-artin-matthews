module

public import ArtinMatthews.GiantTwoSidedExpandedRootTransfer
public import ArtinMatthews.GiantTwoSidedResidueAbsolutePaths
public import ArtinMatthews.GiantTwoSidedRootErrorBudget
public import ArtinMatthews.GiantTwoSidedRootIntervalBudget
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

/-! The full weighted root replacement has arbitrary logarithmic
saving after the actual absolute Haar path mass is summed. -/
namespace ArtinMatthews
open Finset Filter
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

theorem giantCandidateWeightedRootTransfer {I : Type*} (k ell m₀ : ℕ)
    (C₁ C₂ G : ℝ) (hG : 0 ≤ G) {γ q : ℝ} (hγ : 0<γ) (hq0 : 0<q) (hq1 : q<1) :
    ∀ᶠ x : ℝ in atTop,∀ S : Finset (GiantCandidateGroupIndex x),
      let P (j : S) := giantCandidateGroup x j.val
      ∀ (nz : ∀ p : ↥(markedPhysicalBandPrimes P),NeZero p.val),
      letI : ∀ p : ↥(markedPhysicalBandPrimes P),NeZero p.val := nz
      let n := giantTwoSidedSourceMomentLength x
      ∀ (patterns : Fin n → Finset I) (C : Fin n → I → S → Finset (Fin k)),
        (∀ i ν,ν∈patterns i → ∀ j,(C i ν j).card ≤ m₀) →
      ∀ (step : Fin n → ℤ),
        (∀ i,((step i).natAbs:ℝ) ≤ (Real.log x)^C₂) →
      ∀ (ζ : Fin n → ℝ) (K : ∀ i ν,GiantTwoSidedPatternCoefficient P (C i ν) ell)
        (K₀ : Fin n → I → ℝ),
        (∀ i ν,ν∈patterns i → 0 ≤ K₀ i ν ∧ ∀ b c a,‖K i ν b c a‖ ≤ K₀ i ν) →
        (∀ i,(∑ ν∈patterns i,K₀ i ν) ≤ (Real.log x)^C₁) →
      ∀ X : ℝ,x^γ ≤ X →
        ‖giantTwoSidedExpandedPhysicalMoment patterns C step q ζ K
            (giantTwoSidedRootInterval X) (giantTwoSidedRootSlice X) -
          (((⌈2*X⌉₊-⌈X⌉₊:ℕ):ℝ):ℂ)*giantTwoSidedExpandedIndependentMoment patterns C step q ζ K‖ /
            ((⌈2*X⌉₊-⌈X⌉₊:ℕ):ℝ) ≤ (Real.log x)^(-G*(n:ℝ)) := by
  obtain ⟨B,_hB,hpaths⟩ := giantCandidateResidueExpandedRoot_pathMass_eventually
    (I:=I) ell m₀ hq0 hq1 C₁
  let D := max (C₁+B) 0
  have hD : 0 ≤ D := le_max_right _ _
  have hA : 0 ≤ D+G+1 := by linarith
  filter_upwards [giantCandidateExpandedMoment_root_error (I:=I) k ell C₂ (D+G+1) hA
      hγ hq0.le hq1.le,hpaths,giantCandidateRootError_absorb hD hG hγ,
    giantCandidateRootInterval_budget hγ,Real.tendsto_log_atTop.eventually_ge_atTop (1:ℝ)]
    with x herr hmass habs hinterval hlog
  intro S
  let P (j : S) := giantCandidateGroup x j.val
  dsimp only
  intro nz
  let : ∀ p : ↥(markedPhysicalBandPrimes P),NeZero p.val := nz
  intro patterns C hC step hstep ζ K K₀ hK hKmass X hX
  let n := giantTwoSidedSourceMomentLength x
  let L := Real.log x
  let length := ((⌈2*X⌉₊-⌈X⌉₊:ℕ):ℝ)
  let E := 2*L^(-(D+G+1)*(n:ℝ))+Real.exp (-γ*L/4)
  have hlength : 0<length := (Real.exp_pos _).trans_le (hinterval X hX).2
  have hL : 0<L := zero_lt_one.trans_le hlog
  have hE : 0 ≤ E := add_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg hL.le _)) (Real.exp_nonneg _)
  have hmass' : giantTwoSidedResidueExpandedRootMass patterns C step q ζ K ≤ L^(D*(n:ℝ)) := by
    calc
      _ ≤ (L^(C₁+B))^n := hmass S nz k n (giantTwoSidedSourceMomentLength_pos hL).ne'
        patterns C hC step ζ K K₀ hK hKmass
      _ ≤ (L^D)^n := pow_le_pow_left₀ (Real.rpow_nonneg hL.le _)
        (Real.rpow_le_rpow_of_exponent_le hlog (le_max_left _ _)) _
      _ = _ := (Real.rpow_mul_natCast hL.le D n).symm
  apply (div_le_iff₀ hlength).mpr
  calc
    _ ≤ E*length*giantTwoSidedResidueExpandedRootMass patterns C step q ζ K :=
      herr S nz patterns C step hstep X hX ζ K
    _ ≤ E*length*L^(D*(n:ℝ)) := mul_le_mul_of_nonneg_left hmass' (mul_nonneg hE hlength.le)
    _ = length*(E*L^(D*(n:ℝ))) := by ring
    _ ≤ length*L^(-G*(n:ℝ)) := mul_le_mul_of_nonneg_left habs hlength.le
    _ = _ := by ring

end
end ArtinMatthews
