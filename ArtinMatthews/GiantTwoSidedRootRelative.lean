module

public import ArtinMatthews.GiantSourceResidueMass
public import ArtinMatthews.GiantTwoSidedActiveModulus
public import ArtinMatthews.GiantTwoSidedActiveResidueWeight
public import ArtinMatthews.GiantTwoSidedRootMargin
public import ArtinMatthews.GiantTwoSidedRootWeight
public import ArtinMatthews.GiantSourceResidueRelative
public import ArtinMatthews.GiantTwoSidedRootCRTCount
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

/-! Uniform relative replacement of the original path-residue sum.
The deterministic active damping is multiplied back without division. -/
namespace ArtinMatthews
open Finset Filter
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

def giantTwoSidedRootDensity (x : ℝ) (S : Finset (GiantCandidateGroupIndex x))
    {M : ℕ} (labels : Fin (giantTwoSidedSourceMomentLength x+1) →
      MarkedPhysicalMarking (fun i : S => giantCandidateGroup x i.val) M)
    (q : ℝ) (offset : Fin (giantTwoSidedSourceMomentLength x+1) → ℤ) : ℝ :=
  if GiantTwoSidedActiveCompatible univ labels offset then
    giantTwoSidedActiveResidueWeight univ labels
      (markedMemoryVisitQ q (giantTwoSidedSourceMomentLength x)) offset /
        giantTwoSidedActiveModulus labels *
      ∏ p∈giantSourceInactivePrimes x S labels,
        (1-scalarWeightedResidueMean (giantSourceResidueLoss x q offset) p)
  else 0

theorem giantCandidateRootResidue_relative (M : ℕ) (A : ℝ) (hA : 0≤A)
    {γ : ℝ} (hγ : 0<γ) :
    ∀ᶠ x : ℝ in atTop,∀ (S : Finset (GiantCandidateGroupIndex x))
      (labels : Fin (giantTwoSidedSourceMomentLength x+1) →
        MarkedPhysicalMarking (fun i : S => giantCandidateGroup x i.val) M)
      (q : ℝ),0≤q → q≤1 →
      ∀ (offset : Fin (giantTwoSidedSourceMomentLength x+1) → ℤ) (X : ℝ),x^γ≤X →
        |(∑ root∈giantTwoSidedRootInterval X,
            giantTwoSidedRootResidueFactor (fun i : S => giantCandidateGroup x i.val)
              labels q offset (root:ℤ)) -
          ((⌈2*X⌉₊-⌈X⌉₊:ℕ):ℝ)*giantTwoSidedRootDensity x S labels q offset| ≤
          (2*(Real.log x)^(-A*(giantTwoSidedSourceMomentLength x:ℝ))+
            Real.exp (-γ*Real.log x/4))*
            (((⌈2*X⌉₊-⌈X⌉₊:ℕ):ℝ)*giantTwoSidedRootDensity x S labels q offset) := by
  filter_upwards [giantCandidateSourceResidue_relative M A hA hγ,
    giantSourceResidueMean_cap,giantCandidateRootInterval_budget hγ,
    giantCandidateSelectedGroups_geometry_eventually,
    eventually_gt_atTop (1:ℝ),Real.tendsto_log_atTop.eventually_ge_atTop (1:ℝ)]
    with x hrelative hcap hinterval hgeo hx hL
  intro S labels q hq0 hq1 offset X hX
  let P (i : S) := giantCandidateGroup x i.val
  have hP (i : S) (p : ℕ) (hp : p∈P i) : p.Prime :=
    (giantCandidateFullPrimes_range hx hL (mem_giantCandidateFullPrimes.mpr ⟨i.val,hp⟩)).1
  let Q := giantTwoSidedActiveModulus labels
  let U := giantTwoSidedActiveResidueWeight univ labels
    (markedMemoryVisitQ q (giantTwoSidedSourceMomentLength x)) offset
  let V := ∏ p∈giantSourceInactivePrimes x S labels,
    (1-scalarWeightedResidueMean (giantSourceResidueLoss x q offset) p)
  let H := ((⌈2*X⌉₊-⌈X⌉₊:ℕ):ℝ)/(Q:ℝ)
  let E := 2*(Real.log x)^(-A*(giantTwoSidedSourceMomentLength x:ℝ))+
    Real.exp (-γ*Real.log x/4)
  have hU : 0≤U := by
    apply prod_nonneg
    intro p _
    apply prod_nonneg
    intro v _
    split_ifs
    · exact zero_le_one
    · exact (giantSourceVisitQ_bounds hq0 hq1 _ v).1
    · exact zero_le_one
  simp only [giantTwoSidedRootInterval]
  by_cases hc : GiantTwoSidedActiveCompatible univ labels offset
  · have hQ : 0<Q := giantTwoSidedActiveModulus_pos hP labels
    have hH : 0<H := div_pos ((Real.exp_pos _).trans_le (hinterval X hX).2)
      (Nat.cast_pos.mpr hQ)
    have hV : 0<V := by
      apply prod_pos
      intro p hp
      have hb := hcap q hq0 hq1 offset p (giantSourceInactivePrimes_subset x S labels hp)
      linarith
    let C := scalarWeightedResidueCountIco (giantSourceInactivePrimes x S labels)
      (giantSourceResidueLoss x q offset) ⌈X⌉₊ ⌈2*X⌉₊ Q
      (giantTwoSidedRootClass hP labels offset)
    have hr := hrelative S labels q hq0 hq1 offset X hX
      (giantTwoSidedRootClass hP labels offset)
    change |C-H*V|/(H*V)≤E at hr
    have hr' := (div_le_iff₀ (mul_pos hH hV)).mp hr
    rw [giantTwoSidedRootResidue_sum_eq_count hP (hgeo S).1 labels q offset hc ⌈X⌉₊ ⌈2*X⌉₊]
    unfold giantTwoSidedRootDensity
    rw [ite_eq_left hc]
    change |U*C-((⌈2*X⌉₊-⌈X⌉₊:ℕ):ℝ)*(U/Q*V)| ≤
      E*(((⌈2*X⌉₊-⌈X⌉₊:ℕ):ℝ)*(U/Q*V))
    calc
      _ = U*|C-H*V| := by
        rw [show U*C-((⌈2*X⌉₊-⌈X⌉₊:ℕ):ℝ)*(U/Q*V)=U*(C-H*V) by dsimp [H];ring,
          abs_mul,abs_of_nonneg hU]
      _ ≤ U*(E*(H*V)) := mul_le_mul_of_nonneg_left hr' hU
      _ = _ := by dsimp [H];ring
  · rw [giantTwoSidedRootResidue_sum_incompatible (hgeo S).1 labels q offset hc ⌈X⌉₊ ⌈2*X⌉₊]
    simp only [giantTwoSidedRootDensity,ite_eq_right hc,mul_zero,sub_zero,abs_zero]
    exact le_rfl

end
end ArtinMatthews
