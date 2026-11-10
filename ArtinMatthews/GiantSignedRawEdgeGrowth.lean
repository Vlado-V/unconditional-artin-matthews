module

public import ArtinMatthews.GiantSignedRawPositiveAverage
public import ArtinMatthews.GiantSignedRawCoreGrowth
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

/-! Exponential closure of the original raw edge follows from its exact
four-permutation auxiliary average and the literal memory row bound. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {S B I : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell : ℕ}
    [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]
    [∀ g, ∀ p : PB g, NeZero p.val]

section Single
variable {C : B → Finset (Fin k)}

theorem giantSignedRawPositiveApply_row_bound
    (hPS : ∀ j p, p ∈ PS j → p.Prime)
    (hdis : Pairwise (fun i j => Disjoint (PS i) (PS j)))
    (hVS : ∀ j, 0 < bandReciprocalMass (PS j))
    (hVB : ∀ g, 0 < bandReciprocalMass (PB g))
    (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p) (V : B → ℝ)
    {vmin massMax q ρ U u BS : ℝ}
    (hvmin : 0 < vmin) (hV : ∀ g, vmin ≤ V g)
    (hMass : ∀ g, (∑ p : PB g, ν g p) ≤ massMax)
    (hq : 0 < q) (hq1 : q ≤ 1) (hBS : 0 ≤ BS)
    (hbudget : ∀ j (z : ℕ),
      (bandReciprocalMass (PS j))⁻¹ ^ ell * ((z : ℝ) + (ell : ℝ)) ^ ell *
        q ^ ((z : ℝ) / 2) ≤ BS)
    (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (hU : 0 ≤ U) (hu : 1 ≤ u)
    (budget : ℕ) (hC : ∀ g, (C g).card ≤ budget) (κ : ℤ)
    (f : GiantSignedState PS PB (k+ell) → ℂ)
    (hf : ∀ s, ‖f s‖ ≤ U * u ^ (∑ g, s.2.2.1 g))
    (s : GiantSignedState PS PB (k+ell)) :
    giantSignedRawPositiveApply (C := C) ν V κ q ρ (fun t => ‖f t‖) s ≤
      U * u ^ (∑ g, s.2.2.1 g) *
        (giantSignedEdgeUniformConstant ρ u vmin⁻¹ massMax (ell+budget)) ^ Fintype.card B *
          BS ^ Fintype.card S := by
  classical
  let R := U * u ^ (∑ g, s.2.2.1 g) *
    (giantSignedEdgeUniformConstant ρ u vmin⁻¹ massMax (ell+budget)) ^ Fintype.card B *
      BS ^ Fintype.card S
  rw [giantSignedRawPositiveApply_average ν hν V
    (fun g => lt_of_lt_of_le hvmin (hV g)) κ q hρ (fun t => ‖f t‖) (fun _ => norm_nonneg _) s]
  have hi (i : GiantSignedRawOuterChoice (S := S) PB C ell) :
      ‖giantSignedRawCoreApply ν V κ q ρ i.2.2
        (fun t => (‖f ((giantTwoSidedResiduePermute i.2.1.1).symm t.1,
          (giantSignedGroupedTuplePermutation i.2.1.2).symm t.2.1, t.2.2)‖ : ℂ))
        (giantSignedStatePermute PS i.1.1 i.1.2 s)‖ ≤ R := by
    apply giantSignedRawCoreApply_row_bound hPS hdis hVS ν hν V hvmin hV hMass
      hq hq1 hBS hbudget hρ hρ1 hU hu budget hC κ i.2.2
    intro t
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    exact hf _
  calc
    _ ≤ ∑ i : GiantSignedRawOuterChoice (S := S) PB C ell, giantSignedRawOuterWeight i * R :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hi i)
        (giantSignedRawOuterWeight_nonneg hVB i))
    _ = R := by rw [← Finset.sum_mul, giantSignedRawOuterWeight_sum C hVB, one_mul]

theorem giantSignedRawEdgeApply_row_bound
    (hPS : ∀ j p, p ∈ PS j → p.Prime) (hPB : ∀ j p, p ∈ PB j → p.Prime)
    (hdis : Pairwise (fun i j => Disjoint (PS i) (PS j)))
    (hVS : ∀ j, 0 < bandReciprocalMass (PS j))
    (hVB : ∀ g, 0 < bandReciprocalMass (PB g))
    (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p) (V : B → ℝ)
    {vmin massMax q ρ U u BS W : ℝ}
    (hvmin : 0 < vmin) (hV : ∀ g, vmin ≤ V g)
    (hMass : ∀ g, (∑ p : PB g, ν g p) ≤ massMax)
    (hq : 0 < q) (hq1 : q ≤ 1) (hBS : 0 ≤ BS)
    (hbudget : ∀ j (z : ℕ),
      (bandReciprocalMass (PS j))⁻¹ ^ ell * ((z : ℝ) + (ell : ℝ)) ^ ell *
        q ^ ((z : ℝ) / 2) ≤ BS)
    (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (hU : 0 ≤ U) (hu : 1 ≤ u)
    (hW : 0 ≤ W) (budget : ℕ) (hC : ∀ g, (C g).card ≤ budget)
    (κ : ℤ) (θ ζ : ℝ) (K : GiantTwoSidedPatternCoefficient PB C ell)
    (hK : ∀ a b aux, ‖K a b aux‖ ≤ W)
    (η : (s : GiantSignedState PS PB (k+ell)) →
      GiantSignedRawEdgeMove PS PB ell C s.2.2 → ℂ)
    (hη : ∀ s r, ‖η s r‖ ≤ 1)
    (f : GiantSignedState PS PB (k+ell) → ℂ)
    (hf : ∀ s, ‖f s‖ ≤ U * u ^ (∑ g, s.2.2.1 g))
    (s : GiantSignedState PS PB (k+ell)) :
    ‖giantSignedRawEdgeApply ν V κ q ρ θ ζ K η f s‖ ≤
      W * U * u ^ (∑ g, s.2.2.1 g) *
        (giantSignedEdgeUniformConstant ρ u vmin⁻¹ massMax (ell+budget)) ^ Fintype.card B *
          BS ^ Fintype.card S := by
  calc
    _ ≤ W * giantSignedRawPositiveApply (C := C) ν V κ q ρ (fun t => ‖f t‖) s :=
      giantSignedRawEdgeApply_norm_le_positive hPS hPB hVS hVB ν V κ hq.le
        ρ θ ζ W hW K hK η hη f s
    _ ≤ W * (U * u ^ (∑ g, s.2.2.1 g) *
        (giantSignedEdgeUniformConstant ρ u vmin⁻¹ massMax (ell+budget)) ^ Fintype.card B *
          BS ^ Fintype.card S) := mul_le_mul_of_nonneg_left
      (giantSignedRawPositiveApply_row_bound hPS hdis hVS hVB ν hν V hvmin hV hMass
        hq hq1 hBS hbudget hρ hρ1 hU hu budget hC κ f hf s) hW
    _ = _ := by ring

end Single

theorem giantSignedRawEdgeFamilyApply_row_bound
    (hPS : ∀ j p, p ∈ PS j → p.Prime) (hPB : ∀ j p, p ∈ PB j → p.Prime)
    (hdis : Pairwise (fun i j => Disjoint (PS i) (PS j)))
    (hVS : ∀ j, 0 < bandReciprocalMass (PS j))
    (hVB : ∀ g, 0 < bandReciprocalMass (PB g))
    (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p) (V : B → ℝ)
    {vmin massMax q ρ U u BS W : ℝ}
    (hvmin : 0 < vmin) (hV : ∀ g, vmin ≤ V g)
    (hMass : ∀ g, (∑ p : PB g, ν g p) ≤ massMax)
    (hq : 0 < q) (hq1 : q ≤ 1) (hBS : 0 ≤ BS)
    (hbudget : ∀ j (z : ℕ),
      (bandReciprocalMass (PS j))⁻¹ ^ ell * ((z : ℝ) + (ell : ℝ)) ^ ell *
        q ^ ((z : ℝ) / 2) ≤ BS)
    (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (hU : 0 ≤ U) (hu : 1 ≤ u) (hW : 0 ≤ W)
    (budget : ℕ) (patterns : Finset I) (C : I → B → Finset (Fin k))
    (hC : ∀ i ∈ patterns, ∀ g, (C i g).card ≤ budget)
    (κ : ℤ) (θ ζ : ℝ) (K : ∀ i, GiantTwoSidedPatternCoefficient PB (C i) ell)
    (hK : ∀ i ∈ patterns, ∀ a b aux, ‖K i a b aux‖ ≤ W)
    (η : (i : I) → (s : GiantSignedState PS PB (k+ell)) →
      GiantSignedRawEdgeMove PS PB ell (C i) s.2.2 → ℂ)
    (hη : ∀ i ∈ patterns, ∀ s r, ‖η i s r‖ ≤ 1)
    (f : GiantSignedState PS PB (k+ell) → ℂ)
    (hf : ∀ s, ‖f s‖ ≤ U * u ^ (∑ g, s.2.2.1 g))
    (s : GiantSignedState PS PB (k+ell)) :
    ‖giantSignedRawEdgeFamilyApply ν V patterns C κ q ρ θ ζ K η f s‖ ≤
      (patterns.card : ℝ) * W * U * u ^ (∑ g, s.2.2.1 g) *
        (giantSignedEdgeUniformConstant ρ u vmin⁻¹ massMax (ell+budget)) ^ Fintype.card B *
          BS ^ Fintype.card S := by
  unfold giantSignedRawEdgeFamilyApply
  calc
    _ ≤ ∑ i ∈ patterns, W * U * u ^ (∑ g, s.2.2.1 g) *
        (giantSignedEdgeUniformConstant ρ u vmin⁻¹ massMax (ell+budget)) ^ Fintype.card B *
          BS ^ Fintype.card S := norm_sum_le_of_le _ (fun i hi =>
      giantSignedRawEdgeApply_row_bound hPS hPB hdis hVS hVB ν hν V hvmin hV hMass
        hq hq1 hBS hbudget hρ hρ1 hU hu hW budget (hC i hi) κ θ ζ (K i) (hK i hi)
        (η i) (hη i hi) f hf s)
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring

end
end ArtinMatthews
