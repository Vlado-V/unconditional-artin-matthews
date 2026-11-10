module

public import ArtinMatthews.GiantSignedRawPositiveAverage
public import ArtinMatthews.GiantSignedRawSourceGateMass
public import ArtinMatthews.GiantSignedRawCoreGrowth
public import ArtinMatthews.GiantSignedRawGateAverage
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
public import Mathlib.Tactic.Monotonicity.Lemmas
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
public import Mathlib.Topology.Sheaves.Presheaf


set_option backward.privateInPublic true
@[expose] public section

/-! Exact outer gate mass multiplies the actual degree-weighted row bound. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell M : ℕ}
    [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]
    [∀ g, ∀ p : PB g, NeZero p.val]
    {C : B → Finset (Fin k)}

def giantSignedRawMemoryWeight (v : ℝ) (s : GiantSignedState PS PB M) : ℝ :=
  v ^ (∑ j, s.2.2.1 j)

theorem giantSignedRawMemoryWeight_pos {v : ℝ} (hv : 1 ≤ v)
    (s : GiantSignedState PS PB M) : 0 < giantSignedRawMemoryWeight v s :=
  pow_pos (zero_lt_one.trans_le hv) _

def giantSignedRawDegreeRowConstant (S B : Type*) [Fintype S] [Fintype B]
    (ρ v vmin massMax BS : ℝ) (tmax : ℕ) : ℝ :=
  BS ^ Fintype.card S *
    (giantSignedEdgeUniformConstant ρ v vmin⁻¹ massMax tmax) ^ Fintype.card B

theorem giantSignedRawDegreeRowConstant_nonneg
    {ρ v vmin massMax BS : ℝ} {tmax : ℕ} (hρ1 : ρ < 1) (hv : 1 ≤ v) (hBS : 0 ≤ BS) :
    0 ≤ giantSignedRawDegreeRowConstant S B ρ v vmin massMax BS tmax :=
  mul_nonneg (pow_nonneg hBS _)
    (pow_nonneg (giantSignedEdgeUniformConstant_nonneg hρ1 (zero_le_one.trans hv)) _)

theorem giantSignedRawPositiveWeightedGate_bound
    (hPS : ∀ j p, p ∈ PS j → p.Prime)
    (hdis : Pairwise (fun i j => Disjoint (PS i) (PS j)))
    (hVS : ∀ j, 0 < bandReciprocalMass (PS j))
    (hVB : ∀ j, 0 < bandReciprocalMass (PB j))
    (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p) (V : B → ℝ)
    {vmin massMax q ρ v BS : ℝ}
    (hvmin : 0 < vmin) (hVmin : ∀ g, vmin ≤ V g)
    (hMass : ∀ g, (∑ p : PB g, ν g p) ≤ massMax)
    (hq : 0 < q) (hq1 : q ≤ 1) (hBS : 0 ≤ BS)
    (hsmall : ∀ j (z : ℕ), (bandReciprocalMass (PS j))⁻¹ ^ ell *
      ((z : ℝ) + (ell : ℝ)) ^ ell * q ^ ((z : ℝ) / 2) ≤ BS)
    (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (hv : 1 ≤ v)
    (budget : ℕ) (hC : ∀ g, (C g).card ≤ budget) (κ : ℤ)
    (gate : GiantSignedRawOuterChoice (S := S) PB C ell → Prop)
    (s : GiantSignedState PS PB (k+ell)) :
    (∑ r : GiantSignedRawEdgeMove PS PB ell C s.2.2,
      giantSignedRawPositiveCoefficient ν V κ q ρ s r *
        (if gate (giantSignedRawMoveOuter r) then
          giantSignedRawMemoryWeight v (giantSignedRawEdgeTarget κ s r) else 0)) ≤
      (∑ i, if gate i then giantSignedRawOuterWeight i else 0) *
        (giantSignedRawDegreeRowConstant S B ρ v vmin massMax BS (ell+budget) *
          giantSignedRawMemoryWeight v s) := by
  let I := GiantSignedRawOuterChoice (S := S) PB C ell
  let φ : GiantSignedState PS PB (k+ell) → ℝ := giantSignedRawMemoryWeight v
  let A := giantSignedRawDegreeRowConstant S B ρ v vmin massMax BS (ell+budget)
  have hφ (t : GiantSignedState PS PB (k+ell)) : 0 ≤ φ t :=
    (giantSignedRawMemoryWeight_pos hv t).le
  rw [giantSignedRawPositiveGate_average ν hν V (fun g => hvmin.trans_le (hVmin g)) κ q hρ gate φ hφ s]
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  let f (t : GiantSignedState PS PB (k+ell)) : ℂ :=
    (φ ((giantTwoSidedResiduePermute i.2.1.1).symm t.1,
      (giantSignedGroupedTuplePermutation i.2.1.2).symm t.2.1, t.2.2) : ℂ)
  let src := giantSignedStatePermute PS i.1.1 i.1.2 s
  have hf (t : GiantSignedState PS PB (k+ell)) :
      ‖f t‖ ≤ (1 : ℝ) * v ^ (∑ j, t.2.2.1 j) := by
    change ‖(φ t : ℂ)‖ ≤ 1 * φ t
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hφ t), one_mul, le_refl]
  have hrow : ‖giantSignedRawCoreApply ν V κ q ρ i.2.2 f src‖ ≤ A * φ s := by
    have he := giantSignedRawCoreApply_row_bound hPS hdis hVS ν hν V hvmin hVmin
      hMass hq hq1 hBS hsmall hρ hρ1 zero_le_one hv budget hC κ i.2.2 f hf src
    change _ ≤ (1 : ℝ) * φ s *
      (giantSignedEdgeUniformConstant ρ v vmin⁻¹ massMax (ell+budget)) ^ Fintype.card B *
      BS ^ Fintype.card S at he
    exact he.trans_eq (by simp only [A, giantSignedRawDegreeRowConstant, one_mul]; ac_rfl)
  change giantSignedRawOuterWeight i * (if gate i then ‖giantSignedRawCoreApply ν V κ q ρ i.2.2 f src‖
    else 0) ≤ (if gate i then giantSignedRawOuterWeight i else 0) * (A * φ s)
  split_ifs
  · exact mul_le_mul_of_nonneg_left hrow (giantSignedRawOuterWeight_nonneg hVB i)
  · simp only [zero_mul, mul_zero, le_refl]

end
end ArtinMatthews
