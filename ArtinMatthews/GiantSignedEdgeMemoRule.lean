module

public import ArtinMatthews.GiantSignedTraceMemo
public import ArtinMatthews.GiantSignedTraceRows
public import ArtinMatthews.GiantSignedBirthLocalMemo
public import ArtinMatthews.GiantSignedRawConditionalMass
public import ArtinMatthews.GiantSignedRawFreshBirthGate
public import ArtinMatthews.GiantSignedRawBirthConditionalRow
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

/-! The actual family edge retains its performed birth values in the
chronological memo and pays the same nonpivot atom factor in every pattern. -/
namespace ArtinMatthews
open scoped BigOperators ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

universe u
variable {S B I : Type u} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell n H : ℕ}

def giantSignedEdgeMemoRule (hPB : ∀ g p, p ∈ PB g → p.Prime)
    (ν : ∀ g, PB g → ℝ) (V : B → ℝ)
    (patterns : Finset I) (C : I → B → Finset (Fin k)) (κ : ℤ) (q ρ θ ζ : ℝ)
    (K : (a : I) → GiantTwoSidedPatternCoefficient PB (C a) ell)
    (η : (a : I) → (s : GiantSignedState PS PB (k+ell)) →
      GiantSignedRawEdgeMove PS PB ell (C a) s.2.2 → ℂ)
    (v vmin massMax : ℝ) (budget : ℕ) (BS W Δ : ℝ)
    (σ : Equiv.Perm (GiantSignedUniformBirthAddress B (k+ell) n H)) (i : Fin n) :
    GiantSignedTraceMemoRule (GiantSignedBirthMemo B (k+ell) n H)
      (giantSignedEdgeTraceRow ν V patterns C κ q ρ θ ζ K η) where
  update old _ r := giantSignedRawFreshBirthValues hPB i (C r.1.val) r.2.choice.2.1
    (giantSignedBirthClearCurrent (.edge i) old) (giantSignedRawEdgeFreshLabels r.2)
  accept old _ r := giantSignedRawFreshBirthGate hPB σ i (C r.1.val) r.2.choice.2.1
    (giantSignedBirthClearCurrent (.edge i) old) (giantSignedRawEdgeFreshLabels r.2)
  cost := ENNReal.ofReal ((patterns.card : ℝ) * W *
    Δ^(giantSignedUniformBirthStageNonpivots σ (.edge i)).card *
    (giantSignedEdgeUniformConstant ρ v vmin⁻¹ massMax (ell+budget))^Fintype.card B *
    BS^Fintype.card S)

variable [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]
    [∀ g, ∀ p : PB g, NeZero p.val]

theorem giantSignedEdgeMemoRule_mass_le
    (hPS : ∀ j p, p ∈ PS j → p.Prime) (hPB : ∀ j p, p ∈ PB j → p.Prime)
    (hdis : Pairwise (fun a b => Disjoint (PS a) (PS b)))
    (hVS : ∀ j, 0 < bandReciprocalMass (PS j)) (hVB : ∀ g, 0 < bandReciprocalMass (PB g))
    (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p) (V : B → ℝ)
    {vmin massMax q ρ v BS W Δ : ℝ}
    (hvmin : 0 < vmin) (hV : ∀ g, vmin ≤ V g) (hMass : 1 ≤ massMax)
    (hq : 0 < q) (hq1 : q ≤ 1) (hBS : 0 ≤ BS)
    (hbudget : ∀ j (z : ℕ),
      (bandReciprocalMass (PS j))⁻¹ ^ ell * ((z : ℝ) + (ell : ℝ)) ^ ell *
        q ^ ((z : ℝ)/2) ≤ BS)
    (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (hv : 1 ≤ v)
    (hW : 0 ≤ W) (hΔ : 0 ≤ Δ) (budget : ℕ)
    (patterns : Finset I) (C : I → B → Finset (Fin k))
    (hC : ∀ a ∈ patterns, ∀ g, (C a g).card ≤ budget)
    (κ : ℤ) (θ ζ : ℝ)
    (K : (a : I) → GiantTwoSidedPatternCoefficient PB (C a) ell)
    (hK : ∀ a ∈ patterns, ∀ x y aux, ‖K a x y aux‖ ≤ W)
    (η : (a : I) → (s : GiantSignedState PS PB (k+ell)) →
      GiantSignedRawEdgeMove PS PB ell (C a) s.2.2 → ℂ)
    (hη : ∀ a ∈ patterns, ∀ s r, ‖η a s r‖ ≤ 1)
    (hatom : ∀ g p, ν g p ≤ Δ) (hνmass : ∀ g, (∑ p : PB g, ν g p) ≤ massMax)
    (σ : Equiv.Perm (GiantSignedUniformBirthAddress B (k+ell) n H)) (i : Fin n)
    (old : GiantSignedBirthMemo B (k+ell) n H) (s : GiantSignedState PS PB (k+ell)) :
    let E := giantSignedEdgeTraceRow ν V patterns C κ q ρ θ ζ K η
    let R := giantSignedEdgeMemoRule hPB ν V patterns C κ q ρ θ ζ K η
      v vmin massMax budget BS W Δ σ i
    let gauge := fun t : GiantSignedState PS PB (k+ell) => ENNReal.ofReal (v^(∑ g, t.2.2.1 g))
    (∑' r : E.Move s, if R.accept old s r then
      ENNReal.ofReal ‖E.coefficient s r‖ * gauge (E.target s r) else 0) ≤ R.cost * gauge s := by
  dsimp only
  let cleared := giantSignedBirthClearCurrent (.edge i) old
  let exponent := (giantSignedUniformBirthStageNonpivots σ (.edge i)).card
  let rowCost := W * Δ^exponent *
    (giantSignedEdgeUniformConstant ρ v vmin⁻¹ massMax (ell+budget))^Fintype.card B *
      BS^Fintype.card S
  let mass (a : patterns) := giantSignedRawEdgeConditionalMass ν V κ q ρ θ ζ (K a.val) s
    (fun c => giantSignedRawFreshBirthGate hPB σ i (C a.val) c.2.1 cleared)
    (fun m => v^(∑ g, m.1 g))
  have hnonneg (a : patterns) : 0 ≤ mass a := by
    unfold mass giantSignedRawEdgeConditionalMass
    apply Finset.sum_nonneg
    intro r _
    split_ifs
    · exact mul_nonneg (norm_nonneg _) (pow_nonneg (zero_le_one.trans hv) _)
    · exact le_rfl
  have hrow (a : patterns) : mass a ≤ rowCost * v^(∑ g, s.2.2.1 g) := by
    have h := giantSignedRawEdgeBirthConditionalMass_row_bound hPS hPB hdis hVS hVB ν hν V
      hvmin hV hMass hq hq1 hBS hbudget hρ hρ1 hv hW hΔ budget (hC a.val a.property)
      κ θ ζ (K a.val) (hK a.val a.property) s hatom hνmass σ i cleared
      (giantSignedBirthClearCurrent_none (.edge i) old)
    exact h.trans_eq (by dsimp only [rowCost, exponent]; ring)
  have hreal : (∑ a : patterns, mass a) ≤ (patterns.card : ℝ) * rowCost * v^(∑ g, s.2.2.1 g) := by
    calc
      _ ≤ ∑ _a : patterns, rowCost * v^(∑ g, s.2.2.1 g) :=
        Finset.sum_le_sum (fun a _ => hrow a)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]; ring
  change (∑' r : Σ a : patterns, GiantSignedRawEdgeMove PS PB ell (C a.val) s.2.2,
    if giantSignedRawFreshBirthGate hPB σ i (C r.1.val) r.2.choice.2.1 cleared
      (giantSignedRawEdgeFreshLabels r.2) then
        ENNReal.ofReal ‖giantSignedRawEdgeCoefficient ν V κ q ρ θ ζ (K r.1.val) s r.2 *
          η r.1.val s r.2‖ *
        ENNReal.ofReal (v^(∑ g, (giantSignedRawEdgeTarget κ s r.2).2.2.1 g)) else 0) ≤ _
  rw [tsum_fintype, Fintype.sum_sigma]
  calc
    _ ≤ ∑ a : patterns, ENNReal.ofReal (mass a) := by
      apply Finset.sum_le_sum
      intro a _
      unfold mass giantSignedRawEdgeConditionalMass
      rw [ENNReal.ofReal_sum_of_nonneg (fun r _ => by
        split_ifs
        · exact mul_nonneg (norm_nonneg _) (pow_nonneg (zero_le_one.trans hv) _)
        · exact le_rfl)]
      apply Finset.sum_le_sum
      intro r _
      by_cases hg : giantSignedRawFreshBirthGate hPB σ i (C a.val) r.choice.2.1 cleared
          (giantSignedRawEdgeFreshLabels r)
      · rw [if_pos hg, if_pos hg, ENNReal.ofReal_mul (norm_nonneg _)]
        apply mul_le_mul_left
        apply ENNReal.ofReal_le_ofReal
        rw [norm_mul]
        simpa only [mul_one] using mul_le_mul_of_nonneg_left (hη a.val a.property s r)
          (norm_nonneg (giantSignedRawEdgeCoefficient ν V κ q ρ θ ζ (K a.val) s r))
      · rw [if_neg hg, if_neg hg, ENNReal.ofReal_zero]
    _ = ENNReal.ofReal (∑ a : patterns, mass a) :=
      (ENNReal.ofReal_sum_of_nonneg (fun a _ => hnonneg a)).symm
    _ ≤ ENNReal.ofReal ((patterns.card : ℝ) * rowCost * v^(∑ g, s.2.2.1 g)) :=
      ENNReal.ofReal_le_ofReal hreal
    _ = _ := by
      change ENNReal.ofReal ((patterns.card : ℝ) * rowCost * v^(∑ g, s.2.2.1 g)) =
        ENNReal.ofReal ((patterns.card : ℝ) * W * Δ^exponent *
          (giantSignedEdgeUniformConstant ρ v vmin⁻¹ massMax (ell+budget))^Fintype.card B *
            BS^Fintype.card S) * ENNReal.ofReal (v^(∑ g, s.2.2.1 g))
      have hconstant : 0 ≤ giantSignedEdgeUniformConstant ρ v vmin⁻¹ massMax (ell+budget) :=
        giantSignedEdgeUniformConstant_nonneg hρ1 (zero_le_one.trans hv)
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      dsimp only [rowCost]
      ring

end
end ArtinMatthews
