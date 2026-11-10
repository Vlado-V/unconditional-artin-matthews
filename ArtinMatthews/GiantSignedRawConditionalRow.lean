module

public import ArtinMatthews.GiantSignedRawConditionalMass
public import ArtinMatthews.GiantSignedRawEdgeGrowth
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
public import Mathlib.Tactic.ENatToNat
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

/-! The weighted row bound uses a comparison fresh law of the same
total mass in each band. The gated summand retains its actual tilted law. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell : ℕ}
    [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]
    [∀ g, ∀ p : PB g, NeZero p.val]
    {C : B → Finset (Fin k)}

theorem giantSignedRawEdgeConditionalMass_row_bound
    (hPS : ∀ j p, p ∈ PS j → p.Prime) (hPB : ∀ j p, p ∈ PB j → p.Prime)
    (hdis : Pairwise (fun i j => Disjoint (PS i) (PS j)))
    (hVS : ∀ j, 0 < bandReciprocalMass (PS j)) (hVB : ∀ g, 0 < bandReciprocalMass (PB g))
    (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p) (V : B → ℝ)
    {vmin massMax q ρ v BS W F : ℝ}
    (hvmin : 0 < vmin) (hV : ∀ g, vmin ≤ V g) (hMass : 1 ≤ massMax)
    (hq : 0 < q) (hq1 : q ≤ 1) (hBS : 0 ≤ BS)
    (hbudget : ∀ j (z : ℕ),
      (bandReciprocalMass (PS j))⁻¹ ^ ell * ((z : ℝ) + (ell : ℝ)) ^ ell *
        q ^ ((z : ℝ)/2) ≤ BS)
    (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (hv : 1 ≤ v)
    (hW : 0 ≤ W) (hF : 0 ≤ F) (budget : ℕ) (hC : ∀ g, (C g).card ≤ budget)
    (κ : ℤ) (θ ζ : ℝ) (K : GiantTwoSidedPatternCoefficient PB C ell)
    (hK : ∀ a b aux, ‖K a b aux‖ ≤ W)
    (s : GiantSignedState PS PB (k+ell))
    (Gate : (c : GiantSignedEdgeChoice (fun g => ell+(C g).card) s.2.2.1) →
      GiantSignedPrimeTuple PB (fun g => ((c.2.1 g)ᶜ).card) → Prop)
    (hGate : ∀ c, (∑ fresh : GiantSignedPrimeTuple PB (fun g => ((c.2.1 g)ᶜ).card),
        if Gate c fresh then ∏ g, ∏ i, ν g (fresh g i) else 0) ≤
      F * ∏ g, massMax^((c.2.1 g)ᶜ).card) :
    giantSignedRawEdgeConditionalMass ν V κ q ρ θ ζ K s Gate (fun m => v^(∑ g, m.1 g)) ≤
      (W * F) * (v^(∑ g, s.2.2.1 g) *
        (giantSignedEdgeUniformConstant ρ v vmin⁻¹ massMax (ell+budget)) ^ Fintype.card B *
          BS ^ Fintype.card S) := by
  let μ (g : B) (_ : PB g) := massMax / ((PB g).card : ℝ)
  have hμ (g : B) (p : PB g) : 0 ≤ μ g p :=
    div_nonneg (zero_le_one.trans hMass) (Nat.cast_nonneg _)
  have hsum (g : B) : (∑ p : PB g, μ g p) = massMax := by
    have hc : (PB g).card ≠ 0 := by
      intro hz
      have he := Finset.card_eq_zero.mp hz
      have hzero : bandReciprocalMass (PB g) = 0 := by simp [he, bandReciprocalMass]
      exact (hVB g).ne' hzero
    have hc' : ((PB g).card : ℝ) ≠ 0 := by exact_mod_cast hc
    simp only [μ, Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
    rw [← mul_div_assoc, mul_div_cancel_left₀ massMax hc']
  have hGate' (c : GiantSignedEdgeChoice (fun g => ell+(C g).card) s.2.2.1) :
      (∑ fresh : GiantSignedPrimeTuple PB (fun g => ((c.2.1 g)ᶜ).card),
        if Gate c fresh then ∏ g, ∏ i, ν g (fresh g i) else 0) ≤
      F * ∏ g, (∑ p : PB g, μ g p)^((c.2.1 g)ᶜ).card := by
    simp only [hsum]
    exact hGate c
  let f (t : GiantSignedState PS PB (k+ell)) : ℂ := ((v^(∑ g, t.2.2.1 g) : ℝ) : ℂ)
  have hf (t : GiantSignedState PS PB (k+ell)) :
      ‖f t‖ = v^(∑ g, t.2.2.1 g) := by
    rw [show f t = ((v^(∑ g, t.2.2.1 g) : ℝ) : ℂ) from rfl, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (zero_le_one.trans hv) _)]
  have hrow := giantSignedRawPositiveApply_row_bound hPS hdis hVS hVB μ hμ V hvmin hV
    (fun g => (hsum g).le) hq hq1 hBS hbudget hρ hρ1 (U := 1) zero_le_one hv budget hC κ f
    (fun t => by rw [hf, one_mul]) s
  simp only [hf, one_mul] at hrow
  exact (giantSignedRawEdgeConditionalMass_le_positive hPS hPB hVS hVB ν μ hν hμ V κ hq.le
    ρ θ ζ W F hW K hK s Gate hGate' _ (fun _ => pow_nonneg (zero_le_one.trans hv) _)).trans
      (mul_le_mul_of_nonneg_left hrow (mul_nonneg hW hF))

end
end ArtinMatthews
