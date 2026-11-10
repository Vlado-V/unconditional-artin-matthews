module

public import ArtinMatthews.GiantSignedDoubledChronologicalWord
public import ArtinMatthews.GiantSignedTraceEdgeAbsolute
public import ArtinMatthews.GiantSignedTraceProjection
public import ArtinMatthews.GiantSignedTraceTail
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

/-! The omitted mass uses the literal finite boundary weights, including
the small Haar-state and tilted ordered active mass. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

universe u
variable {S B I : Type u} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell : ℕ}
    [Fintype (GiantTwoSidedResidueState PS (k+ell))]

def giantSignedGuardedTraceBoundaryPairing (ν : ∀ g, PB g → ℝ)
    (rows : List (GiantSignedTraceRow.{u,u} (GiantSignedState PS PB (k+ell))))
    (φ : (s : GiantSignedState PS PB (k+ell)) → GiantSignedTrace rows s → ℂ) : ℂ :=
  ∑ y : GiantTwoSidedResidueState PS (k+ell), ∑ a : MarkedPhysicalMarking PB (k+ell),
    let s : GiantSignedState PS PB (k+ell) := (y,a,giantSignedEmptyMemory PB)
    ((giantTwoSidedResidueHaarStateMass PS (k+ell) * giantSignedActiveMass ν a : ℝ) : ℂ) *
      ∑' t : GiantSignedTrace rows s, giantSignedTraceWeight giantSignedBoundary rows s t * φ s t

variable [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]
    [∀ g, ∀ p : PB g, NeZero p.val]

theorem giantSignedGuardedTraceBoundary_projection_error
    (hPS : ∀ j p, p ∈ PS j → p.Prime) (hPB : ∀ j p, p ∈ PB j → p.Prime)
    (hdis : Pairwise (fun i j => Disjoint (PS i) (PS j)))
    (hVS : ∀ j, 0 < bandReciprocalMass (PS j)) (hVB : ∀ g, 0 < bandReciprocalMass (PB g))
    (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p) (V : B → ℝ)
    {vmin massMax q ρ BS W : ℝ} (hvmin : 0 < vmin) (hV : ∀ g, vmin ≤ V g)
    (hMass : ∀ g, (∑ p : PB g, ν g p) ≤ massMax)
    (hq : 0 < q) (hq1 : q ≤ 1) (hBS : 0 ≤ BS)
    (hbudget : ∀ j (z : ℕ), (bandReciprocalMass (PS j))⁻¹ ^ ell *
      ((z : ℝ) + (ell : ℝ)) ^ ell * q ^ ((z : ℝ) / 2) ≤ BS)
    (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (hW : 0 ≤ W) (budget H : ℕ) (θ : ℝ) (n : ℕ)
    (patterns : Fin n → Finset I) (C : Fin n → I → B → Finset (Fin k))
    (hC : ∀ i v, v ∈ patterns i → ∀ g, (C i v g).card ≤ budget)
    (κ : Fin n → ℤ) (visitQ : Fin (n+1) → ℝ) (ζ : Fin n → ℝ)
    (K : (i : Fin n) → (v : I) → GiantTwoSidedPatternCoefficient PB (C i v) ell)
    (hK : ∀ i v, v ∈ patterns i → ∀ a b aux, ‖K i v a b aux‖ ≤ W)
    (η : (i : Fin n) → (v : I) → (s : GiantSignedState PS PB (k+ell)) →
      GiantSignedRawEdgeMove PS PB ell (C i v) s.2.2 → ℂ)
    (hη : ∀ i v, v ∈ patterns i → ∀ s r, ‖η i v s r‖ ≤ 1)
    (φ : (s : GiantSignedState PS PB (k+ell)) →
      GiantSignedTrace (giantSignedChronologicalTraceRows ν V q ρ θ n patterns C κ visitQ ζ K η) s → ℂ)
    (hφ : ∀ s t, ‖φ s t‖ ≤ 1) :
    let rows := giantSignedChronologicalTraceRows ν V q ρ θ n patterns C κ visitQ ζ K η
    ‖giantSignedGuardedTraceBoundaryPairing ν rows φ -
      giantSignedGuardedTraceBoundaryPairing ν rows (fun s t =>
        if GiantSignedTraceWithin (fun x => (∑ g, x.2.2.1 g) ≤ H) rows s t then φ s t else 0)‖ ≤
      ‖giantSignedDoubledChronologicalBoundaryPairing ν V q ρ θ n patterns C κ visitQ ζ K
        (fun i v => giantSignedRawEdgeAbsoluteMultiplier ν V (κ i) q ρ θ (ζ i) (K i v) (η i v))‖ /
        (2:ℝ)^(H-(ell+budget)*Fintype.card B*n) := by
  dsimp only
  let X := GiantSignedState PS PB (k+ell)
  let rows := giantSignedChronologicalTraceRows ν V q ρ θ n patterns C κ visitQ ζ K η
  let w (s : X) := giantSignedTraceWeight giantSignedBoundary rows s
  let good (s : X) := GiantSignedTraceWithin (fun x => (∑ g, x.2.2.1 g) ≤ H) rows s
  let d := (2:ℝ)^(H-(ell+budget)*Fintype.card B*n)
  let η' := fun i v => giantSignedRawEdgeAbsoluteMultiplier ν V (κ i) q ρ θ (ζ i) (K i v) (η i v)
  let Z (s : X) := giantSignedDoubledChronologicalWord ν V q ρ θ giantSignedBoundary n
    patterns C κ visitQ ζ K η' s
  let Δ (s : X) := (∑' t, w s t * φ s t) -
    ∑' t, if good s t then w s t * φ s t else 0

  have hB : (fun s : X => (‖giantSignedBoundary s‖ : ℂ)) = giantSignedBoundary := by
    funext s
    unfold giantSignedBoundary
    split_ifs <;> simp
  have hpoint (s : X) (hs : s.2.2 = giantSignedEmptyMemory PB) : ‖Δ s‖ ≤ (Z s).re / d := by
    have he := giantSignedChronologicalTraceOmission_le hPS hPB hdis hVS hVB ν hν V
      hvmin hV hMass hq hq1 hBS hbudget hρ hρ1 hW budget H θ giantSignedBoundary
      giantSignedBoundary_exponential n patterns C hC κ visitQ ζ K hK η hη s hs (φ s) (hφ s)
    rw [hB] at he
    exact he
  let s₀ (y : GiantTwoSidedResidueState PS (k+ell)) (a : MarkedPhysicalMarking PB (k+ell)) : X :=
    (y,a,giantSignedEmptyMemory PB)
  let mass (a : MarkedPhysicalMarking PB (k+ell)) :=
    giantTwoSidedResidueHaarStateMass PS (k+ell) * giantSignedActiveMass ν a
  have hm (a : MarkedPhysicalMarking PB (k+ell)) : 0 ≤ mass a := by
    unfold mass giantTwoSidedResidueHaarStateMass markedPhysicalMass giantSignedActiveMass
    exact mul_nonneg
      (div_nonneg (Finset.prod_nonneg (fun j _ => pow_nonneg (inv_nonneg.mpr (hVS j).le) _))
        (Nat.cast_nonneg _))
      (Finset.prod_nonneg (fun g _ => Finset.prod_nonneg (fun i _ => hν g (a g i))))
  have he : giantSignedGuardedTraceBoundaryPairing ν rows φ -
      giantSignedGuardedTraceBoundaryPairing ν rows (fun s t => if good s t then φ s t else 0) =
        ∑ y, ∑ a, (mass a : ℂ) * Δ (s₀ y a) := by
    simp only [giantSignedGuardedTraceBoundaryPairing, ← Finset.sum_sub_distrib, ← mul_sub,
      mass, Δ, w, s₀, mul_ite, mul_zero]
  rw [he]
  calc
    _ ≤ ∑ y, ∑ a, mass a * ((Z (s₀ y a)).re / d) := by
      refine (norm_sum_le _ _).trans ?_
      apply Finset.sum_le_sum
      intro y _
      refine (norm_sum_le _ _).trans ?_
      apply Finset.sum_le_sum
      intro a _
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hm a)]
      exact mul_le_mul_of_nonneg_left (hpoint (s₀ y a) rfl) (hm a)
    _ = (giantSignedDoubledChronologicalBoundaryPairing ν V q ρ θ n patterns C κ visitQ ζ K η').re / d := by
      simp only [giantSignedDoubledChronologicalBoundaryPairing, Finset.sum_div, Complex.re_sum,
        Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Z, s₀, mass, mul_div_assoc]
    _ ≤ _ := div_le_div_of_nonneg_right (Complex.re_le_norm _) (pow_nonneg (by norm_num) _)

end
end ArtinMatthews
