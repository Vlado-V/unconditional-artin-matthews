module

public import ArtinMatthews.GiantSignedTraceRows
public import ArtinMatthews.GiantSignedChronologicalGrowth
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

/-! The absolute mass of an actual raw row is a raw row with its phase
removed. It therefore inherits the proved all-degree exponential bound. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

private def giantSignedNormPhase (z : ℂ) : ℂ := star z / (‖z‖ : ℂ)

private theorem giantSignedNormPhase_le (z : ℂ) : ‖giantSignedNormPhase z‖ ≤ 1 := by
  rw [giantSignedNormPhase, norm_div, show ‖star z‖ = ‖z‖ from Complex.norm_conj z, Complex.norm_real,
    Real.norm_of_nonneg (norm_nonneg z)]
  by_cases h : ‖z‖ = 0 <;> simp [h]

private theorem giantSignedNormPhase_mul (z : ℂ) : z * giantSignedNormPhase z = (‖z‖ : ℂ) := by
  by_cases hz : z = 0
  · simp [hz]
  · have hn : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hz
    have he : z * star z = (‖z‖ : ℂ)^2 := Complex.mul_conj' z
    rw [giantSignedNormPhase, ← mul_div_assoc, he, pow_two]
    exact mul_div_cancel_right₀ _ hn

universe u
variable {S B I : Type u} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell : ℕ}

def giantSignedRawEdgeAbsoluteMultiplier (ν : ∀ g, PB g → ℝ) (V : B → ℝ)
    {C : B → Finset (Fin k)} (κ : ℤ) (q ρ θ ζ : ℝ)
    (K : GiantTwoSidedPatternCoefficient PB C ell)
    (η : (s : GiantSignedState PS PB (k+ell)) → GiantSignedRawEdgeMove PS PB ell C s.2.2 → ℂ)
    (s : GiantSignedState PS PB (k+ell)) (r : GiantSignedRawEdgeMove PS PB ell C s.2.2) : ℂ :=
  η s r * giantSignedNormPhase (giantSignedRawEdgeCoefficient ν V κ q ρ θ ζ K s r * η s r)

theorem giantSignedRawEdgeAbsoluteMultiplier_norm_le (ν : ∀ g, PB g → ℝ) (V : B → ℝ)
    {C : B → Finset (Fin k)} (κ : ℤ) (q ρ θ ζ : ℝ)
    (K : GiantTwoSidedPatternCoefficient PB C ell)
    (η : (s : GiantSignedState PS PB (k+ell)) → GiantSignedRawEdgeMove PS PB ell C s.2.2 → ℂ)
    (s : GiantSignedState PS PB (k+ell)) (r : GiantSignedRawEdgeMove PS PB ell C s.2.2)
    (hη : ‖η s r‖ ≤ 1) : ‖giantSignedRawEdgeAbsoluteMultiplier ν V κ q ρ θ ζ K η s r‖ ≤ 1 := by
  rw [giantSignedRawEdgeAbsoluteMultiplier, norm_mul]
  exact mul_le_one₀ hη (norm_nonneg _) (giantSignedNormPhase_le _)

theorem giantSignedRawEdgeAbsoluteMultiplier_coefficient (ν : ∀ g, PB g → ℝ) (V : B → ℝ)
    {C : B → Finset (Fin k)} (κ : ℤ) (q ρ θ ζ : ℝ)
    (K : GiantTwoSidedPatternCoefficient PB C ell)
    (η : (s : GiantSignedState PS PB (k+ell)) → GiantSignedRawEdgeMove PS PB ell C s.2.2 → ℂ)
    (s : GiantSignedState PS PB (k+ell)) (r : GiantSignedRawEdgeMove PS PB ell C s.2.2) :
    giantSignedRawEdgeCoefficient ν V κ q ρ θ ζ K s r *
      giantSignedRawEdgeAbsoluteMultiplier ν V κ q ρ θ ζ K η s r =
        (‖giantSignedRawEdgeCoefficient ν V κ q ρ θ ζ K s r * η s r‖ : ℂ) := by
  rw [giantSignedRawEdgeAbsoluteMultiplier, ← mul_assoc, giantSignedNormPhase_mul]

variable [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]
    [∀ g, ∀ p : PB g, NeZero p.val]

theorem giantSignedEdgeTraceRow_absolute
    (hPS : ∀ j p, p ∈ PS j → p.Prime) (hPB : ∀ j p, p ∈ PB j → p.Prime)
    (hdis : Pairwise (fun i j => Disjoint (PS i) (PS j)))
    (hVS : ∀ j, 0 < bandReciprocalMass (PS j)) (hVB : ∀ g, 0 < bandReciprocalMass (PB g))
    (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p) (V : B → ℝ)
    {vmin massMax q ρ BS W : ℝ} (hvmin : 0 < vmin) (hV : ∀ g, vmin ≤ V g)
    (hMass : ∀ g, (∑ p : PB g, ν g p) ≤ massMax)
    (hq : 0 < q) (hq1 : q ≤ 1) (hBS : 0 ≤ BS)
    (hbudget : ∀ j (z : ℕ), (bandReciprocalMass (PS j))⁻¹ ^ ell *
      ((z : ℝ) + (ell : ℝ)) ^ ell * q ^ ((z : ℝ) / 2) ≤ BS)
    (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (hW : 0 ≤ W) (budget : ℕ)
    (patterns : Finset I) (C : I → B → Finset (Fin k))
    (hC : ∀ v ∈ patterns, ∀ g, (C v g).card ≤ budget)
    (κ : ℤ) (θ ζ : ℝ) (K : (v : I) → GiantTwoSidedPatternCoefficient PB (C v) ell)
    (hK : ∀ v ∈ patterns, ∀ a b aux, ‖K v a b aux‖ ≤ W)
    (η : (v : I) → (s : GiantSignedState PS PB (k+ell)) →
      GiantSignedRawEdgeMove PS PB ell (C v) s.2.2 → ℂ)
    (hη : ∀ v ∈ patterns, ∀ s r, ‖η v s r‖ ≤ 1) :
    GiantSignedTraceRowAbsolute (fun s : GiantSignedState PS PB (k+ell) => ∑ g, s.2.2.1 g)
      (giantSignedEdgeTraceRow ν V patterns C κ q ρ θ ζ K η) := by
  classical
  intro f hf hfexp
  let X := GiantSignedState PS PB (k+ell)
  let row := giantSignedEdgeTraceRow ν V patterns C κ q ρ θ ζ K η
  let η' (v : I) := giantSignedRawEdgeAbsoluteMultiplier ν V κ q ρ θ ζ (K v) (η v)
  have hη' (v : I) (hv : v ∈ patterns) (s : X) (r : GiantSignedRawEdgeMove PS PB ell (C v) s.2.2) :
      ‖η' v s r‖ ≤ 1 :=
    giantSignedRawEdgeAbsoluteMultiplier_norm_le ν V κ q ρ θ ζ (K v) (η v) s r (hη v hv s r)
  let w : X → ℂ := fun s => (f s : ℂ)
  have hw : GiantSignedWordExponential w := by
    obtain ⟨Cf,u,hCf,hu,he⟩ := hfexp
    refine ⟨Cf,u,hCf,hu,fun s => ?_⟩
    simpa only [w, Complex.norm_real, Real.norm_of_nonneg (hf s)] using he s
  have hm (s : X) : (giantSignedTraceRowMass row f s : ℂ) =
      giantSignedRawEdgeFamilyApply ν V patterns C κ q ρ θ ζ K η' w s := by
    rw [← giantSignedEdgeTraceRow_apply]
    let T := Σ v : patterns, GiantSignedRawEdgeMove PS PB ell (C v.val) s.2.2
    let c (r : T) := giantSignedRawEdgeCoefficient ν V κ q ρ θ ζ (K r.1.val) s r.2
    let target (r : T) := giantSignedRawEdgeTarget κ s r.2
    change (((∑' r : T, ‖c r * η r.1.val s r.2‖ * f (target r)) : ℝ) : ℂ) =
      ∑' r : T, c r * η' r.1.val s r.2 * w (target r)
    rw [Complex.ofReal_tsum]
    apply tsum_congr
    intro r
    rw [Complex.ofReal_mul]
    exact congrArg (fun z => z * w (target r))
      (giantSignedRawEdgeAbsoluteMultiplier_coefficient ν V κ q ρ θ ζ
        (K r.1.val) (η r.1.val) s r.2).symm
  refine ⟨?_, ?_⟩
  · intro s
    change Summable (fun r : Σ v : patterns, GiantSignedRawEdgeMove PS PB ell (C v.val) s.2.2 => _)
    exact (hasSum_fintype _).summable
  · obtain ⟨Cf,u,hCf,hu,he⟩ := giantSignedRawEdgeFamilyApply_exponential hPS hPB hdis hVS hVB
      ν hν V hvmin hV hMass hq hq1 hBS hbudget hρ hρ1 hW budget patterns C hC κ θ ζ K hK η' hη' w hw
    refine ⟨Cf,u,hCf,hu,fun s => ?_⟩
    have h0 : 0 ≤ giantSignedTraceRowMass row f s :=
      tsum_nonneg (fun _ => mul_nonneg (norm_nonneg _) (hf _))
    calc
      _ = ‖(giantSignedTraceRowMass row f s : ℂ)‖ :=
        ((Complex.norm_real _).trans (Real.norm_of_nonneg h0)).symm
      _ ≤ _ := by rw [hm]; exact he s

end
end ArtinMatthews
