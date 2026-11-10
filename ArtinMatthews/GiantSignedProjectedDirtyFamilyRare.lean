module

public import ArtinMatthews.GiantSignedRawEdgeEnergy
public import ArtinMatthews.GiantSignedProjectedWord
public import ArtinMatthews.GiantSignedSmallOmissions
public import ArtinMatthews.GiantSignedProjectedPatternEnergy
public import ArtinMatthews.GiantSignedRawRareEnergy
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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

/-! The omission probability applies to the complete dirty pattern
family and its original source and target projections. -/
namespace ArtinMatthews
open scoped BigOperators ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

variable {S B I : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell : ℕ}
    [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]
    [∀ g, ∀ p : PB g, NeZero p.val]

theorem giantSignedProjectedRawDirtyFamily_rare_energy
    (hPS : ∀ j p, p ∈ PS j → p.Prime) (hPB : ∀ j p, p ∈ PB j → p.Prime)
    (hdis : Pairwise (fun i j => Disjoint (PS i) (PS j)))
    (hsep : ∀ i j, Disjoint (PS i) (PB j))
    (hVS : ∀ j, 0 < bandReciprocalMass (PS j)) (hVB : ∀ j, 0 < bandReciprocalMass (PB j))
    (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p) (V : B → ℝ)
    {vmin vmax massMax q ρ v BS : ℝ}
    (hvmin : 0 < vmin) (hVmin : ∀ g, vmin ≤ V g) (hVmax : ∀ g, V g ≤ vmax)
    (hMass : ∀ g, (∑ p : PB g, ν g p) ≤ massMax)
    (hq : 0 < q) (hq1 : q ≤ 1) (hBS : 0 ≤ BS)
    (hsmall : ∀ j (z : ℕ), (bandReciprocalMass (PS j))⁻¹ ^ ell *
      ((z : ℝ) + (ell : ℝ)) ^ ell * q ^ ((z : ℝ) / 2) ≤ BS)
    (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (hv : 1 ≤ v)
    (budget : ℕ) (patterns : Finset I) (C : I → B → Finset (Fin k))
    (hC : ∀ i ∈ patterns, ∀ g, (C i g).card ≤ budget)
    (N kStep : ℕ) (hk : 0 < kStep) (sign : ℤ) (hsign : sign = 1 ∨ sign = -1)
    (hstep : ∀ j p, p ∈ PB j → kStep < p)
    (tSmall tBig : ℝ) (hlabels : ∀ j p, p ∈ PS j → (p : ℝ) ≤ Real.exp tSmall)
    (hgap : (ell : ℝ) * (Fintype.card S : ℝ) * tSmall < tBig)
    (hlower : ∀ j p, p ∈ PB j → Real.exp tBig ≤ (p : ℝ))
    (θ ζ W : ℝ) (hW : 0 ≤ W) (K : ∀ i, GiantTwoSidedPatternCoefficient PB (C i) ell)
    (hK : ∀ i ∈ patterns, ∀ a b aux, ‖K i a b aux‖ ≤ W)
    (η : (i : I) → (s : GiantSignedState PS PB (k+ell)) →
      GiantSignedRawEdgeMove PS PB ell (C i) s.2.2 → ℂ)
    (hη : ∀ i ∈ patterns, ∀ s r, ‖η i s r‖ ≤ 1)
    (f : GiantSignedState PS PB (k+ell) → ℂ)
    (hsym : ∀ s a, GiantSignedMemorySymmetric (fun m => f (s,a,m))) :
    let ε : ℝ := (N : ℝ) / (giantSignedSmallOmissionNumber S (k+ell) ell : ℝ)
    let E := giantSignedRawEdgeEnergyConstant ((patterns.card : ℝ)*W) BS
      (Fintype.card S) (Fintype.card B) ρ v vmin vmax massMax (ell+budget)
    giantSignedStateEnergy PS ν
      (giantSignedProjectedRawEdgeFamilyApply N ν V patterns C (sign * kStep) q ρ θ ζ K
        (fun i s r => η i s r * giantSignedRawEdgeDirtyMultiplier s r) f) ≤
        ENNReal.ofReal ((2 * Real.sqrt E * Real.sqrt ε)^2) * giantSignedStateEnergy PS ν f := by
  dsimp only
  let ε : ℝ := (N : ℝ) / (giantSignedSmallOmissionNumber S (k+ell) ell : ℝ)
  let Ecore := (BS ^ Fintype.card S)^2 *
    (giantSignedEdgeEnergyConstant ρ v vmin vmax massMax (ell+budget)) ^ Fintype.card B
  let E := giantSignedRawEdgeEnergyConstant ((patterns.card : ℝ)*W) BS
    (Fintype.card S) (Fintype.card B) ρ v vmin vmax massMax (ell+budget)
  have hε : 0 ≤ ε := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hcore : 0 ≤ Ecore := by
    dsimp only [Ecore,giantSignedEdgeEnergyConstant]
    exact mul_nonneg (sq_nonneg _)
      (pow_nonneg (mul_nonneg (giantSignedEdgeReverseConstant_nonneg _ _ _) (sq_nonneg _)) _)
  have hE : 0 ≤ E := mul_nonneg (sq_nonneg _) hcore
  have he := giantSignedProjectedRawEdgeFamilyApply_energy_of_patterns hVS ν hν V N
    patterns C (sign * kStep) q ρ θ ζ K (fun i s r => η i s r * giantSignedRawEdgeDirtyMultiplier s r)
    f (ENNReal.ofReal (4 * W^2 * ε * Ecore))
    (fun i hi => giantSignedRawProjectedDirtyRare_energy hPS hPB hdis hsep hVS hVB ν hν V
      hvmin hVmin hVmax hMass hq hq1 hBS hsmall hρ hρ1 hv budget (hC i hi) N kStep hk sign hsign
      hstep tSmall tBig hlabels hgap hlower θ ζ W hW (K i) (hK i hi) (η i) (hη i hi) f hsym)
  refine he.trans_eq ?_
  have hcard : (patterns.card : ℝ≥0∞)^2 = ENNReal.ofReal ((patterns.card : ℝ)^2) := by
    rw [ENNReal.ofReal_pow (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  rw [hcard, ← ENNReal.ofReal_mul (sq_nonneg _)]
  apply congrArg (fun t : ℝ => ENNReal.ofReal t * giantSignedStateEnergy PS ν f)
  rw [mul_pow, mul_pow, Real.sq_sqrt hE, Real.sq_sqrt hε]
  dsimp only [E, giantSignedRawEdgeEnergyConstant, Ecore]
  ring

end
end ArtinMatthews
