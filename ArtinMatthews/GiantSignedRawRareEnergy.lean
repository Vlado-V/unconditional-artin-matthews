module

public import ArtinMatthews.GiantSignedEdgeEnergy
public import ArtinMatthews.GiantSignedRawEdgeSplit
public import ArtinMatthews.GiantSignedSmallOmissions
public import ArtinMatthews.GiantSignedStateMemoryCutoff
public import ArtinMatthews.GiantSignedRawPromoteEnergy
public import ArtinMatthews.GiantSignedRawStoreEnergy
public import ArtinMatthews.GiantSignedStateFiniteSumEnergy
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

/-! The two literal dirty channels give the rare-transfer energy gain. -/
namespace ArtinMatthews
open scoped BigOperators ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell : ℕ}
    [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]
    [∀ g, ∀ p : PB g, NeZero p.val]
    {C : B → Finset (Fin k)}

theorem giantSignedRawProjectedDirtyRare_energy
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
    (budget : ℕ) (hC : ∀ g, (C g).card ≤ budget)
    (N kStep : ℕ) (hk : 0 < kStep) (sign : ℤ) (hsign : sign = 1 ∨ sign = -1)
    (hstep : ∀ j p, p ∈ PB j → kStep < p)
    (tSmall tBig : ℝ) (hlabels : ∀ j p, p ∈ PS j → (p : ℝ) ≤ Real.exp tSmall)
    (hgap : (ell : ℝ) * (Fintype.card S : ℝ) * tSmall < tBig)
    (hlower : ∀ j p, p ∈ PB j → Real.exp tBig ≤ (p : ℝ))
    (θ ζ W : ℝ) (hW : 0 ≤ W) (K : GiantTwoSidedPatternCoefficient PB C ell)
    (hK : ∀ a b aux, ‖K a b aux‖ ≤ W)
    (η : (s : GiantSignedState PS PB (k+ell)) → GiantSignedRawEdgeMove PS PB ell C s.2.2 → ℂ)
    (hη : ∀ s r, ‖η s r‖ ≤ 1)
    (f : GiantSignedState PS PB (k+ell) → ℂ)
    (hsym : ∀ s a, GiantSignedMemorySymmetric (fun m => f (s,a,m))) :
    giantSignedStateEnergy PS ν (giantSignedStateMemoryCutoff N
      (giantSignedRawEdgeApply ν V (sign * kStep) q ρ θ ζ K
        (fun s r => η s r * giantSignedRawEdgeDirtyMultiplier s r)
        (giantSignedStateMemoryCutoff N f))) ≤
      ENNReal.ofReal (4 * W ^ 2 * ((N : ℝ) / (giantSignedSmallOmissionNumber S (k+ell) ell : ℝ)) *
        ((BS ^ Fintype.card S) ^ 2 *
          (giantSignedEdgeEnergyConstant ρ v vmin vmax massMax (ell+budget)) ^ Fintype.card B)) *
        giantSignedStateEnergy PS ν f := by
  let κ : ℤ := sign * kStep
  let ε : ℝ := (N : ℝ) / (giantSignedSmallOmissionNumber S (k+ell) ell : ℝ)
  let E := (BS ^ Fintype.card S) ^ 2 *
    (giantSignedEdgeEnergyConstant ρ v vmin vmax massMax (ell+budget)) ^ Fintype.card B
  let X := W ^ 2 * ε * E
  let fN := giantSignedStateMemoryCutoff N f
  let P := giantSignedRawEdgeApply ν V κ q ρ θ ζ K
    (fun s r => η s r * giantSignedRawPromoteMultiplier s r) fN
  let T := giantSignedRawEdgeApply ν V κ q ρ θ ζ K
    (fun s r => η s r * giantSignedRawStoreOnlyMultiplier s r) fN
  let D := giantSignedRawEdgeApply ν V κ q ρ θ ζ K
    (fun s r => η s r * giantSignedRawEdgeDirtyMultiplier s r) fN
  have hsplit : D = P + T := by
    funext s
    exact giantSignedRawDirtyApply_split ν V κ q ρ θ ζ K η fN s
  have hP : giantSignedStateEnergy PS ν (giantSignedStateMemoryCutoff N P) ≤
      ENNReal.ofReal X * giantSignedStateEnergy PS ν f :=
    giantSignedRawProjectedPromote_energy hPS hPB hdis hsep hVS hVB ν hν V hvmin hVmin hVmax
      hMass hq hq1 hBS hsmall hρ hρ1 hv budget hC N kStep hk sign hsign
      hstep tSmall tBig hlabels hgap hlower θ ζ W hW K hK η hη f hsym
  have hT : giantSignedStateEnergy PS ν (giantSignedStateMemoryCutoff N T) ≤
      ENNReal.ofReal X * giantSignedStateEnergy PS ν f :=
    giantSignedRawProjectedStore_energy hPS hPB hdis hsep hVS hVB ν hν V hvmin hVmin hVmax
      hMass hq hq1 hBS hsmall hρ hρ1 hv budget hC N kStep hk sign hsign
      hstep tSmall tBig hlabels hgap hlower θ ζ W hW K hK η hη f hsym
  let H (i : Fin 2) := if i = 0 then giantSignedStateMemoryCutoff N P else
    giantSignedStateMemoryCutoff N T
  have hsum :
      giantSignedStateEnergy PS ν (giantSignedStateMemoryCutoff N P + giantSignedStateMemoryCutoff N T) ≤
        2 * (giantSignedStateEnergy PS ν (giantSignedStateMemoryCutoff N P) +
          giantSignedStateEnergy PS ν (giantSignedStateMemoryCutoff N T)) := by
    change giantSignedStateEnergy PS ν
      (fun s => giantSignedStateMemoryCutoff N P s + giantSignedStateMemoryCutoff N T s) ≤ _
    simpa [H, Fin.sum_univ_two] using giantSignedStateEnergy_sum_le PS hVS ν hν H
  change giantSignedStateEnergy PS ν (giantSignedStateMemoryCutoff N D) ≤ _
  rw [hsplit, giantSignedStateMemoryCutoff_add]
  calc
    _ ≤ _ := hsum
    _ ≤ 2 * (ENNReal.ofReal X * giantSignedStateEnergy PS ν f +
        ENNReal.ofReal X * giantSignedStateEnergy PS ν f) :=
      mul_le_mul_right (add_le_add hP hT) _
    _ = _ := by
      have hreal : (4 * W ^ 2 * ε * E) = 4 * X := by dsimp only [X]; ring
      change _ = ENNReal.ofReal (4 * W ^ 2 * ε * E) * _
      rw [hreal, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4), ENNReal.ofReal_ofNat,
        ← two_mul, ← mul_assoc, ← mul_assoc] <;> norm_num

end
end ArtinMatthews
