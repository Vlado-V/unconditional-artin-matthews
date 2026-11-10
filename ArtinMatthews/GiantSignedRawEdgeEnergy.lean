module

public import ArtinMatthews.GiantSignedRawEdgeSplit
public import ArtinMatthews.GiantSignedConditioningEnergy
public import ArtinMatthews.GiantSignedEdgeEnergy
public import ArtinMatthews.GiantSignedRawCore
public import ArtinMatthews.GiantSignedRawPositiveAverage
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

/-! Energy of the original full-state raw edge, including its bounded
local multipliers and the canonical dirty-edge selection. -/
namespace ArtinMatthews
open scoped BigOperators ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell : ℕ}
    [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]
    [∀ g, ∀ p : PB g, NeZero p.val]
    {C : B → Finset (Fin k)}

omit [∀ g, ∀ p : PB g, NeZero p.val] in
private theorem state_energy_norm_law (ν : ∀ g, PB g → ℝ)
    (f : GiantSignedState PS PB (k+ell) → ℂ) :
    giantSignedStateEnergy PS ν (fun s => (‖f s‖ : ℂ)) = giantSignedStateEnergy PS ν f := by
  unfold giantSignedStateEnergy
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_norm]

omit [∀ g, ∀ p : PB g, NeZero p.val] in
theorem giantSignedStateEnergy_norm_le
    (hVS : ∀ j, 0 < bandReciprocalMass (PS j))
    (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p)
    {A : ℝ} (F G : GiantSignedState PS PB (k+ell) → ℂ)
    (hFG : ∀ s, ‖F s‖ ≤ A * ‖G s‖) :
    giantSignedStateEnergy PS ν F ≤ ENNReal.ofReal (A ^ 2) * giantSignedStateEnergy PS ν G := by
  have hmass (s : GiantSignedState PS PB (k+ell)) : 0 ≤ giantSignedStateMass PS ν s := by
    apply mul_nonneg
    · apply mul_nonneg
      · unfold giantTwoSidedResidueHaarStateMass markedPhysicalMass
        exact div_nonneg
          (Finset.prod_nonneg (fun j _ => pow_nonneg (inv_nonneg.mpr (hVS j).le) _))
          (Nat.cast_nonneg _)
      · exact Finset.prod_nonneg (fun g _ => Finset.prod_nonneg (fun i _ => hν g _))
    · exact giantSignedMemoryMass_nonneg ν hν s.2.2
  rw [giantSignedStateEnergy_eq_tsum, giantSignedStateEnergy_eq_tsum, ← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro s
  have hs := pow_le_pow_left₀ (norm_nonneg _) (hFG s) 2
  rw [mul_pow] at hs
  calc
    _ ≤ ENNReal.ofReal (giantSignedStateMass PS ν s * (A ^ 2 * ‖G s‖ ^ 2)) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hs (hmass s))
    _ = _ := by
      rw [mul_left_comm, ENNReal.ofReal_mul (sq_nonneg A)]

omit [∀ g, ∀ p : PB g, NeZero p.val] in
private theorem state_energy_inverse_slot
    (ν : ∀ g, PB g → ℝ) (πS : S → Equiv.Perm (Fin (k+ell)))
    (πB : B → Equiv.Perm (Fin (k+ell))) (f : GiantSignedState PS PB (k+ell) → ℂ) :
    giantSignedStateEnergy PS ν (fun s => f ((giantSignedStatePermute PS πS πB).symm s)) =
      giantSignedStateEnergy PS ν f := by
  have h := giantSignedStateEnergy_slot_permute PS ν πS πB
    (fun s => f ((giantSignedStatePermute PS πS πB).symm s))
  simpa only [Equiv.symm_apply_apply] using h.symm

def giantSignedRawEdgeEnergyConstant (W BS : ℝ) (nS nB : ℕ)
    (ρ v vmin vmax massMax : ℝ) (tmax : ℕ) : ℝ :=
  W ^ 2 * ((BS ^ nS) ^ 2 * (giantSignedEdgeEnergyConstant ρ v vmin vmax massMax tmax) ^ nB)

theorem giantSignedRawEdgeApply_energy
    (hPS : ∀ j p, p ∈ PS j → p.Prime) (hPB : ∀ j p, p ∈ PB j → p.Prime)
    (hdis : Pairwise (fun i j => Disjoint (PS i) (PS j)))
    (hVS : ∀ j, 0 < bandReciprocalMass (PS j))
    (hVB : ∀ j, 0 < bandReciprocalMass (PB j))
    (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p) (V : B → ℝ)
    {vmin vmax massMax q ρ v U u BS W : ℝ}
    (hvmin : 0 < vmin) (hVmin : ∀ g, vmin ≤ V g) (hVmax : ∀ g, V g ≤ vmax)
    (hMass : ∀ g, (∑ p : PB g, ν g p) ≤ massMax)
    (hq : 0 < q) (hq1 : q ≤ 1) (hBS : 0 ≤ BS)
    (hbudget : ∀ j (z : ℕ),
      (bandReciprocalMass (PS j))⁻¹ ^ ell * ((z : ℝ) + (ell : ℝ)) ^ ell *
        q ^ ((z : ℝ) / 2) ≤ BS)
    (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (hv : 1 ≤ v) (hU : 0 ≤ U) (hu : 1 ≤ u)
    (hW : 0 ≤ W) (budget : ℕ) (hC : ∀ g, (C g).card ≤ budget)
    (κ : ℤ) (θ ζ : ℝ) (K : GiantTwoSidedPatternCoefficient PB C ell)
    (hK : ∀ a b aux, ‖K a b aux‖ ≤ W)
    (η : (s : GiantSignedState PS PB (k+ell)) → GiantSignedRawEdgeMove PS PB ell C s.2.2 → ℂ)
    (hη : ∀ s r, ‖η s r‖ ≤ 1)
    (f : GiantSignedState PS PB (k+ell) → ℂ)
    (hf : ∀ s, ‖f s‖ ≤ U * u ^ (∑ g, s.2.2.1 g))
    (hsym : ∀ s a, GiantSignedMemorySymmetric (fun m => f (s,a,m))) :
    giantSignedStateEnergy PS ν (giantSignedRawEdgeApply ν V κ q ρ θ ζ K η f) ≤
      ENNReal.ofReal (giantSignedRawEdgeEnergyConstant W BS (Fintype.card S) (Fintype.card B)
        ρ v vmin vmax massMax (ell+budget)) * giantSignedStateEnergy PS ν f := by
  let I := GiantSignedRawOuterChoice (S := S) PB C ell
  let w : I → ℝ := giantSignedRawOuterWeight
  let fτ (i : I) (t : GiantSignedState PS PB (k+ell)) : ℂ :=
    (‖f ((giantTwoSidedResiduePermute i.2.1.1).symm t.1,
      (giantSignedGroupedTuplePermutation i.2.1.2).symm t.2.1, t.2.2)‖ : ℂ)
  let T (i : I) (s : GiantSignedState PS PB (k+ell)) : ℂ :=
    giantSignedRawCoreApply ν V κ q ρ i.2.2 (fτ i) (giantSignedStatePermute PS i.1.1 i.1.2 s)
  let G (s : GiantSignedState PS PB (k+ell)) : ℂ := ∑ i : I, (w i : ℂ) * (‖T i s‖ : ℂ)
  let E := (BS ^ Fintype.card S) ^ 2 *
    (giantSignedEdgeEnergyConstant ρ v vmin vmax massMax (ell+budget)) ^ Fintype.card B
  have hw : ∀ i, 0 ≤ w i := giantSignedRawOuterWeight_nonneg hVB
  have hsum : ∑ i, w i = 1 := giantSignedRawOuterWeight_sum C hVB
  have hVp (g : B) : 0 < V g := lt_of_lt_of_le hvmin (hVmin g)
  have hG (s : GiantSignedState PS PB (k+ell)) : ‖G s‖ = ∑ i : I, w i * ‖T i s‖ := by
    have he : G s = ((∑ i : I, w i * ‖T i s‖ : ℝ) : ℂ) := by
      simp only [G, Complex.ofReal_sum, Complex.ofReal_mul]
    rw [he, Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_nonneg (Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (norm_nonneg _)))
  have hpoint (s : GiantSignedState PS PB (k+ell)) :
      ‖giantSignedRawEdgeApply ν V κ q ρ θ ζ K η f s‖ ≤ W * ‖G s‖ := by
    have h := giantSignedRawEdgeApply_norm_le_positive hPS hPB hVS hVB ν V κ hq.le
      ρ θ ζ W hW K hK η hη f s
    rw [giantSignedRawPositiveApply_average ν hν V hVp κ q hρ
      (fun t => ‖f t‖) (fun _ => norm_nonneg _) s] at h
    simpa only [hG] using h
  have hnorm := giantSignedStateEnergy_norm_le hVS ν hν
    (giantSignedRawEdgeApply ν V κ q ρ θ ζ K η f) G hpoint
  have hi (i : I) : giantSignedStateEnergy PS ν (fun s => (‖T i s‖ : ℂ)) ≤
      ENNReal.ofReal E * giantSignedStateEnergy PS ν f := by
    have hft (t : GiantSignedState PS PB (k+ell)) : ‖fτ i t‖ ≤ U * u ^ (∑ g, t.2.2.1 g) := by
      dsimp [fτ]
      rw [Complex.norm_real, Real.norm_eq_abs, abs_norm]
      exact hf _
    have hfs : ∀ s a, GiantSignedMemorySymmetric (fun m => fτ i (s,a,m)) := by
      intro s a m σ
      change (‖f ((giantTwoSidedResiduePermute i.2.1.1).symm s,
        (giantSignedGroupedTuplePermutation i.2.1.2).symm a, giantSignedMemoryPermute m σ)‖ : ℂ) = _
      exact congrArg (fun z : ℂ => (‖z‖ : ℂ))
        (hsym ((giantTwoSidedResiduePermute i.2.1.1).symm s)
          ((giantSignedGroupedTuplePermutation i.2.1.2).symm a) m σ)
    have he := giantSignedRawCoreApply_energy hPS hdis hVS ν hν V hvmin hVmin hVmax hMass
      hq hq1 hBS hbudget hρ hρ1 hv hU hu budget hC κ i.2.2 (fτ i) hft hfs
    have htest : giantSignedStateEnergy PS ν (fτ i) = giantSignedStateEnergy PS ν f := by
      change giantSignedStateEnergy PS ν
        (fun t => (‖f ((giantSignedStatePermute PS i.2.1.1 i.2.1.2).symm t)‖ : ℂ)) = _
      rw [state_energy_norm_law]
      exact state_energy_inverse_slot ν _ _ f
    rw [state_energy_norm_law]
    calc
      _ = giantSignedStateEnergy PS ν (giantSignedRawCoreApply ν V κ q ρ i.2.2 (fτ i)) :=
        giantSignedStateEnergy_slot_permute PS ν i.1.1 i.1.2 _
      _ ≤ _ := he.trans_eq (by rw [htest])
  have havg := giantSignedStateEnergy_probability_average PS hVS ν hν w hw hsum
    (fun i s => (‖T i s‖ : ℂ))
  have hE : giantSignedStateEnergy PS ν G ≤ ENNReal.ofReal E * giantSignedStateEnergy PS ν f := by
    apply havg.trans
    calc
      _ ≤ ∑ i : I, ENNReal.ofReal (w i) * (ENNReal.ofReal E * giantSignedStateEnergy PS ν f) :=
        Finset.sum_le_sum (fun i _ => mul_le_mul_right (hi i) _)
      _ = _ := by
        rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg (fun i _ => hw i), hsum,
          ENNReal.ofReal_one, one_mul]
  calc
    _ ≤ ENNReal.ofReal (W ^ 2) * (ENNReal.ofReal E * giantSignedStateEnergy PS ν f) :=
      hnorm.trans (mul_le_mul_right hE _)
    _ = _ := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (sq_nonneg W)]
      rfl

theorem giantSignedRawEdgeApply_dirty_energy
    (hPS : ∀ j p, p ∈ PS j → p.Prime) (hPB : ∀ j p, p ∈ PB j → p.Prime)
    (hdis : Pairwise (fun i j => Disjoint (PS i) (PS j)))
    (hVS : ∀ j, 0 < bandReciprocalMass (PS j))
    (hVB : ∀ j, 0 < bandReciprocalMass (PB j))
    (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p) (V : B → ℝ)
    {vmin vmax massMax q ρ v U u BS W : ℝ}
    (hvmin : 0 < vmin) (hVmin : ∀ g, vmin ≤ V g) (hVmax : ∀ g, V g ≤ vmax)
    (hMass : ∀ g, (∑ p : PB g, ν g p) ≤ massMax)
    (hq : 0 < q) (hq1 : q ≤ 1) (hBS : 0 ≤ BS)
    (hbudget : ∀ j (z : ℕ),
      (bandReciprocalMass (PS j))⁻¹ ^ ell * ((z : ℝ) + (ell : ℝ)) ^ ell *
        q ^ ((z : ℝ) / 2) ≤ BS)
    (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (hv : 1 ≤ v) (hU : 0 ≤ U) (hu : 1 ≤ u)
    (hW : 0 ≤ W) (budget : ℕ) (hC : ∀ g, (C g).card ≤ budget)
    (κ : ℤ) (θ ζ : ℝ) (K : GiantTwoSidedPatternCoefficient PB C ell)
    (hK : ∀ a b aux, ‖K a b aux‖ ≤ W)
    (η : (s : GiantSignedState PS PB (k+ell)) → GiantSignedRawEdgeMove PS PB ell C s.2.2 → ℂ)
    (hη : ∀ s r, ‖η s r‖ ≤ 1)
    (f : GiantSignedState PS PB (k+ell) → ℂ)
    (hf : ∀ s, ‖f s‖ ≤ U * u ^ (∑ g, s.2.2.1 g))
    (hsym : ∀ s a, GiantSignedMemorySymmetric (fun m => f (s,a,m))) :
    giantSignedStateEnergy PS ν (giantSignedRawEdgeApply ν V κ q ρ θ ζ K
      (fun s r => η s r * giantSignedRawEdgeDirtyMultiplier s r) f) ≤
      ENNReal.ofReal (giantSignedRawEdgeEnergyConstant W BS (Fintype.card S) (Fintype.card B)
        ρ v vmin vmax massMax (ell+budget)) * giantSignedStateEnergy PS ν f := by
  apply giantSignedRawEdgeApply_energy hPS hPB hdis hVS hVB ν hν V hvmin hVmin hVmax hMass
    hq hq1 hBS hbudget hρ hρ1 hv hU hu hW budget hC κ θ ζ K hK
    (fun s r => η s r * giantSignedRawEdgeDirtyMultiplier s r) _ f hf hsym
  intro s r
  rw [norm_mul]
  simpa only [one_mul] using mul_le_mul (hη s r) (giantSignedRawEdgeDirtyMultiplier_norm s r)
    (norm_nonneg _) zero_le_one

end
end ArtinMatthews
