module

public import ArtinMatthews.GiantSignedRawPromoteNorm
public import ArtinMatthews.GiantSignedEdgeEnergy
public import ArtinMatthews.GiantSignedCappedStateBound
public import ArtinMatthews.GiantSignedEnergyDomination
public import ArtinMatthews.GiantSignedGateEnergy
public import ArtinMatthews.GiantSignedRawCore
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

/-! Source-promotion energy gains the omission probability on the original carrier. -/
namespace ArtinMatthews
open scoped BigOperators ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell : ℕ}
    [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]
    [∀ g, ∀ p : PB g, NeZero p.val]
    {C : B → Finset (Fin k)}

theorem giantSignedRawCoreAbsoluteSection_energy
    (hPS : ∀ j p, p ∈ PS j → p.Prime)
    (hdis : Pairwise (fun i j => Disjoint (PS i) (PS j)))
    (hVS : ∀ j, 0 < bandReciprocalMass (PS j))
    (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p) (V : B → ℝ)
    {vmin vmax massMax q ρ v U BS : ℝ}
    (hvmin : 0 < vmin) (hVmin : ∀ g, vmin ≤ V g) (hVmax : ∀ g, V g ≤ vmax)
    (hMass : ∀ g, (∑ p : PB g, ν g p) ≤ massMax)
    (hq : 0 < q) (hq1 : q ≤ 1) (hBS : 0 ≤ BS)
    (hbudget : ∀ j (z : ℕ), (bandReciprocalMass (PS j))⁻¹ ^ ell *
      ((z : ℝ) + (ell : ℝ)) ^ ell * q ^ ((z : ℝ) / 2) ≤ BS)
    (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (hv : 1 ≤ v) (hU : 0 ≤ U)
    (budget : ℕ) (hC : ∀ g, (C g).card ≤ budget) (κ : ℤ)
    (f : GiantSignedState PS PB (k+ell) → ℂ) (hf : ∀ s, ‖f s‖ ≤ U)
    (hsym : ∀ s a, GiantSignedMemorySymmetric (fun m => f (s,a,m)))
    (i : GiantSignedRawOuterChoice (S := S) PB C ell) :
    giantSignedStateEnergy PS ν (fun s => (giantSignedRawCoreAbsoluteSection ν V κ q ρ f i s : ℂ)) ≤
      ENNReal.ofReal ((BS ^ Fintype.card S) ^ 2 *
        (giantSignedEdgeEnergyConstant ρ v vmin vmax massMax (ell+budget)) ^ Fintype.card B) *
        giantSignedStateEnergy PS ν f := by
  let pS := giantSignedStatePermute PS (PB := PB) i.1.1 i.1.2
  let pT := giantSignedStatePermute PS (PB := PB) i.2.1.1 i.2.1.2
  let g (s : GiantSignedState PS PB (k+ell)) : ℂ := (‖f (pT.symm s)‖ : ℂ)
  let T := giantSignedRawCoreApply ν V κ q ρ i.2.2 g
  have hgrowth (s : GiantSignedState PS PB (k+ell)) : ‖g s‖ ≤ U * (1 : ℝ) ^ (∑ j, s.2.2.1 j) := by
    simpa only [g, Complex.norm_real, Real.norm_eq_abs, abs_norm, one_pow, mul_one] using hf (pT.symm s)
  have hsymg : ∀ s a, GiantSignedMemorySymmetric (fun m => g (s,a,m)) := by
    intro s a m σ
    let s' := (giantTwoSidedResiduePermute i.2.1.1).symm s
    let a' := (giantSignedGroupedTuplePermutation i.2.1.2).symm a
    have he : f (s',a',giantSignedMemoryPermute m σ) = f (s',a',m) := hsym s' a' m σ
    change (‖f (s',a',giantSignedMemoryPermute m σ)‖ : ℂ) = (‖f (s',a',m)‖ : ℂ)
    rw [he]
  have htest : giantSignedStateEnergy PS ν g = giantSignedStateEnergy PS ν f := by
    calc
      _ = giantSignedStateEnergy PS ν (fun s => f (pT.symm s)) := by
        unfold giantSignedStateEnergy
        simp only [g, Complex.norm_real, Real.norm_eq_abs, abs_norm]
      _ = _ := by
        have he := giantSignedStateEnergy_slot_permute PS ν i.2.1.1 i.2.1.2 (fun s => f (pT.symm s))
        simpa only [pT, Equiv.symm_apply_apply] using he.symm
  calc
    _ = giantSignedStateEnergy PS ν (fun s => T (pS s)) := by
      change giantSignedStateEnergy PS ν (fun s => (‖T (pS s)‖ : ℂ)) = _
      unfold giantSignedStateEnergy
      simp only [Complex.norm_real, Real.norm_eq_abs, abs_norm]
    _ = giantSignedStateEnergy PS ν T := giantSignedStateEnergy_slot_permute PS ν i.1.1 i.1.2 T
    _ ≤ ENNReal.ofReal ((BS ^ Fintype.card S) ^ 2 *
        (giantSignedEdgeEnergyConstant ρ v vmin vmax massMax (ell+budget)) ^ Fintype.card B) *
        giantSignedStateEnergy PS ν g :=
      giantSignedRawCoreApply_energy hPS hdis hVS ν hν V hvmin hVmin hVmax hMass
        hq hq1 hBS hbudget hρ hρ1 hv hU le_rfl budget hC κ i.2.2 g hgrowth hsymg
    _ = _ := by rw [htest]

theorem giantSignedRawProjectedPromote_energy
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
        (fun s r => η s r * giantSignedRawPromoteMultiplier s r)
        (giantSignedStateMemoryCutoff N f))) ≤
      ENNReal.ofReal (W ^ 2 * ((N : ℝ) / (giantSignedSmallOmissionNumber S (k+ell) ell : ℝ)) *
        ((BS ^ Fintype.card S) ^ 2 *
          (giantSignedEdgeEnergyConstant ρ v vmin vmax massMax (ell+budget)) ^ Fintype.card B)) *
        giantSignedStateEnergy PS ν f := by
  let I := GiantSignedRawOuterChoice (S := S) PB C ell
  let w : I → ℝ := giantSignedRawOuterWeight
  let κ : ℤ := sign * kStep
  let ε : ℝ := (N : ℝ) / (giantSignedSmallOmissionNumber S (k+ell) ell : ℝ)
  let E := (BS ^ Fintype.card S) ^ 2 *
    (giantSignedEdgeEnergyConstant ρ v vmin vmax massMax (ell+budget)) ^ Fintype.card B
  let fN := giantSignedStateMemoryCutoff N f
  let F := giantSignedStateMemoryCutoff N (giantSignedRawEdgeApply ν V κ q ρ θ ζ K
    (fun s r => η s r * giantSignedRawPromoteMultiplier s r) fN)
  let H (i : I) (s : GiantSignedState PS PB (k+ell)) : ℂ :=
    (giantSignedRawCoreAbsoluteSection ν V κ q ρ fN i s : ℂ)
  let gate := GiantSignedRawOuterCappedSourceGate (PS := PS) (PB := PB) (C := C) (ell := ell) N κ
  let G (s : GiantSignedState PS PB (k+ell)) : ℂ :=
    ∑ i : I, (w i : ℂ) * (if gate s i then H i s else 0)
  have hw : ∀ i, 0 ≤ w i := giantSignedRawOuterWeight_nonneg hVB
  have hε : 0 ≤ ε := div_nonneg (Nat.cast_nonneg N) (Nat.cast_nonneg _)
  have hG (s : GiantSignedState PS PB (k+ell)) : ‖G s‖ =
      ∑ i : I, w i * (if gate s i then giantSignedRawCoreAbsoluteSection ν V κ q ρ fN i s else 0) := by
    have he : G s = ((∑ i : I, w i *
        (if gate s i then giantSignedRawCoreAbsoluteSection ν V κ q ρ fN i s else 0) : ℝ) : ℂ) := by
      simp only [G, H, Complex.ofReal_sum, Complex.ofReal_mul, apply_ite, Complex.ofReal_zero]
    rw [he, Complex.norm_real, Real.norm_eq_abs]
    apply abs_of_nonneg
    apply Finset.sum_nonneg
    intro i _
    apply mul_nonneg (hw i)
    split_ifs
    · exact norm_nonneg _
    · exact le_rfl
  have hpoint (s : GiantSignedState PS PB (k+ell)) : ‖F s‖ ≤ W * ‖G s‖ := by
    rw [hG]
    exact giantSignedRawProjectedPromote_norm_le hPS hPB hVS hVB ν hν V
      (fun j => hvmin.trans_le (hVmin j)) κ hq.le hρ θ ζ W hW K hK η hη N f s
  have hm (s : GiantSignedState PS PB (k+ell)) : (∑ i : I, if gate s i then w i else 0) ≤ ε :=
    giantSignedRawOuterCappedSourceGate_mass hPS hPB hdis hsep hVB N kStep hk sign hsign
      hstep tSmall tBig hlabels hgap hlower s
  have hgate := giantSignedStateEnergy_gate_average PS hVS ν hν w hw gate H ε hε hm
  obtain ⟨U, hU, hb⟩ := giantSignedStateMemoryCutoff_bound N f
  have hsN := giantSignedStateMemoryCutoff_memory_symmetric N f hsym
  have hi (i : I) : giantSignedStateEnergy PS ν (H i) ≤ ENNReal.ofReal E * giantSignedStateEnergy PS ν fN :=
    giantSignedRawCoreAbsoluteSection_energy hPS hdis hVS ν hν V hvmin hVmin hVmax hMass
      hq hq1 hBS hsmall hρ hρ1 hv hU budget hC κ fN hb hsN i
  have hsum : (∑ i : I, ENNReal.ofReal (w i) * giantSignedStateEnergy PS ν (H i)) ≤
      ENNReal.ofReal E * giantSignedStateEnergy PS ν fN := by
    calc
      _ ≤ ∑ i : I, ENNReal.ofReal (w i) * (ENNReal.ofReal E * giantSignedStateEnergy PS ν fN) :=
        Finset.sum_le_sum (fun i _ => mul_le_mul_right (hi i) _)
      _ = _ := by
        rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg (fun i _ => hw i),
          giantSignedRawOuterWeight_sum C hVB, ENNReal.ofReal_one, one_mul]
  change giantSignedStateEnergy PS ν F ≤ ENNReal.ofReal (W ^ 2 * ε * E) * giantSignedStateEnergy PS ν f
  calc
    _ ≤ ENNReal.ofReal (W ^ 2) * giantSignedStateEnergy PS ν G :=
      giantSignedStateEnergy_norm_domination PS hVS ν hν F G W hpoint
    _ ≤ ENNReal.ofReal (W ^ 2) * (ENNReal.ofReal ε * (ENNReal.ofReal E * giantSignedStateEnergy PS ν fN)) :=
      mul_le_mul_right (hgate.trans (mul_le_mul_right hsum _)) _
    _ ≤ ENNReal.ofReal (W ^ 2) * (ENNReal.ofReal ε * (ENNReal.ofReal E * giantSignedStateEnergy PS ν f)) :=
      mul_le_mul_right (mul_le_mul_right (mul_le_mul_right
        (giantSignedStateMemoryCutoff_energy_le ν N f) _) _) _
    _ = _ := by
      rw [ENNReal.ofReal_mul (mul_nonneg (sq_nonneg W) hε), ENNReal.ofReal_mul (sq_nonneg W)]
      ac_rfl

end
end ArtinMatthews
