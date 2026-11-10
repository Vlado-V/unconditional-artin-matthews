module

public import ArtinMatthews.GiantSignedRawCoupledPairing
public import ArtinMatthews.GiantSignedEdgePairingConvergence
public import ArtinMatthews.GiantSignedEdgePairingReal
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

/-! Copied labels, small coordinates and the exact factorial pairing in each raw section. -/
namespace ArtinMatthews
open scoped BigOperators ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell : ℕ}
    [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]
    [∀ g, ∀ p : PB g, NeZero p.val]
    {C : B → Finset (Fin k)}

def giantSignedRawCoupledBlock (ν : ∀ g, PB g → ℝ) (V : B → ℝ)
    (κ : ℤ) (q ρ : ℝ) (F : GiantSignedRawCoupledTest PS PB C ell)
    (i : GiantSignedRawOuterChoice (S := S) PB C ell)
    (c : GiantSignedPatternCopiedLabels PB C)
    (x z : GiantTwoSidedResidueState PS (k+ell)) : ℝ≥0∞ :=
  let DBig := giantSignedCopiedLabelsProduct c * giantTwoSidedPatternAuxiliaryProduct i.2.2
  let D := giantSignedSmallPrefixProduct x * DBig
  ENNReal.ofReal (giantTwoSidedResidueHaarStateMass PS (k+ell) *
      giantSignedPatternCopiedMass ν c * giantSignedSmallEdgeWeight κ DBig q x z) *
    giantSignedEdgeCoupledENNPairing ν V ρ (κ * (D : ℤ))
      (fun X Y a b old out => ENNReal.ofReal
        (giantSignedRawCoupledFiberTest F i x z D (giantSignedPatternSourceFill C c) X Y a b old out))

theorem giantSignedRawCoupledSectionPairing_blocks
    (hVS : ∀ j, 0 < bandReciprocalMass (PS j))
    (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p)
    (V : B → ℝ) (hV : ∀ g, 0 < V g) (κ : ℤ) (q : ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (F : GiantSignedRawCoupledTest PS PB C ell) (hF : ∀ X Y s t, 0 ≤ F X Y s t)
    (i : GiantSignedRawOuterChoice (S := S) PB C ell) :
    giantSignedRawCoupledSectionPairing ν V κ q ρ F i =
      ∑ c : GiantSignedPatternCopiedLabels PB C,
        ∑ x : GiantTwoSidedResidueState PS (k+ell), ∑ z : GiantTwoSidedResidueState PS (k+ell),
          giantSignedRawCoupledBlock ν V κ q ρ F i c x z := by
  let L := GiantSignedPatternCopiedLabels PB C
  let X := GiantTwoSidedResidueState PS (k+ell)
  let A := GiantSignedPrimeTuple PB (fun j => ell + (C j).card)
  let H := giantTwoSidedResidueHaarStateMass PS (k+ell)
  let D₀ (c : L) := giantSignedCopiedLabelsProduct c * giantTwoSidedPatternAuxiliaryProduct i.2.2
  let D (c : L) (x : X) := giantSignedSmallPrefixProduct x * D₀ c
  let w (c : L) (x z : X) := giantSignedSmallEdgeWeight κ (D₀ c) q x z
  let p (c : L) (x z : X) := H * giantSignedPatternCopiedMass ν c * w c x z
  let G (c : L) (x z : X) := giantSignedRawCoupledFiberTest F i x z (D c x)
    (giantSignedPatternSourceFill C c)
  let J (c : L) (x z : X) (a : A) (m : GiantSignedMemory PB) :=
    giantSignedEdgeCoupledApply ν V ρ (κ * (D c x : ℤ)) (G c x z) a m
  let Q (c : L) (x z : X) (a : A) (m : GiantSignedMemory PB) :=
    ENNReal.ofReal (p c x z) * ENNReal.ofReal
      (giantSignedFreePrimeRealMass ν a * (giantSignedMemoryMass ν m * J c x z a m))
  have hp (c : L) (x z : X) : 0 ≤ p c x z :=
    mul_nonneg (mul_nonneg (giantSignedRawSmallHaar_nonneg hVS)
      (Finset.prod_nonneg fun g _ => Finset.prod_nonneg fun j _ => hν g (c g j)))
      (giantSignedSmallEdgeWeight_nonneg _ _ _ _ _)
  have hG (c : L) (x z : X) : ∀ I T a b old out, 0 ≤ G c x z I T a b old out :=
    giantSignedRawCoupledFiberTest_nonneg F hF i x z (D c x) _
  have hJ (c : L) (x z : X) (a : A) (m : GiantSignedMemory PB) : 0 ≤ J c x z a m :=
    giantSignedEdgeCoupledApply_nonneg ν hν V (fun j => (hV j).le) hρ _ _ (hG c x z) a m
  have hpoint (c : L) (x : X) (a : A) (m : GiantSignedMemory PB) :
      ENNReal.ofReal (giantSignedStateMass PS ν (x, giantSignedPatternSourceFill C c a, m) *
        giantSignedRawCoupledSection ν V κ q ρ F i x (giantSignedPatternSourceFill C c a) m) =
          ∑ z : X, Q c x z a m := by
    have hfill : giantSignedPatternFill C (giantSignedPatternSourceFill C c a) =
        giantSignedPatternSourceFill C c :=
      funext (giantSignedPatternSourceFill_patternFill C c a)
    unfold giantSignedRawCoupledSection
    rw [giantSignedPatternSourceFill_product, giantSignedPatternSourceFill_freeLabels, hfill]
    change ENNReal.ofReal (giantSignedStateMass PS ν (x, giantSignedPatternSourceFill C c a, m) *
      ∑ z : X, w c x z * J c x z a m) = _
    rw [Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg (fun z _ =>
      mul_nonneg (giantSignedRawStateMass_nonneg hVS ν hν _)
        (mul_nonneg (giantSignedSmallEdgeWeight_nonneg _ _ _ _ _) (hJ c x z a m)))]
    apply Finset.sum_congr rfl
    intro z _
    dsimp only [Q]
    rw [← ENNReal.ofReal_mul (hp c x z)]
    congr 1
    unfold giantSignedStateMass
    rw [giantSignedPatternSourceFill_mass]
    dsimp only [p]
    ring
  have hblock (c : L) (x z : X) :
      (∑ a : A, ∑' m : GiantSignedMemory PB, Q c x z a m) =
        giantSignedRawCoupledBlock ν V κ q ρ F i c x z := by
    change (∑ a : A, ∑' m : GiantSignedMemory PB, Q c x z a m) =
      ENNReal.ofReal (p c x z) *
        giantSignedEdgeCoupledENNPairing ν V ρ (κ * (D c x : ℤ))
          (fun X Y a b old out => ENNReal.ofReal (G c x z X Y a b old out))
    unfold giantSignedEdgeCoupledENNPairing
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [← ENNReal.tsum_mul_left]
    apply tsum_congr
    intro m
    exact congrArg (fun t : ℝ≥0∞ => ENNReal.ofReal (p c x z) * t)
      (giantSignedEdgeCoupledENNRow_ofReal ν hν V (fun j => (hV j).le) hρ
        (κ * (D c x : ℤ)) (G c x z) (hG c x z) a m).symm
  unfold giantSignedRawCoupledSectionPairing
  simp only [ENNReal.tsum_prod', tsum_fintype]
  calc
    _ = ∑ x : X, ∑ c : L, ∑ a : A, ∑' m : GiantSignedMemory PB, ∑ z : X, Q c x z a m := by
      apply Finset.sum_congr rfl
      intro x _
      rw [← (giantSignedPatternSourceEquiv (P := PB) (ell := ell) C).symm.sum_comp]
      simp only [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro c _
      apply Finset.sum_congr rfl
      intro a _
      apply tsum_congr
      intro m
      exact hpoint c x a m
    _ = ∑ x : X, ∑ c : L, ∑ z : X, ∑ a : A, ∑' m : GiantSignedMemory PB, Q c x z a m := by
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro c _
      have he (a : A) : (∑' m : GiantSignedMemory PB, ∑ z : X, Q c x z a m) =
          ∑ z : X, ∑' m : GiantSignedMemory PB, Q c x z a m := by
        simpa only [tsum_fintype] using
          (ENNReal.tsum_comm (f := fun (m : GiantSignedMemory PB) (z : X) => Q c x z a m))
      simp_rw [he]
      exact Finset.sum_comm
    _ = _ := by
      simp_rw [hblock]
      exact Finset.sum_comm

end
end ArtinMatthews
