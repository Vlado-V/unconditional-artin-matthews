module

public import ArtinMatthews.GiantSignedSmallFreeEdgeData
public import ArtinMatthews.GiantSignedEdgeEnergy
public import ArtinMatthews.GiantSignedPatternFiberEnergy
public import ArtinMatthews.GiantSignedWeightedPairing
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

/-! Full factorial energy of the literal small-state and free-label edge. -/
namespace ArtinMatthews
open scoped BigOperators ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

private theorem ghost_energy_weighted_sum {I B : Type*} [Fintype I] [Fintype B]
    {PB : B → Finset ℕ} (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p)
    (w : I → ℝ) (hw : ∀ i, 0 ≤ w i) {L : ℝ} (hL : 0 ≤ L) (hsum : ∑ i, w i ≤ L)
    (F : I → GiantSignedMemory PB → ℂ) :
    giantSignedGhostMemoryEnergy ν (fun m => ∑ i, (w i : ℂ) * F i m) ≤
      ENNReal.ofReal L * ∑ i, ENNReal.ofReal (w i) * giantSignedGhostMemoryEnergy ν (F i) := by
  classical
  have hpoint (m : GiantSignedMemory PB) :
      ‖∑ i, (w i : ℂ) * F i m‖ ^ 2 ≤ L * ∑ i, w i * ‖F i m‖ ^ 2 := by
    have h := giantSignedWeightedPairing_finite Finset.univ w hw (fun _ => 1) (fun i => F i m)
    simp only [star_one, mul_one, norm_one, one_pow] at h
    exact h.trans (mul_le_mul_of_nonneg_right hsum
      (Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (sq_nonneg _))))
  have hcomm : (∑ i, ENNReal.ofReal (w i) * giantSignedGhostMemoryEnergy ν (F i)) =
      ∑' m : GiantSignedMemory PB, ∑ i, ENNReal.ofReal (w i) *
        ENNReal.ofReal (giantSignedMemoryMass ν m * ‖F i m‖ ^ 2) := by
    unfold giantSignedGhostMemoryEnergy
    simp_rw [← ENNReal.tsum_mul_left]
    calc
      _ = ∑' i : I, ∑' m : GiantSignedMemory PB, ENNReal.ofReal (w i) *
          ENNReal.ofReal (giantSignedMemoryMass ν m * ‖F i m‖ ^ 2) := (tsum_fintype _).symm
      _ = ∑' m : GiantSignedMemory PB, ∑' i : I, ENNReal.ofReal (w i) *
          ENNReal.ofReal (giantSignedMemoryMass ν m * ‖F i m‖ ^ 2) := ENNReal.tsum_comm
      _ = _ := by simp only [tsum_fintype]
  rw [hcomm, ← ENNReal.tsum_mul_left]
  unfold giantSignedGhostMemoryEnergy
  apply ENNReal.tsum_le_tsum
  intro m
  calc
    _ ≤ ENNReal.ofReal (giantSignedMemoryMass ν m * (L * ∑ i, w i * ‖F i m‖ ^ 2)) :=
      ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_left (hpoint m) (giantSignedMemoryMass_nonneg ν hν m))
    _ = _ := by
      rw [mul_left_comm, ENNReal.ofReal_mul hL, Finset.mul_sum,
        ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg
          (giantSignedMemoryMass_nonneg ν hν m) (mul_nonneg (hw i) (sq_nonneg _)))]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [← ENNReal.ofReal_mul (hw i)]
      congr 1
      ring

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell : ℕ} {t : B → ℕ}
    [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]
    [∀ g, ∀ p : PB g, NeZero p.val]

theorem giantSignedSmallFreeEdgeApply_energy
    (hPS : ∀ j p, p ∈ PS j → p.Prime)
    (hdis : Pairwise (fun i j => Disjoint (PS i) (PS j)))
    (hVS : ∀ j, 0 < bandReciprocalMass (PS j))
    (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p) (V : B → ℝ)
    {vmin vmax massMax q ρ v U u BS : ℝ}
    (hvmin : 0 < vmin) (hVmin : ∀ g, vmin ≤ V g) (hVmax : ∀ g, V g ≤ vmax)
    (hMass : ∀ g, (∑ p : PB g, ν g p) ≤ massMax)
    (hq : 0 < q) (hq1 : q ≤ 1) (hBS : 0 ≤ BS)
    (hbudget : ∀ j (z : ℕ),
      (bandReciprocalMass (PS j))⁻¹ ^ ell * ((z : ℝ) + (ell : ℝ)) ^ ell *
        q ^ ((z : ℝ) / 2) ≤ BS)
    (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (hv : 1 ≤ v) (hU : 0 ≤ U) (hu : 1 ≤ u)
    (tmax : ℕ) (ht : ∀ g, t g ≤ tmax) (κ : ℤ) (D : ℕ)
    (f : GiantTwoSidedResidueState PS (k+ell) → GiantSignedPrimeTuple PB t →
      GiantSignedMemory PB → ℂ)
    (hf : ∀ s a m, ‖f s a m‖ ≤ U * u ^ (∑ g, m.1 g))
    (hsym : ∀ s a, GiantSignedMemorySymmetric (f s a)) :
    giantSignedFreeStateEnergy PS ν (giantSignedSmallFreeEdgeApply ν V κ q ρ D f) ≤
      ENNReal.ofReal ((BS ^ Fintype.card S) ^ 2 *
        (giantSignedEdgeEnergyConstant ρ v vmin vmax massMax tmax) ^ Fintype.card B) *
          giantSignedFreeStateEnergy PS ν f := by
  let L := BS ^ Fintype.card S
  let E := (giantSignedEdgeEnergyConstant ρ v vmin vmax massMax tmax) ^ Fintype.card B
  let A (s z : GiantTwoSidedResidueState PS (k+ell)) := giantSignedSmallEdgeWeight κ D q s z
  let T (s z : GiantTwoSidedResidueState PS (k+ell)) (a : GiantSignedPrimeTuple PB t)
      (m : GiantSignedMemory PB) := giantSignedEdgeApply (fun g p => (ν g p : ℂ)) V ρ
        (κ * ((giantSignedSmallPrefixProduct s * D : ℕ) : ℤ))
        (giantSignedSmallPrefixProduct s * D) a (f z) m
  let F (z : GiantTwoSidedResidueState PS (k+ell)) :=
    ∑ a : GiantSignedPrimeTuple PB t, ENNReal.ofReal (giantSignedFreePrimeRealMass ν a) *
      giantSignedGhostMemoryEnergy ν (f z a)
  have hL : 0 ≤ L := pow_nonneg hBS _
  have hA (s z : GiantTwoSidedResidueState PS (k+ell)) : 0 ≤ A s z := norm_nonneg _
  have hrow (s : GiantTwoSidedResidueState PS (k+ell)) : ∑ z, A s z ≤ L :=
    giantSignedSmallEdgeWeight_row hPS hdis hVS κ D hq hq1 hBS hbudget s
  have hcol (z : GiantTwoSidedResidueState PS (k+ell)) : ∑ s, A s z ≤ L :=
    giantSignedSmallEdgeWeight_column hPS hdis hVS κ D hq hq1 hBS hbudget z
  have hedge (s z : GiantTwoSidedResidueState PS (k+ell)) :
      (∑ a : GiantSignedPrimeTuple PB t,
        ENNReal.ofReal (giantSignedFreePrimeRealMass ν a) * giantSignedGhostMemoryEnergy ν (T s z a)) ≤
      ENNReal.ofReal E * F z :=
    giantSignedEdgeApply_energy ν hν V hvmin hVmin hVmax hMass hρ hρ1 hv hU hu tmax ht
      (κ * ((giantSignedSmallPrefixProduct s * D : ℕ) : ℤ))
      (giantSignedSmallPrefixProduct s * D) (f z) (hf z) (hsym z)
  have hlocal (s : GiantTwoSidedResidueState PS (k+ell)) :
      (∑ a : GiantSignedPrimeTuple PB t, ENNReal.ofReal (giantSignedFreePrimeRealMass ν a) *
        giantSignedGhostMemoryEnergy ν (giantSignedSmallFreeEdgeApply ν V κ q ρ D f s a)) ≤
      ENNReal.ofReal L * ENNReal.ofReal E * ∑ z, ENNReal.ofReal (A s z) * F z := by
    calc
      _ ≤ ∑ a : GiantSignedPrimeTuple PB t, ENNReal.ofReal (giantSignedFreePrimeRealMass ν a) *
          (ENNReal.ofReal L * ∑ z, ENNReal.ofReal (A s z) * giantSignedGhostMemoryEnergy ν (T s z a)) := by
        apply Finset.sum_le_sum
        intro a _
        exact mul_le_mul_right (ghost_energy_weighted_sum ν hν (A s) (hA s) hL (hrow s)
          (fun z => T s z a)) _
      _ = ENNReal.ofReal L * ∑ z, ENNReal.ofReal (A s z) *
          ∑ a : GiantSignedPrimeTuple PB t, ENNReal.ofReal (giantSignedFreePrimeRealMass ν a) *
            giantSignedGhostMemoryEnergy ν (T s z a) := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro z _
        apply Finset.sum_congr rfl
        intro a _
        ac_rfl
      _ ≤ ENNReal.ofReal L * ∑ z, ENNReal.ofReal (A s z) * (ENNReal.ofReal E * F z) := by
        apply mul_le_mul_right
        exact Finset.sum_le_sum (fun z _ => mul_le_mul_right (hedge s z) _)
      _ = _ := by
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro z _
        ac_rfl
  rw [giantSignedFreeStateEnergy_factor PS hVS, giantSignedFreeStateEnergy_factor PS hVS]
  have htotal : (∑ s : GiantTwoSidedResidueState PS (k+ell),
      ∑ a : GiantSignedPrimeTuple PB t, ENNReal.ofReal (giantSignedFreePrimeRealMass ν a) *
        giantSignedGhostMemoryEnergy ν (giantSignedSmallFreeEdgeApply ν V κ q ρ D f s a)) ≤
      (ENNReal.ofReal L * ENNReal.ofReal L * ENNReal.ofReal E) * ∑ z, F z := by
    calc
      _ ≤ ∑ s : GiantTwoSidedResidueState PS (k+ell),
          ENNReal.ofReal L * ENNReal.ofReal E * ∑ z, ENNReal.ofReal (A s z) * F z :=
        Finset.sum_le_sum (fun s _ => hlocal s)
      _ = ENNReal.ofReal L * ENNReal.ofReal E * ∑ z,
          (∑ s : GiantTwoSidedResidueState PS (k+ell), ENNReal.ofReal (A s z)) * F z := by
        simp only [Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
      _ ≤ ENNReal.ofReal L * ENNReal.ofReal E * ∑ z, ENNReal.ofReal L * F z := by
        apply mul_le_mul_right
        apply Finset.sum_le_sum
        intro z _
        apply mul_le_mul_left
        rw [← ENNReal.ofReal_sum_of_nonneg (fun s _ => hA s z)]
        exact ENNReal.ofReal_le_ofReal (hcol z)
      _ = _ := by rw [← Finset.mul_sum]; ac_rfl
  apply (mul_le_mul_right htotal _).trans_eq
  rw [pow_two, ENNReal.ofReal_mul (mul_nonneg hL hL), ENNReal.ofReal_mul hL]
  dsimp [F, E]
  ac_rfl

end
end ArtinMatthews
