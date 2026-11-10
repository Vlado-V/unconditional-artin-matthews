module

public import ArtinMatthews.GiantSignedEdgeMoveExpansion
public import ArtinMatthews.GiantSignedEdgeRealPairing
public import ArtinMatthews.GiantSignedEdgeReverseBudget
public import ArtinMatthews.GiantSignedEdgeSlotBudget
public import ArtinMatthews.GiantSignedGhostMemoryCoordinates
public import ArtinMatthews.GiantSignedEdgeCoupledPairing
public import ArtinMatthews.GiantSignedEdgeEnergyGrowth
public import ArtinMatthews.GiantSignedEdgeSquare
public import ArtinMatthews.GiantSignedEdgeWeakColumn
public import ArtinMatthews.GiantSignedGhostMemoryMoments
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

/-! The concrete unrestricted edge has an energy bound given by the
product of its proved row and weak-column constants. -/
namespace ArtinMatthews
open scoped BigOperators ENNReal
noncomputable section

variable {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset ℕ}
variable [∀ j, ∀ p : P j, NeZero p.val] {t : J → ℕ}

def giantSignedEdgeEnergyConstant (ρ v vmin vmax massMax : ℝ) (tmax : ℕ) : ℝ :=
  giantSignedEdgeReverseConstant vmin vmax tmax *
    (giantSignedEdgeUniformConstant ρ v vmin⁻¹ massMax tmax) ^ 2

omit [∀ j, ∀ p : P j, NeZero p.val] in
private theorem free_memory_energy_eq
    (ν : (j : J) → P j → ℝ) (hν : ∀ j p, 0 ≤ ν j p)
    (f : GiantSignedPrimeTuple P t → GiantSignedMemory P → ℂ)
    (hf : ∀ source, Summable (fun m => giantSignedMemoryMass ν m * ‖f source m‖ ^ 2)) :
    (∑ source : GiantSignedPrimeTuple P t,
      ENNReal.ofReal (giantSignedFreePrimeRealMass ν source) *
        giantSignedGhostMemoryEnergy ν (f source)) =
      ENNReal.ofReal (∑ source : GiantSignedPrimeTuple P t,
        giantSignedFreePrimeRealMass ν source *
          ∑' m, giantSignedMemoryMass ν m * ‖f source m‖ ^ 2) := by
  rw [ENNReal.ofReal_sum_of_nonneg (fun source _ =>
    mul_nonneg (giantSignedFreePrimeRealMass_nonneg ν hν source)
      (tsum_nonneg (fun m => mul_nonneg (giantSignedMemoryMass_nonneg ν hν m)
        (sq_nonneg _))))]
  apply Finset.sum_congr rfl
  intro source _
  rw [ENNReal.ofReal_mul (giantSignedFreePrimeRealMass_nonneg ν hν source)]
  unfold giantSignedGhostMemoryEnergy
  rw [ENNReal.ofReal_tsum_of_nonneg
    (fun m => mul_nonneg (giantSignedMemoryMass_nonneg ν hν m) (sq_nonneg _)) (hf source)]

theorem giantSignedEdgeMoveSum_energy
    (ν : (j : J) → P j → ℝ) (hν : ∀ j p, 0 ≤ ν j p)
    (V : J → ℝ) {vmin vmax massMax ρ v B u : ℝ}
    (hvmin : 0 < vmin) (hVmin : ∀ j, vmin ≤ V j) (hVmax : ∀ j, V j ≤ vmax)
    (hMass : ∀ j, (∑ p : P j, ν j p) ≤ massMax)
    (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (hv : 1 ≤ v) (_hB : 0 ≤ B) (_hu : 1 ≤ u)
    (tmax : ℕ) (ht : ∀ j, t j ≤ tmax) (d : ℤ) (D : ℕ)
    (f : GiantSignedPrimeTuple P t → GiantSignedMemory P → ℂ)
    (hf : ∀ target out, ‖f target out‖ ≤ B * u ^ (∑ j, out.1 j))
    (hsym : ∀ target, GiantSignedMemorySymmetric (f target))
    (η : (source : GiantSignedPrimeTuple P t) → (m : GiantSignedMemory P) →
      GiantSignedEdgeChoice t m.1 → GiantSignedPrimeTuple P t → ℂ)
    (hη : ∀ source m c target, ‖η source m c target‖ ≤ 1) :
    (∑ source : GiantSignedPrimeTuple P t,
      ENNReal.ofReal (giantSignedFreePrimeRealMass ν source) *
        giantSignedGhostMemoryEnergy ν (fun m =>
          ∑ c : GiantSignedEdgeChoice t m.1, ∑ target : GiantSignedPrimeTuple P t,
            giantSignedEdgeMoveCoefficient (fun j p => (ν j p : ℂ)) V ρ d D
              source target m c * η source m c target *
                f target (giantSignedEdgeTarget d m source c))) ≤
      ENNReal.ofReal ((giantSignedEdgeEnergyConstant ρ v vmin vmax massMax tmax) ^
        Fintype.card J) *
      ∑ source : GiantSignedPrimeTuple P t,
        ENNReal.ofReal (giantSignedFreePrimeRealMass ν source) *
          giantSignedGhostMemoryEnergy ν (f source) := by
  let R := (giantSignedEdgeUniformConstant ρ v vmin⁻¹ massMax tmax) ^ Fintype.card J
  let C := (giantSignedEdgeReverseConstant vmin vmax tmax *
    giantSignedEdgeUniformConstant ρ v vmin⁻¹ massMax tmax) ^ Fintype.card J
  let F (source : GiantSignedPrimeTuple P t) (m : GiantSignedMemory P) : ℂ :=
    ∑ c : GiantSignedEdgeChoice t m.1, ∑ target : GiantSignedPrimeTuple P t,
      giantSignedEdgeMoveCoefficient (fun j p => (ν j p : ℂ)) V ρ d D
        source target m c * η source m c target * f target (giantSignedEdgeTarget d m source c)
  let g (target : GiantSignedPrimeTuple P t) (out : GiantSignedMemory P) : ℝ :=
    ‖f target out‖ ^ 2 / v ^ (∑ j, out.1 j)
  have hv0 : 0 < v := lt_of_lt_of_le zero_lt_one hv
  have hR : 0 ≤ R := pow_nonneg
    (giantSignedEdgeUniformConstant_nonneg hρ1 hv0.le) _
  have hg0 : ∀ target out, 0 ≤ g target out :=
    fun _ _ => div_nonneg (sq_nonneg _) (pow_pos hv0 _).le
  have hgg : ∀ target out, g target out ≤
      B ^ 2 * (max 1 (u ^ 2 / v)) ^ (∑ j, out.1 j) :=
    giantSignedEdgeSquareTest_growth hv0 f hf
  have hgs : ∀ target m σ, g target (giantSignedMemoryPermute m σ) = g target m :=
    giantSignedEdgeSquareTest_symmetric v f hsym
  have hgnorm : ∀ target out, ‖(g target out : ℂ)‖ ≤
      B ^ 2 * (max 1 (u ^ 2 / v)) ^ (∑ j, out.1 j) := by
    intro target out
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hg0 target out)]
    exact hgg target out
  have hlocal (source : GiantSignedPrimeTuple P t) :
      Summable (fun m : GiantSignedMemory P =>
        giantSignedMemoryMass ν m * ‖F source m‖ ^ 2) ∧
      (∑' m : GiantSignedMemory P, giantSignedMemoryMass ν m * ‖F source m‖ ^ 2) ≤
        R * ∑' m : GiantSignedMemory P, giantSignedMemoryMass ν m * v ^ (∑ j, m.1 j) *
          ‖giantSignedEdgeApply (fun j p => (ν j p : ℂ)) V ρ d D source
            (fun target out => (g target out : ℂ)) m‖ := by
    have hs := giantSignedEdgeApply_norm_summable ν hν V hvmin hVmin hMass hρ hρ1
      (sq_nonneg B) (le_max_left _ _) hv0.le tmax ht d D
      (fun target out => (g target out : ℂ)) hgnorm source
    have hpoint (m : GiantSignedMemory P) :
        giantSignedMemoryMass ν m * ‖F source m‖ ^ 2 ≤
          R * (giantSignedMemoryMass ν m * v ^ (∑ j, m.1 j) *
            ‖giantSignedEdgeApply (fun j p => (ν j p : ℂ)) V ρ d D source
              (fun target out => (g target out : ℂ)) m‖) := by
      have he := giantSignedEdgeMoveSum_sq_le ν hν V hvmin hVmin hMass hρ hρ1 hv
        tmax ht d D source f m (η source m) (hη source m)
      calc
        _ ≤ giantSignedMemoryMass ν m *
            ((v ^ (∑ j, m.1 j) * R) *
              ‖giantSignedEdgeApply (fun j p => (ν j p : ℂ)) V ρ d D source
                (fun target out => (g target out : ℂ)) m‖) :=
          mul_le_mul_of_nonneg_left he (giantSignedMemoryMass_nonneg ν hν m)
        _ = _ := by ring
    have hright := hs.mul_left R
    have hleft := hright.of_nonneg_of_le
      (fun m => mul_nonneg (giantSignedMemoryMass_nonneg ν hν m) (sq_nonneg _)) hpoint
    refine ⟨hleft, ?_⟩
    simpa only [tsum_mul_left] using hleft.tsum_le_tsum hpoint hright
  have hin : ∀ source, Summable (fun m : GiantSignedMemory P =>
      giantSignedMemoryMass ν m * ‖f source m‖ ^ 2) := by
    intro source
    exact giantSignedWeightedEnergy_summable (giantSignedMemoryMass ν)
      (giantSignedMemoryMass_nonneg ν hν) (f source)
      (giantSignedMemory_energy_ne_top ν hν (f source) B u (hf source))
  have hcolumn := giantSignedEdgeApply_weak_column_bound ν hν V hvmin hVmin hVmax hMass
    hρ hρ1 hv (sq_nonneg B) (le_max_left _ _) tmax ht d D g hg0 hgg hgs
  have hcancel : (∑ source : GiantSignedPrimeTuple P t, giantSignedFreePrimeRealMass ν source *
      ∑' m : GiantSignedMemory P, giantSignedMemoryMass ν m * v ^ (∑ j, m.1 j) * g source m) =
      ∑ source : GiantSignedPrimeTuple P t, giantSignedFreePrimeRealMass ν source *
        ∑' m : GiantSignedMemory P, giantSignedMemoryMass ν m * ‖f source m‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro source _
    congr 1
    apply tsum_congr
    intro m
    dsimp [g]
    field_simp [ne_of_gt (pow_pos hv0 (∑ j, m.1 j))]
  rw [hcancel] at hcolumn
  have hreal : (∑ source : GiantSignedPrimeTuple P t, giantSignedFreePrimeRealMass ν source *
      ∑' m : GiantSignedMemory P, giantSignedMemoryMass ν m * ‖F source m‖ ^ 2) ≤
      (R * C) * ∑ source : GiantSignedPrimeTuple P t, giantSignedFreePrimeRealMass ν source *
        ∑' m : GiantSignedMemory P, giantSignedMemoryMass ν m * ‖f source m‖ ^ 2 := by
    calc
      _ ≤ ∑ source : GiantSignedPrimeTuple P t, giantSignedFreePrimeRealMass ν source *
          (R * ∑' m : GiantSignedMemory P,
            giantSignedMemoryMass ν m * v ^ (∑ j, m.1 j) *
              ‖giantSignedEdgeApply (fun j p => (ν j p : ℂ)) V ρ d D source
                (fun target out => (g target out : ℂ)) m‖) :=
        Finset.sum_le_sum (fun source _ => mul_le_mul_of_nonneg_left (hlocal source).2
          (giantSignedFreePrimeRealMass_nonneg ν hν source))
      _ = R * ∑ source : GiantSignedPrimeTuple P t, giantSignedFreePrimeRealMass ν source *
          ∑' m : GiantSignedMemory P, giantSignedMemoryMass ν m * v ^ (∑ j, m.1 j) *
            ‖giantSignedEdgeApply (fun j p => (ν j p : ℂ)) V ρ d D source
              (fun target out => (g target out : ℂ)) m‖ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro source _
        ring
      _ ≤ R * (C * ∑ source : GiantSignedPrimeTuple P t,
          giantSignedFreePrimeRealMass ν source * ∑' m : GiantSignedMemory P,
            giantSignedMemoryMass ν m * ‖f source m‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hcolumn hR
      _ = _ := by ring
  have hRC : R * C = (giantSignedEdgeEnergyConstant ρ v vmin vmax massMax tmax) ^
      Fintype.card J := by
    dsimp [R, C, giantSignedEdgeEnergyConstant]
    rw [← mul_pow]
    congr 1
    ring
  change (∑ source : GiantSignedPrimeTuple P t,
    ENNReal.ofReal (giantSignedFreePrimeRealMass ν source) * giantSignedGhostMemoryEnergy ν (F source)) ≤ _
  rw [free_memory_energy_eq ν hν F (fun source => (hlocal source).1),
    free_memory_energy_eq ν hν f hin]
  rw [hRC] at hreal
  exact (ENNReal.ofReal_le_ofReal hreal).trans_eq
    (ENNReal.ofReal_mul (by
      rw [← hRC]
      exact mul_nonneg hR (pow_nonneg (mul_nonneg
        (giantSignedEdgeReverseConstant_nonneg _ _ _)
        (giantSignedEdgeUniformConstant_nonneg hρ1 hv0.le)) _)))

theorem giantSignedEdgeApply_energy
    (ν : (j : J) → P j → ℝ) (hν : ∀ j p, 0 ≤ ν j p)
    (V : J → ℝ) {vmin vmax massMax ρ v B u : ℝ}
    (hvmin : 0 < vmin) (hVmin : ∀ j, vmin ≤ V j) (hVmax : ∀ j, V j ≤ vmax)
    (hMass : ∀ j, (∑ p : P j, ν j p) ≤ massMax)
    (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (hv : 1 ≤ v) (hB : 0 ≤ B) (hu : 1 ≤ u)
    (tmax : ℕ) (ht : ∀ j, t j ≤ tmax) (d : ℤ) (D : ℕ)
    (f : GiantSignedPrimeTuple P t → GiantSignedMemory P → ℂ)
    (hf : ∀ target out, ‖f target out‖ ≤ B * u ^ (∑ j, out.1 j))
    (hsym : ∀ target, GiantSignedMemorySymmetric (f target)) :
    (∑ source : GiantSignedPrimeTuple P t,
      ENNReal.ofReal (giantSignedFreePrimeRealMass ν source) *
        giantSignedGhostMemoryEnergy ν
          (giantSignedEdgeApply (fun j p => (ν j p : ℂ)) V ρ d D source f)) ≤
      ENNReal.ofReal ((giantSignedEdgeEnergyConstant ρ v vmin vmax massMax tmax) ^
        Fintype.card J) *
      ∑ source : GiantSignedPrimeTuple P t,
        ENNReal.ofReal (giantSignedFreePrimeRealMass ν source) *
          giantSignedGhostMemoryEnergy ν (f source) := by
  have he := giantSignedEdgeMoveSum_energy ν hν V hvmin hVmin hVmax hMass hρ hρ1 hv hB hu
    tmax ht d D f hf hsym (fun _ _ _ _ => 1) (fun _ _ _ _ => by simp)
  simpa only [mul_one, ← giantSignedEdgeApply_eq_choice_sum] using he

end
end ArtinMatthews
