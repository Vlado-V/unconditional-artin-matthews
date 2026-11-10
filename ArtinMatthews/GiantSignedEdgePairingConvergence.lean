module

public import ArtinMatthews.GiantSignedEdgeCoupledPairing
public import ArtinMatthews.GiantSignedEdgePositive
public import ArtinMatthews.GiantSignedEdgeRowBound
public import ArtinMatthews.GiantSignedGhostMemoryMoments
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

/-! Actual exponential tests give summable full-memory edge pairings. -/
namespace ArtinMatthews
open scoped BigOperators ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset ℕ}
    [∀ j, ∀ p : P j, NeZero p.val] {t : J → ℕ}

omit [∀ j, ∀ p : P j, NeZero p.val] in
theorem giantSignedEdgeCoupledApply_nonneg
    (ν : (j : J) → P j → ℝ) (hν : ∀ j p, 0 ≤ ν j p)
    (V : J → ℝ) (hV : ∀ j, 0 ≤ V j) {ρ : ℝ} (hρ : 0 ≤ ρ) (d : ℤ)
    (F : GiantSignedEdgeCoupledTest P t ℝ)
    (hF : ∀ S T source target old out, 0 ≤ F S T source target old out)
    (source : GiantSignedPrimeTuple P t) (m : GiantSignedMemory P) :
    0 ≤ giantSignedEdgeCoupledApply ν V ρ d F source m := by
  unfold giantSignedEdgeCoupledApply
  apply Finset.sum_nonneg
  intro S _
  apply Finset.sum_nonneg
  intro T _
  apply Finset.sum_nonneg
  intro target _
  apply mul_nonneg
  · exact mul_nonneg
      (Finset.prod_nonneg fun j _ => pow_nonneg (inv_nonneg.mpr (hV j)) _)
      (giantSignedFreshPrimeRealMass_nonneg ν hν T target)
  · apply Finset.sum_nonneg
    intro e _
    split_ifs
    · exact mul_nonneg
        (mul_nonneg (giantSignedPendingDamping_nonneg hρ _)
          (giantSignedPendingDamping_nonneg hρ _)) (hF _ _ _ _ _ _)
    · exact le_rfl

omit [∀ j, ∀ p : P j, NeZero p.val] in
theorem giantSignedEdgeCoupledApply_le_positive
    (ν : (j : J) → P j → ℝ) (hν : ∀ j p, 0 ≤ ν j p)
    (V : J → ℝ) (hV : ∀ j, 0 ≤ V j) {ρ : ℝ} (hρ : 0 ≤ ρ) (d : ℤ)
    (F : GiantSignedEdgeCoupledTest P t ℝ)
    (source : GiantSignedPrimeTuple P t) (m : GiantSignedMemory P)
    (G : GiantSignedPrimeTuple P t → GiantSignedMemory P → ℝ)
    (hFG : ∀ S T target out, F S T source target m out ≤ G target out) :
    giantSignedEdgeCoupledApply ν V ρ d F source m ≤
      giantSignedEdgePositiveApply ν V ρ d source G m := by
  unfold giantSignedEdgeCoupledApply giantSignedEdgePositiveApply
  apply Finset.sum_le_sum
  intro S _
  apply Finset.sum_le_sum
  intro T _
  apply Finset.sum_le_sum
  intro target _
  apply mul_le_mul_of_nonneg_left
  · apply Finset.sum_le_sum
    intro e _
    split_ifs
    · exact mul_le_mul_of_nonneg_left (hFG _ _ _ _)
        (mul_nonneg (giantSignedPendingDamping_nonneg hρ _)
          (giantSignedPendingDamping_nonneg hρ _))
    · exact le_rfl
  · exact mul_nonneg
      (Finset.prod_nonneg fun j _ => pow_nonneg (inv_nonneg.mpr (hV j)) _)
      (giantSignedFreshPrimeRealMass_nonneg ν hν T target)

omit [∀ j, ∀ p : P j, NeZero p.val] in
theorem giantSignedEdgeCoupledApply_exponential_bound
    (ν : (j : J) → P j → ℝ) (hν : ∀ j p, 0 ≤ ν j p)
    (V : J → ℝ) (hV : ∀ j, 0 < V j) {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (d : ℤ)
    (F : GiantSignedEdgeCoupledTest P t ℝ) (B u v : ℝ)
    (hB : 0 ≤ B) (hu : 1 ≤ u) (hv : 1 ≤ v)
    (hF : ∀ S T source target old out,
      F S T source target old out ≤ B * u ^ (∑ j, old.1 j) * v ^ (∑ j, out.1 j)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ source m,
      giantSignedEdgeCoupledApply ν V ρ d F source m ≤ C * (u * v) ^ (∑ j, m.1 j) := by
  let rateMax := ∑ j, |(V j)⁻¹|
  let massMax := ∑ j, ∑ p : P j, ν j p
  let tmax := ∑ j, t j
  let K := (giantSignedEdgeUniformConstant ρ v rateMax massMax tmax) ^ Fintype.card J
  have hRate (j : J) : (V j)⁻¹ ≤ rateMax :=
    (le_abs_self _).trans (Finset.single_le_sum (fun i _ => abs_nonneg ((V i)⁻¹)) (Finset.mem_univ j))
  have hMass (j : J) : (∑ p : P j, ν j p) ≤ massMax := by
    change (∑ p : P j, ν j p) ≤ ∑ i, ∑ p : P i, ν i p
    exact Finset.single_le_sum
      (fun i _ => show 0 ≤ ∑ p : P i, ν i p from Finset.sum_nonneg fun p _ => hν i p)
      (Finset.mem_univ j)
  have ht (j : J) : t j ≤ tmax :=
    Finset.single_le_sum (fun i _ => Nat.zero_le (t i)) (Finset.mem_univ j)
  have hu0 : 0 ≤ u := le_trans zero_le_one hu
  have hv0 : 0 ≤ v := le_trans zero_le_one hv
  refine ⟨B * |K|, mul_nonneg hB (abs_nonneg K), ?_⟩
  intro source m
  let G := fun (_ : GiantSignedPrimeTuple P t) (out : GiantSignedMemory P) =>
    (B * u ^ (∑ j, m.1 j)) * v ^ (∑ j, out.1 j)
  have hcomp := giantSignedEdgeCoupledApply_le_positive ν hν V (fun j => (hV j).le)
    hρ d F source m G (fun S T target out => hF S T source target m out)
  have hrow := giantSignedEdgePositiveApply_bound ν hν V hV hρ hρ1 hv
    (mul_nonneg hB (pow_nonneg hu0 _)) hRate hMass tmax ht d source G
    (fun _ _ => le_rfl) m
  calc
    _ ≤ (B * u ^ (∑ j, m.1 j)) * v ^ (∑ j, m.1 j) * K := hcomp.trans hrow
    _ = (B * K) * (u * v) ^ (∑ j, m.1 j) := by rw [mul_pow]; ring
    _ ≤ (B * |K|) * (u * v) ^ (∑ j, m.1 j) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (le_abs_self K) hB)
        (pow_nonneg (mul_nonneg hu0 hv0) _)

theorem giantSignedEdgeCoupled_memory_summable
    (ν : (j : J) → P j → ℝ) (hν : ∀ j p, 0 ≤ ν j p)
    (V : J → ℝ) (hV : ∀ j, 0 < V j) {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (d : ℤ)
    (F : GiantSignedEdgeCoupledTest P t ℝ)
    (hF0 : ∀ S T source target old out, 0 ≤ F S T source target old out)
    (B u v : ℝ) (hB : 0 ≤ B) (hu : 1 ≤ u) (hv : 1 ≤ v)
    (hF : ∀ S T source target old out,
      F S T source target old out ≤ B * u ^ (∑ j, old.1 j) * v ^ (∑ j, out.1 j))
    (source : GiantSignedPrimeTuple P t) :
    Summable (fun m : GiantSignedMemory P =>
      giantSignedMemoryMass ν m * giantSignedEdgeCoupledApply ν V ρ d F source m) := by
  obtain ⟨C, _, hC⟩ := giantSignedEdgeCoupledApply_exponential_bound ν hν V hV hρ hρ1 d
    F B u v hB hu hv hF
  have hbase := (giantSignedMemory_exponential_summable ν hν (u * v)
    (mul_nonneg (le_trans zero_le_one hu) (le_trans zero_le_one hv))).mul_left C
  apply hbase.of_nonneg_of_le
  · intro m
    exact mul_nonneg (giantSignedMemoryMass_nonneg ν hν m)
      (giantSignedEdgeCoupledApply_nonneg ν hν V (fun j => (hV j).le) hρ d F hF0 source m)
  · intro m
    calc
      _ ≤ giantSignedMemoryMass ν m * (C * (u * v) ^ (∑ j, m.1 j)) :=
        mul_le_mul_of_nonneg_left (hC source m) (giantSignedMemoryMass_nonneg ν hν m)
      _ = _ := by ring

omit [∀ j, ∀ p : P j, NeZero p.val] in
theorem giantSignedEdgeCoupled_weighted_eq_terms
    (ν : (j : J) → P j → ℝ) (V : J → ℝ) (ρ : ℝ) (d : ℤ)
    (F : GiantSignedEdgeCoupledTest P t ℝ)
    (source : GiantSignedPrimeTuple P t) (m : GiantSignedMemory P) :
    giantSignedFreePrimeRealMass ν source *
        (giantSignedMemoryMass ν m * giantSignedEdgeCoupledApply ν V ρ d F source m) =
      ∑ S : (j : J) → Finset (Fin (t j)), ∑ T : (j : J) → Finset (Fin (t j)),
        ∑ target : GiantSignedPrimeTuple P t, ∑ e,
          giantSignedEdgeCoupledTerm ν V ρ d F S T source target m e := by
  unfold giantSignedEdgeCoupledApply giantSignedEdgeCoupledTerm giantSignedEdgeJointRealWeight
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S _
  apply Finset.sum_congr rfl
  intro T _
  apply Finset.sum_congr rfl
  intro target _
  apply Finset.sum_congr rfl
  intro e _
  split_ifs <;> ring

omit [∀ j, ∀ p : P j, NeZero p.val] in
theorem giantSignedEdgeCoupledPairing_eq_terms
    (ν : (j : J) → P j → ℝ) (V : J → ℝ) (ρ : ℝ) (d : ℤ)
    (F : GiantSignedEdgeCoupledTest P t ℝ) :
    giantSignedEdgeCoupledPairing ν V ρ d F =
      ∑ source : GiantSignedPrimeTuple P t, ∑' m : GiantSignedMemory P,
        ∑ S : (j : J) → Finset (Fin (t j)), ∑ T : (j : J) → Finset (Fin (t j)),
          ∑ target : GiantSignedPrimeTuple P t, ∑ e,
            giantSignedEdgeCoupledTerm ν V ρ d F S T source target m e := by
  unfold giantSignedEdgeCoupledPairing
  apply Finset.sum_congr rfl
  intro source _
  rw [← tsum_mul_left]
  apply tsum_congr
  intro m
  exact giantSignedEdgeCoupled_weighted_eq_terms ν V ρ d F source m

end
end ArtinMatthews
