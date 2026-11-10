module

public import ArtinMatthews.GiantSignedEdgeMoveExpansion
public import ArtinMatthews.GiantSignedEdgeSlotBudget
public import ArtinMatthews.GiantSignedEdgeRowBound
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

/-! Weighted Cauchy for the actual finite edge moves. The second factor
keeps the original hit condition, promotion ban and both pending dampings. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

private theorem finite_move_square {ι : Type*} [Fintype ι]
    (c η f : ι → ℂ) (hη : ∀ i, ‖η i‖ ≤ 1)
    (φ : ι → ℝ) (hφ : ∀ i, 0 < φ i) :
    ‖∑ i, c i * η i * f i‖ ^ 2 ≤
      (∑ i, ‖c i‖ * φ i) * (∑ i, ‖c i‖ * ‖f i‖ ^ 2 / φ i) := by
  have hs : ‖∑ i, c i * η i * f i‖ ≤ ∑ i, ‖c i‖ * ‖f i‖ := by
    apply norm_sum_le_of_le
    intro i _
    rw [norm_mul, norm_mul]
    calc
      _ ≤ ‖c i‖ * 1 * ‖f i‖ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hη i) (norm_nonneg _)) (norm_nonneg _)
      _ = _ := by ring
  apply (pow_le_pow_left₀ (norm_nonneg _) hs 2).trans
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
  · intro i _
    exact mul_nonneg (norm_nonneg _) (hφ i).le
  · intro i _
    exact div_nonneg (mul_nonneg (norm_nonneg _) (sq_nonneg _)) (hφ i).le
  · intro i _
    exact le_of_eq (by field_simp [ne_of_gt (hφ i)])

variable {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset ℕ} {t : J → ℕ}

omit [DecidableEq J] in
theorem giantSignedEdgeMoveCoefficient_eq_norm
    (ν : (j : J) → P j → ℝ) (hν : ∀ j p, 0 ≤ ν j p)
    (V : J → ℝ) (hV : ∀ j, 0 < V j) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (d : ℤ) (D : ℕ) (source target : GiantSignedPrimeTuple P t)
    (m : GiantSignedMemory P) (c : GiantSignedEdgeChoice t m.1) :
    giantSignedEdgeMoveCoefficient (fun j p => (ν j p : ℂ)) V ρ d D source target m c =
      (‖giantSignedEdgeMoveCoefficient (fun j p => (ν j p : ℂ)) V ρ d D
        source target m c‖ : ℂ) := by
  let a : ℝ := (∏ j, (V j)⁻¹ ^ (c.2.1 j).card) *
    giantSignedFreshPrimeRealMass ν c.2.1 target *
      if GiantSignedEdgeHits d m target c ∧ GiantSignedEdgePromotionBan D c.2.1 target then
        giantSignedPendingDamping ρ m *
          giantSignedPendingDamping ρ (giantSignedEdgeTarget d m source c)
      else 0
  have ha : 0 ≤ a := by
    apply mul_nonneg
    · exact mul_nonneg
        (Finset.prod_nonneg (fun j _ => pow_nonneg (inv_nonneg.mpr (hV j).le) _))
        (giantSignedFreshPrimeRealMass_nonneg ν hν _ _)
    · split_ifs
      · exact mul_nonneg (giantSignedPendingDamping_nonneg hρ _)
          (giantSignedPendingDamping_nonneg hρ _)
      · exact le_rfl
  have he : giantSignedEdgeMoveCoefficient (fun j p => (ν j p : ℂ)) V ρ d D
      source target m c = (a : ℂ) := by
    unfold giantSignedEdgeMoveCoefficient giantSignedPromotionCharge
      giantSignedFreshPrimeMass a giantSignedFreshPrimeRealMass
    split_ifs <;> push_cast <;> rfl
  rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha]

theorem giantSignedEdgeApply_nonnegative_norm
    (ν : (j : J) → P j → ℝ) (hν : ∀ j p, 0 ≤ ν j p)
    (V : J → ℝ) (hV : ∀ j, 0 < V j) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (d : ℤ) (D : ℕ) (source : GiantSignedPrimeTuple P t)
    (f : GiantSignedPrimeTuple P t → GiantSignedMemory P → ℝ)
    (hf : ∀ target out, 0 ≤ f target out) (m : GiantSignedMemory P) :
    ‖giantSignedEdgeApply (fun j p => (ν j p : ℂ)) V ρ d D source
      (fun target out => (f target out : ℂ)) m‖ =
      ∑ c : GiantSignedEdgeChoice t m.1, ∑ target : GiantSignedPrimeTuple P t,
        ‖giantSignedEdgeMoveCoefficient (fun j p => (ν j p : ℂ)) V ρ d D
          source target m c‖ * f target (giantSignedEdgeTarget d m source c) := by
  rw [giantSignedEdgeApply_eq_choice_sum]
  have he : (∑ c : GiantSignedEdgeChoice t m.1, ∑ target : GiantSignedPrimeTuple P t,
      giantSignedEdgeMoveCoefficient (fun j p => (ν j p : ℂ)) V ρ d D
        source target m c * (f target (giantSignedEdgeTarget d m source c) : ℂ)) =
      ((∑ c : GiantSignedEdgeChoice t m.1, ∑ target : GiantSignedPrimeTuple P t,
        ‖giantSignedEdgeMoveCoefficient (fun j p => (ν j p : ℂ)) V ρ d D
          source target m c‖ * f target (giantSignedEdgeTarget d m source c) : ℝ) : ℂ) := by
    simp only [Complex.ofReal_sum, Complex.ofReal_mul]
    apply Finset.sum_congr rfl
    intro c _
    apply Finset.sum_congr rfl
    intro target _
    exact congrArg (fun z : ℂ => z * (f target (giantSignedEdgeTarget d m source c) : ℂ))
      (giantSignedEdgeMoveCoefficient_eq_norm ν hν V hV hρ d D source target m c)
  rw [he, Complex.norm_real, Real.norm_eq_abs]
  exact abs_of_nonneg (Finset.sum_nonneg (fun c _ => Finset.sum_nonneg
    (fun target _ => mul_nonneg (norm_nonneg _) (hf _ _))))

theorem giantSignedEdgeMoveSum_sq_le
    (ν : (j : J) → P j → ℝ) (hν : ∀ j p, 0 ≤ ν j p)
    (V : J → ℝ) {vmin massMax ρ v : ℝ}
    (hvmin : 0 < vmin) (hV : ∀ j, vmin ≤ V j)
    (hMass : ∀ j, (∑ p : P j, ν j p) ≤ massMax)
    (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (hv : 1 ≤ v)
    (tmax : ℕ) (ht : ∀ j, t j ≤ tmax) (d : ℤ) (D : ℕ)
    (source : GiantSignedPrimeTuple P t)
    (f : GiantSignedPrimeTuple P t → GiantSignedMemory P → ℂ)
    (m : GiantSignedMemory P)
    (η : GiantSignedEdgeChoice t m.1 → GiantSignedPrimeTuple P t → ℂ)
    (hη : ∀ c target, ‖η c target‖ ≤ 1) :
    ‖∑ c : GiantSignedEdgeChoice t m.1, ∑ target : GiantSignedPrimeTuple P t,
      giantSignedEdgeMoveCoefficient (fun j p => (ν j p : ℂ)) V ρ d D
        source target m c * η c target * f target (giantSignedEdgeTarget d m source c)‖ ^ 2 ≤
      (v ^ (∑ j, m.1 j) *
        (giantSignedEdgeUniformConstant ρ v vmin⁻¹ massMax tmax) ^ Fintype.card J) *
      ‖giantSignedEdgeApply (fun j p => (ν j p : ℂ)) V ρ d D source
        (fun target out => (‖f target out‖ ^ 2 / v ^ (∑ j, out.1 j) : ℝ)) m‖ := by
  have hv0 : 0 < v := lt_of_lt_of_le zero_lt_one hv
  have hVp (j : J) : 0 < V j := lt_of_lt_of_le hvmin (hV j)
  have hs := finite_move_square
    (fun x : GiantSignedEdgeChoice t m.1 × GiantSignedPrimeTuple P t =>
      giantSignedEdgeMoveCoefficient (fun j p => (ν j p : ℂ)) V ρ d D
        source x.2 m x.1)
    (fun x => η x.1 x.2)
    (fun x => f x.2 (giantSignedEdgeTarget d m source x.1))
    (fun x => hη x.1 x.2)
    (fun x => v ^ (∑ j, (giantSignedEdgeTarget d m source x.1).1 j))
    (fun _ => pow_pos hv0 _)
  simp only [Fintype.sum_prod_type] at hs
  have hpow : ∀ (_target : GiantSignedPrimeTuple P t) (out : GiantSignedMemory P),
      0 ≤ v ^ (∑ j, out.1 j) := fun _ _ => (pow_pos hv0 _).le
  have htest : ∀ target out, 0 ≤ ‖f target out‖ ^ 2 / v ^ (∑ j, out.1 j) :=
    fun target out => div_nonneg (sq_nonneg _) (hpow target out)
  rw [← giantSignedEdgeApply_nonnegative_norm ν hν V hVp hρ d D source
    (fun _ out => v ^ (∑ j, out.1 j)) hpow m] at hs
  have he : (∑ c : GiantSignedEdgeChoice t m.1, ∑ target : GiantSignedPrimeTuple P t,
      ‖giantSignedEdgeMoveCoefficient (fun j p => (ν j p : ℂ)) V ρ d D
        source target m c‖ * ‖f target (giantSignedEdgeTarget d m source c)‖ ^ 2 /
          v ^ (∑ j, (giantSignedEdgeTarget d m source c).1 j)) =
      ‖giantSignedEdgeApply (fun j p => (ν j p : ℂ)) V ρ d D source
        (fun target out => (‖f target out‖ ^ 2 / v ^ (∑ j, out.1 j) : ℝ)) m‖ := by
    rw [giantSignedEdgeApply_nonnegative_norm ν hν V hVp hρ d D source _ htest m]
    simp only [mul_div_assoc]
  rw [he] at hs
  let weight : GiantSignedPrimeTuple P t → GiantSignedMemory P → ℂ :=
    fun _ out => ((v ^ (∑ j, out.1 j) : ℝ) : ℂ)
  have hweight : ∀ target out, ‖weight target out‖ ≤ 1 * v ^ (∑ j, out.1 j) := by
    intro target out
    change ‖((v ^ (∑ j, out.1 j) : ℝ) : ℂ)‖ ≤ _
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (pow_pos hv0 _), one_mul]
  have hr := giantSignedEdgeApply_row_bound ν hν V hvmin hV hMass hρ hρ1 hv
    zero_le_one tmax ht d D source weight hweight m
  simpa only [one_mul] using hs.trans
    (mul_le_mul_of_nonneg_right hr (norm_nonneg _))

theorem giantSignedEdgeApply_sq_le
    (ν : (j : J) → P j → ℝ) (hν : ∀ j p, 0 ≤ ν j p)
    (V : J → ℝ) {vmin massMax ρ v : ℝ}
    (hvmin : 0 < vmin) (hV : ∀ j, vmin ≤ V j)
    (hMass : ∀ j, (∑ p : P j, ν j p) ≤ massMax)
    (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (hv : 1 ≤ v)
    (tmax : ℕ) (ht : ∀ j, t j ≤ tmax) (d : ℤ) (D : ℕ)
    (source : GiantSignedPrimeTuple P t)
    (f : GiantSignedPrimeTuple P t → GiantSignedMemory P → ℂ)
    (m : GiantSignedMemory P) :
    ‖giantSignedEdgeApply (fun j p => (ν j p : ℂ)) V ρ d D source f m‖ ^ 2 ≤
      (v ^ (∑ j, m.1 j) *
        (giantSignedEdgeUniformConstant ρ v vmin⁻¹ massMax tmax) ^ Fintype.card J) *
      ‖giantSignedEdgeApply (fun j p => (ν j p : ℂ)) V ρ d D source
        (fun target out => (‖f target out‖ ^ 2 / v ^ (∑ j, out.1 j) : ℝ)) m‖ := by
  rw [giantSignedEdgeApply_eq_choice_sum]
  simpa only [mul_one] using giantSignedEdgeMoveSum_sq_le ν hν V hvmin hV hMass
    hρ hρ1 hv tmax ht d D source f m (fun _ _ => 1) (fun _ _ => by simp)

end
end ArtinMatthews
