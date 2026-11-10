module

public import ArtinMatthews.MarkedMinorArcRawEdgePatternAction
public import ArtinMatthews.MarkedMinorArcRawGhostWeight
public import ArtinMatthews.MarkedMinorArcDirtyRawEdgePromotionBound
public import ArtinMatthews.MarkedMinorArcRawEdgeChargedPositive
public import ArtinMatthews.MarkedMinorArcRawEdgePatternTranspose
public import ArtinMatthews.MarkedMinorArcRawGhostEnergyReduction
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
public import Mathlib.Tactic.Basify
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

/-! Weighted Cauchy and the genuine column identity for literal
flag-dependent edge restrictions.  Source cutoffs are transposed as part
of the joint kernel, rather than assumed to be invariant. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators

def markedRawEdgePatternNorm {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (A : MarkedRawEdgePatternKernel P pads B Z) : MarkedRawEdgePatternKernel P pads B Z :=
  fun p q s t => (‖A p q s t‖ : ℂ)

theorem markedRawEdgePatternNorm_reverse {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (A : MarkedRawEdgePatternKernel P pads B Z) :
    markedRawEdgePatternReverse (markedRawEdgePatternNorm A) =
      markedRawEdgePatternNorm (markedRawEdgePatternReverse A) := rfl

def markedRawEdgePatternWeightedRow {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (δ γ : J → ℂ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (A : MarkedRawEdgePatternKernel P pads B Z)
    (v₀ : ℝ) (s : MarkedRawState P (pads+1) B Z) : ℝ :=
  ∑ c : MarkedRawEdgeChoice hZ s,
    ‖markedRawEdgeChoiceCharge δ γ hZ s c * markedRawEdgeChoiceFreshMass ν hZ s c *
      A (markedRawEdgeChoicePromoted c) c.store s (markedRawEdgeTargetState hZ s c)‖ *
      (markedRawMemorySchurWeight v₀ (markedRawEdgeTargetMemory hZ s c) /
        markedRawMemorySchurWeight v₀ s.2.2)

def markedRawEdgePatternReverseEnergy {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (δ γ : J → ℂ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (A : MarkedRawEdgePatternKernel P pads B Z)
    (v₀ : ℝ) (f : MarkedRawState P (pads+1) B Z → ℂ)
    (s : MarkedRawState P (pads+1) B Z) : ℝ :=
  ∑ c : MarkedRawEdgeChoice hZ s,
    ‖markedRawEdgeChoiceCharge δ γ hZ s c * markedRawEdgeChoiceFreshMass ν hZ s c *
      A (markedRawEdgeChoicePromoted c) c.store s (markedRawEdgeTargetState hZ s c)‖ *
      (markedRawMemorySchurWeight v₀ s.2.2 /
        markedRawMemorySchurWeight v₀ (markedRawEdgeTargetMemory hZ s c)) *
      ‖f (markedRawEdgeTargetState hZ s c)‖ ^ 2

theorem markedRawEdgePatternApply_cauchy {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (δ γ : J → ℂ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (A : MarkedRawEdgePatternKernel P pads B Z)
    {v₀ : ℝ} (hv₀ : 0 < v₀) (f : MarkedRawState P (pads+1) B Z → ℂ)
    (s : MarkedRawState P (pads+1) B Z) :
    ‖markedRawEdgePatternApply ν δ γ hZ A f s‖ ^ 2 ≤
      markedRawEdgePatternWeightedRow ν δ γ hZ A v₀ s *
        markedRawEdgePatternReverseEnergy ν δ γ hZ A v₀ f s := by
  classical
  have h := markedGhostChoice_finite_cauchy
    (fun c : MarkedRawEdgeChoice hZ s => markedRawEdgeChoiceCharge δ γ hZ s c *
      markedRawEdgeChoiceFreshMass ν hZ s c *
      A (markedRawEdgeChoicePromoted c) c.store s (markedRawEdgeTargetState hZ s c))
    (fun c => f (markedRawEdgeTargetState hZ s c))
    (fun c => markedRawMemorySchurWeight v₀ (markedRawEdgeTargetMemory hZ s c) /
      markedRawMemorySchurWeight v₀ s.2.2)
    (fun _ => div_pos (markedRawMemorySchurWeight_pos hv₀ _) (markedRawMemorySchurWeight_pos hv₀ _))
  convert h using 1
  congr 1
  unfold markedRawEdgePatternWeightedRow markedRawEdgePatternReverseEnergy
  congr 1
  apply Finset.sum_congr rfl
  intro c _
  field_simp [(markedRawMemorySchurWeight_pos hv₀ s.2.2).ne',
    (markedRawMemorySchurWeight_pos hv₀ (markedRawEdgeTargetMemory hZ s c)).ne']

theorem markedRawEdgePatternWeightedRow_mul_weight
    {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (δ γ : J → ℝ)
    (hν : ∀ j p, 0 ≤ ν j p) (hδ : ∀ j, 0 ≤ δ j) (hγ : ∀ j, 0 ≤ γ j)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (A : MarkedRawEdgePatternKernel P pads B Z)
    {v₀ : ℝ} (hv₀ : 0 < v₀) (s : MarkedRawState P (pads+1) B Z) :
    (markedRawEdgePatternWeightedRow ν (fun j => (δ j : ℂ)) (fun j => (γ j : ℂ)) hZ A v₀ s : ℂ) *
      (markedRawMemorySchurWeight v₀ s.2.2 : ℂ) =
      markedRawEdgePatternApply ν (fun j => (δ j : ℂ)) (fun j => (γ j : ℂ)) hZ
        (markedRawEdgePatternNorm A) (fun t => (markedRawMemorySchurWeight v₀ t.2.2 : ℂ)) s := by
  classical
  have hs := (markedRawMemorySchurWeight_pos hv₀ s.2.2).ne'
  unfold markedRawEdgePatternWeightedRow markedRawEdgePatternApply
  rw [← Complex.ofReal_mul, Finset.sum_mul, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro c _
  let R : ℝ := ∏ j, δ j ^ (if (c.promotions j).isSome then 1 else 0) *
    γ j ^ (if c.store j then 1 else 0)
  have hR : 0 ≤ R := Finset.prod_nonneg (fun j _ =>
    mul_nonneg (pow_nonneg (hδ j) _) (pow_nonneg (hγ j) _))
  have hm := markedDirtyRawEdge_prime_mass_nonneg ν (fun _ => 1) hν
    (fun _ => by norm_num) hZ s c
  have hc : markedRawEdgeChoiceCharge (fun j => (δ j : ℂ)) (fun j => (γ j : ℂ)) hZ s c = (R : ℂ) :=
    markedRawEdgeChoiceCharge_ofReal δ γ hZ s c
  rw [mul_assoc, div_mul_cancel₀ _ hs]
  simp only [hc, markedRawEdgeChoiceFreshMass, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg hR, Real.norm_of_nonneg hm, Complex.ofReal_mul, markedRawEdgePatternNorm]
  rfl

theorem markedRawEdgePatternReverseEnergy_eq_apply
    {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (δ γ : J → ℝ)
    (hν : ∀ j p, 0 ≤ ν j p) (hδ : ∀ j, 0 ≤ δ j) (hγ : ∀ j, 0 ≤ γ j)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (A : MarkedRawEdgePatternKernel P pads B Z)
    (v₀ : ℝ) (f : MarkedRawState P (pads+1) B Z → ℂ)
    (s : MarkedRawState P (pads+1) B Z) :
    (markedRawEdgePatternReverseEnergy ν (fun j => (δ j : ℂ)) (fun j => (γ j : ℂ)) hZ A v₀ f s : ℂ) =
      (markedRawMemorySchurWeight v₀ s.2.2 : ℂ) *
        markedRawEdgePatternApply ν (fun j => (δ j : ℂ)) (fun j => (γ j : ℂ)) hZ
          (markedRawEdgePatternNorm A)
          (fun t => ((‖f t‖ ^ 2 / markedRawMemorySchurWeight v₀ t.2.2 : ℝ) : ℂ)) s := by
  classical
  unfold markedRawEdgePatternReverseEnergy markedRawEdgePatternApply
  simp only [Complex.ofReal_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  let R : ℝ := ∏ j, δ j ^ (if (c.promotions j).isSome then 1 else 0) *
    γ j ^ (if c.store j then 1 else 0)
  have hR : 0 ≤ R := Finset.prod_nonneg (fun j _ =>
    mul_nonneg (pow_nonneg (hδ j) _) (pow_nonneg (hγ j) _))
  have hm := markedDirtyRawEdge_prime_mass_nonneg ν (fun _ => 1) hν
    (fun _ => by norm_num) hZ s c
  have hc : markedRawEdgeChoiceCharge (fun j => (δ j : ℂ)) (fun j => (γ j : ℂ)) hZ s c = (R : ℂ) :=
    markedRawEdgeChoiceCharge_ofReal δ γ hZ s c
  simp only [hc, markedRawEdgeChoiceFreshMass, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg hR, Real.norm_of_nonneg hm, Complex.ofReal_mul, Complex.ofReal_div,
    markedRawEdgePatternNorm]
  dsimp only [markedRawEdgeTargetState]
  ring

theorem markedRawEdgePatternReverseEnergy_column
    {J : Type*} [Fintype J] [decJ : DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (δ γ : J → ℝ)
    (hν : ∀ j p, 0 ≤ ν j p) (hδ : ∀ j, 0 ≤ δ j) (hγ : ∀ j, 0 ≤ γ j)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (A : MarkedRawEdgePatternKernel P pads B Z)
    (hAl : ∀ p q z active target, MarkedRawMemorySymmetric (fun m => A p q (z,(active,m)) target))
    (hAr : ∀ p q source z active, MarkedRawMemorySymmetric (fun m => A p q source (z,(active,m))))
    {v₀ : ℝ} (hv₀ : 0 < v₀) (f : MarkedRawState P (pads+1) B Z → ℂ)
    (hf : ∀ z active, MarkedRawMemorySymmetric (fun m => f (z,(active,m)))) :
    (∑ s, markedRawStateMass ν s *
      markedRawEdgePatternReverseEnergy ν (fun j => (δ j : ℂ)) (fun j => (γ j : ℂ)) hZ A v₀ f s) =
      ∑ s, markedRawStateMass ν s * ‖f s‖ ^ 2 *
        markedRawEdgePatternWeightedRow ν (fun j => (γ j : ℂ)) (fun j => (δ j : ℂ))
          hZ (markedRawEdgePatternReverse A) v₀ s := by
  classical
  cases Subsingleton.elim decJ (Classical.decEq J)
  apply Complex.ofReal_injective
  have hl : ∀ p q z active target, MarkedRawMemorySymmetric
      (fun m => markedRawEdgePatternNorm A p q (z,(active,m)) target) := by
    intro p q z active target m σ
    exact congrArg (fun u : ℂ => (‖u‖ : ℂ)) (hAl p q z active target m σ)
  have hr : ∀ p q source z active, MarkedRawMemorySymmetric
      (fun m => markedRawEdgePatternNorm A p q source (z,(active,m))) := by
    intro p q source z active m σ
    exact congrArg (fun u : ℂ => (‖u‖ : ℂ)) (hAr p q source z active m σ)
  have ht := markedRawEdgePatternApply_transpose ν (fun j => (δ j : ℂ)) (fun j => (γ j : ℂ))
    hZ (markedRawEdgePatternNorm A) hl hr
    (fun s => ((‖f s‖ ^ 2 / markedRawMemorySchurWeight v₀ s.2.2 : ℝ) : ℂ))
    (fun s => (markedRawMemorySchurWeight v₀ s.2.2 : ℂ))
    (markedRawGhostEnergyReweight_symmetric v₀ f hf)
    (fun _ _ => markedRawMemorySchurWeight_symmetric v₀)
  calc
    _ = ∑ s, (markedRawStateMass ν s : ℂ) * (markedRawMemorySchurWeight v₀ s.2.2 : ℂ) *
        markedRawEdgePatternApply ν (fun j => (δ j : ℂ)) (fun j => (γ j : ℂ)) hZ
          (markedRawEdgePatternNorm A)
          (fun t => ((‖f t‖ ^ 2 / markedRawMemorySchurWeight v₀ t.2.2 : ℝ) : ℂ)) s := by
      simp only [Complex.ofReal_sum, Complex.ofReal_mul,
        markedRawEdgePatternReverseEnergy_eq_apply ν δ γ hν hδ hγ, mul_assoc]
    _ = _ := ht
    _ = _ := by
      simp only [Complex.ofReal_sum, Complex.ofReal_mul]
      apply Finset.sum_congr rfl
      intro s _
      have hrow := markedRawEdgePatternWeightedRow_mul_weight ν γ δ hν hγ hδ hZ
        (markedRawEdgePatternReverse A) hv₀ s
      rw [markedRawEdgePatternNorm_reverse, ← hrow, Complex.ofReal_div]
      have hw : (markedRawMemorySchurWeight v₀ s.2.2 : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr (markedRawMemorySchurWeight_pos hv₀ s.2.2).ne'
      field_simp [hw]

end
end ArtinMatthews
