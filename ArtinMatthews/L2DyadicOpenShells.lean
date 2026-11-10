module

public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import ArtinMatthews.DyadicMassBootstrap
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Left-open dyadic shells match the actual strict high-cusp domain without
assuming that height level sets have measure zero. -/
namespace ArtinMatthews
open MeasureTheory Set
open scoped ENNReal Topology
noncomputable section

variable {X : Type*} [MeasurableSpace X]

def dyadicL2OpenShell (H : X → ℝ) (T : ℝ) (n : ℕ) : Set X :=
  {x | T * (2 : ℝ) ^ n < H x ∧ H x ≤ T * (2 : ℝ) ^ (n + 1)}

theorem dyadicL2OpenShell_measurable (H : X → ℝ) (hH : Measurable H) (T : ℝ) (n : ℕ) :
    MeasurableSet (dyadicL2OpenShell H T n) :=
  (measurableSet_lt measurable_const hH).inter (measurableSet_le hH measurable_const)

private theorem exists_nat_pow_left_open {x : ℝ} (hx : 1 < x) :
    ∃ n : ℕ, (2 : ℝ) ^ n < x ∧ x ≤ (2 : ℝ) ^ (n + 1) := by
  have he : ∃ m : ℕ, x ≤ (2 : ℝ) ^ m := by
    obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt x (by norm_num : (1 : ℝ) < 2)
    exact ⟨m, hm.le⟩
  let m := Nat.find he
  have hm : x ≤ (2 : ℝ) ^ m := Nat.find_spec he
  have hm0 : 0 < m := by
    by_contra h
    have hz : m = 0 := Nat.eq_zero_of_not_pos h
    rw [hz, pow_zero] at hm
    exact (not_le_of_gt hx) hm
  have hm1 : m - 1 + 1 = m := Nat.sub_add_cancel hm0
  refine ⟨m - 1, ?_, ?_⟩
  · exact lt_of_not_ge (Nat.find_min he (Nat.sub_lt hm0 (by norm_num)))
  · simpa only [hm1] using hm

omit [MeasurableSpace X] in
theorem dyadicL2OpenShell_union (H : X → ℝ) {T : ℝ} (hT : 0 < T) :
    (⋃ n : ℕ, dyadicL2OpenShell H T n) = {x | T < H x} := by
  ext x
  constructor
  · intro hx
    obtain ⟨n, hn⟩ := mem_iUnion.mp hx
    exact (by nlinarith [one_le_pow₀ (show (1 : ℝ) ≤ 2 by norm_num) (n := n)] :
      T ≤ T * (2 : ℝ) ^ n).trans_lt hn.1
  · intro hx
    change T < H x at hx
    have hratio : 1 < H x / T := (lt_div_iff₀ hT).mpr (by simpa only [one_mul] using hx)
    obtain ⟨n, hlo, hhi⟩ := exists_nat_pow_left_open hratio
    refine mem_iUnion.mpr ⟨n, ?_⟩
    constructor
    · exact (mul_comm T _).trans_lt ((lt_div_iff₀ hT).mp hlo)
    · exact ((div_le_iff₀ hT).mp hhi).trans_eq (mul_comm _ T)

omit [MeasurableSpace X] in
theorem dyadicL2OpenShell_pairwise (H : X → ℝ) {T : ℝ} (hT : 0 < T) :
    Pairwise fun n m => Disjoint (dyadicL2OpenShell H T n) (dyadicL2OpenShell H T m) := by
  have hordered (n m : ℕ) (hnm : n < m) : Disjoint (dyadicL2OpenShell H T n) (dyadicL2OpenShell H T m) := by
    apply Set.disjoint_left.mpr
    intro x hn hm
    have hp : (2 : ℝ) ^ (n + 1) ≤ (2 : ℝ) ^ m :=
      pow_le_pow_right₀ (show (1 : ℝ) ≤ 2 by norm_num) hnm
    have ht := mul_le_mul_of_nonneg_left hp hT.le
    exact (not_lt_of_ge (hn.2.trans ht)) hm.1
  intro n m hnm
  rcases lt_or_gt_of_ne hnm with hlt | hgt
  · exact hordered n m hlt
  · exact (hordered m n hgt).symm

theorem memLp_high_of_summable_dyadicOpenShells (μ : Measure X) (H : X → ℝ)
    {T : ℝ} (hT : 0 < T) (f : X → ℂ)
    (hlocal : ∀ n, MemLp f 2 (μ.restrict (dyadicL2OpenShell H T n)))
    (hsum : Summable (fun n => ∫ x in dyadicL2OpenShell H T n, ‖f x‖ ^ 2 ∂μ)) :
    MemLp f 2 (μ.restrict {x | T < H x}) := by
  have hmeas : AEStronglyMeasurable f (μ.restrict (⋃ n, dyadicL2OpenShell H T n)) :=
    AEStronglyMeasurable.iUnion (fun n => (hlocal n).aestronglyMeasurable)
  rw [dyadicL2OpenShell_union H hT] at hmeas
  apply (memLp_two_iff_integrable_sq_norm hmeas).mpr
  have hi : ∀ n, IntegrableOn (fun x => ‖f x‖ ^ 2) (dyadicL2OpenShell H T n) μ := fun n =>
    (memLp_two_iff_integrable_sq_norm (hlocal n).aestronglyMeasurable).mp (hlocal n)
  have hnormsum : Summable (fun n => ∫ x in dyadicL2OpenShell H T n, ‖‖f x‖ ^ 2‖ ∂μ) := by
    have hn (x : X) : ‖‖f x‖ ^ 2‖ = ‖f x‖ ^ 2 := Real.norm_of_nonneg (sq_nonneg _)
    simpa only [hn] using hsum
  have h := integrableOn_iUnion_of_summable_integral_norm hi hnormsum
  rwa [dyadicL2OpenShell_union H hT] at h

theorem memLp_high_of_dyadicOpen_recurrence (μ : Measure X) (H : X → ℝ)
    {T : ℝ} (hT : 0 < T) (f : X → ℂ)
    (hlocal : ∀ n, MemLp f 2 (μ.restrict (dyadicL2OpenShell H T n)))
    (δ D B C : ℝ) (hδ : 0 < δ) (hD : 0 ≤ D) (hC : 0 < C)
    (hbound : ∀ n, (∫ x in dyadicL2OpenShell H T n, ‖f x‖ ^ 2 ∂μ) ≤ C * 2 ^ (B * n))
    (hrec : ∀ n, (∫ x in dyadicL2OpenShell H T (n+1), ‖f x‖ ^ 2 ∂μ) ≤
      D * 2 ^ (-δ * (n+1 : ℕ)) *
        ((∫ x in dyadicL2OpenShell H T n, ‖f x‖ ^ 2 ∂μ) +
         (∫ x in dyadicL2OpenShell H T (n+1), ‖f x‖ ^ 2 ∂μ) +
         (∫ x in dyadicL2OpenShell H T (n+2), ‖f x‖ ^ 2 ∂μ))) :
    MemLp f 2 (μ.restrict {x | T < H x}) := by
  apply memLp_high_of_summable_dyadicOpenShells μ H hT f hlocal
  exact dyadic_mass_summable _ δ D B C (fun n => integral_nonneg fun x => sq_nonneg _) hδ hD hC hbound hrec

end
end ArtinMatthews
