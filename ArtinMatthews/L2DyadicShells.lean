module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Function.L2Space


set_option backward.privateInPublic true
@[expose] public section

/-! Literal dyadic height shells and L2 summation on their complete high-height region. -/
namespace ArtinMatthews
open MeasureTheory Set
open scoped ENNReal Topology
noncomputable section

variable {X : Type*} [MeasurableSpace X]

def dyadicL2Shell (H : X → ℝ) (T : ℝ) (n : ℕ) : Set X :=
  {x | T * (2 : ℝ) ^ n ≤ H x ∧ H x < T * (2 : ℝ) ^ (n + 1)}

theorem dyadicL2Shell_measurable (H : X → ℝ) (hH : Measurable H) (T : ℝ) (n : ℕ) :
    MeasurableSet (dyadicL2Shell H T n) :=
  (measurableSet_le measurable_const hH).inter (measurableSet_lt hH measurable_const)

omit [MeasurableSpace X] in
theorem dyadicL2Shell_union (H : X → ℝ) {T : ℝ} (hT : 0 < T) :
    (⋃ n : ℕ, dyadicL2Shell H T n) = {x | T ≤ H x} := by
  ext x
  constructor
  · intro hx
    obtain ⟨n, hn⟩ := mem_iUnion.mp hx
    exact (by nlinarith [one_le_pow₀ (show (1 : ℝ) ≤ 2 by norm_num) (n := n)] :
      T ≤ T * (2 : ℝ) ^ n).trans hn.1
  · intro hx
    change T ≤ H x at hx
    have hratio : 1 ≤ H x / T := (le_div_iff₀ hT).mpr (by simpa only [one_mul] using hx)
    obtain ⟨n, hlo, hhi⟩ := exists_nat_pow_near hratio (show (1 : ℝ) < 2 by norm_num)
    refine mem_iUnion.mpr ⟨n, ?_⟩
    constructor
    · exact (mul_comm T _).trans_le ((le_div_iff₀ hT).mp hlo)
    · exact ((div_lt_iff₀ hT).mp hhi).trans_eq (mul_comm _ T)

omit [MeasurableSpace X] in
theorem dyadicL2Shell_pairwise (H : X → ℝ) {T : ℝ} (hT : 0 < T) :
    Pairwise fun n m => Disjoint (dyadicL2Shell H T n) (dyadicL2Shell H T m) := by
  have hordered (n m : ℕ) (hnm : n < m) : Disjoint (dyadicL2Shell H T n) (dyadicL2Shell H T m) := by
    apply Set.disjoint_left.mpr
    intro x hn hm
    have hp : (2 : ℝ) ^ (n + 1) ≤ (2 : ℝ) ^ m :=
      pow_le_pow_right₀ (show (1 : ℝ) ≤ 2 by norm_num) hnm
    have ht := mul_le_mul_of_nonneg_left hp hT.le
    exact (not_lt_of_ge (ht.trans hm.1)) hn.2
  intro n m hnm
  rcases lt_or_gt_of_ne hnm with hlt | hgt
  · exact hordered n m hlt
  · exact (hordered m n hgt).symm

theorem memLp_high_of_summable_dyadicShells (μ : Measure X) (H : X → ℝ)
    {T : ℝ} (hT : 0 < T) (f : X → ℂ)
    (hlocal : ∀ n, MemLp f 2 (μ.restrict (dyadicL2Shell H T n)))
    (hsum : Summable (fun n => ∫ x in dyadicL2Shell H T n, ‖f x‖ ^ 2 ∂μ)) :
    MemLp f 2 (μ.restrict {x | T ≤ H x}) := by
  have hmeas : AEStronglyMeasurable f (μ.restrict (⋃ n, dyadicL2Shell H T n)) :=
    AEStronglyMeasurable.iUnion (fun n => (hlocal n).aestronglyMeasurable)
  rw [dyadicL2Shell_union H hT] at hmeas
  apply (memLp_two_iff_integrable_sq_norm hmeas).mpr
  have hi : ∀ n, IntegrableOn (fun x => ‖f x‖ ^ 2) (dyadicL2Shell H T n) μ := fun n =>
    (memLp_two_iff_integrable_sq_norm (hlocal n).aestronglyMeasurable).mp (hlocal n)
  have hnormsum : Summable (fun n => ∫ x in dyadicL2Shell H T n, ‖‖f x‖ ^ 2‖ ∂μ) := by
    have hn (x : X) : ‖‖f x‖ ^ 2‖ = ‖f x‖ ^ 2 := Real.norm_of_nonneg (sq_nonneg _)
    simpa only [hn] using hsum
  have h := integrableOn_iUnion_of_summable_integral_norm hi hnormsum
  rwa [dyadicL2Shell_union H hT] at h

end
end ArtinMatthews
