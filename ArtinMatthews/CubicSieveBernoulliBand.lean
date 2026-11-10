module

public import ArtinMatthews.DivisorWeights
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Measurability.Init
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


set_option backward.privateInPublic true
@[expose] public section

/-! Finite perturbation and derivative estimates for the actual Bernoulli band mean. -/

set_option relaxedAutoImplicit false

noncomputable section
namespace ArtinMatthews

open scoped BigOperators

theorem bernoulliUnitProduct_bounds {ι : Type*} (P : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ P, 0 ≤ f i ∧ f i ≤ 1) :
    0 ≤ ∏ i ∈ P, f i ∧ (∏ i ∈ P, f i) ≤ 1 :=
  ⟨Finset.prod_nonneg (fun i hi => (hf i hi).1),
    Finset.prod_le_one₀ (fun i hi => (hf i hi).1) (fun i hi => (hf i hi).2)⟩

theorem bernoulliUnitProduct_abs_sub_le {ι : Type*} [DecidableEq ι]
    (P : Finset ι) (f g : ι → ℝ)
    (hf : ∀ i ∈ P, 0 ≤ f i ∧ f i ≤ 1)
    (hg : ∀ i ∈ P, 0 ≤ g i ∧ g i ≤ 1) :
    |(∏ i ∈ P, f i) - ∏ i ∈ P, g i| ≤ ∑ i ∈ P, |f i - g i| := by
  induction P using Finset.induction_on with
  | empty => simp
  | @insert a P ha ih =>
    have hfa := hf a (Finset.mem_insert_self _ _)
    have hga := hg a (Finset.mem_insert_self _ _)
    have hfP := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hgP := fun i hi => hg i (Finset.mem_insert_of_mem hi)
    have hp := bernoulliUnitProduct_bounds P f hfP
    have hs : 0 ≤ ∑ i ∈ P, |f i - g i| :=
      Finset.sum_nonneg (fun _ _ => abs_nonneg _)
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha]
    calc
      |f a * (∏ i ∈ P, f i) - g a * ∏ i ∈ P, g i| =
          |(f a - g a) * (∏ i ∈ P, f i) +
            g a * ((∏ i ∈ P, f i) - ∏ i ∈ P, g i)| := by congr 1; ring
      _ ≤ |(f a - g a) * (∏ i ∈ P, f i)| +
          |g a * ((∏ i ∈ P, f i) - ∏ i ∈ P, g i)| := abs_add_le _ _
      _ = |f a - g a| * (∏ i ∈ P, f i) +
          g a * |(∏ i ∈ P, f i) - ∏ i ∈ P, g i| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hp.1, abs_of_nonneg hga.1]
      _ ≤ |f a - g a| + ∑ i ∈ P, |f i - g i| := by
        apply add_le_add (mul_le_of_le_one_right (abs_nonneg _) hp.2)
        exact (mul_le_mul_of_nonneg_left (ih hfP hgP) hga.1).trans
          (mul_le_of_le_one_left hs hga.2)

theorem bernoulliBandMean_eq_half {ι : Type*} [DecidableEq ι]
    (P : Finset ι) (r : ι → ℝ) (V : ℝ) :
    bernoulliBandMean P r V =
      (∑ i ∈ P, r i * ∏ j ∈ P.erase i, (1 - r j / 2)) / V := by
  rw [bernoulliBandMean_eq]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  ring

theorem bernoulliDamping_bounds {ι : Type*} (P : Finset ι) (r : ι → ℝ)
    (hr : ∀ i ∈ P, 0 ≤ r i ∧ r i ≤ 1) :
    ∀ i ∈ P, 0 ≤ 1 - r i / 2 ∧ 1 - r i / 2 ≤ 1 := by
  intro i hi
  obtain ⟨hlo, hhi⟩ := hr i hi
  constructor <;> linarith

theorem bernoulliBandMean_le_mass_div {ι : Type*} [DecidableEq ι]
    (P : Finset ι) (r : ι → ℝ)
    (hr : ∀ i ∈ P, 0 ≤ r i ∧ r i ≤ 1) {V : ℝ} (hV : 0 < V) :
    bernoulliBandMean P r V ≤ (∑ i ∈ P, r i) / V := by
  rw [bernoulliBandMean_eq_half]
  apply div_le_div_of_nonneg_right _ hV.le
  apply Finset.sum_le_sum
  intro i hi
  have hp := bernoulliUnitProduct_bounds (P.erase i) (fun j => 1 - r j / 2)
    (fun j hj => bernoulliDamping_bounds P r hr j (Finset.mem_of_mem_erase hj))
  exact mul_le_of_le_one_right (hr i hi).1 hp.2

theorem bernoulliBandMean_unitInterval {ι : Type*} [DecidableEq ι]
    (P : Finset ι) (r : ι → ℝ)
    (hr : ∀ i ∈ P, 0 ≤ r i ∧ r i ≤ 1) {V : ℝ} (hV : 0 < V)
    (hmass : ∑ i ∈ P, r i ≤ V) :
    0 ≤ bernoulliBandMean P r V ∧ bernoulliBandMean P r V ≤ 1 := by
  refine ⟨bernoulliBandMean_nonneg P r hr hV.le, ?_⟩
  exact (bernoulliBandMean_le_mass_div P r hr hV).trans ((div_le_one hV).mpr hmass)

theorem bernoulliDampingProduct_abs_sub_le {ι : Type*} [DecidableEq ι]
    (P : Finset ι) (r s : ι → ℝ)
    (hr : ∀ i ∈ P, 0 ≤ r i ∧ r i ≤ 1)
    (hs : ∀ i ∈ P, 0 ≤ s i ∧ s i ≤ 1) :
    |(∏ i ∈ P, (1 - r i / 2)) - ∏ i ∈ P, (1 - s i / 2)| ≤
      (∑ i ∈ P, |r i - s i|) / 2 := by
  have h := bernoulliUnitProduct_abs_sub_le P (fun i => 1 - r i / 2)
    (fun i => 1 - s i / 2) (bernoulliDamping_bounds P r hr)
    (bernoulliDamping_bounds P s hs)
  convert h using 1
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  rw [show (1 - r i / 2) - (1 - s i / 2) = -(r i - s i) / 2 by ring]
  rw [abs_div, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2)]

theorem bernoulliBandMean_abs_sub_le {ι : Type*} [DecidableEq ι]
    (P : Finset ι) (r s : ι → ℝ)
    (hr : ∀ i ∈ P, 0 ≤ r i ∧ r i ≤ 1)
    (hs : ∀ i ∈ P, 0 ≤ s i ∧ s i ≤ 1) {V : ℝ} (hV : 0 < V)
    (hsmass : ∑ i ∈ P, s i ≤ V) :
    |bernoulliBandMean P r V - bernoulliBandMean P s V| ≤
      (1 / V + 1 / 2) * ∑ i ∈ P, |r i - s i| := by
  let D : ℝ := ∑ i ∈ P, |r i - s i|
  have hD : 0 ≤ D := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hterm (i : ι) (hi : i ∈ P) :
      |r i * (∏ j ∈ P.erase i, (1 - r j / 2)) -
        s i * ∏ j ∈ P.erase i, (1 - s j / 2)| ≤ |r i - s i| + s i * (D / 2) := by
    have hp := bernoulliUnitProduct_bounds (P.erase i) (fun j => 1 - r j / 2)
      (fun j hj => bernoulliDamping_bounds P r hr j (Finset.mem_of_mem_erase hj))
    have hdiff := bernoulliDampingProduct_abs_sub_le (P.erase i) r s
      (fun j hj => hr j (Finset.mem_of_mem_erase hj))
      (fun j hj => hs j (Finset.mem_of_mem_erase hj))
    have hsub : (∑ j ∈ P.erase i, |r j - s j|) ≤ D :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
        (fun _ _ _ => abs_nonneg _)
    calc
      _ = |(r i - s i) * (∏ j ∈ P.erase i, (1 - r j / 2)) +
          s i * ((∏ j ∈ P.erase i, (1 - r j / 2)) -
            ∏ j ∈ P.erase i, (1 - s j / 2))| := by congr 1; ring
      _ ≤ |(r i - s i) * (∏ j ∈ P.erase i, (1 - r j / 2))| +
          |s i * ((∏ j ∈ P.erase i, (1 - r j / 2)) -
            ∏ j ∈ P.erase i, (1 - s j / 2))| := abs_add_le _ _
      _ = |r i - s i| * (∏ j ∈ P.erase i, (1 - r j / 2)) +
          s i * |(∏ j ∈ P.erase i, (1 - r j / 2)) -
            ∏ j ∈ P.erase i, (1 - s j / 2)| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hp.1, abs_of_nonneg (hs i hi).1]
      _ ≤ |r i - s i| + s i * (D / 2) := by
        exact add_le_add (mul_le_of_le_one_right (abs_nonneg _) hp.2)
          (mul_le_mul_of_nonneg_left (hdiff.trans (div_le_div_of_nonneg_right hsub
            (by norm_num))) (hs i hi).1)
  rw [bernoulliBandMean_eq_half, bernoulliBandMean_eq_half, ← sub_div,
    abs_div, abs_of_pos hV]
  apply (div_le_iff₀ hV).mpr
  calc
    _ = |∑ i ∈ P, (r i * (∏ j ∈ P.erase i, (1 - r j / 2)) -
        s i * ∏ j ∈ P.erase i, (1 - s j / 2))| := by rw [Finset.sum_sub_distrib]
    _ ≤ ∑ i ∈ P, |r i * (∏ j ∈ P.erase i, (1 - r j / 2)) -
        s i * ∏ j ∈ P.erase i, (1 - s j / 2)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ P, (|r i - s i| + s i * (D / 2)) := Finset.sum_le_sum hterm
    _ = D + (∑ i ∈ P, s i) * (D / 2) := by rw [Finset.sum_add_distrib, ← Finset.sum_mul]
    _ ≤ D + V * (D / 2) :=
      add_le_add le_rfl
        (mul_le_mul_of_nonneg_right hsmass (div_nonneg hD (by norm_num)))
    _ = (1 / V + 1 / 2) * (∑ i ∈ P, |r i - s i|) * V := by
      dsimp [D]
      field_simp

def bernoulliProductTangent {ι : Type*} [DecidableEq ι]
    (P : Finset ι) (f v : ι → ℝ) : ℝ :=
  ∑ i ∈ P, (∏ j ∈ P.erase i, f j) * v i

theorem bernoulliUnitProduct_tangent_abs_le {ι : Type*} [DecidableEq ι]
    (P : Finset ι) (f v : ι → ℝ)
    (hf : ∀ i ∈ P, 0 ≤ f i ∧ f i ≤ 1) :
    |bernoulliProductTangent P f v| ≤ ∑ i ∈ P, |v i| := by
  unfold bernoulliProductTangent
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum ?_)
  intro i _
  have hp := bernoulliUnitProduct_bounds (P.erase i) f
    (fun j hj => hf j (Finset.mem_of_mem_erase hj))
  rw [abs_mul, abs_of_nonneg hp.1]
  exact mul_le_of_le_one_left (abs_nonneg _) hp.2

def bernoulliBandMeanTangent {ι : Type*} [DecidableEq ι]
    (P : Finset ι) (r v : ι → ℝ) (V : ℝ) : ℝ :=
  (∑ i ∈ P, (v i * (∏ j ∈ P.erase i, (1 - r j / 2)) +
    r i * bernoulliProductTangent (P.erase i) (fun j => 1 - r j / 2)
      (fun j => -v j / 2))) / V

theorem bernoulliBandMean_hasDerivAt {ι : Type*} [DecidableEq ι]
    (P : Finset ι) (r : ι → ℝ → ℝ) (v : ι → ℝ) (V x : ℝ)
    (hv : ∀ i ∈ P, HasDerivAt (r i) (v i) x) :
    HasDerivAt (fun t => bernoulliBandMean P (fun i => r i t) V)
      (bernoulliBandMeanTangent P (fun i => r i x) v V) x := by
  have hprod (i : ι) :
      HasDerivAt (fun t => ∏ j ∈ P.erase i, (1 - r j t / 2))
        (bernoulliProductTangent (P.erase i) (fun j => 1 - r j x / 2)
          (fun j => -v j / 2)) x := by
    unfold bernoulliProductTangent
    simpa only [smul_eq_mul, neg_div] using HasDerivAt.fun_finsetProd
      (fun j hj => ((hv j (Finset.mem_of_mem_erase hj)).div_const 2).const_sub 1)
  have hsum := HasDerivAt.fun_sum (u := P) (fun i hi => (hv i hi).mul (hprod i))
  have hmean := hsum.div_const V
  convert hmean using 1
  · funext t
    exact bernoulliBandMean_eq_half P (fun i => r i t) V
  · simp only [bernoulliBandMeanTangent]

theorem bernoulliBandMeanTangent_abs_le {ι : Type*} [DecidableEq ι]
    (P : Finset ι) (r v : ι → ℝ)
    (hr : ∀ i ∈ P, 0 ≤ r i ∧ r i ≤ 1) {V : ℝ} (hV : 0 < V)
    (hmass : ∑ i ∈ P, r i ≤ V) :
    |bernoulliBandMeanTangent P r v V| ≤
      (1 / V + 1 / 2) * ∑ i ∈ P, |v i| := by
  let D : ℝ := ∑ i ∈ P, |v i|
  have hD : 0 ≤ D := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hterm (i : ι) (hi : i ∈ P) :
      |v i * (∏ j ∈ P.erase i, (1 - r j / 2)) +
        r i * bernoulliProductTangent (P.erase i) (fun j => 1 - r j / 2)
          (fun j => -v j / 2)| ≤ |v i| + r i * (D / 2) := by
    have hp := bernoulliUnitProduct_bounds (P.erase i) (fun j => 1 - r j / 2)
      (fun j hj => bernoulliDamping_bounds P r hr j (Finset.mem_of_mem_erase hj))
    have ht := bernoulliUnitProduct_tangent_abs_le (P.erase i)
      (fun j => 1 - r j / 2) (fun j => -v j / 2)
      (fun j hj => bernoulliDamping_bounds P r hr j (Finset.mem_of_mem_erase hj))
    have hsum : (∑ j ∈ P.erase i, |-v j / 2|) ≤ D / 2 := by
      simp only [abs_div, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      rw [← Finset.sum_div]
      exact div_le_div_of_nonneg_right
        (Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
          (fun _ _ _ => abs_nonneg _)) (by norm_num)
    calc
      _ ≤ |v i * (∏ j ∈ P.erase i, (1 - r j / 2))| +
          |r i * bernoulliProductTangent (P.erase i) (fun j => 1 - r j / 2)
            (fun j => -v j / 2)| := abs_add_le _ _
      _ = |v i| * (∏ j ∈ P.erase i, (1 - r j / 2)) +
          r i * |bernoulliProductTangent (P.erase i) (fun j => 1 - r j / 2)
            (fun j => -v j / 2)| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hp.1, abs_of_nonneg (hr i hi).1]
      _ ≤ |v i| + r i * (D / 2) :=
        add_le_add (mul_le_of_le_one_right (abs_nonneg _) hp.2)
          (mul_le_mul_of_nonneg_left (ht.trans hsum) (hr i hi).1)
  unfold bernoulliBandMeanTangent
  rw [abs_div, abs_of_pos hV]
  apply (div_le_iff₀ hV).mpr
  calc
    _ ≤ ∑ i ∈ P, |v i * (∏ j ∈ P.erase i, (1 - r j / 2)) +
        r i * bernoulliProductTangent (P.erase i) (fun j => 1 - r j / 2)
          (fun j => -v j / 2)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ P, (|v i| + r i * (D / 2)) := Finset.sum_le_sum hterm
    _ = D + (∑ i ∈ P, r i) * (D / 2) := by rw [Finset.sum_add_distrib, ← Finset.sum_mul]
    _ ≤ D + V * (D / 2) :=
      add_le_add le_rfl
        (mul_le_mul_of_nonneg_right hmass (div_nonneg hD (by norm_num)))
    _ = (1 / V + 1 / 2) * (∑ i ∈ P, |v i|) * V := by
      dsimp [D]
      field_simp

theorem bernoulliBandMean_deriv_abs_le {ι : Type*} [DecidableEq ι]
    (P : Finset ι) (r : ι → ℝ → ℝ) (v : ι → ℝ) {V x : ℝ}
    (hv : ∀ i ∈ P, HasDerivAt (r i) (v i) x)
    (hr : ∀ i ∈ P, 0 ≤ r i x ∧ r i x ≤ 1) (hV : 0 < V)
    (hmass : ∑ i ∈ P, r i x ≤ V) :
    |deriv (fun t => bernoulliBandMean P (fun i => r i t) V) x| ≤
      (1 / V + 1 / 2) * ∑ i ∈ P, |v i| := by
  rw [(bernoulliBandMean_hasDerivAt P r v V x hv).deriv]
  exact bernoulliBandMeanTangent_abs_le P (fun i => r i x) v hr hV hmass

end ArtinMatthews
