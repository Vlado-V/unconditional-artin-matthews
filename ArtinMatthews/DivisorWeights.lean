module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Combinatorics.Matroid.Init
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.Tactic.NormNum.GCD


set_option backward.privateInPublic true
@[expose] public section

/-!
# Finite divisor weights

The arithmetic weight in Section 2 counts the distinct prime divisors from
each finite band and damps this count by powers of one half. These identities
and bounds are finite algebra; they assert no distribution of prime divisors.
-/

namespace ArtinMatthews

/-- The divisors of `u` belonging to the finite band `P`. -/
def activeDivisors (P : Finset ℕ) (u : ℕ) : Finset ℕ :=
  P.filter (fun p => p ∣ u)

/-- The number of distinct members of the band dividing `u`. -/
def bandCount (P : Finset ℕ) (u : ℕ) : ℕ :=
  (activeDivisors P u).card

/-- The unnormalized factor `k ρ^(k-1)` for `ρ = 1/2`.
Natural subtraction also handles `k = 0`, since its leading factor is zero. -/
noncomputable def halfDampedCount (k : ℕ) : ℝ :=
  (k : ℝ) * (1 / 2 : ℝ) ^ (k - 1)

/-- A single band's factor in the divisor weight, with normalizer `V`. -/
noncomputable def bandWeight (P : Finset ℕ) (V : ℝ) (u : ℕ) : ℝ :=
  halfDampedCount (bandCount P u) / V

/-- The actual reciprocal-prime normalizer used for a band in the paper. -/
noncomputable def bandReciprocalMass (P : Finset ℕ) : ℝ :=
  ∑ p ∈ P, 1 / (p : ℝ)

/-- The product of the factors in a finite array of bands. -/
noncomputable def divisorWeight {ι : Type*} (I : Finset ι) (P : ι → Finset ℕ)
    (V : ι → ℝ) (u : ℕ) : ℝ :=
  ∏ i ∈ I, bandWeight (P i) (V i) u

@[simp] theorem halfDampedCount_zero : halfDampedCount 0 = 0 := by
  norm_num [halfDampedCount]

@[simp] theorem halfDampedCount_one : halfDampedCount 1 = 1 := by
  norm_num [halfDampedCount]

@[simp] theorem halfDampedCount_two : halfDampedCount 2 = 1 := by
  norm_num [halfDampedCount]

theorem halfDampedCount_nonneg (k : ℕ) : 0 ≤ halfDampedCount k := by
  unfold halfDampedCount
  positivity

/-- The damped count is at most one, attained at counts one and two. -/
theorem halfDampedCount_le_one (k : ℕ) : halfDampedCount k ≤ 1 := by
  cases k with
  | zero => simp
  | succ n =>
    have hn : (n + 1 : ℝ) ≤ (2 : ℝ) ^ n := by
      exact_mod_cast Nat.succ_le_of_lt (Nat.lt_two_pow_self (n := n))
    simpa [halfDampedCount, one_div_pow, div_eq_mul_inv] using
      (div_le_one (by positivity : (0 : ℝ) < 2 ^ n)).mpr hn

theorem halfDampedCount_pos_iff (k : ℕ) : 0 < halfDampedCount k ↔ 0 < k := by
  cases k with
  | zero => simp
  | succ n =>
    constructor
    · intro _
      exact Nat.succ_pos _
    · intro _
      unfold halfDampedCount
      positivity

theorem bandWeight_nonneg (P : Finset ℕ) {V : ℝ} (hV : 0 ≤ V) (u : ℕ) :
    0 ≤ bandWeight P V u :=
  div_nonneg (halfDampedCount_nonneg _) hV

theorem bandWeight_le (P : Finset ℕ) {V : ℝ} (hV : 0 < V) (u : ℕ) :
    bandWeight P V u ≤ 1 / V :=
  div_le_div_of_nonneg_right (halfDampedCount_le_one _) hV.le

/-- A band has positive weight precisely when it supplies a divisor. -/
theorem bandWeight_pos_iff (P : Finset ℕ) {V : ℝ} (hV : 0 < V) (u : ℕ) :
    0 < bandWeight P V u ↔ ∃ p ∈ P, p ∣ u := by
  rw [bandWeight, div_pos_iff_of_pos_right hV, halfDampedCount_pos_iff,
    bandCount, Finset.card_pos, Finset.nonempty_iff_ne_empty]
  simp [activeDivisors, Finset.filter_eq_empty_iff]

/-- The selected-divisor sum is a counting sum, with no reciprocal `p` weight. -/
theorem bandWeight_eq_selected_sum (P : Finset ℕ) (V : ℝ) (u : ℕ) :
    bandWeight P V u = ∑ _p ∈ activeDivisors P u,
      (1 / 2 : ℝ) ^ (bandCount P u - 1) / V := by
  simp [bandWeight, halfDampedCount, bandCount, Finset.sum_const,
    nsmul_eq_mul, mul_div_assoc]

/-- Expansion of the array into one selected divisor from each band. -/
theorem divisorWeight_eq_selected_sums {ι : Type*} (I : Finset ι)
    (P : ι → Finset ℕ) (V : ι → ℝ) (u : ℕ) :
    divisorWeight I P V u = ∏ i ∈ I, ∑ _p ∈ activeDivisors (P i) u,
      (1 / 2 : ℝ) ^ (bandCount (P i) u - 1) / V i := by
  unfold divisorWeight
  exact Finset.prod_congr rfl (fun i _ => bandWeight_eq_selected_sum (P i) (V i) u)

/-- The selected-divisor expansion as one sum over all choices of one divisor
from each band. -/
theorem divisorWeight_eq_selected_tuple_sum {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (P : ι → Finset ℕ) (V : ι → ℝ) (u : ℕ) :
    divisorWeight I P V u =
      ∑ choices ∈ I.pi (fun i => activeDivisors (P i) u),
        ∏ i ∈ I.attach,
          (fun _p : ℕ => (1 / 2 : ℝ) ^ (bandCount (P i.1) u - 1) / V i.1)
            (choices i.1 i.2) := by
  rw [divisorWeight_eq_selected_sums]
  exact Finset.prod_sum I (fun i => activeDivisors (P i) u)
    (fun i _p => (1 / 2 : ℝ) ^ (bandCount (P i) u - 1) / V i)

/-- The common damping factor and the product of selected-divisor counts.
If a band is empty of divisors, both sides are zero. -/
theorem divisorWeight_eq_damping_mul_counts {ι : Type*} (I : Finset ι)
    (P : ι → Finset ℕ) (V : ι → ℝ) (u : ℕ) :
    divisorWeight I P V u =
      (1 / 2 : ℝ) ^ ((∑ i ∈ I, bandCount (P i) u) - I.card) *
        ∏ i ∈ I, (bandCount (P i) u : ℝ) / V i := by
  classical
  by_cases hc : ∀ i ∈ I, 0 < bandCount (P i) u
  · have hexp : (∑ i ∈ I, (bandCount (P i) u - 1)) =
        (∑ i ∈ I, bandCount (P i) u) - I.card := by
      simpa using (Finset.sum_tsub_distrib I
        (f := fun i => bandCount (P i) u) (g := fun _ => 1) (fun i hi => hc i hi))
    calc
      divisorWeight I P V u =
          ∏ i ∈ I, (1 / 2 : ℝ) ^ (bandCount (P i) u - 1) *
            ((bandCount (P i) u : ℝ) / V i) := by
        apply Finset.prod_congr rfl
        intro i _hi
        unfold bandWeight halfDampedCount
        ring
      _ = (1 / 2 : ℝ) ^ (∑ i ∈ I, (bandCount (P i) u - 1)) *
          ∏ i ∈ I, (bandCount (P i) u : ℝ) / V i := by
        rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
      _ = _ := by rw [hexp]
  · push Not at hc
    obtain ⟨i, hi, hci⟩ := hc
    have hzero : bandCount (P i) u = 0 := Nat.eq_zero_of_le_zero hci
    have hw : divisorWeight I P V u = 0 := by
      apply Finset.prod_eq_zero hi
      simp [bandWeight, hzero]
    have hprod : (∏ i ∈ I, (bandCount (P i) u : ℝ) / V i) = 0 := by
      apply Finset.prod_eq_zero hi
      simp [hzero]
    rw [hw, hprod, mul_zero]

theorem divisorWeight_nonneg {ι : Type*} (I : Finset ι)
    (P : ι → Finset ℕ) {V : ι → ℝ} (hV : ∀ i ∈ I, 0 ≤ V i) (u : ℕ) :
    0 ≤ divisorWeight I P V u :=
  Finset.prod_nonneg (fun i hi => bandWeight_nonneg (P i) (hV i hi) u)

theorem divisorWeight_le {ι : Type*} (I : Finset ι)
    (P : ι → Finset ℕ) {V : ι → ℝ} (hV : ∀ i ∈ I, 0 < V i) (u : ℕ) :
    divisorWeight I P V u ≤ ∏ i ∈ I, 1 / V i := by
  apply Finset.prod_le_prod₀
  · intro i hi
    exact bandWeight_nonneg (P i) (hV i hi).le u
  · intro i hi
    exact bandWeight_le (P i) (hV i hi) u

/-- Exact finite independent Bernoulli first marked moment. No bounds on the
parameters are needed for this algebraic identity. -/
theorem bernoulli_marked_sum {ι : Type*} [DecidableEq ι]
    (P : Finset ι) (r : ι → ℝ) (ρ : ℝ) :
    (∑ A ∈ P.powerset,
      (A.card : ℝ) * ρ ^ (A.card - 1) *
        (∏ i ∈ A, r i) * ∏ i ∈ P \ A, (1 - r i)) =
      ∑ i ∈ P, r i * ∏ j ∈ P.erase i, (1 - r j + ρ * r j) := by
  have hident :
      (fun x : ℝ => ∏ i ∈ P, (1 - r i + x * r i)) =
      (fun x : ℝ => ∑ A ∈ P.powerset,
        x ^ A.card * (∏ i ∈ A, r i) * ∏ i ∈ P \ A, (1 - r i)) := by
    funext x
    rw [show (fun i => 1 - r i + x * r i) =
        (fun i => x * r i + (1 - r i)) by ext i; ring]
    rw [Finset.prod_add]
    apply Finset.sum_congr rfl
    intro A _hA
    rw [Finset.prod_mul_distrib, Finset.prod_const]
  have hleft : HasDerivAt (fun x : ℝ => ∏ i ∈ P, (1 - r i + x * r i))
      (∑ i ∈ P, r i * ∏ j ∈ P.erase i, (1 - r j + ρ * r j)) ρ := by
    convert (HasDerivAt.fun_finsetProd (u := P) (fun i _ =>
      ((hasDerivAt_id ρ).mul_const (r i)).const_add (1 - r i))) using 1 <;>
      simp [mul_comm]
  have hright : HasDerivAt
      (fun x : ℝ => ∑ A ∈ P.powerset,
        x ^ A.card * (∏ i ∈ A, r i) * ∏ i ∈ P \ A, (1 - r i))
      (∑ A ∈ P.powerset,
        (A.card : ℝ) * ρ ^ (A.card - 1) *
          (∏ i ∈ A, r i) * ∏ i ∈ P \ A, (1 - r i)) ρ := by
    exact HasDerivAt.fun_sum (fun A _ =>
      ((hasDerivAt_pow A.card ρ).mul_const (∏ i ∈ A, r i)).mul_const
        (∏ i ∈ P \ A, (1 - r i)))
  rw [← hident] at hright
  exact hright.unique hleft

/-- Probability of the mask `A` in the independent finite Bernoulli model. -/
noncomputable def bernoulliMaskMass {ι : Type*} [DecidableEq ι]
    (P : Finset ι) (r : ι → ℝ) (A : Finset ι) : ℝ :=
  (∏ i ∈ A, r i) * ∏ i ∈ P \ A, (1 - r i)

theorem bernoulliMaskMass_sum {ι : Type*} [DecidableEq ι]
    (P : Finset ι) (r : ι → ℝ) :
    ∑ A ∈ P.powerset, bernoulliMaskMass P r A = 1 := by
  have h := Finset.prod_add r (fun i => 1 - r i) P
  simpa [bernoulliMaskMass] using h.symm

theorem bernoulliMaskMass_nonneg {ι : Type*} [DecidableEq ι]
    (P : Finset ι) (r : ι → ℝ)
    (hr : ∀ i ∈ P, 0 ≤ r i ∧ r i ≤ 1) {A : Finset ι} (hA : A ⊆ P) :
    0 ≤ bernoulliMaskMass P r A := by
  apply mul_nonneg
  · exact Finset.prod_nonneg (fun i hi => (hr i (hA hi)).1)
  · exact Finset.prod_nonneg (fun i hi => sub_nonneg.mpr (hr i (Finset.mem_sdiff.mp hi).1).2)

/-- The one-band expectation, including its normalization. -/
noncomputable def bernoulliBandMean {ι : Type*} [DecidableEq ι]
    (P : Finset ι) (r : ι → ℝ) (V : ℝ) : ℝ :=
  (∑ A ∈ P.powerset, halfDampedCount A.card * bernoulliMaskMass P r A) / V

/-- Exact one-band mean, in an unfactored form that also covers zero factors. -/
theorem bernoulliBandMean_eq {ι : Type*} [DecidableEq ι]
    (P : Finset ι) (r : ι → ℝ) (V : ℝ) :
    bernoulliBandMean P r V =
      (∑ i ∈ P, r i * ∏ j ∈ P.erase i, (1 - r j + (1 / 2 : ℝ) * r j)) / V := by
  unfold bernoulliBandMean halfDampedCount bernoulliMaskMass
  simp_rw [← mul_assoc]
  rw [bernoulli_marked_sum]

theorem bernoulliBandMean_nonneg {ι : Type*} [DecidableEq ι]
    (P : Finset ι) (r : ι → ℝ) (hr : ∀ i ∈ P, 0 ≤ r i ∧ r i ≤ 1)
    {V : ℝ} (hV : 0 ≤ V) : 0 ≤ bernoulliBandMean P r V := by
  apply div_nonneg _ hV
  apply Finset.sum_nonneg
  intro A hA
  exact mul_nonneg (halfDampedCount_nonneg _) (bernoulliMaskMass_nonneg P r hr
    (Finset.mem_powerset.mp hA))

theorem bernoulliBandMean_le {ι : Type*} [DecidableEq ι]
    (P : Finset ι) (r : ι → ℝ) (hr : ∀ i ∈ P, 0 ≤ r i ∧ r i ≤ 1)
    {V : ℝ} (hV : 0 < V) : bernoulliBandMean P r V ≤ 1 / V := by
  apply div_le_div_of_nonneg_right _ hV.le
  calc
    (∑ A ∈ P.powerset, halfDampedCount A.card * bernoulliMaskMass P r A) ≤
        ∑ A ∈ P.powerset, bernoulliMaskMass P r A := by
      apply Finset.sum_le_sum
      intro A hA
      exact mul_le_of_le_one_left
        (bernoulliMaskMass_nonneg P r hr (Finset.mem_powerset.mp hA))
        (halfDampedCount_le_one _)
    _ = 1 := bernoulliMaskMass_sum P r

/-- Factoring the full product out of a sum of products with one omitted factor. -/
theorem sum_mul_prod_erase_eq {ι : Type*} [DecidableEq ι]
    (P : Finset ι) (r f : ι → ℝ) (hf : ∀ i ∈ P, f i ≠ 0) :
    (∑ i ∈ P, r i * ∏ j ∈ P.erase i, f j) =
      (∏ j ∈ P, f j) * ∑ i ∈ P, r i / f i := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.mul_prod_erase P f hi]
  field_simp [hf i hi]

/-- The factored exact one-band mean in the independent Bernoulli model. -/
theorem bernoulliBandMean_factored {ι : Type*} [DecidableEq ι]
    (P : Finset ι) (r : ι → ℝ) (hr : ∀ i ∈ P, 0 ≤ r i ∧ r i ≤ 1) (V : ℝ) :
    bernoulliBandMean P r V =
      ((∏ i ∈ P, (1 - r i + (1 / 2 : ℝ) * r i)) / V) *
        ∑ i ∈ P, r i / (1 - r i + (1 / 2 : ℝ) * r i) := by
  rw [bernoulliBandMean_eq, sum_mul_prod_erase_eq]
  · ring
  · intro i hi
    have := (hr i hi).2
    linarith

/-- The prime-band specialization of the exact expectation formula (2.2),
with an arbitrary normalizer. -/
theorem bernoulliPrimeBandMean_eq (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (V : ℝ) :
    bernoulliBandMean P (fun p => 1 / (p : ℝ)) V =
      ((∏ p ∈ P, (1 - (1 / 2 : ℝ) / (p : ℝ))) / V) *
        ∑ p ∈ P, 1 / ((p : ℝ) - (1 / 2 : ℝ)) := by
  have hr : ∀ p ∈ P, 0 ≤ 1 / (p : ℝ) ∧ 1 / (p : ℝ) ≤ 1 := by
    intro p hp
    have hpos : (0 : ℝ) < p := by exact_mod_cast (hP p hp).pos
    have hone : (1 : ℝ) ≤ p := by exact_mod_cast (hP p hp).one_lt.le
    exact ⟨by positivity, (div_le_one hpos).mpr hone⟩
  rw [bernoulliBandMean_factored P _ hr]
  congr 1
  · congr 1
    apply Finset.prod_congr rfl
    intro p _hp
    ring
  · apply Finset.sum_congr rfl
    intro p hp
    have htwo : (2 : ℝ) ≤ p := by exact_mod_cast (hP p hp).two_le
    have hp0 : (p : ℝ) ≠ 0 := by linarith
    have hhalf : (p : ℝ) - (1 / 2 : ℝ) ≠ 0 := by linarith
    field_simp [hp0, hhalf]
    ring

/-- Formula (2.2) for one band with the paper's reciprocal-prime normalizer. -/
theorem bernoulliPrimeBandMean_eq_reciprocalMass (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) :
    bernoulliBandMean P (fun p => 1 / (p : ℝ)) (bandReciprocalMass P) =
      ((∏ p ∈ P, (1 - (1 / 2 : ℝ) / (p : ℝ))) / bandReciprocalMass P) *
        ∑ p ∈ P, 1 / ((p : ℝ) - (1 / 2 : ℝ)) :=
  bernoulliPrimeBandMean_eq P hP _

/-- Joint expectation over an independent choice of a divisor mask in every band. -/
noncomputable def bernoulliArrayMean {ι α : Type*} [Fintype ι]
    [DecidableEq ι] [DecidableEq α] (P : ι → Finset α)
    (r : ι → α → ℝ) (V : ι → ℝ) : ℝ :=
  ∑ A ∈ Fintype.piFinset (fun i => (P i).powerset),
    ∏ i, halfDampedCount (A i).card * bernoulliMaskMass (P i) (r i) (A i) / V i

/-- Independence between bands gives the product of the one-band means. -/
theorem bernoulliArrayMean_eq_prod {ι α : Type*} [Fintype ι]
    [DecidableEq ι] [DecidableEq α] (P : ι → Finset α)
    (r : ι → α → ℝ) (V : ι → ℝ) :
    bernoulliArrayMean P r V = ∏ i, bernoulliBandMean (P i) (r i) (V i) := by
  unfold bernoulliArrayMean bernoulliBandMean
  simp_rw [Finset.sum_div]
  exact (Finset.prod_univ_sum (fun i : ι => (P i).powerset)
    (fun i A => halfDampedCount A.card * bernoulliMaskMass (P i) (r i) A / V i)).symm

/-- The full finite-band expectation formula (2.2) at `ρ = 1/2`. -/
theorem bernoulliPrimeArrayMean_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : ι → Finset ℕ) (hP : ∀ i p, p ∈ P i → p.Prime) :
    bernoulliArrayMean P (fun _ p => 1 / (p : ℝ))
        (fun i => bandReciprocalMass (P i)) =
      ∏ i, (((∏ p ∈ P i, (1 - (1 / 2 : ℝ) / (p : ℝ))) /
        bandReciprocalMass (P i)) * ∑ p ∈ P i, 1 / ((p : ℝ) - (1 / 2 : ℝ))) := by
  rw [bernoulliArrayMean_eq_prod]
  exact Finset.prod_congr rfl (fun i _ =>
    bernoulliPrimeBandMean_eq_reciprocalMass (P i) (hP i))

end ArtinMatthews
