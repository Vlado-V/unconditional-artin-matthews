module

public import ArtinMatthews.CubicSieveBernoulliBand


set_option backward.privateInPublic true
@[expose] public section

/-! Reciprocal-prime and finite-array forms of the Bernoulli mean estimates. -/

set_option relaxedAutoImplicit false

noncomputable section
namespace ArtinMatthews

open scoped BigOperators

theorem bernoulliPrimeBand_probability_bounds (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (r : ℕ → ℝ)
    (hr : ∀ p ∈ P, 0 ≤ r p ∧ r p ≤ 1 / (p : ℝ)) :
    ∀ p ∈ P, 0 ≤ r p ∧ r p ≤ 1 := by
  intro p hp
  have hpos : (0 : ℝ) < p := by exact_mod_cast (hP p hp).pos
  have hone : (1 : ℝ) ≤ p := by exact_mod_cast (hP p hp).one_le
  exact ⟨(hr p hp).1, (hr p hp).2.trans ((div_le_one hpos).mpr hone)⟩

theorem bernoulliPrimeBand_mass_le (P : Finset ℕ) (r : ℕ → ℝ)
    (hr : ∀ p ∈ P, r p ≤ 1 / (p : ℝ)) :
    (∑ p ∈ P, r p) ≤ bandReciprocalMass P :=
  Finset.sum_le_sum hr

theorem bernoulliPrimeBandMean_unitInterval (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (r : ℕ → ℝ)
    (hr : ∀ p ∈ P, 0 ≤ r p ∧ r p ≤ 1 / (p : ℝ))
    (hV : 0 < bandReciprocalMass P) :
    0 ≤ bernoulliBandMean P r (bandReciprocalMass P) ∧
      bernoulliBandMean P r (bandReciprocalMass P) ≤ 1 :=
  bernoulliBandMean_unitInterval P r (bernoulliPrimeBand_probability_bounds P hP r hr)
    hV (bernoulliPrimeBand_mass_le P r (fun p hp => (hr p hp).2))

theorem bernoulliPrimeBandMean_abs_sub_le (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (r s : ℕ → ℝ)
    (hr : ∀ p ∈ P, 0 ≤ r p ∧ r p ≤ 1 / (p : ℝ))
    (hs : ∀ p ∈ P, 0 ≤ s p ∧ s p ≤ 1 / (p : ℝ))
    (hV : 0 < bandReciprocalMass P) :
    |bernoulliBandMean P r (bandReciprocalMass P) -
        bernoulliBandMean P s (bandReciprocalMass P)| ≤
      (1 / bandReciprocalMass P + 1 / 2) * ∑ p ∈ P, |r p - s p| :=
  bernoulliBandMean_abs_sub_le P r s (bernoulliPrimeBand_probability_bounds P hP r hr)
    (bernoulliPrimeBand_probability_bounds P hP s hs) hV
    (bernoulliPrimeBand_mass_le P s (fun p hp => (hs p hp).2))

theorem bernoulliPrimeBandMean_deriv_abs_le (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (r : ℕ → ℝ → ℝ) (v : ℕ → ℝ) {x : ℝ}
    (hv : ∀ p ∈ P, HasDerivAt (r p) (v p) x)
    (hr : ∀ p ∈ P, 0 ≤ r p x ∧ r p x ≤ 1 / (p : ℝ))
    (hV : 0 < bandReciprocalMass P) :
    |deriv (fun t => bernoulliBandMean P (fun p => r p t) (bandReciprocalMass P)) x| ≤
      (1 / bandReciprocalMass P + 1 / 2) * ∑ p ∈ P, |v p| :=
  bernoulliBandMean_deriv_abs_le P r v hv
    (bernoulliPrimeBand_probability_bounds P hP (fun p => r p x) hr) hV
    (bernoulliPrimeBand_mass_le P (fun p => r p x) (fun p hp => (hr p hp).2))

theorem bernoulliBandMean_prod_abs_sub_le {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    (I : Finset ι) (P : ι → Finset α) (r s : ι → α → ℝ) (V : ι → ℝ)
    {v : ℝ} (hv : 0 < v) (hV : ∀ i ∈ I, v ≤ V i)
    (hr : ∀ i ∈ I, ∀ p ∈ P i, 0 ≤ r i p ∧ r i p ≤ 1)
    (hs : ∀ i ∈ I, ∀ p ∈ P i, 0 ≤ s i p ∧ s i p ≤ 1)
    (hrmass : ∀ i ∈ I, (∑ p ∈ P i, r i p) ≤ V i)
    (hsmass : ∀ i ∈ I, (∑ p ∈ P i, s i p) ≤ V i) :
    |(∏ i ∈ I, bernoulliBandMean (P i) (r i) (V i)) -
        ∏ i ∈ I, bernoulliBandMean (P i) (s i) (V i)| ≤
      (1 / v + 1 / 2) * ∑ i ∈ I, ∑ p ∈ P i, |r i p - s i p| := by
  have hrunit := fun i hi => bernoulliBandMean_unitInterval (P i) (r i) (hr i hi)
    (hv.trans_le (hV i hi)) (hrmass i hi)
  have hsunit := fun i hi => bernoulliBandMean_unitInterval (P i) (s i) (hs i hi)
    (hv.trans_le (hV i hi)) (hsmass i hi)
  calc
    _ ≤ ∑ i ∈ I, |bernoulliBandMean (P i) (r i) (V i) -
        bernoulliBandMean (P i) (s i) (V i)| :=
      bernoulliUnitProduct_abs_sub_le I _ _ hrunit hsunit
    _ ≤ ∑ i ∈ I, (1 / v + 1 / 2) * ∑ p ∈ P i, |r i p - s i p| := by
      apply Finset.sum_le_sum
      intro i hi
      exact (bernoulliBandMean_abs_sub_le (P i) (r i) (s i) (hr i hi) (hs i hi)
        (hv.trans_le (hV i hi)) (hsmass i hi)).trans
        (mul_le_mul_of_nonneg_right
          (add_le_add (one_div_le_one_div_of_le hv (hV i hi)) le_rfl)
          (Finset.sum_nonneg (fun _ _ => abs_nonneg _)))
    _ = _ := (Finset.mul_sum _ _ _).symm

theorem bernoulliBandMean_prod_deriv_abs_le {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    (I : Finset ι) (P : ι → Finset α) (r : ι → α → ℝ → ℝ)
    (d : ι → α → ℝ) (V : ι → ℝ) {v x : ℝ}
    (hv : 0 < v) (hV : ∀ i ∈ I, v ≤ V i)
    (hd : ∀ i ∈ I, ∀ p ∈ P i, HasDerivAt (r i p) (d i p) x)
    (hr : ∀ i ∈ I, ∀ p ∈ P i, 0 ≤ r i p x ∧ r i p x ≤ 1)
    (hrmass : ∀ i ∈ I, (∑ p ∈ P i, r i p x) ≤ V i) :
    |deriv (fun t => ∏ i ∈ I, bernoulliBandMean (P i) (fun p => r i p t) (V i)) x| ≤
      (1 / v + 1 / 2) * ∑ i ∈ I, ∑ p ∈ P i, |d i p| := by
  let m : ι → ℝ := fun i => bernoulliBandMean (P i) (fun p => r i p x) (V i)
  let a : ι → ℝ := fun i =>
    bernoulliBandMeanTangent (P i) (fun p => r i p x) (d i) (V i)
  have hmean (i : ι) (hi : i ∈ I) :=
    bernoulliBandMean_hasDerivAt (P i) (r i) (d i) (V i) x (hd i hi)
  have hprod : HasDerivAt
      (fun t => ∏ i ∈ I, bernoulliBandMean (P i) (fun p => r i p t) (V i))
      (bernoulliProductTangent I m a) x := by
    simpa only [bernoulliProductTangent, smul_eq_mul, m, a] using
      HasDerivAt.fun_finsetProd hmean
  rw [hprod.deriv]
  calc
    _ ≤ ∑ i ∈ I, |a i| := bernoulliUnitProduct_tangent_abs_le I m a (fun i hi =>
      bernoulliBandMean_unitInterval (P i) (fun p => r i p x) (hr i hi)
        (hv.trans_le (hV i hi)) (hrmass i hi))
    _ ≤ ∑ i ∈ I, (1 / v + 1 / 2) * ∑ p ∈ P i, |d i p| := by
      apply Finset.sum_le_sum
      intro i hi
      exact (bernoulliBandMeanTangent_abs_le (P i) (fun p => r i p x) (d i)
        (hr i hi) (hv.trans_le (hV i hi)) (hrmass i hi)).trans
        (mul_le_mul_of_nonneg_right
          (add_le_add (one_div_le_one_div_of_le hv (hV i hi)) le_rfl)
          (Finset.sum_nonneg (fun _ _ => abs_nonneg _)))
    _ = _ := (Finset.mul_sum _ _ _).symm

theorem bernoulliPrimeBandMean_prod_abs_sub_le {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (P : ι → Finset ℕ) (r s : ι → ℕ → ℝ)
    (hP : ∀ i ∈ I, ∀ p ∈ P i, p.Prime) {v : ℝ} (hv : 0 < v)
    (hV : ∀ i ∈ I, v ≤ bandReciprocalMass (P i))
    (hr : ∀ i ∈ I, ∀ p ∈ P i, 0 ≤ r i p ∧ r i p ≤ 1 / (p : ℝ))
    (hs : ∀ i ∈ I, ∀ p ∈ P i, 0 ≤ s i p ∧ s i p ≤ 1 / (p : ℝ)) :
    |(∏ i ∈ I, bernoulliBandMean (P i) (r i) (bandReciprocalMass (P i))) -
        ∏ i ∈ I, bernoulliBandMean (P i) (s i) (bandReciprocalMass (P i))| ≤
      (1 / v + 1 / 2) * ∑ i ∈ I, ∑ p ∈ P i, |r i p - s i p| :=
  bernoulliBandMean_prod_abs_sub_le I P r s (fun i => bandReciprocalMass (P i)) hv hV
    (fun i hi => bernoulliPrimeBand_probability_bounds (P i) (hP i hi) (r i) (hr i hi))
    (fun i hi => bernoulliPrimeBand_probability_bounds (P i) (hP i hi) (s i) (hs i hi))
    (fun i hi => bernoulliPrimeBand_mass_le (P i) (r i) (fun p hp => (hr i hi p hp).2))
    (fun i hi => bernoulliPrimeBand_mass_le (P i) (s i) (fun p hp => (hs i hi p hp).2))

theorem bernoulliPrimeBandMean_prod_deriv_abs_le {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (P : ι → Finset ℕ) (r : ι → ℕ → ℝ → ℝ) (d : ι → ℕ → ℝ)
    (hP : ∀ i ∈ I, ∀ p ∈ P i, p.Prime) {v x : ℝ} (hv : 0 < v)
    (hV : ∀ i ∈ I, v ≤ bandReciprocalMass (P i))
    (hd : ∀ i ∈ I, ∀ p ∈ P i, HasDerivAt (r i p) (d i p) x)
    (hr : ∀ i ∈ I, ∀ p ∈ P i, 0 ≤ r i p x ∧ r i p x ≤ 1 / (p : ℝ)) :
    |deriv (fun t => ∏ i ∈ I,
        bernoulliBandMean (P i) (fun p => r i p t) (bandReciprocalMass (P i))) x| ≤
      (1 / v + 1 / 2) * ∑ i ∈ I, ∑ p ∈ P i, |d i p| :=
  bernoulliBandMean_prod_deriv_abs_le I P r d (fun i => bandReciprocalMass (P i)) hv hV hd
    (fun i hi => bernoulliPrimeBand_probability_bounds (P i) (hP i hi)
      (fun p => r i p x) (hr i hi))
    (fun i hi => bernoulliPrimeBand_mass_le (P i) (fun p => r i p x)
      (fun p hp => (hr i hi p hp).2))

end ArtinMatthews
