module

public import ArtinMatthews.MarkedMinorArcRawPrimeBands
public import ArtinMatthews.MarkedPhysicalMarking


set_option backward.privateInPublic true
@[expose] public section

/-! Exact baseline/tilt arithmetic and sharp relative error. The original
physical atom V⁻¹ and the uniform projective-line probability are explicit;
no equality of physical and tilted measures is asserted. -/
noncomputable section
open scoped BigOperators
namespace ArtinMatthews

theorem markedMemoryBaseline_mul_atom {V q : ℝ} {N p : ℕ}
    (hb : markedMemoryBaseline q N p ≠ 0) :
    markedMemoryBaseline q N p * markedMemoryPrimeAtom V q N p =
      V⁻¹ * (1 / ((p : ℝ)+1)) := by
  unfold markedMemoryPrimeAtom
  field_simp

/-- A single active birth pays the line probability once and the original
V⁻¹ once per active run, including every subsequent promotion. -/
theorem markedMemory_active_run_charge (V q : ℝ) (N p r : ℕ) :
    markedMemoryPrimeAtom V q N p * (V⁻¹)^r =
      (V⁻¹)^(r+1) * (1 / (((p : ℝ)+1)*markedMemoryBaseline q N p)) := by
  simp only [markedMemoryPrimeAtom, one_div, mul_inv_rev, pow_succ]
  ring

/-- A ghost birth has its V factor cancelled, while each later active run
pays its genuine promotion factor V⁻¹. -/
theorem markedMemory_ghost_run_charge {V : ℝ} (hV : V ≠ 0) (q : ℝ) (N p r : ℕ) :
    (V * markedMemoryPrimeAtom V q N p) * (V⁻¹)^r =
      (V⁻¹)^r * (1 / (((p : ℝ)+1)*markedMemoryBaseline q N p)) := by
  simp only [markedMemoryPrimeAtom, one_div, mul_inv_rev]
  field_simp

def markedMemoryTiltRatio (q : ℝ) (N p : ℕ) : ℝ :=
  (p : ℝ) / (((p : ℝ)+1)*markedMemoryBaseline q N p)

theorem markedMemoryPrimeAtom_eq_ratio {V q : ℝ} {N p : ℕ} (hp : p ≠ 0) :
    markedMemoryPrimeAtom V q N p = markedMemoryTiltRatio q N p * ((1/(p : ℝ))/V) := by
  unfold markedMemoryPrimeAtom markedMemoryTiltRatio
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp
  field_simp

/-- The exact ratio has an O((N+1)/p) error, rather than a fixed factor-two
loss which could not be raised to the growing boundary slot count. -/
theorem markedMemoryTiltRatio_error {q : ℝ} (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1)
    {N p : ℕ} (hp : 0 < p) (hlarge : 2*(N+1) ≤ p+1) :
    |markedMemoryTiltRatio q N p - 1| ≤ 2*((N : ℝ)+1)/(p : ℝ) := by
  let E : ℝ := ∑ j : Fin (N+1), markedMemoryEta q N j
  let d : ℝ := ((p : ℝ)+1)*markedMemoryBaseline q N p
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp
  have hp1 : 0 < (p : ℝ)+1 := by positivity
  have hE := markedMemoryEta_sum_bounds hq₀ hq₁ N
  have hb := (markedMemoryBaseline_bounds hq₀ hq₁ hlarge).1
  have hd : (p : ℝ)/2 ≤ d := by
    have h := mul_le_mul_of_nonneg_left hb hp1.le
    dsimp only [d]
    linarith
  have hdpos : 0 < d := (by positivity : 0 < (p : ℝ)/2).trans_le hd
  have hde : d = (p : ℝ)+1-E := by
    dsimp [d, markedMemoryBaseline, E]
    field_simp
  have hnum : |E-1| ≤ (N : ℝ)+1 := by
    apply abs_le.mpr
    constructor <;> dsimp only [E] <;> linarith [hE.1, hE.2, Nat.cast_nonneg N (α := ℝ)]
  have hratio : markedMemoryTiltRatio q N p - 1 = (E-1)/d := by
    change (p : ℝ)/d-1=(E-1)/d
    rw [div_sub_one hdpos.ne']
    congr 1
    rw [hde]
    ring
  rw [hratio, abs_div, abs_of_pos hdpos]
  calc
    _ ≤ ((N : ℝ)+1)/d := div_le_div_of_nonneg_right hnum hdpos.le
    _ ≤ 2*((N : ℝ)+1)/(p : ℝ) := by
      apply (div_le_div_iff₀ hdpos hpR).mpr
      nlinarith [Nat.cast_nonneg N (α := ℝ)]

theorem markedTiltedBandAtom_sharp_error (P : Finset ℕ) {q : ℝ} {N : ℕ}
    (hV : 0 < bandReciprocalMass P) (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1)
    (p : P) (hp : 0 < p.1) (hlarge : 2*(N+1) ≤ p.1+1) :
    |markedTiltedBandAtom P q N p - markedHarmonicAtom P p| ≤
      (2*((N : ℝ)+1)/(p.1 : ℝ))*markedHarmonicAtom P p := by
  have hμ : 0 ≤ markedHarmonicAtom P p := markedHarmonicAtom_nonneg P hV
  have heq : markedTiltedBandAtom P q N p = markedMemoryTiltRatio q N p * markedHarmonicAtom P p :=
    markedMemoryPrimeAtom_eq_ratio hp.ne'
  rw [heq, ← sub_one_mul, abs_mul, abs_of_nonneg hμ]
  exact mul_le_mul_of_nonneg_right (markedMemoryTiltRatio_error hq₀ hq₁ hp hlarge) hμ

/-- The exact mass defect of one band, uniformly over its actual labels. -/
theorem markedTiltedBandMass_error (P : Finset ℕ) {q y : ℝ} {N : ℕ}
    (hV : 0 < bandReciprocalMass P) (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) (hy : 0 < y)
    (hP : ∀ p ∈ P, 0 < p ∧ y ≤ (p : ℝ) ∧ 2*(N+1) ≤ p+1) :
    |(∑ p : P, markedTiltedBandAtom P q N p)-1| ≤ 2*((N : ℝ)+1)/y := by
  rw [← markedHarmonicAtom_sum P hV, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ p : P, |markedTiltedBandAtom P q N p-markedHarmonicAtom P p| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p : P, (2*((N : ℝ)+1)/y)*markedHarmonicAtom P p := by
      apply Finset.sum_le_sum
      intro p _
      obtain ⟨hp, hpy, hlarge⟩ := hP p.1 p.2
      apply (markedTiltedBandAtom_sharp_error P hV hq₀ hq₁ p hp hlarge).trans
      exact mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_left (by positivity) hy hpy) (markedHarmonicAtom_nonneg P hV)
    _ = _ := by rw [← Finset.mul_sum, markedHarmonicAtom_sum P hV, mul_one]

/-- Entrywise full-list normalization. This is the exact original physical
mass times one uniform-line factor per birth entry, not a mass-preserving
identification of sigma and nu. Global birth distinctness remains a separate
condition when these entries are interpreted as distinct prime lifespans. -/
theorem markedMemoryBaseline_rawActiveMass {J : Type*} [Fintype J]
    (P : J → Finset Nat.Primes) (V : J → ℝ) (q : ℝ) (N M : ℕ)
    (a : MarkedRawActive P M)
    (hb : ∀ j k, markedMemoryBaseline q N ((a j k).1 : ℕ) ≠ 0) :
    (∏ j, ∏ k, markedMemoryBaseline q N ((a j k).1 : ℕ)) *
      markedRawActiveMass (fun j p => markedMemoryPrimeAtom (V j) q N (p.1 : ℕ)) a =
      markedPhysicalMass V M * ∏ j, ∏ k, (1 / (((a j k).1 : ℝ)+1)) := by
  unfold markedRawActiveMass
  simp only [← Finset.prod_mul_distrib]
  calc
    _ = ∏ j, ∏ k, (V j)⁻¹ * (1 / (((a j k).1 : ℝ)+1)) := by
      apply Finset.prod_congr rfl
      intro j _
      apply Finset.prod_congr rfl
      intro k _
      exact markedMemoryBaseline_mul_atom (hb j k)
    _ = _ := by
      simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      rfl

end ArtinMatthews
