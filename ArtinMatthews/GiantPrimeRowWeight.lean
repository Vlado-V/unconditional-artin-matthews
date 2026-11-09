module

public import ArtinMatthews.GiantPrimeRowCharge


set_option backward.privateInPublic true
@[expose] public section

/-!
# Literal scalar rows for a chosen prime lifespan

The source rows retain `q_i / ρ²`, `-(1-q_i)V / ρ`, and `-(1-q_i) / ρ`.
Their local contractions and the finite active-run charge recover the
baseline-relative lifespan weight exactly.
-/

namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def giantSignedRowInternalDamping (ρ : ℝ) (p : ℕ) {n : ℕ}
    (offset : Fin n → ℤ) (q : Fin n → ℝ) (i a : Fin n) : ℝ :=
  if (offset i : ZMod p) = (offset a : ZMod p) then ρ * giantSignedRowA (q i) ρ * ρ else 1

theorem giantSignedRowInternalDamping_eq (ρ : ℝ) (hρ : ρ ≠ 0) (p : ℕ) {n : ℕ}
    (offset : Fin n → ℤ) (q : Fin n → ℝ) (i a : Fin n) :
    giantSignedRowInternalDamping ρ p offset q i a = giantSignedPrimeDamping p offset q i a := by
  rw [giantSignedPrimeDamping_eq]
  unfold giantSignedRowInternalDamping
  split_ifs
  · exact giantSignedRowA_cancel (q i) ρ hρ
  · rfl

def giantSignedActiveBirthRows (V ρ : ℝ) (p : ℕ) {n : ℕ}
    (offset : Fin n → ℤ) (q : Fin n → ℝ) (A : Finset (Fin n)) (hA : A.Nonempty) :
    GiantSignedPrimePrefixChoice (A.min' hA) → ℝ
  | none => giantSignedRowBirthAtom V p q * (V⁻¹) ^ (giantSignedActiveRunCount A - 1)
  | some l => (giantSignedRowC (q l.1) V ρ * ρ * giantSignedRowBirthAtom V p q) *
      (V⁻¹) ^ giantSignedActiveRunCount A * giantSignedPrimeOffsetHit p offset l.1 (A.min' hA)

def giantSignedActiveTerminationRows (ρ : ℝ) (p : ℕ) {n : ℕ}
    (offset : Fin n → ℤ) (q : Fin n → ℝ) (A : Finset (Fin n)) (hA : A.Nonempty) :
    GiantSignedPrimeSuffixChoice (A.max' hA) → ℝ
  | none => 1
  | some u => (ρ * giantSignedRowD (q u.1) ρ) *
      giantSignedPrimeOffsetHit p offset u.1 (A.min' hA)

theorem giantSignedActiveBirthRows_eq (V ρ : ℝ) (hV : V ≠ 0) (hρ : ρ ≠ 0) (p : ℕ)
    {n : ℕ} (offset : Fin n → ℤ) (q : Fin n → ℝ) (A : Finset (Fin n)) (hA : A.Nonempty)
    (c : GiantSignedPrimePrefixChoice (A.min' hA)) :
    giantSignedActiveBirthRows V ρ p offset q A hA c =
      ((V⁻¹) ^ giantSignedActiveRunCount A *
        (1 / ((p : ℝ) * giantSignedPrimeResidueBaseline p q))) *
          giantSignedPrimeBirthCoefficient p offset q (A.min' hA) c := by
  cases c with
  | none =>
    simpa only [giantSignedActiveBirthRows, giantSignedPrimeBirthCoefficient, mul_one] using
      giantSignedActiveFirst_runCharge V p q A hA
  | some l =>
    change (giantSignedRowC (q l.1) V ρ * ρ * giantSignedRowBirthAtom V p q) *
        (V⁻¹) ^ giantSignedActiveRunCount A * giantSignedPrimeOffsetHit p offset l.1 (A.min' hA) = _
    rw [giantSignedRowC_cancel (q l.1) V ρ hρ]
    unfold giantSignedPrimeBirthCoefficient
    calc
      _ = (-(1 - q l.1) * giantSignedPrimeOffsetHit p offset l.1 (A.min' hA)) *
          ((V * giantSignedRowBirthAtom V p q) * (V⁻¹) ^ giantSignedActiveRunCount A) := by ring
      _ = _ := by rw [giantSignedGhostFirst_runCharge V hV p q A]; ring

theorem giantSignedActiveTerminationRows_eq (ρ : ℝ) (hρ : ρ ≠ 0) (p : ℕ) {n : ℕ}
    (offset : Fin n → ℤ) (q : Fin n → ℝ) (A : Finset (Fin n)) (hA : A.Nonempty)
    (c : GiantSignedPrimeSuffixChoice (A.max' hA)) :
    giantSignedActiveTerminationRows ρ p offset q A hA c =
      giantSignedPrimeTerminationCoefficient p offset q (A.min' hA) (A.max' hA) c := by
  cases c with
  | none => rfl
  | some u =>
    change (ρ * giantSignedRowD (q u.1) ρ) *
        giantSignedPrimeOffsetHit p offset u.1 (A.min' hA) = _
    rw [giantSignedRowD_cancel (q u.1) ρ hρ]
    rfl

def giantSignedActiveRowWeight (V ρ : ℝ) (p : ℕ) {n : ℕ}
    (offset : Fin n → ℤ) (q : Fin n → ℝ) (A : Finset (Fin n)) (hA : A.Nonempty)
    (c : GiantSignedPrimeActiveEndpointChoice A hA) : ℝ :=
  if GiantSignedPrimeActiveCompatible p offset A (A.min' hA) then
    giantSignedActiveBirthRows V ρ p offset q A hA c.1 *
      (∏ i ∈ Finset.univ.filter (fun i =>
        giantSignedPrimeStart (A.min' hA) c.1 < i ∧
          i < giantSignedPrimeEnd (A.max' hA) c.2 ∧ i ∉ A),
        giantSignedRowInternalDamping ρ p offset q i (A.min' hA)) *
      giantSignedActiveTerminationRows ρ p offset q A hA c.2
  else 0

theorem giantSignedActiveRowWeight_eq (V ρ : ℝ) (hV : V ≠ 0) (hρ : ρ ≠ 0) (p : ℕ)
    {n : ℕ} (offset : Fin n → ℤ) (q : Fin n → ℝ) (A : Finset (Fin n)) (hA : A.Nonempty)
    (c : GiantSignedPrimeActiveEndpointChoice A hA) :
    giantSignedActiveRowWeight V ρ p offset q A hA c =
      ((V⁻¹) ^ giantSignedActiveRunCount A *
        (1 / ((p : ℝ) * giantSignedPrimeResidueBaseline p q))) *
          giantSignedPrimeActiveEndpointWeight p offset q A hA c := by
  rw [giantSignedPrimeActiveEndpointWeight_interval]
  unfold giantSignedActiveRowWeight
  by_cases hc : GiantSignedPrimeActiveCompatible p offset A (A.min' hA)
  · simp only [hc, ite_true]
    rw [giantSignedActiveBirthRows_eq V ρ hV hρ p offset q A hA c.1,
      giantSignedActiveTerminationRows_eq ρ hρ p offset q A hA c.2]
    simp_rw [giantSignedRowInternalDamping_eq ρ hρ]
    ring
  · simp only [hc, ite_false, mul_zero]

def giantSignedOrphanRowWeight (V ρ : ℝ) (p : ℕ) {n : ℕ}
    (offset : Fin n → ℤ) (q : Fin n → ℝ) (c : GiantSignedPrimeOrphanEndpointChoice n) : ℝ :=
  (giantSignedRowC (q c.1) V ρ * ρ * giantSignedRowBirthAtom V p q) *
    (∏ i ∈ Finset.univ.filter (fun i => c.1 < i ∧ i < c.2.1),
      giantSignedRowInternalDamping ρ p offset q i c.1) *
    ((ρ * giantSignedRowD (q c.2.1) ρ) * giantSignedPrimeOffsetHit p offset c.2.1 c.1)

theorem giantSignedOrphanRowWeight_eq (V ρ : ℝ) (hV : V ≠ 0) (hρ : ρ ≠ 0) (p : ℕ)
    {n : ℕ} (offset : Fin n → ℤ) (q : Fin n → ℝ) (c : GiantSignedPrimeOrphanEndpointChoice n) :
    giantSignedOrphanRowWeight V ρ p offset q c =
      (1 / ((p : ℝ) * giantSignedPrimeResidueBaseline p q)) *
        giantSignedPrimeOrphanEndpointWeight p offset q c := by
  have hν : V * giantSignedRowBirthAtom V p q =
      1 / ((p : ℝ) * giantSignedPrimeResidueBaseline p q) := by
    simpa only [giantSignedActiveRunCount_empty, pow_zero, mul_one] using
      giantSignedOrphan_runCharge V hV p q
  unfold giantSignedOrphanRowWeight giantSignedPrimeOrphanEndpointWeight giantSignedPrimeOrphanWeight
  rw [giantSignedRowC_cancel (q c.1) V ρ hρ, giantSignedRowD_cancel (q c.2.1) ρ hρ]
  simp_rw [giantSignedRowInternalDamping_eq ρ hρ]
  calc
    _ = (V * giantSignedRowBirthAtom V p q) *
        ((-(1 - q c.1)) * (-(1 - q c.2.1)) * giantSignedPrimeOffsetHit p offset c.2.1 c.1 *
          ∏ i ∈ Finset.univ.filter (fun i => c.1 < i ∧ i < c.2.1), giantSignedPrimeDamping p offset q i c.1) := by ring
    _ = _ := by rw [hν]

def giantSignedPrimeRowWeight (V ρ : ℝ) (p : ℕ) {n : ℕ}
    (offset : Fin n → ℤ) (q : Fin n → ℝ) (A : Finset (Fin n))
    (c : GiantSignedResidueLifespanChoice A) : ℝ :=
  if hA : A.Nonempty then
    giantSignedActiveRowWeight V ρ p offset q A hA (giantSignedResidueLifespanActiveEquiv A hA c)
  else
    (giantSignedResidueLifespanInactiveEquiv A hA c).elim 1
      (giantSignedOrphanRowWeight V ρ p offset q)

/-- The literal contracted rows have the exact run normalization of the
baseline-relative lifespan weight. -/
theorem giantSignedPrimeRowWeight_eq (V ρ : ℝ) (hV : V ≠ 0) (hρ : ρ ≠ 0) (p : ℕ)
    {n : ℕ} (offset : Fin n → ℤ) (q : Fin n → ℝ) (A : Finset (Fin n))
    (c : GiantSignedResidueLifespanChoice A) (hb : giantSignedPrimeResidueBaseline p q ≠ 0) :
    giantSignedPrimeRowWeight V ρ p offset q A c =
      (V⁻¹) ^ giantSignedActiveRunCount A *
        (giantSignedResidueLifespanWeight p offset q A c / giantSignedPrimeResidueBaseline p q) := by
  by_cases hA : A.Nonempty
  · simp only [giantSignedPrimeRowWeight, giantSignedResidueLifespanWeight, dite_eq_left hA]
    rw [giantSignedActiveRowWeight_eq V ρ hV hρ]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  · have hr : giantSignedActiveRunCount A = 0 := by
      rw [Finset.not_nonempty_iff_eq_empty.mp hA, giantSignedActiveRunCount_empty]
    simp only [giantSignedPrimeRowWeight, giantSignedResidueLifespanWeight, dite_eq_right hA,
      hr, pow_zero, one_mul]
    cases giantSignedResidueLifespanInactiveEquiv A hA c with
    | none => simp only [Option.elim_none, div_self hb]
    | some e =>
      simp only [Option.elim_some]
      rw [giantSignedOrphanRowWeight_eq V ρ hV hρ]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring

end
end ArtinMatthews
