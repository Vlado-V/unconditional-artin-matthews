module

public import ArtinMatthews.GiantSinglePrimeResidue


set_option backward.privateInPublic true
@[expose] public section

/-!
# Exact active single-prime lifespans

Each endpoint choice selects an optional earlier ghost birth and an optional
later ghost termination. Their finite sum equals the literal active residue
expectation. Each weight uses only offsets within its own interval.
-/

namespace ArtinMatthews

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

abbrev GiantSignedPrimePrefixChoice {n : ℕ} (a : Fin n) :=
  Option ↥(Finset.univ.filter (fun l : Fin n => l < a))

abbrev GiantSignedPrimeSuffixChoice {n : ℕ} (z : Fin n) :=
  Option ↥(Finset.univ.filter (fun u : Fin n => z < u))

abbrev GiantSignedPrimeActiveEndpointChoice {n : ℕ} (A : Finset (Fin n))
    (hA : A.Nonempty) :=
  GiantSignedPrimePrefixChoice (A.min' hA) × GiantSignedPrimeSuffixChoice (A.max' hA)

def giantSignedPrimeStart {n : ℕ} (a : Fin n) : GiantSignedPrimePrefixChoice a → Fin n
  | none => a
  | some l => l.1

def giantSignedPrimeEnd {n : ℕ} (z : Fin n) : GiantSignedPrimeSuffixChoice z → Fin n
  | none => z
  | some u => u.1

def giantSignedPrimeBirthCoefficient (p : ℕ) {n : ℕ} (h : Fin n → ℤ)
    (q : Fin n → ℝ) (a : Fin n) : GiantSignedPrimePrefixChoice a → ℝ
  | none => 1
  | some l => (-(1 - q l.1)) * giantSignedPrimeOffsetHit p h l.1 a

def giantSignedPrimeTerminationCoefficient (p : ℕ) {n : ℕ} (h : Fin n → ℤ)
    (q : Fin n → ℝ) (a z : Fin n) : GiantSignedPrimeSuffixChoice z → ℝ
  | none => 1
  | some u => (-(1 - q u.1)) * giantSignedPrimeOffsetHit p h u.1 a

def giantSignedPrimePrefixWeight (p : ℕ) {n : ℕ} (h : Fin n → ℤ)
    (q : Fin n → ℝ) (a : Fin n) (c : GiantSignedPrimePrefixChoice a) : ℝ :=
  giantSignedPrimeBirthCoefficient p h q a c *
    ∏ i ∈ Finset.univ.filter (fun i => giantSignedPrimeStart a c < i ∧ i < a),
      giantSignedPrimeDamping p h q i a

def giantSignedPrimeSuffixWeight (p : ℕ) {n : ℕ} (h : Fin n → ℤ)
    (q : Fin n → ℝ) (a z : Fin n) (c : GiantSignedPrimeSuffixChoice z) : ℝ :=
  giantSignedPrimeTerminationCoefficient p h q a z c *
    ∏ i ∈ Finset.univ.filter (fun i => z < i ∧ i < giantSignedPrimeEnd z c),
      giantSignedPrimeDamping p h q i a

def giantSignedPrimeActiveEndpointWeight (p : ℕ) {n : ℕ} (h : Fin n → ℤ)
    (q : Fin n → ℝ) (A : Finset (Fin n)) (hA : A.Nonempty)
    (c : GiantSignedPrimeActiveEndpointChoice A hA) : ℝ :=
  if GiantSignedPrimeActiveCompatible p h A (A.min' hA) then
    giantSignedPrimePrefixWeight p h q (A.min' hA) c.1 *
      (∏ i ∈ Finset.univ.filter (fun i => A.min' hA < i ∧ i < A.max' hA ∧ i ∉ A),
        giantSignedPrimeDamping p h q i (A.min' hA)) *
      giantSignedPrimeSuffixWeight p h q (A.min' hA) (A.max' hA) c.2
  else 0

private theorem between_self {n : ℕ} (a : Fin n) :
    Finset.univ.filter (fun i : Fin n => a < i ∧ i < a) = ∅ := by
  rw [Finset.filter_eq_empty_iff]
  intro i _ hi
  exact lt_asymm hi.1 hi.2

theorem giantSignedPrimeStart_le {n : ℕ} (a : Fin n) (c : GiantSignedPrimePrefixChoice a) :
    giantSignedPrimeStart a c ≤ a := by
  cases c with
  | none => exact le_rfl
  | some l => exact (Finset.mem_filter.mp l.2).2.le

theorem giantSignedPrimeEnd_ge {n : ℕ} (z : Fin n) (c : GiantSignedPrimeSuffixChoice z) :
    z ≤ giantSignedPrimeEnd z c := by
  cases c with
  | none => exact le_rfl
  | some u => exact (Finset.mem_filter.mp u.2).2.le

theorem giantSignedPrimeActiveEndpoint_bounds {n : ℕ} (A : Finset (Fin n))
    (hA : A.Nonempty) (c : GiantSignedPrimeActiveEndpointChoice A hA)
    (i : Fin n) (hi : i ∈ A) :
    giantSignedPrimeStart (A.min' hA) c.1 ≤ i ∧
      i ≤ giantSignedPrimeEnd (A.max' hA) c.2 :=
  ⟨(giantSignedPrimeStart_le _ _).trans (A.min'_le i hi),
    (A.le_max' i hi).trans (giantSignedPrimeEnd_ge _ _)⟩

/-- The before, internal-unmarked, and after sets partition the unmarked
visits in any finite set. -/
theorem giantSignedPrimeInactive_product {n : ℕ} (s A : Finset (Fin n))
    (hA : A.Nonempty) (f : Fin n → ℝ) :
    (∏ i ∈ s \ A, f i) =
      (∏ i ∈ s.filter (fun i => i < A.min' hA), f i) *
      (∏ i ∈ s.filter (fun i => A.min' hA < i ∧ i < A.max' hA ∧ i ∉ A), f i) *
      (∏ i ∈ s.filter (fun i => A.max' hA < i), f i) := by
  let a := A.min' hA
  let z := A.max' hA
  have ha : a ∈ A := A.min'_mem hA
  have hz : z ∈ A := A.max'_mem hA
  have haz : a ≤ z := A.min'_le_max' hA
  have hpartition : s \ A = (s.filter (fun i => i < a) ∪
      s.filter (fun i => a < i ∧ i < z ∧ i ∉ A)) ∪ s.filter (fun i => z < i) := by
    ext i
    simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro ⟨his, hiA⟩
      have hia : i ≠ a := fun hh => hiA (hh ▸ ha)
      have hiz : i ≠ z := fun hh => hiA (hh ▸ hz)
      by_cases hl : i < a
      · exact Or.inl (Or.inl ⟨his, hl⟩)
      · by_cases hr : z < i
        · exact Or.inr ⟨his, hr⟩
        · exact Or.inl (Or.inr ⟨his, by omega, by omega, hiA⟩)
    · rintro ((⟨his, hl⟩ | ⟨his, hi, hz', hiA⟩) | ⟨his, hr⟩)
      · refine ⟨his, fun hiA => ?_⟩
        have hh := A.min'_le i hiA
        omega
      · exact ⟨his, hiA⟩
      · refine ⟨his, fun hiA => ?_⟩
        have hh := A.le_max' i hiA
        omega
  have hbi : Disjoint (s.filter (fun i => i < a))
      (s.filter (fun i => a < i ∧ i < z ∧ i ∉ A)) := by
    apply Finset.disjoint_left.mpr
    intro i hb hi
    have hb' := (Finset.mem_filter.mp hb).2
    have hi' := (Finset.mem_filter.mp hi).2.1
    omega
  have hba : Disjoint (s.filter (fun i => i < a)) (s.filter (fun i => z < i)) := by
    apply Finset.disjoint_left.mpr
    intro i hb he
    have hb' := (Finset.mem_filter.mp hb).2
    have he' := (Finset.mem_filter.mp he).2
    omega
  have hie : Disjoint (s.filter (fun i => a < i ∧ i < z ∧ i ∉ A))
      (s.filter (fun i => z < i)) := by
    apply Finset.disjoint_left.mpr
    intro i hi he
    have hi' := (Finset.mem_filter.mp hi).2.2.1
    have he' := (Finset.mem_filter.mp he).2
    omega
  rw [hpartition, Finset.prod_union (Finset.disjoint_union_left.mpr ⟨hba, hie⟩),
    Finset.prod_union hbi]

/-- Prefix telescoping includes the absent ghost and every strict earlier birth. -/
theorem giantSignedPrimePrefixWeight_sum (p : ℕ) {n : ℕ} (h : Fin n → ℤ)
    (q : Fin n → ℝ) (a : Fin n) :
    (∑ c : GiantSignedPrimePrefixChoice a, giantSignedPrimePrefixWeight p h q a c) =
      ∏ i ∈ Finset.univ.filter (fun i => i < a), giantSignedPrimeDamping p h q i a := by
  rw [Fintype.sum_option]
  change 1 * (∏ i ∈ Finset.univ.filter (fun i => a < i ∧ i < a),
      giantSignedPrimeDamping p h q i a) +
    (∑ l : ↥(Finset.univ.filter (fun l : Fin n => l < a)),
      (-(1 - q l.1)) * giantSignedPrimeOffsetHit p h l.1 a *
        ∏ i ∈ Finset.univ.filter (fun i => l.1 < i ∧ i < a),
          giantSignedPrimeDamping p h q i a) = _
  rw [between_self]
  simp only [Finset.prod_empty, mul_one]
  rw [Finset.sum_coe_sort (s := Finset.univ.filter (fun l : Fin n => l < a))
    (f := fun l => (-(1 - q l)) * giantSignedPrimeOffsetHit p h l a *
      ∏ i ∈ Finset.univ.filter (fun i => l < i ∧ i < a),
        giantSignedPrimeDamping p h q i a)]
  have ht := marked_memory_prefix (Finset.univ : Finset (Fin n))
    (fun i => (1 - q i) * giantSignedPrimeOffsetHit p h i a) a
  change 1 + _ = _
  simp only [giantSignedPrimeDamping]
  rw [ht]
  simp only [neg_mul, Finset.sum_neg_distrib]
  ring

/-- Suffix telescoping includes the absent ghost and every strict later termination. -/
theorem giantSignedPrimeSuffixWeight_sum (p : ℕ) {n : ℕ} (h : Fin n → ℤ)
    (q : Fin n → ℝ) (a z : Fin n) :
    (∑ c : GiantSignedPrimeSuffixChoice z, giantSignedPrimeSuffixWeight p h q a z c) =
      ∏ i ∈ Finset.univ.filter (fun i => z < i), giantSignedPrimeDamping p h q i a := by
  rw [Fintype.sum_option]
  change 1 * (∏ i ∈ Finset.univ.filter (fun i => z < i ∧ i < z),
      giantSignedPrimeDamping p h q i a) +
    (∑ u : ↥(Finset.univ.filter (fun u : Fin n => z < u)),
      (-(1 - q u.1)) * giantSignedPrimeOffsetHit p h u.1 a *
        ∏ i ∈ Finset.univ.filter (fun i => z < i ∧ i < u.1),
          giantSignedPrimeDamping p h q i a) = _
  rw [between_self]
  simp only [Finset.prod_empty, mul_one]
  rw [Finset.sum_coe_sort (s := Finset.univ.filter (fun u : Fin n => z < u))
    (f := fun u => (-(1 - q u)) * giantSignedPrimeOffsetHit p h u a *
      ∏ i ∈ Finset.univ.filter (fun i => z < i ∧ i < u),
        giantSignedPrimeDamping p h q i a)]
  have ht := marked_memory_suffix (Finset.univ : Finset (Fin n))
    (fun i => (1 - q i) * giantSignedPrimeOffsetHit p h i a) z
  change 1 + _ = _
  simp only [giantSignedPrimeDamping]
  rw [ht]
  simp only [neg_mul, Finset.sum_neg_distrib]
  ring

/-- The finite endpoint sum keeps all strict ghost choices and every
internal unmarked damping factor. -/
theorem giantSignedPrimeActiveEndpointWeight_sum (p : ℕ) {n : ℕ} (h : Fin n → ℤ)
    (q : Fin n → ℝ) (A : Finset (Fin n)) (hA : A.Nonempty) :
    (∑ c : GiantSignedPrimeActiveEndpointChoice A hA,
      giantSignedPrimeActiveEndpointWeight p h q A hA c) =
      if GiantSignedPrimeActiveCompatible p h A (A.min' hA) then
        ∏ i ∈ Finset.univ \ A, giantSignedPrimeDamping p h q i (A.min' hA) else 0 := by
  by_cases hc : GiantSignedPrimeActiveCompatible p h A (A.min' hA)
  · simp only [giantSignedPrimeActiveEndpointWeight, hc, ite_true]
    rw [Fintype.sum_prod_type]
    calc
      _ = (∑ l : GiantSignedPrimePrefixChoice (A.min' hA),
            giantSignedPrimePrefixWeight p h q (A.min' hA) l) *
          (∏ i ∈ Finset.univ.filter (fun i => A.min' hA < i ∧ i < A.max' hA ∧ i ∉ A),
            giantSignedPrimeDamping p h q i (A.min' hA)) *
          (∑ u : GiantSignedPrimeSuffixChoice (A.max' hA),
            giantSignedPrimeSuffixWeight p h q (A.min' hA) (A.max' hA) u) := by
              simp only [Finset.sum_mul, Finset.mul_sum]
              rw [Finset.sum_comm]
      _ = _ := by
        rw [giantSignedPrimePrefixWeight_sum, giantSignedPrimeSuffixWeight_sum]
        exact (giantSignedPrimeInactive_product Finset.univ A hA _).symm
  · simp only [giantSignedPrimeActiveEndpointWeight, hc, ite_false, Finset.sum_const_zero]

/-- The literal active residue average equals the full finite sum of
lifespans, with one reciprocal-prime charge. -/
theorem giantSignedPrimeResidueExpectation_lifespans (p : ℕ) [NeZero p] {n : ℕ}
    (h : Fin n → ℤ) (q : Fin n → ℝ) (A : Finset (Fin n)) (hA : A.Nonempty) :
    giantSignedPrimeResidueExpectation p h q A = (1 / (p : ℝ)) *
      ∑ c : GiantSignedPrimeActiveEndpointChoice A hA,
        giantSignedPrimeActiveEndpointWeight p h q A hA c := by
  rw [giantSignedPrimeActiveEndpointWeight_sum]
  exact giantSignedPrimeResidueExpectation_active p h q A (A.min' hA) (A.min'_mem hA)

/-- Removing the common baseline retains exactly the cost `1 / (p * b_p)`. -/
theorem giantSignedPrimeResidueExpectation_lifespans_normalized (p : ℕ) [NeZero p] {n : ℕ}
    (h : Fin n → ℤ) (q : Fin n → ℝ) (A : Finset (Fin n)) (hA : A.Nonempty)
    (hb : giantSignedPrimeResidueBaseline p q ≠ 0) :
    giantSignedPrimeResidueExpectation p h q A / giantSignedPrimeResidueBaseline p q =
      (1 / ((p : ℝ) * giantSignedPrimeResidueBaseline p q)) *
        ∑ c : GiantSignedPrimeActiveEndpointChoice A hA,
          giantSignedPrimeActiveEndpointWeight p h q A hA c := by
  rw [giantSignedPrimeResidueExpectation_lifespans p h q A hA]
  field_simp

end
end ArtinMatthews
