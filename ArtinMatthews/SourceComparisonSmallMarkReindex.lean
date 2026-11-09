module

public import ArtinMatthews.SourceComparisonSmallMark
public import ArtinMatthews.SourceComparisonActualBands


set_option backward.privateInPublic true
@[expose] public section

/-! Reindexing the distinguished small group preserves the exact combined
inert and active weight. Its removal remains bounded at square exceptions. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section

variable {J G : Type*} [Fintype J] [Fintype G]

theorem sourceComparisonDistinguishedMarkWeight_inert_eq (e : J → ℝ) (x : ℝ)
    (S : Finset ℕ) (P : G → Finset ℕ) (a : ℕ) (t : G → ℕ) (q₀ : ℝ) (q : G → ℝ)
    (b : ((g : G) → Fin (t g) → ℕ) → ℂ) (n : ℕ) :
    sourceComparisonDistinguishedMarkWeight S (Sum.elim (fun j => markedLogPowerBand (e j) x) P)
      a (Sum.elim (fun _ => 1) t) q₀ (Sum.elim (fun _ => 1/2) q)
      (fun l => b (fun g => l (.inr g))) n =
    sourceComparisonInertActiveMarks e x (Sum.elim (fun _ : Unit => S) P)
      (Sum.elim (fun _ => a) t) (Sum.elim (fun _ => q₀) q)
      (fun l => b (fun g => l (.inr g))) n := by
  rw [sourceComparisonDistinguishedMarkWeight_product, sourceComparisonInertActiveMarks_eq]
  change sourceComparisonMarkWeight (fun _ : Unit => S) (fun _ => a) (fun _ => q₀) (fun _ => 1) n *
    sourceComparisonInertActiveMarks e x P t q b n =
    (literalMarkedArrayWeight e x n : ℂ) * sourceComparisonDistinguishedMarkWeight S P a t q₀ q b n
  rw [sourceComparisonInertActiveMarks_eq, sourceComparisonDistinguishedMarkWeight_product]
  ring

def sourceComparisonDistinguishedGroupEmbedding {x : ℝ} (s : GiantCandidateSmallGroupIndex x)
    (i : G ↪ GiantCandidateGroupIndex x)
    (hout : (Sum.inl s : GiantCandidateGroupIndex x) ∉ Set.range i) :
    Unit ⊕ G ↪ GiantCandidateGroupIndex x where
  toFun := Sum.elim (fun _ => Sum.inl s) i
  inj' := by
    rintro (g | g) (j | j) he
    · exact congrArg Sum.inl (Subsingleton.elim g j)
    · exact (hout ⟨j, he.symm⟩).elim
    · exact (hout ⟨g, he⟩).elim
    · exact congrArg Sum.inr (i.injective he)

theorem sourceComparisonDistinguishedGroupEmbedding_band {x : ℝ} (s : GiantCandidateSmallGroupIndex x)
    (i : G ↪ GiantCandidateGroupIndex x)
    (hout : (Sum.inl s : GiantCandidateGroupIndex x) ∉ Set.range i) :
    giantCandidateGroup x ∘ sourceComparisonDistinguishedGroupEmbedding s i hout =
      Sum.elim (fun _ : Unit => giantCandidateSmallGroup x s) (giantCandidateGroup x ∘ i) := by
  funext g
  cases g <;> rfl

theorem sourceComparisonRemovedSmallMark_norm_le (S : Finset ℕ) (P : G → Finset ℕ)
    (t : G → ℕ) (q₀ : ℝ) (q : G → ℝ) (b : ((g : G) → Fin (t g) → ℕ) → ℂ)
    (hS : ∀ p ∈ S, p.Prime) (hP : ∀ g p, p ∈ P g → p.Prime)
    (hdis : ∀ g, Disjoint S (P g)) (hV : 0 < bandReciprocalMass S)
    (hq₀ : 0 ≤ q₀ ∧ q₀ ≤ 1) (n : ℕ) :
    ‖sourceComparisonRemovedSmallMark S P t q₀ q b n‖ ≤
      ‖sourceComparisonDistinguishedMarkWeight S P 1 t q₀ q b n‖ := by
  classical
  let V := bandReciprocalMass S
  let u := bandCount S n
  let W := sourceComparisonMarkWeight P t q b n
  have hterm (p : ℕ) (hp : p ∈ activeDivisors S n) :
      ‖sourceComparisonDistinguishedMarkWeight S P 0 t q₀ q b (n / p)‖ ≤ q₀ ^ (u - 1) * ‖W‖ := by
    obtain ⟨hpS, hpn⟩ := mem_filter.mp hp
    have he : p * (n / p) = n := Nat.mul_div_cancel' hpn
    have hc : u - 1 ≤ bandCount S (n / p) := by
      unfold u bandCount
      have hhit := sourceComparisonActiveDivisors_mul_prime S hS (hS p hpS) (n / p)
      rw [he, inter_eq_right.mpr (singleton_subset_iff.mpr hpS), singleton_union] at hhit
      rw [hhit]
      have hcard := card_insert_le p (activeDivisors S (n / p))
      omega
    have hout (g : G) : p ∉ P g := fun h => disjoint_left.mp (hdis g) hpS h
    have hw := sourceComparisonMarkWeight_mul_outside P t q b hP (hS p hpS) hout (n / p)
    rw [he] at hw
    rw [sourceComparisonDistinguishedMarkWeight_zero, ← hw, norm_mul, norm_pow, Complex.norm_real,
      Real.norm_of_nonneg hq₀.1]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hq₀.1 hq₀.2 hc) (norm_nonneg _)
  rw [sourceComparisonRemovedSmallMark, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hV.le,
    sourceComparisonDistinguishedMarkWeight_one, norm_mul, norm_mul, norm_div, Complex.norm_natCast,
    Complex.norm_real, Real.norm_of_nonneg hV.le, norm_pow, Complex.norm_real, Real.norm_of_nonneg hq₀.1]
  calc
    _ ≤ V⁻¹ * (∑ p ∈ activeDivisors S n,
        ‖sourceComparisonDistinguishedMarkWeight S P 0 t q₀ q b (n / p)‖) :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr hV.le)
    _ ≤ V⁻¹ * ∑ _p ∈ activeDivisors S n, q₀ ^ (u - 1) * ‖W‖ :=
      mul_le_mul_of_nonneg_left (sum_le_sum hterm) (inv_nonneg.mpr hV.le)
    _ = _ := by
      rw [sum_const, nsmul_eq_mul]
      unfold V u W bandCount
      ring

end
end ArtinMatthews
