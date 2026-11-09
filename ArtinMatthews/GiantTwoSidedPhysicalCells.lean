module

public import ArtinMatthews.GiantTwoSidedPhysicalFamilyMatrix
public import ArtinMatthews.GiantTwoSidedPatternDilationBound


set_option backward.privateInPublic true
@[expose] public section

/-! Consecutive position cells localize the actual physical edges.
The cell count is a count of integer positions on the original slice. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

theorem giantTwoSidedPhysicalFamilyMatrix_displacement {I J : Type*}
    [Fintype J] [DecidableEq J] {P : J → Finset ℕ} {k ell H : ℕ} {Z : Finset ℕ}
    (patterns : Finset I) (C : I → J → Finset (Fin k)) (step : ℤ) (q ζ : ℝ)
    (K : ∀ p, GiantTwoSidedPatternCoefficient P (C p) ell)
    (hD : ∀ p ∈ patterns, ∀ (a : MarkedPhysicalMarking P (k+ell)) aux,
      step.natAbs * giantTwoSidedPatternDilation (C p) a aux ≤ H)
    (s t : GiantTwoSidedEndpointState P (k+ell) Z)
    (hst : giantTwoSidedPhysicalFamilyMatrix patterns C step q ζ K s t ≠ 0) :
    ((t.val.1.val : ℤ) - (s.val.1.val : ℤ)).natAbs ≤ H := by
  by_contra! h
  apply hst
  unfold giantTwoSidedPhysicalFamilyMatrix
  rw [Finset.sum_eq_zero, mul_zero]
  intro choice _
  unfold giantTwoSidedPhysicalChoiceCoefficient giantTwoSidedPatternPhysicalCoefficient
  apply if_neg
  intro hc
  have he : (t.val.1.val : ℤ) - (s.val.1.val : ℤ) =
      step * (giantTwoSidedPatternDilation (C choice.1.val)
        (giantTwoSidedEndpointPermute choice.2.1 s).val.2 choice.2.2.2 : ℤ) := by
    have hm := hc.2.1
    change (t.val.1.val : ℤ) = (s.val.1.val : ℤ) +
      step * (giantTwoSidedPatternDilation (C choice.1.val)
        (giantTwoSidedEndpointPermute choice.2.1 s).val.2 choice.2.2.2 : ℤ) at hm
    omega
  rw [he, Int.natAbs_mul, Int.natAbs_natCast] at h
  exact (not_lt_of_ge (hD _ choice.1.property _ _)) h

def giantTwoSidedPhysicalCell (H : ℕ) {Z : Finset ℕ} (z : ↥Z) : ℤ :=
  ((z.val / H : ℕ) : ℤ)

theorem giantTwoSidedPhysicalCell_card_le (Z : Finset ℕ) {H : ℕ} (hH : 0 < H) (b : ℤ) :
    (Finset.univ.filter (fun z : ↥Z => giantTwoSidedPhysicalCell H z = b)).card ≤ H := by
  refine le_trans ?_ (Finset.card_range H).le
  apply Finset.card_le_card_of_injOn (fun z : ↥Z => z.val % H)
  · intro z _
    exact Finset.mem_range.mpr (Nat.mod_lt _ hH)
  · intro z hz v hv he
    change z.val % H = v.val % H at he
    have hd : z.val / H = v.val / H := by
      have hc := (Finset.mem_filter.mp hz).2.trans (Finset.mem_filter.mp hv).2.symm
      change ((z.val / H : ℕ) : ℤ) = ((v.val / H : ℕ) : ℤ) at hc
      exact_mod_cast hc
    apply Subtype.ext
    calc
      z.val = z.val % H + H*(z.val/H) := (Nat.mod_add_div _ _).symm
      _ = v.val % H + H*(v.val/H) := by rw [he,hd]
      _ = v.val := Nat.mod_add_div _ _

theorem giantTwoSidedPhysicalCell_neighbors {Z : Finset ℕ} {H : ℕ} (hH : 0 < H) (z v : ↥Z)
    (h : ((v.val : ℤ) - (z.val : ℤ)).natAbs ≤ H) :
    giantTwoSidedPhysicalCell H v - giantTwoSidedPhysicalCell H z ∈ Finset.Icc (-1 : ℤ) 1 := by
  have ha : |(v.val : ℤ) - (z.val : ℤ)| ≤ (H : ℤ) := by
    rw [← Int.natCast_natAbs]
    exact_mod_cast h
  obtain ⟨h₁,h₂⟩ := abs_le.mp ha
  have hz : z.val ≤ v.val + H := by omega
  have hv : v.val ≤ z.val + H := by omega
  have hl := Nat.div_le_div_right (c := H) hz
  have hr := Nat.div_le_div_right (c := H) hv
  rw [Nat.add_div_right _ hH] at hl hr
  simp only [giantTwoSidedPhysicalCell, Finset.mem_Icc]
  omega

end
end ArtinMatthews
