module

public import ArtinMatthews.GiantPhysicalDyadicPartition
public import ArtinMatthews.GiantTwoSidedPhysicalResidualExpansion


set_option backward.privateInPublic true
@[expose] public section

/-! The cutoff sum splits by the left endpoint into the same dyads as
the physical moment bound. A dyad below the cutoff support contributes zero. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {I J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset ℕ}
  {k ell : ℕ} {Z : Finset ℕ}

def giantPhysicalDyadicLeft (X : ℝ) (f : ℕ → ℂ) (n : ℕ) : ℂ :=
  if n ∈ giantTwoSidedRootInterval X then f n else 0

theorem giantTwoSidedPhysicalCutoffPairing_eq_dyadic
    (patterns : Finset I) (C : I → J → Finset (Fin k)) (step : ℤ) (q ζ : ℝ)
    (K : ∀ p, GiantTwoSidedPatternCoefficient P (C p) ell) (Ψ : ℝ → ℂ) (x : ℝ)
    (f : ℕ → ℂ) (g : GiantTwoSidedEndpointState P (k+ell) Z → ℂ) (N : ℕ)
    (hZ : Z ⊆ Ioc 0 N) :
    giantTwoSidedPhysicalCutoffPairing patterns C step q ζ K Ψ x f g =
      ∑ j ∈ range (Nat.log 2 N + 1),
        giantTwoSidedPhysicalCutoffPairing patterns C step q ζ K Ψ x
          (giantPhysicalDyadicLeft ((2 ^ j : ℕ) : ℝ) f) g := by
  let State := GiantTwoSidedEndpointState P (k+ell) Z
  let Choice := GiantTwoSidedResidueEdgeChoice (P := P) patterns C ell
  let Edge := Choice × State × State
  letI : Fintype Edge := inferInstanceAs (Fintype
    (GiantTwoSidedResidueEdgeChoice (P := P) patterns C ell ×
      GiantTwoSidedEndpointState P (k+ell) Z × GiantTwoSidedEndpointState P (k+ell) Z))
  let pos (e : Edge) := e.2.1.val.1.val
  let μ : ℂ := (markedPhysicalMass (fun j => bandReciprocalMass (P j)) (k+ell) : ℂ)*
    (giantTwoSidedResidueSlotNormalization (J := J) (k+ell) : ℂ)
  let A (u : ℕ → ℂ) (e : Edge) :=
    giantTwoSidedPhysicalChoiceCoefficient step q ζ K e.1 e.2.1 e.2.2 *
      (Ψ ((pos e : ℝ) / (x * (giantTwoSidedPhysicalChoiceDilation e.1 e.2.1 : ℝ))) /
        (pos e : ℂ)) * star (u (pos e)) * g e.2.2
  have he (u : ℕ → ℂ) : giantTwoSidedPhysicalCutoffPairing patterns C step q ζ K Ψ x u g =
      μ * ∑ e : Edge, A u e := by
    simp only [giantTwoSidedPhysicalCutoffPairing, Edge, Choice, State, Fintype.sum_prod_type] <;> rfl
  have hblock (j : ℕ) :
      (∑ e ∈ (univ : Finset Edge).filter (fun e =>
          pos e ∈ giantTwoSidedRootInterval ((2 ^ j : ℕ) : ℝ)), A f e) =
        ∑ e : Edge, A (giantPhysicalDyadicLeft ((2 ^ j : ℕ) : ℝ) f) e := by
    rw [sum_filter]
    apply sum_congr rfl
    intro e _
    by_cases h : pos e ∈ giantTwoSidedRootInterval ((2 ^ j : ℕ) : ℝ)
    · simp only [h, ite_true, A, giantPhysicalDyadicLeft]
    · simp only [h, ite_false, A, giantPhysicalDyadicLeft, star_zero, mul_zero, zero_mul]
  calc
    _ = μ * ∑ e : Edge, A f e := he f
    _ = μ * ∑ j ∈ range (Nat.log 2 N + 1),
          ∑ e ∈ (univ : Finset Edge).filter (fun e =>
            pos e ∈ giantTwoSidedRootInterval ((2 ^ j : ℕ) : ℝ)), A f e := by
      rw [giantPhysicalDyadic_partition univ pos (A f) N
        (fun e _ => (mem_Ioc.mp (hZ e.2.1.val.1.property)).1)
        (fun e _ => (mem_Ioc.mp (hZ e.2.1.val.1.property)).2)]
    _ = _ := by simp only [mul_sum, hblock, he]

theorem giantTwoSidedPhysicalPatternCutoffPairing_eq_dyadic
    (C : J → Finset (Fin k)) (step : ℤ) (q ζ : ℝ)
    (K : GiantTwoSidedPatternCoefficient P C ell) (Ψ : ℝ → ℂ) (x : ℝ)
    (f : ℕ → ℂ) (g : GiantTwoSidedEndpointState P (k+ell) Z → ℂ) (N : ℕ)
    (hZ : Z ⊆ Ioc 0 N) :
    giantTwoSidedPhysicalPatternCutoffPairing C step q ζ K Ψ x f g =
      ∑ j ∈ range (Nat.log 2 N + 1),
        giantTwoSidedPhysicalPatternCutoffPairing C step q ζ K Ψ x
          (giantPhysicalDyadicLeft ((2 ^ j : ℕ) : ℝ) f) g := by
  simpa only [giantTwoSidedPhysicalCutoffPairing_sum_patterns, sum_singleton] using
    giantTwoSidedPhysicalCutoffPairing_eq_dyadic ({()} : Finset Unit) (fun _ => C) step q ζ
      (fun _ => K) Ψ x f g N hZ

theorem giantTwoSidedPhysicalCutoffPairing_dyadic_eq_zero
    (hP : ∀ j p, p ∈ P j → p.Prime)
    (patterns : Finset I) (C : I → J → Finset (Fin k)) (step : ℤ) (q ζ : ℝ)
    (K : ∀ p, GiantTwoSidedPatternCoefficient P (C p) ell) (Ψ : ℝ → ℂ)
    {x a X : ℝ} (hx : 0 < x) (ha : 0 < a) (hsmall : 2 * X ≤ a * x)
    (hΨ : ∀ t < a, Ψ t = 0) (f : ℕ → ℂ)
    (g : GiantTwoSidedEndpointState P (k+ell) Z → ℂ) :
    giantTwoSidedPhysicalCutoffPairing patterns C step q ζ K Ψ x
      (giantPhysicalDyadicLeft X f) g = 0 := by
  unfold giantTwoSidedPhysicalCutoffPairing
  rw [Finset.sum_eq_zero, mul_zero]
  intro c _
  apply Finset.sum_eq_zero
  intro s _
  apply Finset.sum_eq_zero
  intro t _
  by_cases hs : s.val.1.val ∈ giantTwoSidedRootInterval X
  · have hD : 0 < giantTwoSidedPhysicalChoiceDilation c s :=
      giantTwoSidedPhysicalChoiceDilation_pos hP c s
    have hD' : (1 : ℝ) ≤ (giantTwoSidedPhysicalChoiceDilation c s : ℝ) := by
      exact_mod_cast hD
    have harg : (s.val.1.val : ℝ) / (x * (giantTwoSidedPhysicalChoiceDilation c s : ℝ)) < a := by
      apply (div_lt_iff₀ (mul_pos hx (Nat.cast_pos.mpr hD))).mpr
      calc
        (s.val.1.val : ℝ) < 2 * X := (giantTwoSidedRootInterval_bounds hs).2
        _ ≤ a * x := hsmall
        _ ≤ a * (x * (giantTwoSidedPhysicalChoiceDilation c s : ℝ)) :=
          mul_le_mul_of_nonneg_left (le_mul_of_one_le_right hx.le hD') ha.le
    simp only [hΨ _ harg, zero_div, mul_zero, zero_mul]
  · simp only [giantPhysicalDyadicLeft, hs, ite_false, star_zero, mul_zero, zero_mul]

theorem giantTwoSidedPhysicalPatternCutoffPairing_dyadic_eq_zero
    (hP : ∀ j p, p ∈ P j → p.Prime)
    (C : J → Finset (Fin k)) (step : ℤ) (q ζ : ℝ)
    (K : GiantTwoSidedPatternCoefficient P C ell) (Ψ : ℝ → ℂ)
    {x a X : ℝ} (hx : 0 < x) (ha : 0 < a) (hsmall : 2 * X ≤ a * x)
    (hΨ : ∀ t < a, Ψ t = 0) (f : ℕ → ℂ)
    (g : GiantTwoSidedEndpointState P (k+ell) Z → ℂ) :
    giantTwoSidedPhysicalPatternCutoffPairing C step q ζ K Ψ x
      (giantPhysicalDyadicLeft X f) g = 0 := by
  simpa only [giantTwoSidedPhysicalCutoffPairing_sum_patterns, sum_singleton] using
    giantTwoSidedPhysicalCutoffPairing_dyadic_eq_zero hP ({()} : Finset Unit) (fun _ => C)
      step q ζ (fun _ => K) Ψ hx ha hsmall hΨ f g

end
end ArtinMatthews
