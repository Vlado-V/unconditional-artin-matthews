module

public import ArtinMatthews.GiantTwoSidedRootWeight
public import Mathlib.Analysis.Fourier.AddCircle


set_option backward.privateInPublic true
@[expose] public section

/-! The actual integer return is the zero Fourier coefficient of the
signed displacement. All lengths, list sizes and steps remain arbitrary. -/
namespace ArtinMatthews
open MeasureTheory Finset
open scoped BigOperators
noncomputable section

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

theorem giantTwoSidedFourier_integral (d : ℤ) :
    (∫ θ : AddCircle (1 : ℝ), fourier d θ ∂AddCircle.haarAddCircle) =
      if d = 0 then 1 else 0 := by
  classical
  by_cases hd : d = 0
  · simp [hd]
  · rw [ite_eq_right hd]
    exact integral_eq_zero_of_add_right_eq_neg (μ := AddCircle.haarAddCircle)
      (fourier_add_half_inv_index hd (by norm_num : (0 : ℝ) < 1))

theorem giantTwoSidedFourier_norm (d : ℤ) (θ : AddCircle (1 : ℝ)) :
    ‖fourier d θ‖ = 1 := Circle.norm_coe _

theorem giantTwoSidedFourier_sum {ι : Type*} (s : Finset ι) (d : ι → ℤ)
    (θ : AddCircle (1 : ℝ)) :
    fourier (∑ i ∈ s, d i) θ = ∏ i ∈ s, fourier (d i) θ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [sum_empty, prod_empty, fourier_zero]
  | @insert i s hi ih =>
      rw [sum_insert hi, prod_insert hi, fourier_add, ih]

theorem giantTwoSidedPathOffset_last {n : ℕ} (d : Fin n → ℤ) :
    giantTwoSidedPathOffset d (Fin.last n) = ∑ i, d i := by
  simp [giantTwoSidedPathOffset]

theorem giantTwoSidedFourier_path_product {n : ℕ} (d : Fin n → ℤ)
    (θ : AddCircle (1 : ℝ)) :
    fourier (giantTwoSidedPathOffset d (Fin.last n)) θ =
      ∏ i, fourier (d i) θ := by
  rw [giantTwoSidedPathOffset_last, giantTwoSidedFourier_sum]

theorem giantTwoSidedFourier_unitInterval (d : ℤ) :
    (∫ θ in (0 : ℝ)..1, fourier d (θ : AddCircle (1 : ℝ))) =
      if d = 0 then 1 else 0 := by
  have h := fourierCoeff_eq_intervalIntegral
    (fun θ : AddCircle (1 : ℝ) => fourier d θ) 0 0
  simp only [fourierCoeff, neg_zero, fourier_zero, one_smul,
    div_one, zero_add] at h
  rw [← h, giantTwoSidedFourier_integral]

theorem giantTwoSidedPhysicalReturn_fourier {J : Type*} [Fintype J]
    {P : J → Finset ℕ} {k ell n : ℕ} {C : Fin n → J → Finset (Fin k)}
    {Z : Finset ℕ} (s : Fin (n + 1) → GiantTwoSidedEndpointState P (k + ell) Z)
    (π τ : Fin n → J → Equiv.Perm (Fin (k + ell)))
    (aux : ∀ i, GiantTwoSidedPatternAuxiliary P (C i)) (step : Fin n → ℤ)
    (hs : ∀ i, GiantTwoSidedPatternCondition (C i) (step i)
      (giantTwoSidedEndpointPermute (π i) (s i.castSucc))
      (giantTwoSidedEndpointPermute (τ i) (s i.succ)) (aux i)) :
    (∫ θ : AddCircle (1 : ℝ),
      ∏ i, fourier (giantTwoSidedPatternPathIncrement s π aux step i) θ
        ∂AddCircle.haarAddCircle) =
      if (s (Fin.last n)).val.1.val = (s 0).val.1.val then 1 else 0 := by
  classical
  simp_rw [← giantTwoSidedFourier_path_product]
  rw [giantTwoSidedFourier_integral]
  simp only [← giantTwoSidedPatternPath_return_iff s π τ aux step hs]

end
end ArtinMatthews
