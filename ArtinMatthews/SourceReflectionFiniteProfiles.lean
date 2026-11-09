module

public import ArtinMatthews.SourceReflectionExpansion


set_option backward.privateInPublic true
@[expose] public section

/-! A finite family of literal reflected profiles supplies one common
two-ended estimate even when individual small-scale exponents differ. -/
namespace ArtinMatthews.SourceEulerAssembly

open NumberField IsDedekindDomain
open scoped NumberField BigOperators ContDiff
noncomputable section

theorem sourceReflectionFiniteProfiles_derivatives
    {V : Type*} [Fintype V] [Nonempty V] (P : V → ℝ → ℂ)
    (hP : ∀ v : V, ∃ α : ℝ, 0 ≤ α ∧ ∀ A : ℝ, 0 < A →
      ∃ M : ℝ, 0 ≤ M ∧ ∀ k ≤ 2, ∀ x : ℝ,
        ‖iteratedFDeriv ℝ k (fun y => P v (Real.exp y)) x‖ ≤
          M * min (Real.exp (α*x)) (Real.exp (-A*x))) :
    ∃ α : ℝ, 0 ≤ α ∧ ∀ A : ℝ, 0 < A →
      ∃ M : ℝ, 0 ≤ M ∧ ∀ v : V, ∀ k ≤ 2, ∀ x : ℝ,
        ‖iteratedFDeriv ℝ k (fun y => P v (Real.exp y)) x‖ ≤
          M * min (Real.exp (α*x)) (Real.exp (-A*x)) := by
  classical
  choose αv hαv hv using hP
  let α := Finset.univ.inf' Finset.univ_nonempty αv
  have hα : 0 ≤ α := Finset.le_inf' _ _ (fun v _ => hαv v)
  refine ⟨α,hα,fun A hA => ?_⟩
  choose M hM hbound using fun v => hv v A hA
  refine ⟨∑ v, M v, Finset.sum_nonneg (fun v _ => hM v), fun v k hk x => ?_⟩
  have hvα : α ≤ αv v := Finset.inf'_le _ (Finset.mem_univ v)
  have hweight : min (Real.exp (αv v*x)) (Real.exp (-A*x)) ≤
      min (Real.exp (α*x)) (Real.exp (-A*x)) := by
    refine le_min ?_ (min_le_right _ _)
    by_cases hx : x ≤ 0
    · exact (min_le_left _ _).trans
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_right hvα hx))
    · have hx₀ : 0 ≤ x := (lt_of_not_ge hx).le
      exact (min_le_right _ _).trans (Real.exp_le_exp.mpr
        ((mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hA.le) hx₀).trans (mul_nonneg hα hx₀)))
  exact (hbound v k hk x).trans ((mul_le_mul_of_nonneg_left hweight (hM v)).trans
    (mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun v _ => hM v) (Finset.mem_univ v))
      (le_min (Real.exp_pos _).le (Real.exp_pos _).le)))

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
local notation "Prime" => SourceExteriorPrime F S₀
local notation "E" => SourcePrimeExponents F S₀

def sourceReflectionExpansionData_of_finiteProfiles
    {U V : Type} [Fintype V] [Nonempty V]
    (scalar : E → Finset Prime → E → E → U → ℂ)
    (row column : E → Finset Prime → E → E → U → E → ℂ)
    (P : V → ℝ → ℂ) (index : E → Finset Prime → E → E → U → V)
    (hscalar : ∀ h f a n u, ‖scalar h f a n u‖ ≤ sourceReflectionFrozenWeight F S₀ f a)
    (hrow : ∀ h f a n u d, ‖row h f a n u d‖ ≤ 1)
    (hcolumn : ∀ h f a n u c, ‖column h f a n u c‖ ≤ 1)
    (hsmooth : ∀ v : V, ContDiff ℝ ∞ (fun x : ℝ => P v (Real.exp x)))
    (hP : ∀ v : V, ∃ α : ℝ, 0 ≤ α ∧ ∀ A : ℝ, 0 < A →
      ∃ M : ℝ, 0 ≤ M ∧ ∀ k ≤ 2, ∀ x : ℝ,
        ‖iteratedFDeriv ℝ k (fun y => P v (Real.exp y)) x‖ ≤
          M * min (Real.exp (α*x)) (Real.exp (-A*x))) :
    SourceReflectionExpansionData F S₀ U where
  scalar := scalar
  row := row
  column := column
  profile h f a n u := P (index h f a n u)
  scalar_bound := hscalar
  row_bound := hrow
  column_bound := hcolumn
  profile_smooth h f a n u := hsmooth (index h f a n u)
  profile_derivative := by
    obtain ⟨α,hα,hA⟩ := sourceReflectionFiniteProfiles_derivatives P hP
    refine ⟨α,hα,fun A hA₀ => ?_⟩
    obtain ⟨M,hM,hbound⟩ := hA A hA₀
    exact ⟨M,hM,fun h f a n u k hk x => hbound (index h f a n u) k hk x⟩

end
end ArtinMatthews.SourceEulerAssembly
