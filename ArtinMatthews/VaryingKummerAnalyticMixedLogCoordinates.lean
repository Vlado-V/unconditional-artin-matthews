module

public import ArtinMatthews.VaryingKummerAnalyticMixedLattice
public import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem


set_option backward.privateInPublic true
@[expose] public section

/-! The actual Dirichlet unit logarithm, lifted to mixed real/complex Gaussian
coordinates. Complex places have two real coordinates and weight one half. -/

namespace ArtinMatthews.VaryingKummerAnalytic

open Module NumberField NumberField.mixedEmbedding
open NumberField.Units NumberField.Units.dirichletUnitTheorem
open scoped NumberField nonZeroDivisors Classical BigOperators

noncomputable section

variable (K : Type*) [Field K] [NumberField K]
variable (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)

/-- Restore the omitted distinguished place so that the full logarithmic sum is zero. -/
def mixedRestoredPlaceLog (u : logSpace K) (w : InfinitePlace K) : ℝ :=
  if h : w = w₀ then -∑ v, u v else u ⟨w, h⟩

theorem mixedRestoredPlaceLog_sum (u : logSpace K) :
    ∑ w, mixedRestoredPlaceLog K u w = 0 := by
  rw [Fintype.sum_eq_add_sum_subtype_ne _ w₀]
  have hzero : mixedRestoredPlaceLog K u w₀ = -∑ v, u v := by
    simp [mixedRestoredPlaceLog]
  have hne (v : {w : InfinitePlace K // w ≠ w₀}) :
      mixedRestoredPlaceLog K u v = u v := by
    simp only [mixedRestoredPlaceLog, dite_eq_right v.property]
  rw [hzero]
  simp_rw [hne]
  exact neg_add_cancel _

theorem mixedRestoredPlaceLog_continuous (w : InfinitePlace K) :
    Continuous (fun u : logSpace K => mixedRestoredPlaceLog K u w) := by
  unfold mixedRestoredPlaceLog
  split_ifs <;> fun_prop

/-- At an actual unit logarithm, the restored coordinate is the weighted
archimedean logarithm, including the omitted distinguished place. -/
theorem mixedRestoredPlaceLog_unit (u : (𝓞 K)ˣ) (w : InfinitePlace K) :
    mixedRestoredPlaceLog K (logEmbedding K (Additive.ofMul u)) w =
      InfinitePlace.mult w * Real.log (w (u : K)) := by
  by_cases hw : w = w₀
  · subst w
    rw [mixedRestoredPlaceLog, dite_eq_left rfl, sum_logEmbedding_component]
    ring
  · simp only [mixedRestoredPlaceLog, dite_eq_right hw, logEmbedding_component]

/-- The logarithmic scaling at one standard real coordinate of the mixed space. -/
def mixedStandardLogScale (u : logSpace K) : mixedEmbedding.index K → ℝ
  | .inl w => mixedRestoredPlaceLog K u w
  | .inr w => mixedRestoredPlaceLog K u w.1 / 2

theorem mixedStandardLogScale_sum (u : logSpace K) :
    ∑ j, mixedStandardLogScale K u j = 0 := by
  rw [Fintype.sum_sum_type]
  change (∑ w : {w : InfinitePlace K // InfinitePlace.IsReal w}, mixedRestoredPlaceLog K u w) +
    (∑ j : {w : InfinitePlace K // InfinitePlace.IsComplex w} × Fin 2,
      mixedRestoredPlaceLog K u j.1 / 2) = 0
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_ofNat]
  simp only [show ∀ r : ℝ, 2 * (r / 2) = r by intro r; ring]
  rw [← InfinitePlace.sum_eq_sum_add_sum]
  exact mixedRestoredPlaceLog_sum K u

/-- The same scaling in the actual ideal-basis orthonormal coordinate ordering. -/
def mixedIdealLogScale (u : logSpace K) (j : MixedIdealIndex K I) : ℝ :=
  mixedStandardLogScale K u (mixedIdealIndexEquiv K I j)

theorem mixedIdealLogScale_sum (u : logSpace K) :
    ∑ j, mixedIdealLogScale K I u j = 0 := by
  unfold mixedIdealLogScale
  rw [(mixedIdealIndexEquiv K I).sum_comp]
  exact mixedStandardLogScale_sum K u

theorem mixedIdealLogScale_continuous (j : MixedIdealIndex K I) :
    Continuous (fun u : logSpace K => mixedIdealLogScale K I u j) := by
  unfold mixedIdealLogScale mixedStandardLogScale
  split
  · exact mixedRestoredPlaceLog_continuous K _
  · exact (mixedRestoredPlaceLog_continuous K _).div_const _

/-- The averaging domain is the actual Dirichlet unit lattice fundamental domain. -/
def mixedUnitLogDomain : Set (logSpace K) :=
  ZSpan.fundamentalDomain ((basisUnitLattice K).ofZLatticeBasis ℝ (unitLattice K))

theorem mixedUnitLogDomain_measurable : MeasurableSet (mixedUnitLogDomain K) :=
  ZSpan.fundamentalDomain_measurableSet _

theorem mixedUnitLogDomain_bounded : Bornology.IsBounded (mixedUnitLogDomain K) :=
  ZSpan.fundamentalDomain_isBounded _

end
end ArtinMatthews.VaryingKummerAnalytic
