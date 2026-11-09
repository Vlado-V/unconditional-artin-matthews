module

public import ArtinMatthews.PositiveDensityCubicRamification
public import ArtinMatthews.PositiveDensityCubicProgression


set_option backward.privateInPublic true
@[expose] public section

/-! The selected statistic on the actual split progression uses precisely
the unramified Frobenius gate. The comparison retains the shifted weight,
the unit-class restriction and the giant-prime divisor count. -/

noncomputable section
namespace ArtinMatthews

open Filter
open scoped BigOperators Topology

theorem giantSelectedPrimeTest_cubic_frobenius_eventually {S : Finset ℤ}
    (hS : AdmissibleBases S) {u : ℕ} (hprog : IsQuadraticProgressionFor S u 1)
    (Y : ℕ) (ε : ℝ) (Φ : ℝ → ℝ) (hΦ : ∀ t, 0 ≤ Φ t ∧ Φ t ≤ 1)
    {T : ℝ} (hT₁ : 1 < T) (hT₂ : T < 2) (hs : Function.support Φ ⊆ Set.Ioo 1 T) :
    let U := giantSieveEnlargedUnits hprog Y
    ∀ᶠ x : ℝ in atTop,
      giantSelectedPrimeTest U (giantCubicSieveSelection S (giantCubicRamifiedPrimes S)) ε Φ T x =
        giantSelectedPrimeTest U (giantCubicFrobeniusSelection S) ε Φ T x := by
  classical
  let U := giantSieveEnlargedUnits hprog Y
  filter_upwards [giantSieveCandidates_structural_eventually hS U (fun _ => True) ε Φ
    hΦ hT₁ hT₂ hs] with x hx
  unfold giantSelectedPrimeTest
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hU : ∃ v ∈ U, (v : ZMod
      (enlargedModulus (quadraticModulus S) (giantSieveNewPrimes S Y))) = p
  · by_cases hw : giantSieveWeight Φ x p = 0
    · simp only [hw, Complex.ofReal_zero, zero_mul, ite_self]
    · by_cases hg : (giantPrimeFactors (p - 1) x ε).Nonempty
      · have hpU : p ∈ giantSieveCandidates U (fun _ => True) ε Φ T x :=
          mem_giantSieveCandidates.mpr ⟨hp, hU, trivial, hw, hg⟩
        have hp' := hx p hpU
        have hp₃ := (giantSieve_enlarged_prime_conditions hprog hp'.1 hU).2.1
        rw [giantCubicFrobeniusSelection_iff hp'.1 hp₃ hp'.2.2.1]
      · simp only [Finset.not_nonempty_iff_eq_empty.mp hg, Finset.card_empty,
          Nat.cast_zero, Complex.ofReal_zero, mul_zero, ite_self]
  · have hz : giantUnitResidueIndicator (giantSieveEnlargedUnits hprog Y) p = 0 := by
      unfold giantUnitResidueIndicator
      exact ite_eq_right (fun h => hU (Finset.mem_image.mp h))
    simp only [hz, mul_zero, zero_mul, ite_self]

end ArtinMatthews
