module

public import ArtinMatthews.MarkedPhysicalGoodPairingReverse


set_option backward.privateInPublic true
@[expose] public section

/-! Exact two-sided physical cutoff removal. Endpoint support absorbs q,
and reversal turns the target-bad term into a second source-bad term. -/

noncomputable section
namespace ArtinMatthews
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem markedPhysicalGoodVector_norm_le {Ω : Type*} (G : Ω → Prop) (f : Ω → ℂ) (s : Ω) :
    ‖markedPhysicalGoodVector G f s‖ ≤ ‖f s‖ := by
  by_cases hs : G s <;> simp [markedPhysicalGoodVector,hs]

theorem markedPhysicalEdgePairing_masked_endpoint_eq_one
    {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (hP : ∀ j p,p ∈ P j → p.Prime) (V : J → ℝ)
    (pads : ℕ) (Z : Finset (ℤ × ℤ)) (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q q : ℝ) (α β : ℕ → ℂ)
    (G H : MarkedPhysicalState P (pads+1) Z → Prop) :
    let f := fun s : MarkedPhysicalState P (pads+1) Z =>
      markedPhysicalEndpointVector P (pads+1) α β s.1.1.1
    markedPhysicalEdgePairing P hP V pads Z hZ ψ η d₀ Y Q q
      (markedPhysicalGoodVector G f) (markedPhysicalGoodVector H f) =
    markedPhysicalEdgePairing P hP V pads Z hZ ψ η d₀ Y Q 1
      (markedPhysicalGoodVector G f) (markedPhysicalGoodVector H f) := by
  dsimp only
  unfold markedPhysicalEdgePairing
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro t _
  by_cases hs : G s <;> by_cases ht : H t
  · simpa only [markedPhysicalGoodVector,ite_eq_left hs,ite_eq_left ht] using
      markedPhysicalEdgeCoefficient_damping_absorbed P hP V pads Z hZ ψ η d₀ Y Q q α β s t
  · simp only [markedPhysicalGoodVector,ite_eq_left hs,ite_eq_right ht,mul_zero]
  · simp only [markedPhysicalGoodVector,ite_eq_right hs,ite_eq_left ht,star_zero,mul_zero,zero_mul]
  · simp only [markedPhysicalGoodVector,ite_eq_right hs,ite_eq_right ht,star_zero,mul_zero]

theorem markedPhysicalEdgePairing_endpoint_eq_one
    {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (hP : ∀ j p,p ∈ P j → p.Prime) (V : J → ℝ)
    (pads : ℕ) (Z : Finset (ℤ × ℤ)) (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q q : ℝ) (α β : ℕ → ℂ) :
    let f := fun s : MarkedPhysicalState P (pads+1) Z =>
      markedPhysicalEndpointVector P (pads+1) α β s.1.1.1
    markedPhysicalEdgePairing P hP V pads Z hZ ψ η d₀ Y Q q f f =
      markedPhysicalEdgePairing P hP V pads Z hZ ψ η d₀ Y Q 1 f f := by
  dsimp only
  unfold markedPhysicalEdgePairing
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro t _
  exact markedPhysicalEdgeCoefficient_damping_absorbed P hP V pads Z hZ ψ η d₀ Y Q q α β s t

theorem markedPhysicalEdgePairing_good_removal_split
    {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (hP : ∀ j p,p ∈ P j → p.Prime) (V : J → ℝ)
    (pads : ℕ) (Z : Finset (ℤ × ℤ)) (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q q : ℝ) (α β : ℕ → ℂ)
    (G : MarkedPhysicalState P (pads+1) Z → Prop) :
    let f := fun s : MarkedPhysicalState P (pads+1) Z =>
      markedPhysicalEndpointVector P (pads+1) α β s.1.1.1
    markedPhysicalEdgePairing P hP V pads Z hZ ψ η d₀ Y Q q f f -
      markedPhysicalEdgePairing P hP V pads Z hZ ψ η d₀ Y Q q
        (markedPhysicalGoodVector G f) (markedPhysicalGoodVector G f) =
      markedPhysicalEdgePairing P hP V pads Z hZ ψ η d₀ Y Q 1 (markedPhysicalBadVector G f) f +
      markedPhysicalEdgePairing P hP V pads Z hZ ψ η d₀ Y Q 1
        (markedPhysicalGoodVector G f) (markedPhysicalBadVector G f) := by
  dsimp only
  rw [markedPhysicalEdgePairing_endpoint_eq_one P hP V pads Z hZ ψ η d₀ Y Q q α β,
    markedPhysicalEdgePairing_masked_endpoint_eq_one P hP V pads Z hZ ψ η d₀ Y Q q α β G G]
  rw [markedPhysicalEdgePairing_good_bad P hP V pads Z hZ ψ η d₀ Y Q 1 G]
  ring

theorem markedPhysicalEdgePairing_good_removal_bound
    {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (hP : ∀ j p,p ∈ P j → p.Prime)
    (hdis : Pairwise (fun i j => Disjoint (P i) (P j))) (V : J → ℝ)
    (pads : ℕ) (Z : Finset (ℤ × ℤ)) (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q q : ℝ) (α β : ℕ → ℂ)
    (G : MarkedPhysicalState P (pads+1) Z → Prop) :
    let f := fun s : MarkedPhysicalState P (pads+1) Z =>
      markedPhysicalEndpointVector P (pads+1) α β s.1.1.1
    ‖markedPhysicalEdgePairing P hP V pads Z hZ ψ η d₀ Y Q q f f -
      markedPhysicalEdgePairing P hP V pads Z hZ ψ η d₀ Y Q q
        (markedPhysicalGoodVector G f) (markedPhysicalGoodVector G f)‖ ≤
      markedPhysicalEdgeAbsolutePairing P hP V pads Z hZ ψ η d₀ Y Q 1 (markedPhysicalBadVector G f) f +
      markedPhysicalEdgeAbsolutePairing P hP V pads Z hZ (markedRawEdgeReflectedCutoff ψ) η d₀ Y Q 1
        (markedPhysicalBadVector G f) f := by
  dsimp only
  rw [markedPhysicalEdgePairing_good_removal_split P hP V pads Z hZ ψ η d₀ Y Q q α β G]
  apply (norm_add_le _ _).trans
  apply add_le_add
  · exact markedPhysicalEdgePairing_norm_le_absolute P hP V pads Z hZ ψ η d₀ Y Q 1 _ _
  · apply (markedPhysicalEdgePairing_norm_le_absolute P hP V pads Z hZ ψ η d₀ Y Q 1 _ _).trans
    rw [markedPhysicalEdgeAbsolutePairing_reverse P hP hdis V pads Z hZ ψ η d₀ Y Q 1]
    unfold markedPhysicalEdgeAbsolutePairing
    apply Finset.sum_le_sum
    intro s _
    apply Finset.sum_le_sum
    intro t _
    exact mul_le_mul_of_nonneg_left (markedPhysicalGoodVector_norm_le G _ t)
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))

end ArtinMatthews
