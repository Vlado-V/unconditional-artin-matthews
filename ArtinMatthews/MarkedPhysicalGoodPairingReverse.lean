module

public import ArtinMatthews.MarkedPhysicalGoodPairing
public import ArtinMatthews.MarkedMinorArcRawEdgeJointReverse


set_option backward.privateInPublic true
@[expose] public section

/-! Exact absolute reversal of the original physical one-edge pairing.
This turns a target-bad contribution into a source-bad contribution with
the reflected Schwartz cutoff, retaining the physical normalization. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem markedRawEdgeJointCoefficient_norm_reverse_of_copied
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hdisj : Pairwise (fun i j => Disjoint (P i) (P j)))
    (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q ρ : ℝ) (χ : MarkedRawState P (pads+1) B Z → ℂ)
    (s t : MarkedRawState P (pads+1) B Z)
    (hcopy : ((markedRawActiveSplit pads) s.2.1).1 = ((markedRawActiveSplit pads) t.2.1).1) :
    ‖markedRawEdgeJointCoefficient hZ ψ η d₀ Y Q ρ χ s t‖ =
      ‖markedRawEdgeJointCoefficient hZ (markedRawEdgeReflectedCutoff ψ) η d₀ Y Q ρ χ t s‖ := by
  let copied := ((markedRawActiveSplit pads) s.2.1).1
  let a := ((markedRawActiveSplit pads) s.2.1).2
  let b := ((markedRawActiveSplit pads) t.2.1).2
  have hs : (s.1,((markedRawActiveSplit pads).symm (copied,a),s.2.2)) = s := by
    change (s.1,((markedRawActiveSplit pads).symm ((markedRawActiveSplit pads) s.2.1),s.2.2)) = s
    rw [Equiv.symm_apply_apply]
  have ht : (t.1,((markedRawActiveSplit pads).symm (copied,b),t.2.2)) = t := by
    dsimp only [copied,b]
    rw [hcopy]
    change (t.1,((markedRawActiveSplit pads).symm ((markedRawActiveSplit pads) t.2.1),t.2.2)) = t
    rw [Equiv.symm_apply_apply]
  have h := markedRawEdgeJointCoefficient_norm_reverse hdisj hZ ψ η d₀ Y Q ρ χ
    copied s.1 t.1 a b s.2.2 t.2.2
  rwa [hs,ht] at h

theorem markedPhysicalEdgeCoefficient_norm_reverse
    {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (hP : ∀ j p,p ∈ P j → p.Prime)
    (hdisj : Pairwise (fun i j => Disjoint (P i) (P j))) (V : J → ℝ)
    (pads : ℕ) (Z : Finset (ℤ × ℤ)) (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q q : ℝ)
    (s t : MarkedPhysicalState P (pads+1) Z) :
    ‖markedPhysicalEdgeCoefficient P hP V pads Z hZ ψ η d₀ Y Q q s t‖ =
      ‖markedPhysicalEdgeCoefficient P hP V pads Z hZ (markedRawEdgeReflectedCutoff ψ) η d₀ Y Q q t s‖ := by
  have hd : Pairwise (fun i j => Disjoint (markedRawPrimeBand (P i)) (markedRawPrimeBand (P j))) := by
    intro i j hij
    apply Finset.disjoint_left.mpr
    intro p hp hq
    exact (Finset.disjoint_left.mp (hdisj hij)) ((mem_markedRawPrimeBand _ _).mp hp)
      ((mem_markedRawPrimeBand _ _).mp hq)
  unfold markedPhysicalEdgeCoefficient
  dsimp only
  by_cases hc : ((markedRawActiveSplit pads) (markedPhysicalStateToRaw P hP (pads+1) Z s).2.1).1 =
      ((markedRawActiveSplit pads) (markedPhysicalStateToRaw P hP (pads+1) Z t).2.1).1
  · rw [ite_eq_left hc,ite_eq_left hc.symm]
    simp only [norm_mul]
    rw [markedRawEdgeJointCoefficient_norm_reverse_of_copied hd hZ ψ η d₀ Y Q 1 (fun _ => 1) _ _ hc]
    ring
  · rw [ite_eq_right hc,ite_eq_right (Ne.symm hc)]

def markedPhysicalEdgeAbsolutePairing {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (hP : ∀ j p,p ∈ P j → p.Prime) (V : J → ℝ)
    (pads : ℕ) (Z : Finset (ℤ × ℤ)) (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q q : ℝ)
    (f g : MarkedPhysicalState P (pads+1) Z → ℂ) : ℝ :=
  ∑ s,∑ t,‖markedPhysicalEdgeCoefficient P hP V pads Z hZ ψ η d₀ Y Q q s t‖*‖f s‖*‖g t‖

theorem markedPhysicalEdgePairing_norm_le_absolute
    {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (hP : ∀ j p,p ∈ P j → p.Prime) (V : J → ℝ)
    (pads : ℕ) (Z : Finset (ℤ × ℤ)) (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q q : ℝ)
    (f g : MarkedPhysicalState P (pads+1) Z → ℂ) :
    ‖markedPhysicalEdgePairing P hP V pads Z hZ ψ η d₀ Y Q q f g‖ ≤
      markedPhysicalEdgeAbsolutePairing P hP V pads Z hZ ψ η d₀ Y Q q f g := by
  unfold markedPhysicalEdgePairing markedPhysicalEdgeAbsolutePairing
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro s _
  simpa only [norm_mul,norm_star] using norm_sum_le Finset.univ
    (fun t => markedPhysicalEdgeCoefficient P hP V pads Z hZ ψ η d₀ Y Q q s t * star (f s) * g t)

theorem markedPhysicalEdgeAbsolutePairing_reverse
    {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (hP : ∀ j p,p ∈ P j → p.Prime)
    (hdisj : Pairwise (fun i j => Disjoint (P i) (P j))) (V : J → ℝ)
    (pads : ℕ) (Z : Finset (ℤ × ℤ)) (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q q : ℝ)
    (f g : MarkedPhysicalState P (pads+1) Z → ℂ) :
    markedPhysicalEdgeAbsolutePairing P hP V pads Z hZ ψ η d₀ Y Q q f g =
      markedPhysicalEdgeAbsolutePairing P hP V pads Z hZ (markedRawEdgeReflectedCutoff ψ) η d₀ Y Q q g f := by
  unfold markedPhysicalEdgeAbsolutePairing
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro t _
  rw [markedPhysicalEdgeCoefficient_norm_reverse P hP hdisj V pads Z hZ ψ η d₀ Y Q q]
  ring

end
end ArtinMatthews
