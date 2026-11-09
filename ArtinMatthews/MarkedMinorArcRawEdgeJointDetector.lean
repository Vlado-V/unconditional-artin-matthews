module

public import ArtinMatthews.MarkedMinorArcRawEdgeJointReverse
public import ArtinMatthews.MarkedMinorArcRawEdgeDetector


set_option backward.privateInPublic true
@[expose] public section

/-! The exact joint endpoint form of the literal delta/major detector
coefficient. Its reversal keeps the detector's orientation explicit. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def markedRawEdgeReverseDetector (D : ℤ → ℤ → ℤ → ℂ) (b a t : ℤ) : ℂ := D a b (-t)

def markedRawEdgeJointDetectorCoefficient {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (η : ℝ → ℂ) (d₀ Y ρ : ℝ)
    (χ : MarkedRawState P (pads+1) B Z → ℂ) (detector : ℤ → ℤ → ℤ → ℂ)
    (s t : MarkedRawState P (pads+1) B Z) : ℂ :=
  let a := ((markedRawActiveSplit pads) s.2.1).2
  let b := ((markedRawActiveSplit pads) t.2.1).2
  let D := markedRawCopiedProduct ((markedRawActiveSplit pads) s.2.1).1
  if d₀ ≤ (D : ℝ) ∧ (D : ℝ) < 2*d₀ then
    if (D : ℤ) ∣ markedMinorIntegerDet s.1.1 t.1.1 then
      if MarkedRawFullCrossBan s.2.1 b then 0 else
        ((d₀/(D : ℝ) : ℝ) : ℂ) * markedRawEndpointFactor hZ ρ χ s *
          η ((markedRawLastProduct a : ℝ)/Y) * η ((markedRawLastProduct b : ℝ)/Y) *
          detector (markedRawLastProduct a) (markedRawLastProduct b)
            (markedMinorIntegerDet s.1.1 t.1.1 / (D : ℤ)) * markedRawEndpointFactor hZ ρ χ t
    else 0 else 0

theorem markedRawEdgeChoiceDetectorCoefficient_eq_joint
    {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (η : ℝ → ℂ) (d₀ Y ρ : ℝ)
    (χ : MarkedRawState P (pads+1) B Z → ℂ) (detector : ℤ → ℤ → ℤ → ℂ)
    (s : MarkedRawState P (pads+1) B Z) (c : MarkedRawEdgeChoice hZ s) :
    markedRawEdgeChoiceDetectorCoefficient hZ η d₀ Y ρ χ detector s c =
      markedRawEdgeJointDetectorCoefficient hZ η d₀ Y ρ χ detector s (markedRawEdgeTargetState hZ s c) := by
  have hl : ((markedRawActiveSplit pads) (markedRawEdgeTargetState hZ s c).2.1).2 =
      markedRawEdgeTargetLast s.2.2 c.promotions c.fresh := by
    change ((markedRawActiveSplit pads) ((markedRawActiveSplit pads).symm _)).2 = _
    rw [Equiv.apply_symm_apply]
  unfold markedRawEdgeChoiceDetectorCoefficient markedRawEdgeJointDetectorCoefficient
  dsimp only
  rw [hl]
  split_ifs <;> try rfl
  rw [← markedRawEndpointFactor_damping hZ ρ χ s,
    ← markedRawEndpointFactor_damping hZ ρ χ (markedRawEdgeTargetState hZ s c)]
  ring

theorem markedRawEdgeJointDetectorCoefficient_source_permute
    {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (η : ℝ → ℂ) (d₀ Y ρ : ℝ)
    (χ : MarkedRawState P (pads+1) B Z → ℂ) (detector : ℤ → ℤ → ℤ → ℂ)
    (hχ : ∀ z a, MarkedRawMemorySymmetric (fun m => χ (z,(a,m))))
    (z : Z) (a : MarkedRawActive P (pads+1)) (m : MarkedRawMemory P B)
    (σ : (j : J) → Equiv.Perm (Fin (m.1.1 j : ℕ))) (t : MarkedRawState P (pads+1) B Z) :
    markedRawEdgeJointDetectorCoefficient hZ η d₀ Y ρ χ detector (z,(a,markedRawMemoryPermute m σ)) t =
      markedRawEdgeJointDetectorCoefficient hZ η d₀ Y ρ χ detector (z,(a,m)) t := by
  have he : markedRawEndpointFactor hZ ρ χ (z,(a,markedRawMemoryPermute m σ)) =
      markedRawEndpointFactor hZ ρ χ (z,(a,m)) := markedRawEndpointFactor_symmetric hZ ρ χ hχ z a m σ
  unfold markedRawEdgeJointDetectorCoefficient
  dsimp only
  rw [he]

theorem markedRawEdgeJointDetectorCoefficient_target_permute
    {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (η : ℝ → ℂ) (d₀ Y ρ : ℝ)
    (χ : MarkedRawState P (pads+1) B Z → ℂ) (detector : ℤ → ℤ → ℤ → ℂ)
    (hχ : ∀ z a, MarkedRawMemorySymmetric (fun m => χ (z,(a,m))))
    (s : MarkedRawState P (pads+1) B Z) (z : Z) (a : MarkedRawActive P (pads+1))
    (m : MarkedRawMemory P B) (σ : (j : J) → Equiv.Perm (Fin (m.1.1 j : ℕ))) :
    markedRawEdgeJointDetectorCoefficient hZ η d₀ Y ρ χ detector s (z,(a,markedRawMemoryPermute m σ)) =
      markedRawEdgeJointDetectorCoefficient hZ η d₀ Y ρ χ detector s (z,(a,m)) := by
  have he : markedRawEndpointFactor hZ ρ χ (z,(a,markedRawMemoryPermute m σ)) =
      markedRawEndpointFactor hZ ρ χ (z,(a,m)) := markedRawEndpointFactor_symmetric hZ ρ χ hχ z a m σ
  unfold markedRawEdgeJointDetectorCoefficient
  dsimp only
  rw [he]

theorem markedRawEdgeJointDetectorCoefficient_reverse
    {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hdisj : Pairwise (fun i j => Disjoint (P i) (P j)))
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (η : ℝ → ℂ) (d₀ Y ρ : ℝ)
    (χ : MarkedRawState P (pads+1) B Z → ℂ) (detector : ℤ → ℤ → ℤ → ℂ)
    (copied : MarkedRawActive P pads) (x y : Z) (a b : (j : J) → ↥(P j))
    (m n : MarkedRawMemory P B) :
    markedRawEdgeJointDetectorCoefficient hZ η d₀ Y ρ χ detector
      (x,((markedRawActiveSplit pads).symm (copied,a),m))
      (y,((markedRawActiveSplit pads).symm (copied,b),n)) =
      markedRawEdgeJointDetectorCoefficient hZ η d₀ Y ρ χ (markedRawEdgeReverseDetector detector)
        (y,((markedRawActiveSplit pads).symm (copied,b),n))
        (x,((markedRawActiveSplit pads).symm (copied,a),m)) := by
  classical
  let s : MarkedRawState P (pads+1) B Z := (x,((markedRawActiveSplit pads).symm (copied,a),m))
  let t : MarkedRawState P (pads+1) B Z := (y,((markedRawActiveSplit pads).symm (copied,b),n))
  have hs := Equiv.apply_symm_apply (markedRawActiveSplit (P := P) pads) (copied,a)
  have ht := Equiv.apply_symm_apply (markedRawActiveSplit (P := P) pads) (copied,b)
  unfold markedRawEdgeJointDetectorCoefficient
  rw [hs,ht]
  dsimp only
  have hdet : markedMinorIntegerDet y.1 x.1 = -markedMinorIntegerDet x.1 y.1 := by
    unfold markedMinorIntegerDet
    ring
  rw [hdet]
  simp only [dvd_neg]
  by_cases hsrc : markedRawEndpointFactor hZ ρ χ s = 0
  · split_ifs <;> simp only [s] at hsrc ⊢ <;> simp [hsrc]
  by_cases htgt : markedRawEndpointFactor hZ ρ χ t = 0
  · split_ifs <;> simp only [t] at htgt ⊢ <;> simp [htgt]
  have hban : MarkedRawFullCrossBan ((markedRawActiveSplit pads).symm (copied,a)) b ↔
      MarkedRawFullCrossBan ((markedRawActiveSplit pads).symm (copied,b)) a :=
    markedRawFullCrossBan_symmetric hdisj copied a b
      (markedRawEndpointFactor_ne_zero_distinct hZ ρ χ s hsrc)
      (markedRawEndpointFactor_ne_zero_distinct hZ ρ χ t htgt)
  simp only [hban]
  split_ifs with hdyad hdiv hbad <;> try rfl
  rw [Int.neg_ediv_of_dvd hdiv]
  simp only [markedRawEdgeReverseDetector, neg_neg]
  ring

theorem markedRawEdgeReverseDetector_delta (ψ : ℝ → ℂ) (Y : ℝ) :
    markedRawEdgeReverseDetector (markedRawEdgeDeltaDetector ψ Y) =
      markedRawEdgeDeltaDetector (fun u => ψ (-u)) Y := by
  funext b a t
  have h : -t = a-b ↔ t = b-a := by omega
  simp only [markedRawEdgeReverseDetector,markedRawEdgeDeltaDetector,Int.cast_neg,neg_div,h]

end
end ArtinMatthews
