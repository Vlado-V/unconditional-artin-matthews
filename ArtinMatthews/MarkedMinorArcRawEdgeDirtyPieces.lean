module

public import ArtinMatthews.MarkedMinorArcRawEdgeSectorTranspose
public import ArtinMatthews.MarkedMinorArcDirtyGoodCutoff


set_option backward.privateInPublic true
@[expose] public section

/-! Actual good/error endpoint pieces.  The good event is the literal
first-good plus full smaller-band beta-root condition; reversal exchanges
the two endpoint flags and keeps every source/target gate visible. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def markedRawEdgeEndpointPiece {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (G : MarkedRawState P (pads+1) B Z → Prop) (left right : Bool)
    (A : MarkedRawEdgePatternKernel P pads B Z) : MarkedRawEdgePatternKernel P pads B Z :=
  fun p q s t => if decide (G s) = left ∧ decide (G t) = right then A p q s t else 0

theorem markedRawEdgeEndpointPiece_reverse {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (G : MarkedRawState P (pads+1) B Z → Prop) (left right : Bool)
    (A : MarkedRawEdgePatternKernel P pads B Z) :
    markedRawEdgePatternReverse (markedRawEdgeEndpointPiece G left right A) =
      markedRawEdgeEndpointPiece G right left (markedRawEdgePatternReverse A) := by
  funext p q s t
  simp only [markedRawEdgePatternReverse, markedRawEdgeEndpointPiece, and_comm]

/-- Good-good, source-bad, and source-good/target-bad sum to the original
kernel. The source-bad term includes both target statuses. -/
theorem markedRawEdgeEndpointPiece_partition {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (G : MarkedRawState P (pads+1) B Z → Prop) (A : MarkedRawEdgePatternKernel P pads B Z)
    (p q : J → Bool) (s t : MarkedRawState P (pads+1) B Z) :
    A p q s t = markedRawEdgeEndpointPiece G true true A p q s t +
      (markedRawEdgeEndpointPiece G false false A p q s t +
        markedRawEdgeEndpointPiece G false true A p q s t) +
      markedRawEdgeEndpointPiece G true false A p q s t := by
  by_cases hs : G s <;> by_cases ht : G t <;> simp [markedRawEdgeEndpointPiece,hs,ht]

theorem markedRawEndpointFactor_cutoff {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {M B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (ρ : ℝ)
    (G : MarkedRawState P M B Z → Prop) (χ : MarkedRawState P M B Z → ℂ)
    (s : MarkedRawState P M B Z) :
    markedRawEndpointFactor hZ ρ (fun s => if G s then χ s else 0) s =
      if G s then markedRawEndpointFactor hZ ρ χ s else 0 := by
  unfold markedRawEndpointFactor
  by_cases hg : G s <;> by_cases hd : MarkedRawActiveDistinct s.2.1 <;> simp [hg,hd]

theorem markedRawEdgeJointDetectorCoefficient_cutoff
    {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (η : ℝ → ℂ) (d₀ Y ρ : ℝ)
    (G : MarkedRawState P (pads+1) B Z → Prop)
    (χ : MarkedRawState P (pads+1) B Z → ℂ) (D : ℤ → ℤ → ℤ → ℂ)
    (s t : MarkedRawState P (pads+1) B Z) :
    markedRawEdgeJointDetectorCoefficient hZ η d₀ Y ρ (fun s => if G s then χ s else 0) D s t =
      if G s ∧ G t then markedRawEdgeJointDetectorCoefficient hZ η d₀ Y ρ χ D s t else 0 := by
  unfold markedRawEdgeJointDetectorCoefficient
  simp only [markedRawEndpointFactor_cutoff]
  by_cases hs : G s <;> by_cases ht : G t <;> simp only [hs,ht,ite_true,ite_false,true_and,false_and]
  all_goals split_ifs <;> simp

theorem markedRawDirtyGood_joint_detector
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x r d₀ Y ρ : ℝ) {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (w : Z → ℤ × ℤ) (η : ℝ → ℂ)
    (χ : MarkedRawState (markedRawActualPrimeBand e x) (pads+1) B Z → ℂ)
    (D : ℤ → ℤ → ℤ → ℂ) (p q : J → Bool)
    (s t : MarkedRawState (markedRawActualPrimeBand e x) (pads+1) B Z) :
    markedRawEdgeJointDetectorCoefficient hZ η d₀ Y ρ (markedRawDirtyGoodCutoff e x r d₀ Y w χ) D s t =
      markedRawEdgeEndpointPiece (MarkedRawDirtyGood e x r d₀ Y w) true true
        (fun _ _ => markedRawEdgeJointDetectorCoefficient hZ η d₀ Y ρ χ D) p q s t := by
  have hχ : markedRawDirtyGoodCutoff e x r d₀ Y w χ =
      fun s => if MarkedRawDirtyGood e x r d₀ Y w s then χ s else 0 :=
    funext (markedRawDirtyGoodCutoff_eq_ite e x r d₀ Y w χ)
  rw [hχ, markedRawEdgeJointDetectorCoefficient_cutoff]
  simp only [markedRawEdgeEndpointPiece, decide_eq_true_eq]

theorem markedRawEdgeEndpointPiece_source_symmetric
    {J : Type*} [Fintype J] {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (G : MarkedRawState P (pads+1) B Z → Prop) (left right : Bool)
    (A : MarkedRawEdgePatternKernel P pads B Z)
    (hG : ∀ z a m σ, G (z,(a,markedRawMemoryPermute m σ)) ↔ G (z,(a,m)))
    (hA : ∀ p q z a t, MarkedRawMemorySymmetric (fun m => A p q (z,(a,m)) t))
    (p q : J → Bool) (z : Z) (a : MarkedRawActive P (pads+1)) (t : MarkedRawState P (pads+1) B Z) :
    MarkedRawMemorySymmetric (fun m => markedRawEdgeEndpointPiece G left right A p q (z,(a,m)) t) := by
  intro m σ
  have hg := propext (hG z a m σ)
  have ha : A p q (z,(a,markedRawMemoryPermute m σ)) t = A p q (z,(a,m)) t := hA p q z a t m σ
  simp only [markedRawEdgeEndpointPiece,hg,ha]

theorem markedRawEdgeEndpointPiece_target_symmetric
    {J : Type*} [Fintype J] {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (G : MarkedRawState P (pads+1) B Z → Prop) (left right : Bool)
    (A : MarkedRawEdgePatternKernel P pads B Z)
    (hG : ∀ z a m σ, G (z,(a,markedRawMemoryPermute m σ)) ↔ G (z,(a,m)))
    (hA : ∀ p q s z a, MarkedRawMemorySymmetric (fun m => A p q s (z,(a,m))))
    (p q : J → Bool) (s : MarkedRawState P (pads+1) B Z) (z : Z) (a : MarkedRawActive P (pads+1)) :
    MarkedRawMemorySymmetric (fun m => markedRawEdgeEndpointPiece G left right A p q s (z,(a,m))) := by
  intro m σ
  have hg := propext (hG z a m σ)
  have ha : A p q s (z,(a,markedRawMemoryPermute m σ)) = A p q s (z,(a,m)) := hA p q s z a m σ
  simp only [markedRawEdgeEndpointPiece,hg,ha]

theorem markedRawDirtyEndpointPiece_transpose
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x r d₀ Y : ℝ) {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (ν : (j : J) → ↥(markedRawActualPrimeBand e x j) → ℝ) (δ γ : J → ℂ)
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (w : Z → ℤ × ℤ) (left right : Bool)
    (A : MarkedRawEdgePatternKernel (markedRawActualPrimeBand e x) pads B Z)
    (hAl : ∀ p q z a t, MarkedRawMemorySymmetric (fun m => A p q (z,(a,m)) t))
    (hAr : ∀ p q s z a, MarkedRawMemorySymmetric (fun m => A p q s (z,(a,m))))
    (f g : MarkedRawState (markedRawActualPrimeBand e x) (pads+1) B Z → ℂ)
    (hf : ∀ z a, MarkedRawMemorySymmetric (fun m => f (z,(a,m))))
    (hg : ∀ z a, MarkedRawMemorySymmetric (fun m => g (z,(a,m)))) :
    (∑ s, (markedRawStateMass ν s : ℂ) * g s *
      markedRawEdgePatternApply ν δ γ hZ
        (markedRawEdgeEndpointPiece (MarkedRawDirtyGood e x r d₀ Y w) left right A) f s) =
      ∑ s, (markedRawStateMass ν s : ℂ) * f s *
        markedRawEdgePatternApply ν γ δ hZ
          (markedRawEdgeEndpointPiece (MarkedRawDirtyGood e x r d₀ Y w) right left
            (markedRawEdgePatternReverse A)) g s := by
  have hG := markedRawDirtyGood_pending_permute (M := pads+1) (B := B) e x r d₀ Y w
  have h := markedRawEdgePatternApply_transpose ν δ γ hZ
    (markedRawEdgeEndpointPiece (MarkedRawDirtyGood e x r d₀ Y w) left right A)
    (markedRawEdgeEndpointPiece_source_symmetric _ left right A hG hAl)
    (markedRawEdgeEndpointPiece_target_symmetric _ left right A hG hAr) f g hf hg
  rwa [markedRawEdgeEndpointPiece_reverse] at h

end
end ArtinMatthews
