module

public import ArtinMatthews.MarkedMinorArcDirtyMajorBands
public import ArtinMatthews.MarkedMinorArcDirtyRawEdgeFixedCode


set_option backward.privateInPublic true
@[expose] public section

/-! Actual fixed-label choice fibers for the dirty major comparison.
All admissibility restrictions are retained; the target map is injective
because store flags, promoted old indices and fresh labels are fixed. -/
namespace ArtinMatthews
open Finset
noncomputable section

 def markedDirtyMajorChoiceFiber {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z) (I : Finset J)
    (store : J → Bool) (indices : MarkedRawPromotionTuple s.2.2 I)
    (fresh : (j : ↥(univ \ I)) → ↥(P j.1)) : Finset (MarkedDirtyFixedEdgeChoice hZ s I) := by
  classical
  exact univ.filter (fun choice => (markedDirtyFixedEdgeChoiceCode hZ s I choice).2=(store,indices,fresh))

 theorem markedDirtyMajorChoiceFiber_target_injective {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z) (I : Finset J)
    (store : J → Bool) (indices : MarkedRawPromotionTuple s.2.2 I)
    (fresh : (j : ↥(univ \ I)) → ↥(P j.1)) :
    Set.InjOn (fun choice : MarkedDirtyFixedEdgeChoice hZ s I => choice.1.target.1)
      ↑(markedDirtyMajorChoiceFiber hZ s I store indices fresh) := by
  classical
  intro a ha b hb he
  apply markedDirtyFixedEdgeChoiceCode_injective hZ s I
  apply Prod.ext
  · exact Subtype.ext he
  · exact ((mem_filter.mp ha).2).trans ((mem_filter.mp hb).2).symm

 theorem markedDirtyMajorChoiceFiber_promoted {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z) (I : Finset J)
    (store : J → Bool) (indices : MarkedRawPromotionTuple s.2.2 I)
    (fresh : (j : ↥(univ \ I)) → ↥(P j.1))
    (choice : MarkedDirtyFixedEdgeChoice hZ s I)
    (hc : choice ∈ markedDirtyMajorChoiceFiber hZ s I store indices fresh) (j : I) :
    choice.1.promotions j.1=some (indices j) := by
  classical
  have hi := congrArg (fun c => c.2.1) (mem_filter.mp hc).2
  have hh := markedDirtyFixedPromotionTuple_spec s.2.2 choice.1.promotions I choice.2 j
  change markedDirtyFixedPromotionTuple s.2.2 choice.1.promotions I choice.2=indices at hi
  rw [hi] at hh
  exact hh

 /-- The literal finite coefficient sum in a fixed actual code fiber.
The target count and coefficient contraction are proved from the actual edge,
not supplied as row or support hypotheses. -/
 theorem markedDirtyMajorChoiceFiber_sum_norm_le {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (η ψ : ℝ → ℂ)
    (r d₀ Y Q ρ : ℝ) {c Bτ K H W : ℝ}
    (hY : 1 ≤ Y) (hQ : 0 ≤ Q) (hc : 0 < c) (hBτ : 0 ≤ Bτ)
    (hρ₀ : 0 ≤ ρ) (hρ₁ : ρ ≤ 1) (hH : 0 ≤ H) (hW : 0 ≤ W)
    (hη : ∀ t, ‖η t‖ ≤ H) (hψ : ∀ t, ‖ψ t‖ ≤ W)
    (hsupp : Function.support ψ ⊆ Set.Icc (-K) K)
    (w : Z → ℤ × ℤ) (hw : ∀ z,markedMinorIntegerDet z.1 (w z)=1)
    (hτ : ∀ z ∈ Z,c ≤ |markedMinorIntegerTau r z| ∧ |markedMinorIntegerTau r z| ≤ Bτ)
    (χ : MarkedRawState P (pads+1) B Z → ℂ) (hχ : ∀ s, ‖χ s‖ ≤ 1)
    (s : MarkedRawState P (pads+1) B Z) (I : Finset J)
    (store : J → Bool) (indices : MarkedRawPromotionTuple s.2.2 I)
    (fresh : (j : ↥(univ \ I)) → ↥(P j.1)) (jstar : I) :
    (∑ choice ∈ markedDirtyMajorChoiceFiber hZ s I store indices fresh,
      ‖markedRawEdgeChoiceDetectorCoefficient hZ η d₀ Y ρ
        (markedRawFirstGoodCutoff r d₀ Y w χ) (markedRawEdgeMajorDetector ψ Q Y) s choice.1‖) ≤
      (H^2*(W*(4*Q^3/Y)))*(300*(max 1 (max (Bτ/c) K))^2)*Y*
        (1/((s.2.2.2 jstar.1 (indices jstar)).1.1:ℕ)+Y^(-1/10:ℝ)) := by
  classical
  let coeff : MarkedDirtyFixedEdgeChoice hZ s I → ℂ := fun choice =>
    markedRawEdgeChoiceDetectorCoefficient hZ η d₀ Y ρ
      (markedRawFirstGoodCutoff r d₀ Y w χ) (markedRawEdgeMajorDetector ψ Q Y) s choice.1
  let F := markedDirtyMajorChoiceFiber hZ s I store indices fresh
  let S := F.filter (fun choice => coeff choice ≠ 0)
  let T := S.image (fun choice => choice.1.target.1)
  have hSF : S ⊆ F := filter_subset _ _
  have hTZ : T ⊆ Z := by
    intro v hv
    obtain ⟨choice,_hc,rfl⟩ := mem_image.mp hv
    exact choice.1.target.2
  have hedges : ∀ v ∈ T,∃ choice : MarkedRawEdgeChoice hZ s,
      choice.target.1=v ∧ choice.promotions jstar.1=some (indices jstar) ∧
      markedRawEdgeChoiceDetectorCoefficient hZ η d₀ Y ρ
        (markedRawFirstGoodCutoff r d₀ Y w χ) (markedRawEdgeMajorDetector ψ Q Y) s choice ≠ 0 := by
    intro v hv
    obtain ⟨choice,hchoice,rfl⟩ := mem_image.mp hv
    exact ⟨choice.1,rfl,markedDirtyMajorChoiceFiber_promoted hZ s I store indices fresh choice
      (hSF hchoice) jstar,(mem_filter.mp hchoice).2⟩
  have hcount := markedDirtyMajor_actual_targets_count hZ η ψ r d₀ Y Q ρ hY hc hBτ hsupp w hw hτ χ s
    jstar.1 (indices jstar) T hTZ hedges
  have hinj : Set.InjOn (fun choice : MarkedDirtyFixedEdgeChoice hZ s I => choice.1.target.1) ↑S :=
    (markedDirtyMajorChoiceFiber_target_injective hZ s I store indices fresh).mono hSF
  have hcard : T.card=S.card := card_image_iff.mpr hinj
  rw [hcard] at hcount
  have hA : 0 ≤ H^2*(W*(4*Q^3/Y)) := by positivity
  have hbound (choice : MarkedDirtyFixedEdgeChoice hZ s I) : ‖coeff choice‖ ≤ H^2*(W*(4*Q^3/Y)) := by
    have hn := markedDirtyMajor_coefficient_norm_le hZ ψ η d₀ (by linarith : 0 < Y) hQ hρ₀ hρ₁ hH hW
      hη hψ (markedRawFirstGoodCutoff r d₀ Y w χ) (markedRawFirstGoodCutoff_norm_le r d₀ Y w χ hχ) s choice.1
    exact hn.trans (mul_le_of_le_one_right hA (pow_le_one₀ hρ₀ hρ₁))
  have hsum : (∑ choice ∈ F, ‖coeff choice‖) = ∑ choice ∈ S, ‖coeff choice‖ := by
    symm
    apply sum_subset hSF
    intro choice hchoice hn
    have hz : coeff choice=0 := by
      by_contra hne
      exact hn (mem_filter.mpr ⟨hchoice,hne⟩)
    exact norm_eq_zero.mpr hz
  change (∑ choice ∈ F, ‖coeff choice‖) ≤ _
  rw [hsum]
  calc
    _ ≤ ∑ _choice ∈ S, H^2*(W*(4*Q^3/Y)) := sum_le_sum (fun choice _ => hbound choice)
    _ = (H^2*(W*(4*Q^3/Y)))*(S.card:ℝ) := by rw [sum_const,nsmul_eq_mul]; ring
    _ ≤ (H^2*(W*(4*Q^3/Y)))*((300*(max 1 (max (Bτ/c) K))^2)*Y*
        (1/((s.2.2.2 jstar.1 (indices jstar)).1.1:ℕ)+Y^(-1/10:ℝ))) :=
      mul_le_mul_of_nonneg_left hcount hA
    _ = _ := by ring

end
end ArtinMatthews
