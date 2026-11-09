module

public import ArtinMatthews.MarkedMinorArcRawEdgeGeometricAdjoint
public import ArtinMatthews.MarkedWeightedOperatorWord
public import ArtinMatthews.MarkedMemoryGoodWordEnergy


set_option backward.privateInPublic true
@[expose] public section

/-! Literal ghost/edge words with either geometric orientation. The reverse
orientation conjugates the reflected geometric cutoff and eta while
retaining the original store and promotion charges. -/

noncomputable section
namespace ArtinMatthews
open Filter
open scoped BigOperators

def markedMemoryGeometricWord
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
    (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q ρ : ℝ)
    (orientation : ℕ → Bool) (qStage : ℕ → ℝ)
    (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ) :=
  markedOperatorWord (fun j => markedRawGhostApply ν V (qStage j) ρ hZ)
    (fun j => if orientation j then markedRawEdgeSymmetrized ν V hZ
      (markedRawEdgeAdjointCutoff ψ) (fun u => star (η u)) d₀ Y Q ρ (fun s => star (χ j s))
      else markedRawEdgeSymmetrized ν V hZ ψ η d₀ Y Q ρ (χ j))

theorem markedMemoryGeometricWord_forward
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
    (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q ρ : ℝ) (qStage : ℕ → ℝ)
    (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ)
    (n j : ℕ) (f : MarkedRawState P (pads+1) B Z → ℂ) :
    markedMemoryGeometricWord ν V hZ ψ η d₀ Y Q ρ (fun _ => false) qStage χ n j f =
      markedMemoryChronologicalApply ν V hZ ψ η d₀ Y Q ρ qStage χ n j f := by
  induction n generalizing j with
  | zero => rfl
  | succ n ih =>
    simp only [markedMemoryGeometricWord, markedOperatorWord, Bool.false_eq_true, ite_false,
      markedMemoryChronologicalApply, markedRawEdgeSymmetrized] at ih ⊢
    rw [ih]

set_option backward.isDefEq.respectTransparency false in
theorem markedMemoryGeometricWord_actual_energy
    {J : Type*} [Fintype J] [decJ : DecidableEq J]
    (e : J → ℝ) (he : ∀ j, (1/10 : ℝ) ≤ e j) (hinj : Function.Injective e)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (hη : Function.support η ⊆ Set.Icc 1 4) (hηnorm : ∀ t, ‖η t‖ ≤ 1)
    (q ρ G H c T A W : ℝ) (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1)
    (hρ : 0 < ρ) (hρ₁ : ρ < 1) (hgap : Real.sqrt q < ρ^2)
    (hG : 0 < G) (hH : 1 ≤ H) (hc : 0 < c)
    (hT : 0 ≤ T) (hA : 0 ≤ A) (hW : 0 ≤ W)
    (hdepth : 100*(5*G+26) < (Fintype.card J : ℝ))
    (hψnorm : ∀ t, ‖ψ t‖ ≤ W) (hsupp : Function.support ψ ⊆ Set.Icc (-A) A) :
    ∀ᶠ x : ℝ in atTop, ∀ (Z : Finset (ℤ × ℤ))
      (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (r d₀ Y : ℝ) (w : Z → ℤ × ℤ)
      (orientation : ℕ → Bool)
      (χ : ℕ → MarkedRawState (markedRawActualPrimeBand e x)
        (markedPadSlots x) (markedDirtyMemoryCutoff x) Z → ℂ)
      (qStage : ℕ → ℝ)
      (f : MarkedRawState (markedRawActualPrimeBand e x)
        (markedPadSlots x) (markedDirtyMemoryCutoff x) Z → ℂ),
      0 < d₀ → Real.exp ((Real.log x)^(1/10 : ℝ)) ≤ Y →
      Y ≤ Real.exp (H*(Real.log x)^(1/5 : ℝ)) →
      (∀ z, markedMinorIntegerDet z.1 (w z) = 1) →
      (∀ z ∈ Z, c ≤ |markedMinorIntegerTau r z| ∧ |markedMinorIntegerTau r z| ≤ T) →
      (∀ z v : Z, |markedMinorIntegerTau r v.1/markedMinorIntegerTau r z.1| ≤ 16) →
      (∀ j s, ‖χ j s‖ ≤ 1) →
      (∀ j z a, MarkedRawMemorySymmetric (fun m => χ j (z,(a,m)))) →
      (∀ j, 0 ≤ qStage j ∧ qStage j ≤ Real.sqrt q) →
      (∀ z a, MarkedRawMemorySymmetric (fun m => f (z,(a,m)))) →
      ∀ n j : ℕ,
      let ν := markedRawActualPrimeAtom e q x
      let V := fun i => bandReciprocalMass (markedLogPowerBand (e i) x)
      let C := Real.exp ((Fintype.card J : ℝ)*(2*markedRawGhostSchurParameter q ρ/ρ))
      let ε := (Real.log x)^(-G)
      (∑ s, markedRawStateMass ν s *
        ‖markedMemoryGeometricWord ν V hZ ψ η d₀ Y ((Real.log x)^(G+7)) ρ orientation qStage
          (fun i => markedRawDirtyGoodCutoff e x r d₀ Y w (χ i)) n j f s‖^2) ≤
        (C^(n+1)*ε^n)^2 * ∑ s, markedRawStateMass ν s*‖f s‖^2 := by
  classical
  cases Subsingleton.elim decJ (Classical.decEq J)
  have hηstar : Function.support (fun u => star (η u)) ⊆ Set.Icc 1 4 := by
    intro u hu
    apply hη
    intro h
    apply hu
    change star (η u) = 0
    rw [h, star_zero]
  have hηstarnorm : ∀ u, ‖star (η u)‖ ≤ 1 := by simpa only [norm_star] using hηnorm
  have hψstar := markedRawEdgeAdjointCutoff_bounds ψ hψnorm hsupp
  filter_upwards [marked_minor_actual_raw_ghost_energy e he hq₀ hq₁ hρ hgap,
    markedRawEdge_good_actual_energy e he hinj ψ η hη hηnorm G H c T A W ρ
      hG hH hc hT hA hW hρ.le hρ₁ hdepth hψnorm hsupp,
    markedRawEdge_good_actual_energy e he hinj (markedRawEdgeAdjointCutoff ψ)
      (fun u => star (η u)) hηstar hηstarnorm G H c T A W ρ
      hG hH hc hT hA hW hρ.le hρ₁ hdepth hψstar.1 hψstar.2] with x hghost hedge hgeometric
  intro Z hZ r d₀ Y w orientation χ qStage f hd₀ hYlo hYhi hw hτ hbox hχ hχsym hstage hf n j
  let ν := markedRawActualPrimeAtom e q x
  let V := fun i => bandReciprocalMass (markedLogPowerBand (e i) x)
  let χg := fun i => markedRawDirtyGoodCutoff e x r d₀ Y w (χ i)
  let S := fun F : MarkedRawState (markedRawActualPrimeBand e x) (markedPadSlots x)
      (markedDirtyMemoryCutoff x) Z → ℂ =>
    ∀ z a, MarkedRawMemorySymmetric (fun m => F (z,(a,m)))
  let ghost := fun j => markedRawGhostApply (M := markedPadSlots x)
    (B := markedDirtyMemoryCutoff x) ν V (qStage j) ρ hZ
  let edge := fun j => if orientation j then
    markedRawEdgeSymmetrized ν V hZ (markedRawEdgeAdjointCutoff ψ) (fun u => star (η u))
      d₀ Y ((Real.log x)^(G+7)) ρ (fun s => star (χg j s))
    else markedRawEdgeSymmetrized ν V hZ ψ η d₀ Y ((Real.log x)^(G+7)) ρ (χg j)
  have hχg : ∀ i z a, MarkedRawMemorySymmetric (fun m => χg i (z,(a,m))) :=
    fun i => markedRawDirtyGoodCutoff_symmetric e x r d₀ Y w (χ i) (hχsym i)
  have hgS : ∀ i F, S F → S (ghost i F) :=
    fun i F hF => markedRawGhostApply_symmetric ν V (qStage i) ρ hZ F hF
  have hχgstar : ∀ i z a, MarkedRawMemorySymmetric (fun m => star (χg i (z,(a,m)))) :=
    fun i z a m σ => congrArg star (hχg i z a m σ)
  have hcutstar (i : ℕ) : (fun s => star (χg i s)) =
      markedRawDirtyGoodCutoff e x r d₀ Y w (fun s => star (χ i s)) := by
    funext s
    dsimp only [χg]
    rw [markedRawDirtyGoodCutoff_eq_ite, markedRawDirtyGoodCutoff_eq_ite]
    split_ifs <;> simp only [star_zero]
  have heS : ∀ i F, S F → S (edge i F) := by
    intro i F hF
    by_cases hi : orientation i
    · simp only [edge, S, markedRawEdgeSymmetrized, ite_eq_left hi]
      intro z a
      exact markedRawSlotAverage_symmetric _
        (markedRawEdgeApply_symmetric ν V hZ (markedRawEdgeAdjointCutoff ψ) (fun u => star (η u))
          d₀ Y ((Real.log x)^(G+7)) ρ (fun s => star (χg i s)) _ (hχgstar i)
          (markedRawSlotAverage_symmetric F hF)) z a
    · simp only [edge, S, markedRawEdgeSymmetrized, ite_eq_right hi]
      intro z a
      exact markedRawSlotAverage_symmetric _
        (markedRawEdgeApply_symmetric ν V hZ ψ η d₀ Y ((Real.log x)^(G+7)) ρ
          (χg i) _ (hχg i) (markedRawSlotAverage_symmetric F hF)) z a
  apply markedOperatorWord_energy (markedRawStateMass ν) S ghost edge hgS heS
  · intro i F hF
    exact hghost (qStage i) (hstage i).1 (hstage i).2 _ _ Z hZ F hF
  · intro i F hF
    by_cases hi : orientation i
    · simp only [edge, ite_eq_left hi]
      erw [hcutstar i]
      exact hgeometric Z hZ q r d₀ Y w (fun s => star (χ i s)) F hq₀ hq₁ hd₀ hYlo hYhi hw hτ hbox
        (by simpa only [norm_star] using hχ i)
        (fun z a m σ => congrArg star (hχsym i z a m σ)) hF
    · simp only [edge, ite_eq_right hi]
      change (∑ s, markedRawStateMass ν s*
        ‖markedRawEdgeSymmetrized ν V hZ ψ η d₀ Y ((Real.log x)^(G+7)) ρ (χg i) F s‖^2) ≤ _
      exact hedge Z hZ q r d₀ Y w (χ i) F hq₀ hq₁ hd₀ hYlo hYhi hw hτ hbox
        (hχ i) (hχsym i) hF
  · exact hf

end ArtinMatthews
