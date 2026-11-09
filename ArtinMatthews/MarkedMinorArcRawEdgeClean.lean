module

public import ArtinMatthews.MarkedMinorArcRawEdgeAction


set_option backward.privateInPublic true
@[expose] public section

/-! Exact identification of the clean branch of the actual store/promote
operation with the literal raw clean operator already proved small. -/
namespace ArtinMatthews
open Matrix MeasureTheory
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1200000 in
/-- The no-store/no-promote coefficient is exactly the already checked
banned raw clean kernel, including all physical tests and both dampings. -/
theorem markedRawCleanEdgeChoice_coefficient {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q ρ : ℝ) (χ : MarkedRawState P (pads+1) B Z → ℂ)
    (s : MarkedRawState P (pads+1) B Z) (target : Z) (fresh : (j : J) → ↥(P j)) :
    markedRawEdgeChoiceCoefficient hZ ψ η d₀ Y Q ρ χ s (markedRawCleanEdgeChoice hZ s target fresh)=
      markedRawBannedCleanKernel (markedRawCleanKernel hZ ψ η d₀ Y Q ρ χ)
        (((markedRawActiveSplit pads) s.2.1).1,s.2.2)
        (s.1,((markedRawActiveSplit pads) s.2.1).2) (target,fresh) := by
  classical
  let bg : MarkedRawBackground P pads B := (((markedRawActiveSplit pads) s.2.1).1,s.2.2)
  let u : MarkedRawCleanFiber P Z := (s.1,((markedRawActiveSplit pads) s.2.1).2)
  have hs : (markedRawStateSplit pads B Z).symm (bg,u)=s := by
    change (markedRawStateSplit pads B Z).symm ((markedRawStateSplit pads B Z) s)=s
    exact Equiv.symm_apply_apply _ _
  have ht : (markedRawStateSplit pads B Z).symm (bg,(target,fresh))=
      (target,((markedRawActiveSplit pads).symm (((markedRawActiveSplit pads) s.2.1).1,fresh),s.2.2)) := rfl
  dsimp only [markedRawEdgeChoiceCoefficient]
  simp only [markedRawCleanEdgeChoice_target]
  unfold markedRawBannedCleanKernel MarkedRawCleanBan markedRawBanSourceActive
  change _=if MarkedRawFullCrossBan (((markedRawStateSplit pads B Z).symm (bg,u)).2.1) fresh then 0
    else markedRawCleanKernel hZ ψ η d₀ Y Q ρ χ bg u (target,fresh)
  rw [hs]
  unfold markedRawCleanKernel
  dsimp only
  change _=if MarkedRawFullCrossBan s.2.1 fresh then 0 else
    (if d₀ ≤ (markedRawCopiedProduct bg.1 : ℝ) ∧ (markedRawCopiedProduct bg.1 : ℝ) < 2*d₀ then
      if (markedRawCopiedProduct bg.1 : ℤ) ∣ markedMinorIntegerDet s.1.1 target.1 then
        ((d₀/(markedRawCopiedProduct bg.1 : ℝ) : ℝ) : ℂ)*
          markedRawEndpointFactor hZ ρ χ ((markedRawStateSplit pads B Z).symm (bg,u))*
          η ((markedRawLastProduct u.2 : ℝ)/Y)*η ((markedRawLastProduct fresh : ℝ)/Y)*
          ψ ((((markedMinorIntegerDet s.1.1 target.1/(markedRawCopiedProduct bg.1 : ℤ) : ℤ) : ℝ))/Y)*
          (∫ θ : AddCircle (1:ℝ) in (markedMinorCircleMajor Q Y)ᶜ,
            fourier (markedMinorIntegerDet s.1.1 target.1/(markedRawCopiedProduct bg.1 : ℤ)-
              (markedRawLastProduct u.2 : ℤ)+(markedRawLastProduct fresh : ℤ)) θ ∂AddCircle.haarAddCircle)*
          markedRawEndpointFactor hZ ρ χ ((markedRawStateSplit pads B Z).symm (bg,(target,fresh)))
      else 0 else 0)
  rw [hs,ht]
  dsimp only [markedRawCleanEdgeChoice,bg,u]
  simp only [markedRawEdgeTargetLast_none]
  split_ifs <;> try rfl
  all_goals
    rw [← markedRawEndpointFactor_damping hZ ρ χ s,
      ← markedRawEndpointFactor_damping hZ ρ χ
        (target,((markedRawActiveSplit pads).symm (((markedRawActiveSplit pads) s.2.1).1,fresh),s.2.2))]
    ring

end ArtinMatthews
