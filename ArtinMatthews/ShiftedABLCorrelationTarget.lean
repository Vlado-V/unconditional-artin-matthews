module

public import ArtinMatthews.CubicThetaShiftedCorrelation
public import ArtinMatthews.ShiftedCommonPrimePartSquarefree
public import Mathlib.Analysis.SpecialFunctions.Pow.Real


set_option backward.privateInPublic true
@[expose] public section

/-! The literal source correlation estimate consumed by the final
bilinear arithmetic. Its two common-prime-part factors remain explicit. -/

noncomputable section
namespace ArtinMatthews
open Set OAI OAI.SevenEighths
open scoped ContDiff

def ShiftedABLCorrelationBound (N : ℕ) (η : HeckeFamily.Character)
    (ν : ℝ) (Cg : ℕ → ℝ) (C : ℝ) : Prop :=
  ∀ m1 m2 : ℕ, m1 ≠ m2 → Squarefree m1 → Squarefree m2 → N.Coprime (m1*m2) →
    ∀ M T : ℝ, 1 ≤ M → 1 ≤ T →
      M ≤ (m1 : ℝ) → (m1 : ℝ) ≤ 2*M → M ≤ (m2 : ℝ) → (m2 : ℝ) ≤ 2*M →
      ∀ (g : ℝ → ℂ), ContDiff ℝ ∞ g → Function.support g ⊆ Icc T (2*T) →
        (∀ j x, ‖iteratedDeriv j g x‖ ≤ Cg j/T^j) →
        ‖thetaShiftedCorrelation η m1 m2 g‖ ≤ C*(M*T)^ν*
          (Real.sqrt (M*T+1)*Real.sqrt M*(shiftedCommonPrimePart m1 m2 : ℝ)/
            Real.sqrt (m1.gcd m2) +
            (M*T+1)^(3/4 : ℝ)*(shiftedCommonPrimePart m1 m2 : ℝ)^(1/4 : ℝ)/M^(1/4 : ℝ))

def ShiftedABLCorrelationSource (N : ℕ) (η : HeckeFamily.Character) : Prop :=
  ∀ ν : ℝ, 0 < ν → ∀ Cg : ℕ → ℝ, (∀ j, 0 ≤ Cg j) →
    ∃ C : ℝ, 0 < C ∧ ShiftedABLCorrelationBound N η ν Cg C

end ArtinMatthews
