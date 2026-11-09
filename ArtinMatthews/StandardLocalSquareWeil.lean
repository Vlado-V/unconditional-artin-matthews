module

public import ArtinMatthews.StandardAdelicWeilIndex
public import ClassFieldTheory.Definitions.HilbertSymbols.PowerClass


set_option backward.privateInPublic true
@[expose] public section

/-! The actual local analytic Weil factor descends to the genuine square
class quotient at every finite place, including the wild places. -/

namespace ArtinMatthews.QuadraticWeil

open NumberField IsDedekindDomain ClassFieldTheory
open OAI.RepresentationTheory.Weil.AdelicSplitting
open scoped NumberField Classical

noncomputable section

variable (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

local instance standardLocalCompletionCharZero : CharZero (v.adicCompletion F) :=
  ArchimedeanAdeles.Construction.completionCharZero F (.inr v)
local instance standardLocalCompletionMeasurable : MeasurableSpace (v.adicCompletion F) := borel (v.adicCompletion F)
local instance standardLocalCompletionBorel : BorelSpace (v.adicCompletion F) := ⟨rfl⟩

def standardLocalWeil (x : (v.adicCompletion F)ˣ) : ℂ :=
  analyticNormalizedWeil (StandardAdelic.localFiniteCharacter F v) x

theorem standardLocalWeil_square_mul (x y : (v.adicCompletion F)ˣ) :
    standardLocalWeil F v (x * y ^ 2) = standardLocalWeil F v x :=
  analyticNormalizedWeil_square_mul (completion_nondiscrete F (.inr v))
    (StandardAdelic.localFiniteCharacter F v) (StandardAdelic.localFiniteCharacter_continuous F v)
    (StandardAdelic.localFiniteCharacter_unitary F v) (StandardAdelic.localFiniteCharacter_nontrivial F v) x y

theorem standardLocalWeil_eighth (x : (v.adicCompletion F)ˣ) : standardLocalWeil F v x ^ 8 = 1 :=
  analyticNormalizedWeil_eighth (completion_nondiscrete F (.inr v))
    (StandardAdelic.localFiniteCharacter F v) (StandardAdelic.localFiniteCharacter_continuous F v)
    (StandardAdelic.localFiniteCharacter_unitary F v) (StandardAdelic.localFiniteCharacter_nontrivial F v) x

theorem standardLocalWeil_one : standardLocalWeil F v 1 = 1 := by
  simpa only [standardNormalizedWeil, adelicNormalizedWeil, standardLocalWeil,
    analyticNormalizedWeil, StandardAdelic.localFiniteCharacter, Units.val_one, map_one, mul_one] using standardNormalizedWeil_one F (.inr v)

def standardLocalSquareWeil : PowerClassGroup (v.adicCompletion F) 2 → ℂ := by
  unfold PowerClassGroup
  refine Quotient.lift (standardLocalWeil F v) ?_
  intro a b hab
  obtain ⟨y, hy⟩ := QuotientGroup.leftRel_apply.mp hab
  have hy' : y ^ 2 = a⁻¹ * b := hy
  have hb : b = a * y ^ 2 := by rw [hy', mul_inv_cancel_left]
  rw [hb, standardLocalWeil_square_mul]

theorem standardLocalSquareWeil_powerClass (x : (v.adicCompletion F)ˣ) :
    standardLocalSquareWeil F v (powerClass (v.adicCompletion F) 2 x) = standardLocalWeil F v x := rfl

theorem standardLocalSquareWeil_eighth (x : PowerClassGroup (v.adicCompletion F) 2) :
    standardLocalSquareWeil F v x ^ 8 = 1 := by
  induction x using Quotient.inductionOn with
  | h x => exact standardLocalWeil_eighth F v x

theorem standardLocalSquareWeil_ne_zero (x : PowerClassGroup (v.adicCompletion F) 2) :
    standardLocalSquareWeil F v x ≠ 0 := by
  intro he
  have h := standardLocalSquareWeil_eighth F v x
  rw [he, zero_pow (by decide)] at h
  exact zero_ne_one h

theorem standardLocalSquareWeil_one : standardLocalSquareWeil F v 1 = 1 :=
  standardLocalWeil_one F v

end

end ArtinMatthews.QuadraticWeil
