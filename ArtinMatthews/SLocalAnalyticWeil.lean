module

public import ArtinMatthews.StandardLocalSquareWeil
public import ArtinMatthews.SLocalWeakApproximation


set_option backward.privateInPublic true
@[expose] public section

/-! The actual finite S-product of normalized analytic Weil indices,
defined on the genuine local square-class space, without a character premise. -/

namespace ArtinMatthews.QuadraticWeil

open NumberField IsDedekindDomain ClassFieldTheory
open OAI.RepresentationTheory.Weil.AdelicSplitting
open scoped NumberField Classical

noncomputable section

variable (F : Type) [Field F] [NumberField F]
  (S : Finset (HeightOneSpectrum (𝓞 F)))

def sLocalAnalyticWeil (x : SLocalPowerClasses F 2 S) : ℂ :=
  ∏ v : S, standardLocalSquareWeil F v.1 (x v)

theorem sLocalAnalyticWeil_eighth (x : SLocalPowerClasses F 2 S) :
    sLocalAnalyticWeil F S x ^ 8 = 1 := by
  rw [sLocalAnalyticWeil, ← Finset.prod_pow]
  exact Finset.prod_eq_one (fun v _ => standardLocalSquareWeil_eighth F v.1 (x v))

theorem sLocalAnalyticWeil_ne_zero (x : SLocalPowerClasses F 2 S) :
    sLocalAnalyticWeil F S x ≠ 0 := by
  intro he
  have h := sLocalAnalyticWeil_eighth F S x
  rw [he, zero_pow (by decide)] at h
  exact zero_ne_one h

theorem sLocalAnalyticWeil_one : sLocalAnalyticWeil F S 1 = 1 := by
  apply Finset.prod_eq_one
  intro v _
  exact standardLocalSquareWeil_one F v.1

theorem sLocalAnalyticWeil_globalClass (a : Fˣ) :
    sLocalAnalyticWeil F S (sLocalGlobalClassMap F 2 S a) =
      ∏ v : S, standardNormalizedWeil F a (.inr v.1) := by
  apply Finset.prod_congr rfl
  intro v _
  rfl

end

end ArtinMatthews.QuadraticWeil
