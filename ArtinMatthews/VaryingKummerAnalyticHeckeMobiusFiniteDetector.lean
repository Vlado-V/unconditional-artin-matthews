module

public import ArtinMatthews.VaryingKummerAnalyticHeckeMobiusZeroTail
public import ArtinMatthews.VaryingKummerAnalyticHeckeMobiusRemoteTail
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! A zero in the manuscript rectangle forces a large, literal finite
ideal polynomial.  The conductor/height estimates and remote-tail bound
have both been proved for the actual primitive Hecke function. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField Complex
open scoped NumberField nonZeroDivisors Classical BigOperators
noncomputable section
namespace EvenIdealRayCharacter
variable {K : Type*} [Field K] [NumberField K] {M : Ideal (𝓞 K)}
variable (ψ : EvenIdealRayCharacter K M)

def mobiusSmoothedPolynomial (D : ℝ) (ρ : ℂ) (Y R : ℝ) : ℂ :=
  ∑ I ∈ (HeckeIdealMobius.normCutoff K R).filter (fun I => D < (Ideal.absNorm I : ℝ)),
    ψ.mobiusConvolutionCoefficient D I*(Ideal.absNorm I : ℂ)^(-ρ)*
      Complex.exp (-(Ideal.absNorm I : ℂ)/(Y : ℂ))

theorem mobiusSmoothedTail_eq_finite_add_remote (hM : M ≠ ⊥)
    (hprim : OAI.SevenEighths.FiniteFourier.IsPrimitiveOnIdeals ψ.residue)
    (hnp : ψ.IsNonprincipal) {D Y R : ℝ} (hD : 0 ≤ D) (hY : 0 < Y) (hDR : D ≤ R)
    {ρ : ℂ} (hρ : -1 < ρ.re) :
    ψ.mobiusSmoothedTail D ρ Y =
      ψ.mobiusSmoothedPolynomial D ρ Y R + ψ.mobiusSmoothedRemoteTail D ρ Y R := by
  let T : Ideal (𝓞 K) → ℂ := fun I => ψ.mobiusConvolutionCoefficient D I*
    (Ideal.absNorm I : ℂ)^(-ρ)*Complex.exp (-(Ideal.absNorm I : ℂ)/(Y : ℂ))
  have hs : Summable T := (ψ.mobiusSmoothedSum_hasSum_mellin hM hprim hnp hD hY hρ).summable
  let S := HeckeIdealMobius.normCutoff K R
  let F : Ideal (𝓞 K) → ℂ := fun I => if I ∈ S then if D < (Ideal.absNorm I : ℝ) then T I else 0 else 0
  let G : Ideal (𝓞 K) → ℂ := fun I => if R < (Ideal.absNorm I : ℝ) then T I else 0
  have hF : Summable F := by
    apply ((hs.indicator {I | D < (Ideal.absNorm I : ℝ)}).indicator
      (S : Set (Ideal (𝓞 K)))).congr
    intro I
    by_cases hi : I ∈ S <;> by_cases hd : D < (Ideal.absNorm I : ℝ) <;> simp [F,hi,hd]
  have hG : Summable G := hs.indicator {I | R < (Ideal.absNorm I : ℝ)}
  have he (I : Ideal (𝓞 K)) :
      (if D < (Ideal.absNorm I : ℝ) then T I else 0) = F I + G I := by
    have hmem := HeckeIdealMobius.mem_normCutoff K (hD.trans hDR) I
    dsimp only [F,G,S]
    by_cases hi : I ∈ HeckeIdealMobius.normCutoff K R
    · have hni : ¬ R < (Ideal.absNorm I : ℝ) := not_lt.mpr (hmem.mp hi)
      simp [hi,hni]
    · have hni : R < (Ideal.absNorm I : ℝ) := lt_of_not_ge (fun hn => hi (hmem.mpr hn))
      have hdi : D < (Ideal.absNorm I : ℝ) := hDR.trans_lt hni
      simp [hi,hni,hdi]
  have hsumF : (∑' I, F I) = ψ.mobiusSmoothedPolynomial D ρ Y R := by
    rw [tsum_eq_sum (s := S) (fun I hI => by simp [F,hI])]
    calc
      _ = ∑ I ∈ S, if D < (Ideal.absNorm I : ℝ) then T I else 0 := by
        apply Finset.sum_congr rfl
        intro I hI
        simp only [F,hI,ite_true]
      _ = _ := by
        rw [← Finset.sum_filter]
        rfl
  change (∑' I, if D < (Ideal.absNorm I : ℝ) then T I else 0) =
    ψ.mobiusSmoothedPolynomial D ρ Y R + ∑' I, G I
  simp_rw [he]
  rw [hF.tsum_add hG,hsumF]

end EvenIdealRayCharacter

theorem exists_actual_zero_large_finite_mobius_polynomial
    (K : Type*) [Field K] [NumberField K] :
    ∃ r U₀ : ℝ, 0 < r ∧ r < 1/10 ∧ 2 ≤ U₀ ∧ ∀ U : ℝ, U₀ ≤ U →
      ∀ {M : Ideal (𝓞 K)} (ψ : EvenIdealRayCharacter K M) (hM : M ≠ ⊥)
        (hprim : OAI.SevenEighths.FiniteFourier.IsPrimitiveOnIdeals ψ.residue)
        (_hnp : ψ.IsNonprincipal), (Ideal.absNorm M : ℝ) ≤ U →
        ∀ ρ : ℂ, (249/250 : ℝ) ≤ ρ.re → |ρ.im| ≤ 4*U^r →
          ψ.primitiveContinued hM hprim ρ=0 →
          1/8 ≤ ‖ψ.mobiusSmoothedPolynomial (U^2) ρ (U^10) (U^11)‖ := by
  obtain ⟨r,U₀,hr,hr',hU₀,hlarge⟩ := exists_actual_zero_large_mobius_tail K
  obtain ⟨U₁,hU₁,hremote⟩ := exists_actual_mobius_remote_tail_eventually_small K
  refine ⟨r,max U₀ U₁,hr,hr',hU₀.trans (le_max_left _ _),?_⟩
  intro U hU M ψ hM hprim hnp hMU ρ hρ him hz
  have hUU₀ : U₀ ≤ U := (le_max_left _ _).trans hU
  have hUU₁ : U₁ ≤ U := (le_max_right _ _).trans hU
  have hU2 : 2 ≤ U := hU₁.trans hUU₁
  have hU1 : 1 ≤ U := by linarith
  have ha := hlarge U hUU₀ ψ hM hprim hnp hMU ρ hρ him hz
  have hb := hremote U hUU₁ ψ (U^2) ρ (by linarith : (1/2 : ℝ) ≤ ρ.re)
  have he := ψ.mobiusSmoothedTail_eq_finite_add_remote hM hprim hnp
    (sq_nonneg U) (pow_pos (zero_lt_one.trans_le hU1) 10)
    (pow_le_pow_right₀ hU1 (by norm_num : 2 ≤ 11)) (by linarith : -1 < ρ.re)
  rw [he] at ha
  have hn := norm_add_le (ψ.mobiusSmoothedPolynomial (U^2) ρ (U^10) (U^11))
    (ψ.mobiusSmoothedRemoteTail (U^2) ρ (U^10) (U^11))
  linarith

end
end ArtinMatthews.VaryingKummerAnalytic
