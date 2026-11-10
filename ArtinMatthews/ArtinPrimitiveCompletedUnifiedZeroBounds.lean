module

public import ArtinMatthews.ArtinFrobeniusIdealCharacter
public import ArtinMatthews.KummerTowerDiscriminantModulus
public import ArtinMatthews.VaryingKummerAnalyticPrimitiveCompletedUnifiedPair
public import ArtinMatthews.VaryingKummerAnalyticZeroHeightWindow
public import ArtinMatthews.ArtinPrimitiveCompletedUnifiedPairBoundary
public import ArtinMatthews.VaryingKummerAnalyticPrimitiveCompletedUnifiedZeroBounds
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Parameter-uniform zero bounds for the actual discriminant-degree
Frobenius family. The genuine arithmetic constructor supplies the nonzero
boundary value required by the generic zero-pole theorem. -/
namespace ArtinMatthews.VaryingKummerAnalytic.ArtinRay
open NumberField RayClass OAI.PrimeDegreePackets.AnalyticGrowth
open OAI.SevenEighths.FiniteFourier
open scoped NumberField IsMulCommutative Classical BigOperators
noncomputable section

local instance {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] : NeZero (discriminantDegreeModulus K L) :=
  ⟨(discriminantDegreeModulus_pos K L).ne'⟩

theorem exists_discriminantDegree_primitiveCompletedUnifiedPair_zero_bounds :
    ∃ B : ℝ, 0 < B ∧ ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
      [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L]
      [NumberField.IsTotallyComplex K] (χ : Gal(L/K) →* ℂˣ), χ ≠ 1 →
      ∃ (f : Ideal (𝓞 K)) (hf : f ≠ ⊥)
        (_hMf : rationalModulusIdeal (𝓞 K) (discriminantDegreeModulus K L) ≤ f)
        (Ψ : EvenIdealRayCharacter K f) (hprim : IsPrimitiveOnIdeals Ψ.residue),
        Ψ.IsNonprincipal ∧
        f.absNorm ≤ (rationalModulusIdeal (𝓞 K) (discriminantDegreeModulus K L)).absNorm ∧
        (∀ I : primeToModulusIdeals (rationalIdealRayModulus K (discriminantDegreeModulus K L)),
          Ψ.idealHom (I:FractionalIdealGroup K) =
            GaloisIdealCharacter.idealHom K L χ (I:FractionalIdealGroup K)) ∧
        Ψ.primitiveCompletedUnifiedPair hf 0 ≠ 0 ∧ Ψ.primitiveCompletedUnifiedPair hf 1 ≠ 0 ∧
        Ψ.primitiveContinued hf hprim 1 ≠ 0 ∧
        Ψ.inverse.primitiveContinued hf (Ψ.inverse_isPrimitive hf hprim) 1 ≠ 0 ∧
        (∀ T : ℝ, zeroHeightCount (Ψ.primitiveCompletedUnifiedPair hf) T ≤
          5*Real.log |(discr K:ℝ)| +
            5*Real.log ((rationalModulusIdeal (𝓞 K) (discriminantDegreeModulus K L)).absNorm:ℝ) +
              B*(Module.finrank ℚ K:ℝ)*Real.log (|T|+2)) ∧
        (∀ (S : Finset ℂ) (T : ℝ), (∀ ρ ∈ S, 0 < ρ.re) →
          (∀ ρ ∈ S, |T-ρ.im| ≤ 1) →
          (∑ ρ ∈ S, ((zeroMultiplicity (Ψ.primitiveContinued hf hprim) ρ : ℝ) +
            (zeroMultiplicity (Ψ.inverse.primitiveContinued hf (Ψ.inverse_isPrimitive hf hprim)) ρ : ℝ))) ≤
            5*Real.log |(discr K:ℝ)| +
              5*Real.log ((rationalModulusIdeal (𝓞 K) (discriminantDegreeModulus K L)).absNorm:ℝ) +
                B*(Module.finrank ℚ K:ℝ)*Real.log (|T|+2)) := by
  obtain ⟨B,hB,HB⟩ := exists_primitiveCompletedUnifiedPair_finite_height_bound
  refine ⟨B,hB,?_⟩
  intro K L _ _ _ _ _ _ _ _ χ hχ
  obtain ⟨f,hf,hMf,Ψ,hprim,hΨ,hNorm,hAgree,h0,h1,hL,hLi⟩ :=
    discriminantDegree_exists_primitiveCompletedUnifiedPair_boundary_nonzero χ hχ
  have hfNorm : (0:ℝ) < (f.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (fun hz => hf (Ideal.absNorm_eq_zero_iff.mp hz))
  have hlog := Real.log_le_log hfNorm (show (f.absNorm:ℝ) ≤
      ((rationalModulusIdeal (𝓞 K) (discriminantDegreeModulus K L)).absNorm:ℝ) by
    exact_mod_cast hNorm)
  refine ⟨f,hf,hMf,Ψ,hprim,hΨ,hNorm,hAgree,h0,h1,hL,hLi,?_,?_⟩
  · intro T
    have H := HB K f hf Ψ hprim hΨ h0
      (zeroHeightWindow (Ψ.primitiveCompletedUnifiedPair hf) T) T
      (fun _ hρ => (Finset.mem_filter.mp hρ).2)
    change zeroHeightCount (Ψ.primitiveCompletedUnifiedPair hf) T ≤ _ at H
    nlinarith
  · intro S T hpos hT
    have H := HB K f hf Ψ hprim hΨ h0 S T hT
    have he : (∑ ρ ∈ S, (zeroMultiplicity (Ψ.primitiveCompletedUnifiedPair hf) ρ : ℝ)) =
        ∑ ρ ∈ S, ((zeroMultiplicity (Ψ.primitiveContinued hf hprim) ρ : ℝ) +
          (zeroMultiplicity (Ψ.inverse.primitiveContinued hf (Ψ.inverse_isPrimitive hf hprim)) ρ : ℝ)) := by
      apply Finset.sum_congr rfl
      intro ρ hρ
      rw [Ψ.primitiveCompletedUnifiedPair_zeroMultiplicity_eq_primitive hf hprim hΨ h0 (hpos ρ hρ),
        Int.cast_add]
    rw [he] at H
    nlinarith

theorem exists_discriminantDegree_primitiveCompletedUnifiedPair_weighted_zero_bound :
    ∃ B : ℝ, 0 < B ∧ ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
      [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L]
      [NumberField.IsTotallyComplex K] (χ : Gal(L/K) →* ℂˣ), χ ≠ 1 →
      ∃ (f : Ideal (𝓞 K)) (hf : f ≠ ⊥)
        (_hMf : rationalModulusIdeal (𝓞 K) (discriminantDegreeModulus K L) ≤ f)
        (Ψ : EvenIdealRayCharacter K f) (hprim : IsPrimitiveOnIdeals Ψ.residue),
        Ψ.IsNonprincipal ∧
        f.absNorm ≤ (rationalModulusIdeal (𝓞 K) (discriminantDegreeModulus K L)).absNorm ∧
        (∀ I : primeToModulusIdeals (rationalIdealRayModulus K (discriminantDegreeModulus K L)),
          Ψ.idealHom (I:FractionalIdealGroup K) =
            GaloisIdealCharacter.idealHom K L χ (I:FractionalIdealGroup K)) ∧
        Ψ.primitiveCompletedUnifiedPair hf 0 ≠ 0 ∧ Ψ.primitiveCompletedUnifiedPair hf 1 ≠ 0 ∧
        Ψ.primitiveContinued hf hprim 1 ≠ 0 ∧
        Ψ.inverse.primitiveContinued hf (Ψ.inverse_isPrimitive hf hprim) 1 ≠ 0 ∧
        (∀ (Φ : ℂ → ℂ) (C : ℝ), 0 ≤ C →
          (∀ ρ, Ψ.primitiveCompletedUnifiedPair hf ρ = 0 → ‖Φ ρ‖ ≤ C/(1+|ρ.im|)^2) →
          Summable (fun ρ => (zeroMultiplicity (Ψ.primitiveCompletedUnifiedPair hf) ρ : ℂ)*Φ ρ) ∧
          (∑' ρ, ‖(zeroMultiplicity (Ψ.primitiveCompletedUnifiedPair hf) ρ : ℂ)*Φ ρ‖) ≤
            4*C*(Real.log |(discr K:ℝ)| +
              Real.log ((rationalModulusIdeal (𝓞 K) (discriminantDegreeModulus K L)).absNorm:ℝ) +
                B*(Module.finrank ℚ K:ℝ))) := by
  obtain ⟨B,hB,HB⟩ := exists_primitiveCompletedUnifiedPair_weighted_zero_bound
  refine ⟨B,hB,?_⟩
  intro K L _ _ _ _ _ _ _ _ χ hχ
  obtain ⟨f,hf,hMf,Ψ,hprim,hΨ,hNorm,hAgree,h0,h1,hL,hLi⟩ :=
    discriminantDegree_exists_primitiveCompletedUnifiedPair_boundary_nonzero χ hχ
  have hfNorm : (0:ℝ) < (f.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (fun hz => hf (Ideal.absNorm_eq_zero_iff.mp hz))
  have hlog := Real.log_le_log hfNorm (show (f.absNorm:ℝ) ≤
      ((rationalModulusIdeal (𝓞 K) (discriminantDegreeModulus K L)).absNorm:ℝ) by
    exact_mod_cast hNorm)
  refine ⟨f,hf,hMf,Ψ,hprim,hΨ,hNorm,hAgree,h0,h1,hL,hLi,?_⟩
  intro Φ C hC hΦ
  obtain ⟨hS,H⟩ := HB K f hf Ψ hprim hΨ h0 Φ C hC hΦ
  refine ⟨hS,H.trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ 4*C)
  linarith

end
end ArtinMatthews.VaryingKummerAnalytic.ArtinRay
