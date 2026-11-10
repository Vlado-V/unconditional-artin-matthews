module

public import ArtinMatthews.SourceKPRetainedSeedExterior
public import ArtinMatthews.SourceKPRetainedDiagonalSplit
public import ArtinMatthews.SourceKPRetainedExteriorWhittaker
public import ArtinMatthews.SourceKPCuspResidualFourierSymmetries
public import ArtinMatthews.SourceKPRetainedExteriorProduct
public import ArtinMatthews.SourceKPRetainedPrincipalExteriorAll
public import ArtinMatthews.SourceKPRetainedPrincipalTransport
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

/-! The original finite translate average admits exact principal
transport at every rational frequency, with the literal exterior
Whittaker product and the retained Hilbert phase. -/
namespace ArtinMatthews

open NumberField IsDedekindDomain Matrix AllowedGenerators VaryingKummerAnalytic
open StandardAdelic QuadraticWeil
open scoped NumberField MatrixGroups AdeleRing Classical BigOperators

noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
local notation "Pr" => HeightOneSpectrum (𝓞 K)
local notation "Gf" => SourceKPFiniteAdeleProjective K hζ
local notation "A" => GL (Fin 2) 𝔸ᶠ[K]
local notation "B" => sourceKPRetainedFiniteBase K hζ
local notation "D" => sourceKPFiniteAdeleProjectiveDiagonalLift K hζ
local notation "Z" => sourceKPFiniteAdeleProjectiveCenter K hζ
local notation "tuple" => sourceKPAdelicRootSupportTuple K hζ
local notation "rUnit" => FiniteAdeleRing.unitEmbedding (𝓞 K) K
local notation "unitAt" => sourceKPRetainedUnitAt K
local notation "S[" S₀ "]" => sourceHilbertSet K S₀

theorem sourceKPRetainedSeedFourierAt_principal_all
    (S₀ : Finset Pr) (hS : standardWeilBadPlaces K ⊆ S[S₀])
    (R M : S[S₀] → ℕ) {T : ℝ} (hT : 2 < T) (a : A) (m : Kˣ)
    (z : ∀ P : S[S₀], (P.val.adicCompletion K)ˣ) :
    let q₀ := (tuple 1 a S[S₀]).2
    let z' := fun P : S[S₀] => unitAt P.val (rUnit m) * z P
    let θ := sourceKPRetainedDiagonalPhase K hζ (sourceKPRetainedUnitPart K S[S₀] (rUnit m))
      (sourceKPRetainedDiagonalUnit K S[S₀] z)
    sourceKPCuspResidualFrequencyScale K hζ m (1/6) *
        sourceKPRetainedSeedFourierAt K hζ S[S₀] R M (one_le_two.trans hT.le) m q₀
          (D (sourceKPRetainedDiagonalUnit K S[S₀] z)) =
      (sourceKPAdelicCentralComplex K hζ θ : ℂ) *
        sourceKPRetainedSeedCoefficient K hζ S[S₀] R M (one_le_two.trans hT.le) q₀ z' *
          sourceKPRetainedExteriorWhittaker K hζ S₀ hS m := by
  let S := S[S₀]
  let b := sourceKPRetainedExteriorUnitPart K S (rUnit m)
  let A₀ := sourceKPDiagonalHom 𝔸ᶠ[K] b
  let U := (sourceKPRetainedExteriorOrderSupport K S₀ m).image Subtype.val
  let E := (tuple 1 A₀ U).2
  let q₀ := (tuple 1 a S).2
  let hT' : 1 ≤ T := one_le_two.trans hT.le
  let W := sourceKPCuspResidualFourierValue K hζ 1 hT'
  let t := sourceKPRetainedSeedTranslate K hζ S R M q₀
  let kf := sourceKPFiniteLevelLift K hζ
  obtain ⟨k,hUS,hD,hprod⟩ := sourceKPRetainedPrincipalExterior_all K hζ S₀ hS m
  have he : D b = E*kf k := hD
  let z' (P : S) := unitAt P.val (rUnit m)*z P
  let v := D (sourceKPRetainedDiagonalUnit K S z)
  let w := D (sourceKPRetainedDiagonalUnit K S z')
  let θ := sourceKPRetainedDiagonalPhase K hζ (sourceKPRetainedUnitPart K S (rUnit m))
    (sourceKPRetainedDiagonalUnit K S z)
  let g := sourceKPCuspResidualUnitTranslate K hζ m v
  let χ := (sourceKPAdelicCentralComplex K hζ θ : ℂ)
  let G := sourceKPRetainedExteriorWhittaker K hζ S₀ hS m
  have hq (P : Pr) (hP : P ∉ S) : B P q₀ = 1 :=
    sourceKPRetainedFiniteBase_tuple_notMem K hζ a S P hP
  have hterm (i : SourceKPRetainedSeedIndex K S R M) : W (g*t i) = χ*W ((w*E)*t i) := by
    have hgrp : g*t i = Z θ * ((w*t i)*D b) := by
      dsimp only [g]
      rw [sourceKPRetainedResidualUnitTranslate_diagonal]
      exact sourceKPRetainedDiagonal_mul_seedTranslate K hζ S R M (rUnit m) a z i
    have hsup (P : Pr) (hP : P ∈ U) : B P (t i) = 1 := by
      have hPS : P ∉ S := (Finset.disjoint_left.mp hUS) hP
      exact sourceKPRetainedFiniteBase_seedTranslate_notMem K hζ S R M q₀ i P hPS (hq P hPS)
    have hc : Commute E (t i) :=
      sourceKPRetainedExteriorTuple_commute K hζ A₀ U (t i) hsup
    have hregroup : Z θ*((w*t i)*(E*kf k)) = Z θ*((w*E)*t i)*kf k := calc
      _ = Z θ*(w*(t i*E))*kf k := by simp only [mul_assoc]
      _ = _ := by rw [← hc.eq]; simp only [mul_assoc]
    rw [hgrp, he, hregroup]
    change sourceKPCuspResidualFourierValue K hζ 1 hT' (Z θ*((w*E)*t i)*kf k) = _
    rw [sourceKPCuspResidualFourierValue_right_deep, sourceKPCuspResidualFourierValue_center]
  have hs :
      sourceKPRetainedSeedFourierAt K hζ S R M hT' 1 q₀ (w*E) =
        sourceKPRetainedSeedCoefficient K hζ S R M hT' q₀ z' * G := by
    have hp : (∏ P ∈ U, sourceKPResidualExteriorFactor K hζ S₀ hS A₀ P) = G := hprod
    rw [← hp]
    exact sourceKPRetainedSeedFourierAt_exterior K hζ S₀ hS R M hT q₀ hq z' A₀ U hUS
  have hsum :
      sourceKPRetainedSeedFourierAt K hζ S R M hT' 1 q₀ g =
        χ*sourceKPRetainedSeedFourierAt K hζ S R M hT' 1 q₀ (w*E) := by
    change (∑ i, sourceKPRetainedSeedWeight K S R M i * W (g*t i)) =
      χ*(∑ i, sourceKPRetainedSeedWeight K S R M i * W ((w*E)*t i))
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [hterm]
    ring
  change sourceKPCuspResidualFrequencyScale K hζ m (1/6) *
      sourceKPRetainedSeedFourierAt K hζ S R M hT' m q₀ v =
    χ*sourceKPRetainedSeedCoefficient K hζ S R M hT' q₀ z'*G
  rw [← sourceKPRetainedSeedFourierAt_unit_translate]
  change sourceKPRetainedSeedFourierAt K hζ S R M hT' 1 q₀ g = _
  rw [hsum,hs,mul_assoc]

theorem sourceKPRetainedSeedFourierAt_zero_of_bad_exterior
    (S₀ : Finset Pr) (hS : standardWeilBadPlaces K ⊆ S[S₀])
    (R M : S[S₀] → ℕ) {T : ℝ} (hT : 2 < T) (a : A) (m : Kˣ)
    (z : ∀ P : S[S₀], (P.val.adicCompletion K)ˣ)
    (P : SourceExteriorPrime K S₀)
    (hm : exteriorPrincipalValuation P.val m < 0 ∨ exteriorPrincipalValuation P.val m % 3 = 2) :
    sourceKPRetainedSeedFourierAt K hζ S[S₀] R M (one_le_two.trans hT.le) m (tuple 1 a S[S₀]).2
      (D (sourceKPRetainedDiagonalUnit K S[S₀] z)) = 0 := by
  have h := sourceKPRetainedSeedFourierAt_principal_all K hζ S₀ hS R M hT a m z
  dsimp only at h
  rw [sourceKPRetainedExteriorWhittaker_zero_of_bad_order K hζ S₀ hS m P hm, mul_zero] at h
  exact (mul_eq_zero.mp h).resolve_left (sourceKPCuspResidualFrequencyScale_ne_zero K hζ m _)

theorem sourceKPRetainedSeedFourierAt_nonzero_exterior
    (S₀ : Finset Pr) (hS : standardWeilBadPlaces K ⊆ S[S₀])
    (R M : S[S₀] → ℕ) {T : ℝ} (hT : 2 < T) (a : A) (m : Kˣ)
    (z : ∀ P : S[S₀], (P.val.adicCompletion K)ˣ)
    (hm : sourceKPRetainedSeedFourierAt K hζ S[S₀] R M (one_le_two.trans hT.le) m (tuple 1 a S[S₀]).2
      (D (sourceKPRetainedDiagonalUnit K S[S₀] z)) ≠ 0) :
    sourceKPRetainedExteriorWhittaker K hζ S₀ hS m ≠ 0 := by
  intro hzero
  have h := sourceKPRetainedSeedFourierAt_principal_all K hζ S₀ hS R M hT a m z
  dsimp only at h
  rw [hzero,mul_zero] at h
  exact hm ((mul_eq_zero.mp h).resolve_left (sourceKPCuspResidualFrequencyScale_ne_zero K hζ m _))

end
end ArtinMatthews
