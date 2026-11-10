module

public import ArtinMatthews.SourceKPRetainedDiagonalSplit
public import ArtinMatthews.SourceKPRetainedSeedExterior
public import ArtinMatthews.SourceKPRetainedSeedVector
public import ArtinMatthews.SourceKPCuspResidualFourierSymmetries
public import ArtinMatthews.SourceKPRetainedCubeCutoff
public import ArtinMatthews.SourceKPRetainedExteriorProduct
public import ArtinMatthews.SourceKPRetainedPrincipalExterior
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

/-! The literal positive retained seed has the canonical squarefree-cube
coefficient with the exact residue frequency scale. The retained
cubic phase is proved trivial wherever the positive cutoff is nonzero. -/
namespace ArtinMatthews

open NumberField IsDedekindDomain Matrix StandardAdelic QuadraticWeil VaryingKummerAnalytic SourceReflection
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

theorem sourceKPRetainedSeedFourierAt_principal_squarefree_cube
    (S₀ : Finset Pr) (hS : standardWeilBadPlaces K ⊆ S[S₀])
    (R M : S[S₀] → ℕ) {T : ℝ} (hT : 2 < T) (a : A)
    (c : ReflectionSquarefreeExponents K S₀) (n : SourcePrimeExponents K S₀)
    (z : ∀ P : S[S₀], (P.val.adicCompletion K)ˣ) :
    let m := sourcePrimeExponentUnit K hζ S₀ (c.val + 3 • n)
    let q₀ := (tuple 1 a S[S₀]).2
    let C := sourceKPRetainedSeedCoefficient K hζ S[S₀] R M (one_le_two.trans hT.le) q₀
    let z' := fun P : S[S₀] => unitAt P.val (rUnit m) * z P
    let θ := sourceKPRetainedDiagonalPhase K hζ (sourceKPRetainedUnitPart K S[S₀] (rUnit m))
      (sourceKPRetainedDiagonalUnit K S[S₀] z)
    sourceKPCuspResidualFrequencyScale K hζ m (1/6) *
        sourceKPRetainedSeedFourierAt K hζ S[S₀] R M (one_le_two.trans hT.le) m q₀
          (D (sourceKPRetainedDiagonalUnit K S[S₀] z)) =
      (sourceKPAdelicCentralComplex K hζ θ : ℂ) * C z' *
        (reflectionGammaTwo K hζ S₀ c.val /
          ((Real.sqrt (sourcePrimeExponentNorm K S₀ c.val : ℝ) : ℂ) *
            (sourcePrimeExponentNorm K S₀ n : ℂ))) := by
  let S := S[S₀]
  let m := sourcePrimeExponentUnit K hζ S₀ (c.val + 3 • n)
  let b := sourceKPRetainedExteriorUnitPart K S (rUnit m)
  let A₀ := sourceKPDiagonalHom 𝔸ᶠ[K] b
  let U : Finset Pr := (c.val.support ∪ n.support).image Subtype.val
  let E := (tuple 1 A₀ U).2
  let q₀ := (tuple 1 a S).2
  let hT' : 1 ≤ T := one_le_two.trans hT.le
  let W := sourceKPCuspResidualFourierValue K hζ 1 hT'
  let t := sourceKPRetainedSeedTranslate K hζ S R M q₀
  let kf := sourceKPFiniteLevelLift K hζ
  obtain ⟨k,hUS,hD,hprod⟩ :=
    sourceKPRetainedPrincipalExterior_squarefree_cube K hζ S₀ hS c n
  have he : D b = E*kf k := hD
  let z' (P : S) := unitAt P.val (rUnit m)*z P
  let v := D (sourceKPRetainedDiagonalUnit K S z)
  let w := D (sourceKPRetainedDiagonalUnit K S z')
  let θ := sourceKPRetainedDiagonalPhase K hζ (sourceKPRetainedUnitPart K S (rUnit m))
    (sourceKPRetainedDiagonalUnit K S z)
  let g := sourceKPCuspResidualUnitTranslate K hζ m v
  let G := reflectionGammaTwo K hζ S₀ c.val /
    ((Real.sqrt (sourcePrimeExponentNorm K S₀ c.val : ℝ) : ℂ) *
      (sourcePrimeExponentNorm K S₀ n : ℂ))
  let ζc := (sourceKPAdelicCentralComplex K hζ θ : ℂ)
  have hterm (i : SourceKPRetainedSeedIndex K S R M) : W (g*t i) = ζc * W (w*t i) * G := by
    have hgrp : g*t i = Z θ * ((w*t i)*D b) := by
      dsimp only [g]
      rw [sourceKPRetainedResidualUnitTranslate_diagonal]
      exact sourceKPRetainedDiagonal_mul_seedTranslate K hζ S R M (rUnit m) a z i
    have hregroup : Z θ*((w*t i)*(E*kf k)) = Z θ*((w*t i)*E)*kf k := by
      simp only [mul_assoc]
    have hsupp (P : Pr) (hP : P ∈ U) : B P (w*t i) = 1 := by
      have hPS : P ∉ S := (Finset.disjoint_left.mp hUS) hP
      have hq : B P q₀ = 1 := sourceKPRetainedFiniteBase_tuple_notMem K hζ a S P hPS
      rw [map_mul,
        sourceKPRetainedFiniteBase_diagonalUnit_notMem K hζ S z' P hPS,
        sourceKPRetainedFiniteBase_seedTranslate_notMem K hζ S R M q₀ i P hPS hq, one_mul]
    have hfac : W ((w*t i)*E) = W (w*t i)*G := by
      have hG : (∏ P ∈ U, sourceKPResidualExteriorFactor K hζ S₀ hS A₀ P) = G := hprod
      rw [← hG]
      exact sourceKPResidualFourierValue_exterior_product_of_supported K hζ S₀ hS hT A₀ U hUS
        (w*t i) hsupp
    rw [hgrp, he, hregroup]
    change sourceKPCuspResidualFourierValue K hζ 1 hT' (Z θ*((w*t i)*E)*kf k) = _
    rw [sourceKPCuspResidualFourierValue_right_deep, sourceKPCuspResidualFourierValue_center]
    change ζc * W ((w*t i)*E) = _
    rw [hfac, mul_assoc]
  change sourceKPCuspResidualFrequencyScale K hζ m (1/6) *
      sourceKPRetainedSeedFourierAt K hζ S R M hT' m q₀ v =
    ζc * sourceKPRetainedSeedCoefficient K hζ S R M hT' q₀ z' * G
  rw [← sourceKPRetainedSeedFourierAt_unit_translate]
  change (∑ i, sourceKPRetainedSeedWeight K S R M i * W (g*t i)) =
    ζc * (∑ i, sourceKPRetainedSeedWeight K S R M i * W (w*t i))*G
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [hterm]
  ring

theorem sourceKPRetainedSeedFourierAt_principal_squarefree_cube_of_cubeCutoffs
    (S₀ : Finset Pr) (hS : standardWeilBadPlaces K ⊆ S[S₀])
    (R M : S[S₀] → ℕ) {T : ℝ} (hT : 2 < T) (a : A)
    (U : ∀ P : S[S₀], SourceThetaFiniteCutoff K P.val)
    (hCube : ∀ (P : S[S₀]) (t : (P.val.adicCompletion K)ˣ), t ∈ (U P).region → ∃ w, w^3 = t)
    (hcut : ∀ z : ∀ P : S[S₀], (P.val.adicCompletion K)ˣ,
      let q₀ := (tuple 1 a S[S₀]).2
      sourceKPRetainedSeedCoefficient K hζ S[S₀] R M (one_le_two.trans hT.le) q₀ z =
        sourceKPCuspResidualFourierValue K hζ 1 (one_le_two.trans hT.le) q₀ *
          ∏ P : S[S₀], (U P).factor (z P))
    (c : ReflectionSquarefreeExponents K S₀) (n : SourcePrimeExponents K S₀)
    (z : ∀ P : S[S₀], (P.val.adicCompletion K)ˣ) :
    let q₀ := (tuple 1 a S[S₀]).2
    let C₀ := sourceKPCuspResidualFourierValue K hζ 1 (one_le_two.trans hT.le) q₀
    let m := sourcePrimeExponentUnit K hζ S₀ (c.val + 3 • n)
    sourceKPCuspResidualFrequencyScale K hζ m (1/6) *
        sourceKPRetainedSeedFourierAt K hζ S[S₀] R M (one_le_two.trans hT.le) m q₀
          (D (sourceKPRetainedDiagonalUnit K S[S₀] z)) =
      C₀ * (∏ P : S[S₀], (U P).factor (unitAt P.val (rUnit m) * z P)) *
        (reflectionGammaTwo K hζ S₀ c.val /
          ((Real.sqrt (sourcePrimeExponentNorm K S₀ c.val : ℝ) : ℂ) *
            (sourcePrimeExponentNorm K S₀ n : ℂ))) := by
  let S := S[S₀]
  let m := sourcePrimeExponentUnit K hζ S₀ (c.val + 3 • n)
  let q₀ := (tuple 1 a S).2
  let C₀ := sourceKPCuspResidualFourierValue K hζ 1 (one_le_two.trans hT.le) q₀
  let z' (P : S) := unitAt P.val (rUnit m) * z P
  let r := sourceKPRetainedUnitPart K S (rUnit m)
  let v := sourceKPRetainedDiagonalUnit K S z
  let θ := sourceKPRetainedDiagonalPhase K hζ r v
  let G := reflectionGammaTwo K hζ S₀ c.val /
    ((Real.sqrt (sourcePrimeExponentNorm K S₀ c.val : ℝ) : ℂ) *
      (sourcePrimeExponentNorm K S₀ n : ℂ))
  have hraw :
      sourceKPCuspResidualFrequencyScale K hζ m (1/6) *
          sourceKPRetainedSeedFourierAt K hζ S R M (one_le_two.trans hT.le) m q₀ (D v) =
        (sourceKPAdelicCentralComplex K hζ θ : ℂ) *
          sourceKPRetainedSeedCoefficient K hζ S R M (one_le_two.trans hT.le) q₀ z' * G :=
    sourceKPRetainedSeedFourierAt_principal_squarefree_cube K hζ S₀ hS R M hT a c n z
  change sourceKPCuspResidualFrequencyScale K hζ m (1/6) *
    sourceKPRetainedSeedFourierAt K hζ S R M (one_le_two.trans hT.le) m q₀ (D v) =
      C₀ * (∏ P : S, (U P).factor (z' P)) * G
  rw [hraw, hcut]
  by_cases hz : ∀ P : S, z' P ∈ (U P).region
  · have hr : r*v = sourceKPRetainedDiagonalUnit K S z' :=
      sourceKPRetainedDiagonalUnit_mul K S _ _
    have hθ : θ = 1 := by
      apply sourceKPRetainedDiagonalPhase_eq_one_of_local_cubes
      intro P
      rw [hr]
      by_cases hP : P ∈ S
      · rw [sourceKPRetainedDiagonalUnit_unitAt_mem K S z' ⟨P,hP⟩]
        exact hCube ⟨P,hP⟩ (z' ⟨P,hP⟩) (hz ⟨P,hP⟩)
      · refine ⟨1,?_⟩
        rw [sourceKPRetainedDiagonalUnit_unitAt_notMem K S z' P hP, one_pow]
    rw [hθ,map_one,Units.val_one,one_mul]
  · obtain ⟨P,hP⟩ := not_forall.mp hz
    have hzero : (∏ P : S, (U P).factor (z' P)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ P) (Set.indicator_of_notMem hP _)
    change (sourceKPAdelicCentralComplex K hζ θ : ℂ) *
      (C₀ * (∏ P : S, (U P).factor (z' P))) * G =
        C₀ * (∏ P : S, (U P).factor (z' P)) * G
    simp only [hzero, mul_zero, zero_mul]

theorem sourceKPRetainedPositiveSeed_principal_squarefree_cube
    (S₀ : Finset Pr) (hS : standardWeilBadPlaces K ⊆ S[S₀])
    {T : ℝ} (hT : 2 < T) :
    ∃ (a : A) (R M : S[S₀] → ℕ) (U : ∀ P : S[S₀], SourceThetaFiniteCutoff K P.val),
      let q₀ := (tuple 1 a S[S₀]).2
      let C₀ := sourceKPCuspResidualFourierValue K hζ 1 (one_le_two.trans hT.le) q₀
      C₀ ≠ 0 ∧ sourceKPRetainedSeedVector K hζ S[S₀] R M hT q₀ ≠ 0 ∧
      ∀ (c : ReflectionSquarefreeExponents K S₀) (n : SourcePrimeExponents K S₀)
        (z : ∀ P : S[S₀], (P.val.adicCompletion K)ˣ),
        let m := sourcePrimeExponentUnit K hζ S₀ (c.val + 3 • n)
        sourceKPCuspResidualFrequencyScale K hζ m (1/6) *
            sourceKPRetainedSeedFourierAt K hζ S[S₀] R M (one_le_two.trans hT.le) m q₀
              (D (sourceKPRetainedDiagonalUnit K S[S₀] z)) =
          C₀ * (∏ P : S[S₀], (U P).factor (unitAt P.val (rUnit m) * z P)) *
            (reflectionGammaTwo K hζ S₀ c.val /
              ((Real.sqrt (sourcePrimeExponentNorm K S₀ c.val : ℝ) : ℂ) *
                (sourcePrimeExponentNorm K S₀ n : ℂ))) := by
  obtain ⟨a,R,M,U,hne,hv,hCube,hcut⟩ :=
    sourceKPRetainedPositiveSeed_exists_cubeCutoffs K hζ S₀ hS hT
  exact ⟨a,R,M,U,hne,hv,
    sourceKPRetainedSeedFourierAt_principal_squarefree_cube_of_cubeCutoffs
      K hζ S₀ hS R M hT a U hCube hcut⟩

end
end ArtinMatthews
