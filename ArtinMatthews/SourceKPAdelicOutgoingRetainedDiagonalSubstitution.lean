module

public import ArtinMatthews.SourceKPAdelicOutgoingRetainedReflectedTensor
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

/-! The actual principal substitution puts the retained profiles at
the new coordinates. The cubic phase uses the same new coordinate,
and the original finite seed weights give one fixed tensor label. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix StandardAdelic
open scoped NumberField MatrixGroups AdeleRing BigOperators Classical
noncomputable section

private theorem sourceKPRetained_weighted_tensor_sum {I J : Type*} [Fintype I] [Fintype J]
    (w : I → ℂ) (p : ℂ) (c : J → ℂ) (f : I → J → ℂ) :
    (∑ i, w i * (p * ∑ j, c j * f i j)) =
      p * ∑ k : I × J, w k.1 * c k.2 * f k.1 k.2 := by
  simp only [Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ac_rfl

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPAdelicOutgoingRetainedDiagonalPhase_inv_mul
    (P : HeightOneSpectrum (𝓞 K)) (m z : (P.adicCompletion K)ˣ) :
    sourceKPTameUniformizerCharacter K hζ P m (m⁻¹*z) =
      sourceKPTameUniformizerCharacter K hζ P m z := by
  let χ := sourceKPTameUniformizerCharacter K hζ P m
  have hm : χ m = 1 := by
    rw [sourceKPTameUniformizerCharacter_apply K hζ P m m, sourceFiniteKPHilbert_diag K hζ P m,
      one_pow, map_one]
  change χ (m⁻¹*z) = χ z
  rw [map_mul χ, map_inv χ, hm, inv_one, one_mul]

variable (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (hs : 0 < (1 / 6 : ℂ).re)

local notation "S" => sourceHilbertSet K S₀
local notation "A" => GL (Fin 2) 𝔸ᶠ[K]
local notation "L" => sourceKPLocalCompactProductLift K hζ S
local notation "σ" => sourceKPTraceJacquetFrequencyAt K
local notation "Ω" => sourceKPTameUniformizerCharacter K hζ
local notation "C₁" => sourceKPCuspResidualFourierValue K hζ (1 : Kˣ)
local notation "word" => sourceKPReflectedC1RetainedWord K hζ S₀
local notation "pre" => sourceKPAdelicOutgoingReflectedRetainedPrefix K hζ S₀
local notation "Label" => SourceKPAdelicOutgoingRetainedJacquetLabel K hζ hs S
local notation "lift" => sourceKPAdelicOutgoingRetainedJacquetBasisLift K hζ
local notation "F" => sourceKPAdelicOutgoingRetainedJacquetBasisDiagonalProfile K hζ

theorem sourceKPAdelicOutgoingReflectedRetainedC1_substituted_tensor
    {T : ℝ} (hT : 2 < T) (m : Kˣ) (z : SWholeUnits K S)
    (R M₀ : S → ℕ) (i : SourceKPRetainedSeedIndex K S R M₀) (a₀ : A) :
    C₁ (one_le_two.trans hT.le) ((L (word m ((sWholeDiagonal K S m)⁻¹*z) R M₀ i a₀)).2) =
      (∏ P : S, (Ω P.val (σ P.val m) (z.2 P) : ℂ)) *
        ∑ k : Label, C₁ (one_le_two.trans hT.le) ((L (fun P => lift P.val hs (k P))).2) *
          ∏ P : S, F P.val hs (k P) (pre R M₀ i a₀ P) (z.2 P) := by
  let x := (sWholeDiagonal K S m)⁻¹*z
  have hcoord (P : S) : σ P.val m * x.2 P = z.2 P := by
    change σ P.val m * ((σ P.val m)⁻¹ * z.2 P) = z.2 P
    exact mul_inv_cancel_left _ _
  have hphase (P : S) : Ω P.val (σ P.val m) (x.2 P) = Ω P.val (σ P.val m) (z.2 P) :=
    sourceKPAdelicOutgoingRetainedDiagonalPhase_inv_mul K hζ P.val (σ P.val m) (z.2 P)
  have h := sourceKPAdelicOutgoingReflectedRetainedC1_diagonal_tensor K hζ S₀ hs hT m x R M₀ i a₀
  simpa only [hcoord,hphase] using h

theorem sourceKPAdelicOutgoingReflectedRetainedC1_seed_sum_substituted_tensor
    {T : ℝ} (hT : 2 < T) (m : Kˣ) (z : SWholeUnits K S)
    (R M₀ : S → ℕ) (a₀ : A) :
    (∑ i : SourceKPRetainedSeedIndex K S R M₀,
      sourceKPRetainedSeedWeight K S R M₀ i *
        C₁ (one_le_two.trans hT.le) ((L (word m ((sWholeDiagonal K S m)⁻¹*z) R M₀ i a₀)).2)) =
      (∏ P : S, (Ω P.val (σ P.val m) (z.2 P) : ℂ)) *
        ∑ k : SourceKPRetainedSeedIndex K S R M₀ × Label,
          sourceKPRetainedSeedWeight K S R M₀ k.1 *
            C₁ (one_le_two.trans hT.le) ((L (fun P => lift P.val hs (k.2 P))).2) *
              ∏ P : S, F P.val hs (k.2 P) (pre R M₀ k.1 a₀ P) (z.2 P) := by
  simp_rw [sourceKPAdelicOutgoingReflectedRetainedC1_substituted_tensor K hζ S₀ hs hT m z R M₀]
  exact sourceKPRetained_weighted_tensor_sum (sourceKPRetainedSeedWeight K S R M₀) _
    (fun k : Label => C₁ (one_le_two.trans hT.le) ((L (fun P => lift P.val hs (k P))).2))
    (fun i k => ∏ P : S, F P.val hs (k P) (pre R M₀ i a₀ P) (z.2 P))

end
end ArtinMatthews
