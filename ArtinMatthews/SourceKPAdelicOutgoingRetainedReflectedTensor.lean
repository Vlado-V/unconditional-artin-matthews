module

public import ArtinMatthews.SourceKPAdelicOutgoingRetainedDiagonalTensor
public import ArtinMatthews.SourceKPAdelicOutgoingRetainedCompactProfiles
public import ArtinMatthews.SourceKPReflectedC1CoverWords


set_option backward.privateInPublic true
@[expose] public section

/-! The actual reflected retained word is evaluated at the product
of its principal and retained diagonal coordinates. Its signed
Weyl and seed prefix stays literal, and the cubic phase is separate. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix StandardAdelic SourcePhysical
open scoped NumberField MatrixGroups AdeleRing BigOperators Classical SourcePhysical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K)))

local notation "S" => sourceHilbertSet K S₀
local notation "G" => SourceKPAdelicProjective K hζ
local notation "Gf" => SourceKPFiniteAdeleProjective K hζ
local notation "Gₛ" => SourceKPLocalCompactProductGroup K hζ S
local notation "A" => GL (Fin 2) 𝔸ᶠ[K]
local notation "L" => sourceKPLocalCompactProductLift K hζ S
local notation "l" => sourceFiniteKP2ProjectiveLift K hζ
local notation "σ" => sourceKPTraceJacquetFrequencyAt K
local notation "C₁" => sourceKPCuspResidualFourierValue K hζ (1 : Kˣ)
local notation "coef" => sourceKPAdelicOutgoingRetainedResidualCoefficient K hζ S
local notation "word" => sourceKPReflectedC1RetainedWord K hζ S₀
local notation "Ω" => sourceKPTameUniformizerCharacter K hζ

def sourceKPAdelicOutgoingReflectedRetainedPrefix
    (R M₀ : S → ℕ) (i : SourceKPRetainedSeedIndex K S R M₀) (a₀ : A) : Gₛ :=
  fun P => (l P.val (sourceGL2Diagonal (-1)) * l P.val sourceGL2Weyl) *
    l P.val (sourceGL2Upper (sourceJacquetUpperRepresentative K P.val (R P) (M₀ P) (i P))) *
    l P.val (sourceKPAdeleMatrixAt K P.val a₀)

local notation "pre" => sourceKPAdelicOutgoingReflectedRetainedPrefix K hζ S₀

theorem sourceKPAdelicOutgoingReflectedRetainedWord_eq (m : Kˣ) (x : SWholeUnits K S)
    (R M₀ : S → ℕ) (i : SourceKPRetainedSeedIndex K S R M₀) (a₀ : A) :
    word m x R M₀ i a₀ = fun P =>
      l P.val (sourceGL2Diagonal (σ P.val m)) * l P.val (sourceGL2Diagonal (x.2 P)) *
        pre R M₀ i a₀ P := by
  funext P
  simp only [sourceKPReflectedC1RetainedWord, sourceKPAdelicOutgoingReflectedRetainedPrefix,
    sourceFiniteKP2ProjectiveLift, map_mul, mul_assoc]

variable (hs : 0 < (1 / 6 : ℂ).re)

local notation "Label" => SourceKPAdelicOutgoingRetainedJacquetLabel K hζ hs S
local notation "lift" => sourceKPAdelicOutgoingRetainedJacquetBasisLift K hζ
local notation "F" => sourceKPAdelicOutgoingRetainedJacquetBasisDiagonalProfile K hζ

theorem sourceKPAdelicOutgoingReflectedRetainedC1_diagonal_tensor
    {T : ℝ} (hT : 2 < T) (m : Kˣ) (x : SWholeUnits K S)
    (R M₀ : S → ℕ) (i : SourceKPRetainedSeedIndex K S R M₀) (a₀ : A) :
    C₁ (one_le_two.trans hT.le) ((L (word m x R M₀ i a₀)).2) =
      (∏ P : S, (Ω P.val (σ P.val m) (x.2 P) : ℂ)) *
        ∑ k : Label, C₁ (one_le_two.trans hT.le) ((L (fun P => lift P.val hs (k P))).2) *
          ∏ P : S, F P.val hs (k P) (pre R M₀ i a₀ P) (σ P.val m * x.2 P) := by
  have hq (P : S) : sourceKPAdelicLocalBase K hζ P.val (1,(1 : Gf)) = 1 :=
    map_one (sourceKPAdelicLocalBase K hζ P.val)
  have ht := sourceKPAdelicOutgoingRetainedResidualCoefficient_diagonal_mul_tensor K hζ S hs hT
    (1 : Gf) hq (fun P => σ P.val m) x.2 (pre R M₀ i a₀)
  have hw := congrArg (fun g : Gₛ => coef hT (1 : Gf) g)
    (sourceKPAdelicOutgoingReflectedRetainedWord_eq K hζ S₀ m x R M₀ i a₀)
  simpa only [sourceKPAdelicOutgoingRetainedResidualCoefficient, one_mul] using hw.trans ht

theorem sourceKPAdelicOutgoingReflectedRetainedPrefix_profile_uniform
    (R M₀ : S → ℕ) (a₀ : A) (P : S) :
    ∃ n : ℕ, ∃ M : ℝ, 0 < M ∧
      ∀ (i : SourceKPRetainedSeedIndex K S R M₀)
        (k : SourceKPAdelicOutgoingRetainedJacquetBasisIndex K hζ P.val hs),
      Continuous (F P.val hs k (pre R M₀ i a₀ P)) ∧
      (∀ z : (P.val.adicCompletion K)ˣ, z ∉ sourceLocalMulBall K P.val (n : ℤ) →
        F P.val hs k (pre R M₀ i a₀ P) z = 0) ∧
      ∀ z : (P.val.adicCompletion K)ˣ, z ∈ sourceLocalMulBall K P.val 0 →
        ‖F P.val hs k (pre R M₀ i a₀ P) z‖ ≤
          M * ‖(z : P.val.adicCompletion K)‖ ^ (1 / 3 : ℝ) := by
  obtain ⟨n,M,hM,h⟩ := sourceKPAdelicOutgoingRetainedJacquetBasisDiagonalProfile_compact_uniform
    K hζ P.val hs (fun i : SourceKPRetainedSeedIndex K S R M₀ => pre R M₀ i a₀ P)
  refine ⟨n,M,hM,fun i k => ?_⟩
  simpa only [Subgroup.coe_one,mul_one] using h i k (1 : sourceKPLocalCompactCover K hζ P.val)

end
end ArtinMatthews
